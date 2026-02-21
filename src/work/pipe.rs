use crate::constraint::ConstraintOps;
use crate::factors::Factors;
use crate::kernel::{compose_nf, meet_nf};
use crate::nf::NF;
use crate::node::Node;
use crate::rel::{Rel, RelId};
use crate::term::TermStore;
use std::sync::Arc;

use super::{
    flatten_and_parts, nf_domain_filter, nf_left_prefix, nf_right_suffix, nf_rwl_iso, nf_rwr_iso,
    node_from_answers, wrap_compose_with_prefix_suffix, wrap_rel_with_atoms, AndGroup, CallKey,
    CallMode, ComposeWork, Env, FixWork, ProducerSpec, Tables, Work, WorkStep,
};

#[derive(Clone, Copy, Debug)]
enum PipeEnd {
    Front,
    Back,
}

/// Pipeline work: sequential composition with boundary fusion.
///
/// Represents: left ; mid[0] ; mid[1] ; ... ; mid[n-1] ; right
///
/// Normalization absorbs Atoms at boundaries via compose_nf.
/// Or nodes in mid cause splits. Zero in mid annihilates.
///
/// Evaluation alternates front/back via flip. Or distribution is deferred
/// when the other end has non-Or work. Internal Atoms split the pipe to
/// give each segment tighter boundaries.
#[derive(Clone, Debug)]
pub struct PipeWork<C: ConstraintOps> {
    /// Left boundary (fused from front).
    pub(crate) left: Option<NF<C>>,
    /// Middle factors (remaining Rel elements).
    pub(crate) mid: Factors<C>,
    /// Right boundary (fused from back).
    pub(crate) right: Option<NF<C>>,
    /// Flip bit: alternates which end to process for outside-in evaluation.
    pub(crate) flip: bool,
    /// When true, mid has been scanned and contains no normalizable
    /// structure (no Seq, And, Zero, or adjacent Atom pairs).
    /// Popping from ends preserves this invariant; only pushing new
    /// elements or rebuilding mid invalidates it.
    mid_normalized: bool,
    /// Environment for Fix bindings (RelId -> Rel body).
    pub(crate) env: Env<C>,
    /// Tables for call-context tabling.
    pub(crate) tables: Tables<C>,
    /// Call handling mode.
    pub(crate) call_mode: CallMode<C>,
}

impl<C: ConstraintOps> Work<C> {
    /// Step this work item, returning the next state.
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        match self {
            Work::Pipe(pipe) => pipe.step(terms),
            Work::Meet(meet) => meet.step(terms),
            Work::AndGroup(group) => group.step(terms),
            Work::Fix(fix) => fix.step(terms),
            Work::Compose(compose) => compose.step(terms),
            Work::JoinReceiver(join) => join.step(terms),
            Work::Atom(nf) => {
                // Emit the NF once, then done
                let nf = nf.clone();
                WorkStep::Emit(nf, Box::new(Work::Done))
            }
            Work::Done => WorkStep::Done,
        }
    }
}

impl<C: ConstraintOps> PipeWork<C> {
    fn new_with_parts(
        left: Option<NF<C>>,
        mid: Factors<C>,
        right: Option<NF<C>>,
        env: Env<C>,
        tables: Tables<C>,
    ) -> Self {
        PipeWork {
            left,
            mid,
            right,
            flip: false,
            mid_normalized: false,
            env,
            tables,
            call_mode: CallMode::Normal,
        }
    }

    /// Create an empty pipe (represents identity and emits it).
    pub fn new() -> Self {
        Self::new_with_parts(None, Factors::new(), None, Env::new(), Tables::new())
    }

    /// Create a pipe with only mid factors.
    pub fn with_mid(mid: Factors<C>) -> Self {
        Self::new_with_parts(None, mid, None, Env::new(), Tables::new())
    }

    /// Create a pipe with boundaries and mid.
    pub fn with_boundaries(left: Option<NF<C>>, mid: Factors<C>, right: Option<NF<C>>) -> Self {
        Self::new_with_parts(left, mid, right, Env::new(), Tables::new())
    }

    /// Create a pipe with full state including env and tables.
    pub fn with_env_and_tables(
        left: Option<NF<C>>,
        mid: Factors<C>,
        right: Option<NF<C>>,
        env: Env<C>,
        tables: Tables<C>,
    ) -> Self {
        Self::new_with_parts(left, mid, right, env, tables)
    }

    /// Create a pipe from a Rel expression with given env and tables.
    pub fn from_rel(rel: Rel<C>, env: Env<C>, tables: Tables<C>) -> Self {
        let mid = match &rel {
            Rel::Seq(factors) => Factors::from_seq(factors.clone()),
            _ => {
                // Single non-Seq rel becomes a single-element mid
                let factors: Arc<[Arc<Rel<C>>]> = Arc::from(vec![Arc::new(rel)]);
                Factors::from_seq(factors)
            }
        };
        Self::new_with_parts(None, mid, None, env, tables)
    }

    /// Create a producer pipe with boundaries as Atom factors in mid.
    /// The pipe will be: [Atom(left)?] ++ body_factors ++ [Atom(right)?]
    /// This ensures boundaries are visible for call-context key formation.
    pub fn from_rel_with_boundaries(
        rel: Rel<C>,
        left: Option<NF<C>>,
        right: Option<NF<C>>,
        env: Env<C>,
        tables: Tables<C>,
    ) -> Self {
        // Build mid factors: [left_atom?, body_factors..., right_atom?]
        let mut factors_vec: Vec<Arc<Rel<C>>> = Vec::new();

        // Add left boundary as Atom if present
        if let Some(left_nf) = left {
            factors_vec.push(Arc::new(Rel::Atom(Arc::new(left_nf))));
        }

        // Add body factors
        match &rel {
            Rel::Seq(body_factors) => {
                for f in body_factors.iter() {
                    factors_vec.push(f.clone());
                }
            }
            _ => {
                factors_vec.push(Arc::new(rel));
            }
        }

        // Add right boundary as Atom if present
        if let Some(right_nf) = right {
            factors_vec.push(Arc::new(Rel::Atom(Arc::new(right_nf))));
        }

        let factors: Arc<[Arc<Rel<C>>]> = Arc::from(factors_vec);
        let mid = Factors::from_seq(factors);

        Self::new_with_parts(None, mid, None, env, tables)
    }

    /// Check if the pipe is empty (no boundaries and no mid).
    pub fn is_empty(&self) -> bool {
        self.left.is_none() && self.mid.is_empty() && self.right.is_none()
    }

    /// Step this pipeline, returning the next state.
    ///
    /// Two-phase approach for direction-agnostic evaluation:
    /// - Phase A: Try to normalize (absorb atoms, flatten Seq, detect Zero) at BOTH ends
    /// - Phase B: When stuck, advance one end using alternating flip
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        loop {
            // Phase A: Check for empty mid
            if self.mid.is_empty() {
                return self.emit_boundaries(terms);
            }

            // Phase A: Try to normalize at either end
            match self.try_normalize_step(terms) {
                Ok(true) => continue,
                Ok(false) => {}
                Err(step) => return step,
            }

            // Phase A: Normalize adjacent atoms anywhere in mid
            match self.normalize_mid_atoms(terms) {
                Ok(true) => continue,
                Ok(false) => {}
                Err(step) => return step,
            }

            if let Some(step) = self.try_split_call_atom_call() {
                return step;
            }

            // Phase B: Try to batch-advance simple Calls (single-Atom bodies).
            // When a Call resolves to a Fix whose body is a single Atom(nf),
            // we can compose the NF directly into the boundary without creating
            // FixWork/ComposeWork/DiagonalJoin machinery. This is a tight loop
            // that handles chains of such Calls in O(1) per element.
            match self.try_batch_advance_calls(terms) {
                Ok(true) => continue,
                Ok(false) => {}
                Err(step) => return step,
            }

            break;
        }

        // Phase C: General advance - advance one end using flip.
        let end = self.choose_advance_end();
        let result = self.advance_end(end, terms);
        self.flip = !self.flip; // Toggle for next step
        result
    }

    fn try_split_call_atom_call(&self) -> Option<WorkStep<C>> {
        if self.mid.len() != 3 {
            return None;
        }
        let factors = self.mid.to_vec();
        let front = factors.first()?.as_ref();
        let middle = factors.get(1)?.as_ref();
        let back = factors.get(2)?.as_ref();
        if !matches!(front, Rel::Call(_)) {
            return None;
        }
        let middle_nf = match middle {
            Rel::Atom(nf) => nf.as_ref(),
            _ => return None,
        };
        if !matches!(back, Rel::Call(_)) {
            return None;
        }

        let left_seq: Arc<[Arc<Rel<C>>]> = Arc::from(vec![factors[0].clone()]);
        let right_seq: Arc<[Arc<Rel<C>>]> = Arc::from(vec![factors[1].clone(), factors[2].clone()]);
        let mut left_pipe = PipeWork::new_with_parts(
            self.left.clone(),
            Factors::from_seq(left_seq),
            Some(nf_domain_filter(middle_nf)),
            self.env.clone(),
            self.tables.clone(),
        );
        let mut right_pipe = PipeWork::new_with_parts(
            None,
            Factors::from_seq(right_seq),
            self.right.clone(),
            self.env.clone(),
            self.tables.clone(),
        );
        left_pipe.call_mode = self.call_mode.clone();
        right_pipe.call_mode = self.call_mode.clone();
        let left_node = Node::Work(Box::new(Work::Pipe(Box::new(left_pipe))));
        let right_node = Node::Work(Box::new(Work::Pipe(Box::new(right_pipe))));
        let compose = ComposeWork::new(left_node, right_node);
        Some(WorkStep::More(Box::new(Work::Compose(compose))))
    }

    /// Choose which end to advance when normalization is stuck.
    ///
    /// If one end is a Call and the other is not, advance the non-Call end
    /// so any adjacent boundary normalization can flow into the Call key.
    fn choose_advance_end(&self) -> PipeEnd {
        let front_is_call = matches!(self.mid.front().map(|rel| rel.as_ref()), Some(Rel::Call(_)));
        let back_is_call = matches!(self.mid.back().map(|rel| rel.as_ref()), Some(Rel::Call(_)));

        let mut advance_back = self.flip;
        if advance_back && back_is_call && !front_is_call {
            advance_back = false;
        } else if !advance_back && front_is_call && !back_is_call {
            advance_back = true;
        }

        if advance_back {
            PipeEnd::Back
        } else {
            PipeEnd::Front
        }
    }

    /// Emit the composed boundaries when mid is empty.
    fn emit_boundaries(&self, terms: &mut TermStore) -> WorkStep<C> {
        match (&self.left, &self.right) {
            (None, None) => {
                // Empty pipe - emit identity
                WorkStep::Emit(NF::identity(C::default()), Box::new(Work::Done))
            }
            (Some(left), None) => {
                // Only left boundary
                WorkStep::Emit(left.clone(), Box::new(Work::Done))
            }
            (None, Some(right)) => {
                // Only right boundary
                WorkStep::Emit(right.clone(), Box::new(Work::Done))
            }
            (Some(left), Some(right)) => {
                // Compose left and right
                match compose_nf(left, right, terms) {
                    Some(composed) => WorkStep::Emit(composed, Box::new(Work::Done)),
                    None => WorkStep::Done, // Composition failed
                }
            }
        }
    }

    /// Absorb an NF from the front into the left boundary.
    fn absorb_front(&mut self, nf: NF<C>, terms: &mut TermStore) -> bool {
        match &self.left {
            None => {
                // No left boundary, this NF becomes the left boundary
                self.left = Some(nf);
                true
            }
            Some(left) => {
                // Try to compose with left boundary
                match compose_nf(left, &nf, terms) {
                    Some(composed) => {
                        self.left = Some(composed);
                        true
                    }
                    None => {
                        // Composition failed - signal failure
                        false
                    }
                }
            }
        }
    }

    /// Absorb an NF from the back into the right boundary.
    fn absorb_back(&mut self, nf: NF<C>, terms: &mut TermStore) -> bool {
        match &self.right {
            None => {
                // No right boundary, this NF becomes the right boundary
                self.right = Some(nf);
                true
            }
            Some(right) => {
                // Try to compose: nf ; right
                match compose_nf(&nf, right, terms) {
                    Some(composed) => {
                        self.right = Some(composed);
                        true
                    }
                    None => {
                        // Composition failed - signal failure
                        false
                    }
                }
            }
        }
    }

    fn split_or(&self, end: PipeEnd, a: Arc<Rel<C>>, b: Arc<Rel<C>>) -> WorkStep<C> {
        // Create two pipes - one with branch a, one with branch b.
        // Both keep the same boundaries, env, tables, and remaining mid.
        let mut left_pipe = self.clone();
        let mut right_pipe = self.clone();
        match end {
            PipeEnd::Front => {
                left_pipe.mid.push_front_rel(a);
                right_pipe.mid.push_front_rel(b);
            }
            PipeEnd::Back => {
                left_pipe.mid.push_back_rel(a);
                right_pipe.mid.push_back_rel(b);
            }
        }
        // Pushed elements may introduce normalizable structure.
        left_pipe.mid_normalized = false;
        right_pipe.mid_normalized = false;
        WorkStep::Split(
            Box::new(Node::Work(Box::new(Work::Pipe(Box::new(left_pipe))))),
            Box::new(Node::Work(Box::new(Work::Pipe(Box::new(right_pipe))))),
        )
    }

    /// Try to normalize one step at either end.
    /// Returns Ok(true) if progress was made, Ok(false) if stuck,
    /// or Err(step) if normalization yields a terminal result.
    fn try_normalize_step(&mut self, terms: &mut TermStore) -> Result<bool, WorkStep<C>> {
        // Try front first
        if let Some(front) = self.mid.front().cloned() {
            match front.as_ref() {
                Rel::Zero => {
                    // Zero annihilates the pipe
                    return Err(WorkStep::Done);
                }
                Rel::Atom(nf) => {
                    self.mid.pop_front();
                    if self.absorb_front(nf.as_ref().clone(), terms) {
                        return Ok(true);
                    }
                    return Err(WorkStep::Done);
                }
                Rel::Seq(xs) => {
                    self.mid.pop_front();
                    self.mid.push_front_slice_from_seq(xs.clone());
                    self.mid_normalized = false;
                    return Ok(true);
                }
                _ => {}
            }
        }

        // Try back
        if let Some(back) = self.mid.back().cloned() {
            match back.as_ref() {
                Rel::Zero => {
                    // Zero annihilates the pipe
                    return Err(WorkStep::Done);
                }
                Rel::Atom(nf) => {
                    self.mid.pop_back();
                    if self.absorb_back(nf.as_ref().clone(), terms) {
                        return Ok(true);
                    }
                    return Err(WorkStep::Done);
                }
                Rel::Seq(xs) => {
                    self.mid.pop_back();
                    self.mid.push_back_slice_from_seq(xs.clone());
                    self.mid_normalized = false;
                    return Ok(true);
                }
                _ => {}
            }
        }

        // No progress possible
        Ok(false)
    }

    /// Normalize mid factors by flattening Seq and fusing adjacent atoms anywhere.
    fn normalize_mid_atoms(&mut self, terms: &mut TermStore) -> Result<bool, WorkStep<C>> {
        if self.mid.is_empty() || self.mid_normalized {
            return Ok(false);
        }

        let mut factors = self.mid.to_vec();
        let mut changed = false;

        // Flatten nested Seq factors anywhere in the mid.
        loop {
            let mut flattened = Vec::new();
            let mut did_flatten = false;
            for factor in factors {
                match factor.as_ref() {
                    Rel::Seq(xs) => {
                        did_flatten = true;
                        for f in xs.iter() {
                            flattened.push(f.clone());
                        }
                    }
                    _ => flattened.push(factor),
                }
            }
            factors = flattened;
            if !did_flatten {
                break;
            }
            changed = true;
        }

        // Collapse And factors that are fully atomic into a single Atom via meet.
        for rel in factors.iter_mut() {
            let Rel::And(_, _) = rel.as_ref() else {
                continue;
            };
            let parts = flatten_and_parts(rel.clone());
            let mut acc: Option<NF<C>> = None;
            let mut all_atoms = true;
            for part in parts {
                match part.as_ref() {
                    Rel::Atom(nf) => {
                        acc = match acc {
                            None => Some(nf.as_ref().clone()),
                            Some(prev) => meet_nf(&prev, nf.as_ref(), terms),
                        };
                        if acc.is_none() {
                            return Err(WorkStep::Done);
                        }
                    }
                    Rel::Zero => return Err(WorkStep::Done),
                    _ => {
                        all_atoms = false;
                        break;
                    }
                }
            }

            if all_atoms {
                if let Some(nf) = acc {
                    *rel = Arc::new(Rel::Atom(Arc::new(nf)));
                    changed = true;
                }
            }
        }

        if factors.iter().any(|f| matches!(f.as_ref(), Rel::Zero)) {
            return Err(WorkStep::Done);
        }

        // Fuse adjacent Atom factors anywhere.
        let mut i = 0;
        while i + 1 < factors.len() {
            let left = factors[i].clone();
            let right = factors[i + 1].clone();
            if let (Rel::Atom(a), Rel::Atom(b)) = (left.as_ref(), right.as_ref()) {
                let Some(composed) = compose_nf(a, b, terms) else {
                    return Err(WorkStep::Done);
                };
                factors[i] = Arc::new(Rel::Atom(Arc::new(composed)));
                factors.remove(i + 1);
                changed = true;
                i = i.saturating_sub(1);
                continue;
            }
            i += 1;
        }

        if changed {
            let seq: Arc<[Arc<Rel<C>>]> = Arc::from(factors);
            self.mid = Factors::from_seq(seq);
            // Rebuild may have created new adjacent atoms; re-check next time.
            self.mid_normalized = false;
        } else {
            // No changes found — mid is fully normalized.
            self.mid_normalized = true;
        }

        Ok(changed)
    }

    fn left_prefix_iso(&self, terms: &mut TermStore) -> (Option<NF<C>>, Option<NF<C>>) {
        match &self.left {
            Some(nf) => (Some(nf_left_prefix(nf, terms)), Some(nf_rwr_iso(nf, terms))),
            None => (None, None),
        }
    }

    fn right_suffix_iso(&self, terms: &mut TermStore) -> (Option<NF<C>>, Option<NF<C>>) {
        match &self.right {
            Some(nf) => (
                Some(nf_right_suffix(nf, terms)),
                Some(nf_rwl_iso(nf, terms)),
            ),
            None => (None, None),
        }
    }

    fn pop_end(&mut self, end: PipeEnd) {
        match end {
            PipeEnd::Front => {
                self.mid.pop_front();
            }
            PipeEnd::Back => {
                self.mid.pop_back();
            }
        }
    }

    fn and_left_context(
        &self,
        end: PipeEnd,
        mid_empty: bool,
        terms: &mut TermStore,
    ) -> (Option<NF<C>>, Option<NF<C>>) {
        match end {
            PipeEnd::Front => self.left_prefix_iso(terms),
            PipeEnd::Back => {
                if mid_empty {
                    self.left_prefix_iso(terms)
                } else {
                    (self.left.clone(), None)
                }
            }
        }
    }

    fn and_right_context(
        &self,
        end: PipeEnd,
        mid_empty: bool,
        terms: &mut TermStore,
    ) -> (Option<NF<C>>, Option<NF<C>>) {
        match end {
            PipeEnd::Back => self.right_suffix_iso(terms),
            PipeEnd::Front => {
                if mid_empty {
                    self.right_suffix_iso(terms)
                } else {
                    (self.right.clone(), None)
                }
            }
        }
    }

    fn build_and_group(
        &self,
        parts: Vec<Arc<Rel<C>>>,
        left_iso: Option<NF<C>>,
        right_iso: Option<NF<C>>,
    ) -> AndGroup<C> {
        let nodes = parts
            .into_iter()
            .map(|part| {
                let wrapped = wrap_rel_with_atoms(part, left_iso.clone(), right_iso.clone());
                let mut part_pipe =
                    PipeWork::from_rel(wrapped, self.env.clone(), self.tables.clone());
                part_pipe.call_mode = self.call_mode.clone();
                Node::Work(Box::new(Work::Pipe(Box::new(part_pipe))))
            })
            .collect();
        AndGroup::new(nodes)
    }

    fn advance_or(&mut self, end: PipeEnd, a: Arc<Rel<C>>, b: Arc<Rel<C>>) -> WorkStep<C> {
        self.pop_end(end);
        self.split_or(end, a, b)
    }

    fn advance_and(
        &mut self,
        end: PipeEnd,
        rel: Arc<Rel<C>>,
        terms: &mut TermStore,
    ) -> WorkStep<C> {
        self.pop_end(end);

        let parts = flatten_and_parts(rel);
        let mid_empty = self.mid.is_empty();
        let (left_prefix, left_iso) = self.and_left_context(end, mid_empty, terms);
        let (right_suffix, right_iso) = self.and_right_context(end, mid_empty, terms);
        let group = self.build_and_group(parts, left_iso.clone(), right_iso.clone());

        let mut pipe = self.clone();
        let (left_node, right_node, outer_prefix, outer_suffix) = match end {
            PipeEnd::Front => {
                pipe.left = None;
                pipe.right = if right_iso.is_some() {
                    None
                } else {
                    right_suffix.clone()
                };
                let left_node = Node::Work(Box::new(Work::AndGroup(group)));
                let right_node = Node::Work(Box::new(Work::Pipe(Box::new(pipe))));
                let outer_suffix = if right_iso.is_some() {
                    right_suffix
                } else {
                    None
                };
                (left_node, right_node, left_prefix, outer_suffix)
            }
            PipeEnd::Back => {
                pipe.right = None;
                pipe.left = if left_iso.is_some() {
                    None
                } else {
                    left_prefix.clone()
                };
                let left_node = Node::Work(Box::new(Work::Pipe(Box::new(pipe))));
                let right_node = Node::Work(Box::new(Work::AndGroup(group)));
                let outer_prefix = if left_iso.is_some() {
                    left_prefix
                } else {
                    None
                };
                (left_node, right_node, outer_prefix, right_suffix)
            }
        };

        let core = ComposeWork::new(left_node, right_node);
        wrap_compose_with_prefix_suffix(core, outer_prefix, outer_suffix)
    }

    fn advance_fix(&mut self, end: PipeEnd, id: RelId, body: Arc<Rel<C>>) -> WorkStep<C> {
        self.pop_end(end);
        let use_left = matches!(end, PipeEnd::Front) || self.mid.is_empty();
        let use_right = matches!(end, PipeEnd::Back) || self.mid.is_empty();
        let call_left = if use_left { self.left.clone() } else { None };
        let call_right = if use_right { self.right.clone() } else { None };
        let bound_env = self.env.bind(id, body.clone());

        let mut fix_pipe = PipeWork::from_rel_with_boundaries(
            body.as_ref().clone(),
            call_left,
            call_right,
            bound_env,
            self.tables.clone(),
        );
        fix_pipe.call_mode = self.call_mode.clone();

        let fix_node = Node::Work(Box::new(Work::Pipe(Box::new(fix_pipe))));
        let mut pipe = self.clone();
        if use_left {
            pipe.left = None;
        }
        if use_right {
            pipe.right = None;
        }
        let (left_node, right_node) = match end {
            PipeEnd::Front => (fix_node, Node::Work(Box::new(Work::Pipe(Box::new(pipe))))),
            PipeEnd::Back => (Node::Work(Box::new(Work::Pipe(Box::new(pipe)))), fix_node),
        };
        let compose = ComposeWork::new(left_node, right_node);
        WorkStep::More(Box::new(Work::Compose(compose)))
    }

    /// Try to batch-advance Calls at either end whose body is a single Atom.
    ///
    /// When a Call resolves (via env lookup) to a body that is `Rel::Atom(nf)`,
    /// the result is completely deterministic: exactly one NF. Instead of
    /// creating FixWork/Table/ComposeWork/DiagonalJoin machinery (O(1) per
    /// Call but with high constant), we compose the NF directly into the
    /// pipe boundary in a tight loop.
    ///
    /// Returns Ok(true) if progress was made, Ok(false) if no simple Calls
    /// were found, or Err(WorkStep::Done) if composition failed.
    fn try_batch_advance_calls(&mut self, terms: &mut TermStore) -> Result<bool, WorkStep<C>> {
        let mut made_progress = false;
        loop {
            // Try front
            if let Some(front) = self.mid.front() {
                if let Rel::Call(id) = front.as_ref() {
                    let id = *id;
                    if let Some(binding) = self.env.lookup(id) {
                        if let Rel::Atom(nf) = binding.body.as_ref() {
                            self.mid.pop_front();
                            if !self.absorb_front(nf.as_ref().clone(), terms) {
                                return Err(WorkStep::Done);
                            }
                            made_progress = true;
                            continue;
                        }
                    }
                }
            }

            // Try back
            if let Some(back) = self.mid.back() {
                if let Rel::Call(id) = back.as_ref() {
                    let id = *id;
                    if let Some(binding) = self.env.lookup(id) {
                        if let Rel::Atom(nf) = binding.body.as_ref() {
                            self.mid.pop_back();
                            if !self.absorb_back(nf.as_ref().clone(), terms) {
                                return Err(WorkStep::Done);
                            }
                            made_progress = true;
                            continue;
                        }
                    }
                }
            }

            break;
        }
        Ok(made_progress)
    }

    fn advance_call(&mut self, end: PipeEnd, id: RelId) -> WorkStep<C> {
        self.pop_end(end);
        match end {
            PipeEnd::Front => self.handle_call(id, true),
            PipeEnd::Back => self.handle_call(id, false),
        }
    }

    /// Advance the selected end when stuck on normalization.
    fn advance_end(&mut self, end: PipeEnd, terms: &mut TermStore) -> WorkStep<C> {
        let rel = match end {
            PipeEnd::Front => self.mid.front().cloned(),
            PipeEnd::Back => self.mid.back().cloned(),
        };
        let Some(rel) = rel else {
            return self.emit_boundaries(terms);
        };

        match rel.as_ref() {
            Rel::Or(a, b) => self.advance_or(end, a.clone(), b.clone()),
            Rel::And(_, _) => self.advance_and(end, rel.clone(), terms),
            Rel::Fix(id, body) => self.advance_fix(end, *id, body.clone()),
            Rel::Call(id) => self.advance_call(end, *id),
            // Atom/Zero/Seq should have been normalized in try_normalize_step
            _ => WorkStep::Done,
        }
    }

    #[cfg(test)]
    pub(crate) fn advance_front(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        self.advance_end(PipeEnd::Front, terms)
    }

    /// Handle a Call by looking up in the environment and using tabling.
    fn handle_call(&mut self, id: RelId, absorb_front: bool) -> WorkStep<C> {
        let Some(binding) = self.env.lookup(id) else {
            return WorkStep::Done;
        };
        let use_left = if absorb_front {
            true
        } else {
            self.mid.is_empty()
        };
        let use_right = if absorb_front {
            self.mid.is_empty()
        } else {
            true
        };

        let call_left = if use_left { self.left.clone() } else { None };
        let mut call_right = if use_right { self.right.clone() } else { None };

        // Peek at the adjacent mid element in the far direction for an Atom
        // when advancing the front Call. The Call's output flows into the
        // next element, so an adjacent Atom is a sound constraint on output.
        // This doesn't consume the Atom — it remains in mid for normal
        // normalization when the Call's output flows back into the pipe.
        if call_right.is_none() && absorb_front {
            if let Some(Rel::Atom(nf)) = self.mid.front().map(|r| r.as_ref()) {
                call_right = Some(nf_domain_filter(nf.as_ref()));
            }
        }

        let key = Arc::new(CallKey::new(
            id,
            binding.id,
            call_left.clone(),
            call_right.clone(),
        ));
        if let CallMode::ReplayOnly(replay_key, watermark) = &self.call_mode {
            if replay_key.as_ref() == key.as_ref() {
                let table = match self.tables.lookup(&key) {
                    Some(table) => table,
                    None => return WorkStep::Done,
                };
                let snapshot = table.answers_from(*watermark);
                let replay_node = node_from_answers(snapshot);
                let mut pipe = self.clone();
                if use_left {
                    pipe.left = None;
                }
                if use_right {
                    pipe.right = None;
                }
                let (left_node, right_node) = if absorb_front {
                    (
                        replay_node,
                        Node::Work(Box::new(Work::Pipe(Box::new(pipe)))),
                    )
                } else {
                    (
                        Node::Work(Box::new(Work::Pipe(Box::new(pipe)))),
                        replay_node,
                    )
                };
                let compose = ComposeWork::new(left_node, right_node);
                return WorkStep::More(Box::new(Work::Compose(compose)));
            }
        }

        let table = self.tables.get_or_create(&key);
        table.ensure_producer_spec(ProducerSpec {
            key: key.clone(),
            body: binding.body.clone(),
            left: call_left.clone(),
            right: call_right.clone(),
            env: self.env.clone(),
        });
        let snapshot = table.all_answers();
        let snapshot_len = snapshot.len();

        let replay_node = node_from_answers(snapshot);
        let fix = FixWork::new(key, table, snapshot_len, self.tables.clone());
        let fix_node = Node::Work(Box::new(Work::Fix(fix)));

        let gen_node = match replay_node {
            Node::Fail => fix_node,
            _ => Node::Or(Box::new(replay_node), Box::new(fix_node)),
        };

        let mut pipe = self.clone();
        if use_left {
            pipe.left = None;
        }
        if use_right {
            pipe.right = None;
        }

        let (left_node, right_node) = if absorb_front {
            (gen_node, Node::Work(Box::new(Work::Pipe(Box::new(pipe)))))
        } else {
            (Node::Work(Box::new(Work::Pipe(Box::new(pipe)))), gen_node)
        };
        let compose = ComposeWork::new(left_node, right_node);
        WorkStep::More(Box::new(Work::Compose(compose)))
    }
}

impl<C: ConstraintOps> Default for PipeWork<C> {
    fn default() -> Self {
        Self {
            left: None,
            mid: Factors::new(),
            right: None,
            flip: false,
            mid_normalized: true,
            env: Env::new(),
            tables: Tables::new(),
            call_mode: CallMode::Normal,
        }
    }
}
