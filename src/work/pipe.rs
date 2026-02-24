use crate::constraint::ConstraintOps;
use crate::drop_fresh::DropFresh;
use crate::factors::Factors;
use crate::kernel::{compose_nf, meet_nf};
use crate::nf::NF;
use crate::node::Node;
use crate::rel::{Rel, RelId};
use crate::symbol::FuncId;
use crate::term::{Term, TermId, TermStore};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::sync::Arc;

use super::{
    build_child0_tag, build_root_tag, flatten_and_parts, match_child0_tag, match_root_tag,
    nf_domain_filter, nf_left_prefix, nf_right_suffix, nf_rwl_iso, nf_rwr_iso, node_from_answers,
    tags_compatible, wrap_compose_with_prefix_suffix, wrap_node_with_prefix_suffix,
    wrap_rel_with_atoms, AndGroup, BindWork,
    CallKey, CallMode, ComposeWork, Env, FixWork, ProducerSpec, RootTag, Tables, Work, WorkStep,
};

/// Pre-computed dispatch entry for a single atom in an Or-of-Atoms body.
#[derive(Clone, Debug)]
struct DispatchEntry<C: ConstraintOps> {
    atom: Arc<NF<C>>,
    match_root: RootTag,
    build_root: RootTag,
    match_child0: RootTag,
    build_child0: RootTag,
}

/// Cache of pre-computed dispatch tables, keyed by `Arc<Rel<C>>` pointer address.
type DispatchCache<C> = FxHashMap<usize, Arc<[DispatchEntry<C>]>>;

/// Result of dispatch filtering on a flat Or of Atoms.
enum DispatchResult<C: ConstraintOps> {
    /// No atoms matched the boundary's root functor.
    Fail,
    /// Exactly one atom matched - can be absorbed directly.
    Single(NF<C>),
    /// Multiple atoms matched - push filtered Or back into mid.
    Filtered(Rel<C>),
}

/// Collect all branches of a flat Or tree into a Vec.
/// Returns None if the tree contains any non-Atom leaves.
fn collect_flat_or_atoms<C: Clone>(rel: &Rel<C>) -> Option<Vec<Arc<NF<C>>>> {
    let mut atoms = Vec::new();
    collect_flat_or_atoms_inner(rel, &mut atoms)?;
    Some(atoms)
}

fn collect_flat_or_atoms_inner<C: Clone>(rel: &Rel<C>, out: &mut Vec<Arc<NF<C>>>) -> Option<()> {
    match rel {
        Rel::Or(a, b) => {
            collect_flat_or_atoms_inner(a, out)?;
            collect_flat_or_atoms_inner(b, out)?;
            Some(())
        }
        Rel::Atom(nf) => {
            out.push(nf.clone());
            Some(())
        }
        _ => None,
    }
}

/// Build a Rel from a list of atoms (right-nested Or).
fn atoms_to_or_rel<C: Clone>(atoms: &[Arc<NF<C>>]) -> Rel<C> {
    debug_assert!(!atoms.is_empty());
    if atoms.len() == 1 {
        return Rel::Atom(atoms[0].clone());
    }
    let mut rel = Rel::Atom(atoms[atoms.len() - 1].clone());
    for i in (0..atoms.len() - 1).rev() {
        rel = Rel::Or(Arc::new(Rel::Atom(atoms[i].clone())), Arc::new(rel));
    }
    rel
}

/// Check if an NF is a simple wrapper: `$x -> (f $x)`.
///
/// A simple wrapper has:
/// - Exactly one match pattern that is a bare variable (Var(0))
/// - Identity DropFresh(1,1,[(0,0)])
/// - Empty constraint
/// - Exactly one build pattern that is App(f, [Var(0)]) for some f
///
/// Returns the wrapper FuncId if the NF matches, None otherwise.
fn simple_wrapper_func<C: ConstraintOps>(nf: &NF<C>, terms: &TermStore) -> Option<FuncId> {
    // Must have exactly one match and one build pattern
    if nf.match_pats.len() != 1 || nf.build_pats.len() != 1 {
        return None;
    }
    // Match pattern must be Var(0)
    let match_pat = nf.match_pats[0];
    if !match_pat.is_inline_var() || match_pat.inline_var_index() != 0 {
        return None;
    }
    // DropFresh must be identity(1) with empty constraint
    let df = &nf.drop_fresh;
    if df.in_arity != 1 || df.out_arity != 1 || df.map.len() != 1 {
        return None;
    }
    if df.map[0] != (0, 0) {
        return None;
    }
    if !df.constraint.is_empty() {
        return None;
    }
    // Build pattern must be App(f, [Var(0)])
    let build_pat = nf.build_pats[0];
    terms.with_term(build_pat, |term| match term? {
        Term::App(func, children) if children.len() == 1 => {
            if children[0].is_inline_var() && children[0].inline_var_index() == 0 {
                Some(*func)
            } else {
                None
            }
        }
        _ => None,
    })
}

/// Build a chain NF from a sequence of wrapper FuncIds.
///
/// Given FuncIds [f0, f1, ..., fn] (in pipeline order, front to back),
/// builds the NF `$x -> fn(fn-1(...f1(f0($x))...))`.
/// This is equivalent to composing all the individual wrapper NFs but in O(n)
/// instead of O(n^2).
fn build_wrapper_chain_nf<C: ConstraintOps>(
    wrapper_funcs: &[FuncId],
    terms: &mut TermStore,
) -> NF<C> {
    debug_assert!(!wrapper_funcs.is_empty());
    // Build the nested term bottom-up: start with Var(0),
    // then wrap with each func in order
    let mut build_term = TermId::inline_var(0);
    for &func in wrapper_funcs {
        build_term = terms.app1(func, build_term);
    }
    NF::new(
        SmallVec::from_elem(TermId::inline_var(0), 1),
        DropFresh::identity_with_constraint(1, C::default()),
        SmallVec::from_elem(build_term, 1),
    )
}

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
    /// Cached dispatch tables for Or-of-Atoms bodies, keyed by Arc pointer address.
    /// Lazily allocated only when dispatch is actually used.
    dispatch_cache: Option<Box<DispatchCache<C>>>,
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
            Work::Bind(bind) => bind.step(terms),
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
            dispatch_cache: None,
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

    /// Absorb an NF into the boundary at the given end.
    /// Front absorbs into left boundary (left ; nf), back into right (nf ; right).
    fn absorb_at(&mut self, end: PipeEnd, nf: NF<C>, terms: &mut TermStore) -> bool {
        let boundary = match end {
            PipeEnd::Front => &mut self.left,
            PipeEnd::Back => &mut self.right,
        };
        match boundary {
            None => {
                *boundary = Some(nf);
                true
            }
            Some(existing) => {
                // Compose: front = existing ; nf, back = nf ; existing
                let composed = match end {
                    PipeEnd::Front => compose_nf(existing, &nf, terms),
                    PipeEnd::Back => compose_nf(&nf, existing, terms),
                };
                match composed {
                    Some(result) => {
                        *existing = result;
                        true
                    }
                    None => false,
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
        // Try front first, then back
        for &end in &[PipeEnd::Front, PipeEnd::Back] {
            if let Some(result) = self.try_normalize_end(end, terms) {
                return result;
            }
        }
        Ok(false)
    }

    /// Try to normalize one step at the given end.
    /// Returns `Some(result)` if the end was normalizable, `None` if not.
    fn try_normalize_end(
        &mut self,
        end: PipeEnd,
        terms: &mut TermStore,
    ) -> Option<Result<bool, WorkStep<C>>> {
        let rel = match end {
            PipeEnd::Front => self.mid.front().cloned(),
            PipeEnd::Back => self.mid.back().cloned(),
        }?;
        match rel.as_ref() {
            Rel::Zero => Some(Err(WorkStep::Done)),
            Rel::Atom(nf) => {
                self.pop_end(end);
                if self.absorb_at(end, nf.as_ref().clone(), terms) {
                    Some(Ok(true))
                } else {
                    Some(Err(WorkStep::Done))
                }
            }
            Rel::Seq(xs) => {
                self.pop_end(end);
                match end {
                    PipeEnd::Front => self.mid.push_front_slice_from_seq(xs.clone()),
                    PipeEnd::Back => self.mid.push_back_slice_from_seq(xs.clone()),
                }
                self.mid_normalized = false;
                Some(Ok(true))
            }
            _ => None,
        }
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

    /// Order a produced node and the remaining pipe node by end.
    /// Front: produced goes left, pipe goes right.
    /// Back: pipe goes left, produced goes right.
    fn order_by_end(
        &self,
        end: PipeEnd,
        produced: Node<C>,
        pipe: PipeWork<C>,
    ) -> (Node<C>, Node<C>) {
        let pipe_node = Node::Work(Box::new(Work::Pipe(Box::new(pipe))));
        match end {
            PipeEnd::Front => (produced, pipe_node),
            PipeEnd::Back => (pipe_node, produced),
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
        match end {
            PipeEnd::Front => {
                pipe.left = None;
                pipe.right = if right_iso.is_some() {
                    None
                } else {
                    right_suffix.clone()
                };
                let source_node = Node::Work(Box::new(Work::AndGroup(group)));
                let outer_suffix = if right_iso.is_some() {
                    right_suffix
                } else {
                    None
                };

                // Front advancement with remaining mid: use BindWork so each
                // source NF becomes a specific left boundary for the remaining pipe.
                if !mid_empty {
                    let bind = BindWork::new(
                        source_node,
                        pipe.mid,
                        pipe.right,
                        pipe.env,
                        pipe.tables,
                        pipe.call_mode,
                    );
                    let inner = Node::Work(Box::new(Work::Bind(bind)));
                    return wrap_node_with_prefix_suffix(inner, left_prefix, outer_suffix, terms);
                }

                let right_node = Node::Work(Box::new(Work::Pipe(Box::new(pipe))));
                let core = ComposeWork::new(source_node, right_node);
                wrap_compose_with_prefix_suffix(core, left_prefix, outer_suffix, terms)
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
                let core = ComposeWork::new(left_node, right_node);
                wrap_compose_with_prefix_suffix(core, outer_prefix, right_suffix, terms)
            }
        }
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

        // Front advancement with remaining mid: use BindWork so each source
        // NF becomes a specific left boundary for the remaining pipe.
        if matches!(end, PipeEnd::Front) && !pipe.mid.is_empty() {
            let bind = BindWork::new(
                fix_node,
                pipe.mid,
                pipe.right,
                pipe.env,
                pipe.tables,
                pipe.call_mode,
            );
            return WorkStep::More(Box::new(Work::Bind(bind)));
        }

        let (left_node, right_node) = self.order_by_end(end, fix_node, pipe);
        let compose = ComposeWork::new(left_node, right_node);
        WorkStep::More(Box::new(Work::Compose(compose)))
    }

    /// Try to batch-advance Calls at either end whose body is a single Atom
    /// or a flat Or of Atoms (with root functor dispatch).
    ///
    /// When a Call resolves to `Rel::Atom(nf)`, compose the NF directly into
    /// the boundary. When a Call resolves to a flat Or of Atoms and we have a
    /// boundary NF, filter the Or branches by root functor compatibility,
    /// eliminating branches that cannot possibly match.
    ///
    /// Returns Ok(true) if progress was made, Ok(false) if no simple Calls
    /// were found, or Err(WorkStep::Done) if composition failed.
    fn try_batch_advance_calls(&mut self, terms: &mut TermStore) -> Result<bool, WorkStep<C>> {
        // Chain fusion: detect consecutive simple wrapper Calls at the front
        // and fuse them into a single NF in O(n) instead of O(n^2) individual composes.
        if let Some(chain_result) = self.try_fuse_wrapper_chain(terms) {
            return chain_result;
        }

        let mut made_progress = false;
        loop {
            let mut advanced = false;
            for &end in &[PipeEnd::Front, PipeEnd::Back] {
                match self.try_advance_call_at_end(end, terms) {
                    Ok(true) => {
                        made_progress = true;
                        advanced = true;
                        break; // restart loop to try front again
                    }
                    Ok(false) => {} // try next end
                    Err(step) => return Err(step),
                }
            }
            if !advanced {
                break;
            }
        }
        Ok(made_progress)
    }

    /// Detect and fuse a chain of consecutive simple wrapper Calls at the front.
    ///
    /// A simple wrapper NF has the form `$x -> (f $x)`. When multiple such Calls
    /// appear consecutively, we can build the nested term bottom-up in O(n)
    /// instead of doing n individual compose_nf calls (each O(depth)).
    ///
    /// Returns `Some(result)` if a chain of 2+ wrappers was found and fused,
    /// `None` if no chain was found (caller should proceed with normal logic).
    fn try_fuse_wrapper_chain(
        &mut self,
        terms: &mut TermStore,
    ) -> Option<Result<bool, WorkStep<C>>> {
        // Scan consecutive Calls from the front that resolve to simple wrappers
        let mut wrapper_funcs: Vec<FuncId> = Vec::new();
        for rel in self.mid.iter() {
            let Rel::Call(id) = rel else {
                break;
            };
            let Some(binding) = self.env.lookup(*id) else {
                break;
            };
            let Rel::Atom(nf) = binding.body.as_ref() else {
                break;
            };
            let Some(func) = simple_wrapper_func(nf.as_ref(), terms) else {
                break;
            };
            wrapper_funcs.push(func);
        }

        // Need at least 2 wrappers to benefit from fusion
        if wrapper_funcs.len() < 2 {
            return None;
        }

        // Pop all the wrapper Calls from the front
        let count = wrapper_funcs.len();
        for _ in 0..count {
            self.pop_end(PipeEnd::Front);
        }

        // Build the fused NF and absorb it at the front boundary
        let chain_nf = build_wrapper_chain_nf::<C>(&wrapper_funcs, terms);
        if !self.absorb_at(PipeEnd::Front, chain_nf, terms) {
            return Some(Err(WorkStep::Done));
        }
        Some(Ok(true))
    }

    /// Try to advance a Call at the given end. Returns Ok(true) if progress
    /// was made, Ok(false) if no simple Call was found, or Err on failure.
    fn try_advance_call_at_end(
        &mut self,
        end: PipeEnd,
        terms: &mut TermStore,
    ) -> Result<bool, WorkStep<C>> {
        let rel = match end {
            PipeEnd::Front => self.mid.front(),
            PipeEnd::Back => self.mid.back(),
        };
        let Some(rel) = rel else {
            return Ok(false);
        };
        let Rel::Call(id) = rel.as_ref() else {
            return Ok(false);
        };
        let id = *id;
        let body = match self.env.lookup(id) {
            Some(binding) => binding.body.clone(),
            None => return Ok(false),
        };

        // Single Atom body: compose directly
        if let Rel::Atom(nf) = body.as_ref() {
            self.pop_end(end);
            if !self.absorb_at(end, nf.as_ref().clone(), terms) {
                return Err(WorkStep::Done);
            }
            return Ok(true);
        }

        // Flat Or of Atoms: dispatch by root functor
        if let Some(filtered) = self.try_dispatch_or_atoms(body, end, terms) {
            self.pop_end(end);
            match filtered {
                DispatchResult::Fail => return Err(WorkStep::Done),
                DispatchResult::Single(nf) => {
                    if !self.absorb_at(end, nf, terms) {
                        return Err(WorkStep::Done);
                    }
                }
                DispatchResult::Filtered(rel) => {
                    match end {
                        PipeEnd::Front => self.mid.push_front_rel(Arc::new(rel)),
                        PipeEnd::Back => self.mid.push_back_rel(Arc::new(rel)),
                    }
                    self.mid_normalized = false;
                }
            }
            return Ok(true);
        }

        Ok(false)
    }

    /// Build a dispatch table for a flat-Or-of-Atoms body.
    /// Pre-computes all 4 tags (match_root, build_root, match_child0, build_child0)
    /// for each atom so they don't need to be recomputed on every dispatch call.
    fn build_dispatch_table(
        atoms: Vec<Arc<NF<C>>>,
        terms: &mut TermStore,
    ) -> Arc<[DispatchEntry<C>]> {
        let entries: Vec<DispatchEntry<C>> = atoms
            .into_iter()
            .map(|atom| {
                let match_root = match_root_tag(&atom, terms);
                let build_root = build_root_tag(&atom, terms);
                let match_child0 = match_child0_tag(&atom, terms);
                let build_child0 = build_child0_tag(&atom, terms);
                DispatchEntry {
                    atom,
                    match_root,
                    build_root,
                    match_child0,
                    build_child0,
                }
            })
            .collect();
        Arc::from(entries)
    }

    /// Get or build the dispatch table for an Or body, using the cache.
    fn get_dispatch_table(
        &mut self,
        or_body: &Rel<C>,
        terms: &mut TermStore,
    ) -> Option<Arc<[DispatchEntry<C>]>> {
        let cache_key = or_body as *const Rel<C> as usize;

        if let Some(cache) = &self.dispatch_cache {
            if let Some(table) = cache.get(&cache_key) {
                return Some(table.clone());
            }
        }

        let atoms = collect_flat_or_atoms(or_body)?;
        if atoms.len() < 2 {
            return None;
        }

        let table = Self::build_dispatch_table(atoms, terms);
        let cache = self
            .dispatch_cache
            .get_or_insert_with(|| Box::new(DispatchCache::default()));
        cache.insert(cache_key, table.clone());
        Some(table)
    }

    /// Try to filter a flat-Or-of-Atoms relation body by root functor dispatch.
    ///
    /// Given a Call body that is a flat Or of Atoms (possibly wrapped in Fix),
    /// and a boundary NF, extract the boundary's root functor and filter
    /// the Or branches to only those with compatible root functors.
    ///
    /// Uses a cached dispatch table to avoid recomputing tags on every call.
    ///
    /// Returns `None` if dispatch is not applicable (body is not flat Or of Atoms,
    /// or no boundary to dispatch against).
    fn try_dispatch_or_atoms(
        &mut self,
        body: Arc<Rel<C>>,
        end: PipeEnd,
        terms: &mut TermStore,
    ) -> Option<DispatchResult<C>> {
        // Unwrap Fix wrapper if present, getting a reference to the Or body
        let or_body: &Rel<C> = match body.as_ref() {
            Rel::Or(_, _) => body.as_ref(),
            Rel::Fix(_, inner) => match inner.as_ref() {
                Rel::Or(_, _) => inner.as_ref(),
                _ => return None,
            },
            _ => return None,
        };

        // Get or build the cached dispatch table
        let table = self.get_dispatch_table(or_body, terms)?;

        // Get the boundary NF to dispatch against.
        // Front: left boundary's build output flows into the Call's match input.
        // Back: right boundary's match input comes from the Call's build output.
        let boundary = match end {
            PipeEnd::Front => self.left.as_ref()?,
            PipeEnd::Back => self.right.as_ref()?,
        };

        let boundary_tag = match end {
            PipeEnd::Front => build_root_tag(boundary, terms),
            PipeEnd::Back => match_root_tag(boundary, terms),
        };

        // Only dispatch when boundary has a definite functor
        let RootTag::Functor(_) = boundary_tag else {
            return None;
        };

        // Filter entries by compatible root functor using pre-computed tags
        let mut compatible: Vec<Arc<NF<C>>> = table
            .iter()
            .filter(|entry| {
                let (build_tag, match_tag) = match end {
                    PipeEnd::Front => (boundary_tag, entry.match_root),
                    PipeEnd::Back => (entry.build_root, boundary_tag),
                };
                tags_compatible(build_tag, match_tag)
            })
            .map(|entry| entry.atom.clone())
            .collect();

        // Depth-2 dispatch: if many atoms survive root-functor filtering,
        // apply a secondary filter on child[0]'s functor using pre-computed tags.
        const DEPTH2_THRESHOLD: usize = 8;
        if compatible.len() > DEPTH2_THRESHOLD {
            let boundary_child0_tag = match end {
                PipeEnd::Front => build_child0_tag(boundary, terms),
                PipeEnd::Back => match_child0_tag(boundary, terms),
            };
            if let RootTag::Functor(_) = boundary_child0_tag {
                // Re-filter using the cached table entries for child0 tags
                compatible = table
                    .iter()
                    .filter(|entry| {
                        // First check root compatibility (same as above)
                        let (build_tag, match_tag) = match end {
                            PipeEnd::Front => (boundary_tag, entry.match_root),
                            PipeEnd::Back => (entry.build_root, boundary_tag),
                        };
                        if !tags_compatible(build_tag, match_tag) {
                            return false;
                        }
                        // Then check child0 compatibility
                        let (build_c0, match_c0) = match end {
                            PipeEnd::Front => (boundary_child0_tag, entry.match_child0),
                            PipeEnd::Back => (entry.build_child0, boundary_child0_tag),
                        };
                        tags_compatible(build_c0, match_c0)
                    })
                    .map(|entry| entry.atom.clone())
                    .collect();
            }
        }

        if compatible.is_empty() {
            Some(DispatchResult::Fail)
        } else if compatible.len() == 1 {
            Some(DispatchResult::Single(
                compatible.into_iter().next().unwrap().as_ref().clone(),
            ))
        } else {
            Some(DispatchResult::Filtered(atoms_to_or_rel(&compatible)))
        }
    }

    fn advance_call(&mut self, end: PipeEnd, id: RelId, terms: &mut TermStore) -> WorkStep<C> {
        self.pop_end(end);
        self.handle_call(id, end, terms)
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
            Rel::Call(id) => self.advance_call(end, *id, terms),
            // Atom/Zero/Seq should have been normalized in try_normalize_step
            _ => WorkStep::Done,
        }
    }

    #[cfg(test)]
    pub(crate) fn advance_front(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        self.advance_end(PipeEnd::Front, terms)
    }

    /// Check if the replay_key subsumes our call key (strictly more general:
    /// same relation/binding, fewer boundaries). Returns the replay_key clone
    /// if subsumption applies, so the caller can use it as the call key.
    ///
    /// Only generalizes the OUTPUT-side boundary to avoid compose explosion:
    /// - Front-advancing: right boundary is output (safe to relax)
    /// - Back-advancing: left boundary is output (safe to relax)
    ///
    /// Input-side boundaries help prune during production, so relaxing them
    /// causes the general table to produce many irrelevant answers.
    #[cold]
    fn try_generalize_key(
        key: &Arc<CallKey<C>>,
        replay_key: &Arc<CallKey<C>>,
        end: PipeEnd,
    ) -> Option<Arc<CallKey<C>>> {
        if replay_key.bind_id != key.bind_id {
            return None;
        }
        let right_relaxed = replay_key.right.is_none() && key.right.is_some();
        let left_relaxed = replay_key.left.is_none() && key.left.is_some();
        // Only relax the output-side boundary.
        let output_relaxed = match end {
            PipeEnd::Front => right_relaxed && !left_relaxed,
            PipeEnd::Back => left_relaxed && !right_relaxed,
        };
        if !output_relaxed {
            return None;
        }
        let left_compat = left_relaxed || replay_key.left == key.left;
        let right_compat = right_relaxed || replay_key.right == key.right;
        if !(left_compat && right_compat) {
            return None;
        }
        Some(replay_key.clone())
    }

    /// Handle a Call by looking up in the environment and using tabling.
    fn handle_call(&mut self, id: RelId, end: PipeEnd, terms: &mut TermStore) -> WorkStep<C> {
        let Some(binding) = self.env.lookup(id) else {
            return WorkStep::Done;
        };
        // The near-side boundary always participates; the far side only when mid is empty.
        let use_left = matches!(end, PipeEnd::Front) || self.mid.is_empty();
        let use_right = matches!(end, PipeEnd::Back) || self.mid.is_empty();

        let call_left = if use_left { self.left.clone() } else { None };
        let mut call_right = if use_right { self.right.clone() } else { None };

        // Peek at the adjacent mid element in the far direction for an Atom
        // when advancing the front Call. The Call's output flows into the
        // next element, so an adjacent Atom is a sound constraint on output.
        // This doesn't consume the Atom -- it remains in mid for normal
        // normalization when the Call's output flows back into the pipe.
        if call_right.is_none() && matches!(end, PipeEnd::Front) {
            if let Some(Rel::Atom(nf)) = self.mid.front().map(|r| r.as_ref()) {
                call_right = Some(nf_domain_filter(nf.as_ref()));
            }
        }

        let mut key = Arc::new(CallKey::new(
            id,
            binding.id,
            call_left.clone(),
            call_right.clone(),
        ));
        if let CallMode::ReplayOnly(replay_key, watermark) = &self.call_mode {
            // Subsumption: if the replay_key is strictly more general (fewer
            // boundaries) for the same relation, use it as our key. The pipe's
            // own boundaries will filter answers, so this is sound. This avoids
            // creating redundant inner tables entirely.
            // Guard: only attempt generalization when rel IDs match (cheap int
            // comparison) but keys differ. For mutual recursion (even/odd),
            // rel IDs differ, so the cold function is never called.
            if replay_key.as_ref() != key.as_ref() && replay_key.rel == key.rel {
                if let Some(generalized) = Self::try_generalize_key(&key, replay_key, end) {
                    key = generalized;
                }
            }
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

                let absorb_front = matches!(end, PipeEnd::Front);
                if absorb_front && !pipe.mid.is_empty() {
                    let bind = BindWork::new(
                        replay_node,
                        pipe.mid,
                        pipe.right,
                        pipe.env,
                        pipe.tables,
                        pipe.call_mode,
                    );
                    return WorkStep::More(Box::new(Work::Bind(bind)));
                }

                let (left_node, right_node) = self.order_by_end(end, replay_node, pipe);
                let compose = ComposeWork::new_preseed(left_node, right_node, terms);
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

        // Front advancement with remaining mid: use BindWork so each source
        // NF becomes a specific left boundary for the remaining pipe. This
        // prevents downstream Calls from running with unconstrained input.
        let absorb_front = matches!(end, PipeEnd::Front);
        if absorb_front && !pipe.mid.is_empty() {
            let bind = BindWork::new(
                gen_node,
                pipe.mid,
                pipe.right,
                pipe.env,
                pipe.tables,
                pipe.call_mode,
            );
            return WorkStep::More(Box::new(Work::Bind(bind)));
        }

        let (left_node, right_node) = self.order_by_end(end, gen_node, pipe);
        let compose = ComposeWork::new_preseed(left_node, right_node, terms);
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
            dispatch_cache: None,
        }
    }
}
