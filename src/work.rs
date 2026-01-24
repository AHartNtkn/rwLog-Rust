//! Work - Active work items for the evaluation engine.
//!
//! Work represents computations in progress. PipeWork handles
//! sequential composition (Seq) with outside-in boundary fusion.

use crate::constraint::ConstraintOps;
use crate::drop_fresh::DropFresh;
use crate::factors::Factors;
use crate::join::{AndJoiner, JoinStep};
use crate::kernel::{compose_nf, meet_nf};
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::queue::{
    AnswerQueue, AnswerReceiver, AnswerSender, BlockedOn, QueueWaker, RecvResult, SinkResult,
    WakeHub,
};
use crate::rel::{Rel, RelId};
use crate::term::{TermId, TermStore};
use dashmap::DashMap;
use parking_lot::Mutex;
use smallvec::SmallVec;
use std::collections::{HashSet, VecDeque};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// Active work items for evaluation.
#[derive(Clone, Debug)]
pub enum Work<C: ConstraintOps> {
    /// Sequential composition pipeline.
    Pipe(PipeWork<C>),
    /// Conjunction/intersection via fair diagonal join.
    Meet(MeetWork<C>),
    /// N-ary conjunction/intersection via fair diagonal join.
    AndGroup(AndGroup<C>),
    /// Tabled recursive call.
    Fix(FixWork<C>),
    /// Symmetric compose join for sequential composition.
    Compose(ComposeWork<C>),
    /// Receiver for joiner outputs (drives AndGroup producers).
    JoinReceiver(JoinReceiverWork<C>),
    /// Single atomic NF (emits once, then done).
    Atom(NF<C>),
    /// Completed - no more work.
    Done,
}

/// Result of stepping a work item.
#[derive(Clone, Debug)]
pub enum WorkStep<C: ConstraintOps> {
    /// Work exhausted, no answers.
    Done,
    /// Emit an answer, continue with more work.
    Emit(NF<C>, Box<Work<C>>),
    /// Fork into two search branches.
    Split(Box<Node<C>>, Box<Node<C>>),
    /// Continue with modified work.
    More(Box<Work<C>>),
}

/// Call handling mode for PipeWork.
#[derive(Clone, Debug)]
pub enum CallMode<C: ConstraintOps> {
    /// Normal call handling (tabling + producer).
    Normal,
    /// Replay-only for a specific CallKey (used during producer iterations).
    ReplayOnly(Box<CallKey<C>>),
}

fn collect_and_parts<C: ConstraintOps>(rel: Arc<Rel<C>>, out: &mut Vec<Arc<Rel<C>>>) {
    match rel.as_ref() {
        Rel::And(a, b) => {
            collect_and_parts(a.clone(), out);
            collect_and_parts(b.clone(), out);
        }
        _ => out.push(rel),
    }
}

fn flatten_and_parts<C: ConstraintOps>(rel: Arc<Rel<C>>) -> Vec<Arc<Rel<C>>> {
    let mut parts = Vec::new();
    collect_and_parts(rel, &mut parts);
    parts
}

fn wrap_rel_with_atoms<C: ConstraintOps>(
    rel: Arc<Rel<C>>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
) -> Rel<C> {
    if prefix.is_none() && suffix.is_none() {
        return rel.as_ref().clone();
    }

    let mut factors: Vec<Arc<Rel<C>>> = Vec::new();
    if let Some(nf) = prefix {
        factors.push(Arc::new(Rel::Atom(Arc::new(nf))));
    }
    factors.push(rel);
    if let Some(nf) = suffix {
        factors.push(Arc::new(Rel::Atom(Arc::new(nf))));
    }

    Rel::Seq(Arc::from(factors))
}

/// Convert a Rel to a Node tree with the given environment and tables.
pub fn rel_to_node<C: ConstraintOps>(rel: &Rel<C>, env: &Env<C>, tables: &Tables<C>) -> Node<C> {
    match rel {
        Rel::Zero => Node::Fail,

        Rel::Atom(nf) => Node::Emit(nf.as_ref().clone(), Box::new(Node::Fail)),

        Rel::Or(a, b) => Node::Or(
            Box::new(rel_to_node(a, env, tables)),
            Box::new(rel_to_node(b, env, tables)),
        ),

        Rel::And(a, b) => {
            let mut parts = Vec::new();
            collect_and_parts(a.clone(), &mut parts);
            collect_and_parts(b.clone(), &mut parts);
            if parts.is_empty() {
                return Node::Fail;
            }
            if parts.len() == 1 {
                return rel_to_node(parts[0].as_ref(), env, tables);
            }
            let nodes = parts
                .into_iter()
                .map(|part| rel_to_node(part.as_ref(), env, tables))
                .collect();
            Node::Work(boxed_work(Work::AndGroup(AndGroup::new(nodes))))
        }

        Rel::Seq(factors) => {
            let factors_rope = Factors::from_seq(factors.clone());
            let mut pipe = PipeWork::with_mid(factors_rope);
            pipe.env = env.clone();
            pipe.tables = tables.clone();
            Node::Work(boxed_work(Work::Pipe(pipe)))
        }

        Rel::Fix(id, body) => {
            let new_env = env.bind(*id, body.clone());
            rel_to_node(body, &new_env, tables)
        }

        Rel::Call(id) => match env.lookup(*id) {
            Some(_) => {
                let call_rel = Arc::new(rel.clone());
                let factors = Factors::from_seq(Arc::from(vec![call_rel]));
                let mut pipe = PipeWork::with_mid(factors);
                pipe.env = env.clone();
                pipe.tables = tables.clone();
                Node::Work(boxed_work(Work::Pipe(pipe)))
            }
            None => Node::Fail,
        },
    }
}

fn node_from_answers<C: ConstraintOps>(answers: &[NF<C>]) -> Node<C> {
    let mut node = Node::Fail;
    for nf in answers.iter().rev() {
        node = Node::Emit(nf.clone(), Box::new(node));
    }
    node
}

fn boxed_work<C: ConstraintOps>(work: Work<C>) -> Box<Work<C>> {
    Box::new(work)
}

fn boxed_node<C: ConstraintOps>(node: Node<C>) -> Box<Node<C>> {
    Box::new(node)
}

fn wrap_compose_with_prefix_suffix<C: ConstraintOps>(
    core: ComposeWork<C>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
) -> WorkStep<C> {
    let mut node = Node::Work(boxed_work(Work::Compose(core)));

    if let Some(prefix_nf) = prefix {
        let prefix_node = Node::Emit(prefix_nf, Box::new(Node::Fail));
        node = Node::Work(boxed_work(Work::Compose(ComposeWork::new(
            prefix_node, node,
        ))));
    }

    if let Some(suffix_nf) = suffix {
        let suffix_node = Node::Emit(suffix_nf, Box::new(Node::Fail));
        node = Node::Work(boxed_work(Work::Compose(ComposeWork::new(
            node, suffix_node,
        ))));
    }

    match node {
        Node::Work(work) => WorkStep::More(work),
        _ => WorkStep::Done,
    }
}

fn build_var_list(arity: u32, terms: &mut TermStore) -> SmallVec<[TermId; 1]> {
    let mut vars = SmallVec::new();
    for idx in 0..arity {
        vars.push(terms.var(idx));
    }
    vars
}

fn nf_rwl_iso<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let in_arity = nf.drop_fresh.in_arity;
    NF::new(
        nf.match_pats.clone(),
        DropFresh::identity(in_arity),
        build_var_list(in_arity, terms),
    )
}

fn nf_rwr_iso<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let out_arity = nf.drop_fresh.out_arity;
    NF::new(
        build_var_list(out_arity, terms),
        DropFresh::identity(out_arity),
        nf.build_pats.clone(),
    )
}

fn nf_left_prefix<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let out_arity = nf.drop_fresh.out_arity;
    NF::new(
        nf.match_pats.clone(),
        nf.drop_fresh.clone(),
        build_var_list(out_arity, terms),
    )
}

fn nf_right_suffix<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let in_arity = nf.drop_fresh.in_arity;
    NF::new(
        build_var_list(in_arity, terms),
        nf.drop_fresh.clone(),
        nf.build_pats.clone(),
    )
}

/// Pipeline work: sequential composition with boundary fusion.
///
/// Represents: left ; mid[0] ; mid[1] ; ... ; mid[n-1] ; right
///
/// Normalization absorbs Atoms at boundaries via compose_nf.
/// Or nodes in mid cause splits. Zero in mid annihilates.
///
/// Outside-in evaluation: alternates processing front/back to propagate
/// constraints before expanding recursion.
#[derive(Clone, Debug)]
pub struct PipeWork<C: ConstraintOps> {
    /// Left boundary (fused from front).
    pub left: Option<NF<C>>,
    /// Middle factors (remaining Rel elements).
    pub mid: Factors<C>,
    /// Right boundary (fused from back).
    pub right: Option<NF<C>>,
    /// Flip bit: alternates which end to process for outside-in evaluation.
    pub flip: bool,
    /// Environment for Fix bindings (RelId -> Rel body).
    pub env: Env<C>,
    /// Tables for call-context tabling.
    pub tables: Tables<C>,
    /// Call handling mode.
    pub call_mode: CallMode<C>,
}

struct PipeWorkBuilder<C: ConstraintOps> {
    left: Option<NF<C>>,
    mid: Factors<C>,
    right: Option<NF<C>>,
    flip: bool,
    env: Env<C>,
    tables: Tables<C>,
    call_mode: CallMode<C>,
}

impl<C: ConstraintOps> PipeWorkBuilder<C> {
    fn new() -> Self {
        Self {
            left: None,
            mid: Factors::new(),
            right: None,
            flip: false,
            env: Env::new(),
            tables: Tables::new(),
            call_mode: CallMode::Normal,
        }
    }

    fn left(mut self, left: Option<NF<C>>) -> Self {
        self.left = left;
        self
    }

    fn mid(mut self, mid: Factors<C>) -> Self {
        self.mid = mid;
        self
    }

    fn right(mut self, right: Option<NF<C>>) -> Self {
        self.right = right;
        self
    }

    fn env(mut self, env: Env<C>) -> Self {
        self.env = env;
        self
    }

    fn tables(mut self, tables: Tables<C>) -> Self {
        self.tables = tables;
        self
    }

    fn build(self) -> PipeWork<C> {
        PipeWork {
            left: self.left,
            mid: self.mid,
            right: self.right,
            flip: self.flip,
            env: self.env,
            tables: self.tables,
            call_mode: self.call_mode,
        }
    }
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
                WorkStep::Emit(nf, boxed_work(Work::Done))
            }
            Work::Done => WorkStep::Done,
        }
    }
}

impl<C: ConstraintOps> PipeWork<C> {
    fn builder() -> PipeWorkBuilder<C> {
        PipeWorkBuilder::new()
    }

    /// Create an empty pipe (represents identity and emits it).
    pub fn new() -> Self {
        Self::builder().build()
    }

    /// Create a pipe with only mid factors.
    pub fn with_mid(mid: Factors<C>) -> Self {
        Self::builder().mid(mid).build()
    }

    /// Create a pipe with boundaries and mid.
    pub fn with_boundaries(left: Option<NF<C>>, mid: Factors<C>, right: Option<NF<C>>) -> Self {
        Self::builder().left(left).mid(mid).right(right).build()
    }

    /// Create a pipe with full state including env and tables.
    pub fn with_env_and_tables(
        left: Option<NF<C>>,
        mid: Factors<C>,
        right: Option<NF<C>>,
        env: Env<C>,
        tables: Tables<C>,
    ) -> Self {
        Self::builder()
            .left(left)
            .mid(mid)
            .right(right)
            .env(env)
            .tables(tables)
            .build()
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
        Self::builder().mid(mid).env(env).tables(tables).build()
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

        Self::builder().mid(mid).env(env).tables(tables).build()
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

            break;
        }

        // Phase B: Stuck on normalization - advance one end using flip.
        // Prefer advancing a non-Call end when the opposite end is a Call.
        let front_is_call = matches!(self.mid.front().map(|rel| rel.as_ref()), Some(Rel::Call(_)));
        let back_is_call = matches!(self.mid.back().map(|rel| rel.as_ref()), Some(Rel::Call(_)));

        let mut advance_back = self.flip;
        if advance_back && back_is_call && !front_is_call {
            advance_back = false;
        } else if !advance_back && front_is_call && !back_is_call {
            advance_back = true;
        }

        let result = if advance_back {
            self.advance_back(terms)
        } else {
            self.advance_front(terms)
        };
        self.flip = !self.flip; // Toggle for next step
        result
    }

    /// Emit the composed boundaries when mid is empty.
    fn emit_boundaries(&self, terms: &mut TermStore) -> WorkStep<C> {
        match (&self.left, &self.right) {
            (None, None) => {
                // Empty pipe - emit identity
                WorkStep::Emit(NF::identity(C::default()), boxed_work(Work::Done))
            }
            (Some(left), None) => {
                // Only left boundary
                WorkStep::Emit(left.clone(), boxed_work(Work::Done))
            }
            (None, Some(right)) => {
                // Only right boundary
                WorkStep::Emit(right.clone(), boxed_work(Work::Done))
            }
            (Some(left), Some(right)) => {
                // Compose left and right
                match compose_nf(left, right, terms) {
                    Some(composed) => WorkStep::Emit(composed, boxed_work(Work::Done)),
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

    /// Split on an Or node at the front.
    fn split_or_front(&self, a: Arc<Rel<C>>, b: Arc<Rel<C>>) -> WorkStep<C> {
        // Create two pipes - one with branch a, one with branch b.
        // Both keep the same boundaries, env, tables, and remaining mid.

        // Left pipe: a followed by remaining mid
        let mut left_pipe = self.clone();
        left_pipe.mid.push_front_rel(a);

        // Right pipe: b followed by remaining mid
        let mut right_pipe = self.clone();
        right_pipe.mid.push_front_rel(b);

        WorkStep::Split(
            boxed_node(Node::Work(boxed_work(Work::Pipe(left_pipe)))),
            boxed_node(Node::Work(boxed_work(Work::Pipe(right_pipe)))),
        )
    }

    /// Split on an Or node at the back.
    fn split_or_back(&self, a: Arc<Rel<C>>, b: Arc<Rel<C>>) -> WorkStep<C> {
        // Create two pipes - one with branch a, one with branch b.
        // Both keep the same boundaries, env, tables, and remaining mid.

        // Left pipe: remaining mid followed by a
        let mut left_pipe = self.clone();
        left_pipe.mid.push_back_rel(a);

        // Right pipe: remaining mid followed by b
        let mut right_pipe = self.clone();
        right_pipe.mid.push_back_rel(b);

        WorkStep::Split(
            boxed_node(Node::Work(boxed_work(Work::Pipe(left_pipe)))),
            boxed_node(Node::Work(boxed_work(Work::Pipe(right_pipe)))),
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
        if self.mid.is_empty() {
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
        for idx in 0..factors.len() {
            let rel = factors[idx].clone();
            let Rel::And(_, _) = rel.as_ref() else {
                continue;
            };
            let parts = flatten_and_parts(rel);
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
                    factors[idx] = Arc::new(Rel::Atom(Arc::new(nf)));
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
        }

        Ok(changed)
    }

    /// Advance the front factor when stuck on normalization.
    fn advance_front(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let Some(front) = self.mid.front().cloned() else {
            return self.emit_boundaries(terms);
        };

        match front.as_ref() {
            Rel::Or(a, b) => {
                self.mid.pop_front();
                self.split_or_front(a.clone(), b.clone())
            }
            Rel::And(_, _) => {
                self.mid.pop_front();
                let parts = flatten_and_parts(front.clone());

                let (left_prefix, left_iso) = match &self.left {
                    Some(nf) => (Some(nf_left_prefix(nf, terms)), Some(nf_rwr_iso(nf, terms))),
                    None => (None, None),
                };

                let (right_suffix, right_iso) = if self.mid.is_empty() {
                    match &self.right {
                        Some(nf) => (
                            Some(nf_right_suffix(nf, terms)),
                            Some(nf_rwl_iso(nf, terms)),
                        ),
                        None => (None, None),
                    }
                } else {
                    (self.right.clone(), None)
                };

                let nodes = parts
                    .into_iter()
                    .map(|part| {
                        let wrapped =
                            wrap_rel_with_atoms(part, left_iso.clone(), right_iso.clone());
                        let mut part_pipe =
                            PipeWork::from_rel(wrapped, self.env.clone(), self.tables.clone());
                        part_pipe.call_mode = self.call_mode.clone();
                        Node::Work(boxed_work(Work::Pipe(part_pipe)))
                    })
                    .collect();
                let group = AndGroup::new(nodes);
                let left_node = Node::Work(boxed_work(Work::AndGroup(group)));

                let mut pipe = self.clone();
                pipe.left = None;
                pipe.right = if right_iso.is_some() { None } else { right_suffix.clone() };
                let right_node = Node::Work(boxed_work(Work::Pipe(pipe)));

                let core = ComposeWork::new(left_node, right_node);
                let outer_suffix = if right_iso.is_some() { right_suffix } else { None };
                wrap_compose_with_prefix_suffix(core, left_prefix, outer_suffix)
            }
            Rel::Fix(id, body) => {
                self.mid.pop_front();
                let use_left = true;
                let use_right = self.mid.is_empty();
                let call_left = if use_left { self.left.clone() } else { None };
                let call_right = if use_right { self.right.clone() } else { None };
                let bound_env = self.env.bind(*id, body.clone());

                let mut fix_pipe = PipeWork::from_rel_with_boundaries(
                    body.as_ref().clone(),
                    call_left,
                    call_right,
                    bound_env,
                    self.tables.clone(),
                );
                fix_pipe.call_mode = self.call_mode.clone();

                let fix_node = Node::Work(boxed_work(Work::Pipe(fix_pipe)));
                let mut pipe = self.clone();
                if use_left {
                    pipe.left = None;
                }
                if use_right {
                    pipe.right = None;
                }
                let left_node = fix_node;
                let right_node = Node::Work(boxed_work(Work::Pipe(pipe)));
                let compose = ComposeWork::new(left_node, right_node);
                WorkStep::More(boxed_work(Work::Compose(compose)))
            }
            Rel::Call(id) => {
                self.mid.pop_front();
                self.handle_call(*id, true)
            }
            // Atom/Zero/Seq should have been normalized in try_normalize_step
            _ => WorkStep::Done,
        }
    }

    /// Advance the back factor when stuck on normalization.
    fn advance_back(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let Some(back) = self.mid.back().cloned() else {
            return self.emit_boundaries(terms);
        };

        match back.as_ref() {
            Rel::Or(a, b) => {
                self.mid.pop_back();
                self.split_or_back(a.clone(), b.clone())
            }
            Rel::And(_, _) => {
                self.mid.pop_back();
                let parts = flatten_and_parts(back.clone());

                let (right_suffix, right_iso) = match &self.right {
                    Some(nf) => (
                        Some(nf_right_suffix(nf, terms)),
                        Some(nf_rwl_iso(nf, terms)),
                    ),
                    None => (None, None),
                };

                let (left_prefix, left_iso) = if self.mid.is_empty() {
                    match &self.left {
                        Some(nf) => (Some(nf_left_prefix(nf, terms)), Some(nf_rwr_iso(nf, terms))),
                        None => (None, None),
                    }
                } else {
                    (self.left.clone(), None)
                };

                let nodes = parts
                    .into_iter()
                    .map(|part| {
                        let wrapped =
                            wrap_rel_with_atoms(part, left_iso.clone(), right_iso.clone());
                        let mut part_pipe =
                            PipeWork::from_rel(wrapped, self.env.clone(), self.tables.clone());
                        part_pipe.call_mode = self.call_mode.clone();
                        Node::Work(boxed_work(Work::Pipe(part_pipe)))
                    })
                    .collect();
                let group = AndGroup::new(nodes);
                let right_node = Node::Work(boxed_work(Work::AndGroup(group)));

                let mut pipe = self.clone();
                pipe.right = None;
                pipe.left = if left_iso.is_some() { None } else { left_prefix.clone() };
                let left_node = Node::Work(boxed_work(Work::Pipe(pipe)));

                let core = ComposeWork::new(left_node, right_node);
                let outer_prefix = if left_iso.is_some() { left_prefix } else { None };
                wrap_compose_with_prefix_suffix(core, outer_prefix, right_suffix)
            }
            Rel::Fix(id, body) => {
                self.mid.pop_back();
                let use_left = self.mid.is_empty();
                let use_right = true;
                let call_left = if use_left { self.left.clone() } else { None };
                let call_right = if use_right { self.right.clone() } else { None };
                let bound_env = self.env.bind(*id, body.clone());

                let mut fix_pipe = PipeWork::from_rel_with_boundaries(
                    body.as_ref().clone(),
                    call_left,
                    call_right,
                    bound_env,
                    self.tables.clone(),
                );
                fix_pipe.call_mode = self.call_mode.clone();

                let fix_node = Node::Work(boxed_work(Work::Pipe(fix_pipe)));
                let mut pipe = self.clone();
                if use_left {
                    pipe.left = None;
                }
                if use_right {
                    pipe.right = None;
                }
                let left_node = Node::Work(boxed_work(Work::Pipe(pipe)));
                let right_node = fix_node;
                let compose = ComposeWork::new(left_node, right_node);
                WorkStep::More(boxed_work(Work::Compose(compose)))
            }
            Rel::Call(id) => {
                self.mid.pop_back();
                self.handle_call(*id, false)
            }
            // Atom/Zero/Seq should have been normalized in try_normalize_step
            _ => WorkStep::Done,
        }
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
        let call_right = if use_right { self.right.clone() } else { None };

        let key = CallKey::new(id, binding.id, call_left.clone(), call_right.clone());
        if let CallMode::ReplayOnly(replay_key) = &self.call_mode {
            if replay_key.as_ref() == &key {
                let table = match self.tables.lookup(&key) {
                    Some(table) => table,
                    None => return WorkStep::Done,
                };
                let snapshot = table.all_answers();
                let replay_node = node_from_answers(&snapshot);
                let mut pipe = self.clone();
                if use_left {
                    pipe.left = None;
                }
                if use_right {
                    pipe.right = None;
                }
                let (left_node, right_node) = if absorb_front {
                    (replay_node, Node::Work(boxed_work(Work::Pipe(pipe))))
                } else {
                    (Node::Work(boxed_work(Work::Pipe(pipe))), replay_node)
                };
                let compose = ComposeWork::new(left_node, right_node);
                return WorkStep::More(boxed_work(Work::Compose(compose)));
            }
        }

        let table = self.tables.get_or_create(key.clone());
        let snapshot = {
            let mut producer = table.producer.lock();
            if producer.spec.is_none() {
                producer.spec = Some(ProducerSpec {
                    key: key.clone(),
                    body: binding.body.clone(),
                    left: call_left.clone(),
                    right: call_right.clone(),
                    env: self.env.clone(),
                });
            }
            drop(producer);
            table.answers.lock().answers.clone()
        };

        let replay_node = node_from_answers(&snapshot);
        let fix = FixWork::new(key, table, snapshot.len(), self.tables.clone());
        let fix_node = Node::Work(boxed_work(Work::Fix(fix)));

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
            (gen_node, Node::Work(boxed_work(Work::Pipe(pipe))))
        } else {
            (Node::Work(boxed_work(Work::Pipe(pipe))), gen_node)
        };
        let compose = ComposeWork::new(left_node, right_node);
        WorkStep::More(boxed_work(Work::Compose(compose)))
    }
}

impl<C: ConstraintOps> Default for PipeWork<C> {
    fn default() -> Self {
        Self {
            left: None,
            mid: Factors::new(),
            right: None,
            flip: false,
            env: Env::new(),
            tables: Tables::new(),
            call_mode: CallMode::Normal,
        }
    }
}

/// Compose work: symmetric join for sequential composition.
///
/// Represents: left ; right
///
/// Uses fair diagonal enumeration:
/// - Pull alternately from left/right nodes
/// - When a new answer arrives, compose with all seen from the other side
/// - Successful compositions are queued in pending
#[derive(Clone, Debug)]
enum ComposeCursor {
    Left {
        left_idx: usize,
        right_idx: usize,
        right_limit: usize,
    },
    Right {
        right_idx: usize,
        left_idx: usize,
        left_limit: usize,
    },
}

const COMPOSE_BATCH: usize = 1;

#[derive(Clone, Debug)]
pub struct ComposeWork<C: ConstraintOps> {
    /// Left search tree.
    pub left: Box<Node<C>>,
    /// Right search tree.
    pub right: Box<Node<C>>,
    /// Answers seen from left.
    pub seen_l: Vec<NF<C>>,
    /// Answers seen from right.
    pub seen_r: Vec<NF<C>>,
    /// Dedup set for left answers.
    seen_l_set: HashSet<NF<C>>,
    /// Dedup set for right answers.
    seen_r_set: HashSet<NF<C>>,
    /// Successful compositions waiting to be emitted.
    pub pending: VecDeque<NF<C>>,
    /// Dedup set for pending compositions.
    pending_set: HashSet<NF<C>>,
    /// Pending composition cursors.
    pair_queue: VecDeque<ComposeCursor>,
    /// If false, pull from left next; if true, pull from right.
    pub flip: bool,
}

impl<C: ConstraintOps> ComposeWork<C> {
    /// Create a new ComposeWork from two nodes.
    pub fn new(left: Node<C>, right: Node<C>) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            seen_l: Vec::new(),
            seen_r: Vec::new(),
            seen_l_set: HashSet::new(),
            seen_r_set: HashSet::new(),
            pending: VecDeque::new(),
            pending_set: HashSet::new(),
            pair_queue: VecDeque::new(),
            flip: false,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, ComposeWork::new(Node::Fail, Node::Fail))
    }

    fn push_pending(&mut self, nf: NF<C>) {
        if self.pending_set.insert(nf.clone()) {
            self.pending.push_back(nf);
        }
    }

    fn is_empty_identity(nf: &NF<C>) -> bool {
        nf.match_pats.is_empty()
            && nf.build_pats.is_empty()
            && nf.drop_fresh.in_arity == 0
            && nf.drop_fresh.out_arity == 0
    }

    fn compose_pair(
        left_nf: &NF<C>,
        right_nf: &NF<C>,
        terms: &mut TermStore,
    ) -> Option<NF<C>> {
        if Self::is_empty_identity(right_nf) {
            return Some(left_nf.clone());
        }
        if Self::is_empty_identity(left_nf) {
            return Some(right_nf.clone());
        }
        compose_nf(left_nf, right_nf, terms)
    }

    fn enqueue_pairs_left(&mut self, left_idx: usize) {
        let right_limit = self.seen_r.len();
        if right_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Left {
            left_idx,
            right_idx: 0,
            right_limit,
        });
    }

    fn enqueue_pairs_right(&mut self, right_idx: usize) {
        let left_limit = self.seen_l.len();
        if left_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Right {
            right_idx,
            left_idx: 0,
            left_limit,
        });
    }

    fn process_pair_queue(&mut self, terms: &mut TermStore) -> Option<NF<C>> {
        let Some(mut cursor) = self.pair_queue.pop_front() else {
            return None;
        };

        let mut steps = 0;
        loop {
            if steps >= COMPOSE_BATCH {
                break;
            }
            match &mut cursor {
                ComposeCursor::Left {
                    left_idx,
                    right_idx,
                    right_limit,
                } => {
                    if *right_idx >= *right_limit {
                        break;
                    }
                    let left_nf = &self.seen_l[*left_idx];
                    let right_nf = &self.seen_r[*right_idx];
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        self.push_pending(nf);
                    }
                    *right_idx += 1;
                }
                ComposeCursor::Right {
                    right_idx,
                    left_idx,
                    left_limit,
                } => {
                    if *left_idx >= *left_limit {
                        break;
                    }
                    let left_nf = &self.seen_l[*left_idx];
                    let right_nf = &self.seen_r[*right_idx];
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        self.push_pending(nf);
                    }
                    *left_idx += 1;
                }
            }
            steps += 1;
        }

        let cursor_done = match &cursor {
            ComposeCursor::Left {
                right_idx,
                right_limit,
                ..
            } => *right_idx >= *right_limit,
            ComposeCursor::Right {
                left_idx,
                left_limit,
                ..
            } => *left_idx >= *left_limit,
        };
        if !cursor_done {
            self.pair_queue.push_back(cursor);
        }

        if let Some(nf) = self.pending.pop_front() {
            self.pending_set.remove(&nf);
            return Some(nf);
        }

        None
    }

    /// Step this compose work, returning the next state.
    ///
    /// Step policy:
    /// 1. If pending non-empty: emit front
    /// 2. Alternate processing pair cursors and pulling new answers
    /// 3. Alternate pulling from left/right (flip)
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        if let Some(nf) = self.pending.pop_front() {
            self.pending_set.remove(&nf);
            return WorkStep::Emit(nf, boxed_work(Work::Compose(self.take_self())));
        }

        let left_exhausted = matches!(*self.left, Node::Fail);
        let right_exhausted = matches!(*self.right, Node::Fail);

        if let Some(nf) = self.process_pair_queue(terms) {
            return WorkStep::Emit(nf, boxed_work(Work::Compose(self.take_self())));
        }

        if left_exhausted && self.seen_l.is_empty() && self.pair_queue.is_empty() {
            return WorkStep::Done;
        }

        if right_exhausted && self.seen_r.is_empty() && self.pair_queue.is_empty() {
            return WorkStep::Done;
        }

        if left_exhausted && right_exhausted {
            if self.pair_queue.is_empty() {
                return WorkStep::Done;
            }
            return WorkStep::More(boxed_work(Work::Compose(self.take_self())));
        }

        let pull_from_right = if left_exhausted {
            true
        } else if right_exhausted {
            false
        } else {
            self.flip
        };

        if pull_from_right {
            self.pull_right(terms)
        } else {
            self.pull_left(terms)
        }
    }

    fn pull_left(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.left, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.left = rest;
                if self.seen_l_set.insert(nf.clone()) {
                    let idx = self.seen_l.len();
                    self.seen_l.push(nf.clone());
                    self.enqueue_pairs_left(idx);
                }
                self.flip = true;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, boxed_work(Work::Compose(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::Compose(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.left = rest;
                self.flip = true;
                WorkStep::More(boxed_work(Work::Compose(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.left = Node::Fail;
                self.flip = true;
                WorkStep::More(boxed_work(Work::Compose(self.take_self())))
            }
        }
    }

    fn pull_right(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.right, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.right = rest;
                if self.seen_r_set.insert(nf.clone()) {
                    let idx = self.seen_r.len();
                    self.seen_r.push(nf.clone());
                    self.enqueue_pairs_right(idx);
                }
                self.flip = false;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, boxed_work(Work::Compose(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::Compose(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.right = rest;
                self.flip = false;
                WorkStep::More(boxed_work(Work::Compose(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.right = Node::Fail;
                self.flip = false;
                WorkStep::More(boxed_work(Work::Compose(self.take_self())))
            }
        }
    }
}

/// Join receiver work: consume joiner outputs from a queue.
#[derive(Clone, Debug)]
pub struct JoinReceiverWork<C: ConstraintOps> {
    receiver: Arc<Mutex<AnswerReceiver<C>>>,
    blocked: Option<BlockedOn>,
}

impl<C: ConstraintOps> JoinReceiverWork<C> {
    pub fn new(receiver: AnswerReceiver<C>) -> Self {
        Self {
            receiver: Arc::new(Mutex::new(receiver)),
            blocked: None,
        }
    }

    pub fn blocked_on(&self) -> Option<BlockedOn> {
        self.blocked.clone()
    }

    pub fn step(&mut self, _terms: &mut TermStore) -> WorkStep<C> {
        let receiver = self.receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => {
                self.blocked = None;
                WorkStep::Emit(nf, boxed_work(Work::JoinReceiver(self.clone())))
            }
            RecvResult::Closed => WorkStep::Done,
            RecvResult::Empty => {
                self.blocked = Some(receiver.blocked_on());
                WorkStep::More(boxed_work(Work::JoinReceiver(self.clone())))
            }
        }
    }
}

/// AndGroup work: queue-backed join for n-ary conjunction/intersection.
///
/// Represents: And(r0, r1, ..., rn-1)
///
/// Each part runs as a producer that pushes answers into a bounded queue.
/// The joiner consumes those queues round-robin and emits meets into an output queue.
#[derive(Clone, Copy, Debug)]
pub struct AndGroupConfig {
    part_queue_capacity: usize,
    output_queue_capacity: usize,
}

impl Default for AndGroupConfig {
    fn default() -> Self {
        Self {
            part_queue_capacity: 1,
            output_queue_capacity: 1,
        }
    }
}

#[derive(Clone, Debug)]
struct AndProducer<C: ConstraintOps> {
    node: Node<C>,
    sender: Option<AnswerSender<C>>,
    pending: Option<NF<C>>,
    blocked: Option<BlockedOn>,
    done: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AndProducerStep {
    Progress,
    Blocked,
    Done,
}

impl<C: ConstraintOps> AndProducer<C> {
    fn new(node: Node<C>, sender: AnswerSender<C>) -> Self {
        Self {
            node,
            sender: Some(sender),
            pending: None,
            blocked: None,
            done: false,
        }
    }

    fn runnable(&self) -> bool {
        if self.done {
            return false;
        }
        self.blocked.as_ref().map_or(true, |b| b.is_stale())
    }

    fn close_sender(&mut self) {
        self.sender = None;
    }

    fn step(&mut self, terms: &mut TermStore) -> AndProducerStep {
        if self.done {
            return AndProducerStep::Done;
        }

        if let Some(blocked) = &self.blocked {
            if !blocked.is_stale() {
                return AndProducerStep::Blocked;
            }
        }

        if let Some(nf) = self.pending.take() {
            let Some(sender) = self.sender.as_ref() else {
                self.done = true;
                return AndProducerStep::Done;
            };
            match sender.try_send(nf.clone()) {
                SinkResult::Accepted => {
                    self.blocked = None;
                    return AndProducerStep::Progress;
                }
                SinkResult::Full => {
                    self.pending = Some(nf);
                    self.blocked = Some(sender.blocked_on());
                    return AndProducerStep::Blocked;
                }
                SinkResult::Closed => {
                    self.done = true;
                    self.close_sender();
                    return AndProducerStep::Done;
                }
            }
        }

        let current = std::mem::replace(&mut self.node, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                self.node = rest;
                let Some(sender) = self.sender.as_ref() else {
                    self.done = true;
                    return AndProducerStep::Done;
                };
                match sender.try_send(nf.clone()) {
                    SinkResult::Accepted => {
                        self.blocked = None;
                        AndProducerStep::Progress
                    }
                    SinkResult::Full => {
                        self.pending = Some(nf);
                        self.blocked = Some(sender.blocked_on());
                        AndProducerStep::Blocked
                    }
                    SinkResult::Closed => {
                        self.done = true;
                        self.close_sender();
                        AndProducerStep::Done
                    }
                }
            }
            NodeStep::Continue(rest) => {
                self.node = rest;
                if matches!(self.node, Node::Fail) {
                    self.done = true;
                    self.close_sender();
                    return AndProducerStep::Done;
                }
                self.blocked = None;
                AndProducerStep::Progress
            }
            NodeStep::Exhausted => {
                self.node = Node::Fail;
                self.done = true;
                self.close_sender();
                AndProducerStep::Done
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct AndGroup<C: ConstraintOps> {
    producers: Vec<AndProducer<C>>,
    joiner: Arc<Mutex<AndJoiner<C>>>,
    joiner_sink: AnswerSender<C>,
    joiner_blocked: Option<BlockedOn>,
    joiner_done: bool,
    output_receiver: Arc<Mutex<AnswerReceiver<C>>>,
    /// Round-robin turn index across producers + joiner.
    pub turn: usize,
}

impl<C: ConstraintOps> AndGroup<C> {
    /// Create a new AndGroup from part nodes.
    pub fn new(parts: Vec<Node<C>>) -> Self {
        Self::with_config(parts, AndGroupConfig::default())
    }

    pub fn with_config(parts: Vec<Node<C>>, config: AndGroupConfig) -> Self {
        let (hub, _rx) = WakeHub::new();
        let joiner_waker = hub.waker();
        let output_waker = hub.waker();

        let mut receivers = Vec::new();
        let mut producers = Vec::new();

        for part in parts {
            let (tx, rx) =
                AnswerQueue::bounded_with_waker(config.part_queue_capacity, joiner_waker.clone());
            receivers.push(rx);
            producers.push(AndProducer::new(part, tx));
        }

        let (out_tx, out_rx) =
            AnswerQueue::bounded_with_waker(config.output_queue_capacity, output_waker);

        let joiner = AndJoiner::from_state(
            receivers,
            vec![false; producers.len()],
            vec![Vec::new(); producers.len()],
            VecDeque::new(),
            0,
            joiner_waker,
        );

        Self {
            producers,
            joiner: Arc::new(Mutex::new(joiner)),
            joiner_sink: out_tx,
            joiner_blocked: None,
            joiner_done: false,
            output_receiver: Arc::new(Mutex::new(out_rx)),
            turn: 0,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, AndGroup::new(Vec::new()))
    }

    fn joiner_runnable(&self) -> bool {
        if self.joiner_done {
            return false;
        }
        self.joiner_blocked.as_ref().map_or(true, |b| b.is_stale())
    }

    fn poll_output(&mut self) -> Option<NF<C>> {
        let receiver = self.output_receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => Some(nf),
            RecvResult::Empty => None,
            RecvResult::Closed => {
                self.joiner_done = true;
                None
            }
        }
    }

    fn step_joiner(&mut self, terms: &mut TermStore) -> JoinStep {
        let mut joiner = self.joiner.lock();
        let mut sink = crate::queue::AnswerSink::Queue(self.joiner_sink.clone());
        match joiner.step(terms, &mut sink) {
            JoinStep::Progress => {
                self.joiner_blocked = None;
                JoinStep::Progress
            }
            JoinStep::Blocked(blocked) => {
                self.joiner_blocked = Some(blocked.clone());
                JoinStep::Blocked(blocked)
            }
            JoinStep::Done => {
                self.joiner_done = true;
                self.joiner_blocked = None;
                JoinStep::Done
            }
        }
    }

    /// Step this AndGroup, returning the next state.
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        if let Some(nf) = self.poll_output() {
            return WorkStep::Emit(nf, boxed_work(Work::AndGroup(self.take_self())));
        }

        if self.joiner_done {
            return WorkStep::Done;
        }

        let total = self.producers.len() + 1;
        if total == 0 {
            return WorkStep::Done;
        }

        for offset in 0..total {
            let idx = (self.turn + offset) % total;
            if idx == self.producers.len() {
                if !self.joiner_runnable() {
                    continue;
                }
                self.step_joiner(terms);
                self.turn = (idx + 1) % total;
                if let Some(nf) = self.poll_output() {
                    return WorkStep::Emit(nf, boxed_work(Work::AndGroup(self.take_self())));
                }
                return WorkStep::More(boxed_work(Work::AndGroup(self.take_self())));
            }

            if !self.producers[idx].runnable() {
                continue;
            }
            let _ = self.producers[idx].step(terms);
            self.turn = (idx + 1) % total;
            if let Some(nf) = self.poll_output() {
                return WorkStep::Emit(nf, boxed_work(Work::AndGroup(self.take_self())));
            }
            return WorkStep::More(boxed_work(Work::AndGroup(self.take_self())));
        }

        if self.joiner_done {
            WorkStep::Done
        } else {
            WorkStep::More(boxed_work(Work::AndGroup(self.take_self())))
        }
    }
}

/// Meet work: fair diagonal join for conjunction/intersection.
///
/// Represents: And(left_node, right_node)
///
/// Uses fair diagonal enumeration:
/// - Pull alternately from left and right nodes
/// - When a new answer arrives, meet with all seen from other side
/// - Successful meets are queued in pending
///
/// Step policy:
/// 1. If pending non-empty: emit front
/// 2. Alternate pulling from left/right (flip)
/// 3. When new answer arrives, meet with all seen from other side
/// 4. Push successful meets to pending
#[derive(Clone, Debug)]
pub struct MeetWork<C: ConstraintOps> {
    /// Left search tree (boxed to break recursive type cycle)
    pub left: Box<Node<C>>,
    /// Right search tree (boxed to break recursive type cycle)
    pub right: Box<Node<C>>,
    /// Answers seen from left (in insertion order)
    pub seen_l: Vec<NF<C>>,
    /// Answers seen from right (in insertion order)
    pub seen_r: Vec<NF<C>>,
    /// Dedup set for left answers
    seen_l_set: HashSet<NF<C>>,
    /// Dedup set for right answers
    seen_r_set: HashSet<NF<C>>,
    /// Successful meets waiting to be emitted
    pub pending: VecDeque<NF<C>>,
    /// If false, pull from left next; if true, pull from right
    pub flip: bool,
}

impl<C: ConstraintOps> MeetWork<C> {
    /// Create a new MeetWork from two nodes.
    pub fn new(left: Node<C>, right: Node<C>) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            seen_l: Vec::new(),
            seen_r: Vec::new(),
            seen_l_set: HashSet::new(),
            seen_r_set: HashSet::new(),
            pending: VecDeque::new(),
            flip: false,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, MeetWork::new(Node::Fail, Node::Fail))
    }

    /// Step this meet work, returning the next state.
    ///
    /// Step policy:
    /// 1. If pending non-empty: emit front
    /// 2. Alternate pulling from left/right (flip)
    /// 3. When new answer arrives, meet with all seen from other side
    /// 4. Push successful meets to pending
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        // Step 1: If pending has items, emit front
        if let Some(nf) = self.pending.pop_front() {
            return WorkStep::Emit(nf, boxed_work(Work::Meet(self.take_self())));
        }

        // Step 2: Check if both sides are exhausted
        let left_exhausted = matches!(*self.left, Node::Fail);
        let right_exhausted = matches!(*self.right, Node::Fail);

        if left_exhausted && right_exhausted {
            return WorkStep::Done;
        }

        // Step 3: Alternate pulling from left/right based on flip
        // If one side is exhausted, pull from the other
        let pull_from_right = if left_exhausted {
            true
        } else if right_exhausted {
            false
        } else {
            self.flip
        };

        if pull_from_right {
            self.pull_right(terms)
        } else {
            self.pull_left(terms)
        }
    }

    /// Pull from left node and meet with seen_r
    fn pull_left(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.left, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.left = rest;
                if self.seen_l_set.insert(nf.clone()) {
                    self.seen_l.push(nf.clone());
                    for r_nf in self.seen_r.iter() {
                        if let Some(met) = meet_nf(&nf, r_nf, terms) {
                            if !self.pending.contains(&met) {
                                self.pending.push_back(met);
                            }
                        }
                    }
                }
                self.flip = true;
                if let Some(result) = self.pending.pop_front() {
                    WorkStep::Emit(result, boxed_work(Work::Meet(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::Meet(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.left = rest;
                self.flip = true;
                WorkStep::More(boxed_work(Work::Meet(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.left = Node::Fail;
                self.flip = true;
                WorkStep::More(boxed_work(Work::Meet(self.take_self())))
            }
        }
    }

    /// Pull from right node and meet with seen_l
    fn pull_right(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.right, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.right = rest;
                if self.seen_r_set.insert(nf.clone()) {
                    self.seen_r.push(nf.clone());
                    for l_nf in self.seen_l.iter() {
                        if let Some(met) = meet_nf(l_nf, &nf, terms) {
                            if !self.pending.contains(&met) {
                                self.pending.push_back(met);
                            }
                        }
                    }
                }
                self.flip = false;
                if let Some(result) = self.pending.pop_front() {
                    WorkStep::Emit(result, boxed_work(Work::Meet(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::Meet(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.right = rest;
                self.flip = false;
                WorkStep::More(boxed_work(Work::Meet(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.right = Node::Fail;
                self.flip = false;
                WorkStep::More(boxed_work(Work::Meet(self.take_self())))
            }
        }
    }
}

// ============================================================================
// FixWork: Call-context tabling for recursive calls
// ============================================================================

type BindId = u64;

static NEXT_BIND_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Debug)]
struct Binding<C: Clone> {
    id: BindId,
    body: Arc<Rel<C>>,
}

/// Environment for Fix bindings (RelId -> Rel body).
///
/// Uses persistent map for efficient cloning during search.
#[derive(Clone, Debug, Default)]
pub struct Env<C: Clone> {
    bindings: im::HashMap<RelId, Binding<C>>,
}

impl<C: Clone> Env<C> {
    /// Create an empty environment.
    pub fn new() -> Self {
        Self {
            bindings: im::HashMap::new(),
        }
    }

    /// Bind a RelId to a Rel body.
    pub fn bind(&self, id: RelId, body: Arc<Rel<C>>) -> Self {
        let binding = Binding {
            id: NEXT_BIND_ID.fetch_add(1, Ordering::Relaxed),
            body,
        };
        Self {
            bindings: self.bindings.update(id, binding),
        }
    }

    /// Look up a binding.
    fn lookup(&self, id: RelId) -> Option<&Binding<C>> {
        self.bindings.get(&id)
    }

    /// Check if a binding exists.
    pub fn contains(&self, id: RelId) -> bool {
        self.bindings.contains_key(&id)
    }
}

/// Key for call-context tabling.
///
/// Identifies a recursive call by its RelId and adjacent boundary constraints.
/// Two calls with the same key should share their tabled answers.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CallKey<C: ConstraintOps> {
    /// The relation being called.
    pub rel: RelId,
    /// Unique binding id for the Fix scope.
    pub bind_id: BindId,
    /// Left boundary NF (if any).
    pub left: Option<NF<C>>,
    /// Right boundary NF (if any).
    pub right: Option<NF<C>>,
}

impl<C: ConstraintOps> CallKey<C> {
    /// Create a new CallKey.
    pub fn new(rel: RelId, bind_id: BindId, left: Option<NF<C>>, right: Option<NF<C>>) -> Self {
        Self {
            rel,
            bind_id,
            left,
            right,
        }
    }
}

/// State of a tabled call's producer.
#[derive(Clone, Debug, PartialEq)]
pub enum ProducerState {
    /// Producer hasn't started yet.
    NotStarted,
    /// Producer is currently running.
    Running,
    /// Producer has completed.
    Done,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProducerStep {
    Progress,
    Blocked,
    Done,
}

/// Spec for rebuilding a producer iteration.
#[derive(Clone, Debug)]
pub struct ProducerSpec<C: ConstraintOps> {
    /// CallKey for ReplayOnly protection.
    pub key: CallKey<C>,
    /// Body of the Fix relation.
    pub body: Arc<Rel<C>>,
    /// Left boundary to apply for this call.
    pub left: Option<NF<C>>,
    /// Right boundary to apply for this call.
    pub right: Option<NF<C>>,
    /// Environment for resolving Fix bindings.
    pub env: Env<C>,
}

#[derive(Debug)]
struct TableAnswers<C: ConstraintOps> {
    answers: Vec<NF<C>>,
    seen: HashSet<NF<C>>,
    waker: QueueWaker,
}

#[derive(Debug)]
struct TableProducer<C: ConstraintOps> {
    state: ProducerState,
    producer: Option<Node<C>>,
    spec: Option<ProducerSpec<C>>,
    iteration_start_len: usize,
    producer_task_active: bool,
}

/// A table entry for a recursive call.
///
/// Stores the answers produced so far and the producer state.
#[derive(Debug)]
pub struct Table<C: ConstraintOps> {
    answers: Mutex<TableAnswers<C>>,
    producer: Mutex<TableProducer<C>>,
}

impl<C: ConstraintOps> Table<C> {
    /// Create a new empty table.
    pub fn new() -> Self {
        Self::with_waker(QueueWaker::noop())
    }

    pub fn with_waker(waker: QueueWaker) -> Self {
        Self {
            answers: Mutex::new(TableAnswers {
                answers: Vec::new(),
                seen: HashSet::new(),
                waker,
            }),
            producer: Mutex::new(TableProducer {
                state: ProducerState::NotStarted,
                producer: None,
                spec: None,
                iteration_start_len: 0,
                producer_task_active: false,
            }),
        }
    }

    /// Add an answer to the table.
    pub fn add_answer(&self, nf: NF<C>) -> bool {
        let mut answers = self.answers.lock();
        if answers.seen.insert(nf.clone()) {
            answers.answers.push(nf);
            answers.waker.wake();
            true
        } else {
            false
        }
    }

    /// Mark the producer as running.
    pub fn start_producer(
        &self,
        producer: Node<C>,
        spec: ProducerSpec<C>,
        iteration_start_len: usize,
    ) {
        let mut guard = self.producer.lock();
        guard.state = ProducerState::Running;
        guard.producer = Some(producer);
        guard.spec = Some(spec);
        guard.iteration_start_len = iteration_start_len;
    }

    /// Mark the producer as done.
    pub fn finish_producer(&self) {
        {
            let mut guard = self.producer.lock();
            guard.state = ProducerState::Done;
            guard.producer = None;
        }
        self.answers.lock().waker.wake();
    }

    /// Check if producer is done.
    pub fn is_done(&self) -> bool {
        self.producer.lock().state == ProducerState::Done
    }

    /// Check if producer is running.
    pub fn is_running(&self) -> bool {
        self.producer.lock().state == ProducerState::Running
    }

    pub fn producer_state(&self) -> ProducerState {
        self.producer.lock().state.clone()
    }

    pub fn producer_task_active(&self) -> bool {
        self.producer.lock().producer_task_active
    }

    pub fn set_producer_task_active(&self, active: bool) {
        self.producer.lock().producer_task_active = active;
    }

    pub fn try_mark_producer_active(&self) -> bool {
        let mut guard = self.producer.lock();
        if guard.producer_task_active || guard.state == ProducerState::Done || guard.spec.is_none()
        {
            false
        } else {
            guard.producer_task_active = true;
            true
        }
    }

    pub fn producer_spec_is_some(&self) -> bool {
        self.producer.lock().spec.is_some()
    }

    pub fn producer_spec_clone(&self) -> Option<ProducerSpec<C>> {
        self.producer.lock().spec.clone()
    }

    pub fn take_producer_node(&self) -> Option<Node<C>> {
        self.producer.lock().producer.take()
    }

    pub fn set_producer_node(&self, node: Node<C>) {
        self.producer.lock().producer = Some(node);
    }

    pub fn iteration_start_len(&self) -> usize {
        self.producer.lock().iteration_start_len
    }

    pub fn set_iteration_start_len(&self, len: usize) {
        self.producer.lock().iteration_start_len = len;
    }

    pub fn answers_len(&self) -> usize {
        self.answers.lock().answers.len()
    }

    pub fn answer_at(&self, index: usize) -> Option<NF<C>> {
        self.answers.lock().answers.get(index).cloned()
    }

    /// Get all answers.
    pub fn all_answers(&self) -> Vec<NF<C>> {
        self.answers.lock().answers.clone()
    }

    pub fn blocked_on(&self) -> BlockedOn {
        self.answers.lock().waker.blocked_on()
    }
}

#[cfg(test)]
impl<C: ConstraintOps> Table<C> {
    fn lock_answers_for_test(&self) -> parking_lot::MutexGuard<'_, TableAnswers<C>> {
        self.answers.lock()
    }

    fn try_lock_answers_for_test(&self) -> Option<parking_lot::MutexGuard<'_, TableAnswers<C>>> {
        self.answers.try_lock()
    }

    fn lock_producer_for_test(&self) -> parking_lot::MutexGuard<'_, TableProducer<C>> {
        self.producer.lock()
    }

    fn try_lock_producer_for_test(&self) -> Option<parking_lot::MutexGuard<'_, TableProducer<C>>> {
        self.producer.try_lock()
    }
}

impl<C: ConstraintOps> Default for Table<C> {
    fn default() -> Self {
        Self::new()
    }
}

pub fn step_table_producer<C: ConstraintOps>(
    table: &Arc<Table<C>>,
    terms: &mut TermStore,
    tables: &Tables<C>,
) -> ProducerStep {
    let state = table.producer_state();
    if state == ProducerState::Done {
        table.set_producer_task_active(false);
        return ProducerStep::Done;
    }

    if state == ProducerState::NotStarted {
        let Some(spec) = table.producer_spec_clone() else {
            table.finish_producer();
            table.set_producer_task_active(false);
            return ProducerStep::Done;
        };
        let mut producer_pipe = PipeWork::from_rel_with_boundaries(
            spec.body.as_ref().clone(),
            spec.left.clone(),
            spec.right.clone(),
            spec.env.clone(),
            tables.clone(),
        );
        producer_pipe.call_mode = CallMode::ReplayOnly(Box::new(spec.key.clone()));
        let producer_node = Node::Work(boxed_work(Work::Pipe(producer_pipe)));
        table.start_producer(producer_node, spec, table.answers_len());
    }

    let current = table.take_producer_node().unwrap_or(Node::Fail);

    let step = step_node(current, terms);
    match step {
        NodeStep::Emit(nf, rest) => {
            let _ = table.add_answer(nf);
            table.set_producer_node(rest);
            ProducerStep::Progress
        }
        NodeStep::Continue(rest) => {
            table.set_producer_node(rest);
            ProducerStep::Progress
        }
        NodeStep::Exhausted => {
            let has_new = table.answers_len() > table.iteration_start_len();
            if has_new {
                let Some(spec) = table.producer_spec_clone() else {
                    table.finish_producer();
                    table.set_producer_task_active(false);
                    return ProducerStep::Done;
                };
                let mut producer_pipe = PipeWork::from_rel_with_boundaries(
                    spec.body.as_ref().clone(),
                    spec.left.clone(),
                    spec.right.clone(),
                    spec.env.clone(),
                    tables.clone(),
                );
                producer_pipe.call_mode = CallMode::ReplayOnly(Box::new(spec.key.clone()));
                table.set_iteration_start_len(table.answers_len());
                table.set_producer_node(Node::Work(boxed_work(Work::Pipe(producer_pipe))));
                ProducerStep::Progress
            } else {
                table.finish_producer();
                table.set_producer_task_active(false);
                ProducerStep::Done
            }
        }
    }
}

type TableMap<C> = DashMap<CallKey<C>, Arc<Table<C>>>;

/// Collection of tables for call-context tabling.
///
/// Uses a shared concurrent map so all clones see the same tables.
#[derive(Clone, Debug)]
pub struct Tables<C: ConstraintOps> {
    map: Arc<TableMap<C>>,
    queue_bound: usize,
    wake_hub: Arc<WakeHub>,
}

impl<C: ConstraintOps> Tables<C> {
    /// Create an empty Tables collection.
    pub fn new() -> Self {
        Self::with_queue_bound(64)
    }

    pub fn with_queue_bound(queue_bound: usize) -> Self {
        let (wake_hub, _rx) = WakeHub::new();
        Self::with_queue_bound_and_waker(queue_bound, wake_hub)
    }

    pub fn with_queue_bound_and_waker(queue_bound: usize, wake_hub: Arc<WakeHub>) -> Self {
        Self {
            map: Arc::new(DashMap::new()),
            queue_bound: queue_bound.max(1),
            wake_hub,
        }
    }

    /// Look up a table by CallKey.
    pub fn lookup(&self, key: &CallKey<C>) -> Option<Arc<Table<C>>> {
        self.map.get(key).map(|entry| entry.value().clone())
    }

    /// Get or create a table for a CallKey.
    pub fn get_or_create(&self, key: CallKey<C>) -> Arc<Table<C>> {
        if let Some(table) = self.map.get(&key) {
            return table.value().clone();
        }
        let table = Arc::new(Table::with_waker(self.waker()));
        let entry = self.map.entry(key).or_insert(table.clone());
        entry.value().clone()
    }

    /// Check if a table exists for a CallKey.
    pub fn contains(&self, key: &CallKey<C>) -> bool {
        self.map.contains_key(key)
    }

    /// Get the number of tables.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn queue_bound(&self) -> usize {
        self.queue_bound
    }

    pub fn waker(&self) -> QueueWaker {
        self.wake_hub.waker()
    }
}

impl<C: ConstraintOps> Default for Tables<C> {
    fn default() -> Self {
        Self::new()
    }
}

/// FixWork: table handle that streams answers and steps the producer inline.
///
/// The producer runs in iterations. Each iteration evaluates the body with
/// replay-only calls for the current CallKey.
#[derive(Clone, Debug)]
pub struct FixWork<C: ConstraintOps> {
    /// The CallKey for this tabled call.
    pub key: CallKey<C>,
    /// Reference to the table.
    pub table: Arc<Table<C>>,
    /// Current answer index for this handle.
    pub answer_index: usize,
    /// Tables for nested calls.
    pub tables: Tables<C>,
}

impl<C: ConstraintOps> FixWork<C> {
    /// Create a new FixWork handle.
    pub fn new(
        key: CallKey<C>,
        table: Arc<Table<C>>,
        start_index: usize,
        tables: Tables<C>,
    ) -> Self {
        Self {
            key,
            table,
            answer_index: start_index,
            tables,
        }
    }

    /// Step this FixWork handle.
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let _ = terms;
        if let Some(nf) = self.table.answer_at(self.answer_index) {
            self.answer_index += 1;
            return WorkStep::Emit(nf, boxed_work(Work::Fix(self.clone())));
        }

        if self.table.is_done() {
            return WorkStep::Done;
        }

        if !self.table.try_mark_producer_active() {
            if self.table.is_done() {
                return WorkStep::Done;
            }
            return WorkStep::More(boxed_work(Work::Fix(self.clone())));
        }

        let step = step_table_producer(&self.table, terms, &self.tables);
        self.table.set_producer_task_active(false);

        if let Some(nf) = self.table.answer_at(self.answer_index) {
            self.answer_index += 1;
            return WorkStep::Emit(nf, boxed_work(Work::Fix(self.clone())));
        }

        match step {
            ProducerStep::Done => WorkStep::Done,
            ProducerStep::Progress | ProducerStep::Blocked => {
                WorkStep::More(boxed_work(Work::Fix(self.clone())))
            }
        }
    }
}


#[cfg(test)]
#[path = "tests/work.rs"]
mod tests;
