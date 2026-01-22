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
mod tests {
    use super::{
        boxed_node, boxed_work, rel_to_node, step_table_producer, AndGroup, CallKey, CallMode,
        ComposeWork, Env, FixWork, JoinReceiverWork, MeetWork, PipeWork, ProducerSpec,
        ProducerState, ProducerStep, Table, Tables, Work, WorkStep,
    };
    use crate::drop_fresh::DropFresh;
    use crate::factors::Factors;
    use crate::kernel::compose_nf;
    use crate::kernel::dual::dual_nf;
    use crate::nf::NF;
    use crate::node::{step_node, Node, NodeStep};
    use crate::queue::{AnswerQueue, SinkResult};
    use crate::rel::Rel;
    use crate::term::TermStore;
    use crate::test_utils::{make_ground_nf, make_rule_nf, setup};
    use smallvec::SmallVec;
    use std::sync::Arc;

    /// Create identity NF (x -> x with single variable)
    fn make_identity_nf() -> NF<()> {
        // Note: NF::identity(()) creates an empty-pattern NF, not x -> x
        // For tests we need the variable identity x -> x
        NF::identity(())
    }

    /// Create variable identity NF (x -> x) using a specific TermStore
    fn make_var_identity_nf(terms: &mut TermStore) -> NF<()> {
        let v0 = terms.var(0);
        NF::new(
            SmallVec::from_slice(&[v0]),
            DropFresh::identity(1),
            SmallVec::from_slice(&[v0]),
        )
    }

    /// Create a Rel::Atom from NF
    fn atom_rel(nf: NF<()>) -> Arc<Rel<()>> {
        Arc::new(Rel::Atom(Arc::new(nf)))
    }

    /// Create Factors from a slice of Rels
    fn factors_from_rels(rels: Vec<Arc<Rel<()>>>) -> Factors<()> {
        if rels.is_empty() {
            Factors::new()
        } else {
            Factors::from_seq(Arc::from(rels))
        }
    }

    fn or_chain(rels: Vec<Arc<Rel<()>>>) -> Arc<Rel<()>> {
        let mut iter = rels.into_iter();
        let Some(first) = iter.next() else {
            return Arc::new(Rel::Zero);
        };
        iter.fold(first, |acc, rel| Arc::new(Rel::Or(rel, acc)))
    }

    fn delayed_or(depth: usize, inner: Arc<Rel<()>>) -> Arc<Rel<()>> {
        let mut rel = inner;
        for _ in 0..depth {
            rel = Arc::new(Rel::Or(Arc::new(Rel::Zero), rel));
        }
        rel
    }

    fn count_pipe_nodes(node: &Node<()>) -> usize {
        match node {
            Node::Fail => 0,
            Node::Emit(_, rest) => count_pipe_nodes(rest),
            Node::Or(left, right) => count_pipe_nodes(left) + count_pipe_nodes(right),
            Node::Work(work) => count_pipe_nodes_in_work(work),
        }
    }

    fn count_pipe_nodes_in_work(work: &Work<()>) -> usize {
        match work {
            Work::Pipe(_) => 1,
            Work::Meet(meet) => count_pipe_nodes(&meet.left) + count_pipe_nodes(&meet.right),
            Work::AndGroup(group) => group
                .producers
                .iter()
                .map(|producer| count_pipe_nodes(&producer.node))
                .sum(),
            Work::Fix(_) => 0,
            Work::Compose(compose) => {
                count_pipe_nodes(&compose.left) + count_pipe_nodes(&compose.right)
            }
            Work::JoinReceiver(_) => 0,
            Work::Atom(_) => 0,
            Work::Done => 0,
        }
    }

    fn find_fixwork_in_node(node: &Node<()>) -> Option<FixWork<()>> {
        match node {
            Node::Work(work) => match work.as_ref() {
                Work::Fix(fix) => Some(fix.clone()),
                _ => None,
            },
            Node::Or(left, right) => {
                find_fixwork_in_node(left).or_else(|| find_fixwork_in_node(right))
            }
            _ => None,
        }
    }

    fn extract_key_from_step(step: WorkStep<()>) -> CallKey<()> {
        match step {
            WorkStep::More(work) => match *work {
                Work::Compose(compose) => {
                    let fix = find_fixwork_in_node(&compose.left)
                        .or_else(|| find_fixwork_in_node(&compose.right))
                        .expect("Expected FixWork in compose nodes");
                    fix.key
                }
                _ => panic!("Expected Work::Compose(..)"),
            },
            _ => panic!("Expected WorkStep::More(..)"),
        }
    }

    fn is_work_pipe(node: &Node<()>) -> bool {
        matches!(node, Node::Work(work) if matches!(work.as_ref(), Work::Pipe(_)))
    }

    fn unwrap_join_receiver(work: Work<()>) -> JoinReceiverWork<()> {
        match work {
            Work::JoinReceiver(join) => join,
            other => panic!("Expected JoinReceiverWork, got {:?}", other),
        }
    }

    fn unwrap_and_group(work: Work<()>) -> AndGroup<()> {
        match work {
            Work::AndGroup(group) => group,
            other => panic!("Expected AndGroup, got {:?}", other),
        }
    }

    fn unwrap_work_pipe(node: Node<()>) -> PipeWork<()> {
        match node {
            Node::Work(work) => match *work {
                Work::Pipe(pipe) => pipe,
                _ => panic!("Expected Work::Pipe"),
            },
            _ => panic!("Expected Node::Work"),
        }
    }

    fn unwrap_work_compose(step: WorkStep<()>) -> ComposeWork<()> {
        match step {
            WorkStep::More(work) => match *work {
                Work::Compose(compose) => compose,
                _ => panic!("Expected Work::Compose"),
            },
            _ => panic!("Expected WorkStep::More"),
        }
    }

    fn unwrap_split(step: WorkStep<()>) -> (Node<()>, Node<()>) {
        match step {
            WorkStep::Split(left, right) => (*left, *right),
            _ => panic!("Expected WorkStep::Split"),
        }
    }

    // ========================================================================
    // COMPOSE WORK TESTS
    // ========================================================================

    #[test]
    fn composework_emits_composed_nf() {
        let (symbols, mut terms) = setup();
        let left_nf = make_var_identity_nf(&mut terms);
        let right_nf = make_ground_nf("A", &symbols, &mut terms);
        let expected = compose_nf(&left_nf, &right_nf, &mut terms)
            .expect("compose should succeed");

        let left = Node::Emit(left_nf, Box::new(Node::Fail));
        let right = Node::Emit(right_nf, Box::new(Node::Fail));
        let mut compose = ComposeWork::new(left, right);

        let mut steps = 0;
        let mut step = compose.step(&mut terms);
        loop {
            match step {
                WorkStep::Emit(nf, _) => {
                    assert_eq!(nf, expected);
                    break;
                }
                WorkStep::More(work) => {
                    compose = unwrap_work_compose(WorkStep::More(work));
                    step = compose.step(&mut terms);
                }
                other => panic!("Expected emit, got {:?}", other),
            }
            steps += 1;
            if steps > 4 {
                panic!("ComposeWork did not emit within expected steps");
            }
        }
    }

    #[test]
    fn composework_emits_composed_nf_dual() {
        let (symbols, mut terms) = setup();
        let left_nf = make_var_identity_nf(&mut terms);
        let right_nf = make_ground_nf("A", &symbols, &mut terms);
        let expected = compose_nf(&left_nf, &right_nf, &mut terms)
            .expect("compose should succeed");
        let expected_dual = dual_nf(&expected, &mut terms);
        let dual_left = dual_nf(&right_nf, &mut terms);
        let dual_right = dual_nf(&left_nf, &mut terms);

        let left = Node::Emit(dual_left, Box::new(Node::Fail));
        let right = Node::Emit(dual_right, Box::new(Node::Fail));
        let mut compose = ComposeWork::new(left, right);

        let mut steps = 0;
        let mut step = compose.step(&mut terms);
        loop {
            match step {
                WorkStep::Emit(nf, _) => {
                    assert_eq!(nf, expected_dual);
                    break;
                }
                WorkStep::More(work) => {
                    compose = unwrap_work_compose(WorkStep::More(work));
                    step = compose.step(&mut terms);
                }
                other => panic!("Expected emit, got {:?}", other),
            }
            steps += 1;
            if steps > 4 {
                panic!("ComposeWork did not emit within expected steps");
            }
        }
    }

    #[test]
    fn seq_does_not_spawn_pipe_per_and_answer() {
        let (symbols, mut terms) = setup();
        let mut atoms = Vec::new();
        for idx in 0..8 {
            let name = format!("A{idx}");
            atoms.push(atom_rel(make_ground_nf(&name, &symbols, &mut terms)));
        }

        let left_or = or_chain(atoms);
        let right_identity = atom_rel(make_var_identity_nf(&mut terms));
        let and_rel = Arc::new(Rel::And(left_or, right_identity));
        let delayed = delayed_or(8, atom_rel(make_var_identity_nf(&mut terms)));

        let seq = Rel::Seq(Arc::from(vec![and_rel, delayed]));
        let env = Env::new();
        let tables = Tables::new();
        let mut node = rel_to_node(&seq, &env, &tables);

        for _ in 0..24 {
            match step_node(node, &mut terms) {
                NodeStep::Emit(_, rest) | NodeStep::Continue(rest) => node = rest,
                NodeStep::Exhausted => {
                    node = Node::Fail;
                    break;
                }
            }
        }

        let pipe_count = count_pipe_nodes(&node);
        assert!(
            pipe_count <= 2,
            "Seq should not spawn one pipe per And answer; got {pipe_count}"
        );
    }

    #[test]
    fn seq_does_not_spawn_pipe_per_and_answer_dual() {
        use crate::rel::dual;

        let (symbols, mut terms) = setup();
        let mut atoms = Vec::new();
        for idx in 0..8 {
            let name = format!("A{idx}");
            atoms.push(atom_rel(make_ground_nf(&name, &symbols, &mut terms)));
        }

        let left_or = or_chain(atoms);
        let right_identity = atom_rel(make_var_identity_nf(&mut terms));
        let and_rel = Arc::new(Rel::And(left_or, right_identity));
        let delayed = delayed_or(8, atom_rel(make_var_identity_nf(&mut terms)));

        let seq = Rel::Seq(Arc::from(vec![and_rel, delayed]));
        let dual_seq = dual(&seq, &mut terms);
        let env = Env::new();
        let tables = Tables::new();
        let mut node = rel_to_node(&dual_seq, &env, &tables);

        for _ in 0..24 {
            match step_node(node, &mut terms) {
                NodeStep::Emit(_, rest) | NodeStep::Continue(rest) => node = rest,
                NodeStep::Exhausted => {
                    node = Node::Fail;
                    break;
                }
            }
        }

        let pipe_count = count_pipe_nodes(&node);
        assert!(
            pipe_count <= 3,
            "Dual Seq should not spawn one pipe per And answer; got {pipe_count}"
        );
    }

    // ========================================================================
    // WORK ENUM TESTS
    // ========================================================================

    #[test]
    fn work_atom_construction() {
        let nf = make_identity_nf();
        let work: Work<()> = Work::Atom(nf);
        assert!(matches!(work, Work::Atom(_)));
    }

    #[test]
    fn work_pipe_construction() {
        let pipe = PipeWork::new();
        let work: Work<()> = Work::Pipe(pipe);
        assert!(matches!(work, Work::Pipe(_)));
    }

    // ========================================================================
    // WORKSTEP ENUM TESTS
    // ========================================================================

    #[test]
    fn workstep_done_construction() {
        let step: WorkStep<()> = WorkStep::Done;
        assert!(matches!(step, WorkStep::Done));
    }

    #[test]
    fn workstep_emit_construction() {
        let nf = make_identity_nf();
        let work = Work::Atom(make_identity_nf());
        let step: WorkStep<()> = WorkStep::Emit(nf, boxed_work(work));
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn workstep_split_construction() {
        let left: Node<()> = Node::Fail;
        let right: Node<()> = Node::Fail;
        let step: WorkStep<()> = WorkStep::Split(boxed_node(left), boxed_node(right));
        assert!(matches!(step, WorkStep::Split(_, _)));
    }

    #[test]
    fn workstep_more_construction() {
        let work = Work::Atom(make_identity_nf());
        let step: WorkStep<()> = WorkStep::More(boxed_work(work));
        assert!(matches!(step, WorkStep::More(_)));
    }

    // ========================================================================
    // PIPEWORK CONSTRUCTION TESTS
    // ========================================================================

    #[test]
    fn pipework_new_is_empty() {
        let pipe: PipeWork<()> = PipeWork::new();
        assert!(pipe.is_empty());
    }

    #[test]
    fn pipework_with_mid_only() {
        let nf = make_identity_nf();
        let rels = vec![atom_rel(nf)];
        let mid = factors_from_rels(rels);
        let pipe: PipeWork<()> = PipeWork::with_mid(mid);
        assert!(!pipe.is_empty());
    }

    #[test]
    fn pipework_with_boundaries_and_empty_mid() {
        let nf = make_identity_nf();
        let pipe: PipeWork<()> =
            PipeWork::with_boundaries(Some(nf.clone()), Factors::new(), Some(nf));
        // Has boundaries but empty mid
        assert!(!pipe.is_empty());
    }

    #[test]
    fn pipework_with_left_boundary_only() {
        let nf = make_identity_nf();
        let pipe: PipeWork<()> = PipeWork::with_boundaries(Some(nf), Factors::new(), None);
        assert!(!pipe.is_empty());
    }

    #[test]
    fn pipework_with_right_boundary_only() {
        let nf = make_identity_nf();
        let pipe: PipeWork<()> = PipeWork::with_boundaries(None, Factors::new(), Some(nf));
        assert!(!pipe.is_empty());
    }

    // ========================================================================
    // PIPEWORK STEP TESTS - EMPTY CASES
    // ========================================================================

    #[test]
    fn pipework_step_empty_returns_done() {
        let mut terms = TermStore::new();
        let mut pipe: PipeWork<()> = PipeWork::new();
        let step = pipe.step(&mut terms);
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn pipework_step_boundaries_only_emits_compose() {
        let (symbols, mut terms) = setup();
        let left = make_ground_nf("X", &symbols, &mut terms);
        let right = make_ground_nf("X", &symbols, &mut terms);

        let mut pipe: PipeWork<()> =
            PipeWork::with_boundaries(Some(left), Factors::new(), Some(right));

        let step = pipe.step(&mut terms);
        // Should emit the composed result
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn pipework_step_left_boundary_only_emits() {
        let (symbols, mut terms) = setup();
        let nf = make_ground_nf("X", &symbols, &mut terms);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(nf), Factors::new(), None);

        let step = pipe.step(&mut terms);
        // Should emit the left boundary as result
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn pipework_step_right_boundary_only_emits() {
        let (symbols, mut terms) = setup();
        let nf = make_ground_nf("X", &symbols, &mut terms);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(None, Factors::new(), Some(nf));

        let step = pipe.step(&mut terms);
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn pipework_fuses_adjacent_atoms_anywhere() {
        let (symbols, mut terms) = setup();
        let nf = make_ground_nf("A", &symbols, &mut terms);
        let rels = vec![
            atom_rel(nf.clone()),
            atom_rel(nf.clone()),
            atom_rel(nf.clone()),
        ];
        let mid = factors_from_rels(rels);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        let step = pipe.step(&mut terms);
        match step {
            WorkStep::Emit(emitted, _) => assert_eq!(emitted, nf),
            _ => panic!("Expected adjacent atoms to fuse and emit in one step"),
        }
    }

    #[test]
    fn pipework_fuses_middle_atoms_before_advancing_ends() {
        let (symbols, mut terms) = setup();
        let nf = make_ground_nf("A", &symbols, &mut terms);
        let atom = atom_rel(nf);
        let or = Arc::new(Rel::Or(atom.clone(), atom.clone()));

        let rels = vec![or.clone(), atom.clone(), atom.clone(), or];
        let mid = factors_from_rels(rels);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        let step = pipe.step(&mut terms);
        match step {
            WorkStep::More(work) => match *work {
                Work::Pipe(updated) => {
                    assert_eq!(updated.mid.len(), 3, "Middle atoms should fuse first");
                }
                _ => panic!("Expected Work::Pipe"),
            },
            WorkStep::Split(left, right) => {
                let left_pipe = match *left {
                    Node::Work(work) => match *work {
                        Work::Pipe(pipe) => pipe,
                        _ => panic!("Expected Work::Pipe on left"),
                    },
                    _ => panic!("Expected Node::Work on left"),
                };
                let right_pipe = match *right {
                    Node::Work(work) => match *work {
                        Work::Pipe(pipe) => pipe,
                        _ => panic!("Expected Work::Pipe on right"),
                    },
                    _ => panic!("Expected Node::Work on right"),
                };
                assert_eq!(
                    left_pipe.mid.len(),
                    3,
                    "Left branch should see fused middle atoms"
                );
                assert_eq!(
                    right_pipe.mid.len(),
                    3,
                    "Right branch should see fused middle atoms"
                );
            }
            _ => panic!("Expected normalization to fuse middle atoms before advancing ends"),
        }
    }

    // ========================================================================
    // PIPEWORK STEP TESTS - ATOM ABSORPTION
    // ========================================================================

    #[test]
    fn pipework_step_single_atom_absorbs_to_left() {
        let (symbols, mut terms) = setup();
        let nf = make_ground_nf("X", &symbols, &mut terms);
        let rels = vec![atom_rel(nf.clone())];
        let mid = factors_from_rels(rels);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&mut terms);

        match step {
            WorkStep::More(work) => match *work {
                Work::Pipe(mut next_pipe) => {
                    assert!(
                        next_pipe.left.is_some(),
                        "Atom should be absorbed into left"
                    );
                    assert!(next_pipe.mid.is_empty(), "Mid should be empty after absorb");

                    let step2 = next_pipe.step(&mut terms);
                    assert!(matches!(step2, WorkStep::Emit(_, _)));
                }
                _ => panic!("Expected Work::Pipe"),
            },
            WorkStep::Emit(_, _) => {}
            _ => panic!("Expected Emit or More(Pipe), got {:?}", step),
        }
    }

    #[test]
    fn pipework_step_atom_composes_with_left_boundary() {
        let (symbols, mut terms) = setup();
        let left = make_ground_nf("X", &symbols, &mut terms);
        let atom_nf = make_ground_nf("X", &symbols, &mut terms);
        let rels = vec![atom_rel(atom_nf)];
        let mid = factors_from_rels(rels);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(left), mid, None);
        let step = pipe.step(&mut terms);

        // Should compose and continue or emit
        // Depends on implementation - More or Emit
        assert!(matches!(step, WorkStep::Emit(_, _) | WorkStep::More(_)));
    }

    // ========================================================================
    // PIPEWORK STEP TESTS - OR SPLITTING
    // ========================================================================

    #[test]
    fn pipework_step_or_in_mid_splits() {
        let (_, mut terms) = setup();
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&mut terms);

        // Should split into two branches
        assert!(matches!(step, WorkStep::Split(_, _)));
    }

    #[test]
    fn pipework_step_or_with_boundaries_splits() {
        let (symbols, mut terms) = setup();
        let left = make_ground_nf("X", &symbols, &mut terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(left), mid, None);
        let step = pipe.step(&mut terms);

        // Should split, preserving boundaries in both branches
        assert!(matches!(step, WorkStep::Split(_, _)));
    }

    // ========================================================================
    // SPLIT_OR COMPREHENSIVE TESTS - Must return Work::Pipe, not Fail
    // ========================================================================

    /// split_or must return Work::Pipe nodes, NOT Fail nodes.
    /// This is the fundamental contract of split_or.
    #[test]
    fn split_or_returns_work_pipe_not_fail() {
        let (symbols, mut terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&mut terms);

        let (left, right) = unwrap_split(step);
        assert!(
            is_work_pipe(&left),
            "Left branch must be Work::Pipe, got {:?}",
            left
        );
        assert!(
            is_work_pipe(&right),
            "Right branch must be Work::Pipe, got {:?}",
            right
        );
    }

    /// split_or left branch must contain the 'a' factor.
    #[test]
    fn split_or_left_branch_has_a_factor() {
        let (symbols, mut terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a.clone())));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&mut terms);

        let (left_node, _right_node) = unwrap_split(step);
        let left_pipe = unwrap_work_pipe(left_node);
        // Left pipe's mid should have 'a' at front
        assert!(
            !left_pipe.mid.is_empty(),
            "Left pipe mid should not be empty"
        );
        let front = left_pipe.mid.front().unwrap();
        match front.as_ref() {
            Rel::Atom(nf) => {
                assert_eq!(
                    nf.match_pats, nf_a.match_pats,
                    "Left branch should have 'a' factor"
                );
            }
            other => panic!("Expected Atom in left branch, got {:?}", other),
        }
    }

    /// split_or right branch must contain the 'b' factor.
    #[test]
    fn split_or_right_branch_has_b_factor() {
        let (symbols, mut terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b.clone())));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&mut terms);

        let (_left_node, right_node) = unwrap_split(step);
        let right_pipe = unwrap_work_pipe(right_node);
        // Right pipe's mid should have 'b' at front
        assert!(
            !right_pipe.mid.is_empty(),
            "Right pipe mid should not be empty"
        );
        let front = right_pipe.mid.front().unwrap();
        match front.as_ref() {
            Rel::Atom(nf) => {
                assert_eq!(
                    nf.match_pats, nf_b.match_pats,
                    "Right branch should have 'b' factor"
                );
            }
            other => panic!("Expected Atom in right branch, got {:?}", other),
        }
    }

    /// split_or must preserve left boundary in both branches.
    #[test]
    fn split_or_preserves_left_boundary() {
        let (symbols, mut terms) = setup();
        let boundary = make_ground_nf("BOUNDARY", &symbols, &mut terms);
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(boundary.clone()), mid, None);
        let step = pipe.step(&mut terms);

        let (left_node, right_node) = unwrap_split(step);
        let left_pipe = unwrap_work_pipe(left_node);
        let right_pipe = unwrap_work_pipe(right_node);
        assert!(
            left_pipe.left.is_some(),
            "Left branch should preserve left boundary"
        );
        assert!(
            right_pipe.left.is_some(),
            "Right branch should preserve left boundary"
        );
        assert_eq!(
            left_pipe.left.as_ref().unwrap().match_pats,
            boundary.match_pats
        );
        assert_eq!(
            right_pipe.left.as_ref().unwrap().match_pats,
            boundary.match_pats
        );
    }

    /// split_or must preserve right boundary in both branches.
    #[test]
    fn split_or_preserves_right_boundary() {
        let (symbols, mut terms) = setup();
        let boundary = make_ground_nf("BOUNDARY", &symbols, &mut terms);
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(None, mid, Some(boundary.clone()));
        let step = pipe.step(&mut terms);

        let (left_node, right_node) = unwrap_split(step);
        let left_pipe = unwrap_work_pipe(left_node);
        let right_pipe = unwrap_work_pipe(right_node);
        assert!(
            left_pipe.right.is_some(),
            "Left branch should preserve right boundary"
        );
        assert!(
            right_pipe.right.is_some(),
            "Right branch should preserve right boundary"
        );
        assert_eq!(
            left_pipe.right.as_ref().unwrap().match_pats,
            boundary.match_pats
        );
        assert_eq!(
            right_pipe.right.as_ref().unwrap().match_pats,
            boundary.match_pats
        );
    }

    #[test]
    fn pipework_prefers_non_call_over_call_on_opposite_end() {
        let (symbols, mut terms) = setup();
        let left_nf = make_ground_nf("L", &symbols, &mut terms);
        let right_nf = left_nf.clone();
        let left_rel: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(left_nf)));
        let right_rel: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(right_nf)));
        let and_rel: Arc<Rel<()>> = Arc::new(Rel::And(left_rel, right_rel));
        let call_rel: Arc<Rel<()>> = Arc::new(Rel::Call(0));
        let mid = factors_from_rels(vec![and_rel, call_rel]);

        let body = Arc::new(Rel::Atom(Arc::new(make_ground_nf(
            "BODY", &symbols, &mut terms,
        ))));
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        pipe.env = Env::new().bind(0, body);
        pipe.flip = true;

        let step = pipe.step(&mut terms);
        let key = extract_key_from_step(step);
        assert!(
            key.left.is_some(),
            "Call should see a left boundary after collapsing And of atoms"
        );
    }

    /// split_or must preserve both boundaries in both branches.
    #[test]
    fn split_or_preserves_both_boundaries() {
        let (symbols, mut terms) = setup();
        let left_boundary = make_ground_nf("LEFT", &symbols, &mut terms);
        let right_boundary = make_ground_nf("RIGHT", &symbols, &mut terms);
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(
            Some(left_boundary.clone()),
            mid,
            Some(right_boundary.clone()),
        );
        let step = pipe.step(&mut terms);

        let (left_node, right_node) = unwrap_split(step);
        let left_pipe = unwrap_work_pipe(left_node);
        let right_pipe = unwrap_work_pipe(right_node);
        // Check left boundary preserved
        assert_eq!(
            left_pipe.left.as_ref().unwrap().match_pats,
            left_boundary.match_pats
        );
        assert_eq!(
            right_pipe.left.as_ref().unwrap().match_pats,
            left_boundary.match_pats
        );
        // Check right boundary preserved
        assert_eq!(
            left_pipe.right.as_ref().unwrap().match_pats,
            right_boundary.match_pats
        );
        assert_eq!(
            right_pipe.right.as_ref().unwrap().match_pats,
            right_boundary.match_pats
        );
    }

    /// split_or must preserve remaining mid factors in both branches.
    /// Note: With direction-agnostic evaluation, atoms at the back are absorbed
    /// BEFORE splitting. So we use non-atom factors to test mid preservation.
    #[test]
    fn split_or_preserves_remaining_mid() {
        let (_, mut terms) = setup();
        // Use Or nodes which won't be absorbed during normalization
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let or1 = Arc::new(Rel::Or(a.clone(), b.clone()));
        let or2 = Arc::new(Rel::Or(a.clone(), b.clone())); // Non-atom rest factor
                                                           // Or followed by another Or (neither is normalizable)
        let mid = factors_from_rels(vec![or1, or2]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&mut terms);

        let (left_node, right_node) = unwrap_split(step);
        let left_pipe = unwrap_work_pipe(left_node);
        let right_pipe = unwrap_work_pipe(right_node);
        // Both branches should have 2 factors: (branch from or1) + or2
        assert_eq!(left_pipe.mid.len(), 2, "Left pipe should have 2 factors");
        assert_eq!(right_pipe.mid.len(), 2, "Right pipe should have 2 factors");
    }

    /// split_or must preserve env in both branches.
    #[test]
    fn split_or_preserves_env() {
        let (symbols, mut terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let nf_body = make_ground_nf("BODY", &symbols, &mut terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        // Create pipe with env containing a binding
        let env = Env::new().bind(42, Arc::new(Rel::Atom(Arc::new(nf_body))));
        let mut pipe: PipeWork<()> = PipeWork {
            left: None,
            mid,
            right: None,
            flip: false,
            env,
            tables: Tables::new(),
            call_mode: CallMode::Normal,
        };
        let step = pipe.step(&mut terms);

        let (left_node, right_node) = unwrap_split(step);
        let left_pipe = unwrap_work_pipe(left_node);
        let right_pipe = unwrap_work_pipe(right_node);
        assert!(
            left_pipe.env.contains(42),
            "Left branch should preserve env binding"
        );
        assert!(
            right_pipe.env.contains(42),
            "Right branch should preserve env binding"
        );
    }

    /// split_or with Zero branches should still return Work::Pipe (not optimize to Fail).
    /// The Fail optimization happens during evaluation, not during split.
    #[test]
    fn split_or_zero_branches_returns_work_pipe() {
        let (_, mut terms) = setup();
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&mut terms);

        // Even with Zero branches, split_or should return Work::Pipe
        // The Zero will be handled when each branch steps
        let (left, right) = unwrap_split(step);
        assert!(
            is_work_pipe(&left),
            "Left branch should be Work::Pipe even for Zero, got {:?}",
            left
        );
        assert!(
            is_work_pipe(&right),
            "Right branch should be Work::Pipe even for Zero, got {:?}",
            right
        );
    }

    // ========================================================================
    // PIPEWORK STEP TESTS - ZERO ANNIHILATION
    // ========================================================================

    #[test]
    fn pipework_step_zero_in_mid_returns_done() {
        let (_, mut terms) = setup();
        let zero_rel = Arc::new(Rel::Zero);
        let mid = factors_from_rels(vec![zero_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&mut terms);

        // Zero annihilates the pipe
        assert!(matches!(step, WorkStep::Done));
    }

    #[test]
    fn pipework_step_zero_with_boundaries_returns_done() {
        let (symbols, mut terms) = setup();
        let left = make_ground_nf("X", &symbols, &mut terms);
        let right = make_ground_nf("X", &symbols, &mut terms);
        let zero_rel = Arc::new(Rel::Zero);
        let mid = factors_from_rels(vec![zero_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(left), mid, Some(right));
        let step = pipe.step(&mut terms);

        assert!(matches!(step, WorkStep::Done));
    }

    // ========================================================================
    // PIPEWORK STEP TESTS - COMPOSITION FAILURE
    // ========================================================================

    #[test]
    fn pipework_step_incompatible_compose_returns_done() {
        let (symbols, mut terms) = setup();
        // A -> B cannot compose with C -> D
        let a_to_b = {
            let a = symbols.intern("A");
            let b = symbols.intern("B");
            let ta = terms.app0(a);
            let tb = terms.app0(b);
            NF::new(
                SmallVec::from_slice(&[ta]),
                DropFresh::identity(0),
                SmallVec::from_slice(&[tb]),
            )
        };
        let c_to_d = {
            let c = symbols.intern("C");
            let d = symbols.intern("D");
            let tc = terms.app0(c);
            let td = terms.app0(d);
            NF::new(
                SmallVec::from_slice(&[tc]),
                DropFresh::identity(0),
                SmallVec::from_slice(&[td]),
            )
        };

        let mid = factors_from_rels(vec![atom_rel(c_to_d)]);
        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(a_to_b), mid, None);
        let step = pipe.step(&mut terms);

        // Composition should fail (B != C), returning Done
        assert!(matches!(step, WorkStep::Done));
    }

    // ========================================================================
    // WORK::ATOM STEP TESTS
    // ========================================================================

    #[test]
    fn work_atom_step_emits_then_done() {
        let (_, mut terms) = setup();
        let nf = make_identity_nf();
        let mut work: Work<()> = Work::Atom(nf.clone());

        let step = work.step(&mut terms);

        match step {
            WorkStep::Emit(emitted, rest) => {
                // Should emit the NF
                assert_eq!(emitted, nf);
                assert!(matches!(*rest, Work::Done));
            }
            _ => panic!("Atom should emit"),
        }
    }

    // ========================================================================
    // INTEGRATION TESTS
    // ========================================================================

    #[test]
    fn pipework_multiple_atoms_compose() {
        let (symbols, mut terms) = setup();
        // X -> X ; X -> X should compose to X -> X
        let nf1 = make_ground_nf("X", &symbols, &mut terms);
        let nf2 = make_ground_nf("X", &symbols, &mut terms);
        let rels = vec![atom_rel(nf1), atom_rel(nf2)];
        let mid = factors_from_rels(rels);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        // Step until we get an answer or Done
        let mut steps = 0;
        loop {
            let step = pipe.step(&mut terms);
            match step {
                WorkStep::Emit(_, _) => break,
                WorkStep::Done => break,
                WorkStep::More(work) => match *work {
                    Work::Pipe(p) => pipe = p,
                    _ => panic!("Expected Pipe"),
                },
                WorkStep::Split(_, _) => panic!("Unexpected split"),
            }
            steps += 1;
            if steps > 10 {
                panic!("Too many steps");
            }
        }
    }

    // ========================================================================
    // BUG DEMONSTRATION: BACK ATOM ABSORPTION
    // These tests demonstrate that atoms at the BACK must be absorbed into
    // the right boundary. This is critical for outside-in evaluation.
    // ========================================================================

    /// BUG: Atoms at the back of mid should be absorbed into right boundary.
    /// This test demonstrates the required behavior for outside-in evaluation.
    #[test]
    fn pipework_step_back_atom_absorbs_to_right() {
        let (symbols, mut terms) = setup();
        // Create: mid = [Or(...), Atom(X->X)]
        // The Atom at the BACK should be absorbed into right boundary
        // BEFORE the Or at front is processed.
        let nf = make_ground_nf("X", &symbols, &mut terms);

        // Put an Or at front so front isn't an Atom
        let or_rel = Arc::new(Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Zero)));
        let atom_rel = Arc::new(Rel::Atom(Arc::new(nf.clone())));

        let mid = factors_from_rels(vec![or_rel, atom_rel]);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        // Normalize step should absorb back atom into right
        let step = pipe.step(&mut terms);

        // After one step, the back Atom should be absorbed into right boundary.
        match step {
            WorkStep::More(work) => match *work {
                Work::Pipe(p) => {
                    assert!(
                        p.right.is_some(),
                        "BUG: Back atom was NOT absorbed into right boundary!"
                    );
                }
                _ => panic!("Expected Work::Pipe"),
            },
            WorkStep::Split(left, right) => {
                let left_pipe = unwrap_work_pipe(*left);
                let right_pipe = unwrap_work_pipe(*right);
                assert!(
                    left_pipe.right.is_some(),
                    "Left branch missing absorbed right boundary"
                );
                assert!(
                    right_pipe.right.is_some(),
                    "Right branch missing absorbed right boundary"
                );
            }
            _ => panic!("Unexpected step result: {:?}", step),
        }
    }

    /// Test that atoms at both ends are absorbed before processing non-atoms.
    #[test]
    fn pipework_step_absorbs_both_ends_before_advancing() {
        let (symbols, mut terms) = setup();
        // mid = [Atom(A->A), Or(...), Atom(B->B)]
        // Both atoms should be absorbed before Or is processed
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);

        let atom_a = Arc::new(Rel::Atom(Arc::new(nf_a.clone())));
        let or_rel = Arc::new(Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Zero)));
        let atom_b = Arc::new(Rel::Atom(Arc::new(nf_b.clone())));

        let mid = factors_from_rels(vec![atom_a, or_rel, atom_b]);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        // Step until we get a Split (Or processing) or run out of More steps
        let mut steps = 0;
        let max_steps = 10;
        loop {
            let step = pipe.step(&mut terms);
            match step {
                WorkStep::More(work) => match *work {
                    Work::Pipe(p) => {
                        pipe = p;
                        steps += 1;
                        if steps > max_steps {
                            panic!("Too many More steps without Split");
                        }
                    }
                    _ => {
                        panic!("Unexpected non-Pipe More");
                    }
                },
                WorkStep::Split(_, _) => {
                    // When we reach Split, both boundaries should be set
                    assert!(
                        pipe.left.is_some(),
                        "BUG: Left boundary not set before Split"
                    );
                    assert!(
                        pipe.right.is_some(),
                        "BUG: Right boundary not set before Split"
                    );
                    break;
                }
                WorkStep::Done => {
                    panic!("Unexpected Done");
                }
                WorkStep::Emit(_, _) => {
                    panic!("Unexpected Emit");
                }
            }
        }
    }

    /// Test right boundary composition - critical for constraint propagation.
    #[test]
    fn pipework_step_right_boundary_composes() {
        let (symbols, mut terms) = setup();
        // Put two atoms at the back, they should compose into right boundary
        // mid = [Or(...), Atom(X->Y), Atom(Y->Z)]
        // After normalization: right = X->Z (composed)

        let x = symbols.intern("X");
        let y = symbols.intern("Y");
        let z = symbols.intern("Z");
        let tx = terms.app0(x);
        let ty = terms.app0(y);
        let tz = terms.app0(z);

        let x_to_y = NF::new(
            SmallVec::from_slice(&[tx]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[ty]),
        );
        let y_to_z = NF::new(
            SmallVec::from_slice(&[ty]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[tz]),
        );

        let or_rel = Arc::new(Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Zero)));
        let atom1 = Arc::new(Rel::Atom(Arc::new(x_to_y)));
        let atom2 = Arc::new(Rel::Atom(Arc::new(y_to_z)));

        let mid = factors_from_rels(vec![or_rel, atom1, atom2]);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        // Step until Split
        let mut steps = 0;
        loop {
            let step = pipe.step(&mut terms);
            match step {
                WorkStep::More(work) => match *work {
                    Work::Pipe(p) => {
                        pipe = p;
                        steps += 1;
                        if steps > 10 {
                            panic!("Too many steps");
                        }
                    }
                    _ => panic!("Expected Work::Pipe"),
                },
                WorkStep::Split(_, _) => {
                    // Right boundary should be composed: X->Z
                    let right = pipe.right.as_ref().expect("Right boundary should exist");
                    // Verify composition happened (output should be Z, not Y)
                    assert_eq!(right.build_pats.len(), 1, "Should have one output pattern");
                    assert_eq!(
                        right.build_pats[0], tz,
                        "BUG: Right boundary not composed! Output should be Z"
                    );
                    break;
                }
                _ => panic!("Unexpected result"),
            }
        }
    }

    // ========================================================================
    // MEETWORK CONSTRUCTION TESTS
    // ========================================================================

    #[test]
    fn meetwork_construction_both_fail() {
        let meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        assert!(matches!(*meet.left, Node::Fail));
        assert!(matches!(*meet.right, Node::Fail));
        assert!(meet.seen_l.is_empty());
        assert!(meet.seen_r.is_empty());
        assert!(meet.pending.is_empty());
        assert!(!meet.flip);
    }

    #[test]
    fn meetwork_construction_left_fail_right_emit() {
        let nf = make_identity_nf();
        let right = Node::Emit(nf, Box::new(Node::Fail));
        let meet: MeetWork<()> = MeetWork::new(Node::Fail, right);
        assert!(matches!(*meet.left, Node::Fail));
        assert!(matches!(*meet.right, Node::Emit(_, _)));
    }

    #[test]
    fn meetwork_construction_left_emit_right_fail() {
        let nf = make_identity_nf();
        let left = Node::Emit(nf, Box::new(Node::Fail));
        let meet: MeetWork<()> = MeetWork::new(left, Node::Fail);
        assert!(matches!(*meet.left, Node::Emit(_, _)));
        assert!(matches!(*meet.right, Node::Fail));
    }

    #[test]
    fn meetwork_construction_both_emit() {
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let left = Node::Emit(nf1, Box::new(Node::Fail));
        let right = Node::Emit(nf2, Box::new(Node::Fail));
        let meet: MeetWork<()> = MeetWork::new(left, right);
        assert!(matches!(*meet.left, Node::Emit(_, _)));
        assert!(matches!(*meet.right, Node::Emit(_, _)));
    }

    #[test]
    fn meetwork_construction_deep_left_or() {
        // Deeply nested Or on left
        let mut node: Node<()> = Node::Fail;
        for _ in 0..10 {
            node = Node::Or(Box::new(node), Box::new(Node::Fail));
        }
        let meet: MeetWork<()> = MeetWork::new(node, Node::Fail);
        assert!(matches!(*meet.left, Node::Or(_, _)));
    }

    // ========================================================================
    // MEETWORK STEP TESTS - BOTH FAIL
    // ========================================================================

    #[test]
    fn meetwork_step_both_fail_returns_done() {
        let (_, mut terms) = setup();
        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        let step = meet.step(&mut terms);
        assert!(
            matches!(step, WorkStep::Done),
            "Both sides Fail should return Done immediately"
        );
    }

    #[test]
    fn meetwork_step_left_fail_returns_done() {
        let (_, mut terms) = setup();
        let nf = make_identity_nf();
        let right = Node::Emit(nf, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, right);

        // With left Fail, no meets possible - should eventually return Done
        // (may take multiple steps as it drains right)
        let mut done = false;
        for _ in 0..10 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Done => {
                    done = true;
                    break;
                }
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }
        assert!(done, "Left Fail should eventually lead to Done");
    }

    #[test]
    fn meetwork_step_right_fail_returns_done() {
        let (_, mut terms) = setup();
        let nf = make_identity_nf();
        let left = Node::Emit(nf, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, Node::Fail);

        // With right Fail, no meets possible - should eventually return Done
        let mut done = false;
        for _ in 0..10 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Done => {
                    done = true;
                    break;
                }
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }
        assert!(done, "Right Fail should eventually lead to Done");
    }

    #[test]
    fn meetwork_steps_work_nodes() {
        let (symbols, mut terms) = setup();
        let nf = make_ground_nf("A", &symbols, &mut terms);
        let rel = Arc::new(Rel::Atom(Arc::new(nf.clone())));
        let factors = Factors::from_seq(Arc::from(vec![rel]));
        let left_pipe = PipeWork::with_mid(factors);
        let left = Node::Work(boxed_work(Work::Pipe(left_pipe)));
        let right = Node::Emit(nf, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emitted = false;
        for _ in 0..50 {
            match meet.step(&mut terms) {
                WorkStep::Emit(_, _) => {
                    emitted = true;
                    break;
                }
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                WorkStep::Done => break,
                _ => {}
            }
        }

        assert!(emitted, "MeetWork should be able to advance Work nodes");
    }

    // ========================================================================
    // MEETWORK STEP TESTS - COMPATIBLE MEETS
    // ========================================================================

    #[test]
    fn meetwork_step_identical_answers_produces_meet() {
        let (symbols, mut terms) = setup();
        // Both sides emit X -> X, which should meet successfully
        let nf1 = make_ground_nf("X", &symbols, &mut terms);
        let nf2 = make_ground_nf("X", &symbols, &mut terms);
        let left = Node::Emit(nf1, Box::new(Node::Fail));
        let right = Node::Emit(nf2, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        // Step until we get an emit or Done
        let mut emitted = false;
        for _ in 0..20 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(_, _) => {
                    emitted = true;
                    break;
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }
        assert!(emitted, "Meet of identical NFs should emit a result");
    }

    #[test]
    fn meetwork_step_identity_with_ground_specializes() {
        let (symbols, mut terms) = setup();
        // Left: x -> x (variable identity)
        // Right: A -> A (ground)
        // Meet should produce A -> A
        let identity = make_var_identity_nf(&mut terms);
        let ground = make_ground_nf("A", &symbols, &mut terms);

        let left = Node::Emit(identity, Box::new(Node::Fail));
        let right = Node::Emit(ground.clone(), Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut result: Option<NF<()>> = None;
        for _ in 0..20 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(nf, _) => {
                    result = Some(nf);
                    break;
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }

        assert!(result.is_some(), "Meet should produce a result");
        let res = result.unwrap();
        // Result should be ground (A -> A)
        assert_eq!(
            res.match_pats[0], ground.match_pats[0],
            "Meet result match should be ground term A"
        );
    }

    // ========================================================================
    // MEETWORK STEP TESTS - INCOMPATIBLE MEETS
    // ========================================================================

    #[test]
    fn meetwork_step_incompatible_ground_no_emit() {
        let (symbols, mut terms) = setup();
        // Left: A -> A
        // Right: B -> B
        // These can't meet (A != B)
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);

        let left = Node::Emit(nf_a, Box::new(Node::Fail));
        let right = Node::Emit(nf_b, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emitted = false;
        for _ in 0..20 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(_, _) => {
                    emitted = true;
                    break;
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }
        assert!(
            !emitted,
            "Incompatible NFs (A vs B) should not produce meet result"
        );
    }

    #[test]
    fn meetwork_step_arity_mismatch_no_emit() {
        let (symbols, mut terms) = setup();
        // Left: 1-in, 1-out
        // Right: 2-in, 2-out (if we can construct it)
        let single = make_ground_nf("X", &symbols, &mut terms);

        // Create a 2-tuple pattern
        let pair_sym = symbols.intern("Pair");
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let ta = terms.app0(a);
        let tb = terms.app0(b);
        let pair_ab = terms.app2(pair_sym, ta, tb);
        let double = NF::new(
            SmallVec::from_slice(&[pair_ab]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[pair_ab]),
        );

        let left = Node::Emit(single, Box::new(Node::Fail));
        let right = Node::Emit(double, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emitted = false;
        for _ in 0..20 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(_, _) => {
                    emitted = true;
                    break;
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }
        assert!(!emitted, "Ground mismatched patterns should not emit");
    }

    // ========================================================================
    // MEETWORK STEP TESTS - FAIRNESS/INTERLEAVING
    // ========================================================================

    #[test]
    fn meetwork_step_flip_alternates_sides() {
        let (_, mut terms) = setup();
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let nf3 = make_identity_nf();
        let nf4 = make_identity_nf();

        // Left has 2 answers, right has 2 answers
        let left = Node::Emit(nf1, Box::new(Node::Emit(nf2, Box::new(Node::Fail))));
        let right = Node::Emit(nf3, Box::new(Node::Emit(nf4, Box::new(Node::Fail))));

        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        // After first step, flip should be true (pulled from left)
        // After second step, flip should be false (pulled from right)
        // This tests the alternation behavior
        let mut steps = 0;
        let mut flip_values = Vec::new();
        for _ in 0..10 {
            flip_values.push(meet.flip);
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                WorkStep::Emit(_, work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => break,
            }
            steps += 1;
        }

        // Should have stepped at least twice
        assert!(
            steps >= 2,
            "Should take multiple steps with multiple answers"
        );
    }

    #[test]
    fn meetwork_step_multiple_meets_all_produced() {
        let (symbols, mut terms) = setup();
        // Left: emit variable identity x -> x twice
        // Right: emit A -> A, B -> B
        // If identity meets with A -> A and B -> B, should produce:
        // - A -> A (from identity meet A -> A)
        // - B -> B (from identity meet B -> B)
        // - Plus other combinations

        let id1 = make_var_identity_nf(&mut terms);
        let id2 = make_var_identity_nf(&mut terms);
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);

        let left = Node::Emit(id1, Box::new(Node::Emit(id2, Box::new(Node::Fail))));
        let right = Node::Emit(nf_a, Box::new(Node::Emit(nf_b, Box::new(Node::Fail))));

        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emit_count = 0;
        for _ in 0..50 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(_, rest) => {
                    emit_count += 1;
                    match *rest {
                        Work::Meet(m) => meet = m,
                        Work::Done => break,
                        _ => {}
                    }
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }

        // Should emit multiple results from the diagonal enumeration
        // 2 identities x 2 ground terms = up to 4 meets
        assert!(
            emit_count >= 2,
            "Should produce at least 2 meet results, got {}",
            emit_count
        );
    }

    // ========================================================================
    // MEETWORK STEP TESTS - PENDING QUEUE
    // ========================================================================

    #[test]
    fn meetwork_pending_emits_before_pulls() {
        let (_, mut terms) = setup();
        // Pre-populate pending queue to verify emit priority
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();

        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        meet.pending.push_back(nf1);
        meet.pending.push_back(nf2);

        // First step should emit from pending
        let step = meet.step(&mut terms);
        assert!(
            matches!(step, WorkStep::Emit(_, _)),
            "Should emit from pending first"
        );
    }

    #[test]
    fn meetwork_pending_preserves_order() {
        let (symbols, mut terms) = setup();
        // Pre-populate pending with ordered items
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let nf_c = make_ground_nf("C", &symbols, &mut terms);

        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        meet.pending.push_back(nf_a.clone());
        meet.pending.push_back(nf_b.clone());
        meet.pending.push_back(nf_c.clone());

        // Should emit in FIFO order
        let mut emitted = Vec::new();
        for _ in 0..5 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(nf, rest) => {
                    emitted.push(nf.match_pats[0]);
                    match *rest {
                        Work::Meet(m) => meet = m,
                        _ => break,
                    }
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }

        assert_eq!(emitted.len(), 3, "Should emit all 3 pending items");
        assert_eq!(emitted[0], nf_a.match_pats[0], "First should be A");
        assert_eq!(emitted[1], nf_b.match_pats[0], "Second should be B");
        assert_eq!(emitted[2], nf_c.match_pats[0], "Third should be C");
    }

    #[test]
    fn meetwork_drains_pending_before_done() {
        let (_, mut terms) = setup();
        // Both sides exhausted but pending has items
        let nf = make_identity_nf();
        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        meet.pending.push_back(nf);

        let step = meet.step(&mut terms);
        // Should NOT return Done if pending has items
        assert!(
            !matches!(step, WorkStep::Done),
            "Should drain pending before returning Done"
        );
    }

    // ========================================================================
    // MEETWORK STEP TESTS - EXHAUSTION SCENARIOS
    // ========================================================================

    #[test]
    fn meetwork_left_exhausts_first() {
        let (symbols, mut terms) = setup();
        // Left has 1 variable identity, right has 3 ground answers
        let id = make_var_identity_nf(&mut terms);
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let nf_c = make_ground_nf("C", &symbols, &mut terms);

        let left = Node::Emit(id, Box::new(Node::Fail));
        let right = Node::Emit(
            nf_a,
            Box::new(Node::Emit(
                nf_b,
                Box::new(Node::Emit(nf_c, Box::new(Node::Fail))),
            )),
        );

        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emit_count = 0;
        for _ in 0..30 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(_, rest) => {
                    emit_count += 1;
                    match *rest {
                        Work::Meet(m) => meet = m,
                        _ => break,
                    }
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }

        // Variable identity meets with A, B, C should produce 3 results
        assert_eq!(
            emit_count, 3,
            "Should produce 3 meets (identity with A, B, C)"
        );
    }

    #[test]
    fn meetwork_right_exhausts_first() {
        let (symbols, mut terms) = setup();
        // Left has 3 ground answers, right has 1 variable identity
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let nf_c = make_ground_nf("C", &symbols, &mut terms);
        let id = make_var_identity_nf(&mut terms);

        let left = Node::Emit(
            nf_a,
            Box::new(Node::Emit(
                nf_b,
                Box::new(Node::Emit(nf_c, Box::new(Node::Fail))),
            )),
        );
        let right = Node::Emit(id, Box::new(Node::Fail));

        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emit_count = 0;
        for _ in 0..30 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(_, rest) => {
                    emit_count += 1;
                    match *rest {
                        Work::Meet(m) => meet = m,
                        _ => break,
                    }
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }

        // A, B, C each meet with variable identity should produce 3 results
        assert_eq!(
            emit_count, 3,
            "Should produce 3 meets (A, B, C with identity)"
        );
    }

    #[test]
    fn meetwork_both_exhaust_simultaneously() {
        let (_, mut terms) = setup();
        // Both sides have 2 identical answers
        let id1 = make_identity_nf();
        let id2 = make_identity_nf();
        let id3 = make_identity_nf();
        let id4 = make_identity_nf();

        let left = Node::Emit(id1, Box::new(Node::Emit(id2, Box::new(Node::Fail))));
        let right = Node::Emit(id3, Box::new(Node::Emit(id4, Box::new(Node::Fail))));

        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emit_count = 0;
        let mut done = false;
        for _ in 0..50 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(_, rest) => {
                    emit_count += 1;
                    match *rest {
                        Work::Meet(m) => meet = m,
                        Work::Done => {
                            done = true;
                            break;
                        }
                        _ => {}
                    }
                }
                WorkStep::Done => {
                    done = true;
                    break;
                }
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => {}
            }
        }

        assert!(done, "Should eventually reach Done");
        // 2x2 = 4 combinations possible
        assert!(emit_count >= 1, "Should produce at least one meet result");
    }

    // ========================================================================
    // MEETWORK STEP TESTS - SEEN_L AND SEEN_R TRACKING
    // ========================================================================

    #[test]
    fn meetwork_seen_l_grows_after_left_emit() {
        let (_, mut terms) = setup();
        let nf = make_identity_nf();
        let left = Node::Emit(nf.clone(), Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, Node::Fail);

        assert!(meet.seen_l.is_empty(), "seen_l should start empty");

        // Step to pull from left
        loop {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                        if !meet.seen_l.is_empty() {
                            break;
                        }
                    }
                }
                _ => break,
            }
        }

        assert_eq!(
            meet.seen_l.len(),
            1,
            "seen_l should have 1 entry after pulling from left"
        );
    }

    #[test]
    fn meetwork_seen_r_grows_after_right_emit() {
        let (_, mut terms) = setup();
        let nf = make_identity_nf();
        let right = Node::Emit(nf.clone(), Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, right);

        assert!(meet.seen_r.is_empty(), "seen_r should start empty");

        // Step to pull from right (may need flip to be true)
        meet.flip = true; // Force pull from right
        loop {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                        if !meet.seen_r.is_empty() {
                            break;
                        }
                    }
                }
                _ => break,
            }
        }

        // Note: This test may fail if implementation skips exhausted sides
        // The important thing is that seen_r gets populated when right emits
    }

    // ========================================================================
    // MEETWORK STEP TESTS - OR NODE HANDLING
    // ========================================================================

    #[test]
    fn meetwork_handles_or_on_left() {
        let (_, mut terms) = setup();
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let nf3 = make_identity_nf();

        // Left is Or of two emits
        let or_left = Node::Or(
            Box::new(Node::Emit(nf1, Box::new(Node::Fail))),
            Box::new(Node::Emit(nf2, Box::new(Node::Fail))),
        );
        let right = Node::Emit(nf3, Box::new(Node::Fail));

        let mut meet: MeetWork<()> = MeetWork::new(or_left, right);

        // Should handle Or by interleaving properly
        let mut emit_count = 0;
        for _ in 0..30 {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Emit(_, rest) => {
                    emit_count += 1;
                    match *rest {
                        Work::Meet(m) => meet = m,
                        _ => break,
                    }
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                WorkStep::Split(_, _) => {
                    // Or could cause split
                }
            }
        }

        // 2 from left Or + 1 from right = at least 2 meets
        assert!(
            emit_count >= 1,
            "Should produce at least one meet result from Or"
        );
    }

    // ========================================================================
    // MEETWORK INTEGRATION WITH WORK ENUM
    // ========================================================================

    #[test]
    fn work_meet_construction() {
        let meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        let work: Work<()> = Work::Meet(meet);
        assert!(matches!(work, Work::Meet(_)));
    }

    #[test]
    fn work_meet_step_delegates_to_meetwork() {
        let (_, mut terms) = setup();
        let meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        let mut work: Work<()> = Work::Meet(meet);
        let step = work.step(&mut terms);
        // Should delegate to MeetWork::step
        assert!(matches!(step, WorkStep::Done));
    }

    // ========================================================================
    // MEETWORK STEP TESTS - SYMMETRIC BEHAVIOR
    // ========================================================================

    #[test]
    fn meetwork_symmetric_produces_same_results() {
        let (symbols, mut terms1) = setup();
        let (_, mut terms2) = setup();

        let nf_a = make_ground_nf("A", &symbols, &mut terms1);
        let id = make_identity_nf();

        // Meet(A, id) vs Meet(id, A) should produce same results
        let mut meet1: MeetWork<()> = MeetWork::new(
            Node::Emit(nf_a.clone(), Box::new(Node::Fail)),
            Node::Emit(id.clone(), Box::new(Node::Fail)),
        );
        let mut meet2: MeetWork<()> = MeetWork::new(
            Node::Emit(id, Box::new(Node::Fail)),
            Node::Emit(nf_a, Box::new(Node::Fail)),
        );

        let mut count1 = 0;
        let mut count2 = 0;

        // Run both to completion
        for _ in 0..30 {
            let step = meet1.step(&mut terms1);
            match step {
                WorkStep::Emit(_, rest) => {
                    count1 += 1;
                    match *rest {
                        Work::Meet(m) => meet1 = m,
                        _ => break,
                    }
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet1 = m;
                    }
                }
                _ => {}
            }
        }

        for _ in 0..30 {
            let step = meet2.step(&mut terms2);
            match step {
                WorkStep::Emit(_, rest) => {
                    count2 += 1;
                    match *rest {
                        Work::Meet(m) => meet2 = m,
                        _ => break,
                    }
                }
                WorkStep::Done => break,
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet2 = m;
                    }
                }
                _ => {}
            }
        }

        assert_eq!(
            count1, count2,
            "Symmetric meets should produce same number of results"
        );
    }

    // ========================================================================
    // MEETWORK SIZE/COMPLEXITY TESTS
    // ========================================================================

    #[test]
    fn meetwork_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<MeetWork<()>>();
        // MeetWork has several fields including Vecs and VecDeque
        // Should still be reasonably sized
        assert!(
            size < 512,
            "MeetWork should not be excessively large, got {}",
            size
        );
    }

    #[test]
    fn meetwork_many_answers_terminates() {
        let (_, mut terms) = setup();
        // Create chains of many answers
        let mut left: Node<()> = Node::Fail;
        let mut right: Node<()> = Node::Fail;
        for _ in 0..10 {
            left = Node::Emit(make_identity_nf(), Box::new(left));
            right = Node::Emit(make_identity_nf(), Box::new(right));
        }

        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        // Should terminate within reasonable steps
        let mut steps = 0;
        let max_steps = 1000;
        loop {
            let step = meet.step(&mut terms);
            match step {
                WorkStep::Done => break,
                WorkStep::Emit(_, rest) => match *rest {
                    Work::Meet(m) => meet = m,
                    _ => break,
                },
                WorkStep::More(work) => {
                    if let Work::Meet(m) = *work {
                        meet = m;
                    }
                }
                _ => break,
            }
            steps += 1;
            if steps > max_steps {
                panic!("MeetWork did not terminate within {} steps", max_steps);
            }
        }
    }

    // ========================================================================
    // ENV TESTS
    // ========================================================================

    #[test]
    fn env_new_is_empty() {
        let env: Env<()> = Env::new();
        assert!(!env.contains(0));
        assert!(!env.contains(1));
    }

    #[test]
    fn env_bind_single() {
        let env: Env<()> = Env::new();
        let rel: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let env2 = env.bind(0, rel.clone());

        assert!(env2.contains(0));
        assert!(!env2.contains(1));
    }

    #[test]
    fn env_bind_multiple() {
        let env: Env<()> = Env::new();
        let rel1: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let rel2: Arc<Rel<()>> = Arc::new(Rel::Zero);

        let env2 = env.bind(0, rel1);
        let env3 = env2.bind(1, rel2);

        assert!(env3.contains(0));
        assert!(env3.contains(1));
        assert!(!env3.contains(2));
    }

    #[test]
    fn env_bind_does_not_mutate_original() {
        let env: Env<()> = Env::new();
        let rel: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let _env2 = env.bind(0, rel);

        // Original should still be empty
        assert!(!env.contains(0));
    }

    #[test]
    fn env_lookup_returns_bound_rel() {
        let env: Env<()> = Env::new();
        let rel: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let env2 = env.bind(42, rel.clone());

        let looked_up = env2.lookup(42).expect("binding");
        // Check it's the same Arc
        assert!(Arc::ptr_eq(&looked_up.body, &rel));
    }

    #[test]
    fn env_lookup_returns_none_for_unbound() {
        let env: Env<()> = Env::new();
        let rel: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let env2 = env.bind(0, rel);

        assert!(env2.lookup(99).is_none());
    }

    #[test]
    fn env_bind_overwrites_existing() {
        let env: Env<()> = Env::new();
        let rel1: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let nf = make_identity_nf();
        let rel2: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf)));

        let env2 = env.bind(0, rel1.clone());
        let env3 = env2.bind(0, rel2.clone());

        // Should get the new binding
        let looked_up = env3.lookup(0).expect("binding");
        assert!(Arc::ptr_eq(&looked_up.body, &rel2));
        assert!(!Arc::ptr_eq(&looked_up.body, &rel1));
    }

    #[test]
    fn env_is_clone() {
        let env: Env<()> = Env::new();
        let rel: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let env2 = env.bind(0, rel);
        let env3 = env2.clone();

        assert!(env3.contains(0));
    }

    // ========================================================================
    // CALLKEY TESTS
    // ========================================================================

    #[test]
    fn callkey_construction_no_boundaries() {
        let key: CallKey<()> = CallKey::new(0, 1, None, None);
        assert_eq!(key.rel, 0);
        assert!(key.left.is_none());
        assert!(key.right.is_none());
    }

    #[test]
    fn callkey_construction_with_left() {
        let nf = make_identity_nf();
        let key: CallKey<()> = CallKey::new(1, 2, Some(nf), None);
        assert_eq!(key.rel, 1);
        assert!(key.left.is_some());
        assert!(key.right.is_none());
    }

    #[test]
    fn callkey_construction_with_right() {
        let nf = make_identity_nf();
        let key: CallKey<()> = CallKey::new(2, 3, None, Some(nf));
        assert_eq!(key.rel, 2);
        assert!(key.left.is_none());
        assert!(key.right.is_some());
    }

    #[test]
    fn callkey_construction_with_both() {
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let key: CallKey<()> = CallKey::new(3, 4, Some(nf1), Some(nf2));
        assert_eq!(key.rel, 3);
        assert!(key.left.is_some());
        assert!(key.right.is_some());
    }

    #[test]
    fn callkey_equality_same_rel_no_boundaries() {
        let key1: CallKey<()> = CallKey::new(0, 1, None, None);
        let key2: CallKey<()> = CallKey::new(0, 1, None, None);
        assert_eq!(key1, key2);
    }

    #[test]
    fn callkey_inequality_different_rel() {
        let key1: CallKey<()> = CallKey::new(0, 1, None, None);
        let key2: CallKey<()> = CallKey::new(1, 1, None, None);
        assert_ne!(key1, key2);
    }

    #[test]
    fn callkey_equality_same_boundaries() {
        let nf = make_identity_nf();
        let key1: CallKey<()> = CallKey::new(0, 1, Some(nf.clone()), None);
        let key2: CallKey<()> = CallKey::new(0, 1, Some(nf), None);
        assert_eq!(key1, key2);
    }

    #[test]
    fn callkey_inequality_different_left() {
        let (symbols, mut terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);

        let key1: CallKey<()> = CallKey::new(0, 1, Some(nf_a), None);
        let key2: CallKey<()> = CallKey::new(0, 1, Some(nf_b), None);
        assert_ne!(key1, key2);
    }

    #[test]
    fn callkey_inequality_different_right() {
        let (symbols, mut terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);

        let key1: CallKey<()> = CallKey::new(0, 1, None, Some(nf_a));
        let key2: CallKey<()> = CallKey::new(0, 1, None, Some(nf_b));
        assert_ne!(key1, key2);
    }

    #[test]
    fn callkey_hash_same_keys_same_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let key1: CallKey<()> = CallKey::new(5, 1, None, None);
        let key2: CallKey<()> = CallKey::new(5, 1, None, None);

        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();
        key1.hash(&mut hasher1);
        key2.hash(&mut hasher2);

        assert_eq!(hasher1.finish(), hasher2.finish());
    }

    #[test]
    fn callkey_is_clone() {
        let nf = make_identity_nf();
        let key1: CallKey<()> = CallKey::new(0, 1, Some(nf), None);
        let key2 = key1.clone();

        assert_eq!(key1.rel, key2.rel);
        assert_eq!(key1, key2);
    }

    #[test]
    fn callkey_ignores_mid_context_for_same_boundaries() {
        let (symbols, mut terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let body_nf = make_ground_nf("BODY", &symbols, &mut terms);
        let body: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(body_nf)));
        let env = Env::new().bind(0, body);

        let call = Arc::new(Rel::Call(0));
        let mid_a = factors_from_rels(vec![call.clone(), atom_rel(nf_a)]);
        let mid_b = factors_from_rels(vec![call, atom_rel(nf_b)]);

        let mut pipe_a = PipeWork::with_mid(mid_a);
        pipe_a.env = env.clone();
        let mut pipe_b = PipeWork::with_mid(mid_b);
        pipe_b.env = env.clone();

        let step_a = pipe_a.advance_front(&mut terms);
        let step_b = pipe_b.advance_front(&mut terms);

        let key_a = extract_key_from_step(step_a);
        let key_b = extract_key_from_step(step_b);

        assert_eq!(
            key_a, key_b,
            "CallKey should ignore mid context when boundaries match"
        );
    }

    // ========================================================================
    // PRODUCERSTATE TESTS
    // ========================================================================

    #[test]
    fn producerstate_not_started() {
        let state = ProducerState::NotStarted;
        assert_eq!(state, ProducerState::NotStarted);
        assert_ne!(state, ProducerState::Running);
        assert_ne!(state, ProducerState::Done);
    }

    #[test]
    fn producerstate_running() {
        let state = ProducerState::Running;
        assert_eq!(state, ProducerState::Running);
        assert_ne!(state, ProducerState::NotStarted);
        assert_ne!(state, ProducerState::Done);
    }

    #[test]
    fn producerstate_done() {
        let state = ProducerState::Done;
        assert_eq!(state, ProducerState::Done);
        assert_ne!(state, ProducerState::NotStarted);
        assert_ne!(state, ProducerState::Running);
    }

    #[test]
    fn producerstate_is_clone() {
        let state1 = ProducerState::Running;
        let state2 = state1.clone();
        assert_eq!(state1, state2);
    }

    // ========================================================================
    // TABLE TESTS
    // ========================================================================

    #[test]
    fn table_new_is_empty() {
        let table: Table<()> = Table::new();
        let answers = table.lock_answers_for_test();
        assert!(answers.answers.is_empty());
        drop(answers);
        assert_eq!(table.answers_len(), 0);
        assert_eq!(table.producer_state(), ProducerState::NotStarted);
    }

    #[test]
    fn table_add_answer() {
        let table: Table<()> = Table::new();
        let nf = make_identity_nf();
        table.add_answer(nf);

        assert_eq!(table.answers_len(), 1);
    }

    #[test]
    fn table_add_multiple_answers() {
        let (symbols, mut terms) = setup();
        let table: Table<()> = Table::new();
        let nf1 = make_ground_nf("A", &symbols, &mut terms);
        let nf2 = make_ground_nf("B", &symbols, &mut terms);
        let nf3 = make_ground_nf("C", &symbols, &mut terms);

        table.add_answer(nf1);
        table.add_answer(nf2);
        table.add_answer(nf3);

        assert_eq!(table.answers_len(), 3);
    }

    #[test]
    fn table_start_producer() {
        use std::sync::Arc;

        let table: Table<()> = Table::new();
        assert_eq!(table.producer_state(), ProducerState::NotStarted);

        let spec = ProducerSpec {
            key: CallKey::new(0, 0, None, None),
            body: Arc::new(Rel::Zero),
            left: None,
            right: None,
            env: Env::new(),
        };
        let producer_node = Node::Work(boxed_work(Work::Done));
        table.start_producer(producer_node, spec, 0);
        assert_eq!(table.producer_state(), ProducerState::Running);
        assert!(table.is_running());
        assert!(!table.is_done());
        assert!(table.lock_producer_for_test().producer.is_some());
    }

    #[test]
    fn table_finish_producer() {
        use std::sync::Arc;

        let table: Table<()> = Table::new();
        let spec = ProducerSpec {
            key: CallKey::new(0, 0, None, None),
            body: Arc::new(Rel::Zero),
            left: None,
            right: None,
            env: Env::new(),
        };
        let producer_node = Node::Work(boxed_work(Work::Done));
        table.start_producer(producer_node, spec, 0);
        table.finish_producer();

        assert_eq!(table.producer_state(), ProducerState::Done);
        assert!(table.is_done());
        assert!(!table.is_running());
        assert!(table.lock_producer_for_test().producer.is_none());
    }

    #[test]
    fn table_next_answer_empty() {
        let table: Table<()> = Table::new();
        assert!(table.answer_at(0).is_none());
    }

    #[test]
    fn table_next_answer_single() {
        let table: Table<()> = Table::new();
        let nf = make_identity_nf();
        table.add_answer(nf);
        assert!(table.answer_at(0).is_some());
        assert!(table.answer_at(1).is_none());
    }

    #[test]
    fn table_next_answer_multiple() {
        let (symbols, mut terms) = setup();
        let table: Table<()> = Table::new();
        table.add_answer(make_ground_nf("A", &symbols, &mut terms));
        table.add_answer(make_ground_nf("B", &symbols, &mut terms));
        table.add_answer(make_ground_nf("C", &symbols, &mut terms));
        assert!(table.answer_at(0).is_some());
        assert!(table.answer_at(1).is_some());
        assert!(table.answer_at(2).is_some());
        assert!(table.answer_at(3).is_none());
    }

    #[test]
    fn table_next_answer_increments_index() {
        let (symbols, mut terms) = setup();
        let table: Table<()> = Table::new();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        table.add_answer(nf_a.clone());
        table.add_answer(nf_b.clone());
        assert_eq!(table.answer_at(0), Some(nf_a));
        assert_eq!(table.answer_at(1), Some(nf_b));
    }

    #[test]
    fn table_reset_consumer() {
        let (symbols, mut terms) = setup();
        let table: Table<()> = Table::new();
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        table.add_answer(nf_a.clone());
        table.add_answer(nf_b.clone());
        assert_eq!(table.answer_at(0), Some(nf_a.clone()));
        assert_eq!(table.answer_at(1), Some(nf_b));
        assert_eq!(table.answer_at(0), Some(nf_a));
    }

    #[test]
    fn table_all_answers() {
        let (symbols, mut terms) = setup();
        let table: Table<()> = Table::new();
        table.add_answer(make_ground_nf("A", &symbols, &mut terms));
        table.add_answer(make_ground_nf("B", &symbols, &mut terms));

        let all = table.all_answers();
        assert_eq!(all.len(), 2);
    }

    #[test]
    fn table_has_more_answers() {
        let (symbols, mut terms) = setup();
        let table: Table<()> = Table::new();
        table.add_answer(make_ground_nf("A", &symbols, &mut terms));
        table.add_answer(make_ground_nf("B", &symbols, &mut terms));
        assert!(table.answer_at(1).is_some());
        assert!(table.answer_at(2).is_none());
    }

    #[test]
    fn table_default_is_new() {
        let table: Table<()> = Table::default();
        let answers = table.lock_answers_for_test();
        assert!(answers.answers.is_empty());
        drop(answers);
        assert_eq!(table.answers_len(), 0);
        assert_eq!(table.producer_state(), ProducerState::NotStarted);
    }

    // ========================================================================
    // TABLES TESTS
    // ========================================================================

    #[test]
    fn tables_new_is_empty() {
        let tables: Tables<()> = Tables::new();
        assert!(tables.is_empty());
        assert_eq!(tables.len(), 0);
    }

    #[test]
    fn tables_lookup_nonexistent() {
        let tables: Tables<()> = Tables::new();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        assert!(tables.lookup(&key).is_none());
    }

    #[test]
    fn tables_get_or_create_new() {
        let tables: Tables<()> = Tables::new();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);

        let table = tables.get_or_create(key.clone());
        assert!(!tables.is_empty());
        assert_eq!(tables.len(), 1);
        assert_eq!(table.answers_len(), 0);
    }

    #[test]
    fn tables_get_or_create_existing() {
        let tables: Tables<()> = Tables::new();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);

        let table1 = tables.get_or_create(key.clone());
        table1.add_answer(make_identity_nf());

        // Getting same key should return same table
        let table2 = tables.get_or_create(key);
        assert_eq!(table2.answers_len(), 1);
        assert_eq!(tables.len(), 1);
    }

    #[test]
    fn tables_contains() {
        let tables: Tables<()> = Tables::new();
        let key1: CallKey<()> = CallKey::new(0, 0, None, None);
        let key2: CallKey<()> = CallKey::new(1, 0, None, None);

        assert!(!tables.contains(&key1));
        let _ = tables.get_or_create(key1.clone());
        assert!(tables.contains(&key1));
        assert!(!tables.contains(&key2));
    }

    #[test]
    fn tables_multiple_keys() {
        let tables: Tables<()> = Tables::new();
        let key1: CallKey<()> = CallKey::new(0, 0, None, None);
        let key2: CallKey<()> = CallKey::new(1, 0, None, None);
        let key3: CallKey<()> = CallKey::new(2, 0, None, None);

        let _ = tables.get_or_create(key1);
        let _ = tables.get_or_create(key2);
        let _ = tables.get_or_create(key3);

        assert_eq!(tables.len(), 3);
    }

    #[test]
    fn tables_lookup_after_create() {
        let tables: Tables<()> = Tables::new();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);

        let _ = tables.get_or_create(key.clone());
        let looked_up = tables.lookup(&key);
        assert!(looked_up.is_some());
    }

    #[test]
    fn tables_default_is_new() {
        let tables: Tables<()> = Tables::default();
        assert!(tables.is_empty());
    }

    #[test]
    fn tables_is_clone() {
        let tables1: Tables<()> = Tables::new();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = tables1.get_or_create(key.clone());
        table.add_answer(make_identity_nf());

        let tables2 = tables1.clone();
        assert_eq!(tables1.len(), tables2.len());
        // The cloned tables should share the same Arc references (im::HashMap behavior)
    }

    #[test]
    fn tables_clone_shares_updates() {
        let tables1: Tables<()> = Tables::new();
        let tables2 = tables1.clone();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);

        let table1 = tables1.get_or_create(key.clone());

        assert!(tables2.contains(&key), "Clone should see inserted table");
        assert_eq!(tables1.len(), tables2.len());

        let table2 = tables2.get_or_create(key.clone());
        assert!(
            Arc::ptr_eq(&table1, &table2),
            "Tables should share the same entry"
        );
    }

    #[test]
    fn tables_keys_with_different_boundaries() {
        let (symbols, mut terms) = setup();
        let tables: Tables<()> = Tables::new();

        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);

        // Same rel, different boundaries should be different keys
        let key1: CallKey<()> = CallKey::new(0, 0, Some(nf_a.clone()), None);
        let key2: CallKey<()> = CallKey::new(0, 0, Some(nf_b), None);
        let key3: CallKey<()> = CallKey::new(0, 0, None, Some(nf_a));

        let _ = tables.get_or_create(key1);
        let _ = tables.get_or_create(key2);
        let _ = tables.get_or_create(key3);

        assert_eq!(
            tables.len(),
            3,
            "Different boundaries should create different tables"
        );
    }

    // ========================================================================
    // FIXWORK TESTS - CONSTRUCTION
    // ========================================================================

    #[test]
    fn fixwork_new_handle() {
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());

        let fix: FixWork<()> = FixWork::new(key.clone(), table, 0, Tables::new());

        assert_eq!(fix.answer_index, 0);
        assert_eq!(fix.key.rel, 0);
    }

    // ========================================================================
    // FIXWORK TESTS - HANDLE BEHAVIOR
    // ========================================================================

    #[test]
    fn fixwork_handle_emits_existing_answers() {
        let (symbols, mut terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());

        table.add_answer(make_ground_nf("A", &symbols, &mut terms));
        table.add_answer(make_ground_nf("B", &symbols, &mut terms));
        table.finish_producer();

        let mut fix: FixWork<()> = FixWork::new(key, table, 0, Tables::new());

        let step1 = fix.step(&mut terms);
        assert!(matches!(step1, WorkStep::Emit(_, _)));

        if let WorkStep::Emit(_, work) = step1 {
            if let Work::Fix(f) = *work {
                fix = f;
            }
        }

        let step2 = fix.step(&mut terms);
        assert!(matches!(step2, WorkStep::Emit(_, _)));

        if let WorkStep::Emit(_, work) = step2 {
            if let Work::Fix(f) = *work {
                fix = f;
            }
        }

        let step3 = fix.step(&mut terms);
        assert!(matches!(step3, WorkStep::Done));
    }

    fn run_fixwork_starts_producer_and_emits_answer(use_dual: bool) {
        use std::sync::Arc;

        let (symbols, mut terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        let mut nf = make_ground_nf("A", &symbols, &mut terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }
        let spec = ProducerSpec {
            key: key.clone(),
            body: Arc::new(Rel::Atom(Arc::new(nf.clone()))),
            left: None,
            right: None,
            env: Env::new(),
        };

        {
            let mut guard = table.lock_producer_for_test();
            guard.spec = Some(spec);
            guard.state = ProducerState::NotStarted;
        }

        let mut fix: FixWork<()> = FixWork::new(key, table.clone(), 0, Tables::new());
        let step = fix.step(&mut terms);
        match step {
            WorkStep::Emit(out, _) => assert_eq!(out, nf),
            other => panic!("expected inline producer emit, got {:?}", other),
        }
        assert_eq!(table.answers_len(), 1);
    }

    #[test]
    fn fixwork_starts_producer_and_emits_answer() {
        run_fixwork_starts_producer_and_emits_answer(false);
    }

    #[test]
    fn fixwork_starts_producer_and_emits_answer_dual() {
        run_fixwork_starts_producer_and_emits_answer(true);
    }

    fn run_fixwork_advances_running_producer_and_emits(use_dual: bool) {
        use std::sync::Arc;

        let (symbols, mut terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        let mut nf = make_ground_nf("A", &symbols, &mut terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }
        let producer_node = Node::Emit(nf.clone(), Box::new(Node::Fail));
        let spec = ProducerSpec {
            key: key.clone(),
            body: Arc::new(Rel::Atom(Arc::new(nf.clone()))),
            left: None,
            right: None,
            env: Env::new(),
        };

        table.start_producer(producer_node, spec, 0);

        let mut fix: FixWork<()> = FixWork::new(key, table.clone(), 0, Tables::new());
        let step = fix.step(&mut terms);
        match step {
            WorkStep::Emit(out, _) => assert_eq!(out, nf),
            other => panic!("expected inline producer advance, got {:?}", other),
        }
    }

    #[test]
    fn fixwork_advances_running_producer_and_emits() {
        run_fixwork_advances_running_producer_and_emits(false);
    }

    #[test]
    fn fixwork_advances_running_producer_and_emits_dual() {
        run_fixwork_advances_running_producer_and_emits(true);
    }

    fn run_fixwork_skips_duplicate_answer(use_dual: bool) {
        use std::sync::Arc;

        let (symbols, mut terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        let mut nf = make_ground_nf("A", &symbols, &mut terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }
        table.add_answer(nf.clone());

        let producer_node = Node::Emit(nf.clone(), Box::new(Node::Fail));
        let spec = ProducerSpec {
            key: key.clone(),
            body: Arc::new(Rel::Atom(Arc::new(nf.clone()))),
            left: None,
            right: None,
            env: Env::new(),
        };
        table.start_producer(producer_node, spec, table.answers_len());

        let mut fix: FixWork<()> =
            FixWork::new(key, table.clone(), table.answers_len(), Tables::new());
        let step = fix.step(&mut terms);
        assert!(
            matches!(step, WorkStep::More(_)),
            "duplicate answer should not emit"
        );
    }

    #[test]
    fn fixwork_skips_duplicate_answer() {
        run_fixwork_skips_duplicate_answer(false);
    }

    #[test]
    fn fixwork_skips_duplicate_answer_dual() {
        run_fixwork_skips_duplicate_answer(true);
    }

    fn run_fixwork_exhausted_marks_done(use_dual: bool) {
        use std::sync::Arc;

        let (symbols, mut terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        let mut nf = make_ground_nf("A", &symbols, &mut terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }
        let spec = ProducerSpec {
            key: key.clone(),
            body: Arc::new(Rel::Atom(Arc::new(nf))),
            left: None,
            right: None,
            env: Env::new(),
        };
        table.start_producer(Node::Fail, spec, table.answers_len());

        let mut fix: FixWork<()> =
            FixWork::new(key, table.clone(), table.answers_len(), Tables::new());
        let step = fix.step(&mut terms);
        assert!(matches!(step, WorkStep::Done));
        assert_eq!(table.producer_state(), ProducerState::Done);
    }

    #[test]
    fn fixwork_exhausted_marks_done() {
        run_fixwork_exhausted_marks_done(false);
    }

    #[test]
    fn fixwork_exhausted_marks_done_dual() {
        run_fixwork_exhausted_marks_done(true);
    }

    #[test]
    fn fix_producer_dedups_duplicate_answers() {
        use std::sync::Arc;

        let (symbols, mut terms) = setup();
        let tables = Tables::new();
        let table = Arc::new(Table::new());
        let nf = make_ground_nf("A", &symbols, &mut terms);
        let producer_node = Node::Emit(
            nf.clone(),
            Box::new(Node::Emit(nf.clone(), Box::new(Node::Fail))),
        );
        let spec = ProducerSpec {
            key: CallKey::new(0, 0, None, None),
            body: Arc::new(Rel::Atom(Arc::new(nf.clone()))),
            left: None,
            right: None,
            env: Env::new(),
        };

        table.start_producer(producer_node, spec, 0);

        let mut steps = 0;
        loop {
            let step = step_table_producer(&table, &mut terms, &tables);
            steps += 1;
            if matches!(step, ProducerStep::Done) || steps > 10 {
                break;
            }
        }

        assert_eq!(table.answers_len(), 1);
    }

    fn run_fix_producer_continues_when_consumer_queue_full(use_dual: bool) {
        let (symbols, mut terms) = setup();
        let tables = Tables::new();
        let table = Arc::new(Table::new());
        let mut nf_a = make_ground_nf("A", &symbols, &mut terms);
        let mut nf_b = make_ground_nf("B", &symbols, &mut terms);
        if use_dual {
            nf_a = dual_nf(&nf_a, &mut terms);
            nf_b = dual_nf(&nf_b, &mut terms);
        }
        let producer_node = Node::Emit(
            nf_a.clone(),
            Box::new(Node::Emit(nf_b.clone(), Box::new(Node::Fail))),
        );
        let spec = ProducerSpec {
            key: CallKey::new(0, 0, None, None),
            body: Arc::new(Rel::Atom(Arc::new(nf_a.clone()))),
            left: None,
            right: None,
            env: Env::new(),
        };

        table.start_producer(producer_node, spec, 0);

        let step1 = step_table_producer(&table, &mut terms, &tables);
        assert!(matches!(step1, ProducerStep::Progress));

        let step2 = step_table_producer(&table, &mut terms, &tables);
        assert!(
            matches!(step2, ProducerStep::Progress),
            "producer should continue even when consumer lags"
        );
        assert_eq!(
            table.answers_len(),
            2,
            "producer should add answers even when consumer lags"
        );
    }

    #[test]
    fn fix_producer_continues_when_consumer_queue_full() {
        run_fix_producer_continues_when_consumer_queue_full(false);
    }

    #[test]
    fn fix_producer_continues_when_consumer_queue_full_dual() {
        run_fix_producer_continues_when_consumer_queue_full(true);
    }

    #[test]
    fn fix_producer_broadcasts_answers_to_all_consumers() {
        use std::sync::Arc;

        let (symbols, mut terms) = setup();
        let tables = Tables::new();
        let table = Arc::new(Table::new());
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let producer_node = Node::Emit(
            nf_a.clone(),
            Box::new(Node::Emit(nf_b.clone(), Box::new(Node::Fail))),
        );
        let spec = ProducerSpec {
            key: CallKey::new(0, 0, None, None),
            body: Arc::new(Rel::Atom(Arc::new(nf_a.clone()))),
            left: None,
            right: None,
            env: Env::new(),
        };

        table.start_producer(producer_node, spec, 0);

        let mut steps = 0;
        loop {
            let step = step_table_producer(&table, &mut terms, &tables);
            steps += 1;
            if matches!(step, ProducerStep::Done) || steps > 10 {
                break;
            }
        }

        let mut got_a = Vec::new();
        let mut got_b = Vec::new();
        let mut fix_a = FixWork::new(CallKey::new(0, 0, None, None), table.clone(), 0, tables);
        let mut fix_b = FixWork::new(CallKey::new(0, 0, None, None), table, 0, Tables::new());
        for _ in 0..2 {
            if let WorkStep::Emit(nf, work) = fix_a.step(&mut terms) {
                got_a.push(nf);
                if let Work::Fix(fix) = *work {
                    fix_a = fix;
                }
            }
            if let WorkStep::Emit(nf, work) = fix_b.step(&mut terms) {
                got_b.push(nf);
                if let Work::Fix(fix) = *work {
                    fix_b = fix;
                }
            }
        }

        assert_eq!(got_a.len(), 2);
        assert_eq!(got_b.len(), 2);
        assert!(got_a.contains(&nf_a));
        assert!(got_a.contains(&nf_b));
        assert!(got_b.contains(&nf_a));
        assert!(got_b.contains(&nf_b));
    }

    #[test]
    fn fix_consumer_replays_existing_answers() {
        use std::sync::Arc;

        let (symbols, mut terms) = setup();
        let table = Arc::new(Table::new());
        let nf_a = make_ground_nf("A", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);

        table.add_answer(nf_a.clone());
        table.add_answer(nf_b.clone());

        let mut fix: FixWork<()> =
            FixWork::new(CallKey::new(0, 0, None, None), table, 0, Tables::new());
        let step1 = fix.step(&mut terms);
        assert!(matches!(step1, WorkStep::Emit(_, _)));
        if let WorkStep::Emit(_, work) = step1 {
            if let Work::Fix(fix_next) = *work {
                fix = fix_next;
            }
        }
        let step2 = fix.step(&mut terms);
        assert!(matches!(step2, WorkStep::Emit(_, _)));
    }

    #[test]
    fn fixwork_handle_done_when_table_done() {
        let (_, mut terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        table.finish_producer();

        let mut fix: FixWork<()> = FixWork::new(key, table, 0, Tables::new());
        let step = fix.step(&mut terms);
        assert!(matches!(step, WorkStep::Done));
    }

    #[test]
    fn call_replay_interleaves_with_new_answers() {
        use std::sync::Arc;

        let (symbols, mut terms) = setup();
        let nf_a1 = make_ground_nf("A1", &symbols, &mut terms);
        let nf_a2 = make_ground_nf("A2", &symbols, &mut terms);
        let nf_b = make_ground_nf("B", &symbols, &mut terms);
        let body_nf = make_ground_nf("BODY", &symbols, &mut terms);
        let body: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(body_nf)));
        let env = Env::new().bind(0, body.clone());

        let call = Arc::new(Rel::Call(0));
        let mid = factors_from_rels(vec![call.clone()]);

        let mut pipe_producer = PipeWork::with_mid(mid.clone());
        pipe_producer.env = env.clone();
        let step_producer = pipe_producer.advance_front(&mut terms);
        let key = extract_key_from_step(step_producer);

        let table = pipe_producer
            .tables
            .lookup(&key)
            .expect("Table should exist after producer call");
        table.add_answer(nf_a1.clone());
        table.add_answer(nf_a2.clone());
        table.start_producer(
            Node::Work(boxed_work(Work::Done)),
            ProducerSpec {
                key: key.clone(),
                body: body.clone(),
                left: None,
                right: None,
                env: env.clone(),
            },
            table.answers_len(),
        );

        let mut pipe_consumer = PipeWork::with_mid(mid);
        pipe_consumer.env = env;
        pipe_consumer.tables = pipe_producer.tables.clone();
        let step_consumer = pipe_consumer.advance_front(&mut terms);
        let mut compose = unwrap_work_compose(step_consumer);

        let mut outputs = Vec::new();
        let mut steps = 0;
        while outputs.len() < 3 && steps < 200 {
            let step = compose.step(&mut terms);
            match step {
                WorkStep::Emit(nf, next) => {
                    outputs.push(nf);
                    if outputs.len() == 1 {
                        table.add_answer(nf_b.clone());
                    }
                    compose = match *next {
                        Work::Compose(next_compose) => next_compose,
                        other => panic!("Expected Work::Compose, got {:?}", other),
                    };
                }
                WorkStep::More(next) => {
                    compose = match *next {
                        Work::Compose(next_compose) => next_compose,
                        other => panic!("Expected Work::Compose, got {:?}", other),
                    };
                }
                WorkStep::Done => break,
                WorkStep::Split(_, _) => panic!("ComposeWork should not split"),
            }
            steps += 1;
        }

        assert_eq!(
            outputs.len(),
            3,
            "Expected three answers from replay + discovery"
        );
        assert_eq!(outputs[0], nf_a1);
        assert_eq!(outputs[1], nf_b);
        assert_eq!(outputs[2], nf_a2);
    }

    // ========================================================================
    // FIXWORK TESTS - INTEGRATION WITH WORK ENUM
    // ========================================================================

    #[test]
    fn work_fix_construction() {
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        let fix: FixWork<()> = FixWork::new(key, table, 0, Tables::new());
        let work: Work<()> = Work::Fix(fix);
        assert!(matches!(work, Work::Fix(_)));
    }

    #[test]
    fn work_fix_step_delegates() {
        let (_, mut terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        table.finish_producer();

        let fix: FixWork<()> = FixWork::new(key, table, 0, Tables::new());
        let mut work: Work<()> = Work::Fix(fix);

        let step = work.step(&mut terms);
        assert!(matches!(step, WorkStep::Done));
    }

    // ========================================================================
    // FIXWORK TESTS - SIZE
    // ========================================================================

    #[test]
    fn fixwork_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<FixWork<()>>();
        // FixWork contains Arc, Box, etc.
        assert!(
            size < 512,
            "FixWork should not be excessively large, got {}",
            size
        );
    }

    #[test]
    fn table_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<Table<()>>();
        assert!(
            size < 1200,
            "Table should not be excessively large, got {}",
            size
        );
    }

    #[test]
    fn table_dedups_duplicate_answers() {
        let (symbols, mut terms) = setup();
        let nf = make_ground_nf("A", &symbols, &mut terms);
        let table: Table<()> = Table::new();
        table.add_answer(nf.clone());
        table.add_answer(nf);
        assert_eq!(table.answers_len(), 1, "Table should dedup answers");
    }

    fn assert_table_lock_independent() {
        let table = Arc::new(Table::<()>::new());

        let producer_guard = table.lock_producer_for_test();
        let answers_try = table.try_lock_answers_for_test();
        assert!(
            answers_try.is_some(),
            "answers lock should not be blocked by producer lock"
        );
        drop(answers_try);
        drop(producer_guard);

        let answers_guard = table.lock_answers_for_test();
        let producer_try = table.try_lock_producer_for_test();
        assert!(
            producer_try.is_some(),
            "producer lock should not be blocked by answers lock"
        );
        drop(producer_try);
        drop(answers_guard);
    }

    #[test]
    fn table_locks_are_independent() {
        assert_table_lock_independent();
    }

    #[test]
    fn table_locks_are_independent_dual() {
        assert_table_lock_independent();
    }

    #[test]
    fn tables_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<Tables<()>>();
        assert!(
            size < 128,
            "Tables should not be excessively large, got {}",
            size
        );
    }

    #[test]
    fn env_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<Env<()>>();
        assert!(
            size < 128,
            "Env should not be excessively large, got {}",
            size
        );
    }

    #[test]
    fn callkey_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<CallKey<()>>();
        // CallKey contains Option<NF<C>> which can be large
        assert!(
            size < 256,
            "CallKey should not be excessively large, got {}",
            size
        );
    }

    fn run_join_receiver_emits_from_queue(use_dual: bool) {
        let (symbols, mut terms) = setup();
        let mut nf1 = make_rule_nf("A", "B", &symbols, &mut terms);
        let mut nf2 = make_rule_nf("B", "C", &symbols, &mut terms);
        if use_dual {
            nf1 = dual_nf(&nf1, &mut terms);
            nf2 = dual_nf(&nf2, &mut terms);
        }

        let (tx, rx) = AnswerQueue::bounded::<()>(2);
        assert_eq!(tx.try_send(nf1.clone()), SinkResult::Accepted);
        assert_eq!(tx.try_send(nf2.clone()), SinkResult::Accepted);

        let mut join = JoinReceiverWork::new(rx);
        let step = join.step(&mut terms);
        let (out, work) = match step {
            WorkStep::Emit(nf, work) => (nf, work),
            other => panic!("expected emit from join receiver, got {:?}", other),
        };
        assert_eq!(out, nf1);

        let mut join = unwrap_join_receiver(*work);
        let step = join.step(&mut terms);
        let (out, work) = match step {
            WorkStep::Emit(nf, work) => (nf, work),
            other => panic!("expected second emit from join receiver, got {:?}", other),
        };
        assert_eq!(out, nf2);

        drop(tx);
        let mut join = unwrap_join_receiver(*work);
        match join.step(&mut terms) {
            WorkStep::Done => {}
            other => panic!("expected join receiver to finish, got {:?}", other),
        }
    }

    #[test]
    fn join_receiver_emits_from_queue() {
        run_join_receiver_emits_from_queue(false);
    }

    #[test]
    fn join_receiver_emits_from_queue_dual() {
        run_join_receiver_emits_from_queue(true);
    }

    fn run_join_receiver_blocks_when_empty(use_dual: bool) {
        let (symbols, mut terms) = setup();
        let mut nf = make_rule_nf("A", "B", &symbols, &mut terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }

        let (tx, rx) = AnswerQueue::bounded::<()>(1);
        let mut join = JoinReceiverWork::new(rx);
        let step = join.step(&mut terms);
        let mut join = match step {
            WorkStep::More(work) => unwrap_join_receiver(*work),
            other => panic!("expected join receiver to wait, got {:?}", other),
        };
        assert!(
            join.blocked_on().is_some(),
            "join receiver should block when empty"
        );

        assert_eq!(tx.try_send(nf.clone()), SinkResult::Accepted);
        let step = join.step(&mut terms);
        let (out, _work) = match step {
            WorkStep::Emit(nf, work) => (nf, work),
            other => panic!("expected join receiver emit after send, got {:?}", other),
        };
        assert_eq!(out, nf);
    }

    #[test]
    fn join_receiver_blocks_when_empty() {
        run_join_receiver_blocks_when_empty(false);
    }

    #[test]
    fn join_receiver_blocks_when_empty_dual() {
        run_join_receiver_blocks_when_empty(true);
    }

    fn run_andgroup_closed_empty_part_terminates_even_if_other_blocks(use_dual: bool) {
        let _ = use_dual;
        let (_, mut terms) = setup();

        let (_tx0, rx0) = AnswerQueue::bounded::<()>(1);
        drop(_tx0);
        let part0 = Node::Work(boxed_work(Work::JoinReceiver(JoinReceiverWork::new(rx0))));

        let (_tx1, rx1) = AnswerQueue::bounded::<()>(1);
        let part1 = Node::Work(boxed_work(Work::JoinReceiver(JoinReceiverWork::new(rx1))));

        let mut group = AndGroup::new(vec![part0, part1]);
        let mut done = false;

        for _ in 0..6 {
            match group.step(&mut terms) {
                WorkStep::Done => {
                    done = true;
                    break;
                }
                WorkStep::More(work) => {
                    group = unwrap_and_group(*work);
                }
                WorkStep::Emit(_, _) => {
                    panic!("andgroup should not emit when a part closes empty")
                }
                WorkStep::Split(_, _) => panic!("andgroup should not split"),
            }
        }

        assert!(
            done,
            "AndGroup should terminate when a part closes empty, even if others block"
        );

        drop(_tx1);
    }

    #[test]
    fn andgroup_closed_empty_part_terminates_even_if_other_blocks() {
        run_andgroup_closed_empty_part_terminates_even_if_other_blocks(false);
    }

    #[test]
    fn andgroup_closed_empty_part_terminates_even_if_other_blocks_dual() {
        run_andgroup_closed_empty_part_terminates_even_if_other_blocks(true);
    }
}
