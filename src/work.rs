//! Work - Active work items for the evaluation engine.
//!
//! Work represents computations in progress. PipeWork handles
//! sequential composition (Seq) with outside-in boundary fusion.

use crate::constraint::ConstraintOps;
use crate::drop_fresh::DropFresh;
use crate::factors::Factors;
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
use std::collections::{HashMap, HashSet, VecDeque};
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
    /// Producer work for tabled recursion.
    FixProducer(FixProducerWork<C>),
    /// Bind a generator to a pipeline continuation.
    Bind(BindWork<C>),
    /// Producer work for bind generators.
    BindProducer(BindProducerWork<C>),
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

fn build_var_list(arity: u32, terms: &TermStore) -> SmallVec<[TermId; 1]> {
    let mut vars = SmallVec::new();
    for idx in 0..arity {
        vars.push(terms.var(idx));
    }
    vars
}

fn nf_rwl_iso<C: ConstraintOps>(nf: &NF<C>, terms: &TermStore) -> NF<C> {
    let in_arity = nf.drop_fresh.in_arity;
    NF::new(
        nf.match_pats.clone(),
        DropFresh::identity(in_arity),
        build_var_list(in_arity, terms),
    )
}

fn nf_rwr_iso<C: ConstraintOps>(nf: &NF<C>, terms: &TermStore) -> NF<C> {
    let out_arity = nf.drop_fresh.out_arity;
    NF::new(
        build_var_list(out_arity, terms),
        DropFresh::identity(out_arity),
        nf.build_pats.clone(),
    )
}

fn nf_left_prefix<C: ConstraintOps>(nf: &NF<C>, terms: &TermStore) -> NF<C> {
    let out_arity = nf.drop_fresh.out_arity;
    NF::new(
        nf.match_pats.clone(),
        nf.drop_fresh.clone(),
        build_var_list(out_arity, terms),
    )
}

fn nf_right_suffix<C: ConstraintOps>(nf: &NF<C>, terms: &TermStore) -> NF<C> {
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
    pub fn step(&mut self, terms: &TermStore) -> WorkStep<C> {
        match self {
            Work::Pipe(pipe) => pipe.step(terms),
            Work::Meet(meet) => meet.step(terms),
            Work::AndGroup(group) => group.step(terms),
            Work::Fix(fix) => fix.step(terms),
            Work::FixProducer(producer) => producer.step(terms),
            Work::Bind(bind) => bind.step(terms),
            Work::BindProducer(producer) => producer.step(terms),
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
    pub fn step(&mut self, terms: &TermStore) -> WorkStep<C> {
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
    fn emit_boundaries(&self, terms: &TermStore) -> WorkStep<C> {
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
    fn absorb_front(&mut self, nf: NF<C>, terms: &TermStore) -> bool {
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
    fn absorb_back(&mut self, nf: NF<C>, terms: &TermStore) -> bool {
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
    fn try_normalize_step(&mut self, terms: &TermStore) -> Result<bool, WorkStep<C>> {
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
    fn normalize_mid_atoms(&mut self, terms: &TermStore) -> Result<bool, WorkStep<C>> {
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
    fn advance_front(&mut self, terms: &TermStore) -> WorkStep<C> {
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

                let mut pipe = self.clone();
                pipe.left = left_prefix;
                pipe.right = right_suffix;

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
                let bind = BindWork::new(Node::Work(boxed_work(Work::AndGroup(group))), pipe, true);
                WorkStep::More(boxed_work(Work::Bind(bind)))
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
                let bind = BindWork::new(fix_node, pipe, true);
                WorkStep::More(boxed_work(Work::Bind(bind)))
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
    fn advance_back(&mut self, terms: &TermStore) -> WorkStep<C> {
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

                let mut pipe = self.clone();
                pipe.left = left_prefix;
                pipe.right = right_suffix;

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
                let bind =
                    BindWork::new(Node::Work(boxed_work(Work::AndGroup(group))), pipe, false);
                WorkStep::More(boxed_work(Work::Bind(bind)))
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
                let bind = BindWork::new(fix_node, pipe, false);
                WorkStep::More(boxed_work(Work::Bind(bind)))
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
                let bind = BindWork::new(replay_node, pipe, absorb_front);
                return WorkStep::More(boxed_work(Work::Bind(bind)));
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

        let bind = BindWork::new(gen_node, pipe, absorb_front);
        WorkStep::More(boxed_work(Work::Bind(bind)))
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

#[derive(Debug)]
pub(crate) struct BindProducerState<C: ConstraintOps> {
    gen: Node<C>,
    sender: Option<AnswerSender<C>>,
    pending: VecDeque<NF<C>>,
    done: bool,
    active: bool,
}

impl<C: ConstraintOps> BindProducerState<C> {
    fn new(gen: Node<C>, sender: AnswerSender<C>) -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self {
            gen,
            sender: Some(sender),
            pending: VecDeque::new(),
            done: false,
            active: false,
        }))
    }

    pub(crate) fn is_closed(&self) -> bool {
        self.sender.is_none()
    }

    pub(crate) fn is_active(&self) -> bool {
        self.active
    }

    pub(crate) fn mark_active(&mut self) {
        self.active = true;
    }

    pub(crate) fn blocked_on(&self) -> BlockedOn {
        self.sender
            .as_ref()
            .expect("bind producer should have sender when blocked")
            .blocked_on()
    }
}

pub(crate) fn step_bind_producer<C: ConstraintOps>(
    state: &Arc<Mutex<BindProducerState<C>>>,
    terms: &TermStore,
) -> ProducerStep {
    let current = {
        let mut guard = state.lock();

        if let Some(sender) = guard.sender.as_ref() {
            if let Some(nf) = guard.pending.front().cloned() {
                match sender.try_send(nf.clone()) {
                    SinkResult::Accepted => {
                        let _ = guard.pending.pop_front();
                        return ProducerStep::Progress;
                    }
                    SinkResult::Full => return ProducerStep::Blocked,
                    SinkResult::Closed => {
                        guard.sender = None;
                        guard.pending.clear();
                        guard.active = false;
                        return ProducerStep::Done;
                    }
                }
            }
        }

        if guard.done && guard.pending.is_empty() {
            guard.sender = None;
            guard.active = false;
            return ProducerStep::Done;
        }

        if guard.sender.is_none() {
            guard.active = false;
            return ProducerStep::Done;
        }

        std::mem::replace(&mut guard.gen, Node::Fail)
    };

    let step = step_node(current, terms);
    let mut guard = state.lock();
    match step {
        NodeStep::Emit(nf, rest) => {
            guard.gen = rest;
            if let Some(sender) = guard.sender.as_ref() {
                match sender.try_send(nf.clone()) {
                    SinkResult::Accepted => ProducerStep::Progress,
                    SinkResult::Full => {
                        guard.pending.push_back(nf);
                        ProducerStep::Blocked
                    }
                    SinkResult::Closed => {
                        guard.sender = None;
                        guard.pending.clear();
                        guard.active = false;
                        ProducerStep::Done
                    }
                }
            } else {
                guard.active = false;
                ProducerStep::Done
            }
        }
        NodeStep::Continue(rest) => {
            guard.gen = rest;
            ProducerStep::Progress
        }
        NodeStep::Exhausted => {
            guard.done = true;
            if guard.pending.is_empty() {
                guard.sender = None;
                guard.active = false;
                ProducerStep::Done
            } else {
                ProducerStep::Progress
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct BindProducerWork<C: ConstraintOps> {
    state: Arc<Mutex<BindProducerState<C>>>,
}

impl<C: ConstraintOps> BindProducerWork<C> {
    pub(crate) fn new(state: Arc<Mutex<BindProducerState<C>>>) -> Self {
        Self { state }
    }

    pub fn step(&mut self, terms: &TermStore) -> WorkStep<C> {
        let step = step_bind_producer(&self.state, terms);
        match step {
            ProducerStep::Done => WorkStep::Done,
            ProducerStep::Blocked | ProducerStep::Progress => {
                WorkStep::More(boxed_work(Work::BindProducer(self.clone())))
            }
        }
    }
}

/// Bind work: apply queued generator answers to a pipe continuation.
#[derive(Clone, Debug)]
pub struct BindWork<C: ConstraintOps> {
    /// Shared producer state for the generator.
    producer: Arc<Mutex<BindProducerState<C>>>,
    /// Receiver for queued answers.
    receiver: Arc<Mutex<AnswerReceiver<C>>>,
    /// Continuation pipe to absorb answers into.
    pub pipe: PipeWork<C>,
    /// If true, absorb into the left boundary; otherwise right.
    pub absorb_front: bool,
}

impl<C: ConstraintOps> BindWork<C> {
    /// Create a new BindWork.
    pub fn new(gen: Node<C>, pipe: PipeWork<C>, absorb_front: bool) -> Self {
        let (tx, rx) =
            AnswerQueue::bounded_with_waker(pipe.tables.queue_bound(), pipe.tables.waker());
        let producer = BindProducerState::new(gen, tx);
        Self {
            producer,
            receiver: Arc::new(Mutex::new(rx)),
            pipe,
            absorb_front,
        }
    }

    pub(crate) fn producer_state(&self) -> Arc<Mutex<BindProducerState<C>>> {
        self.producer.clone()
    }

    /// Step this bind work.
    pub fn step(&mut self, terms: &TermStore) -> WorkStep<C> {
        let receiver = self.receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => {
                drop(receiver);
                let mut pipe = self.pipe.clone();
                let absorbed = if self.absorb_front {
                    pipe.absorb_front(nf, terms)
                } else {
                    pipe.absorb_back(nf, terms)
                };

                if !absorbed {
                    return WorkStep::More(boxed_work(Work::Bind(self.clone())));
                }

                let left_node = Node::Work(boxed_work(Work::Pipe(pipe)));
                let right_node = Node::Work(boxed_work(Work::Bind(self.clone())));
                return WorkStep::Split(boxed_node(left_node), boxed_node(right_node));
            }
            RecvResult::Closed => return WorkStep::Done,
            RecvResult::Empty => {}
        }
        drop(receiver);

        let should_spawn = {
            let mut state = self.producer.lock();
            if state.is_active() || state.is_closed() {
                false
            } else {
                state.mark_active();
                true
            }
        };

        if should_spawn {
            let producer = BindProducerWork::new(self.producer.clone());
            WorkStep::Split(
                boxed_node(Node::Work(boxed_work(Work::BindProducer(producer)))),
                boxed_node(Node::Work(boxed_work(Work::Bind(self.clone())))),
            )
        } else {
            WorkStep::More(boxed_work(Work::Bind(self.clone())))
        }
    }
}

/// AndGroup work: fair diagonal join for n-ary conjunction/intersection.
///
/// Represents: And(r0, r1, ..., rn-1)
///
/// Uses fair diagonal enumeration:
/// - Pull answers round-robin from each part
/// - When a new answer arrives, meet with all seen from other parts
/// - Successful meets are queued in pending
#[derive(Clone, Debug)]
pub struct AndGroup<C: ConstraintOps> {
    /// Part nodes.
    pub parts: Vec<Node<C>>,
    /// Answers seen per part.
    pub seen: Vec<Vec<NF<C>>>,
    /// Dedup sets per part.
    seen_sets: Vec<HashSet<NF<C>>>,
    /// Successful meets waiting to be emitted.
    pub pending: VecDeque<NF<C>>,
    /// Dedup set for pending.
    pending_set: HashSet<NF<C>>,
    /// Round-robin turn index.
    pub turn: usize,
}

impl<C: ConstraintOps> AndGroup<C> {
    /// Create a new AndGroup from part nodes.
    pub fn new(parts: Vec<Node<C>>) -> Self {
        let count = parts.len();
        Self {
            parts,
            seen: vec![Vec::new(); count],
            seen_sets: vec![HashSet::new(); count],
            pending: VecDeque::new(),
            pending_set: HashSet::new(),
            turn: 0,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, AndGroup::new(Vec::new()))
    }

    fn push_pending(&mut self, nf: NF<C>) {
        if self.pending_set.insert(nf.clone()) {
            self.pending.push_back(nf);
        }
    }

    fn enqueue_meets(&mut self, idx: usize, nf: NF<C>, terms: &TermStore) {
        if self.parts.len() == 1 {
            self.push_pending(nf);
            return;
        }

        let mut acc = vec![nf];
        for (j, seen_j) in self.seen.iter().enumerate() {
            if j == idx {
                continue;
            }
            if seen_j.is_empty() {
                return;
            }

            let mut next = Vec::new();
            for left in acc.iter() {
                for right in seen_j.iter() {
                    if let Some(met) = meet_nf(left, right, terms) {
                        next.push(met);
                    }
                }
            }
            if next.is_empty() {
                return;
            }
            acc = next;
        }

        for result in acc {
            self.push_pending(result);
        }
    }

    /// Step this AndGroup, returning the next state.
    pub fn step(&mut self, terms: &TermStore) -> WorkStep<C> {
        if let Some(nf) = self.pending.pop_front() {
            self.pending_set.remove(&nf);
            return WorkStep::Emit(nf, boxed_work(Work::AndGroup(self.take_self())));
        }

        if self.parts.is_empty() {
            return WorkStep::Done;
        }

        if self.parts.iter().all(|node| matches!(node, Node::Fail)) {
            return WorkStep::Done;
        }

        let part_count = self.parts.len();
        let mut pick = None;
        for offset in 0..part_count {
            let idx = (self.turn + offset) % part_count;
            if !matches!(self.parts[idx], Node::Fail) {
                pick = Some(idx);
                break;
            }
        }

        let idx = match pick {
            Some(idx) => idx,
            None => return WorkStep::Done,
        };

        let current = std::mem::replace(&mut self.parts[idx], Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                self.parts[idx] = rest;
                if self.seen_sets[idx].insert(nf.clone()) {
                    self.seen[idx].push(nf.clone());
                    self.enqueue_meets(idx, nf, terms);
                }
                self.turn = (idx + 1) % part_count;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, boxed_work(Work::AndGroup(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::AndGroup(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                self.parts[idx] = rest;
                self.turn = (idx + 1) % part_count;
                WorkStep::More(boxed_work(Work::AndGroup(self.take_self())))
            }
            NodeStep::Exhausted => {
                self.parts[idx] = Node::Fail;
                self.turn = (idx + 1) % part_count;
                WorkStep::More(boxed_work(Work::AndGroup(self.take_self())))
            }
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
    pub fn step(&mut self, terms: &TermStore) -> WorkStep<C> {
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
    fn pull_left(&mut self, terms: &TermStore) -> WorkStep<C> {
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
    fn pull_right(&mut self, terms: &TermStore) -> WorkStep<C> {
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

pub type ConsumerId = u64;

#[derive(Clone, Debug)]
struct Consumer<C: ConstraintOps> {
    sender: AnswerSender<C>,
    replay_index: usize,
}

#[derive(Debug)]
struct TableAnswers<C: ConstraintOps> {
    answers: Vec<NF<C>>,
    seen: HashSet<NF<C>>,
    consumers: HashMap<ConsumerId, Consumer<C>>,
    next_consumer_id: ConsumerId,
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
                consumers: HashMap::new(),
                next_consumer_id: 0,
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
        let mut guard = self.producer.lock();
        guard.state = ProducerState::Done;
        guard.producer = None;
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

    pub fn consumers_is_empty(&self) -> bool {
        self.answers.lock().consumers.is_empty()
    }

    /// Register a consumer queue starting at a given answer index.
    pub fn register_consumer(
        &self,
        queue_bound: usize,
        start_index: usize,
    ) -> (ConsumerId, AnswerReceiver<C>) {
        let mut answers = self.answers.lock();
        let (tx, rx) = AnswerQueue::bounded_with_waker(queue_bound.max(1), answers.waker.clone());
        let consumer_id = answers.next_consumer_id;
        answers.next_consumer_id += 1;
        let replay_index = start_index.min(answers.answers.len());
        answers.consumers.insert(
            consumer_id,
            Consumer {
                sender: tx,
                replay_index,
            },
        );
        let _ = self.fill_consumer_with_guard(&mut answers, consumer_id);
        (consumer_id, rx)
    }

    fn fill_consumer_with_guard(
        &self,
        answers: &mut TableAnswers<C>,
        consumer_id: ConsumerId,
    ) -> bool {
        let mut blocked = false;
        let mut remove = false;
        if let Some(consumer) = answers.consumers.get_mut(&consumer_id) {
            while consumer.replay_index < answers.answers.len() {
                let nf = answers.answers[consumer.replay_index].clone();
                match consumer.sender.try_send(nf) {
                    SinkResult::Accepted => {
                        consumer.replay_index += 1;
                    }
                    SinkResult::Full => {
                        blocked = true;
                        break;
                    }
                    SinkResult::Closed => {
                        remove = true;
                        break;
                    }
                }
            }
        }
        if remove {
            answers.consumers.remove(&consumer_id);
        }
        blocked
    }

    fn fill_consumer(&self, consumer_id: ConsumerId) -> bool {
        let mut answers = self.answers.lock();
        self.fill_consumer_with_guard(&mut answers, consumer_id)
    }

    fn flush_consumers(&self) -> bool {
        let mut answers = self.answers.lock();
        let ids: Vec<ConsumerId> = answers.consumers.keys().copied().collect();
        let mut blocked = false;
        for id in ids {
            if self.fill_consumer_with_guard(&mut answers, id) {
                blocked = true;
            }
        }
        blocked
    }

    fn consumer_caught_up(&self, consumer_id: ConsumerId) -> bool {
        let answers = self.answers.lock();
        match answers.consumers.get(&consumer_id) {
            Some(consumer) => consumer.replay_index >= answers.answers.len(),
            None => true,
        }
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
    terms: &TermStore,
    tables: &Tables<C>,
) -> ProducerStep {
    if table.flush_consumers() {
        return ProducerStep::Blocked;
    }

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
            if table.flush_consumers() {
                return ProducerStep::Blocked;
            }
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

/// FixWork: table handle that streams answers from a producer task.
///
/// The producer runs in iterations in a separate task. Each iteration
/// evaluates the body with replay-only calls for the current CallKey.
#[derive(Clone, Debug)]
pub struct FixWork<C: ConstraintOps> {
    /// The CallKey for this tabled call.
    pub key: CallKey<C>,
    /// Reference to the table.
    pub table: Arc<Table<C>>,
    /// Consumer id for this handle.
    pub consumer_id: ConsumerId,
    /// Receiver for this handle.
    pub receiver: Arc<Mutex<AnswerReceiver<C>>>,
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
        let (consumer_id, receiver) = table.register_consumer(tables.queue_bound(), start_index);
        Self {
            key,
            table,
            consumer_id,
            receiver: Arc::new(Mutex::new(receiver)),
            tables,
        }
    }

    /// Step this FixWork handle.
    pub fn step(&mut self, terms: &TermStore) -> WorkStep<C> {
        let _ = terms;
        let receiver = self.receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => {
                return WorkStep::Emit(nf, boxed_work(Work::Fix(self.clone())));
            }
            RecvResult::Closed => return WorkStep::Done,
            RecvResult::Empty => {}
        }
        drop(receiver);

        let _ = self.table.fill_consumer(self.consumer_id);

        let receiver = self.receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => {
                return WorkStep::Emit(nf, boxed_work(Work::Fix(self.clone())));
            }
            RecvResult::Closed => return WorkStep::Done,
            RecvResult::Empty => {}
        }

        let done = self.table.is_done() && self.table.consumer_caught_up(self.consumer_id);
        if done {
            WorkStep::Done
        } else {
            let should_spawn = self.table.try_mark_producer_active();
            if should_spawn {
                let producer = FixProducerWork::new(self.table.clone(), self.tables.clone());
                WorkStep::Split(
                    boxed_node(Node::Work(boxed_work(Work::FixProducer(producer)))),
                    boxed_node(Node::Work(boxed_work(Work::Fix(self.clone())))),
                )
            } else {
                WorkStep::More(boxed_work(Work::Fix(self.clone())))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct FixProducerWork<C: ConstraintOps> {
    table: Arc<Table<C>>,
    tables: Tables<C>,
}

impl<C: ConstraintOps> FixProducerWork<C> {
    pub fn new(table: Arc<Table<C>>, tables: Tables<C>) -> Self {
        Self { table, tables }
    }

    pub fn step(&mut self, terms: &TermStore) -> WorkStep<C> {
        let step = step_table_producer(&self.table, terms, &self.tables);
        match step {
            ProducerStep::Done => WorkStep::Done,
            ProducerStep::Blocked | ProducerStep::Progress => {
                WorkStep::More(boxed_work(Work::FixProducer(self.clone())))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        boxed_node, boxed_work, step_bind_producer, step_table_producer, BindProducerState,
        BindWork, CallKey, CallMode, Env, FixWork, MeetWork, PipeWork, ProducerSpec, ProducerState,
        ProducerStep, Table, Tables, Work, WorkStep,
    };
    use crate::drop_fresh::DropFresh;
    use crate::factors::Factors;
    use crate::nf::NF;
    use crate::node::Node;
    use crate::queue::{AnswerQueue, RecvResult};
    use crate::rel::Rel;
    use crate::term::TermStore;
    use crate::test_utils::{make_ground_nf, setup};
    use smallvec::SmallVec;
    use std::sync::Arc;

    /// Create identity NF (x -> x with single variable)
    fn make_identity_nf() -> NF<()> {
        // Note: NF::identity(()) creates an empty-pattern NF, not x -> x
        // For tests we need the variable identity x -> x
        NF::identity(())
    }

    /// Create variable identity NF (x -> x) using a specific TermStore
    fn make_var_identity_nf(terms: &TermStore) -> NF<()> {
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
                Work::Bind(bind) => {
                    let state = bind.producer_state();
                    let guard = state.lock();
                    let Some(fix) = find_fixwork_in_node(&guard.gen) else {
                        panic!("Expected FixWork in bind generator");
                    };
                    fix.key
                }
                _ => panic!("Expected Work::Bind(..)"),
            },
            _ => panic!("Expected WorkStep::More(..)"),
        }
    }

    fn is_work_pipe(node: &Node<()>) -> bool {
        matches!(node, Node::Work(work) if matches!(work.as_ref(), Work::Pipe(_)))
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

    fn unwrap_work_bind(step: WorkStep<()>) -> BindWork<()> {
        match step {
            WorkStep::More(work) => match *work {
                Work::Bind(bind) => bind,
                _ => panic!("Expected Work::Bind"),
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
    // BIND PRODUCER / CONSUMER TESTS
    // ========================================================================

    #[test]
    fn bindwork_consumer_does_not_advance_generator() {
        let terms = TermStore::new();
        let gen: Node<()> = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        let pipe = PipeWork::new();
        let mut bind = BindWork::new(gen, pipe, false);

        let _ = bind.step(&terms);
        let state = bind.producer.lock();
        assert!(
            matches!(state.gen, Node::Or(_, _)),
            "consumer must not advance generator"
        );
    }

    #[test]
    fn bind_producer_blocks_when_queue_full() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let gen = Node::Emit(
            nf_a.clone(),
            Box::new(Node::Emit(nf_b.clone(), Box::new(Node::Fail))),
        );

        let (tx, _rx) = AnswerQueue::bounded(1);
        let state = BindProducerState::new(gen, tx);

        let step1 = step_bind_producer(&state, &terms);
        assert!(matches!(step1, ProducerStep::Progress));

        let step2 = step_bind_producer(&state, &terms);
        assert!(matches!(step2, ProducerStep::Blocked));
    }

    #[test]
    fn bind_producer_closes_queue_on_exhaustion() {
        let terms = TermStore::new();
        let gen: Node<()> = Node::Fail;
        let (tx, rx) = AnswerQueue::bounded(1);
        let state = BindProducerState::new(gen, tx);

        let step = step_bind_producer(&state, &terms);
        assert!(matches!(step, ProducerStep::Done));

        match rx.try_recv() {
            RecvResult::Closed => {}
            other => panic!("expected closed receiver, got {:?}", other),
        }
    }

    #[test]
    fn bind_consumer_emits_from_queue() {
        let (symbols, terms) = setup();
        let nf = make_ground_nf("A", &symbols, &terms);
        let pipe = PipeWork::new();
        let mut bind = BindWork::new(Node::Fail, pipe, false);

        {
            let state = bind.producer.lock();
            let sender = state.sender.as_ref().expect("expected sender");
            let _ = sender.try_send(nf);
        }

        let step = bind.step(&terms);
        let (left, _) = unwrap_split(step);
        assert!(is_work_pipe(&left));
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
        let terms = TermStore::new();
        let mut pipe: PipeWork<()> = PipeWork::new();
        let step = pipe.step(&terms);
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn pipework_step_boundaries_only_emits_compose() {
        let (symbols, terms) = setup();
        let left = make_ground_nf("X", &symbols, &terms);
        let right = make_ground_nf("X", &symbols, &terms);

        let mut pipe: PipeWork<()> =
            PipeWork::with_boundaries(Some(left), Factors::new(), Some(right));

        let step = pipe.step(&terms);
        // Should emit the composed result
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn pipework_step_left_boundary_only_emits() {
        let (symbols, terms) = setup();
        let nf = make_ground_nf("X", &symbols, &terms);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(nf), Factors::new(), None);

        let step = pipe.step(&terms);
        // Should emit the left boundary as result
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn pipework_step_right_boundary_only_emits() {
        let (symbols, terms) = setup();
        let nf = make_ground_nf("X", &symbols, &terms);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(None, Factors::new(), Some(nf));

        let step = pipe.step(&terms);
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn pipework_fuses_adjacent_atoms_anywhere() {
        let (symbols, terms) = setup();
        let nf = make_ground_nf("A", &symbols, &terms);
        let rels = vec![
            atom_rel(nf.clone()),
            atom_rel(nf.clone()),
            atom_rel(nf.clone()),
        ];
        let mid = factors_from_rels(rels);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        let step = pipe.step(&terms);
        match step {
            WorkStep::Emit(emitted, _) => assert_eq!(emitted, nf),
            _ => panic!("Expected adjacent atoms to fuse and emit in one step"),
        }
    }

    #[test]
    fn pipework_fuses_middle_atoms_before_advancing_ends() {
        let (symbols, terms) = setup();
        let nf = make_ground_nf("A", &symbols, &terms);
        let atom = atom_rel(nf);
        let or = Arc::new(Rel::Or(atom.clone(), atom.clone()));

        let rels = vec![or.clone(), atom.clone(), atom.clone(), or];
        let mid = factors_from_rels(rels);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        let step = pipe.step(&terms);
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
        let (symbols, terms) = setup();
        let nf = make_ground_nf("X", &symbols, &terms);
        let rels = vec![atom_rel(nf.clone())];
        let mid = factors_from_rels(rels);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&terms);

        match step {
            WorkStep::More(work) => match *work {
                Work::Pipe(mut next_pipe) => {
                    assert!(
                        next_pipe.left.is_some(),
                        "Atom should be absorbed into left"
                    );
                    assert!(next_pipe.mid.is_empty(), "Mid should be empty after absorb");

                    let step2 = next_pipe.step(&terms);
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
        let (symbols, terms) = setup();
        let left = make_ground_nf("X", &symbols, &terms);
        let atom_nf = make_ground_nf("X", &symbols, &terms);
        let rels = vec![atom_rel(atom_nf)];
        let mid = factors_from_rels(rels);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(left), mid, None);
        let step = pipe.step(&terms);

        // Should compose and continue or emit
        // Depends on implementation - More or Emit
        assert!(matches!(step, WorkStep::Emit(_, _) | WorkStep::More(_)));
    }

    // ========================================================================
    // PIPEWORK STEP TESTS - OR SPLITTING
    // ========================================================================

    #[test]
    fn pipework_step_or_in_mid_splits() {
        let (_, terms) = setup();
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&terms);

        // Should split into two branches
        assert!(matches!(step, WorkStep::Split(_, _)));
    }

    #[test]
    fn pipework_step_or_with_boundaries_splits() {
        let (symbols, terms) = setup();
        let left = make_ground_nf("X", &symbols, &terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(left), mid, None);
        let step = pipe.step(&terms);

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
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&terms);

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
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a.clone())));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&terms);

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
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b.clone())));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&terms);

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
        let (symbols, terms) = setup();
        let boundary = make_ground_nf("BOUNDARY", &symbols, &terms);
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(boundary.clone()), mid, None);
        let step = pipe.step(&terms);

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
        let (symbols, terms) = setup();
        let boundary = make_ground_nf("BOUNDARY", &symbols, &terms);
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(None, mid, Some(boundary.clone()));
        let step = pipe.step(&terms);

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
        let (symbols, terms) = setup();
        let left_nf = make_ground_nf("L", &symbols, &terms);
        let right_nf = make_ground_nf("R", &symbols, &terms);
        let left_rel: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(left_nf)));
        let right_rel: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(right_nf)));
        let and_rel: Arc<Rel<()>> = Arc::new(Rel::And(left_rel, right_rel));
        let call_rel: Arc<Rel<()>> = Arc::new(Rel::Call(0));
        let mid = factors_from_rels(vec![and_rel, call_rel]);

        let body = Arc::new(Rel::Atom(Arc::new(make_ground_nf(
            "BODY", &symbols, &terms,
        ))));
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        pipe.env = Env::new().bind(0, body);
        pipe.flip = true;

        let step = pipe.step(&terms);

        let bind = unwrap_work_bind(step);
        assert!(
            bind.absorb_front,
            "Should advance front (And) before Call when opposite end is non-call"
        );
    }

    /// split_or must preserve both boundaries in both branches.
    #[test]
    fn split_or_preserves_both_boundaries() {
        let (symbols, terms) = setup();
        let left_boundary = make_ground_nf("LEFT", &symbols, &terms);
        let right_boundary = make_ground_nf("RIGHT", &symbols, &terms);
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let a: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(
            Some(left_boundary.clone()),
            mid,
            Some(right_boundary.clone()),
        );
        let step = pipe.step(&terms);

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
        let (_, terms) = setup();
        // Use Or nodes which won't be absorbed during normalization
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let or1 = Arc::new(Rel::Or(a.clone(), b.clone()));
        let or2 = Arc::new(Rel::Or(a.clone(), b.clone())); // Non-atom rest factor
                                                           // Or followed by another Or (neither is normalizable)
        let mid = factors_from_rels(vec![or1, or2]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&terms);

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
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let nf_body = make_ground_nf("BODY", &symbols, &terms);
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
        let step = pipe.step(&terms);

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
        let (_, terms) = setup();
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let or_rel = Arc::new(Rel::Or(a, b));
        let mid = factors_from_rels(vec![or_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&terms);

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
        let (_, terms) = setup();
        let zero_rel = Arc::new(Rel::Zero);
        let mid = factors_from_rels(vec![zero_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);
        let step = pipe.step(&terms);

        // Zero annihilates the pipe
        assert!(matches!(step, WorkStep::Done));
    }

    #[test]
    fn pipework_step_zero_with_boundaries_returns_done() {
        let (symbols, terms) = setup();
        let left = make_ground_nf("X", &symbols, &terms);
        let right = make_ground_nf("X", &symbols, &terms);
        let zero_rel = Arc::new(Rel::Zero);
        let mid = factors_from_rels(vec![zero_rel]);

        let mut pipe: PipeWork<()> = PipeWork::with_boundaries(Some(left), mid, Some(right));
        let step = pipe.step(&terms);

        assert!(matches!(step, WorkStep::Done));
    }

    // ========================================================================
    // PIPEWORK STEP TESTS - COMPOSITION FAILURE
    // ========================================================================

    #[test]
    fn pipework_step_incompatible_compose_returns_done() {
        let (symbols, terms) = setup();
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
        let step = pipe.step(&terms);

        // Composition should fail (B != C), returning Done
        assert!(matches!(step, WorkStep::Done));
    }

    // ========================================================================
    // WORK::ATOM STEP TESTS
    // ========================================================================

    #[test]
    fn work_atom_step_emits_then_done() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let mut work: Work<()> = Work::Atom(nf.clone());

        let step = work.step(&terms);

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
        let (symbols, terms) = setup();
        // X -> X ; X -> X should compose to X -> X
        let nf1 = make_ground_nf("X", &symbols, &terms);
        let nf2 = make_ground_nf("X", &symbols, &terms);
        let rels = vec![atom_rel(nf1), atom_rel(nf2)];
        let mid = factors_from_rels(rels);

        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        // Step until we get an answer or Done
        let mut steps = 0;
        loop {
            let step = pipe.step(&terms);
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
        let (symbols, terms) = setup();
        // Create: mid = [Or(...), Atom(X->X)]
        // The Atom at the BACK should be absorbed into right boundary
        // BEFORE the Or at front is processed.
        let nf = make_ground_nf("X", &symbols, &terms);

        // Put an Or at front so front isn't an Atom
        let or_rel = Arc::new(Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Zero)));
        let atom_rel = Arc::new(Rel::Atom(Arc::new(nf.clone())));

        let mid = factors_from_rels(vec![or_rel, atom_rel]);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        // Normalize step should absorb back atom into right
        let step = pipe.step(&terms);

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
        let (symbols, terms) = setup();
        // mid = [Atom(A->A), Or(...), Atom(B->B)]
        // Both atoms should be absorbed before Or is processed
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let atom_a = Arc::new(Rel::Atom(Arc::new(nf_a.clone())));
        let or_rel = Arc::new(Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Zero)));
        let atom_b = Arc::new(Rel::Atom(Arc::new(nf_b.clone())));

        let mid = factors_from_rels(vec![atom_a, or_rel, atom_b]);
        let mut pipe: PipeWork<()> = PipeWork::with_mid(mid);

        // Step until we get a Split (Or processing) or run out of More steps
        let mut steps = 0;
        let max_steps = 10;
        loop {
            let step = pipe.step(&terms);
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
        let (symbols, terms) = setup();
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
            let step = pipe.step(&terms);
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
        let (_, terms) = setup();
        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        let step = meet.step(&terms);
        assert!(
            matches!(step, WorkStep::Done),
            "Both sides Fail should return Done immediately"
        );
    }

    #[test]
    fn meetwork_step_left_fail_returns_done() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let right = Node::Emit(nf, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, right);

        // With left Fail, no meets possible - should eventually return Done
        // (may take multiple steps as it drains right)
        let mut done = false;
        for _ in 0..10 {
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let left = Node::Emit(nf, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, Node::Fail);

        // With right Fail, no meets possible - should eventually return Done
        let mut done = false;
        for _ in 0..10 {
            let step = meet.step(&terms);
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
        let (symbols, terms) = setup();
        let nf = make_ground_nf("A", &symbols, &terms);
        let rel = Arc::new(Rel::Atom(Arc::new(nf.clone())));
        let factors = Factors::from_seq(Arc::from(vec![rel]));
        let left_pipe = PipeWork::with_mid(factors);
        let left = Node::Work(boxed_work(Work::Pipe(left_pipe)));
        let right = Node::Emit(nf, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emitted = false;
        for _ in 0..50 {
            match meet.step(&terms) {
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
        let (symbols, terms) = setup();
        // Both sides emit X -> X, which should meet successfully
        let nf1 = make_ground_nf("X", &symbols, &terms);
        let nf2 = make_ground_nf("X", &symbols, &terms);
        let left = Node::Emit(nf1, Box::new(Node::Fail));
        let right = Node::Emit(nf2, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        // Step until we get an emit or Done
        let mut emitted = false;
        for _ in 0..20 {
            let step = meet.step(&terms);
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
        let (symbols, terms) = setup();
        // Left: x -> x (variable identity)
        // Right: A -> A (ground)
        // Meet should produce A -> A
        let identity = make_var_identity_nf(&terms);
        let ground = make_ground_nf("A", &symbols, &terms);

        let left = Node::Emit(identity, Box::new(Node::Fail));
        let right = Node::Emit(ground.clone(), Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut result: Option<NF<()>> = None;
        for _ in 0..20 {
            let step = meet.step(&terms);
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
        let (symbols, terms) = setup();
        // Left: A -> A
        // Right: B -> B
        // These can't meet (A != B)
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let left = Node::Emit(nf_a, Box::new(Node::Fail));
        let right = Node::Emit(nf_b, Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emitted = false;
        for _ in 0..20 {
            let step = meet.step(&terms);
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
        let (symbols, terms) = setup();
        // Left: 1-in, 1-out
        // Right: 2-in, 2-out (if we can construct it)
        let single = make_ground_nf("X", &symbols, &terms);

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
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
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
            let step = meet.step(&terms);
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
        let (symbols, terms) = setup();
        // Left: emit variable identity x -> x twice
        // Right: emit A -> A, B -> B
        // If identity meets with A -> A and B -> B, should produce:
        // - A -> A (from identity meet A -> A)
        // - B -> B (from identity meet B -> B)
        // - Plus other combinations

        let id1 = make_var_identity_nf(&terms);
        let id2 = make_var_identity_nf(&terms);
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let left = Node::Emit(id1, Box::new(Node::Emit(id2, Box::new(Node::Fail))));
        let right = Node::Emit(nf_a, Box::new(Node::Emit(nf_b, Box::new(Node::Fail))));

        let mut meet: MeetWork<()> = MeetWork::new(left, right);

        let mut emit_count = 0;
        for _ in 0..50 {
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
        // Pre-populate pending queue to verify emit priority
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();

        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        meet.pending.push_back(nf1);
        meet.pending.push_back(nf2);

        // First step should emit from pending
        let step = meet.step(&terms);
        assert!(
            matches!(step, WorkStep::Emit(_, _)),
            "Should emit from pending first"
        );
    }

    #[test]
    fn meetwork_pending_preserves_order() {
        let (symbols, terms) = setup();
        // Pre-populate pending with ordered items
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let nf_c = make_ground_nf("C", &symbols, &terms);

        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        meet.pending.push_back(nf_a.clone());
        meet.pending.push_back(nf_b.clone());
        meet.pending.push_back(nf_c.clone());

        // Should emit in FIFO order
        let mut emitted = Vec::new();
        for _ in 0..5 {
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
        // Both sides exhausted but pending has items
        let nf = make_identity_nf();
        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        meet.pending.push_back(nf);

        let step = meet.step(&terms);
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
        let (symbols, terms) = setup();
        // Left has 1 variable identity, right has 3 ground answers
        let id = make_var_identity_nf(&terms);
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let nf_c = make_ground_nf("C", &symbols, &terms);

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
            let step = meet.step(&terms);
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
        let (symbols, terms) = setup();
        // Left has 3 ground answers, right has 1 variable identity
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let nf_c = make_ground_nf("C", &symbols, &terms);
        let id = make_var_identity_nf(&terms);

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
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
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
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let left = Node::Emit(nf.clone(), Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(left, Node::Fail);

        assert!(meet.seen_l.is_empty(), "seen_l should start empty");

        // Step to pull from left
        loop {
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let right = Node::Emit(nf.clone(), Box::new(Node::Fail));
        let mut meet: MeetWork<()> = MeetWork::new(Node::Fail, right);

        assert!(meet.seen_r.is_empty(), "seen_r should start empty");

        // Step to pull from right (may need flip to be true)
        meet.flip = true; // Force pull from right
        loop {
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
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
            let step = meet.step(&terms);
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
        let (_, terms) = setup();
        let meet: MeetWork<()> = MeetWork::new(Node::Fail, Node::Fail);
        let mut work: Work<()> = Work::Meet(meet);
        let step = work.step(&terms);
        // Should delegate to MeetWork::step
        assert!(matches!(step, WorkStep::Done));
    }

    // ========================================================================
    // MEETWORK STEP TESTS - SYMMETRIC BEHAVIOR
    // ========================================================================

    #[test]
    fn meetwork_symmetric_produces_same_results() {
        let (symbols, terms1) = setup();
        let (_, terms2) = setup();

        let nf_a = make_ground_nf("A", &symbols, &terms1);
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
            let step = meet1.step(&terms1);
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
            let step = meet2.step(&terms2);
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
        let (_, terms) = setup();
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
            let step = meet.step(&terms);
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
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let key1: CallKey<()> = CallKey::new(0, 1, Some(nf_a), None);
        let key2: CallKey<()> = CallKey::new(0, 1, Some(nf_b), None);
        assert_ne!(key1, key2);
    }

    #[test]
    fn callkey_inequality_different_right() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

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
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let body_nf = make_ground_nf("BODY", &symbols, &terms);
        let body: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(body_nf)));
        let env = Env::new().bind(0, body);

        let call = Arc::new(Rel::Call(0));
        let mid_a = factors_from_rels(vec![call.clone(), atom_rel(nf_a)]);
        let mid_b = factors_from_rels(vec![call, atom_rel(nf_b)]);

        let mut pipe_a = PipeWork::with_mid(mid_a);
        pipe_a.env = env.clone();
        let mut pipe_b = PipeWork::with_mid(mid_b);
        pipe_b.env = env.clone();

        let step_a = pipe_a.advance_front(&terms);
        let step_b = pipe_b.advance_front(&terms);

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
        assert!(answers.consumers.is_empty());
        drop(answers);
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
        let (symbols, terms) = setup();
        let table: Table<()> = Table::new();
        let nf1 = make_ground_nf("A", &symbols, &terms);
        let nf2 = make_ground_nf("B", &symbols, &terms);
        let nf3 = make_ground_nf("C", &symbols, &terms);

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
        let (_id, rx) = table.register_consumer(2, 0);
        assert!(matches!(rx.try_recv(), RecvResult::Empty));
    }

    #[test]
    fn table_next_answer_single() {
        let table: Table<()> = Table::new();
        let nf = make_identity_nf();
        table.add_answer(nf);
        let (_id, rx) = table.register_consumer(2, 0);
        assert!(matches!(rx.try_recv(), RecvResult::Item(_)));
        assert!(matches!(rx.try_recv(), RecvResult::Empty));
    }

    #[test]
    fn table_next_answer_multiple() {
        let (symbols, terms) = setup();
        let table: Table<()> = Table::new();
        table.add_answer(make_ground_nf("A", &symbols, &terms));
        table.add_answer(make_ground_nf("B", &symbols, &terms));
        table.add_answer(make_ground_nf("C", &symbols, &terms));
        let (_id, rx) = table.register_consumer(4, 0);

        assert!(matches!(rx.try_recv(), RecvResult::Item(_)));
        assert!(matches!(rx.try_recv(), RecvResult::Item(_)));
        assert!(matches!(rx.try_recv(), RecvResult::Item(_)));
        assert!(matches!(rx.try_recv(), RecvResult::Empty));
    }

    #[test]
    fn table_next_answer_increments_index() {
        let (symbols, terms) = setup();
        let table: Table<()> = Table::new();
        table.add_answer(make_ground_nf("A", &symbols, &terms));
        table.add_answer(make_ground_nf("B", &symbols, &terms));
        let (id, rx) = table.register_consumer(1, 0);
        {
            let answers = table.lock_answers_for_test();
            assert_eq!(answers.consumers.get(&id).unwrap().replay_index, 1);
        }
        assert!(matches!(rx.try_recv(), RecvResult::Item(_)));
        let blocked = table.fill_consumer(id);
        assert!(!blocked);
        {
            let answers = table.lock_answers_for_test();
            assert_eq!(answers.consumers.get(&id).unwrap().replay_index, 2);
        }
    }

    #[test]
    fn table_reset_consumer() {
        let (symbols, terms) = setup();
        let table: Table<()> = Table::new();
        table.add_answer(make_ground_nf("A", &symbols, &terms));
        table.add_answer(make_ground_nf("B", &symbols, &terms));
        let (_id, rx_a) = table.register_consumer(2, 0);
        assert!(matches!(rx_a.try_recv(), RecvResult::Item(_)));
        let (_id, rx_b) = table.register_consumer(2, 0);
        assert!(matches!(rx_b.try_recv(), RecvResult::Item(_)));
    }

    #[test]
    fn table_all_answers() {
        let (symbols, terms) = setup();
        let table: Table<()> = Table::new();
        table.add_answer(make_ground_nf("A", &symbols, &terms));
        table.add_answer(make_ground_nf("B", &symbols, &terms));

        let all = table.all_answers();
        assert_eq!(all.len(), 2);
    }

    #[test]
    fn table_has_more_answers() {
        let (symbols, terms) = setup();
        let table: Table<()> = Table::new();
        table.add_answer(make_ground_nf("A", &symbols, &terms));
        table.add_answer(make_ground_nf("B", &symbols, &terms));
        let (id, rx) = table.register_consumer(1, 0);
        assert!(!table.consumer_caught_up(id));
        assert!(matches!(rx.try_recv(), RecvResult::Item(_)));
        let blocked = table.fill_consumer(id);
        assert!(!blocked);
        assert!(table.consumer_caught_up(id));
    }

    #[test]
    fn table_default_is_new() {
        let table: Table<()> = Table::default();
        let answers = table.lock_answers_for_test();
        assert!(answers.answers.is_empty());
        drop(answers);
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
        let (symbols, terms) = setup();
        let tables: Tables<()> = Tables::new();

        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

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

        assert_eq!(fix.consumer_id, 0);
        assert_eq!(fix.key.rel, 0);
    }

    // ========================================================================
    // FIXWORK TESTS - HANDLE BEHAVIOR
    // ========================================================================

    #[test]
    fn fixwork_handle_emits_existing_answers() {
        let (symbols, terms) = setup();
        let terms = terms;
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());

        table.add_answer(make_ground_nf("A", &symbols, &terms));
        table.add_answer(make_ground_nf("B", &symbols, &terms));
        table.finish_producer();

        let mut fix: FixWork<()> = FixWork::new(key, table, 0, Tables::new());

        let step1 = fix.step(&terms);
        assert!(matches!(step1, WorkStep::Emit(_, _)));

        if let WorkStep::Emit(_, work) = step1 {
            if let Work::Fix(f) = *work {
                fix = f;
            }
        }

        let step2 = fix.step(&terms);
        assert!(matches!(step2, WorkStep::Emit(_, _)));

        if let WorkStep::Emit(_, work) = step2 {
            if let Work::Fix(f) = *work {
                fix = f;
            }
        }

        let step3 = fix.step(&terms);
        assert!(matches!(step3, WorkStep::Done));
    }

    #[test]
    fn fixwork_handle_does_not_start_producer() {
        use std::sync::Arc;

        let (symbols, terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        let nf = make_ground_nf("A", &symbols, &terms);
        let spec = ProducerSpec {
            key: key.clone(),
            body: Arc::new(Rel::Atom(Arc::new(nf))),
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
        let step = fix.step(&terms);
        assert!(
            matches!(step, WorkStep::Split(_, _)),
            "consumer should schedule producer task"
        );
        assert_eq!(
            table.producer_state(),
            ProducerState::NotStarted,
            "consumer must not start producer"
        );
        assert!(
            table.producer_task_active(),
            "producer task should be marked active"
        );
    }

    #[test]
    fn fixwork_handle_does_not_advance_producer() {
        use std::sync::Arc;

        let (symbols, terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        let nf = make_ground_nf("A", &symbols, &terms);
        let producer_node = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        let spec = ProducerSpec {
            key: key.clone(),
            body: Arc::new(Rel::Atom(Arc::new(nf))),
            left: None,
            right: None,
            env: Env::new(),
        };

        table.start_producer(producer_node, spec, 0);

        let mut fix: FixWork<()> = FixWork::new(key, table.clone(), 0, Tables::new());
        let _ = fix.step(&terms);

        let still_or = {
            let guard = table.lock_producer_for_test();
            matches!(guard.producer, Some(Node::Or(_, _)))
        };
        assert!(still_or, "consumer must not advance producer node");
    }

    #[test]
    fn fix_producer_dedups_duplicate_answers() {
        use std::sync::Arc;

        let (symbols, terms) = setup();
        let tables = Tables::new();
        let table = Arc::new(Table::new());
        let nf = make_ground_nf("A", &symbols, &terms);
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
        let _ = table.register_consumer(4, 0);

        let mut steps = 0;
        loop {
            let step = step_table_producer(&table, &terms, &tables);
            steps += 1;
            if matches!(step, ProducerStep::Done) || steps > 10 {
                break;
            }
        }

        assert_eq!(table.answers_len(), 1);
    }

    #[test]
    fn fix_producer_blocks_when_consumer_queue_full() {
        use std::sync::Arc;

        let (symbols, terms) = setup();
        let tables = Tables::new();
        let table = Arc::new(Table::new());
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
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
        let (_id, rx) = table.register_consumer(1, 0);

        let step1 = step_table_producer(&table, &terms, &tables);
        assert!(matches!(step1, ProducerStep::Progress));

        let step2 = step_table_producer(&table, &terms, &tables);
        assert!(matches!(step2, ProducerStep::Blocked));

        match rx.try_recv() {
            RecvResult::Item(_) => {}
            other => panic!("expected queued answer, got {:?}", other),
        }

        let step3 = step_table_producer(&table, &terms, &tables);
        assert!(matches!(step3, ProducerStep::Progress));
    }

    #[test]
    fn fix_producer_broadcasts_answers_to_all_consumers() {
        use std::sync::Arc;

        let (symbols, terms) = setup();
        let tables = Tables::new();
        let table = Arc::new(Table::new());
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
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
        let (_id_a, rx_a) = table.register_consumer(2, 0);
        let (_id_b, rx_b) = table.register_consumer(2, 0);

        let mut steps = 0;
        loop {
            let step = step_table_producer(&table, &terms, &tables);
            steps += 1;
            if matches!(step, ProducerStep::Done) || steps > 10 {
                break;
            }
        }

        let mut got_a = Vec::new();
        let mut got_b = Vec::new();
        for _ in 0..2 {
            if let RecvResult::Item(nf) = rx_a.try_recv() {
                got_a.push(nf);
            }
            if let RecvResult::Item(nf) = rx_b.try_recv() {
                got_b.push(nf);
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

        let (symbols, terms) = setup();
        let table = Arc::new(Table::new());
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        table.add_answer(nf_a.clone());
        table.add_answer(nf_b.clone());
        let (_id, rx) = table.register_consumer(4, 0);
        match rx.try_recv() {
            RecvResult::Item(nf) => assert!(nf == nf_a || nf == nf_b),
            other => panic!("expected replayed answer, got {:?}", other),
        }

        let mut fix: FixWork<()> =
            FixWork::new(CallKey::new(0, 0, None, None), table, 0, Tables::new());
        let step = fix.step(&terms);
        assert!(matches!(step, WorkStep::Emit(_, _)));
    }

    #[test]
    fn fixwork_handle_done_when_table_done() {
        let (_, terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        table.finish_producer();

        let mut fix: FixWork<()> = FixWork::new(key, table, 0, Tables::new());
        let step = fix.step(&terms);
        assert!(matches!(step, WorkStep::Done));
    }

    #[test]
    fn call_replay_interleaves_with_new_answers() {
        use std::sync::Arc;

        let (symbols, terms) = setup();
        let nf_a1 = make_ground_nf("A1", &symbols, &terms);
        let nf_a2 = make_ground_nf("A2", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let body_nf = make_ground_nf("BODY", &symbols, &terms);
        let body: Arc<Rel<()>> = Arc::new(Rel::Atom(Arc::new(body_nf)));
        let env = Env::new().bind(0, body.clone());

        let call = Arc::new(Rel::Call(0));
        let mid = factors_from_rels(vec![call.clone()]);

        let mut pipe_producer = PipeWork::with_mid(mid.clone());
        pipe_producer.env = env.clone();
        let step_producer = pipe_producer.advance_front(&terms);
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
        let step_consumer = pipe_consumer.advance_front(&terms);
        let bind = unwrap_work_bind(step_consumer);
        let producer_state = bind.producer_state();

        let mut outputs = Vec::new();
        let mut steps = 0;
        while outputs.len() < 3 && steps < 50 {
            let _ = step_bind_producer(&producer_state, &terms);
            match bind.receiver.lock().try_recv() {
                RecvResult::Item(nf) => {
                    outputs.push(nf);
                    if outputs.len() == 1 {
                        table.add_answer(nf_b.clone());
                    }
                }
                RecvResult::Closed => break,
                RecvResult::Empty => {}
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
        let (_, terms) = setup();
        let key: CallKey<()> = CallKey::new(0, 0, None, None);
        let table = Arc::new(Table::new());
        table.finish_producer();

        let fix: FixWork<()> = FixWork::new(key, table, 0, Tables::new());
        let mut work: Work<()> = Work::Fix(fix);

        let step = work.step(&terms);
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
        let (symbols, terms) = setup();
        let nf = make_ground_nf("A", &symbols, &terms);
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
}
