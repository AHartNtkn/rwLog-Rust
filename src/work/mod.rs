//! Work - Active work items for the evaluation engine.
//!
//! Work represents computations in progress. PipeWork handles
//! sequential composition (Seq) with outside-in boundary fusion.

use crate::constraint::ConstraintOps;
use crate::drop_fresh::DropFresh;
use crate::factors::Factors;
use crate::nf::NF;
use crate::node::Node;
use crate::rel::Rel;
use crate::symbol::FuncId;
use crate::term::{Term, TermId, TermStore};
use smallvec::SmallVec;
use std::collections::VecDeque;
use std::sync::Arc;

mod and_group;
mod bind;
mod compose;
mod diagonal;
mod fix;
mod join_receiver;
mod meet;
mod pipe;

pub use and_group::{AndGroup, AndGroupConfig};
pub use bind::BindWork;
pub use compose::ComposeWork;
pub(crate) use diagonal::DiagonalStepResult;
pub use fix::{
    step_table_producer, CallKey, Env, FixStepResult, FixWork, ProducerSpec, ProducerState,
    ProducerStep, Table, Tables,
};
pub use join_receiver::JoinReceiverWork;
pub use meet::MeetWork;
pub use pipe::PipeWork;

#[cfg(test)]
mod tests;

/// Active work items for evaluation.
#[derive(Clone, Debug)]
pub enum Work<C: ConstraintOps> {
    /// Sequential composition pipeline.
    Pipe(Box<PipeWork<C>>),
    /// Conjunction/intersection via fair diagonal join.
    Meet(MeetWork<C>),
    /// N-ary conjunction/intersection via fair diagonal join.
    AndGroup(AndGroup<C>),
    /// Tabled recursive call.
    Fix(FixWork<C>),
    /// Symmetric compose join for sequential composition.
    Compose(ComposeWork<C>),
    /// Monadic bind: feeds each source NF as boundary into a pipe template.
    Bind(BindWork<C>),
    /// Receiver for joiner outputs (drives AndGroup producers).
    JoinReceiver(JoinReceiverWork<C>),
    /// Finite replay stream of precomputed answers (one branch, emit-chain semantics).
    ReplayAnswers(VecDeque<NF<C>>),
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
    Split(Box<Work<C>>, Box<Work<C>>),
    /// Continue with modified work.
    More(Box<Work<C>>),
}

/// Result of stepping a local set of work branches.
#[derive(Clone, Debug)]
pub(crate) enum WorkSetStep<C: ConstraintOps> {
    Emit(NF<C>),
    Continue,
    Exhausted,
}

/// Local scheduler for a disjunction of work branches.
///
/// This is the abstract-machine equivalent of keeping a local `Node::Or` tree:
/// each step advances exactly one branch and rotates ready branches fairly.
#[derive(Clone, Debug)]
pub(crate) struct WorkSet<C: ConstraintOps> {
    root: WorkSetNode<C>,
}

impl<C: ConstraintOps> WorkSet<C> {
    pub(crate) fn new() -> Self {
        Self {
            root: WorkSetNode::Fail,
        }
    }

    pub(crate) fn from_work(work: Work<C>) -> Self {
        Self {
            root: WorkSetNode::from_work(work),
        }
    }

    #[cfg(test)]
    pub(crate) fn from_works<I>(works: I) -> Self
    where
        I: IntoIterator<Item = Work<C>>,
    {
        let mut root = WorkSetNode::Fail;
        for work in works {
            root = or_work_set_node(root, WorkSetNode::from_work(work));
        }
        Self { root }
    }

    pub(crate) fn from_answers(answers: Vec<NF<C>>) -> Self {
        if answers.is_empty() {
            Self::new()
        } else {
            Self::from_work(Work::ReplayAnswers(VecDeque::from(answers)))
        }
    }

    pub(crate) fn or_with(self, other: Self) -> Self {
        Self {
            root: or_work_set_node(self.root, other.root),
        }
    }

    pub(crate) fn is_exhausted(&self) -> bool {
        matches!(self.root, WorkSetNode::Fail)
    }

    pub(crate) fn drain_leading_atoms(&mut self) -> Vec<NF<C>> {
        let mut out = Vec::new();
        let current = std::mem::replace(&mut self.root, WorkSetNode::Fail);
        match current {
            WorkSetNode::Leaf(work) => match *work {
                Work::Atom(nf) => out.push(nf),
                Work::ReplayAnswers(mut answers) => out.extend(answers.drain(..)),
                other => self.root = WorkSetNode::Leaf(Box::new(other)),
            },
            other => self.root = other,
        }
        out
    }

    #[cfg(test)]
    pub(crate) fn branch_count(&self) -> usize {
        self.root.branch_count()
    }

    #[cfg(test)]
    pub(crate) fn branches(&self) -> impl Iterator<Item = &Work<C>> {
        let mut out = Vec::new();
        self.root.collect_branches(&mut out);
        out.into_iter()
    }

    pub(crate) fn step(&mut self, terms: &mut TermStore) -> WorkSetStep<C> {
        let current = std::mem::replace(&mut self.root, WorkSetNode::Fail);
        match step_work_set_node(current, terms) {
            WorkSetNodeStep::Emit(nf, rest) => {
                self.root = rest;
                WorkSetStep::Emit(nf)
            }
            WorkSetNodeStep::Continue(rest) => {
                self.root = rest;
                if self.is_exhausted() {
                    WorkSetStep::Exhausted
                } else {
                    WorkSetStep::Continue
                }
            }
            WorkSetNodeStep::Exhausted => {
                self.root = WorkSetNode::Fail;
                WorkSetStep::Exhausted
            }
        }
    }
}

#[derive(Clone, Debug)]
enum WorkSetNode<C: ConstraintOps> {
    Fail,
    Or(Box<WorkSetNode<C>>, Box<WorkSetNode<C>>),
    Leaf(Box<Work<C>>),
}

impl<C: ConstraintOps> WorkSetNode<C> {
    fn from_work(work: Work<C>) -> Self {
        if matches!(work, Work::Done) {
            WorkSetNode::Fail
        } else {
            WorkSetNode::Leaf(Box::new(work))
        }
    }

    #[cfg(test)]
    fn branch_count(&self) -> usize {
        match self {
            WorkSetNode::Fail => 0,
            WorkSetNode::Leaf(_) => 1,
            WorkSetNode::Or(left, right) => left.branch_count() + right.branch_count(),
        }
    }

    #[cfg(test)]
    fn collect_branches<'a>(&'a self, out: &mut Vec<&'a Work<C>>) {
        match self {
            WorkSetNode::Fail => {}
            WorkSetNode::Leaf(work) => out.push(work.as_ref()),
            WorkSetNode::Or(left, right) => {
                left.collect_branches(out);
                right.collect_branches(out);
            }
        }
    }
}

enum WorkSetNodeStep<C: ConstraintOps> {
    Emit(NF<C>, WorkSetNode<C>),
    Continue(WorkSetNode<C>),
    Exhausted,
}

fn or_work_set_node<C: ConstraintOps>(
    left: WorkSetNode<C>,
    right: WorkSetNode<C>,
) -> WorkSetNode<C> {
    match (&left, &right) {
        (WorkSetNode::Fail, _) => right,
        (_, WorkSetNode::Fail) => left,
        _ => WorkSetNode::Or(Box::new(left), Box::new(right)),
    }
}

fn rebuild_work_set_or_chain<C: ConstraintOps>(
    siblings: Vec<WorkSetNode<C>>,
    leaf: WorkSetNode<C>,
) -> WorkSetNode<C> {
    let mut result = leaf;
    for sibling in siblings.into_iter().rev() {
        result = or_work_set_node(sibling, result);
    }
    result
}

fn step_work_set_or<C: ConstraintOps>(
    left: WorkSetNode<C>,
    right: WorkSetNode<C>,
    terms: &mut TermStore,
) -> WorkSetNodeStep<C> {
    let mut siblings: Vec<WorkSetNode<C>> = vec![right];
    let mut current = left;

    loop {
        match current {
            WorkSetNode::Or(a, b) => {
                siblings.push(*b);
                current = *a;
            }
            WorkSetNode::Fail => match siblings.pop() {
                Some(next) => current = next,
                None => return WorkSetNodeStep::Exhausted,
            },
            _ => break,
        }
    }

    match step_work_set_node(current, terms) {
        WorkSetNodeStep::Emit(nf, new_leaf) => {
            WorkSetNodeStep::Emit(nf, rebuild_work_set_or_chain(siblings, new_leaf))
        }
        WorkSetNodeStep::Continue(new_leaf) => {
            WorkSetNodeStep::Continue(rebuild_work_set_or_chain(siblings, new_leaf))
        }
        WorkSetNodeStep::Exhausted => {
            let rest = rebuild_work_set_or_chain(siblings, WorkSetNode::Fail);
            if matches!(rest, WorkSetNode::Fail) {
                WorkSetNodeStep::Exhausted
            } else {
                WorkSetNodeStep::Continue(rest)
            }
        }
    }
}

fn step_work_set_node<C: ConstraintOps>(
    node: WorkSetNode<C>,
    terms: &mut TermStore,
) -> WorkSetNodeStep<C> {
    match node {
        WorkSetNode::Fail => WorkSetNodeStep::Exhausted,
        WorkSetNode::Or(left, right) => step_work_set_or(*left, *right, terms),
        WorkSetNode::Leaf(work) => match step_work_box(work, terms) {
            WorkStep::Done => WorkSetNodeStep::Continue(WorkSetNode::Fail),
            WorkStep::Emit(nf, next) => WorkSetNodeStep::Emit(nf, WorkSetNode::from_work(*next)),
            WorkStep::Split(left, right) => WorkSetNodeStep::Continue(or_work_set_node(
                WorkSetNode::Leaf(left),
                WorkSetNode::Leaf(right),
            )),
            WorkStep::More(next) => WorkSetNodeStep::Continue(WorkSetNode::Leaf(next)),
        },
    }
}

pub(crate) fn step_work_box<C: ConstraintOps>(
    mut work: Box<Work<C>>,
    terms: &mut TermStore,
) -> WorkStep<C> {
    if let Work::Fix(ref mut fix) = *work {
        return match fix.step_in_place(terms) {
            FixStepResult::Emit(nf) => WorkStep::Emit(nf, work),
            FixStepResult::More => WorkStep::More(work),
            FixStepResult::Done => WorkStep::Done,
        };
    }

    if let Work::Compose(ref mut compose) = *work {
        return match compose.step_in_place(terms) {
            DiagonalStepResult::Emit(nf) => WorkStep::Emit(nf, work),
            DiagonalStepResult::More => WorkStep::More(work),
            DiagonalStepResult::Done => WorkStep::Done,
        };
    }

    if let Work::Meet(ref mut meet) = *work {
        return match meet.step_in_place(terms) {
            DiagonalStepResult::Emit(nf) => WorkStep::Emit(nf, work),
            DiagonalStepResult::More => WorkStep::More(work),
            DiagonalStepResult::Done => WorkStep::Done,
        };
    }

    work.step(terms)
}

/// Call handling mode for PipeWork.
#[derive(Clone, Debug)]
pub enum CallMode<C: ConstraintOps> {
    /// Normal call handling (tabling + producer).
    Normal,
    /// Replay-only for a specific CallKey (used during producer iterations).
    /// The usize is the replay watermark: only answers at index >= watermark
    /// are replayed. This implements semi-naive evaluation by only composing
    /// new (delta) answers in subsequent fixpoint iterations.
    ReplayOnly(Arc<CallKey<C>>, usize),
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

        Rel::Atom(nf) => Node::Emit(Box::new(nf.as_ref().clone()), Box::new(Node::Fail)),

        Rel::Or(a, b) => Node::Or(
            Box::new(rel_to_node(a, env, tables)),
            Box::new(rel_to_node(b, env, tables)),
        ),

        Rel::And(a, b) => {
            let and_rel = Rel::And(a.clone(), b.clone());
            let mut pipe = PipeWork::from_rel(and_rel, env.clone(), tables.clone());
            pipe.call_mode = CallMode::Normal;
            Node::Work(Box::new(Work::Pipe(Box::new(pipe))))
        }

        Rel::Seq(factors) => {
            let factors_rope = Factors::from_seq(factors.clone());
            let mut pipe = PipeWork::with_mid(factors_rope);
            pipe.env = env.clone();
            pipe.tables = tables.clone();
            Node::Work(Box::new(Work::Pipe(Box::new(pipe))))
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
                Node::Work(Box::new(Work::Pipe(Box::new(pipe))))
            }
            None => Node::Fail,
        },
    }
}

fn wrap_work_with_prefix_suffix<C: ConstraintOps>(
    mut work: Work<C>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
) -> WorkStep<C> {
    if let Some(prefix_nf) = prefix {
        work = Work::Compose(ComposeWork::new(Work::Atom(prefix_nf), work));
    }

    if let Some(suffix_nf) = suffix {
        work = Work::Compose(ComposeWork::new(work, Work::Atom(suffix_nf)));
    }

    WorkStep::More(Box::new(work))
}

fn wrap_compose_with_prefix_suffix<C: ConstraintOps>(
    core: ComposeWork<C>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
) -> WorkStep<C> {
    wrap_work_with_prefix_suffix(Work::Compose(core), prefix, suffix)
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

fn nf_domain_filter<C: ConstraintOps>(nf: &NF<C>) -> NF<C> {
    let in_arity = nf.drop_fresh.in_arity;
    NF::new(
        nf.match_pats.clone(),
        DropFresh::identity_with_constraint(in_arity, nf.drop_fresh.constraint.clone()),
        nf.match_pats.clone(),
    )
}

fn nf_range_filter<C: ConstraintOps>(nf: &NF<C>) -> NF<C> {
    let out_arity = nf.drop_fresh.out_arity;
    NF::new(
        nf.build_pats.clone(),
        DropFresh::identity_with_constraint(out_arity, nf.drop_fresh.constraint.clone()),
        nf.build_pats.clone(),
    )
}

/// Root functor tag for indexing NFs by their first pattern's root.
///
/// - `Functor(f)`: the first pattern is `App(f, ...)` with a specific root functor
/// - `Wildcard`: the first pattern is variable-headed or patterns are empty (matches anything)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum RootTag {
    Functor(FuncId),
    Wildcard,
}

/// Extract the root functor tag from a TermId.
/// Returns `Functor(f)` for `App(f, ...)` or inline nullary functors,
/// `Wildcard` for variables or empty.
#[inline]
fn term_root_tag(term_id: TermId, terms: &mut TermStore) -> RootTag {
    if term_id.is_inline_var() {
        return RootTag::Wildcard;
    }
    if term_id.is_inline_nullary() {
        let raw = term_id.inline_nullary_func_raw();
        return match TermStore::func_id_from_raw(raw) {
            Some(f) => RootTag::Functor(f),
            None => RootTag::Wildcard,
        };
    }
    match terms.get_unlocked(term_id) {
        Some(Term::App(f, _)) => RootTag::Functor(*f),
        _ => RootTag::Wildcard,
    }
}

/// Extract the root functor tag of the first build pattern of an NF.
#[inline]
pub(crate) fn build_root_tag<C>(nf: &NF<C>, terms: &mut TermStore) -> RootTag {
    nf.build_pats
        .first()
        .map(|&pat| term_root_tag(pat, terms))
        .unwrap_or(RootTag::Wildcard)
}

/// Extract the root functor tag of the first match pattern of an NF.
#[inline]
pub(crate) fn match_root_tag<C>(nf: &NF<C>, terms: &mut TermStore) -> RootTag {
    nf.match_pats
        .first()
        .map(|&pat| term_root_tag(pat, terms))
        .unwrap_or(RootTag::Wildcard)
}

/// Check if two root tags are compatible for composition.
///
/// Compatible means composition *might* succeed (the root functor precheck won't reject it).
pub(crate) fn tags_compatible(build_tag: RootTag, match_tag: RootTag) -> bool {
    match (build_tag, match_tag) {
        (RootTag::Functor(f), RootTag::Functor(g)) => f == g,
        _ => true, // Wildcard on either side is always compatible
    }
}

/// Extract the root functor tag of child[0] of a term (depth-2 tag).
///
/// For `App(f, [child0, ...])`, returns `term_root_tag(child0)`.
/// For inline nullary (no children), variables, or empty, returns `Wildcard`.
#[inline]
fn term_child0_tag(term_id: TermId, terms: &mut TermStore) -> RootTag {
    if term_id.is_inline() {
        return RootTag::Wildcard; // Inline var or nullary: no children
    }
    match terms.get_unlocked(term_id) {
        Some(Term::App(_, children)) => {
            if let Some(&child0) = children.first() {
                term_root_tag(child0, terms)
            } else {
                RootTag::Wildcard
            }
        }
        _ => RootTag::Wildcard,
    }
}

/// Extract the depth-2 (child[0]) functor tag of the first build pattern of an NF.
#[inline]
pub(crate) fn build_child0_tag<C>(nf: &NF<C>, terms: &mut TermStore) -> RootTag {
    nf.build_pats
        .first()
        .map(|&pat| term_child0_tag(pat, terms))
        .unwrap_or(RootTag::Wildcard)
}

/// Extract the depth-2 (child[0]) functor tag of the first match pattern of an NF.
#[inline]
pub(crate) fn match_child0_tag<C>(nf: &NF<C>, terms: &mut TermStore) -> RootTag {
    nf.match_pats
        .first()
        .map(|&pat| term_child0_tag(pat, terms))
        .unwrap_or(RootTag::Wildcard)
}
