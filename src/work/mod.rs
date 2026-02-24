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
            Node::Work(Box::new(Work::AndGroup(AndGroup::new(nodes))))
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

fn node_from_answers<C: ConstraintOps>(answers: Vec<NF<C>>) -> Node<C> {
    let mut node = Node::Fail;
    for nf in answers.into_iter().rev() {
        node = Node::Emit(Box::new(nf), Box::new(node));
    }
    node
}

fn wrap_node_with_prefix_suffix<C: ConstraintOps>(
    mut node: Node<C>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
    terms: &mut TermStore,
) -> WorkStep<C> {
    if let Some(prefix_nf) = prefix {
        let prefix_node = Node::Emit(Box::new(prefix_nf), Box::new(Node::Fail));
        node = Node::Work(Box::new(Work::Compose(ComposeWork::new_preseed(
            prefix_node,
            node,
            terms,
        ))));
    }

    if let Some(suffix_nf) = suffix {
        let suffix_node = Node::Emit(Box::new(suffix_nf), Box::new(Node::Fail));
        node = Node::Work(Box::new(Work::Compose(ComposeWork::new_preseed(
            node,
            suffix_node,
            terms,
        ))));
    }

    match node {
        Node::Work(work) => WorkStep::More(work),
        _ => WorkStep::Done,
    }
}

fn wrap_compose_with_prefix_suffix<C: ConstraintOps>(
    core: ComposeWork<C>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
    terms: &mut TermStore,
) -> WorkStep<C> {
    let node = Node::Work(Box::new(Work::Compose(core)));
    wrap_node_with_prefix_suffix(node, prefix, suffix, terms)
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
