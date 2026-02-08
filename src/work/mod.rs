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
use crate::term::{TermId, TermStore};
use smallvec::SmallVec;
use std::sync::Arc;

mod and_group;
mod compose;
mod diagonal;
mod fix;
mod join_receiver;
mod meet;
mod pipe;

pub use and_group::{AndGroup, AndGroupConfig};
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
    ReplayOnly(Arc<CallKey<C>>),
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

fn node_from_answers<C: ConstraintOps>(answers: &[NF<C>]) -> Node<C> {
    let mut node = Node::Fail;
    for nf in answers.iter().rev() {
        node = Node::Emit(nf.clone(), Box::new(node));
    }
    node
}

fn wrap_compose_with_prefix_suffix<C: ConstraintOps>(
    core: ComposeWork<C>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
) -> WorkStep<C> {
    let mut node = Node::Work(Box::new(Work::Compose(core)));

    if let Some(prefix_nf) = prefix {
        let prefix_node = Node::Emit(prefix_nf, Box::new(Node::Fail));
        node = Node::Work(Box::new(Work::Compose(ComposeWork::new(prefix_node, node))));
    }

    if let Some(suffix_nf) = suffix {
        let suffix_node = Node::Emit(suffix_nf, Box::new(Node::Fail));
        node = Node::Work(Box::new(Work::Compose(ComposeWork::new(node, suffix_node))));
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

fn nf_domain_filter<C: ConstraintOps>(nf: &NF<C>) -> NF<C> {
    let in_arity = nf.drop_fresh.in_arity;
    NF::new(
        nf.match_pats.clone(),
        DropFresh::identity_with_constraint(in_arity, nf.drop_fresh.constraint.clone()),
        nf.match_pats.clone(),
    )
}
