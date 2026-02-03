//! Compilation from Rel AST to node graph.
//!
//! This module transforms the Rel IR into a dataflow graph of nodes
//! that can be executed by the scheduler.

use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::rel::{Rel, RelId};
use crate::runtime::node::{JoinOp, Node, NodeId};
use crate::runtime::scheduler::Runtime;
use crate::term::TermStore;
use std::collections::HashMap;
use std::sync::Arc;

/// Compile a Rel expression into the runtime, returning the root node ID.
///
/// The `env` maps Fix-bound RelIds to their Table node IDs.
/// This is populated during compilation when Fix nodes are encountered.
pub fn compile_rel<C: ConstraintOps>(
    rel: &Rel<C>,
    env: &mut HashMap<RelId, NodeId>,
    runtime: &mut Runtime<C>,
    terms: &mut TermStore,
) -> Option<NodeId> {
    match rel {
        Rel::Zero => {
            // Zero relation - never produces outputs.
            // We represent this as an Atom node with an impossible NF,
            // but actually we should just return None to indicate failure.
            // For now, create a table node that has no body (always empty).
            let id = NodeId::new(runtime.nodes.len() as u32);
            let node = Node::table(id, "__zero__".to_string());
            runtime.add_node(node);
            Some(id)
        }

        Rel::Atom(nf) => {
            let id = NodeId::new(runtime.nodes.len() as u32);
            let node = Node::atom(id, (**nf).clone(), terms);
            runtime.add_node(node);
            Some(id)
        }

        Rel::Or(a, b) => {
            let left = compile_rel(a, env, runtime, terms)?;
            let right = compile_rel(b, env, runtime, terms)?;

            let id = NodeId::new(runtime.nodes.len() as u32);
            let node = Node::or(id, left, right);
            runtime.add_node(node);

            runtime.add_edge(left, id);
            runtime.add_edge(right, id);

            Some(id)
        }

        Rel::And(a, b) => {
            let left = compile_rel(a, env, runtime, terms)?;
            let right = compile_rel(b, env, runtime, terms)?;

            let id = NodeId::new(runtime.nodes.len() as u32);
            let node = Node::join(id, left, right, JoinOp::Meet);
            runtime.add_node(node);

            runtime.add_edge(left, id);
            runtime.add_edge(right, id);

            Some(id)
        }

        Rel::Seq(parts) => {
            if parts.is_empty() {
                // Empty Seq is identity - create an empty table
                let id = NodeId::new(runtime.nodes.len() as u32);
                let node = Node::table(id, "__identity__".to_string());
                runtime.add_node(node);
                return Some(id);
            }

            // Compile first part
            let mut cur = compile_rel(&parts[0], env, runtime, terms)?;

            // Chain remaining parts with Compose joins
            for part in parts.iter().skip(1) {
                let next = compile_rel(part, env, runtime, terms)?;

                let id = NodeId::new(runtime.nodes.len() as u32);
                let node = Node::join(id, cur, next, JoinOp::Compose);
                runtime.add_node(node);

                runtime.add_edge(cur, id);
                runtime.add_edge(next, id);

                cur = id;
            }

            Some(cur)
        }

        Rel::Fix(rel_id, body) => {
            // Create table node first (before compiling body)
            let table_id = NodeId::new(runtime.nodes.len() as u32);
            let table_node = Node::table(table_id, format!("fix_{}", rel_id));
            runtime.add_node(table_node);

            // Register in environment so Call nodes can find it
            env.insert(*rel_id, table_id);

            // Compile body
            let body_id = compile_rel(body, env, runtime, terms)?;

            // Set body root
            if let Some(table) = runtime.get_node_mut(table_id) {
                table.set_body_root(body_id);
            }
            runtime.add_edge(body_id, table_id);

            Some(table_id)
        }

        Rel::Call(rel_id) => {
            // Look up the table for this RelId
            let table_id = env.get(rel_id).copied()?;

            let id = NodeId::new(runtime.nodes.len() as u32);
            let node = Node::call(id, table_id);
            runtime.add_node(node);

            runtime.add_edge(table_id, id);

            Some(id)
        }
    }
}

/// Compile a top-level program with definitions and a query.
///
/// Returns the root node ID for the query.
pub fn compile_program<C: ConstraintOps>(
    defs: &[(RelId, Rel<C>)],
    query: &Rel<C>,
    runtime: &mut Runtime<C>,
    terms: &mut TermStore,
) -> Option<NodeId> {
    let mut env: HashMap<RelId, NodeId> = HashMap::new();

    // First pass: create table nodes for all definitions
    for (rel_id, _) in defs {
        let table_id = NodeId::new(runtime.nodes.len() as u32);
        let table_node = Node::table(table_id, format!("def_{}", rel_id));
        runtime.add_node(table_node);
        env.insert(*rel_id, table_id);
    }

    // Second pass: compile bodies and link them
    for (rel_id, body) in defs {
        let table_id = env.get(rel_id).copied()?;
        let body_id = compile_rel(body, &mut env, runtime, terms)?;

        if let Some(table) = runtime.get_node_mut(table_id) {
            table.set_body_root(body_id);
        }
        runtime.add_edge(body_id, table_id);
    }

    // Compile query
    compile_rel(query, &mut env, runtime, terms)
}

/// Helper to create an Atom relation from an NF.
pub fn atom<C: ConstraintOps>(nf: NF<C>) -> Rel<C> {
    Rel::Atom(Arc::new(nf))
}

/// Helper to create a Seq relation from parts.
pub fn seq<C: ConstraintOps>(parts: Vec<Rel<C>>) -> Rel<C> {
    Rel::Seq(Arc::from(parts.into_iter().map(Arc::new).collect::<Vec<_>>()))
}

/// Helper to create an Or relation.
pub fn or<C: ConstraintOps>(a: Rel<C>, b: Rel<C>) -> Rel<C> {
    Rel::Or(Arc::new(a), Arc::new(b))
}

/// Helper to create an And relation.
pub fn and<C: ConstraintOps>(a: Rel<C>, b: Rel<C>) -> Rel<C> {
    Rel::And(Arc::new(a), Arc::new(b))
}

/// Helper to create a Fix relation.
pub fn fix<C: ConstraintOps>(id: RelId, body: Rel<C>) -> Rel<C> {
    Rel::Fix(id, Arc::new(body))
}

/// Helper to create a Call relation.
pub fn call<C: ConstraintOps>(id: RelId) -> Rel<C> {
    Rel::Call(id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;
    use smallvec::smallvec;

    fn setup() -> (SymbolStore, TermStore) {
        (SymbolStore::new(), TermStore::new())
    }

    // ========================================================================
    // BASIC COMPILATION TESTS
    // ========================================================================

    #[test]
    fn compile_atom() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let rel: Rel<()> = atom(nf);

        let mut runtime: Runtime<()> = Runtime::new();
        let mut env = HashMap::new();
        let id = compile_rel(&rel, &mut env, &mut runtime, &mut terms);

        assert!(id.is_some());
        assert_eq!(runtime.nodes.len(), 1);
    }

    #[test]
    fn compile_or() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let s_z = terms.app1(s, z_term);

        let nf1: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);
        let nf2: NF<()> = NF::new(smallvec![s_z], smallvec![s_z]);

        let rel: Rel<()> = or(atom(nf1), atom(nf2));

        let mut runtime: Runtime<()> = Runtime::new();
        let mut env = HashMap::new();
        let id = compile_rel(&rel, &mut env, &mut runtime, &mut terms);

        assert!(id.is_some());
        // 2 atoms + 1 or
        assert_eq!(runtime.nodes.len(), 3);
    }

    #[test]
    fn compile_and() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let rel: Rel<()> = and(atom(nf.clone()), atom(nf));

        let mut runtime: Runtime<()> = Runtime::new();
        let mut env = HashMap::new();
        let id = compile_rel(&rel, &mut env, &mut runtime, &mut terms);

        assert!(id.is_some());
        // 2 atoms + 1 join
        assert_eq!(runtime.nodes.len(), 3);
    }

    #[test]
    fn compile_seq() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let rel: Rel<()> = seq(vec![atom(nf.clone()), atom(nf.clone()), atom(nf)]);

        let mut runtime: Runtime<()> = Runtime::new();
        let mut env = HashMap::new();
        let id = compile_rel(&rel, &mut env, &mut runtime, &mut terms);

        assert!(id.is_some());
        // 3 atoms + 2 compose joins
        assert_eq!(runtime.nodes.len(), 5);
    }

    #[test]
    fn compile_fix_and_call() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Fix(0, Or(Atom, Call(0)))
        let rel: Rel<()> = fix(0, or(atom(nf), call(0)));

        let mut runtime: Runtime<()> = Runtime::new();
        let mut env = HashMap::new();
        let id = compile_rel(&rel, &mut env, &mut runtime, &mut terms);

        assert!(id.is_some());
        // 1 table + 1 atom + 1 call + 1 or
        assert_eq!(runtime.nodes.len(), 4);

        // Check that the table has a body root
        let table = runtime.get_node(id.unwrap()).unwrap();
        assert!(table.body_root().is_some());
    }

    // ========================================================================
    // PROGRAM COMPILATION TESTS
    // ========================================================================

    #[test]
    fn compile_program_with_defs() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Define: 0 -> Or(Atom, Call(0))
        let defs: Vec<(RelId, Rel<()>)> = vec![(0, or(atom(nf.clone()), call(0)))];

        // Query: Call(0)
        let query: Rel<()> = call(0);

        let mut runtime: Runtime<()> = Runtime::new();
        let id = compile_program(&defs, &query, &mut runtime, &mut terms);

        assert!(id.is_some());
        // 1 table (def_0) + 1 atom + 1 call (in body) + 1 or + 1 call (query)
        assert_eq!(runtime.nodes.len(), 5);
    }

    // ========================================================================
    // PEANO ADDITION EXAMPLE
    // ========================================================================

    #[test]
    fn compile_peano_add() {
        let (symbols, mut terms) = setup();

        // Constructors
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let cons = symbols.intern("cons");

        // Terms
        let z_term = terms.app0(z);
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Base case: (cons z x) -> x
        let cons_z_x = terms.app2(cons, z_term, v0);
        let nf_base: NF<()> = NF::new(smallvec![cons_z_x], smallvec![v0]);

        // Recursive step:
        // pre: (cons (s n) x) -> (cons n x)
        let s_v0 = terms.app1(s, v0);
        let cons_sn_x = terms.app2(cons, s_v0, v1);
        let cons_n_x = terms.app2(cons, v0, v1);
        let nf_pre: NF<()> = NF::new(smallvec![cons_sn_x], smallvec![cons_n_x]);

        // post: x -> (s x)
        let nf_post: NF<()> = NF::new(smallvec![v0], smallvec![s_v0]);

        // add = Or(Atom(base), Seq(Atom(pre), Call(add), Atom(post)))
        // Using Fix(0, ...) where 0 is the add relation
        let add_body: Rel<()> = or(
            atom(nf_base),
            seq(vec![atom(nf_pre), call(0), atom(nf_post)]),
        );
        let add: Rel<()> = fix(0, add_body);

        let mut runtime: Runtime<()> = Runtime::new();
        let mut env = HashMap::new();
        let id = compile_rel(&add, &mut env, &mut runtime, &mut terms);

        assert!(id.is_some());

        // Structure:
        // - 1 table (for Fix)
        // - 1 atom (base)
        // - 1 atom (pre)
        // - 1 call (recursive)
        // - 1 atom (post)
        // - 2 compose joins (for seq of 3)
        // - 1 or
        assert_eq!(runtime.nodes.len(), 8);
    }
}
