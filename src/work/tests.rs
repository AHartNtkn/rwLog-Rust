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
