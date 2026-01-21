use super::*;
use crate::constraint::ConstraintOps;
use crate::term::TermStore;
use crate::test_utils::setup;
use smallvec::SmallVec;
use std::sync::Arc;

#[derive(Clone, Default)]
struct TestStore {
    bindings: Vec<(u32, crate::term::TermId)>,
}

struct TestTheory;

impl Theory for TestTheory {
    type Store = TestStore;

    fn entails_eq(store: &Self::Store, a: crate::term::TermId, b: crate::term::TermId) -> bool {
        let _ = store;
        a == b
    }

    fn entails_neq(_store: &Self::Store, a: crate::term::TermId, b: crate::term::TermId) -> bool {
        a != b
    }

    fn extract_subst(store: &Self::Store) -> crate::subst::Subst {
        let mut subst = crate::subst::Subst::new();
        for (v, t) in store.bindings.iter().copied() {
            subst.bind(v, t);
        }
        subst
    }

    fn merge_store(a: &Self::Store, b: &Self::Store) -> Option<Self::Store> {
        let mut merged = a.clone();
        for (v, t) in b.bindings.iter().copied() {
            if let Some(existing) = merged.bindings.iter().find(|(ev, _)| *ev == v) {
                if existing.1 != t {
                    return None;
                }
            } else {
                merged.bindings.push((v, t));
            }
        }
        Some(merged)
    }

    fn apply_subst(
        store: &Self::Store,
        subst: &crate::subst::Subst,
        terms: &TermStore,
    ) -> Self::Store {
        let mut out = store.clone();
        for (_, t) in out.bindings.iter_mut() {
            *t = crate::subst::apply_subst(*t, subst, terms);
        }
        out
    }

    fn freeze_store(store: &Self::Store) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(store.bindings.len() as u32).to_le_bytes());
        for (v, t) in store.bindings.iter().copied() {
            out.extend_from_slice(&v.to_le_bytes());
            out.extend_from_slice(&t.raw().to_le_bytes());
        }
        out
    }

    fn thaw_store(bytes: &[u8]) -> Self::Store {
        let mut i = 0;
        if bytes.len() < 4 {
            return TestStore::default();
        }
        let mut count_bytes = [0u8; 4];
        count_bytes.copy_from_slice(&bytes[i..i + 4]);
        i += 4;
        let count = u32::from_le_bytes(count_bytes) as usize;
        let mut bindings = Vec::with_capacity(count);
        for _ in 0..count {
            if i + 8 > bytes.len() {
                break;
            }
            let mut v_bytes = [0u8; 4];
            let mut t_bytes = [0u8; 4];
            v_bytes.copy_from_slice(&bytes[i..i + 4]);
            i += 4;
            t_bytes.copy_from_slice(&bytes[i..i + 4]);
            i += 4;
            let v = u32::from_le_bytes(v_bytes);
            let t = crate::term::TermId::from_raw(u32::from_le_bytes(t_bytes));
            bindings.push((v, t));
        }
        TestStore { bindings }
    }

    fn remap_vars(store: &Self::Store, map: &[Option<u32>], terms: &TermStore) -> Self::Store {
        let mut out = store.clone();
        for (v, t) in out.bindings.iter_mut() {
            if (*v as usize) < map.len() {
                if let Some(new_v) = map[*v as usize] {
                    *v = new_v;
                }
            }
            *t = crate::nf::apply_var_renaming(*t, map, terms);
        }
        out
    }

    fn collect_vars(store: &Self::Store, terms: &TermStore, out: &mut Vec<u32>) {
        for (v, t) in store.bindings.iter().copied() {
            out.push(v);
            out.extend(crate::nf::collect_vars_ordered(t, terms));
        }
    }

    fn is_empty(store: &Self::Store) -> bool {
        store.bindings.is_empty()
    }
}

fn bind_builtin() -> Builtin<TestTheory> {
    Builtin {
        arity: 2,
        guard: |_store, _terms, _args| true,
        add: |store, terms, args| {
            if args.len() != 2 {
                return false;
            }
            let v = match terms.is_var(args[0]) {
                Some(idx) => idx,
                None => return false,
            };
            store.bindings.push((v, args[1]));
            true
        },
    }
}

fn test_program() -> (Arc<ChrProgram<TestTheory>>, PredId, PredId) {
    let mut builtins = BuiltinRegistry::default();
    builtins.builtins.push(bind_builtin());

    let mut builder = ChrProgramBuilder::<TestTheory>::new(builtins);
    let p = builder.pred("p", 1, vec![]);
    let q = builder.pred("q", 1, vec![]);
    let _ = builder.pred("r", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let head_p = HeadPat::new(p, vec![x]);
    let body_q = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);

    builder.rule(vec![head_p], vec![], GuardProg::empty(), body_q, 0);

    (builder.build(), p, q)
}

fn alive_args_for_pred(store: &ChrStore, pred: PredId) -> Vec<SmallVec<[crate::term::TermId; 4]>> {
    store
        .inst
        .iter()
        .filter(|inst| inst.alive && inst.pred == pred)
        .map(|inst| inst.args.clone())
        .collect()
}

#[test]
fn duplicate_constraints_get_distinct_cids() {
    let (symbols, terms) = setup();
    let (program, p, _) = test_program();
    let mut state = ChrState::new(program, TestStore::default());

    let a = terms.app0(symbols.intern("A"));
    let cid1 = state.introduce(p, &[a], &terms);
    let cid2 = state.introduce(p, &[a], &terms);

    assert_ne!(cid1, cid2);
    assert_eq!(alive_args_for_pred(&state.store, p).len(), 2);
}

#[test]
fn empty_constraints_combine_across_programs() {
    let state_a: ChrState<TestTheory> = ChrState::new(ChrProgram::empty(), TestStore::default());
    let state_b: ChrState<TestTheory> = ChrState::new(ChrProgram::empty(), TestStore::default());

    let combined = state_a
        .combine(&state_b)
        .expect("empty constraints should combine");
    assert!(
        combined.is_empty(),
        "combined constraint should remain empty"
    );
}

#[test]
fn empty_constraint_combines_with_non_empty_other_program() {
    let (symbols, terms) = setup();
    let (program, p, _) = test_program();

    let mut non_empty = ChrState::new(program, TestStore::default());
    let a = terms.app0(symbols.intern("A"));
    non_empty.introduce(p, &[a], &terms);

    let empty: ChrState<TestTheory> = ChrState::new(ChrProgram::empty(), TestStore::default());
    let combined = empty
        .combine(&non_empty)
        .expect("empty constraint should not block combine");

    assert_eq!(
        combined.program.program_id, non_empty.program.program_id,
        "combined state should keep the non-empty program"
    );
    assert_eq!(
        alive_args_for_pred(&combined.store, p),
        alive_args_for_pred(&non_empty.store, p),
        "combined state should preserve non-empty constraints"
    );
}

#[test]
fn propagation_rule_fires_once_via_token_store() {
    let (symbols, terms) = setup();
    let mut builtins = BuiltinRegistry::default();
    builtins.builtins.push(bind_builtin());

    let mut builder = ChrProgramBuilder::<TestTheory>::new(builtins);
    let p = builder.pred("p", 1, vec![]);
    let q = builder.pred("q", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let head_p = HeadPat::new(p, vec![x]);
    let body_q = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);
    builder.rule(vec![head_p], vec![], GuardProg::empty(), body_q, 0);

    let program = builder.build();
    let mut state = ChrState::new(program, TestStore::default());

    let a = terms.app0(symbols.intern("A"));
    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&terms));
    assert_eq!(alive_args_for_pred(&state.store, q).len(), 1);

    // Re-run; should not re-fire propagation.
    assert!(state.solve_to_fixpoint(&terms));
    assert_eq!(alive_args_for_pred(&state.store, q).len(), 1);
}

#[test]
fn simplification_removes_head() {
    let (symbols, terms) = setup();
    let mut builder = ChrProgramBuilder::<TestTheory>::new(BuiltinRegistry::default());
    let p = builder.pred("p", 1, vec![]);
    let q = builder.pred("q", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let head_p = HeadPat::new(p, vec![x]);
    let body_q = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);
    builder.rule(vec![], vec![head_p], GuardProg::empty(), body_q, 0);

    let program = builder.build();
    let mut state = ChrState::new(program, TestStore::default());
    let a = terms.app0(symbols.intern("A"));
    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&terms));

    assert_eq!(alive_args_for_pred(&state.store, p).len(), 0);
    assert_eq!(alive_args_for_pred(&state.store, q).len(), 1);
}

#[test]
fn simpagation_keeps_kept_head() {
    let (symbols, terms) = setup();
    let mut builder = ChrProgramBuilder::<TestTheory>::new(BuiltinRegistry::default());
    let p = builder.pred("p", 1, vec![]);
    let r = builder.pred("r", 1, vec![]);
    let s = builder.pred("s", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let head_p = HeadPat::new(p, vec![x]);
    let head_r = HeadPat::new(r, vec![x]);
    let body_s = BodyProg::new(vec![BodyInstr::AddChr {
        pred: s,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);
    builder.rule(vec![head_p], vec![head_r], GuardProg::empty(), body_s, 0);

    let program = builder.build();
    let mut state = ChrState::new(program, TestStore::default());
    let a = terms.app0(symbols.intern("A"));
    state.introduce(p, &[a], &terms);
    state.introduce(r, &[a], &terms);
    assert!(state.solve_to_fixpoint(&terms));

    assert_eq!(alive_args_for_pred(&state.store, p).len(), 1);
    assert_eq!(alive_args_for_pred(&state.store, r).len(), 0);
    assert_eq!(alive_args_for_pred(&state.store, s).len(), 1);
}

#[test]
fn guard_blocks_rule_on_neq() {
    let (symbols, terms) = setup();
    let mut builder = ChrProgramBuilder::<TestTheory>::new(BuiltinRegistry::default());
    let p = builder.pred("p", 2, vec![]);
    let q = builder.pred("q", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let y = builder.pat_var(RVar(1));
    let head_p = HeadPat::new(p, vec![x, y]);
    let guard = GuardProg::new(vec![GuardInstr::Eq(
        GVal::RVar(RVar(0)),
        GVal::RVar(RVar(1)),
    )]);
    let body_q = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);
    builder.rule(vec![], vec![head_p], guard, body_q, 0);

    let program = builder.build();
    let mut state = ChrState::new(program, TestStore::default());
    let a = terms.app0(symbols.intern("A"));
    let b = terms.app0(symbols.intern("B"));

    state.introduce(p, &[a, b], &terms);
    assert!(state.solve_to_fixpoint(&terms));
    assert_eq!(alive_args_for_pred(&state.store, q).len(), 0);

    state.introduce(p, &[a, a], &terms);
    assert!(state.solve_to_fixpoint(&terms));
    assert_eq!(alive_args_for_pred(&state.store, q).len(), 1);
}

#[test]
fn guard_unbound_rvar_fails() {
    let (symbols, terms) = setup();
    let mut builder = ChrProgramBuilder::<TestTheory>::new(BuiltinRegistry::default());
    let p = builder.pred("p", 1, vec![]);
    let q = builder.pred("q", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let head_p = HeadPat::new(p, vec![x]);
    let guard = GuardProg::new(vec![GuardInstr::Eq(
        GVal::RVar(RVar(1)),
        GVal::RVar(RVar(0)),
    )]);
    let body_q = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);
    builder.rule(vec![], vec![head_p], guard, body_q, 0);

    let program = builder.build();
    let mut state = ChrState::new(program, TestStore::default());
    let a = terms.app0(symbols.intern("A"));

    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&terms));
    assert_eq!(alive_args_for_pred(&state.store, q).len(), 0);
}

#[test]
fn join_rejects_duplicate_cid() {
    let (symbols, terms) = setup();
    let mut builder = ChrProgramBuilder::<TestTheory>::new(BuiltinRegistry::default());
    let p = builder.pred("p", 1, vec![]);
    let q = builder.pred("q", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let head1 = HeadPat::new(p, vec![x]);
    let head2 = HeadPat::new(p, vec![x]);
    let body_q = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);
    builder.rule(vec![head1, head2], vec![], GuardProg::empty(), body_q, 0);

    let program = builder.build();
    let mut state = ChrState::new(program, TestStore::default());
    let a = terms.app0(symbols.intern("A"));

    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&terms));
    assert_eq!(alive_args_for_pred(&state.store, q).len(), 0);

    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&terms));
    assert_eq!(alive_args_for_pred(&state.store, q).len(), 1);
}

#[test]
fn committed_choice_respects_priority() {
    let (symbols, terms) = setup();
    let mut builder = ChrProgramBuilder::<TestTheory>::new(BuiltinRegistry::default());
    let p = builder.pred("p", 1, vec![]);
    let q1 = builder.pred("q1", 1, vec![]);
    let q2 = builder.pred("q2", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let head_p = HeadPat::new(p, vec![x]);
    let body_q1 = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q1,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);
    let body_q2 = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q2,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);

    builder.rule(
        vec![],
        vec![head_p.clone()],
        GuardProg::empty(),
        body_q1,
        10,
    );
    builder.rule(vec![], vec![head_p], GuardProg::empty(), body_q2, 0);

    let program = builder.build();
    let mut state = ChrState::new(program, TestStore::default());
    let a = terms.app0(symbols.intern("A"));
    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&terms));

    assert_eq!(alive_args_for_pred(&state.store, q1).len(), 1);
    assert_eq!(alive_args_for_pred(&state.store, q2).len(), 0);
}

#[test]
fn freeze_thaw_remaps_tokens_and_cids() {
    let (symbols, terms) = setup();
    let mut builder = ChrProgramBuilder::<TestTheory>::new(BuiltinRegistry::default());
    let p = builder.pred("p", 1, vec![]);
    let q = builder.pred("q", 1, vec![]);

    let x = builder.pat_var(RVar(0));
    let head_p = HeadPat::new(p, vec![x]);
    let body_q = BodyProg::new(vec![BodyInstr::AddChr {
        pred: q,
        args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
    }]);
    builder.rule(vec![head_p], vec![], GuardProg::empty(), body_q, 0);

    let program = builder.build();
    let mut state = ChrState::new(program.clone(), TestStore::default());
    let a = terms.app0(symbols.intern("A"));
    let b = terms.app0(symbols.intern("B"));

    let cid_a = state.introduce(p, &[a], &terms);
    let _cid_b = state.introduce(p, &[b], &terms);
    assert!(state.solve_to_fixpoint(&terms));

    // Kill the first constraint to force remapping.
    state.store.inst[cid_a.0 as usize].alive = false;
    let frozen = freeze_chr(&state);
    let thawed = thaw_chr(program, &frozen, &terms).expect("thaw should succeed");

    assert_eq!(alive_args_for_pred(&thawed.store, p).len(), 1);
    assert_eq!(alive_args_for_pred(&thawed.store, q).len(), 2);
}
