use super::*;
use crate::constraint::ConstraintOps;
use crate::test_utils::setup;
use smallvec::SmallVec;
use std::sync::Arc;

fn test_program() -> (Arc<ChrProgram>, PredId, PredId) {
    let mut builder = ChrProgramBuilder::new();
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
        .map(|inst| {
            let args = store.args(inst);
            let mut sv: SmallVec<[crate::term::TermId; 4]> = SmallVec::new();
            sv.extend_from_slice(args);
            sv
        })
        .collect()
}

#[test]
fn duplicate_constraints_get_distinct_cids() {
    let (symbols, terms) = setup();
    let (program, p, _) = test_program();
    let mut state = ChrState::new(program);

    let a = terms.app0(symbols.intern("A"));
    let cid1 = state.introduce(p, &[a], &terms);
    let cid2 = state.introduce(p, &[a], &terms);

    assert_ne!(cid1, cid2);
    assert_eq!(alive_args_for_pred(state.store(), p).len(), 2);
}

#[test]
fn empty_constraints_combine_across_programs() {
    let state_a = ChrState::new(ChrProgram::empty());
    let state_b = ChrState::new(ChrProgram::empty());

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

    let mut non_empty = ChrState::new(program);
    let a = terms.app0(symbols.intern("A"));
    non_empty.introduce(p, &[a], &terms);

    let empty = ChrState::new(ChrProgram::empty());
    let combined = empty
        .combine(&non_empty)
        .expect("empty constraint should not block combine");

    assert_eq!(
        combined.program.program_id, non_empty.program.program_id,
        "combined state should keep the non-empty program"
    );
    assert_eq!(
        alive_args_for_pred(combined.store(), p),
        alive_args_for_pred(non_empty.store(), p),
        "combined state should preserve non-empty constraints"
    );
}

#[test]
fn propagation_rule_fires_once_via_token_store() {
    let (symbols, mut terms) = setup();

    let mut builder = ChrProgramBuilder::new();
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
    let mut state = ChrState::new(program);

    let a = terms.app0(symbols.intern("A"));
    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));
    assert_eq!(alive_args_for_pred(state.store(), q).len(), 1);

    // Re-run; should not re-fire propagation.
    assert!(state.solve_to_fixpoint(&mut terms));
    assert_eq!(alive_args_for_pred(state.store(), q).len(), 1);
}

#[test]
fn simplification_removes_head() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
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
    let mut state = ChrState::new(program);
    let a = terms.app0(symbols.intern("A"));
    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));

    assert_eq!(alive_args_for_pred(state.store(), p).len(), 0);
    assert_eq!(alive_args_for_pred(state.store(), q).len(), 1);
}

#[test]
fn simpagation_keeps_kept_head() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
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
    let mut state = ChrState::new(program);
    let a = terms.app0(symbols.intern("A"));
    state.introduce(p, &[a], &terms);
    state.introduce(r, &[a], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));

    assert_eq!(alive_args_for_pred(state.store(), p).len(), 1);
    assert_eq!(alive_args_for_pred(state.store(), r).len(), 0);
    assert_eq!(alive_args_for_pred(state.store(), s).len(), 1);
}

#[test]
fn guard_blocks_rule_on_neq() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
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
    let mut state = ChrState::new(program);
    let a = terms.app0(symbols.intern("A"));
    let b = terms.app0(symbols.intern("B"));

    state.introduce(p, &[a, b], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));
    assert_eq!(alive_args_for_pred(state.store(), q).len(), 0);

    state.introduce(p, &[a, a], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));
    assert_eq!(alive_args_for_pred(state.store(), q).len(), 1);
}

#[test]
fn guard_unbound_rvar_fails() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
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
    let mut state = ChrState::new(program);
    let a = terms.app0(symbols.intern("A"));

    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));
    assert_eq!(alive_args_for_pred(state.store(), q).len(), 0);
}

#[test]
fn join_rejects_duplicate_cid() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
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
    let mut state = ChrState::new(program);
    let a = terms.app0(symbols.intern("A"));

    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));
    assert_eq!(alive_args_for_pred(state.store(), q).len(), 0);

    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));
    assert_eq!(alive_args_for_pred(state.store(), q).len(), 1);
}

#[test]
fn committed_choice_respects_priority() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
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
    let mut state = ChrState::new(program);
    let a = terms.app0(symbols.intern("A"));
    state.introduce(p, &[a], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));

    assert_eq!(alive_args_for_pred(state.store(), q1).len(), 1);
    assert_eq!(alive_args_for_pred(state.store(), q2).len(), 0);
}

#[test]
fn freeze_thaw_remaps_tokens_and_cids() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
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
    let mut state = ChrState::new(program.clone());
    let a = terms.app0(symbols.intern("A"));
    let b = terms.app0(symbols.intern("B"));

    let cid_a = state.introduce(p, &[a], &terms);
    let _cid_b = state.introduce(p, &[b], &terms);
    assert!(state.solve_to_fixpoint(&mut terms));

    // Kill the first constraint to force remapping.
    state.data_mut().store.inst[cid_a.0 as usize].alive = false;
    let frozen = freeze_chr(&state);
    let thawed = thaw_chr(program, &frozen, &terms).expect("thaw should succeed");

    assert_eq!(alive_args_for_pred(thawed.store(), p).len(), 1);
    assert_eq!(alive_args_for_pred(thawed.store(), q).len(), 2);
}

/// Minimal reproduction of the normalize cache collision bug.
///
/// The normalize cache previously used commutative addition to combine
/// per-constraint hashes. Two distinct constraint states whose per-constraint
/// hashes happened to have the same sum would produce the same cache key,
/// causing one to return the other's cached result.
///
/// This test constructs exactly that scenario:
/// - State A: {p(a(z)), p(d(z))} — both constraints pass, normalization = Some
/// - State B: {p(b(z)), p(c(z))} — p(c(z)) triggers "fail", normalization = None
///
/// Under the old additive hash, A and B had the same hash because their
/// arg TermId raw values sum to the same total (indices 0+3 == 1+2).
/// Normalizing A first (cached as Some) caused B to return the stale
/// Some instead of correctly returning None.
#[test]
fn normalize_cache_must_not_return_stale_result_for_additive_collision() {
    let (symbols, terms) = setup();
    let c_sym = symbols.intern("c");

    // Build a CHR program: p/1 where p(X) <=> top_functor(X, c, 1) | fail
    let mut builder = ChrProgramBuilder::new();
    let p = builder.pred("p", 1, vec![]);

    // Head: p(X) where X is RVar(0)
    let x = builder.pat_var(RVar(0));
    let head = HeadPat::new(p, vec![x]);

    // Guard: top_functor(X, c, 1) — checks if X's root functor is `c` with arity 1
    let guard = GuardProg::new(vec![GuardInstr::TopFunctor {
        t: GVal::RVar(RVar(0)),
        f: c_sym,
        arity: 1,
    }]);

    // Body: fail
    let body = BodyProg::new(vec![BodyInstr::Fail]);

    // Simplification rule: removed=[head], kept=[], guard, body
    builder.rule(vec![], vec![head], guard, body, 0);

    let program = builder.build();

    // Create four unary terms. Store allocation is sequential, so:
    //   (a z) → index 0, raw = 0x80000000
    //   (b z) → index 1, raw = 0x80000001
    //   (c z) → index 2, raw = 0x80000002
    //   (d z) → index 3, raw = 0x80000003
    let z = terms.app0(symbols.intern("z"));
    let a_z = terms.app1(symbols.intern("a"), z);
    let b_z = terms.app1(symbols.intern("b"), z);
    let c_z = terms.app1(c_sym, z);
    let d_z = terms.app1(symbols.intern("d"), z);

    // Verify the collision precondition: raw sums must be equal.
    // If TermStore allocation changes, this assertion will catch it
    // and the test needs updating to find new colliding pairs.
    let sum_a = a_z.raw() as u64 + d_z.raw() as u64;
    let sum_b = b_z.raw() as u64 + c_z.raw() as u64;
    assert_eq!(
        sum_a,
        sum_b,
        "Precondition: raw sums must collide for this test to exercise \
         the additive hash weakness. a_z={:#x}, b_z={:#x}, c_z={:#x}, d_z={:#x}",
        a_z.raw(),
        b_z.raw(),
        c_z.raw(),
        d_z.raw(),
    );

    // State A: {p(a(z)), p(d(z))} — neither triggers the c-guard, both pass.
    let mut state_a = ChrState::new(program.clone());
    state_a.introduce(p, &[a_z], &terms);
    state_a.introduce(p, &[d_z], &terms);

    let mut terms_mut = terms;

    // Normalize state A — should succeed (constraints remain alive).
    let result_a = state_a.normalize_owned(&mut terms_mut);
    assert!(result_a.is_some(), "State A should normalize successfully");

    // State B: {p(b(z)), p(c(z))} — p(c(z)) triggers the c-guard → fail.
    let mut state_b = ChrState::new(program.clone());
    state_b.introduce(p, &[b_z], &terms_mut);
    state_b.introduce(p, &[c_z], &terms_mut);

    // Normalize state B — MUST fail (return None).
    // With the old additive hash, this returned Some (stale cache hit from A).
    let result_b = state_b.normalize_owned(&mut terms_mut);
    assert!(
        result_b.is_none(),
        "BUG: State B {{p(b(z)), p(c(z))}} should fail because p(c(z)) \
         triggers the c-guard, but it returned Some. The normalize cache \
         returned a stale result from State A due to a hash collision."
    );
}

// =========================================================================
// Equality builtin tests ($x = $y via BuiltinId(0))
// =========================================================================

/// Rule body posts `$X = val` → normalization extracts the substitution.
#[test]
fn equality_in_body_produces_subst() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
    let p = builder.pred("p", 1, vec![]);

    // Rule: p(X) <=> $X = (a z).
    // When p(Var(0)) is introduced, the body unifies Var(0) with (a z).
    let x = builder.pat_var(RVar(0));
    let head_p = HeadPat::new(p, vec![x]);

    let a_sym = symbols.intern("a");
    let z_sym = symbols.intern("z");
    let z_pat = builder.pat_app(z_sym, vec![]);
    let a_z_pat = builder.pat_app(a_sym, vec![z_pat]);

    let body = BodyProg::new(vec![BodyInstr::AddBuiltin {
        bid: BuiltinId(0),
        args: vec![ArgExpr::RVar(RVar(0)), ArgExpr::Pat(a_z_pat)].into_boxed_slice(),
    }]);
    builder.rule(vec![], vec![head_p], GuardProg::empty(), body, 0);

    let program = builder.build();
    let v0 = terms.var(0);
    let mut state = ChrState::new(program);
    state.introduce(p, &[v0], &terms);

    let (result_state, subst_opt) = state.normalize_owned(&mut terms).expect("should normalize");
    let subst = subst_opt.expect("should produce a substitution from $X = (a z)");

    // Var(0) should be bound to (a z).
    let bound = subst.get(0).expect("Var(0) should be bound");
    let a_z_term = terms.app1(a_sym, terms.app0(z_sym));
    assert_eq!(
        bound, a_z_term,
        "Var(0) should be bound to (a z), got {:?}",
        bound
    );
    // The simplification rule removed p, so no alive constraints remain.
    assert!(
        result_state.is_empty(),
        "p should have been removed by simplification"
    );
}

/// Equality between two ground terms that are structurally the same succeeds.
#[test]
fn equality_of_identical_ground_terms_succeeds() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
    let p = builder.pred("p", 2, vec![]);
    let q = builder.pred("q", 1, vec![]);

    // Rule: p(X, Y) <=> $X = $Y | q(X).
    // When X == Y, the equality succeeds and q(X) is posted.
    let x = builder.pat_var(RVar(0));
    let y = builder.pat_var(RVar(1));
    let head_p = HeadPat::new(p, vec![x, y]);

    let body = BodyProg::new(vec![
        BodyInstr::AddBuiltin {
            bid: BuiltinId(0),
            args: vec![ArgExpr::RVar(RVar(0)), ArgExpr::RVar(RVar(1))].into_boxed_slice(),
        },
        BodyInstr::AddChr {
            pred: q,
            args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
        },
    ]);
    builder.rule(vec![], vec![head_p], GuardProg::empty(), body, 0);

    let program = builder.build();
    let a = terms.app0(symbols.intern("A"));

    let mut state = ChrState::new(program);
    state.introduce(p, &[a, a], &terms);

    let (result_state, _) = state.normalize_owned(&mut terms).expect("should normalize");
    assert_eq!(
        alive_args_for_pred(result_state.store(), q).len(),
        1,
        "q should have been posted since A == A"
    );
}

/// Equality between two different ground terms causes the rule body to fail.
#[test]
fn equality_of_different_ground_terms_fails_body() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
    let p = builder.pred("p", 2, vec![]);
    let q = builder.pred("q", 1, vec![]);

    // Rule: p(X, Y) <=> $X = $Y, q(X).
    // When X != Y, the equality fails and the entire body fails.
    let x = builder.pat_var(RVar(0));
    let y = builder.pat_var(RVar(1));
    let head_p = HeadPat::new(p, vec![x, y]);

    let body = BodyProg::new(vec![
        BodyInstr::AddBuiltin {
            bid: BuiltinId(0),
            args: vec![ArgExpr::RVar(RVar(0)), ArgExpr::RVar(RVar(1))].into_boxed_slice(),
        },
        BodyInstr::AddChr {
            pred: q,
            args: vec![ArgExpr::RVar(RVar(0))].into_boxed_slice(),
        },
    ]);
    builder.rule(vec![], vec![head_p], GuardProg::empty(), body, 0);

    let program = builder.build();
    let a = terms.app0(symbols.intern("A"));
    let b = terms.app0(symbols.intern("B"));

    let mut state = ChrState::new(program);
    state.introduce(p, &[a, b], &terms);

    // Body fails because A != B, so the whole normalization fails.
    let result = state.normalize_owned(&mut terms);
    assert!(
        result.is_none(),
        "Normalization should fail when equality A == B fails in body"
    );
}

/// Structural decomposition: eq(f(a, Var(3)), f(a, b)) binds Var(3) to b.
#[test]
fn equality_structural_decomposition_binds_variable() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
    let p = builder.pred("p", 2, vec![]);

    // Rule: p(X, Y) <=> $X = $Y.
    let x = builder.pat_var(RVar(0));
    let y = builder.pat_var(RVar(1));
    let head_p = HeadPat::new(p, vec![x, y]);

    let body = BodyProg::new(vec![BodyInstr::AddBuiltin {
        bid: BuiltinId(0),
        args: vec![ArgExpr::RVar(RVar(0)), ArgExpr::RVar(RVar(1))].into_boxed_slice(),
    }]);
    builder.rule(vec![], vec![head_p], GuardProg::empty(), body, 0);

    let program = builder.build();
    let f_sym = symbols.intern("f");
    let a = terms.app0(symbols.intern("a"));
    let b = terms.app0(symbols.intern("b"));
    let v3 = terms.var(3);
    let f_a_v3 = terms.app2(f_sym, a, v3);
    let f_a_b = terms.app2(f_sym, a, b);

    let mut state = ChrState::new(program);
    state.introduce(p, &[f_a_v3, f_a_b], &terms);

    let (_result_state, subst_opt) = state.normalize_owned(&mut terms).expect("should normalize");
    let subst = subst_opt.expect("should produce substitution from structural decomposition");

    let bound = subst.get(3).expect("Var(3) should be bound");
    assert_eq!(
        bound, b,
        "Var(3) should be bound to b via structural decomposition"
    );
}

/// Occurs check: unifying Var(0) with f(Var(0)) must fail.
#[test]
fn equality_occurs_check_fails() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
    let p = builder.pred("p", 2, vec![]);

    // Rule: p(X, Y) <=> $X = $Y.
    let x = builder.pat_var(RVar(0));
    let y = builder.pat_var(RVar(1));
    let head_p = HeadPat::new(p, vec![x, y]);

    let body = BodyProg::new(vec![BodyInstr::AddBuiltin {
        bid: BuiltinId(0),
        args: vec![ArgExpr::RVar(RVar(0)), ArgExpr::RVar(RVar(1))].into_boxed_slice(),
    }]);
    builder.rule(vec![], vec![head_p], GuardProg::empty(), body, 0);

    let program = builder.build();
    let f_sym = symbols.intern("f");
    let v0 = terms.var(0);
    let f_v0 = terms.app1(f_sym, v0);

    let mut state = ChrState::new(program);
    state.introduce(p, &[v0, f_v0], &terms);

    let result = state.normalize_owned(&mut terms);
    assert!(
        result.is_none(),
        "Normalization should fail due to occurs check: Var(0) = f(Var(0))"
    );
}

/// Multiple equalities in a single rule body accumulate into one substitution.
#[test]
fn equality_multiple_bindings_accumulate() {
    let (symbols, mut terms) = setup();
    let mut builder = ChrProgramBuilder::new();
    let p = builder.pred("p", 3, vec![]);

    // Rule: p(X, Y, Z) <=> $X = (a), $Y = (b), $Z = (c).
    let x = builder.pat_var(RVar(0));
    let y = builder.pat_var(RVar(1));
    let z = builder.pat_var(RVar(2));
    let head_p = HeadPat::new(p, vec![x, y, z]);

    let a_pat = builder.pat_app(symbols.intern("a"), vec![]);
    let b_pat = builder.pat_app(symbols.intern("b"), vec![]);
    let c_pat = builder.pat_app(symbols.intern("c"), vec![]);

    let body = BodyProg::new(vec![
        BodyInstr::AddBuiltin {
            bid: BuiltinId(0),
            args: vec![ArgExpr::RVar(RVar(0)), ArgExpr::Pat(a_pat)].into_boxed_slice(),
        },
        BodyInstr::AddBuiltin {
            bid: BuiltinId(0),
            args: vec![ArgExpr::RVar(RVar(1)), ArgExpr::Pat(b_pat)].into_boxed_slice(),
        },
        BodyInstr::AddBuiltin {
            bid: BuiltinId(0),
            args: vec![ArgExpr::RVar(RVar(2)), ArgExpr::Pat(c_pat)].into_boxed_slice(),
        },
    ]);
    builder.rule(vec![], vec![head_p], GuardProg::empty(), body, 0);

    let program = builder.build();
    let v0 = terms.var(0);
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    let mut state = ChrState::new(program);
    state.introduce(p, &[v0, v1, v2], &terms);

    let (_result_state, subst_opt) = state.normalize_owned(&mut terms).expect("should normalize");
    let subst = subst_opt.expect("should produce substitution from three equalities");

    let a = terms.app0(symbols.intern("a"));
    let b = terms.app0(symbols.intern("b"));
    let c = terms.app0(symbols.intern("c"));

    assert_eq!(subst.get(0), Some(a), "Var(0) should be bound to a");
    assert_eq!(subst.get(1), Some(b), "Var(1) should be bound to b");
    assert_eq!(subst.get(2), Some(c), "Var(2) should be bound to c");
}
