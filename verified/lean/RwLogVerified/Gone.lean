/-
The terms a variable is excluded from: the ground term an exclusion excludes
a variable from when that is all it says (`unit_on`, against `Sorts.unitOn`),
and those of a list of exclusions (`gone`, against `Sorts.gone`), with their
charges.

`unit_on` solves the equations of the exclusion together with the variable
and the equations themselves as output. The variable is excluded from a term
when the solution gives it a ground term, and replaces the variables of the
equations as replacing the variable by that term does: one comparison of
identifiers, since a term is stored once.
-/
import RwLogVerified.Sole
import RwLogVerified.Iface
import RwLog.Sorts.Gone

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## Ground terms -/

theorem allIn_empty (t : Pat) : AllIn ∅ t ↔ t.vars = [] := by
  simp [AllIn, List.eq_nil_iff_forall_not_mem]

theorem ground?_of_vars : ∀ {p : Pat}, p.vars = [] →
    ∃ g, Sorts.ground? p = some g ∧ p = GTerm.toPat g
  | .var v, h => by simp [Term.vars] at h
  | .sym f, _ => ⟨.sym f, rfl, rfl⟩
  | .app a b, h => by
    simp only [Term.vars, List.append_eq_nil_iff] at h
    obtain ⟨ga, ha, ea⟩ := ground?_of_vars h.1
    obtain ⟨gb, hb, eb⟩ := ground?_of_vars h.2
    refine ⟨.app ga gb, by simp [Sorts.ground?, ha, hb], ?_⟩
    rw [ea, eb]; rfl

theorem ground?_none_of_vars : ∀ {p : Pat}, p.vars ≠ [] → Sorts.ground? p = none
  | .var v, _ => rfl
  | .sym f, h => by simp [Term.vars] at h
  | .app a b, h => by
    by_cases ha : a.vars = []
    · have hb : b.vars ≠ [] := fun hb => h (by simp [Term.vars, ha, hb])
      simp [Sorts.ground?, ground?_none_of_vars hb]
    · simp [Sorts.ground?, ground?_none_of_vars ha]

/-- `ground` answers whether the term has no variable, and leaves table `A`
empty. It spends seven ticks and thirteen for each distinct subterm. -/
theorem ground_spec (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId) {tp : Pat}
    (hI : Inv s) (hp : Repr nm s.nodes.val p.val tp) (hroom : Room s (7 + 13 * tp.subs.card)) :
    cover.ground s p ⦃ b s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s.ticks.val ≤ s'.ticks.val ∧
        s'.ticks.val ≤ s.ticks.val + (7 + 13 * tp.subs.card) ∧ (∀ k, tbl s' .A k = none) ∧
        b = decide (tp.vars = []) ⦄ := by
  unfold cover.ground
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_spec s .A hI (by unfold Room; omega) as ⟨s1, hn1, ht1, hI1, hA1, ho1⟩
  step with clear_spec s1 .B hI1 (by unfold Room; omega) as ⟨s2, hn2, ht2, hI2, hB2, ho2⟩
  have hA2 : ∀ k, tbl s2 .A k = none := fun k => by rw [ho2 .A (by simp)]; exact hA1 k
  have hM : Marked nm s2.nodes.val (tbl s2 .A) ∅ :=
    ⟨fun k hk => absurd (hA2 k) hk, fun t ht => by simp at ht⟩
  have hB : AllOK nm s2.nodes.val (tbl s2 .B) ∅ := fun k w hk => by
    rw [hB2 k] at hk; cases hk
  have hP := pending_card_le (nm := nm) s2.nodes.val (tbl s2 .B) tp.subs
  step with all_marked_spec hnm s2 p tp.subs hI2 (by rw [hn2, hn1]; exact hp) hM hB
    (Finset.Subset.refl _) (by unfold Room; omega) as ⟨b, s3, h3⟩
  have hc := h3.cost
  have hm := h3.mono
  refine ⟨h3.inv, by rw [h3.nodes, hn2, hn1], by omega, by omega, fun k => by
    rw [h3.tblA]; exact hA2 k, ?_⟩
  rw [h3.res]
  exact decide_eq_decide.2 (allIn_empty tp)

/-! ## Two substitutions that do the same to a term -/

theorem bind_eq_iff {σ τ : Nat → Pat} : ∀ t : Pat,
    t.bind σ = t.bind τ ↔ ∀ w ∈ t.vars, σ w = τ w
  | .var v => by simp [Term.vars]
  | .sym f => by simp [Term.vars]
  | .app a b => by
    simp only [Term.bind_app, Term.app.injEq, bind_eq_iff a, bind_eq_iff b, Term.vars,
      List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ w (hw | hw)
      · exact h1 w hw
      · exact h2 w hw
    · exact fun h => ⟨fun w hw => h w (Or.inl hw), fun w hw => h w (Or.inr hw)⟩

theorem enc_bind_eq_iff {σ τ : Nat → Pat} : ∀ E : Eqns Nat,
    (encEqs nm E).bind σ = (encEqs nm E).bind τ ↔ ∀ w ∈ E.vars, σ w = τ w
  | [] => by simp [encEqs, Eqns.vars]
  | p :: E => by
    simp only [encEqs, Term.bind_app, Term.app.injEq, bind_eq_iff, enc_bind_eq_iff E, Eqns.vars,
      List.flatMap_cons, List.mem_append]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ w ((hw | hw) | hw)
      · exact h1 w hw
      · exact h2 w hw
      · exact h3 w hw
    · exact fun h => ⟨⟨fun w hw => h w (Or.inl (Or.inl hw)), fun w hw => h w (Or.inl (Or.inr hw))⟩,
        fun w hw => h w (Or.inr hw)⟩

/-- What an exclusion excludes a variable from, by the solution of its
equations: the solution does to the equations what replacing the variable by
its value does, and the value is ground. -/
theorem unitOn_of_solve {x : Nat} {E : Eqns Nat} {θ : Nat → Pat} (h : solve E = some θ) :
    Sorts.unitOn x E =
      if (encEqs nm E).bind (Term.single x (θ x)) = (encEqs nm E).bind θ then Sorts.ground? (θ x)
      else none := by
  have hiff : (E.vars.all fun w => decide (w = x ∨ θ w = .var w)) = true ↔
      (encEqs nm E).bind (Term.single x (θ x)) = (encEqs nm E).bind θ := by
    rw [enc_bind_eq_iff, List.all_eq_true]
    refine forall_congr' fun w => forall_congr' fun _ => ?_
    rw [decide_eq_true_eq]
    unfold Term.single
    by_cases e : w = x
    · subst e; simp
    · simp only [e, false_or, ↓reduceIte]; exact eq_comm
  unfold Sorts.unitOn
  rw [h]
  simp only
  by_cases hc : (E.vars.all fun w => decide (w = x ∨ θ w = .var w)) = true
  · rw [ite_pos' hc, ite_pos' (hiff.1 hc)]
  · rw [ite_neg' hc, ite_neg' fun h' => hc (hiff.2 h')]

/-! ## The term an exclusion excludes a variable from -/

/-- The ticks `unit_on` may spend. -/
def unitCost (nm : Option Nat → RwLog.Sym) (x : Nat) (E : Eqns Nat) : Nat :=
  solveCost E (.app (.var x) (encEqs nm E)) + 27 * dcount E (.app (.var x) (encEqs nm E)) + 15

/-- `unit_on` gives the ground term the exclusion excludes the variable from
when that is all it says (`Sorts.unitOn`). -/
theorem unit_on_spec (hnm : Function.Injective nm) (s : store.Store) (v e : store.TermId)
    {x : Nat} {E : Eqns Nat} (hI : Inv s) (hv : VarAt s.nodes.val v.val x)
    (he : Repr nm s.nodes.val e.val (encEqs nm E)) (hroom : Room s (unitCost nm x E)) :
    sorts.unit_on s v e ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + unitCost nm x E ∧
        match Sorts.unitOn x E with
        | none => o = none
        | some g => ∃ gi, o = some gi ∧ Repr nm s'.nodes.val gi.val (GTerm.toPat g) ⦄ := by
  unfold sorts.unit_on
  have hroom' := hroom
  unfold Room at hroom'
  simp only [unitCost] at hroom'
  have hDe : (encEqs nm E).subs.card ≤ dcount E (Term.app (Term.var x) (encEqs nm E)) := by
    unfold dcount
    refine Finset.card_le_card fun u hu => ?_
    simp only [Term.subs, Finset.mem_union, Finset.mem_insert]
    exact Or.inr (Or.inr (Or.inr hu))
  step with alloc_spec s (.App v e) hI ⟨hv.lt, he.lt⟩ (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  have ro : Repr nm s1.nodes.val out.val (Term.app (Term.var x) (encEqs nm E)) := .app hr1 (hx1.repr (.var hv)) (hx1.repr he)
  step with solve_into_spec hnm s1 e out hI1 (hx1.repr he) ro (by unfold Room; omega)
    as ⟨ok, o', s2, hI2, hx2, ht2, hres⟩
  have hx12 := hx1.trans hx2
  cases ok with
  | false =>
    simp only [SolveRes, Bool.false_eq_true, ↓reduceIte, Eqns.solveOn, Option.map_eq_none_iff] at hres
    have hU : Sorts.unitOn x E = none := by unfold Sorts.unitOn; rw [hres]
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    rw [hU]
    exact ⟨hI2, hx12, by simp only [unitCost]; omega, rfl⟩
  | true =>
    simp only [SolveRes, ↓reduceIte, Eqns.solveOn, Option.map_eq_some_iff] at hres
    obtain ⟨t', hrep, ⟨θ, hθ, rfl⟩, hcard⟩ := hres
    have hrep' : Repr nm s2.nodes.val o'.val (.app (θ x) ((encEqs nm E).bind θ)) := hrep
    have hDg : (θ x).subs.card ≤ dcount E (Term.app (Term.var x) (encEqs nm E)) := by
      refine le_trans (Finset.card_le_card fun u hu => ?_) hcard
      show u ∈ (Term.app (θ x) ((encEqs nm E).bind θ)).subs
      simp only [Term.subs, Finset.mem_union, Finset.mem_insert]
      exact Or.inr (Or.inl hu)
    simp only [↓reduceIte]
    step with uncons_repr s2 o' hI2.toWf hrep' (by unfold Room; omega) as ⟨oo, s3, hK0, hu⟩
    obtain ⟨g, solved, rfl, rg, rsol⟩ := hu
    have K3 := hK0.kept hI2
    have ht3 := K3.ticks
    have hx3 : Extends s s3 := hx12.trans (Extends.of_eq K3.nodes (by omega))
    simp only
    step with ground_spec hnm s3 g K3.inv (by rw [K3.nodes]; exact rg) (by unfold Room; omega)
      as ⟨b, s4, hI4, hn4, hm4, ht4, hA4, hb⟩
    have hn4' : s4.nodes.val = s2.nodes.val := by rw [hn4, K3.nodes]
    have hx4 : Extends s s4 := hx12.trans (Extends.of_eq hn4' (by omega))
    have hUs := unitOn_of_solve (nm := nm) (x := x) hθ
    cases b with
    | false =>
      have hng : (θ x).vars ≠ [] := by simpa using hb.symm
      have hU : Sorts.unitOn x E = none := by
        rw [hUs, ground?_none_of_vars hng]; simp
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      rw [hU]
      exact ⟨hI4, hx4, by simp only [unitCost]; omega, rfl⟩
    | true =>
      have hgr : (θ x).vars = [] := by simpa using hb.symm
      obtain ⟨g0, hg0, eg0⟩ := ground?_of_vars hgr
      simp only [↓reduceIte]
      have hleaf : LeafOK nm s4.nodes.val (tbl s4 .B) (term.Leaf.Sub v g) (Term.single x (θ x)) :=
        ⟨x, θ x, hx4.varAt hv, by rw [hn4']; exact rg, rfl⟩
      have hpc := pending_card_le (nm := nm) s4.nodes.val (tbl s4 .A) (encEqs nm E).subs
      step with rebuild_spec hnm s4 (term.Leaf.Sub v g) e (t := encEqs nm E)
        (σ := Term.single x (θ x)) (encEqs nm E).subs hI4 (hx4.repr he) hleaf
        (by intro k w hk; rw [hA4 k] at hk; cases hk) (Finset.Subset.refl _)
        (by unfold Room; omega) as ⟨only1, s5, hR5⟩
      have hc5 := hR5.cost
      have hm5 := hR5.mono
      step with same_w s5 only1 solved hR5.inv.toWf (by unfold Room; omega) as ⟨b1, s6, hb1, hK6⟩
      have K6 := hK6.kept hR5.inv
      have ht6 := K6.ticks
      have hx6 : Extends s s6 := (hx4.trans hR5.ext).trans (Extends.of_eq K6.nodes (by omega))
      have rsol5 : Repr nm s5.nodes.val solved.val ((encEqs nm E).bind θ) :=
        hR5.ext.repr (by rw [hn4']; exact rsol)
      have hsame : only1.val = solved.val ↔
          (encEqs nm E).bind (Term.single x (θ x)) = (encEqs nm E).bind θ := by
        constructor
        · intro h
          have := hR5.repr
          rw [h] at this
          exact this.unique rsol5
        · intro h
          have := hR5.repr
          rw [h] at this
          exact Repr.inj hnm hR5.inv.nodesOK this rsol5
      cases b1 with
      | false =>
        have hne : ¬ only1.val = solved.val := by simpa using hb1.symm
        have hU : Sorts.unitOn x E = none := by
          rw [hUs, ite_neg' fun h => hne (hsame.2 h)]
        simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        rw [hU]
        exact ⟨K6.inv, hx6, by simp only [unitCost]; omega, rfl⟩
      | true =>
        have heq : only1.val = solved.val := by simpa using hb1.symm
        have hU : Sorts.unitOn x E = some g0 := by
          rw [hUs, ite_pos' (hsame.1 heq), hg0]
        simp only [↓reduceIte, WP.spec_ok]
        rw [hU]
        refine ⟨K6.inv, hx6, by simp only [unitCost]; omega, g, rfl, ?_⟩
        rw [← eg0, K6.nodes]
        exact hR5.ext.repr (by rw [hn4']; exact rg)

/-! ## The terms a list of exclusions excludes a variable from -/

/-- The ticks going through exclusions may spend. -/
def goneLoopCost (nm : Option Nat → RwLog.Sym) (x : Nat) : List (Eqns Nat) → Nat
  | [] => 1
  | E :: X => unitCost nm x E + 2 + goneLoopCost nm x X

theorem gone_loop_spec (hnm : Function.Injective nm) (v : store.TermId) (x : Nat) :
    ∀ (X : List (Eqns Nat)) (acc : List GTerm) (s : store.Store) (xs out : store.TermId),
    Inv s → VarAt s.nodes.val v.val x →
    Repr nm s.nodes.val xs.val (encList (nm none) (X.map (encEqs nm))) →
    Repr nm s.nodes.val out.val (encList (nm none) (acc.map GTerm.toPat)) →
    Room s (goneLoopCost nm x X) →
    sorts.gone_loop xs s v out ⦃ res =>
      Inv res.1 ∧ Extends s res.1 ∧ res.1.ticks.val ≤ s.ticks.val + goneLoopCost nm x X ∧
        Repr nm res.1.nodes.val res.2.val
          (encList (nm none) (((X.filterMap (Sorts.unitOn x)).reverse ++ acc).map GTerm.toPat)) ⦄ := by
  intro X
  induction X with
  | nil =>
    intro acc s xs out hI hv hxs hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [goneLoopCost] at hroom'
    unfold sorts.gone_loop
    rw [loop]
    simp only [sorts.gone_loop.body]
    step with uncons_repr s xs hI.toWf hxs (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    simp only [uncurry, bind_ok, WP.spec_ok]
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by have := K1.ticks; omega), by
      have := K1.ticks; simp only [goneLoopCost]; omega, ?_⟩
    rw [K1.nodes]
    simpa using hout
  | cons E X ih =>
    intro acc s xs out hI hv hxs hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [goneLoopCost] at hroom'
    unfold sorts.gone_loop
    rw [loop]
    simp only [sorts.gone_loop.body]
    step with uncons_repr s xs hI.toWf hxs (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨e, t, rfl, re, rt⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with unit_on_spec hnm s1 v e K1.inv (hx1.varAt hv) (hx1.repr re)
      (by unfold Room; omega) as ⟨r1, hI2, hx2, ht2, hres⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hI2 hx2 ht2 hres
    have hx12 := hx1.trans hx2
    cases hU : Sorts.unitOn x E with
    | none =>
      rw [hU] at hres
      subst hres
      simp only [uncurry, bind_ok]
      have IH := ih acc s2 t out hI2 (hx12.varAt hv) (hx12.repr rt) (hx12.repr hout)
        (by unfold Room; omega)
      unfold sorts.gone_loop at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx12.trans hx', by simp only [goneLoopCost]; omega, ?_⟩
      simpa only [List.filterMap_cons, hU] using hr'
    | some g0 =>
      rw [hU] at hres
      obtain ⟨gi, rfl, rgi⟩ := hres
      simp only [uncurry]
      step with alloc_spec s2 (.App gi out) hI2 ⟨rgi.lt, (hx12.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r3, hI3, ht3, htb3, hx3, hr3⟩
      obtain ⟨out1, s3⟩ := r3
      simp only [norm] at hI3 ht3 htb3 hx3 hr3
      simp only [uncurry, bind_ok]
      have rout1 : Repr nm s3.nodes.val out1.val
          (encList (nm none) ((g0 :: acc).map GTerm.toPat)) :=
        .app hr3 (hx3.repr rgi) (hx3.repr (hx12.repr hout))
      have hx13 := hx12.trans hx3
      have IH := ih (g0 :: acc) s3 t out1 hI3 (hx13.varAt hv) (hx13.repr rt) rout1
        (by unfold Room; omega)
      unfold sorts.gone_loop at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx13.trans hx', by simp only [goneLoopCost]; omega, ?_⟩
      simpa only [List.filterMap_cons, hU, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hr'

/-- The ticks `gone` may spend. -/
def goneCost (nm : Option Nat → RwLog.Sym) (x : Nat) (X : List (Eqns Nat)) : Nat :=
  goneLoopCost nm x X + 2 * X.length + 3

/-- `gone` lists the terms the exclusions exclude the variable from
(`Sorts.gone`), in their order. -/
theorem gone_spec (hnm : Function.Injective nm) (s : store.Store) (xs v : store.TermId)
    {x : Nat} {X : List (Eqns Nat)} (hI : Inv s) (hv : VarAt s.nodes.val v.val x)
    (hxs : Repr nm s.nodes.val xs.val (encList (nm none) (X.map (encEqs nm))))
    (hroom : Room s (goneCost nm x X)) :
    sorts.gone s xs v ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + goneCost nm x X ∧
        Repr nm s'.nodes.val r.val (encList (nm none) ((Sorts.gone X x).map GTerm.toPat)) ⦄ := by
  unfold sorts.gone
  have hroom' := hroom
  unfold Room at hroom'
  simp only [goneCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  have rnil : Repr nm s1.nodes.val out.val
      (encList (nm none) (([] : List GTerm).map GTerm.toPat)) := .nil hr1
  step with gone_loop_spec hnm v x X [] s1 xs out hI1 (hx1.varAt hv) (hx1.repr hxs) rnil
    (by unfold Room; omega) as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  have hlen : (X.filterMap (Sorts.unitOn x)).length ≤ X.length := List.length_filterMap_le _ _
  simp only [List.append_nil] at hr2
  step with rev_spec _ s2 out1 hI2.toWf hr2
    (by simp only [List.length_map, List.length_reverse]; unfold Room; omega)
    as ⟨r, s3, hR3, hr3⟩
  simp only [List.length_map, List.length_reverse] at hR3
  have ht3 := hR3.ticks
  refine ⟨⟨hR3.wf, by rw [hR3.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR3.ext, by
    simp only [goneCost]; omega, ?_⟩
  simpa only [Sorts.gone, ← List.map_reverse, List.reverse_reverse] using hr3

end RwLogVerified
