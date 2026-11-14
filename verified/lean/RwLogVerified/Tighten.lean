/-
# Bringing a store to a tight one, on the store

`sorts::always_on` is `Sorts.always`: whether an exclusion always holds.
`sorts::any_always` is that for a list. `sorts::first_sole` finds the first
entry whose variable has values with one root (`Sorts.sole` of its
conjunction and of the terms the exclusions exclude it from).
-/
import RwLogVerified.Open

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## Whether an exclusion always holds -/

/-- The ticks the test may take. -/
def alwaysCost (nm : Option Nat → RwLog.Sym) (E : Eqns Nat) : Nat :=
  solveCost E (encEqs nm E) + 1

/-- `always_on` is `Sorts.always`. -/
theorem always_on_spec (hnm : Function.Injective nm) (s : store.Store) (e : store.TermId)
    {E : Eqns Nat} (hI : Inv s) (he : Repr nm s.nodes.val e.val (encEqs nm E))
    (hroom : Room s (alwaysCost nm E)) :
    sorts.always_on s e ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + alwaysCost nm E ∧
        b = Sorts.always E ⦄ := by
  unfold sorts.always_on
  have hroom' := hroom
  unfold Room at hroom'
  simp only [alwaysCost] at hroom'
  step with solve_into_spec hnm s e e hI he he (by unfold Room; omega)
    as ⟨ok, o', s2, hI2, hx2, ht2, hres⟩
  cases ok with
  | false =>
    simp only [SolveRes, Bool.false_eq_true, ↓reduceIte, Eqns.solveOn, Option.map_eq_none_iff]
      at hres
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hI2, hx2, by simp only [alwaysCost]; omega, ?_⟩
    unfold Sorts.always
    rw [hres]
  | true =>
    simp only [SolveRes, ↓reduceIte, Eqns.solveOn, Option.map_eq_some_iff] at hres
    obtain ⟨t', hrep, ⟨θ, hθ, rfl⟩, -⟩ := hres
    simp only [↓reduceIte]
    step with same_spec s2 o' e hI2 (by unfold Room; omega) as ⟨b, s3, hb, hK⟩
    have ht3 := hK.ticks
    refine ⟨hK.inv, hx2.trans (Extends.of_eq hK.nodes (by omega)), by
      simp only [alwaysCost]; omega, ?_⟩
    have hsame : o'.val = e.val ↔ ∀ w ∈ E.vars, θ w = Term.var w := by
      rw [← enc_bind_eq_iff (nm := nm), Term.bind_var_id]
      constructor
      · intro h
        rw [h] at hrep
        exact hrep.unique (hx2.repr he)
      · intro h
        rw [h] at hrep
        exact Repr.inj hnm hI2.nodesOK hrep (hx2.repr he)
    unfold Sorts.always
    rw [hθ, hb]
    simp only
    rw [Bool.eq_iff_iff, decide_eq_true_eq, hsame, List.all_eq_true]
    simp only [decide_eq_true_eq]

/-- The ticks the test of a list may take. -/
def anyAlwaysCost (nm : Option Nat → RwLog.Sym) : List (Eqns Nat) → Nat
  | [] => 1
  | E :: X => alwaysCost nm E + 1 + anyAlwaysCost nm X

theorem any_always_loop_spec (hnm : Function.Injective nm) :
    ∀ (X : List (Eqns Nat)) (s : store.Store) (xs : store.TermId) (found : Bool),
    Inv s → Repr nm s.nodes.val xs.val (encX nm X) → Room s (anyAlwaysCost nm X) →
    sorts.any_always_loop s xs found true ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + anyAlwaysCost nm X ∧
        b = (found || X.any Sorts.always) ⦄ := by
  intro X
  induction X with
  | nil =>
    intro s xs found hI hxs hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [anyAlwaysCost] at hroom'
    unfold sorts.any_always_loop
    rw [loop]
    simp only [sorts.any_always_loop.body, ↓reduceIte]
    step with uncons_repr s xs hI.toWf (p := Term.sym (nm none)) hxs (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok]
    rw [loop]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [anyAlwaysCost]; omega, by simp⟩
  | cons E X ih =>
    intro s xs found hI hxs hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [anyAlwaysCost] at hroom'
    unfold sorts.any_always_loop
    rw [loop]
    simp only [sorts.any_always_loop.body, ↓reduceIte]
    step with uncons_repr s xs hI.toWf (p := Term.app (encEqs nm E) (encX nm X)) hxs
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨e, rest, rfl, re, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with always_on_spec hnm s1 e K1.inv (hx1.repr re) (by unfold Room; omega)
      as ⟨r2, hI2, hx2, ht2, hb⟩
    obtain ⟨b, s2⟩ := r2
    simp only at hI2 hx2 ht2 hb
    cases b with
    | true =>
      simp only [↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hI2, hx1.trans hx2, by simp only [anyAlwaysCost]; omega, ?_⟩
      simp [← hb]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 rest found hI2 ((hx1.trans hx2).repr rrest) (by unfold Room; omega)
      unfold sorts.any_always_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨b', s'⟩ ⟨hI', hx', ht', hb'⟩
      refine ⟨hI', (hx1.trans hx2).trans hx', by simp only [anyAlwaysCost]; omega, ?_⟩
      simp [hb', ← hb]

/-- `any_always` is whether some exclusion of the list always holds. -/
theorem any_always_spec (hnm : Function.Injective nm) (s : store.Store) (xs : store.TermId)
    {X : List (Eqns Nat)} (hI : Inv s) (hxs : Repr nm s.nodes.val xs.val (encX nm X))
    (hroom : Room s (anyAlwaysCost nm X)) :
    sorts.any_always s xs ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + anyAlwaysCost nm X ∧
        b = X.any Sorts.always ⦄ := by
  unfold sorts.any_always
  refine WP.spec_mono (any_always_loop_spec hnm X s xs false hI hxs hroom) ?_
  rintro ⟨b, s'⟩ ⟨hI', hx', ht', hb⟩
  exact ⟨hI', hx', ht', by simpa using hb⟩

/-! ## The first entry whose values have one root -/

/-- The ticks going through the entries may spend. -/
noncomputable def scanCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r : Nat)
    (X : List (Eqns Nat)) : List (Nat × Sorts.Conj) → Nat
  | [] => 1
  | e :: L => goneCost nm e.1 X + soleAll S u r (Sorts.sumSize (Sorts.gone X e.1)) + 5 +
      scanCost nm S u r X L

/-- What `first_sole` finds in the entries `L`, after those of `acc`. -/
def FoundSole (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (X : List (Eqns Nat))
    (nodes : List store.Node) (acc L : List (Nat × Sorts.Conj)) :
    Option (store.TermId × store.TermId × store.TermId × store.TermId) → Prop
  | none => ∀ e ∈ L, Sorts.sole S e.2 (Sorts.gone X e.1) = none
  | some (v, f, kids, others) => ∃ pre en post κ, L = pre ++ en :: post ∧
      (∀ e ∈ pre, Sorts.sole S e.2 (Sorts.gone X e.1) = none) ∧
      Sorts.sole S en.2 (Sorts.gone X en.1) = some κ ∧ VarAt nodes v.val en.1 ∧
      Repr nm nodes f.val (.sym κ.1) ∧
      Repr nm nodes kids.val
        (encList (nm none) ((altOf S en.2 κ.1 κ.2).map (cpat (nm none) U))) ∧
      Repr nm nodes others.val (encVarEntries nm U (acc ++ pre ++ post))

theorem first_sole_loop_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) {r : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (decls names x : store.TermId) (X : List (Eqns Nat)) :
    ∀ (L acc : List (Nat × Sorts.Conj)) (s : store.Store) (seen es : store.TermId),
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val x.val (encX nm X) → (∀ p ∈ L, Sub U p.2) →
    Repr nm s.nodes.val es.val (encVarEntries nm U L) →
    Repr nm s.nodes.val seen.val (encVarEntries nm U acc) →
    Room s (scanCost nm S U.length r X L + 2 * acc.length) →
    sorts.first_sole_loop s decls names x seen es none true ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + scanCost nm S U.length r X L + 2 * acc.length ∧
        FoundSole nm S U X s'.nodes.val acc.reverse L o ⦄ := by
  intro L
  induction L with
  | nil =>
    intro acc s seen es hI hde hU hx hsub hes hseen hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [scanCost] at hroom'
    unfold sorts.first_sole_loop
    rw [loop]
    simp only [sorts.first_sole_loop.body, ↓reduceIte]
    step with uncons_repr s es hI.toWf (p := Term.sym (nm none)) hes (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok]
    rw [loop]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [scanCost]; omega, by
      intro e he; cases he⟩
  | cons en L ih =>
    intro acc s seen es hI hde hU hx hsub hes hseen hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [scanCost] at hroom'
    unfold sorts.first_sole_loop
    rw [loop]
    simp only [sorts.first_sole_loop.body, ↓reduceIte]
    step with uncons_repr s es hI.toWf (p := Term.app (varEntry nm U en) (encVarEntries nm U L))
      hes (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨e, rest, rfl, re, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with uncons_repr s1 e K1.inv.toWf
      (p := Term.app (Term.var en.1) (cpat (nm none) U en.2)) (hx1.repr re)
      (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1'
    obtain ⟨vi, ci, rfl, rv, rc⟩ := hu1
    have K2 := hK1'.kept K1.inv
    have ht2 := K2.ticks
    have hx2 : Extends s s2 := hx1.trans (Extends.of_eq K2.nodes (by omega))
    have hvv : VarAt s2.nodes.val vi.val en.1 := by
      rw [K2.nodes]
      cases rv with
      | var h => exact h
    step with gone_spec hnm s2 x vi K2.inv hvv (hx2.repr hx) (by unfold Room; omega)
      as ⟨r3, hI3, hx3, ht3, rg⟩
    obtain ⟨g, s3⟩ := r3
    simp only at hI3 hx3 ht3 rg
    have hx03 := hx2.trans hx3
    step with sole_root_spec hC hr en.2 (Sorts.gone X en.1) (hsub en (by simp)) s3 decls names
      ci g hI3 (hx03.repr hde) (hx03.repr hU) (hx3.repr (by rw [K2.nodes]; exact rc)) rg
      (by unfold Room; omega) as ⟨r4, hI4, hx4, ht4, hres⟩
    obtain ⟨o2, s4⟩ := r4
    simp only at hI4 hx4 ht4 hres
    have hx04 := hx03.trans hx4
    cases hso : Sorts.sole S en.2 (Sorts.gone X en.1) with
    | none =>
      rw [hso] at hres
      subst hres
      simp only [uncurry]
      step with alloc_spec s4 (.App e seen) hI4 ⟨(hx04.repr re).lt, (hx04.repr hseen).lt⟩
        (by unfold Room; omega) as ⟨r5, hI5, ht5, htb5, hx5, hr5⟩
      obtain ⟨seen1, s5⟩ := r5
      simp only [norm] at hI5 ht5 htb5 hx5 hr5
      simp only [uncurry, bind_ok]
      have hx05 := hx04.trans hx5
      have rs : Repr nm s5.nodes.val seen1.val (encVarEntries nm U (en :: acc)) :=
        .app hr5 (hx05.repr re) (hx05.repr hseen)
      have IH := ih (en :: acc) s5 seen1 rest hI5 (hx05.repr hde) (hx05.repr hU) (hx05.repr hx)
        (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) (hx05.repr rrest) rs
        (by simp only [List.length_cons]; unfold Room; omega)
      unfold sorts.first_sole_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨o', s'⟩ ⟨hI', hx', ht', hF⟩
      simp only [List.length_cons] at ht'
      refine ⟨hI', hx05.trans hx', by simp only [scanCost]; omega, ?_⟩
      cases o' with
      | none =>
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact hso
        · exact hF e he
      | some q =>
        obtain ⟨v, f, kids, others⟩ := q
        obtain ⟨pre, en', post, κ, rfl, hpre, hs, hv, hf, hk, ho⟩ := hF
        refine ⟨en :: pre, en', post, κ, rfl, ?_, hs, hv, hf, hk, ?_⟩
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact hso
          · exact hpre e he
        · simpa [List.append_assoc] using ho
    | some κ =>
      rw [hso] at hres
      obtain ⟨fi, kids, rfl, rf, rk⟩ := hres
      simp only [uncurry]
      step with rev_onto_spec (acc.map (varEntry nm U)) (L.map (varEntry nm U)) s4 seen rest
        hI4.toWf (hx04.repr hseen) (hx04.repr rrest)
        (by simp only [List.length_map]; unfold Room; omega) as ⟨r5, hR, hr5⟩
      obtain ⟨others, s5⟩ := r5
      simp only [List.length_map] at hR hr5
      have ht5 := hR.ticks
      simp only [uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI4.empty⟩, hx04.trans hR.ext, by
        simp only [scanCost]; omega, [], en, L, κ, rfl, (by intro e he; cases he), hso,
        (hx3.trans (hx4.trans hR.ext)).varAt hvv, hR.ext.repr rf, hR.ext.repr rk, ?_⟩
      simpa [encVarEntries, List.map_append, List.map_reverse] using hr5

/-- The ticks `first_sole` may take. -/
noncomputable def firstSoleCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r : Nat)
    (X : List (Eqns Nat)) (L : List (Nat × Sorts.Conj)) : Nat :=
  scanCost nm S u r X L + 1

/-- `first_sole` finds the first entry whose variable has values with one
root, with that root, the conjunctions of its arguments, and the other
entries in their order; or finds that there is none. -/
theorem first_sole_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) {r : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (s : store.Store) (decls names x es : store.TermId) (X : List (Eqns Nat))
    (L : List (Nat × Sorts.Conj)) (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hx : Repr nm s.nodes.val x.val (encX nm X)) (hsub : ∀ p ∈ L, Sub U p.2)
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (hroom : Room s (firstSoleCost nm S U.length r X L)) :
    sorts.first_sole s decls names x es ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + firstSoleCost nm S U.length r X L ∧
        FoundSole nm S U X s'.nodes.val [] L o ⦄ := by
  unfold sorts.first_sole
  have hroom' := hroom
  unfold Room at hroom'
  simp only [firstSoleCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨seen, s1, hI1, ht1, htb1, hx1, hr1⟩
  have rnil : Repr nm s1.nodes.val seen.val (encVarEntries nm U []) := .nil hr1
  refine WP.spec_mono (first_sole_loop_spec hnm hC hr decls names x X L [] s1 seen es hI1
    (hx1.repr hde) (hx1.repr hU) (hx1.repr hx) hsub (hx1.repr hes) rnil
    (by simp only [List.length_nil]; unfold Room; omega)) ?_
  rintro ⟨o, s'⟩ ⟨hI', hx', ht', hF⟩
  simp only [List.length_nil] at ht'
  exact ⟨hI', hx1.trans hx', by simp only [firstSoleCost]; omega, by simpa using hF⟩

end RwLogVerified
