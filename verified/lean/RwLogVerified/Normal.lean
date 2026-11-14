/-
# The normal store of a problem, on the store

`sorts::start` builds a store that denotes pairs whose first parts are what
a problem denotes (`Prob.begin_spec`): the equations solved, the variables
left numbered by first occurrence, the sorts pushed down to the variables,
and the pattern paired with the tuple of all the variables. `sorts::normal`
tightens it, numbers it, normalises its exclusions and cuts it to the first
part of the pair, which is the normal store of the problem (`Prob.norm`).
-/
import RwLogVerified.Assemble
import RwLogVerified.Number
import RwLogVerified.Tight
import RwLog.Sorts.Norm

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The sorts of the patterns pushed down -/

/-- The ticks pushing the sorts of a list of sorted patterns may take. -/
noncomputable def pairsCost (S : Sorts) (Ns : Finset Name) : List (Name × Pat) → Nat
  | [] => 1
  | a :: L => pushCost S Ns a.2 + 2 * (Ns.card * a.2.subs.card) + 3 + pairsCost S Ns L

/-- A bound on the number of atoms the sorts of a list of sorted patterns
put on their variables. -/
def atomsMax (Ns : Finset Name) : List (Name × Pat) → Nat
  | [] => 0
  | a :: L => Ns.card * a.2.subs.card + atomsMax Ns L

/-- What pushing the sorts of a list of sorted patterns gives: atoms in
front of the ones there were that hold exactly when every pattern is in its
sort, or a pattern no instance of which is in its sort. -/
def PairsRes (nm : Option Nat → RwLog.Sym) (S : Sorts) (Ns : Finset Name)
    (nodes : List store.Node) (L : List (Name × Pat)) (acc : Sorts.Atoms) (ok : Bool)
    (out : store.TermId) : Prop :=
  if ok then ∃ A : Sorts.Atoms,
    Repr nm nodes out.val (encList (nm none) ((A ++ acc).map atomPat)) ∧
      (∀ a ∈ A, a.2 ∈ Ns ∧ ∃ b ∈ L, a.1 ∈ b.2.vars) ∧ A.length ≤ atomsMax Ns L ∧
      ∀ σ : Nat → GTerm,
        (∀ a ∈ L, Sorts.mem S a.1 (a.2.bind σ) = true) ↔ Sorts.Atoms.Holds S A σ
  else ∃ a ∈ L, ∀ σ : Nat → GTerm, Sorts.mem S a.1 (a.2.bind σ) = false

theorem push_pairs_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (decls : store.TermId) :
    ∀ (L : List (Name × Pat)) (s : store.Store) (out l : store.TermId) (acc : Sorts.Atoms),
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val l.val (encList (nm none) (L.map ppair)) →
    Repr nm s.nodes.val out.val (encList (nm none) (acc.map atomPat)) →
    (∀ a ∈ L, a.1 ∈ Ns ∧ a.2.firstOrder = true) → Room s (pairsCost S Ns L) →
    sorts.push_pairs_loop s decls out l true true ⦃ s' out' ok' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + pairsCost S Ns L ∧
        PairsRes nm S Ns s'.nodes.val L acc ok' out' ⦄ := by
  intro L
  induction L with
  | nil =>
    intro s out l acc hI hd hl hout hin hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [pairsCost] at hroom'
    unfold sorts.push_pairs_loop
    rw [loop]
    simp only [sorts.push_pairs_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
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
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [pairsCost]; omega, ?_⟩
    simp only [PairsRes, ↓reduceIte]
    exact ⟨[], (by rw [K1.nodes]; exact hout), fun a ha => (by cases ha), (by simp), fun σ => (by
      simp [Sorts.Atoms.Holds])⟩
  | cons a L ih =>
    intro s out l acc hI hd hl hout hin hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [pairsCost] at hroom'
    obtain ⟨haN, hafo⟩ := hin a List.mem_cons_self
    unfold sorts.push_pairs_loop
    rw [loop]
    simp only [sorts.push_pairs_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf (p := Term.app (ppair a) (encList (nm none) (L.map ppair)))
      hl (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ei, rest, rfl, re, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with uncons_repr s1 ei K1.inv.toWf (p := Term.app (Term.sym a.1) a.2) (hx1.repr re)
      (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1'
    obtain ⟨ni, pi, rfl, rn, rp⟩ := hu1
    have K2 := hK1'.kept K1.inv
    have ht2 := K2.ticks
    have hx12 : Extends s1 s2 := Extends.of_eq K2.nodes (by omega)
    have hx2 : Extends s s2 := hx1.trans hx12
    step with push_sort_spec hnm S hS Ns a.2 hafo haN hNs s2 decls ni pi K2.inv (hx2.repr hd)
      (hx12.repr rn) (hx12.repr rp) (by unfold Room; omega) as ⟨r3, hI3, hx3, hA3, ht3, hres⟩
    obtain ⟨o3, s3⟩ := r3
    simp only at hI3 hx3 hA3 ht3 hres
    have hx03 := hx2.trans hx3
    cases o3 with
    | none =>
      simp only at hres
      simp only [uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hI3, hx03, by simp only [pairsCost]; omega, ?_⟩
      simp only [PairsRes, Bool.false_eq_true, ↓reduceIte]
      exact ⟨a, List.mem_cons_self, hres⟩
    | some atoms =>
      simp only at hres
      obtain ⟨A1, hrA, hnd, hA1, hsem⟩ := hres
      have hlen := atoms_length_le hnd hA1
      simp only [uncurry]
      step with rev_onto_spec (A1.map atomPat) (acc.map atomPat) s3 atoms out hI3.toWf hrA
        (hx03.repr hout) (by simp only [List.length_map]; unfold Room; omega) as ⟨r4, hR, hr4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only [List.length_map] at hR hr4
      have ht4 := hR.ticks
      have hI4 : Inv s4 := ⟨hR.wf, by rw [hR.stk]; exact hI3.empty⟩
      have hx04 := hx03.trans hR.ext
      simp only [uncurry, bind_ok]
      have IH := ih s4 out1 rest (A1.reverse ++ acc) hI4 (hx04.repr hd) (hx04.repr rrest)
        (by simpa [List.map_append, List.map_reverse] using hr4)
        (fun m hm => hin m (List.mem_cons_of_mem _ hm)) (by unfold Room; omega)
      unfold sorts.push_pairs_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out', ok'⟩ ⟨hI', hx', ht', hP⟩
      refine ⟨hI', hx04.trans hx', by simp only [pairsCost]; omega, ?_⟩
      cases ok' with
      | true =>
        simp only [PairsRes, ↓reduceIte] at hP ⊢
        obtain ⟨A, hr, hA, hAl, hs⟩ := hP
        refine ⟨A ++ A1.reverse, by rw [List.append_assoc]; exact hr, ?_, ?_, fun σ => ?_⟩
        · intro b hb
          rcases List.mem_append.1 hb with hb | hb
          · obtain ⟨h1, c, hc, h2⟩ := hA b hb
            exact ⟨h1, c, List.mem_cons_of_mem _ hc, h2⟩
          · obtain ⟨h1, h2⟩ := hA1 b (List.mem_reverse.1 hb)
            exact ⟨h1, a, List.mem_cons_self, var_mem_subs_iff.1 h2⟩
        · simp only [List.length_append, List.length_reverse, atomsMax]
          omega
        · rw [Sorts.Atoms.holds_append, holds_reverse, ← hs σ, ← hsem σ, List.forall_mem_cons]
          exact and_comm
      | false =>
        simp only [PairsRes, Bool.false_eq_true, ↓reduceIte] at hP ⊢
        obtain ⟨m, hm, hσ⟩ := hP
        exact ⟨m, List.mem_cons_of_mem _ hm, hσ⟩

/-- `push_pairs` pushes the sort of each pattern of a list down to its
variables. -/
theorem push_pairs_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (L : List (Name × Pat)) (s : store.Store) (decls l : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hl : Repr nm s.nodes.val l.val (encList (nm none) (L.map ppair)))
    (hin : ∀ a ∈ L, a.1 ∈ Ns ∧ a.2.firstOrder = true) (hroom : Room s (pairsCost S Ns L + 1)) :
    sorts.push_pairs s decls l ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + pairsCost S Ns L + 1 ∧
        match o with
        | some out => PairsRes nm S Ns s'.nodes.val L [] true out
        | none => ∃ a ∈ L, ∀ σ : Nat → GTerm, Sorts.mem S a.1 (a.2.bind σ) = false ⦄ := by
  unfold sorts.push_pairs
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with push_pairs_loop_spec hnm S hS Ns hNs decls L s1 out l [] hI1 (hx1.repr hd)
    (hx1.repr hl) (.nil hr1) hin (by unfold Room; omega) as ⟨s2, out1, ok1, hI2, hx2, ht2, hP⟩
  cases ok1 with
  | true =>
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨hI2, hx1.trans hx2, by omega, hP⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [PairsRes, Bool.false_eq_true, ↓reduceIte] at hP
    exact ⟨hI2, hx1.trans hx2, by omega, hP⟩

/-! ## An entry for each variable -/

theorem entries_of_loop_spec (hnm : Function.Injective nm) (U : List Name) (A : Sorts.Atoms)
    (names atoms : store.TermId) :
    ∀ (V : List Nat) (s : store.Store) (l out : store.TermId) (O : List Pat),
    Inv s → Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val atoms.val (encList (nm none) (A.map atomPat)) →
    Repr nm s.nodes.val l.val (encList (nm none) (V.map Term.var)) →
    Repr nm s.nodes.val out.val (encList (nm none) O) →
    Room s (repCost (upsCost U.length A.length + 3) V.length) →
    sorts.entries_of_loop l s names atoms out ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + repCost (upsCost U.length A.length + 3) V.length ∧
        Repr nm s'.nodes.val out'.val (encList (nm none)
          ((V.map fun v => varEntry nm U (v, Sorts.upsOf A v)).reverse ++ O)) ⦄ := by
  intro V
  induction V with
  | nil =>
    intro s l out O hI hU hA hl hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, repCost] at hroom'
    unfold sorts.entries_of_loop
    rw [loop]
    simp only [sorts.entries_of_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val +
          repCost (upsCost U.length A.length + 3) ([] : List Nat).length ∧
        Repr nm s1.nodes.val out.val (encList (nm none)
          ((([] : List Nat).map fun v => varEntry nm U (v, Sorts.upsOf A v)).reverse ++ O)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil, repCost]; omega,
        by rw [K1.nodes]; simpa using hout⟩
    step*
  | cons v V ih =>
    intro s l out O hI hU hA hl hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, repCost] at hroom'
    unfold sorts.entries_of_loop
    rw [loop]
    simp only [sorts.entries_of_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (Term.var v) (encList (nm none) (V.map Term.var))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨vi, rest, rfl, rv, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    have hv : VarAt s.nodes.val vi.val v := by
      cases rv with
      | var h => exact h
    step with ups_spec hnm U A s1 names atoms vi K1.inv (hx1.repr hU) (hx1.repr hA)
      (hx1.varAt hv) (by unfold Room; omega) as ⟨r2, hI2, hx2, hB2, ht2, hr2⟩
    obtain ⟨c, s2⟩ := r2
    simp only at hI2 hx2 hB2 ht2 hr2
    have hx02 := hx1.trans hx2
    step with alloc_spec s2 (.App vi c) hI2 ⟨(hx02.varAt hv).lt, hr2.lt⟩
      (by unfold Room; omega) as ⟨r3, hI3, ht3, htb3, hx3, hr3⟩
    obtain ⟨e, s3⟩ := r3
    simp only [norm] at hI3 ht3 htb3 hx3 hr3
    have hx03 := hx02.trans hx3
    have re : Repr nm s3.nodes.val e.val (varEntry nm U (v, Sorts.upsOf A v)) :=
      .app hr3 (.var (hx03.varAt hv)) (hx3.repr hr2)
    step with alloc_spec s3 (.App e out) hI3 ⟨re.lt, (hx03.repr hout).lt⟩
      (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
    obtain ⟨out1, s4⟩ := r4
    simp only [norm] at hI4 ht4 htb4 hx4 hr4
    have hx04 := hx03.trans hx4
    have hout1 : Repr nm s4.nodes.val out1.val
        (encList (nm none) (varEntry nm U (v, Sorts.upsOf A v) :: O)) :=
      .app hr4 (hx4.repr re) (hx04.repr hout)
    simp only [uncurry, bind_ok]
    have IH := ih s4 rest out1 (varEntry nm U (v, Sorts.upsOf A v) :: O) hI4 (hx04.repr hU)
      (hx04.repr hA) (hx04.repr rrest) hout1 (by unfold Room; omega)
    unfold sorts.entries_of_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
    refine ⟨hI', hx04.trans hx', by simp only [List.length_cons, repCost]; omega, ?_⟩
    simpa using hr'

/-- The ticks `entries_of` may take for `k` variables, `u` names and `a`
atoms. -/
def entriesCost (u a k : Nat) : Nat := repCost (upsCost u a + 3) k + 2 * k + 3

/-- `entries_of` gives each variable of a list with the conjunction of the
sorts the atoms put on it. -/
theorem entries_of_spec (hnm : Function.Injective nm) (U : List Name) (A : Sorts.Atoms)
    (V : List Nat) (s : store.Store) (names atoms l : store.TermId) (hI : Inv s)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hA : Repr nm s.nodes.val atoms.val (encList (nm none) (A.map atomPat)))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) (V.map Term.var)))
    (hroom : Room s (entriesCost U.length A.length V.length)) :
    sorts.entries_of s names atoms l ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + entriesCost U.length A.length V.length ∧
        Repr nm s'.nodes.val r.val
          (encVarEntries nm U (V.map fun v => (v, Sorts.upsOf A v))) ⦄ := by
  unfold sorts.entries_of
  have hroom' := hroom
  unfold Room at hroom'
  simp only [entriesCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with entries_of_loop_spec hnm U A names atoms V s1 l out [] hI1 (hx1.repr hU)
    (hx1.repr hA) (hx1.repr hl) (.nil hr1) (by unfold Room; omega)
    as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  simp only [List.append_nil] at hr2
  refine WP.spec_mono (rev_spec _ s2 out1 hI2.toWf hr2
    (by simp only [List.length_reverse, List.length_map]; unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  simp only [List.length_reverse, List.length_map, List.reverse_reverse] at hR hr
  have ht3 := hR.ticks
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext,
    by simp only [entriesCost]; omega, ?_⟩
  unfold encVarEntries
  simpa [List.map_map, Function.comp_def] using hr

/-! ## The tuple of the variables -/

/-- The members of a list paired onto a term, the last outermost. -/
def tupOnto (z : Sym) (V : List Nat) (T : Pat) : Pat :=
  V.foldl (fun acc v => .app (.app (.sym z) (.var v)) acc) T

theorem tupOnto_range (n : Nat) : tupOnto "" (List.range n) (.sym "") = Sorts.tup n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, tupOnto, List.foldl_append]
    show Term.app (Term.app (Term.sym "") (Term.var n)) (tupOnto "" (List.range n) (.sym "")) = _
    rw [ih]
    rfl

theorem tuple_loop_spec (nil : store.TermId) :
    ∀ (V : List Nat) (s : store.Store) (l out : store.TermId) (T : Pat),
    Inv s → Repr nm s.nodes.val nil.val (.sym (nm none)) →
    Repr nm s.nodes.val l.val (encList (nm none) (V.map Term.var)) →
    Repr nm s.nodes.val out.val T → Room s (3 * V.length + 1) →
    sorts.tuple_loop l s nil out ⦃ out' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 3 * V.length + 1 ∧
        Repr nm s'.nodes.val out'.val (tupOnto (nm none) V T) ⦄ := by
  intro V
  induction V with
  | nil =>
    intro s l out T hI hnil hl hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.tuple_loop
    rw [loop]
    simp only [sorts.tuple_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + 3 * ([] : List Nat).length + 1 ∧
        Repr nm s1.nodes.val out.val (tupOnto (nm none) [] T) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
        by rw [K1.nodes]; exact hout⟩
    step*
  | cons v V ih =>
    intro s l out T hI hnil hl hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.tuple_loop
    rw [loop]
    simp only [sorts.tuple_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (Term.var v) (encList (nm none) (V.map Term.var))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨vi, rest, rfl, rv, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with alloc_spec s1 (.App nil vi) K1.inv ⟨(hx1.repr hnil).lt, (hx1.repr rv).lt⟩
      (by unfold Room; omega) as ⟨r2, hI2, ht2, htb2, hx2, hr2⟩
    obtain ⟨head, s2⟩ := r2
    simp only [norm] at hI2 ht2 htb2 hx2 hr2
    have hx02 := hx1.trans hx2
    have rh : Repr nm s2.nodes.val head.val (.app (.sym (nm none)) (.var v)) :=
      .app hr2 (hx02.repr hnil) (hx02.repr rv)
    step with alloc_spec s2 (.App head out) hI2 ⟨rh.lt, (hx02.repr hout).lt⟩
      (by unfold Room; omega) as ⟨r3, hI3, ht3, htb3, hx3, hr3⟩
    obtain ⟨out1, s3⟩ := r3
    simp only [norm] at hI3 ht3 htb3 hx3 hr3
    have hx03 := hx02.trans hx3
    have hout1 : Repr nm s3.nodes.val out1.val
        (.app (.app (.sym (nm none)) (.var v)) T) :=
      .app hr3 (hx3.repr rh) (hx03.repr hout)
    simp only [uncurry, bind_ok]
    have IH := ih s3 rest out1 _ hI3 (hx03.repr hnil) (hx03.repr rrest) hout1
      (by unfold Room; omega)
    unfold sorts.tuple_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨out', s'⟩ ⟨hI', hx', ht', hr'⟩
    exact ⟨hI', hx03.trans hx', by simp only [List.length_cons]; omega, hr'⟩

/-- `tuple` gives the tuple of the first variables. -/
theorem tuple_spec (hz : nm none = "") (n : Nat) (s : store.Store) (nil l : store.TermId)
    (hI : Inv s) (hnil : Repr nm s.nodes.val nil.val (.sym (nm none)))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) ((List.range n).map Term.var)))
    (hroom : Room s (3 * n + 1)) :
    sorts.tuple s nil l ⦃ out s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 3 * n + 1 ∧
        Repr nm s'.nodes.val out.val (Sorts.tup n) ⦄ := by
  unfold sorts.tuple
  refine WP.spec_mono (tuple_loop_spec nil (List.range n) s l nil _ hI hnil hl hnil
    (by simpa using hroom)) ?_
  rintro ⟨out, s'⟩ ⟨hI', hx', ht', hr'⟩
  rw [hz, tupOnto_range] at hr'
  exact ⟨hI', hx', by simpa using ht', hr'⟩

/-! ## The store a problem starts from -/

/-- A pattern, sorted patterns and exclusions as one term. -/
def pack3 (nm : Option Nat → RwLog.Sym) (T : Pat) (A : List (Name × Pat)) (X : List (Eqns Nat)) :
    Pat :=
  .app T (.app (encList (nm none) (A.map ppair)) (encX nm X))

theorem pack3_bind (σ : Nat → Pat) (T : Pat) (A : List (Name × Pat)) (X : List (Eqns Nat)) :
    (pack3 nm T A X).bind σ =
      pack3 nm (T.bind σ) (A.map fun a => (a.1, a.2.bind σ))
        (X.map fun E => E.map fun p => (p.1.bind σ, p.2.bind σ)) := by
  simp only [pack3, Term.bind_app, encX, encList_bind, List.map_map]
  congr 3
  refine List.map_congr_left fun E _ => ?_
  simp only [Function.comp_apply, encEqs_bind]

theorem mem_vars_encEqs {v : Nat} :
    ∀ {E : Eqns Nat}, v ∈ (encEqs nm E).vars ↔ ∃ p ∈ E, v ∈ p.1.vars ∨ v ∈ p.2.vars
  | [] => by simp [encEqs, Term.vars]
  | p :: E => by simp [encEqs, Term.vars, mem_vars_encEqs (E := E), or_assoc]

theorem mem_vars_pack3 {v : Nat} {T : Pat} {A : List (Name × Pat)} {X : List (Eqns Nat)} :
    v ∈ (pack3 nm T A X).vars ↔ v ∈ T.vars ∨ (∃ a ∈ A, v ∈ a.2.vars) ∨
      ∃ E ∈ X, ∃ p ∈ E, v ∈ p.1.vars ∨ v ∈ p.2.vars := by
  simp only [pack3, Term.vars, List.mem_append, encX, mem_vars_encList, List.mem_map,
    exists_exists_and_eq_and, mem_vars_encEqs, ppair, List.nil_append]

/-- The variables left once the equations of a problem are solved, in the
order they first occur in the pattern, the sorted patterns and the
exclusions. -/
def leftVars (nm : Option Nat → RwLog.Sym) (P : Sorts.Prob) (θ : Nat → Pat) : List Nat :=
  Sorts.firsts ((pack3 nm P.t P.a P.x).bind θ).vars

theorem mem_occ {P : Sorts.Prob} {θ : Nat → Pat} {v : Nat} :
    v ∈ P.occ θ ↔ v ∈ (P.t.bind θ).vars ∨ (∃ a ∈ P.a, v ∈ (a.2.bind θ).vars) ∨
      ∃ E ∈ P.x, ∃ p ∈ E, v ∈ (p.1.bind θ).vars ∨ v ∈ (p.2.bind θ).vars := by
  simp [Sorts.Prob.occ]

theorem mem_leftVars {P : Sorts.Prob} {θ : Nat → Pat} {v : Nat} :
    v ∈ leftVars nm P θ ↔ v ∈ P.occ θ := by
  unfold leftVars
  rw [(Sorts.firsts_spec _).2.1, pack3_bind, mem_vars_pack3, mem_occ]
  simp only [List.mem_map, exists_exists_and_eq_and]

/-- The sorted patterns of the starting store. -/
def sortedOf (P : Sorts.Prob) (θ : Nat → Pat) (F : List Nat) : List (Name × Pat) :=
  P.a.map fun a => (a.1, (a.2.bind θ).rename fun v => F.idxOf v)

/-- The exclusions of the starting store. -/
def exclOf (P : Sorts.Prob) (θ : Nat → Pat) (F : List Nat) : List (Eqns Nat) :=
  P.x.map fun E => E.map fun p =>
    ((p.1.bind θ).rename fun v => F.idxOf v, (p.2.bind θ).rename fun v => F.idxOf v)

/-- The starting store: the pattern paired with the tuple of the variables,
the exclusions, and for each variable the sorts the atoms put on it. -/
def startSt (P : Sorts.Prob) (θ : Nat → Pat) (F : List Nat) (A : Sorts.Atoms) : TSt :=
  ⟨Sorts.tpair ((P.t.bind θ).rename fun v => F.idxOf v) (Sorts.tup F.length), exclOf P θ F,
    (List.range F.length).map fun v => (v, Sorts.upsOf A v), F.length⟩

/-- The solved parts of a problem, numbered. -/
theorem pack_num (P : Sorts.Prob) (θ : Nat → Pat) :
    ((pack3 nm P.t P.a P.x).bind θ).bind (numSub (leftVars nm P θ)) =
      pack3 nm ((P.t.bind θ).rename fun v => (leftVars nm P θ).idxOf v)
        (sortedOf P θ (leftVars nm P θ)) (exclOf P θ (leftVars nm P θ)) := by
  have hin : ∀ v, v ∈ P.occ θ → v ∈ leftVars nm P θ := fun v hv => mem_leftVars.2 hv
  rw [pack3_bind, pack3_bind]
  have e1 : (P.t.bind θ).bind (numSub (leftVars nm P θ)) =
      (P.t.bind θ).rename fun v => (leftVars nm P θ).idxOf v :=
    bind_numSub fun v hv => hin v (mem_occ.2 (.inl hv))
  have e2 : ((P.a.map fun a => (a.1, a.2.bind θ)).map fun a : Name × Pat =>
      (a.1, a.2.bind (numSub (leftVars nm P θ)))) = sortedOf P θ (leftVars nm P θ) := by
    simp only [List.map_map, sortedOf]
    refine List.map_congr_left fun a ha => ?_
    simp only [Function.comp_apply]
    rw [bind_numSub fun v hv => hin v (mem_occ.2 (.inr (.inl ⟨a, ha, hv⟩)))]
  have e3 : ((P.x.map fun E => E.map fun p => (p.1.bind θ, p.2.bind θ)).map fun E : Eqns Nat =>
      E.map fun p => (p.1.bind (numSub (leftVars nm P θ)),
        p.2.bind (numSub (leftVars nm P θ)))) = exclOf P θ (leftVars nm P θ) := by
    simp only [List.map_map, exclOf]
    refine List.map_congr_left fun E hE => ?_
    simp only [Function.comp_apply, List.map_map]
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp_apply]
    rw [bind_numSub fun v hv => hin v (mem_occ.2 (.inr (.inr ⟨E, hE, p, hp, .inl hv⟩))),
      bind_numSub fun v hv => hin v (mem_occ.2 (.inr (.inr ⟨E, hE, p, hp, .inr hv⟩)))]
  rw [e1, e2, e3]

theorem map_idxOf_self {F : List Nat} (h : F.Nodup) : F.map (fun v => F.idxOf v) = List.range F.length := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact h.idxOf_getElem i (by simpa using h1)

theorem repCost_mono_left {c c' : Nat} (h : c ≤ c') : ∀ n, repCost c n ≤ repCost c' n
  | 0 => Nat.le_refl _
  | n + 1 => by simp only [repCost]; have := repCost_mono_left h n; omega

theorem entriesCost_mono (u k : Nat) {a a' : Nat} (h : a ≤ a') :
    entriesCost u a k ≤ entriesCost u a' k := by
  unfold entriesCost
  have := repCost_mono_left (c := upsCost u a + 3) (c' := upsCost u a' + 3)
    (by unfold upsCost; omega) k
  omega

/-- The ticks `start` may take once the equations are solved by `θ`. -/
noncomputable def startRest (nm : Option Nat → RwLog.Sym) (S : Sorts) (u : Nat) (P : Sorts.Prob)
    (θ : Nat → Pat) : Nat :=
  firstsCost ((pack3 nm P.t P.a P.x).bind θ) + numCost 0 (leftVars nm P θ).length +
    14 * ((encList (nm none) ((leftVars nm P θ).map Term.var)).subs ∪
      ((pack3 nm P.t P.a P.x).bind θ).subs).card +
    pairsCost S (Sorts.names S) (sortedOf P θ (leftVars nm P θ)) +
    entriesCost u (atomsMax (Sorts.names S) (sortedOf P θ (leftVars nm P θ)))
      (leftVars nm P θ).length +
    3 * (leftVars nm P θ).length + 20

/-- The ticks `start` may take. -/
noncomputable def startCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u : Nat) (P : Sorts.Prob) :
    Nat :=
  2 + solveCost P.e (pack3 nm P.t P.a P.x) + ((solve P.e).map (startRest nm S u P)).getD 0

/-- What `start` returns: nothing when the equations have no solution or a
sort rejects every instance of its pattern, and otherwise the starting store
with atoms that hold exactly when every pattern is in its sort. -/
def StartPost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (P : Sorts.Prob)
    (nodes : List store.Node)
    (res : Option (store.TermId × store.TermId × store.TermId × store.TermId)) : Prop :=
  match solve P.e with
  | none => res = none
  | some θ =>
    match res with
    | none => ∃ a ∈ sortedOf P θ (leftVars nm P θ),
        ∀ σ : Nat → GTerm, Sorts.mem S a.1 (a.2.bind σ) = false
    | some (t0, x0, es, next) => ∃ A : Sorts.Atoms,
        (∀ a ∈ A, a.2 ∈ Sorts.names S ∧ a.1 < (leftVars nm P θ).length) ∧
        (∀ σ : Nat → GTerm, (∀ a ∈ sortedOf P θ (leftVars nm P θ),
          Sorts.mem S a.1 (a.2.bind σ) = true) ↔ Sorts.Atoms.Holds S A σ) ∧
        Holds nm U nodes (startSt P θ (leftVars nm P θ) A) t0 x0 es next

/-- `start` gives the starting store of a problem. -/
theorem start_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (P : Sorts.Prob) (hP : P.FO)
    (hPa : ∀ a ∈ P.a, a.1 ∈ Sorts.names S) (s : store.Store)
    (decls names t e a x : store.TermId) (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ht : Repr nm s.nodes.val t.val P.t) (he : Repr nm s.nodes.val e.val (encEqs nm P.e))
    (ha : Repr nm s.nodes.val a.val (encList (nm none) (P.a.map ppair)))
    (hx : Repr nm s.nodes.val x.val (encX nm P.x))
    (hroom : Room s (startCost nm S U.length P)) :
    sorts.start s decls names t e a x ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + startCost nm S U.length P ∧
        StartPost nm S U P s'.nodes.val res ⦄ := by
  unfold sorts.start
  have hroom' := hroom
  unfold Room at hroom'
  simp only [startCost] at hroom'
  step with alloc_spec s (.App a x) hI ⟨ha.lt, hx.lt⟩ (by unfold Room; omega)
    as ⟨ax, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  have rax : Repr nm s1.nodes.val ax.val
      (.app (encList (nm none) (P.a.map ppair)) (encX nm P.x)) :=
    .app hr1 (hx1.repr ha) (hx1.repr hx)
  step with alloc_spec s1 (.App t ax) hI1 ⟨(hx1.repr ht).lt, rax.lt⟩ (by unfold Room; omega)
    as ⟨pack, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr2
  have hx02 := hx1.trans hx2
  have rpack : Repr nm s2.nodes.val pack.val (pack3 nm P.t P.a P.x) :=
    .app hr2 (hx02.repr ht) (hx2.repr rax)
  step with solve_into_spec hnm s2 e pack hI2 (hx02.repr he) rpack (by unfold Room; omega)
    as ⟨ok, solved, s3, hI3, hx3, ht3, hres⟩
  have hx03 := hx02.trans hx3
  cases ok with
  | false =>
    simp only [SolveRes, Bool.false_eq_true, ↓reduceIte, Eqns.solveOn, Option.map_eq_none_iff]
      at hres
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hI3, hx03, by simp only [startCost]; omega, ?_⟩
    simp only [StartPost, hres]
  | true =>
    simp only [SolveRes, ↓reduceIte, Eqns.solveOn, Option.map_eq_some_iff] at hres
    obtain ⟨q', rsolved, ⟨θ, hθ, rfl⟩, -⟩ := hres
    simp only [hθ, Option.map_some, Option.getD_some, startRest] at hroom'
    simp only [↓reduceIte]
    have hθfo := solve_fo P.e hP.e θ hθ
    obtain ⟨hFnd, -, -⟩ := Sorts.firsts_spec ((pack3 nm P.t P.a P.x).bind θ).vars
    have hnum := pack_num (nm := nm) P θ
    have hFdef : leftVars nm P θ = Sorts.firsts ((pack3 nm P.t P.a P.x).bind θ).vars := rfl
    have hlt : ∀ v ∈ P.occ θ, (leftVars nm P θ).idxOf v < (leftVars nm P θ).length :=
      fun v hv => List.idxOf_lt_length_of_mem (mem_leftVars.2 hv)
    rw [← hFdef] at hFnd
    obtain ⟨F, hF⟩ : ∃ F, F = leftVars nm P θ := ⟨_, rfl⟩
    rw [← hF] at hroom' hFnd hnum hFdef hlt
    have hfc : firstsCost ((pack3 nm P.t P.a P.x).bind θ) =
        8 * ((pack3 nm P.t P.a P.x).bind θ).subs.card + 2 * F.length + 8 := by
      rw [firstsCost, ← hFdef]
    step with firsts_spec hnm s3 solved hI3 rsolved (by unfold Room; omega)
      as ⟨vs, s4, hI4, hx4, ht4, rvs⟩
    rw [← hFdef] at rvs
    have hx04 := hx03.trans hx4
    step with number_spec (nm := nm) F hFnd s4 vs hI4 rvs (by unfold Room; omega)
      as ⟨next, s5, hI5, hx5, ht5, hA5, hnext, hleaf5⟩
    have hx05 := hx04.trans hx5
    step with clear_spec s5 .A hI5 (by unfold Room; omega) as ⟨s6, d1, d2, d3, d4, d5⟩
    have hx56 : Extends s5 s6 := Extends.of_eq d1 (by omega)
    have hx06 := hx05.trans hx56
    have hleaf : LeafOK nm s6.nodes.val (tbl s6 .B) term.Leaf.Map (numSub F) := by
      rw [d1, d5 .B (by simp)]
      exact hleaf5
    have hpc := pending_card_le (nm := nm) s6.nodes.val (tbl s6 .A)
      ((encList (nm none) (F.map Term.var)).subs ∪ ((pack3 nm P.t P.a P.x).bind θ).subs)
    step with rebuild_spec hnm s6 .Map vs (t := encList (nm none) (F.map Term.var))
      (σ := numSub F)
      ((encList (nm none) (F.map Term.var)).subs ∪ ((pack3 nm P.t P.a P.x).bind θ).subs) d3
      ((hx5.trans hx56).repr rvs) hleaf (by intro k v hk; rw [d4] at hk; cases hk)
      Finset.subset_union_left (by unfold Room; omega) as ⟨vars, s7, h7⟩
    have hc7 := h7.cost
    have hm7 := h7.mono
    step with rebuild_spec hnm s7 .Map solved (t := (pack3 nm P.t P.a P.x).bind θ)
      (σ := numSub F)
      ((encList (nm none) (F.map Term.var)).subs ∪ ((pack3 nm P.t P.a P.x).bind θ).subs) h7.inv
      ((((hx4.trans hx5).trans hx56).trans h7.ext).repr rsolved)
      (by rw [h7.tblB]; exact hleaf.extends h7.ext) h7.memo Finset.subset_union_right
      (by unfold Room; omega) as ⟨packed, s8, h8⟩
    have hc8 := h8.cost
    have hm8 := h8.mono
    have hx08 := (hx06.trans h7.ext).trans h8.ext
    have rvars : Repr nm s8.nodes.val vars.val
        (encList (nm none) ((List.range F.length).map Term.var)) := by
      have := h8.ext.repr h7.repr
      rw [encList_bind, List.map_map] at this
      have e : F.map (Term.bind (numSub F) ∘ Term.var) =
          (List.range F.length).map Term.var := by
        rw [← map_idxOf_self hFnd, List.map_map]
        refine List.map_congr_left fun v hv => ?_
        simp [numSub, hv]
      rwa [e] at this
    have rpacked := h8.repr
    rw [hnum] at rpacked
    step with uncons_repr s8 packed h8.inv.toWf
      (p := Term.app ((P.t.bind θ).rename fun v => F.idxOf v)
        (Term.app (encList (nm none) ((sortedOf P θ F).map ppair)) (encX nm (exclOf P θ F))))
      rpacked (by unfold Room; omega) as ⟨o9, s9, hK9, hu9⟩
    obtain ⟨t1, ax1, rfl, rt1, rax1⟩ := hu9
    have K9 := hK9.kept h8.inv
    have ht9 := K9.ticks
    have hx89 : Extends s8 s9 := Extends.of_eq K9.nodes (by omega)
    step with uncons_repr s9 ax1 K9.inv.toWf
      (p := Term.app (encList (nm none) ((sortedOf P θ F).map ppair)) (encX nm (exclOf P θ F)))
      (hx89.repr rax1) (by unfold Room; omega) as ⟨o10, s10, hK10, hu10⟩
    obtain ⟨a1, x1, rfl, ra1, rx1⟩ := hu10
    have K10 := hK10.kept K9.inv
    have ht10 := K10.ticks
    have hx910 : Extends s9 s10 := Extends.of_eq K10.nodes (by omega)
    have hx010 := (hx08.trans hx89).trans hx910
    have hNs : ∀ m ∈ Sorts.names S, ∀ f k ks, Sorts.step S m f k = some ks →
        ∀ m', some m' ∈ ks → m' ∈ Sorts.names S ∧ m' ≠ nm none := fun m _ f k ks hst m' hm' =>
      ⟨step_kid_names hst hm', hC.nz _ (step_kid_names hst hm')⟩
    have hin : ∀ b ∈ sortedOf P θ F, b.1 ∈ Sorts.names S ∧ b.2.firstOrder = true := by
      intro b hb
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hb
      exact ⟨hPa a' ha', Term.fo_bind (Term.fo_bind (hP.a a' ha') fun v _ => hθfo v)
        fun _ _ => rfl⟩
    step with push_pairs_spec hnm S hC.sorts (Sorts.names S) hNs (sortedOf P θ F) s10 decls a1
      K10.inv (hx010.repr hde) (hx910.repr ra1) hin (by unfold Room; omega)
      as ⟨o11, s11, hI11, hx11, ht11, hres11⟩
    have hx011 := hx010.trans hx11
    cases o11 with
    | none =>
      simp only at hres11
      simp only [WP.spec_ok]
      have hcost : s11.ticks.val ≤ s.ticks.val + startCost nm S U.length P := by
        simp only [startCost, hθ, Option.map_some, Option.getD_some, startRest, ← hF]
        omega
      refine ⟨hI11, hx011, hcost, ?_⟩
      simp only [StartPost, hθ, ← hF]
      exact hres11
    | some atoms =>
      simp only [PairsRes, ↓reduceIte, List.append_nil] at hres11
      obtain ⟨A, rA, hA, hAl, hsem⟩ := hres11
      have hmono := entriesCost_mono U.length F.length hAl
      step with entries_of_spec hnm U A (List.range F.length) s11 names atoms vars hI11
        (hx011.repr hU) rA (((hx89.trans hx910).trans hx11).repr rvars)
        (by simp only [List.length_range]; unfold Room; omega) as ⟨es, s12, hI12, hx12, ht12, res⟩
      simp only [List.length_range] at ht12
      step with alloc_spec s12 .Nil hI12 trivial (by unfold Room; omega)
        as ⟨nil, s13, hI13, ht13, htb13, hx13, hr13⟩
      simp only [norm] at hr13
      have hx813 := (((hx89.trans hx910).trans hx11).trans hx12).trans hx13
      step with tuple_spec hz F.length s13 nil vars hI13 (.nil hr13) (hx813.repr rvars)
        (by unfold Room; omega) as ⟨all, s14, hI14, hx14, ht14, rall⟩
      have rt1' : Repr nm s14.nodes.val t1.val ((P.t.bind θ).rename fun v => F.idxOf v) :=
        (hx813.trans hx14).repr rt1
      step with alloc_spec s14 (.App nil t1) hI14 ⟨(hx14.repr (Repr.nil (nm := nm) hr13)).lt,
        rt1'.lt⟩ (by unfold Room; omega) as ⟨head, s15, hI15, ht15, htb15, hx15, hr15⟩
      simp only [norm] at hr15
      have rhead : Repr nm s15.nodes.val head.val
          (.app (.sym (nm none)) ((P.t.bind θ).rename fun v => F.idxOf v)) :=
        .app hr15 ((hx14.trans hx15).repr (.nil hr13)) (hx15.repr rt1')
      step with alloc_spec s15 (.App head all) hI15 ⟨rhead.lt, (hx15.repr rall).lt⟩
        (by unfold Room; omega) as ⟨t0, s16, hI16, ht16, htb16, hx16, hr16⟩
      simp only [norm] at hr16
      have hx816 := ((hx813.trans hx14).trans hx15).trans hx16
      have hcost : s16.ticks.val ≤ s.ticks.val + startCost nm S U.length P := by
        simp only [startCost, hθ, Option.map_some, Option.getD_some, startRest, ← hF]
        omega
      refine ⟨hI16, hx08.trans hx816, hcost, ?_⟩
      simp only [StartPost, hθ, ← hF]
      refine ⟨A, fun b hb => ?_, hsem, ⟨?_, ?_, ?_, ?_⟩⟩
      · obtain ⟨h1, c, hc, h2⟩ := hA b hb
        refine ⟨h1, ?_⟩
        obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hc
        simp only [Term.vars_rename] at h2
        obtain ⟨w, hw, hwb⟩ := List.mem_map.1 h2
        rw [← hwb]
        exact hlt w (mem_occ.2 (.inr (.inl ⟨a', ha', hw⟩)))
      · have := Repr.app hr16 (hx16.repr rhead) ((hx15.trans hx16).repr rall)
        rw [hz] at this
        exact this
      · exact ((((((hx910.trans hx11).trans hx12).trans hx13).trans hx14).trans hx15).trans
          hx16).repr rx1
      · exact (((hx13.trans hx14).trans hx15).trans hx16).repr res
      · exact ((((((((((hx56.trans h7.ext).trans h8.ext).trans hx89).trans hx910).trans
          hx11).trans hx12).trans hx13).trans hx14).trans hx15).trans hx16).varAt hnext

/-! ## The starting store denotes the problem -/

theorem idxOf_inj_of_mem {F : List Nat} {v w : Nat} (hv : v ∈ F) (hw : w ∈ F)
    (e : F.idxOf v = F.idxOf w) : v = w := by
  have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)
  have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hw)
  simp only [e] at h1
  exact h1.symm.trans h2

/-- A problem one of whose sorts rejects every instance of its pattern,
solved and numbered, denotes nothing. -/
theorem den_empty_of_reject {S : Sorts} {P : Sorts.Prob} {θ : Nat → Pat}
    (hsolve : solve P.e = some θ)
    (h : ∃ a ∈ sortedOf P θ (leftVars nm P θ),
      ∀ σ : Nat → GTerm, Sorts.mem S a.1 (a.2.bind σ) = false) : P.Den S = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨σ, hσ, -⟩
  obtain ⟨b, hb, hnever⟩ := h
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
  obtain ⟨τ, fwd⟩ := Sorts.Prob.begin_back (ρ := fun v => (leftVars nm P θ).idxOf v) hsolve
    (fun v hv w hw e => idxOf_inj_of_mem (mem_leftVars.2 hv) (mem_leftVars.2 hw) e) hσ.1
  have h1 := hnever τ
  simp only at h1
  rw [fwd a.2 fun v hv => mem_occ.2 (.inr (.inl ⟨a, ha, hv⟩)), hσ.2.1 a ha] at h1
  cases h1

/-- The starting store is well formed, has all its variables in its pattern,
and denotes pairs whose first parts are what the problem denotes. -/
theorem startSt_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {P : Sorts.Prob} (hP : P.FO) {θ : Nat → Pat} (hsolve : solve P.e = some θ)
    {A : Sorts.Atoms}
    (hA : ∀ a ∈ A, a.2 ∈ Sorts.names S ∧ a.1 < (leftVars nm P θ).length)
    (hsem : ∀ σ : Nat → GTerm, (∀ a ∈ sortedOf P θ (leftVars nm P θ),
      Sorts.mem S a.1 (a.2.bind σ) = true) ↔ Sorts.Atoms.Holds S A σ) :
    (startSt P θ (leftVars nm P θ) A).OK ∧
      (∀ p ∈ (startSt P θ (leftVars nm P θ) A).L, Sub U p.2) ∧
      (startSt P θ (leftVars nm P θ) A).abs.store.Fin (leftVars nm P θ).length ∧
      (startSt P θ (leftVars nm P θ) A).abs.store.Full ∧
      (∀ g ∈ (startSt P θ (leftVars nm P θ) A).abs.store.Den S, ∃ x y, g = Sorts.tpair x y) ∧
      P.Den S = {x | ∃ y, Sorts.tpair x y ∈ (startSt P θ (leftVars nm P θ) A).abs.store.Den S} := by
  generalize hF : leftVars nm P θ = F at hA hsem ⊢
  have hok : (startSt P θ F A).OK := by
    refine ⟨?_, fun e he => ?_⟩
    · simp only [startSt, List.map_map]
      exact (List.nodup_range (n := F.length)).map_on fun _ _ _ _ h => h
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 he
      exact List.mem_range.1 hv
  have hup : ∀ v, F.length ≤ v → Sorts.upsOf A v = ∅ := fun v hv =>
    Finset.eq_empty_of_forall_notMem fun n hn => by
      have := (hA _ (Sorts.mem_upsOf.1 hn)).2
      omega
  have hconj : ∀ v, (startSt P θ F A).abs.conj v = Sorts.upsOf A v := by
    intro v
    rw [hok.conj]
    by_cases hv : v < F.length
    · exact conjOf_mem hok.nodup (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩)
    · rw [hup v (by omega)]
      refine conjOf_not fun e he e' => hv ?_
      rw [← e']
      exact hok.lt e he
  refine ⟨hok, fun p hp n hn => ?_, ?_⟩
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hp
    exact hC.names n (hA _ (Sorts.mem_upsOf.1 hn)).1
  · refine Sorts.Prob.begin_spec (S := S) hP hsolve (ρ := fun v => F.idxOf v) (n := F.length)
      (s := (startSt P θ F A).abs.store) ?_ ?_ rfl rfl ?_ ?_
    · intro v hv w hw e
      rw [← hF] at e
      exact idxOf_inj_of_mem (mem_leftVars.2 hv) (mem_leftVars.2 hw) e
    · intro v hv
      rw [← hF]
      exact List.idxOf_lt_length_of_mem (mem_leftVars.2 hv)
    · intro τ
      show (∀ v, Sorts.MemC S ((startSt P θ F A).abs.conj v) (τ v)) ↔ _
      simp only [hconj]
      rw [← Sorts.holds_iff_upsOf, ← hsem τ]
      simp only [sortedOf, List.forall_mem_map]
    · intro v hv
      show (startSt P θ F A).abs.conj v = ∅
      rw [hconj, hup v hv]

/-! ## The normal store -/

/-- The pattern and the sorts of a tight store with its variables numbered,
without exclusions. -/
noncomputable def numRaw (S : Sorts) (st : TSt) : Sorts.Raw :=
  ⟨st.T.rename fun v => (Sorts.firsts st.T.vars).idxOf v,
    (Sorts.firsts st.T.vars).map (upConj S st.L st.X), ∅⟩

/-- The exclusions of a tight store with its variables numbered. -/
def numX (st : TSt) : List (Eqns Nat) :=
  st.X.map (Eqns.ren fun v => (Sorts.firsts st.T.vars).idxOf v)

/-- The normal forms of these exclusions. -/
noncomputable def numYs (S : Sorts) (st : TSt) : List Sorts.Binds :=
  Sorts.normExs S (numRaw S st) (numX st)

/-- Their value lists. -/
noncomputable def numLs (S : Sorts) (st : TSt) : List (List Pat) :=
  (numYs S st).map (vals (numRaw S st).c.length)

/-- The value lists that are instances of no other. -/
noncomputable def numZs (S : Sorts) (st : TSt) : List (List Pat) :=
  Sorts.antichain coversV (numLs S st)

/-- The first part of the numbered pattern. -/
noncomputable def numLeft (S : Sorts) (st : TSt) : Pat := Sorts.left (numRaw S st).t

/-- The number of variables of the first part. -/
noncomputable def numJ (S : Sorts) (st : TSt) : Nat :=
  (Sorts.firsts (numLeft S st).vars).length

/-- The subterms of the lists of a list, counted list by list. -/
def listsCard (nm : Option Nat → RwLog.Sym) (Ls : List (List Pat)) : Nat :=
  (Ls.map fun B => (encList (nm none) B).subs.card).sum

theorem le_listsCard : ∀ {Ls : List (List Pat)} {B : List Pat}, B ∈ Ls →
    (encList (nm none) B).subs.card ≤ listsCard nm Ls
  | [], _, h => by cases h
  | A :: Ls, B, h => by
    simp only [listsCard, List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_listsCard h
      simp only [listsCard] at this
      omega

theorem varsTo_take {j k : Nat} (h : j ≤ k) : (varsTo k).take j = varsTo j := by
  unfold varsTo
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-- The ticks `normal` may take after tightening, from the tight store. -/
noncomputable def tailCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (rc q : Nat)
    (st : TSt) : Nat :=
  renumberCost nm S U.length rc q st.T st.X st.L + placesCost (numRaw S st).c.length +
    normExsCost nm S U rc (numRaw S st) (numX st) +
    antiCost (numRaw S st).c.length (listsCard nm (numLs S st)) (numLs S st).length +
    firstsCost (numLeft S st) + 10 * numJ S st +
    cutCost (numJ S st) (listsCard nm (numZs S st)) (numZs S st).length + 10

/-- A tight store that denotes pairs whose first parts are what a problem
denotes gives the normal store of the problem: the first part of its
numbered pattern, the sorts of the variables of that part, and the
exclusions over them. -/
theorem tail_spec {S : Sorts} (hS : S.WellFormed) {P : Sorts.Prob} (hP : P.FO) {st : TSt}
    (hok : st.OK) (hpairs : ∀ g ∈ st.abs.store.Den S, ∃ x y, g = Sorts.tpair x y)
    (hfst : P.Den S = {x | ∃ y, Sorts.tpair x y ∈ st.abs.store.Den S})
    (hI : Sorts.Inv S st.abs)
    (hsole : ∀ v ∈ st.abs.t.vars,
      Sorts.sole S (st.abs.conj v) (Sorts.gone st.abs.x v) = none) :
    ∃ b, (numRaw S st).t = Sorts.tpair (numLeft S st) b ∧
      numJ S st ≤ (numRaw S st).c.length ∧
      (∀ θ ∈ numYs S st, Sorts.Pre (numRaw S st).c.length θ) ∧
      (∀ E ∈ numX st, E.FO) ∧ (∀ E ∈ numX st, ∀ v ∈ E.vars, v < (numRaw S st).c.length) ∧
      P.norm S hS = some ⟨numLeft S st, (numRaw S st).c.take (numJ S st),
        ((Sorts.antichain (Sorts.covers (numRaw S st).c.length) (numYs S st)).filter
          fun θ => decide (Sorts.Low (numJ S st) θ)).toFinset⟩ := by
  obtain ⟨a, b, hab, hnorm⟩ := Sorts.Prob.norm_of_tight hS hP hpairs hfst hI hsole
  obtain ⟨hN, -⟩ := Sorts.ofTight_normal hS hI hsole
  rw [ofTight_abs hok] at hab hnorm hN
  have hab' : (numRaw S st).t = Sorts.tpair a b := hab
  have hleft : numLeft S st = a := by unfold numLeft; rw [hab']; rfl
  subst hleft
  have hlen : ∀ v, v ∈ (numRaw S st).t.vars ↔ v < (numRaw S st).c.length := hN.len
  obtain ⟨hnd, hmem, -⟩ := Sorts.firsts_spec (numLeft S st).vars
  have hw : Sorts.width (numLeft S st) = numJ S st := by
    unfold numJ Sorts.width
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext v
    simp [hmem]
  have hjk : numJ S st ≤ (numRaw S st).c.length := by
    rw [← hw]
    unfold Sorts.width
    calc (numLeft S st).vars.toFinset.card ≤ (Finset.range (numRaw S st).c.length).card :=
          Finset.card_le_card fun v hv => by
            rw [List.mem_toFinset] at hv
            rw [Finset.mem_range, ← hlen, hab', Sorts.tpair_vars]
            exact List.mem_append_left _ hv
      _ = (numRaw S st).c.length := Finset.card_range _
  have hfo : ∀ E ∈ numX st, E.FO := by
    intro E hE p hp
    obtain ⟨E0, hE0, rfl⟩ := List.mem_map.1 hE
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hp
    exact ⟨Sorts.rename_fo (hI.xfo E0 hE0 p0 hp0).1 _, Sorts.rename_fo (hI.xfo E0 hE0 p0 hp0).2 _⟩
  have hv : ∀ E ∈ numX st, ∀ v ∈ E.vars, v < (numRaw S st).c.length := by
    intro E hE v hv
    obtain ⟨E0, hE0, rfl⟩ := List.mem_map.1 hE
    obtain ⟨p, hp, hvp⟩ := List.mem_flatMap.1 hv
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hp
    simp only [Term.vars_rename, ← List.map_append] at hvp
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hvp
    have hwT : w ∈ st.T.vars := hI.xv E0 hE0 w (List.mem_flatMap.2 ⟨p0, hp0, hw'⟩)
    have : (numRaw S st).c.length = (Sorts.firsts st.T.vars).length := List.length_map _
    rw [this]
    exact List.idxOf_lt_length_of_mem ((Sorts.firsts_spec st.T.vars).2.1 w |>.2 hwT)
  refine ⟨b, hab', hjk, fun θ hθ => ?_, hfo, hv, ?_⟩
  · obtain ⟨E, hE, hEθ⟩ := List.mem_filterMap.1 hθ
    exact (Sorts.normEx_some (hfo E hE) (hv E hE) hEθ).1
  · rw [hnorm, hw]
    simp only [Sorts.Raw.cut, Sorts.assembled, List.toFinset_filter]
    rfl

/-- What `normal` returns: nothing when the problem has no normal store, and
otherwise the pattern, the sorts of the variables and the exclusions, each
as the list of its values, of the normal store of the problem. -/
def NormalPost (nm : Option Nat → RwLog.Sym) (S : Sorts) (hS : S.WellFormed) (U : List Name)
    (P : Sorts.Prob) (nodes : List store.Node)
    (res : Option (store.TermId × store.TermId × store.TermId)) : Prop :=
  match res with
  | none => P.norm S hS = none
  | some (t', cs', xs') => ∃ r : Sorts.Raw, P.norm S hS = some r ∧ Repr nm nodes t'.val r.t ∧
      Repr nm nodes cs'.val (encList (nm none) (r.c.map (cpat (nm none) U))) ∧
      ∃ Y : List Sorts.Binds, Y.toFinset = r.x ∧
        Repr nm nodes xs'.val (encLL nm (Y.map (vals r.c.length)))

/-- `normal` computes the normal store of a problem (`Sorts.Prob.norm`),
within the charge of `start` and a bound on the charge of tightening the
starting store in as many rounds as it takes and of what follows it on the
tight store. -/
theorem normal_spec (hnm : Function.Injective nm) (hz : nm none = "") {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hS : S.WellFormed)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (P : Sorts.Prob) (hP : P.FO)
    (hPa : ∀ a ∈ P.a, a.1 ∈ Sorts.names S) (B : Nat)
    (hB : ∀ θ A k o, solve P.e = some θ →
      tightenRes S k (startSt P θ (leftVars nm P θ) A) = some o →
      tightenCost nm S U.length rc k (startSt P θ (leftVars nm P θ) A) +
        (match o with
          | none => 0
          | some st' => tailCost nm S U rc q st') ≤ B)
    (s : store.Store) (decls names t e a x : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ht : Repr nm s.nodes.val t.val P.t) (he : Repr nm s.nodes.val e.val (encEqs nm P.e))
    (ha : Repr nm s.nodes.val a.val (encList (nm none) (P.a.map ppair)))
    (hx : Repr nm s.nodes.val x.val (encX nm P.x))
    (hroom : Room s (startCost nm S U.length P + B)) :
    sorts.normal s decls names t e a x ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + startCost nm S U.length P + B ∧
        NormalPost nm S hS U P s'.nodes.val res ⦄ := by
  unfold sorts.normal
  have hroom' := hroom
  unfold Room at hroom'
  step with start_spec hnm hz hC P hP hPa s decls names t e a x hI hde hU ht he ha hx
    (by unfold Room; omega) as ⟨o, s1, hI1, hx1, ht1, hpost⟩
  unfold StartPost at hpost
  cases hsolve : solve P.e with
  | none =>
    rw [hsolve] at hpost
    simp only at hpost
    subst hpost
    simp only [WP.spec_ok]
    refine ⟨hI1, hx1, by omega, ?_⟩
    simp only [NormalPost]
    refine Sorts.Prob.norm_of_empty hS hP ?_
    ext g
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨σ, hσ, -⟩
    exact solve_none hsolve σ hσ.1
  | some θ =>
    rw [hsolve] at hpost
    simp only at hpost
    cases o with
    | none =>
      simp only at hpost
      simp only [WP.spec_ok]
      refine ⟨hI1, hx1, by omega, ?_⟩
      simp only [NormalPost]
      exact Sorts.Prob.norm_of_empty hS hP (den_empty_of_reject hsolve hpost)
    | some val =>
      obtain ⟨t0, x0, es0, next0⟩ := val
      simp only at hpost
      obtain ⟨A, hA, hsem, hH⟩ := hpost
      obtain ⟨hok, hsubL, hfin, hfull, hpairs, hfst⟩ := startSt_spec hC hP hsolve hA hsem
      obtain ⟨k, o, hrun, hmatch⟩ := tighten_sound hS _ hok hfin hfull
      have hBk := hB θ A k o hsolve hrun
      step with tighten_spec hnm hC hr s1 decls names t0 x0 es0 next0 _ k o hI1 (hx1.repr hde)
        (hx1.repr hU) hH hsubL hrun (by unfold Room; omega) as ⟨o1, s2, hI2, hx2, ht2, hres⟩
      have hx02 := hx1.trans hx2
      cases o with
      | none =>
        simp only at hres hmatch hBk
        subst hres
        simp only [WP.spec_ok]
        refine ⟨hI2, hx02, by omega, ?_⟩
        simp only [NormalPost]
        refine Sorts.Prob.norm_of_empty hS hP ?_
        rw [hfst, hmatch]
        simp
      | some st' =>
        simp only at hres hmatch hBk
        obtain ⟨t11, x1, es1, next1, rfl, hH', hsub'⟩ := hres
        obtain ⟨hden', hInv, hsole, hGood⟩ := hmatch
        simp only [tailCost] at hBk
        obtain ⟨b, hab, hjk, hPre, hfoX, hvX, hnorm⟩ := tail_spec hS hP hGood.ok
          (by rw [hden']; exact hpairs) (by rw [hden']; exact hfst) hInv hsole
        obtain ⟨-, hFmem', -⟩ := Sorts.firsts_spec st'.T.vars
        step with renumber_spec hnm hC hS hUS hr hq s2 decls names t11 x1 es1 st'.T st'.X st'.L
          hI2 (hx02.repr hde) (hx02.repr hU) hH'.t hH'.x hH'.es hsub' (by unfold Room; omega)
          as ⟨t21, x2, cs, s3, hI3, hx3, ht3, rT, rX, rC⟩
        have hx03 := hx02.trans hx3
        have rT' : Repr nm s3.nodes.val t21.val (numRaw S st').t := by
          rw [bind_numSub fun v hv => (hFmem' v).2 hv] at rT
          exact rT
        have rX' : Repr nm s3.nodes.val x2.val (encX nm (numX st')) := by
          rw [encX_numSub (nm := nm) (X := st'.X) fun E hE p hp =>
            ⟨fun v hv => (hFmem' v).2 (hInv.xv E hE v
              (List.mem_flatMap.2 ⟨p, hp, List.mem_append_left _ hv⟩)),
            fun v hv => (hFmem' v).2 (hInv.xv E hE v
              (List.mem_flatMap.2 ⟨p, hp, List.mem_append_right _ hv⟩))⟩] at rX
          exact rX
        have rC' : Repr nm s3.nodes.val cs.val
            (encList (nm none) ((numRaw S st').c.map (cpat (nm none) U))) := by
          simpa [numRaw, List.map_map, Function.comp_def] using rC
        have hklen : ((numRaw S st').c.map (cpat (nm none) U)).length =
            (numRaw S st').c.length := List.length_map _
        step with places_spec ((numRaw S st').c.map (cpat (nm none) U)) s3 cs hI3 rC'
          (by rw [hklen]; unfold Room; omega) as ⟨vs, s4, hI4, hx4, ht4, rvs⟩
        rw [hklen] at ht4 rvs
        have hx04 := hx03.trans hx4
        have hcN : ∀ v, ∀ n ∈ (numRaw S st').conj v, n ∈ Sorts.names S := by
          intro v n hn
          have e : (numRaw S st').conj v =
              ((Sorts.firsts st'.T.vars)[v]?.map (upConj S st'.L st'.X)).getD ∅ := by
            simp [Sorts.Raw.conj, numRaw, List.getD_eq_getElem?_getD]
          rw [e] at hn
          cases hw : (Sorts.firsts st'.T.vars)[v]? with
          | none => rw [hw] at hn; simp at hn
          | some w =>
            rw [hw] at hn
            simp only [Option.map_some, Option.getD_some, upConj, Finset.mem_filter] at hn
            exact hn.1
        step with norm_exs_spec hnm hC hr (numRaw S st') hcN (numX st') hfoX hvX s4 decls names
          vs cs x2 hI4 (hx04.repr hde) (hx04.repr hU) rvs (hx4.repr rC') (hx4.repr rX')
          (by unfold Room; omega) as ⟨ys, s5, hI5, hx5, ht5, rys⟩
        have rys' : Repr nm s5.nodes.val ys.val (encLL nm (numLs S st')) := rys
        have hL : ∀ B' ∈ numLs S st', B'.length = (numRaw S st').c.length ∧
            (encList (nm none) B').subs.card ≤ listsCard nm (numLs S st') := by
          intro B' hB'
          refine ⟨?_, le_listsCard hB'⟩
          obtain ⟨θ', -, rfl⟩ := List.mem_map.1 hB'
          exact vals_length _ _
        step with antichain_spec hnm (numRaw S st').c.length (listsCard nm (numLs S st'))
          (numLs S st') s5 vs ys hI5 (hx5.repr rvs) rys' hL (by unfold Room; omega)
          as ⟨zs, s6, hI6, hx6, ht6, rzs⟩
        have rzs' : Repr nm s6.nodes.val zs.val (encLL nm (numZs S st')) := rzs
        have hx36 := (hx4.trans hx5).trans hx6
        have rT6 : Repr nm s6.nodes.val t21.val
            (Term.app (Term.app (Term.sym "") (numLeft S st')) b) := by
          have := hx36.repr rT'
          rw [hab] at this
          exact this
        step with uncons_repr s6 t21 hI6.toWf
          (p := Term.app (Term.app (Term.sym "") (numLeft S st')) b) rT6
          (by unfold Room; omega) as ⟨o7, s7, hK7, hu7⟩
        obtain ⟨head, bi, rfl, rhead, -⟩ := hu7
        have K7 := hK7.kept hI6
        have ht7 := K7.ticks
        have hx67 : Extends s6 s7 := Extends.of_eq K7.nodes (by omega)
        step with uncons_repr s7 head K7.inv.toWf
          (p := Term.app (Term.sym "") (numLeft S st')) (hx67.repr rhead)
          (by unfold Room; omega) as ⟨o8, s8, hK8, hu8⟩
        obtain ⟨nili, left, rfl, -, rleft⟩ := hu8
        have K8 := hK8.kept K7.inv
        have ht8 := K8.ticks
        have hx78 : Extends s7 s8 := Extends.of_eq K8.nodes (by omega)
        step with firsts_spec hnm s8 left K8.inv (hx78.repr rleft) (by unfold Room; omega)
          as ⟨ws, s9, hI9, hx9, ht9, rws⟩
        have hx69 := (hx67.trans hx78).trans hx9
        have hx49 := (hx5.trans hx6).trans hx69
        have hwl : ((Sorts.firsts (numLeft S st').vars).map Term.var).length = numJ S st' := by
          simp [numJ]
        step with take_len_spec ((Sorts.firsts (numLeft S st').vars).map Term.var)
          (varsTo (numRaw S st').c.length) s9 vs ws hI9 rws (hx49.repr rvs)
          (by rw [hwl, varsTo_length]; exact hjk) (by rw [hwl]; unfold Room; omega)
          as ⟨ks, s10, hI10, hx10, ht10, rks⟩
        rw [hwl] at ht10 rks
        rw [varsTo_take hjk] at rks
        step with take_len_spec (varsTo (numJ S st')) ((numRaw S st').c.map (cpat (nm none) U))
          s10 cs ks hI10 rks ((((hx4.trans hx5).trans hx6).trans hx69).trans hx10 |>.repr rC')
          (by rw [varsTo_length, hklen]; exact hjk) (by rw [varsTo_length]; unfold Room; omega)
          as ⟨cs1, s11, hI11, hx11, ht11, rcs1⟩
        rw [varsTo_length] at ht11 rcs1
        have hLz : ∀ B' ∈ numZs S st', B'.length = (numRaw S st').c.length ∧
            (encList (nm none) B').subs.card ≤ listsCard nm (numZs S st') := fun B' hB' =>
          ⟨(hL B' (antichain_subset _ _ B' hB')).1, le_listsCard hB'⟩
        step with cut_exs_spec hnm (numJ S st') (numRaw S st').c.length
          (listsCard nm (numZs S st')) hjk (numZs S st') s11 vs ks zs hI11
          (((hx49.trans hx10).trans hx11).repr rvs) (hx11.repr rks)
          (((hx69.trans hx10).trans hx11).repr rzs') hLz (by unfold Room; omega)
          as ⟨xs1, s12, hI12, hx12, ht12, rxs1⟩
        refine ⟨hI12, ((((hx03.trans hx36).trans hx69).trans hx10).trans hx11).trans hx12,
          by omega, ?_⟩
        simp only [NormalPost]
        have hY : ∀ θ' ∈ numYs S st', ∀ b' ∈ θ', b'.1 < (numRaw S st').c.length :=
          fun θ' hθ' => (hPre θ' hθ').dom
        have eZ : numZs S st' = (Sorts.antichain (Sorts.covers (numRaw S st').c.length)
            (numYs S st')).map (vals (numRaw S st').c.length) := antichain_vals hY
        have e : ((numZs S st').filter (lowV (numJ S st'))).map (List.take (numJ S st')) =
            ((Sorts.antichain (Sorts.covers (numRaw S st').c.length) (numYs S st')).filter
              fun θ' => decide (Sorts.Low (numJ S st') θ')).map (vals (numJ S st')) := by
          rw [eZ, List.filter_map, List.map_map]
          have e1 : (Sorts.antichain (Sorts.covers (numRaw S st').c.length) (numYs S st')).filter
              (lowV (numJ S st') ∘ vals (numRaw S st').c.length) =
              (Sorts.antichain (Sorts.covers (numRaw S st').c.length) (numYs S st')).filter
                fun θ' => decide (Sorts.Low (numJ S st') θ') :=
            List.filter_congr fun θ' hθ' =>
              lowV_vals (hPre θ' (antichain_subset _ _ θ' hθ')) hjk
          rw [e1]
          exact List.map_congr_left fun θ' _ => take_vals hjk θ'
        rw [e] at rxs1
        refine ⟨_, hnorm, ?_, ?_, _, rfl, ?_⟩
        · exact ((((hx78.trans hx9).trans hx10).trans hx11).trans hx12).repr rleft
        · rw [← List.map_take] at rcs1
          exact hx12.repr rcs1
        · show Repr nm s12.nodes.val xs1.val (encLL nm (List.map
            (vals (List.take (numJ S st') (numRaw S st').c).length) _))
          rw [List.length_take, Nat.min_eq_left hjk]
          exact rxs1

end RwLogVerified
