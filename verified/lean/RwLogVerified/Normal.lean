/-
# The normal store of a problem, on the store

`sorts::start` builds a store that denotes what a problem denotes
(`Prob.begin_spec`): the equations solved, the variables left numbered by
first occurrence, and the sorts pushed down to the variables. Its variables
need not all occur in its pattern. `sorts::normal` replaces the variables
with one value, drops the ones that are not in the pattern
(`Sorts.prune_spec`), tightens what is left, numbers it and normalises its
exclusions, which gives the normal store of the problem (`Prob.norm`).
-/
import RwLogVerified.Assemble
import RwLogVerified.Number
import RwLogVerified.Prune
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

/-! ## The nil symbol

The store has no name for a symbol: every theorem here holds for any one to
one naming `nm` of the nil node and the numbered symbols. The specification
pairs two patterns under the empty symbol (`Sorts.tpair`), and the
operations of the domain pair them under the nil node (`dom::pair`), so the
theorems about pairs are for the namings that give the nil node the empty
symbol. There are such namings
(`exists_naming`); an engine that reads `tpair` off the store has to use
one. -/

/-- A one to one naming that gives the nil node the empty symbol. -/
theorem exists_naming : ∃ nm : Option Nat → RwLog.Sym, Function.Injective nm ∧ nm none = "" := by
  refine ⟨fun o => match o with
    | none => ""
    | some n => String.ofList (List.replicate (n + 1) 'a'), ?_, rfl⟩
  intro a b h
  have hlen : ∀ n : Nat, (String.ofList (List.replicate (n + 1) 'a')).length = n + 1 := by
    intro n; simp
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some m => have := congrArg String.length h; rw [hlen] at this; simp at this
  | some n =>
    cases b with
    | none => have := congrArg String.length h; rw [hlen] at this; simp at this
    | some m =>
      have := congrArg String.length h
      rw [hlen, hlen] at this
      rw [Nat.add_right_cancel this]


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

/-- The starting store: the pattern, the exclusions, and for each variable
the sorts the atoms put on it. -/
def startSt (P : Sorts.Prob) (θ : Nat → Pat) (F : List Nat) (A : Sorts.Atoms) : TSt :=
  ⟨(P.t.bind θ).rename fun v => F.idxOf v, exclOf P θ F,
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
      (leftVars nm P θ).length + 16

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
theorem start_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat}
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
      have hx812 := ((hx89.trans hx910).trans hx11).trans hx12
      have hcost : s12.ticks.val ≤ s.ticks.val + startCost nm S U.length P := by
        simp only [startCost, hθ, Option.map_some, Option.getD_some, startRest, ← hF]
        omega
      refine ⟨hI12, hx08.trans hx812, hcost, ?_⟩
      simp only [StartPost, hθ, ← hF]
      refine ⟨A, fun b hb => ?_, hsem, ⟨?_, ?_, ?_, ?_⟩⟩
      · obtain ⟨h1, c, hc, h2⟩ := hA b hb
        refine ⟨h1, ?_⟩
        obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hc
        simp only [Term.vars_rename] at h2
        obtain ⟨w, hw, hwb⟩ := List.mem_map.1 h2
        rw [← hwb]
        exact hlt w (mem_occ.2 (.inr (.inl ⟨a', ha', hw⟩)))
      · exact hx812.repr rt1
      · exact ((hx910.trans hx11).trans hx12).repr rx1
      · exact res
      · exact ((((((hx56.trans h7.ext).trans h8.ext).trans hx89).trans hx910).trans
          hx11).trans hx12).varAt hnext

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

/-- The starting store is first-order, with its variables below the next
one, and denotes what the problem denotes. -/
theorem startSt_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {P : Sorts.Prob} (hP : P.FO) {θ : Nat → Pat} (hsolve : solve P.e = some θ)
    {A : Sorts.Atoms}
    (hA : ∀ a ∈ A, a.2 ∈ Sorts.names S ∧ a.1 < (leftVars nm P θ).length)
    (hsem : ∀ σ : Nat → GTerm, (∀ a ∈ sortedOf P θ (leftVars nm P θ),
      Sorts.mem S a.1 (a.2.bind σ) = true) ↔ Sorts.Atoms.Holds S A σ) :
    (startSt P θ (leftVars nm P θ) A).OK ∧
      (∀ p ∈ (startSt P θ (leftVars nm P θ) A).L, Sub U p.2) ∧
      (startSt P θ (leftVars nm P θ) A).abs.store.Fin (startSt P θ (leftVars nm P θ) A).N ∧
      P.Den S = (startSt P θ (leftVars nm P θ) A).abs.store.Den S := by
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

/-! ### Without the hidden variables -/

/-- A state without its hidden variables: the solved forms of the exclusions
over the variables of the pattern, and the entries of these variables. -/
def pruneSt (st : TSt) : TSt :=
  ⟨st.T, Sorts.pruneX (Sorts.firsts st.T.vars) st.X,
    st.L.filter (fun e => decide (e.1 ∈ Sorts.firsts st.T.vars)), st.N⟩

theorem conjOf_filter (K : List Nat) (L : List (Nat × Sorts.Conj)) (u : Nat) :
    conjOf (L.filter fun e => decide (e.1 ∈ K)) u = if u ∈ K then conjOf L u else ∅ := by
  induction L with
  | nil => simp [conjOf_nil]
  | cons e L ih =>
    by_cases he : e.1 ∈ K
    · rw [List.filter_cons_of_pos (by simpa using he), conjOf_cons, conjOf_cons, ih]
      by_cases hu : u = e.1
      · subst hu; simp [he]
      · simp [hu]
    · rw [List.filter_cons_of_neg (by simpa using he), ih, conjOf_cons]
      by_cases hu : u = e.1
      · subst hu; simp [he]
      · simp [hu]

theorem pruneSt_ok {st : TSt} (h : st.OK) : (pruneSt st).OK :=
  ⟨(h.nodup.sublist (List.filter_sublist.map Prod.fst)),
    fun e he => h.lt e (List.mem_filter.1 he).1⟩

theorem pruneSt_abs {st : TSt} (h : st.OK) (htv : ∀ v ∈ st.T.vars, v < st.N) :
    (pruneSt st).abs = st.abs.prune := by
  have hmem := (Sorts.firsts_spec st.T.vars).2.1
  refine cstore_ext rfl (Sorts.pruneX_congr hmem st.X) ?_ fun u => ?_
  · rw [Sorts.CStore.prune_length, TSt.abs_length, TSt.abs_length]; rfl
  · rw [(pruneSt_ok h).conj, Sorts.CStore.prune_conj (by rw [TSt.abs_length]; exact htv), h.conj]
    show conjOf (st.L.filter fun e => decide (e.1 ∈ Sorts.firsts st.T.vars)) u = _
    rw [conjOf_filter]
    simp only [hmem]
    rfl

/-- A first-order state with its one-valued variables replaced and its
hidden variables dropped is one the rounds of `tighten` go on from, and
denotes the same; a state with an entry without a member denotes nothing. -/
theorem front_sound {S : Sorts} (hS : S.WellFormed) {st : TSt} (hok : st.OK)
    (hfin : st.abs.store.Fin st.N) :
    if settleOk S st.L = true then
      (pruneSt (settleSt S st)).Good S ∧
        (pruneSt (settleSt S st)).abs.store.Den S = st.abs.store.Den S
    else st.abs.store.Den S = ∅ := by
  by_cases hflag : settleOk S st.L = true
  · simp only [hflag, ↓reduceIte]
    obtain ⟨hden, hlen, hfin', -⟩ := Sorts.settle_spec S (st.L.map Prod.fst) st.abs
    have habs := settleSt_abs (S := S) hok
    have hok1 := settleSt_ok (S := S) hok
    have hfin1 : (settleSt S st).abs.store.Fin (settleSt S st).abs.c.length := by
      rw [habs, hlen]
      exact hfin' (by rw [TSt.abs_length]; exact hfin)
    have hmanyL : ∀ e ∈ (settleSt S st).L, Sorts.count S e.2 = .many := by
      intro e he
      obtain ⟨he1, he2⟩ := mem_settleKept.1 he
      have hnn := (List.all_eq_true.1 hflag) e he1
      cases hc : Sorts.count S e.2 with
      | none => rw [hc] at hnn; simp [noneB] at hnn
      | one g => rw [hc] at he2; simp [isOne] at he2
      | many => rfl
    have hmany : ∀ u, Sorts.count S ((settleSt S st).abs.conj u) = .many := by
      intro u
      rw [hok1.conj]
      by_cases hu : ∃ c, (u, c) ∈ (settleSt S st).L
      · obtain ⟨c, hc⟩ := hu
        rw [conjOf_mem hok1.nodup hc]
        exact hmanyL _ hc
      · rw [conjOf_not fun e he e' => hu ⟨e.2, by rw [← e']; exact he⟩]
        exact count_empty S
    obtain ⟨hd, hk, -⟩ := Sorts.prune_spec hS hfin1 hmany
    have hpa := pruneSt_abs hok1 (fun v hv => by
      have := hfin1.tv v hv
      rwa [TSt.abs_length] at this)
    exact ⟨⟨pruneSt_ok hok1, by rw [hpa]; exact hk,
      fun e he => hmanyL e (List.mem_filter.1 he).1⟩, by rw [hpa, hd, habs, hden]⟩
  · simp only [hflag, Bool.false_eq_true, ↓reduceIte]
    have hex : ∃ e ∈ st.L, Sorts.count S e.2 = .none := by
      by_contra hne
      refine hflag (List.all_eq_true.2 fun e he => ?_)
      cases hc : Sorts.count S e.2 with
      | none => exact absurd ⟨e, he, hc⟩ hne
      | one g => rfl
      | many => rfl
    obtain ⟨e, he, hc⟩ := hex
    ext g
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨σ, hσ, -⟩
    have hm : Sorts.MemC S (st.abs.conj e.1) (σ e.1) := hσ.1 e.1
    rw [hok.conj, conjOf_mem hok.nodup he] at hm
    exact Sorts.count_none.1 hc ⟨_, hm⟩

/-! ### The charge -/

/-- What `normal` comes to on a starting store with at most `k` rounds:
nothing when more are needed, and otherwise the tight state reached, or
nothing when the store denotes nothing. -/
def normRes (S : Sorts) (k : Nat) (st : TSt) : Option (Option TSt) :=
  if settleOk S st.L then tightRun S k (pruneSt (settleSt S st)) else some none

/-- The ticks `normal` may take after tightening, from the tight store. -/
noncomputable def tailCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (rc q : Nat)
    (st : TSt) : Nat :=
  renumberCost nm S U.length rc q st.T st.X st.L + placesCost (numRaw S st).c.length +
    normExsCost nm S U rc (numRaw S st) (numX st) +
    antiCost (numRaw S st).c.length (listsCard nm (numLs S st)) (numLs S st).length

/-- The ticks `normal` may take after `start`, from the starting store, with
at most `k` rounds that come to `o`. -/
noncomputable def normCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (rc q k : Nat)
    (st : TSt) (o : Option TSt) : Nat :=
  settleCost nm S U.length st.L st.T st.X +
    if settleOk S st.L then
      firstsCost (settleSt S st).T +
        pruneCost nm (Sorts.firsts (settleSt S st).T.vars) (settleSt S st).X
          (settleSt S st).L.length +
        runCost nm S U.length rc k (pruneSt (settleSt S st)) +
        (match o with
          | none => 0
          | some st' => tailCost nm S U rc q st')
    else 0

/-- A bound on what `normal` spends after `start`: on replacing the
variables with one value, dropping the hidden ones, tightening in as many
rounds as it takes, and what follows on the tight store. -/
def NormBound (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (rc q : Nat)
    (P : Sorts.Prob) (B : Nat) : Prop :=
  ∀ θ A k o, solve P.e = some θ →
    normRes S k (startSt P θ (leftVars nm P θ) A) = some o →
    normCost nm S U rc q k (startSt P θ (leftVars nm P θ) A) o ≤ B

/-! ### The tight store, numbered -/

/-- A tight store that denotes what a problem denotes gives the normal store
of the problem: its pattern numbered, the sorts of its variables, and its
exclusions normalised. -/
theorem tail_spec {S : Sorts} (hS : S.WellFormed) {P : Sorts.Prob} (hP : P.FO) {st : TSt}
    (hok : st.OK) (hden : st.abs.store.Den S = P.Den S) (hI : Sorts.Inv S st.abs)
    (hsole : ∀ v ∈ st.abs.t.vars,
      Sorts.sole S (st.abs.conj v) (Sorts.gone st.abs.x v) = none) :
    (∀ θ ∈ numYs S st, Sorts.Pre (numRaw S st).c.length θ) ∧
      (∀ E ∈ numX st, E.FO) ∧ (∀ E ∈ numX st, ∀ v ∈ E.vars, v < (numRaw S st).c.length) ∧
      (Sorts.antichain (Sorts.covers (numRaw S st).c.length) (numYs S st)).Nodup ∧
      P.norm S hS = some ⟨(numRaw S st).t, (numRaw S st).c,
        (Sorts.antichain (Sorts.covers (numRaw S st).c.length) (numYs S st)).toFinset⟩ := by
  obtain ⟨hN, hD⟩ := Sorts.ofTight_normal hS hI hsole
  rw [ofTight_abs hok] at hN hD
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
  refine ⟨fun θ hθ => ?_, hfo, hv, ?_, ?_⟩
  · obtain ⟨E, hE, hEθ⟩ := List.mem_filterMap.1 hθ
    exact (Sorts.normEx_some (hfo E hE) (hv E hE) hEθ).1
  · have := Sorts.ofTight_nodup hS hI hsole
    rw [ofTightXs_abs hok] at this
    exact this
  · exact Sorts.Prob.norm_unique hS hP hN (hD.trans hden)

/-- What `normal` returns: nothing when the problem has no normal store, and
otherwise the pattern, the sorts of the variables and the exclusions, each
as the list of its values, of the normal store of the problem. -/
def NormalPost (nm : Option Nat → RwLog.Sym) (S : Sorts) (hS : S.WellFormed) (U : List Name)
    (P : Sorts.Prob) (nodes : List store.Node)
    (res : Option sorts.Rep) : Prop :=
  match res with
  | none => P.norm S hS = none
  | some o => ∃ r : Sorts.Raw, P.norm S hS = some r ∧ Repr nm nodes o.t.val r.t ∧
      Repr nm nodes o.c.val (encList (nm none) (r.c.map (cpat (nm none) U))) ∧
      ∃ Y : List Sorts.Binds, Y.Nodup ∧ Y.toFinset = r.x ∧
        Repr nm nodes o.x.val (encLL nm (Y.map (vals r.c.length)))

/-- `normal` computes the normal store of a problem (`Sorts.Prob.norm`),
within the charge of `start` and a bound on the charge of what follows it:
replacing the variables with one value, dropping the hidden ones, tightening
in as many rounds as it takes, and numbering the tight store. -/
theorem normal_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) (hS : S.WellFormed)
    (hUS : ∀ n ∈ U, n ∈ Sorts.names S) {rc q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (P : Sorts.Prob) (hP : P.FO)
    (hPa : ∀ a ∈ P.a, a.1 ∈ Sorts.names S) (B : Nat) (hB : NormBound nm S U rc q P B)
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
  step with start_spec hnm hC P hP hPa s decls names t e a x hI hde hU ht he ha hx
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
      obtain ⟨hok, hsubL, hfin, hden0⟩ := startSt_spec hC hP hsolve hA hsem
      have hBθ := hB θ A
      have hfront := front_sound hS hok hfin
      generalize startSt P θ (leftVars nm P θ) A = st0 at hH hok hsubL hfin hden0 hBθ hfront
      by_cases hflag : settleOk S st0.L = true
      · simp only [hflag, ↓reduceIte] at hfront
        obtain ⟨hG, hden1⟩ := hfront
        obtain ⟨k, o, hrun, hmatch⟩ := tighten_sound hS _ hG
        have hBk := hBθ k o hsolve (by simp only [normRes, hflag, ↓reduceIte]; exact hrun)
        simp only [normCost, hflag, ↓reduceIte] at hBk
        step with settle_spec hnm hC st0.L st0.T st0.X s1 decls names t0 x0 es0 hI1
          (hx1.repr hde) (hx1.repr hU) hsubL hH.es hH.t hH.x (by unfold Room; omega)
          as ⟨ok0, t1, x1, es1, s2, hI2, hx2, ht2, h0, h1, h2, h3⟩
        rw [hflag] at h0
        subst h0
        simp only [↓reduceIte]
        have hx02 := hx1.trans hx2
        step with firsts_spec hnm s2 t1 (tp := (settleSt S st0).T) hI2 h1 (by unfold Room; omega)
          as ⟨ks, s3, hI3, hx3, ht3, rks⟩
        step with prune_spec hnm (U := U) (Sorts.firsts (settleSt S st0).T.vars)
          (settleSt S st0).X (settleSt S st0).L s3 ks x1 es1 hI3 rks (hx3.repr h2) (hx3.repr h3)
          (by unfold Room; omega) as ⟨x2, es2, s4, hI4, hx4, ht4, rx2, res2⟩
        have hx04 := (hx02.trans hx3).trans hx4
        have hH4 : Holds nm U s4.nodes.val (pruneSt (settleSt S st0)) t1 x2 es2 next0 :=
          ⟨(hx3.trans hx4).repr h1, rx2, res2, ((hx2.trans hx3).trans hx4).varAt hH.next⟩
        have hsub4 : ∀ p ∈ (pruneSt (settleSt S st0)).L, Sub U p.2 := fun p hp =>
          hsubL p (mem_settleKept.1 (List.mem_filter.1 hp).1).1
        step with tighten_spec hnm hC hr s4 decls names t1 x2 es2 next0 _ k o hI4
          (hx04.repr hde) (hx04.repr hU) hH4 hsub4 hrun (by unfold Room; omega)
          as ⟨o1, s5, hI5, hx5, ht5, hres⟩
        have hx05 := hx04.trans hx5
        cases o with
        | none =>
          simp only at hres hmatch hBk
          subst hres
          simp only [WP.spec_ok]
          refine ⟨hI5, hx05, by omega, ?_⟩
          simp only [NormalPost]
          refine Sorts.Prob.norm_of_empty hS hP ?_
          rw [hden0, ← hden1, hmatch]
        | some st' =>
          simp only at hres hmatch hBk
          obtain ⟨t11, x3, es3, next1, rfl, hH', hsub'⟩ := hres
          obtain ⟨hden', hInv, hsole, hGood⟩ := hmatch
          simp only [tailCost] at hBk
          obtain ⟨hPre, hfoX, hvX, hndZ, hnorm⟩ := tail_spec hS hP hGood.ok
            (by rw [hden', hden1, hden0]) hInv hsole
          obtain ⟨-, hFmem', -⟩ := Sorts.firsts_spec st'.T.vars
          step with renumber_spec hnm hC hS hUS hr hq s5 decls names t11 x3 es3 st'.T st'.X st'.L
            hI5 (hx05.repr hde) (hx05.repr hU) hH'.t hH'.x hH'.es hsub' (by unfold Room; omega)
            as ⟨t21, x4, cs, s6, hI6, hx6, ht6, rT, rX, rC⟩
          have hx06 := hx05.trans hx6
          have rT' : Repr nm s6.nodes.val t21.val (numRaw S st').t := by
            rw [bind_numSub fun v hv => (hFmem' v).2 hv] at rT
            exact rT
          have rX' : Repr nm s6.nodes.val x4.val (encX nm (numX st')) := by
            rw [encX_numSub (nm := nm) (X := st'.X) fun E hE p hp =>
              ⟨fun v hv => (hFmem' v).2 (hInv.xv E hE v
                (List.mem_flatMap.2 ⟨p, hp, List.mem_append_left _ hv⟩)),
              fun v hv => (hFmem' v).2 (hInv.xv E hE v
                (List.mem_flatMap.2 ⟨p, hp, List.mem_append_right _ hv⟩))⟩] at rX
            exact rX
          have rC' : Repr nm s6.nodes.val cs.val
              (encList (nm none) ((numRaw S st').c.map (cpat (nm none) U))) := by
            simpa [numRaw, List.map_map, Function.comp_def] using rC
          have hklen : ((numRaw S st').c.map (cpat (nm none) U)).length =
              (numRaw S st').c.length := List.length_map _
          step with places_spec ((numRaw S st').c.map (cpat (nm none) U)) s6 cs hI6 rC'
            (by rw [hklen]; unfold Room; omega) as ⟨vs, s7, hI7, hx7, ht7, rvs⟩
          rw [hklen] at ht7 rvs
          have hx07 := hx06.trans hx7
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
          step with norm_exs_spec hnm hC hr (numRaw S st') hcN (numX st') hfoX hvX s7 decls names
            vs cs x4 hI7 (hx07.repr hde) (hx07.repr hU) rvs (hx7.repr rC') (hx7.repr rX')
            (by unfold Room; omega) as ⟨ys, s8, hI8, hx8, ht8, rys⟩
          have rys' : Repr nm s8.nodes.val ys.val (encLL nm (numLs S st')) := rys
          have hL : ∀ B' ∈ numLs S st', B'.length = (numRaw S st').c.length ∧
              (encList (nm none) B').subs.card ≤ listsCard nm (numLs S st') := by
            intro B' hB'
            refine ⟨?_, le_listsCard hB'⟩
            obtain ⟨θ', -, rfl⟩ := List.mem_map.1 hB'
            exact vals_length _ _
          step with antichain_spec hnm (numRaw S st').c.length (listsCard nm (numLs S st'))
            (numLs S st') s8 vs ys hI8 (hx8.repr rvs) rys' hL (by unfold Room; omega)
            as ⟨zs, s9, hI9, hx9, ht9, rzs⟩
          refine ⟨hI9, ((hx06.trans hx7).trans hx8).trans hx9, by omega, ?_⟩
          simp only [NormalPost]
          have hY : ∀ θ' ∈ numYs S st', ∀ b' ∈ θ', b'.1 < (numRaw S st').c.length :=
            fun θ' hθ' => (hPre θ' hθ').dom
          have eZ : Sorts.antichain coversV (numLs S st') =
              (Sorts.antichain (Sorts.covers (numRaw S st').c.length)
                (numYs S st')).map (vals (numRaw S st').c.length) := antichain_vals hY
          rw [eZ] at rzs
          exact ⟨_, hnorm, ((hx7.trans hx8).trans hx9).repr rT',
            ((hx7.trans hx8).trans hx9).repr rC', _, hndZ, rfl, rzs⟩
      · have hfl : settleOk S st0.L = false := by simpa using hflag
        simp only [hfl, Bool.false_eq_true, ↓reduceIte] at hfront
        have hBk := hBθ 0 none hsolve (by simp only [normRes, hfl, Bool.false_eq_true, ↓reduceIte])
        simp only [normCost, hfl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hBk
        step with settle_spec hnm hC st0.L st0.T st0.X s1 decls names t0 x0 es0 hI1
          (hx1.repr hde) (hx1.repr hU) hsubL hH.es hH.t hH.x (by unfold Room; omega)
          as ⟨ok0, t1, x1, es1, s2, hI2, hx2, ht2, h0, h1, h2, h3⟩
        rw [hfl] at h0
        subst h0
        simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        refine ⟨hI2, hx1.trans hx2, by omega, ?_⟩
        simp only [NormalPost]
        exact Sorts.Prob.norm_of_empty hS hP (by rw [hden0]; exact hfront)

end RwLogVerified
