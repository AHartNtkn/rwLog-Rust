/-
# `sorts::prune` against the specification

`sorts::solved_ex` gives the solved form of an exclusion
(`Sorts.solvedEx`), and `sorts::prune` keeps the solved forms whose
variables are all among given ones, with the entries of these variables
(`Sorts.pruneX`). With `Sorts.prune_spec` this drops the hidden variables of
a store all of whose variables have infinitely many values.
-/
import RwLogVerified.Assemble
import RwLogVerified.Number
import RwLogVerified.Tight
import RwLog.Sorts.Prune

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## Equations as a list of terms -/

/-- An equation as a term. -/
def eqPat (p : Pat × Pat) : Pat := .app p.1 p.2

theorem encEqs_eq_encList (E : Eqns Nat) : encEqs nm E = encList (nm none) (E.map eqPat) := by
  induction E with
  | nil => rfl
  | cons p E ih => simp only [encEqs, List.map_cons, encList, ih, eqPat]

theorem vars_encEqs (E : Eqns Nat) : (encEqs nm E).vars = E.vars := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    simp only [encEqs, Term.vars, ih]
    simp [Eqns.vars]

/-! ## The equations of the moved variables -/

/-- The equations of the variables whose value is not themselves. -/
def movedOf (VP : List (Nat × Pat)) : Eqns Nat :=
  (VP.filter fun q => decide (q.2 ≠ .var q.1)).map fun q => (.var q.1, q.2)

theorem movedOf_map (θ : Nat → Pat) (V : List Nat) :
    movedOf (V.map fun y => (y, θ y)) = Sorts.solvedOn θ V := by
  simp [movedOf, Sorts.solvedOn, List.filter_map, Function.comp_def]

theorem moved_loop_spec (hnm : Function.Injective nm) :
    ∀ (VP : List (Nat × Pat)) (s : store.Store) (out vs l : store.TermId) (O : List Pat),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) (VP.map fun q => Term.var q.1)) →
    Repr nm s.nodes.val l.val (encList (nm none) (VP.map Prod.snd)) →
    Repr nm s.nodes.val out.val (encList (nm none) O) →
    Room s (5 * VP.length + 1) →
    sorts.moved_loop s out vs l true ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 5 * VP.length + 1 ∧
        Repr nm s'.nodes.val out'.val
          (encList (nm none) (((movedOf VP).map eqPat).reverse ++ O)) ⦄ := by
  intro VP
  induction VP with
  | nil =>
    intro s out vs l O hI hvs hl hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.moved_loop
    rw [loop]
    simp only [sorts.moved_loop.body, ↓reduceIte]
    step with uncons_repr s vs hI.toWf (p := Term.sym (nm none)) hvs (by unfold Room; omega)
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
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
      by rw [K1.nodes]; exact hout⟩
  | cons q VP ih =>
    intro s out vs l O hI hvs hl hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.moved_loop
    rw [loop]
    simp only [sorts.moved_loop.body, ↓reduceIte]
    step with uncons_repr s vs hI.toWf
      (p := Term.app (Term.var q.1) (encList (nm none) (VP.map fun q => Term.var q.1))) hvs
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨v, vrest, rfl, rv, rvrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with uncons_repr s1 l K1.inv.toWf
      (p := Term.app q.2 (encList (nm none) (VP.map Prod.snd))) (by rw [K1.nodes]; exact hl)
      (by unfold Room; omega) as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨p, lrest, rfl, rp, rlrest⟩ := hu1
    rw [K1.nodes] at rp rlrest
    have K2 := hK1.kept K1.inv
    have ht2 := K2.ticks
    step with same_spec s2 v p K2.inv (by unfold Room; omega) as ⟨r2, hres, K3⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hres K3
    have ht3 := K3.ticks
    have hn3 : s3.nodes.val = s.nodes.val := by rw [K3.nodes, K2.nodes, K1.nodes]
    have hx3 : Extends s s3 := Extends.of_eq hn3 (by omega)
    by_cases e : v.val = p.val
    · have : b = true := by simp [hres, e]
      subst this
      have hq : q.2 = Term.var q.1 := by rw [e] at rv; exact rp.unique rv
      simp only [↓reduceIte, uncurry, bind_ok]
      have IH := ih s3 out vrest lrest O K3.inv (hx3.repr rvrest) (hx3.repr rlrest)
        (hx3.repr hout) (by unfold Room; omega)
      unfold sorts.moved_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx3.trans hx', by simp only [List.length_cons]; omega, ?_⟩
      have em : movedOf (q :: VP) = movedOf VP := by simp [movedOf, hq]
      rw [em]
      exact hr'
    · have : b = false := by simp [hres, e]
      subst this
      have hq : q.2 ≠ Term.var q.1 := fun h => e (Repr.inj hnm hI.nodesOK rv (h ▸ rp))
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry]
      step with alloc_spec s3 (.App v p) K3.inv ⟨(hx3.repr rv).lt, (hx3.repr rp).lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨eq, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx3.trans hx4
      have req : Repr nm s4.nodes.val eq.val (eqPat (Term.var q.1, q.2)) :=
        .app hr4 (hx04.repr rv) (hx04.repr rp)
      step with alloc_spec s4 (.App eq out) hI4 ⟨req.lt, (hx04.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r5, hI5, ht5, htb5, hx5, hr5⟩
      obtain ⟨out1, s5⟩ := r5
      simp only [norm] at hI5 ht5 htb5 hx5 hr5
      have hx05 := hx04.trans hx5
      have hout1 : Repr nm s5.nodes.val out1.val
          (encList (nm none) (eqPat (Term.var q.1, q.2) :: O)) :=
        .app hr5 (hx5.repr req) (hx05.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s5 out1 vrest lrest (eqPat (Term.var q.1, q.2) :: O) hI5 (hx05.repr rvrest)
        (hx05.repr rlrest) hout1 (by unfold Room; omega)
      unfold sorts.moved_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx05.trans hx', by simp only [List.length_cons]; omega, ?_⟩
      have em : movedOf (q :: VP) = (Term.var q.1, q.2) :: movedOf VP := by simp [movedOf, hq]
      rw [em]
      simpa using hr'

/-- `moved` lists the equations of the variables whose value is not
themselves, in order. -/
theorem moved_spec (hnm : Function.Injective nm) (VP : List (Nat × Pat)) (s : store.Store)
    (vs l : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (VP.map fun q => Term.var q.1)))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) (VP.map Prod.snd)))
    (hroom : Room s (7 * VP.length + 4)) :
    sorts.moved s vs l ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 7 * VP.length + 4 ∧
        Repr nm s'.nodes.val res.val (encEqs nm (movedOf VP)) ⦄ := by
  unfold sorts.moved
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with moved_loop_spec hnm VP s1 out vs l [] hI1 (hx1.repr hvs) (hx1.repr hl) (.nil hr1)
    (by unfold Room; omega) as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  have hlen : (movedOf VP).length ≤ VP.length := by
    simp only [movedOf, List.length_map]
    exact List.length_filter_le _ _
  refine WP.spec_mono (rev_spec (nm := nm) (((movedOf VP).map eqPat).reverse ++ [])
    s2 out1 hI2.toWf hr2 (by simp only [List.length_map, List.length_append,
      List.length_reverse, List.length_nil]; unfold Room; omega)) ?_
  rintro ⟨res, s3⟩ ⟨hR, hr3⟩
  have ht3 := hR.ticks
  simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil] at ht3
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext, by omega, ?_⟩
  rw [encEqs_eq_encList]
  simpa using hr3

/-! ## The solved form of an exclusion -/

/-- The ticks `solved_ex` may take. -/
def solvedExCost (nm : Option Nat → RwLog.Sym) (E : Eqns Nat) : Nat :=
  firstsCost (encEqs nm E) +
    solveCost E (encList (nm none) ((Sorts.firsts E.vars).map Term.var)) +
    7 * (Sorts.firsts E.vars).length + 4

/-- `solved_ex` gives the solved form of an exclusion. -/
theorem solved_ex_spec (hnm : Function.Injective nm) (E : Eqns Nat) (s : store.Store)
    (e : store.TermId) (hI : Inv s) (he : Repr nm s.nodes.val e.val (encEqs nm E))
    (hroom : Room s (solvedExCost nm E)) :
    sorts.solved_ex s e ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + solvedExCost nm E ∧
        match Sorts.solvedEx E with
        | none => res = none
        | some E' => ∃ r, res = some r ∧ Repr nm s'.nodes.val r.val (encEqs nm E') ⦄ := by
  unfold sorts.solved_ex
  have hroom' := hroom
  unfold Room at hroom'
  simp only [solvedExCost] at hroom'
  step with firsts_spec hnm s e hI he (by unfold Room; omega) as ⟨vs, s1, hI1, hx1, ht1, rvs⟩
  rw [vars_encEqs] at rvs
  step with solve_into_spec hnm s1 e vs hI1 (hx1.repr he) rvs (by unfold Room; omega)
    as ⟨ok, vals, s2, hI2, hx2, ht2, hres⟩
  have hx02 := hx1.trans hx2
  cases ok with
  | false =>
    simp only [SolveRes, Bool.false_eq_true, ↓reduceIte, Eqns.solveOn, Option.map_eq_none_iff]
      at hres
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hI2, hx02, by simp only [solvedExCost]; omega, ?_⟩
    simp only [Sorts.solvedEx, hres, Option.map_none]
  | true =>
    simp only [SolveRes, ↓reduceIte, Eqns.solveOn, Option.map_eq_some_iff] at hres
    obtain ⟨q', rvals, ⟨θ, hθ, rfl⟩, -⟩ := hres
    simp only [↓reduceIte]
    have e1 : (encList (nm none) ((Sorts.firsts E.vars).map Term.var)).bind θ =
        encList (nm none) (((Sorts.firsts E.vars).map fun y => (y, θ y)).map Prod.snd) := by
      rw [encList_bind]
      simp [List.map_map, Function.comp_def]
    rw [e1] at rvals
    have e2 : (Sorts.firsts E.vars).map Term.var =
        ((Sorts.firsts E.vars).map fun y => (y, θ y)).map fun q : Nat × Pat => Term.var q.1 := by
      simp [List.map_map, Function.comp_def]
    rw [e2] at rvs
    step with moved_spec hnm ((Sorts.firsts E.vars).map fun y => (y, θ y)) s2 vs vals hI2
      (hx2.repr rvs) rvals (by simp only [List.length_map]; unfold Room; omega)
      as ⟨ti, s3, hI3, hx3, ht3, rti⟩
    simp only [List.length_map] at ht3
    refine ⟨hI3, hx02.trans hx3, by simp only [solvedExCost]; omega, ?_⟩
    simp only [Sorts.solvedEx, hθ, Option.map_some]
    rw [movedOf_map] at rti
    exact ⟨ti, rfl, rti⟩

/-- The ticks the solved forms of a list of exclusions may take, without
the last reversal. -/
def solvedExsLoopCost (nm : Option Nat → RwLog.Sym) : List (Eqns Nat) → Nat
  | [] => 1
  | E :: X => solvedExCost nm E + 2 + solvedExsLoopCost nm X

theorem solved_exs_loop_spec (hnm : Function.Injective nm) :
    ∀ (X : List (Eqns Nat)) (s : store.Store) (xs out : store.TermId) (O : List (Eqns Nat)),
    Inv s → Repr nm s.nodes.val xs.val (encX nm X) → Repr nm s.nodes.val out.val (encX nm O) →
    Room s (solvedExsLoopCost nm X) →
    sorts.solved_exs_loop xs s out ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + solvedExsLoopCost nm X ∧
        Repr nm s'.nodes.val out'.val
          (encX nm ((X.filterMap Sorts.solvedEx).reverse ++ O)) ⦄ := by
  intro X
  induction X with
  | nil =>
    intro s xs out O hI hxs hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [solvedExsLoopCost] at hroom'
    unfold sorts.solved_exs_loop
    rw [loop]
    simp only [sorts.solved_exs_loop.body]
    step with uncons_repr s xs hI.toWf (p := Term.sym (nm none)) hxs (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + solvedExsLoopCost nm ([] : List (Eqns Nat)) ∧
        Repr nm s1.nodes.val out.val
          (encX nm ((([] : List (Eqns Nat)).filterMap Sorts.solvedEx).reverse ++ O)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [solvedExsLoopCost]; omega,
        by rw [K1.nodes]; exact hout⟩
    step*
  | cons E X ih =>
    intro s xs out O hI hxs hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [solvedExsLoopCost] at hroom'
    unfold sorts.solved_exs_loop
    rw [loop]
    simp only [sorts.solved_exs_loop.body]
    step with uncons_repr s xs hI.toWf (p := Term.app (encEqs nm E) (encX nm X)) hxs
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ei, rest, rfl, re, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with solved_ex_spec hnm E s1 ei K1.inv (hx1.repr re) (by unfold Room; omega)
      as ⟨r1, hI2, hx2, ht2, hres⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hI2 hx2 ht2 hres
    have hx02 := hx1.trans hx2
    cases hsE : Sorts.solvedEx E with
    | none =>
      rw [hsE] at hres
      simp only at hres
      subst hres
      simp only [uncurry, bind_ok]
      have IH := ih s2 rest out O hI2 (hx02.repr rrest) (hx02.repr hout) (by unfold Room; omega)
      unfold sorts.solved_exs_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx02.trans hx', by simp only [solvedExsLoopCost]; omega, ?_⟩
      simpa [List.filterMap_cons, hsE] using hr'
    | some E' =>
      rw [hsE] at hres
      simp only at hres
      obtain ⟨e1, rfl, re1⟩ := hres
      simp only [uncurry]
      step with alloc_spec s2 (.App e1 out) hI2 ⟨re1.lt, (hx02.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r3, hI3, ht3, htb3, hx3, hr3⟩
      obtain ⟨out1, s3⟩ := r3
      simp only [norm] at hI3 ht3 htb3 hx3 hr3
      have hx03 := hx02.trans hx3
      have hout1 : Repr nm s3.nodes.val out1.val (encX nm (E' :: O)) :=
        .app hr3 (hx3.repr re1) (hx03.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s3 rest out1 (E' :: O) hI3 (hx03.repr rrest) hout1 (by unfold Room; omega)
      unfold sorts.solved_exs_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx03.trans hx', by simp only [solvedExsLoopCost]; omega, ?_⟩
      simpa [List.filterMap_cons, hsE] using hr'

/-- The ticks `solved_exs` may take. -/
def solvedExsCost (nm : Option Nat → RwLog.Sym) (X : List (Eqns Nat)) : Nat :=
  solvedExsLoopCost nm X + 2 * X.length + 3

/-- `solved_exs` lists the solved forms of the exclusions that have one. -/
theorem solved_exs_spec (hnm : Function.Injective nm) (X : List (Eqns Nat)) (s : store.Store)
    (xs : store.TermId) (hI : Inv s) (hxs : Repr nm s.nodes.val xs.val (encX nm X))
    (hroom : Room s (solvedExsCost nm X)) :
    sorts.solved_exs s xs ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + solvedExsCost nm X ∧
        Repr nm s'.nodes.val res.val (encX nm (X.filterMap Sorts.solvedEx)) ⦄ := by
  unfold sorts.solved_exs
  have hroom' := hroom
  unfold Room at hroom'
  simp only [solvedExsCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with solved_exs_loop_spec hnm X s1 xs out [] hI1 (hx1.repr hxs) (.nil hr1)
    (by unfold Room; omega) as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  have hlen : (X.filterMap Sorts.solvedEx).length ≤ X.length := List.length_filterMap_le _ _
  have hr2' : Repr nm s2.nodes.val out1.val (encList (nm none)
      (((X.filterMap Sorts.solvedEx).reverse ++ []).map (encEqs nm))) := hr2
  refine WP.spec_mono (rev_spec (nm := nm) _ s2 out1 hI2.toWf hr2'
    (by simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil]
        unfold Room; omega)) ?_
  rintro ⟨res, s3⟩ ⟨hR, hr3⟩
  have ht3 := hR.ticks
  simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil] at ht3
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext,
    by simp only [solvedExsCost]; omega, ?_⟩
  unfold encX
  simpa [List.map_reverse] using hr3

/-! ## The variables table `B` marks -/

theorem TblVal.extends {s s' : store.Store} {B : Nat → Option Nat} {M : Nat → Option Pat}
    (h : TblVal nm s.nodes.val B M) (hx : Extends s s') : TblVal nm s'.nodes.val B M := by
  refine ⟨fun q u hq => ?_, fun w p hw => ?_⟩
  · obtain ⟨w, p, h1, h2, h3⟩ := h.sound q u hq
    exact ⟨w, p, hx.varAt h1, h2, hx.repr h3⟩
  · obtain ⟨q, u, h1, h2⟩ := h.complete w p hw
    exact ⟨q, u, hx.varAt h1, h2⟩

/-- Whether the table has an entry at a node of a variable says whether the
variable has a value. -/
theorem TblVal.isSome {nodes : List store.Node} {B : Nat → Option Nat} {M : Nat → Option Pat}
    (h : TblVal nm nodes B M) (hN : NodesOK nodes) {q w : Nat} (hq : VarAt nodes q w) :
    (B q).isSome = (M w).isSome := by
  cases hB : B q with
  | some u =>
    obtain ⟨w', p, h1, h2, -⟩ := h.sound q u hB
    rw [hq.unique h1, h2]
    rfl
  | none =>
    cases hM : M w with
    | none => rfl
    | some p =>
      obtain ⟨q', u, h1, h2⟩ := h.complete w p hM
      rw [VarAt.inj hN hq h1, h2] at hB
      cases hB

/-- The table that gives each variable of a list one value. -/
theorem putAll_mark (c : Pat) (K : List Nat) :
    putAll (K.map fun v => (v, c)) (fun _ => none) = fun w => if w ∈ K then some c else none := by
  induction K using List.reverseRecOn with
  | nil => rfl
  | append_singleton K v ih =>
    unfold putAll at ih ⊢
    rw [List.map_append, List.foldl_append, ih]
    funext w
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.mem_append,
      List.mem_singleton]
    by_cases hw : w = v
    · subst hw; simp
    · simp [hw]

/-- The variables of a list replaced by a constant. -/
def markSub (z : RwLog.Sym) (K : List Nat) (w : Nat) : Pat := if w ∈ K then .sym z else .var w

theorem prune_loop_spec (nil : store.TermId) :
    ∀ (R : List Nat) (s : store.Store) (l : store.TermId) (M : Nat → Option Pat),
    Inv s → Repr nm s.nodes.val l.val (encList (nm none) (R.map Term.var)) →
    Repr nm s.nodes.val nil.val (Term.sym (nm none)) →
    TblVal nm s.nodes.val (tbl s .B) M → Room s (2 * R.length + 1) →
    sorts.prune_loop l s nil ⦃ s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s.ticks.val ≤ s'.ticks.val ∧
        s'.ticks.val ≤ s.ticks.val + 2 * R.length + 1 ∧
        TblVal nm s'.nodes.val (tbl s' .B)
          (putAll (R.map fun v => (v, Term.sym (nm none))) M) ⦄ := by
  intro R
  induction R with
  | nil =>
    intro s l M hI hl hnil hT hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.prune_loop
    rw [loop]
    simp only [sorts.prune_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ s1.nodes.val = s.nodes.val ∧ s.ticks.val ≤ s1.ticks.val ∧
        s1.ticks.val ≤ s.ticks.val + 2 * ([] : List Nat).length + 1 ∧
        TblVal nm s1.nodes.val (tbl s1 .B)
          (putAll (([] : List Nat).map fun v => (v, Term.sym (nm none))) M) :=
      ⟨K1.inv, K1.nodes, by omega, by simp only [List.length_nil]; omega,
        by rw [K1.nodes, K1.tbl]; exact hT⟩
    step*
  | cons v R ih =>
    intro s l M hI hl hnil hT hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.prune_loop
    rw [loop]
    simp only [sorts.prune_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (Term.var v) (encList (nm none) (R.map Term.var))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨vi, rest, rfl, rv, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hvv : VarAt s.nodes.val vi.val v := by
      cases rv with
      | var h => exact h
    simp only [uncurry]
    step with set_spec s1 .B vi nil K1.inv (by rw [K1.nodes]; exact hvv.lt)
      (by unfold Room; omega) as ⟨s2, g1, g2, g3, g4, g5⟩
    have hn2 : s2.nodes.val = s.nodes.val := by rw [g1, K1.nodes]
    rw [K1.tbl] at g4
    have IH := ih s2 rest (Function.update M v (some (Term.sym (nm none)))) g3
      (by rw [hn2]; exact rrest) (by rw [hn2]; exact hnil)
      (by rw [hn2, g4]; exact hT.set hI.nodesOK hvv hnil) (by unfold Room; omega)
    unfold sorts.prune_loop at IH
    refine WP.spec_mono IH ?_
    rintro s' ⟨hI', hn', hlo', ht', hT'⟩
    exact ⟨hI', by rw [hn', hn2], by omega, by simp only [List.length_cons]; omega, hT'⟩

/-! ## The entries of the marked variables -/

theorem kept_entries_loop_spec {U : List Name} (M : Nat → Option Pat) :
    ∀ (L : List (Nat × Sorts.Conj)) (s : store.Store) (es out : store.TermId)
      (O : List (Nat × Sorts.Conj)),
    Inv s → Repr nm s.nodes.val es.val (encVarEntries nm U L) →
    Repr nm s.nodes.val out.val (encVarEntries nm U O) →
    TblVal nm s.nodes.val (tbl s .B) M → Room s (4 * L.length + 1) →
    sorts.kept_entries_loop es s out ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ tbl s' = tbl s ∧ s'.ticks.val ≤ s.ticks.val + 4 * L.length + 1 ∧
        Repr nm s'.nodes.val out'.val
          (encVarEntries nm U ((L.filter fun e => (M e.1).isSome).reverse ++ O)) ⦄ := by
  intro L
  induction L with
  | nil =>
    intro s es out O hI hes hout hT hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.kept_entries_loop
    rw [loop]
    simp only [sorts.kept_entries_loop.body]
    step with uncons_repr s es hI.toWf (p := Term.sym (nm none)) hes (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧ tbl s1 = tbl s ∧
        s1.ticks.val ≤ s.ticks.val + 4 * ([] : List (Nat × Sorts.Conj)).length + 1 ∧
        Repr nm s1.nodes.val out.val (encVarEntries nm U
          ((([] : List (Nat × Sorts.Conj)).filter fun e => (M e.1).isSome).reverse ++ O)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), K1.tbl, by simp only [List.length_nil]; omega,
        by rw [K1.nodes]; exact hout⟩
    step*
  | cons en L ih =>
    intro s es out O hI hes hout hT hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.kept_entries_loop
    rw [loop]
    simp only [sorts.kept_entries_loop.body]
    step with uncons_repr s es hI.toWf
      (p := Term.app (varEntry nm U en) (encVarEntries nm U L)) hes
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ei, rest, rfl, re, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with uncons_repr s1 ei K1.inv.toWf
      (p := Term.app (Term.var en.1) (cpat (nm none) U en.2)) (by rw [K1.nodes]; exact re)
      (by unfold Room; omega) as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨vi, ci, rfl, rv, -⟩ := hu1
    rw [K1.nodes] at rv
    have K2 := hK1.kept K1.inv
    have ht2 := K2.ticks
    have hvv : VarAt s.nodes.val vi.val en.1 := by
      cases rv with
      | var h => exact h
    step with get_spec s2 .B vi K2.inv (by rw [K2.nodes, K1.nodes]; exact hvv.lt)
      (by unfold Room; omega) as ⟨r2, hget, K3⟩
    obtain ⟨o2, s3⟩ := r2
    simp only at hget K3
    have ht3 := K3.ticks
    rw [K2.tbl, K1.tbl] at hget
    have hn3 : s3.nodes.val = s.nodes.val := by rw [K3.nodes, K2.nodes, K1.nodes]
    have htb3 : tbl s3 = tbl s := by rw [K3.tbl, K2.tbl, K1.tbl]
    have hx3 : Extends s s3 := Extends.of_eq hn3 (by omega)
    have hsome : o2.isSome = (M en.1).isSome := by
      rw [← hT.isSome hI.nodesOK hvv, ← hget]
      cases o2 <;> rfl
    cases o2 with
    | none =>
      have hM : (M en.1).isSome = false := by rw [← hsome]; rfl
      simp only [uncurry, bind_ok]
      have IH := ih s3 rest out O K3.inv (hx3.repr rrest) (hx3.repr hout)
        (by rw [hn3, htb3]; exact hT) (by unfold Room; omega)
      unfold sorts.kept_entries_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', htb', ht', hr'⟩
      refine ⟨hI', hx3.trans hx', by rw [htb', htb3], by simp only [List.length_cons]; omega, ?_⟩
      have e : (en :: L).filter (fun e => (M e.1).isSome) = L.filter fun e => (M e.1).isSome := by
        simp [hM]
      rw [e]
      exact hr'
    | some u =>
      have hM : (M en.1).isSome = true := by rw [← hsome]; rfl
      simp only [uncurry]
      step with alloc_spec s3 (.App ei out) K3.inv ⟨(hx3.repr re).lt, (hx3.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx3.trans hx4
      have hout1 : Repr nm s4.nodes.val out1.val (encVarEntries nm U (en :: O)) :=
        .app hr4 (hx04.repr re) (hx04.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s4 rest out1 (en :: O) hI4 (hx04.repr rrest) hout1
        (by rw [htb4, htb3]; exact hT.extends hx04) (by unfold Room; omega)
      unfold sorts.kept_entries_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', htb', ht', hr'⟩
      refine ⟨hI', hx04.trans hx', by rw [htb', htb4, htb3],
        by simp only [List.length_cons]; omega, ?_⟩
      have e : (en :: L).filter (fun e => (M e.1).isSome) =
          en :: L.filter fun e => (M e.1).isSome := by simp [hM]
      rw [e]
      simpa using hr'

/-- `kept_entries` keeps the entries of the variables table `B` has an entry
for, and leaves the tables. -/
theorem kept_entries_spec {U : List Name} (M : Nat → Option Pat) (L : List (Nat × Sorts.Conj))
    (s : store.Store) (es : store.TermId) (hI : Inv s)
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (hT : TblVal nm s.nodes.val (tbl s .B) M) (hroom : Room s (6 * L.length + 4)) :
    sorts.kept_entries s es ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' = tbl s ∧ s'.ticks.val ≤ s.ticks.val + 6 * L.length + 4 ∧
        Repr nm s'.nodes.val res.val
          (encVarEntries nm U (L.filter fun e => (M e.1).isSome)) ⦄ := by
  unfold sorts.kept_entries
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with kept_entries_loop_spec (nm := nm) (U := U) M L s1 es out [] hI1 (hx1.repr hes)
    (.nil hr1) (by rw [htb1]; exact hT.extends hx1) (by unfold Room; omega)
    as ⟨s2, out1, hI2, hx2, htb2, ht2, hr2⟩
  have hlen : (L.filter fun e => (M e.1).isSome).length ≤ L.length := List.length_filter_le _ _
  have hr2' : Repr nm s2.nodes.val out1.val (encList (nm none)
      (((L.filter fun e : Nat × Sorts.Conj => (M e.1).isSome).reverse ++ []).map
        (varEntry nm U))) := hr2
  refine WP.spec_mono (rev_spec (nm := nm) _ s2 out1 hI2.toWf hr2'
    (by simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil]
        unfold Room; omega)) ?_
  rintro ⟨res, s3⟩ ⟨hR, hr3⟩
  have ht3 := hR.ticks
  simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil] at ht3
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext,
    by rw [hR.tbl, htb2, htb1], by omega, ?_⟩
  unfold encVarEntries
  simpa [List.map_reverse] using hr3

/-! ## The members whose closed form has no variable -/

/-- The ticks `closed_ones` may take in its loop. -/
def closedLoopCost : List (Pat × Pat) → Nat
  | [] => 1
  | q :: LC => 13 * q.2.subs.card + 10 + closedLoopCost LC

theorem closed_ones_loop_spec (hnm : Function.Injective nm) :
    ∀ (LC : List (Pat × Pat)) (s : store.Store) (out l cs : store.TermId) (O : List Pat),
    Inv s → Repr nm s.nodes.val l.val (encList (nm none) (LC.map Prod.fst)) →
    Repr nm s.nodes.val cs.val (encList (nm none) (LC.map Prod.snd)) →
    Repr nm s.nodes.val out.val (encList (nm none) O) → Room s (closedLoopCost LC) →
    sorts.closed_ones_loop s out l cs true ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + closedLoopCost LC ∧
        Repr nm s'.nodes.val out'.val (encList (nm none)
          (((LC.filter fun q => decide (q.2.vars = [])).map Prod.fst).reverse ++ O)) ⦄ := by
  intro LC
  induction LC with
  | nil =>
    intro s out l cs O hI hl hcs hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [closedLoopCost] at hroom'
    unfold sorts.closed_ones_loop
    rw [loop]
    simp only [sorts.closed_ones_loop.body, ↓reduceIte]
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
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [closedLoopCost]; omega,
      by rw [K1.nodes]; exact hout⟩
  | cons q LC ih =>
    intro s out l cs O hI hl hcs hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [closedLoopCost] at hroom'
    unfold sorts.closed_ones_loop
    rw [loop]
    simp only [sorts.closed_ones_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf
      (p := Term.app q.1 (encList (nm none) (LC.map Prod.fst))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ei, rest, rfl, re, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with uncons_repr s1 cs K1.inv.toWf
      (p := Term.app q.2 (encList (nm none) (LC.map Prod.snd))) (by rw [K1.nodes]; exact hcs)
      (by unfold Room; omega) as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨ci, crest, rfl, rc, rcrest⟩ := hu1
    rw [K1.nodes] at rc rcrest
    have K2 := hK1.kept K1.inv
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    step with ground_spec hnm s2 ci K2.inv (by rw [hn2]; exact rc) (by unfold Room; omega)
      as ⟨r3, hI3, hn3, hlo3, ht3, hA3, hb⟩
    obtain ⟨b, s3⟩ := r3
    simp only at hI3 hn3 hlo3 ht3 hA3 hb
    have hn03 : s3.nodes.val = s.nodes.val := by rw [hn3, hn2]
    have hx3 : Extends s s3 := Extends.of_eq hn03 (by omega)
    cases b with
    | false =>
      have hq : decide (q.2.vars = []) = false := hb.symm
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s3 out rest crest O hI3 (hx3.repr rrest) (hx3.repr rcrest) (hx3.repr hout)
        (by unfold Room; omega)
      unfold sorts.closed_ones_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx3.trans hx', by simp only [closedLoopCost]; omega, ?_⟩
      have e : (q :: LC).filter (fun q => decide (q.2.vars = [])) =
          LC.filter fun q => decide (q.2.vars = []) := by simp [hq]
      rw [e]
      exact hr'
    | true =>
      have hq : decide (q.2.vars = []) = true := hb.symm
      simp only [↓reduceIte, uncurry]
      step with alloc_spec s3 (.App ei out) hI3 ⟨(hx3.repr re).lt, (hx3.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx3.trans hx4
      have hout1 : Repr nm s4.nodes.val out1.val (encList (nm none) (q.1 :: O)) :=
        .app hr4 (hx04.repr re) (hx04.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s4 out1 rest crest (q.1 :: O) hI4 (hx04.repr rrest) (hx04.repr rcrest) hout1
        (by unfold Room; omega)
      unfold sorts.closed_ones_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx04.trans hx', by simp only [closedLoopCost]; omega, ?_⟩
      have e : (q :: LC).filter (fun q => decide (q.2.vars = [])) =
          q :: LC.filter fun q => decide (q.2.vars = []) := by simp [hq]
      rw [e]
      simpa using hr'

/-- `closed_ones` keeps the members whose closed form has no variable. -/
theorem closed_ones_spec (hnm : Function.Injective nm) (LC : List (Pat × Pat)) (s : store.Store)
    (l cs : store.TermId) (hI : Inv s)
    (hl : Repr nm s.nodes.val l.val (encList (nm none) (LC.map Prod.fst)))
    (hcs : Repr nm s.nodes.val cs.val (encList (nm none) (LC.map Prod.snd)))
    (hroom : Room s (closedLoopCost LC + 2 * LC.length + 3)) :
    sorts.closed_ones s l cs ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + closedLoopCost LC + 2 * LC.length + 3 ∧
        Repr nm s'.nodes.val res.val (encList (nm none)
          ((LC.filter fun q => decide (q.2.vars = [])).map Prod.fst)) ⦄ := by
  unfold sorts.closed_ones
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with closed_ones_loop_spec hnm LC s1 out l cs [] hI1 (hx1.repr hl) (hx1.repr hcs)
    (.nil hr1) (by unfold Room; omega) as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  have hlen : (LC.filter fun q => decide (q.2.vars = [])).length ≤ LC.length :=
    List.length_filter_le _ _
  refine WP.spec_mono (rev_spec (nm := nm)
    (((LC.filter fun q => decide (q.2.vars = [])).map Prod.fst).reverse ++ [])
    s2 out1 hI2.toWf hr2 (by simp only [List.length_map, List.length_append,
      List.length_reverse, List.length_nil]; unfold Room; omega)) ?_
  rintro ⟨res, s3⟩ ⟨hR, hr3⟩
  have ht3 := hR.ticks
  simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil] at ht3
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext, by omega, ?_⟩
  simpa using hr3

/-! ## `prune` -/

/-- The solved forms of the exclusions, each with the term it becomes when
the variables of `K` are replaced by a constant. -/
def closedOf (nm : Option Nat → RwLog.Sym) (K : List Nat) (X : List (Eqns Nat)) :
    List (Pat × Pat) :=
  (X.filterMap Sorts.solvedEx).map fun E' =>
    (encEqs nm E', (encEqs nm E').bind (markSub (nm none) K))

/-- The ticks `prune` may take. -/
def pruneCost (nm : Option Nat → RwLog.Sym) (K : List Nat) (X : List (Eqns Nat)) (l : Nat) :
    Nat :=
  solvedExsCost nm X + 2 * K.length + 6 * l + 14 * (encX nm (X.filterMap Sorts.solvedEx)).subs.card +
    closedLoopCost (closedOf nm K X) + 2 * X.length + 20

/-- `prune` keeps the solved forms of the exclusions whose variables are all
in the list, and the entries of the variables in the list. -/
theorem prune_spec (hnm : Function.Injective nm) {U : List Name} (K : List Nat)
    (X : List (Eqns Nat)) (L : List (Nat × Sorts.Conj)) (s : store.Store)
    (ks xs es : store.TermId) (hI : Inv s)
    (hks : Repr nm s.nodes.val ks.val (encList (nm none) (K.map Term.var)))
    (hxs : Repr nm s.nodes.val xs.val (encX nm X))
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (hroom : Room s (pruneCost nm K X L.length)) :
    sorts.prune s ks xs es ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + pruneCost nm K X L.length ∧
        Repr nm s'.nodes.val res.1.val (encX nm (Sorts.pruneX K X)) ∧
        Repr nm s'.nodes.val res.2.val
          (encVarEntries nm U (L.filter fun e => decide (e.1 ∈ K))) ⦄ := by
  unfold sorts.prune
  have hroom' := hroom
  unfold Room at hroom'
  simp only [pruneCost] at hroom'
  have hXl : (X.filterMap Sorts.solvedEx).length ≤ X.length := List.length_filterMap_le _ _
  have hCl : (closedOf nm K X).length ≤ X.length := by
    simp only [closedOf, List.length_map]; exact hXl
  step with solved_exs_spec hnm X s xs hI hxs (by unfold Room; omega)
    as ⟨sol, s1, hI1, hx1, ht1, rsol⟩
  step with alloc_spec s1 .Nil hI1 trivial (by unfold Room; omega)
    as ⟨nil, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr2
  have hx02 := hx1.trans hx2
  step with clear_spec s2 .B hI2 (by unfold Room; omega) as ⟨s3, c1, c2, c3, c4, c5⟩
  step with prune_loop_spec (nm := nm) nil K s3 ks (fun _ => none) c3
    (by rw [c1]; exact hx02.repr hks) (by rw [c1]; exact .nil hr2)
    ⟨fun q u h => (by rw [c4] at h; cases h), fun w v h => (by cases h)⟩
    (by unfold Room; omega) as ⟨s4, hI4, hn4, hlo4, ht4, hT4⟩
  rw [putAll_mark] at hT4
  have hn04 : s4.nodes.val = s2.nodes.val := by rw [hn4, c1]
  have hx24 : Extends s2 s4 := Extends.of_eq hn04 (by omega)
  have hx04 := hx02.trans hx24
  step with kept_entries_spec (nm := nm) (U := U)
    (fun w => if w ∈ K then some (Term.sym (nm none)) else none) L s4 es hI4 (hx04.repr hes) hT4
    (by unfold Room; omega) as ⟨es1, s5, hI5, hx5, htb5, ht5, res1⟩
  have hx05 := hx04.trans hx5
  step with clear_spec s5 .A hI5 (by unfold Room; omega) as ⟨s6, d1, d2, d3, d4, d5⟩
  have hx56 : Extends s5 s6 := Extends.of_eq d1 (by omega)
  have hx06 := hx05.trans hx56
  have eσ : (fun w => (if w ∈ K then some (Term.sym (nm none) : Pat) else none).getD
      (Term.var w)) = markSub (nm none) K := by
    funext w
    unfold markSub
    split <;> rfl
  have hleaf : LeafOK nm s6.nodes.val (tbl s6 .B) term.Leaf.Map (markSub (nm none) K) := by
    rw [d5 .B (by simp), htb5, ← eσ]
    exact (hT4.extends (hx5.trans hx56)).leaf
  have hpc := pending_card_le (nm := nm) s6.nodes.val (tbl s6 .A)
    (encX nm (X.filterMap Sorts.solvedEx)).subs
  step with rebuild_spec hnm s6 .Map sol (t := encX nm (X.filterMap Sorts.solvedEx))
    (σ := markSub (nm none) K) (encX nm (X.filterMap Sorts.solvedEx)).subs d3
    ((((hx2.trans hx24).trans hx5).trans hx56).repr rsol) hleaf
    (by intro q v hq; rw [d4] at hq; cases hq)
    (Finset.Subset.refl _) (by unfold Room; omega) as ⟨closed, s7, h7⟩
  have hc7 := h7.cost
  have hx07 := hx06.trans h7.ext
  have rl : Repr nm s7.nodes.val sol.val (encList (nm none) ((closedOf nm K X).map Prod.fst)) := by
    have := (((((hx2.trans hx24).trans hx5).trans hx56).trans h7.ext).repr rsol)
    simpa [closedOf, encX, List.map_map, Function.comp_def] using this
  have rc : Repr nm s7.nodes.val closed.val
      (encList (nm none) ((closedOf nm K X).map Prod.snd)) := by
    have := h7.repr
    simpa [closedOf, encX, encList_bind, List.map_map, Function.comp_def] using this
  step with closed_ones_spec hnm (closedOf nm K X) s7 sol closed h7.inv rl rc
    (by unfold Room; omega) as ⟨xs1, s8, hI8, hx8, ht8, rxs⟩
  refine ⟨hI8, hx07.trans hx8, by simp only [pruneCost]; omega, ?_, ?_⟩
  · have e : ((closedOf nm K X).filter fun q => decide (q.2.vars = [])).map Prod.fst =
        (Sorts.pruneX K X).map (encEqs nm) := by
      simp only [closedOf, Sorts.pruneX, List.filter_map, List.map_map]
      congr 1
      refine List.filter_congr fun E' _ => ?_
      simp only [Function.comp_apply]
      refine decide_eq_decide.2 ?_
      rw [bind_vars_nil, vars_encEqs]
      constructor
      · intro h v hv
        have := h v hv
        by_contra hK
        simp [markSub, hK, Term.vars] at this
      · intro h v hv
        simp [markSub, h v hv, Term.vars]
    rw [e] at rxs
    exact rxs
  · have e : (L.filter fun e => (if e.1 ∈ K then some (Term.sym (nm none) : Pat) else none).isSome) =
        L.filter fun e => decide (e.1 ∈ K) := by
      refine List.filter_congr fun e _ => ?_
      by_cases h : e.1 ∈ K <;> simp [h]
    rw [e] at res1
    exact (((hx56.trans h7.ext).trans hx8).repr res1)

end RwLogVerified
