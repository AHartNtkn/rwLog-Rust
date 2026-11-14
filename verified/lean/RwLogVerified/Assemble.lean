/-
# The exclusions of a normal store, on the store

A solved exclusion is the list of the values it gives the variables of the
store. `sorts::covers` tests whether one is an instance of another
(`coversV`, which is `Sorts.covers` on value lists), `sorts::norm_exs` is
`Sorts.normExs`, and `sorts::antichain` is `Sorts.antichain` with that test.
-/
import RwLogVerified.Solved
import RwLog.Sorts.Hidden

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## One exclusion an instance of another -/

/-- The value list `A` is the value list `B` with each variable replaced by
its value in `A`. -/
def coversV (A B : List Pat) : Bool :=
  decide (B.map (Term.bind fun w => A.getD w (.var w)) = A)

/-- Table `B` holds, for each variable `M` has a value for, a node of that
value, and nothing else. -/
structure TblVal (nm : Option Nat → RwLog.Sym) (nodes : List store.Node) (B : Nat → Option Nat)
    (M : Nat → Option Pat) : Prop where
  sound : ∀ q u, B q = some u → ∃ w p, VarAt nodes q w ∧ M w = some p ∧ Repr nm nodes u p
  complete : ∀ w p, M w = some p → ∃ q u, VarAt nodes q w ∧ B q = some u

theorem TblVal.set {nodes : List store.Node} {B : Nat → Option Nat} {M : Nat → Option Pat}
    (h : TblVal nm nodes B M) (hN : NodesOK nodes) {q u w : Nat} {p : Pat}
    (hq : VarAt nodes q w) (hu : Repr nm nodes u p) :
    TblVal nm nodes (Function.update B q (some u)) (Function.update M w (some p)) := by
  constructor
  · intro q' u' hB
    by_cases e : q' = q
    · subst e
      rw [Function.update_self] at hB
      cases hB
      exact ⟨w, p, hq, by rw [Function.update_self], hu⟩
    · rw [Function.update_of_ne e] at hB
      obtain ⟨w', p', h1, h2, h3⟩ := h.sound q' u' hB
      refine ⟨w', p', h1, ?_, h3⟩
      rw [Function.update_of_ne]
      · exact h2
      · rintro rfl
        exact e (h1.inj hN hq)
  · intro w' p' hM'
    by_cases e : w' = w
    · subst e
      exact ⟨q, u, hq, by rw [Function.update_self]⟩
    · rw [Function.update_of_ne e] at hM'
      obtain ⟨q', u', h1, h2⟩ := h.complete w' p' hM'
      refine ⟨q', u', h1, ?_⟩
      rw [Function.update_of_ne]
      · exact h2
      · rintro rfl
        exact e (h1.unique hq)

/-- The table is the substitution of its values. -/
theorem TblVal.leaf {nodes : List store.Node} {B : Nat → Option Nat} {M : Nat → Option Pat}
    (h : TblVal nm nodes B M) :
    LeafOK nm nodes B term.Leaf.Map fun w => (M w).getD (.var w) := by
  refine ⟨fun q u hq => ?_, fun v hv => ?_⟩
  · obtain ⟨w, p, h1, h2, h3⟩ := h.sound q u hq
    refine ⟨w, h1, ?_⟩
    show Repr nm nodes u ((M w).getD (.var w))
    rw [h2]
    exact h3
  · cases hM : M v with
    | none =>
      show (M v).getD (.var v) = .var v
      rw [hM]
      rfl
    | some p =>
      obtain ⟨q, u, h1, h2⟩ := h.complete v p hM
      rw [hv q h1] at h2
      cases h2

/-- The values the bindings of a list give, over what there was. -/
def putAll (L : List (Nat × Pat)) (M : Nat → Option Pat) : Nat → Option Pat :=
  L.foldl (fun M b => Function.update M b.1 (some b.2)) M

theorem putAll_zip : ∀ A : List Pat,
    putAll ((List.range A.length).zip A) (fun _ => none) = fun w => A[w]? := by
  intro A
  induction A using List.reverseRecOn with
  | nil => rfl
  | append_singleton A p ih =>
    have e : (List.range (A ++ [p]).length).zip (A ++ [p]) =
        (List.range A.length).zip A ++ [(A.length, p)] := by
      rw [List.length_append, List.length_singleton, List.range_succ,
        List.zip_append (by simp)]
      rfl
    rw [e]
    unfold putAll at ih ⊢
    rw [List.foldl_append, ih]
    funext w
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hw : w = A.length
    · subst hw
      simp
    · rw [Function.update_of_ne hw]
      by_cases hlt : w < A.length
      · simp [List.getElem?_append_left hlt]
      · have h1 : A[w]? = none := by simp; omega
        have h2 : (A ++ [p])[w]? = none := by simp; omega
        rw [h1, h2]

theorem covers_loop_spec :
    ∀ (L : List (Nat × Pat)) (s : store.Store) (vs l : store.TermId) (M : Nat → Option Pat),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) (L.map fun b => Term.var b.1)) →
    Repr nm s.nodes.val l.val (encList (nm none) (L.map fun b => b.2)) →
    TblVal nm s.nodes.val (tbl s .B) M → Room s (3 * L.length + 1) →
    sorts.covers_loop s vs l true ⦃ s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s.ticks.val ≤ s'.ticks.val ∧
        s'.ticks.val ≤ s.ticks.val + 3 * L.length + 1 ∧
        TblVal nm s'.nodes.val (tbl s' .B) (putAll L M) ⦄ := by
  intro L
  induction L with
  | nil =>
    intro s vs l M hI hvs hl hT hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.covers_loop
    rw [loop]
    simp only [sorts.covers_loop.body, ↓reduceIte]
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
    refine ⟨K1.inv, K1.nodes, by omega, by simp only [List.length_nil]; omega, ?_⟩
    rw [K1.nodes, K1.tbl]
    exact hT
  | cons b L ih =>
    intro s vs l M hI hvs hl hT hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.covers_loop
    rw [loop]
    simp only [sorts.covers_loop.body, ↓reduceIte]
    step with uncons_repr s vs hI.toWf
      (p := Term.app (Term.var b.1) (encList (nm none) (L.map fun b => Term.var b.1))) hvs
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨vi, vrest, rfl, rv, rvrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with uncons_repr s1 l K1.inv.toWf
      (p := Term.app b.2 (encList (nm none) (L.map fun b => b.2))) (by rw [K1.nodes]; exact hl)
      (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1'
    obtain ⟨pi, lrest, rfl, rp, rlrest⟩ := hu1
    rw [K1.nodes] at rp rlrest
    have K2 := hK1'.kept K1.inv
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    have hB2 : tbl s2 .B = tbl s .B := by rw [K2.tbl, K1.tbl]
    have hvv : VarAt s.nodes.val vi.val b.1 := by
      cases rv with
      | var h => exact h
    simp only [uncurry]
    step with set_spec s2 .B vi pi K2.inv (by rw [hn2]; exact hvv.lt)
      (by unfold Room; omega) as ⟨s3, g1, g2, g3, g4, g5⟩
    have hn3 : s3.nodes.val = s.nodes.val := by rw [g1, hn2]
    rw [hB2] at g4
    have IH := ih s3 vrest lrest (Function.update M b.1 (some b.2)) g3
      (by rw [hn3]; exact rvrest) (by rw [hn3]; exact rlrest)
      (by rw [hn3, g4]; exact hT.set hI.nodesOK hvv rp) (by unfold Room; omega)
    unfold sorts.covers_loop at IH
    refine WP.spec_mono IH ?_
    rintro s' ⟨hI', hn', hlo', ht', hT'⟩
    exact ⟨hI', by rw [hn', hn3], by omega, by simp only [List.length_cons]; omega, hT'⟩

/-- The ticks `covers` may take on `k` variables and the list `T` of the
values of the second exclusion. -/
def coversCost (k : Nat) (T : Pat) : Nat := 3 * k + 14 * T.subs.card + 9

/-- `covers` tests whether the first value list is an instance of the
second. -/
theorem covers_spec (hnm : Function.Injective nm) (A B : List Pat) (s : store.Store)
    (vs a b : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo A.length)))
    (ha : Repr nm s.nodes.val a.val (encList (nm none) A))
    (hb : Repr nm s.nodes.val b.val (encList (nm none) B))
    (hroom : Room s (coversCost A.length (encList (nm none) B))) :
    sorts.covers s vs a b ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + coversCost A.length (encList (nm none) B) ∧
        r = coversV A B ⦄ := by
  unfold sorts.covers
  have hroom' := hroom
  unfold Room at hroom'
  simp only [coversCost] at hroom'
  step with clear_spec s .B hI (by unfold Room; omega) as ⟨s1, c1, c2, c3, c4, c5⟩
  have hlen : (List.range A.length).length ≤ A.length := by simp
  have e1 : ((List.range A.length).zip A).map (fun b => (Term.var b.1 : Pat)) =
      varsTo A.length := by
    have : ((List.range A.length).zip A).map (fun b => (Term.var b.1 : Pat)) =
        (((List.range A.length).zip A).map Prod.fst).map Term.var := by
      rw [List.map_map]
      rfl
    rw [this, List.map_fst_zip hlen]
    rfl
  have e2 : ((List.range A.length).zip A).map (fun b => b.2) = A :=
    List.map_snd_zip (by simp)
  step with covers_loop_spec (nm := nm) ((List.range A.length).zip A) s1 vs a
    (fun _ => none) c3 (by rw [c1, e1]; exact hvs) (by rw [c1, e2]; exact ha)
    ⟨fun q u h => (by rw [c4] at h; cases h), fun w v h => (by cases h)⟩
    (by simp only [List.length_zip, List.length_range, Nat.min_self]; unfold Room; omega)
    as ⟨s2, hI2, hn2, hlo2, ht2, hT2⟩
  simp only [List.length_zip, List.length_range, Nat.min_self] at ht2
  rw [putAll_zip] at hT2
  step with clear_spec s2 .A hI2 (by unfold Room; omega) as ⟨s3, d1, d2, d3, d4, d5⟩
  have hn3 : s3.nodes.val = s.nodes.val := by rw [d1, hn2, c1]
  have hleaf : LeafOK nm s3.nodes.val (tbl s3 .B) term.Leaf.Map
      (fun w => (A[w]?).getD (.var w)) := by
    rw [d1, d5 .B (by simp)]
    exact hT2.leaf
  have hpc := pending_card_le (nm := nm) s3.nodes.val (tbl s3 .A) (encList (nm none) B).subs
  step with rebuild_spec hnm s3 .Map b (t := encList (nm none) B)
    (σ := fun w => (A[w]?).getD (.var w)) (encList (nm none) B).subs d3
    (by rw [hn3]; exact hb) hleaf (by intro q v hq; rw [d4] at hq; cases hq)
    (Finset.Subset.refl _) (by unfold Room; omega) as ⟨r, s4, h4⟩
  have hc4 := h4.cost
  have hx4 : Extends s s4 := (Extends.of_eq hn3 (by omega)).trans h4.ext
  have hr4 := h4.repr
  rw [encList_bind] at hr4
  have ha4 := hx4.repr ha
  refine WP.spec_mono (same_spec s4 r a h4.inv (by unfold Room; omega)) ?_
  rintro ⟨res, s5⟩ ⟨hres, hK⟩
  have ht5 := hK.ticks
  refine ⟨hK.inv, hx4.trans (Extends.of_eq hK.nodes (by omega)),
    by simp only [coversCost]; omega, ?_⟩
  rw [hres]
  unfold coversV
  have eσ : (fun w => A.getD w (.var w)) = fun w => (A[w]?).getD (Term.var w : Pat) := by
    funext w
    rw [List.getD_eq_getElem?_getD]
  rw [eσ]
  refine decide_eq_decide.2 ⟨fun e => ?_, fun e => ?_⟩
  · rw [e] at hr4
    exact encList_inj _ (hr4.unique ha4)
  · rw [e] at hr4
    exact Repr.inj hnm h4.inv.nodesOK hr4 ha4

/-! ## Lists of exclusions -/

/-- A list of value lists as a term. -/
abbrev encLL (nm : Option Nat → RwLog.Sym) (Ls : List (List Pat)) : Pat :=
  encList (nm none) (Ls.map (encList (nm none)))

/-- The values an exclusion gives the variables below `k`. -/
def vals (k : Nat) (θ : Sorts.Binds) : List Pat := (List.range k).map (PSubst.apply θ)

theorem repCost_mono (c : Nat) {n n' : Nat} (h : n ≤ n') : repCost c n ≤ repCost c n' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => simp only [repCost]; omega

/-- The ticks `norm_exs` may take in its loop. -/
noncomputable def exsCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (rc : Nat)
    (r : Sorts.Raw) : List (Eqns Nat) → Nat
  | [] => 1
  | E :: X => normExCost nm S U rc r E + 2 + exsCost nm S U rc r X

theorem norm_exs_loop_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) {rc : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc) (r : Sorts.Raw)
    (hcN : ∀ v, ∀ n ∈ r.conj v, n ∈ Sorts.names S) (decls names vs cs : store.TermId) :
    ∀ (X : List (Eqns Nat)) (s : store.Store) (x out : store.TermId) (O : List (List Pat)),
    (∀ E ∈ X, E.FO) → (∀ E ∈ X, ∀ v ∈ E.vars, v < r.c.length) →
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val vs.val (encList (nm none) (varsTo r.c.length)) →
    Repr nm s.nodes.val cs.val (encList (nm none) (r.c.map (cpat (nm none) U))) →
    Repr nm s.nodes.val x.val (encList (nm none) (X.map (encEqs nm))) →
    Repr nm s.nodes.val out.val (encLL nm O) → Room s (exsCost nm S U rc r X) →
    sorts.norm_exs_loop x s decls names vs cs out ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + exsCost nm S U rc r X ∧
        Repr nm s'.nodes.val out'.val
          (encLL nm (((Sorts.normExs S r X).map (vals r.c.length)).reverse ++ O)) ⦄ := by
  intro X
  induction X with
  | nil =>
    intro s x out O hfo hv hI hd hU hvs hcs hx hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [exsCost] at hroom'
    unfold sorts.norm_exs_loop
    rw [loop]
    simp only [sorts.norm_exs_loop.body]
    step with uncons_repr s x hI.toWf (p := Term.sym (nm none)) hx (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧ s1.ticks.val ≤ s.ticks.val + exsCost nm S U rc r [] ∧
        Repr nm s1.nodes.val out.val
          (encLL nm (((Sorts.normExs S r []).map (vals r.c.length)).reverse ++ O)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [exsCost]; omega,
        by rw [K1.nodes]; exact hout⟩
    step*
  | cons E X ih =>
    intro s x out O hfo hv hI hd hU hvs hcs hx hout hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [exsCost] at hroom'
    unfold sorts.norm_exs_loop
    rw [loop]
    simp only [sorts.norm_exs_loop.body]
    step with uncons_repr s x hI.toWf
      (p := Term.app (encEqs nm E) (encList (nm none) (X.map (encEqs nm)))) hx
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ei, rest, rfl, re, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with norm_ex_spec hnm hC hr r hcN E (hfo E List.mem_cons_self)
      (hv E List.mem_cons_self) s1 decls names vs cs ei K1.inv (hx1.repr hd) (hx1.repr hU)
      (hx1.repr hvs) (hx1.repr hcs) (hx1.repr re) (by unfold Room; omega)
      as ⟨r1, hI2, hx2, ht2, hres⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hI2 hx2 ht2 hres
    have hx02 := hx1.trans hx2
    cases o1 with
    | none =>
      simp only at hres
      simp only [uncurry, bind_ok]
      have IH := ih s2 rest out O (fun E' h => hfo E' (List.mem_cons_of_mem _ h))
        (fun E' h => hv E' (List.mem_cons_of_mem _ h)) hI2 (hx02.repr hd) (hx02.repr hU)
        (hx02.repr hvs) (hx02.repr hcs) (hx02.repr rrest) (hx02.repr hout)
        (by unfold Room; omega)
      unfold sorts.norm_exs_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx02.trans hx', by simp only [exsCost]; omega, ?_⟩
      have e : Sorts.normExs S r (E :: X) = Sorts.normExs S r X := by
        simp only [Sorts.normExs, List.filterMap_cons, hres]
      rw [e]
      exact hr'
    | some res =>
      simp only at hres
      obtain ⟨θ, hn, hrv⟩ := hres
      simp only [uncurry]
      step with alloc_spec s2 (.App res out) hI2 ⟨hrv.lt, (hx02.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx02.trans hx4
      have hout1 : Repr nm s4.nodes.val out1.val (encLL nm (vals r.c.length θ :: O)) :=
        .app hr4 (hx4.repr hrv) (hx04.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s4 rest out1 (vals r.c.length θ :: O)
        (fun E' h => hfo E' (List.mem_cons_of_mem _ h))
        (fun E' h => hv E' (List.mem_cons_of_mem _ h)) hI4 (hx04.repr hd) (hx04.repr hU)
        (hx04.repr hvs) (hx04.repr hcs) (hx04.repr rrest) hout1 (by unfold Room; omega)
      unfold sorts.norm_exs_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx04.trans hx', by simp only [exsCost]; omega, ?_⟩
      have e : Sorts.normExs S r (E :: X) = θ :: Sorts.normExs S r X := by
        simp only [Sorts.normExs, List.filterMap_cons, hn]
      rw [e]
      simpa using hr'

/-- The ticks `norm_exs` may take. -/
noncomputable def normExsCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name)
    (rc : Nat) (r : Sorts.Raw) (X : List (Eqns Nat)) : Nat :=
  exsCost nm S U rc r X + 2 * X.length + 3

/-- `norm_exs` gives the normal forms of the exclusions that have one
(`Sorts.normExs`), each as the list of its values. -/
theorem norm_exs_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) {rc : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc) (r : Sorts.Raw)
    (hcN : ∀ v, ∀ n ∈ r.conj v, n ∈ Sorts.names S) (X : List (Eqns Nat)) (hfo : ∀ E ∈ X, E.FO)
    (hv : ∀ E ∈ X, ∀ v ∈ E.vars, v < r.c.length) (s : store.Store)
    (decls names vs cs x : store.TermId) (hI : Inv s) (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo r.c.length)))
    (hcs : Repr nm s.nodes.val cs.val (encList (nm none) (r.c.map (cpat (nm none) U))))
    (hx : Repr nm s.nodes.val x.val (encList (nm none) (X.map (encEqs nm))))
    (hroom : Room s (normExsCost nm S U rc r X)) :
    sorts.norm_exs s decls names vs cs x ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + normExsCost nm S U rc r X ∧
        Repr nm s'.nodes.val res.val (encLL nm ((Sorts.normExs S r X).map (vals r.c.length))) ⦄ := by
  unfold sorts.norm_exs
  have hroom' := hroom
  unfold Room at hroom'
  simp only [normExsCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with norm_exs_loop_spec hnm hC hr r hcN decls names vs cs X s1 x out [] hfo hv hI1
    (hx1.repr hd) (hx1.repr hU) (hx1.repr hvs) (hx1.repr hcs) (hx1.repr hx) (.nil hr1)
    (by unfold Room; omega) as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  have hlen : (Sorts.normExs S r X).length ≤ X.length := List.length_filterMap_le _ _
  refine WP.spec_mono (rev_spec (nm := nm)
    ((((Sorts.normExs S r X).map (vals r.c.length)).reverse ++ []).map (encList (nm none)))
    s2 out1 hI2.toWf hr2 (by simp only [List.length_map, List.length_append,
      List.length_reverse, List.length_nil]; unfold Room; omega)) ?_
  rintro ⟨res, s3⟩ ⟨hR, hr3⟩
  have ht3 := hR.ticks
  simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil] at ht3
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext,
    by simp only [normExsCost]; omega, ?_⟩
  unfold encLL
  simpa [List.map_reverse, List.map_map] using hr3

/-! ## Dropping the exclusions another covers -/

/-- The ticks `covers` may take on `k` variables when the value list of the
second exclusion has at most `m` subterms. -/
def coversCostU (k m : Nat) : Nat := 3 * k + 14 * m + 9

theorem any_covers_loop_spec (hnm : Function.Injective nm) (A : List Pat) (m : Nat)
    (vs a : store.TermId) :
    ∀ (Ls : List (List Pat)) (s : store.Store) (l : store.TermId),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) (varsTo A.length)) →
    Repr nm s.nodes.val a.val (encList (nm none) A) →
    Repr nm s.nodes.val l.val (encLL nm Ls) →
    (∀ B ∈ Ls, (encList (nm none) B).subs.card ≤ m) →
    Room s (repCost (coversCostU A.length m + 1) Ls.length) →
    sorts.any_covers_loop s vs a false l true ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + repCost (coversCostU A.length m + 1) Ls.length ∧
        r = Ls.any (coversV A) ⦄ := by
  intro Ls
  induction Ls with
  | nil =>
    intro s l hI hvs ha hl hm hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, repCost] at hroom'
    unfold sorts.any_covers_loop
    rw [loop]
    simp only [sorts.any_covers_loop.body, ↓reduceIte]
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
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega),
      by simp only [List.length_nil, repCost]; omega, rfl⟩
  | cons B Ls ih =>
    intro s l hI hvs ha hl hm hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, repCost] at hroom'
    have hBm := hm B List.mem_cons_self
    have hcc : coversCost A.length (encList (nm none) B) ≤ coversCostU A.length m := by
      simp only [coversCost, coversCostU]; omega
    unfold sorts.any_covers_loop
    rw [loop]
    simp only [sorts.any_covers_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf
      (p := Term.app (encList (nm none) B) (encLL nm Ls)) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨bi, rest, rfl, rb, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with covers_spec hnm A B s1 vs a bi K1.inv (hx1.repr hvs) (hx1.repr ha) (hx1.repr rb)
      (by unfold Room; omega) as ⟨r1, hI2, hx2, ht2, hres⟩
    obtain ⟨b1, s2⟩ := r1
    simp only at hI2 hx2 ht2 hres
    have hx02 := hx1.trans hx2
    cases b1 with
    | true =>
      simp only [↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hI2, hx02, by simp only [List.length_cons, repCost]; omega, ?_⟩
      simp [List.any_cons, ← hres]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 rest hI2 (hx02.repr hvs) (hx02.repr ha) (hx02.repr rrest)
        (fun B' h => hm B' (List.mem_cons_of_mem _ h)) (by unfold Room; omega)
      unfold sorts.any_covers_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨r', s'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx02.trans hx', by simp only [List.length_cons, repCost]; omega, ?_⟩
      simp [List.any_cons, ← hres, hr']

theorem drop_covered_loop_spec (hnm : Function.Injective nm) (A : List Pat) (k m : Nat)
    (vs a : store.TermId) :
    ∀ (Ls : List (List Pat)) (s : store.Store) (l out : store.TermId) (O : List (List Pat)),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) (varsTo k)) →
    Repr nm s.nodes.val a.val (encList (nm none) A) →
    Repr nm s.nodes.val l.val (encLL nm Ls) → Repr nm s.nodes.val out.val (encLL nm O) →
    (∀ B ∈ Ls, B.length = k) → (encList (nm none) A).subs.card ≤ m →
    Room s (repCost (coversCostU k m + 2) Ls.length) →
    sorts.drop_covered_loop l s vs a out ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + repCost (coversCostU k m + 2) Ls.length ∧
        Repr nm s'.nodes.val out'.val
          (encLL nm ((Ls.filter fun B => !coversV B A).reverse ++ O)) ⦄ := by
  intro Ls
  induction Ls with
  | nil =>
    intro s l out O hI hvs ha hl hout hk hAm hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, repCost] at hroom'
    unfold sorts.drop_covered_loop
    rw [loop]
    simp only [sorts.drop_covered_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + repCost (coversCostU k m + 2) ([] : List (List Pat)).length ∧
        Repr nm s1.nodes.val out.val
          (encLL nm ((([] : List (List Pat)).filter fun B => !coversV B A).reverse ++ O)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil, repCost]; omega,
        by rw [K1.nodes]; exact hout⟩
    step*
  | cons B Ls ih =>
    intro s l out O hI hvs ha hl hout hk hAm hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, repCost] at hroom'
    have hBk := hk B List.mem_cons_self
    have hcc : coversCost B.length (encList (nm none) A) ≤ coversCostU k m := by
      simp only [coversCost, coversCostU, hBk]; omega
    unfold sorts.drop_covered_loop
    rw [loop]
    simp only [sorts.drop_covered_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (encList (nm none) B) (encLL nm Ls)) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨bi, rest, rfl, rb, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with covers_spec hnm B A s1 vs bi a K1.inv (by rw [hBk]; exact hx1.repr hvs)
      (hx1.repr rb) (hx1.repr ha) (by unfold Room; omega) as ⟨r1, hI2, hx2, ht2, hres⟩
    obtain ⟨b1, s2⟩ := r1
    simp only at hI2 hx2 ht2 hres
    have hx02 := hx1.trans hx2
    cases b1 with
    | true =>
      simp only [↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 rest out O hI2 (hx02.repr hvs) (hx02.repr ha) (hx02.repr rrest)
        (hx02.repr hout) (fun B' h => hk B' (List.mem_cons_of_mem _ h)) hAm
        (by unfold Room; omega)
      unfold sorts.drop_covered_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx02.trans hx', by simp only [List.length_cons, repCost]; omega, ?_⟩
      have e : ((B :: Ls).filter fun B => !coversV B A) = Ls.filter fun B => !coversV B A := by
        simp [← hres]
      rw [e]
      exact hr'
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry]
      step with alloc_spec s2 (.App bi out) hI2 ⟨(hx02.repr rb).lt, (hx02.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx02.trans hx4
      have hout1 : Repr nm s4.nodes.val out1.val (encLL nm (B :: O)) :=
        .app hr4 (hx04.repr rb) (hx04.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s4 rest out1 (B :: O) hI4 (hx04.repr hvs) (hx04.repr ha) (hx04.repr rrest)
        hout1 (fun B' h => hk B' (List.mem_cons_of_mem _ h)) hAm (by unfold Room; omega)
      unfold sorts.drop_covered_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx04.trans hx', by simp only [List.length_cons, repCost]; omega, ?_⟩
      have e : ((B :: Ls).filter fun B => !coversV B A) =
          B :: Ls.filter fun B => !coversV B A := by
        simp [← hres]
      rw [e]
      simpa using hr'

/-- The ticks `drop_covered` may take on a list of `n` exclusions. -/
def dropCost (k m n : Nat) : Nat := repCost (coversCostU k m + 2) n + 2 * n + 3

/-- `drop_covered` gives the members that are not instances of `A`. -/
theorem drop_covered_spec (hnm : Function.Injective nm) (A : List Pat) (k m : Nat)
    (Ls : List (List Pat)) (s : store.Store) (vs a l : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo k)))
    (ha : Repr nm s.nodes.val a.val (encList (nm none) A))
    (hl : Repr nm s.nodes.val l.val (encLL nm Ls)) (hk : ∀ B ∈ Ls, B.length = k)
    (hAm : (encList (nm none) A).subs.card ≤ m) (hroom : Room s (dropCost k m Ls.length)) :
    sorts.drop_covered s vs a l ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + dropCost k m Ls.length ∧
        Repr nm s'.nodes.val res.val (encLL nm (Ls.filter fun B => !coversV B A)) ⦄ := by
  unfold sorts.drop_covered
  have hroom' := hroom
  unfold Room at hroom'
  simp only [dropCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with drop_covered_loop_spec hnm A k m vs a Ls s1 l out [] hI1 (hx1.repr hvs)
    (hx1.repr ha) (hx1.repr hl) (.nil hr1) hk hAm (by unfold Room; omega)
    as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  have hlen : (Ls.filter fun B => !coversV B A).length ≤ Ls.length := List.length_filter_le _ _
  refine WP.spec_mono (rev_spec (nm := nm)
    (((Ls.filter fun B => !coversV B A).reverse ++ []).map (encList (nm none)))
    s2 out1 hI2.toWf hr2 (by simp only [List.length_map, List.length_append,
      List.length_reverse, List.length_nil]; unfold Room; omega)) ?_
  rintro ⟨res, s3⟩ ⟨hR, hr3⟩
  have ht3 := hR.ticks
  simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil] at ht3
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext,
    by simp only [dropCost]; omega, ?_⟩
  simpa [List.map_reverse] using hr3

/-- One round of `antichain`: the exclusion `A` put before the ones kept so
far, unless one of them covers it; the ones it covers are dropped. -/
def acStep (Acc : List (List Pat)) (A : List Pat) : List (List Pat) :=
  if Acc.any (coversV A) then Acc else A :: Acc.filter fun B => !coversV B A

theorem antichain_fold : ∀ Ls : List (List Pat),
    Ls.reverse.foldl acStep [] = Sorts.antichain coversV Ls
  | [] => rfl
  | A :: Ls => by
    rw [List.reverse_cons, List.foldl_append, antichain_fold Ls]
    simp only [List.foldl_cons, List.foldl_nil, acStep, Sorts.antichain]

theorem acStep_length (Acc : List (List Pat)) (A : List Pat) :
    (acStep Acc A).length ≤ Acc.length + 1 := by
  unfold acStep
  split
  · omega
  · have := List.length_filter_le (fun B => !coversV B A) Acc
    simp only [List.length_cons]; omega

theorem mem_acStep {Acc : List (List Pat)} {A B : List Pat} (h : B ∈ acStep Acc A) :
    B = A ∨ B ∈ Acc := by
  unfold acStep at h
  split at h
  · exact Or.inr h
  · rcases List.mem_cons.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.1 h).1

/-- The ticks of one round of `antichain` among `n` exclusions. -/
def antiRound (k m n : Nat) : Nat := repCost (coversCostU k m + 1) n + dropCost k m n + 2

theorem dropCost_mono (k m : Nat) {n n' : Nat} (h : n ≤ n') : dropCost k m n ≤ dropCost k m n' := by
  have := repCost_mono (coversCostU k m + 2) h
  simp only [dropCost]; omega

theorem antichain_loop_spec (hnm : Function.Injective nm) (k m N : Nat) (vs : store.TermId) :
    ∀ (Ls : List (List Pat)) (s : store.Store) (l acc : store.TermId) (Acc : List (List Pat)),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) (varsTo k)) →
    Repr nm s.nodes.val l.val (encLL nm Ls) → Repr nm s.nodes.val acc.val (encLL nm Acc) →
    (∀ B ∈ Ls, B.length = k ∧ (encList (nm none) B).subs.card ≤ m) →
    (∀ B ∈ Acc, B.length = k ∧ (encList (nm none) B).subs.card ≤ m) →
    Acc.length + Ls.length ≤ N → Room s (repCost (antiRound k m N) Ls.length) →
    sorts.antichain_loop l s vs acc ⦃ acc' s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + repCost (antiRound k m N) Ls.length ∧
        Repr nm s'.nodes.val acc'.val (encLL nm (Ls.foldl acStep Acc)) ⦄ := by
  intro Ls
  induction Ls with
  | nil =>
    intro s l acc Acc hI hvs hl hacc hL hA hN hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, repCost] at hroom'
    unfold sorts.antichain_loop
    rw [loop]
    simp only [sorts.antichain_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + repCost (antiRound k m N) ([] : List (List Pat)).length ∧
        Repr nm s1.nodes.val acc.val (encLL nm (([] : List (List Pat)).foldl acStep Acc)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil, repCost]; omega,
        by rw [K1.nodes]; exact hacc⟩
    step*
  | cons A Ls ih =>
    intro s l acc Acc hI hvs hl hacc hL hA hN hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, repCost] at hroom'
    simp only [List.length_cons] at hN
    obtain ⟨hAk, hAm⟩ := hL A List.mem_cons_self
    have hR1 : antiRound k m N = repCost (coversCostU k m + 1) N + dropCost k m N + 2 := rfl
    have hc1 : repCost (coversCostU k m + 1) Acc.length ≤ repCost (coversCostU k m + 1) N :=
      repCost_mono _ (by omega)
    have hc2 : dropCost k m Acc.length ≤ dropCost k m N := dropCost_mono k m (by omega)
    unfold sorts.antichain_loop
    rw [loop]
    simp only [sorts.antichain_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (encList (nm none) A) (encLL nm Ls)) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ai, rest, rfl, ra, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with any_covers_loop_spec hnm A m vs ai Acc s1 acc K1.inv
      (by rw [hAk]; exact hx1.repr hvs) (hx1.repr ra) (hx1.repr hacc) (fun B h => (hA B h).2)
      (by rw [hAk]; unfold Room; omega) as ⟨r1, hI2, hx2, ht2, hres⟩
    obtain ⟨b1, s2⟩ := r1
    simp only at hI2 hx2 ht2 hres
    rw [hAk] at ht2
    have hx02 := hx1.trans hx2
    cases b1 with
    | true =>
      simp only [↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 rest acc Acc hI2 (hx02.repr hvs) (hx02.repr rrest) (hx02.repr hacc)
        (fun B h => hL B (List.mem_cons_of_mem _ h)) hA (by omega) (by unfold Room; omega)
      unfold sorts.antichain_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨acc', s'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx02.trans hx', by simp only [List.length_cons, repCost]; omega, ?_⟩
      have e : acStep Acc A = Acc := by simp only [acStep, ← hres, ↓reduceIte]
      rw [List.foldl_cons, e]
      exact hr'
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry]
      step with drop_covered_spec hnm A k m Acc s2 vs ai acc hI2 (hx02.repr hvs) (hx02.repr ra)
        (hx02.repr hacc) (fun B h => (hA B h).1) hAm (by unfold Room; omega)
        as ⟨r3, hI3, hx3, ht3, hr3⟩
      obtain ⟨kept, s3⟩ := r3
      simp only at hI3 hx3 ht3 hr3
      have hx03 := hx02.trans hx3
      step with alloc_spec s3 (.App ai kept) hI3 ⟨(hx03.repr ra).lt, hr3.lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨acc1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx03.trans hx4
      have e : acStep Acc A = A :: Acc.filter fun B => !coversV B A := by
        simp only [acStep, ← hres, Bool.false_eq_true, ↓reduceIte]
      have hacc1 : Repr nm s4.nodes.val acc1.val (encLL nm (acStep Acc A)) := by
        rw [e]
        exact .app hr4 (hx04.repr ra) (hx4.repr hr3)
      have hlen := acStep_length Acc A
      simp only [uncurry, bind_ok]
      have IH := ih s4 rest acc1 (acStep Acc A) hI4 (hx04.repr hvs) (hx04.repr rrest) hacc1
        (fun B h => hL B (List.mem_cons_of_mem _ h))
        (fun B h => by
          rcases mem_acStep h with rfl | h
          · exact ⟨hAk, hAm⟩
          · exact hA B h)
        (by omega) (by unfold Room; omega)
      unfold sorts.antichain_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨acc', s'⟩ ⟨hI', hx', ht', hr'⟩
      exact ⟨hI', hx04.trans hx', by simp only [List.length_cons, repCost]; omega, hr'⟩

/-- The ticks `antichain` may take on `n` exclusions. -/
def antiCost (k m n : Nat) : Nat := repCost (antiRound k m n) n + 2 * n + 3

/-- `antichain` gives the exclusions that are instances of no other, one of
each (`Sorts.antichain`). -/
theorem antichain_spec (hnm : Function.Injective nm) (k m : Nat) (Ls : List (List Pat))
    (s : store.Store) (vs l : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo k)))
    (hl : Repr nm s.nodes.val l.val (encLL nm Ls))
    (hL : ∀ B ∈ Ls, B.length = k ∧ (encList (nm none) B).subs.card ≤ m)
    (hroom : Room s (antiCost k m Ls.length)) :
    sorts.antichain s vs l ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + antiCost k m Ls.length ∧
        Repr nm s'.nodes.val res.val (encLL nm (Sorts.antichain coversV Ls)) ⦄ := by
  unfold sorts.antichain
  have hroom' := hroom
  unfold Room at hroom'
  simp only [antiCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨acc, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with rev_spec (nm := nm) (Ls.map (encList (nm none))) s1 l hI1.toWf (hx1.repr hl)
    (by simp only [List.length_map]; unfold Room; omega) as ⟨l1, s2, hR, hr2⟩
  have ht2 := hR.ticks
  simp only [List.length_map] at ht2
  have hI2 : Inv s2 := ⟨hR.wf, by rw [hR.stk]; exact hI1.empty⟩
  have hx02 := hx1.trans hR.ext
  rw [← List.map_reverse] at hr2
  have IH := antichain_loop_spec hnm k m Ls.length vs Ls.reverse s2 l1 acc [] hI2
    (hx02.repr hvs) hr2 (hR.ext.repr (.nil hr1)) (fun B h => hL B (List.mem_reverse.1 h))
    (fun B h => by cases h) (by simp) (by simp only [List.length_reverse]; unfold Room; omega)
  refine WP.spec_mono IH ?_
  rintro ⟨res, s3⟩ ⟨hI3, hx3, ht3, hr3⟩
  simp only [List.length_reverse] at ht3
  refine ⟨hI3, hx02.trans hx3, by simp only [antiCost]; omega, ?_⟩
  rw [antichain_fold] at hr3
  exact hr3

/-! ## Terms closed by a substitution -/

theorem mem_vars_encList (z : RwLog.Sym) {v : Nat} :
    ∀ {L : List Pat}, v ∈ (encList z L).vars ↔ ∃ p ∈ L, v ∈ p.vars
  | [] => by simp [encList, Term.vars]
  | p :: L => by simp [encList, Term.vars, mem_vars_encList z (L := L)]

theorem bind_vars_nil {σ : Nat → Pat} {t : Pat} :
    (t.bind σ).vars = [] ↔ ∀ v ∈ t.vars, (σ v).vars = [] := by
  constructor
  · intro h v hv
    rw [List.eq_nil_iff_forall_not_mem]
    intro u hu
    have := Term.vars_sub_bind (σ := σ) hv u hu
    rw [h] at this
    cases this
  · intro h
    rw [List.eq_nil_iff_forall_not_mem]
    intro u hu
    obtain ⟨v, hv, hu'⟩ := Term.vars_bind_mem hu
    rw [h v hv] at hu'
    cases hu'

/-- A substitution that puts a variable or a constant for each variable
makes no new subterm. -/
theorem subs_bind_leaf {σ : Nat → Pat} (hσ : ∀ v, (σ v).subs = {σ v}) (t : Pat) :
    (t.bind σ).subs ⊆ t.subs.image (Term.bind σ) := by
  induction t with
  | var v =>
    intro w hw
    simp only [Term.bind_var, hσ v, Finset.mem_singleton] at hw
    subst hw
    exact Finset.mem_image.2 ⟨.var v, Term.self_mem_subs _, rfl⟩
  | sym f =>
    intro w hw
    simp only [Term.bind_sym, Term.subs, Finset.mem_singleton] at hw
    subst hw
    exact Finset.mem_image.2 ⟨.sym f, Term.self_mem_subs _, rfl⟩
  | app a b iha ihb =>
    intro w hw
    simp only [Term.bind_app, Term.subs, Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hw | hw
    · exact Finset.mem_image.2 ⟨.app a b, Term.self_mem_subs _, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (iha hw)
      exact Finset.mem_image.2 ⟨u, by simp [Term.subs, hu], rfl⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (ihb hw)
      exact Finset.mem_image.2 ⟨u, by simp [Term.subs, hu], rfl⟩

/-! ## The tests on value lists are the tests of the specification -/

@[simp] theorem vals_length (k : Nat) (θ : Sorts.Binds) : (vals k θ).length = k := by
  simp [vals]

theorem getD_vals {k : Nat} {θ : Sorts.Binds} (hθ : ∀ b ∈ θ, b.1 < k) (w : Nat) :
    (vals k θ).getD w (.var w) = PSubst.apply θ w := by
  unfold vals
  rw [Sorts.getD_map_range]
  split
  · rfl
  · rename_i h
    exact (Sorts.apply_of_not_mem fun b hb hbv => h (by rw [← hbv]; exact hθ b hb)).symm

/-- `coversV` on the values of two exclusions is `Sorts.covers`. -/
theorem coversV_vals {k : Nat} {θ θ' : Sorts.Binds} (hθ : ∀ b ∈ θ, b.1 < k) :
    coversV (vals k θ) (vals k θ') = Sorts.covers k θ θ' := by
  have e : (fun w => (vals k θ).getD w (.var w)) = PSubst.apply θ := funext (getD_vals hθ)
  unfold coversV Sorts.covers
  rw [e, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
  unfold vals
  rw [List.map_map, List.map_inj_left]
  constructor
  · intro h x hx
    exact (h x (List.mem_range.2 hx)).symm
  · intro h x hx
    exact (h x (List.mem_range.1 hx)).symm

theorem antichain_subset {α : Type} (le : α → α → Bool) :
    ∀ (L : List α) (a : α), a ∈ Sorts.antichain le L → a ∈ L
  | [], a, h => by simp [Sorts.antichain] at h
  | b :: L, a, h => by
    unfold Sorts.antichain at h
    split at h
    · exact List.mem_cons_of_mem _ (antichain_subset le L a h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (antichain_subset le L a (List.mem_filter.1 h).1)

/-- `Sorts.antichain` goes through a map that keeps the test. -/
theorem antichain_map {α β : Type} (f : α → β) (le : α → α → Bool) (le' : β → β → Bool) :
    ∀ L : List α, (∀ a ∈ L, ∀ b ∈ L, le' (f a) (f b) = le a b) →
      Sorts.antichain le' (L.map f) = (Sorts.antichain le L).map f
  | [], _ => rfl
  | a :: L, hle => by
    have ih := antichain_map f le le' L fun b hb c hc =>
      hle b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc)
    have hsub : ∀ b ∈ Sorts.antichain le L, b ∈ a :: L := fun b hb =>
      List.mem_cons_of_mem _ (antichain_subset le L b hb)
    have hany : ((Sorts.antichain le L).map f).any (le' (f a)) =
        (Sorts.antichain le L).any (le a) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, List.mem_map]
      constructor
      · rintro ⟨_, ⟨b, hb, rfl⟩, h⟩
        exact ⟨b, hb, by rw [← hle a List.mem_cons_self b (hsub b hb)]; exact h⟩
      · rintro ⟨b, hb, h⟩
        exact ⟨f b, ⟨b, hb, rfl⟩, by rw [hle a List.mem_cons_self b (hsub b hb)]; exact h⟩
    have hfil : ((Sorts.antichain le L).map f).filter (fun b => !le' b (f a)) =
        ((Sorts.antichain le L).filter fun b => !le b a).map f := by
      rw [List.filter_map]
      congr 1
      refine List.filter_congr fun b hb => ?_
      simp only [Function.comp, hle b (hsub b hb) a List.mem_cons_self]
    simp only [List.map_cons, Sorts.antichain, ih, hany, hfil]
    split <;> rfl

/-- The exclusions of an assembled store, as value lists, are what
`antichain` gives on the value lists. -/
theorem antichain_vals {k : Nat} {Y : List Sorts.Binds} (hY : ∀ θ ∈ Y, ∀ b ∈ θ, b.1 < k) :
    Sorts.antichain coversV (Y.map (vals k)) =
      (Sorts.antichain (Sorts.covers k) Y).map (vals k) :=
  antichain_map (vals k) (Sorts.covers k) coversV Y fun θ hθ _ _ => coversV_vals (hY θ hθ)

end RwLogVerified
