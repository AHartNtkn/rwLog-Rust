/-
# The exclusions of a normal store, on the store

A solved exclusion is the list of the values it gives the variables of the
store. `sorts::covers` tests whether one is an instance of another
(`coversV`, which is `Sorts.covers` on value lists), `sorts::norm_exs` is
`Sorts.normExs`, `sorts::antichain` is `Sorts.antichain` with that test,
`sorts::low` is `Sorts.Low`, and `sorts::cut_exs` keeps the exclusions of
`Sorts.Raw.cut` with the values of the first variables.
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

/-! ## The first members of a list -/

theorem take_len_loop_spec :
    ∀ (Bs : List Pat) (s : store.Store) (out l «by» : store.TermId) (Ps O : List Pat),
    Inv s → Repr nm s.nodes.val «by».val (encList (nm none) Bs) →
    Repr nm s.nodes.val l.val (encList (nm none) Ps) →
    Repr nm s.nodes.val out.val (encList (nm none) O) → Bs.length ≤ Ps.length →
    Room s (3 * Bs.length + 1) →
    sorts.take_len_loop s out l «by» true ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 3 * Bs.length + 1 ∧
        Repr nm s'.nodes.val out'.val (encList (nm none) ((Ps.take Bs.length).reverse ++ O)) ⦄ := by
  intro Bs
  induction Bs with
  | nil =>
    intro s out l by0 Ps O hI hby hl hout hlen hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.take_len_loop
    rw [loop]
    simp only [sorts.take_len_loop.body, ↓reduceIte]
    step with uncons_repr s by0 hI.toWf (p := Term.sym (nm none)) hby (by unfold Room; omega)
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
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega, ?_⟩
    rw [K1.nodes]
    simpa using hout
  | cons b Bs ih =>
    intro s out l by0 Ps O hI hby hl hout hlen hroom
    cases Ps with
    | nil => simp at hlen
    | cons p Ps =>
      have hroom' := hroom
      unfold Room at hroom'
      simp only [List.length_cons] at hroom' hlen
      unfold sorts.take_len_loop
      rw [loop]
      simp only [sorts.take_len_loop.body, ↓reduceIte]
      step with uncons_repr s by0 hI.toWf (p := Term.app b (encList (nm none) Bs)) hby
        (by unfold Room; omega) as ⟨r0, hK0, hu⟩
      obtain ⟨o, s1⟩ := r0
      simp only at hu
      simp only at hK0
      obtain ⟨bi, brest, rfl, rb, rbrest⟩ := hu
      have K1 := hK0.kept hI
      have ht1 := K1.ticks
      step with uncons_repr s1 l K1.inv.toWf (p := Term.app p (encList (nm none) Ps))
        (by rw [K1.nodes]; exact hl) (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
      obtain ⟨o1, s2⟩ := r1
      simp only at hu1
      simp only at hK1'
      obtain ⟨pi, lrest, rfl, rp, rlrest⟩ := hu1
      rw [K1.nodes] at rp rlrest
      have K2 := hK1'.kept K1.inv
      have ht2 := K2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
      have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
      simp only [uncurry]
      step with alloc_spec s2 (.App pi out) K2.inv
        ⟨by rw [hn2]; exact rp.lt, by rw [hn2]; exact hout.lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx2.trans hx4
      have hout1 : Repr nm s4.nodes.val out1.val (encList (nm none) (p :: O)) :=
        .app hr4 (hx04.repr rp) (hx04.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s4 out1 lrest brest Ps (p :: O) hI4 (hx04.repr rbrest) (hx04.repr rlrest)
        hout1 (by omega) (by unfold Room; omega)
      unfold sorts.take_len_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx04.trans hx', by simp only [List.length_cons]; omega, ?_⟩
      simpa using hr'

/-- `take_len` gives as many of the first members of a list as the other
list has members. -/
theorem take_len_spec (Bs Ps : List Pat) (s : store.Store) (l by0 : store.TermId) (hI : Inv s)
    (hby : Repr nm s.nodes.val by0.val (encList (nm none) Bs))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) Ps)) (hlen : Bs.length ≤ Ps.length)
    (hroom : Room s (5 * Bs.length + 4)) :
    sorts.take_len s l by0 ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 5 * Bs.length + 4 ∧
        Repr nm s'.nodes.val res.val (encList (nm none) (Ps.take Bs.length)) ⦄ := by
  unfold sorts.take_len
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with take_len_loop_spec (nm := nm) Bs s1 out l by0 Ps [] hI1 (hx1.repr hby) (hx1.repr hl)
    (.nil hr1) hlen (by unfold Room; omega) as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  have hl2 : ((Ps.take Bs.length).reverse ++ []).length ≤ Bs.length := by
    simp
  refine WP.spec_mono (rev_spec (nm := nm) ((Ps.take Bs.length).reverse ++ [])
    s2 out1 hI2.toWf hr2 (by unfold Room; omega)) ?_
  rintro ⟨res, s3⟩ ⟨hR, hr3⟩
  have ht3 := hR.ticks
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext, by omega, ?_⟩
  simpa using hr3

theorem drop_len_loop_spec :
    ∀ (Bs : List Pat) (s : store.Store) (l «by» : store.TermId) (Ps : List Pat),
    Inv s → Repr nm s.nodes.val «by».val (encList (nm none) Bs) →
    Repr nm s.nodes.val l.val (encList (nm none) Ps) → Bs.length ≤ Ps.length →
    Room s (2 * Bs.length + 1) →
    sorts.drop_len_loop s l «by» true ⦃ l' s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s.ticks.val ≤ s'.ticks.val ∧
        s'.ticks.val ≤ s.ticks.val + 2 * Bs.length + 1 ∧
        Repr nm s'.nodes.val l'.val (encList (nm none) (Ps.drop Bs.length)) ⦄ := by
  intro Bs
  induction Bs with
  | nil =>
    intro s l by0 Ps hI hby hl hlen hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.drop_len_loop
    rw [loop]
    simp only [sorts.drop_len_loop.body, ↓reduceIte]
    step with uncons_repr s by0 hI.toWf (p := Term.sym (nm none)) hby (by unfold Room; omega)
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
    rw [K1.nodes]
    simpa using hl
  | cons b Bs ih =>
    intro s l by0 Ps hI hby hl hlen hroom
    cases Ps with
    | nil => simp at hlen
    | cons p Ps =>
      have hroom' := hroom
      unfold Room at hroom'
      simp only [List.length_cons] at hroom' hlen
      unfold sorts.drop_len_loop
      rw [loop]
      simp only [sorts.drop_len_loop.body, ↓reduceIte]
      step with uncons_repr s by0 hI.toWf (p := Term.app b (encList (nm none) Bs)) hby
        (by unfold Room; omega) as ⟨r0, hK0, hu⟩
      obtain ⟨o, s1⟩ := r0
      simp only at hu
      simp only at hK0
      obtain ⟨bi, brest, rfl, rb, rbrest⟩ := hu
      have K1 := hK0.kept hI
      have ht1 := K1.ticks
      step with uncons_repr s1 l K1.inv.toWf (p := Term.app p (encList (nm none) Ps))
        (by rw [K1.nodes]; exact hl) (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
      obtain ⟨o1, s2⟩ := r1
      simp only at hu1
      simp only at hK1'
      obtain ⟨pi, lrest, rfl, rp, rlrest⟩ := hu1
      rw [K1.nodes] at rp rlrest
      have K2 := hK1'.kept K1.inv
      have ht2 := K2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
      simp only [uncurry, bind_ok]
      have IH := ih s2 lrest brest Ps K2.inv (by rw [hn2]; exact rbrest)
        (by rw [hn2]; exact rlrest) (by omega) (by unfold Room; omega)
      unfold sorts.drop_len_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨l', s'⟩ ⟨hI', hn', hlo', ht', hr'⟩
      refine ⟨hI', by rw [hn', hn2], by omega, by simp only [List.length_cons]; omega, ?_⟩
      simpa using hr'

/-- `drop_len` gives a list without as many of its first members as the
other list has members. -/
theorem drop_len_spec (Bs Ps : List Pat) (s : store.Store) (l by0 : store.TermId) (hI : Inv s)
    (hby : Repr nm s.nodes.val by0.val (encList (nm none) Bs))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) Ps)) (hlen : Bs.length ≤ Ps.length)
    (hroom : Room s (2 * Bs.length + 1)) :
    sorts.drop_len s l by0 ⦃ l' s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s.ticks.val ≤ s'.ticks.val ∧
        s'.ticks.val ≤ s.ticks.val + 2 * Bs.length + 1 ∧
        Repr nm s'.nodes.val l'.val (encList (nm none) (Ps.drop Bs.length)) ⦄ := by
  unfold sorts.drop_len
  exact drop_len_loop_spec Bs s l by0 Ps hI hby hl hlen hroom

/-! ## Exclusions over the first variables -/

/-- The value list says nothing of the variables from `j` on: each is its
own value, and the values of the ones before have only variables before. -/
def lowV (j : Nat) (V : List Pat) : Bool :=
  decide (V.drop j = (varsTo V.length).drop j ∧ ∀ p ∈ V.take j, ∀ v ∈ p.vars, v < j)

/-- The variables below `j` replaced by a constant. -/
def nilSub (z : RwLog.Sym) (j : Nat) (w : Nat) : Pat := if w < j then .sym z else .var w

theorem putAll_const (c : Pat) : ∀ j : Nat,
    putAll ((List.range j).map fun v => (v, c)) (fun _ => none) =
      fun w => if w < j then some c else none
  | 0 => rfl
  | j + 1 => by
    have ih := putAll_const c j
    unfold putAll at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    funext w
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    by_cases hw : w = j
    · subst hw
      simp
    · rw [Function.update_of_ne hw]
      by_cases hlt : w < j
      · have : w < j + 1 := by omega
        simp only [hlt, this, ↓reduceIte]
      · have : ¬ w < j + 1 := by omega
        simp only [hlt, this, ↓reduceIte]

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

theorem subs_take (z : RwLog.Sym) : ∀ (V : List Pat) (j : Nat), ∃ F : Finset Pat,
    F.card ≤ j + 1 ∧ (encList z (V.take j)).subs ⊆ (encList z V).subs ∪ F
  | [], j => ⟨∅, by simp, by simp⟩
  | p :: V, 0 => ⟨{Term.sym z}, by simp, by
      intro w hw
      simp only [List.take_zero, encList, Term.subs, Finset.mem_singleton] at hw
      subst hw
      simp⟩
  | p :: V, j + 1 => by
    obtain ⟨F, hF, hsub⟩ := subs_take z V j
    refine ⟨insert (.app p (encList z (V.take j))) F, by
      have := Finset.card_insert_le (Term.app p (encList z (V.take j))) F
      omega, ?_⟩
    intro w hw
    simp only [List.take_succ_cons, encList, Term.subs, Finset.mem_insert, Finset.mem_union]
      at hw ⊢
    rcases hw with rfl | hw | hw
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl hw))
    · rcases Finset.mem_union.1 (hsub hw) with h | h
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr h)

/-- The first members of a list have few subterms the list has not. -/
theorem card_take_le (z : RwLog.Sym) (V : List Pat) (j : Nat) :
    (encList z (V.take j)).subs.card ≤ (encList z V).subs.card + j + 1 := by
  obtain ⟨F, hF, hsub⟩ := subs_take z V j
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (encList z V).subs F
  omega

theorem low_loop_spec (nil : store.TermId) :
    ∀ (R : List Nat) (s : store.Store) (l : store.TermId) (M : Nat → Option Pat),
    Inv s → Repr nm s.nodes.val l.val (encList (nm none) (R.map Term.var)) →
    Repr nm s.nodes.val nil.val (Term.sym (nm none)) →
    TblVal nm s.nodes.val (tbl s .B) M → Room s (2 * R.length + 1) →
    sorts.low_loop l s nil ⦃ s' =>
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
    unfold sorts.low_loop
    rw [loop]
    simp only [sorts.low_loop.body]
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
    unfold sorts.low_loop
    rw [loop]
    simp only [sorts.low_loop.body]
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
    unfold sorts.low_loop at IH
    refine WP.spec_mono IH ?_
    rintro s' ⟨hI', hn', hlo', ht', hT'⟩
    exact ⟨hI', by rw [hn', hn2], by omega, by simp only [List.length_cons]; omega, hT'⟩

/-- The ticks `low` may take with `j` first variables on a value list of at
most `m` subterms. -/
def lowCost (j m : Nat) : Nat := 38 * j + 27 * m + 50

/-- `low` tests whether an exclusion says nothing of the variables after
the first ones. -/
theorem low_spec (hnm : Function.Injective nm) (j m : Nat) (V : List Pat) (s : store.Store)
    (vs ks vals : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo V.length)))
    (hks : Repr nm s.nodes.val ks.val (encList (nm none) (varsTo j)))
    (hvals : Repr nm s.nodes.val vals.val (encList (nm none) V)) (hj : j ≤ V.length)
    (hm : (encList (nm none) V).subs.card ≤ m) (hroom : Room s (lowCost j m)) :
    sorts.low s vs ks vals ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + lowCost j m ∧ b = lowV j V ⦄ := by
  unfold sorts.low
  have hroom' := hroom
  unfold Room at hroom'
  simp only [lowCost] at hroom'
  step with drop_len_spec (nm := nm) (varsTo j) V s vals ks hI hks hvals
    (by simpa using hj) (by simp only [varsTo_length]; unfold Room; omega)
    as ⟨later, s1, hI1, hn1, hlo1, ht1, hr1⟩
  simp only [varsTo_length] at ht1 hr1
  step with drop_len_spec (nm := nm) (varsTo j) (varsTo V.length) s1 vs ks hI1
    (by rw [hn1]; exact hks) (by rw [hn1]; exact hvs) (by simpa using hj)
    (by simp only [varsTo_length]; unfold Room; omega)
    as ⟨own, s2, hI2, hn2, hlo2, ht2, hr2⟩
  simp only [varsTo_length] at ht2 hr2
  rw [hn1] at hn2
  rw [hn1, ← hn2] at hr1
  step with same_spec s2 later own hI2 (by unfold Room; omega) as ⟨b, s3, hb, hK3⟩
  have ht3 := hK3.ticks
  have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
  have hx3 : Extends s s3 := Extends.of_eq hn3 (by omega)
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hK3.inv, hx3, by simp only [lowCost]; omega, ?_⟩
    unfold lowV
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨e, -⟩
    have : later.val = own.val := Repr.inj hnm hI2.nodesOK hr1 (by rw [e]; exact hr2)
    simp [this] at hb
  | true =>
    have e1 : V.drop j = (varsTo V.length).drop j := by
      have : later.val = own.val := by simpa using hb.symm
      rw [this] at hr1
      exact encList_inj _ (hr1.unique hr2)
    simp only [↓reduceIte]
    step with take_len_spec (nm := nm) (varsTo j) V s3 vals ks hK3.inv (hx3.repr hks)
      (hx3.repr hvals) (by simpa using hj) (by simp only [varsTo_length]; unfold Room; omega)
      as ⟨first, s4, hI4, hx4, ht4, hr4⟩
    simp only [varsTo_length] at ht4 hr4
    have hx04 := hx3.trans hx4
    step with alloc_spec s4 .Nil hI4 trivial (by unfold Room; omega)
      as ⟨nil, s5, hI5, ht5, htb5, hx5, hr5⟩
    simp only [norm] at hr5
    have hx05 := hx04.trans hx5
    step with clear_spec s5 .B hI5 (by unfold Room; omega) as ⟨s6, c1, c2, c3, c4, c5⟩
    step with low_loop_spec (nm := nm) nil (List.range j) s6 ks (fun _ => none) c3
      (by rw [c1]; exact hx05.repr hks) (by rw [c1]; exact .nil hr5)
      ⟨fun q u h => (by rw [c4] at h; cases h), fun w v h => (by cases h)⟩
      (by simp only [List.length_range]; unfold Room; omega) as ⟨s7, hI7, hn7, hlo7, ht7, hT7⟩
    simp only [List.length_range] at ht7
    rw [putAll_const] at hT7
    step with clear_spec s7 .A hI7 (by unfold Room; omega) as ⟨s8, d1, d2, d3, d4, d5⟩
    have hn8 : s8.nodes.val = s5.nodes.val := by rw [d1, hn7, c1]
    have hx08 : Extends s s8 := hx05.trans (Extends.of_eq hn8 (by omega))
    have eσ : (fun w => (if w < j then some (Term.sym (nm none) : Pat) else none).getD
        (Term.var w)) = nilSub (nm none) j := by
      funext w
      unfold nilSub
      split <;> rfl
    have hleaf : LeafOK nm s8.nodes.val (tbl s8 .B) term.Leaf.Map (nilSub (nm none) j) := by
      rw [d1, d5 .B (by simp), ← eσ]
      exact hT7.leaf
    have hpc := pending_card_le (nm := nm) s8.nodes.val (tbl s8 .A)
      (encList (nm none) (V.take j)).subs
    have hct := card_take_le (nm none) V j
    step with rebuild_spec hnm s8 .Map first (t := encList (nm none) (V.take j))
      (σ := nilSub (nm none) j) (encList (nm none) (V.take j)).subs d3
      (by rw [hn8]; exact hx5.repr hr4) hleaf (by intro q v hq; rw [d4] at hq; cases hq)
      (Finset.Subset.refl _) (by unfold Room; omega) as ⟨closed, s9, h9⟩
    have hc9 := h9.cost
    have hσ : ∀ v, (nilSub (nm none) j v).subs = {nilSub (nm none) j v} := by
      intro v
      unfold nilSub
      split <;> rfl
    have hcb : ((encList (nm none) (V.take j)).bind (nilSub (nm none) j)).subs.card ≤
        (encList (nm none) (V.take j)).subs.card :=
      (Finset.card_le_card (subs_bind_leaf hσ _)).trans Finset.card_image_le
    refine WP.spec_mono (ground_spec hnm s9 closed h9.inv h9.repr (by unfold Room; omega)) ?_
    rintro ⟨b, s10⟩ ⟨hI10, hn10, hlo10, ht10, -, hb10⟩
    refine ⟨hI10, (hx08.trans h9.ext).trans (Extends.of_eq hn10 hlo10),
      by simp only [lowCost]; omega, ?_⟩
    rw [hb10]
    unfold lowV
    refine decide_eq_decide.2 ?_
    rw [bind_vars_nil]
    constructor
    · intro h
      refine ⟨e1, fun p hp v hv => ?_⟩
      have := h v ((mem_vars_encList _).2 ⟨p, hp, hv⟩)
      by_contra hlt
      simp [nilSub, hlt, Term.vars] at this
    · rintro ⟨-, h⟩ v hv
      obtain ⟨p, hp, hv'⟩ := (mem_vars_encList _).1 hv
      simp [nilSub, h p hp v hv', Term.vars]

theorem cut_exs_loop_spec (hnm : Function.Injective nm) (j k m : Nat) (hjk : j ≤ k)
    (vs ks : store.TermId) :
    ∀ (Ls : List (List Pat)) (s : store.Store) (l out : store.TermId) (O : List (List Pat)),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) (varsTo k)) →
    Repr nm s.nodes.val ks.val (encList (nm none) (varsTo j)) →
    Repr nm s.nodes.val l.val (encLL nm Ls) → Repr nm s.nodes.val out.val (encLL nm O) →
    (∀ B ∈ Ls, B.length = k ∧ (encList (nm none) B).subs.card ≤ m) →
    Room s (repCost (lowCost j m + 5 * j + 6) Ls.length) →
    sorts.cut_exs_loop l s vs ks out ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + repCost (lowCost j m + 5 * j + 6) Ls.length ∧
        Repr nm s'.nodes.val out'.val
          (encLL nm (((Ls.filter (lowV j)).map (List.take j)).reverse ++ O)) ⦄ := by
  intro Ls
  induction Ls with
  | nil =>
    intro s l out O hI hvs hks hl hout hL hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, repCost] at hroom'
    unfold sorts.cut_exs_loop
    rw [loop]
    simp only [sorts.cut_exs_loop.body]
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
          repCost (lowCost j m + 5 * j + 6) ([] : List (List Pat)).length ∧
        Repr nm s1.nodes.val out.val
          (encLL nm (((([] : List (List Pat)).filter (lowV j)).map (List.take j)).reverse ++ O)) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil, repCost]; omega,
        by rw [K1.nodes]; exact hout⟩
    step*
  | cons B Ls ih =>
    intro s l out O hI hvs hks hl hout hL hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, repCost] at hroom'
    obtain ⟨hBk, hBm⟩ := hL B List.mem_cons_self
    unfold sorts.cut_exs_loop
    rw [loop]
    simp only [sorts.cut_exs_loop.body]
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
    step with low_spec hnm j m B s1 vs ks bi K1.inv (by rw [hBk]; exact hx1.repr hvs)
      (hx1.repr hks) (hx1.repr rb) (by omega) hBm (by unfold Room; omega)
      as ⟨r1, hI2, hx2, ht2, hres⟩
    obtain ⟨b1, s2⟩ := r1
    simp only at hI2 hx2 ht2 hres
    have hx02 := hx1.trans hx2
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 rest out O hI2 (hx02.repr hvs) (hx02.repr hks) (hx02.repr rrest)
        (hx02.repr hout) (fun B' h => hL B' (List.mem_cons_of_mem _ h)) (by unfold Room; omega)
      unfold sorts.cut_exs_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx02.trans hx', by simp only [List.length_cons, repCost]; omega, ?_⟩
      have e : (B :: Ls).filter (lowV j) = Ls.filter (lowV j) := by simp [← hres]
      rw [e]
      exact hr'
    | true =>
      simp only [↓reduceIte, uncurry]
      step with take_len_spec (nm := nm) (varsTo j) B s2 bi ks hI2 (hx02.repr hks)
        (hx02.repr rb) (by simp only [varsTo_length]; omega)
        (by simp only [varsTo_length]; unfold Room; omega) as ⟨r3, hI3, hx3, ht3, hr3⟩
      obtain ⟨first, s3⟩ := r3
      simp only [varsTo_length] at hI3 hx3 ht3 hr3
      have hx03 := hx02.trans hx3
      step with alloc_spec s3 (.App first out) hI3 ⟨hr3.lt, (hx03.repr hout).lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx03.trans hx4
      have hout1 : Repr nm s4.nodes.val out1.val (encLL nm (B.take j :: O)) :=
        .app hr4 (hx4.repr hr3) (hx04.repr hout)
      simp only [uncurry, bind_ok]
      have IH := ih s4 rest out1 (B.take j :: O) hI4 (hx04.repr hvs) (hx04.repr hks)
        (hx04.repr rrest) hout1 (fun B' h => hL B' (List.mem_cons_of_mem _ h))
        (by unfold Room; omega)
      unfold sorts.cut_exs_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
      refine ⟨hI', hx04.trans hx', by simp only [List.length_cons, repCost]; omega, ?_⟩
      have e : (B :: Ls).filter (lowV j) = B :: Ls.filter (lowV j) := by simp [← hres]
      rw [e]
      simpa using hr'

/-- The ticks `cut_exs` may take on `n` exclusions. -/
def cutCost (j m n : Nat) : Nat := repCost (lowCost j m + 5 * j + 6) n + 2 * n + 3

/-- `cut_exs` keeps the exclusions that say nothing of the variables after
the first `j`, each as the values of these. -/
theorem cut_exs_spec (hnm : Function.Injective nm) (j k m : Nat) (hjk : j ≤ k)
    (Ls : List (List Pat)) (s : store.Store) (vs ks l : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo k)))
    (hks : Repr nm s.nodes.val ks.val (encList (nm none) (varsTo j)))
    (hl : Repr nm s.nodes.val l.val (encLL nm Ls))
    (hL : ∀ B ∈ Ls, B.length = k ∧ (encList (nm none) B).subs.card ≤ m)
    (hroom : Room s (cutCost j m Ls.length)) :
    sorts.cut_exs s vs ks l ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + cutCost j m Ls.length ∧
        Repr nm s'.nodes.val res.val (encLL nm ((Ls.filter (lowV j)).map (List.take j))) ⦄ := by
  unfold sorts.cut_exs
  have hroom' := hroom
  unfold Room at hroom'
  simp only [cutCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with cut_exs_loop_spec hnm j k m hjk vs ks Ls s1 l out [] hI1 (hx1.repr hvs)
    (hx1.repr hks) (hx1.repr hl) (.nil hr1) hL (by unfold Room; omega)
    as ⟨s2, out1, hI2, hx2, ht2, hr2⟩
  have hlen : (Ls.filter (lowV j)).length ≤ Ls.length := List.length_filter_le _ _
  refine WP.spec_mono (rev_spec (nm := nm)
    ((((Ls.filter (lowV j)).map (List.take j)).reverse ++ []).map (encList (nm none)))
    s2 out1 hI2.toWf hr2 (by simp only [List.length_map, List.length_append,
      List.length_reverse, List.length_nil]; unfold Room; omega)) ?_
  rintro ⟨res, s3⟩ ⟨hR, hr3⟩
  have ht3 := hR.ticks
  simp only [List.length_map, List.length_append, List.length_reverse, List.length_nil] at ht3
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext,
    by simp only [cutCost]; omega, ?_⟩
  unfold encLL
  simpa [List.map_reverse, List.map_map] using hr3

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

theorem take_vals {j k : Nat} (hjk : j ≤ k) (θ : Sorts.Binds) :
    (vals k θ).take j = vals j θ := by
  unfold vals
  rw [← List.map_take, List.take_range, Nat.min_eq_left hjk]

/-- `lowV` on the values of an exclusion in solved form is `Sorts.Low`. -/
theorem lowV_vals {j k : Nat} {θ : Sorts.Binds} (hθ : Sorts.Pre k θ) (hjk : j ≤ k) :
    lowV j (vals k θ) = decide (Sorts.Low j θ) := by
  unfold lowV
  refine decide_eq_decide.2 ?_
  rw [take_vals hjk, vals_length]
  have hdrop : (vals k θ).drop j = (varsTo k).drop j ↔
      ∀ x, j ≤ x → x < k → PSubst.apply θ x = .var x := by
    unfold vals varsTo
    rw [← List.map_drop, ← List.map_drop, List.map_inj_left]
    constructor
    · intro h x hjx hxk
      refine h x ?_
      have : x = (List.range k)[x]'(by simpa using hxk) := by simp
      rw [this]
      exact List.mem_drop_iff_getElem.2 ⟨x - j, by simp; omega, by simp; omega⟩
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_drop_iff_getElem.1 hx
      simp only [List.length_range] at hi
      simp only [List.getElem_range]
      exact h _ (by omega) (by omega)
  rw [hdrop]
  constructor
  · rintro ⟨h1, h2⟩ b hb
    have hbk := hθ.dom b hb
    have hap : PSubst.apply θ b.1 = b.2 := Sorts.apply_of_mem hθ.sorted hb
    have hlt : b.1 < j := by
      by_contra hge
      have := h1 b.1 (by omega) hbk
      rw [hap] at this
      exact absurd (hθ.later b hb b.1 this) (Nat.lt_irrefl _)
    refine ⟨hlt, fun v hv => ?_⟩
    refine h2 (PSubst.apply θ b.1) ?_ v (by rw [hap]; exact hv)
    unfold vals
    exact List.mem_map.2 ⟨b.1, List.mem_range.2 hlt, rfl⟩
  · intro hL
    refine ⟨fun x hjx _ => Sorts.apply_of_not_mem fun b hb hbx => ?_, fun p hp v hv => ?_⟩
    · have := (hL b hb).1
      omega
    · unfold vals at hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
      have hxj := List.mem_range.1 hx
      by_cases hex : ∃ b ∈ θ, b.1 = x
      · obtain ⟨b, hb, rfl⟩ := hex
        rw [Sorts.apply_of_mem hθ.sorted hb] at hv
        exact (hL b hb).2 v hv
      · rw [Sorts.apply_of_not_mem fun b hb hbx => hex ⟨b, hb, hbx⟩] at hv
        simp only [Term.vars, List.mem_singleton] at hv
        omega

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
