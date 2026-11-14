/-
# The solved form of an exclusion, on the store

A solved exclusion over the variables of a numbered store is the list of
the values it gives them. `sorts::places` lists the variables of a store.
`sorts::orient` turns the aliases of a solution to their first variable
(`Sorts.orient`). `sorts::push_all` pushes the sorts of the variables onto
their values, `sorts::ups` reads the sorts the atoms put on one variable,
and `sorts::close` binds the free variables left with one value
(`Sorts.close`). `sorts::norm_ex` is `Sorts.normEx`.
-/
import RwLogVerified.Number
import RwLogVerified.Push
import RwLog.Sorts.CloseVals

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The variables of a numbered store -/

/-- The variables below `k`. -/
def varsTo (k : Nat) : List Pat := (List.range k).map Term.var

theorem varsTo_succ (k : Nat) : varsTo (k + 1) = varsTo k ++ [Term.var k] := by
  simp [varsTo, List.range_succ]

@[simp] theorem varsTo_length (k : Nat) : (varsTo k).length = k := by simp [varsTo]

theorem places_loop_spec :
    ∀ (ps : List Pat) (s : store.Store) (cs out v : store.TermId) (n : Nat),
    Inv s → Repr nm s.nodes.val cs.val (encList (nm none) ps) →
    Repr nm s.nodes.val out.val (encList (nm none) (varsTo n).reverse) →
    VarAt s.nodes.val v.val n → Room s (numCost n ps.length) →
    sorts.places_loop cs s out v ⦃ s' out' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + numCost n ps.length ∧
        Repr nm s'.nodes.val out'.val (encList (nm none) (varsTo (n + ps.length)).reverse) ⦄ := by
  intro ps
  induction ps with
  | nil =>
    intro s cs out v n hI hcs hout hv hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, numCost] at hroom'
    unfold sorts.places_loop
    rw [loop]
    simp only [sorts.places_loop.body]
    step with uncons_repr s cs hI.toWf (p := Term.sym (nm none)) hcs (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧
        s1.ticks.val ≤ s.ticks.val + numCost n ([] : List Pat).length ∧
        Repr nm s1.nodes.val out.val
          (encList (nm none) (varsTo (n + ([] : List Pat).length)).reverse) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil, numCost]; omega,
        by rw [K1.nodes]; exact hout⟩
    step*
  | cons p ps ih =>
    intro s cs out v n hI hcs hout hv hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, numCost] at hroom'
    unfold sorts.places_loop
    rw [loop]
    simp only [sorts.places_loop.body]
    step with uncons_repr s cs hI.toWf (p := Term.app p (encList (nm none) ps)) hcs
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨hd, rest, rfl, -, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with alloc_spec s1 (.App v out) K1.inv
      ⟨by rw [K1.nodes]; exact hv.lt, by rw [K1.nodes]; exact hout.lt⟩ (by unfold Room; omega)
      as ⟨r2, hI2, ht2, htb2, hx2, hr2⟩
    obtain ⟨out1, s2⟩ := r2
    simp only [norm] at hI2 ht2 htb2 hx2 hr2
    have hx02 := hx1.trans hx2
    step with var_succ_spec s2 v hI2 (hx02.varAt hv) (by unfold Room; omega)
      as ⟨r3, hI3, hx3, htb3, hv3, ht3⟩
    obtain ⟨v1, s3⟩ := r3
    simp only at hI3 hx3 htb3 hv3 ht3
    simp only [uncurry, bind_ok]
    have hx03 := hx02.trans hx3
    have hout1 : Repr nm s3.nodes.val out1.val (encList (nm none) (varsTo (n + 1)).reverse) := by
      rw [varsTo_succ, List.reverse_append]
      exact hx3.repr (.app hr2 (.var (hx02.varAt hv)) (hx02.repr hout))
    have IH := ih s3 rest out1 v1 (n + 1) hI3 (hx03.repr rrest) hout1 hv3 (by unfold Room; omega)
    unfold sorts.places_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨s', out'⟩ ⟨hI', hx', ht', hr'⟩
    refine ⟨hI', hx03.trans hx', by simp only [List.length_cons, numCost]; omega, ?_⟩
    rw [List.length_cons, show n + (ps.length + 1) = n + 1 + ps.length by omega]
    exact hr'

/-- The ticks `places` may take for `k` variables. -/
def placesCost (k : Nat) : Nat := numCost 0 k + 2 * k + 4

/-- `places` lists the variables of a store with a conjunction for each. -/
theorem places_spec (ps : List Pat) (s : store.Store) (cs : store.TermId) (hI : Inv s)
    (hcs : Repr nm s.nodes.val cs.val (encList (nm none) ps))
    (hroom : Room s (placesCost ps.length)) :
    sorts.places s cs ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + placesCost ps.length ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (varsTo ps.length)) ⦄ := by
  unfold sorts.places
  have hroom' := hroom
  unfold Room at hroom'
  simp only [placesCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  step with alloc_spec s1 .V0 hI1 trivial (by unfold Room; omega)
    as ⟨v, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr1 hr2
  have hx02 := hx1.trans hx2
  step with places_loop_spec (nm := nm) ps s2 cs out v 0 hI2 (hx02.repr hcs)
    (hx2.repr (.nil hr1)) (.zero hr2) (by unfold Room; omega) as ⟨s3, out1, hI3, hx3, ht3, hr3⟩
  rw [Nat.zero_add] at hr3
  step with rev_spec (varsTo ps.length).reverse s3 out1 hI3.toWf hr3
    (by simp only [List.length_reverse, varsTo_length]; unfold Room; omega) as ⟨r, s4, hR, hr4⟩
  simp only [List.length_reverse, varsTo_length] at hR
  rw [List.reverse_reverse] at hr4
  have ht4 := hR.ticks
  exact ⟨⟨hR.wf, by rw [hR.stk]; exact hI3.empty⟩, (hx02.trans hx3).trans hR.ext,
    by simp only [placesCost]; omega, hr4⟩

/-! ## Turning aliases to their first variable -/

/-- The first variable of the list whose value is the variable `w`. -/
def firstOf : List (Nat × Pat) → Nat → Option Nat
  | [], _ => none
  | b :: L, w => if b.2 = .var w then some b.1 else firstOf L w

theorem firstOf_map (μ : Nat → Pat) (w : Nat) : ∀ l : List Nat,
    firstOf (l.map fun v => (v, μ v)) w = l.find? fun v => decide (μ v = .var w)
  | [] => rfl
  | v :: l => by
    simp only [List.map_cons, firstOf, List.find?_cons]
    by_cases h : μ v = .var w
    · simp [h]
    · simp [h, firstOf_map μ w l]

/-- Table `B` holds, for each variable `M` has an entry for, the variable
of that entry, and nothing else. -/
structure TblMap (nodes : List store.Node) (B : Nat → Option Nat) (M : Nat → Option Nat) :
    Prop where
  sound : ∀ q u, B q = some u → ∃ w v, VarAt nodes q w ∧ VarAt nodes u v ∧ M w = some v
  complete : ∀ w v, M w = some v → ∃ q u, VarAt nodes q w ∧ B q = some u

theorem TblMap.none_of {nodes : List store.Node} {B M : Nat → Option Nat} (h : TblMap nodes B M)
    (hN : NodesOK nodes) {q w : Nat} (hq : VarAt nodes q w) (hB : B q = none) : M w = none := by
  cases hM : M w with
  | none => rfl
  | some v =>
    obtain ⟨q', u, hq', hu⟩ := h.complete w v hM
    rw [hq'.inj hN hq, hB] at hu
    cases hu

theorem TblMap.set {nodes : List store.Node} {B M : Nat → Option Nat} (h : TblMap nodes B M)
    {q u w v : Nat} (hq : VarAt nodes q w) (hu : VarAt nodes u v) (hM : M w = none) :
    TblMap nodes (Function.update B q (some u)) (Function.update M w (some v)) := by
  constructor
  · intro q' u' hB
    by_cases e : q' = q
    · subst e
      rw [Function.update_self] at hB
      cases hB
      exact ⟨w, v, hq, hu, by rw [Function.update_self]⟩
    · rw [Function.update_of_ne e] at hB
      obtain ⟨w', v', h1, h2, h3⟩ := h.sound q' u' hB
      refine ⟨w', v', h1, h2, ?_⟩
      rw [Function.update_of_ne]
      · exact h3
      · rintro rfl
        rw [hM] at h3
        cases h3
  · intro w' v' hM'
    by_cases e : w' = w
    · subst e
      exact ⟨q, u, hq, by rw [Function.update_self]⟩
    · rw [Function.update_of_ne e] at hM'
      obtain ⟨q', u', h1, h2⟩ := h.complete w' v' hM'
      refine ⟨q', u', h1, ?_⟩
      rw [Function.update_of_ne]
      · exact h2
      · rintro rfl
        exact e (h1.unique hq)

theorem orient_loop_spec :
    ∀ (L : List (Nat × Pat)) (s : store.Store) (vs l : store.TermId) (M : Nat → Option Nat),
    Inv s → Repr nm s.nodes.val vs.val (encList (nm none) (L.map fun b => Term.var b.1)) →
    Repr nm s.nodes.val l.val (encList (nm none) (L.map fun b => b.2)) →
    TblMap s.nodes.val (tbl s .B) M → Room s (5 * L.length + 1) →
    sorts.orient_loop s vs l true ⦃ s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ s.ticks.val ≤ s'.ticks.val ∧
        s'.ticks.val ≤ s.ticks.val + 5 * L.length + 1 ∧
        TblMap s'.nodes.val (tbl s' .B) fun w => (M w).or (firstOf L w) ⦄ := by
  intro L
  induction L with
  | nil =>
    intro s vs l M hI hvs hl hT hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.orient_loop
    rw [loop]
    simp only [sorts.orient_loop.body, ↓reduceIte]
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
    simpa [firstOf] using hT
  | cons b L ih =>
    intro s vs l M hI hvs hl hT hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.orient_loop
    rw [loop]
    simp only [sorts.orient_loop.body, ↓reduceIte]
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
    have hvv : VarAt s.nodes.val vi.val b.1 := by
      cases rv with
      | var h => exact h
    step with is_var_w s2 pi (q := b.2) K2.inv.toWf (by rw [hn2]; exact rp)
      (by unfold Room; omega) as ⟨r2, hb, hK2'⟩
    obtain ⟨isv, s3⟩ := r2
    simp only at hb hK2'
    have K3 := hK2'.kept K2.inv
    have ht3 := K3.ticks
    have hn3 : s3.nodes.val = s.nodes.val := by rw [K3.nodes, hn2]
    have hB3 : tbl s3 .B = tbl s .B := by rw [K3.tbl, K2.tbl, K1.tbl]
    cases isv with
    | false =>
      have hnv : ∀ w, b.2 ≠ .var w := fun w e => by
        have := hb.2 ⟨w, e⟩
        cases this
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
      have IH := ih s3 vrest lrest M K3.inv (by rw [hn3]; exact rvrest) (by rw [hn3]; exact rlrest)
        (by rw [hn3, hB3]; exact hT) (by unfold Room; omega)
      unfold sorts.orient_loop at IH
      refine WP.spec_mono IH ?_
      rintro s' ⟨hI', hn', hlo', ht', hT'⟩
      refine ⟨hI', by rw [hn', hn3], by omega, by simp only [List.length_cons]; omega, ?_⟩
      have e : (fun w => (M w).or (firstOf (b :: L) w)) = fun w => (M w).or (firstOf L w) := by
        funext w
        simp only [firstOf, hnv w, ↓reduceIte]
      rw [e]
      exact hT'
    | true =>
      obtain ⟨w0, hw0⟩ := hb.1 rfl
      have hpv : VarAt s.nodes.val pi.val w0 := by
        rw [hw0] at rp
        cases rp with
        | var h => exact h
      simp only [uncurry, ↓reduceIte]
      step with get_spec s3 .B pi K3.inv (by rw [hn3]; exact hpv.lt) (by unfold Room; omega)
        as ⟨r4, hg, hK4⟩
      obtain ⟨o2, s4⟩ := r4
      simp only at hg hK4
      have ht4 := hK4.ticks
      have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
      have hB4 : tbl s4 .B = tbl s .B := by rw [hK4.tbl, hB3]
      rw [hB3] at hg
      cases o2 with
      | some u =>
        simp only [Option.map_some] at hg
        obtain ⟨w', v', h1, -, h3⟩ := hT.sound pi.val u.val hg.symm
        have hw' : w' = w0 := h1.unique hpv
        subst hw'
        simp only [uncurry, bind_ok]
        have IH := ih s4 vrest lrest M hK4.inv (by rw [hn4]; exact rvrest)
          (by rw [hn4]; exact rlrest) (by rw [hn4, hB4]; exact hT) (by unfold Room; omega)
        unfold sorts.orient_loop at IH
        refine WP.spec_mono IH ?_
        rintro s' ⟨hI', hn', hlo', ht', hT'⟩
        refine ⟨hI', by rw [hn', hn4], by omega, by simp only [List.length_cons]; omega, ?_⟩
        have e : (fun w => (M w).or (firstOf (b :: L) w)) = fun w => (M w).or (firstOf L w) := by
          funext w
          by_cases hw : w = w'
          · subst hw; simp [h3]
          · have : b.2 ≠ .var w := by rw [hw0]; intro e; cases e; exact hw rfl
            simp only [firstOf, this, ↓reduceIte]
        rw [e]
        exact hT'
      | none =>
        simp only [Option.map_none] at hg
        have hM0 : M w0 = none := hT.none_of hI.nodesOK hpv hg.symm
        simp only [uncurry]
        step with set_spec s4 .B pi vi hK4.inv (by rw [hn4]; exact hpv.lt)
          (by unfold Room; omega) as ⟨s5, g1, g2, g3, g4, g5⟩
        have hn5 : s5.nodes.val = s.nodes.val := by rw [g1, hn4]
        rw [hB4] at g4
        have IH := ih s5 vrest lrest (Function.update M w0 (some b.1)) g3
          (by rw [hn5]; exact rvrest) (by rw [hn5]; exact rlrest)
          (by rw [hn5, g4]; exact hT.set hpv hvv hM0) (by unfold Room; omega)
        unfold sorts.orient_loop at IH
        refine WP.spec_mono IH ?_
        rintro s' ⟨hI', hn', hlo', ht', hT'⟩
        refine ⟨hI', by rw [hn', hn5], by omega, by simp only [List.length_cons]; omega, ?_⟩
        have e : (fun w => (M w).or (firstOf (b :: L) w)) =
            fun w => (Function.update M w0 (some b.1) w).or (firstOf L w) := by
          funext w
          by_cases hw : w = w0
          · subst hw; simp [hM0, firstOf, hw0]
          · have : b.2 ≠ .var w := by rw [hw0]; intro e; cases e; exact hw rfl
            simp only [firstOf, this, ↓reduceIte, Function.update_of_ne hw]
        rw [e]
        exact hT'

/-- The ticks `orient` may take on `k` variables whose values are the list
`T`. -/
def orientCost (k : Nat) (T : Pat) : Nat := 5 * k + 14 * T.subs.card + 8

/-- `orient` renames each variable that is the value of a variable to the
first variable it is the value of. -/
theorem orient_spec (hnm : Function.Injective nm) (k : Nat) (μ : Nat → Pat) (s : store.Store)
    (vs vals : store.TermId) (hI : Inv s)
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo k)))
    (hvals : Repr nm s.nodes.val vals.val (encList (nm none) ((List.range k).map μ)))
    (hroom : Room s (orientCost k (encList (nm none) ((List.range k).map μ)))) :
    sorts.orient s vs vals ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + orientCost k (encList (nm none) ((List.range k).map μ)) ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) ((List.range k).map (Sorts.orient k μ))) ⦄ := by
  unfold sorts.orient
  have hroom' := hroom
  unfold Room at hroom'
  simp only [orientCost] at hroom'
  step with clear_spec s .B hI (by unfold Room; omega) as ⟨s1, c1, c2, c3, c4, c5⟩
  have e1 : ((List.range k).map fun v => (v, μ v)).map (fun b => (Term.var b.1 : Pat)) =
      varsTo k := by
    simp [varsTo, List.map_map, Function.comp_def]
  have e2 : ((List.range k).map fun v => (v, μ v)).map (fun b => b.2) = (List.range k).map μ := by
    simp [List.map_map, Function.comp_def]
  step with orient_loop_spec (nm := nm) ((List.range k).map fun v => (v, μ v)) s1 vs vals
    (fun _ => none) c3 (by rw [c1, e1]; exact hvs) (by rw [c1, e2]; exact hvals)
    ⟨fun q u h => (by rw [c4] at h; cases h), fun w v h => (by cases h)⟩
    (by simp only [List.length_map, List.length_range]; unfold Room; omega)
    as ⟨s2, hI2, hn2, hlo2, ht2, hT2⟩
  simp only [List.length_map, List.length_range, Option.none_or] at ht2 hT2
  step with clear_spec s2 .A hI2 (by unfold Room; omega) as ⟨s3, d1, d2, d3, d4, d5⟩
  have hn3 : s3.nodes.val = s.nodes.val := by rw [d1, hn2, c1]
  have hM : ∀ w, firstOf ((List.range k).map fun v => (v, μ v)) w =
      (List.range k).find? fun v => decide (μ v = .var w) := fun w => firstOf_map μ w _
  have hleaf : LeafOK nm s3.nodes.val (tbl s3 .B) term.Leaf.Map
      (fun w => .var (Sorts.rep k μ w)) := by
    rw [d1, d5 .B (by simp)]
    refine ⟨fun q u hq => ?_, fun v hv => ?_⟩
    · obtain ⟨w, v, h1, h2, h3⟩ := hT2.sound q u hq
      refine ⟨w, h1, ?_⟩
      rw [hM] at h3
      have : Sorts.rep k μ w = v := by
        unfold Sorts.rep
        rw [h3]
        rfl
      show Repr nm _ u (.var (Sorts.rep k μ w))
      rw [this]
      exact .var h2
    · cases h3 : firstOf ((List.range k).map fun v => (v, μ v)) v with
      | none =>
        rw [hM] at h3
        have : Sorts.rep k μ v = v := by
          unfold Sorts.rep
          rw [h3]
          rfl
        simp only [this]
      | some v' =>
        obtain ⟨q, u, h1, h2⟩ := hT2.complete v v' h3
        rw [hv q h1] at h2
        cases h2
  have hpc := pending_card_le (nm := nm) s3.nodes.val (tbl s3 .A)
    (encList (nm none) ((List.range k).map μ)).subs
  step with rebuild_spec hnm s3 .Map vals (t := encList (nm none) ((List.range k).map μ))
    (σ := fun w => .var (Sorts.rep k μ w)) (encList (nm none) ((List.range k).map μ)).subs d3
    (by rw [hn3]; exact hvals) hleaf (by intro q v hq; rw [d4] at hq; cases hq)
    (Finset.Subset.refl _) (by unfold Room; omega) as ⟨r, s4, h4⟩
  have hc4 := h4.cost
  refine ⟨h4.inv, (Extends.of_eq hn3 (by omega)).trans h4.ext, by simp only [orientCost]; omega,
    ?_⟩
  have := h4.repr
  rw [encList_bind, List.map_map] at this
  exact this

/-! ## Pushing the sorts of the variables onto their values -/

/-- The ticks of a loop that spends `c` in each of `n` rounds. -/
def repCost (c : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => c + repCost c n

/-- The ticks one sort pushed onto a pattern may take, with the atoms put
in front of a list. -/
noncomputable def pushOne (S : Sorts) (Ns : Finset Name) (p : Pat) : Nat :=
  pushCost S Ns p + 2 * (Ns.card * p.subs.card) + 2

theorem atoms_length_le {Ns : Finset Name} {P : Finset Pat} {A : Sorts.Atoms} (hnd : A.Nodup)
    (h : ∀ a ∈ A, a.2 ∈ Ns ∧ Term.var a.1 ∈ P) : A.length ≤ Ns.card * P.card := by
  rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun a => (a.2, (Term.var a.1 : Pat))) ?_ ?_
  · intro a ha
    have := h a (List.mem_toFinset.1 ha)
    exact Finset.mem_product.2 ⟨this.1, this.2⟩
  · intro a _ b _ e
    simp only [Prod.mk.injEq, Term.var.injEq] at e
    exact Prod.ext e.2 e.1

theorem holds_reverse {S : Sorts} {A : Sorts.Atoms} {σ : Nat → GTerm} :
    Sorts.Atoms.Holds S A.reverse σ ↔ Sorts.Atoms.Holds S A σ := by
  simp only [Sorts.Atoms.Holds, List.mem_reverse]

/-- What pushing the sorts of a list onto a pattern gives: atoms in front
of the ones there were that hold exactly when the instance of the pattern
is in every sort of the list, or nothing when one of the sorts has no
instance of the pattern. -/
def PushRes (nm : Option Nat → RwLog.Sym) (S : Sorts) (Ns : Finset Name)
    (nodes : List store.Node) (ns : List Name) (p0 : Pat) (acc : Sorts.Atoms) (ok : Bool)
    (out : store.TermId) : Prop :=
  if ok then ∃ A : Sorts.Atoms,
      Repr nm nodes out.val (encList (nm none) ((A ++ acc).map atomPat)) ∧
      (∀ a ∈ A, a.2 ∈ Ns ∧ Term.var a.1 ∈ p0.subs) ∧
      A.length ≤ ns.length * (Ns.card * p0.subs.card) ∧
      ∀ σ : Nat → GTerm, (∀ n ∈ ns, Sorts.mem S n (p0.bind σ) = true) ↔ Sorts.Atoms.Holds S A σ
  else ∃ n ∈ ns, ∀ σ : Nat → GTerm, Sorts.mem S n (p0.bind σ) = false

theorem PushRes.cons {S : Sorts} {Ns : Finset Name} {nodes : List store.Node} {n : Name}
    {ns : List Name} {p0 : Pat} {acc A1 : Sorts.Atoms} {ok : Bool} {out : store.TermId}
    (hA1 : ∀ a ∈ A1, a.2 ∈ Ns ∧ Term.var a.1 ∈ p0.subs)
    (hlen1 : A1.length ≤ Ns.card * p0.subs.card)
    (hsem : ∀ σ : Nat → GTerm, Sorts.mem S n (p0.bind σ) = true ↔ Sorts.Atoms.Holds S A1 σ)
    (h : PushRes nm S Ns nodes ns p0 (A1.reverse ++ acc) ok out) :
    PushRes nm S Ns nodes (n :: ns) p0 acc ok out := by
  cases ok with
  | true =>
    simp only [PushRes, ↓reduceIte] at h ⊢
    obtain ⟨A, hr, hA, hlen, hs⟩ := h
    refine ⟨A ++ A1.reverse, by rw [List.append_assoc]; exact hr, ?_, ?_, fun σ => ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hA a ha
      · exact hA1 a (List.mem_reverse.1 ha)
    · simp only [List.length_append, List.length_reverse, List.length_cons, Nat.succ_mul]
      omega
    · rw [Sorts.Atoms.holds_append, holds_reverse, ← hs σ, ← hsem σ, List.forall_mem_cons]
      exact and_comm
  | false =>
    simp only [PushRes, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨m, hm, hσ⟩ := h
    exact ⟨m, List.mem_cons_of_mem _ hm, hσ⟩

theorem push_conj_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name) (p0 : Pat) (hfo : p0.firstOrder = true)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (decls p : store.TermId) :
    ∀ (ns : List Name) (s : store.Store) (out c : store.TermId) (acc : Sorts.Atoms),
    Inv s → Repr nm s.nodes.val decls.val sp → Repr nm s.nodes.val p.val p0 →
    Repr nm s.nodes.val c.val (namesPat (nm none) ns) →
    Repr nm s.nodes.val out.val (encList (nm none) (acc.map atomPat)) → (∀ n ∈ ns, n ∈ Ns) →
    Room s (repCost (pushOne S Ns p0) ns.length) →
    sorts.push_conj_loop s decls p out c true true ⦃ s' out' ok' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + repCost (pushOne S Ns p0) ns.length ∧
        PushRes nm S Ns s'.nodes.val ns p0 acc ok' out' ⦄ := by
  intro ns
  induction ns with
  | nil =>
    intro s out c acc hI hd hp hc hout hin hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, repCost] at hroom'
    unfold sorts.push_conj_loop
    rw [loop]
    simp only [sorts.push_conj_loop.body, ↓reduceIte]
    step with uncons_repr s c hI.toWf (p := Term.sym (nm none)) hc (by unfold Room; omega)
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
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega),
      by simp only [List.length_nil, repCost]; omega, ?_⟩
    simp only [PushRes, ↓reduceIte]
    exact ⟨[], (by rw [K1.nodes]; exact hout), fun a ha => (by cases ha), (by simp), fun σ => (by
      simp [Sorts.Atoms.Holds])⟩
  | cons n ns ih =>
    intro s out c acc hI hd hp hc hout hin hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, repCost] at hroom'
    have hP1 : pushOne S Ns p0 = pushCost S Ns p0 + 2 * (Ns.card * p0.subs.card) + 2 := rfl
    unfold sorts.push_conj_loop
    rw [loop]
    simp only [sorts.push_conj_loop.body, ↓reduceIte]
    step with uncons_repr s c hI.toWf (p := Term.app (Term.sym n) (namesPat (nm none) ns)) hc
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ni, rest, rfl, rn, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with push_sort_spec hnm S hS Ns p0 hfo (hin n List.mem_cons_self) hNs s1 decls ni p
      K1.inv (hx1.repr hd) (hx1.repr rn) (hx1.repr hp) (by unfold Room; omega)
      as ⟨r1, hI2, hx2, hA2, ht2, hres⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hI2 hx2 hA2 ht2 hres
    have hx02 := hx1.trans hx2
    cases o1 with
    | none =>
      simp only at hres
      simp only [uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hI2, hx02, by simp only [List.length_cons, repCost]; omega, ?_⟩
      simp only [PushRes, Bool.false_eq_true, ↓reduceIte]
      exact ⟨n, List.mem_cons_self, hres⟩
    | some atoms =>
      simp only at hres
      obtain ⟨A1, hrA, hnd, hA1, hsem⟩ := hres
      have hlen := atoms_length_le hnd hA1
      simp only [uncurry]
      step with rev_onto_spec (A1.map atomPat) (acc.map atomPat) s2 atoms out hI2.toWf hrA
        (hx02.repr hout) (by simp only [List.length_map]; unfold Room; omega) as ⟨r3, hR, hr3⟩
      obtain ⟨out1, s3⟩ := r3
      simp only [List.length_map] at hR hr3
      have ht3 := hR.ticks
      have hI3 : Inv s3 := ⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩
      have hx03 := hx02.trans hR.ext
      simp only [uncurry, bind_ok]
      have IH := ih s3 out1 rest (A1.reverse ++ acc) hI3 (hx03.repr hd) (hx03.repr hp)
        (hx03.repr rrest) (by simpa [List.map_append, List.map_reverse] using hr3)
        (fun m hm => hin m (List.mem_cons_of_mem _ hm)) (by unfold Room; omega)
      unfold sorts.push_conj_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out', ok'⟩ ⟨hI', hx', ht', hP⟩
      exact ⟨hI', hx03.trans hx', by simp only [List.length_cons, repCost]; omega,
        hP.cons hA1 hlen hsem⟩

/-- `push_conj` pushes each sort of a conjunction onto a pattern. -/
theorem push_conj_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name) (p0 : Pat) (hfo : p0.firstOrder = true)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (ns : List Name) (s : store.Store) (decls c p out : store.TermId) (acc : Sorts.Atoms)
    (hI : Inv s) (hd : Repr nm s.nodes.val decls.val sp) (hp : Repr nm s.nodes.val p.val p0)
    (hc : Repr nm s.nodes.val c.val (namesPat (nm none) ns))
    (hout : Repr nm s.nodes.val out.val (encList (nm none) (acc.map atomPat)))
    (hin : ∀ n ∈ ns, n ∈ Ns) (hroom : Room s (repCost (pushOne S Ns p0) ns.length)) :
    sorts.push_conj s decls c p out ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + repCost (pushOne S Ns p0) ns.length ∧
        match o with
        | some l => PushRes nm S Ns s'.nodes.val ns p0 acc true l
        | none => ∃ n ∈ ns, ∀ σ : Nat → GTerm, Sorts.mem S n (p0.bind σ) = false ⦄ := by
  unfold sorts.push_conj
  step with push_conj_loop_spec hnm S hS Ns p0 hfo hNs decls p ns s out c acc hI hd hp hc hout
    hin hroom as ⟨s1, out1, ok1, hI1, hx1, ht1, hP⟩
  cases ok1 with
  | true =>
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨hI1, hx1, ht1, hP⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [PushRes, Bool.false_eq_true, ↓reduceIte] at hP
    exact ⟨hI1, hx1, ht1, hP⟩

/-- A bound on the number of atoms the sorts of the variables of a list put
on the variables of their values. -/
noncomputable def atomsBound (Ns : Finset Name) (U : List Name) :
    List (Sorts.Conj × Pat) → Nat
  | [] => 0
  | b :: L => (conjList U (· ∈ b.1)).length * (Ns.card * b.2.subs.card) + atomsBound Ns U L

/-- What pushing the sorts of each variable onto its value gives. -/
def AllRes (nm : Option Nat → RwLog.Sym) (S : Sorts) (Ns : Finset Name) (U : List Name)
    (nodes : List store.Node) (L : List (Sorts.Conj × Pat)) (acc : Sorts.Atoms) (ok : Bool)
    (out : store.TermId) : Prop :=
  if ok then ∃ A : Sorts.Atoms,
      Repr nm nodes out.val (encList (nm none) ((A ++ acc).map atomPat)) ∧
      (∀ a ∈ A, a.2 ∈ Ns ∧ ∃ b ∈ L, Term.var a.1 ∈ b.2.subs) ∧ A.length ≤ atomsBound Ns U L ∧
      ∀ σ : Nat → GTerm, (∀ b ∈ L, ∀ n ∈ b.1, Sorts.mem S n (b.2.bind σ) = true) ↔
        Sorts.Atoms.Holds S A σ
  else ∃ b ∈ L, ∃ n ∈ b.1, ∀ σ : Nat → GTerm, Sorts.mem S n (b.2.bind σ) = false

theorem AllRes.cons {S : Sorts} {Ns : Finset Name} {U : List Name} {nodes : List store.Node}
    {b : Sorts.Conj × Pat} {L : List (Sorts.Conj × Pat)} {acc A1 : Sorts.Atoms} {ok : Bool}
    {out : store.TermId} (hA1 : ∀ a ∈ A1, a.2 ∈ Ns ∧ Term.var a.1 ∈ b.2.subs)
    (hlen1 : A1.length ≤ (conjList U (· ∈ b.1)).length * (Ns.card * b.2.subs.card))
    (hsem : ∀ σ : Nat → GTerm, (∀ n ∈ b.1, Sorts.mem S n (b.2.bind σ) = true) ↔
      Sorts.Atoms.Holds S A1 σ)
    (h : AllRes nm S Ns U nodes L (A1 ++ acc) ok out) :
    AllRes nm S Ns U nodes (b :: L) acc ok out := by
  cases ok with
  | true =>
    simp only [AllRes, ↓reduceIte] at h ⊢
    obtain ⟨A, hr, hA, hlen, hs⟩ := h
    refine ⟨A ++ A1, by rw [List.append_assoc]; exact hr, ?_, ?_, fun σ => ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨h1, b', hb', h2⟩ := hA a ha
        exact ⟨h1, b', List.mem_cons_of_mem _ hb', h2⟩
      · exact ⟨(hA1 a ha).1, b, List.mem_cons_self, (hA1 a ha).2⟩
    · simp only [List.length_append, atomsBound]
      omega
    · rw [Sorts.Atoms.holds_append, ← hs σ, ← hsem σ, List.forall_mem_cons]
      exact and_comm
  | false =>
    simp only [AllRes, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨b', hb', hσ⟩ := h
    exact ⟨b', List.mem_cons_of_mem _ hb', hσ⟩

/-- The ticks pushing the sorts of the variables of a list onto their values
may take. -/
noncomputable def pushAllCost (S : Sorts) (Ns : Finset Name) (U : List Name) :
    List (Sorts.Conj × Pat) → Nat
  | [] => 1
  | b :: L => 2 + repCost (pushOne S Ns b.2) (conjList U (· ∈ b.1)).length + pushAllCost S Ns U L

theorem push_all_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (U : List Name) (decls : store.TermId) :
    ∀ (L : List (Sorts.Conj × Pat)) (s : store.Store) (out cs l : store.TermId)
      (acc : Sorts.Atoms),
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val cs.val (encList (nm none) (L.map fun b => cpat (nm none) U b.1)) →
    Repr nm s.nodes.val l.val (encList (nm none) (L.map fun b => b.2)) →
    Repr nm s.nodes.val out.val (encList (nm none) (acc.map atomPat)) →
    (∀ b ∈ L, Sub U b.1 ∧ (∀ n ∈ b.1, n ∈ Ns) ∧ b.2.firstOrder = true) →
    Room s (pushAllCost S Ns U L) →
    sorts.push_all_loop s decls out cs l true true ⦃ s' out' ok' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + pushAllCost S Ns U L ∧
        AllRes nm S Ns U s'.nodes.val L acc ok' out' ⦄ := by
  intro L
  induction L with
  | nil =>
    intro s out cs l acc hI hd hcs hl hout hL hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [pushAllCost] at hroom'
    unfold sorts.push_all_loop
    rw [loop]
    simp only [sorts.push_all_loop.body, ↓reduceIte]
    step with uncons_repr s cs hI.toWf (p := Term.sym (nm none)) hcs (by unfold Room; omega)
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
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [pushAllCost]; omega, ?_⟩
    simp only [AllRes, ↓reduceIte]
    exact ⟨[], (by rw [K1.nodes]; exact hout), fun a ha => (by cases ha), (by simp), fun σ => (by
      simp [Sorts.Atoms.Holds])⟩
  | cons b L ih =>
    intro s out cs l acc hI hd hcs hl hout hL hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [pushAllCost] at hroom'
    obtain ⟨hsub, hbNs, hbfo⟩ := hL b List.mem_cons_self
    unfold sorts.push_all_loop
    rw [loop]
    simp only [sorts.push_all_loop.body, ↓reduceIte]
    step with uncons_repr s cs hI.toWf
      (p := Term.app (cpat (nm none) U b.1) (encList (nm none) (L.map fun b => cpat (nm none) U b.1)))
      hcs (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ci, crest, rfl, rc, rcrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with uncons_repr s1 l K1.inv.toWf
      (p := Term.app b.2 (encList (nm none) (L.map fun b => b.2))) (hx1.repr hl)
      (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1'
    obtain ⟨pi, lrest, rfl, rp, rlrest⟩ := hu1
    have K2 := hK1'.kept K1.inv
    have ht2 := K2.ticks
    have hx12 : Extends s1 s2 := Extends.of_eq K2.nodes (by omega)
    have hx2 : Extends s s2 := hx1.trans hx12
    step with push_conj_spec hnm S hS Ns b.2 hbfo hNs (conjList U (· ∈ b.1)) s2 decls ci pi out
      acc K2.inv (hx2.repr hd) (hx12.repr rp) (hx2.repr rc) (hx2.repr hout)
      (fun n hn => hbNs n (mem_conjList.1 hn).2) (by unfold Room; omega)
      as ⟨r3, hI3, hx3, ht3, hres⟩
    obtain ⟨o2, s3⟩ := r3
    simp only at hI3 hx3 ht3 hres
    have hx03 := hx2.trans hx3
    have hmem : ∀ n, n ∈ conjList U (· ∈ b.1) ↔ n ∈ b.1 := fun n =>
      ⟨fun h => (mem_conjList.1 h).2, fun h => mem_conjList.2 ⟨hsub n h, h⟩⟩
    cases o2 with
    | none =>
      simp only at hres
      obtain ⟨n, hn, hσ⟩ := hres
      simp only [uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hI3, hx03, by simp only [pushAllCost]; omega, ?_⟩
      simp only [AllRes, Bool.false_eq_true, ↓reduceIte]
      exact ⟨b, List.mem_cons_self, n, (hmem n).1 hn, hσ⟩
    | some o3 =>
      simp only [PushRes, ↓reduceIte] at hres
      obtain ⟨A1, hrA, hA1, hlen1, hsem⟩ := hres
      simp only [uncurry, bind_ok]
      have IH := ih s3 o3 crest lrest (A1 ++ acc) hI3 (hx03.repr hd)
        ((hx12.trans hx3).repr (hx1.repr rcrest)) (hx3.repr (hx12.repr rlrest)) hrA
        (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')) (by unfold Room; omega)
      unfold sorts.push_all_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', out', ok'⟩ ⟨hI', hx', ht', hP⟩
      refine ⟨hI', hx03.trans hx', by simp only [pushAllCost]; omega, hP.cons hA1 hlen1 fun σ => ?_⟩
      rw [← hsem σ]
      exact ⟨fun h n hn => h n ((hmem n).1 hn), fun h n hn => h n ((hmem n).2 hn)⟩

/-- `push_all` pushes each sort of each variable onto its value. -/
theorem push_all_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (U : List Name) (L : List (Sorts.Conj × Pat)) (s : store.Store)
    (decls cs l : store.TermId) (hI : Inv s) (hd : Repr nm s.nodes.val decls.val sp)
    (hcs : Repr nm s.nodes.val cs.val (encList (nm none) (L.map fun b => cpat (nm none) U b.1)))
    (hl : Repr nm s.nodes.val l.val (encList (nm none) (L.map fun b => b.2)))
    (hL : ∀ b ∈ L, Sub U b.1 ∧ (∀ n ∈ b.1, n ∈ Ns) ∧ b.2.firstOrder = true)
    (hroom : Room s (pushAllCost S Ns U L + 1)) :
    sorts.push_all s decls cs l ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + pushAllCost S Ns U L + 1 ∧
        match o with
        | some out => AllRes nm S Ns U s'.nodes.val L [] true out
        | none => ∃ b ∈ L, ∃ n ∈ b.1, ∀ σ : Nat → GTerm, Sorts.mem S n (b.2.bind σ) = false ⦄ := by
  unfold sorts.push_all
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨out, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with push_all_loop_spec hnm S hS Ns hNs U decls L s1 out cs l [] hI1 (hx1.repr hd)
    (hx1.repr hcs) (hx1.repr hl) (.nil hr1) hL (by unfold Room; omega)
    as ⟨s2, out1, ok1, hI2, hx2, ht2, hP⟩
  cases ok1 with
  | true =>
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨hI2, hx1.trans hx2, by omega, hP⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [AllRes, Bool.false_eq_true, ↓reduceIte] at hP
    exact ⟨hI2, hx1.trans hx2, by omega, hP⟩

/-! ## The sorts the atoms put on a variable -/

theorem ups_loop_spec (y : store.TermId) (yv : Nat) :
    ∀ (A : Sorts.Atoms) (s : store.Store) (l list : store.TermId) (xs : List Name),
    Inv s → VarAt s.nodes.val y.val yv →
    Repr nm s.nodes.val l.val (encList (nm none) (A.map atomPat)) →
    Repr nm s.nodes.val list.val (namesPat (nm none) xs) → Room s (4 * A.length + 1) →
    sorts.ups_loop l s y list ⦃ s' list' =>
      Inv s' ∧ Extends s s' ∧ tbl s' = tbl s ∧ s'.ticks.val ≤ s.ticks.val + 4 * A.length + 1 ∧
        ∃ xs', Repr nm s'.nodes.val list'.val (namesPat (nm none) xs') ∧
          xs'.length ≤ xs.length + A.length ∧ ∀ n, n ∈ xs' ↔ n ∈ xs ∨ (yv, n) ∈ A ⦄ := by
  intro A
  induction A with
  | nil =>
    intro s l list xs hI hy hl hlist hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil] at hroom'
    unfold sorts.ups_loop
    rw [loop]
    simp only [sorts.ups_loop.body]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hfin : Inv s1 ∧ Extends s s1 ∧ tbl s1 = tbl s ∧
        s1.ticks.val ≤ s.ticks.val + 4 * ([] : Sorts.Atoms).length + 1 ∧
        ∃ xs', Repr nm s1.nodes.val list.val (namesPat (nm none) xs') ∧
          xs'.length ≤ xs.length + ([] : Sorts.Atoms).length ∧
          ∀ n, n ∈ xs' ↔ n ∈ xs ∨ (yv, n) ∈ ([] : Sorts.Atoms) :=
      ⟨K1.inv, Extends.of_eq K1.nodes (by omega), K1.tbl, by simp only [List.length_nil]; omega,
        xs, by rw [K1.nodes]; exact hlist, by simp, by simp⟩
    step*
  | cons a A ih =>
    intro s l list xs hI hy hl hlist hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.ups_loop
    rw [loop]
    simp only [sorts.ups_loop.body]
    step with uncons_repr s l hI.toWf
      (p := Term.app (atomPat a) (encList (nm none) (A.map atomPat))) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ai, rest, rfl, ra, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with uncons_repr s1 ai K1.inv.toWf (p := Term.app (Term.var a.1) (Term.sym a.2))
      (hx1.repr ra) (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1'
    obtain ⟨vi, ni, rfl, rv, rn⟩ := hu1
    have K2 := hK1'.kept K1.inv
    have ht2 := K2.ticks
    have hx2 : Extends s s2 := hx1.trans (Extends.of_eq K2.nodes (by omega))
    have hvv : VarAt s2.nodes.val vi.val a.1 := by
      rw [K2.nodes]
      cases rv with
      | var h => exact h
    step with same_spec s2 vi y K2.inv (by unfold Room; omega) as ⟨r2, hb, hK2⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hb hK2
    have K3 := hK2
    have ht3 := K3.ticks
    have hx3 : Extends s s3 := hx2.trans (Extends.of_eq K3.nodes (by omega))
    have htb3 : tbl s3 = tbl s := by rw [K3.tbl, K2.tbl, K1.tbl]
    subst hb
    by_cases hq : vi.val = y.val
    · have hae : a.1 = yv := by
        rw [hq] at hvv
        exact hvv.unique (hx2.varAt hy)
      simp only [hq, decide_true, ↓reduceIte, uncurry]
      step with alloc_spec s3 (.App ni list) K3.inv
        ⟨by rw [K3.nodes, K2.nodes]; exact rn.lt, by rw [K3.nodes, K2.nodes, K1.nodes]; exact hlist.lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨list1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      have hx04 := hx3.trans hx4
      have hlist1 : Repr nm s4.nodes.val list1.val (namesPat (nm none) (a.2 :: xs)) :=
        .app hr4 (hx4.repr (by rw [K3.nodes, K2.nodes]; exact rn)) (hx04.repr hlist)
      simp only [uncurry, bind_ok]
      have IH := ih s4 rest list1 (a.2 :: xs) hI4 (hx04.varAt hy) (hx04.repr rrest) hlist1
        (by unfold Room; omega)
      unfold sorts.ups_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', list'⟩ ⟨hI', hx', htb', ht', xs', hr', hlen', hm'⟩
      refine ⟨hI', hx04.trans hx', by rw [htb', htb4, htb3], by simp only [List.length_cons]; omega,
        xs', hr', by simp only [List.length_cons] at hlen' ⊢; omega, fun n => ?_⟩
      rw [hm' n, List.mem_cons, List.mem_cons]
      constructor
      · rintro ((rfl | h) | h)
        · exact Or.inr (Or.inl (Prod.ext hae.symm rfl))
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (by rw [← h]))
        · exact Or.inr h
    · have hae : a.1 ≠ yv := by
        rintro rfl
        exact hq (hvv.inj K2.inv.nodesOK (hx2.varAt hy))
      simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s3 rest list xs K3.inv (hx3.varAt hy) (hx3.repr rrest) (hx3.repr hlist)
        (by unfold Room; omega)
      unfold sorts.ups_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', list'⟩ ⟨hI', hx', htb', ht', xs', hr', hlen', hm'⟩
      refine ⟨hI', hx3.trans hx', by rw [htb', htb3], by simp only [List.length_cons]; omega,
        xs', hr', by simp only [List.length_cons]; omega, fun n => ?_⟩
      rw [hm' n, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact absurd (by rw [← h]) hae
        · exact Or.inr h

/-- The ticks `ups` may take with `u` names and `a` atoms. -/
def upsCost (u a : Nat) : Nat := 6 * a + 3 * u + 6

/-- `ups` gives the conjunction of the sorts the atoms put on a variable. -/
theorem ups_spec (hnm : Function.Injective nm) (U : List Name) (A : Sorts.Atoms)
    (s : store.Store) (names atoms y : store.TermId) {yv : Nat} (hI : Inv s)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hA : Repr nm s.nodes.val atoms.val (encList (nm none) (A.map atomPat)))
    (hy : VarAt s.nodes.val y.val yv) (hroom : Room s (upsCost U.length A.length)) :
    sorts.ups s names atoms y ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' .B = tbl s .B ∧
        s'.ticks.val ≤ s.ticks.val + upsCost U.length A.length ∧
        Repr nm s'.nodes.val r.val (cpat (nm none) U (Sorts.upsOf A yv)) ⦄ := by
  unfold sorts.ups
  have hroom' := hroom
  unfold Room at hroom'
  simp only [upsCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨list, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with ups_loop_spec (nm := nm) y yv A s1 atoms list [] hI1 (hx1.varAt hy) (hx1.repr hA)
    (.nil hr1) (by unfold Room; omega) as ⟨s2, list1, hI2, hx2, htb2, ht2, xs', hr2, hlen2, hm2⟩
  simp only [List.length_nil, Nat.zero_add] at hlen2
  step with conj_of_spec hnm U xs' s2 names list1 hI2.toWf ((hx1.trans hx2).repr hU) hr2
    (by unfold Room; omega) as ⟨r, s3, hR, hr3⟩
  have ht3 := hR.ticks
  refine ⟨⟨hR.wf, by rw [hR.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR.ext,
    by rw [hR.tbl, htb2, htb1], by simp only [upsCost]; omega, ?_⟩
  have e : conjList U (· ∈ xs') = conjList U (· ∈ Sorts.upsOf A yv) :=
    conjList_congr fun n _ => by rw [hm2 n, Sorts.mem_upsOf]; simp
  unfold cpat
  rw [← e]
  exact hr3

/-! ## Binding the free variables left with one value -/

/-- The variables of the list become what `τ` says; any other stays. -/
def subOn (τ : Nat → Pat) (R : List Nat) (y : Nat) : Pat := if y ∈ R then τ y else .var y

theorem single_self (y : Nat) : Term.single y (Term.var y : Pat) = Term.var := by
  funext w
  by_cases h : w = y
  · simp [Term.single, h]
  · simp [Term.single, h]

theorem toPat_lift (g : GTerm) : GTerm.toPat g = Term.lift g := by
  unfold GTerm.toPat Term.lift Term.rename
  exact Term.bind_congr fun v _ => v.elim

theorem oneSub_cases (S : Sorts) (k : Nat) (ν : Nat → Pat) (C : Nat → Sorts.Conj) (y : Nat) :
    Sorts.oneSub S k ν C y = .var y ∨ ∃ g : GTerm, Sorts.oneSub S k ν C y = Term.lift g := by
  by_cases h : y < k ∧ ν y = .var y
  · cases hc : Sorts.count S (C y) with
    | none => exact Or.inl (Sorts.oneSub_none fun g hg => by rw [hc] at hg; cases hg)
    | many => exact Or.inl (Sorts.oneSub_none fun g hg => by rw [hc] at hg; cases hg)
    | one g => exact Or.inr ⟨g, Sorts.oneSub_one h.1 h.2 hc⟩
  · exact Or.inl (Sorts.oneSub_not h)

theorem bind_subOn_cons {τ : Nat → Pat}
    (hτ : ∀ y, τ y = .var y ∨ ∃ g : GTerm, τ y = Term.lift g) {R : List Nat} {y : Nat}
    (hy : y ∉ R) (t : Pat) :
    (t.bind (Term.single y (τ y))).bind (subOn τ R) = t.bind (subOn τ (y :: R)) := by
  rw [Term.bind_bind]
  refine Term.bind_congr fun w _ => ?_
  by_cases hw : w = y
  · subst hw
    simp only [Term.single, ↓reduceIte, subOn, List.mem_cons, true_or]
    rcases hτ w with e | ⟨g, e⟩
    · rw [e]
      simp [subOn, hy]
    · rw [e]
      exact Sorts.lift_bind_pat g _
  · simp [Term.single, hw, subOn, List.mem_cons]

theorem subOn_range (S : Sorts) (k : Nat) (ν : Nat → Pat) (C : Nat → Sorts.Conj) :
    subOn (Sorts.oneSub S k ν C) (List.range k) = Sorts.oneSub S k ν C := by
  funext y
  by_cases hy : y < k
  · simp [subOn, hy]
  · simp only [subOn, List.mem_range, hy, ↓reduceIte]
    exact (Sorts.oneSub_not fun h => hy h.1).symm

/-- What the loop of `close` gives on the variables of a list: nothing when
one of them has no value in its sorts; the values with each replaced as `τ`
says otherwise. -/
def CloseRes (nm : Option Nat → RwLog.Sym) (S : Sorts) (nodes : List store.Node)
    (C : Nat → Sorts.Conj) (τ : Nat → Pat) (R : List Nat) (Tc : Pat) (ok : Bool)
    (vals : store.TermId) : Prop :=
  if ok then (∀ y ∈ R, Sorts.count S (C y) ≠ .none) ∧ Repr nm nodes vals.val (Tc.bind (subOn τ R))
  else ∃ y ∈ R, Sorts.count S (C y) = .none

theorem CloseRes.cons {S : Sorts} {nodes : List store.Node} {C : Nat → Sorts.Conj}
    {τ : Nat → Pat} (hτ : ∀ y, τ y = .var y ∨ ∃ g : GTerm, τ y = Term.lift g) {y : Nat}
    {R : List Nat} {Tc : Pat} {ok : Bool} {vals : store.TermId} (hy : y ∉ R)
    (hc : Sorts.count S (C y) ≠ .none)
    (h : CloseRes nm S nodes C τ R (Tc.bind (Term.single y (τ y))) ok vals) :
    CloseRes nm S nodes C τ (y :: R) Tc ok vals := by
  cases ok with
  | true =>
    simp only [CloseRes, ↓reduceIte] at h ⊢
    exact ⟨List.forall_mem_cons.2 ⟨hc, h.1⟩, by rw [← bind_subOn_cons hτ hy]; exact h.2⟩
  | false =>
    simp only [CloseRes, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨y', hy', h'⟩ := h
    exact ⟨y', List.mem_cons_of_mem _ hy', h'⟩

/-- The ticks the loop of `close` may take on the variables of a list, with
`u` names, conjunctions that reach at most `rc`, `a` atoms and the values
`Tc`. -/
noncomputable def closeCost (S : Sorts) (u rc a : Nat) (τ : Nat → Pat) : List Nat → Pat → Nat
  | [], _ => 1
  | y :: R, Tc => upsCost u a + countCost S u rc + 14 * Tc.subs.card + 9 +
      closeCost S u rc a τ R (Tc.bind (Term.single y (τ y)))

theorem close_loop_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) (k : Nat) (ν : Nat → Pat) (A : Sorts.Atoms) (hAU : ∀ a ∈ A, a.2 ∈ U)
    {a : Nat} (hAa : A.length ≤ a) {rc : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc) (decls names atoms : store.TermId) :
    ∀ (R : List Nat) (s : store.Store) (vals vs l : store.TermId) (Tc : Pat),
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val atoms.val (encList (nm none) (A.map atomPat)) →
    Repr nm s.nodes.val vs.val (encList (nm none) (R.map Term.var)) →
    Repr nm s.nodes.val l.val (encList (nm none) (R.map ν)) → Repr nm s.nodes.val vals.val Tc →
    R.Nodup → (∀ y ∈ R, y < k) →
    Room s (closeCost S U.length rc a (Sorts.oneSub S k ν (Sorts.upsOf A)) R Tc) →
    sorts.close_loop s decls names atoms vals vs l true true ⦃ s' vals' ok' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val +
          closeCost S U.length rc a (Sorts.oneSub S k ν (Sorts.upsOf A)) R Tc ∧
        CloseRes nm S s'.nodes.val (Sorts.upsOf A) (Sorts.oneSub S k ν (Sorts.upsOf A)) R Tc ok'
          vals' ⦄ := by
  have hτ := oneSub_cases S k ν (Sorts.upsOf A)
  intro R
  induction R with
  | nil =>
    intro s vals vs l Tc hI hd hU hA hvs hl hvals hnd hlt hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [closeCost] at hroom'
    unfold sorts.close_loop
    rw [loop]
    simp only [sorts.close_loop.body, ↓reduceIte]
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
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [closeCost]; omega, ?_⟩
    simp only [CloseRes, ↓reduceIte]
    refine ⟨fun y hy => (by cases hy), ?_⟩
    have e : subOn (Sorts.oneSub S k ν (Sorts.upsOf A)) [] = Term.var := by
      funext y
      simp [subOn]
    rw [e, Term.bind_var_id, K1.nodes]
    exact hvals
  | cons y R ih =>
    intro s vals vs l Tc hI hd hU hA hvs hl hvals hnd hlt hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [closeCost, upsCost] at hroom'
    rw [List.nodup_cons] at hnd
    have hyk := hlt y List.mem_cons_self
    unfold sorts.close_loop
    rw [loop]
    simp only [sorts.close_loop.body, ↓reduceIte]
    step with uncons_repr s vs hI.toWf
      (p := Term.app (Term.var y) (encList (nm none) (R.map Term.var))) hvs
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨yi, vrest, rfl, ry, rvrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with uncons_repr s1 l K1.inv.toWf
      (p := Term.app (ν y) (encList (nm none) (R.map ν))) (hx1.repr hl)
      (by unfold Room; omega) as ⟨r1, hK1', hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1'
    obtain ⟨pi, lrest, rfl, rp, rlrest⟩ := hu1
    have K2 := hK1'.kept K1.inv
    have ht2 := K2.ticks
    have hx12 : Extends s1 s2 := Extends.of_eq K2.nodes (by omega)
    have hx2 : Extends s s2 := hx1.trans hx12
    have hyv : VarAt s.nodes.val yi.val y := by
      cases ry with
      | var h => exact h
    step with ups_spec hnm U A s2 names atoms yi K2.inv (hx2.repr hU) (hx2.repr hA)
      (hx2.varAt hyv) (by unfold Room; simp only [upsCost]; omega)
      as ⟨r3, hI3, hx3, hB3, ht3, hr3⟩
    obtain ⟨ci, s3⟩ := r3
    simp only [upsCost] at hI3 hx3 hB3 ht3 hr3
    have hx03 := hx2.trans hx3
    have hsub : Sub U (Sorts.upsOf A y) := fun n hn => hAU _ (Sorts.mem_upsOf.1 hn)
    have hmono := countCost_mono S U.length (hr (Sorts.upsOf A y))
    step with count_spec hC (Sorts.upsOf A y) hsub s3 decls names ci hI3 (hx03.repr hd)
      (hx03.repr hU) hr3 (by unfold Room; omega) as ⟨r4, hI4, hx4, ht4, hres⟩
    obtain ⟨cnt, s4⟩ := r4
    simp only at hI4 hx4 ht4 hres
    have hx04 := hx03.trans hx4
    have hrest4 : Repr nm s4.nodes.val vrest.val (encList (nm none) (R.map Term.var)) :=
      hx04.repr rvrest
    have hlrest4 : Repr nm s4.nodes.val lrest.val (encList (nm none) (R.map ν)) :=
      (hx3.trans hx4).repr (hx12.repr rlrest)
    cases cnt with
    | None =>
      simp only at hres
      simp only [uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hI4, hx04, by simp only [closeCost, upsCost]; omega, ?_⟩
      simp only [CloseRes, Bool.false_eq_true, ↓reduceIte]
      exact ⟨y, List.mem_cons_self, hres⟩
    | Many =>
      simp only at hres
      have hone : Sorts.oneSub S k ν (Sorts.upsOf A) y = .var y :=
        Sorts.oneSub_none fun g hg => by rw [hres] at hg; cases hg
      simp only [uncurry, bind_ok]
      have IH := ih s4 vals vrest lrest
        (Tc.bind (Term.single y (Sorts.oneSub S k ν (Sorts.upsOf A) y))) hI4 (hx04.repr hd)
        (hx04.repr hU) (hx04.repr hA) hrest4 hlrest4
        (by rw [hone, single_self, Term.bind_var_id]; exact hx04.repr hvals) hnd.2
        (fun y' hy' => hlt y' (List.mem_cons_of_mem _ hy')) (by unfold Room; omega)
      unfold sorts.close_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨s', vals', ok'⟩ ⟨hI', hx', ht', hP⟩
      exact ⟨hI', hx04.trans hx', by simp only [closeCost, upsCost]; omega,
        hP.cons hτ hnd.1 (by rw [hres]; simp)⟩
    | One g =>
      simp only at hres
      obtain ⟨t, hct, rg⟩ := hres
      rw [toPat_lift] at rg
      simp only [uncurry]
      step with same_spec s4 pi yi hI4 (by unfold Room; omega) as ⟨r5, hb, hK5⟩
      obtain ⟨b, s5⟩ := r5
      simp only at hb hK5
      have ht5 := hK5.ticks
      have hx45 : Extends s4 s5 := Extends.of_eq hK5.nodes (by omega)
      have hx05 := hx04.trans hx45
      subst hb
      by_cases hq : pi.val = yi.val
      · have hν : ν y = .var y := by
          have h1 : Repr nm s1.nodes.val yi.val (ν y) := by rw [← hq]; exact rp
          exact h1.unique (.var (hx1.varAt hyv))
        have hone : Sorts.oneSub S k ν (Sorts.upsOf A) y = Term.lift t :=
          Sorts.oneSub_one hyk hν hct
        simp only [hq, decide_true, ↓reduceIte, uncurry]
        step with clear_spec s5 .A hK5.inv (by unfold Room; omega) as ⟨s6, c1, c2, c3, c4, c5⟩
        have hx56 : Extends s5 s6 := Extends.of_eq c1 (by omega)
        have hx06 := hx05.trans hx56
        have hpc := pending_card_le (nm := nm) s6.nodes.val (tbl s6 .A) Tc.subs
        step with rebuild_spec hnm s6 (.Sub yi g) vals (t := Tc)
          (σ := Term.single y (Term.lift t)) Tc.subs c3 (hx06.repr hvals)
          ⟨y, Term.lift t, hx06.varAt hyv, (hx45.trans hx56).repr rg, rfl⟩
          (by intro q v hq'; rw [c4] at hq'; cases hq') (Finset.Subset.refl _)
          (by unfold Room; omega) as ⟨r7, h7⟩
        obtain ⟨vals1, s7⟩ := r7
        simp only at h7
        have hc7 := h7.cost
        have hx07 := hx06.trans h7.ext
        simp only [uncurry, bind_ok]
        have IH := ih s7 vals1 vrest lrest
          (Tc.bind (Term.single y (Sorts.oneSub S k ν (Sorts.upsOf A) y))) h7.inv (hx07.repr hd)
          (hx07.repr hU) (hx07.repr hA) (((hx45.trans hx56).trans h7.ext).repr hrest4)
          (((hx45.trans hx56).trans h7.ext).repr hlrest4) (by rw [hone]; exact h7.repr) hnd.2
          (fun y' hy' => hlt y' (List.mem_cons_of_mem _ hy')) (by unfold Room; omega)
        unfold sorts.close_loop at IH
        refine WP.spec_mono IH ?_
        rintro ⟨s', vals', ok'⟩ ⟨hI', hx', ht', hP⟩
        exact ⟨hI', hx07.trans hx', by simp only [closeCost, upsCost]; omega,
          hP.cons hτ hnd.1 (by rw [hct]; simp)⟩
      · have hν : ν y ≠ .var y := by
          intro e
          apply hq
          rw [e] at rp
          exact Repr.inj hnm K1.inv.nodesOK rp (.var (hx1.varAt hyv))
        have hone : Sorts.oneSub S k ν (Sorts.upsOf A) y = .var y :=
          Sorts.oneSub_not fun h => hν h.2
        simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
        have IH := ih s5 vals vrest lrest
          (Tc.bind (Term.single y (Sorts.oneSub S k ν (Sorts.upsOf A) y))) hK5.inv
          (hx05.repr hd) (hx05.repr hU) (hx05.repr hA) (hx45.repr hrest4) (hx45.repr hlrest4)
          (by rw [hone, single_self, Term.bind_var_id]; exact hx05.repr hvals) hnd.2
          (fun y' hy' => hlt y' (List.mem_cons_of_mem _ hy')) (by unfold Room; omega)
        unfold sorts.close_loop at IH
        refine WP.spec_mono IH ?_
        rintro ⟨s', vals', ok'⟩ ⟨hI', hx', ht', hP⟩
        exact ⟨hI', hx05.trans hx', by simp only [closeCost, upsCost]; omega,
          hP.cons hτ hnd.1 (by rw [hct]; simp)⟩

/-- A bound on the ticks of the loop of `close` that does not depend on the
values bound: `c` ticks and a rebuild in each of the rounds, on values
that start with `d` subterms and gain at most `m` in a round. -/
def closeCostU (c m : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, d => c + 14 * d + closeCostU c m n (d + m)

theorem closeCost_le (S : Sorts) (u rc a : Nat) {τ : Nat → Pat} {m : Nat}
    (hm : ∀ y, (τ y).subs.card ≤ m) : ∀ (R : List Nat) (Tc : Pat) (d : Nat), Tc.subs.card ≤ d →
    closeCost S u rc a τ R Tc ≤ closeCostU (upsCost u a + countCost S u rc + 9) m R.length d
  | [], _, _, _ => by simp [closeCost, closeCostU]
  | y :: R, Tc, d, hd => by
    have h1 : (Tc.bind (Term.single y (τ y))).subs.card ≤ d + m := by
      refine (Finset.card_le_card (Term.subs_bind_single y (τ y) Tc)).trans ?_
      refine (Finset.card_union_le _ _).trans ?_
      have := Finset.card_image_le (s := Tc.subs) (f := Term.bind (Term.single y (τ y)))
      have := hm y
      omega
    have := closeCost_le S u rc a hm R _ _ h1
    simp only [closeCost, closeCostU, List.length_cons]
    omega

/-- `close` binds each free variable that the atoms leave one value to that
value, and gives nothing when they leave a variable no value. -/
theorem close_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) (k : Nat) (ν : Nat → Pat) (A : Sorts.Atoms) (hAU : ∀ a ∈ A, a.2 ∈ U)
    {a : Nat} (hAa : A.length ≤ a) {rc : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (s : store.Store) (decls names vs vals atoms : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hA : Repr nm s.nodes.val atoms.val (encList (nm none) (A.map atomPat)))
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo k)))
    (hvals : Repr nm s.nodes.val vals.val (encList (nm none) ((List.range k).map ν)))
    (hroom : Room s (closeCostU (upsCost U.length a + countCost S U.length rc + 9)
      (Sorts.soleMax S U) k (encList (nm none) ((List.range k).map ν)).subs.card)) :
    sorts.close s decls names vs vals atoms ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + closeCostU (upsCost U.length a + countCost S U.length rc + 9)
          (Sorts.soleMax S U) k (encList (nm none) ((List.range k).map ν)).subs.card ∧
        match o with
        | some res => (∀ y, y < k → Sorts.count S (Sorts.upsOf A y) ≠ .none) ∧
            Repr nm s'.nodes.val res.val (encList (nm none)
              ((List.range k).map fun v => (ν v).bind (Sorts.oneSub S k ν (Sorts.upsOf A))))
        | none => ∃ y, y < k ∧ Sorts.count S (Sorts.upsOf A y) = .none ⦄ := by
  unfold sorts.close
  have hle := closeCost_le S U.length rc a (τ := Sorts.oneSub S k ν (Sorts.upsOf A))
    (Sorts.oneSub_subs_le (S := S) (k := k) (ν := ν) (C := Sorts.upsOf A) (U := U)
      fun y n hn => hAU _ (Sorts.mem_upsOf.1 hn))
    (List.range k) (encList (nm none) ((List.range k).map ν)) _ (Nat.le_refl _)
  rw [List.length_range] at hle
  have hroom' := hroom
  unfold Room at hroom'
  step with close_loop_spec hnm hC k ν A hAU hAa hr decls names atoms (List.range k) s vals vs
    vals (encList (nm none) ((List.range k).map ν)) hI hd hU hA hvs hvals hvals
    List.nodup_range (fun y hy => List.mem_range.1 hy) (by unfold Room; omega)
    as ⟨s1, vals1, ok1, hI1, hx1, ht1, hP⟩
  cases ok1 with
  | true =>
    simp only [↓reduceIte, WP.spec_ok]
    simp only [CloseRes, ↓reduceIte, subOn_range, encList_bind, List.map_map] at hP
    exact ⟨hI1, hx1, by omega, fun y hy => hP.1 y (List.mem_range.2 hy), hP.2⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [CloseRes, Bool.false_eq_true, ↓reduceIte] at hP
    obtain ⟨y, hy, hc⟩ := hP
    exact ⟨hI1, hx1, by omega, y, List.mem_range.1 hy, hc⟩

/-! ## `sorts::norm_ex` -/

/-- The sorts and the values of the variables of a store. -/
def valsOf (r : Sorts.Raw) (ν : Nat → Pat) : List (Sorts.Conj × Pat) :=
  (List.range r.c.length).map fun v => (r.conj v, ν v)

theorem range_map_conj (r : Sorts.Raw) : (List.range r.c.length).map r.conj = r.c := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [Sorts.Raw.conj, h2]

/-- The ticks `norm_ex` may take once the equations are solved. -/
noncomputable def afterSolve (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (rc : Nat)
    (r : Sorts.Raw) : Option (Nat → Pat) → Nat
  | none => 0
  | some μ =>
    orientCost r.c.length (encList (nm none) ((List.range r.c.length).map μ)) +
      pushAllCost S (Sorts.names S) U (valsOf r (Sorts.orient r.c.length μ)) + 1 +
      closeCostU (upsCost U.length
          (atomsBound (Sorts.names S) U (valsOf r (Sorts.orient r.c.length μ))) +
        countCost S U.length rc + 9) (Sorts.soleMax S U) r.c.length
        (encList (nm none) ((List.range r.c.length).map (Sorts.orient r.c.length μ))).subs.card

/-- The ticks `norm_ex` may take. -/
noncomputable def normExCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name)
    (rc : Nat) (r : Sorts.Raw) (E : Eqns Nat) : Nat :=
  solveCost E (encList (nm none) (varsTo r.c.length)) + afterSolve nm S U rc r (solve E)

theorem oneSub_apply {S : Sorts} {k : Nat} {θ : Sorts.Binds} {ν : Nat → Pat}
    (h : ∀ v, v < k → PSubst.apply θ v = ν v) (C : Nat → Sorts.Conj) :
    Sorts.oneSub S k (PSubst.apply θ) C = Sorts.oneSub S k ν C := by
  funext y
  by_cases hy : y < k
  · simp only [Sorts.oneSub, h y hy]
  · rw [Sorts.oneSub_not fun h' => hy h'.1, Sorts.oneSub_not fun h' => hy h'.1]

/-- `norm_ex` is the normal form of an exclusion (`Sorts.normEx`): the list
of the values its bindings give the variables of the store, or nothing when
it excludes nothing. -/
theorem norm_ex_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) {rc : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc) (r : Sorts.Raw)
    (hcN : ∀ v, ∀ n ∈ r.conj v, n ∈ Sorts.names S) (E : Eqns Nat) (hE : E.FO)
    (hEv : ∀ v ∈ E.vars, v < r.c.length) (s : store.Store)
    (decls names vs cs e : store.TermId) (hI : Inv s) (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hvs : Repr nm s.nodes.val vs.val (encList (nm none) (varsTo r.c.length)))
    (hcs : Repr nm s.nodes.val cs.val (encList (nm none) (r.c.map (cpat (nm none) U))))
    (he : Repr nm s.nodes.val e.val (encEqs nm E)) (hroom : Room s (normExCost nm S U rc r E)) :
    sorts.norm_ex s decls names vs cs e ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + normExCost nm S U rc r E ∧
        match o with
        | some res => ∃ θ, Sorts.normEx S r E = some θ ∧
            Repr nm s'.nodes.val res.val
              (encList (nm none) ((List.range r.c.length).map (PSubst.apply θ)))
        | none => Sorts.normEx S r E = none ⦄ := by
  unfold sorts.norm_ex
  have hroom' := hroom
  unfold Room at hroom'
  simp only [normExCost] at hroom'
  step with solve_into_spec hnm s e vs (E := E) (o := encList (nm none) (varsTo r.c.length)) hI he
    hvs (by unfold Room; omega) as ⟨ok1, solved, s1, hI1, hx1, ht1, hres⟩
  cases ok1 with
  | false =>
    simp only [SolveRes, Bool.false_eq_true, ↓reduceIte] at hres
    have hs : solve E = none := by simpa [Eqns.solveOn] using hres
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hI1, hx1, by simp only [normExCost]; omega, ?_⟩
    unfold Sorts.normEx
    rw [hs]
    rfl
  | true =>
    simp only [SolveRes, ↓reduceIte] at hres
    obtain ⟨o', ho', hso, -⟩ := hres
    cases hs : solve E with
    | none => rw [Eqns.solveOn, hs] at hso; cases hso
    | some μ =>
      rw [hs] at hroom'
      simp only [afterSolve] at hroom'
      have hne : Sorts.normEx S r E =
          Sorts.close S r (Sorts.bindsOf r.c.length (Sorts.orient r.c.length μ)) := by
        unfold Sorts.normEx
        rw [hs]
        rfl
      have ho'' : o' = encList (nm none) ((List.range r.c.length).map μ) := by
        rw [Eqns.solveOn, hs] at hso
        simp only [Option.map_some, Option.some.injEq] at hso
        rw [← hso, encList_bind, varsTo, List.map_map]
        rfl
      subst ho''
      simp only [↓reduceIte]
      step with orient_spec hnm r.c.length μ s1 vs solved hI1 (hx1.repr hvs) ho'
        (by unfold Room; omega) as ⟨vals, s2, hI2, hx2, ht2, hr2⟩
      have hx02 := hx1.trans hx2
      have hθ : Sorts.Pre r.c.length (Sorts.bindsOf r.c.length (Sorts.orient r.c.length μ)) :=
        Sorts.pre_solved hs hE hEv
      have hap : ∀ v, v < r.c.length →
          PSubst.apply (Sorts.bindsOf r.c.length (Sorts.orient r.c.length μ)) v =
            Sorts.orient r.c.length μ v := fun v hv => Sorts.apply_bindsOf hv
      have hNs : ∀ m ∈ Sorts.names S, ∀ f k ks, Sorts.step S m f k = some ks →
          ∀ m', some m' ∈ ks → m' ∈ Sorts.names S ∧ m' ≠ nm none := fun m _ f k ks hst m' hm' =>
        ⟨step_kid_names hst hm', hC.nz _ (step_kid_names hst hm')⟩
      have e1 : (valsOf r (Sorts.orient r.c.length μ)).map (fun b => cpat (nm none) U b.1) =
          r.c.map (cpat (nm none) U) := by
        conv_rhs => rw [← range_map_conj r]
        simp [valsOf, List.map_map, Function.comp_def]
      have e2 : (valsOf r (Sorts.orient r.c.length μ)).map (fun b => b.2) =
          (List.range r.c.length).map (Sorts.orient r.c.length μ) := by
        simp [valsOf, List.map_map, Function.comp_def]
      have hmemL : ∀ b ∈ valsOf r (Sorts.orient r.c.length μ),
          ∃ v, v < r.c.length ∧ b = (r.conj v, Sorts.orient r.c.length μ v) := by
        intro b hb
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
        exact ⟨v, List.mem_range.1 hv, rfl⟩
      step with push_all_spec hnm S hC.sorts (Sorts.names S) hNs U
        (valsOf r (Sorts.orient r.c.length μ)) s2 decls cs vals hI2 (hx02.repr hd)
        (by rw [e1]; exact hx02.repr hcs) (by rw [e2]; exact hr2)
        (by
          intro b hb
          obtain ⟨v, hv, rfl⟩ := hmemL b hb
          refine ⟨fun n hn => hC.names n (hcN v n hn), hcN v, ?_⟩
          rw [← hap v hv]
          exact hθ.apply_fo v)
        (by unfold Room; omega) as ⟨o, s3, hI3, hx3, ht3, hres3⟩
      have hx03 := hx02.trans hx3
      cases o with
      | none =>
        simp only at hres3
        obtain ⟨b, hb, n, hn, hσ⟩ := hres3
        obtain ⟨v, hv, rfl⟩ := hmemL b hb
        simp only [WP.spec_ok]
        refine ⟨hI3, hx03, by simp only [normExCost, hs, afterSolve]; omega, ?_⟩
        rw [hne]
        exact Sorts.close_none_of_reject hθ hn fun τ => by rw [hap v hv]; exact hσ τ
      | some atoms =>
        simp only [AllRes, ↓reduceIte, List.append_nil] at hres3
        obtain ⟨A, hrA, hA, hlenA, hsem⟩ := hres3
        have hA' : ∀ τ : Nat → GTerm, Sorts.Atoms.Holds S A τ ↔
            Sorts.InSorts S r (Sorts.bindsOf r.c.length (Sorts.orient r.c.length μ)) τ := by
          intro τ
          rw [← hsem τ]
          constructor
          · intro h v hv n hn
            rw [hap v hv]
            exact h (r.conj v, Sorts.orient r.c.length μ v)
              (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩) n hn
          · intro h b hb n hn
            obtain ⟨v, hv, rfl⟩ := hmemL b hb
            have := h v hv n hn
            rwa [hap v hv] at this
        have hAk : ∀ a ∈ A, a.1 < r.c.length := by
          intro a ha
          obtain ⟨-, b, hb, hsub⟩ := hA a ha
          obtain ⟨v, hv, rfl⟩ := hmemL b hb
          have := var_mem_subs_iff.1 hsub
          rw [← hap v hv] at this
          exact hθ.apply_lt hv _ this
        simp only
        step with close_spec hnm hC r.c.length (Sorts.orient r.c.length μ) A
          (fun a ha => hC.names _ (hA a ha).1) hlenA hr s3 decls names vs vals atoms hI3
          (hx03.repr hd) (hx03.repr hU) hrA (hx03.repr hvs) (hx3.repr hr2)
          (by unfold Room; omega) as ⟨o2, s4, hI4, hx4, ht4, hres4⟩
        refine ⟨hI4, hx03.trans hx4, by simp only [normExCost, hs, afterSolve]; omega, ?_⟩
        cases o2 with
        | none =>
          simp only at hres4 ⊢
          obtain ⟨y, -, hc⟩ := hres4
          rw [hne]
          exact Sorts.close_none_of_atoms hθ hA' hc
        | some res =>
          simp only at hres4 ⊢
          obtain ⟨hall, hrr⟩ := hres4
          obtain ⟨θ', hcl, hval⟩ := Sorts.close_some_of_atoms hθ hA' hAk hall
          refine ⟨θ', by rw [hne]; exact hcl, ?_⟩
          have e : (List.range r.c.length).map (PSubst.apply θ') =
              (List.range r.c.length).map fun v => (Sorts.orient r.c.length μ v).bind
                (Sorts.oneSub S r.c.length (Sorts.orient r.c.length μ) (Sorts.upsOf A)) := by
            refine List.map_congr_left fun v hv => ?_
            rw [hval v, hap v (List.mem_range.1 hv), oneSub_apply hap]
          rw [e]
          exact hrr

end RwLogVerified
