/-
# The next variable, settling and opening a variable, on the store

`sorts::var_succ` builds the variable after a given one. `sorts::settle`
replaces each variable of a list whose sorts have one member by that member
(`Sorts.CStore.settle`). `sorts::open_var` replaces a variable by a symbol
applied to new variables, one for each conjunction of a list
(`Sorts.CStore.exp`).
-/
import RwLogVerified.Gone
import RwLog.Sorts.Loop

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The next variable -/

theorem VarAt.ne_zero {nodes : List store.Node} {i L : Nat} (hroot : nodes[0]? = some .V0)
    (hv : VarAt nodes i L) (hL : L ≠ 0) : i ≠ 0 := by
  intro e
  subst e
  exact hL (hv.unique (.zero hroot))

/-- Going down the variable while its last digit is one: what is left on the
stack is one frame for each digit passed, and the node returned is the
variable after what is left of the digits. -/
theorem var_succ_loop0_spec : ∀ (n : Nat) (s : store.Store) (q low : store.TermId),
    Wf s → VarAt s.nodes.val q.val n → Room s (2 * Nat.log2 (n + 1) + 2) →
    sorts.var_succ_loop0 s q low true ⦃ res =>
      Wf res.1 ∧ Extends s res.1 ∧ tbl res.1 = tbl s ∧
      ∃ k L fs, stk res.1 = fs ++ stk s ∧ fs.length = k ∧
        VarAt res.1.nodes.val res.2.val L ∧ L ≠ 0 ∧ L * 2 ^ k = n + 1 ∧
        res.1.ticks.val ≤ s.ticks.val + 2 * k + 2 ⦄ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s q low hW hv hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.var_succ_loop0
    rw [loop]
    simp only [sorts.var_succ_loop0.body, ↓reduceIte]
    step with read_w s q hW hv.lt (by unfold Room; omega) as ⟨r0, hnd, hK1⟩
    obtain ⟨nd, s1⟩ := r0
    simp only at hnd hK1
    have ht1 := hK1.ticks
    have hx1 : Extends s s1 := Extends.of_eq hK1.nodes (by omega)
    cases hv with
    | zero h =>
      obtain rfl : nd = .V0 := by rw [h] at hnd; exact (Option.some.inj hnd).symm
      simp only [uncurry]
      step with alloc_w s1 (.VR q) hK1.wf ⟨.V0, by rw [hK1.nodes]; exact h, trivial⟩
        (by unfold Room; omega) as ⟨r2, hW2, ht2, htb2, hx2, hn2, hst2⟩
      obtain ⟨low1, s2⟩ := r2
      simp only [norm] at hW2 ht2 htb2 hx2 hn2 hst2
      simp only [uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hW2, hx1.trans hx2, by rw [htb2, hK1.tbl], 0, 1, [], by
        rw [hst2, hK1.stk]; rfl, rfl, ?_, by omega, by omega, by omega⟩
      exact VarAt.right (n := 0) hn2 ((hx1.trans hx2).varAt (.zero h))
    | @left _ a m h ha =>
      obtain rfl : nd = .VL a := by rw [h] at hnd; exact (Option.some.inj hnd).symm
      simp only [uncurry]
      step with alloc_w s1 (.VR a) hK1.wf (by rw [hK1.nodes]; exact ha.node)
        (by unfold Room; omega) as ⟨r2, hW2, ht2, htb2, hx2, hn2, hst2⟩
      obtain ⟨low1, s2⟩ := r2
      simp only [norm] at hW2 ht2 htb2 hx2 hn2 hst2
      simp only [uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hW2, hx1.trans hx2, by rw [htb2, hK1.tbl], 0, 2 * m + 1, [], by
        rw [hst2, hK1.stk]; rfl, rfl, ?_, by omega, by omega, by omega⟩
      exact VarAt.right hn2 ((hx1.trans hx2).varAt ha)
    | @right _ a m h ha =>
      obtain rfl : nd = .VR a := by rw [h] at hnd; exact (Option.some.inj hnd).symm
      simp only [uncurry]
      have hlog : Nat.log2 (2 * m + 1 + 1) = Nat.log2 (m + 1) + 1 := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
        exact Nat.log2_two_mul (by omega)
      rw [hlog] at hroom'
      step with push_w s1 (.Visit q q) hK1.wf (by unfold Room; omega)
        as ⟨s2, hn2, htb2, ht2, hW2, hst2⟩
      have IH := ih m (by omega) s2 a low hW2 (by rw [hn2, hK1.nodes]; exact ha)
        (by unfold Room; omega)
      unfold sorts.var_succ_loop0 at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hW', hx', htb', k, L, fs, hst', hk, hv', hL, hmul, ht'⟩
      have hx12 : Extends s s2 := hx1.trans (Extends.of_eq hn2 (by omega))
      refine ⟨hW', hx12.trans hx', by rw [htb', htb2, hK1.tbl], k + 1, L,
        fs ++ [.Visit q q], by rw [hst', hst2, hK1.stk]; simp, by simp [hk], hv', hL, ?_,
        by omega⟩
      rw [pow_succ, ← Nat.mul_assoc]
      omega

/-- Doubling the variable once for each frame on the stack. -/
theorem var_succ_loop1_spec : ∀ (fs : List store.Frame) (s : store.Store) (r : store.TermId)
    (L : Nat), Wf s → stk s = fs → VarAt s.nodes.val r.val L → L ≠ 0 →
    Room s (2 * fs.length + 1) →
    sorts.var_succ_loop1 s r ⦃ r' s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' = tbl s ∧ VarAt s'.nodes.val r'.val (L * 2 ^ fs.length) ∧
        s'.ticks.val ≤ s.ticks.val + 2 * fs.length + 1 ⦄ := by
  intro fs
  induction fs with
  | nil =>
    intro s r L hW hst hv hL hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.var_succ_loop1
    rw [loop]
    simp only [sorts.var_succ_loop1.body]
    step with pop_w s hW (by unfold Room; omega) as ⟨r0, hn1, htb1, ht1, hW1, ho, hst1⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hn1 htb1 ht1 hW1 ho hst1
    rw [hst] at ho hst1
    subst ho
    simp only [List.head?_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, uncurry,
      bind_ok, WP.spec_ok]
    refine ⟨⟨hW1, by rw [hst1]; rfl⟩, Extends.of_eq hn1 (by omega), htb1, ?_, by
      simp only [List.length_nil]; omega⟩
    rw [hn1]
    simpa using hv
  | cons f fs ih =>
    intro s r L hW hst hv hL hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.var_succ_loop1
    rw [loop]
    simp only [sorts.var_succ_loop1.body]
    step with pop_w s hW (by unfold Room; omega) as ⟨r0, hn1, htb1, ht1, hW1, ho, hst1⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hn1 htb1 ht1 hW1 ho hst1
    rw [hst] at ho hst1
    subst ho
    simp only [List.tail_cons] at hst1
    simp only [List.head?_cons, Option.isSome_some, ↓reduceIte, uncurry]
    have hv1 : VarAt s1.nodes.val r.val L := by rw [hn1]; exact hv
    step with alloc_w s1 (.VL r) hW1 hv1.node (by unfold Room; omega)
      as ⟨r2, hW2, ht2, htb2, hx2, hnd2, hst2⟩
    obtain ⟨r1, s2⟩ := r2
    simp only at hW2 ht2 htb2 hx2 hnd2 hst2
    simp only [norm, ite_neg' (hv1.ne_zero hW1.root hL)] at hnd2
    simp only [uncurry, bind_ok]
    have IH := ih s2 r1 (2 * L) hW2 (by rw [hst2, hst1]) (.left hnd2 (hx2.varAt hv1))
      (by omega) (by unfold Room; omega)
    unfold sorts.var_succ_loop1 at IH
    refine WP.spec_mono IH ?_
    rintro ⟨r', s'⟩ ⟨hI', hx', htb', hv', ht'⟩
    refine ⟨hI', (Extends.of_eq hn1 (by omega)).trans (hx2.trans hx'), by
      rw [htb', htb2, htb1], ?_, by simp only [List.length_cons]; omega⟩
    have e : L * 2 ^ (f :: fs).length = 2 * L * 2 ^ fs.length := by
      simp only [List.length_cons, pow_succ]
      rw [Nat.mul_comm 2 L, Nat.mul_assoc, Nat.mul_comm 2]
    rw [e]
    exact hv'

/-- The ticks the next variable may take. -/
def succCost (n : Nat) : Nat := 4 * Nat.log2 (n + 1) + 4

/-- `var_succ` builds the variable after `n`, within `succCost n` ticks. -/
theorem var_succ_spec (s : store.Store) (v : store.TermId) {n : Nat} (hI : Inv s)
    (hv : VarAt s.nodes.val v.val n) (hroom : Room s (succCost n)) :
    sorts.var_succ s v ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' = tbl s ∧ VarAt s'.nodes.val r.val (n + 1) ∧
        s'.ticks.val ≤ s.ticks.val + succCost n ⦄ := by
  unfold sorts.var_succ
  have hroom' := hroom
  unfold Room at hroom'
  simp only [succCost] at hroom'
  step with alloc_w s .V0 hI.toWf trivial (by unfold Room; omega)
    as ⟨low, s1, hW1, ht1, htb1, hx1, hnd1, hst1⟩
  step with var_succ_loop0_spec n s1 v low hW1 (hx1.varAt hv) (by unfold Room; omega)
    as ⟨s2, low1, hW2, hx2, htb2, k, L, fs, hst2, hk, hv2, hL, hmul, ht2⟩
  rw [hst1, hI.empty, List.append_nil] at hst2
  have hkl : k ≤ Nat.log2 (n + 1) := by
    refine (Nat.le_log2 (by omega)).2 ?_
    calc 2 ^ k = 1 * 2 ^ k := (Nat.one_mul _).symm
      _ ≤ L * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = n + 1 := hmul
  step with var_succ_loop1_spec fs s2 low1 L hW2 hst2 hv2 hL (by unfold Room; omega)
    as ⟨r, s3, hI3, hx3, htb3, hv3, ht3⟩
  refine ⟨hI3, (hx1.trans hx2).trans hx3, by rw [htb3, htb2, htb1], ?_, by
    simp only [succCost]; omega⟩
  rw [hk, hmul] at hv3
  exact hv3

/-! ## Settling the variables whose sorts have one member -/

/-- An entry of a store: a variable with the conjunction of its sorts. -/
noncomputable def varEntry (nm : Option Nat → RwLog.Sym) (U : List Name)
    (p : Nat × Sorts.Conj) : Pat :=
  .app (.var p.1) (cpat (nm none) U p.2)

/-- A list of entries as a term. -/
noncomputable def encVarEntries (nm : Option Nat → RwLog.Sym) (U : List Name)
    (L : List (Nat × Sorts.Conj)) : Pat :=
  encList (nm none) (L.map (varEntry nm U))

/-- A list of exclusions as a term. -/
def encX (nm : Option Nat → RwLog.Sym) (X : List (Eqns Nat)) : Pat :=
  encList (nm none) (X.map (encEqs nm))

theorem encX_subst (x : Nat) (u : Pat) (X : List (Eqns Nat)) :
    (encX nm X).bind (Term.single x u) = encX nm (X.map (Eqns.subst x u)) := by
  simp only [encX, encList_bind, List.map_map]
  congr 1
  exact List.map_congr_left fun E _ => enc_subst x u E

/-- The pattern and the exclusions after each entry whose conjunction has one
member has had its variable replaced by that member. -/
def settleT (S : Sorts) :
    List (Nat × Sorts.Conj) → Pat × List (Eqns Nat) → Pat × List (Eqns Nat)
  | [], r => r
  | p :: L, r =>
    match Sorts.count S p.2 with
    | .one g => settleT S L (r.1.bind (Term.single p.1 (GTerm.toPat g)),
        r.2.map (Eqns.subst p.1 (GTerm.toPat g)))
    | _ => settleT S L r

/-- Whether there is one member. -/
def isOne : Sorts.Count → Bool
  | .one _ => true
  | _ => false

/-- The entries whose conjunction does not have one member. -/
def settleKept (S : Sorts) (L : List (Nat × Sorts.Conj)) : List (Nat × Sorts.Conj) :=
  L.filter fun p => !isOne (Sorts.count S p.2)

/-- The ticks going through the entries may spend. -/
noncomputable def settleLoopCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u : Nat) :
    List (Nat × Sorts.Conj) → Pat × List (Eqns Nat) → Nat
  | [], _ => 1
  | p :: L, r =>
    match Sorts.count S p.2 with
    | .one g => countCost S u (Sorts.reachSet S p.2).card + 13 + 14 * r.1.subs.card +
        14 * (encX nm r.2).subs.card +
        settleLoopCost nm S u L (r.1.bind (Term.single p.1 (GTerm.toPat g)),
          r.2.map (Eqns.subst p.1 (GTerm.toPat g)))
    | _ => countCost S u (Sorts.reachSet S p.2).card + 3 + settleLoopCost nm S u L r

section settle

variable {S : Sorts} {en : Nat × Sorts.Conj} {L : List (Nat × Sorts.Conj)}
  {r : Pat × List (Eqns Nat)}

theorem settleT_keep (h : ∀ g, Sorts.count S en.2 ≠ .one g) :
    settleT S (en :: L) r = settleT S L r := by
  cases hc : Sorts.count S en.2 with
  | one g => exact absurd hc (h g)
  | none => simp only [settleT, hc]
  | many => simp only [settleT, hc]

theorem settleT_one {g : GTerm} (h : Sorts.count S en.2 = .one g) :
    settleT S (en :: L) r = settleT S L (r.1.bind (Term.single en.1 (GTerm.toPat g)),
      r.2.map (Eqns.subst en.1 (GTerm.toPat g))) := by
  simp only [settleT, h]

theorem settleKept_keep (h : ∀ g, Sorts.count S en.2 ≠ .one g) :
    settleKept S (en :: L) = en :: settleKept S L := by
  cases hc : Sorts.count S en.2 with
  | one g => exact absurd hc (h g)
  | none => simp [settleKept, hc, isOne]
  | many => simp [settleKept, hc, isOne]

theorem settleKept_one {g : GTerm} (h : Sorts.count S en.2 = .one g) :
    settleKept S (en :: L) = settleKept S L := by
  simp [settleKept, h, isOne]

theorem settleLoopCost_keep {u : Nat} (h : ∀ g, Sorts.count S en.2 ≠ .one g) :
    settleLoopCost nm S u (en :: L) r =
      countCost S u (Sorts.reachSet S en.2).card + 3 + settleLoopCost nm S u L r := by
  cases hc : Sorts.count S en.2 with
  | one g => exact absurd hc (h g)
  | none => simp only [settleLoopCost, hc]
  | many => simp only [settleLoopCost, hc]

theorem settleLoopCost_one {u : Nat} {g : GTerm} (h : Sorts.count S en.2 = .one g) :
    settleLoopCost nm S u (en :: L) r =
      countCost S u (Sorts.reachSet S en.2).card + 13 + 14 * r.1.subs.card +
        14 * (encX nm r.2).subs.card +
        settleLoopCost nm S u L (r.1.bind (Term.single en.1 (GTerm.toPat g)),
          r.2.map (Eqns.subst en.1 (GTerm.toPat g))) := by
  simp only [settleLoopCost, h]

theorem settleLoopCost_ge {u : Nat} :
    countCost S u (Sorts.reachSet S en.2).card + 3 ≤ settleLoopCost nm S u (en :: L) r := by
  cases hc : Sorts.count S en.2 with
  | one g => rw [settleLoopCost_one hc]; omega
  | none => rw [settleLoopCost_keep (by intro g h; rw [hc] at h; cases h)]; omega
  | many => rw [settleLoopCost_keep (by intro g h; rw [hc] at h; cases h)]; omega

end settle

theorem settle_loop_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) (decls names : store.TermId) :
    ∀ (L acc : List (Nat × Sorts.Conj)) (T : Pat) (X : List (Eqns Nat)) (s : store.Store)
      (es t x kept : store.TermId),
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    (∀ p ∈ L, Sub U p.2) →
    Repr nm s.nodes.val es.val (encVarEntries nm U L) →
    Repr nm s.nodes.val t.val T → Repr nm s.nodes.val x.val (encX nm X) →
    Repr nm s.nodes.val kept.val (encVarEntries nm U acc) →
    Room s (settleLoopCost nm S U.length L (T, X)) →
    sorts.settle_loop es s decls names t x kept ⦃ res =>
      Inv res.1 ∧ Extends s res.1 ∧
        res.1.ticks.val ≤ s.ticks.val + settleLoopCost nm S U.length L (T, X) ∧
        Repr nm res.1.nodes.val res.2.1.val (settleT S L (T, X)).1 ∧
        Repr nm res.1.nodes.val res.2.2.1.val (encX nm (settleT S L (T, X)).2) ∧
        Repr nm res.1.nodes.val res.2.2.2.val
          (encVarEntries nm U ((settleKept S L).reverse ++ acc)) ⦄ := by
  intro L
  induction L with
  | nil =>
    intro acc T X s es t x kept hI hde hU hsub hes ht hx hkept hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [settleLoopCost] at hroom'
    unfold sorts.settle_loop
    rw [loop]
    simp only [sorts.settle_loop.body]
    step with uncons_repr s es hI.toWf (p := Term.sym (nm none)) hes (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok, WP.spec_ok]
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [settleLoopCost]; omega, ?_⟩
    rw [K1.nodes]
    exact ⟨ht, hx, by simpa [settleKept] using hkept⟩
  | cons en L ih =>
    intro acc T X s es t x kept hI hde hU hsub hes ht hx hkept hroom
    have hroom' := hroom
    unfold Room at hroom'
    have hge := settleLoopCost_ge (nm := nm) (S := S) (en := en) (L := L) (r := (T, X))
      (u := U.length)
    unfold sorts.settle_loop
    rw [loop]
    simp only [sorts.settle_loop.body]
    step with uncons_repr s es hI.toWf (p := Term.app (varEntry nm U en) (encVarEntries nm U L)) hes
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
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
    step with count_spec hC en.2 (hsub en (by simp)) s2 decls names ci K2.inv (hx2.repr hde)
      (hx2.repr hU) (by rw [K2.nodes]; exact rc) (by unfold Room; omega)
      as ⟨r3, hI3, hx3, ht3, hres⟩
    obtain ⟨c1, s3⟩ := r3
    simp only at hI3 hx3 ht3 hres
    have hx03 := hx2.trans hx3
    cases c1 with
    | One gi =>
      obtain ⟨g, hc, rg⟩ := hres
      rw [settleLoopCost_one hc] at hroom'
      simp only at hroom'
      simp only [uncurry]
      step with clear_spec s3 .A hI3 (by unfold Room; omega) as ⟨s4, hn4, ht4, hI4, hA4, hB4⟩
      have hx34 : Extends s3 s4 := Extends.of_eq hn4 (by omega)
      have hx04 := hx03.trans hx34
      have hpc5 := pending_card_le (nm := nm) s4.nodes.val (tbl s4 .A) T.subs
      step with rebuild_spec hnm s4 (term.Leaf.Sub vi gi) t (t := T)
        (σ := Term.single en.1 (GTerm.toPat g)) T.subs hI4 (hx04.repr ht)
        ⟨en.1, GTerm.toPat g, (hx3.trans hx34).varAt hvv, hx34.repr rg, rfl⟩
        (by intro k w hk; rw [hA4 k] at hk; cases hk) (Finset.Subset.refl _)
        (by unfold Room; omega) as ⟨r5, hR5⟩
      obtain ⟨t1, s5⟩ := r5
      simp only at hR5
      have hc5 := hR5.cost
      have hm5 := hR5.mono
      have hx05 := hx04.trans hR5.ext
      have hpc6 := pending_card_le (nm := nm) s5.nodes.val (tbl s5 .A) (encX nm X).subs
      step with rebuild_spec hnm s5 (term.Leaf.Sub vi gi) x (t := encX nm X)
        (σ := Term.single en.1 (GTerm.toPat g)) (encX nm X).subs hR5.inv (hx05.repr hx)
        ⟨en.1, GTerm.toPat g, ((hx3.trans hx34).trans hR5.ext).varAt hvv,
          (hx34.trans hR5.ext).repr rg, rfl⟩
        hR5.memo (Finset.Subset.refl _) (by unfold Room; omega) as ⟨r6, hR6⟩
      obtain ⟨x1, s6⟩ := r6
      simp only at hR6
      have hc6 := hR6.cost
      have hm6 := hR6.mono
      have hx06 := hx05.trans hR6.ext
      simp only [uncurry, bind_ok]
      have IH := ih acc (T.bind (Term.single en.1 (GTerm.toPat g)))
        (X.map (Eqns.subst en.1 (GTerm.toPat g))) s6 rest t1 x1 kept hR6.inv (hx06.repr hde)
        (hx06.repr hU) (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) (hx06.repr rrest)
        (hR6.ext.repr hR5.repr) (by rw [← encX_subst]; exact hR6.repr) (hx06.repr hkept)
        (by unfold Room; omega)
      unfold sorts.settle_loop at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hI', hx', ht', h1, h2, h3⟩
      refine ⟨hI', hx06.trans hx', by
        rw [settleLoopCost_one hc]; simp only; omega, ?_, ?_, ?_⟩
      · rw [settleT_one hc]; exact h1
      · rw [settleT_one hc]; exact h2
      · rw [settleKept_one hc]; exact h3
    | None | Many =>
      have hne : ∀ g, Sorts.count S en.2 ≠ .one g := by intro g h; rw [hres] at h; cases h
      rw [settleLoopCost_keep hne] at hroom'
      simp only [uncurry]
      step with alloc_spec s3 (.App e kept) hI3 ⟨(hx03.repr re).lt, (hx03.repr hkept).lt⟩
        (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
      obtain ⟨kept1, s4⟩ := r4
      simp only [norm] at hI4 ht4 htb4 hx4 hr4
      simp only [uncurry, bind_ok]
      have hx04 := hx03.trans hx4
      have rk : Repr nm s4.nodes.val kept1.val (encVarEntries nm U (en :: acc)) :=
        .app hr4 (hx04.repr re) (hx04.repr hkept)
      have IH := ih (en :: acc) T X s4 rest t x kept1 hI4 (hx04.repr hde) (hx04.repr hU)
        (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) (hx04.repr rrest) (hx04.repr ht)
        (hx04.repr hx) rk (by unfold Room; omega)
      unfold sorts.settle_loop at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hI', hx', ht', h1, h2, h3⟩
      refine ⟨hI', hx04.trans hx', by rw [settleLoopCost_keep hne]; omega, ?_, ?_, ?_⟩
      · rw [settleT_keep hne]; exact h1
      · rw [settleT_keep hne]; exact h2
      · rw [settleKept_keep hne]
        simpa using h3

/-- The ticks settling a list of entries may take. -/
noncomputable def settleCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u : Nat)
    (L : List (Nat × Sorts.Conj)) (T : Pat) (X : List (Eqns Nat)) : Nat :=
  settleLoopCost nm S u L (T, X) + 2 * L.length + 3

/-- `settle` replaces, in the pattern and in the exclusions, the variable of
each entry whose conjunction has one member by that member, and returns the
other entries in their order. -/
theorem settle_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) (L : List (Nat × Sorts.Conj)) (T : Pat) (X : List (Eqns Nat))
    (s : store.Store) (decls names t x es : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hsub : ∀ p ∈ L, Sub U p.2)
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (ht : Repr nm s.nodes.val t.val T) (hx : Repr nm s.nodes.val x.val (encX nm X))
    (hroom : Room s (settleCost nm S U.length L T X)) :
    sorts.settle s decls names t x es ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + settleCost nm S U.length L T X ∧
        Repr nm s'.nodes.val r.1.val (settleT S L (T, X)).1 ∧
        Repr nm s'.nodes.val r.2.1.val (encX nm (settleT S L (T, X)).2) ∧
        Repr nm s'.nodes.val r.2.2.val (encVarEntries nm U (settleKept S L)) ⦄ := by
  unfold sorts.settle
  have hroom' := hroom
  unfold Room at hroom'
  simp only [settleCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨kept, s1, hI1, ht1, htb1, hx1, hr1⟩
  have rnil : Repr nm s1.nodes.val kept.val (encVarEntries nm U []) := .nil hr1
  step with settle_loop_spec hnm hC decls names L [] T X s1 es t x kept hI1 (hx1.repr hde)
    (hx1.repr hU) hsub (hx1.repr hes) (hx1.repr ht) (hx1.repr hx) rnil
    (by unfold Room; omega) as ⟨s2, t1, x1, kept1, hI2, hx2, ht2, h1, h2, h3⟩
  have hlen : (settleKept S L).length ≤ L.length := List.length_filter_le _ _
  simp only [List.append_nil] at h3
  step with rev_spec ((settleKept S L).reverse.map (varEntry nm U)) s2 kept1 hI2.toWf h3
    (by simp only [List.length_map, List.length_reverse]; unfold Room; omega)
    as ⟨kept2, s3, hR3, hr3⟩
  simp only [List.length_map, List.length_reverse] at hR3
  have ht3 := hR3.ticks
  refine ⟨⟨hR3.wf, by rw [hR3.stk]; exact hI2.empty⟩, (hx1.trans hx2).trans hR3.ext, by
    simp only [settleCost]; omega, hR3.ext.repr h1, hR3.ext.repr h2, ?_⟩
  simpa only [encVarEntries, ← List.map_reverse, List.reverse_reverse] using hr3

/-! ### Against `CStore.settle` -/

theorem set_conj (s : Sorts.CStore) (w : Nat) (g : GTerm) (u : Nat) :
    (s.set w g).conj u = if u = w then ∅ else s.conj u :=
  congrFun (congrArg Sorts.Store.c (Sorts.CStore.set_store s w g)) u

/-- Settling the variables of a list without repetition is settling the
entries of these variables. -/
theorem settle_link (S : Sorts) : ∀ (ws : List Nat) (s : Sorts.CStore), ws.Nodup →
    (Sorts.CStore.settle S s ws).t = (settleT S (ws.map fun w => (w, s.conj w)) (s.t, s.x)).1 ∧
    (Sorts.CStore.settle S s ws).x = (settleT S (ws.map fun w => (w, s.conj w)) (s.t, s.x)).2 ∧
    ∀ u, (Sorts.CStore.settle S s ws).conj u =
      if u ∈ ws ∧ isOne (Sorts.count S (s.conj u)) = true then ∅ else s.conj u := by
  intro ws
  induction ws with
  | nil => intro s _; simp [Sorts.CStore.settle, settleT]
  | cons w ws ih =>
    intro s hnd
    obtain ⟨hw, hnd'⟩ := List.nodup_cons.1 hnd
    cases hc : Sorts.count S (s.conj w) with
    | one g =>
      have hmap : (ws.map fun u => (u, (s.set w g).conj u)) = ws.map fun u => (u, s.conj u) :=
        List.map_congr_left fun u hu => by
          rw [set_conj, ite_neg' (fun e : u = w => hw (e ▸ hu))]
      obtain ⟨h1, h2, h3⟩ := ih (s.set w g) hnd'
      rw [hmap] at h1 h2
      have e : Sorts.CStore.settle S s (w :: ws) = Sorts.CStore.settle S (s.set w g) ws := by
        simp only [Sorts.CStore.settle, hc]
      rw [e, List.map_cons, settleT_one (en := (w, s.conj w)) hc]
      refine ⟨h1, h2, fun u => ?_⟩
      rw [h3 u, set_conj]
      by_cases huw : u = w
      · subst huw
        simp [hw, hc, isOne]
      · simp [huw]
    | none =>
      have hne : ∀ g, Sorts.count S (s.conj w) ≠ .one g := by intro g h; rw [hc] at h; cases h
      obtain ⟨h1, h2, h3⟩ := ih s hnd'
      have e : Sorts.CStore.settle S s (w :: ws) = Sorts.CStore.settle S s ws := by
        simp only [Sorts.CStore.settle, hc]
      rw [e, List.map_cons, settleT_keep (en := (w, s.conj w)) hne]
      refine ⟨h1, h2, fun u => ?_⟩
      rw [h3 u]
      by_cases huw : u = w
      · subst huw
        simp [hw, hc, isOne]
      · simp [huw]
    | many =>
      have hne : ∀ g, Sorts.count S (s.conj w) ≠ .one g := by intro g h; rw [hc] at h; cases h
      obtain ⟨h1, h2, h3⟩ := ih s hnd'
      have e : Sorts.CStore.settle S s (w :: ws) = Sorts.CStore.settle S s ws := by
        simp only [Sorts.CStore.settle, hc]
      rw [e, List.map_cons, settleT_keep (en := (w, s.conj w)) hne]
      refine ⟨h1, h2, fun u => ?_⟩
      rw [h3 u]
      by_cases huw : u = w
      · subst huw
        simp [hw, hc, isOne]
      · simp [huw]

/-! ## Opening a variable -/

/-- `H` applied to the `k` variables from `N`. -/
def appVars : Pat → Nat → Nat → Pat
  | H, _, 0 => H
  | H, N, k + 1 => appVars (.app H (.var N)) (N + 1) k

theorem appVars_eq : ∀ (k : Nat) (H : Pat) (N : Nat),
    appVars H N k = ((List.range k).map fun i => (.var (N + i) : Pat)).foldl .app H := by
  intro k
  induction k with
  | zero => intro H N; rfl
  | succ k ih =>
    intro H N
    rw [appVars, ih, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

theorem appVars_sym (f : Sym) (N n : Nat) : appVars (.sym f) N n = Sorts.expVar N n f :=
  appVars_eq n _ N

/-- The entries of the variables from `N`, one for each conjunction. -/
def entsFrom : Nat → List Sorts.Conj → List (Nat × Sorts.Conj)
  | _, [] => []
  | N, c :: cs => (N, c) :: entsFrom (N + 1) cs

theorem entsFrom_length : ∀ (cs : List Sorts.Conj) (N : Nat), (entsFrom N cs).length = cs.length
  | [], _ => rfl
  | _ :: cs, N => by simp [entsFrom, entsFrom_length cs]

/-- The ticks going through the conjunctions may spend. -/
def openLoopCost : Nat → Nat → Nat
  | _, 0 => 1
  | N, k + 1 => succCost N + 4 + openLoopCost (N + 1) k

theorem open_var_loop_spec {U : List Name} :
    ∀ (cs : List Sorts.Conj) (acc : List (Nat × Sorts.Conj)) (H : Pat) (N : Nat)
      (s : store.Store) (kids head next es : store.TermId),
    Inv s → Repr nm s.nodes.val kids.val (encList (nm none) (cs.map (cpat (nm none) U))) →
    Repr nm s.nodes.val head.val H → VarAt s.nodes.val next.val N →
    Repr nm s.nodes.val es.val (encVarEntries nm U acc) → Room s (openLoopCost N cs.length) →
    sorts.open_var_loop kids s head next es ⦃ res =>
      Inv res.1 ∧ Extends s res.1 ∧ res.1.ticks.val ≤ s.ticks.val + openLoopCost N cs.length ∧
        Repr nm res.1.nodes.val res.2.1.val (appVars H N cs.length) ∧
        VarAt res.1.nodes.val res.2.2.1.val (N + cs.length) ∧
        Repr nm res.1.nodes.val res.2.2.2.val
          (encVarEntries nm U ((entsFrom N cs).reverse ++ acc)) ⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro acc H N s kids head next es hI hk hh hn hes hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil, openLoopCost] at hroom'
    unfold sorts.open_var_loop
    rw [loop]
    simp only [sorts.open_var_loop.body]
    step with uncons_repr s kids hI.toWf (p := Term.sym (nm none)) hk (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok, WP.spec_ok]
    refine ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by
      simp only [List.length_nil, openLoopCost]; omega, ?_⟩
    rw [K1.nodes]
    exact ⟨hh, hn, by simpa [entsFrom] using hes⟩
  | cons c cs ih =>
    intro acc H N s kids head next es hI hk hh hn hes hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, openLoopCost] at hroom'
    unfold sorts.open_var_loop
    rw [loop]
    simp only [sorts.open_var_loop.body]
    step with uncons_repr s kids hI.toWf
      (p := Term.app (cpat (nm none) U c) (encList (nm none) (cs.map (cpat (nm none) U)))) hk
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨k, rest, rfl, rk, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    simp only [uncurry]
    step with alloc_spec s1 (.App head next) K1.inv ⟨(hx1.repr hh).lt, (hx1.varAt hn).lt⟩
      (by unfold Room; omega) as ⟨r2, hI2, ht2, htb2, hx2, hr2⟩
    obtain ⟨head1, s2⟩ := r2
    simp only [norm] at hI2 ht2 htb2 hx2 hr2
    simp only [uncurry]
    have hx02 := hx1.trans hx2
    step with alloc_spec s2 (.App next k) hI2 ⟨(hx02.varAt hn).lt, (hx02.repr rk).lt⟩
      (by unfold Room; omega) as ⟨r3, hI3, ht3, htb3, hx3, hr3⟩
    obtain ⟨e, s3⟩ := r3
    simp only [norm] at hI3 ht3 htb3 hx3 hr3
    simp only [uncurry]
    have hx03 := hx02.trans hx3
    have re : Repr nm s3.nodes.val e.val (varEntry nm U (N, c)) :=
      .app hr3 (.var (hx03.varAt hn)) (hx03.repr rk)
    step with alloc_spec s3 (.App e es) hI3 ⟨re.lt, (hx03.repr hes).lt⟩
      (by unfold Room; omega) as ⟨r4, hI4, ht4, htb4, hx4, hr4⟩
    obtain ⟨es1, s4⟩ := r4
    simp only [norm] at hI4 ht4 htb4 hx4 hr4
    simp only [uncurry]
    have hx04 := hx03.trans hx4
    step with var_succ_spec s4 next hI4 (hx04.varAt hn) (by unfold Room; omega)
      as ⟨r5, hI5, hx5, htb5, hv5, ht5⟩
    obtain ⟨next1, s5⟩ := r5
    simp only at hI5 hx5 htb5 hv5 ht5
    simp only [uncurry, bind_ok]
    have hx05 := hx04.trans hx5
    have IH := ih ((N, c) :: acc) (.app H (.var N)) (N + 1) s5 rest head1 next1 es1 hI5
      (hx05.repr rrest)
      ((hx3.trans (hx4.trans hx5)).repr (.app hr2 (hx02.repr hh) (.var (hx02.varAt hn))))
      hv5 (hx5.repr (.app hr4 (hx4.repr re) (hx04.repr hes))) (by unfold Room; omega)
    unfold sorts.open_var_loop at IH
    refine WP.spec_mono IH ?_
    rintro res ⟨hI', hx', ht', h1, h2, h3⟩
    refine ⟨hI', hx05.trans hx', by simp only [List.length_cons, openLoopCost]; omega, h1, ?_, ?_⟩
    · rw [List.length_cons, show N + (cs.length + 1) = N + 1 + cs.length by omega]; exact h2
    · simpa [entsFrom] using h3

/-- The ticks opening a variable may take. -/
def openCost (nm : Option Nat → RwLog.Sym) (N k : Nat) (T : Pat) (X : List (Eqns Nat)) : Nat :=
  openLoopCost N k + 2 * k + 14 + 14 * T.subs.card + 14 * (encX nm X).subs.card

/-- `open_var` replaces, in the pattern and in the exclusions, a variable by a
symbol applied to the variables from `N`, one for each conjunction of the
list (`Sorts.CStore.exp`), and returns the entries of these variables and
the variable after them. -/
theorem open_var_spec (hnm : Function.Injective nm) {U : List Name} (s : store.Store)
    (v f kids next t x : store.TermId) {xv N : Nat} {fs : Sym} {cs : List Sorts.Conj}
    {T : Pat} {X : List (Eqns Nat)} (hI : Inv s) (hv : VarAt s.nodes.val v.val xv)
    (hf : Repr nm s.nodes.val f.val (.sym fs))
    (hk : Repr nm s.nodes.val kids.val (encList (nm none) (cs.map (cpat (nm none) U))))
    (hn : VarAt s.nodes.val next.val N) (ht : Repr nm s.nodes.val t.val T)
    (hx : Repr nm s.nodes.val x.val (encX nm X)) (hroom : Room s (openCost nm N cs.length T X)) :
    sorts.open_var s v f kids next t x ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + openCost nm N cs.length T X ∧
        Repr nm s'.nodes.val r.1.val (T.bind (Term.single xv (Sorts.expVar N cs.length fs))) ∧
        Repr nm s'.nodes.val r.2.1.val
          (encX nm (X.map (Eqns.subst xv (Sorts.expVar N cs.length fs)))) ∧
        Repr nm s'.nodes.val r.2.2.1.val (encVarEntries nm U (entsFrom N cs)) ∧
        VarAt s'.nodes.val r.2.2.2.val (N + cs.length) ⦄ := by
  unfold sorts.open_var
  have hroom' := hroom
  unfold Room at hroom'
  simp only [openCost] at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨es, s1, hI1, ht1, htb1, hx1, hr1⟩
  have rnil : Repr nm s1.nodes.val es.val (encVarEntries nm U []) := .nil hr1
  step with open_var_loop_spec cs [] (.sym fs) N s1 kids f next es hI1 (hx1.repr hk)
    (hx1.repr hf) (hx1.varAt hn) rnil (by unfold Room; omega)
    as ⟨s2, head, next1, es1, hI2, hx2, ht2, h1, h2, h3⟩
  rw [appVars_sym] at h1
  simp only [List.append_nil] at h3
  have hlen := entsFrom_length cs N
  step with rev_spec ((entsFrom N cs).reverse.map (varEntry nm U)) s2 es1 hI2.toWf h3
    (by simp only [List.length_map, List.length_reverse, hlen]; unfold Room; omega)
    as ⟨es2, s3, hR3, hr3⟩
  simp only [List.length_map, List.length_reverse, hlen] at hR3
  have ht3 := hR3.ticks
  have hI3 : Inv s3 := ⟨hR3.wf, by rw [hR3.stk]; exact hI2.empty⟩
  have hx03 := (hx1.trans hx2).trans hR3.ext
  step with clear_spec s3 .A hI3 (by unfold Room; omega) as ⟨s4, hn4, ht4, hI4, hA4, hB4⟩
  have hx34 : Extends s3 s4 := Extends.of_eq hn4 (by omega)
  have hx04 := hx03.trans hx34
  have hh4 : Repr nm s4.nodes.val head.val (Sorts.expVar N cs.length fs) :=
    (hR3.ext.trans hx34).repr h1
  have hpc5 := pending_card_le (nm := nm) s4.nodes.val (tbl s4 .A) T.subs
  step with rebuild_spec hnm s4 (term.Leaf.Sub v head) t (t := T)
    (σ := Term.single xv (Sorts.expVar N cs.length fs)) T.subs hI4 (hx04.repr ht)
    ⟨xv, _, hx04.varAt hv, hh4, rfl⟩
    (by intro k w hk; rw [hA4 k] at hk; cases hk) (Finset.Subset.refl _)
    (by unfold Room; omega) as ⟨t1, s5, hR5⟩
  have hc5 := hR5.cost
  have hm5 := hR5.mono
  have hx05 := hx04.trans hR5.ext
  have hpc6 := pending_card_le (nm := nm) s5.nodes.val (tbl s5 .A) (encX nm X).subs
  step with rebuild_spec hnm s5 (term.Leaf.Sub v head) x (t := encX nm X)
    (σ := Term.single xv (Sorts.expVar N cs.length fs)) (encX nm X).subs hR5.inv (hx05.repr hx)
    ⟨xv, _, hx05.varAt hv, hR5.ext.repr hh4, rfl⟩
    hR5.memo (Finset.Subset.refl _) (by unfold Room; omega) as ⟨x1, s6, hR6⟩
  have hc6 := hR6.cost
  have hm6 := hR6.mono
  have hx36 := (hx34.trans hR5.ext).trans hR6.ext
  refine ⟨hR6.inv, hx05.trans hR6.ext, by simp only [openCost]; omega, hR6.ext.repr hR5.repr, by
    rw [← encX_subst]; exact hR6.repr, ?_, (hR3.ext.trans hx36).varAt h2⟩
  refine hx36.repr ?_
  simpa only [encVarEntries, ← List.map_reverse, List.reverse_reverse] using hr3

/-- The pattern and the exclusions `open_var` returns are those of
`Sorts.CStore.exp` when the variables from `N` are those after the last of
the store. -/
theorem exp_link (S : Sorts) (s : Sorts.CStore) (v : Nat) (f : Sym) (n : Nat) :
    (s.exp S v f n).t = s.t.bind (Term.single v (Sorts.expVar s.c.length n f)) ∧
    (s.exp S v f n).x = s.x.map (Eqns.subst v (Sorts.expVar s.c.length n f)) :=
  ⟨rfl, rfl⟩

end RwLogVerified
