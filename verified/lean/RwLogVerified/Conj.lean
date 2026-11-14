/-
# Conjunctions of sorts on the store

A conjunction of sorts is a set of names. In the store it is the list of its
names in the order of the list of every name, read from its end
(`conjList`), so one set is one identifier. This file proves the functions of
`rust/src/sorts.rs` that build conjunctions (`conj_of`, `conj_meet`) against
that list.

Table `A` flags names while a conjunction is built. `Flagged` says which.
-/
import RwLogVerified.Sorts
import RwLog.Sorts.Conj

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-- A list of names as a term. -/
def namesPat (z : Sym) (xs : List Name) : Pat := encList z (xs.map fun n => (.sym n : Pat))

/-- The members of a conjunction as the store lists them: those of `U` that
satisfy `F`, the first last. -/
noncomputable def conjList (U : List Name) (F : Name → Prop) : List Name :=
  haveI := Classical.decPred F
  (U.filter fun n => decide (F n)).reverse

theorem conjList_nil (F : Name → Prop) : conjList [] F = [] := by simp [conjList]

theorem conjList_cons_pos {F : Name → Prop} {x : Name} (h : F x) (ns : List Name) :
    conjList (x :: ns) F = conjList ns F ++ [x] := by
  simp [conjList, h]

theorem conjList_cons_neg {F : Name → Prop} {x : Name} (h : ¬ F x) (ns : List Name) :
    conjList (x :: ns) F = conjList ns F := by
  simp [conjList, h]

theorem conjList_congr {U : List Name} {F G : Name → Prop} (h : ∀ n ∈ U, F n ↔ G n) :
    conjList U F = conjList U G := by
  simp only [conjList]
  congr 1
  apply List.filter_congr
  intro n hn
  simp [h n hn]

theorem mem_conjList {U : List Name} {F : Name → Prop} {n : Name} :
    n ∈ conjList U F ↔ n ∈ U ∧ F n := by
  simp [conjList]

/-- A function ran that may have written table `A`: the invariant, the nodes
there were, table `B` and the stack, and at most `n` ticks spent. -/
structure RanA (s s' : store.Store) (n : Nat) : Prop where
  wf : Wf s'
  ext : Extends s s'
  tbl : tbl s' .B = tbl s .B
  stk : stk s' = stk s
  ticks : s'.ticks.val ≤ s.ticks.val + n

theorem Ran.ranA {s s' : store.Store} {n : Nat} (h : Ran s s' n) : RanA s s' n :=
  ⟨h.wf, h.ext, by rw [h.tbl], h.stk, h.ticks⟩

theorem RanA.trans {a b c : store.Store} {n m : Nat} (h₁ : RanA a b n) (h₂ : RanA b c m) :
    RanA a c (n + m) :=
  ⟨h₂.wf, h₁.ext.trans h₂.ext, by rw [h₂.tbl, h₁.tbl], by rw [h₂.stk, h₁.stk], by
    have := h₁.ticks; have := h₂.ticks; omega⟩

theorem RanA.mono {a b : store.Store} {n m : Nat} (h : RanA a b n) (hnm : n ≤ m) : RanA a b m :=
  ⟨h.wf, h.ext, h.tbl, h.stk, by have := h.ticks; omega⟩

/-- Table `A` flags the names of `U` that satisfy `F`, and no other name of
`U`. Every name of `U` is in the store. -/
def Flagged (nm : Option Nat → RwLog.Sym) (s : store.Store) (U : List Name) (F : Name → Prop) :
    Prop :=
  ∀ n ∈ U, ∃ i, Repr nm s.nodes.val i (.sym n) ∧ ((tbl s .A i).isSome ↔ F n)

theorem Flagged.mono {s s' : store.Store} {U : List Name} {F : Name → Prop}
    (h : Flagged nm s U F) (hx : Extends s s') (ht : tbl s' .A = tbl s .A) : Flagged nm s' U F := by
  intro n hn
  obtain ⟨i, hi, hiff⟩ := h n hn
  exact ⟨i, hx.repr hi, by rw [ht]; exact hiff⟩

theorem Flagged.congr {s : store.Store} {U : List Name} {F G : Name → Prop}
    (h : Flagged nm s U F) (hFG : ∀ n ∈ U, F n ↔ G n) : Flagged nm s U G := by
  intro n hn
  obtain ⟨i, hi, hiff⟩ := h n hn
  exact ⟨i, hi, hiff.trans (hFG n hn)⟩

/-- What the flag of a name of `U` says. -/
theorem Flagged.iff (hnm : Function.Injective nm) {s : store.Store} {U : List Name}
    {F : Name → Prop} (h : Flagged nm s U F) (hW : Wf s) {n : Name} (hn : n ∈ U) {i : Nat}
    (hi : Repr nm s.nodes.val i (.sym n)) : (tbl s .A i).isSome ↔ F n := by
  obtain ⟨j, hj, hiff⟩ := h n hn
  rw [Repr.inj hnm hW.nodesOK hi hj]
  exact hiff

/-- Flagging one more name. -/
theorem Flagged.set (hnm : Function.Injective nm) {s s' : store.Store} {U : List Name}
    {F : Name → Prop} (h : Flagged nm s U F) (hW : Wf s) (hn : s'.nodes.val = s.nodes.val)
    {k : Nat} {v : Nat} (ht : tbl s' .A = Function.update (tbl s .A) k (some v)) {n : Name}
    (hk : Repr nm s.nodes.val k (.sym n)) : Flagged nm s' U (fun m => F m ∨ m = n) := by
  intro m hm
  obtain ⟨i, hi, hiff⟩ := h m hm
  refine ⟨i, by rw [hn]; exact hi, ?_⟩
  rw [ht]
  by_cases e : i = k
  · subst e
    have := Repr.unique hi hk
    cases this
    simp
  · have hne : m ≠ n := by
      rintro rfl
      exact e (Repr.inj hnm hW.nodesOK hi hk)
    simp [Function.update, e, hne, hiff]

/-- Every member of a list of names in the store is in the store. -/
theorem namesPat_mem {nodes : List store.Node} : ∀ {xs : List Name} {i : Nat},
    Repr nm nodes i (namesPat (nm none) xs) → ∀ n ∈ xs, ∃ j, Repr nm nodes j (.sym n)
  | [], _, _, n, hn => by cases hn
  | x :: xs, i, h, n, hn => by
    simp only [namesPat, List.map_cons, encList] at h
    obtain ⟨a, b, -, ha, hb⟩ := Repr.app_inv h
    rcases List.mem_cons.1 hn with rfl | hn
    · exact ⟨_, ha⟩
    · exact namesPat_mem (xs := xs) hb n hn

/-- Every member of a list in the store is in the store. -/
theorem encList_mem_repr {nodes : List store.Node} : ∀ {xs : List Pat} {i : Nat},
    Repr nm nodes i (encList (nm none) xs) → ∀ j (h : j < xs.length), ∃ k, Repr nm nodes k xs[j]
  | [], _, _, j, h => by simp at h
  | x :: xs, i, h, j, hj => by
    simp only [encList] at h
    obtain ⟨a, b, -, ha, hb⟩ := Repr.app_inv h
    cases j with
    | zero => exact ⟨_, ha⟩
    | succ j => exact encList_mem_repr (xs := xs) hb j (by simpa using hj)

/-- After a clearing no name is flagged. -/
theorem Flagged.clear {s : store.Store} {U : List Name}
    (hU : ∀ n ∈ U, ∃ j, Repr nm s.nodes.val j (.sym n)) (ht : ∀ k, tbl s .A k = none) :
    Flagged nm s U (fun _ => False) := by
  intro n hn
  obtain ⟨j, hj⟩ := hU n hn
  exact ⟨j, hj, by simp [ht j]⟩

/-! ## Flagging the members of a list -/

theorem flag_list_loop_spec (hnm : Function.Injective nm) {U : List Name} :
    ∀ (xs : List Name) (s : store.Store) (list : store.TermId) (F : Name → Prop), Wf s →
    Repr nm s.nodes.val list.val (namesPat (nm none) xs) → Flagged nm s U F →
    Room s (2 * xs.length + 1) →
    sorts.mark_loop list s ⦃ s' =>
      s'.nodes.val = s.nodes.val ∧ RanA s s' (2 * xs.length + 1) ∧
        Flagged nm s' U (fun m => F m ∨ m ∈ xs) ⦄ := by
  intro xs
  induction xs with
  | nil =>
    intro s list F hW hl hF hroom
    unfold sorts.mark_loop
    rw [loop]
    simp only [sorts.mark_loop.body]
    step with uncons_repr s list hW hl (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hK hu ⊢
    subst hu
    have hfin : s1.nodes.val = s.nodes.val ∧ RanA s s1 (2 * ([] : List Name).length + 1) ∧
        Flagged nm s1 U (fun m => F m ∨ m ∈ ([] : List Name)) :=
      ⟨hK.nodes, hK.ran.ranA, (hF.mono hK.ran.ext (by rw [hK.tbl])).congr (by simp)⟩
    step*
  | cons x xs ih =>
    intro s list F hW hl hF hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.mark_loop
    rw [loop]
    simp only [sorts.mark_loop.body]
    step with uncons_repr s list hW hl (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hK hu ⊢
    obtain ⟨h, t, rfl, rh, rt⟩ := hu
    have ht1 := hK.ticks
    have rh1 : Repr nm s1.nodes.val h.val (.sym x) := by rw [hK.nodes]; exact rh
    step with set_flag_w s1 .A h true hK.wf rh1.lt (by unfold Room; omega)
      as ⟨s2, hn2, ht2, hW2, hA2, hB2, hst2⟩
    have hF1 : Flagged nm s1 U F := hF.mono hK.ran.ext (by rw [hK.tbl])
    have hF2 := hF1.set hnm hK.wf hn2 hA2 rh1
    have IH := ih s2 t (fun m => F m ∨ m = x) hW2 (by rw [hn2, hK.nodes]; exact rt) hF2
      (by unfold Room; omega)
    unfold sorts.mark_loop at IH
    simp only [uncurry]
    refine WP.spec_mono IH ?_
    rintro s' ⟨hn', hR, hF'⟩
    have hR2 : RanA s s2 2 :=
      ⟨hW2, Extends.of_eq (by rw [hn2, hK.nodes]) (by omega),
        by rw [hB2 .B (by intro h; cases h), hK.tbl], by rw [hst2, hK.stk], by omega⟩
    refine ⟨by rw [hn', hn2, hK.nodes], (hR2.trans hR).mono (by simp only [List.length_cons]; omega),
      hF'.congr ?_⟩
    intro m _
    simp only [List.mem_cons]
    tauto

/-- `mark` flags each member of a list of names, and changes nothing else. -/
theorem flag_list_spec (hnm : Function.Injective nm) {U : List Name} (xs : List Name)
    (s : store.Store) (list : store.TermId) (F : Name → Prop) (hW : Wf s)
    (hl : Repr nm s.nodes.val list.val (namesPat (nm none) xs)) (hF : Flagged nm s U F)
    (hroom : Room s (2 * xs.length + 1)) :
    sorts.mark s list ⦃ s' =>
      s'.nodes.val = s.nodes.val ∧ RanA s s' (2 * xs.length + 1) ∧
        Flagged nm s' U (fun m => F m ∨ m ∈ xs) ⦄ :=
  flag_list_loop_spec hnm xs s list F hW hl hF hroom

/-! ## The flagged names, as a list -/

theorem pick_loop_spec (hnm : Function.Injective nm) {U : List Name} :
    ∀ (ns : List Name) (s : store.Store) (names out : store.TermId) (acc : List Name)
      (F : Name → Prop), Wf s →
    Repr nm s.nodes.val names.val (namesPat (nm none) ns) → (∀ n ∈ ns, n ∈ U) →
    Flagged nm s U F → Repr nm s.nodes.val out.val (namesPat (nm none) acc) →
    Room s (3 * ns.length + 1) →
    sorts.pick_loop names s out ⦃ r s' =>
      Ran s s' (3 * ns.length + 1) ∧
        Repr nm s'.nodes.val r.val (namesPat (nm none) (conjList ns F ++ acc)) ⦄ := by
  intro ns
  induction ns with
  | nil =>
    intro s names out acc F hW hl hU hF ho hroom
    unfold sorts.pick_loop
    rw [loop]
    simp only [sorts.pick_loop.body]
    step with uncons_repr s names hW hl (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    subst hu
    have hfin : Ran s s1 (3 * ([] : List Name).length + 1) ∧
        Repr nm s1.nodes.val out.val (namesPat (nm none) (conjList [] F ++ acc)) :=
      ⟨hK.ran, by rw [hK.nodes]; simpa [conjList_nil] using ho⟩
    step*
  | cons x ns ih =>
    intro s names out acc F hW hl hU hF ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.pick_loop
    rw [loop]
    simp only [sorts.pick_loop.body]
    step with uncons_repr s names hW hl (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    obtain ⟨h, t, rfl, rh, rt⟩ := hu
    simp only at hK
    have ht1 := hK.ticks
    have rh1 : Repr nm s1.nodes.val h.val (.sym x) := by rw [hK.nodes]; exact rh
    have hF1 : Flagged nm s1 U F := hF.mono hK.ran.ext (by rw [hK.tbl])
    have hfx := hF1.iff hnm hK.wf (hU x (List.mem_cons_self ..)) rh1
    step with get_flag_w s1 .A h hK.wf rh1.lt (by unfold Room; omega) as ⟨r1, hfl, hK2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hfl hK2
    have ht2 := hK2.ticks
    have hR2 : Ran s s2 2 := (hK.ran.trans hK2.ran)
    have hx2 := hR2.ext
    have hF2 : Flagged nm s2 U F := hF.mono hx2 (by rw [hR2.tbl])
    have hU' : ∀ n ∈ ns, n ∈ U := fun n hn => hU n (List.mem_cons_of_mem _ hn)
    by_cases hx : F x
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hfx.2 hx)
      rw [hv] at hfl
      simp only [Option.map_some] at hfl
      subst hfl
      step with alloc_w s2 (.App h out) hK2.wf
        (by rw [hK2.nodes, hK.nodes]; exact ⟨rh.lt, ho.lt⟩) (by unfold Room; omega)
        as ⟨r3, hW3, ht3, htb3, hx3, hid, hst3⟩
      obtain ⟨out1, s3⟩ := r3
      simp only at hW3 ht3 htb3 hx3 hid hst3 ⊢
      have hxe : Extends s s3 := hx2.trans hx3
      have hout1 : Repr nm s3.nodes.val out1.val (namesPat (nm none) (x :: acc)) := by
        simp only [namesPat, List.map_cons, encList]
        exact .app hid (hxe.repr rh) (hxe.repr ho)
      have IH := ih s3 t out1 (x :: acc) F hW3 (hxe.repr rt) hU'
        (hF2.mono hx3 (by rw [htb3])) hout1 (by unfold Room; omega)
      unfold sorts.pick_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hr⟩
      have hR3 : Ran s s3 3 :=
        ⟨hW3, hxe, by rw [htb3, hR2.tbl], by rw [hst3, hR2.stk], by omega⟩
      refine ⟨(hR3.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
      have e : conjList (x :: ns) F ++ acc = conjList ns F ++ x :: acc := by
        simp [conjList_cons_pos hx]
      rw [e]
      exact hr
    · have hnone : (tbl s1 .A h.val) = none := by
        cases hv : tbl s1 .A h.val with
        | none => rfl
        | some v => exact absurd (hfx.1 (by simp [hv])) hx
      rw [hnone] at hfl
      simp only [Option.map_none] at hfl
      subst hfl
      have IH := ih s2 t out acc F hK2.wf (hx2.repr rt) hU' hF2 (hx2.repr ho)
        (by unfold Room; omega)
      unfold sorts.pick_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hr⟩
      refine ⟨(hR2.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
      have e : conjList (x :: ns) F = conjList ns F := conjList_cons_neg hx ns
      rw [e]
      exact hr

/-- `pick` lists the names of `ns` that table `A` flags, the first last. -/
theorem pick_spec (hnm : Function.Injective nm) {U : List Name} (ns : List Name)
    (s : store.Store) (names : store.TermId) (F : Name → Prop) (hW : Wf s)
    (hl : Repr nm s.nodes.val names.val (namesPat (nm none) ns)) (hU : ∀ n ∈ ns, n ∈ U)
    (hF : Flagged nm s U F) (hroom : Room s (3 * ns.length + 2)) :
    sorts.pick s names ⦃ r s' =>
      Ran s s' (3 * ns.length + 2) ∧
        Repr nm s'.nodes.val r.val (namesPat (nm none) (conjList ns F)) ⦄ := by
  unfold sorts.pick
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨out, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have IH := pick_loop_spec hnm ns s1 names out [] F hW1 (hx1.repr hl) hU
    (hF.mono hx1 (by rw [htb1])) (.nil hid) (by unfold Room; omega)
  refine WP.spec_mono IH ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  have hR1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  exact ⟨(hR1.trans hR).mono (by omega), by simpa using hr⟩

/-! ## Building a conjunction -/

/-- `conj_of` gives the conjunction of the sorts of a list: one identifier
for one set of sorts. -/
theorem conj_of_spec (hnm : Function.Injective nm) (U xs : List Name) (s : store.Store)
    (names list : store.TermId) (hW : Wf s)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hl : Repr nm s.nodes.val list.val (namesPat (nm none) xs))
    (hroom : Room s (2 * xs.length + 3 * U.length + 4)) :
    sorts.conj_of s names list ⦃ r s' =>
      RanA s s' (2 * xs.length + 3 * U.length + 4) ∧
        Repr nm s'.nodes.val r.val (namesPat (nm none) (conjList U (· ∈ xs))) ⦄ := by
  unfold sorts.conj_of
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_w s .A hW (by unfold Room; omega) as ⟨s1, hn1, ht1, hW1, hA1, hB1, hst1⟩
  have hx1 : Extends s s1 := Extends.of_eq hn1 (by omega)
  have hF1 : Flagged nm s1 U (fun _ => False) :=
    Flagged.clear (fun n hn => namesPat_mem (hx1.repr hU) n hn) hA1
  step with flag_list_spec hnm xs s1 list _ hW1 (hx1.repr hl) hF1 (by unfold Room; omega)
    as ⟨s2, hn2, hR2, hF2⟩
  have ht2 := hR2.ticks
  have hF2' : Flagged nm s2 U (· ∈ xs) := hF2.congr (by simp)
  have IH := pick_spec hnm U s2 names (· ∈ xs) hR2.wf (hR2.ext.repr (hx1.repr hU))
    (fun _ h => h) hF2' (by unfold Room; omega)
  refine WP.spec_mono IH ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  have hR1 : RanA s s1 1 :=
    ⟨hW1, hx1, by rw [hB1 .B (by intro h; cases h)], hst1, by omega⟩
  exact ⟨((hR1.trans hR2).trans hR.ranA).mono (by omega), hr⟩

/-- `conj_meet` gives the conjunction of two conjunctions: the sorts of
either. -/
theorem conj_meet_spec (hnm : Function.Injective nm) (U xs ys : List Name) (s : store.Store)
    (names a b : store.TermId) (hW : Wf s)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ha : Repr nm s.nodes.val a.val (namesPat (nm none) xs))
    (hb : Repr nm s.nodes.val b.val (namesPat (nm none) ys))
    (hroom : Room s (2 * xs.length + 2 * ys.length + 3 * U.length + 5)) :
    sorts.conj_meet s names a b ⦃ r s' =>
      RanA s s' (2 * xs.length + 2 * ys.length + 3 * U.length + 5) ∧
        Repr nm s'.nodes.val r.val
          (namesPat (nm none) (conjList U (fun m => m ∈ xs ∨ m ∈ ys))) ⦄ := by
  unfold sorts.conj_meet
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_w s .A hW (by unfold Room; omega) as ⟨s1, hn1, ht1, hW1, hA1, hB1, hst1⟩
  have hx1 : Extends s s1 := Extends.of_eq hn1 (by omega)
  have hF1 : Flagged nm s1 U (fun _ => False) :=
    Flagged.clear (fun n hn => namesPat_mem (hx1.repr hU) n hn) hA1
  step with flag_list_spec hnm xs s1 a _ hW1 (hx1.repr ha) hF1 (by unfold Room; omega)
    as ⟨s2, hn2, hR2, hF2⟩
  have ht2 := hR2.ticks
  step with flag_list_spec hnm ys s2 b _ hR2.wf (hR2.ext.repr (hx1.repr hb)) hF2
    (by unfold Room; omega) as ⟨s3, hn3, hR3, hF3⟩
  have ht3 := hR3.ticks
  have hF3' : Flagged nm s3 U (fun m => m ∈ xs ∨ m ∈ ys) := hF3.congr (by simp)
  have IH := pick_spec hnm U s3 names (fun m => m ∈ xs ∨ m ∈ ys) hR3.wf
    (hR3.ext.repr (hR2.ext.repr (hx1.repr hU))) (fun _ h => h) hF3' (by unfold Room; omega)
  refine WP.spec_mono IH ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  have hR1 : RanA s s1 1 :=
    ⟨hW1, hx1, by rw [hB1 .B (by intro h; cases h)], hst1, by omega⟩
  exact ⟨(((hR1.trans hR2).trans hR3).trans hR.ranA).mono (by omega), hr⟩

/-! ## The step of each sort of a conjunction -/

/-- What a sort gives each argument, as a term. -/
def rowPat (z : Sym) (ks : List (Option Name)) : Pat := encList z (ks.map (kidPat z))

/-- The step of each sort of a list, or nothing when one has none. -/
def stepAll (S : Sorts) (f : Sym) (m : Nat) : List Name → Option (List (List (Option Name)))
  | [] => some []
  | n :: ns =>
    match Sorts.step S n f m with
    | none => none
    | some ks => (stepAll S f m ns).map (ks :: ·)

theorem rows_done (s : store.Store) (decls head args out c : store.TermId) (ok1 : Bool) :
    sorts.rows_loop s decls head args out c ok1 false ⦃ r => r = (s, out, ok1) ⦄ := by
  unfold sorts.rows_loop
  rw [loop]
  simp only [sorts.rows_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem rows_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) {f : Sym} {ag : List Pat} :
    ∀ (cs : List Name) (s : store.Store) (decls head args out c : store.TermId)
      (acc : List (List (Option Name))), Wf s →
    Repr nm s.nodes.val decls.val sp → Repr nm s.nodes.val head.val (.sym f) →
    Repr nm s.nodes.val args.val (encList (nm none) ag) →
    Repr nm s.nodes.val c.val (namesPat (nm none) cs) →
    Repr nm s.nodes.val out.val (encList (nm none) (acc.map (rowPat (nm none)))) →
    Room s (cs.length * (stepCost S ag.length + 2) + 1) →
    sorts.rows_loop s decls head args out c true true ⦃ r =>
      Ran s r.1 (cs.length * (stepCost S ag.length + 2) + 1) ∧
        match stepAll S f ag.length cs with
        | some rs => r.2.2 = true ∧
            Repr nm r.1.nodes.val r.2.1.val
              (encList (nm none) ((rs.reverse ++ acc).map (rowPat (nm none))))
        | none => r.2.2 = false ⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro s decls head args out c acc hW hd hh ha hc ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.rows_loop
    rw [loop]
    simp only [sorts.rows_loop.body, ↓reduceIte]
    step with uncons_repr s c hW hc (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := rows_done s1 decls head args out c true
    unfold sorts.rows_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by omega), by simpa [stepAll] using (by rw [hK.nodes]; exact ho)⟩
  | cons x cs ih =>
    intro s decls head args out c acc hW hd hh ha hc ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    unfold sorts.rows_loop
    rw [loop]
    simp only [sorts.rows_loop.body, ↓reduceIte]
    step with uncons_repr s c hW hc (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    obtain ⟨n, t, rfl, rn, rt⟩ := hu
    have ht1 := hK.ticks
    have hx1 := hK.ran.ext
    step with step_spec hnm S hS s1 decls n head args hK.wf (hx1.repr hd) (hx1.repr rn)
      (hx1.repr hh) (hx1.repr ha) (by unfold Room; omega) as ⟨r1, hR2, hst⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hR2 hst
    have ht2 := hR2.ticks
    have R2 := hK.ran.trans hR2
    cases hstep : Sorts.step S x f ag.length with
    | none =>
      rw [hstep] at hst
      subst hst
      simp only [uncurry, bind_ok]
      have hdn := rows_done s2 decls head args out c false
      unfold sorts.rows_loop at hdn
      refine WP.spec_mono hdn ?_
      rintro r rfl
      refine ⟨R2.mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega), ?_⟩
      simp [stepAll, hstep]
    | some ks =>
      rw [hstep] at hst
      obtain ⟨k, rfl, rk⟩ := hst
      step with alloc_w s2 (.App k out) hR2.wf ⟨rk.lt, (R2.ext.repr ho).lt⟩
        (by unfold Room; omega) as ⟨r3, hW3, ht3, htb3, hx3, hid, hst3⟩
      obtain ⟨out1, s3⟩ := r3
      simp only at hW3 ht3 htb3 hx3 hid hst3 ⊢
      have R3 : Ran s s3 (stepCost S ag.length + 2) :=
        ⟨hW3, R2.ext.trans hx3, by rw [htb3, R2.tbl], by rw [hst3, R2.stk], by omega⟩
      have hout1 : Repr nm s3.nodes.val out1.val
          (encList (nm none) ((ks :: acc).map (rowPat (nm none)))) := by
        simp only [List.map_cons, encList]
        exact .app hid (hx3.repr rk) (R3.ext.repr ho)
      have IH := ih s3 decls head args out1 t (ks :: acc) hW3 (R3.ext.repr hd) (R3.ext.repr hh)
        (R3.ext.repr ha) (R3.ext.repr rt) hout1 (by unfold Room; omega)
      unfold sorts.rows_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R3.trans hR).mono
        (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega), ?_⟩
      simp only [stepAll, hstep]
      cases hall : stepAll S f ag.length cs with
      | none => rw [hall] at hr; simpa using hr
      | some rs =>
        rw [hall] at hr
        simpa [List.reverse_cons, List.append_assoc] using hr

/-- `rows` gives the step of each sort of a list, the first last, or nothing
when one of them has none. -/
theorem rows_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) {f : Sym} {ag : List Pat} (cs : List Name) (s : store.Store)
    (decls c head args : store.TermId) (hW : Wf s)
    (hd : Repr nm s.nodes.val decls.val sp) (hh : Repr nm s.nodes.val head.val (.sym f))
    (ha : Repr nm s.nodes.val args.val (encList (nm none) ag))
    (hc : Repr nm s.nodes.val c.val (namesPat (nm none) cs))
    (hroom : Room s (cs.length * (stepCost S ag.length + 2) + 2)) :
    sorts.rows s decls c head args ⦃ o s' =>
      Ran s s' (cs.length * (stepCost S ag.length + 2) + 2) ∧
        match stepAll S f ag.length cs with
        | some rs => ∃ r, o = some r ∧
            Repr nm s'.nodes.val r.val (encList (nm none) (rs.reverse.map (rowPat (nm none))))
        | none => o = none ⦄ := by
  unfold sorts.rows
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨out, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have hR1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  step with rows_loop_spec hnm S hS cs s1 decls head args out c [] hW1 (hx1.repr hd)
    (hx1.repr hh) (hx1.repr ha) (hx1.repr hc) (.nil hid) (by unfold Room; omega) as ⟨s2, out1, ok1, hR, hr⟩
  have R := (hR1.trans hR).mono (m := cs.length * (stepCost S ag.length + 2) + 2) (by omega)
  cases hall : stepAll S f ag.length cs with
  | none =>
    rw [hall] at hr
    simp only at hr
    subst hr
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨R, rfl⟩
  | some rs =>
    rw [hall] at hr
    obtain ⟨rfl, hr⟩ := hr
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨R, out1, rfl, by simpa using hr⟩

/-! ## The first member of each row -/

theorem heads_loop_spec (hnm : Function.Injective nm) {U : List Name} :
    ∀ (rs : List (List (Option Name))) (s : store.Store) (rows out : store.TermId)
      (acc : List (List (Option Name))) (F : Name → Prop), Wf s →
    Repr nm s.nodes.val rows.val (encList (nm none) (rs.map (rowPat (nm none)))) →
    (∀ r ∈ rs, r ≠ []) → (∀ r ∈ rs, ∀ m, some m ∈ r → m ≠ nm none) → Flagged nm s U F →
    Repr nm s.nodes.val out.val (encList (nm none) (acc.map (rowPat (nm none)))) →
    Room s (5 * rs.length + 1) →
    sorts.heads_loop rows s out ⦃ r s' =>
      RanA s s' (5 * rs.length + 1) ∧
        Flagged nm s' U (fun m => F m ∨ ∃ r ∈ rs, r.head? = some (some m)) ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) (((rs.map List.tail).reverse ++ acc).map (rowPat (nm none)))) ⦄ := by
  intro rs
  induction rs with
  | nil =>
    intro s rows out acc F hW hl hne hz hF ho hroom
    unfold sorts.heads_loop
    rw [loop]
    simp only [sorts.heads_loop.body]
    step with uncons_repr s rows hW hl (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    have hfin : RanA s s1 (5 * ([] : List (List (Option Name))).length + 1) ∧
        Flagged nm s1 U (fun m => F m ∨ ∃ r ∈ ([] : List (List (Option Name))),
          r.head? = some (some m)) ∧
        Repr nm s1.nodes.val out.val (encList (nm none)
          ((((([] : List (List (Option Name))).map List.tail).reverse ++ acc).map
            (rowPat (nm none))))) :=
      ⟨hK.ran.ranA, (hF.mono hK.ran.ext (by rw [hK.tbl])).congr (by simp),
        by rw [hK.nodes]; simpa using ho⟩
    step*
  | cons x rs ih =>
    intro s rows out acc F hW hl hne hz hF ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.heads_loop
    rw [loop]
    simp only [sorts.heads_loop.body]
    step with uncons_repr s rows hW hl (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨r, more, rfl, rr, rmore⟩ := hu
    have ht1 := hK.ticks
    have hx1 := hK.ran.ext
    obtain ⟨k0, ktl, rfl⟩ : ∃ k0 ktl, x = k0 :: ktl := by
      cases x with
      | nil => exact absurd rfl (hne [] (List.mem_cons_self ..))
      | cons a b => exact ⟨a, b, rfl⟩
    step with uncons_repr s1 r hK.wf (hx1.repr rr) (by unfold Room; omega) as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [rowPat] at hu2
    simp only at hK2
    obtain ⟨k, kt, rfl, rk, rkt⟩ := hu2
    rw [hK.nodes] at rk rkt
    have ht2 := hK2.ticks
    have R2 := hK.ran.trans hK2.ran
    have hk0 : ∀ m, k0 = some m → m ≠ nm none := fun m e =>
      hz _ (List.mem_cons_self ..) m (by rw [e]; exact List.mem_cons_self ..)
    step with is_nil_kid hnm s2 k hK2.wf (R2.ext.repr rk) hk0 (by unfold Room; omega)
      as ⟨r3, hb, hK3⟩
    obtain ⟨b, s3⟩ := r3
    simp only at hb hK3 ⊢
    have ht3 := hK3.ticks
    have R3 := R2.trans hK3.ran
    have hF3 : Flagged nm s3 U F := hF.mono R3.ext (by rw [R3.tbl])
    have hne' : ∀ r ∈ rs, r ≠ [] := fun r hr => hne r (List.mem_cons_of_mem _ hr)
    have hz' : ∀ r ∈ rs, ∀ m, some m ∈ r → m ≠ nm none :=
      fun r hr => hz r (List.mem_cons_of_mem _ hr)
    cases k0 with
    | none =>
      rw [show b = true from hb.2 rfl]
      simp only [uncurry, ↓reduceIte, bind_ok]
      have R4 : RanA s s3 4 := R3.ranA.mono (by omega)
      have ht4' := (R4).ticks
      step with alloc_w s3 (.App kt out) (R4).wf
        ⟨((R4).ext.repr rkt).lt, ((R4).ext.repr ho).lt⟩
        (by unfold Room; omega) as ⟨r5, hW5, ht5, htb5, hx5, hid, hst5⟩
      obtain ⟨out1, s5⟩ := r5
      simp only at hW5 ht5 htb5 hx5 hid hst5 ⊢
      have R5 : RanA s s5 5 :=
        ⟨hW5, (R4).ext.trans hx5, by rw [htb5, (R4).tbl], by rw [hst5, (R4).stk], by omega⟩
      have hout1 : Repr nm s5.nodes.val out1.val
          (encList (nm none) ((ktl :: acc).map (rowPat (nm none)))) := by
        simp only [List.map_cons, encList, rowPat]
        exact .app hid (R5.ext.repr rkt) (R5.ext.repr ho)
      have IH := ih s5 more out1 (ktl :: acc) (F) hW5 (R5.ext.repr rmore) hne' hz'
        ((hF3).mono hx5 (by rw [htb5])) hout1 (by unfold Room; omega)
      unfold sorts.heads_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hF', hr⟩
      refine ⟨(R5.trans hR).mono (by simp only [List.length_cons]; omega), hF'.congr (by intro m _; simp), ?_⟩
      simpa [List.reverse_cons, List.append_assoc] using hr
    | some m0 =>
      have hbf : b = false := by
        cases b with
        | false => rfl
        | true => cases hb.1 rfl
      rw [hbf]
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
      have rk3 : Repr nm s3.nodes.val k.val (.sym m0) := R3.ext.repr (by simpa [kidPat] using rk)
      step with set_flag_w s3 .A k true hK3.wf rk3.lt (by unfold Room; omega)
        as ⟨s4, hn4, ht4, hW4, hA4, hB4, hst4⟩
      have R4 : RanA s s4 4 :=
        ⟨hW4, R3.ext.trans (Extends.of_eq hn4 (by omega)),
          by rw [hB4 .B (by intro h; cases h), R3.tbl], by rw [hst4, R3.stk], by omega⟩
      have hG := hF3.set hnm hK3.wf hn4 hA4 rk3
      have hiff : ∀ m ∈ U, ((F m ∨ m = m0) ∨ ∃ r ∈ rs, r.head? = some (some m)) ↔
          (F m ∨ ∃ r ∈ (some m0 :: ktl) :: rs, r.head? = some (some m)) := by
        intro m _
        simp only [List.mem_cons, exists_eq_or_imp, List.head?_cons, Option.some.injEq]
        have : (m0 = m) ↔ (m = m0) := eq_comm
        rw [this]
        tauto
      have ht4' := (R4).ticks
      step with alloc_w s4 (.App kt out) (R4).wf
        ⟨((R4).ext.repr rkt).lt, ((R4).ext.repr ho).lt⟩
        (by unfold Room; omega) as ⟨r5, hW5, ht5, htb5, hx5, hid, hst5⟩
      obtain ⟨out1, s5⟩ := r5
      simp only at hW5 ht5 htb5 hx5 hid hst5 ⊢
      have R5 : RanA s s5 5 :=
        ⟨hW5, (R4).ext.trans hx5, by rw [htb5, (R4).tbl], by rw [hst5, (R4).stk], by omega⟩
      have hout1 : Repr nm s5.nodes.val out1.val
          (encList (nm none) ((ktl :: acc).map (rowPat (nm none)))) := by
        simp only [List.map_cons, encList, rowPat]
        exact .app hid (R5.ext.repr rkt) (R5.ext.repr ho)
      have IH := ih s5 more out1 (ktl :: acc) (fun m => F m ∨ m = m0) hW5 (R5.ext.repr rmore) hne' hz'
        ((hG).mono hx5 (by rw [htb5])) hout1 (by unfold Room; omega)
      unfold sorts.heads_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hF', hr⟩
      refine ⟨(R5.trans hR).mono (by simp only [List.length_cons]; omega), hF'.congr hiff, ?_⟩
      simpa [List.reverse_cons, List.append_assoc] using hr

/-- `heads` flags the first member of each row that is a sort, and gives the
rows without their first members, the first row last. -/
theorem heads_spec (hnm : Function.Injective nm) {U : List Name}
    (rs : List (List (Option Name))) (s : store.Store) (rows : store.TermId) (F : Name → Prop)
    (hW : Wf s) (hl : Repr nm s.nodes.val rows.val (encList (nm none) (rs.map (rowPat (nm none)))))
    (hne : ∀ r ∈ rs, r ≠ []) (hz : ∀ r ∈ rs, ∀ m, some m ∈ r → m ≠ nm none)
    (hF : Flagged nm s U F) (hroom : Room s (5 * rs.length + 2)) :
    sorts.heads s rows ⦃ r s' =>
      RanA s s' (5 * rs.length + 2) ∧
        Flagged nm s' U (fun m => F m ∨ ∃ r ∈ rs, r.head? = some (some m)) ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) ((rs.map List.tail).reverse.map (rowPat (nm none)))) ⦄ := by
  unfold sorts.heads
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨out, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have IH := heads_loop_spec hnm rs s1 rows out [] F hW1 (hx1.repr hl) hne hz
    (hF.mono hx1 (by rw [htb1])) (.nil hid) (by unfold Room; omega)
  refine WP.spec_mono IH ?_
  rintro ⟨r, s'⟩ ⟨hR, hF', hr⟩
  have hR1 : RanA s s1 1 := ⟨hW1, hx1, by rw [htb1], hst1, by omega⟩
  exact ⟨(hR1.trans hR).mono (by omega), hF', by simpa using hr⟩

/-! ## One step of a conjunction -/

/-- The rows give the sort `m` to the argument at position `i`. -/
def colF (rs : List (List (Option Name))) (i : Nat) (m : Name) : Prop :=
  ∃ r ∈ rs, r[i]? = some (some m)

/-- The conjunction of each argument, as terms. -/
noncomputable def kidsPats (z : Sym) (U : List Name) (rs : List (List (Option Name))) (k : Nat) :
    List Pat :=
  (List.range k).map fun i => namesPat z (conjList U (colF rs i))

theorem colF_tails (rs : List (List (Option Name))) (i : Nat) (m : Name) :
    colF (rs.map List.tail).reverse i m ↔ colF rs (i + 1) m := by
  simp only [colF, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
    exact ⟨r, hr, by
          cases r with
          | nil => simp at h
          | cons _ _ => simpa using h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by
          cases r with
          | nil => simp at h
          | cons _ _ => simpa using h⟩

theorem kidsPats_succ (z : Sym) (U : List Name) (rs : List (List (Option Name))) (k : Nat) :
    kidsPats z U rs (k + 1) =
      namesPat z (conjList U (colF rs 0)) :: kidsPats z U (rs.map List.tail).reverse k := by
  simp only [kidsPats, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  rw [conjList_congr fun m _ => (colF_tails rs i m).symm]

theorem step_conj_loop_spec (hnm : Function.Injective nm) {U : List Name} :
    ∀ (ag : List Pat) (rs : List (List (Option Name))) (s : store.Store)
      (args names rows : store.TermId) (ts : List Pat), Wf s →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val args.val (encList (nm none) ag) →
    Repr nm s.nodes.val rows.val (encList (nm none) (rs.map (rowPat (nm none)))) →
    (∀ r ∈ rs, r.length = ag.length) → (∀ r ∈ rs, ∀ m, some m ∈ r → m ≠ nm none) →
    List.Forall₂ (fun f t => Repr nm s.nodes.val (fkey f) t) (stk s) ts →
    Room s (ag.length * (5 * rs.length + 3 * U.length + 7) + 1) →
    sorts.step_conj_loop args s names rows ⦃ s' =>
      Wf s' ∧ Extends s s' ∧ tbl s' .B = tbl s .B ∧
        s'.ticks.val ≤ s.ticks.val + (ag.length * (5 * rs.length + 3 * U.length + 7) + 1) ∧
        (stk s').length = (stk s).length + ag.length ∧
        List.Forall₂ (fun f t => Repr nm s'.nodes.val (fkey f) t) (stk s')
          ((kidsPats (nm none) U rs ag.length).reverse ++ ts) ⦄ := by
  intro ag
  induction ag with
  | nil =>
    intro rs s args names rows ts hW hU ha hrows hlen hz hstk hroom
    unfold sorts.step_conj_loop
    rw [loop]
    simp only [sorts.step_conj_loop.body]
    step with uncons_repr s args hW ha (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    subst hu
    have hfin : Wf s1 ∧ Extends s s1 ∧ tbl s1 .B = tbl s .B ∧
        s1.ticks.val ≤ s.ticks.val +
          (([] : List Pat).length * (5 * rs.length + 3 * U.length + 7) + 1) ∧
        (stk s1).length = (stk s).length + ([] : List Pat).length ∧
        List.Forall₂ (fun f t => Repr nm s1.nodes.val (fkey f) t) (stk s1)
          ((kidsPats (nm none) U rs ([] : List Pat).length).reverse ++ ts) := by
      refine ⟨hK.wf, hK.ran.ext, by rw [hK.tbl], by have := hK.ticks; simp; omega,
        by rw [hK.stk]; simp, ?_⟩
      rw [hK.stk, hK.nodes]
      simpa [kidsPats] using hstk
    step*
  | cons a ag ih =>
    intro rs s args names rows ts hW hU ha hrows hlen hz hstk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    unfold sorts.step_conj_loop
    rw [loop]
    simp only [sorts.step_conj_loop.body]
    step with uncons_repr s args hW ha (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    obtain ⟨h, t, rfl, -, rt⟩ := hu
    have ht1 := hK.ticks
    have hx1 := hK.ran.ext
    step with clear_w s1 .A hK.wf (by unfold Room; omega) as ⟨s2, hn2, ht2, hW2, hA2, hB2, hst2⟩
    have hx2 : Extends s s2 := hx1.trans (Extends.of_eq hn2 (by omega))
    have hF2 : Flagged nm s2 U (fun _ => False) :=
      Flagged.clear (fun n hn => namesPat_mem (hx2.repr hU) n hn) hA2
    have hne : ∀ r ∈ rs, r ≠ [] := by
      intro r hr e
      have := hlen r hr
      rw [e] at this
      simp at this
    step with heads_spec hnm rs s2 rows _ hW2 (hx2.repr hrows) hne hz hF2 (by unfold Room; omega)
      as ⟨r3, hR3, hF3, hr3⟩
    obtain ⟨rows1, s3⟩ := r3
    simp only at hR3 hF3 hr3
    have ht3 := hR3.ticks
    have hx3 := hx2.trans hR3.ext
    have hF3' : Flagged nm s3 U (colF rs 0) := hF3.congr (by
      intro m _
      simp only [false_or, colF]
      constructor
      · rintro ⟨r, hr, h⟩
        exact ⟨r, hr, by
          cases r with
          | nil => simp at h
          | cons _ _ => simpa using h⟩
      · rintro ⟨r, hr, h⟩
        exact ⟨r, hr, by
          cases r with
          | nil => simp at h
          | cons _ _ => simpa using h⟩)
    step with pick_spec hnm U s3 names _ hR3.wf (hx3.repr hU) (fun _ h => h) hF3'
      (by unfold Room; omega) as ⟨r4, hR4, hr4⟩
    obtain ⟨k, s4⟩ := r4
    simp only at hR4 hr4
    have ht4 := hR4.ticks
    have hx4 := hx3.trans hR4.ext
    step with push_w s4 (.Visit k k) hR4.wf (by unfold Room; omega) as ⟨s5, p1, p2, p3, hW5, p5⟩
    have hx5 : Extends s s5 := hx4.trans (Extends.of_eq p1 (by omega))
    have hx45 : Extends s4 s5 := Extends.of_eq p1 (by omega)
    have hstk5 : stk s5 = .Visit k k :: stk s := by
      rw [p5, hR4.stk, hR3.stk, hst2, hK.stk]
    have hF5 : List.Forall₂ (fun f t => Repr nm s5.nodes.val (fkey f) t) (stk s5)
        (namesPat (nm none) (conjList U (colF rs 0)) :: ts) := by
      rw [hstk5]
      exact .cons (hx45.repr hr4) (hstk.imp fun _ _ h => hx5.repr h)
    have hlen' : ∀ r ∈ (rs.map List.tail).reverse, r.length = ag.length := by
      intro r hr
      simp only [List.mem_reverse, List.mem_map] at hr
      obtain ⟨r0, hr0, rfl⟩ := hr
      have := hlen r0 hr0
      simp only [List.length_cons] at this
      simp [this]
    have hz' : ∀ r ∈ (rs.map List.tail).reverse, ∀ m, some m ∈ r → m ≠ nm none := by
      intro r hr m hm
      simp only [List.mem_reverse, List.mem_map] at hr
      obtain ⟨r0, hr0, rfl⟩ := hr
      exact hz r0 hr0 m (List.mem_of_mem_tail hm)
    have hrl : ((rs.map List.tail).reverse).length = rs.length := by simp
    have IH := ih (rs.map List.tail).reverse s5 t names rows1 _ hW5 (hx5.repr hU) (hx5.repr rt)
      ((hx45.trans (Extends.refl _)).repr (hR4.ext.repr hr3)) hlen' hz' hF5
      (by rw [hrl]; unfold Room; omega)
    unfold sorts.step_conj_loop at IH
    simp only [uncurry]
    refine WP.spec_mono IH ?_
    rintro s' ⟨hW', hx', hB', ht', hsl, hfr⟩
    rw [hrl] at ht'
    refine ⟨hW', hx5.trans hx', ?_, ?_, ?_, ?_⟩
    · rw [hB', p2, hR4.tbl, hR3.tbl, hB2 .B (by intro h; cases h), hK.tbl]
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · rw [hsl, hstk5]; simp only [List.length_cons]; omega
    · rw [List.length_cons, kidsPats_succ, List.reverse_cons, List.append_assoc]
      simpa using hfr

theorem stepAll_length {S : Sorts} {f : Sym} {m : Nat} :
    ∀ {cs : List Name} {rs : List (List (Option Name))}, stepAll S f m cs = some rs →
      rs.length = cs.length
  | [], rs, h => by simp only [stepAll, Option.some.injEq] at h; subst h; rfl
  | n :: ns, rs, h => by
    simp only [stepAll] at h
    cases hs : Sorts.step S n f m with
    | none => simp [hs] at h
    | some ks =>
      cases ha : stepAll S f m ns with
      | none => simp [hs, ha] at h
      | some rs' =>
        simp only [hs, ha, Option.map_some, Option.some.injEq] at h
        subst h
        simp [stepAll_length ha]

/-- The rows are the steps of the sorts. -/
theorem mem_stepAll {S : Sorts} {f : Sym} {m : Nat} :
    ∀ {cs : List Name} {rs : List (List (Option Name))}, stepAll S f m cs = some rs →
      ∀ r, r ∈ rs ↔ ∃ n ∈ cs, Sorts.step S n f m = some r
  | [], rs, h, r => by simp only [stepAll, Option.some.injEq] at h; subst h; simp
  | n :: ns, rs, h, r => by
    simp only [stepAll] at h
    cases hs : Sorts.step S n f m with
    | none => simp [hs] at h
    | some ks =>
      cases ha : stepAll S f m ns with
      | none => simp [hs, ha] at h
      | some rs' =>
        simp only [hs, ha, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [List.mem_cons, exists_eq_or_imp, hs, Option.some.injEq, mem_stepAll ha r]
        constructor
        · rintro (rfl | h)
          · exact Or.inl rfl
          · exact Or.inr h
        · rintro (rfl | h)
          · exact Or.inl rfl
          · exact Or.inr h

/-- Some sort has no step exactly when the rows are nothing. -/
theorem stepAll_eq_none {S : Sorts} {f : Sym} {m : Nat} :
    ∀ {cs : List Name}, stepAll S f m cs = none ↔ ∃ n ∈ cs, Sorts.step S n f m = none
  | [] => by simp [stepAll]
  | n :: ns => by
    simp only [stepAll, List.mem_cons, exists_eq_or_imp]
    cases hs : Sorts.step S n f m with
    | none => simp
    | some ks => simp [stepAll_eq_none (cs := ns)]

theorem kidsPats_congr (z : Sym) (U : List Name) {rs rs' : List (List (Option Name))}
    (h : ∀ r, r ∈ rs ↔ r ∈ rs') (k : Nat) : kidsPats z U rs k = kidsPats z U rs' k := by
  simp only [kidsPats]
  apply List.map_congr_left
  intro i _
  rw [conjList_congr]
  intro m _
  simp only [colF, h]

/-- The ticks one step of a conjunction of `c` sorts may spend, on `m`
arguments, with `u` names in all. -/
def stepConjCost (S : Sorts) (u c m : Nat) : Nat :=
  c * (stepCost S m + 2) + m * (5 * c + 3 * u + 9) + 5

/-- `step_conj` gives, for each argument, the conjunction of the sorts the
members of the list give it, or nothing when one of them has no step. No name
a step gives is the end of a list. Table `B` is left as it was. -/
theorem step_conj_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) {f : Sym} {ag : List Pat} (U cs : List Name)
    (s : store.Store) (decls names c head args : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hc : Repr nm s.nodes.val c.val (namesPat (nm none) cs))
    (hh : Repr nm s.nodes.val head.val (.sym f))
    (ha : Repr nm s.nodes.val args.val (encList (nm none) ag))
    (hz : ∀ n ∈ cs, ∀ ks, Sorts.step S n f ag.length = some ks → ∀ m, some m ∈ ks → m ≠ nm none)
    (hroom : Room s (stepConjCost S U.length cs.length ag.length)) :
    sorts.step_conj s decls names c head args ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' .B = tbl s .B ∧
        s'.ticks.val ≤ s.ticks.val + stepConjCost S U.length cs.length ag.length ∧
        match stepAll S f ag.length cs with
        | some rs => ∃ r, o = some r ∧
            Repr nm s'.nodes.val r.val (encList (nm none) (kidsPats (nm none) U rs ag.length))
        | none => o = none ⦄ := by
  unfold sorts.step_conj
  have hroom' := hroom
  unfold Room stepConjCost at hroom'
  have hmul : ag.length * (5 * cs.length + 3 * U.length + 9) =
      ag.length * (5 * cs.length + 3 * U.length + 7) + 2 * ag.length := by ring
  step with rows_spec hnm S hS cs s decls c head args hI.toWf hd hh ha hc
    (by unfold Room; omega) as ⟨o1, s1, hR1, hr1⟩
  have ht1 := hR1.ticks
  cases hall : stepAll S f ag.length cs with
  | none =>
    rw [hall] at hr1
    simp only at hr1
    subst hr1
    simp only [WP.spec_ok]
    exact ⟨⟨hR1.wf, by rw [hR1.stk]; exact hI.empty⟩, hR1.ext, by rw [hR1.tbl],
      by unfold stepConjCost; omega, rfl⟩
  | some rs =>
    rw [hall] at hr1
    obtain ⟨rows0, rfl, hrows⟩ := hr1
    simp only
    have hlenrs := stepAll_length hall
    have hmem := mem_stepAll hall
    have hlen : ∀ r ∈ rs.reverse, r.length = ag.length := by
      intro r hr
      obtain ⟨n, -, hn⟩ := (hmem r).1 (List.mem_reverse.1 hr)
      exact Sorts.step_length hn
    have hz' : ∀ r ∈ rs.reverse, ∀ m, some m ∈ r → m ≠ nm none := by
      intro r hr
      obtain ⟨n, hn, hs⟩ := (hmem r).1 (List.mem_reverse.1 hr)
      exact hz n hn r hs
    have hstk1 : stk s1 = [] := by rw [hR1.stk]; exact hI.empty
    step with step_conj_loop_spec hnm ag rs.reverse s1 args names rows0 [] hR1.wf
      (hR1.ext.repr hU) (hR1.ext.repr ha) hrows hlen hz' (by rw [hstk1]; exact .nil)
      (by rw [List.length_reverse, hlenrs]; unfold Room; omega)
      as ⟨s2, hW2, hx2, hB2, ht2, hsl2, hfr2⟩
    rw [List.length_reverse, hlenrs] at ht2
    rw [hstk1] at hsl2
    simp only [List.length_nil, Nat.zero_add, List.append_nil] at hsl2 hfr2
    step with alloc_w s2 .Nil hW2 trivial (by unfold Room; omega)
      as ⟨nil, s3, hW3, ht3, htb3, hx3, hid, hst3⟩
    step with unstack_spec (nm := nm) (stk s3) _ [] s3 nil hW3 rfl
      (by rw [hst3]; exact hfr2.imp fun _ _ h => hx3.repr h) (.nil hid)
      (by rw [hst3, hsl2]; unfold Room; omega) as ⟨ti, s4, h1, h2, h3, h4, h5⟩
    rw [hst3, hsl2] at h4
    refine ⟨h1, ((hR1.ext.trans hx2).trans hx3).trans h2,
      by rw [h5, htb3, hB2, hR1.tbl], by unfold stepConjCost; omega, ti, rfl, ?_⟩
    rw [List.reverse_reverse, List.append_nil] at h3
    rw [← kidsPats_congr (nm none) U (rs := rs.reverse) (rs' := rs) (fun r => List.mem_reverse)]
    exact h3

/-! ## Against the specification of a conjunction -/

/-- The rows are something exactly when every sort accepts the root. -/
theorem stepAll_isSome_iff {S : Sorts} {f : Sym} {m : Nat} {cs : List Name} :
    (stepAll S f m cs).isSome = true ↔ Sorts.Accepts S cs.toFinset f m := by
  have key : (stepAll S f m cs).isSome = true ↔ ¬ stepAll S f m cs = none := by
    cases stepAll S f m cs <;> simp
  rw [key, stepAll_eq_none]
  simp only [Sorts.Accepts, List.mem_toFinset, not_exists, not_and]
  constructor
  · intro h n hn
    cases hs : Sorts.step S n f m with
    | none => exact absurd hs (h n hn)
    | some _ => rfl
  · intro h n hn hs
    have := h n hn
    rw [hs] at this
    cases this

/-- The sorts the rows give an argument are those the specification gives
it. -/
theorem colF_iff_kidC {S : Sorts} {f : Sym} {m : Nat} {cs : List Name}
    {rs : List (List (Option Name))} (h : stepAll S f m cs = some rs) (i : Nat) (n : Name) :
    colF rs i n ↔ n ∈ Sorts.kidC S cs.toFinset f m i := by
  rw [Sorts.mem_kidC]
  simp only [colF, mem_stepAll h, List.mem_toFinset]
  constructor
  · rintro ⟨r, ⟨n', hn', hs⟩, hr⟩
    exact ⟨n', hn', r, hs, hr⟩
  · rintro ⟨n', hn', r, hs, hr⟩
    exact ⟨r, ⟨n', hn', hs⟩, hr⟩

/-- The identifier `i` is the conjunction `c` of sorts, among the names
`U`. -/
def ConjAt (nm : Option Nat → RwLog.Sym) (nodes : List store.Node) (U : List Name) (i : Nat)
    (c : Sorts.Conj) : Prop :=
  Repr nm nodes i (namesPat (nm none) (conjList U (· ∈ c)))

/-- One conjunction is one identifier. -/
theorem ConjAt.inj (hnm : Function.Injective nm) {s : store.Store} (hW : Wf s) {U : List Name}
    {i j : Nat} {c : Sorts.Conj} (hi : ConjAt nm s.nodes.val U i c)
    (hj : ConjAt nm s.nodes.val U j c) : i = j :=
  Repr.inj hnm hW.nodesOK hi hj

theorem toFinset_conjList {U : List Name} {c : Sorts.Conj} (hc : ∀ n ∈ c, n ∈ U) :
    (conjList U (· ∈ c)).toFinset = c := by
  ext n
  simp only [List.mem_toFinset, mem_conjList]
  exact ⟨fun h => h.2, fun h => ⟨hc n h, h⟩⟩

theorem length_conjList_le (U : List Name) (F : Name → Prop) : (conjList U F).length ≤ U.length := by
  simp only [conjList, List.length_reverse]
  exact List.length_filter_le _ _

theorem stepConjCost_mono (S : Sorts) (u : Nat) {c c' : Nat} (h : c ≤ c') (m : Nat) :
    stepConjCost S u c m ≤ stepConjCost S u c' m := by
  unfold stepConjCost
  have h1 := Nat.mul_le_mul_right (stepCost S m + 2) h
  have h2 : m * (5 * c + 3 * u + 9) ≤ m * (5 * c' + 3 * u + 9) :=
    Nat.mul_le_mul_left m (by omega)
  omega

/-- `step_conj` is one step of a conjunction of sorts (`Sorts.Accepts`,
`Sorts.kidC`): nothing when a sort of the conjunction has no term with that
root, and otherwise the conjunction of each argument. `U` lists every name of
the conjunction, and no name a step gives is the end of a list. -/
theorem step_conj_conj_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) {f : Sym} {ag : List Pat} (U : List Name) (c : Sorts.Conj)
    (s : store.Store) (decls names ci head args : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hcU : ∀ n ∈ c, n ∈ U) (hc : ConjAt nm s.nodes.val U ci.val c)
    (hh : Repr nm s.nodes.val head.val (.sym f))
    (ha : Repr nm s.nodes.val args.val (encList (nm none) ag))
    (hz : ∀ n ∈ c, ∀ ks, Sorts.step S n f ag.length = some ks → ∀ m, some m ∈ ks → m ≠ nm none)
    (hroom : Room s (stepConjCost S U.length U.length ag.length)) :
    sorts.step_conj s decls names ci head args ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' .B = tbl s .B ∧
        s'.ticks.val ≤ s.ticks.val + stepConjCost S U.length U.length ag.length ∧
        if Sorts.Accepts S c f ag.length then
          ∃ r kids, o = some r ∧ kids.length = ag.length ∧
            Repr nm s'.nodes.val r.val (encList (nm none) kids) ∧
            ∀ i (h : i < kids.length), ∃ k, Repr nm s'.nodes.val k kids[i] ∧
              ConjAt nm s'.nodes.val U k (Sorts.kidC S c f ag.length i)
        else o = none ⦄ := by
  have hfin := toFinset_conjList hcU
  have hle := length_conjList_le U (· ∈ c)
  have hmono := stepConjCost_mono S U.length hle ag.length
  have hroom' := hroom
  unfold Room at hroom'
  refine WP.spec_mono (step_conj_spec hnm S hS U (conjList U (· ∈ c)) s decls names ci head args
    hI hd hU hc hh ha (fun n hn => hz n (mem_conjList.1 hn).2) (by unfold Room; omega)) ?_
  rintro ⟨o, s'⟩ ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, h3, by omega, ?_⟩
  cases hall : stepAll S f ag.length (conjList U (· ∈ c)) with
  | none =>
    rw [hall] at h5
    have hacc : ¬ Sorts.Accepts S c f ag.length := by
      rw [← hfin, ← stepAll_isSome_iff, hall]
      simp
    simp only [hacc, ↓reduceIte]
    exact h5
  | some rs =>
    rw [hall] at h5
    obtain ⟨r, rfl, hr⟩ := h5
    have hacc : Sorts.Accepts S c f ag.length := by
      rw [← hfin, ← stepAll_isSome_iff, hall]
      rfl
    simp only [hacc, ↓reduceIte]
    refine ⟨r, kidsPats (nm none) U rs ag.length, rfl, by simp [kidsPats], hr, ?_⟩
    intro i hi
    have hi' : i < ag.length := by simpa [kidsPats] using hi
    obtain ⟨k, hk⟩ := encList_mem_repr hr i hi
    refine ⟨k, hk, ?_⟩
    have e : (kidsPats (nm none) U rs ag.length)[i] =
        namesPat (nm none) (conjList U (· ∈ Sorts.kidC S c f ag.length i)) := by
      simp only [kidsPats, List.getElem_map, List.getElem_range]
      rw [conjList_congr]
      intro n _
      rw [colF_iff_kidC hall, hfin]
    rw [e] at hk
    exact hk

end RwLogVerified
