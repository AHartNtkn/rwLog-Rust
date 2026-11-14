/-
The one root of the members of a conjunction that are not among finitely many
ground terms (`sole_root`), proved against `Sorts.sole`, with its charge: a
polynomial in the size of the sorts, the size of the terms and the number of
conjunctions a conjunction reaches.
-/
import RwLogVerified.ButLink
import RwLog.Sorts.Roots

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## A member with a root that is not among the terms -/

open Classical in
/-- Has the conjunction a member with the root that is not among the terms? -/
noncomputable def leftAt (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (key : Sym × Nat) : Bool :=
  if Sorts.LiveKey S (Sorts.live S) c key then !onlyInL (keySoles S c key) key.1 key.2 G
  else false

/-- The ticks `left_at` may spend on a root with `k` arguments. -/
def leftCost (S : Sorts) (u r k : Nat) (G : List GTerm) : Nat :=
  stepConjCost S u u k + solesCost S u r k + onlyCost k G

/-- `left_at` gives the conjunctions of the arguments at a root when the
conjunction has a member with the root that is not among the terms. -/
theorem left_at_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (c : Sorts.Conj) (G : List GTerm) (f : Sym) (ksp : List Pat)
    (hc : Sub U c) (s : store.Store) (decls names ci g fi ks : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hf : Repr nm s.nodes.val fi.val (.sym f))
    (hks : Repr nm s.nodes.val ks.val (encList (nm none) ksp))
    (hroom : Room s (leftCost S U.length r ksp.length G)) :
    sorts.left_at s decls names ci g fi ks ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + leftCost S U.length r ksp.length G ∧
        if leftAt S c G (f, ksp.length) = true then
          ∃ kids, o = some kids ∧ Repr nm s'.nodes.val kids.val
            (encList (nm none) ((altOf S c f ksp.length).map (cpat (nm none) U)))
        else o = none ⦄ := by
  unfold sorts.left_at
  have hroom' := hroom
  unfold Room at hroom'
  simp only [leftCost] at hroom'
  have hal : (altOf S c f ksp.length).length = ksp.length := by simp [altOf]
  have hsl : (keySoles S c (f, ksp.length)).length = ksp.length := by simp [keySoles, altOf]
  have hsub : ∀ d ∈ altOf S c f ksp.length, Sub U d := by
    intro d hd
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
    exact fun x hx => hC.names x (Sorts.kidC_subset_names hx)
  step with step_conj_conj_spec hC.inj S hC.sorts (f := f) (ag := ksp) U c s decls names ci fi ks
    hI hde hU hc hci hf hks (fun n _ ks' hs m' hm' => hC.nz m' (step_kid_names hs hm'))
    (by unfold Room; omega) as ⟨o, s1, hI1, hx1, htb1, ht1, hres⟩
  by_cases hacc : Sorts.Accepts S c f ksp.length
  swap
  · simp only [hacc, ↓reduceIte] at hres
    subst hres
    have hnl : ¬ Sorts.LiveKey S (Sorts.live S) c (f, ksp.length) := fun h => hacc h.1
    have hla : leftAt S c G (f, ksp.length) = false := by
      unfold leftAt; rw [ite_neg' hnl]
    simp only [WP.spec_ok]
    refine ⟨hI1, hx1, by simp only [leftCost]; omega, ?_⟩
    simp [hla]
  simp only [hacc, ↓reduceIte] at hres
  obtain ⟨kidsi, kids, rfl, hkl, rkids, hk⟩ := hres
  have hkids : kids = (altOf S c f ksp.length).map (cpat (nm none) U) := by
    apply List.ext_getElem
    · simp [altOf, hkl]
    · intro i h₁ h₂
      obtain ⟨k', rk', ck'⟩ := hk i h₁
      simp only [altOf, List.getElem_map, List.getElem_range]
      exact rk'.unique ck'
  subst hkids
  simp only
  step with soles_spec hC (altOf S c f ksp.length) hsub (fun d _ => hr d) s1 decls names kidsi
    hI1 (hx1.repr hde) (hx1.repr hU) rkids (by rw [hal]; unfold Room; omega)
    as ⟨o1, s2, hI2, hx2, ht2, hso1, hso2⟩
  rw [hal] at ht2
  have hx12 := hx1.trans hx2
  by_cases hall : ∀ d ∈ altOf S c f ksp.length, Sorts.count S d ≠ .none
  swap
  · obtain ⟨d, hd, hdn⟩ : ∃ d ∈ altOf S c f ksp.length, Sorts.count S d = .none := by
      by_contra h0
      exact hall fun d hd hdn => h0 ⟨d, hd, hdn⟩
    have := hso2 d hd hdn
    subst this
    have hnl : ¬ Sorts.LiveKey S (Sorts.live S) c (f, ksp.length) := by
      intro h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
      exact Sorts.count_none.1 hdn (Sorts.mem_live_iff.1 (h.2 i (List.mem_range.1 hi)))
    have hla : leftAt S c G (f, ksp.length) = false := by
      unfold leftAt; rw [ite_neg' hnl]
    simp only [WP.spec_ok]
    refine ⟨hI2, hx12, by simp only [leftCost]; omega, ?_⟩
    simp [hla]
  obtain ⟨so, rfl, rso⟩ := hso1 hall
  have hlive : Sorts.LiveKey S (Sorts.live S) c (f, ksp.length) := by
    refine ⟨hacc, fun i hi => ?_⟩
    by_contra hn
    exact hall _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
      (Sorts.count_none.2 fun h => hn (Sorts.mem_live_iff.2 h))
  have rso' : Repr nm s2.nodes.val so.val
      (encList (nm none) ((keySoles S c (f, ksp.length)).map (solePat (nm none)))) := by
    rw [keySoles, List.map_map]; exact rso
  simp only
  step with only_in_spec hC.inj (keySoles S c (f, ksp.length)) f ksp hsl G s2 so fi ks g
    hI2.toWf rso' (hx12.repr hf) (hx12.repr hks) (hx12.repr hg)
    (by rw [hsl]; unfold Room; omega) as ⟨b, s3, hR3, hb⟩
  rw [hsl] at hR3
  have ht3 := hR3.ticks
  have hla : leftAt S c G (f, ksp.length) = !b := by
    unfold leftAt; rw [ite_pos' hlive, hb]
  cases b with
  | true =>
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨hR3.ranB.inv hI2, hx12.trans hR3.ext, by simp only [leftCost]; omega, ?_⟩
    simp [hla]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hR3.ranB.inv hI2, hx12.trans hR3.ext, by simp only [leftCost]; omega, ?_⟩
    rw [hla]
    simp only [Bool.not_false, ↓reduceIte]
    exact ⟨kidsi, rfl, (hx2.trans hR3.ext).repr rkids⟩

/-! ## Going through the roots -/

/-- Going through roots with the one found so far: the first root with a
member left, and whether a second has one. -/
noncomputable def foldSole (S : Sorts) (c : Sorts.Conj) (G : List GTerm) :
    List (Sym × Nat) → Option (Sym × Nat) → Option (Sym × Nat) × Bool
  | [], fo => (fo, false)
  | κ :: K, fo =>
    if leftAt S c G κ = true then
      match fo with
      | some _ => (fo, true)
      | none => foldSole S c G K (some κ)
    else foldSole S c G K fo

/-- The ticks going through roots may spend. -/
def soleLoopCost (S : Sorts) (u r : Nat) (G : List GTerm) : List (Sym × Nat) → Nat
  | [] => 1
  | κ :: K => leftCost S u r κ.2 G + 2 + soleLoopCost S u r G K

/-- The root found is in the store with the conjunctions of its arguments. -/
def FoundAt (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (c : Sorts.Conj)
    (s : store.Store) : Option (Sym × Nat) → Option (store.TermId × store.TermId) → Prop
  | none, none => True
  | some κ, some x => Repr nm s.nodes.val x.1.val (.sym κ.1) ∧
      Repr nm s.nodes.val x.2.val (encList (nm none) ((altOf S c κ.1 κ.2).map (cpat (nm none) U)))
  | _, _ => False

theorem FoundAt.mono {S : Sorts} {U : List Name} {c : Sorts.Conj} {s s' : store.Store}
    (hx : Extends s s') {fo : Option (Sym × Nat)} {found : Option (store.TermId × store.TermId)}
    (h : FoundAt nm S U c s fo found) : FoundAt nm S U c s' fo found := by
  cases fo <;> cases found <;> simp only [FoundAt] at h ⊢
  exact ⟨hx.repr h.1, hx.repr h.2⟩

theorem sole_root_done (s : store.Store) (decls names c g keys : store.TermId)
    (found : Option (store.TermId × store.TermId)) (many : Bool) :
    sorts.sole_root_loop s decls names c g keys found many false ⦃ r => r = (s, found, many) ⦄ := by
  unfold sorts.sole_root_loop
  rw [loop]
  simp only [sorts.sole_root_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem sole_root_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (c : Sorts.Conj) (G : List GTerm) (hc : Sub U c) (decls names ci g : store.TermId) :
    ∀ (K : List (Sym × Nat)) (es : List (Pat × List Pat)) (fo : Option (Sym × Nat))
      (s : store.Store) (keys : store.TermId) (found : Option (store.TermId × store.TermId)),
    List.Forall₂ ExAt K es → Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val ci.val (cpat (nm none) U c) →
    Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)) →
    Repr nm s.nodes.val keys.val (encList (nm none) (es.map (entPat (nm none)))) →
    FoundAt nm S U c s fo found →
    Room s (soleLoopCost S U.length r G K) →
    sorts.sole_root_loop s decls names ci g keys found false true ⦃ res =>
      Inv res.1 ∧ Extends s res.1 ∧
        res.1.ticks.val ≤ s.ticks.val + soleLoopCost S U.length r G K ∧
        res.2.2 = (foldSole S c G K fo).2 ∧
        FoundAt nm S U c res.1 (foldSole S c G K fo).1 res.2.1 ⦄ := by
  intro K
  induction K with
  | nil =>
    intro es fo s keys found hK hI hde hU hci hg hks hfd hroom
    cases hK
    have hroom' := hroom
    unfold Room at hroom'
    simp only [soleLoopCost] at hroom'
    unfold sorts.sole_root_loop
    rw [loop]
    simp only [sorts.sole_root_loop.body, ↓reduceIte]
    step with uncons_repr s keys hI.toWf hks (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := sole_root_done s1 decls names ci g keys found false
    unfold sorts.sole_root_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro res rfl
    exact ⟨hK0.ran.ranB.inv hI, hK0.ran.ext, hK0.ran.ticks, rfl, hfd.mono hK0.ran.ext⟩
  | cons κ K ih =>
    intro es fo s keys found hK hI hde hU hci hg hks hfd hroom
    obtain ⟨f, a⟩ := κ
    obtain ⟨e, es', hx, hK', rfl⟩ := List.forall₂_cons_left_iff.1 hK
    obtain ⟨he1, he2⟩ := hx
    simp only at he1 he2
    have hroom' := hroom
    unfold Room at hroom'
    simp only [soleLoopCost] at hroom'
    unfold sorts.sole_root_loop
    rw [loop]
    simp only [sorts.sole_root_loop.body, ↓reduceIte]
    step with uncons_repr s keys hI.toWf hks (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨key, t, rfl, rkey, rt⟩ := hu
    have ht1 := hK0.ticks
    step with uncons_repr s1 key hK0.wf (hK0.ran.ext.repr rkey) (by unfold Room; omega)
      as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [entPat] at hu1
    simp only at hK1
    obtain ⟨fi, ks, rfl, rf, rk⟩ := hu1
    rw [hK0.nodes] at rf rk
    rw [he1] at rf
    have ht2 := hK1.ticks
    have R2 := hK0.ran.trans hK1.ran
    have I2 : Inv s2 := R2.ranB.inv hI
    step with left_at_spec hC hr c G f e.2 hc s2 decls names ci g fi ks I2
      (R2.ext.repr hde) (R2.ext.repr hU) (R2.ext.repr hci) (R2.ext.repr hg)
      (R2.ext.repr rf) (R2.ext.repr rk) (by rw [he2]; unfold Room; omega)
      as ⟨r3, hI3, hx3, ht3, hres⟩
    obtain ⟨o2, s3⟩ := r3
    simp only at hI3 hx3 ht3 hres
    rw [he2] at ht3 hres
    have hx23 := R2.ext.trans hx3
    have hpos : 1 ≤ soleLoopCost S U.length r G K := by
      cases K <;> simp only [soleLoopCost] <;> omega
    cases hla : leftAt S c G (f, a) with
    | false =>
      rw [hla] at hres
      simp only [Bool.false_eq_true, ↓reduceIte] at hres
      subst hres
      simp only [uncurry, bind_ok]
      have IH := ih es' fo s3 t found hK' hI3 (hx23.repr hde) (hx23.repr hU)
        (hx23.repr hci) (hx23.repr hg) (hx23.repr rt) (hfd.mono hx23) (by unfold Room; omega)
      unfold sorts.sole_root_loop at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hI', hx', ht', hres'⟩
      refine ⟨hI', hx23.trans hx', by simp only [soleLoopCost]; omega, ?_⟩
      simpa only [foldSole, hla, Bool.false_eq_true, ↓reduceIte] using hres'
    | true =>
      rw [hla] at hres
      simp only [↓reduceIte] at hres
      obtain ⟨kidsi, rfl, rkids⟩ := hres
      cases fo with
      | none =>
        cases found with
        | some x => simp only [FoundAt] at hfd
        | none =>
          simp only [uncurry, bind_ok, Option.isSome_none,
            Bool.false_eq_true, ↓reduceIte]
          have IH := ih es' (some (f, a)) s3 t (some (fi, kidsi)) hK' hI3 (hx23.repr hde)
            (hx23.repr hU) (hx23.repr hci) (hx23.repr hg) (hx23.repr rt)
            ⟨hx23.repr rf, rkids⟩ (by unfold Room; omega)
          unfold sorts.sole_root_loop at IH
          refine WP.spec_mono IH ?_
          rintro res ⟨hI', hx', ht', hres'⟩
          refine ⟨hI', hx23.trans hx', by simp only [soleLoopCost]; omega, ?_⟩
          simpa only [foldSole, hla, ↓reduceIte] using hres'
      | some κ0 =>
        cases found with
        | none => simp only [FoundAt] at hfd
        | some x =>
          simp only [uncurry, bind_ok, Option.isSome_some,
            ↓reduceIte]
          have hdn := sole_root_done s3 decls names ci g keys (some x) true
          unfold sorts.sole_root_loop at hdn
          refine WP.spec_mono hdn ?_
          rintro res rfl
          refine ⟨hI3, hx23, by simp only [soleLoopCost]; omega, ?_⟩
          simp only [foldSole, hla, ↓reduceIte]
          exact ⟨trivial, hfd.mono hx23⟩

/-! ## The one root -/

/-- The roots `sole_root` goes through. -/
def soleKeysL (S : Sorts) (cl : List Name) (G : List GTerm) : List (Sym × Nat) :=
  addKeys (conjKeys S [] cl) (G.map termKey)

/-- The one root, as `sole_root` finds it. -/
noncomputable def soleL (S : Sorts) (U : List Name) (c : Sorts.Conj) (G : List GTerm) :
    Option (Sym × Nat) :=
  if Sorts.RestOK S c then none
  else if (foldSole S c G (soleKeysL S (conjList U (· ∈ c)) G) none).2 = true then none
  else (foldSole S c G (soleKeysL S (conjList U (· ∈ c)) G) none).1

/-- The ticks `sole_root` may spend. -/
noncomputable def soleRunCost (S : Sorts) (U : List Name) (r : Nat) (c : Sorts.Conj)
    (G : List GTerm) : Nat :=
  U.length * (3 * S.length + 4) + 2 + conjKeysCost S [] (conjList U (· ∈ c)) +
    termKeysCost (conjKeys S [] (conjList U (· ∈ c))) G +
    soleLoopCost S U.length r G (soleKeysL S (conjList U (· ∈ c)) G)

theorem sole_root_run {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (c : Sorts.Conj) (G : List GTerm) (hc : Sub U c) (s : store.Store)
    (decls names ci g : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hroom : Room s (soleRunCost S U r c G)) :
    sorts.sole_root s decls names ci g ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + soleRunCost S U r c G ∧
        FoundAt nm S U c s' (soleL S U c G) o ⦄ := by
  unfold sorts.sole_root
  have hroom' := hroom
  unfold Room at hroom'
  simp only [soleRunCost] at hroom'
  step with rest_ok_spec hC.inj S hC.sorts c hc s decls ci hI.toWf hde hci
    (by unfold Room; omega) as ⟨b, s1, hR1, hb⟩
  have ht1 := hR1.ticks
  cases b with
  | true =>
    have hro : Sorts.RestOK S c := hb.1 rfl
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨hR1.ranB.inv hI, hR1.ext, by simp only [soleRunCost]; omega, ?_⟩
    unfold soleL
    rw [ite_pos' hro]
    trivial
  | false =>
    have hro : ¬ Sorts.RestOK S c := fun h => absurd (hb.2 h) (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with alloc_w s1 .Nil hR1.wf trivial (by unfold Room; omega)
      as ⟨nil, s2, hW2, ht2, htb2, hx2, hid2, hst2⟩
    have rnil : Repr nm s2.nodes.val nil.val
        (encList (nm none) (([] : List (Pat × List Pat)).map (entPat (nm none)))) := .nil hid2
    have R2 : Ran s s2 (U.length * (3 * S.length + 4) + 1 + 1) :=
      hR1.trans ⟨hW2, hx2, htb2, hst2, by omega⟩
    step with add_conj_keys_loop_spec hC.inj S hC.sorts (conjList U (· ∈ c)) [] [] s2 decls ci nil
      .nil hW2 (R2.ext.repr hde) (R2.ext.repr hci) rnil (by unfold Room; omega)
      as ⟨k0, s3, hR3, es1, hK1, rk1⟩
    have ht3 := hR3.ticks
    have R3 := R2.trans hR3
    step with add_term_keys_loop_spec hC.inj G _ es1 s3 g k0 hK1 hR3.wf (R3.ext.repr hg) rk1
      (by unfold Room; omega) as ⟨keys, s4, hR4, es2, hK2, rk2⟩
    have ht4 := hR4.ticks
    have R4 := R3.trans hR4
    step with sole_root_loop_spec hC hr c G hc decls names ci g _ es2 none s4 keys none hK2
      (R4.ranB.inv hI) (R4.ext.repr hde) (R4.ext.repr hU) (R4.ext.repr hci) (R4.ext.repr hg) rk2
      trivial (by unfold Room; simp only [soleKeysL] at hroom'; omega)
      as ⟨s5, found, many, hI5, hx5, ht5, hm, hfd⟩
    have hsl : soleL S U c G =
        if (foldSole S c G (soleKeysL S (conjList U (· ∈ c)) G) none).2 = true then none
        else (foldSole S c G (soleKeysL S (conjList U (· ∈ c)) G) none).1 := by
      unfold soleL; rw [ite_neg' hro]
    have hcost : s5.ticks.val ≤ s.ticks.val + soleRunCost S U r c G := by
      simp only [soleRunCost, soleKeysL]; omega
    rw [hsl]
    change many = (foldSole S c G (soleKeysL S (conjList U (· ∈ c)) G) none).2 at hm
    change FoundAt nm S U c s5 (foldSole S c G (soleKeysL S (conjList U (· ∈ c)) G) none).1
      found at hfd
    rw [← hm]
    cases many with
    | true =>
      simp only [↓reduceIte, WP.spec_ok]
      exact ⟨hI5, R4.ext.trans hx5, hcost, trivial⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨hI5, R4.ext.trans hx5, hcost, hfd⟩

/-! ## What is found is what the specification finds -/

theorem foldSole_some (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (κ0 : Sym × Nat) :
    ∀ K : List (Sym × Nat), foldSole S c G K (some κ0) =
      (some κ0, !(K.filter fun κ => leftAt S c G κ).isEmpty)
  | [] => rfl
  | κ :: K => by
    cases h : leftAt S c G κ
    · simp only [foldSole, h, Bool.false_eq_true, ↓reduceIte, foldSole_some S c G κ0 K,
        List.filter_cons_of_neg, not_false_eq_true]
    · simp [foldSole, h]

theorem foldSole_none (S : Sorts) (c : Sorts.Conj) (G : List GTerm) :
    ∀ K : List (Sym × Nat), foldSole S c G K none =
      match K.filter fun κ => leftAt S c G κ with
      | [] => (none, false)
      | κ :: R => (some κ, !R.isEmpty)
  | [] => rfl
  | κ :: K => by
    cases h : leftAt S c G κ
    · simp only [foldSole, h, Bool.false_eq_true, ↓reduceIte, foldSole_none S c G K,
        List.filter_cons_of_neg, not_false_eq_true]
    · simp only [foldSole, h, ↓reduceIte, foldSole_some, List.filter_cons_of_pos]

theorem leftAt_iff (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (key : Sym × Nat) :
    leftAt S c G key = true ↔
      Sorts.LiveKey S (Sorts.live S) c key ∧ Sorts.onlyIn S c key.1 key.2 G = false := by
  obtain ⟨f, k⟩ := key
  unfold leftAt
  by_cases h : Sorts.LiveKey S (Sorts.live S) c (f, k)
  · rw [ite_pos' h, onlyInL_eq]; simp [h]
  · rw [ite_neg' h]; simp [h]

theorem toFinset_eq_singleton {α : Type} [DecidableEq α] {l : List α} (hl : l.Nodup) {a : α} :
    l.toFinset = {a} ↔ l = [a] := by
  constructor
  · intro h
    have h1 : l.length = 1 := by rw [← List.toFinset_card_of_nodup hl, h]; rfl
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 h1
    have : x ∈ ([x] : List α).toFinset := by simp
    rw [h] at this
    rw [Finset.mem_singleton.1 this]
  · rintro rfl; rfl

/-- What `sole_root` finds is the one root of the specification. -/
theorem soleL_eq {S : Sorts} {U : List Name} {c : Sorts.Conj} (hc : Sub U c) (G : List GTerm) :
    soleL S U c G = Sorts.sole S c G := by
  unfold soleL Sorts.sole
  by_cases hro : Sorts.RestOK S c
  · rw [ite_pos' hro, ite_pos' hro]
  rw [ite_neg' hro, ite_neg' hro]
  set K := soleKeysL S (conjList U (· ∈ c)) G with hKd
  have hnd : (K.filter fun κ => leftAt S c G κ).Nodup :=
    (addKeys_nodup _ _ (conjKeys_nodup S _ [] List.nodup_nil)).filter _
  have hset : Sorts.survivors S c G = (K.filter fun κ => leftAt S c G κ).toFinset := by
    ext x
    have hcK : x ∈ conjKeys S [] (conjList U (· ∈ c)) ↔ ∃ m ∈ c, x ∈ defKeys S m := by
      rw [mem_conjKeysL]
      simp only [List.not_mem_nil, false_or]
      constructor
      · rintro ⟨m, hm, hx⟩; exact ⟨m, (mem_conjList.1 hm).2, hx⟩
      · rintro ⟨m, hm, hx⟩; exact ⟨m, mem_conjList.2 ⟨hc m hm, hm⟩, hx⟩
    simp only [Sorts.survivors, Finset.mem_filter, Finset.mem_union, List.mem_toFinset,
      List.mem_filter, hKd, soleKeysL, mem_addKeys, hcK, mem_caseKeys_def, filterMap_key,
      leftAt_iff]
  have key : ∀ o : Option (Sym × Nat), (∀ κ, o = some κ ↔
      (K.filter fun κ => leftAt S c G κ) = [κ]) → o = Sorts.only (Sorts.survivors S c G) := by
    intro o ho
    cases hon : Sorts.only (Sorts.survivors S c G) with
    | some κ =>
      rw [Sorts.only_eq_some, hset, toFinset_eq_singleton hnd] at hon
      exact (ho κ).2 hon
    | none =>
      cases o with
      | none => rfl
      | some κ =>
        have := (ho κ).1 rfl
        rw [← toFinset_eq_singleton hnd, ← hset, ← Sorts.only_eq_some, hon] at this
        cases this
  apply key
  intro κ
  rw [foldSole_none]
  cases hF : (K.filter fun κ => leftAt S c G κ) with
  | nil => simp
  | cons x R =>
    cases R with
    | nil => simp
    | cons y R' => simp

/-! ## The charge -/

/-- A bound on the ticks `left_at` may spend on a root with `W` arguments at
most and terms of size `N` at most. -/
def leftB (S : Sorts) (u r N W : Nat) : Nat :=
  stepConjCost S u u W + solesCost S u r W + ((4 * W + 11) * N + 1)

theorem leftCost_le (S : Sorts) (u r : Nat) {k W N : Nat} {G : List GTerm} (hk : k ≤ W)
    (hG : Sorts.sumSize G ≤ N) : leftCost S u r k G ≤ leftB S u r N W := by
  have a1 : stepCost S k ≤ stepCost S W := by unfold stepCost; omega
  have a2 : stepConjCost S u u k ≤ stepConjCost S u u W := by
    unfold stepConjCost
    have b1 := Nat.mul_le_mul_left u (Nat.add_le_add_right a1 2)
    have b2 := Nat.mul_le_mul_right (5 * u + 3 * u + 9) hk
    omega
  have a3 : solesCost S u r k ≤ solesCost S u r W := by
    unfold solesCost
    have := Nat.mul_le_mul_right (countCost S u r + 5) hk
    omega
  have a4 : onlyCost k G ≤ (4 * W + 11) * N + 1 := by
    have b1 := onlyCost_le k G
    have b2 : (4 * k + 11) * Sorts.sumSize G ≤ (4 * W + 11) * N := Nat.mul_le_mul (by omega) hG
    omega
  unfold leftCost leftB
  omega

theorem soleLoopCost_le (S : Sorts) (u r : Nat) {W N : Nat} {G : List GTerm}
    (hG : Sorts.sumSize G ≤ N) : ∀ K : List (Sym × Nat), (∀ κ ∈ K, κ.2 ≤ W) →
    soleLoopCost S u r G K ≤ K.length * (leftB S u r N W + 2) + 1
  | [], _ => by simp [soleLoopCost]
  | κ :: K, h => by
    have ih := soleLoopCost_le S u r hG K fun κ' hκ' => h κ' (List.mem_cons_of_mem _ hκ')
    have h1 := leftCost_le S u r (h κ List.mem_cons_self) hG
    simp only [soleLoopCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The ticks `sole_root` may spend on terms of size `N`, where a conjunction
reaches `r` conjunctions at most: a polynomial in the size of the sorts, `N`
and `r`. -/
def soleAll (S : Sorts) (u r N : Nat) : Nat :=
  u * (3 * S.length + 4) + 2 + butKeysCost S u (7 * N) +
    (butKeysW S u (7 * N) * (leftB S u r N (butKeysW S u (7 * N)) + 2) + 1)

theorem soleRunCost_le (S : Sorts) (U : List Name) (r : Nat) (c : Sorts.Conj) {G : List GTerm}
    {N : Nat} (hG : Sorts.sumSize G ≤ N) : soleRunCost S U r c G ≤ soleAll S U.length r N := by
  unfold soleRunCost soleAll
  set cl := conjList U (· ∈ c) with hcl
  set gw := kw (G.map termKey) with hgw
  set B := butKeysW S U.length gw with hB
  have hlen : cl.length ≤ U.length := length_conjList_le U (· ∈ c)
  have hm1 := Nat.mul_le_mul_right (sortsW S) hlen
  have hm2 := Nat.mul_le_mul_right (3 * S.length + 5) hlen
  have hBe : B = 1 + (U.length * sortsW S + sortsW S) + gw := by
    rw [hB]; unfold butKeysW; rw [Nat.add_mul, Nat.one_mul]
  obtain ⟨hc1, hc2⟩ := conjKeys_le S cl [] B (by simp only [keysCost]; omega)
  simp only [keysCost] at hc1
  have hm3 := Nat.mul_le_mul_right (B + 4) hm1
  have hGl := length_le_kw (G.map termKey)
  rw [List.length_map] at hGl
  have hsq : B * (B + 5) = B * (B + 4) + B := by rw [Nat.mul_add, Nat.mul_add]; omega
  have h1 := termKeysCost_le G (conjKeys S [] cl) B (by omega)
  have h2 := keysCost_addKeys_le (G.map termKey) (conjKeys S [] cl)
  have h3 : (cl.length * sortsW S + G.length) * (B + 4) ≤ B * (B + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : G.length * B ≤ G.length * (B + 4) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul] at h3
  have hgw7 : gw ≤ 7 * N := by
    have := kw_terms_le G
    omega
  have hW : B ≤ butKeysW S U.length (7 * N) := by
    rw [hB]; unfold butKeysW; omega
  have hKC : butKeysCost S U.length gw ≤ butKeysCost S U.length (7 * N) := by
    unfold butKeysCost
    rw [← hB]
    have := Nat.mul_le_mul hW (Nat.add_le_add_right hW 5)
    omega
  have hkeys : conjKeysCost S [] cl + termKeysCost (conjKeys S [] cl) G ≤
      butKeysCost S U.length gw := by
    unfold butKeysCost
    rw [← hB, hsq]
    omega
  obtain ⟨hl, hk⟩ := le_keysCost (soleKeysL S cl G)
  have hkc : keysCost (soleKeysL S cl G) ≤ B := by unfold soleKeysL; omega
  have hloop := soleLoopCost_le S U.length r (W := butKeysW S U.length (7 * N)) hG
    (soleKeysL S cl G) fun κ hκ => by
      have := hk κ hκ
      omega
  have hmul := Nat.mul_le_mul_right
    (leftB S U.length r N (butKeysW S U.length (7 * N)) + 2)
    (Nat.le_trans hl (Nat.le_trans hkc hW))
  omega

/-! ## The whole -/

/-- `sole_root` finds the one root of the members of the conjunction that
are not among the ground terms of the list (`Sorts.sole`), with the
conjunction of each of its arguments, within `soleAll` ticks. -/
theorem sole_root_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (c : Sorts.Conj) (G : List GTerm) (hc : Sub U c) (s : store.Store)
    (decls names ci g : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hroom : Room s (soleAll S U.length r (Sorts.sumSize G))) :
    sorts.sole_root s decls names ci g ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + soleAll S U.length r (Sorts.sumSize G) ∧
        match Sorts.sole S c G with
        | none => o = none
        | some κ => ∃ fi kids, o = some (fi, kids) ∧ Repr nm s'.nodes.val fi.val (.sym κ.1) ∧
            Repr nm s'.nodes.val kids.val
              (encList (nm none) ((altOf S c κ.1 κ.2).map (cpat (nm none) U))) ⦄ := by
  have hle := soleRunCost_le S U r c (G := G) (Nat.le_refl _)
  refine WP.spec_mono (sole_root_run hC hr c G hc s decls names ci g hI hde hU hci hg
    (by unfold Room at hroom ⊢; omega)) ?_
  rintro ⟨o, s'⟩ ⟨hI', hx', ht', hfd⟩
  refine ⟨hI', hx', by omega, ?_⟩
  rw [soleL_eq hc] at hfd
  cases hs : Sorts.sole S c G with
  | none =>
    rw [hs] at hfd
    cases o with
    | none => rfl
    | some x => simp only [FoundAt] at hfd
  | some κ =>
    rw [hs] at hfd
    cases o with
    | none => simp only [FoundAt] at hfd
    | some x => exact ⟨x.1, x.2, rfl, hfd.1, hfd.2⟩

end RwLogVerified
