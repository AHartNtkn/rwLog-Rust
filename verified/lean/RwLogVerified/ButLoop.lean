/-
The loops of inclusion but for finitely many terms: what one conjunction, sort
and list of terms leave to ask (`but_one`), and asking until nothing is left
(`included_but`), proved against what the roots leave (`keyAsks`), with the
charge of each.
-/
import RwLogVerified.But

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## What a conjunction, a sort and terms leave to ask -/

/-- What the roots of a list leave to ask, in front of what is left already;
nothing when a root gives nothing. -/
noncomputable def foldAsks (S : Sorts) (c : Sorts.Conj) (n : Name) (G : List GTerm) :
    List (Sym × Nat) → List Ask → Option (List Ask)
  | [], T => some T
  | κ :: K, T =>
    match keyAsks S c n G κ with
    | some A => foldAsks S c n G K (A ++ T)
    | none => none

/-- The ticks going through roots may spend. -/
def butLoopCost (S : Sorts) (u r q : Nat) (G : List GTerm) : List (Sym × Nat) → Nat
  | [] => 1
  | κ :: K => butKeyCost S u r q κ.2 G + 2 + butLoopCost S u r q G K

theorem but_one_done (s : store.Store) (decls names c n g keys todo : store.TermId) (okb : Bool) :
    sorts.but_one_loop s decls names c n g keys todo okb false ⦃ r => r = (s, todo, okb) ⦄ := by
  unfold sorts.but_one_loop
  rw [loop]
  simp only [sorts.but_one_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem but_one_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (c : Sorts.Conj) (n : Name) (G : List GTerm) (hc : Sub U c)
    (decls names ci ni g : store.TermId) :
    ∀ (K : List (Sym × Nat)) (es : List (Pat × List Pat)) (T : List Ask) (s : store.Store)
      (keys todo : store.TermId) (okb : Bool),
    List.Forall₂ ExAt K es → Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val ci.val (cpat (nm none) U c) → Repr nm s.nodes.val ni.val (.sym n) →
    Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)) →
    Repr nm s.nodes.val keys.val (encList (nm none) (es.map (entPat (nm none)))) →
    Repr nm s.nodes.val todo.val (encList (nm none) (T.map (askPat (nm none) U))) →
    Room s (butLoopCost S U.length r q G K) →
    sorts.but_one_loop s decls names ci ni g keys todo okb true ⦃ res =>
      Inv res.1 ∧ Extends s res.1 ∧
        res.1.ticks.val ≤ s.ticks.val + butLoopCost S U.length r q G K ∧
        match foldAsks S c n G K T with
        | some T' => res.2.2 = okb ∧ Repr nm res.1.nodes.val res.2.1.val
            (encList (nm none) (T'.map (askPat (nm none) U)))
        | none => res.2.2 = false ⦄ := by
  intro K
  induction K with
  | nil =>
    intro es T s keys todo okb hK hI hde hU hci hni hg hks htd hroom
    cases hK
    have hroom' := hroom
    unfold Room at hroom'
    simp only [butLoopCost] at hroom'
    unfold sorts.but_one_loop
    rw [loop]
    simp only [sorts.but_one_loop.body, ↓reduceIte]
    step with uncons_repr s keys hI.toWf hks (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := but_one_done s1 decls names ci ni g keys todo okb
    unfold sorts.but_one_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro res rfl
    exact ⟨hK0.ran.ranB.inv hI, hK0.ran.ext, hK0.ran.ticks, rfl, hK0.ran.ext.repr htd⟩
  | cons κ K ih =>
    intro es T s keys todo okb hK hI hde hU hci hni hg hks htd hroom
    obtain ⟨f, a⟩ := κ
    obtain ⟨e, es', hx, hK', rfl⟩ := List.forall₂_cons_left_iff.1 hK
    obtain ⟨he1, he2⟩ := hx
    simp only at he1 he2
    have hroom' := hroom
    unfold Room at hroom'
    simp only [butLoopCost] at hroom'
    unfold sorts.but_one_loop
    rw [loop]
    simp only [sorts.but_one_loop.body, ↓reduceIte]
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
    step with but_key_spec hC hr hq c n G f e.2 T hc s2 decls names ci ni g fi ks todo I2
      (R2.ext.repr hde) (R2.ext.repr hU) (R2.ext.repr hci) (R2.ext.repr hni) (R2.ext.repr hg)
      (R2.ext.repr rf) (R2.ext.repr rk) (R2.ext.repr htd) (by rw [he2]; unfold Room; omega)
      as ⟨r3, hI3, hx3, ht3, hres⟩
    obtain ⟨o2, s3⟩ := r3
    simp only at hI3 hx3 ht3 hres
    rw [he2] at ht3 hres
    have hx23 := R2.ext.trans hx3
    cases hka : keyAsks S c n G (f, a) with
    | none =>
      rw [hka] at hres
      subst hres
      simp only [uncurry, bind_ok]
      have hdn := but_one_done s3 decls names ci ni g keys todo false
      unfold sorts.but_one_loop at hdn
      refine WP.spec_mono hdn ?_
      rintro res rfl
      have hpos : 1 ≤ butLoopCost S U.length r q G K := by
        cases K <;> simp only [butLoopCost] <;> omega
      refine ⟨hI3, hx23, by simp only [butLoopCost]; omega, ?_⟩
      simp only [foldAsks, hka]
    | some A =>
      rw [hka] at hres
      obtain ⟨td, rfl, rtd⟩ := hres
      simp only [uncurry, bind_ok]
      have IH := ih es' (A ++ T) s3 t td okb hK' hI3 (hx23.repr hde) (hx23.repr hU)
        (hx23.repr hci) (hx23.repr hni) (hx23.repr hg) (hx23.repr rt) rtd (by unfold Room; omega)
      unfold sorts.but_one_loop at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hI', hx', ht', hres'⟩
      refine ⟨hI', hx23.trans hx', by simp only [butLoopCost]; omega, ?_⟩
      simpa only [foldAsks, hka] using hres'

/-- What a conjunction, a sort and terms leave to ask, in front of what is
left already; nothing when the conjunction has a member outside the sort that
is not among the terms. -/
noncomputable def oneAsks (S : Sorts) (U : List Name) (c : Sorts.Conj) (n : Name)
    (G : List GTerm) (T : List Ask) : Option (List Ask) :=
  if Sorts.FreshOut S c n then none
  else foldAsks S c n G (butKeysL S (conjList U (· ∈ c)) n G) T

/-- The ticks `but_one` may spend. -/
noncomputable def oneCost (S : Sorts) (U : List Name) (r q : Nat) (c : Sorts.Conj) (n : Name)
    (G : List GTerm) : Nat :=
  freshCost S U.length q + butKeysX S (conjList U (· ∈ c)) n G +
    butLoopCost S U.length r q G (butKeysL S (conjList U (· ∈ c)) n G)

/-- `but_one` puts what a conjunction, a sort and terms leave to ask in
front, or gives nothing. -/
theorem but_one_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (c : Sorts.Conj) (n : Name) (G : List GTerm) (T : List Ask) (hc : Sub U c) (s : store.Store)
    (decls names ci ni g todo : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hni : Repr nm s.nodes.val ni.val (.sym n))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (htd : Repr nm s.nodes.val todo.val (encList (nm none) (T.map (askPat (nm none) U))))
    (hroom : Room s (oneCost S U r q c n G)) :
    sorts.but_one s decls names ci ni g todo ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + oneCost S U r q c n G ∧
        match oneAsks S U c n G T with
        | some T' => ∃ td, o = some td ∧
            Repr nm s'.nodes.val td.val (encList (nm none) (T'.map (askPat (nm none) U)))
        | none => o = none ⦄ := by
  unfold sorts.but_one
  have hroom' := hroom
  unfold Room at hroom'
  simp only [oneCost] at hroom'
  step with fresh_out_spec hC c n hc (fun m => hq _ m) s decls names ci ni hI hde hU hci hni
    (by unfold Room; omega) as ⟨b, s1, hI1, hx1, ht1, hb⟩
  cases b with
  | true =>
    have hfo : Sorts.FreshOut S c n := hb.1 rfl
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨hI1, hx1, by simp only [oneCost]; omega, ?_⟩
    unfold oneAsks
    rw [ite_pos' hfo]
  | false =>
    have hfo : ¬ Sorts.FreshOut S c n := fun h => absurd (hb.2 h) (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with but_keys_spec hC.inj S hC.sorts (conjList U (· ∈ c)) n G s1 decls ci ni g
      hI1.toWf (hx1.repr hde) (hx1.repr hci) (hx1.repr hni) (hx1.repr hg) (by unfold Room; omega)
      as ⟨keys, s2, hR2, es, hK, rkeys⟩
    have ht2 := hR2.ticks
    have hx2 := hx1.trans hR2.ext
    step with but_one_loop_spec hC hr hq c n G hc decls names ci ni g _ es T s2 keys todo true hK
      (hR2.ranB.inv hI1) (hx2.repr hde) (hx2.repr hU) (hx2.repr hci) (hx2.repr hni)
      (hx2.repr hg) rkeys (hx2.repr htd) (by unfold Room; omega)
      as ⟨s3, td, okb, hI3, hx3, ht3, hres⟩
    have hoa : oneAsks S U c n G T =
        foldAsks S c n G (butKeysL S (conjList U (· ∈ c)) n G) T := by
      unfold oneAsks; rw [ite_neg' hfo]
    rw [hoa]
    cases hfa : foldAsks S c n G (butKeysL S (conjList U (· ∈ c)) n G) T with
    | none =>
      rw [hfa] at hres
      subst hres
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨hI3, hx2.trans hx3, by simp only [oneCost]; omega, rfl⟩
    | some T' =>
      rw [hfa] at hres
      obtain ⟨rfl, rtd⟩ := hres
      simp only [↓reduceIte, WP.spec_ok]
      exact ⟨hI3, hx2.trans hx3, by simp only [oneCost]; omega, td, rfl, rtd⟩

end RwLogVerified
