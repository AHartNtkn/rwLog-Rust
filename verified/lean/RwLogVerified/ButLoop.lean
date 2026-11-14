/-
The loops of inclusion but for finitely many terms: what one conjunction, sort
and list of terms leave to ask (`but_one`), and asking until nothing is left
(`included_but`), proved against what the roots leave (`keyAsks`), with the
charge of each.
-/
import RwLogVerified.But
import RwLogVerified.Among

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

/-! ## Asking until nothing is left -/

/-- What is left to ask holds. -/
def HoldA (S : Sorts) (a : Ask) : Prop := Sorts.Hold S a.1 a.2.1 a.2.2

/-- The size of the terms of what is left to ask. -/
def mu (T : List Ask) : Nat := (T.map fun a => Sorts.sumSize a.2.2).sum

/-- What is left to ask is of conjunctions of names listed, each with a term
at least. -/
def AsksInv (U : List Name) (T : List Ask) : Prop := ∀ a ∈ T, Sub U a.1 ∧ a.2.2 ≠ []

/-- One step of asking is right: with nothing given the first does not hold,
and otherwise what is left is smaller and holds exactly when what was left
did. -/
def StepOK (S : Sorts) (U : List Name) : Prop :=
  ∀ (a : Ask) (T : List Ask), AsksInv U (a :: T) →
    match oneAsks S U a.1 a.2.1 a.2.2 T with
    | none => ¬ HoldA S a
    | some T' => AsksInv U T' ∧ mu T' < mu (a :: T) ∧
        ((∀ x ∈ T', HoldA S x) ↔ ∀ x ∈ a :: T, HoldA S x)

theorem sumSize_pos {G : List GTerm} (h : G ≠ []) : 0 < Sorts.sumSize G := by
  cases G with
  | nil => exact absurd rfl h
  | cons g G =>
    have := Sorts.size_pos g
    simp only [Sorts.sumSize, List.map_cons, List.sum_cons]
    omega

/-! ### The questions answered are remembered

A question is asked once: the questions answered are kept, and one that is
kept is passed over. `butRun` is the run, `butRunCost` what it spends. -/

theorem foldAsks_append (S : Sorts) (c : Sorts.Conj) (n : Name) (G : List GTerm) :
    ∀ (K : List (Sym × Nat)) (A T : List Ask),
      foldAsks S c n G K (A ++ T) = (foldAsks S c n G K A).map (· ++ T)
  | [], A, T => rfl
  | κ :: K, A, T => by
    simp only [foldAsks]
    cases keyAsks S c n G κ with
    | none => rfl
    | some B =>
      show foldAsks S c n G K (B ++ (A ++ T)) = (foldAsks S c n G K (B ++ A)).map (· ++ T)
      rw [← List.append_assoc]
      exact foldAsks_append S c n G K (B ++ A) T

/-- What a question leaves to ask in front of what is left is what it leaves
to ask, in front of what is left. -/
theorem oneAsks_append (S : Sorts) (U : List Name) (c : Sorts.Conj) (n : Name) (G : List GTerm)
    (T : List Ask) : oneAsks S U c n G T = (oneAsks S U c n G []).map (· ++ T) := by
  unfold oneAsks
  split
  · rfl
  · have := foldAsks_append S c n G (butKeysL S (conjList U (· ∈ c)) n G) [] T
    rwa [List.nil_append] at this

theorem askPat_inj {z : Sym} {U : List Name} {a b : Ask} (ha : Sub U a.1) (hb : Sub U b.1)
    (h : askPat z U a = askPat z U b) : a = b := by
  obtain ⟨c, n, G⟩ := a
  obtain ⟨d, m, H⟩ := b
  simp only [askPat, accPat, Term.app.injEq, Term.sym.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hG : G = H := List.map_injective_iff.2 (fun _ _ => toPat_inj) (encList_inj z h3)
  have hc : c = d := cpat_inj ha hb h1
  subst hc h2 hG
  rfl

theorem askPat_mem {z : Sym} {U : List Name} {a : Ask} {seen : List Ask} (ha : Sub U a.1)
    (hs : AsksInv U seen) : askPat z U a ∈ seen.map (askPat z U) ↔ a ∈ seen := by
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, e⟩
    rw [askPat_inj ha (hs b hb).1 e.symm]
    exact hb
  · exact fun h => ⟨a, h, rfl⟩

open Classical in
/-- Asking what is left, passing over what was answered: whether nothing
that is asked fails. The number bounds the steps. -/
noncomputable def butRun (S : Sorts) (U : List Name) : Nat → List Ask → List Ask → Bool
  | 0, _, _ => true
  | _ + 1, [], _ => true
  | N + 1, a :: T, seen =>
    if a ∈ seen then butRun S U N T seen
    else
      match oneAsks S U a.1 a.2.1 a.2.2 T with
      | none => false
      | some T' => butRun S U N T' (a :: seen)

open Classical in
/-- The ticks that run spends: for each question taken, two for each
question answered and two, and for one not answered before, what its step
spends and three. -/
noncomputable def butRunCost (S : Sorts) (U : List Name) (r q : Nat) :
    Nat → List Ask → List Ask → Nat
  | 0, _, _ => 1
  | _ + 1, [], _ => 1
  | N + 1, a :: T, seen =>
    2 * seen.length + 2 +
      if a ∈ seen then butRunCost S U r q N T seen
      else
        oneCost S U r q a.1 a.2.1 a.2.2 + 2 +
          match oneAsks S U a.1 a.2.1 a.2.2 T with
          | none => 0
          | some T' => 1 + butRunCost S U r q N T' (a :: seen)

theorem butRun_nil (S : Sorts) (U : List Name) (N : Nat) (seen : List Ask) :
    butRun S U N [] seen = true := by cases N <;> rfl

theorem butRunCost_nil (S : Sorts) (U : List Name) (r q N : Nat) (seen : List Ask) :
    butRunCost S U r q N [] seen = 1 := by cases N <;> rfl

theorem included_but_done (s : store.Store) (decls names todo seen : store.TermId) (okb : Bool) :
    sorts.included_but_loop s decls names todo seen okb false ⦃ r => r = (okb, s) ⦄ := by
  unfold sorts.included_but_loop
  rw [loop]
  simp only [sorts.included_but_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem included_but_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {r q : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (hstep : StepOK S U)
    (decls names : store.TermId) :
    ∀ (N : Nat) (T seen : List Ask) (s : store.Store) (todo seeni : store.TermId), mu T ≤ N →
    AsksInv U T → AsksInv U seen → Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val todo.val (encList (nm none) (T.map (askPat (nm none) U))) →
    Repr nm s.nodes.val seeni.val (encList (nm none) (seen.map (askPat (nm none) U))) →
    Room s (butRunCost S U r q N T seen) →
    sorts.included_but_loop s decls names todo seeni true true ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + butRunCost S U r q N T seen ∧
        b = butRun S U N T seen ⦄ := by
  have base : ∀ (N : Nat) (seen : List Ask) (s : store.Store) (todo seeni : store.TermId), Inv s →
      Repr nm s.nodes.val todo.val
        (encList (nm none) (([] : List Ask).map (askPat (nm none) U))) →
      Room s (butRunCost S U r q N [] seen) →
      sorts.included_but_loop s decls names todo seeni true true ⦃ b s' =>
        Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + butRunCost S U r q N [] seen ∧
          b = butRun S U N [] seen ⦄ := by
    intro N seen s todo seeni hI htd hroom
    rw [butRunCost_nil] at hroom ⊢
    rw [butRun_nil]
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.included_but_loop
    rw [loop]
    simp only [sorts.included_but_loop.body, ↓reduceIte]
    step with uncons_repr s todo hI.toWf htd (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := included_but_done s1 decls names todo seeni true
    unfold sorts.included_but_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro res rfl
    have := hK0.ticks
    exact ⟨hK0.ran.ranB.inv hI, hK0.ran.ext, by omega, rfl⟩
  intro N
  induction N with
  | zero =>
    intro T seen s todo seeni hmu hinv _ hI _ _ htd _ hroom
    cases T with
    | nil => exact base 0 seen s todo seeni hI htd hroom
    | cons a T =>
      have := sumSize_pos (hinv a List.mem_cons_self).2
      simp only [mu, List.map_cons, List.sum_cons] at hmu
      omega
  | succ N ih =>
    intro T seen s todo seeni hmu hinv hsinv hI hde hU htd hsn hroom
    cases T with
    | nil => exact base (N + 1) seen s todo seeni hI htd hroom
    | cons a T =>
      obtain ⟨c, n, G⟩ := a
      have hsub : Sub U c := (hinv _ List.mem_cons_self).1
      have hGpos : 0 < Sorts.sumSize G := sumSize_pos (hinv _ List.mem_cons_self).2
      have hinvT : AsksInv U T := fun x hx => hinv x (List.mem_cons_of_mem _ hx)
      have hroom' := hroom
      unfold Room at hroom'
      rw [butRunCost] at hroom' ⊢
      rw [butRun]
      dsimp only at hroom' ⊢
      unfold sorts.included_but_loop
      rw [loop]
      simp only [sorts.included_but_loop.body, ↓reduceIte]
      step with uncons_repr s todo hI.toWf htd (by unfold Room; omega) as ⟨r0, hK0, hu⟩
      obtain ⟨o, s1⟩ := r0
      simp only at hu
      simp only at hK0
      obtain ⟨ai, t, rfl, rai, rt⟩ := hu
      have K0 := hK0.kept hI
      have ht1 := K0.ticks
      have hx1 : Extends s s1 := Extends.of_eq K0.nodes (by omega)
      step with among_spec hC.inj (seen.map (askPat (nm none) U)) s1 ai seeni K0.inv
        (hx1.repr rai) (hx1.repr hsn) (by unfold Room; simp only [List.length_map]; omega)
        as ⟨rm, hI2, hn2, htb2, ht2, hm2, hbm⟩
      obtain ⟨bm, s2⟩ := rm
      simp only [List.length_map] at hI2 hn2 htb2 ht2 hm2 hbm
      have hx2 : Extends s s2 := hx1.trans (Extends.of_eq hn2 hm2)
      have hbm' : bm = true ↔ (c, n, G) ∈ seen := by
        rw [hbm, decide_eq_true_iff]
        exact askPat_mem hsub hsinv
      by_cases hmem : (c, n, G) ∈ seen
      · rw [ite_pos' hmem] at hroom' ⊢
        rw [ite_pos' hmem]
        have hbt : bm = true := hbm'.2 hmem
        subst hbt
        simp only [↓reduceIte, uncurry, bind_ok]
        have IH := ih T seen s2 t seeni
          (by simp only [mu, List.map_cons, List.sum_cons] at hmu ⊢; omega) hinvT hsinv hI2
          (hx2.repr hde) (hx2.repr hU) (hx2.repr rt) (hx2.repr hsn) (by unfold Room; omega)
        unfold sorts.included_but_loop at IH
        refine WP.spec_mono IH ?_
        rintro ⟨b, s'⟩ ⟨hI', hx', ht', hb⟩
        exact ⟨hI', hx2.trans hx', by omega, hb⟩
      · rw [ite_neg' hmem] at hroom' ⊢
        rw [ite_neg' hmem]
        have hbf : bm = false := by
          cases bm with
          | false => rfl
          | true => exact absurd (hbm'.1 rfl) hmem
        subst hbf
        simp only [Bool.false_eq_true, ↓reduceIte, uncurry]
        step with uncons_repr s2 ai hI2.toWf (hx2.repr rai) (by unfold Room; omega)
          as ⟨r1, hK1, hu1⟩
        obtain ⟨o1, s3⟩ := r1
        simp only [askPat] at hu1
        simp only at hK1
        obtain ⟨c1, r1, rfl, rc1, rr1⟩ := hu1
        have K1 := hK1.kept hI2
        have ht3 := K1.ticks
        have hx3 : Extends s s3 := hx2.trans (Extends.of_eq K1.nodes (by omega))
        have hx23 : Extends s2 s3 := Extends.of_eq K1.nodes (by omega)
        step with uncons_repr s3 r1 hK1.wf (hx23.repr rr1) (by unfold Room; omega)
          as ⟨r2, hK2, hu2⟩
        obtain ⟨o2, s4⟩ := r2
        simp only at hu2
        simp only at hK2
        obtain ⟨n1, g1, rfl, rn1, rg1⟩ := hu2
        have K2 := hK2.kept K1.inv
        have ht4 := K2.ticks
        have hx34 : Extends s3 s4 := Extends.of_eq K2.nodes (by omega)
        have hx4 : Extends s s4 := hx3.trans hx34
        have hx24 : Extends s2 s4 := hx23.trans hx34
        step with but_one_spec hC hr hq c n G T hsub s4 decls names c1 n1 g1 t K2.inv
          (hx4.repr hde) (hx4.repr hU) (hx24.repr rc1) (hx34.repr rn1) (hx34.repr rg1)
          (hx4.repr rt) (by unfold Room; omega) as ⟨r3, hI5, hx5, ht5, hres⟩
        obtain ⟨o3, s5⟩ := r3
        simp only at hI5 hx5 ht5 hres
        have hx05 := hx4.trans hx5
        have hst := hstep (c, n, G) T hinv
        simp only at hst
        cases hoa : oneAsks S U c n G T with
        | none =>
          rw [hoa] at hres hst
          subst hres
          simp only [uncurry, bind_ok]
          have hdn := included_but_done s5 decls names todo seeni false
          unfold sorts.included_but_loop at hdn
          refine WP.spec_mono hdn ?_
          rintro res rfl
          exact ⟨hI5, hx05, by omega, rfl⟩
        | some T' =>
          rw [hoa] at hres hst hroom'
          simp only at hroom'
          obtain ⟨td, rfl, rtd⟩ := hres
          obtain ⟨hinv', hlt, -⟩ := hst
          simp only [uncurry]
          step with alloc_ran s5 (.App ai seeni) hI5.toWf
            ⟨(hx05.repr rai).lt, (hx05.repr hsn).lt⟩ (by unfold Room; omega)
            as ⟨rs, hR6, hid6⟩
          obtain ⟨sn1, s6⟩ := rs
          simp only at hR6 hid6
          simp only [uncurry, bind_ok]
          have ht6 := hR6.ticks
          have hx06 := hx05.trans hR6.ext
          have rsn : Repr nm s6.nodes.val sn1.val
              (encList (nm none) (((c, n, G) :: seen).map (askPat (nm none) U))) :=
            .app hid6 (hx06.repr rai) (hx06.repr hsn)
          have IH := ih T' ((c, n, G) :: seen) s6 td sn1 (by omega) hinv'
            (fun x hx => by
              rcases List.mem_cons.1 hx with rfl | hx
              · exact hinv _ List.mem_cons_self
              · exact hsinv x hx)
            (hR6.ranB.inv hI5) (hx06.repr hde) (hx06.repr hU) (hR6.ext.repr rtd) rsn
            (by unfold Room; omega)
          unfold sorts.included_but_loop at IH
          refine WP.spec_mono IH ?_
          rintro ⟨b, s'⟩ ⟨hI', hx', ht', hb⟩
          exact ⟨hI', hx06.trans hx', by omega, hb⟩

/-! ### The run answers the question -/

theorem mu_cons (a : Ask) (T : List Ask) : mu (a :: T) = Sorts.sumSize a.2.2 + mu T := by
  simp [mu]

theorem mu_append (A B : List Ask) : mu (A ++ B) = mu A + mu B := by simp [mu]

theorem mu_one (a : Ask) : mu [a] = Sorts.sumSize a.2.2 := by simp [mu]

theorem le_mu_of_mem {x : Ask} : ∀ {A : List Ask}, x ∈ A → Sorts.sumSize x.2.2 ≤ mu A
  | b :: A, h => by
    rw [mu_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_mu_of_mem h
      omega

/-- One question alone: what it leaves to ask is smaller, and holds exactly
when it does. -/
theorem step_one {S : Sorts} {U : List Name} (hstep : StepOK S U) {a : Ask}
    (ha : Sub U a.1 ∧ a.2.2 ≠ []) :
    match oneAsks S U a.1 a.2.1 a.2.2 [] with
    | none => ¬ HoldA S a
    | some A => AsksInv U A ∧ (∀ x ∈ A, Sorts.sumSize x.2.2 < Sorts.sumSize a.2.2) ∧
        ((∀ x ∈ A, HoldA S x) ↔ HoldA S a) := by
  have h := hstep a [] (fun x hx => by rw [List.mem_singleton.1 hx]; exact ha)
  cases hoa : oneAsks S U a.1 a.2.1 a.2.2 [] with
  | none => rw [hoa] at h; exact h
  | some A =>
    rw [hoa] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, fun x hx => ?_, ?_⟩
    · have := le_mu_of_mem hx
      rw [mu_one] at h2
      omega
    · rw [h3]
      simp

/-- Questions that each leave only questions among them to ask all hold. -/
theorem holds_of_closed {S : Sorts} {U : List Name} (hstep : StepOK S U) {seen : List Ask}
    (hs : AsksInv U seen)
    (hcl : ∀ a ∈ seen, ∃ A, oneAsks S U a.1 a.2.1 a.2.2 [] = some A ∧ ∀ x ∈ A, x ∈ seen) :
    ∀ (k : Nat), ∀ a ∈ seen, Sorts.sumSize a.2.2 ≤ k → HoldA S a := by
  intro k
  induction k with
  | zero =>
    intro a ha hk
    have := sumSize_pos (hs a ha).2
    omega
  | succ k ih =>
    intro a ha hk
    obtain ⟨A, hA, hin⟩ := hcl a ha
    have h := step_one hstep (hs a ha)
    rw [hA] at h
    exact h.2.2.1 fun x hx => ih x (hin x hx) (by have := h.2.1 x hx; omega)

/-- The run from one question: when every question left or answered holds if
the first does, and what an answered question leaves to ask is left or
answered, the run says whether the first holds. -/
theorem butRun_spec {S : Sorts} {U : List Name} (hstep : StepOK S U) (a0 : Ask) :
    ∀ (N : Nat) (T seen : List Ask), mu T ≤ N → AsksInv U T → AsksInv U seen →
    (∀ x ∈ T ++ seen, HoldA S a0 → HoldA S x) →
    (∀ a ∈ seen, ∃ A, oneAsks S U a.1 a.2.1 a.2.2 [] = some A ∧ ∀ x ∈ A, x ∈ T ∨ x ∈ seen) →
    (a0 ∈ T ∨ a0 ∈ seen) →
    (butRun S U N T seen = true ↔ HoldA S a0) := by
  have base : ∀ (N : Nat) (seen : List Ask), AsksInv U seen →
      (∀ a ∈ seen, ∃ A, oneAsks S U a.1 a.2.1 a.2.2 [] = some A ∧
        ∀ x ∈ A, x ∈ ([] : List Ask) ∨ x ∈ seen) →
      (a0 ∈ ([] : List Ask) ∨ a0 ∈ seen) →
      (butRun S U N [] seen = true ↔ HoldA S a0) := by
    intro N seen hs hcl h0
    rw [butRun_nil]
    simp only [true_iff]
    have h0' : a0 ∈ seen := h0.resolve_left (by simp)
    refine holds_of_closed hstep hs (fun a ha => ?_) _ a0 h0' (Nat.le_refl _)
    obtain ⟨A, hA, hin⟩ := hcl a ha
    exact ⟨A, hA, fun x hx => (hin x hx).resolve_left (by simp)⟩
  intro N
  induction N with
  | zero =>
    intro T seen hmu hinv hs _ hcl h0
    cases T with
    | nil => exact base 0 seen hs hcl h0
    | cons a T =>
      have := sumSize_pos (hinv a List.mem_cons_self).2
      rw [mu_cons] at hmu
      omega
  | succ N ih =>
    intro T seen hmu hinv hs himp hcl h0
    cases T with
    | nil => exact base (N + 1) seen hs hcl h0
    | cons a T =>
      have ha := hinv a List.mem_cons_self
      have hpos := sumSize_pos ha.2
      have hinvT : AsksInv U T := fun x hx => hinv x (List.mem_cons_of_mem _ hx)
      rw [mu_cons] at hmu
      rw [butRun]
      by_cases hmem : a ∈ seen
      · rw [ite_pos' hmem]
        refine ih T seen (by omega) hinvT hs (fun x hx => himp x ?_) (fun b hb => ?_) ?_
        · rcases List.mem_append.1 hx with h | h
          · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
          · exact List.mem_append_right _ h
        · obtain ⟨A, hA, hin⟩ := hcl b hb
          refine ⟨A, hA, fun x hx => ?_⟩
          rcases hin x hx with h | h
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inr hmem
            · exact Or.inl h
          · exact Or.inr h
        · rcases h0 with h | h
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inr hmem
            · exact Or.inl h
          · exact Or.inr h
      · rw [ite_neg' hmem, oneAsks_append]
        have h1 := step_one hstep ha
        have himpa : HoldA S a0 → HoldA S a :=
          himp a (List.mem_append_left _ List.mem_cons_self)
        cases hoa : oneAsks S U a.1 a.2.1 a.2.2 [] with
        | none =>
          rw [hoa] at h1
          simp only [Option.map_none, Bool.false_eq_true, false_iff]
          exact fun h => h1 (himpa h)
        | some A =>
          rw [hoa] at h1
          obtain ⟨hA, hlt, hiff⟩ := h1
          simp only [Option.map_some]
          have hmuA : mu A < Sorts.sumSize a.2.2 := by
            have h2 := hstep a [] (fun x hx => by rw [List.mem_singleton.1 hx]; exact ha)
            rw [hoa] at h2
            have := h2.2.1
            rw [mu_one] at this
            exact this
          refine ih (A ++ T) (a :: seen) (by rw [mu_append]; omega) (fun x hx => ?_)
            (fun x hx => ?_) (fun x hx h => ?_) (fun b hb => ?_) ?_
          · rcases List.mem_append.1 hx with h | h
            · exact hA x h
            · exact hinvT x h
          · rcases List.mem_cons.1 hx with rfl | h
            · exact ha
            · exact hs x h
          · rcases List.mem_append.1 hx with hx | hx
            · rcases List.mem_append.1 hx with hx | hx
              · exact hiff.2 (himpa h) x hx
              · exact himp x (List.mem_append_left _ (List.mem_cons_of_mem _ hx)) h
            · rcases List.mem_cons.1 hx with rfl | hx
              · exact himpa h
              · exact himp x (List.mem_append_right _ hx) h
          · rcases List.mem_cons.1 hb with rfl | hb
            · exact ⟨A, hoa, fun x hx => Or.inl (List.mem_append_left _ hx)⟩
            · obtain ⟨A', hA', hin⟩ := hcl b hb
              refine ⟨A', hA', fun x hx => ?_⟩
              rcases hin x hx with h | h
              · rcases List.mem_cons.1 h with rfl | h
                · exact Or.inr List.mem_cons_self
                · exact Or.inl (List.mem_append_right _ h)
              · exact Or.inr (List.mem_cons_of_mem _ h)
          · rcases h0 with h | h
            · rcases List.mem_cons.1 h with rfl | h
              · exact Or.inr List.mem_cons_self
              · exact Or.inl (List.mem_append_right _ h)
            · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The ticks `included_but` may spend: those of the run from the one
question, or of the inclusion when there is no term. -/
noncomputable def inclButCharge (S : Sorts) (U : List Name) (r q : Nat) (c : Sorts.Conj)
    (n : Name) (G : List GTerm) : Nat :=
  inclCost S U.length q + butRunCost S U r q (Sorts.sumSize G) [(c, n, G)] [] + 6

/-- `included_but` answers whether every member of the conjunction, but for
the terms, is in the sort (`Sorts.Hold`), given that one step of asking is
right and what it spends. -/
theorem included_but_run {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {r q : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (hstep : StepOK S U)
    (c : Sorts.Conj) (n : Name) (G : List GTerm)
    (hc : Sub U c) (hn : n ≠ nm none) (s : store.Store) (decls names ci ni g : store.TermId)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hni : Repr nm s.nodes.val ni.val (.sym n))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hroom : Room s (inclButCharge S U r q c n G)) :
    sorts.included_but s decls names ci ni g ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + inclButCharge S U r q c n G ∧
        (b = true ↔ Sorts.Hold S c n G) ⦄ := by
  unfold sorts.included_but
  have hroom' := hroom
  unfold Room at hroom'
  simp only [inclButCharge] at hroom'
  have hW := hI.toWf
  step with is_nil_list hC.inj s g hW hg (by unfold Room; omega) as ⟨b, s1, hb, hK1⟩
  rw [List.map_eq_nil_iff] at hb
  have ht1 := hK1.ticks
  have R1 := hK1.ran
  have I1 : Inv s1 := R1.ranB.inv hI
  cases b with
  | true =>
    have hG0 : G = [] := hb.1 rfl
    subst hG0
    have hmono : inclCost S U.length (Sorts.reachGSet S (c, some n)).card ≤ inclCost S U.length q :=
      outCost_mono S U.length (hq c n)
    simp only [↓reduceIte]
    refine WP.spec_mono (included_spec hC c n hc hn s1 decls names ci ni I1 (R1.ext.repr hde)
      (R1.ext.repr hU) (R1.ext.repr hci) (R1.ext.repr hni) (by unfold Room; omega)) ?_
    rintro ⟨b, s'⟩ ⟨hI', hx', ht', hb'⟩
    refine ⟨hI', R1.ext.trans hx', by simp only [inclButCharge]; omega, ?_⟩
    rw [hb', Sorts.hold_nil]
  | false =>
    have hG0 : G ≠ [] := fun h => absurd (hb.2 h) (by simp)
    have hinv0 : AsksInv U [(c, n, G)] := fun a ha => by
      rw [List.mem_singleton.1 ha]; exact ⟨hc, hG0⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with alloc_ran s1 .Nil hK1.wf trivial (by unfold Room; omega) as ⟨nil, s2, hR2, hid2⟩
    have ht2 := hR2.ticks
    have R2 := R1.trans hR2
    step with alloc_ran s2 (.App ni g) hR2.wf ⟨(R2.ext.repr hni).lt, (R2.ext.repr hg).lt⟩
      (by unfold Room; omega) as ⟨ri, s3, hR3, hid3⟩
    have ht3 := hR3.ticks
    have R3 := R2.trans hR3
    have rr : Repr nm s3.nodes.val ri.val (.app (.sym n) (accPat (nm none) G)) :=
      .app hid3 (R3.ext.repr hni) (R3.ext.repr hg)
    step with alloc_ran s3 (.App ci ri) hR3.wf ⟨(R3.ext.repr hci).lt, rr.lt⟩
      (by unfold Room; omega) as ⟨aski, s4, hR4, hid4⟩
    have ht4 := hR4.ticks
    have R4 := R3.trans hR4
    have rask : Repr nm s4.nodes.val aski.val (askPat (nm none) U (c, n, G)) :=
      .app hid4 (R4.ext.repr hci) (hR4.ext.repr rr)
    step with alloc_ran s4 (.App aski nil) hR4.wf
      ⟨rask.lt, (hR4.ext.repr (hR3.ext.repr (Repr.nil hid2 : Repr nm s2.nodes.val nil.val _))).lt⟩
      (by unfold Room; omega) as ⟨todo, s5, hR5, hid5⟩
    have ht5 := hR5.ticks
    have R5 := R4.trans hR5
    have rtd : Repr nm s5.nodes.val todo.val
        (encList (nm none) ([(c, n, G)].map (askPat (nm none) U))) :=
      .app hid5 (hR5.ext.repr rask) (hR5.ext.repr (hR4.ext.repr (hR3.ext.repr (.nil hid2))))
    refine WP.spec_mono (included_but_loop_spec hC hr hq hstep decls names (Sorts.sumSize G)
      [(c, n, G)] [] s5 todo nil (by simp [mu]) hinv0 (fun a ha => by cases ha)
      (R5.ranB.inv hI) (R5.ext.repr hde) (R5.ext.repr hU) rtd
      (hR5.ext.repr (hR4.ext.repr (hR3.ext.repr (.nil hid2)))) (by unfold Room; omega)) ?_
    rintro ⟨b, s'⟩ ⟨hI', hx', ht', hb'⟩
    refine ⟨hI', R5.ext.trans hx', by simp only [inclButCharge]; omega, ?_⟩
    rw [hb']
    exact butRun_spec hstep (c, n, G) _ _ _ (by simp [mu]) hinv0 (fun a ha => by cases ha)
      (fun x hx h => by
        rw [List.append_nil, List.mem_singleton] at hx
        rw [hx]; exact h)
      (fun a ha => by cases ha) (Or.inl List.mem_cons_self)

/-! ### The bound: the questions that differ

The run asks a question once, so what it spends is bounded by the questions
that can come up, however often each does. -/

theorem length_le_of_nodup {α : Type} {l Q : List α} (hn : l.Nodup) (h : ∀ x ∈ l, x ∈ Q) :
    l.length ≤ Q.length :=
  (List.subperm_of_subset hn h).length_le

open Classical in
/-- What the run spends is bounded by the questions that can come up. Let
`Q` list them: it has the questions asked and answered, and with a question
those its step leaves to ask, `W` at most. Let a step on one of them spend
`B` at most. Then each question taken off costs one search of the questions
answered, `2 |Q| + 2` at most, and each question of `Q` is answered once at
most, for `B + 3` and the searches for the `W` it leaves. -/
theorem butRunCost_le {S : Sorts} {U : List Name} {r q : Nat} (Q : List Ask) (B W : Nat)
    (hB : ∀ a ∈ Q, oneCost S U r q a.1 a.2.1 a.2.2 ≤ B)
    (hW : ∀ a ∈ Q, ∀ C, oneAsks S U a.1 a.2.1 a.2.2 [] = some C →
      C.length ≤ W ∧ ∀ x ∈ C, x ∈ Q) :
    ∀ (N : Nat) (T seen : List Ask), seen.Nodup → (∀ x ∈ seen, x ∈ Q) → (∀ x ∈ T, x ∈ Q) →
      butRunCost S U r q N T seen + seen.length * (B + 3 + W * (2 * Q.length + 2)) ≤
        T.length * (2 * Q.length + 2) + Q.length * (B + 3 + W * (2 * Q.length + 2)) + 1 := by
  intro N
  generalize hP : 2 * Q.length + 2 = P
  generalize hD : B + 3 + W * P = D
  induction N with
  | zero =>
    intro T seen hn hs _
    have := Nat.mul_le_mul_right D (length_le_of_nodup hn hs)
    rw [butRunCost]
    omega
  | succ N ih =>
    intro T seen hn hs hT
    have hsl := length_le_of_nodup hn hs
    have hsD := Nat.mul_le_mul_right D hsl
    cases T with
    | nil =>
      rw [butRunCost]
      omega
    | cons a T =>
      have hT' : ∀ x ∈ T, x ∈ Q := fun x hx => hT x (List.mem_cons_of_mem _ hx)
      have haQ : a ∈ Q := hT a List.mem_cons_self
      rw [butRunCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      by_cases ha : a ∈ seen
      · rw [ite_pos' ha]
        have := ih T seen hn hs hT'
        omega
      · rw [ite_neg' ha]
        have hn' : (a :: seen).Nodup := List.nodup_cons.2 ⟨ha, hn⟩
        have hs' : ∀ x ∈ a :: seen, x ∈ Q := fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact haQ
          · exact hs x hx
        have hsl' := length_le_of_nodup hn' hs'
        rw [List.length_cons] at hsl'
        have hsD' := Nat.mul_le_mul_right D hsl'
        rw [Nat.add_mul, Nat.one_mul] at hsD'
        have hb := hB a haQ
        rw [oneAsks_append]
        cases hoa : oneAsks S U a.1 a.2.1 a.2.2 [] with
        | none =>
          simp only [Option.map_none]
          omega
        | some C =>
          simp only [Option.map_some]
          show 2 * seen.length + 2 + (oneCost S U r q a.1 a.2.1 a.2.2 + 2 +
              (1 + butRunCost S U r q N (C ++ T) (a :: seen))) + seen.length * D ≤
            T.length * P + P + Q.length * D + 1
          obtain ⟨hCl, hCQ⟩ := hW a haQ C hoa
          have hCT : ∀ x ∈ C ++ T, x ∈ Q := fun x hx => by
            rcases List.mem_append.1 hx with h | h
            · exact hCQ x h
            · exact hT' x h
          have := ih (C ++ T) (a :: seen) hn' hs' hCT
          rw [List.length_cons, List.length_append, Nat.add_mul, Nat.one_mul, Nat.add_mul] at this
          have hCP := Nat.mul_le_mul_right P hCl
          omega

/-- What `included_but` spends is bounded by the questions that can come up
from its own (`butRunCost_le`): the inclusion, and for each of them a step,
and a search of them for each question it leaves. -/
theorem inclButCharge_le {S : Sorts} {U : List Name} {r q : Nat} (Q : List Ask) (B W : Nat)
    (hB : ∀ a ∈ Q, oneCost S U r q a.1 a.2.1 a.2.2 ≤ B)
    (hW : ∀ a ∈ Q, ∀ C, oneAsks S U a.1 a.2.1 a.2.2 [] = some C →
      C.length ≤ W ∧ ∀ x ∈ C, x ∈ Q)
    {c : Sorts.Conj} {n : Name} {G : List GTerm} (h0 : (c, n, G) ∈ Q) :
    inclButCharge S U r q c n G ≤
      inclCost S U.length q + 2 * Q.length +
        Q.length * (B + 3 + W * (2 * Q.length + 2)) + 9 := by
  have := butRunCost_le Q B W hB hW (Sorts.sumSize G) [(c, n, G)] [] List.nodup_nil
    (fun x hx => by cases hx) (fun x hx => by rw [List.mem_singleton.1 hx]; exact h0)
  simp only [List.length_nil, Nat.zero_mul, Nat.add_zero, List.length_singleton, Nat.one_mul]
    at this
  unfold inclButCharge
  omega

end RwLogVerified
