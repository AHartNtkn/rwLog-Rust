/-
One step of asking in inclusion but for finitely many terms is right: what
`but_one` leaves to ask holds exactly when what was asked holds
(`Sorts.hold_iff`), and is of smaller terms (`Sorts.sum_proj_le`). With that
and a bound on what one step spends, `included_but` decides `Sorts.Hold`.
-/
import RwLogVerified.ButLoop

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The arguments that are the one member held -/

/-- The argument at a place is the one member held for it. -/
def SoleAt (sl : List (Option GTerm)) (args : List GTerm) (j : Nat) : Prop :=
  ∃ a, args[j]? = some a ∧ sl[j]? = some (some a)

theorem soleAt_zero {o : Option GTerm} {sl : List (Option GTerm)} {a : GTerm} {ar : List GTerm} :
    SoleAt (o :: sl) (a :: ar) 0 ↔ o = some a := by
  simp only [SoleAt, List.getElem?_cons_zero, Option.some.injEq]
  constructor
  · rintro ⟨b, rfl, h⟩; exact h
  · intro h; exact ⟨a, rfl, h⟩

theorem soleAt_succ {o : Option GTerm} {sl : List (Option GTerm)} {a : GTerm} {ar : List GTerm}
    {j : Nat} : SoleAt (o :: sl) (a :: ar) (j + 1) ↔ SoleAt sl ar j := by
  simp only [SoleAt, List.getElem?_cons_succ]

theorem missCount_eq_zero : ∀ (sl : List (Option GTerm)) (args : List GTerm),
    sl.length = args.length → (missCount sl args = 0 ↔ ∀ j < args.length, SoleAt sl args j)
  | [], [], _ => by simp [missCount]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | o :: sl, a :: ar, h => by
    have ih := missCount_eq_zero sl ar (by simpa using h)
    simp only [missCount, List.length_cons]
    constructor
    · intro h0 j hj
      rcases j with _ | j
      · rw [soleAt_zero]
        by_contra hne
        simp [hne] at h0
      · rw [soleAt_succ]
        exact ih.1 (by omega) j (by omega)
    · intro hall
      have h1 : o = some a := soleAt_zero.1 (hall 0 (by omega))
      have h2 := ih.2 fun j hj => soleAt_succ.1 (hall (j + 1) (by omega))
      simp [h1, h2]

theorem missCount_le_one : ∀ (sl : List (Option GTerm)) (args : List GTerm) (i : Nat),
    sl.length = args.length → i < args.length →
    ((∀ j < args.length, j ≠ i → SoleAt sl args j) ↔
      missCount sl args ≤ 1 ∧ (missCount sl args = 0 ∨ ¬ SoleAt sl args i))
  | [], [], _, _, hi => by simp at hi
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | o :: sl, a :: ar, i, h, hi => by
    have hl : sl.length = ar.length := by simpa using h
    have h0 := missCount_eq_zero sl ar hl
    simp only [missCount, List.length_cons]
    rcases i with _ | i
    · rw [soleAt_zero]
      have hiff : (∀ j < ar.length + 1, j ≠ 0 → SoleAt (o :: sl) (a :: ar) j) ↔
          missCount sl ar = 0 := by
        rw [h0]
        constructor
        · intro hall j hj
          exact soleAt_succ.1 (hall (j + 1) (by omega) (by omega))
        · intro hall j hj hne
          rcases j with _ | j
          · exact absurd rfl hne
          · exact soleAt_succ.2 (hall j (by omega))
      rw [hiff]
      by_cases hoa : o = some a
      · simp only [hoa, ↓reduceIte, Nat.zero_add, not_true_eq_false, or_false]; omega
      · simp only [hoa, ↓reduceIte, not_false_eq_true, or_true, and_true]; omega
    · have ih := missCount_le_one sl ar i hl (by simpa using hi)
      rw [soleAt_succ]
      have hiff : (∀ j < ar.length + 1, j ≠ i + 1 → SoleAt (o :: sl) (a :: ar) j) ↔
          o = some a ∧ ∀ j < ar.length, j ≠ i → SoleAt sl ar j := by
        constructor
        · intro hall
          exact ⟨soleAt_zero.1 (hall 0 (by omega) (by omega)), fun j hj hne =>
            soleAt_succ.1 (hall (j + 1) (by omega) (by omega))⟩
        · rintro ⟨h1, hall⟩ j hj hne
          rcases j with _ | j
          · exact soleAt_zero.2 h1
          · exact soleAt_succ.2 (hall j (by omega) (by omega))
      rw [hiff, ih]
      by_cases hoa : o = some a
      · simp only [hoa, ↓reduceIte, Nat.zero_add, true_and]
      · simp only [hoa, ↓reduceIte, false_and, false_iff, not_and, not_or]
        intro hle
        have hz : missCount sl ar = 0 := by omega
        exact ⟨by omega, fun hn => hn (h0.1 hz i (by simpa using hi))⟩

theorem contribL_getElem? (any : Bool) : ∀ (sl : List (Option GTerm)) (args : List GTerm)
    (accs : List (List GTerm)) (i : Nat) (o : Option GTerm) (a : GTerm) (l : List GTerm),
    sl[i]? = some o → args[i]? = some a → accs[i]? = some l →
    (contribL any sl args accs)[i]? = some (if any = true ∧ o = some a then l else a :: l)
  | [], _, _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | o' :: sl, a' :: ar, acc :: accs, 0, o, a, l, h1, h2, h3 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2 h3
    subst h1 h2 h3
    simp [contribL]
  | o' :: sl, a' :: ar, acc :: accs, i + 1, o, a, l, h1, h2, h3 => by
    simp only [List.getElem?_cons_succ] at h1 h2 h3
    simpa [contribL] using contribL_getElem? any sl ar accs i o a l h1 h2 h3

/-! ## The argument a term gives a place -/

open Classical in
/-- The argument at a place of a term with the root whose other arguments
are each the one member held for them. -/
noncomputable def pick (sl : List (Option GTerm)) (f : Sym) (k i : Nat) (t : GTerm) :
    Option GTerm :=
  if (termKey t).1 = f ∧ (termKey t).2 = k ∧ ∀ j < k, j ≠ i → SoleAt sl (gspine t []).2 j then
    (gspine t []).2[i]?
  else none

theorem projStep_getElem? {sl : List (Option GTerm)} {f : Sym} {k i : Nat} (hsl : sl.length = k)
    {A : List (List GTerm)} (hi : i < k) {l : List GTerm} (hl : A[i]? = some l) (t : GTerm) :
    (projStep sl f k A t)[i]? = some ((pick sl f k i t).toList ++ l) := by
  classical
  unfold projStep pick
  by_cases hkey : (termKey t).1 = f ∧ (termKey t).2 = k
  swap
  · rw [ite_neg' (fun h => hkey ⟨h.1, h.2.1⟩), ite_neg' (fun h => hkey ⟨h.1, h.2.1⟩)]
    simpa using hl
  obtain ⟨rfl, rfl⟩ := hkey
  have hal : (gspine t []).2.length = (termKey t).2 := rfl
  have hM := missCount_le_one sl (gspine t []).2 i (hsl.trans hal.symm) (by omega)
  rw [hal] at hM
  obtain ⟨a, ha⟩ : ∃ a, (gspine t []).2[i]? = some a :=
    ⟨(gspine t []).2[i]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨o, ho⟩ : ∃ o, sl[i]? = some o := ⟨sl[i]'(by omega), List.getElem?_eq_getElem _⟩
  have hsole : SoleAt sl (gspine t []).2 i ↔ o = some a := by
    simp only [SoleAt, ha, ho, Option.some.injEq]
    constructor
    · rintro ⟨b, rfl, h⟩; exact h
    · intro h; exact ⟨a, rfl, h⟩
  by_cases hm : missCount sl (gspine t []).2 ≤ 1
  · simp only [true_and, hm, ↓reduceIte]
    rw [contribL_getElem? _ sl _ A i o a l ho ha hl]
    by_cases h0 : missCount sl (gspine t []).2 = 0
    · have hP := hM.2 ⟨hm, Or.inl h0⟩
      rw [ite_pos' hP, ha]
      simp [h0]
    · by_cases hs : o = some a
      · have hnP : ¬ ∀ j < (termKey t).2, j ≠ i → SoleAt sl (gspine t []).2 j := by
          intro hP
          rcases (hM.1 hP).2 with h | h
          · exact h0 h
          · exact h (hsole.2 hs)
        have hpos : 0 < missCount sl (gspine t []).2 := Nat.pos_of_ne_zero h0
        simp only [hnP, ↓reduceIte, hs, hpos, decide_true, and_self, Option.toList_none,
          List.nil_append]
      · have hP := hM.2 ⟨hm, Or.inr fun h => hs (hsole.1 h)⟩
        rw [ite_pos' hP, ha]
        simp [hs]
  · have hnP : ¬ ∀ j < (termKey t).2, j ≠ i → SoleAt sl (gspine t []).2 j :=
      fun hP => hm (hM.1 hP).1
    simp only [true_and, hm, hnP, ↓reduceIte, Option.toList_none, List.nil_append]
    exact hl

theorem projsL_getElem? {sl : List (Option GTerm)} {f : Sym} {k i : Nat} (hsl : sl.length = k)
    (hi : i < k) : ∀ (G : List GTerm) (A : List (List GTerm)) (l : List GTerm), A.length = k →
    A[i]? = some l →
    (projsL sl f k G A)[i]? = some ((G.filterMap (pick sl f k i)).reverse ++ l)
  | [], A, l, _, hl => by simpa [projsL] using hl
  | t :: G, A, l, hA, hl => by
    have ih := projsL_getElem? (f := f) hsl hi G (projStep sl f k A t) _ (length_projStep hsl hA t)
      (projStep_getElem? hsl hi hl t)
    simp only [projsL, List.foldl_cons] at ih ⊢
    rw [ih]
    cases h : pick sl f k i t <;> simp [h]

/-! ## What `but_key` computes is what the specification asks -/

theorem oneOf_eq_some {S : Sorts} {d : Sorts.Conj} {t : GTerm} :
    oneOf S d = some t ↔ Sorts.count S d = .one t := by
  unfold oneOf
  cases h : Sorts.count S d <;> simp

theorem keySoles_getElem? (S : Sorts) (c : Sorts.Conj) (f : Sym) {k j : Nat} (hj : j < k) :
    (keySoles S c (f, k))[j]? = some (oneOf S (Sorts.kidC S c f k j)) := by
  simp [keySoles, altOf, hj]

theorem ones_iff {S : Sorts} {c : Sorts.Conj} {f : Sym} {skip : Option Nat} {args : List GTerm} :
    Sorts.Ones S c f skip args ↔
      ∀ j < args.length, some j ≠ skip → SoleAt (keySoles S c (f, args.length)) args j := by
  unfold Sorts.Ones
  refine forall_congr' fun j => ?_
  constructor
  · intro h hj hne
    exact ⟨args[j], List.getElem?_eq_getElem hj, by
      rw [keySoles_getElem? S c f hj]; exact congrArg some (oneOf_eq_some.2 (h hj hne))⟩
  · intro h hj hne
    obtain ⟨a, ha, hs⟩ := h hj hne
    rw [List.getElem?_eq_getElem hj] at ha
    cases ha
    rw [keySoles_getElem? S c f hj] at hs
    exact oneOf_eq_some.1 (Option.some.inj hs)

theorem spine_gspine (t : GTerm) : t.spine = some ((gspine t []).1, (gspine t []).2) := by
  have hg : t = Term.mk (gspine t []).1 (gspine t []).2 := by simpa using gspine_mk t []
  conv_lhs => rw [hg]
  exact Term.spine_mk _ _

theorem onlyInL_eq (S : Sorts) (c : Sorts.Conj) (f : Sym) (k : Nat) (G : List GTerm) :
    onlyInL (keySoles S c (f, k)) f k G = Sorts.onlyIn S c f k G := by
  unfold onlyInL Sorts.onlyIn
  congr 1
  funext t
  rw [spine_gspine]
  simp only
  refine decide_eq_decide.2 (and_congr Iff.rfl (and_congr_right fun hk => ?_))
  change (gspine t []).2.length = k at hk
  subst hk
  have hl : (keySoles S c (f, (gspine t []).2.length)).length = (gspine t []).2.length := by
    simp [keySoles, altOf]
  rw [missCount_eq_zero _ _ hl, ones_iff]
  simp

theorem pick_eq (S : Sorts) (c : Sorts.Conj) (f : Sym) (k i : Nat) (G : List GTerm) :
    G.filterMap (pick (keySoles S c (f, k)) f k i) = Sorts.proj S c f k i G := by
  classical
  unfold Sorts.proj
  congr 1
  funext t
  rw [spine_gspine]
  simp only
  unfold pick
  have hiff : ((termKey t).1 = f ∧ (termKey t).2 = k ∧
      ∀ j < k, j ≠ i → SoleAt (keySoles S c (f, k)) (gspine t []).2 j) ↔
      ((gspine t []).1 = f ∧ (gspine t []).2.length = k ∧
        Sorts.Ones S c f (some i) (gspine t []).2) := by
    refine and_congr Iff.rfl (and_congr_right fun hk => ?_)
    change (gspine t []).2.length = k at hk
    subst hk
    rw [ones_iff]
    simp only [ne_eq, Option.some.injEq]
  by_cases h : (gspine t []).1 = f ∧ (gspine t []).2.length = k ∧
      Sorts.Ones S c f (some i) (gspine t []).2
  · rw [ite_pos' h, ite_pos' (hiff.2 h)]
  · rw [ite_neg' h, ite_neg' fun h' => h (hiff.1 h')]

theorem getElem?_zip {α β : Type} : ∀ (l₁ : List α) (l₂ : List β) (i : Nat) (a : α) (b : β),
    (l₁.zip l₂)[i]? = some (a, b) ↔ l₁[i]? = some a ∧ l₂[i]? = some b
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | x :: l₁, y :: l₂, 0, a, b => by simp
  | x :: l₁, y :: l₂, i + 1, a, b => by simpa using getElem?_zip l₁ l₂ i a b

theorem altOf_getElem? (S : Sorts) (c : Sorts.Conj) (f : Sym) (k i : Nat) :
    (altOf S c f k)[i]? = if i < k then some (Sorts.kidC S c f k i) else none := by
  unfold altOf
  by_cases hi : i < k <;> simp [hi]

/-- The terms left for each argument of a root. -/
noncomputable def accsL (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (key : Sym × Nat) :
    List (List GTerm) :=
  projsL (keySoles S c key) key.1 key.2 G (List.replicate key.2 [])

theorem length_accsL (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (f : Sym) (k : Nat) :
    (accsL S c G (f, k)).length = k :=
  length_projsL (by simp [keySoles, altOf]) G _ (List.length_replicate ..)

theorem accsL_getElem? (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (f : Sym) (k i : Nat) :
    (accsL S c G (f, k))[i]? =
      if i < k then some (Sorts.proj S c f k i G).reverse else none := by
  by_cases hi : i < k
  · rw [ite_pos' hi]
    have h := projsL_getElem? (sl := keySoles S c (f, k)) (f := f) (by simp [keySoles, altOf]) hi
      G (List.replicate k []) [] (List.length_replicate ..) (by simp [hi])
    rw [pick_eq, List.append_nil] at h
    exact h
  · rw [ite_neg' hi]
    exact List.getElem?_eq_none (by rw [length_accsL]; omega)

theorem mem_keyItems {S : Sorts} {c : Sorts.Conj} {G : List GTerm} {f : Sym} {k : Nat}
    {kn : List (Option Name)} {x : Sorts.Conj × Option Name × List GTerm} :
    x ∈ keyItems S c G (f, k) kn ↔ ∃ i < k, x.1 = Sorts.kidC S c f k i ∧ kn[i]? = some x.2.1 ∧
      x.2.2 = (Sorts.proj S c f k i G).reverse := by
  obtain ⟨d, m, l⟩ := x
  have hacc := accsL_getElem? S c G f k
  unfold accsL at hacc
  unfold keyItems
  rw [List.mem_iff_getElem?]
  refine exists_congr fun i => ?_
  rw [getElem?_zip, getElem?_zip, altOf_getElem?, hacc]
  by_cases hi : i < k
  · simp only [hi, ↓reduceIte, Option.some.injEq, true_and]
    constructor
    · rintro ⟨rfl, h1, rfl⟩; exact ⟨rfl, h1, rfl⟩
    · rintro ⟨rfl, h1, rfl⟩; exact ⟨rfl, h1, rfl⟩
  · simp [hi]

/-! ## What a root leaves to ask holds exactly when the root's ask holds -/

/-- What an argument asks holds. -/
def itemOK (S : Sorts) (x : Sorts.Conj × Option Name × List GTerm) : Prop :=
  ∀ m, x.2.1 = some m → Sorts.Hold S x.1 m x.2.2

theorem askOf_some {x : Sorts.Conj × Option Name × List GTerm} {a : Ask} (h : askOf x = some a) :
    a.1 = x.1 ∧ x.2.1 = some a.2.1 ∧ a.2.2 = x.2.2 ∧ a.2.2 ≠ [] := by
  obtain ⟨d, k, l⟩ := x
  cases k with
  | none => simp [askOf] at h
  | some m =>
    cases l with
    | nil => simp [askOf] at h
    | cons b l =>
      simp only [askOf, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, by simp⟩

theorem push_iff (S : Sorts) (items : List (Sorts.Conj × Option Name × List GTerm)) :
    (pushOK S items ∧ ∀ a ∈ items.filterMap askOf, HoldA S a) ↔ ∀ x ∈ items, itemOK S x := by
  constructor
  · rintro ⟨h1, h2⟩ ⟨d, k, l⟩ hx m hm
    simp only at hm
    subst hm
    cases l with
    | nil => exact Sorts.hold_nil.2 (h1 _ hx m rfl rfl)
    | cons a l => exact h2 (d, m, a :: l) (List.mem_filterMap.2 ⟨_, hx, rfl⟩)
  · intro h
    refine ⟨fun x hx m hm hl => ?_, fun a ha => ?_⟩
    · have := h x hx m hm
      rw [hl] at this
      exact Sorts.hold_nil.1 this
    · obtain ⟨x, hx, hxa⟩ := List.mem_filterMap.1 ha
      obtain ⟨h1, h2, h3, -⟩ := askOf_some hxa
      have := h x hx a.2.1 h2
      rw [← h1, ← h3] at this
      exact this

theorem askKey_iff (S : Sorts) (c : Sorts.Conj) (n : Name) (G : List GTerm) (f : Sym) (k : Nat) :
    Sorts.AskKey S c n G (f, k) ↔
      ∃ A, keyAsks S c n G (f, k) = some A ∧ ∀ a ∈ A, HoldA S a := by
  classical
  unfold Sorts.AskKey keyAsks
  by_cases hlive : Sorts.LiveKey S (Sorts.live S) c (f, k)
  swap
  · rw [ite_neg' hlive]
    simp [hlive]
  rw [ite_pos' hlive]
  simp only [hlive, forall_const]
  cases hs : Sorts.step S n f k with
  | none =>
    simp only
    rw [← onlyInL_eq]
    by_cases ho : onlyInL (keySoles S c (f, k)) f k G = true
    · simp [ho]
    · simp [ho]
  | some kn =>
    simp only
    have hR : (∃ A, (if pushOK S (keyItems S c G (f, k) kn) then
        some ((keyItems S c G (f, k) kn).filterMap askOf).reverse else none) = some A ∧
          ∀ a ∈ A, HoldA S a) ↔ ∀ x ∈ keyItems S c G (f, k) kn, itemOK S x := by
      rw [← push_iff]
      by_cases hok : pushOK S (keyItems S c G (f, k) kn)
      · rw [ite_pos' hok]
        simp [hok]
      · rw [ite_neg' hok]
        simp [hok]
    rw [hR]
    constructor
    · intro h x hx m hm
      obtain ⟨i, hi, h1, h2, h3⟩ := mem_keyItems.1 hx
      rw [h1, h3]
      rw [hm] at h2
      exact (Sorts.Hold.congr fun t => List.mem_reverse).2 (h i hi m h2)
    · intro h i hi m hm
      have := h (Sorts.kidC S c f k i, some m, (Sorts.proj S c f k i G).reverse)
        (mem_keyItems.2 ⟨i, hi, rfl, hm, rfl⟩) m rfl
      exact (Sorts.Hold.congr fun t => List.mem_reverse).1 this

/-! ## What a root leaves to ask is of smaller terms -/

theorem mu_reverse (l : List Ask) : mu l.reverse = mu l := by
  simp [mu, List.sum_reverse]

theorem sumSize_reverse (l : List GTerm) : Sorts.sumSize l.reverse = Sorts.sumSize l := by
  simp [Sorts.sumSize, List.sum_reverse]

theorem mu_filterMap_le : ∀ items : List (Sorts.Conj × Option Name × List GTerm),
    mu (items.filterMap askOf) ≤ (items.map fun x => Sorts.sumSize x.2.2).sum
  | [] => by simp [mu]
  | x :: items => by
    have ih := mu_filterMap_le items
    cases h : askOf x with
    | none =>
      simp only [List.filterMap_cons, h, List.map_cons, List.sum_cons]
      omega
    | some a =>
      obtain ⟨-, -, h3, -⟩ := askOf_some h
      simp only [List.filterMap_cons, h, mu, List.map_cons, List.sum_cons, h3] at ih ⊢
      omega

theorem map_zip_snd_snd {α β γ : Type} : ∀ (l₁ : List α) (l₂ : List β) (l₃ : List γ),
    l₁.length = l₃.length → l₂.length = l₃.length → (l₁.zip (l₂.zip l₃)).map (·.2.2) = l₃
  | _, _, [], _, _ => by simp
  | [], _, _ :: _, h, _ => by simp at h
  | _ :: _, [], _ :: _, _, h => by simp at h
  | a :: l₁, b :: l₂, c :: l₃, h1, h2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact map_zip_snd_snd l₁ l₂ l₃ (by simpa using h1) (by simpa using h2)

theorem accsL_eq (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (f : Sym) (k : Nat) :
    accsL S c G (f, k) = (List.range k).map fun i => (Sorts.proj S c f k i G).reverse := by
  apply List.ext_getElem?
  intro i
  rw [accsL_getElem?]
  by_cases hi : i < k <;> simp [hi]

theorem sum_keyItems (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (f : Sym) (k : Nat)
    {kn : List (Option Name)} (hkn : kn.length = k) :
    ((keyItems S c G (f, k) kn).map fun x => Sorts.sumSize x.2.2).sum =
      Sorts.projW S c G (f, k) := by
  have h1 : (keyItems S c G (f, k) kn).map (·.2.2) = accsL S c G (f, k) := by
    unfold keyItems
    exact map_zip_snd_snd _ _ _ (by rw [← accsL, length_accsL]; simp [altOf])
      (by rw [← accsL, length_accsL, hkn])
  have h2 : ((keyItems S c G (f, k) kn).map fun x => Sorts.sumSize x.2.2) =
      ((keyItems S c G (f, k) kn).map (·.2.2)).map Sorts.sumSize := by
    rw [List.map_map]; rfl
  rw [h2, h1, accsL_eq, List.map_map]
  unfold Sorts.projW
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  exact sumSize_reverse _

theorem keyAsks_small {S : Sorts} {U : List Name} (hnames : ∀ n ∈ Sorts.names S, n ∈ U)
    {c : Sorts.Conj} {n : Name} {G : List GTerm} {f : Sym} {k : Nat} {A : List Ask}
    (h : keyAsks S c n G (f, k) = some A) :
    mu A ≤ Sorts.projW S c G (f, k) ∧ ∀ a ∈ A, Sub U a.1 ∧ a.2.2 ≠ [] := by
  classical
  unfold keyAsks at h
  by_cases hlive : Sorts.LiveKey S (Sorts.live S) c (f, k)
  swap
  · rw [ite_neg' hlive] at h
    cases h
    simp [mu]
  rw [ite_pos' hlive] at h
  cases hs : Sorts.step S n f k with
  | none =>
    simp only [hs] at h
    by_cases ho : onlyInL (keySoles S c (f, k)) f k G = true
    · rw [ite_pos' ho] at h
      cases h
      simp [mu]
    · rw [ite_neg' ho] at h
      cases h
  | some kn =>
    simp only [hs] at h
    by_cases hok : pushOK S (keyItems S c G (f, k) kn)
    · rw [ite_pos' hok] at h
      cases h
      refine ⟨?_, fun a ha => ?_⟩
      · rw [mu_reverse, ← sum_keyItems S c G f k (Sorts.step_length hs)]
        exact mu_filterMap_le _
      · rw [List.mem_reverse] at ha
        obtain ⟨x, hx, hxa⟩ := List.mem_filterMap.1 ha
        obtain ⟨h1, -, -, h4⟩ := askOf_some hxa
        obtain ⟨i, -, hi1, -, -⟩ := mem_keyItems.1 hx
        refine ⟨?_, h4⟩
        rw [h1, hi1]
        exact fun y hy => hnames y (Sorts.kidC_subset_names hy)
    · rw [ite_neg' hok] at h
      cases h

/-! ## One step of asking is right -/

theorem mu_append (A B : List Ask) : mu (A ++ B) = mu A + mu B := by simp [mu]

theorem foldAsks_spec {S : Sorts} {U : List Name} (hnames : ∀ n ∈ Sorts.names S, n ∈ U)
    (c : Sorts.Conj) (n : Name) (G : List GTerm) : ∀ (K : List (Sym × Nat)) (T : List Ask),
    match foldAsks S c n G K T with
    | some T' => ∃ A, T' = A ++ T ∧ mu A ≤ (K.map (Sorts.projW S c G)).sum ∧
        (∀ a ∈ A, Sub U a.1 ∧ a.2.2 ≠ []) ∧
        ((∀ a ∈ A, HoldA S a) ↔ ∀ κ ∈ K, Sorts.AskKey S c n G κ)
    | none => ∃ κ ∈ K, ¬ Sorts.AskKey S c n G κ
  | [], T => by
    simp only [foldAsks]
    exact ⟨[], rfl, by simp [mu], by simp, by simp⟩
  | (f, k) :: K, T => by
    cases hka : keyAsks S c n G (f, k) with
    | none =>
      simp only [foldAsks, hka]
      refine ⟨(f, k), List.mem_cons_self, fun h => ?_⟩
      obtain ⟨A, hA, -⟩ := (askKey_iff S c n G f k).1 h
      rw [hka] at hA
      cases hA
    | some Aκ =>
      have ih := foldAsks_spec hnames c n G K (Aκ ++ T)
      have hk' : Sorts.AskKey S c n G (f, k) ↔ ∀ a ∈ Aκ, HoldA S a := by
        rw [askKey_iff, hka]
        simp
      obtain ⟨hmu, hinv⟩ := keyAsks_small hnames hka
      simp only [foldAsks, hka]
      cases hfa : foldAsks S c n G K (Aκ ++ T) with
      | none =>
        rw [hfa] at ih
        obtain ⟨κ', hκ', hn⟩ := ih
        exact ⟨κ', List.mem_cons_of_mem _ hκ', hn⟩
      | some T' =>
        rw [hfa] at ih
        obtain ⟨A', rfl, hmu', hinv', hiff⟩ := ih
        refine ⟨A' ++ Aκ, by simp, ?_, ?_, ?_⟩
        · rw [mu_append]
          simp only [List.map_cons, List.sum_cons]
          omega
        · intro a ha
          rcases List.mem_append.1 ha with h | h
          · exact hinv' a h
          · exact hinv a h
        · constructor
          · intro h κ hκ
            rcases List.mem_cons.1 hκ with rfl | hκ
            · exact hk'.2 fun a ha => h a (List.mem_append_right _ ha)
            · exact hiff.1 (fun a ha => h a (List.mem_append_left _ ha)) κ hκ
          · intro h a ha
            rcases List.mem_append.1 ha with ha | ha
            · exact hiff.2 (fun κ hκ => h κ (List.mem_cons_of_mem _ hκ)) a ha
            · exact hk'.1 (h _ List.mem_cons_self) a ha

/-- One step of asking is right, for well-formed sorts whose names are
listed. -/
theorem stepOK {S : Sorts} {U : List Name} (hS : S.WellFormed)
    (hnames : ∀ n ∈ Sorts.names S, n ∈ U) : StepOK S U := by
  rintro ⟨c, n, G⟩ T hinv
  obtain ⟨hsub, hG⟩ := hinv _ List.mem_cons_self
  simp only at hsub hG ⊢
  unfold oneAsks
  have hh := Sorts.hold_iff hS hG c n
  by_cases hfo : Sorts.FreshOut S c n
  · rw [ite_pos' hfo]
    exact fun h => (hh.1 h).1 hfo
  rw [ite_neg' hfo]
  have hf := foldAsks_spec hnames c n G (butKeysL S (conjList U (· ∈ c)) n G) T
  have hmem : ∀ κ, κ ∈ butKeysL S (conjList U (· ∈ c)) n G ↔ κ ∈ Sorts.butKeys S c n G :=
    fun κ => mem_butKeysL hsub n G
  cases hfa : foldAsks S c n G (butKeysL S (conjList U (· ∈ c)) n G) T with
  | none =>
    rw [hfa] at hf
    obtain ⟨κ, hκ, hn⟩ := hf
    exact fun h => hn ((hh.1 h).2 κ ((hmem κ).1 hκ))
  | some T' =>
    rw [hfa] at hf
    obtain ⟨A, rfl, hmu, hinvA, hiff⟩ := hf
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with h | h
      · exact hinvA a h
      · exact hinv a (List.mem_cons_of_mem _ h)
    · have h1 := Sorts.sum_proj_le (S := S) c (butKeysL_nodup S (conjList U (· ∈ c)) n G) G
      have h2 : 0 < G.length := List.length_pos_iff.2 hG
      rw [mu_append]
      simp only [mu, List.map_cons, List.sum_cons] at hmu ⊢
      omega
    · constructor
      · intro h x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hh.2 ⟨hfo, fun κ hκ =>
            hiff.1 (fun a ha => h a (List.mem_append_left _ ha)) κ ((hmem κ).2 hκ)⟩
        · exact h x (List.mem_append_right _ hx)
      · intro h x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hiff.2 (fun κ hκ => (hh.1 (h _ List.mem_cons_self)).2 κ ((hmem κ).1 hκ)) x hx
        · exact h x (List.mem_cons_of_mem _ hx)

/-! ## What one step of asking spends -/

theorem arity_lt_size : ∀ (g : GTerm) (acc : List GTerm),
    (gspine g acc).2.length + 1 ≤ g.size + acc.length
  | .var v, _ => v.elim
  | .sym f, acc => by simp only [gspine, Term.size]; omega
  | .app g u, acc => by
    have h1 := arity_lt_size g (u :: acc)
    have h2 := Sorts.size_pos u
    simp only [gspine, Term.size, List.length_cons] at h1 ⊢
    omega

theorem termKey_lt (t : GTerm) : (termKey t).2 + 1 ≤ t.size := by
  simpa [termKey] using arity_lt_size t []

theorem sumSize_cons (t : GTerm) (G : List GTerm) :
    Sorts.sumSize (t :: G) = t.size + Sorts.sumSize G := by simp [Sorts.sumSize]

theorem kw_cons (κ : Sym × Nat) (ks : List (Sym × Nat)) : kw (κ :: ks) = 5 + 2 * κ.2 + kw ks := by
  simp [kw]

theorem kw_terms_le : ∀ G : List GTerm, kw (G.map termKey) ≤ 7 * Sorts.sumSize G
  | [] => by simp [kw]
  | t :: G => by
    have h1 := kw_terms_le G
    have h2 := termKey_lt t
    rw [List.map_cons, kw_cons, sumSize_cons]
    omega

theorem onlyCost_le (L : Nat) : ∀ G : List GTerm, onlyCost L G ≤ (4 * L + 11) * Sorts.sumSize G + 1
  | [] => by simp [onlyCost]
  | t :: G => by
    have ih := onlyCost_le L G
    have h2 := termKey_lt t
    have h3 : 4 * L + 7 ≤ (4 * L + 7) * t.size := Nat.le_mul_of_pos_right _ (by omega)
    have h4 : (4 * L + 11) * t.size = (4 * L + 7) * t.size + 4 * t.size := by
      have : 4 * L + 11 = 4 * L + 7 + 4 := by omega
      rw [this, Nat.add_mul]
    rw [sumSize_cons, Nat.mul_add, h4]
    simp only [onlyCost]
    omega

theorem projsCost_le (L : Nat) : ∀ G : List GTerm,
    projsCost L G ≤ (13 * L + 15) * Sorts.sumSize G + 1
  | [] => by simp [projsCost]
  | t :: G => by
    have ih := projsCost_le L G
    have h2 := termKey_lt t
    have h3 : 13 * L + 11 ≤ (13 * L + 11) * t.size := Nat.le_mul_of_pos_right _ (by omega)
    have h4 : (13 * L + 15) * t.size = (13 * L + 11) * t.size + 4 * t.size := by
      have : 13 * L + 15 = 13 * L + 11 + 4 := by omega
      rw [this, Nat.add_mul]
    rw [sumSize_cons, Nat.mul_add, h4]
    simp only [projsCost]
    omega

/-- A bound on the ticks `but_key` may spend on a root with `W` arguments at
most and terms of size `N` at most. -/
def keyB (S : Sorts) (u r q N W : Nat) : Nat :=
  stepConjCost S u u W + solesCost S u r W + stepCost S W + ((4 * W + 11) * N + 1) +
    (2 * W + 3 + ((13 * W + 15) * N + 1)) + (W * (inclCost S u q + 8) + 1)

theorem butKeyCost_le (S : Sorts) (u r q : Nat) {k W N : Nat} {G : List GTerm} (hk : k ≤ W)
    (hG : Sorts.sumSize G ≤ N) : butKeyCost S u r q k G ≤ keyB S u r q N W := by
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
  have a5 : projsCost k G ≤ (13 * W + 15) * N + 1 := by
    have b1 := projsCost_le k G
    have b2 : (13 * k + 15) * Sorts.sumSize G ≤ (13 * W + 15) * N := Nat.mul_le_mul (by omega) hG
    omega
  have a6 := Nat.mul_le_mul_right (inclCost S u q + 8) hk
  unfold butKeyCost keyB projsAllCost
  omega

theorem butLoopCost_le (S : Sorts) (u r q : Nat) {W N : Nat} {G : List GTerm}
    (hG : Sorts.sumSize G ≤ N) : ∀ K : List (Sym × Nat), (∀ κ ∈ K, κ.2 ≤ W) →
    butLoopCost S u r q G K ≤ K.length * (keyB S u r q N W + 2) + 1
  | [], _ => by simp [butLoopCost]
  | κ :: K, h => by
    have ih := butLoopCost_le S u r q hG K fun κ' hκ' => h κ' (List.mem_cons_of_mem _ hκ')
    have h1 := butKeyCost_le S u r q (h κ List.mem_cons_self) hG
    simp only [butLoopCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem le_keysCost : ∀ K : List (Sym × Nat), K.length ≤ keysCost K ∧ ∀ κ ∈ K, κ.2 ≤ keysCost K
  | [] => by simp [keysCost]
  | κ :: K => by
    obtain ⟨h1, h2⟩ := le_keysCost K
    refine ⟨by simp only [List.length_cons, keysCost]; omega, fun κ' hκ' => ?_⟩
    rcases List.mem_cons.1 hκ' with rfl | hκ'
    · simp only [keysCost]; omega
    · have := h2 κ' hκ'
      simp only [keysCost]; omega

/-- A bound on the ticks one step of asking may spend, on terms of size `N`
at most. -/
def oneB (S : Sorts) (u r q N : Nat) : Nat :=
  freshCost S u q + butKeysCost S u (7 * N) +
    (butKeysW S u (7 * N) * (keyB S u r q N (butKeysW S u (7 * N)) + 2) + 1)

theorem oneCost_le (S : Sorts) (U : List Name) (r q : Nat) (c : Sorts.Conj) (n : Name)
    {G : List GTerm} {N : Nat} (hG : Sorts.sumSize G ≤ N) :
    oneCost S U r q c n G ≤ oneB S U.length r q N := by
  obtain ⟨hx, hw⟩ := butKeysX_le S (U := U) c n G
  have hgw : kw (G.map termKey) ≤ 7 * N := by
    have := kw_terms_le G
    omega
  have hW : butKeysW S U.length (kw (G.map termKey)) ≤ butKeysW S U.length (7 * N) := by
    unfold butKeysW; omega
  have hKC : butKeysCost S U.length (kw (G.map termKey)) ≤ butKeysCost S U.length (7 * N) := by
    unfold butKeysCost
    have := Nat.mul_le_mul hW (Nat.add_le_add_right hW 5)
    omega
  obtain ⟨hlen, hk⟩ := le_keysCost (butKeysL S (conjList U (· ∈ c)) n G)
  have hloop := butLoopCost_le S U.length r q (W := butKeysW S U.length (7 * N)) hG
    (butKeysL S (conjList U (· ∈ c)) n G) fun κ hκ => by
      have := hk κ hκ
      omega
  have hmul := Nat.mul_le_mul_right
    (keyB S U.length r q N (butKeysW S U.length (7 * N)) + 2)
    (Nat.le_trans hlen (Nat.le_trans hw hW))
  unfold oneCost oneB
  omega

/-! ## The whole -/

/-- The ticks `included_but` may spend on terms of size `N`, where a
conjunction reaches `r` conjunctions at most and a key `q` keys at most: a
polynomial in the size of the sorts, `N`, `r` and `q`. -/
def inclButAll (S : Sorts) (u r q N : Nat) : Nat := inclButCost S u q N (oneB S u r q N)

/-- `included_but` answers whether every member of the conjunction, but for
the ground terms of the list, is in the sort (`Sorts.Hold`), for well-formed
sorts, within `inclButAll` ticks. -/
theorem included_but_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (hS : S.WellFormed) {r q : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (c : Sorts.Conj) (n : Name) (G : List GTerm) (hc : Sub U c) (hn : n ≠ nm none)
    (s : store.Store) (decls names ci ni g : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hni : Repr nm s.nodes.val ni.val (.sym n))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hroom : Room s (inclButAll S U.length r q (Sorts.sumSize G))) :
    sorts.included_but s decls names ci ni g ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + inclButAll S U.length r q (Sorts.sumSize G) ∧
        (b = true ↔ Sorts.Hold S c n G) ⦄ :=
  included_but_run hC hr hq (stepOK hS hC.names) c n G
    (fun c' n' _ h => oneCost_le S U r q c' n' h) hc hn s decls names ci ni g hI hde hU hci hni hg
    hroom

end RwLogVerified
