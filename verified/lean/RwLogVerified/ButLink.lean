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

end RwLogVerified
