/-
# The maximal members of a list under a decided preorder

`cov y x` says that `y` covers `x`. `List.tops` keeps the members no other
member strictly covers, `List.thin` keeps a member unless one kept before it
covers it, and `List.maximaBy` is one after the other: one member of each
class of maximal members. Nothing here mentions an rwlog type.
-/
import Mathlib.Data.List.Basic

namespace List

variable {α : Type} (cov : α → α → Bool)

/-- The members that no member strictly covers. -/
def tops (xs : List α) : List α := xs.filter fun x => !xs.any fun y => cov y x && !cov x y

/-- Each member unless one kept before it covers it. -/
def thin (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.any (fun y => cov y x) then acc else acc ++ [x]) []

/-- One member of each class of maximal members. -/
def maximaBy (xs : List α) : List α := thin cov (tops cov xs)

variable {cov}

theorem mem_thinFold (xs : List α) : ∀ {acc : List α} {y : α}, y ∈ acc →
    y ∈ xs.foldl (fun acc x => if acc.any (fun y => cov y x) then acc else acc ++ [x]) acc := by
  induction xs with
  | nil => intro acc y h; exact h
  | cons a xs ih =>
    intro acc y h
    rw [List.foldl_cons]
    split
    · exact ih h
    · exact ih (List.mem_append_left _ h)

theorem thin_spec (xs : List α) : ∀ acc : List α,
    acc.Pairwise (fun y x => cov y x = false) →
    (∀ x ∈ xs.foldl (fun acc x => if acc.any (fun y => cov y x) then acc else acc ++ [x]) acc,
        x ∈ acc ∨ x ∈ xs) ∧
      (xs.foldl (fun acc x => if acc.any (fun y => cov y x) then acc else acc ++ [x]) acc).Pairwise
        (fun y x => cov y x = false) ∧
      (∀ x, x ∈ acc ∨ x ∈ xs → (∀ a, cov a a = true) →
        ∃ z ∈ xs.foldl (fun acc x => if acc.any (fun y => cov y x) then acc else acc ++ [x]) acc,
          cov z x = true) := by
  induction xs with
  | nil =>
    intro acc h
    refine ⟨fun x hx => .inl hx, h, fun x hx hr => ?_⟩
    rcases hx with hx | hx
    · exact ⟨x, hx, hr x⟩
    · cases hx
  | cons a xs ih =>
    intro acc h
    rw [List.foldl_cons]
    by_cases hc : acc.any (fun y => cov y a) = true
    · simp only [hc, ↓reduceIte]
      obtain ⟨h₁, h₂, h₃⟩ := ih acc h
      refine ⟨fun x hx => (h₁ x hx).imp id (List.mem_cons_of_mem _), h₂, fun x hx hr => ?_⟩
      rcases hx with hx | hx
      · exact h₃ x (.inl hx) hr
      · rcases List.mem_cons.1 hx with rfl | hx
        · obtain ⟨y, hy, hya⟩ := List.any_eq_true.1 hc
          exact ⟨y, mem_thinFold xs hy, hya⟩
        · exact h₃ x (.inr hx) hr
    · simp only [hc]
      have hacc : (acc ++ [a]).Pairwise (fun y x => cov y x = false) := by
        rw [List.pairwise_append]
        refine ⟨h, List.pairwise_singleton _ _, fun u hu v hv => ?_⟩
        rw [List.mem_singleton] at hv; subst hv
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hc
        exact hc u hu
      obtain ⟨h₁, h₂, h₃⟩ := ih (acc ++ [a]) hacc
      refine ⟨fun x hx => ?_, h₂, fun x hx hr => ?_⟩
      · rcases h₁ x hx with hx | hx
        · rcases List.mem_append.1 hx with hx | hx
          · exact .inl hx
          · exact .inr (by rw [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self)
        · exact .inr (List.mem_cons_of_mem _ hx)
      · refine h₃ x ?_ hr
        rcases hx with hx | hx
        · exact .inl (List.mem_append_left _ hx)
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact .inl (List.mem_append_right _ (List.mem_singleton.2 rfl))
          · exact .inr hx

theorem mem_thin {xs : List α} {x : α} (h : x ∈ thin cov xs) : x ∈ xs := by
  rcases (thin_spec xs [] List.Pairwise.nil).1 x h with h | h
  · cases h
  · exact h

theorem thin_pairwise (xs : List α) : (thin cov xs).Pairwise fun y x => cov y x = false :=
  (thin_spec xs [] List.Pairwise.nil).2.1

theorem thin_covers (hr : ∀ a, cov a a = true) {xs : List α} {x : α} (h : x ∈ xs) :
    ∃ z ∈ thin cov xs, cov z x = true :=
  (thin_spec xs [] List.Pairwise.nil).2.2 x (.inr h) hr

theorem mem_tops {xs : List α} {x : α} :
    x ∈ tops cov xs ↔ x ∈ xs ∧ ∀ y ∈ xs, cov y x = true → cov x y = true := by
  simp only [tops, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
    Bool.and_eq_true, not_and, Bool.not_eq_false]

theorem countP_succ_le {p q : α → Bool} : ∀ {l : List α} {y : α},
    (∀ z ∈ l, p z = true → q z = true) → y ∈ l → q y = true → p y = false →
    l.countP p + 1 ≤ l.countP q
  | [], _, _, hy, _, _ => by cases hy
  | a :: l, y, hpq, hy, hq, hp => by
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [List.countP_cons_of_neg (by simp [hp]), List.countP_cons_of_pos hq]
      exact Nat.succ_le_succ (List.countP_mono_left fun z hz => hpq z (List.mem_cons_of_mem _ hz))
    · have ih := countP_succ_le (fun z hz => hpq z (List.mem_cons_of_mem _ hz)) hy hq hp
      by_cases hpa : p a = true
      · rw [List.countP_cons_of_pos hpa, List.countP_cons_of_pos (hpq a List.mem_cons_self hpa)]
        omega
      · rw [List.countP_cons_of_neg hpa]
        by_cases hqa : q a = true
        · rw [List.countP_cons_of_pos hqa]; omega
        · rw [List.countP_cons_of_neg hqa]; exact ih

/-- Every member is covered by a member that no member strictly covers. -/
theorem tops_covers (hr : ∀ a, cov a a = true)
    (ht : ∀ a b c, cov a b = true → cov b c = true → cov a c = true) (xs : List α) :
    ∀ (n : Nat) (x : α), x ∈ xs → xs.countP (fun y => cov y x && !cov x y) ≤ n →
      ∃ z ∈ tops cov xs, cov z x = true
  | n, x, hx, hn => by
    by_cases htop : x ∈ tops cov xs
    · exact ⟨x, htop, hr x⟩
    · rw [mem_tops] at htop
      simp only [hx, true_and, not_forall] at htop
      obtain ⟨y, hy, hyx, hxy⟩ := htop
      have hxy' : cov x y = false := by simpa using hxy
      have hlt : xs.countP (fun z => cov z y && !cov y z) + 1 ≤
          xs.countP (fun z => cov z x && !cov x z) := by
        refine countP_succ_le (y := y) (fun z _ hz => ?_) hy (by simp [hyx, hxy']) (by simp [hr y])
        simp only [Bool.and_eq_true, Bool.not_eq_true', ] at hz ⊢
        refine ⟨ht _ _ _ hz.1 hyx, ?_⟩
        cases hxz : cov x z with
        | false => rfl
        | true => rw [ht _ _ _ hyx hxz] at hz; exact absurd hz.2 (by simp)
      match n, hn with
      | 0, hn => omega
      | n + 1, hn =>
        obtain ⟨z, hz, hzy⟩ := tops_covers hr ht xs n y hy (by omega)
        exact ⟨z, hz, ht _ _ _ hzy hyx⟩

theorem mem_maximaBy {xs : List α} {x : α} (h : x ∈ maximaBy cov xs) : x ∈ xs :=
  (mem_tops.1 (mem_thin h)).1

/-- No kept member covers another. -/
theorem maximaBy_pairwise (xs : List α) :
    (maximaBy cov xs).Pairwise fun y x => cov y x = false ∧ cov x y = false := by
  have h := thin_pairwise (cov := cov) (tops cov xs)
  have hm : ∀ x ∈ maximaBy cov xs, x ∈ tops cov xs := fun x hx => mem_thin hx
  unfold maximaBy at hm ⊢
  refine (List.Pairwise.and_mem.1 h).imp ?_
  rintro y x ⟨hy, hx, hyx⟩
  refine ⟨hyx, ?_⟩
  cases hxy : cov x y with
  | false => rfl
  | true =>
    have := (mem_tops.1 (hm y hy)).2 x (mem_tops.1 (hm x hx)).1 hxy
    rw [hyx] at this; cases this

/-- Every member is covered by a kept one. -/
theorem maximaBy_covers (hr : ∀ a, cov a a = true)
    (ht : ∀ a b c, cov a b = true → cov b c = true → cov a c = true) {xs : List α} {x : α}
    (h : x ∈ xs) : ∃ z ∈ maximaBy cov xs, cov z x = true := by
  obtain ⟨t, htop, htx⟩ := tops_covers hr ht xs _ x h (Nat.le_refl _)
  obtain ⟨z, hz, hzt⟩ := thin_covers hr htop
  exact ⟨z, hz, ht _ _ _ hzt htx⟩

end List
