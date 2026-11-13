/-
# List facts with no rwLog content
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card

namespace RwLog

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  cases l with
  | nil => simp
  | cons a as =>
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨by simp, ih _ ?_ _ rfl⟩
    have := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons] at h
    omega

theorem length_eraseDups {α : Type} [DecidableEq α] (l : List α) :
    l.eraseDups.length = l.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (nodup_eraseDups l)]
  congr 1; ext; simp

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun x => (x, f x)
  | [] => rfl
  | x :: l => by simp [zip_map_self f l]

theorem map_zip_map_self {α β γ : Type} (f : α → β) (h : α × β → γ) (l : List α) :
    (l.zip (l.map f)).map h = l.map fun a => h (a, f a) := by
  rw [zip_map_self, List.map_map]; rfl

/-! ## Sums of natural numbers over lists -/

theorem sum_flatMap_map {α β : Type} (f : α → List β) (g : β → Nat) (xs : List α) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]

/-- A sum over a `filterMap` is a sum over the list, with dropped members
counting zero. -/
theorem sum_filterMap_map {α β : Type} (f : α → Option β) (g : β → Nat) (xs : List α) :
    ((xs.filterMap f).map g).sum = (xs.map fun x => (f x).elim 0 g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons]
    cases h : f x with
    | none => simp only [ih, List.map_cons, List.sum_cons, h, Option.elim_none, Nat.zero_add]
    | some y => simp only [ih, List.map_cons, List.sum_cons, h, Option.elim_some]

theorem le_sum_map_of_mem {α : Type} (f : α → Nat) {xs : List α} {x : α} (h : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => cases h
  | cons y xs ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

theorem sum_map_le {α : Type} {f g : α → Nat} {xs : List α} (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons y xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem sum_map_add' {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons y xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul_left' {α : Type} (a : Nat) (f : α → Nat) (xs : List α) :
    (xs.map fun x => a * f x).sum = a * (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons y xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_mul_right' {α : Type} (a : Nat) (f : α → Nat) (xs : List α) :
    (xs.map fun x => f x * a).sum = (xs.map f).sum * a := by
  induction xs with
  | nil => simp
  | cons y xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

end RwLog
