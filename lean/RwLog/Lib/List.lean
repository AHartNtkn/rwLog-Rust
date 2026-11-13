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

end RwLog
