/-
# A greatest fixpoint on finite sets of indices

`gfpFrom ok n S` shrinks `S` to its largest subset closed under `ok`, used by
engines to decide which pieces of work have finished together.
-/
import Mathlib.Data.List.Basic
import Mathlib.Order.Nat

namespace RwLog

/-- Shrink `S` to the largest subset closed under `ok`. Each pass that changes
`S` removes a member, so `S.length` passes reach the fixpoint. -/
def gfpFrom (ok : List Nat → Nat → Bool) : Nat → List Nat → List Nat
  | 0, S => S
  | n + 1, S =>
    let S' := S.filter (ok S)
    if S'.length = S.length then S else gfpFrom ok n S'

/-- `gfpFrom` returns a subset closed under `ok`, given enough passes. -/
theorem gfpFrom_closed (ok : List Nat → Nat → Bool) :
    ∀ (n : Nat) (S : List Nat), S.length ≤ n →
      ∀ i ∈ gfpFrom ok n S, i ∈ S ∧ ok (gfpFrom ok n S) i = true
  | 0, S, hS, i, hi => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hS)] at hi; simp [gfpFrom] at hi
  | n + 1, S, hS, i, hi => by
    unfold gfpFrom at hi ⊢
    simp only at hi ⊢
    split
    · rename_i heq
      simp only [heq, ↓reduceIte] at hi
      refine ⟨hi, ?_⟩
      have := List.length_filter_eq_length_iff.1 heq i hi
      exact this
    · rename_i hne
      simp only [hne, ↓reduceIte] at hi
      have hlt : (S.filter (ok S)).length < S.length :=
        lt_of_le_of_ne (List.length_filter_le _ _) hne
      obtain ⟨h1, h2⟩ := gfpFrom_closed ok n _ (by omega) i hi
      exact ⟨(List.mem_filter.1 h1).1, h2⟩

/-- `ok` only grows with its set argument. -/
def OkMono (ok : List Nat → Nat → Bool) : Prop :=
  ∀ S S' : List Nat, (∀ j ∈ S, j ∈ S') → ∀ i, ok S i = true → ok S' i = true

/-- Every set inside `S` that is closed under `ok` survives the shrinking. -/
theorem subset_gfpFrom {ok : List Nat → Nat → Bool} (hm : OkMono ok) (X : List Nat)
    (hX : ∀ i ∈ X, ok X i = true) : ∀ n S, (∀ i ∈ X, i ∈ S) → ∀ i ∈ X, i ∈ gfpFrom ok n S
  | 0, S, hS => hS
  | n + 1, S, hS => by
    have hS' : ∀ i ∈ X, i ∈ S.filter (ok S) := fun i hi =>
      List.mem_filter.2 ⟨hS i hi, hm X S hS i (hX i hi)⟩
    simp only [gfpFrom]
    split
    · exact hS
    · exact subset_gfpFrom hm X hX n _ hS'

theorem gfpFrom_sub (ok : List Nat → Nat → Bool) : ∀ n S, ∀ i ∈ gfpFrom ok n S, i ∈ S
  | 0, _ => fun _ h => h
  | n + 1, S => by
    simp only [gfpFrom]
    split
    · exact fun _ h => h
    · exact fun i hi => (List.mem_filter.1 (gfpFrom_sub ok n _ i hi)).1


end RwLog
