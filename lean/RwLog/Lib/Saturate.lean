/-
# Saturating a finite set

`saturate U f` iterates a function that only adds elements of `U`, as many
times as `U` has elements. The result is closed under `f`, and it is the
least such set.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate

namespace RwLog

variable {α : Type} [DecidableEq α]

/-- `f` iterated `U.card` times from the empty set, each round keeping what
was there and staying inside `U`. -/
def saturate (U : Finset α) (f : Finset α → Finset α) : Finset α :=
  (fun s => s ∪ (f s ∩ U))^[U.card] ∅

namespace saturate

variable (U : Finset α) (f : Finset α → Finset α)

private def round (s : Finset α) : Finset α := s ∪ (f s ∩ U)

private theorem iter_subset (i : Nat) : (round U f)^[i] ∅ ⊆ U := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact Finset.union_subset ih Finset.inter_subset_right

private theorem iter_mono (i : Nat) : (round U f)^[i] ∅ ⊆ (round U f)^[i + 1] ∅ := by
  rw [Function.iterate_succ_apply']
  exact Finset.subset_union_left

private theorem iter_stable {i : Nat} (h : (round U f)^[i + 1] ∅ = (round U f)^[i] ∅) (j : Nat) :
    (round U f)^[i + j] ∅ = (round U f)^[i] ∅ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih, ← Function.iterate_succ_apply' (round U f), h]

private theorem iter_card (i : Nat) :
    i ≤ ((round U f)^[i] ∅).card ∨ ∃ k < i, (round U f)^[k + 1] ∅ = (round U f)^[k] ∅ := by
  induction i with
  | zero => left; simp
  | succ i ih =>
    rcases ih with h | ⟨k, hk, he⟩
    · by_cases he : (round U f)^[i + 1] ∅ = (round U f)^[i] ∅
      · exact Or.inr ⟨i, Nat.lt_succ_self i, he⟩
      · left
        have hss : (round U f)^[i] ∅ ⊂ (round U f)^[i + 1] ∅ :=
          Finset.ssubset_iff_subset_ne.mpr ⟨iter_mono U f i, fun e => he e.symm⟩
        have := Finset.card_lt_card hss
        omega
    · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, he⟩

/-- The saturation is closed: a round adds nothing. -/
theorem closed : f (saturate U f) ∩ U ⊆ saturate U f := by
  have key : (round U f)^[U.card + 1] ∅ = (round U f)^[U.card] ∅ := by
    rcases iter_card U f U.card with h | ⟨k, hk, he⟩
    · have hsub := iter_subset U f U.card
      have heq : (round U f)^[U.card] ∅ = U := Finset.eq_of_subset_of_card_le hsub h
      apply Finset.Subset.antisymm
      · rw [heq]; exact iter_subset U f _
      · exact iter_mono U f _
    · have h1 := iter_stable U f he (U.card - k)
      have h2 := iter_stable U f he (U.card + 1 - k)
      have e1 : k + (U.card - k) = U.card := by omega
      have e2 : k + (U.card + 1 - k) = U.card + 1 := by omega
      rw [e1] at h1; rw [e2] at h2
      rw [h1, h2]
  intro x hx
  have : x ∈ (round U f)^[U.card + 1] ∅ := by
    rw [Function.iterate_succ_apply']
    exact Finset.mem_union_right _ hx
  rw [key] at this
  exact this

theorem subset : saturate U f ⊆ U := iter_subset U f _

/-- Anything true of everything a round adds is true of the saturation. -/
theorem induction {p : α → Prop}
    (step : ∀ s : Finset α, (∀ x ∈ s, p x) → ∀ x ∈ f s ∩ U, p x) :
    ∀ x ∈ saturate U f, p x := by
  have : ∀ i, ∀ x ∈ (round U f)^[i] ∅, p x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      rcases Finset.mem_union.mp hx with h | h
      · exact ih x h
      · exact step _ ih x h
  exact this _

/-- A chain that starts empty and grows by rounds reaches the saturation. -/
theorem chain (g : Nat → Finset α) (h0 : g 0 = ∅)
    (hstep : ∀ n, g (n + 1) = g n ∪ (f (g n) ∩ U)) : g U.card = saturate U f := by
  have : ∀ n, g n = (round U f)^[n] ∅ := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [Function.iterate_succ_apply', ← ih, hstep]; rfl
  exact this _

end saturate

end RwLog
