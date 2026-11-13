/-
# The key of a node in the trie

`alloc` finds a node by a key: a list of digits below seventeen. A number is
written in base sixteen, the most significant digit first, and ended by the
digit sixteen, so no number's key is the start of another's and keys can be
written one after the other. Different nodes have different keys.
-/
import Aeneas

namespace RwLogVerified

/-- The digits of `x` in base sixteen, the most significant first. Zero has
no digits. -/
def digits (x : Nat) : List Nat :=
  if _ : x = 0 then [] else digits (x / 16) ++ [x % 16]
decreasing_by omega

theorem digits_zero : digits 0 = [] := by rw [digits]; simp

theorem digits_pos {x : Nat} (h : x ≠ 0) : digits x = digits (x / 16) ++ [x % 16] := by
  rw [digits]; simp [h]

theorem digits_lt (x : Nat) : ∀ d ∈ digits x, d < 16 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases h : x = 0
    · subst h; simp [digits_zero]
    · rw [digits_pos h]
      intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact ih (x / 16) (by omega) d hd
      · simp only [List.mem_singleton] at hd; omega

/-- The number a list of digits writes. -/
def ofDigits (ds : List Nat) : Nat := ds.foldl (fun acc d => acc * 16 + d) 0

theorem ofDigits_append (ds : List Nat) (d : Nat) : ofDigits (ds ++ [d]) = ofDigits ds * 16 + d := by
  simp [ofDigits, List.foldl_append]

theorem ofDigits_digits (x : Nat) : ofDigits (digits x) = x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases h : x = 0
    · subst h; simp [digits_zero, ofDigits]
    · rw [digits_pos h, ofDigits_append, ih (x / 16) (by omega)]; omega

theorem digits_inj {x y : Nat} (h : digits x = digits y) : x = y := by
  rw [← ofDigits_digits x, ← ofDigits_digits y, h]

theorem digits_length_le (k x : Nat) (h : x < 16 ^ k) : (digits x).length ≤ k := by
  induction k generalizing x with
  | zero =>
    have : x = 0 := by simpa using h
    subst this; simp [digits_zero]
  | succ k ih =>
    by_cases hx : x = 0
    · subst hx; simp [digits_zero]
    · rw [digits_pos hx, List.length_append, List.length_singleton]
      have := ih (x / 16) (by rw [pow_succ] at h; omega)
      omega

/-- The key of a number: its digits and the end mark. -/
def wd (x : Nat) : List Nat := digits x ++ [16]

theorem wd_lt (x : Nat) : ∀ d ∈ wd x, d < 17 := by
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · have := digits_lt x d hd; omega
  · simp only [List.mem_singleton] at hd; omega

theorem append_mark_inj {m : Nat} {l₁ l₂ r₁ r₂ : List Nat} (h₁ : m ∉ l₁) (h₂ : m ∉ l₂)
    (h : l₁ ++ m :: r₁ = l₂ ++ m :: r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simpa using h
    | cons b l₂ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (by intro e; exact h₂ (by simp [e]))
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm (by intro e; exact h₁ (by simp [e]))
    | cons b l₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨e, r⟩ := ih (fun hm => h₁ (List.mem_cons_of_mem _ hm))
        (fun hm => h₂ (List.mem_cons_of_mem _ hm)) h.2
      exact ⟨by rw [h.1, e], r⟩

/-- Keys of numbers can be written one after the other. -/
theorem wd_append_inj {x y : Nat} {r₁ r₂ : List Nat} (h : wd x ++ r₁ = wd y ++ r₂) :
    x = y ∧ r₁ = r₂ := by
  simp only [wd, List.append_assoc, List.singleton_append] at h
  have hx : 16 ∉ digits x := fun hm => by have := digits_lt x 16 hm; omega
  have hy : 16 ∉ digits y := fun hm => by have := digits_lt y 16 hm; omega
  obtain ⟨e, r⟩ := append_mark_inj hx hy h
  exact ⟨digits_inj e, r⟩

theorem wd_length_le (k x : Nat) (h : x < 16 ^ k) : (wd x).length ≤ k + 1 := by
  simp only [wd, List.length_append, List.length_singleton]
  have := digits_length_le k x h
  omega

end RwLogVerified
