/-
# Running two computations side by side

`Cost.race x y` runs `x` and `y` under budgets that double until one of them
finishes, and returns that one's result. It never needs to know in advance
which of the two is the cheap one. The budgets are 0, 1, 3, 7, ...; at each
budget `x` is tried first.

* `race_val`: its result is the result of `x` or of `y`.
* `race_ticks`: it spends at most 7 times what the cheaper of the two needs.
* `le_race_ticks`: it spends at least what the cheaper of the two needs.

Let `m` be the smaller of the two costs. A budget `b < m` fails twice and
costs `2 b`; the first budget `b ≥ m` costs at most `b + m`. The budgets
double, so the failed ones add up to less than twice the last, and the last
is below `2 m`: in all less than `3 (2 m) + m`.
-/
import RwLog.Trusted.Cost

namespace RwLog

namespace Cost

/-! ## What it returns and what it spends -/

variable {α : Type}

/-- One budget of the race, spelled out. -/
theorem raceFrom_eq (x y : Cost α) (b : Nat) :
    raceFrom x y b =
      if x.ticks ≤ b then ⟨x.val, x.ticks⟩
      else if y.ticks ≤ b then ⟨y.val, b + y.ticks⟩
      else ⟨(raceFrom x y (2 * b + 1)).val, b + (b + (raceFrom x y (2 * b + 1)).ticks)⟩ := by
  rw [raceFrom]
  by_cases hx : x.ticks ≤ b
  · simp [withinP, within, hx, bind, pure]
  · by_cases hy : y.ticks ≤ b
    · simp [withinP, within, hx, hy, bind, pure]
    · simp [withinP, within, hx, hy, bind]

theorem raceFrom_val (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    (raceFrom x y b).val = x.val ∨ (raceFrom x y b).val = y.val
  | n, b, hn => by
    rw [raceFrom_eq]
    by_cases hx : x.ticks ≤ b
    · simp [hx]
    · by_cases hy : y.ticks ≤ b
      · simp [hx, hy]
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn => exact raceFrom_val x y n (2 * b + 1) (by omega)

/-- From a budget below twice the cheaper cost `m`, the race spends at most
`7 m - 2 b - 3`. -/
theorem raceFrom_ticks (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    b + 1 ≤ 2 * min x.ticks y.ticks →
    (raceFrom x y b).ticks + 2 * b + 3 ≤ 7 * min x.ticks y.ticks
  | n, b, hn, hb => by
    rw [raceFrom_eq]
    by_cases hx : x.ticks ≤ b
    · simp only [hx, ite_true]; omega
    · by_cases hy : y.ticks ≤ b
      · simp only [hx, hy, ite_true, ite_false]; omega
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn =>
          have := raceFrom_ticks x y n (2 * b + 1) (by omega) (by omega)
          omega

/-- The race returns the result of one of the two. -/
theorem race_val (x y : Cost α) : (race x y).val = x.val ∨ (race x y).val = y.val :=
  raceFrom_val x y x.ticks 0 (by omega)

/-- The race spends at most 7 times what the cheaper of the two needs. -/
theorem race_ticks (x y : Cost α) : (race x y).ticks ≤ 7 * min x.ticks y.ticks := by
  by_cases h : 1 ≤ 2 * min x.ticks y.ticks
  · have := raceFrom_ticks x y x.ticks 0 (by omega) (by omega)
    unfold race
    omega
  · unfold race
    rw [raceFrom_eq]
    by_cases hx : x.ticks ≤ 0
    · simp only [hx, ite_true]; omega
    · have hy : y.ticks ≤ 0 := by omega
      simp only [hx, hy, ite_true, ite_false]; omega

/-- A race costs at least what the cheaper of the two costs. -/
theorem le_raceFrom_ticks {α : Type} (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    min x.ticks y.ticks ≤ (raceFrom x y b).ticks
  | n, b, hn => by
    rw [raceFrom_eq]
    by_cases hx : x.ticks ≤ b
    · simp only [hx, ite_true]; omega
    · by_cases hy : y.ticks ≤ b
      · simp only [hx, hy, ite_true, ite_false]; omega
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn =>
          have := le_raceFrom_ticks x y n (2 * b + 1) (by omega)
          omega

theorem le_race_ticks {α : Type} (x y : Cost α) : min x.ticks y.ticks ≤ (race x y).ticks :=
  le_raceFrom_ticks x y x.ticks 0 (by omega)

/-! ## Which of the two finished -/

theorem raceFrom_cases {α : Type} (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    b ≤ 2 * y.ticks →
    ((raceFrom x y b).val = x.val ∧ x.ticks ≤ 2 * y.ticks) ∨
      ((raceFrom x y b).val = y.val ∧ y.ticks < x.ticks)
  | n, b, hn, hb => by
    rw [raceFrom_eq]
    by_cases hx : x.ticks ≤ b
    · exact .inl ⟨by simp only [hx, ite_true], by omega⟩
    · by_cases hy : y.ticks ≤ b
      · exact .inr ⟨by simp only [hx, hy, ite_true, ite_false], by omega⟩
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn => exact raceFrom_cases x y n (2 * b + 1) (by omega) (by omega)

/-- The race returns the result of the first when the first needs at most
twice what the second needs, and otherwise the result of the second, which
then needs less than the first. -/
theorem race_cases {α : Type} (x y : Cost α) :
    ((race x y).val = x.val ∧ x.ticks ≤ 2 * y.ticks) ∨
      ((race x y).val = y.val ∧ y.ticks < x.ticks) :=
  raceFrom_cases x y x.ticks 0 (by omega) (by omega)

end Cost

end RwLog
