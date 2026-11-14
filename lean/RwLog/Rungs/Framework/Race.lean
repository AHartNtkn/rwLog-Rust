/-
# Running two computations side by side

`Cost.race x y` runs `x` and `y` under budgets that double until one of them
finishes, and returns that one's result. It never needs to know in advance
which of the two is the cheap one. The budgets are 0, 1, 3, 7, ...; at each
budget `x` is tried first.

* `race_val`: its result is the result of `x` or of `y`.
* `race_ticks`: it spends at most 7 times what the cheaper of the two needs.
* `le_race_ticks`: it spends at least what the cheaper of the two needs.
* `race_peak_le`, `race_held`: it never has more cells live than the hungrier
  of the two alone, and leaves live what the side it returns leaves live.

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

/-- One budget of the race, spelled out: what it returns. -/
theorem raceFrom_val_eq (x y : Cost α) (b : Nat) :
    (raceFrom x y b).val =
      if x.ticks ≤ b then x.val
      else if y.ticks ≤ b then y.val
      else (raceFrom x y (2 * b + 1)).val := by
  rw [raceFrom]
  by_cases hx : x.ticks ≤ b
  · simp [withinP, within, hx, bind, pure]
  · by_cases hy : y.ticks ≤ b
    · simp [withinP, within, hx, hy, bind, pure]
    · simp [withinP, within, hx, hy, bind]

/-- One budget of the race, spelled out: what it spends. -/
theorem raceFrom_ticks_eq (x y : Cost α) (b : Nat) :
    (raceFrom x y b).ticks =
      if x.ticks ≤ b then x.ticks
      else if y.ticks ≤ b then b + y.ticks
      else b + (b + (raceFrom x y (2 * b + 1)).ticks) := by
  rw [raceFrom]
  by_cases hx : x.ticks ≤ b
  · simp [withinP, within, hx, bind, pure]
  · by_cases hy : y.ticks ≤ b
    · simp [withinP, within, hx, hy, bind, pure]
    · simp [withinP, within, hx, hy, bind]

/-- One budget of the race, spelled out: the cells it leaves live. A side
that was given up on leaves none. -/
theorem raceFrom_held_eq (x y : Cost α) (b : Nat) :
    (raceFrom x y b).held =
      if x.ticks ≤ b then x.held
      else if y.ticks ≤ b then y.held
      else (raceFrom x y (2 * b + 1)).held := by
  rw [raceFrom]
  by_cases hx : x.ticks ≤ b
  · simp [withinP, within, hx, bind, pure]
  · by_cases hy : y.ticks ≤ b
    · simp [withinP, within, hx, hy, bind, pure]
    · simp [withinP, within, hx, hy, bind]

/-- One budget of the race, spelled out: the most cells live at one moment. A
side that was given up on had at most its own peak live and left nothing. -/
theorem raceFrom_peak_eq (x y : Cost α) (b : Nat) :
    (raceFrom x y b).peak =
      if x.ticks ≤ b then x.peak
      else if y.ticks ≤ b then max (min b x.peak) y.peak
      else max (min b x.peak) (max (min b y.peak) (raceFrom x y (2 * b + 1)).peak) := by
  rw [raceFrom]
  by_cases hx : x.ticks ≤ b
  · simp [withinP, within, hx, bind, pure, x.held_le]
  · by_cases hy : y.ticks ≤ b
    · simp [withinP, within, hx, hy, bind, pure, y.held_le]
    · simp [withinP, within, hx, hy, bind]

theorem raceFrom_val (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    (raceFrom x y b).val = x.val ∨ (raceFrom x y b).val = y.val
  | n, b, hn => by
    rw [raceFrom_val_eq]
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
    rw [raceFrom_ticks_eq]
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
    rw [raceFrom_ticks_eq]
    by_cases hx : x.ticks ≤ 0
    · simp only [hx, ite_true]; omega
    · have hy : y.ticks ≤ 0 := by omega
      simp only [hx, hy, ite_true, ite_false]; omega

/-- A race costs at least what the cheaper of the two costs. -/
theorem le_raceFrom_ticks {α : Type} (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    min x.ticks y.ticks ≤ (raceFrom x y b).ticks
  | n, b, hn => by
    rw [raceFrom_ticks_eq]
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

/-! ## What it holds -/

theorem raceFrom_peak_le (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    (raceFrom x y b).peak ≤ max x.peak y.peak
  | n, b, hn => by
    rw [raceFrom_peak_eq]
    by_cases hx : x.ticks ≤ b
    · simp only [hx, ite_true]; exact le_max_left _ _
    · by_cases hy : y.ticks ≤ b
      · simp only [hx, hy, ite_true, ite_false]
        exact max_le_max (min_le_right _ _) le_rfl
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn =>
          have := raceFrom_peak_le x y n (2 * b + 1) (by omega)
          have h₁ : min b x.peak ≤ max x.peak y.peak := (min_le_right _ _).trans (le_max_left _ _)
          have h₂ : min b y.peak ≤ max x.peak y.peak := (min_le_right _ _).trans (le_max_right _ _)
          exact max_le h₁ (max_le h₂ this)

/-- A race never has more cells live than the hungrier of the two alone:
each attempt that is given up on is rolled back. -/
theorem race_peak_le (x y : Cost α) : (race x y).peak ≤ max x.peak y.peak :=
  raceFrom_peak_le x y x.ticks 0 (by omega)

theorem raceFrom_held (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    ((raceFrom x y b).val = x.val ∧ (raceFrom x y b).held = x.held) ∨
      ((raceFrom x y b).val = y.val ∧ (raceFrom x y b).held = y.held)
  | n, b, hn => by
    rw [raceFrom_val_eq, raceFrom_held_eq]
    by_cases hx : x.ticks ≤ b
    · simp [hx]
    · by_cases hy : y.ticks ≤ b
      · simp [hx, hy]
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn => exact raceFrom_held x y n (2 * b + 1) (by omega)

/-- A race leaves live what the side it returns leaves live. -/
theorem race_held (x y : Cost α) :
    ((race x y).val = x.val ∧ (race x y).held = x.held) ∨
      ((race x y).val = y.val ∧ (race x y).held = y.held) :=
  raceFrom_held x y x.ticks 0 (by omega)

/-! ## Which of the two finished -/

theorem raceFrom_cases {α : Type} (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    b ≤ 2 * y.ticks →
    ((raceFrom x y b).val = x.val ∧ x.ticks ≤ 2 * y.ticks) ∨
      ((raceFrom x y b).val = y.val ∧ y.ticks < x.ticks)
  | n, b, hn, hb => by
    rw [raceFrom_val_eq]
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

/-! ## Races of computations that cost the same -/

theorem raceFrom_sim {α β : Type} (x y : Cost α) (x' y' : Cost β) (hx : x'.ticks = x.ticks)
    (hy : y'.ticks = y.ticks) : ∀ (n b : Nat), x.ticks - b ≤ n →
    (raceFrom x' y' b).ticks = (raceFrom x y b).ticks ∧
      (((raceFrom x y b).val = x.val ∧ (raceFrom x' y' b).val = x'.val) ∨
        ((raceFrom x y b).val = y.val ∧ (raceFrom x' y' b).val = y'.val))
  | n, b, hn => by
    rw [raceFrom_val_eq x y, raceFrom_val_eq x' y', raceFrom_ticks_eq x y, raceFrom_ticks_eq x' y',
      hx, hy]
    by_cases h1 : x.ticks ≤ b
    · simp only [h1, ite_true]
      exact ⟨trivial, .inl ⟨trivial, trivial⟩⟩
    · by_cases h2 : y.ticks ≤ b
      · simp only [h1, h2, ite_true, ite_false]
        exact ⟨trivial, .inr ⟨trivial, trivial⟩⟩
      · simp only [h1, h2, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn =>
          obtain ⟨ht, hv⟩ := raceFrom_sim x y x' y' hx hy n (2 * b + 1) (by omega)
          exact ⟨by rw [ht], hv⟩

/-- Two races whose sides cost the same cost the same and are won by the same
side. -/
theorem race_sim {α β : Type} (x y : Cost α) (x' y' : Cost β) (hx : x'.ticks = x.ticks)
    (hy : y'.ticks = y.ticks) :
    (race x' y').ticks = (race x y).ticks ∧
      (((race x y).val = x.val ∧ (race x' y').val = x'.val) ∨
        ((race x y).val = y.val ∧ (race x' y').val = y'.val)) :=
  raceFrom_sim x y x' y' hx hy x.ticks 0 (by omega)

end Cost

end RwLog
