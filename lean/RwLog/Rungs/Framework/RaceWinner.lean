/-
# Who wins a race

`Cost.race x y` returns the result of one of the two computations, and which
one, and at what cost, depends only on what the two cost. `Cost.firstWins`
and `Cost.raceCost` are that choice and that cost as functions of the two
costs (`Cost.race_val_eq`, `Cost.race_ticks_eq`). The race costs at least what its winner costs
(`Cost.winner_le_raceCost`) and at most 7 times the cheaper of the two
(`Cost.raceCost_le`).
-/
import RwLog.Rungs.Framework.Race

namespace RwLog

namespace Cost

/-- A computation that returns `v` in `t` ticks and allocates nothing. -/
def costing {α : Type} (v : α) (t : Nat) : Cost α := ⟨v, t, 0, 0, Nat.le_refl _⟩

theorem costing_ticks {α : Type} (v : α) (t : Nat) : (costing v t).ticks = t := rfl
theorem costing_val {α : Type} (v : α) (t : Nat) : (costing v t).val = v := rfl

/-- The race of a computation that costs `tx` against one that costs `ty`:
whether the first one is returned, and what the race costs. -/
def outcome (tx ty : Nat) : Cost Bool := race (costing true tx) (costing false ty)

/-- The race of a computation that costs `tx` against one that costs `ty`
returns the first. -/
def firstWins (tx ty : Nat) : Bool := (outcome tx ty).val

/-- What the race of a computation that costs `tx` against one that costs
`ty` costs. -/
def raceCost (tx ty : Nat) : Nat := (outcome tx ty).ticks

variable {α : Type}

theorem raceFrom_outcome (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    (raceFrom x y b).val =
        (if (raceFrom (costing true x.ticks) (costing false y.ticks) b).val then x.val
          else y.val) ∧
      (raceFrom x y b).ticks = (raceFrom (costing true x.ticks) (costing false y.ticks) b).ticks
  | n, b, hn => by
    rw [raceFrom_val_eq x y b, raceFrom_ticks_eq x y b,
      raceFrom_val_eq (costing true x.ticks) (costing false y.ticks) b,
      raceFrom_ticks_eq (costing true x.ticks) (costing false y.ticks) b]
    simp only [costing_ticks, costing_val]
    by_cases hx : x.ticks ≤ b
    · simp [hx]
    · by_cases hy : y.ticks ≤ b
      · simp [hx, hy]
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn =>
          obtain ⟨h₁, h₂⟩ := raceFrom_outcome x y n (2 * b + 1) (by omega)
          exact ⟨h₁, by rw [h₂]⟩

/-- A race returns its first computation or its second according to what the
two cost. -/
theorem race_val_eq (x y : Cost α) :
    (race x y).val = if firstWins x.ticks y.ticks then x.val else y.val :=
  (raceFrom_outcome x y x.ticks 0 (by omega)).1

/-- A race costs a function of what the two cost. -/
theorem race_ticks_eq (x y : Cost α) : (race x y).ticks = raceCost x.ticks y.ticks :=
  (raceFrom_outcome x y x.ticks 0 (by omega)).2

theorem raceCost_le (tx ty : Nat) : raceCost tx ty ≤ 7 * min tx ty :=
  race_ticks (costing true tx) (costing false ty)

theorem winner_le_raceFrom (tx ty : Nat) : ∀ (n b : Nat), tx - b ≤ n →
    (if (raceFrom (costing true tx) (costing false ty) b).val then tx else ty) ≤
      (raceFrom (costing true tx) (costing false ty) b).ticks
  | n, b, hn => by
    rw [raceFrom_val_eq (costing true tx) (costing false ty) b,
      raceFrom_ticks_eq (costing true tx) (costing false ty) b]
    simp only [costing_ticks, costing_val]
    by_cases hx : tx ≤ b
    · simp [hx]
    · by_cases hy : ty ≤ b
      · simp [hx, hy]
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn =>
          have := winner_le_raceFrom tx ty n (2 * b + 1) (by omega)
          omega

/-- A race costs at least what its winner costs. -/
theorem winner_le_raceCost (tx ty : Nat) :
    (if firstWins tx ty then tx else ty) ≤ raceCost tx ty :=
  winner_le_raceFrom tx ty tx 0 (by omega)

end Cost

end RwLog
