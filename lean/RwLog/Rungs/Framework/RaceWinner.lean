/-
# Who wins a race

`Cost.race x y` returns the result of one of the two computations, and which
one, and at what cost, depends only on what the two cost. `Cost.firstWins`
and `Cost.raceCost` are that choice and that cost as functions of the two
costs (`Cost.race_eq`). The race costs at least what its winner costs
(`Cost.winner_le_raceCost`) and at most 7 times the cheaper of the two
(`Cost.raceCost_le`).
-/
import RwLog.Rungs.Framework.Race

namespace RwLog

namespace Cost

/-- The race of a computation that costs `tx` against one that costs `ty`:
whether the first one is returned, and what the race costs. -/
def outcome (tx ty : Nat) : Cost Bool := race ⟨true, tx⟩ ⟨false, ty⟩

/-- The race of a computation that costs `tx` against one that costs `ty`
returns the first. -/
def firstWins (tx ty : Nat) : Bool := (outcome tx ty).val

/-- What the race of a computation that costs `tx` against one that costs
`ty` costs. -/
def raceCost (tx ty : Nat) : Nat := (outcome tx ty).ticks

variable {α : Type}

theorem raceFrom_outcome (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    raceFrom x y b =
      ⟨if (raceFrom (⟨true, x.ticks⟩ : Cost Bool) ⟨false, y.ticks⟩ b).val then x.val else y.val,
        (raceFrom (⟨true, x.ticks⟩ : Cost Bool) ⟨false, y.ticks⟩ b).ticks⟩
  | n, b, hn => by
    rw [raceFrom_eq x y b, raceFrom_eq (⟨true, x.ticks⟩ : Cost Bool) ⟨false, y.ticks⟩ b]
    by_cases hx : x.ticks ≤ b
    · simp [hx]
    · by_cases hy : y.ticks ≤ b
      · simp [hx, hy]
      · simp only [hx, hy, ite_false]
        match n, hn with
        | 0, hn => omega
        | n + 1, hn => rw [raceFrom_outcome x y n (2 * b + 1) (by omega)]

/-- A race returns its first computation or its second according to what the
two cost, and costs a function of what the two cost. -/
theorem race_eq (x y : Cost α) :
    race x y = ⟨if firstWins x.ticks y.ticks then x.val else y.val, raceCost x.ticks y.ticks⟩ :=
  raceFrom_outcome x y x.ticks 0 (by omega)

theorem raceCost_le (tx ty : Nat) : raceCost tx ty ≤ 7 * min tx ty :=
  race_ticks (⟨true, tx⟩ : Cost Bool) ⟨false, ty⟩

theorem winner_le_raceFrom (tx ty : Nat) : ∀ (n b : Nat), tx - b ≤ n →
    (if (raceFrom (⟨true, tx⟩ : Cost Bool) ⟨false, ty⟩ b).val then tx else ty) ≤
      (raceFrom (⟨true, tx⟩ : Cost Bool) ⟨false, ty⟩ b).ticks
  | n, b, hn => by
    rw [raceFrom_eq (⟨true, tx⟩ : Cost Bool) ⟨false, ty⟩ b]
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
