/-
# Running two computations side by side

`Cost.race x y` runs `x` and `y` under budgets that double until one of them
finishes, and returns that one's result. It never needs to know in advance
which of the two is the cheap one: whatever it spends is within a constant
factor of the cheaper (obligation `race_ticks`, factor 7).

The budgets are 0, 1, 3, 7, ...; at each budget `x` is tried first.
-/
import RwLog.Trusted.Cost

namespace RwLog

namespace Cost

/-- `within`, keeping the fact that a computation that was given up on needed
more than the budget. The value and the ticks are those of `within`. -/
def withinP {α : Type} (b : Nat) (m : Cost α) :
    Cost { o : Option α // o = none → b < m.ticks } :=
  ⟨⟨(within b m).val, by
    unfold within
    split
    · intro h; cases h
    · intro _; omega⟩, (within b m).ticks⟩

/-- Run `x` and `y` under the budget `b`, then `2 b + 1`, and so on, until one
of them finishes. -/
def raceFrom {α : Type} (x y : Cost α) (b : Nat) : Cost α := do
  let r ← withinP b x
  match r with
  | ⟨some v, _⟩ => pure v
  | ⟨none, h⟩ => do
    have _ : b < x.ticks := h rfl
    let r' ← within b y
    match r' with
    | some v => pure v
    | none => raceFrom x y (2 * b + 1)
termination_by x.ticks - b
decreasing_by omega

/-- Run `x` and `y` side by side until one of them finishes. -/
def race {α : Type} (x y : Cost α) : Cost α := raceFrom x y 0

end Cost

end RwLog
