/-
# The mirrored machine in the cost monad

`Mirror.machine C` is `Engine.mirrored` (`Gen.lean`, which says what it does
and why) for any costed machine `C`, in the cost monad: the same text, with
`Cost.race` and `Cost.tick` written out. The proofs are carried out on it.

`go_lead_emit` to `go_catch` say what one race does, case by case, in terms
of which of the two steps wins (`Cost.firstWins`) and what the race costs
(`Cost.raceCost`).
-/
import RwLog.Rungs.Mirror.Gen
import RwLog.Rungs.Framework.RaceWinner
import RwLog.Rungs.Framework.Cost

namespace RwLog

namespace Mirror

open Cost

/-- The answers of a run, as answers to the query: those of the run on the
mirror image are swapped back. -/
def orient (fwd : Bool) (as : List Span) : List Span := if fwd then as else as.map Span.swap

variable (C : CostedRuntime)

/-- One step of the machine, from a gap of `g`. -/
def go : Nat → Bool → C.State → C.State → Cost (Step (StOf C.State))
  | 0, f, x, y => do
    Cost.tick 1
    let r ← Cost.race (Sum.inl <$> C.step x) (Sum.inr <$> C.step y)
    match r with
    | .inl (.emit as x') => pure (.emit (orient f as) ⟨x', y, f, 1⟩)
    | .inl .done => pure .done
    | .inr (.emit as y') => pure (.emit (orient (!f) as) ⟨y', x, !f, 1⟩)
    | .inr .done => pure .done
  | g + 1, f, x, y => do
    Cost.tick 1
    let r ← Cost.race (Sum.inl <$> C.step x) (Sum.inr <$> C.step y)
    match r with
    | .inl (.emit as x') => pure (.emit (orient f as) ⟨x', y, f, g + 2⟩)
    | .inl .done => pure .done
    | .inr (.emit _ y') => go g f x y'
    | .inr .done => pure .done

/-- `C` run on the query and on its mirror image, side by side. -/
def machine : CostedRuntime where
  State := StOf C.State
  init P q := do
    let x ← C.init P q
    let y ← C.init P.dual q.dual
    pure ⟨x, y, true, 0⟩
  step st := go C st.gap st.fwd st.lead st.lag

/-! ## One race, case by case -/

variable {C}

/-- The leader's step wins the race against the other run's. -/
abbrev wins (x y : C.State) : Bool := firstWins (C.step x).ticks (C.step y).ticks

/-- What the race of the two next steps costs. -/
abbrev raced (x y : C.State) : Nat := raceCost (C.step x).ticks (C.step y).ticks

theorem race_steps (x y : C.State) :
    Cost.race (Sum.inl <$> C.step x) (Sum.inr <$> C.step y) =
      ⟨if wins x y then .inl (C.step x).val else .inr (C.step y).val, raced x y⟩ := by
  rw [Cost.race_eq]; rfl

theorem go_lead_emit {x y x' : C.State} {as : List Span} (g : Nat) (f : Bool)
    (hw : wins x y = true) (hx : (C.step x).val = .emit as x') :
    go C g f x y = ⟨.emit (orient f as) ⟨x', y, f, g + 1⟩, 1 + raced x y⟩ := by
  cases g <;>
  · unfold go
    refine Cost.ext ?_ ?_
    · simp only [bind_val, race_steps, hw, ite_true, hx, pure_val]
    · simp only [bind_ticks, race_steps, hw, ite_true, hx, pure_ticks, tick_ticks,
        Nat.add_zero]

theorem go_lead_done {x y : C.State} (g : Nat) (f : Bool)
    (hw : wins x y = true) (hx : (C.step x).val = .done) :
    go C g f x y = ⟨.done, 1 + raced x y⟩ := by
  cases g <;>
  · unfold go
    refine Cost.ext ?_ ?_
    · simp only [bind_val, race_steps, hw, ite_true, hx, pure_val]
    · simp only [bind_ticks, race_steps, hw, ite_true, hx, pure_ticks, tick_ticks,
        Nat.add_zero]

theorem go_lag_done {x y : C.State} (g : Nat) (f : Bool)
    (hw : wins x y = false) (hy : (C.step y).val = .done) :
    go C g f x y = ⟨.done, 1 + raced x y⟩ := by
  cases g <;>
  · unfold go
    refine Cost.ext ?_ ?_
    · simp only [bind_val, race_steps, hw, hy, pure_val, Bool.false_eq_true, ite_false]
    · simp only [bind_ticks, race_steps, hw, hy, pure_ticks, tick_ticks,
        Nat.add_zero, Bool.false_eq_true, ite_false]

/-- The other run was level with the leader and its step wins: it becomes the
leader. -/
theorem go_overtake {x y y' : C.State} {as : List Span} (f : Bool)
    (hw : wins x y = false) (hy : (C.step y).val = .emit as y') :
    go C 0 f x y = ⟨.emit (orient (!f) as) ⟨y', x, !f, 1⟩, 1 + raced x y⟩ := by
  unfold go
  refine Cost.ext ?_ ?_
  · simp only [bind_val, race_steps, hw, hy, pure_val, Bool.false_eq_true, ite_false]
  · simp only [bind_ticks, race_steps, hw, hy, pure_ticks, tick_ticks,
      Nat.add_zero, Bool.false_eq_true, ite_false]

/-- The other run was behind and its step wins: it is one step closer, and
the machine races again. -/
theorem go_catch {x y y' : C.State} {as : List Span} (g : Nat) (f : Bool)
    (hw : wins x y = false) (hy : (C.step y).val = .emit as y') :
    go C (g + 1) f x y = ⟨(go C g f x y').val, 1 + raced x y + (go C g f x y').ticks⟩ := by
  rw [go]
  refine Cost.ext ?_ ?_
  · simp only [bind_val, race_steps, hw, hy, Bool.false_eq_true, ite_false]
  · simp only [bind_ticks, race_steps, hw, hy, tick_ticks, Bool.false_eq_true,
      ite_false]
    omega

end Mirror

end RwLog
