/-
# The mirrored machine in the cost monad

`Mirror.machine C` is `Engine.mirrored` (`Gen.lean`, which says what it does
and why) for any costed machine `C`, in the cost monad: the same text, with
`Cost.race` and `Cost.tick` written out. The proofs are carried out on it.

`go_alone_emit` to `go_catch` say what one round of races does, case by
case, in terms of which of the two steps wins a race (`Cost.firstWins`) and
what the race costs (`Cost.raceCost`).
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

/-- The step from level runs, given what the two races returned. -/
def level {σ : Type} (f : Bool) (x y : σ) : Step σ ⊕ Step σ → Step σ ⊕ Step σ → Step (StOf σ)
  | .inl (.emit as x'), .inl _ => .emit (orient f as) ⟨x', y, f, 1⟩
  | .inr (.emit as y'), .inr _ => .emit (orient (!f) as) ⟨y', x, !f, 1⟩
  | .inl (.emit as x'), .inr (.emit _ y') => .emit (orient f as) ⟨x', y', f, 0⟩
  | .inr (.emit _ y'), .inl (.emit as x') => .emit (orient f as) ⟨x', y', f, 0⟩
  | _, _ => .done

/-- One step of the machine, from a gap of `g`. -/
def go : Nat → Bool → C.State → C.State → Cost (Step (StOf C.State))
  | 0, f, x, y => do
    Cost.tick 1
    let r ← Cost.race (Sum.inl <$> C.step x) (Sum.inr <$> C.step y)
    let r' ← Cost.race (Sum.inr <$> C.step y) (Sum.inl <$> C.step x)
    pure (level f x y r r')
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

/-- The step of `x` wins the race when it is raced before the step of `y`. -/
abbrev wins (x y : C.State) : Bool := firstWins (C.step x).ticks (C.step y).ticks

/-- What the race of the step of `x` before the step of `y` costs. -/
abbrev raced (x y : C.State) : Nat := raceCost (C.step x).ticks (C.step y).ticks

theorem race_steps (x y : C.State) :
    Cost.race (Sum.inl <$> C.step x) (Sum.inr <$> C.step y) =
      ⟨if wins x y then .inl (C.step x).val else .inr (C.step y).val, raced x y⟩ := by
  rw [Cost.race_eq]; rfl

theorem race_steps' (x y : C.State) :
    Cost.race (Sum.inr <$> C.step y) (Sum.inl <$> C.step x) =
      ⟨if wins y x then .inr (C.step y).val else .inl (C.step x).val, raced y x⟩ := by
  rw [Cost.race_eq]; rfl

/-! ### Level runs -/

/-- The step from level runs: the two races, and what they returned. -/
theorem go_zero (f : Bool) (x y : C.State) :
    go C 0 f x y =
      ⟨level f x y (if wins x y then .inl (C.step x).val else .inr (C.step y).val)
          (if wins y x then .inr (C.step y).val else .inl (C.step x).val),
        1 + raced x y + raced y x⟩ := by
  unfold go
  refine Cost.ext ?_ ?_
  · simp only [bind_val, race_steps, race_steps', pure_val]
  · simp only [bind_ticks, race_steps, race_steps', pure_ticks, tick_ticks, Nat.add_zero]
    omega

/-- The leader's step wins both races: it takes its step alone. -/
theorem go_alone_emit {x y x' : C.State} {as : List Span} (f : Bool)
    (h1 : wins x y = true) (h2 : wins y x = false) (hx : (C.step x).val = .emit as x') :
    go C 0 f x y = ⟨.emit (orient f as) ⟨x', y, f, 1⟩, 1 + raced x y + raced y x⟩ := by
  rw [go_zero]; simp [h1, h2, hx, level]

theorem go_alone_done {x y : C.State} (f : Bool)
    (h1 : wins x y = true) (h2 : wins y x = false) (hx : (C.step x).val = .done) :
    go C 0 f x y = ⟨.done, 1 + raced x y + raced y x⟩ := by
  rw [go_zero]; simp [h1, h2, hx, level]

/-- The other run's step wins both races: it takes its step alone and becomes
the leader. -/
theorem go_overtake {x y y' : C.State} {as : List Span} (f : Bool)
    (h1 : wins x y = false) (h2 : wins y x = true) (hy : (C.step y).val = .emit as y') :
    go C 0 f x y = ⟨.emit (orient (!f) as) ⟨y', x, !f, 1⟩, 1 + raced x y + raced y x⟩ := by
  rw [go_zero]; simp [h1, h2, hy, level]

theorem go_overtake_done {x y : C.State} (f : Bool)
    (h1 : wins x y = false) (h2 : wins y x = true) (hy : (C.step y).val = .done) :
    go C 0 f x y = ⟨.done, 1 + raced x y + raced y x⟩ := by
  rw [go_zero]; simp [h1, h2, hy, level]

/-- Neither run wins both races: both take their step, and stay level. -/
theorem go_both_emit {x y x' y' : C.State} {as bs : List Span} (f : Bool)
    (h : wins x y = wins y x) (hx : (C.step x).val = .emit as x')
    (hy : (C.step y).val = .emit bs y') :
    go C 0 f x y = ⟨.emit (orient f as) ⟨x', y', f, 0⟩, 1 + raced x y + raced y x⟩ := by
  rw [go_zero, ← h]; cases wins x y <;> simp [hx, hy, level]

theorem go_both_done {x y : C.State} (f : Bool)
    (h : wins x y = wins y x) (hd : (C.step x).val = .done ∨ (C.step y).val = .done) :
    go C 0 f x y = ⟨.done, 1 + raced x y + raced y x⟩ := by
  rw [go_zero, ← h]
  rcases hd with hd | hd
  · cases wins x y <;> cases hy : (C.step y).val <;> simp [hd, level]
  · cases wins x y <;> cases hx : (C.step x).val <;> simp [hd, level]

/-! ### One run behind -/

theorem go_lead_emit {x y x' : C.State} {as : List Span} (g : Nat) (f : Bool)
    (hw : wins x y = true) (hx : (C.step x).val = .emit as x') :
    go C (g + 1) f x y = ⟨.emit (orient f as) ⟨x', y, f, g + 2⟩, 1 + raced x y⟩ := by
  unfold go
  refine Cost.ext ?_ ?_
  · simp only [bind_val, race_steps, hw, ite_true, hx, pure_val]
  · simp only [bind_ticks, race_steps, hw, ite_true, hx, pure_ticks, tick_ticks,
      Nat.add_zero]

theorem go_lead_done {x y : C.State} (g : Nat) (f : Bool)
    (hw : wins x y = true) (hx : (C.step x).val = .done) :
    go C (g + 1) f x y = ⟨.done, 1 + raced x y⟩ := by
  unfold go
  refine Cost.ext ?_ ?_
  · simp only [bind_val, race_steps, hw, ite_true, hx, pure_val]
  · simp only [bind_ticks, race_steps, hw, ite_true, hx, pure_ticks, tick_ticks,
      Nat.add_zero]

theorem go_lag_done {x y : C.State} (g : Nat) (f : Bool)
    (hw : wins x y = false) (hy : (C.step y).val = .done) :
    go C (g + 1) f x y = ⟨.done, 1 + raced x y⟩ := by
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
