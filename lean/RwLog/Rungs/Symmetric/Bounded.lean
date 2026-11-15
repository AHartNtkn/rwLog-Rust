/-
# A turn is a bounded piece of work

What a turn of a strategy costs (`turn`, `Machine.lean`): at most the ticks
it was given and one unit of work more (`turn_ticks`). A turn stops at the
first unit that finds it with nothing left, so only its last unit can go
beyond what it was given; and what it reports as spent, from which the
strategy's debt is made, leaves out at most one unit that did nothing
(`turn_counted`).
-/
import RwLog.Rungs.Symmetric.Invariant

namespace RwLog

namespace Symmetric

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  {K : Kernel R Cost} {hK : K.Refines D}

/-- A turn with nothing left costs nothing. -/
theorem turn_ticks_zero (i : Nat) (g : GoalOf R Rel) (f : Nat) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (c : Nat) :
    (turn (K := DerivationKernel.over D K hK P) i g f 0 st s c).ticks = 0 := by
  at_cost K hK
  cases f <;> simp [turn]

/-- **A turn costs at most what it was given and one unit more**, `U` being
the most a unit of work of the goal costs. -/
theorem turn_ticks (i : Nat) (g : GoalOf R Rel) (U : Nat)
    (hU : ∀ st s, (work (K := DerivationKernel.over D K hK P) i g st s).ticks ≤ U) :
    ∀ (f left : Nat) (st : StateOf R Rel (Ans D P)) (s : Strat Rel (Ans D P)) (c : Nat),
      (turn (K := DerivationKernel.over D K hK P) i g f left st s c).ticks ≤ left + U + 1
  | 0, _, _, _, _ => by
    at_cost K hK
    simp [turn]
  | f + 1, left, st, s, c => by
    have ih := turn_ticks i g U hU f
    have h1 := hU st s
    have hz := fun st' s' c' => turn_ticks_zero (K := K) (hK := hK) (P := P) i g f st' s' c'
    at_cost K hK
    by_cases hl : left = 0
    · simp [turn, hl]
    · simp only [turn, hl, ↓reduceIte, Cost.bind_ticks, Kernel.metered, Cost.metered_ticks,
        Cost.metered_val]
      generalize work (K := _) i g st s = w at h1 ⊢
      by_cases hd : w.val.2.2 = true
      · simp only [hd, ↓reduceIte, Cost.bind_ticks, Kernel.tick, Cost.tick_ticks]
        have h2 := ih (left - (w.ticks + 1)) w.val.1 w.val.2.1 (c + w.ticks + 1)
        by_cases hle : w.ticks + 1 ≤ left
        · omega
        · have h0 : left - (w.ticks + 1) = 0 := by omega
          rw [h0, hz]
          omega
      · simp only [hd, Bool.false_eq_true, ↓reduceIte, Cost.pure_ticks]
        omega

end Symmetric

end RwLog
