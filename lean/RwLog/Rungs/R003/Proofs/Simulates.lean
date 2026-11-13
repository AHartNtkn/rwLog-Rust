/-
# R003 simulates R002 within a factor of 7

Both machines are the tabled round machine with their own oracle. R003's
oracle returns R002's answer, possibly without the spans that repeat an
earlier one (`unfolder_exact`), so the two machines go through the same states
(`Tabled.step_val_of_skips`), and everything a round does after the oracle has
answered costs R003 no more than it costs R002 (`Tabled.rest_skips`). One call
of R003's oracle costs at most 7 times the walk (`unfolder_ticks`), so a step
of R003 costs at most 7 times the same step of R002, and so does a run
(`Tabled.spent_le_of_skips`).

As in `Proofs/SameMachine.lean`, the exactness of the shared evaluation is a
hypothesis.
-/
import RwLog.Rungs.R003.Proofs.SameMachine
import RwLog.Rungs.R002.Proofs.Same
import RwLog.Rungs.Framework.Latency

namespace RwLog

namespace R003

/-- R003's unfolder gives the walk's verdict, and the walk's answers with some
repeats left out. -/
theorem unfolder_skips_of (h : Obligation.shared_exact) :
    Oracle.SkipsRepeats unfolder R002.onDemand :=
  Oracle.ExactModRepeats.skips (unfolder_exact_of h) R002.onDemand_exact

/-- One call of R003's unfolder costs at most 7 times the walk. -/
theorem unfolder_ticks_le (P : Program) (d : Nat) (g : R001.Goal) :
    (unfolder P d g).ticks ≤ 7 * (R002.onDemand P d g).ticks :=
  Nat.le_trans (unfolder_ticks P d g) (Nat.mul_le_mul_left 7 (Nat.min_le_left _ _))

/-- What R003 has spent after any number of steps, against what R002 has. -/
theorem spent_le_of (h : Obligation.shared_exact) (n : Nat) (st : R001.State) :
    costed.spent st n ≤ 7 * R002.costed.spent st n :=
  Tabled.spent_le_of_skips (unfolder_skips_of h) (by omega) unfolder_ticks_le n st

/-- R003 simulates R002 within a factor of 7, given that the shared
evaluation is exact. -/
theorem simulates_of (h : Obligation.shared_exact) : Obligation.simulates := by
  refine Simulates.of_steps ?_
  intro P q _ n
  have hc : costed.runtime = R001.runtime := runtime_eq_of h
  have hb : R002.costed.runtime = R001.runtime := R002.runtime_eq
  have hp : costed.paid P q n = costed.spent (R001.State.ofGoal P ⟨none, q, none⟩) n :=
    Tabled.paid_eq unfolder P q n
  have hp' : R002.costed.paid P q n = R002.costed.spent (R001.State.ofGoal P ⟨none, q, none⟩) n :=
    Tabled.paid_eq R002.onDemand P q n
  refine ⟨n, by rw [hp, hp']; exact spent_le_of h n _, ?_, ?_⟩
  · show ∀ a ∈ R002.costed.runtime.emitted (R002.costed.runtime.init P q) n,
      ∃ b ∈ costed.runtime.emitted (costed.runtime.init P q) n, b.CoversLive P.theory a
    rw [hc, hb]
    exact fun a ha => ⟨a, ha, Span.CoversLive.refl _ a⟩
  · show R002.costed.runtime.Halts (R002.costed.runtime.init P q) n →
      costed.runtime.Halts (costed.runtime.init P q) n
    rw [hc, hb]
    exact id

end R003

end RwLog
