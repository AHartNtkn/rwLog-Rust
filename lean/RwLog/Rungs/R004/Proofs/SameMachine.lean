/-
# R004 is the same machine as R001, within 7 times R003's cost

R004's unfolder returns the answer of R003's unfolder or of the evaluation
pruned from the right (`Cost.race_val`). The first gives R001's verdict and
R001's answers with or without the repeats (`R003.unfolder_exact`), and the
second gives them without the repeats (`pruned_exact`), so R004's unfolder
does too (`unfolder_exact`). The tabled machine does the same with either
(`Tabled.machine_runtime_modRepeats`), so R004's runtime is R001's, and
`sound`, `complete` and `honest_exhaustion` are R001's theorems rewritten
along that equality.

Whatever R004's unfolder returns is R003's answer with some repeats left out
(`unfolder_skips`), so everything a round does after the oracle has answered
costs R004 no more than it costs R003 (`Tabled.spent_le_of_skips`). One call
of R004's unfolder costs at most 7 times R003's (`unfolder_ticks`), and so
does a run (`simulates`).
-/
import RwLog.Rungs.Framework.Latency
import RwLog.Rungs.R004.Proofs.PrunedExact
import RwLog.Rungs.R003.Proofs.Same

namespace RwLog

namespace R004

/-! ## The race -/

theorem unfolder_ticks : Obligation.unfolder_ticks := fun P d g =>
  Cost.race_ticks (R003.unfolder P d g) (pruned P d g)

/-- One call of R004's unfolder costs at most 7 times R003's. -/
theorem unfolder_ticks_le (P : Program) (d : Nat) (g : R001.Goal) :
    (unfolder P d g).ticks ≤ 7 * (R003.unfolder P d g).ticks :=
  Nat.le_trans (unfolder_ticks P d g) (Nat.mul_le_mul_left 7 (Nat.min_le_left _ _))

/-- One call of R004's unfolder costs at most 7 times the evaluation pruned
from the right. -/
theorem unfolder_ticks_le_pruned (P : Program) (d : Nat) (g : R001.Goal) :
    (unfolder P d g).ticks ≤ 7 * (pruned P d g).ticks :=
  Nat.le_trans (unfolder_ticks P d g) (Nat.mul_le_mul_left 7 (Nat.min_le_right _ _))

/-! ## Same machine -/

theorem unfolder_exact : Obligation.unfolder_exact := by
  intro P d g
  rcases Cost.race_val (R003.unfolder P d g) (pruned P d g) with e | e
  · have hv : (unfolder P d g).val = (R003.unfolder P d g).val := e
    rw [hv]
    exact R003.unfolder_exact P d g
  · have : (unfolder P d g).val =
        (R001.unfoldFinal P d g, (R001.unfoldAnswers P d g).eraseDups) :=
      e.trans (pruned_exact P d g)
    rw [this]
    exact ⟨rfl, .inr rfl⟩

theorem runtime_eq : Obligation.runtime_eq :=
  Tabled.machine_runtime_modRepeats unfolder unfolder_exact

theorem sound : Obligation.sound := by
  unfold Obligation.sound
  rw [runtime_eq]
  exact R001.sound

theorem complete : Obligation.complete := by
  unfold Obligation.complete
  rw [runtime_eq]
  exact R001.complete

theorem honest_exhaustion : Obligation.honest_exhaustion := by
  unfold Obligation.honest_exhaustion
  rw [runtime_eq]
  exact R001.honest_exhaustion

/-! ## Never much worse -/

/-- R004's unfolder gives R003's verdict, and R003's answers with some repeats
left out. -/
theorem unfolder_skips : Oracle.SkipsRepeats unfolder R003.unfolder := by
  intro P d g
  rcases Cost.race_val (R003.unfolder P d g) (pruned P d g) with e | e
  · have hv : (unfolder P d g).val = (R003.unfolder P d g).val := e
    rw [hv]
    exact ⟨rfl, Thins.refl _ _⟩
  · have hv : (unfolder P d g).val =
        (R001.unfoldFinal P d g, (R001.unfoldAnswers P d g).eraseDups) :=
      e.trans (pruned_exact P d g)
    obtain ⟨h1, h2⟩ := R003.unfolder_exact P d g
    rw [hv, h1]
    refine ⟨rfl, ?_⟩
    rcases h2 with h | h <;> rw [h]
    · exact Thins.eraseDups _
    · exact Thins.refl _ _

/-- What R004 has spent after any number of steps, against what R003 has. -/
theorem spent_le (n : Nat) (st : R001.State) :
    costed.spent st n ≤ 7 * R003.costed.spent st n :=
  Tabled.spent_le_of_skips unfolder_skips (by omega) unfolder_ticks_le n st

theorem simulates : Obligation.simulates := by
  refine Simulates.of_steps fun P q _ n => ?_
  have hc : costed.runtime = R001.runtime := runtime_eq
  have hb : R003.costed.runtime = R001.runtime := R003.runtime_eq
  refine ⟨n, spent_le n _, ?_, ?_⟩
  · show ∀ a ∈ R003.costed.runtime.emitted (R003.costed.runtime.init P q) n,
      ∃ b ∈ costed.runtime.emitted (costed.runtime.init P q) n, b.CoversLive P.theory a
    rw [hc, hb]
    exact fun a ha => ⟨a, ha, Span.CoversLive.refl _ a⟩
  · show R003.costed.runtime.Halts (R003.costed.runtime.init P q) n →
      costed.runtime.Halts (costed.runtime.init P q) n
    rw [hc, hb]
    exact id

end R004

end RwLog
