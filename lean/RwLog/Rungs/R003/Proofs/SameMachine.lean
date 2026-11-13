/-
# R003 is the same machine as R001

R003's unfolder returns the answer of the walk or of the shared evaluation
(`race_val`). The walk computes R001's unfolding race (`R002.onDemand_exact`)
and the shared evaluation computes it with the repeated answers removed
(obligation `shared_exact`), so the unfolder gives R001's verdict and R001's
answers with or without the repeats (`unfolder_exact`). The tabled machine
does the same with either (`Tabled.machine_runtime_modRepeats`), so R003's
runtime is R001's, and `sound`, `complete` and `honest_exhaustion` are R001's
theorems rewritten along that equality.

`shared_exact` is proved elsewhere, so each theorem here takes it as a
hypothesis: every obligation of this file is one application, e.g.
`runtime_eq_of shared_exact`.
-/
import RwLog.Rungs.Tabled.Repeats
import RwLog.Rungs.R003.Proofs.Race
import RwLog.Rungs.R002.Proofs.OnDemand
import RwLog.Rungs.R001.Proofs.Tier0

namespace RwLog

namespace R003

/-- R003's unfolder gives R001's verdict and R001's answers, with or without
the repeats, given that the shared evaluation does. -/
theorem unfolder_exact_of (h : Obligation.shared_exact) : Obligation.unfolder_exact := by
  intro P d g
  rcases Cost.race_val (R002.onDemand P d g) (shared P d g) with e | e
  · have : (unfolder P d g).val = (R001.unfoldFinal P d g, R001.unfoldAnswers P d g) :=
      e.trans (R002.onDemand_exact P d g)
    rw [this]
    exact ⟨rfl, .inl rfl⟩
  · have : (unfolder P d g).val =
        (R001.unfoldFinal P d g, (R001.unfoldAnswers P d g).eraseDups) := e.trans (h P d g)
    rw [this]
    exact ⟨rfl, .inr rfl⟩

/-- R003's runtime is R001's, given that the shared evaluation is exact. -/
theorem runtime_eq_of (h : Obligation.shared_exact) : Obligation.runtime_eq :=
  Tabled.machine_runtime_modRepeats unfolder (unfolder_exact_of h)

theorem sound_of (h : Obligation.shared_exact) : Obligation.sound := by
  unfold Obligation.sound
  rw [runtime_eq_of h]
  exact R001.sound

theorem complete_of (h : Obligation.shared_exact) : Obligation.complete := by
  unfold Obligation.complete
  rw [runtime_eq_of h]
  exact R001.complete

theorem honest_exhaustion_of (h : Obligation.shared_exact) : Obligation.honest_exhaustion := by
  unfold Obligation.honest_exhaustion
  rw [runtime_eq_of h]
  exact R001.honest_exhaustion

end R003

end RwLog
