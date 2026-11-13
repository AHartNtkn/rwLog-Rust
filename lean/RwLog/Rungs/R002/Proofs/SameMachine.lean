/-
# R002 is the same machine as R001

The "same machine" obligations of `Spec.lean` that do not concern the
unfolders themselves. Both `baseline` and `costed` are the charged tabled
machine of `Tabled.lean` with an oracle, and `Tabled.machine_runtime`
(`Proofs/Machine.lean`) says that machine is `R001.runtime` whenever the oracle
computes R001's unfolding race. So:

* `baseline_exact` follows from `eager_exact`;
* `runtime_eq` follows from `onDemand_exact`;
* `sound`, `complete` and `honest_exhaustion` are R001's theorems rewritten
  along `runtime_eq`.

`eager_exact` and `onDemand_exact` are proved elsewhere, so each theorem here
takes the one it needs as a hypothesis. With them in hand, every obligation of
this file is one application, e.g. `baseline_exact_of eager_exact`.
-/
import RwLog.Rungs.Tabled.Exact
import RwLog.Rungs.R002.Spec
import RwLog.Rungs.R001.Proofs.Tier0

namespace RwLog

namespace R002

/-- The costed baseline is R001, given that the eager unfolder is exact. -/
theorem baseline_exact_of (h : Obligation.eager_exact) : Obligation.baseline_exact :=
  Tabled.machine_runtime eager h

/-- R002's runtime is R001's, given that the on-demand unfolder is exact. -/
theorem runtime_eq_of (h : Obligation.onDemand_exact) : Obligation.runtime_eq :=
  Tabled.machine_runtime onDemand h

theorem sound_of (h : Obligation.onDemand_exact) : Obligation.sound := by
  unfold Obligation.sound
  rw [runtime_eq_of h]
  exact R001.sound

theorem complete_of (h : Obligation.onDemand_exact) : Obligation.complete := by
  unfold Obligation.complete
  rw [runtime_eq_of h]
  exact R001.complete

theorem honest_exhaustion_of (h : Obligation.onDemand_exact) : Obligation.honest_exhaustion := by
  unfold Obligation.honest_exhaustion
  rw [runtime_eq_of h]
  exact R001.honest_exhaustion

end R002

end RwLog
