/-
# R002 is R001's machine: the obligations, unconditionally

`Proofs/SameMachine.lean` derives each "same machine" obligation from the
exactness of one unfolder, and `Proofs/Eager.lean` and `Proofs/OnDemand.lean`
prove both exact.
-/
import RwLog.Rungs.R002.Proofs.SameMachine
import RwLog.Rungs.R002.Proofs.Eager
import RwLog.Rungs.R002.Proofs.OnDemand

namespace RwLog

namespace R002

theorem baseline_exact : Obligation.baseline_exact := baseline_exact_of eager_exact
theorem runtime_eq : Obligation.runtime_eq := runtime_eq_of onDemand_exact
theorem sound : Obligation.sound := sound_of onDemand_exact
theorem complete : Obligation.complete := complete_of onDemand_exact
theorem honest_exhaustion : Obligation.honest_exhaustion := honest_exhaustion_of onDemand_exact

end R002

end RwLog
