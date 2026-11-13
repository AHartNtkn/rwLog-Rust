/-
# R003 is R001's machine, within 7 times R002's cost: the obligations, unconditionally

`Proofs/SameMachine.lean` and `Proofs/Simulates.lean` derive each obligation
from the exactness of the shared evaluation, and `Proofs/SharedExact.lean`
proves it exact.
-/
import RwLog.Rungs.R003.Proofs.Simulates
import RwLog.Rungs.R003.Proofs.SharedExact

namespace RwLog

namespace R003

theorem unfolder_exact : Obligation.unfolder_exact := unfolder_exact_of shared_exact
theorem runtime_eq : Obligation.runtime_eq := runtime_eq_of shared_exact
theorem sound : Obligation.sound := sound_of shared_exact
theorem complete : Obligation.complete := complete_of shared_exact
theorem honest_exhaustion : Obligation.honest_exhaustion := honest_exhaustion_of shared_exact
theorem simulates : Obligation.simulates := simulates_of shared_exact

end R003

end RwLog
