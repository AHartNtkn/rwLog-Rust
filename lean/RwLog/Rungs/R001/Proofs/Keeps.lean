/-
# R001 has every property a rung keeps

`Runtime.Keeps` (`Trusted/Properties.lean`) for R001's runtime, from the
obligations proved one by one.
-/
import RwLog.Rungs.R001.Proofs.Tier0
import RwLog.Rungs.R001.Proofs.Termination
import RwLog.Rungs.R001.Proofs.Symmetry
import RwLog.Rungs.R001.Proofs.SymmetryRound

namespace RwLog

namespace R001

theorem keeps : Obligation.keeps where
  sound := sound
  complete := complete
  pointComplete := Runtime.Complete.pointwise (R := runtime) complete
  honest := honest_exhaustion
  derivationGeneral := derivation_general
  terminates := fun _ _ _ h => h
  orComm := or_comm_trace
  orAssoc := or_assoc
  emptySide := empty_side
  convTrace := conv_trace
  dualTrace := dual_trace
  theoryMono := theory_mono_answers
  noSubsumed := no_subsumed

end R001

end RwLog
