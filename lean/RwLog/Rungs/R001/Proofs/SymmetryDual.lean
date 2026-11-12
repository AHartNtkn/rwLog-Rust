/-
# Rung R001, Symmetry: the mirrored run

`dual_trace` for every well-formed theory: simplification keeps coverage
(`simplify_mono`), so it respects equivalent spans, which is all the mirrored
run needs (`Symmetry.dual_trace_of_mono`).
-/
import RwLog.Rungs.R001.Proofs.SymmetryRound
import RwLog.Rungs.R001.Proofs.SimplifyMono

namespace RwLog

namespace R001

/-- **P1.4 strong, for the mirrored program.** -/
theorem dual_trace : Obligation.dual_trace := Symmetry.dual_trace_of_mono simplify_mono

end R001

end RwLog
