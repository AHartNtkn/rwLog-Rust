/-
# Exact coverage: the simplification laws hold for every well-formed theory

`SimpLaws` is `simplify_mono` together with the fact that simplification
commutes with converse.
-/
import RwLog.Rungs.R001.Proofs.Exact.Basic
import RwLog.Rungs.R001.Proofs.SimplifyMono
import RwLog.Rungs.R001.Proofs.SymmetryCands

namespace RwLog

namespace R001

namespace Exact

theorem simpLaws_of_wf {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) : SimpLaws T where
  mono := (simplify_mono T hwf).1
  compR s t := ((simplify_mono T hwf).2 s t).1
  compL s t := ((simplify_mono T hwf).2 s t).2.1
  meetR s t := ((simplify_mono T hwf).2 s t).2.2.1
  meetL s t := ((simplify_mono T hwf).2 s t).2.2.2
  swap := Symmetry.simplify_swap T

end Exact

end R001

end RwLog
