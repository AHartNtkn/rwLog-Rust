/-
# R003: the race obligations

`Rungs/Framework/Race.lean` proves what `Cost.race` returns and what it
spends, for any two computations. The obligations of `Spec.lean` about the
race, and the bound on R003's own unfolder, are instances.
-/
import RwLog.Rungs.Framework.Race
import RwLog.Rungs.R003.Spec

namespace RwLog

namespace R003

theorem race_val : Obligation.race_val := fun _ x y => Cost.race_val x y

theorem race_ticks : Obligation.race_ticks := fun _ x y => Cost.race_ticks x y

theorem unfolder_ticks : Obligation.unfolder_ticks := fun P d g =>
  Cost.race_ticks (R002.onDemand P d g) (shared P d g)

end R003

end RwLog
