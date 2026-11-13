/-
# Rung R002: the unfolding race on demand

R002 is R001's tabled round machine with one part computed differently: the
unfolding race every goal runs each round (`Unfold.lean`). R001 builds the
goal's unfolding to the current depth and normalizes all of it, every round,
for every incomplete table. R002 walks the same products on demand, stops at
the first one that shows the unfolding is not final, and never enters a part
that the spans around it already rule out.

Both machines are the costed machine of `Tabled.lean` with their own oracle,
so they are charged alike for everything else:

* `baseline` is R001 with its cost: forgetting the ticks gives `R001.runtime`
  (obligation `baseline_exact`);
* `costed` is R002, and `runtime` is `costed` with the ticks forgotten.

The two oracles return the same answer (obligation `onDemand_exact`), so
R002 takes the very same steps as R001, and every property proved of R001
holds of R002 as it stands. What changes is the cost.
-/
import RwLog.Rungs.R002.Unfold

namespace RwLog

namespace R002

/-- R001 with its cost. -/
def baseline : CostedRuntime := Tabled.machine eager

/-- R002 with its cost. -/
def costed : CostedRuntime := Tabled.machine onDemand

def runtime : Runtime := costed.runtime

/-- Rung R002: no preprocessing, an empty artifact store, and the tabled
round machine with the unfolding race on demand. -/
def rung : Rung where
  pre := Preprocessor.id
  rt := runtime

end R002

end RwLog
