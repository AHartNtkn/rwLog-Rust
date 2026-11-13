/-
# Rung R003: the unfolding race with shared work

R003 is R002 (and so R001) with one more way of answering the unfolding race.
`shared` (`Shared.lean`) keeps one copy of each span and evaluates a
sub-expression once for each interface it is reached with, where R002's walk
(`R002.onDemand`) goes through every product. `shared` is not always the
cheaper of the two, because the walk stops at the first product that still
contains a call, so R003 runs both under doubling budgets and takes the answer
of whichever finishes first (`Cost.race`): each race costs at most 7 times
what the cheaper of the two would have cost alone.

The two answers are the same up to spans that repeat an earlier one, which
the tabled machine drops in any case, so R003 takes the very same steps as
R001 (obligation `runtime_eq`) and keeps every property proved of it.
-/
import RwLog.Rungs.R003.Race
import RwLog.Rungs.R003.Shared

namespace RwLog

namespace R003

/-- R003's unfolding race: the walk and the shared evaluation, side by side. -/
def unfolder : Oracle := fun P d g => Cost.race (R002.onDemand P d g) (shared P d g)

/-- R003 with its cost. -/
def costed : CostedRuntime := Tabled.machine unfolder

def runtime : Runtime := costed.runtime

/-- Rung R003: no preprocessing, an empty artifact store, and the tabled
round machine with the unfolding race answered by the cheaper of the walk and
the shared evaluation. -/
def rung : Rung where
  pre := Preprocessor.id
  rt := runtime

end R003

end RwLog
