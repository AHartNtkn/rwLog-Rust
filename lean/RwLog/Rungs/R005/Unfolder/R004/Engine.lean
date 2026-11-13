/-
# Rung R004: the unfolding race, pruned from the right as well

R004 is R003 (and so R001) with one more way of answering the unfolding race.
`pruned` (`Pruned.lean`) goes through the unfolded goal from the right, so a
test at the right end of a goal rules derivations out before what stands to
its left is enumerated, and then replays the derivations that are left from
the left, so that it returns the very spans R001's race returns.

`pruned` is not always the cheapest, so R004 races it against R003's
unfolder, which is itself the race of R002's walk and R003's shared
evaluation: each call costs at most 7 times the cheaper of `pruned` and
R003's unfolder.

The answers are the same up to spans that repeat an earlier one, which the
tabled machine drops in any case, so R004 takes the very same steps as R001
(obligation `runtime_eq`) and keeps every property proved of it.
-/
import RwLog.Rungs.R005.Unfolder.R004.Pruned

namespace RwLog

namespace R004

/-- R004's unfolding race: R003's unfolder and the evaluation pruned from the
right, side by side. -/
def unfolder : Oracle := fun P d g => Cost.race (R003.unfolder P d g) (pruned P d g)

/-- R004 with its cost. -/
def costed : CostedRuntime := Tabled.machine unfolder

def runtime : Runtime := costed.runtime

/-- Rung R004: no preprocessing, an empty artifact store, and the tabled
round machine with the unfolding race answered by the cheapest of the walk,
the shared evaluation and the evaluation pruned from the right. -/
def rung : Rung where
  pre := Preprocessor.id
  rt := runtime

end R004

end RwLog
