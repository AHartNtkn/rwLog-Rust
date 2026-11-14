/-
# R005, the yardstick

R005 is the top rung of epoch 1 (`lean/EPOCH1.md`), written once against the
derivation kernel. The next engine is measured against it.

It is three things put together.

* The tabled round machine (`Rungs/Tabled/Machine.lean`): a table for every
  goal, the join and the two push strategies for every split of a chain or a
  meet, completion by the largest set of tables that can no longer grow.
* The unfolding race every table asks once a round
  (`Rungs/Tabled/Unfold.lean`): the walk from the left, the shared evaluation
  and the walk from the right, side by side.
* The mirror (`Rungs/Mirror/Machine.lean`): that machine on the root node and
  on its converse, side by side, so what a query costs does not depend on the
  end it was written from.

`R001.engine` is the tabled machine with the unfolding race answered by
building the whole unfolding. It is the base R005 is compared with: where it
halts, R005 halts.

Each is an `Engine`, so each is a machine with its cost at every kernel of
every constraint domain (`Engine.costedAt`), and at every one of them it is
sound and no less general than a derivation
(`Rungs/Framework/Derivation.lean`).
-/
import RwLog.Rungs.Tabled.Unfold
import RwLog.Rungs.Mirror.Machine

namespace RwLog

/-- The tabled machine with the unfolding race answered by building the whole
unfolding: the proper baseline. -/
def R001.engine : Engine := Tabled.engine Tabled.Unfold.eagerRace

/-- The tabled machine with the three evaluations of the unfolding raced. -/
def R004.engine : Engine := Tabled.engine Tabled.Unfold.raced

/-- R005: the tabled machine with the raced unfolding, on the root node and
on its converse, side by side. -/
def R005.engine : Engine := R004.engine.mirrored

end RwLog
