/-
# Rung R005: R004 on the query and on its mirror image, side by side

What R004 pays for a query depends on the end the query is written from
(`Family.lean`): its shared evaluation is keyed on what stands to the left of
a sub-expression, and nothing in it mirrors that.

R005 removes the dependence without touching R004's evaluation. It is
`Engine.mirrored` (`Rungs/Mirror/Gen.lean`) of R004: it runs R004 on the query
and R004 on the mirror image of the query in the mirrored program, and its
`k`-th step is the `k`-th step of whichever of the two runs gets there first,
with the answers of the run on the mirror image swapped back. R004's run on
the mirror image is the mirror image of its run, step for step, so the
answers are R004's whichever run wins.

Started on the mirror image, R005 races the same two runs, and no step of it
prefers one of them except for being ahead. So it pays exactly the same on a
query and on its mirror image, step for step, and exponentially less than
R004 on the family where R004 is slow from one end.
-/
import RwLog.Rungs.Mirror.Machine
import RwLog.Rungs.R005.Unfolder.R004.Gen
import RwLog.Rungs.R005.Unfolder.R004.Engine

namespace RwLog

namespace R005

/-- R005 as an engine: R004's engine, mirrored. -/
def engine : Engine := R004.engine.mirrored

/-- R005 with its cost. -/
def costed : CostedRuntime := RwLog.Mirror.machine R004.costed

def runtime : Runtime := costed.runtime

/-- Rung R005: no preprocessing, an empty artifact store, and R004 run on the
query and on its mirror image side by side. -/
def rung : Rung where
  pre := Preprocessor.id
  rt := runtime

end R005

end RwLog
