/-
# R005, parked: what the yardstick has to be shown to have

R005 is the top rung of epoch 1 (`lean/EPOCH1.md`). Master keeps its machine
text (`Engine.lean`, with the unfolders under `Unfolder/` and the tabled
machine under `Rungs/Tabled/`) because the next engine is measured against
it: roadmap M3 part B rewrites that text once against the restated trusted
interface, and M4 re-establishes the statements below there.

**Nothing in this file is proved on master.** Every statement here is a
theorem at the tag `epoch-1` (`R005.<name> : Obligation.<name>`, in
`Rungs/R005/Proofs/Admission.lean` at the tag), where the proofs rest on
R001 to R004. The statements of epoch 1 that say how R005 was admitted over
R004 (`same_trace`, `simulates`, `separates`, `improves`, `admits`) are not
restated here: they are history and are not re-proved.

* **The baseline's properties.** `keeps`, and the three every rung must
  state (`sound`, `complete`, `honest_exhaustion`).
* **The same cost from both ends.** R005's run on the mirror image of a query
  and its run on the query go through related states, every step costs
  exactly the same, and the answers are the same swapped (`mirror_exact`).
  The same holds for the converse of a query (`conv_exact`). So its cost does
  not depend on direction: on the mirror image and on the converse it has
  covered a pair, or halted, within 2 ticks of what it pays on the query
  (`direction_free`). The 2 ticks are for the converse, which is one symbol
  longer and is read twice.
* **One text.** `costed_engine`: the machine these statements are about is
  the engine at the kernel of the language.

## What was never claimed

* **Not the cheaper of the two directions at every step.** R005 pays for
  both runs until one of them finishes a step, so a step costs up to 14 times
  the cheaper of the two, and the first `n` steps up to `2 n` such rounds.
* **Nothing new about tables.** Each of the two runs is R004's: a goal whose
  unfolding never becomes final is still answered by tables that evaluate
  the unconstrained side of a sequence in full, from whichever end.
-/
import RwLog.Rungs.R005.Engine
import RwLog.Rungs.Mirror.Direction
import RwLog.Trusted.Properties

namespace RwLog

namespace R005

namespace Obligation

/-- P0.1 to P0.3 for R005. -/
def sound : Prop := runtime.Sound
def complete : Prop := runtime.Complete
def honest_exhaustion : Prop := runtime.HonestExhaustion

/-- R005 keeps every property of the proper baseline, and halts wherever
R001 halts (`Trusted/Properties.lean`). -/
def keeps : Prop := runtime.Keeps R001.runtime

/-! ### The same cost from both ends -/

/-- The run on the mirror image and the run on the query go through related
states: every step costs the same and emits the same answers swapped, up to
order and equivalence. -/
def mirror_exact : Prop := DualBisim costed RwLog.Mirror.Dual

/-- The run on the converse and the run on the query go through related
states: every step costs the same and emits the same answers swapped. -/
def conv_exact : Prop := ∃ rel, ConvBisim costed rel

/-- R005's cost does not depend on direction, within 2 ticks. -/
def direction_free : Prop := DirectionFree costed fun c _ => c + 2

/-- The machine these statements are about is an engine at the kernel of the
language: `costed` is what `engine` computes there. -/
def costed_engine : Prop := engine.costed = costed

end Obligation

end R005

end RwLog
