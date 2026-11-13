/-
# Rung R005: what must be proved

Every property is stated here as a `Prop` in the `R005.Obligation` namespace
and nothing in this file is proved: an obligation is discharged by a theorem
`R005.<name> : Obligation.<name>` in another file, and `AxiomAudit.lean` lists
the discharged ones.

R005 is judged against R004 by cost (`Trusted/Cost.lean`), and it is the
first rung that is admitted.

* **The same answers.** R005 emits, step for step, what R004 emits, up to
  order and equivalence (`same_trace`), and keeps every property of the
  baseline (`keeps`); the three every rung must state are stated (`sound`,
  `complete`, `honest_exhaustion`).
* **The same cost from both ends.** R005's run on the mirror image of a query
  and its run on the query go through related states, every step costs
  exactly the same, and the answers are the same swapped (`mirror_exact`).
  The same holds for the converse of a query (`conv_exact`). So its cost does
  not depend on direction: on the mirror image and on the converse it has
  covered a pair, or halted, within 2 ticks of what it pays on the query
  (`direction_free`). The 2 ticks are for the converse, which is one symbol
  longer and is read twice.
* **Never much worse.** R005 simulates R004 within a quadratic bound
  (`simulates`): by the step at which R004 has covered a pair after paying
  `c`, R005 has taken at most `c + 1` steps, each of at most two races of
  two steps that cost R004 at most `c`.
* **Exponentially better on a family.** `sepFam k` is
  `bit ; (bit ; … ; (bit ; $x -> c))` (`Family.lean`). R004 has paid at least
  `2 ^ k` before it covers anything on it; R005 covers `(z, c)` within a
  cubic bound (`separates`), because its run on the mirror image finishes its
  first round within one.
* **Admission.** `admits`: R005 advances on R004 with the numerals `bounds`
  and its cost does not depend on direction within `dirBound`.

## What is not claimed

* **Not the cheaper of the two directions at every step.** R005 pays for
  both runs until one of them finishes a step, so a step costs up to 14 times
  the cheaper of the two, and the first `n` steps up to `2 n` such rounds.
* **Nothing new about tables.** Each of the two runs is R004's: a goal whose
  unfolding never becomes final is still answered by tables that evaluate
  the unconstrained side of a sequence in full, from whichever end.
-/
import RwLog.Rungs.R005.Engine
import RwLog.Rungs.R005.Family
import RwLog.Rungs.Mirror.Direction
import RwLog.Trusted.Properties

namespace RwLog

namespace R005

namespace Obligation

/-! ### The same answers -/

/-- R005 emits, step for step, what R004 emits, up to order and
equivalence. -/
def same_trace : Prop :=
  ∀ P q, P.WellFormed q → ∀ n,
    TraceEquiv (runtime.trace (runtime.init P q) n) (R004.runtime.trace (R004.runtime.init P q) n)

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

/-! ### Never much worse -/

/-- R005 simulates R004 within `c + n + 2 (c + 1) (1 + 14 c)`. -/
def simulates : Prop := Simulates R004.costed costed RwLog.Mirror.bound

/-! ### Exponentially better on a family -/

/-- On `sepFam k`, an input of size `12 k + 15`, R005 has covered the pair
`(z, c)` within `24 k + 32 + 2800000 (k + 2) ^ 3` ticks, and R004 has paid at
least `2 ^ k` at any step at which it has covered it. -/
def separates : Prop :=
  Separates R004.costed costed sepFam (fun _ => sepTarget) (fun k => 12 * k + 15)
    (fun k => 2 ^ k) fun k => 24 * k + 32 + 28 * mirrorFirst k

/-! ### Admission -/

/-- The numerals R005 advances with: simulation within `29 (c + n + 1) ^ 2`,
the `k`-th input of size at most `15 (k + 1)`, covered within
`22400032 (k + 1) ^ 3` ticks. -/
def bounds : Bounds := ⟨29, 2, 15, 1, 22400032, 3⟩

/-- The numerals of the direction bound: `2 (c + n + 1)`. -/
def dirBound : DirBound := ⟨2, 1⟩

/-- The improvement: R005 improves on R004 with these numerals, on `sepFam`
and the pair `(z, c)`. -/
def improves : Prop := Improves R004.costed costed bounds sepFam fun _ => sepTarget

/-- The machine these obligations are about is an engine at the kernel of the
language: `costed` is what `engine` computes there. -/
def costed_engine : Prop := engine.costed = costed

/-- The admission of the rung: R005 above R004, neither with any
preprocessing, so preprocessing is recorded to cost nothing; and R005's cost
does not depend on direction. -/
def admits : Prop :=
  Admits ⟨Preprocessor.id, R004.engine⟩ ⟨Preprocessor.id, engine⟩ bounds dirBound (fun _ => 0)
    sepFam fun _ => sepTarget

end Obligation

end R005

end RwLog
