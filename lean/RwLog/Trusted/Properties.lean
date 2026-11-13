/-
# The properties every rung keeps

The proper baseline R001 has every qualitative execution property the ladder
asks for, and a later rung may add properties but never drop one. This file
states those properties for an arbitrary runtime, so that the list a rung is
held to does not depend on how any one machine is built. `Runtime.Keeps R Base`
collects them; a rung above the proper baseline proves `Keeps` with R001's
runtime as `Base`.

Names follow the execution-properties document:

* P0.1 to P0.3 (`Sound`, `Complete`, `HonestExhaustion`, `Trusted/Engine.lean`),
  and completeness against the ground semantics pair by pair
  (`PointComplete`): in every model, every pair the query relates is related
  by an emitted answer;
* P3.0 `DerivationGeneral`: no answer is less general than its derivation;
* termination wherever the base terminates (`TerminatesWhere`). For R001's
  runtime as the base this carries its whole termination class: tabling
  termination (P2.1), boundary pushing, finite-side propagation (P1.3);
* P1.1 `OrComm`, `OrAssoc`: the order and grouping of `|` do not change the
  run;
* P1.2 `EmptySide`: a side that fails finitely makes `;` and `&` fail
  finitely;
* P1.4 strong `ConvTrace`, `DualTrace`: the run of the converse, and of the
  mirrored query in the mirrored program, is the mirror image of the run,
  step for step;
* P2.3 `TheoryMonoAnswers`: adding rules to the theory only removes answers;
* P3.1 and P3.2 `NoSubsumed`: no answer is covered by an earlier one.

"Step for step" is up to the order of the answers of one step and up to
equivalent answers (`TraceEquiv`).

Not here, because they are statements about one machine's internal state and
have to be restated for a machine built differently: prompt pruning (P2.4,
`R001.Obligation.prompt_pruning`), and the table invariants.
-/
import RwLog.Trusted.Engine
import RwLog.SpanLayer.Coverage

namespace RwLog

/-- Two answer lists of one step agree up to order and equivalent answers. -/
def StepEquiv (xs ys : List Span) : Prop :=
  ∃ ys', ys'.Perm ys ∧ List.Forall₂ Span.Equiv xs ys'

/-- Two traces agree step for step, up to `StepEquiv`. -/
def TraceEquiv (t t' : List (List Span)) : Prop := List.Forall₂ StepEquiv t t'

namespace Runtime

variable (R : Runtime)

/-- Completeness against the ground semantics, pair by pair: in every model,
every pair the query relates is related by some emitted answer. -/
def PointComplete : Prop :=
  ∀ P q, P.WellFormed q → ∀ M, P.theory.Model M → ∀ p ∈ P.semAt M q,
    ∃ n, ∃ a ∈ R.emitted (R.init P q) n, p ∈ a.denAt M

/-- P3.0: every emitted answer refines the span of one derivation: it is that
span, instantiated only by equations the theory forces, so no answer is less
general than its derivation. -/
def DerivationGeneral : Prop :=
  ∀ P q, P.WellFormed q → ∀ a ∈ R.Answers P q, ∃ s, Derives P q s ∧ a.Refines P.theory s

/-- The runtime halts on every query the base halts on. -/
def TerminatesWhere (Base : Runtime) : Prop :=
  ∀ P q, P.WellFormed q → Base.Terminates P q → R.Terminates P q

/-- P1.1: swapping the branches of `|` does not change the run. -/
def OrComm : Prop :=
  ∀ P (a b : Rel) n, R.trace (R.init P (.or a b)) n = R.trace (R.init P (.or b a)) n

/-- P1.1: regrouping `|` does not change the run. -/
def OrAssoc : Prop :=
  ∀ P (a b c : Rel) n, R.trace (R.init P (.or (.or a b) c)) n =
    R.trace (R.init P (.or a (.or b c))) n

/-- P1.2: a side that halts with no answer makes `;` and `&` halt, on either
side and whatever the other side does. -/
def EmptySide : Prop :=
  ∀ P (a b : Rel), P.WellFormed (.seq a b) →
    R.Terminates P a → R.Answers P a = ∅ →
    R.Terminates P (.seq a b) ∧ R.Terminates P (.seq b a) ∧
    R.Terminates P (.and a b) ∧ R.Terminates P (.and b a)

/-- P1.4 strong, for the converse: running `conv q` is running `q` with every
answer swapped, step for step. -/
def ConvTrace : Prop :=
  ∀ P q n, R.trace (R.init P (.conv q)) n = (R.trace (R.init P q) n).map (·.map Span.swap)

/-- P1.4 strong, for the mirrored program: running the mirror image of a
query in the mirrored program is the mirror image of the run, step for
step. -/
def DualTrace : Prop :=
  ∀ P q n, (∀ ρ ∈ P.theory, ρ.WellFormed) →
    TraceEquiv (R.trace (R.init P.dual q.dual) n)
      ((R.trace (R.init P q) n).map (·.map Span.swap))

/-- P2.3: adding rules only removes answers: in every model of the larger
theory, each answer under it relates only pairs that one answer under the
smaller theory relates, unless it relates nothing in any such model. -/
def TheoryMonoAnswers : Prop :=
  ∀ P (T : Theory) q, P.WellFormed q → (∀ ρ ∈ T, ρ.WellFormed) → (∀ ρ ∈ P.theory, ρ ∈ T) →
    ∀ a ∈ R.Answers { P with theory := T } q,
      a.Dead T ∨ ∃ b ∈ R.Answers P q, b.CoversLive T a

/-- P3.1 and P3.2: no emitted answer is covered by an earlier one. -/
def NoSubsumed : Prop :=
  ∀ P q, P.WellFormed q → ∀ n,
    (R.emitted (R.init P q) n).Pairwise fun a b => ¬ a.Covers b

/-- Every property a rung keeps, with the termination class of `Base`. -/
structure Keeps (Base : Runtime) : Prop where
  sound : R.Sound
  complete : R.Complete
  pointComplete : R.PointComplete
  honest : R.HonestExhaustion
  derivationGeneral : R.DerivationGeneral
  terminates : R.TerminatesWhere Base
  orComm : R.OrComm
  orAssoc : R.OrAssoc
  emptySide : R.EmptySide
  convTrace : R.ConvTrace
  dualTrace : R.DualTrace
  theoryMono : R.TheoryMonoAnswers
  noSubsumed : R.NoSubsumed

end Runtime

end RwLog
