/-
# Properties of a run that are no law

The laws are `Runtime.Laws` (`Trusted/Properties.lean`): soundness,
completeness pair by pair, and an honest report of being done. This file has
further properties of a run that machines in this development are proved to
have. None of them is asked of a rung. They are here because proofs use
them: of the laws, and of what an admission asks.

* `DerivationGeneral`: every answer relates exactly the pairs of the span of
  one derivation.
* `TerminatesWhere Base`: the run halts wherever the run of `Base` halts.
* `EmptySide`: a side that halts with no answer makes `;` and `&` halt.
* `OrComm`, `OrAssoc`, `SeqAssoc`, `AndComm`, `AndAssoc`, `WritingFree`: two
  ways of writing one input have the same trace.
* `ConvTrace`, `DualTrace`: the trace on the converse, and on the mirror
  image, is the trace with every answer swapped, up to the order of the
  answers of one step and up to equivalent answers (`TraceEquiv`).
* `FinalMaximal`: when a run reports that it is done, its final report is the
  set of maximal emitted answers.

`KeepsPointwise`, `Keeps` and `Rung.Keeps` collect them, with the laws, as
the machines here were proved to have them together.
-/
import RwLog.Trusted.Properties

namespace RwLog

/-! ## Traces up to order and equivalence -/

section
variable {A B : Type} [Answer A] [Answer B]

/-- Two answer lists of one step agree up to order and answers equivalent in
`M`. The two lists may hold answers of two different types. -/
def StepEquiv (M : Interp) (xs : List A) (ys : List B) : Prop :=
  ∃ ys', ys'.Perm ys ∧ List.Forall₂ (Answer.Equiv M) xs ys'

/-- What two steps show agrees: answers and final reports up to `StepEquiv`,
and certificates for the same level. -/
def ShownEquiv (M : Interp) : Shown A → Shown B → Prop
  | .answers xs, .answers ys => StepEquiv M xs ys
  | .level n, .level m => n = m
  | .final xs, .final ys => StepEquiv M xs ys
  | _, _ => False

/-- Two traces agree step for step, up to `ShownEquiv`. -/
def TraceEquiv (M : Interp) (t : List (Shown A)) (t' : List (Shown B)) : Prop :=
  List.Forall₂ (ShownEquiv M) t t'

end

/-! ## Writing the same input in another way -/

/-- One use of a law of `|`, `;` or `&` at the root of an expression. -/
inductive RelOf.Law : Rel → Rel → Prop
  | orComm (a b : Rel) : Law (.or a b) (.or b a)
  | orAssoc (a b c : Rel) : Law (.or (.or a b) c) (.or a (.or b c))
  | seqAssoc (a b c : Rel) : Law (.seq (.seq a b) c) (.seq a (.seq b c))
  | andComm (a b : Rel) : Law (.and a b) (.and b a)
  | andAssoc (a b c : Rel) : Law (.and (.and a b) c) (.and a (.and b c))

/-- Two expressions are the same up to the order and grouping of `|` and `&`
and the grouping of `;`: the laws, used anywhere and any number of times. -/
inductive RelOf.SameWriting : Rel → Rel → Prop
  | law {a b : Rel} : RelOf.Law a b → SameWriting a b
  | refl (a : Rel) : SameWriting a a
  | symm {a b : Rel} : SameWriting a b → SameWriting b a
  | trans {a b c : Rel} : SameWriting a b → SameWriting b c → SameWriting a c
  | or {a a' b b' : Rel} : SameWriting a a' → SameWriting b b' → SameWriting (.or a b) (.or a' b')
  | and {a a' b b' : Rel} : SameWriting a a' → SameWriting b b' →
      SameWriting (.and a b) (.and a' b')
  | seq {a a' b b' : Rel} : SameWriting a a' → SameWriting b b' →
      SameWriting (.seq a b) (.seq a' b')
  | conv {a a' : Rel} : SameWriting a a' → SameWriting (.conv a) (.conv a')

/-- Two programs define the same names in the same order, with bodies that
are the same up to `RelOf.SameWriting`, with the same sorts. -/
def ProgramOf.SameWriting (P P' : Program) : Prop :=
  P'.sorts = P.sorts ∧
    List.Forall₂ (fun d d' => d.1 = d'.1 ∧ RelOf.SameWriting d.2 d'.2) P.defs P'.defs

namespace Runtime

variable (R : Runtime)

/-- Every emitted answer refines the span of one derivation: it
relates exactly the pairs that span relates, so no answer is less general
than its derivation. -/
def DerivationGeneral : Prop :=
  ∀ P q, P.WellFormed q → ∀ a ∈ R.Answers P q,
    ∃ s, Derives P q s ∧ Answer.Refines P.sorts.interp a s

/-- The runtime halts on every query the base halts on. -/
def TerminatesWhere (Base : Runtime) : Prop :=
  ∀ P q, P.WellFormed q → Base.Terminates P q → R.Terminates P q

/-- Swapping the branches of `|` does not change the run. -/
def OrComm : Prop :=
  ∀ P (a b : Rel) n, R.trace (R.init P (.or a b)) n = R.trace (R.init P (.or b a)) n

/-- Regrouping `|` does not change the run. -/
def OrAssoc : Prop :=
  ∀ P (a b c : Rel) n, R.trace (R.init P (.or (.or a b) c)) n =
    R.trace (R.init P (.or a (.or b c))) n

/-- Regrouping `;` does not change the run. -/
def SeqAssoc : Prop :=
  ∀ P (a b c : Rel) n, R.trace (R.init P (.seq (.seq a b) c)) n =
    R.trace (R.init P (.seq a (.seq b c))) n

/-- Swapping the sides of `&` does not change the run. -/
def AndComm : Prop :=
  ∀ P (a b : Rel) n, R.trace (R.init P (.and a b)) n = R.trace (R.init P (.and b a)) n

/-- Regrouping `&` does not change the run. -/
def AndAssoc : Prop :=
  ∀ P (a b c : Rel) n, R.trace (R.init P (.and (.and a b) c)) n =
    R.trace (R.init P (.and a (.and b c))) n

/-- The run does not depend on how the input is written: two programs and two
queries that are the same up to the order and grouping of `|` and `&` and the
grouping of `;`, anywhere in the query and in the bodies, have the same run.
`OrComm`, `OrAssoc`, `SeqAssoc`, `AndComm` and `AndAssoc` are the cases of one
law at the root of the query. -/
def WritingFree : Prop :=
  ∀ (P P' : Program) (q q' : Rel), P.SameWriting P' → RelOf.SameWriting q q' →
    ∀ n, R.trace (R.init P q) n = R.trace (R.init P' q') n

/-- A side that halts with no answer makes `;` and `&` halt, on either
side and whatever the other side does. -/
def EmptySide : Prop :=
  ∀ P (a b : Rel), P.WellFormed (.seq a b) →
    R.Terminates P a → R.Answers P a = ∅ →
    R.Terminates P (.seq a b) ∧ R.Terminates P (.seq b a) ∧
    R.Terminates P (.and a b) ∧ R.Terminates P (.and b a)

/-- Running `conv q` is running `q` with every
answer swapped, step for step. Like `DualTrace`, it is up to the order of the
answers of one step and up to equivalent answers: a machine is not held to an
order among the answers of a step. It is asked of well-formed input, like
every property of a run: a domain need not represent a span that is not
first-order, so the representative of such a span and of the span with its
sides exchanged need not be each other's converse (`Trusted/Domain.lean`). -/
def ConvTrace : Prop :=
  ∀ P q n, P.WellFormed q →
    TraceEquiv P.sorts.interp (R.trace (R.init P (.conv q)) n)
      ((R.trace (R.init P q) n).map Shown.swap)

/-- Running the mirror image of a
query in the mirrored program is the mirror image of the run, step for
step. -/
def DualTrace : Prop :=
  ∀ P q n, P.WellFormed q →
    TraceEquiv P.sorts.interp (R.trace (R.init P.dual q.dual) n)
      ((R.trace (R.init P q) n).map Shown.swap)

/-- When a run reports that it is done, its final report is the set of
maximal emitted answers: every reported answer was emitted, every emitted
answer is covered by a reported one, and no reported answer covers another.
So the report is irredundant, and it holds one answer for each class of
equivalent maximal answers. -/
def FinalMaximal : Prop :=
  ∀ P q, P.WellFormed q → ∀ n fin, R.final (R.init P q) n = some fin →
    (∀ a ∈ fin, a ∈ R.emitted (R.init P q) n) ∧
    (∀ a ∈ R.emitted (R.init P q) n, ∃ b ∈ fin, Answer.Covers P.sorts.interp b a) ∧
    fin.Pairwise fun a b => ¬ Answer.Covers P.sorts.interp a b ∧ ¬ Answer.Covers P.sorts.interp b a

/-! ## What is kept -/

/-- The laws with the further properties stated on pairs and runs alone, and
the halting of `Base`. -/
structure KeepsPointwise (Base : Runtime) : Prop where
  sound : R.Sound
  pointComplete : R.PointComplete
  honest : R.HonestExhaustion
  honestProgress : R.HonestProgress
  derivationGeneral : R.DerivationGeneral
  terminates : R.TerminatesWhere Base
  orComm : R.OrComm
  orAssoc : R.OrAssoc
  emptySide : R.EmptySide
  convTrace : R.ConvTrace
  dualTrace : R.DualTrace

/-- A machine with these properties has the laws. -/
theorem KeepsPointwise.laws {R : Runtime} {Base : Runtime} (h : R.KeepsPointwise Base) :
    R.Laws := ⟨h.sound, h.pointComplete, h.honest⟩

/-- The list of `KeepsPointwise`, and completeness span by span. -/
structure Keeps (Base : Runtime) : Prop extends R.KeepsPointwise Base where
  complete : R.Complete

end Runtime

/-- Whatever the artifact store, the rung as one machine on the original
input has every property of `KeepsPointwise`. -/
def Rung.Keeps (G : Rung) (κ : KernelRung) (Base : Runtime) : Prop :=
  ∀ A, (G.runtime κ A).KeepsPointwise Base

end RwLog
