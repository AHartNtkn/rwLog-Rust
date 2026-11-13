/-
# The properties every rung keeps

The proper baseline has every qualitative execution property the ladder asks
for, and a later rung may add properties but never drop one. This file states
those properties for an arbitrary runtime and an arbitrary type of answers
(`Trusted/Runtime.lean`), each on what the answers denote, so that the list a
rung is held to does not depend on how any one machine is built or on what
its answers are made of. `Runtime.Keeps R Base` collects them for a machine,
and `Rung.Keeps G Base` for a whole rung, preprocessor and machine together.

## The list

* P0.1 to P0.3 (`Sound`, `Complete`, `HonestExhaustion`,
  `Trusted/Runtime.lean`), and completeness against the ground semantics pair
  by pair (`PointComplete`): in every model, every pair the query relates is
  related by an emitted answer;
* `HonestProgress` (`Trusted/Runtime.lean`): a progress certificate for level
  `n` is true when it is emitted;
* P3.0 `DerivationGeneral`: no answer is less general than its derivation;
* termination wherever the base terminates (`TerminatesWhere`): tabling
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

## Stated here, and fields of `Keeps` from the first machine that has them

* `SeqAssoc`, `AndComm`, `AndAssoc`: the grouping of `;` and the order and
  grouping of `&` do not change the run, stated like `OrComm`. `WritingFree`
  is all five laws together, used anywhere in the query and in the bodies of
  the program and any number of times: the run does not depend on how the
  input happens to be written.
* `FinalMaximal`: when a run reports that it is done, its final report is the
  set of maximal emitted answers.
* `Fair`: the fairness bound, in the last section. It is about ticks, so it
  is a property of a machine with its cost (`Trusted/Cost.lean`).

## Whole rungs

A rung is a preprocessor followed by a machine, and from the outside it is
one machine on the original input (`Rung.runtime`). `Rung.Keeps` says what
that machine keeps, which is what a preprocessor must respect: every property
in the list except `Complete`. One emitted answer covering a whole derivable
span of the original program does not survive preprocessing in general (a
preprocessor may split a definition), so a rung is held to `PointComplete`.
The trace laws and the mirror obligation (`DualTrace`) are stated on the
original input, so the preprocessor must commute with them.

Not here, because they are statements about one machine's internal state and
have to be restated for a machine built differently: prompt pruning (P2.4)
and the table invariants.
-/
import RwLog.Trusted.Cost

namespace RwLog

/-! ## Traces up to order and equivalence -/

section
variable {A B : Type} [Answer A] [Answer B]

/-- Two answer lists of one step agree up to order and equivalent answers.
The two lists may hold answers of two different types. -/
def StepEquiv (xs : List A) (ys : List B) : Prop :=
  ∃ ys', ys'.Perm ys ∧ List.Forall₂ Answer.Equiv xs ys'

/-- What two steps show agrees: answers and final reports up to `StepEquiv`,
and certificates for the same level. -/
def ShownEquiv : Shown A → Shown B → Prop
  | .answers xs, .answers ys => StepEquiv xs ys
  | .level n, .level m => n = m
  | .final xs, .final ys => StepEquiv xs ys
  | _, _ => False

/-- Two traces agree step for step, up to `ShownEquiv`. -/
def TraceEquiv (t : List (Shown A)) (t' : List (Shown B)) : Prop := List.Forall₂ ShownEquiv t t'

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
are the same up to `RelOf.SameWriting`, under the same theory. -/
def ProgramOf.SameWriting (P P' : Program) : Prop :=
  P'.theory = P.theory ∧
    List.Forall₂ (fun d d' => d.1 = d'.1 ∧ RelOf.SameWriting d.2 d'.2) P.defs P'.defs

namespace Runtime

variable (R : Runtime)

/-! ## Properties of one machine -/

/-- Completeness against the ground semantics, pair by pair: in every model,
every pair the query relates is related by some emitted answer. -/
def PointComplete : Prop :=
  ∀ P q, P.WellFormed q → ∀ M, P.theory.Model M → ∀ p ∈ P.semAt M q,
    ∃ n, ∃ a ∈ R.emitted (R.init P q) n, p ∈ Answer.den M a

/-- P3.0: every emitted answer refines the span of one derivation: in every
model of the theory it relates exactly the pairs that span relates, so no
answer is less general than its derivation. -/
def DerivationGeneral : Prop :=
  ∀ P q, P.WellFormed q → ∀ a ∈ R.Answers P q, ∃ s, Derives P q s ∧ Answer.Refines P.theory a s

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
  ∀ P q n, R.trace (R.init P (.conv q)) n = (R.trace (R.init P q) n).map Shown.swap

/-- P1.4 strong, for the mirrored program: running the mirror image of a
query in the mirrored program is the mirror image of the run, step for
step. -/
def DualTrace : Prop :=
  ∀ P q n, (∀ ρ ∈ P.theory, ρ.WellFormed) →
    TraceEquiv (R.trace (R.init P.dual q.dual) n) ((R.trace (R.init P q) n).map Shown.swap)

/-- P2.3: adding rules only removes answers: in every model of the larger
theory, each answer under it relates only pairs that one answer under the
smaller theory relates, unless it relates nothing in any such model. -/
def TheoryMonoAnswers : Prop :=
  ∀ P (T : Theory) q, P.WellFormed q → (∀ ρ ∈ T, ρ.WellFormed) → (∀ ρ ∈ P.theory, ρ ∈ T) →
    ∀ a ∈ R.Answers { P with theory := T } q,
      Answer.Dead T a ∨ ∃ b ∈ R.Answers P q, Answer.CoversLive T b a

/-- P3.1 and P3.2: no emitted answer is covered by an earlier one. -/
def NoSubsumed : Prop :=
  ∀ P q, P.WellFormed q → ∀ n,
    (R.emitted (R.init P q) n).Pairwise fun a b => ¬ Answer.Covers a b

/-- When a run reports that it is done, its final report is the set of
maximal emitted answers: every reported answer was emitted, every emitted
answer is covered by a reported one, and no reported answer covers another.
So the report is irredundant, and it holds one answer for each class of
equivalent maximal answers. -/
def FinalMaximal : Prop :=
  ∀ P q, P.WellFormed q → ∀ n fin, R.final (R.init P q) n = some fin →
    (∀ a ∈ fin, a ∈ R.emitted (R.init P q) n) ∧
    (∀ a ∈ R.emitted (R.init P q) n, ∃ b ∈ fin, Answer.Covers b a) ∧
    fin.Pairwise fun a b => ¬ Answer.Covers a b ∧ ¬ Answer.Covers b a

/-! ## What is kept -/

/-- Every property a rung keeps that is stated on pairs and runs alone, with
the termination class of `Base`. This is the list a whole rung is held to
(`Rung.Keeps`). -/
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
  theoryMono : R.TheoryMonoAnswers
  noSubsumed : R.NoSubsumed

/-- Every property a machine keeps: the list of `KeepsPointwise`, and
completeness span by span. -/
structure Keeps (Base : Runtime) : Prop extends R.KeepsPointwise Base where
  complete : R.Complete

end Runtime

/-! ## Whole rungs -/

/-- The rung as one runtime on the original input, for an artifact store: its
first state is the machine's first state on the preprocessed input. -/
def Rung.runtime (G : Rung) (A : ArtifactStore) : Runtime where
  Ans := G.rt.Ans
  State := G.rt.State
  init P q := G.rt.init (G.pre.run A P q).val.1 (G.pre.run A P q).val.2.1
  step := G.rt.step

/-- What a whole rung keeps: whatever the artifact store, the rung as one
machine on the original input has every property of `KeepsPointwise`. -/
def Rung.Keeps (G : Rung) (Base : Runtime) : Prop :=
  ∀ A, (G.runtime A).KeepsPointwise Base

/-! ## Fairness

Search is fair: an answer is not starved by the alternatives that compete
with it. The bound says by how much they may delay it, relative to what the
answer costs when its alternative is the whole query.

### Alternatives

`Alternative P q q' f`: `q'` is `q` with some of its choices made. A choice is
made at a union, by taking one of its members (the members of a union are
counted however it is bracketed), and behind a call, by making choices in its
body, so the choices of a recursion are made level by level. `f` is the
number of members of each union at which a choice was made, multiplied: the
alternatives that compete with `q'` along the nesting. The query `q'` relates
only pairs that `q` relates.

### The bound

`Fair C c` has two parts, and a machine must meet both, so an answer arrives
within the smaller of the two.

* `share`: a pair that `C` covers within `n` ticks when run on `q'` alone is
  covered within `c * (f * n + size)` ticks when run on `q`. For one union of
  `m` members that is `m * n`. Through a recursion `f` multiplies level by
  level, so this part alone allows a delay exponential in the depth.
* `flat`: a pair that `C` covers within `n` ticks when run on `q'` alone is
  covered within `c * n` *steps* when run on `q`, whatever `f` is. The depth
  of the nesting does not appear. A step of a fair machine may be a round in
  which every goal it has opened and not finished does one unit of work, so
  in ticks this is `n` times what a round costs, which is the number of live
  goals opened so far. What a machine has opened is not something the
  specification can see, and a machine could inflate any count of it; what a
  step costs is in `CostedRuntime.paid` and cannot be declared.

Every member of a union counts in `f`, whether or not it is still running.

### What is false

A bound polynomial in the size of an answer's derivation and of the input is
false for every machine that emits spans and pays a tick for each:
`bit ; … ; bit` with `k` factors has `2 ^ k` answers, no two covered by one
sound span, each with a derivation of size linear in `k`. That is
`FirstWording` and `firstWording_false` in `Rungs/Framework/Fairness.lean`.
-/

/-- The members of a union, however it is bracketed. An expression that is
not a union is its own only member. -/
def RelOf.members : Rel → List Rel
  | .or a b => a.members ++ b.members
  | e => [e]

/-- `q'` is `q` with some of its choices made, and `f` is the number of
members of each union at which a choice was made, multiplied. -/
inductive Alternative (P : Program) : Rel → Rel → Nat → Prop
  | same (e : Rel) : Alternative P e e 1
  | pick {a b m e' : Rel} {f : Nat} : m ∈ (RelOf.or a b).members → Alternative P m e' f →
      Alternative P (.or a b) e' ((RelOf.or a b).members.length * f)
  | seq {a b a' b' : Rel} {f g : Nat} : Alternative P a a' f → Alternative P b b' g →
      Alternative P (.seq a b) (.seq a' b') (f * g)
  | and {a b a' b' : Rel} {f g : Nat} : Alternative P a a' f → Alternative P b b' g →
      Alternative P (.and a b) (.and a' b') (f * g)
  | conv {a a' : Rel} {f : Nat} : Alternative P a a' f → Alternative P (.conv a) (.conv a') f
  | call {n : Name} {e' : Rel} {f : Nat} : Alternative P (P.body n) e' f →
      Alternative P (.call n) e' f

/-- The fairness bound with constant `c`. -/
structure Fair (C : CostedRuntime) (c : Nat) : Prop where
  /-- A pair covered within `n` ticks by an alternative run alone is covered
  within `c * (f * n + size)` ticks, `f` being the alternatives that compete
  with it along the nesting, multiplied. -/
  share : ∀ P q q' f, P.WellFormed q → Alternative P q q' f →
    ∀ M, P.theory.Model M → ∀ x n, C.Covered P q' M x n →
      C.CoversWithin P q M x (c * (f * C.paid P q' n + P.size + q.size))
  /-- A pair covered within `n` ticks by an alternative run alone is covered
  within `c * n` steps, however deep the alternative is nested. -/
  flat : ∀ P q q' f, P.WellFormed q → Alternative P q q' f →
    ∀ M, P.theory.Model M → ∀ x n, C.Covered P q' M x n →
      ∃ m, m ≤ c * C.paid P q' n ∧ C.Covered P q M x m

end RwLog
