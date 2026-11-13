/-
# Answers, steps and runtimes

## Answers

A machine emits *answers*. What an answer is made of is the machine's own
business; the specification only asks what it means. `Answer A` says that the
values of `A` are answers: in every interpretation an answer denotes a
relation between ground terms (`den`), and every answer has a converse
(`swap`) that denotes the converse relation. Every property of a machine is
stated on these denotations, so a machine whose answers are not spans is held
to the same statements. `Span` is the instance the language itself provides.

`Answer.Covers`, `Equiv`, `Dead` and `Refines` compare answers, possibly of
two different types, by what they denote in one interpretation. The
properties below use them in the interpretation of the program's sorts.

## Steps

A step of a machine has one of three outputs.

* `emit as s`: it emits the answers `as` (possibly none) and goes on from
  `s`. A step may emit several answers at once, and the order inside one step
  carries no meaning.
* `progress n s`: it emits a *progress certificate for level `n`* and goes on
  from `s`. The certificate claims that every pair the query relates whose two
  terms have size at most `n` is related by an answer already emitted
  (`Runtime.HonestProgress`). A query that never halts can still report this.
* `done final`: it reports that it is done. `final` is its final report, the
  answers it stands by (`Runtime.FinalMaximal`, in `Trusted/Properties.lean`).

## Runtimes

A runtime is a deterministic small-step machine with its type of answers.
`run`, `emitted`, `final`, `Halts` and `trace` observe the first `n` steps of
a run. The trace is everything an observer sees, step by step: the answers of
an emitting step, the level of a certificate, the final report.

The properties every machine must prove against the specification (soundness,
completeness, honest exhaustion, honest progress) are stated here, so a
machine cannot weaken them.
-/
import RwLog.SpanLayer.Derives
import RwLog.Trusted.Semantics

namespace RwLog

/-! ## Answers -/

/-- The values of `A` are answers: each denotes a relation between ground
terms in every interpretation, and has a converse that denotes the converse
relation. -/
class Answer (A : Type) where
  /-- The pairs an answer relates in an interpretation. -/
  den : Interp → A → PRel
  /-- The converse answer. -/
  swap : A → A
  den_swap : ∀ M a, den M (swap a) = (den M a).inv

/-- Spans are answers. -/
instance : Answer Span where
  den M s := s.denAt M
  swap := Span.swap
  den_swap M s := by
    ext p
    constructor
    · rintro ⟨σ, h₁, h₂, hc⟩; exact ⟨σ, h₂, h₁, hc⟩
    · rintro ⟨σ, h₁, h₂, hc⟩; exact ⟨σ, h₂, h₁, hc⟩

namespace Answer

variable {A B : Type} [Answer A] [Answer B]

/-- `a` covers `b` in `M`: `a` relates every pair `b` relates. -/
def Covers (M : Interp) (a : A) (b : B) : Prop := den M b ⊆ den M a

/-- Two answers are equivalent in `M` when each covers the other. -/
def Equiv (M : Interp) (a : A) (b : B) : Prop := Covers M a b ∧ Covers M b a

/-- The answer relates no pair in `M`. -/
def Dead (M : Interp) (a : A) : Prop := den M a = ∅

/-- `a` and `b` relate the same pairs in `M`. -/
def Refines (M : Interp) (a : A) (b : B) : Prop := den M a = den M b

end Answer

/-! ## Steps -/

/-- What a step does: it emits answers and goes on, or emits a progress
certificate for a level and goes on, or reports that it is done, with its
final report. `A` is the type of answers and `S` the type of states. -/
inductive StepOf (A : Type) (S : Type) where
  | emit (as : List A) (s : S)
  | progress (n : Nat) (s : S)
  | done (final : List A)

/-- A step with every answer swapped. -/
def StepOf.swap {A S : Type} [Answer A] : StepOf A S → StepOf A S
  | .emit as s => .emit (as.map Answer.swap) s
  | .progress n s => .progress n s
  | .done final => .done (final.map Answer.swap)

/-- What one step shows an observer: the answers it emits, the level it
certifies, or its final report. -/
inductive Shown (A : Type) where
  | answers (as : List A)
  | level (n : Nat)
  | final (as : List A)

/-- What a step shows with every answer swapped. -/
def Shown.swap {A : Type} [Answer A] : Shown A → Shown A
  | .answers as => .answers (as.map Answer.swap)
  | .level n => .level n
  | .final as => .final (as.map Answer.swap)

/-! ## Runtimes -/

/-- A runtime: a deterministic small-step answer enumerator, with its type of
answers. -/
structure Runtime where
  Ans : Type
  [answer : Answer Ans]
  State : Type
  init : Program → Rel → State
  step : State → StepOf Ans State

attribute [instance] Runtime.answer

namespace Runtime

variable (R : Runtime)

/-- Run for `n` steps: the answers emitted, and the final report if the run
reported that it is done. -/
def run : R.State → Nat → List R.Ans × Option (List R.Ans)
  | _, 0 => ([], none)
  | s, n + 1 =>
    match R.step s with
    | .emit as s' => let r := run s' n; (as ++ r.1, r.2)
    | .progress _ s' => run s' n
    | .done final => ([], some final)

/-- The observable trace of the first `n` steps: what each step showed, in
order, ending with the final report if the run reported that it is done. -/
def trace : R.State → Nat → List (Shown R.Ans)
  | _, 0 => []
  | s, n + 1 =>
    match R.step s with
    | .emit as s' => .answers as :: trace s' n
    | .progress k s' => .level k :: trace s' n
    | .done final => [.final final]

/-- Answers emitted within the first `n` steps. -/
def emitted (s : R.State) (n : Nat) : List R.Ans := (R.run s n).1

/-- The final report, if the run reported that it is done within `n`
steps. -/
def final (s : R.State) (n : Nat) : Option (List R.Ans) := (R.run s n).2

/-- The run reported that it is done within `n` steps. -/
def Halts (s : R.State) (n : Nat) : Prop := (R.final s n).isSome = true

/-- The step taken after `k` steps emits a progress certificate for level
`n`. -/
def Certifies (s : R.State) (k n : Nat) : Prop := (R.trace s (k + 1))[k]? = some (.level n)

/-! ## Properties every machine proves (Tier 0)

They are stated for the runtime against the program and query it is run on
and against the specification, in the interpretation of the program's
sorts. -/

/-- Every emitted answer relates only pairs the query relates. -/
def Sound : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
    Answer.den P.sorts.interp a ⊆ P.pairs q

/-- Every derivable span is covered by a single emitted answer after
finitely many steps: the answer relates every pair the span relates. A span
that relates nothing needs no answer, so an engine may prune it. Because one
answer must cover the whole span, an engine that only emits ground answers
cannot be complete. -/
def Complete : Prop :=
  ∀ P q, P.WellFormed q → ∀ s, Derives P q s →
    Answer.Dead P.sorts.interp s ∨
      ∃ n, ∃ a ∈ R.emitted (R.init P q) n, Answer.Covers P.sorts.interp a s

/-- If the runtime reports it is done, the answers it emitted cover the
query exactly. -/
def HonestExhaustion : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, R.Halts (R.init P q) n →
    P.pairs q = ⋃ a ∈ R.emitted (R.init P q) n, Answer.den P.sorts.interp a

/-- A progress certificate is true when it is emitted: if the step taken
after `k` steps certifies level `n`, then every pair the query relates whose
two terms have size at most `n` is related by an answer emitted in the first
`k` steps. -/
def HonestProgress : Prop :=
  ∀ P q, P.WellFormed q → ∀ k n, R.Certifies (R.init P q) k n →
    ∀ p ∈ P.pairs q, p.1.size ≤ n → p.2.size ≤ n →
      ∃ a ∈ R.emitted (R.init P q) k, p ∈ Answer.den P.sorts.interp a

/-- The runtime reports it is done on every query of a class. -/
def TerminatesOn (C : Program → Rel → Prop) : Prop :=
  ∀ P q, P.WellFormed q → C P q → ∃ n, R.Halts (R.init P q) n

/-! ## Observing a whole run

Properties that compare runs (duality, order independence) are stated on
everything a run ever emits and on whether it ever reports that it is done. -/

/-- Every answer the run on `q` emits at some point. -/
def Answers (P : Program) (q : Rel) : Set R.Ans := {a | ∃ n, a ∈ R.emitted (R.init P q) n}

/-- The run on `q` reports that it is done at some point. -/
def Terminates (P : Program) (q : Rel) : Prop := ∃ n, R.Halts (R.init P q) n

end Runtime

end RwLog
