/-
# The cost model and what counts as an improvement

Rungs from the second on are admitted by comparing costs, so cost has to be
part of the trusted statement and not of a submission.

## Charged computations

`Cost α` is a value together with the ticks spent computing it and the space
it used (`Trusted/CostMonad.lean`). The operations on nodes and answers and
what each is charged are in `Trusted/Charged.lean` and `Trusted/Kernel.lean`;
what an operation on representatives is charged is given by a kernel rung
(`KernelRung`, `Trusted/Kernel.lean`). An engine is written against an
abstract kernel and can do nothing to a representative, and make no answer,
except through those operations, so what it spends at a kernel rung is fixed
by its text (`Engine`, below).

A computation can be run under a budget (`Cost.within`): if it needs no more
than the budget it is run and charged as usual, and otherwise the whole budget
is spent and nothing is learned from it. This is the one way to give up on a
computation, and giving up is never cheaper than the budget allowed.

## Costed runtimes

A `CostedRuntime` is a small-step machine, with its type of answers
(`Trusted/Runtime.lean`), whose step is a charged computation.
Forgetting the ticks gives an ordinary `Runtime`, the one the correctness
theorems are about, so cost and behaviour cannot drift apart.

## What is measured: finishing a level

Cost is how soon a machine has finished the levels of a relation
(`Trusted/Levels.lean`). Level `c` is the pairs with a derivation of weight
at most `c`; it belongs to the program as written and mentions no machine. A
machine may report a level, and a report is true when the answers emitted so
far relate every pair of that level (`Runtime.HonestReports`). A machine has
finished level `c` when it has reported a level `c` or higher, or has
reported that it is done (`Runtime.Finished`).

`FinishesUsing μ P q c b` says the machine has finished level `c` of `q`
having used at most `b` of a resource. The run is one continuing run: it is
not started again for each level. So the cost of finishing a level never
falls as the level rises.

Nothing is measured answer by answer. Two correct machines may emit different
answers for the same relation, in different orders, and one answer with
variables may cover what another machine needs many answers for; none of
that is compared. No clause says when a particular pair is covered.

## Resources

What a machine has used on an input by the end of its first `n` steps is a
number, and there is one such number for each resource (`Meter`). Time is the
ticks paid (`Meter.time`) and space is the most cells live at any moment so
far (`Meter.space`).

Between two steps the cells that are live are those of the state the machine
holds (`CostedRuntime.live`); during a step they are those of the state it
started from and what the step has allocated. So a machine that lets go of
something uses less from the next step on. An engine does not get to say how
many cells its state takes: it lists what the state holds and proves that
the state is determined by the listing (`Engine.held`, `Engine.held_inj`),
and the cells of the listing are counted here (`Engine.liveAt`).

## Never worse

`NeverWorse Old New p` compares two machines on the same program, level by
level: whenever `Old` has finished a level `c` of an input, `New` finishes
that level having paid at most `p` of what `Old` has paid and of the size of
the input and `c`; and whenever `Old` has reported that it is done, `New`
reports that it is done having paid at most `p` of what `Old` has paid and
of the size of the input. It is asked on every well-formed input. Both
machines are run on the same program, so the levels are the same levels, and
"inside any larger program" is "on every program".

## A win on a class

A class (`ProgClass`) is three computable functions on an input: `mem`
decides membership, `rank` is the number the gain is stated in, and `level`
is the level of the member the comparison is about. The facts about a class
that mention no machine are `ProgClass.Proper`: members are well formed,
their size is at most a stated function of their rank, and the rank is
unbounded over the members.

`WinsOn ρ Old New C lo hi`, for a resource `ρ`: on every member of `C`, of
rank `k`, `New` finishes the member's level having used at most `hi k`, and
`Old` has used at least `lo k` at any step by which it has finished it. The
upper bound on `New` mentions no other machine.

The members are whole programs. Nothing is claimed about a program that has
a member as a part: a machine may stop early or drop work in a larger
program, and then a gain on the part need not show in the whole. A class
that is meant to reach larger programs has those programs as members, and
its bounds are proved of them.

## The kinds of win

A kind is a resource (time or space) and the size of the gain (`Gap`), and
the numerals of the improvement are explicit (`Bounds`).

* An exponential gain. The old machine has used at least `2 ^ k` of the
  resource where the new one uses a polynomial in `k`.
* A polynomial gain. The old machine has used at least
  `(k + 1) ^ gain * hi k` with `gain` positive, so the ratio grows without
  bound.

Since the size of a member is polynomial in its rank, `2 ^ k` is exponential
in a root of the size of the input. `Improves kind Old New b C` is the
statement for two machines. `Advances` is `Improves` for the whole rung (its
engine at the kernel of the language, run on the preprocessed input),
together with a recorded bound on the cost of preprocessing.

## Direction

A relation can be asked for from either end, and what it costs must not
depend on which end the query was written from. There are two ways to write a
query the other way round: `conv q`, in the same program, and the mirror image
`q.dual` in the mirrored program, in which every span is swapped and every
sequence reversed. `C.conv` and `C.mirror` are the machine `C` run on those,
with every answer swapped back, so both are machines for the original query.
`DirectionFree C p` says that `C` and each of them are never worse than the
other within `p`. Weight does not depend on the direction an expression is
written in, so the levels of a query and of its converse are the same levels
the other way round.

## Admission

A rung is admitted above the rung below it by a proof of `Admits κ kind`, at
a kernel rung `κ` (`Trusted/Kernel.lean`), and by nothing else.

* It is not a trade (`neverWorse`). On every program and at every level it
  finishes what the rung below has finished, and reports that it is done
  where the rung below does, having paid no more than a bound on what the
  rung below has paid. The bound depends on the kind of win
  (`Bounds.worse`). A rung admitted by an exponential win may be a
  polynomial worse elsewhere. A rung admitted by a polynomial win stays
  within a constant factor, with no term in the size of the input: with a
  polynomial allowed, one rung could gain a polynomial on a class and lose
  one elsewhere, and the next do the reverse, for ever.
* It is a strict improvement: it advances on the rung below by a win of the
  stated kind on a class (`Advances`).
* The cost of a relation forward and backward is comparable: its cost does
  not depend on direction, within a polynomial whose numerals its
  specification writes out (`direction`).
A rung admitted by a win in space is held to the same first clause, in time,
so it does not buy space with time beyond that bound.

`Ladder κ base G` (`Trusted/Properties.lean`, where the laws are stated) is
the ladder itself: the base, and each rung admitted above the rung below it.
Every rung of a ladder, the base included, has the laws and reports levels
truly.

What carries a gain upward is the first clause. A rung above stays within
its bound of the rung that made a gain, on the members of that gain's class
as on every program. Rungs admitted by polynomial wins lose at most a
constant factor each, so they give back no gain whose ratio is unbounded. A
rung admitted by an exponential win may lose a polynomial, so it may give
back the gain of an earlier polynomial rung; nothing here forbids that.
-/
import RwLog.Trusted.Engine

namespace RwLog

/-! ## Costed runtimes -/

/-- A small-step machine whose step is a charged computation. Building its
first state from the program and the query is a charged computation too:
whatever a machine does before its first step is paid for by every answer. -/
structure CostedRuntime where
  Ans : Type
  [answer : Answer Ans]
  State : Type
  init : Program → Rel → Cost State
  step : State → Cost (StepOf Ans State)
  /-- The cells of a state: what the machine holds between two steps. -/
  live : State → Nat

attribute [instance] CostedRuntime.answer

namespace CostedRuntime

variable (C : CostedRuntime)

/-- The state the machine starts in. -/
def start (P : Program) (q : Rel) : C.State := (C.init P q).val

/-- The machine with the ticks forgotten. -/
def runtime : Runtime where
  Ans := C.Ans
  State := C.State
  init := C.start
  step s := (C.step s).val

/-- The ticks spent in the first `n` steps. A finished machine spends
nothing more. -/
def spent : C.State → Nat → Nat
  | _, 0 => 0
  | s, n + 1 =>
    (C.step s).ticks + match (C.step s).val with
      | .emit _ s' => spent s' n
      | .progress _ s' => spent s' n
      | .done _ => 0

/-- The ticks paid on `q` by the end of the first `n` steps: building the
first state, and the steps. -/
def paid (P : Program) (q : Rel) (n : Nat) : Nat := (C.init P q).ticks + C.spent (C.start P q) n

/-- The most cells live at one moment of the first `n` steps from the state
`s`. Between two steps the cells of the state are live (`live`). While a step
runs, the cells of the state it started from are live and so is what the step
has allocated (its `peak`). What a step allocated and its next state does not
hold is live no longer when the step is over. -/
def peakFrom : C.State → Nat → Nat
  | s, 0 => C.live s
  | s, n + 1 =>
    max (C.live s + (C.step s).peak) (match (C.step s).val with
      | .emit _ s' => peakFrom s' n
      | .progress _ s' => peakFrom s' n
      | .done _ => 0)

/-- The space used on `q` by the end of the first `n` steps: the most cells
live at one moment, counting the building of the first state. -/
def space (P : Program) (q : Rel) (n : Nat) : Nat :=
  max (C.init P q).peak (C.peakFrom (C.start P q) n)

theorem peakFrom_mono (s : C.State) (n : Nat) : C.peakFrom s n ≤ C.peakFrom s (n + 1) := by
  induction n generalizing s with
  | zero => exact (Nat.le_add_right _ _).trans (le_max_left _ _)
  | succ n ih =>
    simp only [peakFrom]
    cases (C.step s).val with
    | emit _ s' => exact max_le_max le_rfl (ih s')
    | progress _ s' => exact max_le_max le_rfl (ih s')
    | done _ => exact le_rfl

/-- The space used never shrinks as the run goes on. -/
theorem space_mono (P : Program) (q : Rel) {n m : Nat} (h : n ≤ m) :
    C.space P q n ≤ C.space P q m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    exact ih.trans (max_le_max le_rfl (C.peakFrom_mono _ _))

end CostedRuntime

/-! ## Finishing a level -/

/-- A resource: what a machine has used on an input by the end of its first
`n` steps. -/
abbrev Meter := (C : CostedRuntime) → Program → Rel → Nat → Nat

/-- Time: the ticks paid. -/
def Meter.time : Meter := fun C => C.paid

/-- Space: the most cells live at any moment so far. A cell a machine has
let go of is not counted from the end of the step in which it let go. -/
def Meter.space : Meter := fun C => C.space

/-- What a gain is a gain in. -/
inductive Resource where
  | time
  | space
  deriving DecidableEq, Repr

/-- The meter of a resource. -/
def Resource.meter : Resource → Meter
  | .time => Meter.time
  | .space => Meter.space

namespace CostedRuntime

variable (C : CostedRuntime)

/-- The machine has finished level `c` of `q` within `n` steps: it has
reported a level `c` or higher, or that it is done. -/
def Finished (P : Program) (q : Rel) (c n : Nat) : Prop :=
  C.runtime.Finished (C.start P q) c n

/-- The machine has used at most `b` of the resource by some step by which
it has finished level `c` of `q`. -/
def FinishesUsing (μ : Meter) (P : Program) (q : Rel) (c b : Nat) : Prop :=
  ∃ n, C.Finished P q c n ∧ μ C P q n ≤ b

/-- The machine has paid at most `b` ticks by some step at which it has
reported that it is done. -/
def ExhaustsWithin (P : Program) (q : Rel) (b : Nat) : Prop :=
  ∃ n, C.runtime.Halts (C.start P q) n ∧ C.paid P q n ≤ b

end CostedRuntime

/-! ## Never worse -/

/-- `New` is never worse than `Old`, in time, within `p`: on every
well-formed input and for every number of steps of `Old`, every level `c`
that `Old` has finished is finished by `New` having paid at most `p` of what
`Old` has paid and of the size of the input and `c`; and if `Old` has
reported that it is done then `New` reports that it is done having paid at
most `p` of what `Old` has paid and of the size of the input. -/
def NeverWorse (Old New : CostedRuntime) (p : Nat → Nat → Nat) : Prop :=
  ∀ P q, P.WellFormed q → ∀ n,
    (∀ c, Old.Finished P q c n →
      New.FinishesUsing Meter.time P q c (p (Old.paid P q n) (P.size + q.size + c))) ∧
    (Old.runtime.Halts (Old.start P q) n →
      New.ExhaustsWithin P q (p (Old.paid P q n) (P.size + q.size)))

/-- The numerals of a polynomial bound: a coefficient and a degree. -/
structure PolyBound where
  coeff : Nat
  deg : Nat

/-- The bound `coeff * (c + n + 1) ^ deg`, for what the other machine has
paid `c` and the size `n`. -/
def PolyBound.fn (d : PolyBound) (c n : Nat) : Nat := d.coeff * (c + n + 1) ^ d.deg

/-! ## Direction -/

namespace CostedRuntime

variable (C : CostedRuntime)

/-- `C` run on the mirror image of the query in the mirrored program, with
every answer swapped back: a machine for the original query. -/
def mirror : CostedRuntime where
  Ans := C.Ans
  State := C.State
  init P q := C.init P.dual q.dual
  step s := ⟨(C.step s).val.swap, (C.step s).ticks, (C.step s).peak, (C.step s).held,
    (C.step s).held_le⟩
  live := C.live

/-- `C` run on the converse of the query, with every answer swapped back: a
machine for the original query. -/
def conv : CostedRuntime where
  Ans := C.Ans
  State := C.State
  init P q := C.init P (.conv q)
  step s := ⟨(C.step s).val.swap, (C.step s).ticks, (C.step s).peak, (C.step s).held,
    (C.step s).held_le⟩
  live := C.live

end CostedRuntime

/-- The cost of `C` does not depend on the direction a query is written in,
within `p`: `C` and `C` run on the mirror image are each never worse than the
other within `p`, and so are `C` and `C` run on the converse. -/
structure DirectionFree (C : CostedRuntime) (p : Nat → Nat → Nat) : Prop where
  toMirror : NeverWorse C C.mirror p
  ofMirror : NeverWorse C.mirror C p
  toConv : NeverWorse C C.conv p
  ofConv : NeverWorse C.conv C p

/-! ## Classes -/

/-- A class of inputs. All three components are functions, so membership is
decided, and the rank and the level of a member are computed. -/
structure ProgClass where
  /-- Is the input a member? -/
  mem : Program → Rel → Bool
  /-- The number a gain on the class is stated in. -/
  rank : Program → Rel → Nat
  /-- The level of the member the comparison is about. -/
  level : Program → Rel → Nat

/-- The facts about a class that mention no machine. `size` bounds the size
of a member by its rank. -/
structure ProgClass.Proper (C : ProgClass) (size : Nat → Nat) : Prop where
  wf : ∀ P r, C.mem P r → P.WellFormed r
  size_le : ∀ P r, C.mem P r → P.size + r.size ≤ size (C.rank P r)
  /-- There are members of every rank or more. -/
  unbounded : ∀ k, ∃ P r, C.mem P r ∧ k ≤ C.rank P r

/-! ## A win on a class -/

/-- `New` wins over `Old` on the class `C` in the resource `ρ`: on a member
of rank `k`, `New` finishes the member's level having used at most `hi k`,
and `Old` has used at least `lo k` at any step by which it has
finished it. -/
structure WinsOn (ρ : Resource) (Old New : CostedRuntime) (C : ProgClass)
    (lo hi : Nat → Nat) : Prop where
  above : ∀ P r, C.mem P r → New.FinishesUsing ρ.meter P r (C.level P r) (hi (C.rank P r))
  below : ∀ P r, C.mem P r → ∀ n, Old.Finished P r (C.level P r) n →
    lo (C.rank P r) ≤ ρ.meter Old P r n

/-! ## The kinds of win -/

/-- How large a gain is. -/
inductive Gap where
  /-- The old machine uses `2 ^ k` where the new one uses a polynomial. -/
  | exponential
  /-- The old machine uses `(k + 1) ^ gain` times what the new one uses. -/
  | polynomial
  deriving DecidableEq, Repr

/-- The kind of win that admits a rung: a gain of some size in some
resource. -/
structure Kind where
  resource : Resource
  gap : Gap
  deriving DecidableEq, Repr

/-- The numerals of an improvement. -/
structure Bounds where
  /-- The size of a member of rank `k`. -/
  sizeCoeff : Nat
  sizeDeg : Nat
  /-- What the new machine uses on a member of rank `k`. -/
  hiCoeff : Nat
  hiDeg : Nat
  /-- The degree of a polynomial win; an exponential win does not use it. -/
  gain : Nat
  /-- What the new machine may pay more than the old one on any program: a
  coefficient, and for an exponential win a degree. -/
  worseCoeff : Nat
  worseDeg : Nat

namespace Bounds

/-- The bound `sizeCoeff * (k + 1) ^ sizeDeg` on the size of a member of
rank `k`. -/
def size (b : Bounds) (k : Nat) : Nat := b.sizeCoeff * (k + 1) ^ b.sizeDeg

/-- The bound `hiCoeff * (k + 1) ^ hiDeg` on what the new machine uses on a
member of rank `k`. -/
def hi (b : Bounds) (k : Nat) : Nat := b.hiCoeff * (k + 1) ^ b.hiDeg

/-- What the old machine has used at least, on a member of rank `k`. For a
polynomial win it is `(k + 1) ^ gain` times the new machine's bound;
otherwise `2 ^ k`. -/
def lo (b : Bounds) : Gap → Nat → Nat
  | .polynomial, k => (k + 1) ^ b.gain * b.hi k
  | .exponential, k => 2 ^ k

/-- What the new machine may pay on any program, for what the old machine has
paid `c` and the size `n`. A rung admitted by an exponential win may be a
polynomial worse elsewhere: `worseCoeff * (c + n + 1) ^ worseDeg`. A rung
admitted by a polynomial win may not trade: it stays within a constant
factor, `worseCoeff * (c + 1)`, with no term in the size. -/
def worse (b : Bounds) : Gap → Nat → Nat → Nat
  | .exponential, c, n => b.worseCoeff * (c + n + 1) ^ b.worseDeg
  | .polynomial, c, _ => b.worseCoeff * (c + 1)

end Bounds

/-- `New` improves on `Old` by a win of the given kind, on the class `C`,
with the numerals `b`: the class is proper with members of size at most
`b.size`; and `New` wins over `Old` on `C`, in the resource of the kind, with
`Old` at `b.lo kind.gap` or more and `New` within `b.hi`. The ratio of a
polynomial win grows. -/
structure Improves (kind : Kind) (Old New : CostedRuntime) (b : Bounds) (C : ProgClass) :
    Prop where
  proper : C.Proper b.size
  grows : kind.gap = .polynomial → 0 < b.gain
  wins : WinsOn kind.resource Old New C (b.lo kind.gap) b.hi

/-! ## Engines

A costed machine that is admitted to the ladder is not written in `Cost`. It
is written once for every derivation kernel (`Trusted/Kernel.lean`), and its
cost is what that text spends at a kernel. It is handed the root node of the
normal form of the query, and what it emits are answers of the kernel. -/

/-- What a state holds, as the things that are counted: representatives,
nodes, answers and numbers. -/
structure Holding (S N A : Type) where
  reps : List S
  nodes : List N
  answers : List A
  words : List Nat

/-- A machine written against an arbitrary derivation kernel: its states over
types of spans, nodes and answers, how it builds its first state from the
root node, and its step.

An engine does not get to say how much space its state takes. It says what
its state holds (`held`), and the state is determined by that (`held_inj`):
two states that hold the same are the same state. So there is nothing in a
state that is not counted, and an engine uses less space only by holding
less. -/
structure Engine where
  State : Type → Type → Type → Type
  init : {S N A : Type} → {M : Type → Type} → [DerivationKernel S N A M] → N → M (State S N A)
  step : {S N A : Type} → {M : Type → Type} → [DerivationKernel S N A M] →
    State S N A → M (StepOf A (State S N A))
  held : {S N A : Type} → State S N A → Holding S N A
  held_inj : ∀ (S N A : Type), Function.Injective (@held S N A)

/-- The state of an engine at a kernel of a constraint domain `dom`, whose
type of representatives `R S` depends on the sorts: the program, the root
node, and the engine's own state at the derivation kernel of that program. -/
structure Engine.StateAt (E : Engine) {R : Sorts → Type} [∀ S, Answer (R S)]
    (dom : ∀ S, Domain (R S)) where
  P : Program
  root : Rel
  st : E.State (R P.sorts) Rel (Ans (dom P.sorts) P)

/-- The representative of an answer of the root goal; nothing for an answer
of another goal. -/
def Ans.rootSpan {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program} (root : Rel)
    (a : Ans D P) : Option R :=
  if a.goal = ⟨none, root, none⟩ then some a.span else none

/-- What the machine reports of a step of the engine: of the answers it
emits or stands by in its final report, those of the root goal, as
representatives with the sorts they are representatives for, at one tick for
each answer looked at. A report of a level is passed on as it is. -/
def Engine.report (E : Engine) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
    (dom : ∀ S, Domain (R S)) (P : Program) (root : Rel) :
    StepOf (Ans (dom P.sorts) P) (E.State (R P.sorts) Rel (Ans (dom P.sorts) P)) →
      Cost (StepOf ((S : Sorts) × R S) (E.StateAt dom))
  | .emit as st' => do
    Cost.tick as.length
    pure (.emit ((as.filterMap (Ans.rootSpan root)).map (Sigma.mk P.sorts)) ⟨P, root, st'⟩)
  | .progress n st' => pure (.progress n ⟨P, root, st'⟩)
  | .done final => do
    Cost.tick final.length
    pure (.done ((final.filterMap (Ans.rootSpan root)).map (Sigma.mk P.sorts)))

/-- The cells of a number a state holds: one, and one for each time it can
be halved. -/
def wordCells (w : Nat) : Nat := 1 + Nat.log2 w

/-- The cells of a node a state holds: its identifier, and one for each of
its members. -/
def Charged.nodeCells (n : Rel) : Nat := 1 + Charged.members n.view

/-- The cells of a boundary, for representatives of `cells` cells: nothing
for an absent one. -/
def boundCells {R : Type} (cells : R → Nat) : Option R → Nat
  | none => 0
  | some r => cells r

/-- The cells of an answer a state holds, for representatives of `cells`
cells: its representative, and its goal. -/
def Ans.cells {R : Type} [Answer R] {D : Domain R} {P : Program} (cells : R → Nat)
    (a : Ans D P) : Nat :=
  cells a.span + boundCells cells a.goal.lb + Charged.nodeCells a.goal.node +
    boundCells cells a.goal.rb

/-- The cells of a state of an engine, for representatives of `cells` cells:
the program and the root node, and everything the engine's own state holds
(`Engine.held`). Two things held are counted apart, though a machine might
hold a part of both once. -/
def Engine.liveAt (E : Engine) {R : Sorts → Type} [∀ S, Answer (R S)]
    (dom : ∀ S, Domain (R S)) (cells : ∀ S, R S → Nat) (s : E.StateAt dom) : Nat :=
  s.P.size + s.root.size + ((E.held s.st).reps.map (cells s.P.sorts)).sum +
    ((E.held s.st).nodes.map Charged.nodeCells).sum +
    ((E.held s.st).answers.map (Ans.cells (cells s.P.sorts))).sum +
    ((E.held s.st).words.map wordCells).sum

/-- The engine at a constraint domain and a kernel that returns what the
domain returns: a machine with the cost that kernel charges. The type of
representatives, the domain and its kernel are given for the sorts of each
program: which values are canonical depends on the sorts declared, so one
type for every program could not satisfy the laws of a domain. An answer of
the machine is a representative with the sorts it is a representative for
(`Answer` of a dependent pair, `Trusted/Runtime.lean`).

Building the first state brings the program and the query to their normal
form (`Charged.load`) and runs the engine's `init` on the root node. A step
is the engine's step, reported by `Engine.report`.

The cells of a state are counted with representatives of `cells` cells
(`Engine.liveAt`). Where no size of a representative is given, each counts
one cell. -/
def Engine.costedAt (E : Engine) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
    (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
    (cells : ∀ S, R S → Nat := fun _ _ => 1) :
    CostedRuntime where
  Ans := (S : Sorts) × R S
  State := E.StateAt dom
  init P q := do
    let root ← Charged.load P q
    let st ← @Engine.init E (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
      (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P) root
    pure ⟨P, root, st⟩
  step s :=
    @Engine.step E (R s.P.sorts) Rel (Ans (dom s.P.sorts) s.P) Cost
      (DerivationKernel.over (dom s.P.sorts) (K s.P.sorts) (hK s.P.sorts) s.P) s.st >>=
      E.report dom s.P s.root
  live := E.liveAt dom cells

/-- The engine at a kernel rung: a machine with the cost that rung
charges, and representatives of the size that rung gives them. -/
def Engine.costed (E : Engine) (κ : KernelRung) : CostedRuntime :=
  E.costedAt κ.dom κ.kernel κ.refines κ.cells

/-! ## One orientation of the input

An input has a mirror image: the mirrored query in the mirrored program
(`ProgramOf.dual`), which relates the same pairs the other way round. So does
a query alone: its converse. A machine may be run on one chosen member of
this family of four inputs, with what it shows swapped when the member
relates the pairs the other way round. The choice depends on the normal
forms only, and it is the same choice whichever of the four it is made from,
so the run on an input and the run on its mirror image are one run of the
machine, shown twice.

The four inputs are not always four. When the least of them stands for the
input and for its mirror image at once, there is no choice to make: the
relation is its own converse, and the machine is run on the union of that
query with its converse, a node that is its own converse. -/

/-- The program with every body in its normal form. -/
def ProgramOf.normed (P : Program) : Program :=
  { P with defs := P.defs.map fun d => (d.1, d.2.norm) }

/-- An input chosen to run: the program, the root node, and whether what the
run shows is the converse of what was asked. -/
structure Oriented where
  swap : Bool
  P : Program
  root : Rel

/-- The least of a node and a list of nodes, by the order on expressions. -/
def leastRel : Rel → List Rel → Rel
  | m, [] => m
  | m, x :: xs => leastRel (if relCmp x m = .lt then x else m) xs

/-- The candidate to run, of a first candidate and the others, each a node
with whether it relates the pairs the other way round: the least node. If it
is a candidate both ways round, the run is of the union of it with its
converse and nothing is swapped. -/
def pick (Pn : Program) (first : Rel × Bool) (rest : List (Rel × Bool)) : Oriented :=
  let m := leastRel first.1 (rest.map Prod.fst)
  let ways := ((first :: rest).filter fun x => x.1 = m).map Prod.snd
  if ways.all (· = false) then ⟨false, Pn, m⟩
  else if ways.all (· = true) then ⟨true, Pn, m⟩
  else ⟨false, Pn, (RelOf.or m m.normConv).norm⟩

/-- The input a machine is run on, of the four the input is one of.

The mirrored program is compared with the program, body by body in normal
form, and the lesser is run; if they are the same the program is its own
mirror image. The candidates for the root are then the query and its
converse; in a program that is its own mirror image the mirrored query and
its converse are candidates too. -/
def orient (P : Program) (q : Rel) : Oriented :=
  match listCmp relCmp (P.defs.map fun d => d.2.norm) (P.dual.defs.map fun d => d.2.norm) with
  | .lt => pick P.normed (q.norm, false) [((RelOf.conv q).norm, true)]
  | .gt => pick P.dual.normed (q.dual.norm, true) [((RelOf.conv q.dual).norm, false)]
  | .eq => pick P.normed (q.norm, false)
      [((RelOf.conv q).norm, true), (q.dual.norm, true), ((RelOf.conv q.dual).norm, false)]

/-- Choosing the input to run: the program and the query are brought to
their normal form four times and compared, at the charge of `Charged.load`
for each. The charge is the same for an input and for its mirror image. -/
def Charged.orient (P : Program) (q : Rel) : Cost Oriented :=
  Charged.op (RwLog.orient P q) (4 * (P.size + q.size + 1) ^ 2) (8 * (P.size + q.size + 1))

/-- What a step shows, the other way round if the run is of the mirror
image. -/
def StepOf.shownAs {A S : Type} [Answer A] (swap : Bool) : StepOf A S → StepOf A (Bool × S)
  | .emit as s => .emit (if swap then as.map Answer.swap else as) (swap, s)
  | .progress n s => .progress n (swap, s)
  | .done final => .done (if swap then final.map Answer.swap else final)

/-- A machine run on one orientation of its input (`orient`): its first
state is the machine's first state on the chosen input, and what a step
shows is swapped when the chosen input relates the pairs the other way
round. -/
def CostedRuntime.oriented (C : CostedRuntime) : CostedRuntime where
  Ans := C.Ans
  State := Bool × C.State
  init P q := do
    let o ← Charged.orient P q
    let s ← C.init o.P o.root
    pure (o.swap, s)
  step s := do
    let r ← C.step s.2
    pure (r.shownAs s.1)
  live s := 1 + C.live s.2

/-! ## Whole rungs

A rung is a preprocessor followed by a machine. Its run-time cost is the cost
of its machine on the preprocessed input, compared on the original input, and
the cost of preprocessing is recorded beside it: any preprocessing is allowed,
and a reader sees what it costs. What a machine costs is what it spends at a
kernel rung, and two rungs are compared at the same one. -/

/-- Preprocessors, run one after another (`Preprocessor.runAll`), followed by
an engine, run on the input as it is given or on one orientation of it
(`CostedRuntime.oriented`). -/
structure CostedRung where
  pre : List Preprocessor
  eng : Engine
  oriented : Bool := false

namespace CostedRung

variable (G : CostedRung) (κ : KernelRung)

/-- The rung's machine with its cost at a kernel rung. -/
def rt : CostedRuntime :=
  if G.oriented then (G.eng.costed κ).oriented else G.eng.costed κ

/-- The rung with the ticks forgotten. -/
def rung : Rung := ⟨G.pre, (G.rt κ).runtime⟩

/-- The rung as one machine on the original input: its first state is the
machine's first state on the preprocessed input, at the machine's charge. The
ticks of preprocessing are not counted here (`Advances.preCost` records
them). -/
def machine (A : ArtifactStore) : CostedRuntime where
  Ans := (G.rt κ).Ans
  State := (G.rt κ).State
  init P q := (G.rt κ).init (Preprocessor.runAll κ G.pre A P q).val.1
    (Preprocessor.runAll κ G.pre A P q).val.2.1
  step := (G.rt κ).step
  live := (G.rt κ).live

end CostedRung

/-- The rung `New` advances on `Old` at the kernel rung `κ` by a win of the
given kind: whatever the artifact store, it improves on `Old` at run time on
the class `C` with the numerals `b`, and preprocessing an input of size `n`
costs at most `pre n` ticks. `pre` is any explicit function: it is recorded,
not capped. -/
structure Advances (κ : KernelRung) (kind : Kind) (Old New : CostedRung) (b : Bounds) (pre : Nat → Nat)
    (C : ProgClass) : Prop where
  improves : ∀ A, Improves kind (Old.machine κ A) (New.machine κ A) b C
  preCost : ∀ A P q, P.WellFormed q → (Preprocessor.runAll κ New.pre A P q).ticks ≤ pre (P.size + q.size)

/-! ## Admission -/

/-- The rung `New` is admitted above `Old` at the kernel rung `κ` by a win of
the given kind. Whatever the artifact store: it advances on `Old` by the win;
on every program and at every level it finishes what `Old` has finished, and
reports that it is done where `Old` does, having paid at most
`b.worse kind.gap` of what `Old` has paid, which is a polynomial for an
exponential win and a constant factor for a polynomial win; and its cost does
not depend on direction, within the polynomial `d`. -/
structure Admits (κ : KernelRung) (kind : Kind) (Old New : CostedRung) (b : Bounds)
    (d : PolyBound) (pre : Nat → Nat) (C : ProgClass) : Prop
    extends Advances κ kind Old New b pre C where
  neverWorse : ∀ A, NeverWorse (Old.machine κ A) (New.machine κ A) (b.worse kind.gap)
  direction : ∀ A, DirectionFree (New.machine κ A) d.fn

end RwLog
