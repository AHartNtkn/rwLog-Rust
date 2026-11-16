/-
# The cost model and what counts as an improvement

Rungs from R002 on are admitted by comparing costs, so cost has to be part of
the trusted statement and not of a submission.

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

## Latency

Cost is how soon answers arrive. Almost no query worth running ever reports
that it is done, so the measure cannot depend on halting, and two correct
machines may emit different answers for the same query (one general span
where the other emits several instances), so it cannot count answers either.
What is comparable is *coverage latency*: for a ground pair that the query
relates, the ticks a machine has spent by the first
step at which some emitted answer relates that pair. `CoversWithin` says the
coverage latency of a pair is at most a given number of ticks. *Exhaustion
latency* is the ticks spent by the step at which the machine reports that it
is done (`ExhaustsWithin`); it is infinite on most queries.

## Resources

What a machine has used on an input by the end of its first `n` steps is a
number, and there is one such number for each resource (`Meter`). Time is the
ticks paid (`Meter.time`) and space is the most cells live at any moment so
far (`Meter.space`). A comparison is written once, for any resource.

Between two steps the cells that are live are those of the state the machine
holds (`CostedRuntime.live`); during a step they are those of the state it
started from and what the step has allocated. So a machine that lets go of
something uses less from the next step on. An engine does not get to say how
many cells its state takes: it lists what the state holds and proves that
the state is determined by the listing (`Engine.held`, `Engine.held_inj`),
and the cells of the listing are counted here (`Engine.liveAt`).

## Comparing two machines

`SimulatesBy μ Old New p`: every pair is covered by `New` having used at most
the explicit function `p` of what `Old` has used when it covers it and of the
size of the input, and likewise for exhaustion when `Old` halts. Nothing here
depends on either machine halting. `Simulates` is the case of time. It is
what "comparable" means where two costs are asked to be comparable, as for
the two directions of a relation. An admission does not ask it of a rung
against the rung below.

## Classes and contexts

A gain is shown on a class of inputs and inside larger programs
(`lean/ADMISSION.md` gives the reasons for each choice).

A class (`ProgClass`) is three computable functions on an input: `mem`
decides membership, `rank` is the number the gain is stated in, and `tgt`
lists finitely many ground pairs, the answers the comparison is about. The
facts about a class that mention no machine are `ProgClass.Proper`: members
are well formed, their size is at most a stated function of their rank,
their targets are nonempty and related by the member, and the rank is
unbounded over the members.

A context (`Context`) is an expression with one hole and further definitions.
Plugging a member into it gives a larger program and query, with the
member's sorts. A context demands the member's answers when two things hold.
The hole is open (`Ctx.Open`): between the hole and the root there is only
`|` with anything, converse, and `;` with a single span that accepts every
term on the hole's side, so nothing tells the hole which of its answers are
wanted. And the pair that is compared needs the targets
(`Context.Demands`): in the interpretation of the sorts the context relates it with the
targets in the hole, and does not relate it with everything the member
relates except the targets.

`SeparatesOn μ Old New C lo hi ctx`: on every member of `C`, of rank `k`,
`New` covers every target having used at most `hi k`; and in every open
context, for every pair the context demands, `Old` has used at least `lo k`
at any step at which it has covered the pair, and `New` covers it having used
at most `ctx (hi k) res n`, where `n` is the size of the context alone and
`res` is the residue: what `New` itself uses to cover the pair when the hole
holds the targets written out (`RelOf.ofPairs`). The residue is what the rest
of the context costs. Neither machine has to halt. The two upper bounds on
`New` mention no other machine; they are `MeetsOn`.

## Three kinds of win

A rung improves on its predecessor by a win of some kind (`Kind`), and the
numerals of the improvement are explicit (`Bounds`).

A kind is a resource (time or space) and the size of the gain (`Gap`).

* An exponential gain. The old machine has used at least `2 ^ k` of the
  resource, and the bound in context is a polynomial.
* A polynomial gain. The old machine has used at least
  `(k + 1) ^ gain * hi k` with `gain` positive, so the ratio grows without
  bound. The bound in context is linear in `hi k` and in the residue.

Since the size of a member is polynomial in its rank, `2 ^ k` is exponential
in a root of the size of the input. `Improves kind Old New b C` is the
statement for two machines. `Advances` is `Improves` for the whole rung (its
engine at the kernel of the language, run on the preprocessed input),
together with a recorded bound on the cost of preprocessing.

Exponential wins are taken first while there are any. That is a rule for
choosing the next rung, not a clause of the statement.

## Direction

A relation can be asked for from either end, and what an answer costs must not
depend on which end the query was written from. There are two ways to write a
query the other way round: `conv q`, in the same program, and the mirror image
`q.dual` in the mirrored program, in which every span is swapped and every
sequence reversed. `C.conv` and `C.mirror` are the machine `C` run on those,
with every answer swapped back, so both are machines for the original query.
`DirectionFree C p` says that `C` and each of them simulate each other within
`p`: whenever one has covered a pair, the other covers it within `p` of what
the first has paid, and likewise for exhaustion. So no pair arrives more than
polynomially later because the query was written from the other end.

## The record of wins

No later rung may lose a gain an earlier rung made. So wins are kept on a
record, and every admission is held to every win on it. A win on record (`Win`) is the kind of an admission, its
class and its numerals. A machine keeps it within a factor `c`
(`Win.KeptBy`) when, in the resource of the win, it covers every target of a
member of rank `k` having used at most `c * hi k`, and in every open context
at most `c` times the bound in context the win was admitted with. The bound
is the recorded one, not what the rung below happens to use, so the factors
of successive rungs do not multiply.

## Admission

A rung is admitted by a proof of `Admits κ kind` over the record of the rung
below it, at a kernel rung `κ` (`Trusted/Kernel.lean`), and by nothing else.
It is a strict improvement: it advances on its predecessor by a win of that
kind (`Advances`). It loses no earlier gain: it keeps every win on the record
within a constant factor that its specification writes out. It loses no
halting: it halts on every input on which its predecessor halts. And the cost
of a relation forward and backward is comparable: its cost does not depend
on direction, within a polynomial whose numerals its specification writes
out. A separation with other functions does not admit it, and neither does a
gain on a sequence of inputs that is not a class, a gain that holds only
when the input is the whole program, an improvement that holds from one end
only, or a gain that gives back a win of an earlier rung.

Every clause is about what has been paid when an answer has arrived, or
about whether a run halts. None compares two runs step by step.

`Ladder κ base G record` (`Trusted/Properties.lean`, where the laws are
stated) is the ladder itself: the base has the empty record, and each
admission is over the whole record of the rung below and puts its own win on
it. So every rung of a ladder has every win below it at once, each within a
constant factor of the bound it was admitted with. Every rung of a ladder,
the base included, has the laws (`CostedRung.Lawful`): an admission says how
a rung costs less, and by itself it does not say that the rung is right.

`SeparatesExhaustion` is the comparison for the report of exhaustion instead
of answers, on a sequence of inputs. It is the special case for the rare
queries that halt: it is recorded where it holds, and it does not admit a
rung.
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

/-! ## Latency -/

namespace CostedRuntime

variable (C : CostedRuntime)

/-- Some answer emitted in the first `n` steps on `q` relates the pair `x`
in `M`. -/
def Covered (P : Program) (q : Rel) (M : Interp) (x : GTerm × GTerm) (n : Nat) : Prop :=
  ∃ a ∈ C.runtime.emitted (C.start P q) n, x ∈ Answer.den M a

/-- The coverage latency of `x` in `M` is at most `c`: the machine has spent
at most `c` ticks by some step at which an emitted answer relates `x`. -/
def CoversWithin (P : Program) (q : Rel) (M : Interp) (x : GTerm × GTerm) (c : Nat) : Prop :=
  ∃ n, C.Covered P q M x n ∧ C.paid P q n ≤ c

/-- The exhaustion latency is at most `c`: the machine has spent at most `c`
ticks by some step at which it has reported that it is done. -/
def ExhaustsWithin (P : Program) (q : Rel) (c : Nat) : Prop :=
  ∃ n, C.runtime.Halts (C.start P q) n ∧ C.paid P q n ≤ c

end CostedRuntime

/-! ## Resources -/

/-- A resource: what a machine has used on an input by the end of its first
`n` steps. -/
abbrev Meter := (C : CostedRuntime) → Program → Rel → Nat → Nat

/-- Time: the ticks paid. -/
def Meter.time : Meter := fun C => C.paid

/-- Space: the most cells live at any moment so far. A cell a machine has
let go of is not counted from the end of the step in which it let go. -/
def Meter.space : Meter := fun C => C.space

namespace CostedRuntime

variable (C : CostedRuntime)

/-- The machine has used at most `c` of the resource by some step at which an
emitted answer relates `x`. For time this is `CoversWithin`. -/
def CoversUsing (μ : Meter) (P : Program) (q : Rel) (M : Interp) (x : GTerm × GTerm)
    (c : Nat) : Prop :=
  ∃ n, C.Covered P q M x n ∧ μ C P q n ≤ c

/-- The machine has used at most `c` of the resource by some step at which it
has reported that it is done. For time this is `ExhaustsWithin`. -/
def ExhaustsUsing (μ : Meter) (P : Program) (q : Rel) (c : Nat) : Prop :=
  ∃ n, C.runtime.Halts (C.start P q) n ∧ μ C P q n ≤ c

end CostedRuntime

/-! ## Improvement -/

/-- `New` simulates `Old` within `p` in the resource `μ`: for every
well-formed input and every number of steps of `Old`, every pair that `Old`
has covered is covered by `New` having used at most
`p` of what `Old` has used and of the input's size, and if `Old` has halted
then `New` halts within the same bound. -/
def SimulatesBy (μ : Meter) (Old New : CostedRuntime) (p : Nat → Nat → Nat) : Prop :=
  ∀ P q, P.WellFormed q → ∀ n,
    (∀ x, Old.Covered P q P.sorts.interp x n →
      New.CoversUsing μ P q P.sorts.interp x (p (μ Old P q n) (P.size + q.size))) ∧
    (Old.runtime.Halts (Old.start P q) n →
      New.ExhaustsUsing μ P q (p (μ Old P q n) (P.size + q.size)))

/-- `New` simulates `Old` within `p` in time. -/
def Simulates (Old New : CostedRuntime) (p : Nat → Nat → Nat) : Prop :=
  SimulatesBy Meter.time Old New p

/-- The special case for inputs that halt: `New` reports that it is done
within `hi k` ticks, and `Old` has paid at least `lo k` whenever it has. This
does not admit a rung. -/
def SeparatesExhaustion (Old New : CostedRuntime) (fam : Nat → Program × Rel)
    (size lo hi : Nat → Nat) : Prop :=
  ∀ k, (fam k).1.WellFormed (fam k).2 ∧ (fam k).1.size + (fam k).2.size ≤ size k ∧
    New.ExhaustsWithin (fam k).1 (fam k).2 (hi k) ∧
    (∀ n, Old.runtime.Halts (Old.start (fam k).1 (fam k).2) n →
      lo k ≤ Old.paid (fam k).1 (fam k).2 n)

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
within `p`: `C` and `C` run on the mirror image simulate each other within
`p`, and so do `C` and `C` run on the converse. -/
structure DirectionFree (C : CostedRuntime) (p : Nat → Nat → Nat) : Prop where
  toMirror : Simulates C C.mirror p
  ofMirror : Simulates C.mirror C p
  toConv : Simulates C C.conv p
  ofConv : Simulates C.conv C p

/-- The numerals of a direction bound: a coefficient and a degree. -/
structure DirBound where
  coeff : Nat
  deg : Nat

/-- The bound `coeff * (c + n + 1) ^ deg`, for what the other machine has
paid `c` and the size of the input `n`. -/
def DirBound.fn (d : DirBound) (c n : Nat) : Nat := d.coeff * (c + n + 1) ^ d.deg

/-! ## Classes -/

/-- A ground term as a pattern. -/
def GTerm.toPat (t : GTerm) : Pat := t.rename Empty.elim

/-- The pairs of a list written out as an expression: a union of ground
spans. It relates exactly the pairs of the list, in every interpretation. -/
def RelOf.ofPairs : List (GTerm × GTerm) → Rel
  | [] => .zero
  | x :: xs => .or (.span ⟨x.1.toPat, x.2.toPat, []⟩) (ofPairs xs)

/-- A class of inputs. All three components are functions, so membership is
decided, and the rank and the targets of a member are computed. -/
structure ProgClass where
  /-- Is the input a member? -/
  mem : Program → Rel → Bool
  /-- The number a gain on the class is stated in. -/
  rank : Program → Rel → Nat
  /-- The ground pairs the comparison is about. -/
  tgt : Program → Rel → List (GTerm × GTerm)

/-- The facts about a class that mention no machine. `size` bounds the size
of a member by its rank. -/
structure ProgClass.Proper (C : ProgClass) (size : Nat → Nat) : Prop where
  wf : ∀ P r, C.mem P r → P.WellFormed r
  size_le : ∀ P r, C.mem P r → P.size + r.size ≤ size (C.rank P r)
  nonempty : ∀ P r, C.mem P r → C.tgt P r ≠ []
  /-- The member relates every target. -/
  related : ∀ P r, C.mem P r → ∀ x ∈ C.tgt P r, x ∈ P.pairs r
  /-- There are members of every rank or more. -/
  unbounded : ∀ k, ∃ P r, C.mem P r ∧ k ≤ C.rank P r

/-! ## Contexts -/

/-- An expression with one hole. -/
inductive Ctx where
  | hole
  | orL (K : Ctx) (b : Rel)
  | orR (a : Rel) (K : Ctx)
  | andL (K : Ctx) (b : Rel)
  | andR (a : Rel) (K : Ctx)
  | seqL (K : Ctx) (b : Rel)
  | seqR (a : Rel) (K : Ctx)
  | conv (K : Ctx)

namespace Ctx

/-- The expression with `r` in the hole. -/
def fill (r : Rel) : Ctx → Rel
  | hole => r
  | orL K b => .or (K.fill r) b
  | orR a K => .or a (K.fill r)
  | andL K b => .and (K.fill r) b
  | andR a K => .and a (K.fill r)
  | seqL K b => .seq (K.fill r) b
  | seqR a K => .seq a (K.fill r)
  | conv K => .conv (K.fill r)

/-- The meaning of a context in `M` as a function of the meaning `X` of its
hole, given the meaning `ρ` of each name. -/
def denAt (M : Interp) (ρ : Name → PRel) (X : PRel) : Ctx → PRel
  | hole => X
  | orL K b => K.denAt M ρ X ∪ denoteAt M ρ b
  | orR a K => denoteAt M ρ a ∪ K.denAt M ρ X
  | andL K b => K.denAt M ρ X ∩ denoteAt M ρ b
  | andR a K => denoteAt M ρ a ∩ K.denAt M ρ X
  | seqL K b => (K.denAt M ρ X).comp (denoteAt M ρ b)
  | seqR a K => (denoteAt M ρ a).comp (K.denAt M ρ X)
  | conv K => (K.denAt M ρ X).inv

/-- The size of a context: its nodes other than the hole, and the sizes of
the expressions beside the path to the hole. -/
def size : Ctx → Nat
  | hole => 0
  | orL K b => 1 + K.size + b.size
  | orR a K => 1 + a.size + K.size
  | andL K b => 1 + K.size + b.size
  | andR a K => 1 + a.size + K.size
  | seqL K b => 1 + K.size + b.size
  | seqR a K => 1 + a.size + K.size
  | conv K => 1 + K.size

end Ctx

/-- The span accepts every term on its left: its left pattern is a variable
that its store does not mention. -/
def Span.OpenLeft (s : Span) : Prop := ∃ v, s.l = .var v ∧ ∀ c ∈ s.c, v ∉ c.vars

/-- The span accepts every term on its right. -/
def Span.OpenRight (s : Span) : Prop := s.swap.OpenLeft

/-- The hole is open: nothing between it and the root restricts it. Above
the hole there is only `|` with anything on the other side, converse, and
`;` with a single span that accepts every term on the hole's side. Under `&`,
or under `;` with anything else, the other side says which answers of the
hole are wanted, so the hole is not open. -/
def Ctx.Open : Ctx → Prop
  | .hole => True
  | .orL K _ => K.Open
  | .orR _ K => K.Open
  | .conv K => K.Open
  | .seqL K (.span s) => s.OpenLeft ∧ K.Open
  | .seqR (.span s) K => s.OpenRight ∧ K.Open
  | _ => False

/-- A context: an expression with one hole, and further definitions. -/
structure Context where
  shape : Ctx
  defs : List (Name × Rel)

namespace Context

variable (K : Context)

/-- The member's program with the context's definitions. The sorts are the
member's. -/
def program (P : Program) : Program := { P with defs := P.defs ++ K.defs }

/-- The context's query with `r` in the hole. -/
def query (r : Rel) : Rel := K.shape.fill r

/-- The size of the context alone. -/
def size : Nat := K.shape.size + (K.defs.map fun d => 1 + d.2.size).sum

/-- The hole is open. -/
def Open : Prop := K.shape.Open

/-- With `(P, r)` plugged in, the pair `y` needs the pairs `X` of `r` in
`M`: the context relates `y` when the hole holds `X`, and does not when the
hole holds everything `r` relates except `X`. -/
def Demands (P : Program) (r : Rel) (M : Interp) (X : PRel) (y : GTerm × GTerm) : Prop :=
  y ∈ K.shape.denAt M ((K.program P).meaningAt M) X ∧
  y ∉ K.shape.denAt M ((K.program P).meaningAt M) ((K.program P).semAt M r \ X)

end Context

/-! ## Separation on a class, in context -/

/-- `New` meets an upper bound on the class `C` in the resource `μ`, on a
member and in context.

On a member `(P, r)` of rank `k`, `New` covers every target having used at
most `hi k`.

In every context `K` whose hole is open and whose plugged input is well
formed, for every pair `y` that needs the targets: if `New` covers `y` having
used `res` when the hole holds the targets written out, then it covers `y`
having used at most `inCtx k res K.size` when the hole holds `r`.

The machine does not have to halt, and no other machine is mentioned. -/
structure MeetsOn (μ : Meter) (New : CostedRuntime) (C : ProgClass)
    (hi : Nat → Nat) (inCtx : Nat → Nat → Nat → Nat) : Prop where
  alone : ∀ P r, C.mem P r → ∀ x ∈ C.tgt P r,
    New.CoversUsing μ P r P.sorts.interp x (hi (C.rank P r))
  inContext : ∀ P r, C.mem P r → ∀ K : Context, K.Open →
    (K.program P).WellFormed (K.query r) →
    ∀ y, K.Demands P r P.sorts.interp {x | x ∈ C.tgt P r} y →
      ∀ res, New.CoversUsing μ (K.program P) (K.query (.ofPairs (C.tgt P r)))
          P.sorts.interp y res →
        New.CoversUsing μ (K.program P) (K.query r) P.sorts.interp y
          (inCtx (C.rank P r) res K.size)

/-- `New` is separated from `Old` on the class `C` in the resource `μ`.

`New` meets the upper bound `hi` on a member of rank `k`, and
`ctx (hi k) res K.size` in a context `K` with residue `res` (`MeetsOn`).

In every context `K` whose hole is open and whose plugged input is well
formed, for every pair `y` that needs the targets, `Old` has used at least
`lo k` at any step at which it has covered `y`.

The member alone is the context that is only a hole, so the lower bound on
`Old` holds there for every target. Neither machine has to halt. -/
structure SeparatesOn (μ : Meter) (Old New : CostedRuntime) (C : ProgClass)
    (lo hi : Nat → Nat) (ctx : Nat → Nat → Nat → Nat) : Prop
    extends MeetsOn μ New C hi (fun k => ctx (hi k)) where
  below : ∀ P r, C.mem P r → ∀ K : Context, K.Open →
    (K.program P).WellFormed (K.query r) →
    ∀ y, K.Demands P r P.sorts.interp {x | x ∈ C.tgt P r} y →
      ∀ n, Old.Covered (K.program P) (K.query r) P.sorts.interp y n →
        lo (C.rank P r) ≤ μ Old (K.program P) (K.query r) n

/-! ## Three kinds of win -/

/-- How large a gain is. -/
inductive Gap where
  /-- The old machine uses `2 ^ k` where the new one uses a polynomial. -/
  | exponential
  /-- The old machine uses `(k + 1) ^ gain` times what the new one uses. -/
  | polynomial
  deriving DecidableEq, Repr

/-- What a gain is a gain in. -/
inductive Resource where
  | time
  | space
  deriving DecidableEq, Repr

/-- The meter of a resource. -/
def Resource.meter : Resource → Meter
  | .time => Meter.time
  | .space => Meter.space

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
  /-- The degree of a polynomial win; the other kinds do not use it. -/
  gain : Nat
  /-- The bound in context. -/
  ctxCoeff : Nat
  ctxDeg : Nat

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

/-- The bound in context, for the new machine's bound on the member `h`, the
residue `res` and the size of the context `n`. For a polynomial win it is
linear in `h` and `res`, `ctxCoeff * (n + 1) ^ ctxDeg * (h + res + 1)`;
otherwise the polynomial `ctxCoeff * (h + res + n + 1) ^ ctxDeg`. -/
def ctx (b : Bounds) : Gap → Nat → Nat → Nat → Nat
  | .polynomial, h, res, n => b.ctxCoeff * (n + 1) ^ b.ctxDeg * (h + res + 1)
  | .exponential, h, res, n => b.ctxCoeff * (h + res + n + 1) ^ b.ctxDeg

end Bounds

/-- `New` improves on `Old` by a win of the given kind, on the class `C`,
with the numerals `b`: the class is proper with members of size at most
`b.size`; and it is separated from `Old` on `C`, in the resource of the kind,
with `Old` at `b.lo kind.gap` or more, `New` within `b.hi` on a member and
within `b.ctx kind.gap` in context. The ratio of a polynomial win grows. -/
structure Improves (kind : Kind) (Old New : CostedRuntime) (b : Bounds) (C : ProgClass) :
    Prop where
  proper : C.Proper b.size
  grows : kind.gap = .polynomial → 0 < b.gain
  separates : SeparatesOn kind.resource.meter Old New C (b.lo kind.gap) b.hi (b.ctx kind.gap)

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
each answer looked at. A progress certificate is reported as it is. -/
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
ticks of preprocessing are not counted here (`Admits.preCost` records
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

/-! ## The record of wins

No later rung may lose a gain an earlier rung made. So every win is put on
record when it is admitted, and every later admission, of whatever kind, is
held to every win on the record. -/

/-- A win on record: the kind of the win, the class it was shown on, and the
numerals it was admitted with. What a later rung is held to are the upper
bound `b.hi` on a member and the bound in context `b.ctx kind.gap`, in the
resource of the kind. -/
structure Win where
  kind : Kind
  cls : ProgClass
  b : Bounds

/-- The machine `M` keeps the win `w` within the factor `c`: in the resource
of the win, on a member of rank `k` of its class `M` covers every target
having used at most `c * w.b.hi k`, and in every open context, for every pair
that needs the targets, at most `c` times the bound in context the win was
admitted with, at `M`'s own residue. -/
def Win.KeptBy (w : Win) (M : CostedRuntime) (c : Nat) : Prop :=
  MeetsOn w.kind.resource.meter M w.cls (fun k => c * w.b.hi k)
    (fun k res n => c * w.b.ctx w.kind.gap (w.b.hi k) res n)

/-- The rung `New` is admitted above `Old` at the kernel rung `κ` by a win of
the given kind, over the wins on `record`: it advances on `Old`; whatever the
artifact store, it halts on every input on which `Old` halts, its cost does
not depend on direction, within the polynomial `d`, and it keeps every win on
the record within the factor `keep`. -/
structure Admits (κ : KernelRung) (kind : Kind) (Old New : CostedRung) (b : Bounds)
    (d : DirBound) (pre : Nat → Nat) (C : ProgClass) (record : List Win) (keep : Nat) : Prop
    extends Advances κ kind Old New b pre C where
  halts : ∀ A P q, P.WellFormed q → (Old.machine κ A).runtime.Terminates P q →
    (New.machine κ A).runtime.Terminates P q
  direction : ∀ A, DirectionFree (New.machine κ A) d.fn
  keeps : ∀ A, ∀ w ∈ record, w.KeptBy (New.machine κ A) keep

end RwLog
