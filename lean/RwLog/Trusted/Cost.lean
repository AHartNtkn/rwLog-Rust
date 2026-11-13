/-
# The cost model and what counts as an improvement

Rungs from R002 on are admitted by comparing costs, so cost has to be part of
the trusted statement and not of a submission.

## Charged computations

`Cost α` is a value together with the ticks spent computing it and the space
it used (`Trusted/CostMonad.lean`). The operations on spans, nodes and answers
and what each is charged are in `Trusted/Charged.lean` and
`Trusted/Kernel.lean`. An engine is written against an abstract kernel and can
do nothing to a span, and make no answer, except through those operations, so
what it spends is fixed by its text (`Engine`, below).

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
relates in a model of the theory, the ticks a machine has spent by the first
step at which some emitted answer relates that pair. `CoversWithin` says the
coverage latency of a pair is at most a given number of ticks. *Exhaustion
latency* is the ticks spent by the step at which the machine reports that it
is done (`ExhaustsWithin`); it is infinite on most queries.

## Resources

What a machine has used on an input by the end of its first `n` steps is a
number, and there is one such number for each resource (`Meter`). Time is the
ticks paid (`Meter.time`). Simulation and separation are written once, for any
resource.

## Improvement

`SimulatesBy μ Old New p`: every pair is covered by `New` having used at most
the explicit function `p` of what `Old` has used when it covers it and of the
size of the input, and likewise for exhaustion when `Old` halts. Nothing here
depends on either machine halting. `Simulates` is the case of time.

## Classes and contexts

A gain is shown on a class of inputs and inside larger programs
(`lean/ADMISSION.md` gives the reasons for each choice).

A class (`ProgClass`) is three computable functions on an input: `mem`
decides membership, `rank` is the number the gain is stated in, and `tgt`
lists finitely many ground pairs, the answers the comparison is about. The
facts about a class that mention no machine are `ProgClass.Proper`: members
are well formed, their theory has a model, their size is at most a stated
function of their rank, their targets are nonempty and related by the member
in every model, and the rank is unbounded over the members.

A context (`Context`) is an expression with one hole and further definitions.
Plugging a member into it gives a larger program and query, under the
member's theory. A context demands the member's answers when two things hold.
The hole is open (`Ctx.Open`): between the hole and the root there is only
`|` with anything, converse, and `;` with a single span that accepts every
term on the hole's side, so nothing tells the hole which of its answers are
wanted. And the pair that is compared needs the targets
(`Context.Demands`): in the model at hand the context relates it with the
targets in the hole, and does not relate it with everything the member
relates except the targets.

`SeparatesOn μ Old New C lo hi ctx`: on every member of `C`, of rank `k`,
`New` covers every target having used at most `hi k`; and in every open
context, for every pair the context demands, `Old` has used at least `lo k`
at any step at which it has covered the pair, and `New` covers it having used
at most `ctx (hi k) res n`, where `n` is the size of the context alone and
`res` is the residue: what `New` itself uses to cover the pair when the hole
holds the targets written out (`RelOf.ofPairs`). The residue is what the rest
of the context costs. Neither machine has to halt.

## Three kinds of win

A rung improves on its predecessor in one of three ways (`Kind`), and the
numerals of the improvement are explicit (`Bounds`).

* Exponential in time. The old machine has paid at least `2 ^ k`; the new one
  simulates it within a polynomial, and the bound in context is a polynomial.
* Polynomial in time. The old machine has paid at least
  `(k + 1) ^ gain * hi k` with `gain` positive, so the ratio grows without
  bound. The new machine simulates the old one within a constant factor,
  `simCoeff * (c + 1)`, with no term in the size of the input: a gain of
  unbounded ratio can then never be given back by later polynomial rungs. The
  bound in context is linear in `hi k` and in the residue.
* Space. As exponential in time, with space in place of ticks in the
  separation, and the old machine simulated within a polynomial both in ticks
  and in space.

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

## Admission

A rung is admitted by a proof of `Admits kind`, and by nothing else: it
advances on its predecessor by a win of that kind (`Advances`), and its cost
does not depend on direction, within a polynomial whose numerals its
specification writes out. A simulation or a separation with other functions
does not admit it, and neither does a gain on a sequence of inputs that is
not a class, a gain that holds only when the input is the whole program, or
an improvement that holds from one end only.

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

/-- The most cells live at one moment of the first `n` steps, above what was
live when they started. It is the peak of the steps run one after the other
(`Cost.bind_peak`). -/
def peakFrom : C.State → Nat → Nat
  | _, 0 => 0
  | s, n + 1 =>
    max (C.step s).peak ((C.step s).held + match (C.step s).val with
      | .emit _ s' => peakFrom s' n
      | .progress _ s' => peakFrom s' n
      | .done _ => 0)

/-- The space used on `q` by the end of the first `n` steps: the most cells
live at one moment, counting the building of the first state. -/
def space (P : Program) (q : Rel) (n : Nat) : Nat :=
  max (C.init P q).peak ((C.init P q).held + C.peakFrom (C.start P q) n)

theorem peakFrom_mono (s : C.State) (n : Nat) : C.peakFrom s n ≤ C.peakFrom s (n + 1) := by
  induction n generalizing s with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [peakFrom]
    cases (C.step s).val with
    | emit _ s' => exact max_le_max le_rfl (Nat.add_le_add_left (ih s') _)
    | progress _ s' => exact max_le_max le_rfl (Nat.add_le_add_left (ih s') _)
    | done _ => exact le_rfl

/-- The space used never shrinks as the run goes on. -/
theorem space_mono (P : Program) (q : Rel) {n m : Nat} (h : n ≤ m) :
    C.space P q n ≤ C.space P q m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    exact ih.trans (max_le_max le_rfl (Nat.add_le_add_left (C.peakFrom_mono _ _) _))

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
has covered in a model of the theory is covered by `New` having used at most
`p` of what `Old` has used and of the input's size, and if `Old` has halted
then `New` halts within the same bound. -/
def SimulatesBy (μ : Meter) (Old New : CostedRuntime) (p : Nat → Nat → Nat) : Prop :=
  ∀ P q, P.WellFormed q → ∀ n,
    (∀ M, P.theory.Model M → ∀ x, Old.Covered P q M x n →
      New.CoversUsing μ P q M x (p (μ Old P q n) (P.size + q.size))) ∧
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

/-- `C` run on the converse of the query, with every answer swapped back: a
machine for the original query. -/
def conv : CostedRuntime where
  Ans := C.Ans
  State := C.State
  init P q := C.init P (.conv q)
  step s := ⟨(C.step s).val.swap, (C.step s).ticks, (C.step s).peak, (C.step s).held,
    (C.step s).held_le⟩

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
spans. It relates exactly the pairs of the list, in every model. -/
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
  model : ∀ P r, C.mem P r → ∃ M, P.theory.Model M
  nonempty : ∀ P r, C.mem P r → C.tgt P r ≠ []
  /-- In every model the member relates every target. -/
  related : ∀ P r, C.mem P r → ∀ M, P.theory.Model M → ∀ x ∈ C.tgt P r, x ∈ P.semAt M r
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

/-- The member's program with the context's definitions. The theory is the
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

/-- `New` is separated from `Old` on the class `C` in the resource `μ`.

On a member `(P, r)` of rank `k`, in every model, `New` covers every target
having used at most `hi k`.

In every context `K` whose hole is open and whose plugged input is well
formed, in every model, for every pair `y` that needs the targets: `Old` has
used at least `lo k` at any step at which it has covered `y`; and if `New`
covers `y` having used `res` when the hole holds the targets written out,
then it covers `y` having used at most `ctx (hi k) res K.size` when the hole
holds `r`.

The member alone is the context that is only a hole, so the lower bound on
`Old` holds there for every target. Neither machine has to halt. -/
structure SeparatesOn (μ : Meter) (Old New : CostedRuntime) (C : ProgClass)
    (lo hi : Nat → Nat) (ctx : Nat → Nat → Nat → Nat) : Prop where
  alone : ∀ P r, C.mem P r → ∀ M, P.theory.Model M → ∀ x ∈ C.tgt P r,
    New.CoversUsing μ P r M x (hi (C.rank P r))
  inContext : ∀ P r, C.mem P r → ∀ K : Context, K.Open →
    (K.program P).WellFormed (K.query r) → ∀ M, P.theory.Model M →
    ∀ y, K.Demands P r M {x | x ∈ C.tgt P r} y →
      (∀ n, Old.Covered (K.program P) (K.query r) M y n →
        lo (C.rank P r) ≤ μ Old (K.program P) (K.query r) n) ∧
      (∀ res, New.CoversUsing μ (K.program P) (K.query (.ofPairs (C.tgt P r))) M y res →
        New.CoversUsing μ (K.program P) (K.query r) M y
          (ctx (hi (C.rank P r)) res K.size))

/-! ## Three kinds of win -/

/-- The kind of win that admits a rung. -/
inductive Kind where
  /-- Exponential in time. -/
  | expTime
  /-- Polynomial in time, with a ratio that grows without bound. -/
  | polyTime
  deriving DecidableEq, Repr

/-- The resource a kind of win is a gain in. -/
def Kind.meter : Kind → Meter
  | .expTime => Meter.time
  | .polyTime => Meter.time

/-- The numerals of an improvement. -/
structure Bounds where
  /-- The simulation bound: a coefficient, and a degree that a polynomial win
  does not use. -/
  simCoeff : Nat
  simDeg : Nat
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

/-- The simulation bound, for what the old machine has used `c` and the size
of the input `n`. For a polynomial win it is the constant factor
`simCoeff * (c + 1)`, whatever the size; otherwise the polynomial
`simCoeff * (c + n + 1) ^ simDeg`. -/
def sim (b : Bounds) : Kind → Nat → Nat → Nat
  | .polyTime, c, _ => b.simCoeff * (c + 1)
  | .expTime, c, n => b.simCoeff * (c + n + 1) ^ b.simDeg

/-- What the old machine has used at least, on a member of rank `k`. For a
polynomial win it is `(k + 1) ^ gain` times the new machine's bound;
otherwise `2 ^ k`. -/
def lo (b : Bounds) : Kind → Nat → Nat
  | .polyTime, k => (k + 1) ^ b.gain * b.hi k
  | .expTime, k => 2 ^ k

/-- The bound in context, for the new machine's bound on the member `h`, the
residue `res` and the size of the context `n`. For a polynomial win it is
linear in `h` and `res`, `ctxCoeff * (n + 1) ^ ctxDeg * (h + res + 1)`;
otherwise the polynomial `ctxCoeff * (h + res + n + 1) ^ ctxDeg`. -/
def ctx (b : Bounds) : Kind → Nat → Nat → Nat → Nat
  | .polyTime, h, res, n => b.ctxCoeff * (n + 1) ^ b.ctxDeg * (h + res + 1)
  | .expTime, h, res, n => b.ctxCoeff * (h + res + n + 1) ^ b.ctxDeg

end Bounds

/-- `New` improves on `Old` by a win of the given kind, on the class `C`,
with the numerals `b`: the class is proper with members of size at most
`b.size`; `New` is never worse than `b.sim kind` of `Old` on any answer of
any input; and it is separated from `Old` on `C`, in the resource of the
kind, with `Old` at `b.lo kind` or more, `New` within `b.hi` on a member and
within `b.ctx kind` in context. The ratio of a polynomial win grows. -/
structure Improves (kind : Kind) (Old New : CostedRuntime) (b : Bounds) (C : ProgClass) :
    Prop where
  proper : C.Proper b.size
  grows : kind = .polyTime → 0 < b.gain
  simulates : Simulates Old New (b.sim kind)
  separates : SeparatesOn kind.meter Old New C (b.lo kind) b.hi (b.ctx kind)

/-! ## Engines

A costed machine that is admitted to the ladder is not written in `Cost`. It
is written once for every derivation kernel (`Trusted/Kernel.lean`), and its
cost is what that text spends at a kernel. It is handed the root node of the
normal form of the query, and what it emits are answers of the kernel. -/

/-- A machine written against an arbitrary derivation kernel: its states over
types of spans, nodes and answers, how it builds its first state from the
root node, and its step. -/
structure Engine where
  State : Type → Type → Type → Type
  init : {S N A : Type} → {M : Type → Type} → [DerivationKernel S N A M] → N → M (State S N A)
  step : {S N A : Type} → {M : Type → Type} → [DerivationKernel S N A M] →
    State S N A → M (StepOf A (State S N A))

/-- The state of an engine at a kernel on the spans of the language: the
program, the root node, and the engine's own state at the derivation kernel
of that program. -/
structure Engine.StateAt (E : Engine) where
  P : Program
  root : Rel
  st : E.State Span Rel (Ans P)

/-- The span of an answer of the root goal; nothing for an answer of another
goal. -/
def Ans.rootSpan {P : Program} (root : Rel) (a : Ans P) : Option Span :=
  if a.goal = ⟨none, root, none⟩ then some a.span else none

/-- What the machine reports of a step of the engine: of the answers it
emits or stands by in its final report, those of the root goal, as spans, at
one tick for each answer looked at. A progress certificate is reported as it
is. -/
def Engine.report (E : Engine) (P : Program) (root : Rel) :
    StepOf (Ans P) (E.State Span Rel (Ans P)) → Cost (StepOf Span E.StateAt)
  | .emit as st' => do
    Cost.tick as.length
    pure (.emit (as.filterMap (Ans.rootSpan root)) ⟨P, root, st'⟩)
  | .progress n st' => pure (.progress n ⟨P, root, st'⟩)
  | .done final => do
    Cost.tick final.length
    pure (.done (final.filterMap (Ans.rootSpan root)))

/-- The engine at a kernel on the spans of the language that returns what the
specification kernel returns: a machine with the cost that kernel charges.

Building the first state brings the program and the query to their normal
form (`Charged.load`) and runs the engine's `init` on the root node. A step
is the engine's step, reported by `Engine.report`. -/
def Engine.costedAt (E : Engine) (K : Kernel Span Cost) (hK : K.Refines) : CostedRuntime where
  Ans := Span
  State := E.StateAt
  init P q := do
    let root ← Charged.load P q
    let st ← @Engine.init E Span Rel (Ans P) Cost (DerivationKernel.over K hK P) root
    pure ⟨P, root, st⟩
  step s :=
    @Engine.step E Span Rel (Ans s.P) Cost (DerivationKernel.over K hK s.P) s.st >>=
      E.report s.P s.root

/-- The engine at the specification kernel: a machine with its cost. -/
def Engine.costed (E : Engine) : CostedRuntime := E.costedAt Kernel.std Kernel.std_refines

/-! ## Whole rungs

A rung is a preprocessor followed by a machine. Its run-time cost is the cost
of its machine on the preprocessed input, compared on the original input, and
the cost of preprocessing is recorded beside it: any preprocessing is allowed,
and a reader sees what it costs. -/

/-- A preprocessor followed by an engine. -/
structure CostedRung where
  pre : Preprocessor
  eng : Engine

namespace CostedRung

variable (G : CostedRung)

/-- The rung's machine with its cost. -/
def rt : CostedRuntime := G.eng.costed

/-- The rung with the ticks forgotten. -/
def rung : Rung := ⟨G.pre, G.rt.runtime⟩

/-- The rung as one machine on the original input: its first state is the
machine's first state on the preprocessed input, at the machine's charge. The
ticks of preprocessing are not counted here (`Admits.preCost` records
them). -/
def machine (A : ArtifactStore) : CostedRuntime where
  Ans := G.rt.Ans
  State := G.rt.State
  init P q := G.rt.init (G.pre.run A P q).val.1 (G.pre.run A P q).val.2.1
  step := G.rt.step

end CostedRung

/-- The rung `New` advances on `Old` by a win of the given kind: whatever the
artifact store, it improves on `Old` at run time on the class `C` with the
numerals `b`, and preprocessing an input of size `n` costs at most `pre n`
ticks. `pre` is any explicit function: it is recorded, not capped. -/
structure Advances (kind : Kind) (Old New : CostedRung) (b : Bounds) (pre : Nat → Nat)
    (C : ProgClass) : Prop where
  improves : ∀ A, Improves kind (Old.machine A) (New.machine A) b C
  preCost : ∀ A P q, P.WellFormed q → (New.pre.run A P q).ticks ≤ pre (P.size + q.size)

/-- The rung `New` is admitted above `Old` by a win of the given kind: it
advances on `Old`, and whatever the artifact store, its cost does not depend
on direction, within the polynomial `d`. -/
structure Admits (kind : Kind) (Old New : CostedRung) (b : Bounds) (d : DirBound)
    (pre : Nat → Nat) (C : ProgClass) : Prop
    extends Advances kind Old New b pre C where
  direction : ∀ A, DirectionFree (New.machine A) d.fn

end RwLog
