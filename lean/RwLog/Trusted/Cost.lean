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

## Improvement

`Simulates Old New p`: every pair is covered by `New` at a cost bounded by
the explicit function `p` of the cost at which `Old` covers it and of the size
of the input, and likewise for exhaustion when `Old` halts. Nothing here
depends on either machine halting.

`Separates Old New fam tgt size lo hi`: the input `fam k` has size at most
`size k`; every pair of the target `tgt k` (a nonempty set of ground pairs) is
covered by `New` within `hi k` ticks; and `Old` has paid at least `lo k` ticks
before covering any of them. The inputs of the family need not halt on either
machine.

A rung improves on its predecessor when it simulates it with a polynomial `p`
and is separated from it by a family with `size` and `hi` polynomial and `lo`
exponential, all given as explicit numerals. `Improves Old New b fam tgt` is
that statement: `b : Bounds` holds the numerals (a coefficient and a degree
for each polynomial), the simulation bound is `b.sim`, the family has size at
most `b.size k`, `New` covers the targets within `b.hi k` and `Old` has paid
at least `2 ^ k`. Since the size of `fam k` is polynomial in `k`, `2 ^ k` is
exponential in a root of the size of the input. `Advances` is `Improves` for
the whole rung (its engine at the kernel of the language, run on the
preprocessed input) for bounds its specification writes out, together with a
recorded bound on the cost of preprocessing.

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

A rung is admitted by a proof of `Admits`, and by nothing else: it advances
on its predecessor (`Advances`), and its cost does not depend on direction,
within a polynomial whose numerals its specification writes out. `Simulates`
and `Separates` with other functions do not admit it, and neither does an
improvement that holds from one end only.

`SeparatesExhaustion` is the same comparison for the report of exhaustion
instead of answers. It is the special case for the rare queries that halt: it
is recorded where it holds, and it does not admit a rung.
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

/-! ## Improvement -/

/-- `New` simulates `Old` within `p`: for every well-formed input and every
number of steps of `Old`, every pair that `Old` has covered in a model of the
theory is covered by `New` within `p` of what `Old` has paid and of the
input's size, and if `Old` has halted then `New` halts within the same
bound. -/
def Simulates (Old New : CostedRuntime) (p : Nat → Nat → Nat) : Prop :=
  ∀ P q, P.WellFormed q → ∀ n,
    (∀ M, P.theory.Model M → ∀ x, Old.Covered P q M x n →
      New.CoversWithin P q M x (p (Old.paid P q n) (P.size + q.size))) ∧
    (Old.runtime.Halts (Old.start P q) n →
      New.ExhaustsWithin P q (p (Old.paid P q n) (P.size + q.size)))

/-- `New` is separated from `Old` on a family of well-formed inputs of size
at most `size k` whose theories have a model, by the nonempty sets of ground
pairs `tgt k`: in every model, `New` covers every pair of `tgt k` within
`hi k` ticks, and `Old` has paid at least `lo k` ticks at any step at which it
has covered one. Neither machine has to halt. -/
def Separates (Old New : CostedRuntime) (fam : Nat → Program × Rel) (tgt : Nat → PRel)
    (size lo hi : Nat → Nat) : Prop :=
  ∀ k, (fam k).1.WellFormed (fam k).2 ∧ (fam k).1.size + (fam k).2.size ≤ size k ∧
    (∃ M, (fam k).1.theory.Model M) ∧ (tgt k).Nonempty ∧
    ∀ M, (fam k).1.theory.Model M → ∀ x ∈ tgt k,
      New.CoversWithin (fam k).1 (fam k).2 M x (hi k) ∧
      ∀ n, Old.Covered (fam k).1 (fam k).2 M x n →
        lo k ≤ Old.paid (fam k).1 (fam k).2 n

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

/-! ## Admission -/

/-- The numerals of an improvement: a coefficient and a degree for each of
the three polynomials. -/
structure Bounds where
  simCoeff : Nat
  simDeg : Nat
  sizeCoeff : Nat
  sizeDeg : Nat
  hiCoeff : Nat
  hiDeg : Nat

namespace Bounds

/-- The simulation bound `simCoeff * (c + n + 1) ^ simDeg`, for what the old
machine has paid `c` and the size of the input `n`. -/
def sim (b : Bounds) (c n : Nat) : Nat := b.simCoeff * (c + n + 1) ^ b.simDeg

/-- The bound `sizeCoeff * (k + 1) ^ sizeDeg` on the size of the `k`-th
input. -/
def size (b : Bounds) (k : Nat) : Nat := b.sizeCoeff * (k + 1) ^ b.sizeDeg

/-- The bound `hiCoeff * (k + 1) ^ hiDeg` on what the new machine pays on the
`k`-th input. -/
def hi (b : Bounds) (k : Nat) : Nat := b.hiCoeff * (k + 1) ^ b.hiDeg

end Bounds

/-- `New` improves on `Old`: it is never worse than the polynomial `b.sim`
of `Old`'s cost on any answer of any input, and on the family `fam`, whose
`k`-th member has size at most the polynomial `b.size k`, it covers the
targets within the polynomial `b.hi k` while `Old` has paid at least `2 ^ k`
before covering any of them. -/
structure Improves (Old New : CostedRuntime) (b : Bounds) (fam : Nat → Program × Rel)
    (tgt : Nat → PRel) : Prop where
  simulates : Simulates Old New b.sim
  separates : Separates Old New fam tgt b.size (fun k => 2 ^ k) b.hi

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

/-- The rung `New` advances on `Old`: whatever the artifact store, it
improves on `Old` at run time with the numerals `b`, and preprocessing an
input of size `n` costs at most `pre n` ticks. `pre` is any explicit
function: it is recorded, not capped. -/
structure Advances (Old New : CostedRung) (b : Bounds) (pre : Nat → Nat)
    (fam : Nat → Program × Rel) (tgt : Nat → PRel) : Prop where
  improves : ∀ A, Improves (Old.machine A) (New.machine A) b fam tgt
  preCost : ∀ A P q, P.WellFormed q → (New.pre.run A P q).ticks ≤ pre (P.size + q.size)

/-- The rung `New` is admitted above `Old`: it advances on `Old`, and
whatever the artifact store, its cost does not depend on direction, within
the polynomial `d`. -/
structure Admits (Old New : CostedRung) (b : Bounds) (d : DirBound) (pre : Nat → Nat)
    (fam : Nat → Program × Rel) (tgt : Nat → PRel) : Prop
    extends Advances Old New b pre fam tgt where
  direction : ∀ A, DirectionFree (New.machine A) d.fn

end RwLog
