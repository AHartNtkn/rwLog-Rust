/-
# The cost model and what counts as an improvement

Rungs from R002 on are admitted by comparing costs, so cost has to be part of
the trusted statement and not of a submission.

## Charged computations

`Cost α` is a value together with the number of ticks spent computing it. A
costed engine is written in this monad, and the only way it spends ticks is by
calling a *charged primitive* of this file. Each primitive computes exactly
the kernel operation it names (its `val` is that operation by definition) and
charges a fixed function of the sizes of its arguments, and of its result
when it builds one:

* composing or conjoining two spans: the sizes of both spans and of the result;
* testing whether a chain of spans composes, without building the result: the
  sizes of the spans;
* a coverage test: the sizes of both spans;
* simplifying a span by a theory: for each instantiation stage, the size of
  the theory times the size of the span and of the closure of its store.

List traversal over data that was already charged is free. A term is charged
by its size wherever it is used, never by one, so sharing or interning cannot
hide work.

A computation can be run under a budget (`Cost.within`): if it needs no more
than the budget it is run and charged as usual, and otherwise the whole budget
is spent and nothing is learned from it. This is the one way to give up on a
computation, and giving up is never cheaper than the budget allowed.

## Costed runtimes

A `CostedRuntime` is a small-step machine whose step is a charged computation.
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
exponential, all given as explicit numerals.

`SeparatesExhaustion` is the same comparison for the report of exhaustion
instead of answers. It is the special case for the rare queries that halt: it
is recorded where it holds, and it does not admit a rung.
-/
import RwLog.Trusted.Engine
import RwLog.Kernel.Refute
import RwLog.SpanLayer.Coverage

namespace RwLog

/-! ## Sizes -/

def Store.size (c : Store) : Nat := (c.map Term.size).sum

def Span.size (s : Span) : Nat := s.l.size + s.r.size + Store.size s.c

/-- The size of an expression: its nodes, with each span counted by its
size. -/
def Rel.size : Rel → Nat
  | .zero => 1
  | .span s => 1 + s.size
  | .or a b => 1 + a.size + b.size
  | .and a b => 1 + a.size + b.size
  | .seq a b => 1 + a.size + b.size
  | .conv a => 1 + a.size
  | .call _ => 1

def Body.size : Body → Nat
  | .fail => 1
  | .conj eqs cs => 1 + (eqs.map fun e => e.1.size + e.2.size).sum + Store.size cs

def TRule.size (ρ : TRule) : Nat := Store.size ρ.heads + ρ.body.size

def Theory.size (T : Theory) : Nat := (T.map TRule.size).sum

def Program.size (P : Program) : Nat := (P.defs.map fun d => 1 + d.2.size).sum + P.theory.size

/-! ## Charged computations -/

/-- A value and the ticks spent computing it. -/
structure Cost (α : Type) where
  val : α
  ticks : Nat

namespace Cost

instance : Monad Cost where
  pure a := ⟨a, 0⟩
  bind m f := let r := f m.val; ⟨r.val, m.ticks + r.ticks⟩

/-- Spend `n` ticks. -/
def tick (n : Nat) : Cost Unit := ⟨(), n⟩

@[simp] theorem pure_val {α : Type} (a : α) : (pure a : Cost α).val = a := rfl
@[simp] theorem pure_ticks {α : Type} (a : α) : (pure a : Cost α).ticks = 0 := rfl
@[simp] theorem bind_val {α β : Type} (m : Cost α) (f : α → Cost β) :
    (m >>= f).val = (f m.val).val := rfl
@[simp] theorem bind_ticks {α β : Type} (m : Cost α) (f : α → Cost β) :
    (m >>= f).ticks = m.ticks + (f m.val).ticks := rfl
@[simp] theorem tick_val (n : Nat) : (tick n).val = () := rfl
@[simp] theorem tick_ticks (n : Nat) : (tick n).ticks = n := rfl

/-- Run `m` with a budget of `b` ticks. If `m` needs no more than `b` it
runs and is charged as usual; otherwise `b` ticks are spent and there is no
result. -/
def within {α : Type} (b : Nat) (m : Cost α) : Cost (Option α) :=
  if m.ticks ≤ b then ⟨some m.val, m.ticks⟩ else ⟨none, b⟩

/-! ### Free list traversals

These spend only what the function they are given spends. They are defined by
plain recursion so that forgetting the ticks gives the list function of the
same name. -/

def mapL {α β : Type} (f : α → Cost β) : List α → Cost (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapL f xs
    pure (y :: ys)

def flatMapL {α β : Type} (f : α → Cost (List β)) : List α → Cost (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← flatMapL f xs
    pure (y ++ ys)

def filterL {α : Type} (f : α → Cost Bool) : List α → Cost (List α)
  | [] => pure []
  | x :: xs => do
    let b ← f x
    let ys ← filterL f xs
    pure (if b then x :: ys else ys)

def filterMapL {α β : Type} (f : α → Cost (Option β)) : List α → Cost (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← filterMapL f xs
    pure (match y with
      | some b => b :: ys
      | none => ys)

/-- Stops at the first member that satisfies `f`, as `List.any` does. -/
def anyL {α : Type} (f : α → Cost Bool) : List α → Cost Bool
  | [] => pure false
  | x :: xs => do
    let b ← f x
    if b then pure true else anyL f xs

/-- Stops at the first member that fails `f`, as `List.all` does. -/
def allL {α : Type} (f : α → Cost Bool) : List α → Cost Bool
  | [] => pure true
  | x :: xs => do
    let b ← f x
    if b then allL f xs else pure false

def foldL {α β : Type} (f : β → α → Cost β) : β → List α → Cost β
  | b, [] => pure b
  | b, x :: xs => do
    let b' ← f b x
    foldL f b' xs

/-- Stops at the first member that satisfies `f`, as `List.find?` does. -/
def findL {α : Type} (f : α → Cost Bool) : List α → Cost (Option α)
  | [] => pure none
  | x :: xs => do
    let b ← f x
    if b then pure (some x) else findL f xs

end Cost

/-! ## Charged primitives -/

/-- A chain of spans composed from the left; `none` when some composition has
no match. The empty chain composes. -/
def Span.chain : List Span → Option Span
  | [] => some ⟨.var 0, .var 0, []⟩
  | s :: rest => rest.foldl (fun acc t => acc.bind (·.compose t)) (some s)

/-- What simplifying a span costs: at each instantiation stage, the theory is
matched against the closure of the span's store. -/
def Theory.simplifyCharge (T : Theory) : Nat → Span → Nat
  | n, s =>
    let w := (T.size + 1) * (s.size + Store.size (T.saturate s.c) + 1)
    if T.refutes? s.c then w
    else match n, T.bind? s.c with
      | n + 1, some θ => w + T.simplifyCharge n (s.inst θ)
      | _, _ => w

namespace Charged

/-- The size of an optional result. -/
def outSize : Option Span → Nat
  | none => 0
  | some s => s.size

def compose (x y : Span) : Cost (Option Span) :=
  ⟨x.compose y, x.size + y.size + outSize (x.compose y)⟩

def meet (x y : Span) : Cost (Option Span) :=
  ⟨x.meet y, x.size + y.size + outSize (x.meet y)⟩

/-- Does the chain compose? Only the test is charged: no result is built. -/
def composable (xs : List Span) : Cost Bool :=
  ⟨(Span.chain xs).isSome, (xs.map Span.size).sum⟩

def covers (a s : Span) : Cost Bool := ⟨a.covers? s, a.size + s.size⟩

def simplify (T : Theory) (s : Span) : Cost (Option Span) :=
  ⟨T.simplify s, T.simplifyCharge s.c.varCount s⟩

end Charged

/-! ## Costed runtimes -/

/-- A small-step machine whose step is a charged computation. -/
structure CostedRuntime where
  State : Type
  init : Program → Rel → State
  step : State → Cost (Step State)

namespace CostedRuntime

variable (C : CostedRuntime)

/-- The machine with the ticks forgotten. -/
def runtime : Runtime where
  State := C.State
  init := C.init
  step s := (C.step s).val

/-- The ticks spent in the first `n` steps. A finished machine spends
nothing more. -/
def spent : C.State → Nat → Nat
  | _, 0 => 0
  | s, n + 1 =>
    (C.step s).ticks + match (C.step s).val with
      | .emit _ s' => spent s' n
      | .done => 0

end CostedRuntime

/-! ## Latency -/

namespace CostedRuntime

variable (C : CostedRuntime)

/-- Some answer emitted in the first `n` steps on `q` relates the pair `x`
in `M`. -/
def Covered (P : Program) (q : Rel) (M : Interp) (x : GTerm × GTerm) (n : Nat) : Prop :=
  ∃ a ∈ C.runtime.emitted (C.init P q) n, x ∈ a.denAt M

/-- The coverage latency of `x` in `M` is at most `c`: the machine has spent
at most `c` ticks by some step at which an emitted answer relates `x`. -/
def CoversWithin (P : Program) (q : Rel) (M : Interp) (x : GTerm × GTerm) (c : Nat) : Prop :=
  ∃ n, C.Covered P q M x n ∧ C.spent (C.init P q) n ≤ c

/-- The exhaustion latency is at most `c`: the machine has spent at most `c`
ticks by some step at which it has reported that it is done. -/
def ExhaustsWithin (P : Program) (q : Rel) (c : Nat) : Prop :=
  ∃ n, C.runtime.Halts (C.init P q) n ∧ C.spent (C.init P q) n ≤ c

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
      New.CoversWithin P q M x (p (Old.spent (Old.init P q) n) (P.size + q.size))) ∧
    (Old.runtime.Halts (Old.init P q) n →
      New.ExhaustsWithin P q (p (Old.spent (Old.init P q) n) (P.size + q.size)))

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
        lo k ≤ Old.spent (Old.init (fam k).1 (fam k).2) n

/-- The special case for inputs that halt: `New` reports that it is done
within `hi k` ticks, and `Old` has paid at least `lo k` whenever it has. This
does not admit a rung. -/
def SeparatesExhaustion (Old New : CostedRuntime) (fam : Nat → Program × Rel)
    (size lo hi : Nat → Nat) : Prop :=
  ∀ k, (fam k).1.WellFormed (fam k).2 ∧ (fam k).1.size + (fam k).2.size ≤ size k ∧
    New.ExhaustsWithin (fam k).1 (fam k).2 (hi k) ∧
    (∀ n, Old.runtime.Halts (Old.init (fam k).1 (fam k).2) n →
      lo k ≤ Old.spent (Old.init (fam k).1 (fam k).2) n)

end RwLog
