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
* a coverage test: the sizes of both spans, and the search that places the
  covering span's store in the other's (`matchAllWork`): every attempt to
  match one constraint onto another, at every point of the search, by the
  sizes of the two. With an empty store there is no search;
* simplifying a span by a theory: for each instantiation stage, the size of
  the theory times the size of the span and of the closure of its store, and
  the search for firings: every round of the closure, and the two readings of
  the closed store, match the heads of every bounded rule against the store
  (`Theory.firingsWork`, `Theory.saturateWork`). With an empty theory there
  is no search.

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

## Improvement

`Simulates Old New p`: whatever `Old` has emitted and whether it has halted
after some number of steps, `New` has covered and matched it at a cost bounded
by the explicit function `p` of the cost `Old` paid and of the size of the
input. This bounds both coverage latency and exhaustion latency.

`Separates Old New fam lo hi`: on the family `fam`, `New` halts within cost
`hi k`, while `Old` has paid at least `lo k` whenever it has halted.

A rung improves on its predecessor when it simulates it with a polynomial `p`
and is separated from it by a family with `hi` polynomial and `lo`
exponential, all given as explicit numerals.
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

/-- The work of `matchAll`: every attempt to match a pattern onto a member of
the store, at every point of the search, charged by the sizes of the two. -/
def matchAllWork : List Pat → List Pat → PSubst → Nat
  | [], _, _ => 0
  | p :: ps, ts, θ =>
    (ts.map fun t => p.size + t.size +
      match matchInto p t θ with
      | some θ' => matchAllWork ps ts θ'
      | none => 0).sum

/-- The work of listing the firings of a theory on a store: the heads of each
bounded rule are matched against the store. -/
def Theory.firingsWork (T : Theory) (c : Store) : Nat :=
  (T.map fun ρ => if ρ.bounded then matchAllWork ρ.heads c [] else 0).sum

/-- The work of closing a store: the firings are listed in every round. -/
def Theory.saturateWork (T : Theory) (c : Store) : Nat :=
  T.firingsWork c + if _ : T.newAtoms c = [] then 0 else T.saturateWork (c ++ T.newAtoms c)
termination_by T.room c
decreasing_by exact Theory.room_lt ‹_›

/-- What simplifying a span costs: at each instantiation stage, the store is
closed, and the theory is matched against the closure twice, once to look for
a refutation and once for a forced equation. -/
def Theory.simplifyCharge (T : Theory) : Nat → Span → Nat
  | n, s =>
    let w := (T.size + 1) * (s.size + Store.size (T.saturate s.c) + 1) +
      T.saturateWork s.c + 2 * T.firingsWork (T.saturate s.c)
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

/-- The search of a coverage test: once the two sides match, the store of `a`
is placed in the store of `s`. -/
def coversWork (a s : Span) : Nat :=
  match (matchInto a.l s.l []).bind (matchInto a.r s.r) with
  | none => 0
  | some θ => matchAllWork a.c s.c θ

def covers (a s : Span) : Cost Bool := ⟨a.covers? s, a.size + s.size + coversWork a s⟩

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

/-! ## Improvement -/

/-- `New` simulates `Old` within `p`: for every well-formed input and every
number of steps of `Old`, some number of steps of `New` costs at most `p` of
what `Old` paid and of the input's size, covers in every model every answer
`Old` has emitted, and has halted if `Old` has. -/
def Simulates (Old New : CostedRuntime) (p : Nat → Nat → Nat) : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, ∃ m,
    New.spent (New.init P q) m ≤ p (Old.spent (Old.init P q) n) (P.size + q.size) ∧
    (∀ a ∈ Old.runtime.emitted (Old.init P q) n,
      ∃ b ∈ New.runtime.emitted (New.init P q) m, b.CoversLive P.theory a) ∧
    (Old.runtime.Halts (Old.init P q) n → New.runtime.Halts (New.init P q) m)

/-- `New` is separated from `Old` on a family of well-formed inputs: `New`
halts within cost `hi k`, and `Old` has paid at least `lo k` whenever it has
halted. -/
def Separates (Old New : CostedRuntime) (fam : Nat → Program × Rel) (lo hi : Nat → Nat) : Prop :=
  ∀ k, (fam k).1.WellFormed (fam k).2 ∧
    (∃ m, New.runtime.Halts (New.init (fam k).1 (fam k).2) m ∧
      New.spent (New.init (fam k).1 (fam k).2) m ≤ hi k) ∧
    (∀ n, Old.runtime.Halts (Old.init (fam k).1 (fam k).2) n →
      lo k ≤ Old.spent (Old.init (fam k).1 (fam k).2) n)

end RwLog
