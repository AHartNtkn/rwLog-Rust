/-
# The charged primitives

Every operation on spans that an engine can perform, as a charged computation
(`Trusted/CostMonad.lean`). Each primitive computes exactly the kernel
operation it names (its `val` is that operation by definition) and charges a
fixed function of the sizes of its arguments, and of its result when it
builds one:

* composing or conjoining two spans: the sizes of both spans and of the result;
* testing whether a chain of spans composes, without building the result: the
  sizes of the spans;
* testing whether two spans are the same as written: the sizes of both;
* taking an interface of a span as a boundary: the size of the span;
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

Swapping the two sides of a span is free.

Space: an operation that builds a span holds the size of what it built, and a
test holds nothing. While it runs, an operation has at most one cell live for
each tick it spends (`Charged.op`).

These charges are postulated. A kernel rung (`Trusted/KernelRung.lean`)
replaces them by charges derived on a machine.

A term is charged by its size wherever it is used, never by one, so sharing
or interning cannot hide work.
-/
import RwLog.Trusted.CostMonad
import RwLog.Kernel.Refute
import RwLog.Kernel.Iface
import RwLog.Kernel.Canon
import RwLog.Kernel.NormalForm
import RwLog.SpanLayer.Coverage

namespace RwLog

/-! ## Sizes -/

def Store.size (c : Store) : Nat := (c.map Term.size).sum

def Span.size (s : Span) : Nat := s.l.size + s.r.size + Store.size s.c

/-- The size of an expression: its nodes, with each span counted by its
size. -/
def RelOf.size : Rel → Nat
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

def ProgramOf.size (P : Program) : Nat := (P.defs.map fun d => 1 + d.2.size).sum + P.theory.size

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

/-- An operation that returns `v` in `t` ticks and leaves `h` cells live. Its
peak is the larger of the two: an allocation is a tick. -/
def op {α : Type} (v : α) (t h : Nat) : Cost α := ⟨v, t, max t h, h⟩

@[simp] theorem op_val {α : Type} (v : α) (t h : Nat) : (op v t h).val = v := rfl
@[simp] theorem op_ticks {α : Type} (v : α) (t h : Nat) : (op v t h).ticks = t := rfl
@[simp] theorem op_held {α : Type} (v : α) (t h : Nat) : (op v t h).held = h := rfl

def compose (x y : Span) : Cost (Option Span) :=
  op (x.compose y) (x.size + y.size + outSize (x.compose y)) (outSize (x.compose y))

def meet (x y : Span) : Cost (Option Span) :=
  op (x.meet y) (x.size + y.size + outSize (x.meet y)) (outSize (x.meet y))

/-- Does the chain compose? Only the test is charged: no result is built. -/
def composable (xs : List Span) : Cost Bool :=
  op (Span.chain xs).isSome (xs.map Span.size).sum 0

/-- The search of a coverage test: once the two sides match, the store of `a`
is placed in the store of `s`. -/
def coversWork (a s : Span) : Nat :=
  match (matchInto a.l s.l []).bind (matchInto a.r s.r) with
  | none => 0
  | some θ => matchAllWork a.c s.c θ

def covers (a s : Span) : Cost Bool := op (a.covers? s) (a.size + s.size + coversWork a s) 0

def simplify (T : Theory) (s : Span) : Cost (Option Span) :=
  op (T.simplify s) (T.simplifyCharge s.c.varCount s) (outSize (T.simplify s))

/-- Are the two spans the same span, as written? -/
def eq (x y : Span) : Cost Bool := op (decide (x = y)) (x.size + y.size) 0

/-- The right interface of a span, as a boundary. -/
def rightBound (s : Span) : Cost (Option Span) :=
  op (bound s.rightIface) s.size (outSize (bound s.rightIface))

/-- The left interface of a span, as a boundary. -/
def leftBound (s : Span) : Cost (Option Span) :=
  op (bound s.leftIface) s.size (outSize (bound s.leftIface))

/-! ## Nodes of the normal form

The query and the bodies are brought to their normal form
(`Kernel/NormalForm.lean`) and interned before the first step. A node is then
an identifier: comparing two is one tick, and reading a node is one tick for
the node and one for each member. A node that is made later (a stretch of a
chain, a meet without one member, a joined chain, a merged meet) is interned
at one tick, and one cell, for each of its members. -/

/-- Bringing the program and the query to their normal form and interning
every node with its converse: sorting the members of a meet or a union
compares them as written, so the charge is quadratic in the size of the
input. -/
def load (P : Program) (q : Rel) : Cost Rel :=
  op q.norm ((P.size + q.size) ^ 2) (2 * (P.size + q.size))

/-- The number of members a node is read with. -/
def members : NodeView Span Rel → Nat
  | .span _ => 0
  | .call _ _ => 0
  | .chain xs => xs.length
  | .meet xs => xs.length
  | .union xs => xs.length

/-- Read a node. -/
def view (n : Rel) : Cost (NodeView Span Rel) := op n.view (1 + members n.view) 0

/-- The stretch `[i, j)` of a chain, as a node. -/
def interval (n : Rel) (i j : Nat) : Cost (Option Rel) := op (n.interval i j) (1 + (j - i)) (j - i)

/-- A meet without its `i`-th member, as a node. -/
def without (n : Rel) (i : Nat) : Cost (Option Rel) :=
  op (n.without i) (1 + n.meetParts.length) n.meetParts.length

/-- The node of the body a call node reads: the normal form of the body, or
of its converse. -/
def bodyOf (P : Program) : Rel → Option Rel
  | .call n => some (P.body n).norm
  | .conv (.call n) => some (P.body n).normConv
  | _ => none

def body (P : Program) (n : Rel) : Cost (Option Rel) := op (bodyOf P n) 1 0

/-- The converse of a node. It was interned with the node. -/
def convNode (n : Rel) : Cost Rel := op n.normConv 1 0

/-- Are the two nodes the same node? -/
def eqNode (m n : Rel) : Cost Bool := op (decide (m = n)) 1 0

end Charged

end RwLog
