/-
# The charged primitives

The operations on the nodes of the normal form, as charged computations
(`Trusted/CostMonad.lean`), and the sizes they are charged by. Each
primitive computes exactly the operation it names (its `val` is that
operation by definition) and charges a fixed function of its arguments.

No operation on representatives is charged here. What an operation of a
constraint domain costs is what its kernel charges
(`KernelRung`, `Trusted/Kernel.lean`), and the charges of the kernel of the
domain of sorts are derived on a machine (`verified/`).

Space: while it runs, an operation has at most one cell live for each tick it
spends (`Charged.op`).

The charges of the operations on nodes are postulated: no machine holds
nodes yet (roadmap L45). A term of the input is charged by its size, never by
one.
-/
import RwLog.Trusted.CostMonad
import RwLog.Kernel.Match
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

/-- The size of a sort declaration: its cases with their arguments, and the
shapes it leaves out. -/
def SortDef.size (d : SortDef) : Nat :=
  1 + (d.cases.map fun c => 1 + c.2.length).sum +
    match d.rest with
    | none => 0
    | some r => 1 + r.1.length

def Sorts.size (S : Sorts) : Nat := (S.map fun d => 1 + d.2.size).sum

def ProgramOf.size (P : Program) : Nat := (P.defs.map fun d => 1 + d.2.size).sum + P.sorts.size

namespace Charged

/-- An operation that returns `v` in `t` ticks and leaves `h` cells live. Its
peak is the larger of the two: an allocation is a tick. -/
def op {α : Type} (v : α) (t h : Nat) : Cost α := ⟨v, t, max t h, h, le_max_right _ _⟩

@[simp] theorem op_val {α : Type} (v : α) (t h : Nat) : (op v t h).val = v := rfl
@[simp] theorem op_ticks {α : Type} (v : α) (t h : Nat) : (op v t h).ticks = t := rfl
@[simp] theorem op_held {α : Type} (v : α) (t h : Nat) : (op v t h).held = h := rfl

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
