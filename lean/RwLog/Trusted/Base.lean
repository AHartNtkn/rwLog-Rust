/-
# The base machine

What a kernel operation costs is not postulated. It is what a program for it
spends on this machine, and the machine has one unit of cost.

## The machine

A *store* is a sequence of nodes. A node is a variable, a symbol, or an
application of two earlier nodes; a *pointer* is the position of a node. Nodes
are only ever added at the end and never changed, so a pointer means the same
term for as long as it exists, and two terms share a subterm by pointing at
the same node. No node is stored twice: asking for a node that is already
there returns its pointer. So two pointers stand for the same term exactly
when they are the same pointer (`Heap.tm_inj`, `Kernel/Machine/Heap.lean`).
Every store starts with the node of the variable `0`.

A program is written for every machine (`Base`): the type of pointers, of
variable words and of symbol words are abstract, and so is the monad. All it
can do to a term is

* read the node at a pointer,
* ask for the pointer of a node, which adds the node if it is new,
* ask whether two pointers are the same pointer,
* compare two variable words or two symbol words (equality and order),
* renumber a variable word into the left or right half of the variables
  (`2 v` and `2 v + 1`, the renumbering of two-sided matching),
* look a key up in a table, or set it. A table is a value the program holds;
  its keys are pointers and words, and its entries are whatever the program
  likes, other tables included.

Each of these is one tick, whatever the store holds. Nothing else tells a
program anything about a pointer or a word; in particular pointers have no
order. A program cannot touch the ticks except by spending more (`tick`), and
it can run a computation and learn what it spent (`metered`). What it does
between two of these (control, and moving the values it holds) is free.

Recursion on the store is not bounded in advance: a program may be defined as
a fixed point (`partial_fixpoint`), so the monad has an order in which the
computation that never finishes is least. That a program finishes is proved
about it, with its result and its cost.

## The machine of the language

`Mach` is the instance all costs are read at: pointers and variable words are
numbers, symbol words are symbols, a table is an association list, and a
computation maps a store to nothing (it failed or did not finish) or to a
result, a store and the ticks spent. Reading a position outside the store
fails, and so does asking for an application whose parts are not in the
store, so every node of every store points backwards. `Heap.tm` reads a
pointer as the term it stands for.

This is the machine the Rust implementation is measured on: the store is an
arena whose allocation looks the node up in a trie of tables first, a table is
a vector the program owns and uses once, and the ticks are a counter in the
arena's interface.
-/
import RwLog.Trusted.CostMonad
import RwLog.Trusted.Syntax

namespace RwLog

open Lean.Order

/-! ## Nodes, keys, and the interface of a machine -/

/-- A node of a store: a variable, a symbol, or the application of two nodes. -/
inductive Node (P V F : Type) where
  | var (v : V)
  | sym (f : F)
  | app (a b : P)
  deriving DecidableEq, Repr

/-- A key of a table: a pointer, a variable word or a symbol word. -/
inductive Key (P V F : Type) where
  | ptr (p : P)
  | word (v : V)
  | name (f : F)
  deriving DecidableEq, Repr

/-- A machine: pointers `P`, variable words `V`, symbol words `F`, and the
monad `M` its programs run in. Every operation that returns in `M`, other than
`tick`, is one tick on the machine of the language. -/
class Base (P : Type) (V F : outParam Type) (M : outParam (Type → Type)) extends Monad M where
  /-- The order in which the computation that never finishes is least. -/
  [ccpo : ∀ α, CCPO (M α)]
  [mono : MonoBind M]
  /-- Spend ticks. -/
  tick : Nat → M Unit
  /-- Run a computation and return what it spent with its result. -/
  metered : {α : Type} → M α → M (α × Nat)
  /-- The node of the variable `0`, which every store starts with. -/
  root : P
  /-- The node at a pointer. -/
  read : P → M (Node P V F)
  /-- The pointer of a node. The node is added if the store does not have
  it. -/
  alloc : Node P V F → M P
  /-- Are the two pointers the same pointer? -/
  same : P → P → M Bool
  eqV : V → V → M Bool
  cmpV : V → V → M Ordering
  eqF : F → F → M Bool
  cmpF : F → F → M Ordering
  /-- The variable word `2 v`: `v` in the first of two spans being matched. -/
  inl : V → M V
  /-- The variable word `2 v + 1`: `v` in the second. -/
  inr : V → M V
  /-- Tables with entries in `α`. -/
  Tbl : Type → Type
  /-- The table with no entries. -/
  empty : {α : Type} → Tbl α
  get : {α : Type} → Tbl α → Key P V F → M (Option α)
  set : {α : Type} → Tbl α → Key P V F → α → M (Tbl α)

attribute [instance_reducible, instance] Base.ccpo
attribute [instance] Base.mono

/-! ## The machine of the language -/

/-- A node of the machine of the language. -/
abbrev Cell := Node Nat Nat Sym

/-- May the node be added to a store of `n` nodes? The parts of an application
must already be there. -/
def Cell.Fits (n : Nat) : Cell → Prop
  | .app a b => a < n ∧ b < n
  | _ => True

instance (n : Nat) (c : Cell) : Decidable (c.Fits n) := by
  cases c <;> unfold Cell.Fits <;> infer_instance

/-- A store: its nodes in the order they were added. An application points
at two earlier nodes, and no node occurs twice. -/
structure Heap where
  cells : List Cell
  back : ∀ (i a b : Nat), cells[i]? = some (Node.app a b) → a < i ∧ b < i
  nodup : cells.Nodup

namespace Heap

/-- The store every computation starts from: the variable `0`. -/
def init : Heap where
  cells := [.var 0]
  back := by
    intro i a b h
    cases i with
    | zero => simp at h
    | succ i => simp at h
  nodup := by simp

def size (h : Heap) : Nat := h.cells.length

/-- Add a new node at the end. -/
def push (h : Heap) (c : Cell) (hc : c.Fits h.size) (hn : c ∉ h.cells) : Heap where
  cells := h.cells ++ [c]
  back := by
    intro i a b hi
    rcases Nat.lt_trichotomy i h.cells.length with hlt | heq | hgt
    · rw [List.getElem?_append_left hlt] at hi
      exact h.back i a b hi
    · subst heq
      simp only [List.getElem?_concat_length, Option.some.injEq] at hi
      subst hi
      exact hc
    · rw [List.getElem?_eq_none (by simp; omega)] at hi
      cases hi
  nodup := by
    rw [List.nodup_append]
    refine ⟨h.nodup, by simp, ?_⟩
    intro a ha b hb e
    simp only [List.mem_singleton] at hb
    subst hb e
    exact hn ha

/-- The term a node stands for, given the terms of the nodes before it. -/
def cellTerm (acc : List Pat) : Cell → Pat
  | .var v => .var v
  | .sym f => .sym f
  | .app a b => .app (acc.getD a (.var 0)) (acc.getD b (.var 0))

/-- The terms the nodes stand for, in order. -/
def termsOf (cs : List Cell) : List Pat :=
  cs.foldl (fun acc c => acc ++ [cellTerm acc c]) []

/-- The term a pointer stands for. -/
def tm (h : Heap) (p : Nat) : Pat := (termsOf h.cells).getD p (.var 0)

end Heap

/-- A computation on the machine of the language: from a store, nothing (it
failed or did not finish), or a result, the store it leaves, and the ticks
spent. -/
def Mach (α : Type) : Type := Heap → Option (Cost (α × Heap))

namespace Mach

/-- Run `m`, then `f` on its result from the store it leaves. The ticks add. -/
def bind {α β : Type} (m : Mach α) (f : α → Mach β) : Mach β := fun h =>
  match m h with
  | none => none
  | some r =>
    match f r.val.1 r.val.2 with
    | none => none
    | some r' => some ⟨r'.val, r.ticks + r'.ticks⟩

instance : Monad Mach where
  pure a := fun h => some ⟨(a, h), 0⟩
  bind := Mach.bind

instance (α : Type) : PartialOrder (Mach α) :=
  inferInstanceAs (PartialOrder (Heap → Option (Cost (α × Heap))))

instance (α : Type) : CCPO (Mach α) :=
  inferInstanceAs (CCPO (Heap → Option (Cost (α × Heap))))

instance : MonoBind Mach where
  bind_mono_left {_ _ a₁ a₂ f} h := by
    intro s
    have hs : FlatOrder.rel (b := none) (a₁ s) (a₂ s) := h s
    change FlatOrder.rel (b := none) (Mach.bind a₁ f s) (Mach.bind a₂ f s)
    unfold Mach.bind
    revert hs
    generalize a₁ s = x
    generalize a₂ s = y
    intro hs
    cases hs
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right {_ _ a f₁ f₂} h := by
    intro s
    change FlatOrder.rel (b := none) (Mach.bind a f₁ s) (Mach.bind a f₂ s)
    unfold Mach.bind
    cases a s with
    | none => exact FlatOrder.rel.refl
    | some r =>
      have hr : FlatOrder.rel (b := none) (f₁ r.val.1 r.val.2) (f₂ r.val.1 r.val.2) :=
        h r.val.1 r.val.2
      dsimp only
      revert hr
      generalize f₁ r.val.1 r.val.2 = x
      generalize f₂ r.val.1 r.val.2 = y
      intro hr
      cases hr
      · exact FlatOrder.rel.bot
      · exact FlatOrder.rel.refl

/-- Spend `n` ticks. -/
def tick (n : Nat) : Mach Unit := fun h => some ⟨((), h), n⟩

/-- The node at `p`. It fails outside the store. -/
def read (p : Nat) : Mach Cell := fun h => (h.cells[p]?).map fun c => ⟨(c, h), 1⟩

/-- The position of a node: where it is, if the store has it, and otherwise
the end of the store, where it is added. It fails on a new application whose
parts are not in the store. -/
def alloc (c : Cell) : Mach Nat := fun h =>
  if hn : c ∈ h.cells then some ⟨(h.cells.idxOf c, h), 1⟩
  else if hc : c.Fits h.size then some ⟨(h.size, h.push c hc hn), 1⟩ else none

/-- Run `m` and return what it spent with its result. -/
def metered {α : Type} (m : Mach α) : Mach (α × Nat) := fun h =>
  (m h).map fun r => ⟨((r.val.1, r.ticks), r.val.2), r.ticks⟩

/-- A step that only computes: one tick, and the store is not touched. -/
def step {α : Type} (a : α) : Mach α := fun h => some ⟨(a, h), 1⟩

/-- A table: an association list, with the newest entry of a key first. -/
abbrev Tbl (α : Type) : Type := List (Key Nat Nat Sym × α)

/-- Run two computations side by side until one finishes (`Cost.race`), from
the same store. The loser's work is thrown away with its store. If either
does not finish, neither does the race. -/
def race {α : Type} (x y : Mach α) : Mach α := fun h =>
  match x h, y h with
  | some a, some b => some (Cost.race a b)
  | _, _ => none

end Mach

/-- The machine of the language. -/
instance Base.std : Base Nat Nat Sym Mach where
  tick := Mach.tick
  metered := Mach.metered
  root := 0
  read := Mach.read
  alloc := Mach.alloc
  same p q := Mach.step (decide (p = q))
  eqV v w := Mach.step (decide (v = w))
  cmpV v w := Mach.step (compare v w)
  eqF f g := Mach.step (decide (f = g))
  cmpF f g := Mach.step (compare f g)
  inl v := Mach.step (2 * v)
  inr v := Mach.step (2 * v + 1)
  Tbl := Mach.Tbl
  empty := []
  get t k := Mach.step (t.lookup k)
  set t k a := Mach.step ((k, a) :: t)

end RwLog
