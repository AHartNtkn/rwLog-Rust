/-
# The normal form of an expression

An engine does not work on expressions as they are written. The kernel
(`Trusted/Kernel.lean`) brings the query and every body to a normal form, and
the nodes of the normal form are what goals, tables and answers are indexed
by. In the normal form

* a *chain* is a `;` nest flattened to the list of its members, none of them
  a chain;
* a *meet* is a `&` nest flattened to the multiset of its members, none of
  them a meet;
* a *union* is a `|` nest flattened to the set of its members, none of them a
  union; the empty union is `0`;
* converse is pushed inward: it reverses a chain, maps over a meet and a
  union, swaps a span, and stays only on a call.

Adjacent spans of a chain are not fused.

A node of the normal form is written as an expression: a chain is the
right-nested `;` of its members, a meet the right-nested `&` of its members
sorted by the structural order `relCmp`, a union the right-nested `|` of its
members sorted and without repeats. So two expressions that differ only in
the grouping of `;`, in the order and grouping of `&`, or in the order,
grouping and repetition of `|`, have the same normal form, and equality of
nodes is equality of expressions.

`normB false e` is the normal form of `e`, and `normB true e` the normal form
of its converse. `Kernel/NormalFormCorrect.lean` proves that the normal form
has the derivable spans, and so the meaning, of the expression.
`Kernel/NormalFormStable.lean` proves that the normal form is stable: which
expressions are nodes (`Normal`), that normalising a node returns it, and
that every node read from a node or made from nodes is a node.
-/
import RwLog.Kernel.Canon

namespace RwLog

/-- The members of a `;` nest. -/
def seqParts {S : Type} : RelOf S → List (RelOf S)
  | .seq a b => seqParts a ++ seqParts b
  | e => [e]

/-- The members of a `&` nest. -/
def andParts {S : Type} : RelOf S → List (RelOf S)
  | .and a b => andParts a ++ andParts b
  | e => [e]

/-- Rebuild a right-nested `;` from its members. -/
def mkSeq {S : Type} : List (RelOf S) → RelOf S
  | [] => .zero
  | [e] => e
  | e :: es => .seq e (mkSeq es)

/-- Rebuild a right-nested `&` from its members. -/
def mkAnd {S : Type} : List (RelOf S) → RelOf S
  | [] => .zero
  | [e] => e
  | e :: es => .and e (mkAnd es)

/-- Sorted by the structural order, keeping repeats. -/
def sortedParts (es : List Rel) : List Rel := es.mergeSort fun a b => relCmp a b != .gt

/-- The normal form of an expression (`normB false`) and of its converse
(`normB true`). -/
def normB : Bool → Rel → Rel
  | _, .zero => .zero
  | false, .span s => .span s
  | true, .span s => .span s.swap
  | b, .or x y => mkOr (sortedBranches (orBranches (normB b x) ++ orBranches (normB b y)))
  | b, .and x y => mkAnd (sortedParts (andParts (normB b x) ++ andParts (normB b y)))
  | false, .seq x y => mkSeq (seqParts (normB false x) ++ seqParts (normB false y))
  | true, .seq x y => mkSeq (seqParts (normB true y) ++ seqParts (normB true x))
  | b, .conv x => normB (!b) x
  | false, .call n => .call n
  | true, .call n => .conv (.call n)

/-- The normal form of an expression. -/
def RelOf.norm (e : Rel) : Rel := normB false e

/-- The normal form of the converse of an expression. -/
def RelOf.normConv (e : Rel) : Rel := normB true e

/-! ## Reading a node

What a node of the normal form is, as an engine sees it: the kind of the node
and its members. -/

/-- The kind of a node and its members, over any type `N` of members. -/
inductive NodeView (S N : Type) where
  /-- A span. -/
  | span (s : S)
  /-- A call; `flip` says the converse of the body is meant. -/
  | call (n : Name) (flip : Bool)
  /-- A chain: at least two members, in order, none of them a chain. -/
  | chain (xs : List N)
  /-- A meet: at least two members, sorted, none of them a meet. -/
  | meet (xs : List N)
  /-- A union: its members, sorted and without repeats, none of them a union.
  The empty union is `0`. -/
  | union (xs : List N)
  deriving DecidableEq, Repr

/-- The view of a node. An expression that is not a node of the normal form
(a converse of something other than a call) reads as the empty union. -/
def RelOf.view : Rel → NodeView Span Rel
  | .zero => .union []
  | .span s => .span s
  | .call n => .call n false
  | .conv (.call n) => .call n true
  | .conv _ => .union []
  | .seq a b => .chain (seqParts (.seq a b))
  | .and a b => .meet (andParts (.and a b))
  | .or a b => .union (orBranches (.or a b))

/-- The members of a node read as a chain: a node that is not a chain is a
chain of one. -/
abbrev RelOf.chainParts (e : Rel) : List Rel := seqParts e

/-- The members of a node read as a meet: a node that is not a meet is a
meet of one. -/
abbrev RelOf.meetParts (e : Rel) : List Rel := andParts e

/-- The members of a node read as a union: `0` has none, and a node that is
not a union is a union of one. -/
def RelOf.unionParts : Rel → List Rel
  | .zero => []
  | e => orBranches e

/-- The interval `[i, j)` of a node read as a chain, as a node. It is defined
for `i < j` within the chain. -/
def RelOf.interval (e : Rel) (i j : Nat) : Option Rel :=
  if i < j ∧ j ≤ e.chainParts.length then some (mkSeq ((e.chainParts.take j).drop i)) else none

/-- A node read as a meet, without its `i`-th member, as a node. It is defined
when the meet has at least two members and `i` is one of them. -/
def RelOf.without (e : Rel) (i : Nat) : Option Rel :=
  if i < e.meetParts.length ∧ 2 ≤ e.meetParts.length then some (mkAnd (e.meetParts.eraseIdx i))
  else none

end RwLog
