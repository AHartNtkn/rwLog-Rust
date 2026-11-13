/-
# Canonical expressions and boundaries

Two operations on syntax that the tabled machines use and the cost model
charges (`Trusted/Charged.lean`).

`canon`: `|` is associative, commutative and idempotent, with `0` as unit, so
every `|` nest is flattened into its branches, `0` branches are dropped, the
branches are sorted by a fixed linear order and deduplicated, and the result is
rebuilt right-nested.

`bound`: an interface span as a boundary, with the trivial interface
`$x -> $x` represented as no boundary.
-/
import RwLog.Trusted.Syntax
import Mathlib.Data.List.Sort

namespace RwLog

/-- A boundary, with the trivial interface `$x -> $x` (the identity)
represented as no boundary. -/
def bound (s : Span) : Option Span :=
  match s.l, s.c with
  | .var _, [] => none
  | _, _ => some s

/-- A structural linear order on patterns. -/
def patCmp : Pat → Pat → Ordering
  | .var a, .var b => compare a b
  | .var _, _ => .lt
  | _, .var _ => .gt
  | .sym f, .sym g => compare f g
  | .sym _, _ => .lt
  | _, .sym _ => .gt
  | .app a b, .app c d => (patCmp a c).then (patCmp b d)

/-- Lexicographic extension of an order to lists. -/
def listCmp {α : Type} (f : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (f x y).then (listCmp f xs ys)

def spanCmp (a b : Span) : Ordering :=
  ((patCmp a.l b.l).then (patCmp a.r b.r)).then (listCmp patCmp a.c b.c)

/-- A structural linear order on expressions. -/
def relCmp : Rel → Rel → Ordering
  | .zero, .zero => .eq
  | .zero, _ => .lt
  | _, .zero => .gt
  | .span a, .span b => spanCmp a b
  | .span _, _ => .lt
  | _, .span _ => .gt
  | .or a b, .or c d => (relCmp a c).then (relCmp b d)
  | .or _ _, _ => .lt
  | _, .or _ _ => .gt
  | .and a b, .and c d => (relCmp a c).then (relCmp b d)
  | .and _ _, _ => .lt
  | _, .and _ _ => .gt
  | .seq a b, .seq c d => (relCmp a c).then (relCmp b d)
  | .seq _ _, _ => .lt
  | _, .seq _ _ => .gt
  | .conv a, .conv b => relCmp a b
  | .conv _, _ => .lt
  | _, .conv _ => .gt
  | .call m, .call n => compare m n

/-- The branches of a `|` nest. -/
def orBranches {S : Type} : RelOf S → List (RelOf S)
  | .or a b => orBranches a ++ orBranches b
  | e => [e]

/-- Rebuild a right-nested `|` from branches. -/
def mkOr {S : Type} : List (RelOf S) → RelOf S
  | [] => .zero
  | [e] => e
  | e :: es => .or e (mkOr es)

/-- Sorted, without repeats. -/
def sortedBranches (es : List Rel) : List Rel :=
  ((es.filter (· ≠ .zero)).mergeSort fun a b => relCmp a b != .gt).eraseDups

/-- The canonical form of an expression. -/
def canon : Rel → Rel
  | .zero => .zero
  | .span s => .span s
  | .or a b => mkOr (sortedBranches (orBranches (canon a) ++ orBranches (canon b)))
  | .and a b => .and (canon a) (canon b)
  | .seq a b => .seq (canon a) (canon b)
  | .conv a => .conv (canon a)
  | .call n => .call n

end RwLog
