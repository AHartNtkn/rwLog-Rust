/-
# Levels

How much of a relation has been found is measured by levels. They are read
off the program as it is written, and they mention no machine: no order of
answers, no step, no table.

## Weight

A derivation of a pair is a way the program relates it: a span that relates
it; a derivation by one side of a `|`; a derivation by each side of a `;`,
through a middle term; a derivation by each side of a `&`; a derivation of
the swapped pair under a converse; a derivation by the body of a relation
definition, under a call of it. Its weight counts the spans used and the
definitions unfolded:

* a span weighs 1;
* `;` and `&` add the weights of their two sides;
* `|` and converse keep the weight;
* unfolding a relation definition adds 1.

Every derivation weighs at least 1, and there are finitely many shapes of
derivation of a given weight.

## Levels

`LevelAt P M c e p`: the pair `p` has a derivation by `e` of weight at most
`c`, in the program `P` and the interpretation `M`. Level `c` of `e`
(`ProgramOf.level`) is the set of those pairs in the interpretation of the
program's sorts. Level 0 is empty, the levels grow with `c`, and together
they are the relation (`Rungs/Framework/Levels.lean`).

A level is a set of ground pairs, so it does not depend on how a machine
writes its answers: one answer with variables may cover a whole level.
-/
import RwLog.Trusted.Semantics

namespace RwLog

/-- The pair `p` has a derivation by `e` of weight at most `c`, in the
program `P` and the interpretation `M`. -/
inductive LevelAt (P : Program) (M : Interp) : Nat → Rel → GTerm × GTerm → Prop
  /-- A span weighs 1. -/
  | span {c : Nat} {s : Span} {p : GTerm × GTerm} :
      1 ≤ c → p ∈ s.denAt M → LevelAt P M c (.span s) p
  /-- `|` keeps the weight. -/
  | orl {c : Nat} {a b : Rel} {p : GTerm × GTerm} : LevelAt P M c a p → LevelAt P M c (.or a b) p
  | orr {c : Nat} {a b : Rel} {p : GTerm × GTerm} : LevelAt P M c b p → LevelAt P M c (.or a b) p
  /-- `;` adds the weights. -/
  | seq {c ca cb : Nat} {a b : Rel} {x m z : GTerm} :
      LevelAt P M ca a (x, m) → LevelAt P M cb b (m, z) → ca + cb ≤ c →
      LevelAt P M c (.seq a b) (x, z)
  /-- `&` adds the weights. -/
  | and {c ca cb : Nat} {a b : Rel} {p : GTerm × GTerm} :
      LevelAt P M ca a p → LevelAt P M cb b p → ca + cb ≤ c → LevelAt P M c (.and a b) p
  /-- Converse keeps the weight. -/
  | conv {c : Nat} {a : Rel} {p : GTerm × GTerm} :
      LevelAt P M c a (p.2, p.1) → LevelAt P M c (.conv a) p
  /-- Unfolding a relation definition adds 1. -/
  | call {c : Nat} {n : Name} {p : GTerm × GTerm} :
      LevelAt P M c (P.body n) p → LevelAt P M (c + 1) (.call n) p

/-- Level `c` of `e` in `M`: the pairs with a derivation of weight at most
`c`. -/
def ProgramOf.levelAt (P : Program) (M : Interp) (c : Nat) (e : Rel) : PRel :=
  {p | LevelAt P M c e p}

/-- Level `c` of an expression in a program: the pairs with a derivation of
weight at most `c`, in the interpretation of the program's sorts. -/
def ProgramOf.level (P : Program) (c : Nat) (e : Rel) : PRel := P.levelAt P.sorts.interp c e

end RwLog
