/-
# Goals and tables of answers, for every machine that tables

A machine that tables evaluates *goals*. A goal `⟨lb, n, rb⟩` is the relation
`lb ; n ; rb`, where `n` is a node of the normal form of the query or of a
body (`Kernel/NormalForm.lean`) and the optional boundaries are
representatives that relate a term only to itself. Two goals are the same
goal when their nodes are the same node and their boundaries the same
representatives.

This file is the text every such machine shares: the goal, the test for the
same goal, the position of the table of a goal, the test that one answer
covers another, the maximal answers of a list, and the rule that combines
the two sides of a split. It is written once, for arbitrary types of
representatives, nodes and answers and an arbitrary monad, against the
derivation kernel (`Trusted/Kernel.lean`). What these operations return at
the kernel of a program is in `Rungs/Framework/GoalsVal.lean`.

A machine brings the names into its own namespace with `export Goals (…)`,
constructors included.
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.Framework.Traverse

namespace RwLog

namespace Goals

open Traverse

/-- The goal `lb ; node ; rb`. -/
structure GoalOf (S N : Type) where
  lb : Option S
  node : N
  rb : Option S
  deriving DecidableEq

/-- The goal as the rules of the kernel name it. -/
def toGoal {R : Type} (g : GoalOf R Rel) : Goal R := ⟨g.lb, g.node, g.rb⟩

/-- Which rule combines the two sides of a split: `join` for a chain, `meetA`
for a meet. -/
inductive Kind where
  | seq
  | and
  deriving DecidableEq, Repr

/-- The members a meet of `k` members is split at: the first of two; every
member otherwise. -/
def andSplits (k : Nat) : List Nat := if k ≤ 2 then [0] else List.range k

section

variable {S N A : Type} {M : Type → Type} [K : DerivationKernel S N A M]

/-- Are two boundaries the same representative? -/
def sameBound : Option S → Option S → M Bool
  | none, none => pure true
  | some a, some b => K.eq a b
  | _, _ => pure false

/-- Are two goals the same goal? -/
def same (g h : GoalOf S N) : M Bool := do
  let b ← K.eqNode g.node h.node
  if b then do
    let l ← sameBound (K := K) g.lb h.lb
    if l then sameBound (K := K) g.rb h.rb else pure false
  else pure false

/-- The position of the first table whose goal is `g`, counting from `i`.
`goal` reads the goal of a table. -/
def indexFrom {T : Type} (goal : T → GoalOf S N) (g : GoalOf S N) : Nat → List T → M (Option Nat)
  | _, [] => pure none
  | i, t :: ts => do
    let b ← same (K := K) (goal t) g
    if b then pure (some i) else indexFrom goal g (i + 1) ts

/-- Does the first answer cover the second? -/
def coversA (y x : A) : M Bool := K.covers (K.span y) (K.span x)

/-- The answers no other answer of the list strictly covers, one of each
class of answers that cover each other. -/
def maxima (xs : List A) : M (List A) := do
  let top ← filterL (fun x => do
    let b ← anyL (fun y => do
      let c ← coversA (K := K) y x
      if c then do
        let c' ← coversA (K := K) x y
        pure !c'
      else pure false) xs
    pure !b) xs
  foldL (fun acc x => do
    let b ← anyL (fun y => coversA (K := K) y x) acc
    pure (if b then acc else acc ++ [x])) [] top

/-- The candidates that no answer of the table covers, without the ones
another of them strictly covers. -/
def fresh (old cands : List A) : M (List A) := do
  let cs ← filterL (fun c => do
    let b ← anyL (fun t => coversA (K := K) t c) old
    pure !b) cands
  maxima (K := K) cs

/-- Combine an answer of the left side of a split with an answer of the right
one. -/
def both : Kind → A → A → M (Option A)
  | .seq, x, y => K.join x y
  | .and, x, y => K.meetA x y

end

end Goals

end RwLog
