/-
# The tabled round machine

The tabled machine evaluates *goals*. A goal `⟨lb, n, rb⟩` is the relation
`lb ; n ; rb`, where `n` is a node of the normal form of the query or of a
body (`Kernel/NormalForm.lean`) and the optional boundaries are
representatives that relate a term only to itself. Every goal gets a table,
and two goals are the same goal when their nodes are the same node and their
boundaries the same representatives, so recursive calls with the same
boundaries share one table.

The machine is written once, for arbitrary types of representatives, nodes
and answers and an arbitrary monad, against the derivation kernel
(`Trusted/Kernel.lean`). It can make an answer only by a rule of that kernel,
and what it spends is what the kernel charges. There is no second copy of it.

## Rounds

One step is one round. In a round every incomplete table recomputes its
candidate answers from the answers all tables held at the start of the round,
and then all tables are updated at once. Each step emits the answers the root
table gained in that round.

## What a goal computes

A goal reads its node (`view`) and computes by the kind of the node.

* A span: the rule `leaf`.
* A union: the answers of the goal of each member, with the same boundaries,
  each by the rule `inj`. The empty union has no answer.
* A call: the answers of the goal of the body, by the rule `unfold`.
* A chain or a meet is *split* in two, and each split runs three strategies
  side by side:
  - *join*: combine every answer of the left sub-goal with every answer of
    the right one (the rules `join` and `meetA`);
  - *push left*: once the left sub-goal is complete, take each of its maximal
    answers `x` and run the right side with the interface of `x` as a
    boundary;
  - *push right*: the mirror image.

  A chain of two members is split between them. A longer chain is split
  after its first member and before its last one: the normal form does not
  keep how a chain was bracketed, and these two splits are each other's
  mirror image, so a goal and its converse are evaluated as mirror images. A
  meet of two members is split into the two. A larger meet is split into
  each member and the meet of the others, for every member: the order of the
  members of a meet is not the same in a node and in its converse.

Beside these every incomplete table asks the *unfolding race* once a round:
an oracle that says, for a goal and a depth, whether the goal's unfolding to
that depth is final and, if it is, what its answers are
(`Rungs/Tabled/Unfold.lean`). The depth is the number of rounds run.

A candidate enters a table unless it is covered by an answer already there or
strictly covered by another candidate of the same round; among equal
candidates one is kept. So no table holds an answer covered by an earlier
one.

## Completion

A table is complete when its answers can no longer grow. At the end of a
round the machine computes the largest set `S` of incomplete tables such that
each table in `S` gained nothing this round and has a strategy all of whose
dependencies existed at the start of the round, gained nothing, and are
complete or in `S`. Every table in `S` is then marked complete. A goal whose
unfolding is final has a strategy with no dependencies.

When the root table is complete the machine is done, and its final report is
the maximal answers of the root table.
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.Framework.Traverse
import RwLog.Lib.Gfp

namespace RwLog

namespace Tabled

open Traverse

/-- The goal `lb ; node ; rb`. -/
structure GoalOf (S N : Type) where
  lb : Option S
  node : N
  rb : Option S

/-- A table: a goal, the answers found so far, and whether it is complete. -/
structure TableOf (S N A : Type) where
  goal : GoalOf S N
  answers : List A
  done : Bool

/-- The machine state: the tables, the root first, and the number of rounds
run, which is the depth the unfolding race is asked at. -/
structure StateOf (S N A : Type) where
  tables : List (TableOf S N A)
  depth : Nat

/-- The unfolding race: is the goal's unfolding to this depth final, and its
answers if it is (none otherwise). -/
abbrev GOracle (S N A : Type) (M : Type → Type) := Nat → GoalOf S N → M (Bool × List A)

/-- An unfolding race for every derivation kernel. -/
abbrev Unfolder :=
  {S N A : Type} → {M : Type → Type} → [DerivationKernel S N A M] → GOracle S N A M

/-- Which rule combines the two sides of a split: `join` for a chain, `meetA`
for a meet. -/
inductive Kind where
  | seq
  | and
  deriving DecidableEq, Repr

/-- The split points of a chain of `k` members: between the two members of a
chain of two; after the first and before the last member otherwise. -/
def seqSplits (k : Nat) : List Nat := if k ≤ 2 then [1] else [1, k - 1]

/-- The members a meet of `k` members is split at: the first of two; every
member otherwise. -/
def andSplits (k : Nat) : List Nat := if k ≤ 2 then [0] else List.range k

section

variable {S N A : Type} {M : Type → Type} [K : DerivationKernel S N A M]

/-! ## Tables -/

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

def findTable (ts : List (TableOf S N A)) (g : GoalOf S N) : M (Option (TableOf S N A)) :=
  findL (fun t => same (K := K) t.goal g) ts

/-- The position of the table of a goal, counting from `i`. -/
def indexFrom (g : GoalOf S N) : Nat → List (TableOf S N A) → M (Option Nat)
  | _, [] => pure none
  | i, t :: ts => do
    let b ← same (K := K) t.goal g
    if b then pure (some i) else indexFrom g (i + 1) ts

def indexOf (ts : List (TableOf S N A)) (g : GoalOf S N) : M (Option Nat) :=
  indexFrom (K := K) g 0 ts

/-- The answers a goal has so far. -/
def answersOf (ts : List (TableOf S N A)) (g : GoalOf S N) : M (List A) := do
  let t ← findTable (K := K) ts g
  pure (match t with
    | some t => t.answers
    | none => [])

/-- The goal's table exists and is complete. -/
def doneOf (ts : List (TableOf S N A)) (g : GoalOf S N) : M Bool := do
  let t ← findTable (K := K) ts g
  pure (match t with
    | some t => t.done
    | none => false)

/-! ## Answers of one table -/

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

/-! ## Splits -/

/-- The two sub-goals of every split of a chain or a meet, with the rule that
combines them. A node of another kind has no split. -/
def splitsOf (g : GoalOf S N) :
    NodeView Unit N → M (List (Kind × GoalOf S N × GoalOf S N))
  | .chain xs => filterMapL (fun i => do
      let l ← K.interval g.node 0 i
      let r ← K.interval g.node i xs.length
      pure (match l, r with
        | some l, some r => some (Kind.seq, ⟨g.lb, l, none⟩, ⟨none, r, g.rb⟩)
        | _, _ => none)) (seqSplits xs.length)
  | .meet xs => filterMapL (fun i => do
      let r ← K.without g.node i
      pure (match xs[i]?, r with
        | some l, some r => some (Kind.and, ⟨g.lb, l, g.rb⟩, ⟨g.lb, r, g.rb⟩)
        | _, _ => none)) (andSplits xs.length)
  | _ => pure []

/-- Combine an answer of the left sub-goal with an answer of the right one. -/
def both : Kind → A → A → M (Option A)
  | .seq, x, y => K.join x y
  | .and, x, y => K.meetA x y

/-- The goal the push-left strategy runs for an answer `x` of the left
sub-goal: the right side, with the interface of `x` as a boundary. -/
def pushL (g R : GoalOf S N) : Kind → A → M (GoalOf S N)
  | .seq, x => do
    let c ← K.rightBound (K.span x)
    pure ⟨c, R.node, g.rb⟩
  | .and, x => do
    let l ← K.leftBound (K.span x)
    let r ← K.rightBound (K.span x)
    pure ⟨l, R.node, r⟩

/-- The goal the push-right strategy runs for an answer `y` of the right
sub-goal. -/
def pushR (g L : GoalOf S N) : Kind → A → M (GoalOf S N)
  | .seq, y => do
    let c ← K.leftBound (K.span y)
    pure ⟨g.lb, L.node, c⟩
  | .and, y => do
    let l ← K.leftBound (K.span y)
    let r ← K.rightBound (K.span y)
    pure ⟨l, L.node, r⟩

/-- Combine an answer `y` of the right sub-goal with an answer `x` of the
goal pushed for it. The answer that was pushed comes first in a meet. -/
def fromR : Kind → A → A → M (Option A)
  | .seq, y, x => K.join x y
  | .and, y, x => K.meetA y x

/-- Each answer with the goal pushed for it. -/
def pushes (f : A → M (GoalOf S N)) (xs : List A) : M (List (A × GoalOf S N)) :=
  mapL (fun x => do
    let p ← f x
    pure (x, p)) xs

/-- The candidates of one split, and its strategies: the goals each of them
depends on. -/
def way (ts : List (TableOf S N A)) (g : GoalOf S N) (w : Kind × GoalOf S N × GoalOf S N) :
    M (List A × List (List (GoalOf S N))) := do
  let k := w.1
  let L := w.2.1
  let R := w.2.2
  let xs ← answersOf (K := K) ts L
  let ys ← answersOf (K := K) ts R
  let join ← flatMapL (fun x => filterMapL (fun y => both (K := K) k x y) ys) xs
  let dl ← doneOf (K := K) ts L
  let pl ← if dl then do
      let m ← maxima (K := K) xs
      pushes (pushL (K := K) g R k) m
    else pure []
  let dr ← doneOf (K := K) ts R
  let pr ← if dr then do
      let m ← maxima (K := K) ys
      pushes (pushR (K := K) g L k) m
    else pure []
  let cl ← flatMapL (fun p => do
    let ys' ← answersOf (K := K) ts p.2
    filterMapL (fun y => both (K := K) k p.1 y) ys') pl
  let cr ← flatMapL (fun p => do
    let xs' ← answersOf (K := K) ts p.2
    filterMapL (fun x => fromR (K := K) k p.1 x) xs') pr
  pure (join ++ cl ++ cr,
    [[L, R]] ++ (if dl then [L :: pl.map Prod.snd] else []) ++
      (if dr then [R :: pr.map Prod.snd] else []))

/-! ## Candidates and strategies -/

/-- The candidates a goal computes from the tables, and its strategies. -/
def produceTables (ts : List (TableOf S N A)) (g : GoalOf S N) :
    M (List A × List (List (GoalOf S N))) := do
  let v ← K.view g.node
  match v with
  | .span _ => do
    let a ← K.leaf g.lb g.node g.rb
    pure (a.toList, [[]])
  | .call _ _ => do
    let b ← K.body g.node
    match b with
    | none => pure ([], [[]])
    | some b => do
      let gb : GoalOf S N := ⟨g.lb, b, g.rb⟩
      let xs ← answersOf (K := K) ts gb
      let ys ← filterMapL (fun x => K.unfold x g.node) xs
      pure (ys, [[gb]])
  | .union xs => do
    let gs : List (GoalOf S N) := xs.map fun x => ⟨g.lb, x, g.rb⟩
    let ys ← flatMapL (fun p => do
      let as ← answersOf (K := K) ts p.1
      filterMapL (fun a => K.inj a g.node p.2) as) gs.zipIdx
    pure (ys, [gs])
  | v => do
    let ws ← splitsOf (K := K) g v
    let rs ← mapL (way (K := K) ts g) ws
    pure (rs.flatMap Prod.fst, rs.flatMap Prod.snd)

/-- The candidates and the strategies of a goal, given what the unfolding
race said about it: its answers, and a strategy with no dependencies, when
its unfolding is final. -/
def produce (ts : List (TableOf S N A)) (g : GoalOf S N) (u : Bool × List A) :
    M (List A × List (List (GoalOf S N))) := do
  let r ← produceTables (K := K) ts g
  pure (u.2 ++ r.1, (if u.1 then [[]] else []) ++ r.2)

end

/-! ## One round -/

/-- The tables that complete at the end of a round. `done` and `gained` say
of each table at the start of the round whether it was complete and whether
it gained an answer in the round; `deps` are its strategies, each dependency
as the position of its table, if it had one. -/
def completing (done gained : List Bool) (deps : List (List (List (Option Nat)))) : List Nat :=
  let S0 := (List.range done.length).filter fun i => !done.getD i false && !gained.getD i true
  let ok (S : List Nat) (i : Nat) : Bool :=
    (deps.getD i []).any fun strat => strat.all fun
      | none => false
      | some j => !gained.getD j true && (done.getD j false || S.contains j)
  gfpFrom ok S0.length S0

section

variable {S N A : Type} {M : Type → Type} [K : DerivationKernel S N A M]

/-- Add a goal unless it has a table or is already there. -/
def addGoal (acc : List (GoalOf S N)) (p : GoalOf S N × Option Nat) : M (List (GoalOf S N)) :=
  match p.2 with
  | some _ => pure acc
  | none => do
    let b ← anyL (fun h => same (K := K) h p.1) acc
    pure (if b then acc else acc ++ [p.1])

/-- One round: every incomplete table asks the unfolding race and recomputes
its candidates, and the tables are updated at once. Returns the new state
and the answers the root table gained. A round costs at least one tick. -/
def round (U : GOracle S N A M) (st : StateOf S N A) : M (StateOf S N A × List A) := do
  let ts := st.tables
  K.tick 1
  let us ← mapL (fun t => if t.done then pure (false, []) else U st.depth t.goal) ts
  let outs ← mapL (fun p => if p.1.done then pure ([], []) else produce (K := K) ts p.1.goal p.2)
    (ts.zip us)
  let ts1 ← mapL (fun p => do
    let f ← fresh (K := K) p.1.answers p.2.1
    pure ({ p.1 with answers := p.1.answers ++ f } : TableOf S N A)) (ts.zip outs)
  let reqs ← mapL (fun o => mapL (fun strat => mapL (fun d => do
    let i ← indexOf (K := K) ts d
    pure (d, i)) strat) o.2) outs
  let newGoals ← foldL (addGoal (K := K)) [] reqs.flatten.flatten
  let gained := (ts.zip ts1).map fun p => decide (p.2.answers.length ≠ p.1.answers.length)
  let C := completing (ts.map (·.done)) gained (reqs.map fun o => o.map fun s => s.map Prod.snd)
  let ts2 : List (TableOf S N A) :=
    ts1.mapIdx fun i t => if C.contains i then { t with done := true } else t
  let ts3 : List (TableOf S N A) := ts2 ++ newGoals.map fun g => ⟨g, [], false⟩
  let rootNew := match ts.head?, ts1.head? with
    | some t, some t' => t'.answers.drop t.answers.length
    | _, _ => []
  pure (⟨ts3, st.depth + 1⟩, rootNew)

/-- A step: a round, or the final report when the root table is complete. -/
def step (U : GOracle S N A M) (st : StateOf S N A) : M (StepOf A (StateOf S N A)) :=
  match st.tables.head? with
  | none => pure (.done [])
  | some t =>
    if t.done then do
      let fin ← maxima (K := K) t.answers
      pure (.done fin)
    else do
      let r ← round (K := K) U st
      pure (.emit r.2 r.1)

end

/-- The tabled round machine with a given unfolding race, as an engine. Its
first state is the table of the root goal alone. -/
def engine (U : Unfolder) : Engine where
  State := StateOf
  init root := pure ⟨[⟨⟨none, root, none⟩, [], false⟩], 0⟩
  step st := step U st

end Tabled

end RwLog
