/-
# The symmetric engine

The machine of `lean/SYMMETRIC_ENGINE.md`, with the request rule of
`lean/SYMMETRIC_ENGINE_SIMULATION.md` sections 9.4 and 10 (the split
balance, with goals opened in a request waiting for the next). It is written
once, for arbitrary types of representatives, nodes and answers and an
arbitrary monad, against the derivation kernel (`Trusted/Kernel.lean`). It
can make an answer only by a rule of that kernel, and what it spends is what
the kernel charges.

## Goals and tables

A goal `⟨lb, n, rb⟩` is the relation `lb ; n ; rb` for a node `n` of the
normal form and optional boundaries. Every goal that is opened has a table,
and two goals are the same goal when their nodes are the same node and their
boundaries the same representatives. Tables are never removed, so a table is
named by its position.

A table holds the answers found for its goal, none of them covered by an
earlier one, whether it is complete, and its *strategies* in *groups*, each
group with a *level*.

## Strategies

* A span: the rule `leaf`, once.
* A call: the answers of the goal of its body, by the rule `unfold`.
* A union: the answers of the goal of each member, by the rule `inj`.
* A chain: for every place it can be split in two, one group of three
  strategies. *Join* combines every answer of the left side with every
  answer of the right side, each pair once. *Push left*, once the table of
  the left side is complete, opens for each of its maximal answers the right
  side between the right interface of the answer and the boundary of the
  goal, and joins the answer with the answers of that goal. *Push right* is
  its mirror image.
* A meet: for every member (for the first member of a meet of two), one
  group of three strategies on the member and the meet of the others. *Join*
  conjoins every answer of the one with every answer of the other. A *push*,
  once the table of one side is complete, opens for each of its maximal
  answers the other side between the two interfaces of the answer, and
  conjoins.

A strategy keeps cursors into the tables it reads, so it combines nothing
twice.

## A request

One step of the machine is one request to the root goal. A request gives a
*round* to the root. In its round a goal lets its lowest groups work. If
none of them can do anything, the next lowest work, and so on. A group works
by each of its strategies doing its own work and then by giving a round to
every goal its strategies read. Where a goal has one group its strategies do
everything their inputs allow. Where it has several, each strategy of a
working group does one unit, so that the balance can react. The level of a
group rises by the ticks of its own work and by how much the levels of the
goals it gave a round to rose; the level of a goal is the lowest level of
its groups.

A goal has one round in a request, whoever asks, and a goal met again below
itself adds nothing. A goal opened during a request has its first round in
the next request. So the goals that have a round in a request are among
those open when it starts, and a round is nested no deeper than their
number. That number is what `advance` is given to count down, and it is
never used up.

## Completion

A table is complete when one of its strategies has nothing left to do and
reads only complete tables. For goals that depend on themselves, the machine
computes at the end of every request the largest set of open tables each of
which has a strategy with nothing left to do that reads only tables that are
complete or in the set, and marks them complete.

When the root table is complete the machine is done, and its final report is
the maximal answers of the root table.

The table of a goal that is its own converse holds the converse of every
answer it holds: the converse goes in with the answer. So a run whose root is
its own converse shows, at every step, a set of answers that is its own
converse, which is what the choice of one orientation of the input
(`CostedRuntime.oriented`, `Trusted/Cost.lean`) leaves to the machine.

The interface check of the design note (a strategy that completes a chain
goal with no answer by reading the edges of its sides from the program) is
not in this file, and a goal and its converse do not yet share a table.
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.Framework.Traverse
import RwLog.Lib.Gfp

namespace RwLog

namespace Symmetric

open Traverse

/-- The goal `lb ; node ; rb`. -/
structure GoalOf (S N : Type) where
  lb : Option S
  node : N
  rb : Option S
  deriving DecidableEq

/-- Which rule combines the two sides of a split: `join` for a chain, `meetA`
for a meet. -/
inductive Kind where
  | seq
  | and
  deriving DecidableEq, Repr

/-- The cursor of a join: every pair of the first `na` answers of the one
side and the first `nb` of the other is combined, and `inner` of the pairs
of the next answer. -/
structure Cursor where
  na : Nat
  nb : Nat
  inner : Nat
  deriving DecidableEq, Repr

/-- The next pair of positions to combine in tables of `la` and `lb`
answers, if one is left, and the cursor after it: an answer all of whose
pairs are combined is counted in. The first argument counts the answers not
yet counted in, and is never used up. -/
def Cursor.next (la lb : Nat) : Nat → Cursor → Option (Nat × Nat) × Cursor
  | 0, c => (none, c)
  | f + 1, c =>
    if c.na < la then
      if c.inner < c.nb then (some (c.na, c.inner), { c with inner := c.inner + 1 })
      else Cursor.next la lb f ⟨c.na + 1, c.nb, 0⟩
    else if c.nb < lb then
      if c.inner < c.na then (some (c.inner, c.nb), { c with inner := c.inner + 1 })
      else Cursor.next la lb f ⟨c.na, c.nb + 1, 0⟩
    else (none, c)

/-- What `Cursor.next` is given to count down. -/
def Cursor.room (la lb : Nat) (c : Cursor) : Nat := (la - c.na) + (lb - c.nb) + 1

/-- Every pair still to combine, in order, and the cursor after them. The
first argument counts the pairs and is never used up. -/
def Cursor.all (la lb : Nat) : Nat → Cursor → List (Nat × Nat) × Cursor
  | 0, c => ([], c)
  | f + 1, c =>
    match Cursor.next la lb (c.room la lb) c with
    | (none, c') => ([], c')
    | (some p, c') =>
      let r := Cursor.all la lb f c'
      (p :: r.1, r.2)

/-- Is a pair left to combine? -/
def Cursor.pending (la lb : Nat) (c : Cursor) : Bool := decide (c.na < la) || decide (c.nb < lb)

/-- A strategy of a table, with its cursors. The tables it reads are named
by their positions. -/
inductive Strat (N A : Type) where
  /-- A span: has the rule `leaf` been tried? -/
  | span (ran : Bool)
  /-- A call (`isCall`) reads the table of its body, a union the tables of
  its members, each from the position given. -/
  | copy (isCall : Bool) (subs : List (Nat × Nat))
  /-- Every pair of answers of two tables. -/
  | join (k : Kind) (a b : Nat) (c : Cursor)
  /-- Once the table `side` is complete, its maximal answers are pushed into
  the node `other`. `todo` is the answers still to push, nothing before the
  maximal ones are taken. `subs` is each answer pushed with the table opened
  for it and the position that table is read from. -/
  | push (k : Kind) (left : Bool) (side : Nat) (other : N) (todo : Option (List A))
      (subs : List (A × Nat × Nat))

/-- The strategies of one split, with the level of the group. -/
structure Group (N A : Type) where
  level : Nat
  strats : List (Strat N A)

/-- A table. `self` says the goal is its own converse: its node is the
converse of itself and its two boundaries are the same. `groups` is nothing
until the goal has its first round. `born` is the request the goal was
opened in, `stamp` the last request it had a round in, and `delta` how much
its level rose in that round. -/
structure Table (S N A : Type) where
  goal : GoalOf S N
  self : Bool
  answers : List A
  done : Bool
  groups : Option (List (Group N A))
  born : Nat
  stamp : Nat
  delta : Nat

/-- The machine state: the tables, the root first, the number of requests
made, and how many answers of the root table have been emitted. -/
structure StateOf (S N A : Type) where
  tables : List (Table S N A)
  round : Nat
  shown : Nat

/-- The members a meet of `k` members is split at: the first of two; every
member otherwise. -/
def andSplits (k : Nat) : List Nat := if k ≤ 2 then [0] else List.range k

/-- Change the table at a position. -/
def StateOf.modify {S N A : Type} (st : StateOf S N A) (i : Nat)
    (f : Table S N A → Table S N A) : StateOf S N A :=
  { st with tables := st.tables.modify i f }

/-- The answers of the table at a position. -/
def StateOf.answers {S N A : Type} (st : StateOf S N A) (i : Nat) : List A :=
  match st.tables[i]? with
  | some t => t.answers
  | none => []

/-- Is the goal of the table at a position its own converse? -/
def StateOf.isSelf {S N A : Type} (st : StateOf S N A) (i : Nat) : Bool :=
  match st.tables[i]? with
  | some t => t.self
  | none => false

/-- Is the table at a position complete? -/
def StateOf.isDone {S N A : Type} (st : StateOf S N A) (i : Nat) : Bool :=
  match st.tables[i]? with
  | some t => t.done
  | none => false

/-- The level of a list of groups: the lowest. -/
def levelOf {N A : Type} (gs : List (Group N A)) : Nat :=
  match gs.map (·.level) with
  | [] => 0
  | l :: ls => ls.foldl min l

/-- The levels of a list of groups, each once, lowest first. -/
def levelsOf {N A : Type} (gs : List (Group N A)) : List Nat :=
  ((gs.map (·.level)).mergeSort (· ≤ ·)).eraseDups

section pure

variable {S N A : Type}

/-- The tables a strategy reads now. -/
def Strat.feeds (st : StateOf S N A) : Strat N A → List Nat
  | .span _ => []
  | .copy _ subs => subs.map Prod.fst
  | .join _ a b _ => [a, b]
  | .push _ _ side _ _ subs => if st.isDone side then subs.map (·.2.1) else [side]

/-- Has the strategy work it could do now? -/
def Strat.pending (st : StateOf S N A) : Strat N A → Bool
  | .span ran => !ran
  | .copy _ subs => subs.any fun p => decide (p.2 < (st.answers p.1).length)
  | .join _ a b c => c.pending (st.answers a).length (st.answers b).length
  | .push _ _ side _ todo subs =>
    st.isDone side && (match todo with
      | none => true
      | some l => !l.isEmpty || subs.any fun e => decide (e.2.2 < (st.answers e.2.1).length))

/-- The strategy has nothing left to do and every table it reads passes
`ok`. With `ok` the test for a complete table, the answers of the goal can
no longer grow by this strategy. -/
def Strat.quiet (st : StateOf S N A) (ok : Nat → Bool) (s : Strat N A) : Bool :=
  !s.pending st && (match s with
    | .span ran => ran
    | .copy _ subs => subs.all fun p => ok p.1
    | .join _ a b _ => ok a && ok b
    | .push _ _ side _ todo subs =>
      st.isDone side && todo.isSome && subs.all fun e => ok e.2.1)

/-- The tables that complete at the end of a request: the largest set of
open tables that have had a round, each with a strategy that has nothing
left to do and reads only tables that are complete or in the set. -/
def completing (st : StateOf S N A) : List Nat :=
  let S0 := (List.range st.tables.length).filter fun i =>
    match st.tables[i]? with
    | some t => !t.done && t.groups.isSome
    | none => false
  let ok (X : List Nat) (i : Nat) : Bool :=
    match st.tables[i]? with
    | some t => (t.groups.getD []).any fun g =>
        g.strats.any fun s => s.quiet st fun j => st.isDone j || X.contains j
    | none => false
  gfpFrom ok S0.length S0

end pure

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

/-- Is a goal its own converse? The converse of `lb ; n ; rb` is the converse
of `n` between the exchanged boundaries. -/
def selfConverse (g : GoalOf S N) : M Bool := do
  let c ← K.convNode g.node
  let b ← K.eqNode c g.node
  if b then sameBound (K := K) g.lb g.rb else pure false

/-- The position of the table of a goal, counting from `i`. -/
def indexFrom (g : GoalOf S N) : Nat → List (Table S N A) → M (Option Nat)
  | _, [] => pure none
  | i, t :: ts => do
    let b ← same (K := K) t.goal g
    if b then pure (some i) else indexFrom g (i + 1) ts

/-- The table of a goal: its position, the goal being opened if it has no
table yet. -/
def openGoal (st : StateOf S N A) (g : GoalOf S N) : M (StateOf S N A × Nat) := do
  let i ← indexFrom (K := K) g 0 st.tables
  match i with
  | some i => pure (st, i)
  | none => do
    let self ← selfConverse (K := K) g
    pure ({ st with tables := st.tables ++ [⟨g, self, [], false, none, st.round, 0, 0⟩] },
      st.tables.length)

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

/-- Put an answer in the table at `i`, unless an answer there covers it. -/
def addOne (i : Nat) (st : StateOf S N A) (a : A) : M (StateOf S N A × Bool) := do
  let b ← anyL (fun y => coversA (K := K) y a) (st.answers i)
  pure (if b then (st, false)
    else (st.modify i fun t => { t with answers := t.answers ++ [a] }, true))

/-- Put an answer in the table at `i`, unless an answer there covers it. In
the table of a goal that is its own converse the converse of the answer is
an answer too, and goes in with it: such a table holds the converse of
everything it holds, at every moment. -/
def addAnswer (i : Nat) (st : StateOf S N A) (a : A) : M (StateOf S N A) := do
  let (st, added) ← addOne (K := K) i st a
  if added && st.isSelf i then do
    let a' ← K.swapA a
    let (st, _) ← addOne (K := K) i st a'
    pure st
  else pure st

/-- Put what a rule returned, if anything, in the table at `i`. -/
def addOption (i : Nat) (st : StateOf S N A) : Option A → M (StateOf S N A)
  | none => pure st
  | some a => addAnswer (K := K) i st a

/-! ## The strategies of a goal -/

/-- Combine an answer of the left side with an answer of the right one. -/
def both : Kind → A → A → M (Option A)
  | .seq, x, y => K.join x y
  | .and, x, y => K.meetA x y

/-- Combine an answer that was pushed with an answer of the goal opened for
it. In a chain the answer of the left side comes first; in a meet the answer
pushed does. -/
def pushed : Kind → Bool → A → A → M (Option A)
  | .seq, true, x, y => K.join x y
  | .seq, false, x, y => K.join y x
  | .and, _, x, y => K.meetA x y

/-- The goal opened for an answer `x` that is pushed into the node `other`:
in a chain, the other side between the interface of `x` and the boundary of
the goal; in a meet, the other side between the two interfaces of `x`. -/
def pushGoal (g : GoalOf S N) (other : N) : Kind → Bool → A → M (GoalOf S N)
  | .seq, true, x => do
    let c ← K.rightBound (K.span x)
    pure ⟨c, other, g.rb⟩
  | .seq, false, x => do
    let c ← K.leftBound (K.span x)
    pure ⟨g.lb, other, c⟩
  | .and, _, x => do
    let l ← K.leftBound (K.span x)
    let r ← K.rightBound (K.span x)
    pure ⟨l, other, r⟩

/-- The group of one split: the goals of its two sides are opened. -/
def splitGroup (k : Kind) (L R : GoalOf S N) (st : StateOf S N A) :
    M (StateOf S N A × Group N A) := do
  let (st, a) ← openGoal (K := K) st L
  let (st, b) ← openGoal (K := K) st R
  pure (st, ⟨0, [.join k a b ⟨0, 0, 0⟩, .push k true a R.node none [],
    .push k false b L.node none []]⟩)

/-- The groups of a goal, by the kind of its node. The goals its strategies
read are opened. -/
def expand (g : GoalOf S N) (st : StateOf S N A) : M (StateOf S N A × List (Group N A)) := do
  let v ← K.view g.node
  match v with
  | .span _ => pure (st, [⟨0, [.span false]⟩])
  | .call _ _ => do
    let b ← K.body g.node
    match b with
    | none => pure (st, [⟨0, [.copy true []]⟩])
    | some b => do
      let (st, j) ← openGoal (K := K) st ⟨g.lb, b, g.rb⟩
      pure (st, [⟨0, [.copy true [(j, 0)]]⟩])
  | .union xs => do
    let (st, subs) ← foldL (fun (acc : StateOf S N A × List (Nat × Nat)) x => do
      let (st, j) ← openGoal (K := K) acc.1 ⟨g.lb, x, g.rb⟩
      pure (st, acc.2 ++ [(j, 0)])) (st, []) xs
    pure (st, [⟨0, [.copy false subs]⟩])
  | .chain xs =>
    foldL (fun (acc : StateOf S N A × List (Group N A)) i => do
      let l ← K.interval g.node 0 i
      let r ← K.interval g.node i xs.length
      match l, r with
      | some l, some r => do
        let (st, gr) ← splitGroup (K := K) .seq ⟨g.lb, l, none⟩ ⟨none, r, g.rb⟩ acc.1
        pure (st, acc.2 ++ [gr])
      | _, _ => pure acc) (st, []) ((List.range xs.length).drop 1)
  | .meet xs =>
    foldL (fun (acc : StateOf S N A × List (Group N A)) i => do
      let r ← K.without g.node i
      match xs[i]?, r with
      | some l, some r => do
        let (st, gr) ← splitGroup (K := K) .and ⟨g.lb, l, g.rb⟩ ⟨g.lb, r, g.rb⟩ acc.1
        pure (st, acc.2 ++ [gr])
      | _, _ => pure acc) (st, []) (andSplits xs.length)

/-! ## The work of one strategy -/

/-- A call or a union takes in the answers of the table at `j` from the
position `pos`, each by its rule; `m` is the place of the member in the
union. -/
def copyFrom (i : Nat) (g : GoalOf S N) (isCall : Bool) (m : Nat) (st : StateOf S N A)
    (as : List A) : M (StateOf S N A) :=
  foldL (fun st a => do
    let c ← if isCall then K.unfold a g.node else K.inj a g.node m
    addOption (K := K) i st c) st as

/-- Combine the pairs at the positions given. -/
def joinPairs (i : Nat) (k : Kind) (xs ys : List A) (st : StateOf S N A)
    (ps : List (Nat × Nat)) : M (StateOf S N A) :=
  foldL (fun st p =>
    match xs[p.1]?, ys[p.2]? with
    | some x, some y => do
      let c ← both (K := K) k x y
      addOption (K := K) i st c
    | _, _ => pure st) st ps

/-- Open the goal of each answer that is pushed. -/
def pushOpen (g : GoalOf S N) (other : N) (k : Kind) (left : Bool) (st : StateOf S N A)
    (xs : List A) : M (StateOf S N A × List (A × Nat × Nat)) :=
  foldL (fun (acc : StateOf S N A × List (A × Nat × Nat)) x => do
    let h ← pushGoal (K := K) g other k left x
    let (st, j) ← openGoal (K := K) acc.1 h
    pure (st, acc.2 ++ [(x, j, 0)])) (st, []) xs

/-- Combine an answer that was pushed with the answers given of the goal
opened for it. -/
def pushTake (i : Nat) (k : Kind) (left : Bool) (x : A) (st : StateOf S N A) (ys : List A) :
    M (StateOf S N A) :=
  foldL (fun st y => do
    let c ← pushed (K := K) k left x y
    addOption (K := K) i st c) st ys

/-- The work of one strategy of the table at `i`: everything its inputs
allow (`whole`), or one unit. Returns the state, the strategy with its
cursors moved, and whether anything was done. -/
def work (whole : Bool) (i : Nat) (g : GoalOf S N) (st : StateOf S N A) :
    Strat N A → M (StateOf S N A × Strat N A × Bool)
  | .span true => pure (st, .span true, false)
  | .span false => do
    let a ← K.leaf g.lb g.node g.rb
    let st ← addOption (K := K) i st a
    pure (st, .span true, true)
  | .copy isCall subs =>
    if whole then do
      let st' ← foldL (fun acc (p : (Nat × Nat) × Nat) =>
        copyFrom (K := K) i g isCall p.2 acc ((st.answers p.1.1).drop p.1.2)) st subs.zipIdx
      pure (st', .copy isCall (subs.map fun p => (p.1, max p.2 (st.answers p.1).length)),
        (Strat.copy isCall subs : Strat N A).pending st)
    else
      match subs.zipIdx.find? fun p => decide (p.1.2 < (st.answers p.1.1).length) with
      | none => pure (st, .copy isCall subs, false)
      | some p => do
        let st' ← copyFrom (K := K) i g isCall p.2 st (((st.answers p.1.1).drop p.1.2).take 1)
        pure (st', .copy isCall (subs.modify p.2 fun q => (q.1, q.2 + 1)), true)
  | .join k a b c =>
    let xs := st.answers a
    let ys := st.answers b
    if whole then do
      let r := Cursor.all xs.length ys.length (xs.length * ys.length + 1) c
      let st' ← joinPairs (K := K) i k xs ys st r.1
      pure (st', .join k a b r.2, !r.1.isEmpty)
    else
      match Cursor.next xs.length ys.length (c.room xs.length ys.length) c with
      | (none, c') => pure (st, .join k a b c', false)
      | (some p, c') => do
        let st' ← joinPairs (K := K) i k xs ys st [p]
        pure (st', .join k a b c', true)
  | .push k left side other todo subs =>
    if !st.isDone side then pure (st, .push k left side other todo subs, false)
    else if whole then do
      let xs ← match todo with
        | none => maxima (K := K) (st.answers side)
        | some l => pure l
      let (st1, new) ← pushOpen (K := K) g other k left st xs
      let subs' := subs ++ new
      let st2 ← foldL (fun acc (e : A × Nat × Nat) =>
        pushTake (K := K) i k left e.1 acc ((st1.answers e.2.1).drop e.2.2)) st1 subs'
      pure (st2, .push k left side other (some [])
          (subs'.map fun e => (e.1, e.2.1, max e.2.2 (st1.answers e.2.1).length)),
        (Strat.push k left side other todo subs : Strat N A).pending st)
    else
      match todo with
      | none => do
        let xs ← maxima (K := K) (st.answers side)
        pure (st, .push k left side other (some xs) subs, true)
      | some (x :: rest) => do
        let (st1, new) ← pushOpen (K := K) g other k left st [x]
        pure (st1, .push k left side other (some rest) (subs ++ new), true)
      | some [] =>
        match subs.zipIdx.find? fun p => decide (p.1.2.2 < (st.answers p.1.2.1).length) with
        | none => pure (st, .push k left side other (some []) subs, false)
        | some p => do
          let st' ← pushTake (K := K) i k left p.1.1 st
            (((st.answers p.1.2.1).drop p.1.2.2).take 1)
          pure (st', .push k left side other (some [])
            (subs.modify p.2 fun e => (e.1, e.2.1, e.2.2 + 1)), true)

/-! ## A round -/

/-- The groups of the table at `i`. -/
def groupsAt (st : StateOf S N A) (i : Nat) : List (Group N A) :=
  match st.tables[i]? with
  | some t => t.groups.getD []
  | none => []

/-- Change the group `k` of the table at `i`. -/
def setGroup (st : StateOf S N A) (i k : Nat) (f : Group N A → Group N A) : StateOf S N A :=
  st.modify i fun t => { t with groups := t.groups.map fun gs => gs.modify k f }

/-- The group `k` of the table at `i` works: each of its strategies does its
own work, and then every table they read has its round (`adv`). Returns how
much the level of the group rose, and whether anything was done. -/
def workGroup (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (whole : Bool) (i : Nat)
    (g : GoalOf S N) (k : Nat) (st : StateOf S N A) : M (StateOf S N A × Nat × Bool) := do
  let n := ((groupsAt st i)[k]?.map (·.strats.length)).getD 0
  let (st, d, did) ← foldL (fun (acc : StateOf S N A × Nat × Bool) j =>
    match ((groupsAt acc.1 i)[k]?).bind (·.strats[j]?) with
    | none => pure acc
    | some s => do
      let (r, t) ← K.metered (work (K := K) whole i g acc.1 s)
      let st' := setGroup r.1 i k fun gr => { gr with strats := gr.strats.set j r.2.1 }
      pure (st', if r.2.2 then acc.2.1 + t else acc.2.1, acc.2.2 || r.2.2))
    (st, 0, false) (List.range n)
  let feeds := (((groupsAt st i)[k]?.map (·.strats)).getD []).flatMap (Strat.feeds st)
  let (st, d) ← foldL (fun (acc : StateOf S N A × Nat) h => do
    let (st', dh) ← adv h acc.1
    pure (st', acc.2 + dh)) (st, d) feeds.eraseDups
  pure (setGroup st i k fun gr => { gr with level := gr.level + d }, d, did || decide (0 < d))

/-- The groups of the table at `i` that stand at the level `lv` work.
Returns whether any of them did anything. -/
def workLevel (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (whole : Bool) (i : Nat)
    (g : GoalOf S N) (lv : Nat) (st : StateOf S N A) : M (StateOf S N A × Bool) :=
  foldL (fun (acc : StateOf S N A × Bool) (p : Group N A × Nat) =>
    if p.1.level = lv then do
      let (st', _, did) ← workGroup (K := K) adv whole i g p.2 acc.1
      pure (st', acc.2 || did)
    else pure acc) (st, false) (groupsAt st i).zipIdx

/-- The round of the table at `i`. The first argument is the number of
tables that can still have a round nested in this one. Returns how much the
level of the goal rose. -/
def advance : Nat → Nat → StateOf S N A → M (StateOf S N A × Nat)
  | 0, _, st => pure (st, 0)
  | fuel + 1, i, st =>
    match st.tables[i]? with
    | none => pure (st, 0)
    | some t =>
      if t.done then pure (st, 0)
      else if t.stamp = st.round then pure (st, t.delta)
      else if t.born = st.round then pure (st, 0)
      else do
        K.tick 1
        let st ← match t.groups with
          | some _ => pure st
          | none => do
            let (st', gs) ← expand (K := K) t.goal st
            pure (st'.modify i fun t => { t with groups := some gs })
        let st := st.modify i fun t => { t with stamp := st.round, delta := 0 }
        let gs := groupsAt st i
        let low := levelOf gs
        let whole := decide (gs.length ≤ 1)
        let (st, _) ← foldL (fun (acc : StateOf S N A × Bool) lv =>
          if acc.2 then pure acc
          else workLevel (K := K) (advance fuel) whole i t.goal lv acc.1) (st, false)
          (levelsOf gs)
        let gs' := groupsAt st i
        let fin := gs'.any fun gr => gr.strats.any fun s => s.quiet st st.isDone
        let d := levelOf gs' - low
        pure (st.modify i fun t => { t with done := t.done || fin, delta := d }, d)

/-- One request: a round of the root, and then the tables that complete
together are marked. Returns the answers the root table gained. A request
costs at least one tick. -/
def request (st : StateOf S N A) : M (StateOf S N A × List A) := do
  K.tick 1
  let st : StateOf S N A := { st with round := st.round + 1 }
  let (st, _) ← advance (K := K) st.tables.length 0 st
  let C := completing st
  let st : StateOf S N A :=
    { st with tables := st.tables.mapIdx fun i t => if C.contains i then { t with done := true } else t }
  let new := (st.answers 0).drop st.shown
  pure ({ st with shown := (st.answers 0).length }, new)

/-- A step: a request, or the final report when the root table is
complete. -/
def step (st : StateOf S N A) : M (StepOf A (StateOf S N A)) :=
  match st.tables.head? with
  | none => pure (.done [])
  | some t =>
    if t.done then do
      let fin ← maxima (K := K) t.answers
      pure (.done fin)
    else do
      let r ← request (K := K) st
      pure (.emit r.2 r.1)

/-- The first state: the table of the root goal alone. -/
def init (root : N) : M (StateOf S N A) := do
  let self ← selfConverse (K := K) ⟨none, root, none⟩
  pure ⟨[⟨⟨none, root, none⟩, self, [], false, none, 0, 0, 0⟩], 0, 0⟩

end

/-- The symmetric engine. Its first state is the table of the root goal
alone. -/
def engine : Engine where
  State := StateOf
  init root := init root
  step st := step st

end Symmetric

end RwLog
