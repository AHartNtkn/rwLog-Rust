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
  answer of the right side, each pair once. *Push left* opens, for each
  answer of the left side as it arrives, the right side between the right
  interface of the answer and the boundary of the goal, and joins the answer
  with the answers of that goal. *Push right* is its mirror image.
* A meet: for every member (for the first member of a meet of two), one
  group of three strategies on the member and the meet of the others. *Join*
  conjoins every answer of the one with every answer of the other. A *push*
  opens, for each answer of one side as it arrives, the other side between
  the two interfaces of the answer, and conjoins.

A strategy keeps cursors into the tables it reads, so it combines nothing
twice. It takes its units in an order that
reaches everything, however fast the tables it reads grow: a strategy that
reads several tables reads next the one it has read least, and a join shares
its ticks among its pairs by where their answers came from.

An answer has a *path*: for each union on the way to it, the member chosen
and the number of members (`Table.paths`). A union puts its choice before the
path of the answer it copies, a call keeps the path, and a join puts the
paths of its two answers one after the other. A join files the answers of
its tables by their paths (`Cursor.see`). The pairs whose answers came from
the same choices so far are a *class*, and the join shares its ticks among
the classes of one choice as a union shares its ticks among its members: the
class fed least that has a pair left is served, and so on down to a single
class, where the pair of the earliest answers is taken (`Cursor.next`). So a
pair waits for the pairs of other choices by the number of members at each
choice on the way to it, and not by how many answers the other members
have.

A push does not wait for its side to be complete: a side that is a union
with a member that never finishes is never complete, and the answers of its
other members would never be pushed. A push shares its ticks as a join does.
Its units are opening the goal of an answer of its side, and combining an
answer whose goal is open with an answer of that goal. Each is filed with the
cursor of the push as a pair is filed with the cursor of a join, the path of
the answer of the side first (`Cursor.opened`, `Cursor.read`), and the unit
of the least key is taken. So opening goals for the answers of one member of
a union does not keep the push from the answers of another.

Once the side is complete, an answer of it that a later answer of it covers
is *superseded* (`supersede`, `superseded`): what it would give, the answer
that covers it gives. The cover tests are made once, when the push first
works with its side complete; a side that never completes is never tested.
The units of the superseded are taken off the cursor (`Cursor.kill`), the
goals opened for them are read no more, and the push has nothing left to do
without them. So whether a goal completes does not depend on the order in
which the answers of a side arrive: the answers not superseded are the
maximal answers of the side, and only the goals opened for those have to
complete.

## A request

One step of the machine is one request to the root goal. A request gives a
*round* to the root. In its round a goal lets its lowest groups work. If
none of them does anything, the next lowest work, and so on. A group works
by each of its strategies having a *turn* and then by giving a round to
every goal its strategies read. The level of a group rises by the ticks of
its own work and by how much the levels of the goals it gave a round to
rose; the level of a goal is the lowest level of its groups.

A turn is a bounded amount of work, counted in ticks. It is worth
`turnTicks` ticks for each unit of the *weight* of the strategy: one for the
strategy itself, and for each table it reads the number of strategies that
work for that table, its own and those of every table read from it through
any number of strategies. So a strategy is given as much as what feeds it is
given together, and a table that several strategies fill is read as fast as
it is filled. In its turn a strategy does unit after unit until it has spent
what the turn is worth or can do nothing more. A unit is not divided: the
last one is done whole, and what it cost beyond the turn the strategy
*owes*. A strategy that owes has that much less in its next turn, and if it
owes a whole turn or more it does nothing and owes a turn less. So over any
number of rounds a strategy spends what its turns were worth and at most one
unit more, whatever its units cost.

The weights are counted from the state as it stands, and counting them is
not charged, like the rest of the bookkeeping of a request (the levels, the
tables that complete together). An implementation has to keep them as tables
are opened.

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

## The interface check

A chain goal can be complete with no answer although neither side of any
split ever completes: `p ; q` where every answer of `p` ends in a constructor
that no answer of `q` begins with. For each split and each side that
contains a call, the machine reads from the program the spans the answers
of that side can end with (for the right side: begin with): it follows the
edge of the node inwards, composing adjacent spans, through unions and
through each call once (`runs`). The other side is opened under the
interface of each of those spans, as ordinary goals. If all of them complete
with no answer, the chain goal is complete. The checks of a goal are one
group of their own. A check makes no answer.

A node is an identifier, and nothing tells the machine how deep the program
below it is. So a reading is given a depth and says when the depth was not
enough. The state holds the depth readings are tried at (`StateOf.depth`),
and it doubles whenever one fails: a depth larger than needed costs nothing,
and a reading that failed is tried again by its check, in its next unit of
work. What was read is kept (`StateOf.edges`), so each side is read once
whatever the number of goals on its node, and once the depth of the program
is reached every side is read when the groups of its goal are made. A check
that is not offered (its side has no call, or one of the interfaces
restricts nothing) is not made. A check one of whose goals has an answer can
do nothing more, and a group of such checks is removed from its table.

## The unfolding race

The check reads one span through a call, and a clash can lie deeper on both
sides (`SYMMETRIC_ENGINE_SIMULATION.md`, section 11). So every chain goal
has an *unfolding race* (`Rungs/Framework/RaceSpec.lean`): asked for a goal
and a depth, it says whether the unfolding of the goal to that depth is
final and, if it is, gives its answers. The race stands beside the groups of
its goal: it takes no turn and is no part of any level. At the end of a round
of the goal it asks once at its next depth. Its budget is the ticks of the
goal's own strategies plus the number of rounds the goal has had, and an ask
may cost what is left of the budget and no more (`Kernel.within`). An ask
that needs more is given up, what it was allowed is charged to the race, and
the next ask is made when twice as much is left (with nothing left no ask is
made); so the asks given up at one
depth cost together less than twice the ask that succeeds. A final verdict
puts the answers in the table and completes the goal. A goal that is not
complete has rounds as long as it is asked for, so its race is asked at
every depth. Only a chain has a race: the verdict of the unfolding of a
call, a union or a meet is made of the verdicts of its body or members.

A goal and its converse do not share a table: no exact property needs it,
and whether it would save anything is not measured (design note, section 1).
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.Framework.RaceSpec
import RwLog.Lib.Gfp

namespace RwLog

namespace Symmetric

open Traverse

export Goals (GoalOf GoalOf.mk GoalOf.lb GoalOf.node GoalOf.rb toGoal Kind Kind.seq Kind.and
  andSplits
  sameBound same indexFrom coversA maxima both)

/-- Where an answer came from: for each union on the way to it, the member
chosen and the number of members, the outermost union first. -/
abbrev Path := List (Nat × Nat)

/-- One step on the way down to a pair of answers of a join: a choice on the
path of the first answer (`0`), one on the path of the second (`1`), each with
the member chosen and the number of members, or the end of both paths
(`2`). -/
abbrev Step := Nat × Nat × Nat

/-- The steps down to a pair of answers with the paths `u` and `v`: the
choices of the first answer, those of the second, and the end. -/
def stepsOf (u v : Path) : List Step :=
  (u.map fun e => (0, e)) ++ (v.map fun e => (1, e)) ++ [(2, 0, 0)]

/-- The cursor of a join. `pa` and `pb` are the paths of the answers of its
two tables, as far as it has filed them; `todo` is the pairs of positions of
answers filed that it has not combined, and `done` those it has; `fed` is,
for each run of steps down to a pair combined, the ticks the pairs of those
steps cost. A *class* of pairs is a beginning of the steps of a pair: the
pairs whose answers came from those choices. A class has no work but that of
its pairs. -/
structure Cursor where
  pa : List Path
  pb : List Path
  todo : List (Nat × Nat)
  done : List (Nat × Nat)
  fed : List (List Step × Nat)
  deriving DecidableEq, Repr

/-- The cursor of a join that has combined nothing. -/
def Cursor.start : Cursor := ⟨[], [], [], [], []⟩

/-- The pairs of positions below `a1` and `b1` that are not both below `a0`
and `b0`: the pairs that tables of `a0` and `b0` answers gain when they grow
to `a1` and `b1`. -/
def pairsNew (a0 b0 a1 b1 : Nat) : List (Nat × Nat) :=
  ((List.range' a0 (a1 - a0)).flatMap fun i => (List.range b1).map fun j => (i, j)) ++
    ((List.range a0).flatMap fun i => (List.range' b0 (b1 - b0)).map fun j => (i, j))

/-- The cursor with the answers filed that its tables have gained: `pa` and
`pb` are the paths of all their answers now. The path of an answer that was
filed stays, and the pairs with an answer newly filed are still to
combine. -/
def Cursor.see (pa pb : List Path) (c : Cursor) : Cursor :=
  let pa' := c.pa ++ pa.drop c.pa.length
  let pb' := c.pb ++ pb.drop c.pb.length
  { c with pa := pa', pb := pb',
           todo := c.todo ++ pairsNew c.pa.length c.pb.length pa'.length pb'.length }

/-- The ticks spent on the pairs of a class. -/
def Cursor.fedOf (c : Cursor) (k : List Step) : Nat :=
  ((c.fed.filter fun e => k.isPrefixOf e.1).map (·.2)).sum

/-- Count `t` ticks more for the pairs of the steps `ss`. -/
def bump (ss : List Step) (t : Nat) : List (List Step × Nat) → List (List Step × Nat)
  | [] => [(ss, t)]
  | e :: l => if e.1 = ss then (e.1, e.2 + t) :: l else e :: bump ss t l

/-- The steps down to the pair at the positions `p`. -/
def Cursor.stepsAt (c : Cursor) (p : Nat × Nat) : List Step :=
  stepsOf (c.pa.getD p.1 []) (c.pb.getD p.2 [])

/-- The place of a class among its siblings: what it was fed and one tick
more, once for each member of its choice and once more, and then its member.
Among the members of one choice this is the order by what each was fed, the
earlier member first of two fed alike; and whatever choices the siblings come
from, only finitely many places come before any place. -/
def Cursor.place (c : Cursor) (k : List Step) (s : Step) : Nat :=
  (c.fedOf k + 1) * (s.2.2 + 1) + s.2.1

/-- The entry of the key of a pair for its class at the depth `i`: the place
of the class, and its step. -/
def Cursor.group (c : Cursor) (ss : List Step) (i : Nat) : List Nat :=
  let s := ss.getD i (2, 0, 0)
  [c.place (ss.take (i + 1)) s, s.1, s.2.1, s.2.2]

/-- The key of a pair: the entry of each of its classes, the widest first,
and last the pair by the later of its two positions. -/
def Cursor.keyOf (c : Cursor) (p : Nat × Nat) : List (List Nat) :=
  ((List.range (c.stepsAt p).length).map (c.group (c.stepsAt p))) ++ [[max p.1 p.2, p.1, p.2]]

/-- Of the entries of a list, the first that no other comes before in the
order given. -/
def chooseBy {α : Type} (lt : α → α → Bool) (l : List α) : Option α :=
  l.foldl (fun best p =>
    match best with
    | none => some p
    | some b => if lt p b then some p else some b) none

/-- The next pair of positions to combine among the answers filed, if one is
left: the pair of the least key. The ticks of a join are shared among the
classes as a union shares its ticks among its members: of the classes of one
choice that have a pair left, the one fed least is served, and so on down to a
single class, where the pair of the earliest answers is taken. So a pair
waits for the pairs of other choices by the number of members at each choice
on the way to it, and not by how many answers the other members have. -/
def Cursor.next (c : Cursor) : Option (Nat × Nat) :=
  chooseBy (fun p b => decide (c.keyOf p < c.keyOf b)) c.todo

/-- The cursor after the pair `p` was combined at `t` ticks: every class of
the pair has been fed that much. -/
def Cursor.mark (c : Cursor) (p : Nat × Nat) (t : Nat) : Cursor :=
  { c with todo := c.todo.filter fun x => x != p, done := p :: c.done,
           fed := bump (c.stepsAt p) t c.fed }

/-- The cursor of a push with one more answer of its side seen, of the path
`pth`. -/
def Cursor.opened (pth : Path) (c : Cursor) : Cursor :=
  { c with pa := c.pa ++ [pth] }

/-- The cursor of a push with one more unit filed for the answer of the side
at `s`: `pth` is the path of the answer to combine it with, and empty for the
unit that opens its goal. The unit is still to take. -/
def Cursor.read (s : Nat) (pth : Path) (c : Cursor) : Cursor :=
  { c with pb := c.pb ++ [pth], todo := c.todo ++ [(s, c.pb.length)] }

/-- The cursor of a push without the units of the answers of its side at the
positions `dead`: they are not to take any more. -/
def Cursor.kill (dead : List Nat) (c : Cursor) : Cursor :=
  { c with todo := c.todo.filter fun x => !dead.contains x.1 }

/-- Is a pair left to combine in tables of `la` and `lb` answers: one of
answers filed, or one with an answer not filed yet? -/
def Cursor.pending (la lb : Nat) (c : Cursor) : Bool :=
  !c.todo.isEmpty || (decide (c.pa.length < la) && decide (0 < lb)) ||
    (decide (c.pb.length < lb) && decide (0 < la))

/-- The state of an interface check: its side is still to be read; it is not
offered; or the tables of the goals opened for the interfaces. -/
inductive Check where
  | reading
  | off
  | opened (subs : List Nat)

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
  /-- The answers of the table `side` are pushed into the node `other`, each
  as it arrives. `subs` is the answers of the side seen, in the order of the
  table, each with the table opened for it, once it is opened, and how many
  answers of that table are filed. `dead` is the positions in `subs` of the
  answers superseded, those a later answer covers, once the side is complete
  and they are known. Nothing more is done for them, and the goal completes
  without them, since what they give the answer that covers them gives. `reads` is the units filed, each with the
  position in `subs` of its answer of the side: opening the goal of that
  answer (`none`), or combining it with the answer at a position of its table.
  The cursor `c` has the paths of the answers seen and of the units filed,
  and the units still to take. The cursor `fc` shares the rounds the push
  gives the tables it opened: a unit of it is one round offered to the table
  of the answer of the side at its first position (`feedPush`). -/
  | push (k : Kind) (left : Bool) (side : Nat) (other : N)
      (subs : List (A × Option (Nat × Nat))) (dead : Option (List Nat))
      (reads : List (Nat × Option Nat)) (c : Cursor) (fc : Cursor)
  /-- The interface check of one split of a chain: the node `side` (the left
  side of the split if `left`) is read from the program, and the node `other`
  is opened under each interface it can show. -/
  | check (left : Bool) (side other : N) (c : Check)

/-- The strategies of one split, with the level of the group, and what each
strategy owes: the ticks its last turn cost beyond what the turn was worth,
less what its turns since were worth (nothing for a strategy `owed` has no
entry for). -/
structure Group (N A : Type) where
  level : Nat
  strats : List (Strat N A)
  owed : List Nat

/-- The unfolding race of a chain goal: the depth it asks at next, the ticks
its asks have cost, and the budget of the last ask it gave up at this depth
(nothing given up: 0). -/
structure Race where
  depth : Nat
  spent : Nat
  gaveUp : Nat
  deriving DecidableEq

/-- A table. `self` says the goal is its own converse: its node is the
converse of itself and its two boundaries are the same. `groups` is nothing
until the goal has its first round. `born` is the request the goal was
opened in, `stamp` the last request it had a round in, and `delta` how much
its level rose in that round. `race` is the unfolding race of a chain goal,
from its first round on; `own` is the ticks of the work of the goal's own
strategies, and `rounds` the number of rounds it has had. `fed` is the ticks
its rounds have cost the strategies that gave them. -/
structure Table (S N A : Type) where
  goal : GoalOf S N
  self : Bool
  answers : List A
  done : Bool
  groups : Option (List (Group N A))
  born : Nat
  stamp : Nat
  delta : Nat
  race : Option Race
  own : Nat
  rounds : Nat
  fed : Nat
  paths : List Path

/-- The machine state: the tables, the root first, the number of requests
made, how many answers of the root table have been emitted, and the edges
read so far: for a node and an end of it (its last end if the flag is set),
the interfaces its answers can show there, or nothing if a check on it is
not offered; and the depth edges are read to. -/
structure StateOf (S N A : Type) where
  tables : List (Table S N A)
  round : Nat
  shown : Nat
  edges : List (N × Bool × Option (List S))
  depth : Nat

/-- Change the table at a position. -/
def StateOf.modify {S N A : Type} (st : StateOf S N A) (i : Nat)
    (f : Table S N A → Table S N A) : StateOf S N A :=
  { st with tables := st.tables.modify i f }

/-- The answers of the table at a position. -/
def StateOf.answers {S N A : Type} (st : StateOf S N A) (i : Nat) : List A :=
  match st.tables[i]? with
  | some t => t.answers
  | none => []

/-- The paths of the answers of the table at a position, one for each
answer: the empty path for an answer that was given none. -/
def StateOf.pathsAt {S N A : Type} (st : StateOf S N A) (i : Nat) : List Path :=
  match st.tables[i]? with
  | some t => (List.range t.answers.length).map fun n => t.paths.getD n []
  | none => []

/-- Give the path `pth` to the answers the table at `i` has gained since it
had `n`. An answer that was given no path has the empty one. -/
def stamp {S N A : Type} (i n : Nat) (pth : Path) (st : StateOf S N A) : StateOf S N A :=
  st.modify i fun t =>
    let ps := t.paths ++ List.replicate (n - t.paths.length) []
    { t with paths := ps ++ List.replicate (t.answers.length - ps.length) pth }

/-- Is the goal of the table at a position its own converse? -/
def StateOf.isSelf {S N A : Type} (st : StateOf S N A) (i : Nat) : Bool :=
  match st.tables[i]? with
  | some t => t.self
  | none => false

/-- What the table at a position has been fed. -/
def StateOf.fedAt {S N A : Type} (st : StateOf S N A) (i : Nat) : Nat :=
  match st.tables[i]? with
  | some t => t.fed
  | none => 0

/-- Is the table at a position complete? -/
def StateOf.isDone {S N A : Type} (st : StateOf S N A) (i : Nat) : Bool :=
  match st.tables[i]? with
  | some t => t.done
  | none => false

/-- Of the entries that pass `ok`, the first with the least key. -/
def leastBy {α : Type} (key : α → Nat) (ok : α → Bool) (l : List α) : Option α :=
  (l.filter ok).foldl (fun best x =>
    match best with
    | none => some x
    | some b => if key x < key b then some x else some b) none

theorem mem_of_leastBy {α : Type} {key : α → Nat} {ok : α → Bool} {l : List α} {x : α}
    (h : leastBy key ok l = some x) : x ∈ l := by
  have main : ∀ (ys : List α) (best : Option α),
      ys.foldl (fun best x =>
        match best with
        | none => some x
        | some b => if key x < key b then some x else some b) best = some x →
      x ∈ ys ∨ best = some x := by
    intro ys
    induction ys with
    | nil => intro best h; exact .inr h
    | cons y ys ih =>
      intro best h
      rcases ih _ h with h' | h'
      · exact .inl (List.mem_cons_of_mem _ h')
      · cases best with
        | none => cases h'; exact .inl List.mem_cons_self
        | some b =>
          simp only at h'
          split at h'
          · cases h'; exact .inl List.mem_cons_self
          · exact .inr h'
  rcases main _ _ h with h' | h'
  · exact List.mem_of_mem_filter h'
  · cases h'

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
  | .push _ _ side _ subs dead _ _ _ => side :: subs.zipIdx.filterMap fun e =>
      if (dead.getD []).contains e.2 then none else e.1.2.map Prod.fst
  | .check _ _ _ (.opened subs) =>
    if subs.any fun j => !(st.answers j).isEmpty then [] else subs
  | .check _ _ _ _ => []

/-- The strategy can do nothing more, and cannot complete its goal: a check
that is not offered, or one of whose goals has an answer. -/
def Strat.dead (st : StateOf S N A) : Strat N A → Bool
  | .check _ _ _ .off => true
  | .check _ _ _ (.opened subs) => subs.any fun j => !(st.answers j).isEmpty
  | _ => false

/-- Has the strategy work it could do now? -/
def Strat.pending (st : StateOf S N A) : Strat N A → Bool
  | .span ran => !ran
  | .copy _ subs => subs.any fun p => decide (p.2 < (st.answers p.1).length)
  | .join _ a b c => c.pending (st.answers a).length (st.answers b).length
  | .push _ _ side _ subs dead _ c _ =>
    decide (subs.length < (st.answers side).length) || !c.todo.isEmpty ||
      subs.zipIdx.any fun e => !(dead.getD []).contains e.2 &&
        match e.1.2 with
        | some t => decide (t.2 < (st.answers t.1).length)
        | none => false
  | .check _ _ _ .reading => true
  | .check _ _ _ _ => false

/-- The strategy has nothing left to do and every table it reads passes
`ok`. With `ok` the test for a complete table, the answers of the goal can
no longer grow by this strategy. -/
def Strat.quiet (st : StateOf S N A) (ok : Nat → Bool) (s : Strat N A) : Bool :=
  !s.pending st && (match s with
    | .span ran => ran
    | .copy _ subs => subs.all fun p => ok p.1
    | .join _ a b _ => ok a && ok b
    | .push _ _ side _ subs dead _ _ _ => st.isDone side && dead.isSome && subs.zipIdx.all fun e =>
        (dead.getD []).contains e.2 ||
          match e.1.2 with
          | some t => ok t.1
          | none => false
    | .check _ _ _ (.opened subs) => subs.all fun j => ok j && (st.answers j).isEmpty
    | .check _ _ _ _ => false)

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

/-- Is a goal its own converse? The converse of `lb ; n ; rb` is the converse
of `n` between the exchanged boundaries. -/
def selfConverse (g : GoalOf S N) : M Bool := do
  let c ← K.convNode g.node
  let b ← K.eqNode c g.node
  if b then sameBound (K := K) g.lb g.rb else pure false

/-- The table of a goal: its position, the goal being opened if it has no
table yet. -/
def openGoal (st : StateOf S N A) (g : GoalOf S N) : M (StateOf S N A × Nat) := do
  let i ← indexFrom (K := K) (·.goal) g 0 st.tables
  match i with
  | some i => pure (st, i)
  | none => do
    let self ← selfConverse (K := K) g
    pure ({ st with tables := st.tables ++ [⟨g, self, [], false, none, st.round, 0, 0, none, 0, 0, 0, []⟩] },
      st.tables.length)

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
  pure (st, ⟨0, [.join k a b Cursor.start, .push k true a R.node [] none [] Cursor.start Cursor.start,
    .push k false b L.node [] none [] Cursor.start Cursor.start], []⟩)

/-! ## Reading an edge from the program -/

/-- A run of spans at one end of a node, composed (nothing when a call that
is being read was met first), and whether the run is a whole product of the
node. -/
abbrev Run (S : Type) := Option S × Bool

/-- Add a run to a list that may have it. -/
def addRun (acc : List (Run S)) (r : Run S) : M (List (Run S)) := do
  let b ← anyL (fun (q : Run S) =>
    if q.2 = r.2 then sameBound (K := K) q.1 r.1 else pure false) acc
  pure (if b then acc else acc ++ [r])

/-- Does a node contain a call, without unfolding one? A node with none has
finitely many answers. Nothing if the node is deeper than the first
argument. -/
def hasCall : Nat → N → M (Option Bool)
  | 0, _ => pure none
  | d + 1, n => do
    let v ← K.view n
    match v with
    | .span _ => pure (some false)
    | .call _ _ => pure (some true)
    | .chain xs | .meet xs | .union xs =>
      foldL (fun (acc : Option Bool) x =>
        match acc with
        | some false => hasCall d x
        | r => pure r) (some false) xs

/-- The runs `rs` at the edge of a chain, continued through the next member
inwards, whose runs are `ys`: a run that is not a whole product stays, and a
whole one is composed with each run of the member. -/
def extendRuns (last : Bool) (rs ys : List (Run S)) : M (List (Run S)) :=
  foldL (fun (acc : List (Run S)) (r : Run S) =>
    match r with
    | (some x, true) =>
      foldL (fun (acc : List (Run S)) (q : Run S) =>
        match q.1 with
        | none => addRun (K := K) acc (some x, false)
        | some y => do
          let z ← if last then K.compose y x else K.compose x y
          match z with
          | none => pure acc
          | some z => addRun (K := K) acc (some z, q.2)) acc ys
    | _ => pure acc) (rs.filter fun r => !r.2) rs

/-- The runs of spans the answers of a node end with (`last`) or begin with:
every answer of the node is a product of one of them, with something before
it (after it) unless the run is whole. The edge is followed inwards, through
unions and through each call once: `seen` is the calls being read. A meet is
not read. Nothing if the program is deeper than the first argument. -/
def runs (last : Bool) : Nat → List N → N → M (Option (List (Run S)))
  | 0, _, _ => pure none
  | d + 1, seen, n => do
    let v ← K.view n
    match v with
    | .span _ => do
      let a ← K.leaf none n none
      pure (some (match a with
        | some a => [(some (K.span a), true)]
        | none => []))
    | .meet _ => pure (some [(none, false)])
    | .union xs =>
      foldL (fun (acc : Option (List (Run S))) x =>
        match acc with
        | none => pure none
        | some rs => do
          let r ← runs last d seen x
          match r with
          | none => pure none
          | some r => do
            let rs' ← foldL (addRun (K := K)) rs r
            pure (some rs')) (some []) xs
    | .call _ _ => do
      let b ← anyL (fun m => K.eqNode m n) seen
      if b then pure (some [(none, false)])
      else do
        let bd ← K.body n
        match bd with
        | none => pure (some [])
        | some bd => runs last d (n :: seen) bd
    | .chain xs =>
      match (if last then xs.reverse else xs) with
      | [] => pure (some [(none, false)])
      | e :: rest => do
        let r ← runs last d seen e
        foldL (fun (acc : Option (List (Run S))) x =>
          match acc with
          | none => pure none
          | some rs =>
            if rs.any (·.2) then do
              let r ← runs last d seen x
              match r with
              | none => pure none
              | some ys => do
                let rs' ← extendRuns (K := K) last rs ys
                pure (some rs')
            else pure acc) r rest

/-- The interfaces the answers of a node can show at one end, read to the
depth given: nothing if the depth was not enough; otherwise the interfaces,
or nothing where a check on them is not offered, because the node contains no
call or because one of the interfaces restricts nothing. -/
def readEdge (last : Bool) (depth : Nat) (n : N) : M (Option (Option (List S))) := do
  let c ← hasCall (K := K) depth n
  match c with
  | none => pure none
  | some false => pure (some none)
  | some true => do
    let r ← runs (K := K) last depth [] n
    match r with
    | none => pure none
    | some rs => do
      let ps ← foldL (fun (acc : Option (List S)) (r : Run S) =>
        match acc, r.1 with
        | some ps, some x => do
          let p ← if last then K.rightBound x else K.leftBound x
          match p with
          | none => pure none
          | some p => do
            let b ← anyL (fun q => K.eq q p) ps
            pure (some (if b then ps else ps ++ [p]))
        | _, _ => pure none) (some []) rs
      pure (some ps)

/-- What was read at an end of a node, if it was. -/
def lookupEdge (n : N) (last : Bool) :
    List (N × Bool × Option (List S)) → M (Option (Option (List S)))
  | [] => pure none
  | e :: es =>
    if e.2.1 = last then do
      let b ← K.eqNode e.1 n
      if b then pure (some e.2.2) else lookupEdge n last es
    else lookupEdge n last es

/-- The edge of a node at one end: what was read of it, or a reading to the
depth of the state. What is read is kept. If the depth was not enough,
nothing is returned and the depth of the state doubles. -/
def edgeOf (st : StateOf S N A) (last : Bool) (n : N) :
    M (StateOf S N A × Option (Option (List S))) := do
  let c ← lookupEdge (K := K) n last st.edges
  match c with
  | some e => pure (st, some e)
  | none => do
    let r ← readEdge (K := K) last st.depth n
    pure (match r with
      | some e => ({ st with edges := st.edges ++ [(n, last, e)] }, some e)
      | none => ({ st with depth := 2 * st.depth }, none))

/-- The check of one side of a split, unless it is not offered. -/
def checkOf (st : StateOf S N A) (left : Bool) (side other : N) :
    M (StateOf S N A × List (Strat N A)) := do
  let (st, e) ← edgeOf (K := K) st left side
  pure (st, match e with
    | some none => []
    | _ => [.check left side other .reading])

/-- The groups of the splits of a chain goal of `k` members, and its
interface checks. -/
def chainGroups (g : GoalOf S N) (k : Nat) (st : StateOf S N A) :
    M (StateOf S N A × List (Group N A) × List (Strat N A)) :=
  foldL (fun (acc : StateOf S N A × List (Group N A) × List (Strat N A)) i => do
    let l ← K.interval g.node 0 i
    let r ← K.interval g.node i k
    match l, r with
    | some l, some r => do
      let (st, gr) ← splitGroup (K := K) .seq ⟨g.lb, l, none⟩ ⟨none, r, g.rb⟩ acc.1
      let (st, cl) ← checkOf (K := K) st true l r
      let (st, cr) ← checkOf (K := K) st false r l
      pure (st, acc.2.1 ++ [gr], acc.2.2 ++ cl ++ cr)
    | _, _ => pure acc) (st, [], []) ((List.range k).drop 1)

/-- The groups of a goal, by the kind of its node. The goals its strategies
read are opened. -/
def expand (g : GoalOf S N) (st : StateOf S N A) : M (StateOf S N A × List (Group N A)) := do
  let v ← K.view g.node
  match v with
  | .span _ => pure (st, [⟨0, [.span false], []⟩])
  | .call _ _ => do
    let b ← K.body g.node
    match b with
    | none => pure (st, [⟨0, [.copy true []], []⟩])
    | some b => do
      let (st, j) ← openGoal (K := K) st ⟨g.lb, b, g.rb⟩
      pure (st, [⟨0, [.copy true [(j, 0)]], []⟩])
  | .union xs => do
    let (st, subs) ← foldL (fun (acc : StateOf S N A × List (Nat × Nat)) x => do
      let (st, j) ← openGoal (K := K) acc.1 ⟨g.lb, x, g.rb⟩
      pure (st, acc.2 ++ [(j, 0)])) (st, []) xs
    pure (st, [⟨0, [.copy false subs], []⟩])
  | .chain xs => do
    let r ← chainGroups (K := K) g xs.length st
    pure (r.1, if r.2.2.isEmpty then r.2.1 else r.2.1 ++ [⟨0, r.2.2, []⟩])
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

/-- See the answers that the side of a push has gained, each with its path:
each is one more answer seen, and the unit that opens its goal is filed. -/
def seeSide : List (A × Path) → List (A × Option (Nat × Nat)) → List (Nat × Option Nat) →
    Cursor → List (A × Option (Nat × Nat)) × List (Nat × Option Nat) × Cursor
  | [], subs, reads, c => (subs, reads, c)
  | x :: rest, subs, reads, c =>
    seeSide rest (subs ++ [(x.1, none)]) (reads ++ [(subs.length, none)])
      ((c.opened x.2).read subs.length [])

/-- File the answers that the table opened for the answer of the side at `s`
has gained since `n` of them were filed: each is one more unit of the
cursor. -/
def fileReads (s : Nat) : Nat → List (Nat × Option Nat) → Cursor → List Path →
    List (Nat × Option Nat) × Cursor
  | _, reads, c, [] => (reads, c)
  | n, reads, c, pth :: rest =>
    fileReads s (n + 1) (reads ++ [(s, some n)]) (c.read s pth) rest

/-- File the answers that the tables opened by a push have gained: the
answers seen with every answer of their tables filed, the units, and the
cursor. `s` is the position of the first answer of the list. Nothing is
filed for an answer superseded. -/
def pushFile (st : StateOf S N A) (dead : List Nat) (s : Nat) (reads : List (Nat × Option Nat))
    (c : Cursor) : List (A × Option (Nat × Nat)) →
      List (A × Option (Nat × Nat)) × List (Nat × Option Nat) × Cursor
  | [] => ([], reads, c)
  | (x, none) :: rest =>
    let out := pushFile st dead (s + 1) reads c rest
    ((x, none) :: out.1, out.2)
  | (x, some t) :: rest =>
    if dead.contains s then
      let out := pushFile st dead (s + 1) reads c rest
      ((x, some t) :: out.1, out.2)
    else
      let pths := st.pathsAt t.1
      let r := fileReads s t.2 reads c (pths.drop t.2)
      let out := pushFile st dead (s + 1) r.1 r.2 rest
      ((x, some (t.1, pths.length)) :: out.1, out.2)

/-- The answers superseded once the answers `new` are seen after the answers
`seen`: each new answer is compared with every answer seen before it that is
not superseded, and supersedes those it covers. -/
def supersede : List A → List A → List Nat → M (List Nat)
  | [], _, dead => pure dead
  | y :: rest, seen, dead => do
    let ks ← filterL (fun e : A × Nat =>
      if dead.contains e.2 then pure false else coversA (K := K) y e.1) seen.zipIdx
    supersede rest (seen ++ [y]) (dead ++ ks.map (·.2))

/-- The answers of the table `side` that are superseded, once that table is
complete: found once, by `supersede` over all its answers, and kept. -/
def superseded (st : StateOf S N A) (side : Nat) : Option (List Nat) → M (Option (List Nat))
  | some d => pure (some d)
  | none =>
    if st.isDone side then do
      let d ← supersede (K := K) (st.answers side) [] []
      pure (some d)
    else pure none

/-- The table opened for one answer, with none of its answers filed. -/
def openedAt (new : List (A × Nat × Nat)) : Option (Nat × Nat) :=
  new.head?.map fun e => (e.2.1, 0)

/-- Open the other side of a split under each interface of a check. -/
def checkOpen (g : GoalOf S N) (left : Bool) (other : N) (st : StateOf S N A) (ps : List S) :
    M (StateOf S N A × List Nat) :=
  foldL (fun (acc : StateOf S N A × List Nat) p => do
    let (st, j) ← openGoal (K := K) acc.1
      (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩)
    pure (st, acc.2 ++ [j])) (st, []) ps

/-- One unit of the work of a strategy of the table at `i`. Returns the
state, the strategy with its cursors moved, and whether anything was
done. -/
def work (i : Nat) (g : GoalOf S N) (st : StateOf S N A) :
    Strat N A → M (StateOf S N A × Strat N A × Bool)
  | .span true => pure (st, .span true, false)
  | .span false => do
    let a ← K.leaf g.lb g.node g.rb
    let st ← addOption (K := K) i st a
    pure (st, .span true, true)
  | .copy isCall subs =>
    match leastBy (fun p => p.1.2) (fun p => decide (p.1.2 < (st.answers p.1.1).length))
        subs.zipIdx with
    | none => pure (st, .copy isCall subs, false)
    | some p => do
      let pth := (st.pathsAt p.1.1).getD p.1.2 []
      let st' ← copyFrom (K := K) i g isCall p.2 st (((st.answers p.1.1).drop p.1.2).take 1)
      pure (stamp i (st.answers i).length (if isCall then pth else (p.2, subs.length) :: pth) st',
        .copy isCall (subs.modify p.2 fun q => (q.1, q.2 + 1)), true)
  | .join k a b c =>
    let xs := st.answers a
    let ys := st.answers b
    let c := c.see (st.pathsAt a) (st.pathsAt b)
    match c.next with
    | none => pure (st, .join k a b c, false)
    | some p => do
      let (st', t) ← K.metered (joinPairs (K := K) i k xs ys st [p])
      pure (stamp i (st.answers i).length (c.pa.getD p.1 [] ++ c.pb.getD p.2 []) st',
        .join k a b (c.mark p (t + 1)), true)
  | .push k left side other subs dead reads c fc => do
    let new := ((st.answers side).zip (st.pathsAt side)).drop subs.length
    let dead ← superseded (K := K) st side dead
    let f0 := seeSide new subs reads c
    let f := pushFile st (dead.getD []) 0 f0.2.1 (f0.2.2.kill (dead.getD [])) f0.1
    match f.2.2.next with
    | none => pure (st, .push k left side other f.1 dead f.2.1 f.2.2 fc, false)
    | some p =>
      match f.1[p.1]?, f.2.1[p.2]? with
      | some (x, none), some (_, none) => do
        let (out, t) ← K.metered (pushOpen (K := K) g other k left st [x])
        pure (out.1, .push k left side other (f.1.set p.1 (x, openedAt out.2)) dead f.2.1
          (f.2.2.mark p (t + 1)) fc, true)
      | some (x, some tb), some (_, some r) => do
        let (st', t) ← K.metered (pushTake (K := K) i k left x st
          (((st.answers tb.1).drop r).take 1))
        let u := f.2.2.pa.getD p.1 []
        let v := f.2.2.pb.getD p.2 []
        pure (stamp i (st.answers i).length (if left then u ++ v else v ++ u) st',
          .push k left side other f.1 dead f.2.1 (f.2.2.mark p (t + 1)) fc, true)
      | _, _ => pure (st, .push k left side other f.1 dead f.2.1 (f.2.2.mark p 1) fc, true)
  | .check left side other .reading => do
    let (st, e) ← edgeOf (K := K) st left side
    match e with
    | none => pure (st, .check left side other .reading, true)
    | some none => pure (st, .check left side other .off, true)
    | some (some ps) => do
      let (st, subs) ← checkOpen (K := K) g left other st ps
      pure (st, .check left side other (.opened subs), true)
  | .check left side other c => pure (st, .check left side other c, false)

/-! ## A round -/

/-- The groups of the table at `i`. -/
def groupsAt (st : StateOf S N A) (i : Nat) : List (Group N A) :=
  match st.tables[i]? with
  | some t => t.groups.getD []
  | none => []

/-- Change the group `k` of the table at `i`. -/
def setGroup (st : StateOf S N A) (i k : Nat) (f : Group N A → Group N A) : StateOf S N A :=
  st.modify i fun t => { t with groups := t.groups.map fun gs => gs.modify k f }

/-- The strategies of the table at `i`. -/
def stratsAt (st : StateOf S N A) (i : Nat) : List (Strat N A) :=
  (groupsAt st i).flatMap (·.strats)

/-- The tables given, with every table that is read from one of them through
any number of strategies. The first argument counts the tables still to
find, and is never used up. -/
def upstream (st : StateOf S N A) : Nat → List Nat → List Nat
  | 0, seen => seen
  | f + 1, seen =>
    let next := (seen ++ seen.flatMap fun j => (stratsAt st j).flatMap (Strat.feeds st)).eraseDups
    if next.length = seen.length then seen else upstream st f next

/-- How many strategies work for the table at `h`: its own, and those of
every table read from it through any number of strategies. -/
def above (st : StateOf S N A) (h : Nat) : Nat :=
  ((upstream st st.tables.length [h]).map fun j => (stratsAt st j).length).sum

/-- The weight of a strategy: one for itself, and for each table it reads
the number of strategies that work for that table. -/
def weight (st : StateOf S N A) (s : Strat N A) : Nat :=
  1 + ((s.feeds st).eraseDups.map (above st)).sum

/-- What a turn is worth, in ticks, for each unit of weight. -/
def turnTicks : Nat := 4

/-- Put what the strategy at `j` owes. -/
def setOwed (l : List Nat) (j v : Nat) : List Nat :=
  (l ++ List.replicate (j + 1 - l.length) 0).set j v

/-- A strategy of the table at `i` works while it has ticks left: unit after
unit, until `left` ticks are spent or it can do nothing. `c` is what it has
spent so far. A unit that did something is charged one tick more than the
kernel charged for it, so a strategy that did anything has spent something,
at every kernel: a kernel may charge nothing. The last unit is done whole,
whatever it costs. Returns the state, the strategy with its cursors moved,
and what was spent. The first argument counts the ticks down, and is never
used up. -/
def turn (i : Nat) (g : GoalOf S N) :
    Nat → Nat → StateOf S N A → Strat N A → Nat → M (StateOf S N A × Strat N A × Nat)
  | 0, _, st, s, c => pure (st, s, c)
  | f + 1, left, st, s, c =>
    if left = 0 then pure (st, s, c)
    else do
      let (r, t) ← K.metered (work (K := K) i g st s)
      if r.2.2 then do
        K.tick 1
        turn i g f (left - (t + 1)) r.1 r.2.1 (c + t + 1)
      else pure (r.1, r.2.1, c)

/-- Each strategy of the group `k` of the table at `i` has its turn, in
order. A turn is worth `turnTicks` ticks for each unit of the weight of the
strategy. A strategy that owes that much or more does nothing and owes that
much less. Otherwise it works until it has spent what the turn is worth less
what it owed, and owes what it spent beyond that. Returns what the turns
cost, and whether anything was done. -/
def workStrats (i : Nat) (g : GoalOf S N) (k : Nat) (st : StateOf S N A) :
    M (StateOf S N A × Nat × Bool) :=
  let n := ((groupsAt st i)[k]?.map (·.strats.length)).getD 0
  foldL (fun (acc : StateOf S N A × Nat × Bool) j =>
    match ((groupsAt acc.1 i)[k]?).bind fun gr => gr.strats[j]?.map fun s => (s, gr.owed.getD j 0) with
    | none => pure acc
    | some (s, o) => do
      let a := turnTicks * weight acc.1 s
      let (st', s', c) ← turn (K := K) i g (a - o) (a - o) acc.1 s 0
      let st' := setGroup st' i k fun gr =>
        { gr with strats := gr.strats.set j s', owed := setOwed gr.owed j (o + c - a) }
      pure (st', acc.2.1 + c, acc.2.2 || decide (0 < c)))
    (st, 0, false) (List.range n)

/-- The table at `h` has its round (`adv`), and what the round cost is added
to what the table has been fed. Returns how much its level rose, and what the
round cost. -/
def feed (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (h : Nat) (st : StateOf S N A) :
    M (StateOf S N A × Nat × Nat) := do
  let (r, c) ← K.metered (adv h st)
  pure (r.1.modify h fun t => { t with fed := t.fed + c }, r.2, c)

/-- Each of the tables given has its round. Returns `d` and how much their
levels rose. -/
def feedAll (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (st : StateOf S N A) (d : Nat)
    (feeds : List Nat) : M (StateOf S N A × Nat) :=
  foldL (fun (acc : StateOf S N A × Nat) h => do
    let (st', dh, _) ← feed (K := K) adv h acc.1
    pure (st', acc.2 + dh)) (st, d) feeds

/-- The tables given are offered a round in order, until the round of one
has cost something: a table that is complete, or has had its round in this
request, costs nothing and passes the offer on. Returns `d` and how much
their levels rose. -/
def feedFirst (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (st : StateOf S N A)
    (d : Nat) (feeds : List Nat) : M (StateOf S N A × Nat) := do
  let r ← foldL (fun (acc : StateOf S N A × Nat × Bool) h =>
    if acc.2.2 then pure acc
    else do
      let (st', dh, c) ← feed (K := K) adv h acc.1
      pure (st', acc.2.1 + dh, decide (0 < c))) (st, d, false) feeds
  pure (r.1, r.2.1)

/-- The tables given, the one that has been fed least first. -/
def byFed (st : StateOf S N A) (feeds : List Nat) : List Nat :=
  feeds.mergeSort fun a b => decide (st.fedAt a ≤ st.fedAt b)

/-- The tables a strategy reads that have a round whenever its group is
fed: all of them, but for a push its side only. The tables a push opened
share their rounds (`feedPush`). -/
def Strat.feeds0 (st : StateOf S N A) : Strat N A → List Nat
  | .push _ _ side _ _ _ _ _ _ => [side]
  | s => s.feeds st

/-- A unit of the feed cursor is filed for each answer of the side whose
table is opened, not complete and not superseded, and has no unit filed. -/
def fileToks (st : StateOf S N A) (dead : List Nat) :
    List ((A × Option (Nat × Nat)) × Nat) → Cursor → Cursor
  | [], fc => fc
  | (e, n) :: rest, fc =>
    match e.2 with
    | some t =>
      if dead.contains n || st.isDone t.1 || fc.todo.any (fun x => x.1 == n) then
        fileToks st dead rest fc
      else fileToks st dead rest (fc.read n [])
    | none => fileToks st dead rest fc

/-- The feed cursor of a push brought up to date: it has the path of every
answer of the side seen, no unit of an answer superseded, and a unit for
every table opened that could use a round. -/
def syncFeed (st : StateOf S N A) (side : Nat) (dead : List Nat)
    (subs : List (A × Option (Nat × Nat))) (fc : Cursor) : Cursor :=
  let fc1 := (((st.pathsAt side).take subs.length).drop fc.pa.length).foldl
    (fun c pth => c.opened pth) fc
  fileToks st dead subs.zipIdx (fc1.kill dead)

/-- The tables a push opened are offered a round in the order of its feed
cursor, until the round of one has cost something: the classes of the
answers pushed share the ticks as the classes of a join's pairs share its
ticks, so a table waits for the tables of other choices by the number of
members at each choice on the way to its answer, and not by how many
answers the other members have. A unit taken is marked with what the round
cost. Returns the state, `d` and how much the levels of the tables rose, and
the cursor. The first argument counts the units, and is never used up. -/
def feedToks (adv : Nat → StateOf S N A → M (StateOf S N A × Nat))
    (subs : List (A × Option (Nat × Nat))) :
    Nat → StateOf S N A → Nat → Cursor → M (StateOf S N A × Nat × Cursor)
  | 0, st, d, fc => pure (st, d, fc)
  | f + 1, st, d, fc =>
    match fc.next with
    | none => pure (st, d, fc)
    | some x =>
      match (subs[x.1]?).bind (·.2) with
      | none => feedToks adv subs f st d (fc.mark x 0)
      | some t => do
        let r ← feed (K := K) adv t.1 st
        if 0 < r.2.2 then pure (r.1, d + r.2.1, fc.mark x r.2.2)
        else feedToks adv subs f r.1 (d + r.2.1) (fc.mark x r.2.2)

/-- The tables a push opened have their share of rounds (`feedToks`), after
its feed cursor is brought up to date. Any other strategy is left as it is.
Returns the strategy with its feed cursor moved. -/
def feedPush (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (st : StateOf S N A) (d : Nat) :
    Strat N A → M (StateOf S N A × Nat × Strat N A)
  | .push k left side other subs dead reads c fc => do
    let fc0 := syncFeed st side (dead.getD []) subs fc
    let r ← feedToks (K := K) adv subs fc0.todo.length st d fc0
    pure (r.1, r.2.1, .push k left side other subs dead reads c r.2.2)
  | s => pure (st, d, s)

/-- Each push of the strategies given feeds the tables it opened
(`feedPush`), in order. -/
def feedPushes (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) :
    StateOf S N A → Nat → List (Strat N A) → M (StateOf S N A × Nat × List (Strat N A))
  | st, d, [] => pure (st, d, [])
  | st, d, s :: rest => do
    let a ← feedPush (K := K) adv st d s
    let b ← feedPushes adv a.1 a.2.1 rest
    pure (b.1, b.2.1, a.2.2 :: b.2.2)

/-- The tables the group `k` of the table at `i` reads have their rounds
(`adv`). The members of a union share the ticks: one member has its round,
the one that has been fed least of those that still need one. The tables a
push opened share the ticks by where the answers pushed came from
(`feedPush`). Every other table a group reads has its round. Returns `d` and
how much their levels rose, and the strategies of the group with the feed
cursors of its pushes moved. -/
def feedGroup (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (i k : Nat)
    (st : StateOf S N A) (d : Nat) : M (StateOf S N A × Nat × List (Strat N A)) :=
  let strats : List (Strat N A) := ((groupsAt st i)[k]?.map (·.strats)).getD []
  match strats with
  | [Strat.copy false subs] => do
    let r ← feedFirst (K := K) adv st d (byFed st (subs.map Prod.fst).eraseDups)
    pure (r.1, r.2, strats)
  | _ => do
    let r ← feedAll (K := K) adv st d (strats.flatMap (Strat.feeds0 st)).eraseDups
    feedPushes (K := K) adv r.1 r.2 strats

/-- The group `k` of the table at `i` works: each of its strategies does its
own work, and then the tables they read have their rounds (`feedGroup`). The
ticks of the strategies' own work are added to the own work of the table.
Returns how much the level of the group rose, and whether anything was
done. -/
def workGroup (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (i : Nat)
    (g : GoalOf S N) (k : Nat) (st : StateOf S N A) : M (StateOf S N A × Nat × Bool) := do
  let (st, d0, did) ← workStrats (K := K) i g k st
  let (st, d, strats) ← feedGroup (K := K) adv i k st d0
  pure ((setGroup st i k fun gr => { gr with level := gr.level + d, strats := strats }).modify i
    fun t => { t with own := t.own + d0 }, d, did || decide (0 < d))

/-- The groups of the table at `i` that stand at the level `lv` work.
Returns whether any of them did anything. -/
def workLevel (adv : Nat → StateOf S N A → M (StateOf S N A × Nat)) (i : Nat)
    (g : GoalOf S N) (lv : Nat) (st : StateOf S N A) : M (StateOf S N A × Bool) :=
  foldL (fun (acc : StateOf S N A × Bool) (p : Group N A × Nat) =>
    if p.1.level = lv then do
      let (st', _, did) ← workGroup (K := K) adv i g p.2 acc.1
      pure (st', acc.2 || did)
    else pure acc) (st, false) (groupsAt st i).zipIdx

/-- The race a goal starts with: one for a chain, at depth 0. The verdict of
the unfolding of any other node is made of the verdicts of its body or
members, and the strategies of its goal make it. -/
def raceOf (g : GoalOf S N) : M (Option Race) := do
  let v ← K.view g.node
  pure (match v with
    | .chain _ => some ⟨0, 0, 0⟩
    | _ => none)

/-- Before the round of the table at `i`, read as `t`: its groups and its
race are made if it has no groups, and the round is stamped. -/
def prepare (i : Nat) (t : Table S N A) (st : StateOf S N A) : M (StateOf S N A) := do
  let st ← match t.groups with
    | some _ => pure st
    | none => do
      let (st', gs) ← expand (K := K) t.goal st
      let r ← raceOf (K := K) t.goal
      pure (st'.modify i fun t => { t with groups := some gs, race := r })
  pure (st.modify i fun t => { t with stamp := st.round, delta := 0 })

/-- The race of the table at `i` asks once at its next depth. The ask may
cost what is left of the race's budget, which is the own work of the table
plus its rounds, less what the race has spent, and no more: an ask that
needs more is given up and charged, and the next is made when twice as much
is left; with nothing left no ask is made. A final verdict puts the answers in the table; a verdict that is
not final moves the race to the next depth. Returns whether the verdict was
final. The race takes no group's turn and is no part of any level. -/
def askRace (U : GOracle S N A M) (i : Nat) (g : GoalOf S N) (st : StateOf S N A) :
    M (StateOf S N A × Bool) :=
  match st.tables[i]? with
  | none => pure (st, false)
  | some t =>
    match t.race with
    | none => pure (st, false)
    | some r =>
      let left := t.own + t.rounds - r.spent
      if left < max 1 (2 * r.gaveUp) then pure (st, false)
      else do
        let (u, c) ← K.metered (K.within left (U r.depth g))
        match u with
        | none =>
          pure (st.modify i fun t => { t with race := some ⟨r.depth, r.spent + c, left⟩ }, false)
        | some u =>
          if u.1 then do
            let st ← foldL (addAnswer (K := K) i) st u.2
            pure (st.modify i fun t => { t with race := some ⟨r.depth, r.spent + c, 0⟩ }, true)
          else
            pure (st.modify i fun t => { t with race := some ⟨r.depth + 1, r.spent + c, 0⟩ }, false)

/-- The round of the table at `i`. The first argument is the number of
tables that can still have a round nested in this one. After its groups have
worked, the race of the table asks once if it is within its budget, and the
table is complete if a strategy has nothing left to do and reads only
complete tables, or if its race found the unfolding final. Returns how much
the level of the goal rose. -/
def advance (U : GOracle S N A M) : Nat → Nat → StateOf S N A → M (StateOf S N A × Nat)
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
        let st ← prepare (K := K) i t st
        let gs := groupsAt st i
        let low := levelOf gs
        let (st, _) ← foldL (fun (acc : StateOf S N A × Bool) lv =>
          if acc.2 then pure acc
          else workLevel (K := K) (advance U fuel) i t.goal lv acc.1) (st, false)
          (levelsOf gs)
        let st := st.modify i fun t =>
          { t with groups := t.groups.map fun gs =>
              gs.filter fun gr => !gr.strats.all (Strat.dead st) }
        let (st, raced) ← askRace (K := K) U i t.goal st
        let gs' := groupsAt st i
        let fin := (gs'.any fun gr => gr.strats.any fun s => s.quiet st st.isDone) || raced
        let d := levelOf gs' - low
        pure (st.modify i fun t =>
          { t with done := t.done || fin, delta := d, rounds := t.rounds + 1 }, d)

/-- One request: a round of the root, and then the tables that complete
together are marked. Returns the answers the root table gained. A request
costs at least one tick. -/
def request (U : GOracle S N A M) (st : StateOf S N A) : M (StateOf S N A × List A) := do
  K.tick 1
  let st : StateOf S N A := { st with round := st.round + 1 }
  let (st, _) ← advance (K := K) U st.tables.length 0 st
  let C := completing st
  let st : StateOf S N A :=
    { st with tables := st.tables.mapIdx fun i t => if C.contains i then { t with done := true } else t }
  let new := (st.answers 0).drop st.shown
  pure ({ st with shown := (st.answers 0).length }, new)

/-- A step: a request, or the final report when the root table is
complete. -/
def step (U : GOracle S N A M) (st : StateOf S N A) : M (StepOf A (StateOf S N A)) :=
  match st.tables.head? with
  | none => pure (.done [])
  | some t =>
    if t.done then do
      let fin ← maxima (K := K) t.answers
      pure (.done fin)
    else do
      let r ← request (K := K) U st
      pure (.emit r.2 r.1)

/-- The first state: the table of the root goal alone. -/
def init (root : N) : M (StateOf S N A) := do
  let self ← selfConverse (K := K) ⟨none, root, none⟩
  pure ⟨[⟨⟨none, root, none⟩, self, [], false, none, 0, 0, 0, none, 0, 0, 0, []⟩], 0, 0, [], 1⟩

end

/-- The symmetric engine with a given unfolding race. Its first state is the
table of the root goal alone. -/
def engine (u : Unfolder) : Engine where
  State := StateOf
  init root := init root
  step st := step u st

end Symmetric

end RwLog
