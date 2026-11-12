/-
# Rung R001: the proper baseline

R001 evaluates *goals*. A goal `⟨lb, e, rb⟩` is the relation `lb ; e ; rb`,
where `e` is a sub-expression of the query or of a definition body and the
optional boundaries `lb`, `rb` are interface spans `p {c} -> p` (identities
restricted to the instances of `p` that satisfy `c`). Every goal gets a
table, and goals are identified up to equivalent boundaries, so recursive
calls with the same boundaries share one table (variant tabling).

## Rounds

The machine works in rounds, and one step is one round. In a round every
incomplete table recomputes its candidate answers from the answers all
tables held at the start of the round, then all tables are updated at once.
Nothing inside a round depends on the order of tables or of answers, which
is what makes the trace independent of the order of `|` branches and makes
the mirrored program's trace the mirror of this one, step for step. Each
step emits the answers the root table gained in that round.

## What a goal computes

* `zero`: nothing. A span: `lb ; s ; rb`, by matching.
* `a | b`, a call, a converse: the answers of the sub-goal(s), with
  boundaries pushed in unchanged (swapped through a converse). A goal whose
  expression is a converse is stored as the converse of the swapped goal.
* `a ; b` and `a & b` run three strategies side by side:
  - *join*: combine every answer of the left sub-goal with every answer of
    the right one (`;` composes, `&` meets). The left sub-goal of
    `lb ; (a ; b) ; rb` is `lb ; a`, the right one `b ; rb`; for `&` both
    keep both boundaries.
  - *push left*: once the left sub-goal is complete, take each of its
    maximal answers `x`, and run the right side with `x`'s interface pushed
    in as a boundary (`x ; b ; rb` becomes `x ; (x.rightIface ; b ; rb)`).
  - *push right*: the mirror image.
  This is boundary pushing (`@t ; R` follows `R` under the boundary `t`) and
  finite-side propagation for both `;` and `&`, with no preferred direction.

Candidates are simplified before they enter a table (`Theory.simplify`):
every equation the theory forces on a candidate's store instantiates the
whole candidate, and a candidate whose store the theory refutes
(`Theory.refutes?`) is dropped. A candidate is also dropped when it is
covered by an answer already in the table or strictly covered by another
candidate of the same round; among equivalent candidates one is kept. So
tables, and the answers the root emits, hold no refuted, duplicate or
subsumed answers.

## Completion

A table is complete when its answers can no longer grow. At the end of a
round the machine computes the largest set `S` of incomplete tables such
that each table in `S` gained nothing this round and has a strategy all of
whose dependencies existed at the start of the round, gained nothing, and
are complete or in `S`. Every table in `S` is then marked complete. This is
an exact check on the whole state, not a counter. When every table stops
changing, `S` contains all of them, so the machine never stalls.
-/
import RwLog.Kernel.Refute
import RwLog.Trusted.Engine

namespace RwLog

namespace Span

/-- The constraints of `s` that only mention variables of `p`. -/
def storeOn (s : Span) (p : Pat) : Store := s.c.filter fun a => a.vars.all (· ∈ p.vars)

/-- The right interface `r {c|r} -> r`: `s ; s.rightIface = s`. -/
def rightIface (s : Span) : Span := ⟨s.r, s.r, s.storeOn s.r⟩

/-- The left interface `l {c|l} -> l`: `s.leftIface ; s = s`. -/
def leftIface (s : Span) : Span := ⟨s.l, s.l, s.storeOn s.l⟩

end Span

namespace R001

/-- A boundary, with the trivial interface `$x -> $x` (the identity)
represented as no boundary. -/
def bound (s : Span) : Option Span :=
  match s.l, s.c with
  | .var _, [] => none
  | _, _ => some s

/-- The goal `lb ; e ; rb`. -/
structure Goal where
  lb : Option Span
  e : Rel
  rb : Option Span
  deriving DecidableEq, Repr

/-- Boundaries are equal as table keys when they are equivalent. -/
def boundEq : Option Span → Option Span → Bool
  | none, none => true
  | some a, some b => a.covers? b && b.covers? a
  | _, _ => false

/-- Goals are equal as table keys: the same expression and equivalent
boundaries. -/
def Goal.same (g h : Goal) : Bool := decide (g.e = h.e) && boundEq g.lb h.lb && boundEq g.rb h.rb

/-- The mirror image of a goal: `(lb ; e ; rb)ᵒ = rbᵒ ; eᵒ ; lbᵒ`. -/
def Goal.dual (g : Goal) : Goal := ⟨g.rb.map Span.swap, g.e.dual, g.lb.map Span.swap⟩

/-- Strip converses: `norm g = (flip, g')` with `g` the converse of `g'` when
`flip` holds, and `g'.e` not a converse. -/
def Goal.norm : Goal → Bool × Goal
  | ⟨lb, .conv a, rb⟩ =>
    let r := Goal.norm ⟨rb.map Span.swap, a, lb.map Span.swap⟩
    (!r.1, r.2)
  | g => (false, g)
termination_by g => sizeOf g.e

/-- A table: a goal, the answers found so far, and whether it is complete. -/
structure Table where
  goal : Goal
  answers : List Span
  done : Bool
  deriving Repr

abbrev Tables := List Table

/-- The table of a goal whose expression is not a converse. -/
def findTable (ts : Tables) (g : Goal) : Option Table :=
  List.find? (fun t => t.goal.same g) ts

/-- The position of the table of a goal whose expression is not a
converse. -/
def indexOf (ts : Tables) (g : Goal) : Option Nat :=
  List.findIdx? (fun t => t.goal.same g) ts

def orient (flip : Bool) (xs : List Span) : List Span := if flip then xs.map Span.swap else xs

/-- The answers a goal currently has. -/
def answersOf (ts : Tables) (g : Goal) : List Span :=
  let n := g.norm
  match findTable ts n.2 with
  | some t => orient n.1 t.answers
  | none => []

/-- The goal's table exists and is complete. -/
def doneOf (ts : Tables) (g : Goal) : Bool :=
  match findTable ts g.norm.2 with
  | some t => t.done
  | none => false

/-! ## Kernel steps with pruning -/

/-- Simplify a span by its theory: instantiate it by every equation the
theory forces, and drop it if the theory refutes it. -/
def live (T : Theory) (s : Span) : List Span := (T.simplify s).toList

def composeLive (T : Theory) (x y : Span) : List Span :=
  match x.compose y with
  | some z => live T z
  | none => []

def meetLive (T : Theory) (x y : Span) : List Span :=
  match x.meet y with
  | some z => live T z
  | none => []

/-- `lb ; s ; rb`. -/
def spanAnswer (T : Theory) (lb : Option Span) (s : Span) (rb : Option Span) : List Span :=
  let left : Option Span := match lb with
    | none => some s
    | some l => l.compose s
  let both : Option Span := left.bind fun s' => match rb with
    | none => some s'
    | some r => s'.compose r
  match both with
  | some z => live T z
  | none => []

/-- The answers of a list that no other member strictly covers, one per
class of equivalent answers. -/
def maxima (xs : List Span) : List Span :=
  let top := xs.filter fun x => !xs.any fun y => y.covers? x && !x.covers? y
  top.foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x]) []

/-- The candidates that enter a table holding `old`: not covered by an old
answer, not strictly covered by another candidate, one per equivalence
class. -/
def fresh (old cands : List Span) : List Span :=
  maxima (cands.filter fun c => !old.any fun t => t.covers? c)

/-! ## Goals: sub-goals, candidates and strategies -/

/-- The sub-goals of a sequence `lb ; (a ; b) ; rb`. -/
def seqLeft (g : Goal) (a : Rel) : Goal := ⟨g.lb, a, none⟩
def seqRight (g : Goal) (b : Rel) : Goal := ⟨none, b, g.rb⟩

/-- The goal the push-left strategy runs for a left answer `x`, and the
mirror one for a right answer `y`. -/
def seqPushL (g : Goal) (b : Rel) (x : Span) : Goal := ⟨bound x.rightIface, b, g.rb⟩
def seqPushR (g : Goal) (a : Rel) (y : Span) : Goal := ⟨g.lb, a, bound y.leftIface⟩

/-- The sub-goals of a conjunction `lb ; (a & b) ; rb`. -/
def andLeft (g : Goal) (a : Rel) : Goal := ⟨g.lb, a, g.rb⟩
def andRight (g : Goal) (b : Rel) : Goal := ⟨g.lb, b, g.rb⟩

/-- The goal a conjunction runs for an answer `x` of one side. -/
def andPush (e : Rel) (x : Span) : Goal := ⟨bound x.leftIface, e, bound x.rightIface⟩

/-- The goal a call or converse forwards to. -/
def callGoal (P : Program) (g : Goal) (n : Name) : Goal := ⟨g.lb, P.body n, g.rb⟩
def convGoal (g : Goal) (a : Rel) : Goal := ⟨g.rb.map Span.swap, a, g.lb.map Span.swap⟩

/-- The candidate answers of a goal, computed from the tables at the start of
a round, and the goals it needs. -/
def produce (P : Program) (ts : Tables) (g : Goal) : List Span × List Goal :=
  let T := P.theory
  match g.e with
  | .zero => ([], [])
  | .span s => (spanAnswer T g.lb s g.rb, [])
  | .or a b =>
    let ga : Goal := ⟨g.lb, a, g.rb⟩
    let gb : Goal := ⟨g.lb, b, g.rb⟩
    (answersOf ts ga ++ answersOf ts gb, [ga, gb])
  | .call n =>
    let gb := callGoal P g n
    (answersOf ts gb, [gb])
  | .conv a =>
    let g' := convGoal g a
    ((answersOf ts g').map Span.swap, [g'])
  | .seq a b =>
    let L := seqLeft g a
    let R := seqRight g b
    let xs := answersOf ts L
    let ys := answersOf ts R
    let join := xs.flatMap fun x => ys.flatMap fun y => composeLive T x y
    let pl := if doneOf ts L then (maxima xs).map fun x => (x, seqPushL g b x) else []
    let pr := if doneOf ts R then (maxima ys).map fun y => (y, seqPushR g a y) else []
    (join ++ pl.flatMap (fun p => (answersOf ts p.2).flatMap fun y => composeLive T p.1 y)
          ++ pr.flatMap (fun p => (answersOf ts p.2).flatMap fun x => composeLive T x p.1),
     [L, R] ++ pl.map Prod.snd ++ pr.map Prod.snd)
  | .and a b =>
    let L := andLeft g a
    let R := andRight g b
    let xs := answersOf ts L
    let ys := answersOf ts R
    let join := xs.flatMap fun x => ys.flatMap fun y => meetLive T x y
    let pl := if doneOf ts L then (maxima xs).map fun x => (x, andPush b x) else []
    let pr := if doneOf ts R then (maxima ys).map fun y => (y, andPush a y) else []
    (join ++ pl.flatMap (fun p => (answersOf ts p.2).flatMap fun y => meetLive T p.1 y)
          ++ pr.flatMap (fun p => (answersOf ts p.2).flatMap fun x => meetLive T x p.1),
     [L, R] ++ pl.map Prod.snd ++ pr.map Prod.snd)

/-- The strategies of a goal, each given by the goals it depends on. The
goal may complete through any one of them. -/
def strategies (P : Program) (ts : Tables) (g : Goal) : List (List Goal) :=
  match g.e with
  | .zero => [[]]
  | .span _ => [[]]
  | .or a b => [[⟨g.lb, a, g.rb⟩, ⟨g.lb, b, g.rb⟩]]
  | .call n => [[callGoal P g n]]
  | .conv a => [[convGoal g a]]
  | .seq a b =>
    let L := seqLeft g a
    let R := seqRight g b
    [[L, R]]
      ++ (if doneOf ts L then [L :: (maxima (answersOf ts L)).map (seqPushL g b)] else [])
      ++ (if doneOf ts R then [R :: (maxima (answersOf ts R)).map (seqPushR g a)] else [])
  | .and a b =>
    let L := andLeft g a
    let R := andRight g b
    [[L, R]]
      ++ (if doneOf ts L then [L :: (maxima (answersOf ts L)).map (andPush b)] else [])
      ++ (if doneOf ts R then [R :: (maxima (answersOf ts R)).map (andPush a)] else [])

/-! ## One round -/

/-- Shrink `S` to the largest subset closed under `ok`. Each pass that changes
`S` removes a member, so `S.length` passes reach the fixpoint. -/
def gfpFrom (ok : List Nat → Nat → Bool) : Nat → List Nat → List Nat
  | 0, S => S
  | n + 1, S =>
    let S' := S.filter (ok S)
    if S'.length = S.length then S else gfpFrom ok n S'

/-- The tables that complete at the end of a round. `ts` is the state at the
start of the round and `ts'` the state after this round's answers were
added. -/
def completing (P : Program) (ts ts' : Tables) : List Nat :=
  let n := ts.length
  let gained (j : Nat) : Bool := decide ((ts'.getD j ⟨⟨none, .zero, none⟩, [], false⟩).answers.length
    ≠ (ts.getD j ⟨⟨none, .zero, none⟩, [], false⟩).answers.length)
  let isDone (j : Nat) : Bool := (ts.getD j ⟨⟨none, .zero, none⟩, [], false⟩).done
  let S0 := (List.range n).filter fun i => !isDone i && !gained i
  let ok (S : List Nat) (i : Nat) : Bool :=
    (strategies P ts (ts.getD i ⟨⟨none, .zero, none⟩, [], false⟩).goal).any fun deps =>
      deps.all fun d =>
        match indexOf ts d.norm.2 with
        | none => false
        | some j => !gained j && (isDone j || S.contains j)
  gfpFrom ok S0.length S0

/-- The machine state: the program, the tables (the root first), and whether
the query is the converse of the root goal. -/
structure State where
  P : Program
  tables : Tables
  rootFlip : Bool

/-- One round. Returns the new state and the answers the root gained. -/
def round (st : State) : State × List Span :=
  let ts := st.tables
  let outs := ts.map fun t => if t.done then ([], []) else produce st.P ts t.goal
  let ts1 : Tables := (ts.zip outs).map fun p => { p.1 with answers := p.1.answers ++ fresh p.1.answers p.2.1 }
  let reqs := (outs.flatMap Prod.snd).map fun g => g.norm.2
  let newGoals := reqs.foldl
    (fun acc g => if ts.any (fun t => t.goal.same g) || acc.any (fun h => h.same g) then acc else acc ++ [g]) []
  let S := completing st.P ts ts1
  let ts2 : Tables := ts1.mapIdx fun i t => if S.contains i then { t with done := true } else t
  let ts3 : Tables := ts2 ++ newGoals.map fun g => ⟨g, [], false⟩
  let rootNew := match ts.head?, ts1.head? with
    | some t, some t' => t'.answers.drop t.answers.length
    | _, _ => []
  (⟨st.P, ts3, st.rootFlip⟩, orient st.rootFlip rootNew)

/-- The state for a goal: its table alone. -/
def State.ofGoal (P : Program) (g : Goal) : State :=
  let n := g.norm
  ⟨P, [⟨n.2, [], false⟩], n.1⟩

/-- The root table is complete. -/
def State.finished (st : State) : Bool :=
  match st.tables.head? with
  | some t => t.done
  | none => true

def step (st : State) : Step State :=
  if st.finished then .done else
  let r := round st
  .emit r.2 r.1

def runtime : Runtime where
  State := State
  init P q := State.ofGoal P ⟨none, q, none⟩
  step := step

/-- Rung R001: no preprocessing, an empty artifact store, and the tabled
round machine. -/
def rung : Rung where
  pre := Preprocessor.id
  rt := runtime

end R001

end RwLog
