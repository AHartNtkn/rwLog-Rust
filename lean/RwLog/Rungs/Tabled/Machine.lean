/-
# The tabled round machine as a charged computation

This is rung R001's machine (`RwLog.R001`, see `Rungs/R001/Engine.lean` for
what it does and why) written in the cost monad, definition for definition, so
that its cost is the cost of the kernel operations it performs. The only part
left open is the unfolding race: the machine takes an `Oracle` that says, for
a goal and a depth, whether the goal's unfolding to that depth is final and,
if it is, what its answers are. Each incomplete table asks the oracle once per
round.

Two oracles are given in `Rungs/R002/Unfold.lean`: R001's own way of computing the
answer, and R002's. Because both go through this one machine, they are charged
the same for everything else.

Comparing two table keys is charged as the comparison of their expressions
and the coverage tests on their boundaries; bringing a goal to its table key
is charged by the size of the goal.
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.R001.Engine

namespace RwLog

open R001 Cost

/-- The size of a goal: its expression and its boundaries. -/
def goalSize (g : Goal) : Nat :=
  g.e.size + ((g.lb.toList ++ g.rb.toList).map Span.size).sum

/-- The unfolding race, as a charged computation: is the goal's unfolding to
this depth final, and its answers if it is (none otherwise). -/
abbrev Oracle := Program → Nat → Goal → Cost (Bool × List Span)

namespace Tabled

/-! ## Charged table operations -/

/-- Are two boundaries equivalent? Each covers the other. -/
def sameBound : Option Span → Option Span → Cost Bool
  | none, none => pure true
  | some a, some b => do
    let x ← Charged.covers a b
    if x then Charged.covers b a else pure false
  | _, _ => pure false

/-- Compare two table keys: the expressions as written, then the boundaries
up to equivalence. -/
def same (g h : Goal) : Cost Bool := do
  let b ← Charged.eqRel g.e h.e
  if b then do
    let l ← sameBound g.lb h.lb
    if l then sameBound g.rb h.rb else pure false
  else pure false

/-- Bring a goal to its table key. -/
def norm (g : Goal) : Cost (Bool × Goal) := ⟨g.norm, goalSize g⟩

def findTable (ts : Tables) (g : Goal) : Cost (Option Table) :=
  findL (fun t => same t.goal g) ts

/-- The position of the first table with this key, counting from `i`. -/
def indexFrom (g : Goal) : Nat → Tables → Cost (Option Nat)
  | _, [] => pure none
  | i, t :: ts => do
    let b ← same t.goal g
    if b then pure (some i) else indexFrom g (i + 1) ts

def indexOf (ts : Tables) (g : Goal) : Cost (Option Nat) := indexFrom g 0 ts

def answersOf (ts : Tables) (g : Goal) : Cost (List Span) := do
  let n ← norm g
  let t ← findTable ts n.2
  pure (match t with
    | some t => orient n.1 t.answers
    | none => [])

def doneOf (ts : Tables) (g : Goal) : Cost Bool := do
  let n ← norm g
  let t ← findTable ts n.2
  pure (match t with
    | some t => t.done
    | none => false)

/-! ## Charged kernel steps -/

def live (T : Theory) (s : Span) : Cost (List Span) := do
  let r ← Charged.simplify T s
  pure r.toList

def composeLive (T : Theory) (x y : Span) : Cost (List Span) := do
  let z ← Charged.compose x y
  match z with
  | some z => live T z
  | none => pure []

def meetLive (T : Theory) (x y : Span) : Cost (List Span) := do
  let z ← Charged.meet x y
  match z with
  | some z => live T z
  | none => pure []

def spanAnswer (T : Theory) (lb : Option Span) (s : Span) (rb : Option Span) : Cost (List Span) := do
  let left ← match lb with
    | none => pure (some s)
    | some l => Charged.compose l s
  let both ← match left, rb with
    | none, _ => pure none
    | some s', none => pure (some s')
    | some s', some r => Charged.compose s' r
  match both with
  | some z => live T z
  | none => pure []

def maxima (xs : List Span) : Cost (List Span) := do
  let top ← filterL (fun x => do
    let b ← anyL (fun y => do
      let c ← Charged.covers y x
      if c then do
        let c' ← Charged.covers x y
        pure !c'
      else pure false) xs
    pure !b) xs
  foldL (fun acc x => do
    let b ← anyL (fun y => Charged.covers y x) acc
    pure (if b then acc else acc ++ [x])) [] top

def fresh (old cands : List Span) : Cost (List Span) := do
  let cs ← filterL (fun c => do
    let b ← anyL (fun t => Charged.covers t c) old
    pure !b) cands
  maxima cs

/-! ## Candidates and strategies -/

/-- The candidates of the strategies that read other tables, and the goals
they need. -/
def produceStrategies (P : Program) (ts : Tables) (g : Goal) : Cost (List Span × List Goal) :=
  let T := P.theory
  match g.e with
  | .zero => pure ([], [])
  | .span s => do
    let xs ← spanAnswer T g.lb s g.rb
    pure (xs, [])
  | .or a b => do
    let gs := orLeaves g a b
    let xs ← flatMapL (answersOf ts) gs
    pure (xs, gs)
  | .call n => do
    let gb := callGoal P g n
    let xs ← answersOf ts gb
    pure (xs, [gb])
  | .conv a => do
    let g' := convGoal g a
    let xs ← answersOf ts g'
    pure (xs.map Span.swap, [g'])
  | .seq a b => do
    let L := seqLeft g a
    let R := seqRight g b
    let xs ← answersOf ts L
    let ys ← answersOf ts R
    let join ← flatMapL (fun x => flatMapL (fun y => composeLive T x y) ys) xs
    let dl ← doneOf ts L
    let pl ← if dl then do
        let m ← maxima xs
        pure (m.map fun x => (x, seqPushL g b x))
      else pure []
    let dr ← doneOf ts R
    let pr ← if dr then do
        let m ← maxima ys
        pure (m.map fun y => (y, seqPushR g a y))
      else pure []
    let cl ← flatMapL (fun p => do
      let ys' ← answersOf ts p.2
      flatMapL (fun y => composeLive T p.1 y) ys') pl
    let cr ← flatMapL (fun p => do
      let xs' ← answersOf ts p.2
      flatMapL (fun x => composeLive T x p.1) xs') pr
    pure (join ++ cl ++ cr, [L, R] ++ pl.map Prod.snd ++ pr.map Prod.snd)
  | .and a b => do
    let L := andLeft g a
    let R := andRight g b
    let xs ← answersOf ts L
    let ys ← answersOf ts R
    let join ← flatMapL (fun x => flatMapL (fun y => meetLive T x y) ys) xs
    let dl ← doneOf ts L
    let pl ← if dl then do
        let m ← maxima xs
        pure (m.map fun x => (x, andPush b x))
      else pure []
    let dr ← doneOf ts R
    let pr ← if dr then do
        let m ← maxima ys
        pure (m.map fun y => (y, andPush a y))
      else pure []
    let cl ← flatMapL (fun p => do
      let ys' ← answersOf ts p.2
      flatMapL (fun y => meetLive T p.1 y) ys') pl
    let cr ← flatMapL (fun p => do
      let xs' ← answersOf ts p.2
      flatMapL (fun x => meetLive T x p.1) xs') pr
    pure (join ++ cl ++ cr, [L, R] ++ pl.map Prod.snd ++ pr.map Prod.snd)

/-- The candidates of a goal, given what the oracle said about it. -/
def produce (P : Program) (ts : Tables) (g : Goal) (u : Bool × List Span) :
    Cost (List Span × List Goal) := do
  let r ← produceStrategies P ts g
  pure (u.2 ++ r.1, r.2)

/-- The strategies that read other tables. -/
def tableStrategies (P : Program) (ts : Tables) (g : Goal) : Cost (List (List Goal)) :=
  match g.e with
  | .zero => pure [[]]
  | .span _ => pure [[]]
  | .or a b => pure [orLeaves g a b]
  | .call n => pure [[callGoal P g n]]
  | .conv a => pure [[convGoal g a]]
  | .seq a b => do
    let L := seqLeft g a
    let R := seqRight g b
    let dl ← doneOf ts L
    let sl ← if dl then do
        let xs ← answersOf ts L
        let m ← maxima xs
        pure [L :: m.map (seqPushL g b)]
      else pure []
    let dr ← doneOf ts R
    let sr ← if dr then do
        let ys ← answersOf ts R
        let m ← maxima ys
        pure [R :: m.map (seqPushR g a)]
      else pure []
    pure ([[L, R]] ++ sl ++ sr)
  | .and a b => do
    let L := andLeft g a
    let R := andRight g b
    let dl ← doneOf ts L
    let sl ← if dl then do
        let xs ← answersOf ts L
        let m ← maxima xs
        pure [L :: m.map (andPush b)]
      else pure []
    let dr ← doneOf ts R
    let sr ← if dr then do
        let ys ← answersOf ts R
        let m ← maxima ys
        pure [R :: m.map (andPush a)]
      else pure []
    pure ([[L, R]] ++ sl ++ sr)

/-- The strategies of a goal whose unfolding is final or not, as the oracle
said. -/
def strategies (P : Program) (final : Bool) (ts : Tables) (g : Goal) : Cost (List (List Goal)) := do
  let s ← tableStrategies P ts g
  pure ((if final then [[]] else []) ++ s)

/-! ## One round -/

def gfpFrom (ok : List Nat → Nat → Cost Bool) : Nat → List Nat → Cost (List Nat)
  | 0, S => pure S
  | n + 1, S => do
    let S' ← filterL (ok S) S
    if S'.length = S.length then pure S else gfpFrom ok n S'

/-- The tables that complete at the end of a round; `finals` is what the
oracle said about each table. -/
def completing (P : Program) (finals : List Bool) (ts ts' : Tables) : Cost (List Nat) :=
  let n := ts.length
  let gained (j : Nat) : Bool := decide ((ts'.getD j ⟨⟨none, .zero, none⟩, [], false⟩).answers.length
    ≠ (ts.getD j ⟨⟨none, .zero, none⟩, [], false⟩).answers.length)
  let isDone (j : Nat) : Bool := (ts.getD j ⟨⟨none, .zero, none⟩, [], false⟩).done
  let S0 := (List.range n).filter fun i => !isDone i && !gained i
  let ok (S : List Nat) (i : Nat) : Cost Bool := do
    let strats ← strategies P (finals.getD i false) ts
      (ts.getD i ⟨⟨none, .zero, none⟩, [], false⟩).goal
    anyL (fun deps => allL (fun d => do
      let k ← norm d
      let j ← indexOf ts k.2
      pure (match j with
        | none => false
        | some j => !gained j && (isDone j || S.contains j))) deps) strats
  gfpFrom ok S0.length S0

/-- One round: every incomplete table is read (charged by the size of its
goal), asks the oracle, recomputes its candidates, and the tables are updated
at once. A round costs at least one tick. -/
def round (U : Oracle) (st : State) : Cost (State × List Span) := do
  let ts := st.tables
  tick 1
  let us ← mapL (fun t => if t.done then pure (false, []) else do
    tick (goalSize t.goal)
    U st.P st.depth t.goal) ts
  let outs ← mapL (fun p => if p.1.done then pure ([], []) else produce st.P ts p.1.goal p.2)
    (ts.zip us)
  let ts1 ← mapL (fun p => do
    let f ← fresh p.1.answers p.2.1
    pure { p.1 with answers := p.1.answers ++ f }) (ts.zip outs)
  let reqs ← mapL (fun g => do
    let k ← norm g
    pure k.2) (outs.flatMap Prod.snd)
  let newGoals ← foldL (fun acc g => do
    let b ← anyL (fun t => same t.goal g) ts
    if b then pure acc else do
      let b' ← anyL (fun h => same h g) acc
      pure (if b' then acc else acc ++ [g])) [] reqs
  let S ← completing st.P (us.map Prod.fst) ts ts1
  let ts2 : Tables := ts1.mapIdx fun i t => if S.contains i then { t with done := true } else t
  let ts3 : Tables := ts2 ++ newGoals.map fun g => ⟨g, [], false⟩
  let rootNew := match ts.head?, ts1.head? with
    | some t, some t' => t'.answers.drop t.answers.length
    | _, _ => []
  pure (⟨st.P, ts3, st.rootFlip, st.depth + 1⟩, orient st.rootFlip rootNew)

def step (U : Oracle) (st : State) : Cost (Step State) :=
  if st.finished then pure .done else do
    let r ← round U st
    pure (.emit r.2 r.1)

/-- The state for a goal: its table alone. Bringing the goal to its table key
is charged. -/
def ofGoal (P : Program) (g : Goal) : Cost State := do
  let n ← norm g
  pure ⟨P, [⟨n.2, [], false⟩], n.1, 0⟩

/-- The tabled round machine with a given unfolding oracle. -/
def machine (U : Oracle) : CostedRuntime where
  State := State
  init P q := ofGoal P ⟨none, q, none⟩
  step := step U

/-! ## A round, split at the oracle -/

/-- What a table does with the oracle in a round. -/
def ask (U : Oracle) (st : State) (t : Table) : Cost (Bool × List Span) :=
  if t.done then pure (false, []) else do
    tick (goalSize t.goal)
    U st.P st.depth t.goal

/-- A round is one tick, the tables asking the oracle, and a remainder that
sees only what the oracle answered. Two oracles with the same answers
therefore differ in cost only by what the tables spend asking. -/
theorem round_split (st : State) :
    ∃ K : List (Bool × List Span) → Cost (State × List Span), ∀ U : Oracle,
      round U st = (do
        tick 1
        let us ← mapL (ask U st) st.tables
        K us) :=
  ⟨_, fun _ => rfl⟩

end Tabled

end RwLog
