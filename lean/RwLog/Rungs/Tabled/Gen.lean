/-
# The tabled round machine, written against the kernel

This is the tabled round machine (`Rungs/R001/Engine.lean` says what it does
and why) as an engine: it is written for an arbitrary type of spans and an
arbitrary monad, and everything it does to a span is an operation of the
kernel (`Trusted/Kernel.lean`). Its cost is therefore not its own to declare.

The one part left open is the unfolding race: the machine takes an oracle
that says, for a goal and a depth, whether the goal's unfolding to that depth
is final and, if it is, what its answers are. Each incomplete table asks the
oracle once per round. An oracle is written against the kernel too.

`Rungs/Tabled/Machine.lean` is this text read at the kernel of the language,
definition for definition (`Rungs/Tabled/Reading.lean` proves they are equal),
and the proofs about the machine are carried out on that reading.
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.R001.Engine
import RwLog.Rungs.Framework.Traverse

namespace RwLog

open R001 Traverse

/-- The size of an expression: its nodes, with each span counted by its
size. -/
def Gen.relSize {S : Type} {M : Type → Type} [Kernel S M] : RelOf S → Nat
  | .zero => 1
  | .span s => 1 + Kernel.size s
  | .or a b => 1 + relSize a + relSize b
  | .and a b => 1 + relSize a + relSize b
  | .seq a b => 1 + relSize a + relSize b
  | .conv a => 1 + relSize a
  | .call _ => 1

/-- The size of a goal: its expression and its boundaries. -/
def Gen.goalSize {S : Type} {M : Type → Type} [Kernel S M] (g : GoalOf S) : Nat :=
  Gen.relSize g.e + ((g.lb.toList ++ g.rb.toList).map Kernel.size).sum

/-- The unfolding race, written against the kernel: is the goal's unfolding
to this depth final, and its answers if it is (none otherwise). -/
abbrev GOracle (S : Type) (M : Type → Type) := ProgramOf S → Nat → GoalOf S → M (Bool × List S)

/-- An unfolding race for every kernel. -/
abbrev Unfolder := {S : Type} → {M : Type → Type} → [Kernel S M] → GOracle S M

namespace Tabled

namespace Gen

open RwLog.Gen

def gfpFrom {M : Type → Type} [Monad M] (ok : List Nat → Nat → M Bool) : Nat → List Nat → M (List Nat)
  | 0, S => pure S
  | n + 1, S => do
    let S' ← filterL (ok S) S
    if S'.length = S.length then pure S else gfpFrom ok n S'

variable {Sp : Type} {M : Type → Type} [Kernel Sp M]

/-! ## Charged table operations -/

/-- Strip converses from a canonical expression, swapping the boundaries. -/
def stripConv (lb : Option Sp) : RelOf Sp → Option Sp → Bool × GoalOf Sp
  | .conv a, rb =>
    let r := stripConv (rb.map Kernel.swap) a (lb.map Kernel.swap)
    (!r.1, r.2)
  | e, rb => (false, ⟨lb, e, rb⟩)

/-- Bring a goal to its table key: the canonical form of its expression, with
converses stripped. Charged by the size of the whole goal. -/
def norm (g : GoalOf Sp) : M (Bool × GoalOf Sp) := do
  let e ← Kernel.canon g.e
  Kernel.tick Sp ((g.lb.toList ++ g.rb.toList).map Kernel.size).sum
  pure (stripConv g.lb e g.rb)

/-- Are two boundaries equivalent? Each covers the other. -/
def sameBound : Option Sp → Option Sp → M Bool
  | none, none => pure true
  | some a, some b => do
    let x ← Kernel.covers a b
    if x then Kernel.covers b a else pure false
  | _, _ => pure false

/-- Compare two table keys: the expressions as written, then the boundaries
up to equivalence. -/
def same (g h : GoalOf Sp) : M Bool := do
  let b ← Kernel.eqRel g.e h.e
  if b then do
    let l ← sameBound g.lb h.lb
    if l then sameBound g.rb h.rb else pure false
  else pure false

/-- The answers of a table, read for a goal that is its key or the converse
of its key. -/
def orient (flip : Bool) (xs : List Sp) : List Sp := if flip then xs.map Kernel.swap else xs

/-- The goal a converse forwards to. -/
def convGoal (g : GoalOf Sp) (a : RelOf Sp) : GoalOf Sp :=
  ⟨g.rb.map Kernel.swap, a, g.lb.map Kernel.swap⟩

def findTable (ts : TablesOf Sp) (g : GoalOf Sp) : M (Option (TableOf Sp)) :=
  findL (fun t => same t.goal g) ts

/-- The position of the first table with this key, counting from `i`. -/
def indexFrom (g : GoalOf Sp) : Nat → TablesOf Sp → M (Option Nat)
  | _, [] => pure none
  | i, t :: ts => do
    let b ← same t.goal g
    if b then pure (some i) else indexFrom g (i + 1) ts

def indexOf (ts : TablesOf Sp) (g : GoalOf Sp) : M (Option Nat) := indexFrom g 0 ts

def answersOf (ts : TablesOf Sp) (g : GoalOf Sp) : M (List Sp) := do
  let n ← norm g
  let t ← findTable ts n.2
  pure (match t with
    | some t => orient n.1 t.answers
    | none => [])

def doneOf (ts : TablesOf Sp) (g : GoalOf Sp) : M Bool := do
  let n ← norm g
  let t ← findTable ts n.2
  pure (match t with
    | some t => t.done
    | none => false)

/-! ## Charged kernel steps -/

def live (T : Theory) (s : Sp) : M (List Sp) := do
  let r ← Kernel.simplify T s
  pure r.toList

def composeLive (T : Theory) (x y : Sp) : M (List Sp) := do
  let z ← Kernel.compose x y
  match z with
  | some z => live T z
  | none => pure []

def meetLive (T : Theory) (x y : Sp) : M (List Sp) := do
  let z ← Kernel.meet x y
  match z with
  | some z => live T z
  | none => pure []

def spanAnswer (T : Theory) (lb : Option Sp) (s : Sp) (rb : Option Sp) : M (List Sp) := do
  let left ← match lb with
    | none => pure (some s)
    | some l => Kernel.compose l s
  let both ← match left, rb with
    | none, _ => pure none
    | some s', none => pure (some s')
    | some s', some r => Kernel.compose s' r
  match both with
  | some z => live T z
  | none => pure []

def maxima (xs : List Sp) : M (List Sp) := do
  let top ← filterL (fun x => do
    let b ← anyL (fun y => do
      let c ← Kernel.covers y x
      if c then do
        let c' ← Kernel.covers x y
        pure !c'
      else pure false) xs
    pure !b) xs
  foldL (fun acc x => do
    let b ← anyL (fun y => Kernel.covers y x) acc
    pure (if b then acc else acc ++ [x])) [] top

def fresh (old cands : List Sp) : M (List Sp) := do
  let cs ← filterL (fun c => do
    let b ← anyL (fun t => Kernel.covers t c) old
    pure !b) cands
  maxima cs

/-! ## Pushed goals

The goal a strategy runs for an answer of the other side takes an interface
of that answer as a boundary, at the kernel's charge. -/

def seqPushL (g : GoalOf Sp) (b : RelOf Sp) (x : Sp) : M (GoalOf Sp) := do
  let c ← Kernel.rightBound x
  pure ⟨c, b, g.rb⟩

def seqPushR (g : GoalOf Sp) (a : RelOf Sp) (y : Sp) : M (GoalOf Sp) := do
  let c ← Kernel.leftBound y
  pure ⟨g.lb, a, c⟩

def andPush (e : RelOf Sp) (x : Sp) : M (GoalOf Sp) := do
  let l ← Kernel.leftBound x
  let r ← Kernel.rightBound x
  pure ⟨l, e, r⟩

/-- Each answer with the goal pushed for it. -/
def pushes (f : Sp → M (GoalOf Sp)) (xs : List Sp) : M (List (Sp × GoalOf Sp)) :=
  mapL (fun x => do
    let p ← f x
    pure (x, p)) xs

/-! ## Candidates and strategies -/

/-- The candidates of the strategies that read other tables, and the goals
they need. -/
def produceStrategies (P : ProgramOf Sp) (ts : TablesOf Sp) (g : GoalOf Sp) : M (List Sp × List (GoalOf Sp)) :=
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
    pure (xs.map Kernel.swap, [g'])
  | .seq a b => do
    let L := seqLeft g a
    let R := seqRight g b
    let xs ← answersOf ts L
    let ys ← answersOf ts R
    let join ← flatMapL (fun x => flatMapL (fun y => composeLive T x y) ys) xs
    let dl ← doneOf ts L
    let pl ← if dl then do
        let m ← maxima xs
        pushes (seqPushL g b) m
      else pure []
    let dr ← doneOf ts R
    let pr ← if dr then do
        let m ← maxima ys
        pushes (seqPushR g a) m
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
        pushes (andPush b) m
      else pure []
    let dr ← doneOf ts R
    let pr ← if dr then do
        let m ← maxima ys
        pushes (andPush a) m
      else pure []
    let cl ← flatMapL (fun p => do
      let ys' ← answersOf ts p.2
      flatMapL (fun y => meetLive T p.1 y) ys') pl
    let cr ← flatMapL (fun p => do
      let xs' ← answersOf ts p.2
      flatMapL (fun x => meetLive T x p.1) xs') pr
    pure (join ++ cl ++ cr, [L, R] ++ pl.map Prod.snd ++ pr.map Prod.snd)

/-- The candidates of a goal, given what the oracle said about it. -/
def produce (P : ProgramOf Sp) (ts : TablesOf Sp) (g : GoalOf Sp) (u : Bool × List Sp) :
    M (List Sp × List (GoalOf Sp)) := do
  let r ← produceStrategies P ts g
  pure (u.2 ++ r.1, r.2)

/-- The strategies that read other tables. -/
def tableStrategies (P : ProgramOf Sp) (ts : TablesOf Sp) (g : GoalOf Sp) : M (List (List (GoalOf Sp))) :=
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
        let ps ← mapL (seqPushL g b) m
        pure [L :: ps]
      else pure []
    let dr ← doneOf ts R
    let sr ← if dr then do
        let ys ← answersOf ts R
        let m ← maxima ys
        let ps ← mapL (seqPushR g a) m
        pure [R :: ps]
      else pure []
    pure ([[L, R]] ++ sl ++ sr)
  | .and a b => do
    let L := andLeft g a
    let R := andRight g b
    let dl ← doneOf ts L
    let sl ← if dl then do
        let xs ← answersOf ts L
        let m ← maxima xs
        let ps ← mapL (andPush b) m
        pure [L :: ps]
      else pure []
    let dr ← doneOf ts R
    let sr ← if dr then do
        let ys ← answersOf ts R
        let m ← maxima ys
        let ps ← mapL (andPush a) m
        pure [R :: ps]
      else pure []
    pure ([[L, R]] ++ sl ++ sr)

/-- The strategies of a goal whose unfolding is final or not, as the oracle
said. -/
def strategies (P : ProgramOf Sp) (final : Bool) (ts : TablesOf Sp) (g : GoalOf Sp) : M (List (List (GoalOf Sp))) := do
  let s ← tableStrategies P ts g
  pure ((if final then [[]] else []) ++ s)

/-! ## One round -/

/-- The tables that complete at the end of a round; `finals` is what the
oracle said about each table. -/
def completing (P : ProgramOf Sp) (finals : List Bool) (ts ts' : TablesOf Sp) : M (List Nat) :=
  let n := ts.length
  let gained (j : Nat) : Bool := decide ((ts'.getD j ⟨⟨none, .zero, none⟩, [], false⟩).answers.length
    ≠ (ts.getD j ⟨⟨none, .zero, none⟩, [], false⟩).answers.length)
  let isDone (j : Nat) : Bool := (ts.getD j ⟨⟨none, .zero, none⟩, [], false⟩).done
  let S0 := (List.range n).filter fun i => !isDone i && !gained i
  let ok (S : List Nat) (i : Nat) : M Bool := do
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
at once. A round costs at least one Kernel.tick Sp. -/
def round (U : GOracle Sp M) (st : StateOf Sp) : M (StateOf Sp × List Sp) := do
  let ts := st.tables
  Kernel.tick Sp 1
  let us ← mapL (fun t => if t.done then pure (false, []) else do
    Kernel.tick Sp (goalSize t.goal)
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
  let ts2 : TablesOf Sp := ts1.mapIdx fun i t => if S.contains i then { t with done := true } else t
  let ts3 : TablesOf Sp := ts2 ++ newGoals.map fun g => ⟨g, [], false⟩
  let rootNew := match ts.head?, ts1.head? with
    | some t, some t' => t'.answers.drop t.answers.length
    | _, _ => []
  pure (⟨st.P, ts3, st.rootFlip, st.depth + 1⟩, orient st.rootFlip rootNew)

def step (U : GOracle Sp M) (st : StateOf Sp) : M (StepOf Sp (StateOf Sp)) :=
  if st.finished then pure .done else do
    let r ← round U st
    pure (.emit r.2 r.1)

/-- The state for a goal: its table alone. Bringing the goal to its table key
is charged. -/
def ofGoal (P : ProgramOf Sp) (g : GoalOf Sp) : M (StateOf Sp) := do
  let n ← norm g
  pure ⟨P, [⟨n.2, [], false⟩], n.1, 0⟩

/-- The tabled round machine with a given unfolding race, as an engine. -/
def engine (U : Unfolder) : Engine where
  State := StateOf
  init P q := ofGoal P ⟨none, q, none⟩
  step st := step U st

end Gen

end Tabled

end RwLog
