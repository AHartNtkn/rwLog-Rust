/-
# Goal-directed tables as a charged computation

The machine of `Gen.lean` (which says what it does and why) written in the
cost monad, definition for definition, with the charged table operations of
`Rungs/Tabled/Machine.lean`. `Reading.lean` proves it is that engine read at
the kernel of the language; the proofs about the machine are carried out
here.
-/
import RwLog.Rungs.Tabled.Machine
import RwLog.Rungs.Directed.Gen

namespace RwLog

open R001 Cost

namespace Directed



/-- The candidates of a sequence `lb ; (a ; b) ; rb`, and the goals it
needs. -/
def seqCandidates (P : Program) (ts : Tables) (g : Goal) (a b : Rel) :
    Cost (List Span × List Goal) := do
  let T := P.theory
  let L := seqLeft g a
  let R := seqRight g b
  let lB := g.lb.isSome || isSpan a
  let rB := g.rb.isSome || isSpan b
  if lB || rB then do
    let pl ← if lB then do
        let xs ← Tabled.answersOf ts L
        let m ← Tabled.maxima xs
        Tabled.pushes (Tabled.seqPushL g b) m
      else pure []
    let pr ← if rB then do
        let ys ← Tabled.answersOf ts R
        let m ← Tabled.maxima ys
        Tabled.pushes (Tabled.seqPushR g a) m
      else pure []
    let cl ← flatMapL (fun p => do
      let ys' ← Tabled.answersOf ts p.2
      flatMapL (fun y => Tabled.composeLive T p.1 y) ys') pl
    let cr ← flatMapL (fun p => do
      let xs' ← Tabled.answersOf ts p.2
      flatMapL (fun x => Tabled.composeLive T x p.1) xs') pr
    pure (cl ++ cr,
      (if lB then [L] else []) ++ (if rB then [R] else []) ++ pl.map Prod.snd ++ pr.map Prod.snd)
  else do
    let xs ← Tabled.answersOf ts L
    let ys ← Tabled.answersOf ts R
    let join ← flatMapL (fun x => flatMapL (fun y => Tabled.composeLive T x y) ys) xs
    pure (join, [L, R])

/-- The candidates of a goal, and the goals it needs. -/
def candidates (P : Program) (ts : Tables) (g : Goal) : Cost (List Span × List Goal) :=
  match g.e with
  | .seq a b => seqCandidates P ts g a b
  | _ => Tabled.produceStrategies P ts g

/-- One round: every table is read (charged by the size of its goal) and
recomputes its candidates, and the tables are updated at once. A round costs
at least one tick. -/
def round (st : State) : Cost (State × List Span) := do
  let ts := st.tables
  tick 1
  let outs ← mapL (fun t => do
    tick (goalSize t.goal)
    candidates st.P ts t.goal) ts
  let ts1 ← mapL (fun p => do
    let f ← Tabled.fresh p.1.answers p.2.1
    pure { p.1 with answers := p.1.answers ++ f }) (ts.zip outs)
  let reqs ← mapL (fun g => do
    let k ← Tabled.norm g
    pure k.2) (outs.flatMap Prod.snd)
  let newGoals ← foldL (fun acc g => do
    let b ← anyL (fun t => Tabled.same t.goal g) ts
    if b then pure acc else do
      let b' ← anyL (fun h => Tabled.same h g) acc
      pure (if b' then acc else acc ++ [g])) [] reqs
  let ts3 : Tables := ts1 ++ newGoals.map fun g => ⟨g, [], false⟩
  let rootNew := match ts.head?, ts1.head? with
    | some t, some t' => t'.answers.drop t.answers.length
    | _, _ => []
  pure (⟨st.P, ts3, st.rootFlip, st.depth + 1⟩, R001.orient st.rootFlip rootNew)

/-- A step is a round: the machine never reports exhaustion. -/
def step (st : State) : Cost (Step State) := do
  let r ← round st
  pure (.emit r.2 r.1)

/-- The goal-directed tabled machine. -/
def machine : CostedRuntime where
  State := State
  init P q := Tabled.ofGoal P ⟨none, q, none⟩
  step := step

end Directed

end RwLog
