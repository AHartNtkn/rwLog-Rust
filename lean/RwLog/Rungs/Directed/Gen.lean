/-
# Goal-directed tables, written against the kernel

The tabled round machine (`Rungs/Tabled/Base/Engine.lean`) evaluates the two factors
of a sequence `lb ; (a ; b) ; rb` on their own and joins their answers, and
pushes the answers of one factor into the other only once that factor is
complete. So a factor that nothing restricts is evaluated in full, however
little of it the other factor can use.

This machine keeps the goals, the tables and the rounds, and reads a sequence
by what restricts it. The sequence is *restricted on the left* when it has a
left boundary or `a` is a span, and on the right likewise.

* Restricted on the left: the left sub-goal `lb ; a` is evaluated, and each of
  its maximal answers `x` is pushed into the right factor as it arrives: the
  goal `x.rightIface ; b ; rb` is run and its answers are composed with `x`.
  The right factor is never evaluated without a boundary.
* Restricted on the right: the mirror image.
* Restricted on both sides: both of the above.
* Restricted on neither: the join of the two sub-goals, as in R001.

A span at an end of a sequence is thereby a boundary of the other factor's
goal: its table holds the span, and the span's interface is pushed.

Everything else is read as the tabled machine reads it. There is no unfolding
race and no table of this machine is ever marked complete, so it never
reports exhaustion, and a conjunction is the join of its sides. The machine is
sound, and is run beside a machine that is complete (`Rungs/Hedge`), which is
where completeness and exhaustion come from.

Like the tabled machine it is written for an arbitrary kernel
(`Trusted/Kernel.lean`). `Machine.lean` is this text in the cost monad, and
`Reading.lean` proves the two equal at the kernel of the language.
-/
import RwLog.Rungs.Tabled.Gen

namespace RwLog

open R001 Traverse

namespace Directed

/-- Is the expression a span? -/
def isSpan {S : Type} : RelOf S → Bool
  | .span _ => true
  | _ => false

namespace Gen

open RwLog.Gen Tabled.Gen

variable {Sp : Type} {M : Type → Type} [Kernel Sp M]

/-- The candidates of a sequence `lb ; (a ; b) ; rb`, and the goals it
needs. -/
def seqCandidates (P : ProgramOf Sp) (ts : TablesOf Sp) (g : GoalOf Sp) (a b : RelOf Sp) :
    M (List Sp × List (GoalOf Sp)) := do
  let T := P.theory
  let L := seqLeft g a
  let R := seqRight g b
  let lB := g.lb.isSome || isSpan a
  let rB := g.rb.isSome || isSpan b
  if lB || rB then do
    let pl ← if lB then do
        let xs ← Tabled.Gen.answersOf ts L
        let m ← Tabled.Gen.maxima xs
        Tabled.Gen.pushes (Tabled.Gen.seqPushL g b) m
      else pure []
    let pr ← if rB then do
        let ys ← Tabled.Gen.answersOf ts R
        let m ← Tabled.Gen.maxima ys
        Tabled.Gen.pushes (Tabled.Gen.seqPushR g a) m
      else pure []
    let cl ← flatMapL (fun p => do
      let ys' ← Tabled.Gen.answersOf ts p.2
      flatMapL (fun y => Tabled.Gen.composeLive T p.1 y) ys') pl
    let cr ← flatMapL (fun p => do
      let xs' ← Tabled.Gen.answersOf ts p.2
      flatMapL (fun x => Tabled.Gen.composeLive T x p.1) xs') pr
    pure (cl ++ cr,
      (if lB then [L] else []) ++ (if rB then [R] else []) ++ pl.map Prod.snd ++ pr.map Prod.snd)
  else do
    let xs ← Tabled.Gen.answersOf ts L
    let ys ← Tabled.Gen.answersOf ts R
    let join ← flatMapL (fun x => flatMapL (fun y => Tabled.Gen.composeLive T x y) ys) xs
    pure (join, [L, R])

/-- The candidates of a goal, and the goals it needs. -/
def candidates (P : ProgramOf Sp) (ts : TablesOf Sp) (g : GoalOf Sp) :
    M (List Sp × List (GoalOf Sp)) :=
  match g.e with
  | .seq a b => seqCandidates P ts g a b
  | _ => Tabled.Gen.produceStrategies P ts g

/-- One round: every table is read (charged by the size of its goal) and
recomputes its candidates, and the tables are updated at once. A round costs
at least one tick. -/
def round (st : StateOf Sp) : M (StateOf Sp × List Sp) := do
  let ts := st.tables
  Kernel.tick Sp 1
  let outs ← mapL (fun t => do
    Kernel.tick Sp (goalSize t.goal)
    candidates st.P ts t.goal) ts
  let ts1 ← mapL (fun p => do
    let f ← Tabled.Gen.fresh p.1.answers p.2.1
    pure { p.1 with answers := p.1.answers ++ f }) (ts.zip outs)
  let reqs ← mapL (fun g => do
    let k ← Tabled.Gen.norm g
    pure k.2) (outs.flatMap Prod.snd)
  let newGoals ← foldL (fun acc g => do
    let b ← anyL (fun t => Tabled.Gen.same t.goal g) ts
    if b then pure acc else do
      let b' ← anyL (fun h => Tabled.Gen.same h g) acc
      pure (if b' then acc else acc ++ [g])) [] reqs
  let ts3 : TablesOf Sp := ts1 ++ newGoals.map fun g => ⟨g, [], false⟩
  let rootNew := match ts.head?, ts1.head? with
    | some t, some t' => t'.answers.drop t.answers.length
    | _, _ => []
  pure (⟨st.P, ts3, st.rootFlip, st.depth + 1⟩, Tabled.Gen.orient st.rootFlip rootNew)

/-- A step is a round: the machine never reports exhaustion. -/
def step (st : StateOf Sp) : M (StepOf Sp (StateOf Sp)) := do
  let r ← round st
  pure (.emit r.2 r.1)

/-- The goal-directed tabled machine, as an engine. -/
def engine : Engine where
  State := StateOf
  init P q := Tabled.Gen.ofGoal P ⟨none, q, none⟩
  step st := step st

end Gen

end Directed

end RwLog
