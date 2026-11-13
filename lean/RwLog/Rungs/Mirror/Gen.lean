/-
# A machine run on a query and on its mirror image, side by side

What a machine pays for a query can depend on the end the query was written
from. `Engine.mirrored E` removes that dependence for any machine `E`: it runs
`E` on the query and `E` on the mirror image of the query in the mirrored
program, and its `k`-th step is the `k`-th step of whichever of the two gets
there first.

## The state

The two runs are kept apart. One of them is the *leader*: it has taken as
many steps as the machine has. The other is `gap` steps behind. `fwd` says
whether the leader is the run on the query itself.

## A step

The machine pays one tick of its own and races the next steps of the two runs
(`Kernel.race`).

When one run is behind, the leader's step is raced first against the other
run's.

* If the leader's step finishes first, its answers are emitted, swapped back
  if the leader is the run on the mirror image, and the gap grows by one.
* If the other run's step finishes first, it is one step closer and nothing
  is emitted yet: the machine races again. So a step of the machine ends only
  when one of the two runs has taken one more step than the machine had, and
  the answers of that step are emitted once.

When the two runs are level there is no leader to prefer, and the mirror
image of the query would have the two runs the other way round. So the
machine races them twice, once in each order (`level`).

* If the same run wins both races, it takes its step alone, its answers are
  emitted, and it is the leader, one step ahead.
* Otherwise each run has won a race, both steps are in hand, and both runs
  take their step: the answers of the leader's are emitted and the runs stay
  level.

If a step that was taken reports that it is done, the machine is done.

For a machine whose run on the mirror image is the mirror image of its run,
step for step (`Runtime.DualTrace`), the `k`-th steps of the two runs emit
the same answers up to swapping, so what the machine emits does not depend on
which of them won, and when one of them is done so is the other
(`Rungs/Mirror/Trace.lean`).

## What it costs

A race costs at most 7 times the cheaper of the two steps it races, and each
of the two runs takes at most `n` steps by the time the machine has taken
`n`. So the first `n` steps of the machine cost at most `2 n` rounds of at
most two races, each race of at most 7 times the cheaper of what the two runs
pay for their first `n` steps (`Rungs/Mirror/Bounds.lean`).

On the mirror image of the query the same two runs are raced, and no step of
the machine prefers one of them except for being ahead. So the machine pays
exactly the same, step for step, on a query and on its mirror image
(`Rungs/Mirror/Direction.lean`).

This is the machine written against the kernel. `Machine.lean` is the same
text in the cost monad, for any costed machine, and `Reading.lean` proves the
two equal at the kernel of the language.
-/
import RwLog.Trusted.Cost

namespace RwLog

namespace Mirror

/-- The two runs: the leader, the other run, whether the leader is the run on
the query itself, and how many steps the other run is behind. -/
structure StOf (σ : Type) where
  lead : σ
  lag : σ
  fwd : Bool
  gap : Nat

namespace Gen

variable {Sp : Type} {M : Type → Type} [Kernel Sp M]

/-- The mirror image of an expression: every span is swapped and every
sequence reversed. -/
def dualRel : RelOf Sp → RelOf Sp
  | .zero => .zero
  | .span s => .span (Kernel.swap s)
  | .or a b => .or (dualRel a) (dualRel b)
  | .and a b => .and (dualRel a) (dualRel b)
  | .seq a b => .seq (dualRel b) (dualRel a)
  | .conv a => .conv (dualRel a)
  | .call n => .call n

/-- The mirrored program: every body is mirrored. -/
def dualProg (P : ProgramOf Sp) : ProgramOf Sp :=
  { P with defs := P.defs.map fun d => (d.1, dualRel d.2) }

/-- The answers of a run, as answers to the query: those of the run on the
mirror image are swapped back. -/
def orient (fwd : Bool) (as : List Sp) : List Sp := if fwd then as else as.map Kernel.swap

/-- The step from level runs, given what the two races returned: the first
raced the leader `x` before the other run `y`, the second `y` before `x`. -/
def level {σ : Type} (f : Bool) (x y : σ) :
    StepOf Sp σ ⊕ StepOf Sp σ → StepOf Sp σ ⊕ StepOf Sp σ → StepOf Sp (StOf σ)
  | .inl (.emit as x'), .inl _ => .emit (orient f as) ⟨x', y, f, 1⟩
  | .inr (.emit as y'), .inr _ => .emit (orient (!f) as) ⟨y', x, !f, 1⟩
  | .inl (.emit as x'), .inr (.emit _ y') => .emit (orient f as) ⟨x', y', f, 0⟩
  | .inr (.emit _ y'), .inl (.emit as x') => .emit (orient f as) ⟨x', y', f, 0⟩
  | _, _ => .done

/-- One step of the machine, from a gap of `g`: race the leader `x` against
the other run `y` until one of them has taken one more step than the machine
had. -/
def go {σ : Type} (step : σ → M (StepOf Sp σ)) :
    Nat → Bool → σ → σ → M (StepOf Sp (StOf σ))
  | 0, f, x, y => do
    Kernel.tick Sp 1
    let r ← Kernel.race Sp (Sum.inl <$> step x) (Sum.inr <$> step y)
    let r' ← Kernel.race Sp (Sum.inr <$> step y) (Sum.inl <$> step x)
    pure (level f x y r r')
  | g + 1, f, x, y => do
    Kernel.tick Sp 1
    let r ← Kernel.race Sp (Sum.inl <$> step x) (Sum.inr <$> step y)
    match r with
    | .inl (.emit as x') => pure (.emit (orient f as) ⟨x', y, f, g + 2⟩)
    | .inl .done => pure .done
    | .inr (.emit _ y') => go step g f x y'
    | .inr .done => pure .done

end Gen

end Mirror

/-- `E` run on the query and on its mirror image, side by side. -/
def Engine.mirrored (E : Engine) : Engine where
  State S := Mirror.StOf (E.State S)
  init P q := do
    let x ← E.init P q
    let y ← E.init (Mirror.Gen.dualProg P) (Mirror.Gen.dualRel q)
    pure ⟨x, y, true, 0⟩
  step st := Mirror.Gen.go (fun s => E.step s) st.gap st.fwd st.lead st.lag

end RwLog
