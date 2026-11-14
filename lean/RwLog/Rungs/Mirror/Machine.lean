/-
# A machine run on a query and on its converse, side by side

What a machine pays for a query can depend on the end the query was written
from. `Engine.mirrored E` removes that dependence for any engine `E`: it runs
`E` on the root node and `E` on the converse of the root node
(`DerivationKernel.convNode`), and its `k`-th step is the `k`-th step of
whichever of the two gets there first.

In the normal form the converse of a node is its mirror image: chains are
reversed, spans swapped, and a call reads the converse of its body. So the
run on the converse node is the run on the mirror image of the query in the
mirrored program, and no second program is needed.

## The state

The two runs are kept apart. One of them is the *leader*: it has taken as
many steps as the machine has. The other is `gap` steps behind. `fwd` says
whether the leader is the run on the root node itself.

## A step

The machine pays one tick of its own and races the next steps of the two runs
(`Kernel.race`).

When one run is behind, the leader's step is raced first against the other
run's.

* If the leader's step finishes first, what it shows is shown, its answers
  conversed (`swapA`) if the leader is the run on the converse, and the gap
  grows by one.
* If the other run's step finishes first, it is one step closer and nothing
  is shown yet: the machine races again. So a step of the machine ends only
  when one of the two runs has taken one more step than the machine had, and
  what that step shows is shown once.

When the two runs are level there is no leader to prefer, and the converse of
the query would have the two runs the other way round. So the machine races
them twice, once in each order (`level`).

* If the same run wins both races, it takes its step alone, what it shows is
  shown, and it is the leader, one step ahead.
* Otherwise each run has won a race, both steps are in hand, and both runs
  take their step: what the leader's shows is shown and the runs stay level.

If a step that was taken reports that it is done, the machine is done, with
that step's final report.

For a machine whose run on the converse is the mirror image of its run, step
for step, the `k`-th steps of the two runs show the same answers up to
converse and order, so what the machine shows does not depend on which of
them won, and when one of them is done so is the other.

## What it costs

A race costs at most 7 times the cheaper of the two steps it races, and each
of the two runs takes at most `n` steps by the time the machine has taken
`n`. On the converse of the query the same two runs are raced, and no step of
the machine prefers one of them except for being ahead.
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.Framework.Traverse

namespace RwLog

namespace Mirror

open Traverse

/-- The two runs: the leader, the other run, whether the leader is the run on
the root node itself, and how many steps the other run is behind. -/
structure StOf (σ : Type) where
  lead : σ
  lag : σ
  fwd : Bool
  gap : Nat

section

variable {S N A : Type} {M : Type → Type} [K : DerivationKernel S N A M]

/-- The answers of a run, as answers of the root goal: those of the run on
the converse are conversed. -/
def orient (fwd : Bool) (as : List A) : M (List A) :=
  if fwd then pure as else mapL (fun a => K.swapA a) as

variable {σ : Type}

/-- What a step of one run shows, as a step of the machine: `fwd` says
whether the run is the one on the root node, and `next` is the state of the
machine once the run has taken the step. -/
def shown (fwd : Bool) (next : σ → StOf σ) : StepOf A σ → M (StepOf A (StOf σ))
  | .emit as s => do
    let bs ← orient (K := K) fwd as
    pure (.emit bs (next s))
  | .progress n s => pure (.progress n (next s))
  | .done fin => do
    let bs ← orient (K := K) fwd fin
    pure (.done bs)

/-- The state a run is in after its step, if it goes on. -/
def after : StepOf A σ → Option σ
  | .emit _ s => some s
  | .progress _ s => some s
  | .done _ => none

/-- The step from level runs, given what the two races returned: the first
raced the leader `x` before the other run `y`, the second `y` before `x`. -/
def level (f : Bool) (x y : σ) :
    StepOf A σ ⊕ StepOf A σ → StepOf A σ ⊕ StepOf A σ → M (StepOf A (StOf σ))
  | .inl sx, .inl _ => shown (K := K) f (fun x' => ⟨x', y, f, 1⟩) sx
  | .inr sy, .inr _ => shown (K := K) (!f) (fun y' => ⟨y', x, !f, 1⟩) sy
  | .inl sx, .inr sy | .inr sy, .inl sx =>
    match after sy with
    | some y' => shown (K := K) f (fun x' => ⟨x', y', f, 0⟩) sx
    | none =>
      match after sx with
      | some _ => shown (K := K) (!f) (fun y' => ⟨y', x, !f, 0⟩) sy
      | none => shown (K := K) f (fun x' => ⟨x', y, f, 0⟩) sx

/-- One step of the machine, from a gap of `g`: race the leader `x` against
the other run `y` until one of them has taken one more step than the machine
had. -/
def go (step : σ → M (StepOf A σ)) : Nat → Bool → σ → σ → M (StepOf A (StOf σ))
  | 0, f, x, y => do
    K.tick 1
    let r ← K.race (Sum.inl <$> step x) (Sum.inr <$> step y)
    let r' ← K.race (Sum.inr <$> step y) (Sum.inl <$> step x)
    level (K := K) f x y r r'
  | g + 1, f, x, y => do
    K.tick 1
    let r ← K.race (Sum.inl <$> step x) (Sum.inr <$> step y)
    match r with
    | .inl sx => shown (K := K) f (fun x' => ⟨x', y, f, g + 2⟩) sx
    | .inr sy =>
      match after sy with
      | some y' => go step g f x y'
      | none => shown (K := K) (!f) (fun y' => ⟨y', x, !f, 0⟩) sy

end

end Mirror

/-- `E` run on the root node and on its converse, side by side. -/
def Engine.mirrored (E : Engine) : Engine where
  State S N A := Mirror.StOf (E.State S N A)
  init {_ _ _ _} K root := do
    let x ← E.init root
    let c ← K.convNode root
    let y ← E.init c
    pure ⟨x, y, true, 0⟩
  step {_ _ _ _} K st := Mirror.go (K := K) (fun s => E.step s) st.gap st.fwd st.lead st.lag

end RwLog
