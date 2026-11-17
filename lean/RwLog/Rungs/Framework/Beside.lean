/-
# Two engines side by side

`Engine.beside E F` runs the engines `E` and `F` on the same root, each on a
state of its own, and shares the ticks between them.

Each engine has an account of what its steps have been charged. The engine
charged less takes the next step, the first of two charged alike. Its step
is run under a budget (`Kernel.within`): one tick, or twice the budget it
last gave up at. The budget is for the step and one tick for each answer it
shows. A step that fits is taken, its answers are emitted, and the engine is
charged what was spent under the budget and one tick. A step that does not fit
is given up: the state is as it was, the engine is charged the budget, and
the step is tried again with twice as much when the engine's turn comes. A
state is a value, so giving a step up costs nothing but the ticks spent on
it.

When `E` reports that it is done, the pair reports that it is done, with
`E`'s final report. When `F` reports that it is done, its final report is
emitted and `F` takes no more steps.

The pair reports that it is done exactly where `E` does, and emits everything
`E` emits (`Framework/BesideLaws.lean`). When `F` has taken `n` steps the pair
has emitted what those steps emit, or is done, and has spent a fixed multiple
of what those steps cost, whatever the steps of `E` cost
(`Engine.beside_paid`). So an engine put beside `E` need not be complete, and
it need not halt.
-/
import RwLog.Rungs.Framework.Holding

namespace RwLog

namespace Beside

/-- The state of two engines side by side: the state of each (nothing for a
second engine that is done), what each has been charged, and the budget each
last gave a step up at (nothing given up since its last step: 0). -/
structure State (X Y : Type) where
  fst : X
  snd : Option Y
  paidFst : Nat
  paidSnd : Nat
  gaveFst : Nat
  gaveSnd : Nat

/-- The budget of the next try of a step: one tick, or twice the budget last
given up at. -/
def budget (gave : Nat) : Nat := max 1 (2 * gave)

section

variable {S N A : Type} {M : Type → Type} [K : DerivationKernel S N A M] {X Y : Type}

/-- The number of answers a step shows. -/
def shown : StepOf A X → Nat
  | .emit as _ => as.length
  | .progress _ _ => 0
  | .done fin => fin.length

/-- A step charged one tick more for each answer it shows. The machine
charges as much again for reporting them (`Engine.report`), and that charge
is outside any budget; counted here, it is never more than what the budget
allowed. -/
def counted (m : M (StepOf A X)) : M (StepOf A X) := do
  let r ← m
  K.tick (shown r)
  pure r

/-- A step of the pair, from a step of each engine. -/
def step (f : X → M (StepOf A X)) (g : Y → M (StepOf A Y)) (s : State X Y) :
    M (StepOf A (State X Y)) :=
  match s.snd with
  | some y =>
    if s.paidFst ≤ s.paidSnd then do
      let r ← K.metered (K.within (budget s.gaveFst) (counted (K := K) (f s.fst)))
      match r.1 with
      | none => pure (.emit [] { s with paidFst := s.paidFst + budget s.gaveFst,
                                        gaveFst := budget s.gaveFst })
      | some (.emit as x) => pure (.emit as { s with fst := x, paidFst := s.paidFst + r.2 + 1,
                                                     gaveFst := 0 })
      | some (.progress n x) =>
        pure (.progress n { s with fst := x, paidFst := s.paidFst + r.2 + 1, gaveFst := 0 })
      | some (.done fin) => pure (.done fin)
    else do
      let r ← K.metered (K.within (budget s.gaveSnd) (counted (K := K) (g y)))
      match r.1 with
      | none => pure (.emit [] { s with paidSnd := s.paidSnd + budget s.gaveSnd,
                                        gaveSnd := budget s.gaveSnd })
      | some (.emit as y') =>
        pure (.emit as { s with snd := some y', paidSnd := s.paidSnd + r.2 + 1, gaveSnd := 0 })
      | some (.progress _ y') =>
        pure (.emit [] { s with snd := some y', paidSnd := s.paidSnd + r.2 + 1, gaveSnd := 0 })
      | some (.done fin) =>
        pure (.emit fin { s with snd := none, paidSnd := s.paidSnd + r.2 + 1, gaveSnd := 0 })
  | none => do
    let r ← f s.fst
    match r with
    | .emit as x => pure (.emit as { s with fst := x })
    | .progress n x => pure (.progress n { s with fst := x })
    | .done fin => pure (.done fin)

/-- The first state of the pair: the first state of each engine, nothing
charged. -/
def init (i : M X) (j : M Y) : M (State X Y) := do
  let x ← i
  let y ← j
  pure ⟨x, some y, 0, 0, 0, 0⟩

end

end Beside

section Holding

variable {S N A : Type}

attribute [local instance] Pack.node Pack.answer

instance : Pack S N A (Holding S N A) :=
  Pack.ofInj (fun h => (h.reps, h.nodes, h.answers, h.words))
    (fun a b e => by cases a; cases b; simp_all)

end Holding

/-- Two engines side by side (`Beside.step`). What the pair holds is what
each engine holds and the four numbers of the accounts. -/
def Engine.beside (E F : Engine) : Engine where
  State S N A := Beside.State (E.State S N A) (F.State S N A)
  init {S N A M} _ root :=
    Beside.init (S := S) (N := N) (A := A) (M := M) (E.init root) (F.init root)
  step {S N A M} _ s := Beside.step (S := S) (N := N) (A := A) (M := M) E.step F.step s
  held s := Pack.pack (E.held s.fst, s.snd.map F.held, s.paidFst, s.paidSnd, s.gaveFst, s.gaveSnd)
  held_inj S N A := by
    intro a b e
    have h := Pack.inj e
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have e1 := E.held_inj S N A h1
    have e2 : a.snd = b.snd := Option.map_injective (F.held_inj S N A) h2
    cases a; cases b; simp_all

end RwLog
