/-
# Charged computations

`Cost α` is a value together with what computing it used: the ticks spent,
and the space, counted in cells of the store.

Space has two numbers. `peak` is the most cells that were live at one moment
of the computation, above what was live when it started. `held` is the cells
the computation leaves live when it returns: what it built and handed on.
Running `m` and then `f` peaks at the larger of the peak of `m` and what `m`
holds plus the peak of `f`, and holds what both hold. An allocation is a
tick, so no operation of the kernel has a peak above its ticks.

There is no depth component. The only depth a run has is that of the call
stack, and the verified kernel keeps its stacks in the store (roadmap L43),
where they are counted as space.

This file has the monad, the budget (`Cost.within`), reading what a
computation spent (`Cost.metered`) and the free list traversals. The charged primitives, and what the ticks are used for, are in
`Trusted/Cost.lean`. It comes first because a preprocessor is a charged
computation too (`Trusted/Engine.lean`).
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Common

namespace RwLog

/-! ## Charged computations -/

/-- A value, the ticks spent computing it, the most cells live at one moment
while computing it, and the cells it leaves live. -/
structure Cost (α : Type) where
  val : α
  ticks : Nat
  peak : Nat
  held : Nat

namespace Cost

instance : Monad Cost where
  pure a := ⟨a, 0, 0, 0⟩
  bind m f := let r := f m.val
    ⟨r.val, m.ticks + r.ticks, max m.peak (m.held + r.peak), m.held + r.held⟩

/-- Spend `n` ticks. Nothing is allocated. -/
def tick (n : Nat) : Cost Unit := ⟨(), n, 0, 0⟩

/-- Run a computation and return what it spent beside its value. Reading the
tick counter is free. -/
def metered {α : Type} (m : Cost α) : Cost (α × Nat) := ⟨(m.val, m.ticks), m.ticks, m.peak, m.held⟩

@[simp] theorem pure_val {α : Type} (a : α) : (pure a : Cost α).val = a := rfl
@[simp] theorem pure_ticks {α : Type} (a : α) : (pure a : Cost α).ticks = 0 := rfl
@[simp] theorem bind_val {α β : Type} (m : Cost α) (f : α → Cost β) :
    (m >>= f).val = (f m.val).val := rfl
@[simp] theorem bind_ticks {α β : Type} (m : Cost α) (f : α → Cost β) :
    (m >>= f).ticks = m.ticks + (f m.val).ticks := rfl
@[simp] theorem tick_val (n : Nat) : (tick n).val = () := rfl
@[simp] theorem tick_ticks (n : Nat) : (tick n).ticks = n := rfl
@[simp] theorem pure_peak {α : Type} (a : α) : (pure a : Cost α).peak = 0 := rfl
@[simp] theorem pure_held {α : Type} (a : α) : (pure a : Cost α).held = 0 := rfl
@[simp] theorem bind_peak {α β : Type} (m : Cost α) (f : α → Cost β) :
    (m >>= f).peak = max m.peak (m.held + (f m.val).peak) := rfl
@[simp] theorem bind_held {α β : Type} (m : Cost α) (f : α → Cost β) :
    (m >>= f).held = m.held + (f m.val).held := rfl
@[simp] theorem tick_peak (n : Nat) : (tick n).peak = 0 := rfl
@[simp] theorem tick_held (n : Nat) : (tick n).held = 0 := rfl
@[simp] theorem metered_val {α : Type} (m : Cost α) : (metered m).val = (m.val, m.ticks) := rfl
@[simp] theorem metered_ticks {α : Type} (m : Cost α) : (metered m).ticks = m.ticks := rfl
@[simp] theorem metered_peak {α : Type} (m : Cost α) : (metered m).peak = m.peak := rfl
@[simp] theorem metered_held {α : Type} (m : Cost α) : (metered m).held = m.held := rfl

/-- Run `m` with a budget of `b` ticks. If `m` needs no more than `b` it
runs and is charged as usual; otherwise `b` ticks are spent and there is no
result. A computation that is given up on is rolled back: it leaves nothing
live, and while it ran it had at most its own peak live, and at most one cell
for each tick it was allowed. -/
def within {α : Type} (b : Nat) (m : Cost α) : Cost (Option α) :=
  if m.ticks ≤ b then ⟨some m.val, m.ticks, m.peak, m.held⟩ else ⟨none, b, min b m.peak, 0⟩

/-! ### Free list traversals

These spend only what the function they are given spends. They are defined by
plain recursion so that forgetting the ticks gives the list function of the
same name. -/

def mapL {α β : Type} (f : α → Cost β) : List α → Cost (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapL f xs
    pure (y :: ys)

def flatMapL {α β : Type} (f : α → Cost (List β)) : List α → Cost (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← flatMapL f xs
    pure (y ++ ys)

def filterL {α : Type} (f : α → Cost Bool) : List α → Cost (List α)
  | [] => pure []
  | x :: xs => do
    let b ← f x
    let ys ← filterL f xs
    pure (if b then x :: ys else ys)

def filterMapL {α β : Type} (f : α → Cost (Option β)) : List α → Cost (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← filterMapL f xs
    pure (match y with
      | some b => b :: ys
      | none => ys)

/-- Stops at the first member that satisfies `f`, as `List.any` does. -/
def anyL {α : Type} (f : α → Cost Bool) : List α → Cost Bool
  | [] => pure false
  | x :: xs => do
    let b ← f x
    if b then pure true else anyL f xs

/-- Stops at the first member that fails `f`, as `List.all` does. -/
def allL {α : Type} (f : α → Cost Bool) : List α → Cost Bool
  | [] => pure true
  | x :: xs => do
    let b ← f x
    if b then allL f xs else pure false

def foldL {α β : Type} (f : β → α → Cost β) : β → List α → Cost β
  | b, [] => pure b
  | b, x :: xs => do
    let b' ← f b x
    foldL f b' xs

/-- Stops at the first member that satisfies `f`, as `List.find?` does. -/
def findL {α : Type} (f : α → Cost Bool) : List α → Cost (Option α)
  | [] => pure none
  | x :: xs => do
    let b ← f x
    if b then pure (some x) else findL f xs

/-! ## Running two computations side by side

`race x y` runs `x` and `y` under budgets that double until one of them
finishes, and returns that one's result. It spends between once and 7 times
what the cheaper of the two needs (`Rungs/Framework/Race.lean`). -/

/-- `within`, keeping the fact that a computation that was given up on needed
more than the budget. The value and the ticks are those of `within`. -/
def withinP {α : Type} (b : Nat) (m : Cost α) :
    Cost { o : Option α // o = none → b < m.ticks } :=
  ⟨⟨(within b m).val, by
    unfold within
    split
    · intro h; cases h
    · intro _; omega⟩, (within b m).ticks, (within b m).peak, (within b m).held⟩

/-- Run `x` and `y` under the budget `b`, then `2 b + 1`, and so on, until one
of them finishes. -/
def raceFrom {α : Type} (x y : Cost α) (b : Nat) : Cost α := do
  let r ← withinP b x
  match r with
  | ⟨some v, _⟩ => pure v
  | ⟨none, h⟩ => do
    have _ : b < x.ticks := h rfl
    let r' ← within b y
    match r' with
    | some v => pure v
    | none => raceFrom x y (2 * b + 1)
termination_by x.ticks - b
decreasing_by omega

/-- Run `x` and `y` side by side until one of them finishes. -/
def race {α : Type} (x y : Cost α) : Cost α := raceFrom x y 0

end Cost

end RwLog
