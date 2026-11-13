/-
# Charged computations

`Cost α` is a value together with the number of ticks spent computing it.
This file has the monad, the budget (`Cost.within`) and the free list
traversals. The charged primitives, and what the ticks are used for, are in
`Trusted/Cost.lean`. It comes first because a preprocessor is a charged
computation too (`Trusted/Engine.lean`).
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Common

namespace RwLog

/-! ## Charged computations -/

/-- A value and the ticks spent computing it. -/
structure Cost (α : Type) where
  val : α
  ticks : Nat

namespace Cost

instance : Monad Cost where
  pure a := ⟨a, 0⟩
  bind m f := let r := f m.val; ⟨r.val, m.ticks + r.ticks⟩

/-- Spend `n` ticks. -/
def tick (n : Nat) : Cost Unit := ⟨(), n⟩

@[simp] theorem pure_val {α : Type} (a : α) : (pure a : Cost α).val = a := rfl
@[simp] theorem pure_ticks {α : Type} (a : α) : (pure a : Cost α).ticks = 0 := rfl
@[simp] theorem bind_val {α β : Type} (m : Cost α) (f : α → Cost β) :
    (m >>= f).val = (f m.val).val := rfl
@[simp] theorem bind_ticks {α β : Type} (m : Cost α) (f : α → Cost β) :
    (m >>= f).ticks = m.ticks + (f m.val).ticks := rfl
@[simp] theorem tick_val (n : Nat) : (tick n).val = () := rfl
@[simp] theorem tick_ticks (n : Nat) : (tick n).ticks = n := rfl

/-- Run `m` with a budget of `b` ticks. If `m` needs no more than `b` it
runs and is charged as usual; otherwise `b` ticks are spent and there is no
result. -/
def within {α : Type} (b : Nat) (m : Cost α) : Cost (Option α) :=
  if m.ticks ≤ b then ⟨some m.val, m.ticks⟩ else ⟨none, b⟩

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
    · intro _; omega⟩, (within b m).ticks⟩

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
