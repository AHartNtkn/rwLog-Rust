/-
# Charged computations

`Cost α` is a value together with the number of ticks spent computing it.
This file has the monad, the budget (`Cost.within`) and the free list
traversals. The charged primitives, and what the ticks are used for, are in
`Trusted/Cost.lean`. It comes first because a preprocessor is a charged
computation too (`Trusted/Engine.lean`).
-/
import Mathlib.Data.List.Basic

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

end Cost

end RwLog
