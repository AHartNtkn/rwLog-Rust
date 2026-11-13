/-
# List traversals in any monad

The traversals of `Trusted/CostMonad.lean`, for an arbitrary monad, so that an
engine written against the kernel can use them. They are defined by the same
plain recursion, and at `Cost` they are the traversals of that file
(`Rungs/Framework/TraverseStd.lean`).
-/
import Mathlib.Data.List.Basic

namespace RwLog

namespace Traverse

variable {M : Type → Type} [Monad M] {α β : Type}

def mapL (f : α → M β) : List α → M (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapL f xs
    pure (y :: ys)

def flatMapL (f : α → M (List β)) : List α → M (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← flatMapL f xs
    pure (y ++ ys)

def filterL (f : α → M Bool) : List α → M (List α)
  | [] => pure []
  | x :: xs => do
    let b ← f x
    let ys ← filterL f xs
    pure (if b then x :: ys else ys)

def filterMapL (f : α → M (Option β)) : List α → M (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← filterMapL f xs
    pure (match y with
      | some b => b :: ys
      | none => ys)

/-- Stops at the first member that satisfies `f`. -/
def anyL (f : α → M Bool) : List α → M Bool
  | [] => pure false
  | x :: xs => do
    let b ← f x
    if b then pure true else anyL f xs

/-- Stops at the first member that fails `f`. -/
def allL (f : α → M Bool) : List α → M Bool
  | [] => pure true
  | x :: xs => do
    let b ← f x
    if b then allL f xs else pure false

def foldL (f : β → α → M β) : β → List α → M β
  | b, [] => pure b
  | b, x :: xs => do
    let b' ← f b x
    foldL f b' xs

/-- Stops at the first member that satisfies `f`. -/
def findL (f : α → M Bool) : List α → M (Option α)
  | [] => pure none
  | x :: xs => do
    let b ← f x
    if b then pure (some x) else findL f xs

end Traverse

end RwLog
