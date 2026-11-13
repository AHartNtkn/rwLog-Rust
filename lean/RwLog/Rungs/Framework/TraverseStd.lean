/-
# The traversals at `Cost`, and the kernel of the language unfolded

At the cost monad the traversals of `Traverse.lean` are those of
`Trusted/CostMonad.lean`, and each operation of the language's kernel is the
charged primitive it was defined as. These are the rewriting rules that read
an engine written against the kernel as a machine in `Cost`.
-/
import RwLog.Rungs.Framework.Traverse
import RwLog.Trusted.Cost

open Lean Elab Tactic Meta in
/-- Unfold every `match` of the goal to the case analysis it stands for. Two
definitions with the same text have matchers of different names, which are
equal only once unfolded. -/
elab "unfold_matches" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let env ← getEnv
  let t' ← Meta.deltaExpand t fun n => (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
  replaceMainGoal [← g.replaceTargetDefEq t']

/-- Closes an equation between two readings of one text. -/
macro "same_text" : tactic => `(tactic| first | rfl | (unfold_matches; rfl))

namespace RwLog

namespace Traverse

variable {α β : Type}

theorem mapL_std (f : α → Cost β) : ∀ xs : List α, Traverse.mapL f xs = Cost.mapL f xs
  | [] => rfl
  | x :: xs => by simp only [Traverse.mapL, Cost.mapL, mapL_std f xs]

theorem flatMapL_std (f : α → Cost (List β)) :
    ∀ xs : List α, Traverse.flatMapL f xs = Cost.flatMapL f xs
  | [] => rfl
  | x :: xs => by simp only [Traverse.flatMapL, Cost.flatMapL, flatMapL_std f xs]

theorem filterL_std (f : α → Cost Bool) : ∀ xs : List α, Traverse.filterL f xs = Cost.filterL f xs
  | [] => rfl
  | x :: xs => by simp only [Traverse.filterL, Cost.filterL, filterL_std f xs]

theorem filterMapL_std (f : α → Cost (Option β)) :
    ∀ xs : List α, Traverse.filterMapL f xs = Cost.filterMapL f xs
  | [] => rfl
  | x :: xs => by simp only [Traverse.filterMapL, Cost.filterMapL, filterMapL_std f xs]; rfl

theorem anyL_std (f : α → Cost Bool) : ∀ xs : List α, Traverse.anyL f xs = Cost.anyL f xs
  | [] => rfl
  | x :: xs => by simp only [Traverse.anyL, Cost.anyL, anyL_std f xs]

theorem allL_std (f : α → Cost Bool) : ∀ xs : List α, Traverse.allL f xs = Cost.allL f xs
  | [] => rfl
  | x :: xs => by simp only [Traverse.allL, Cost.allL, allL_std f xs]

theorem foldL_std (f : β → α → Cost β) :
    ∀ (xs : List α) (b : β), Traverse.foldL f b xs = Cost.foldL f b xs
  | [], _ => rfl
  | x :: xs, b => by simp only [Traverse.foldL, Cost.foldL, foldL_std f xs]

theorem findL_std (f : α → Cost Bool) : ∀ xs : List α, Traverse.findL f xs = Cost.findL f xs
  | [] => rfl
  | x :: xs => by simp only [Traverse.findL, Cost.findL, findL_std f xs]

end Traverse

end RwLog
