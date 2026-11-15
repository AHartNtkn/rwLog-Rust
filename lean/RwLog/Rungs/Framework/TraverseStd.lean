/-
# The traversals at `Cost`, and the kernel of the language unfolded

At the cost monad the traversals of `Traverse.lean` are those of
`Trusted/CostMonad.lean`, and each operation of the language's kernel is the
charged primitive it was defined as. These are the rewriting rules that read
an engine written against the kernel as a machine in `Cost`.
-/
import RwLog.Rungs.Framework.Traverse
import RwLog.Trusted.Cost
import RwLog.Rungs.Framework.Cost

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

/-- A fold keeps what each of its steps keeps. -/
theorem foldL_inv (I : β → Prop) (f : β → α → Cost β) (xs : List α)
    (h : ∀ b x, x ∈ xs → I b → I (f b x).val) (b : β) (hb : I b) :
    I (Traverse.foldL f b xs).val := by
  rw [foldL_std]
  exact Cost.foldL_inv I f xs h b hb

/-- A fold keeps what each of its steps keeps, where what is kept may speak
of the members passed. -/
theorem foldL_done (I : List α → β → Prop) (f : β → α → Cost β) (xs : List α)
    (h : ∀ done b x, x ∈ xs → I done b → I (done ++ [x]) (f b x).val) (b : β) (hb : I [] b) :
    I xs (Traverse.foldL f b xs).val := by
  have main : ∀ (ys done : List α) (b : β), (∀ y ∈ ys, y ∈ xs) → I done b →
      I (done ++ ys) (Cost.foldL f b ys).val := by
    intro ys
    induction ys with
    | nil =>
      intro done b _ hb
      rw [List.append_nil]
      exact hb
    | cons y ys ih =>
      intro done b hys hb
      have := ih (done ++ [y]) (f b y).val (fun z hz => hys z (List.mem_cons_of_mem _ hz))
        (h done b y (hys y List.mem_cons_self) hb)
      rw [List.append_assoc, List.singleton_append] at this
      simp only [Cost.foldL, Cost.bind_val]
      exact this
  rw [foldL_std]
  exact main xs [] b (fun _ h => h) hb

/-- A fold keeps what each of its steps keeps, where what is kept may speak
of the members passed and a step knows which members are still to come. -/
theorem foldL_split (I : List α → β → Prop) (f : β → α → Cost β) (xs : List α)
    (h : ∀ done rest b x, xs = done ++ x :: rest → I done b → I (done ++ [x]) (f b x).val)
    (b : β) (hb : I [] b) : I xs (Traverse.foldL f b xs).val := by
  have main : ∀ (ys done : List α) (b : β), xs = done ++ ys → I done b →
      I (done ++ ys) (Cost.foldL f b ys).val := by
    intro ys
    induction ys with
    | nil =>
      intro done b _ hb
      rw [List.append_nil]
      exact hb
    | cons y ys ih =>
      intro done b hys hb
      have := ih (done ++ [y]) (f b y).val (by rw [hys, List.append_assoc, List.singleton_append])
        (h done ys b y hys hb)
      rw [List.append_assoc, List.singleton_append] at this
      simp only [Cost.foldL, Cost.bind_val]
      exact this
  rw [foldL_std]
  exact main xs [] b rfl hb

end Traverse

end RwLog
