/-
# What the table operations of the tabled machine return

The tabled machine (`Rungs/Tabled/Machine.lean`) at the derivation kernel of
a program over a kernel that returns what a domain returns: the value of each
operation on goals and tables.
-/
import RwLog.Rungs.Tabled.Machine
import RwLog.Rungs.Framework.GoalsVal
import RwLog.Kernel.NormalFormDepth

namespace RwLog

namespace Tabled

open Traverse

export Goals (sameBound_val same_val indexFrom_val covB coversA_val maxima_val fresh_val
  covB_iff covB_refl covB_trans)

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D)

/-! ## Tables -/

/-- The table of a goal: the first one with that goal. -/
def lookup (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    Option (TableOf R Rel (Ans D P)) :=
  ts.find? fun t => decide (t.goal = g)

theorem findTable_val (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (findTable (K := DerivationKernel.over D K hK P) ts g).val = lookup ts g := by
  have hs := fun t : TableOf R Rel (Ans D P) => same_val (P := P) K hK t.goal g
  at_cost K hK
  simp only [findTable, findL_std, Cost.findL_val, hs, lookup]

theorem indexOf_val (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (indexOf (K := DerivationKernel.over D K hK P) ts g).val =
      ts.findIdx? fun t => decide (t.goal = g) := by
  unfold indexOf; rw [indexFrom_val]; simp

theorem answersOf_val (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (answersOf (K := DerivationKernel.over D K hK P) ts g).val =
      match lookup ts g with
      | some t => t.answers
      | none => [] := by
  have hf := findTable_val (P := P) K hK ts g
  at_cost K hK
  simp only [answersOf, Cost.bind_val, hf, Cost.pure_val]
  cases lookup ts g <;> rfl

theorem doneOf_val (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) :
    (doneOf (K := DerivationKernel.over D K hK P) ts g).val =
      match lookup ts g with
      | some t => t.done
      | none => false := by
  have hf := findTable_val (P := P) K hK ts g
  at_cost K hK
  simp only [doneOf, Cost.bind_val, hf, Cost.pure_val]
  cases lookup ts g <;> rfl

end Tabled

end RwLog
