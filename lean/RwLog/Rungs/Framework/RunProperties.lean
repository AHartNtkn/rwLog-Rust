/-
# Properties of a run that are no law

The laws are `Runtime.Laws` (`Trusted/Properties.lean`): soundness,
completeness pair by pair, and an honest report of being done. This file has
what proofs use beside them. None of it is asked of a rung.

* `StepEquiv`, `ShownEquiv`, `TraceEquiv`: what two runs show agrees up to
  the order of the answers of one step and up to equivalent answers. It is
  how two machines are proved to cost the same
  (`Rungs/Framework/Direction.lean`).
* `FinalMaximal`: when a run reports that it is done, its final report is the
  set of maximal emitted answers. This is the filter on the final set of
  answers that leaves out an answer another answer covers.
-/
import RwLog.Trusted.Properties

namespace RwLog

/-! ## Traces up to order and equivalence -/

section
variable {A B : Type} [Answer A] [Answer B]

/-- Two answer lists of one step agree up to order and answers equivalent in
`M`. The two lists may hold answers of two different types. -/
def StepEquiv (M : Interp) (xs : List A) (ys : List B) : Prop :=
  ∃ ys', ys'.Perm ys ∧ List.Forall₂ (Answer.Equiv M) xs ys'

/-- What two steps show agrees: answers and final reports up to
`StepEquiv`. -/
def ShownEquiv (M : Interp) : Shown A → Shown B → Prop
  | .answers xs, .answers ys => StepEquiv M xs ys
  | .final xs, .final ys => StepEquiv M xs ys
  | _, _ => False

/-- Two traces agree step for step, up to `ShownEquiv`. -/
def TraceEquiv (M : Interp) (t : List (Shown A)) (t' : List (Shown B)) : Prop :=
  List.Forall₂ (ShownEquiv M) t t'

end

namespace Runtime

variable (R : Runtime)

/-- When a run reports that it is done, its final report is the set of
maximal emitted answers: every reported answer was emitted, every emitted
answer is covered by a reported one, and no reported answer covers another.
So the report is irredundant, and it holds one answer for each class of
equivalent maximal answers. -/
def FinalMaximal : Prop :=
  ∀ P q, P.WellFormed q → ∀ n fin, R.final (R.init P q) n = some fin →
    (∀ a ∈ fin, a ∈ R.emitted (R.init P q) n) ∧
    (∀ a ∈ R.emitted (R.init P q) n, ∃ b ∈ fin, Answer.Covers P.sorts.interp b a) ∧
    fin.Pairwise fun a b => ¬ Answer.Covers P.sorts.interp a b ∧ ¬ Answer.Covers P.sorts.interp b a

end Runtime

end RwLog
