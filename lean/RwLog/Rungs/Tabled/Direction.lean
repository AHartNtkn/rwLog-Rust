/-
# The tabled round machine on a converse, and on a regrouped choice

For any unfolding oracle:

* `convBisim`: the run on `conv q` goes through the states of the run on
  `q` with the root's orientation flipped, at the same cost step for step,
  and emits the same answers swapped.
* `start_or_comm`, `start_or_assoc`: swapping or regrouping the branches of
  `|` gives the same first state.
* `init_ticks`: the first state costs the size of the query.
* `step_pos`: a step that emits costs at least a tick.

These are what the mirrored machine (`Rungs/Mirror`) asks of the machine it
mirrors.
-/
import RwLog.Rungs.Tabled.Exact
import RwLog.Rungs.Tabled.Base.Proofs.Symmetry
import RwLog.Rungs.Framework.Direction

namespace RwLog

namespace Tabled

open R001 Cost

variable (U : Oracle)

theorem round_flip (st : State) :
    round U st.flip =
      ⟨(((round U st).val.1).flip, (round U st).val.2.map Span.swap), (round U st).ticks⟩ := by
  refine Cost.ext ?_ rfl
  simp only [round, StateOf.flip, bind_val, pure_val, R001.orient_not]

theorem step_flip_ticks (st : State) : (step U st.flip).ticks = (step U st).ticks := by
  unfold step
  by_cases h : st.finished = true
  · have h' : st.flip.finished = true := h
    simp only [h, h', ite_true]
  · have h' : ¬ st.flip.finished = true := h
    simp only [h, h', Bool.false_eq_true, ↓reduceIte, bind_ticks, pure_ticks, round_flip]

theorem step_flip_val (st : State) :
    Step.Rel (fun xs ys => xs = ys.map Span.swap) (fun s s' => s = s'.flip)
      (step U st.flip).val (step U st).val := by
  unfold step
  by_cases h : st.finished = true
  · have h' : st.flip.finished = true := h
    simp only [h, h', ite_true]
    exact trivial
  · have h' : ¬ st.flip.finished = true := h
    simp only [h, h', Bool.false_eq_true, ↓reduceIte, bind_val, pure_val, round_flip]
    exact ⟨rfl, rfl⟩

theorem start_conv (P : Program) (q : Rel) :
    (machine U).start P (.conv q) = StateOf.flip ((machine U).start P q) := by
  show (ofGoal P ⟨none, .conv q, none⟩).val = StateOf.flip (ofGoal P ⟨none, q, none⟩).val
  simp only [ofGoal, norm, bind_val, pure_val, GoalOf.norm, canon]
  rw [GoalOf.stripConv]
  rfl

/-- The run on `conv q` is the run on `q` with the root's orientation
flipped: the same cost, step for step, and the same answers swapped. -/
theorem convBisim : ConvBisim (machine U) fun s s' => s = s'.flip where
  ticks s s' h := by subst h; exact step_flip_ticks U s'
  step s s' h := by subst h; exact step_flip_val U s'
  start := start_conv U

theorem start_or_comm (P : Program) (a b : Rel) :
    (machine U).start P (.or a b) = (machine U).start P (.or b a) := by
  show (ofGoal P ⟨none, .or a b, none⟩).val = (ofGoal P ⟨none, .or b a, none⟩).val
  simp only [ofGoal, norm, bind_val, pure_val, GoalOf.norm, Symmetry.canon_or_comm a b]

theorem start_or_assoc (P : Program) (a b c : Rel) :
    (machine U).start P (.or (.or a b) c) = (machine U).start P (.or a (.or b c)) := by
  show (ofGoal P ⟨none, .or (.or a b) c, none⟩).val = (ofGoal P ⟨none, .or a (.or b c), none⟩).val
  simp only [ofGoal, norm, bind_val, pure_val, GoalOf.norm, Symmetry.canon_or_assoc a b c]

/-- The first state costs the size of the query. -/
theorem init_ticks (P : Program) (q : Rel) : ((machine U).init P q).ticks = q.size := by
  show goalSize ⟨none, q, none⟩ + 0 = _
  simp [goalSize]

/-- A step that emits costs at least a tick. -/
theorem step_pos (s : State) (as : List Span) (s' : State)
    (h : ((machine U).step s).val = .emit as s') : 1 ≤ ((machine U).step s).ticks := by
  show 1 ≤ (step U s).ticks
  have h : (step U s).val = .emit as s' := h
  unfold step at h ⊢
  by_cases hf : s.finished = true
  · simp only [hf, ite_true, pure_val] at h
    cases h
  · simp only [hf, Bool.false_eq_true, ↓reduceIte, bind_ticks, pure_ticks, round, tick_ticks]
    omega

end Tabled

end RwLog
