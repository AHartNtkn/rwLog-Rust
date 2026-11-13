/-
# Reaching a state

`R.Reach s es n s'`: the runtime gets from `s` to `s'` in `n` steps, none of
which reports that it is done, emitting `es`. A run of any length is such a
path, followed or not by a step that reports it is done (`run_cases`), which
is how an invariant of the states is carried to what a run emits.
-/
import RwLog.Rungs.Framework.Runtime

namespace RwLog

namespace Runtime

variable (R : Runtime)

/-- From `s`, `n` steps that emit `es` in all lead to `s'`. -/
inductive Reach (s : R.State) : List Span → Nat → R.State → Prop
  | refl : Reach s [] 0 s
  | step {es : List Span} {n : Nat} {s' s'' : R.State} {as : List Span} :
    Reach s es n s' → R.step s' = .emit as s'' → Reach s (es ++ as) (n + 1) s''

variable {R}

/-- A path that starts with a step. -/
theorem Reach.head {s s' s'' : R.State} {as es : List Span} {n : Nat}
    (h : R.step s = .emit as s') (r : R.Reach s' es n s'') : R.Reach s (as ++ es) (n + 1) s'' := by
  induction r with
  | refl => simpa using Reach.step Reach.refl h
  | step _ h' ih => rw [← List.append_assoc]; exact Reach.step ih h'

/-- A run through a path is the path and then the run from where it ends. -/
theorem Reach.run {s s' : R.State} {es : List Span} {n : Nat} (r : R.Reach s es n s') :
    ∀ k, R.run s (n + k) = (es ++ (R.run s' k).1, (R.run s' k).2) := by
  induction r with
  | refl => intro k; simp
  | @step es n s' s'' as _ h ih =>
    intro k
    rw [show n + 1 + k = n + (k + 1) by omega, ih (k + 1), R.run_succ_emit h]
    simp

theorem Reach.emitted {s s' : R.State} {es : List Span} {n : Nat} (r : R.Reach s es n s') :
    R.emitted s n = es := by
  have := r.run 0
  simp only [Nat.add_zero, run_zero, List.append_nil] at this
  unfold Runtime.emitted
  rw [this]

/-- A path that ends at a state that is done is a run that halts, with the
path's answers. -/
theorem Reach.halts {s s' : R.State} {es : List Span} {n : Nat} (r : R.Reach s es n s')
    (h : R.step s' = .done) : R.Halts s (n + 1) ∧ R.emitted s (n + 1) = es := by
  have := r.run 1
  rw [R.run_succ_done h] at this
  unfold Runtime.Halts Runtime.emitted
  rw [this]
  simp

/-- A run of `n` steps is a path of `n` steps, or a shorter path to a state
that is done. -/
theorem run_cases : ∀ (n : Nat) (s : R.State),
    (∃ s', R.Reach s (R.emitted s n) n s' ∧ ¬ R.Halts s n) ∨
      (∃ k s', k < n ∧ R.Reach s (R.emitted s n) k s' ∧ R.step s' = .done ∧ R.Halts s n)
  | 0, s => .inl ⟨s, .refl, by simp [Halts, run_zero]⟩
  | n + 1, s => by
    cases h : R.step s with
    | done =>
      right
      refine ⟨0, s, Nat.succ_pos _, ?_, h, ?_⟩
      · unfold Runtime.emitted; rw [R.run_succ_done h]; exact .refl
      · unfold Halts; rw [R.run_succ_done h]
    | emit as s₁ =>
      have e : R.emitted s (n + 1) = as ++ R.emitted s₁ n := by
        unfold Runtime.emitted; rw [R.run_succ_emit h]
      have eh : R.Halts s (n + 1) ↔ R.Halts s₁ n := by
        unfold Halts; rw [R.run_succ_emit h]
      rcases run_cases n s₁ with ⟨s', r, hn⟩ | ⟨k, s', hk, r, hd, hh⟩
      · exact .inl ⟨s', by rw [e]; exact r.head h, fun hh => hn (eh.1 hh)⟩
      · exact .inr ⟨k + 1, s', by omega, by rw [e]; exact r.head h, hd, eh.2 hh⟩

end Runtime

end RwLog
