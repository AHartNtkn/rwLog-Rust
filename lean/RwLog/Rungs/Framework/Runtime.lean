/-
# Runs of any runtime

Facts about `Runtime.run`, `emitted`, `Halts`, `trace` and `Answers` that hold
for every runtime, so no rung proves them again.

* A run only appends: what is emitted within `m` steps is a prefix of what is
  emitted within `m + j` (`run_prefix`, `emitted_subset`), and nothing is
  emitted after the run reports that it is done (`emitted_of_halts`).
* `stateAfter s n` is the state after `n` steps, a finished state staying
  put. A run halts exactly when some `stateAfter` state steps to `done`
  (`halts_iff_stateAfter`).
* The answers of a halting run are the answers emitted when it halts
  (`answers_eq_of_halts`), so a halting run has finitely many answers
  (`finite_answers`): P3.3 holds for every runtime.
* `emitted` is the concatenation of the `trace` (`emitted_eq_flatten_trace`).
-/
import RwLog.Trusted.Engine
import Mathlib.Data.Set.Finite.Basic

namespace RwLog

namespace Runtime

variable (R : Runtime)

/-! ## Running -/

theorem run_zero (s : R.State) : R.run s 0 = ([], false) := rfl

theorem run_succ_emit {s s' : R.State} {as : List Span} (h : R.step s = .emit as s') (n : Nat) :
    R.run s (n + 1) = (as ++ (R.run s' n).1, (R.run s' n).2) := by
  simp only [run, h]

theorem run_succ_done {s : R.State} (h : R.step s = .done) (n : Nat) :
    R.run s (n + 1) = ([], true) := by
  simp only [run, h]

/-- Emitting only appends. -/
theorem run_prefix : ∀ (m j : Nat) (s : R.State), ∃ r, (R.run s (m + j)).1 = (R.run s m).1 ++ r
  | 0, j, s => ⟨(R.run s j).1, by simp [run]⟩
  | m + 1, j, s => by
    rw [show m + 1 + j = (m + j) + 1 by omega]
    simp only [run]
    split
    · rename_i as s' _
      obtain ⟨r, hr⟩ := run_prefix m j s'
      exact ⟨r, by rw [hr, List.append_assoc]⟩
    · exact ⟨[], by simp⟩

theorem emitted_prefix (s : R.State) {m n : Nat} (h : m ≤ n) : R.emitted s m <+: R.emitted s n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨r, hr⟩ := R.run_prefix m j s
  exact ⟨r, hr.symm⟩

theorem emitted_subset (s : R.State) {m n : Nat} (h : m ≤ n) {a : Span} (ha : a ∈ R.emitted s m) :
    a ∈ R.emitted s n :=
  (R.emitted_prefix s h).subset ha

theorem Halts.mono {s : R.State} {m n : Nat} (hm : R.Halts s m) (h : m ≤ n) : R.Halts s n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold Halts at hm ⊢
  rw [R.run_halted hm j]; exact hm

/-- Nothing is emitted after the run reports that it is done. -/
theorem emitted_of_halts {s : R.State} {n : Nat} (hn : R.Halts s n) (m : Nat) {a : Span}
    (ha : a ∈ R.emitted s m) : a ∈ R.emitted s n := by
  rcases le_total m n with h | h
  · exact R.emitted_subset s h ha
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    unfold emitted at ha ⊢
    rwa [R.run_halted hn j] at ha

/-! ## Answers -/

theorem mem_answers {P : Program} {q : Rel} {a : Span} :
    a ∈ R.Answers P q ↔ ∃ n, a ∈ R.emitted (R.init P q) n := Iff.rfl

/-- The answers of a halting run are those emitted when it halts. -/
theorem answers_eq_of_halts {P : Program} {q : Rel} {n : Nat} (hn : R.Halts (R.init P q) n) :
    R.Answers P q = {a | a ∈ R.emitted (R.init P q) n} :=
  Set.ext fun _ => ⟨fun ⟨m, ha⟩ => R.emitted_of_halts hn m ha, fun ha => ⟨n, ha⟩⟩

/-- P3.3, for every runtime: a halting run has finitely many answers. -/
theorem finite_answers {P : Program} {q : Rel} (h : R.Terminates P q) : (R.Answers P q).Finite := by
  obtain ⟨n, hn⟩ := h
  rw [R.answers_eq_of_halts hn]
  exact List.finite_toSet _

/-! ## The state after `n` steps -/

/-- The state after `n` steps (a finished state stays put). -/
def stateAfter (s : R.State) : Nat → R.State
  | 0 => s
  | n + 1 =>
    match R.step s with
    | .emit _ s' => stateAfter s' n
    | .done => s

theorem stateAfter_done {s : R.State} (h : R.step s = .done) : ∀ k, R.stateAfter s k = s
  | 0 => rfl
  | k + 1 => by simp only [stateAfter, h]

theorem stateAfter_succ_emit {s s' : R.State} {as : List Span} (h : R.step s = .emit as s')
    (k : Nat) : R.stateAfter s (k + 1) = R.stateAfter s' k := by
  simp only [stateAfter, h]

theorem stateAfter_add (s : R.State) :
    ∀ m k, R.stateAfter s (m + k) = R.stateAfter (R.stateAfter s m) k
  | 0, k => by simp [stateAfter]
  | m + 1, k => by
    cases h : R.step s with
    | done => rw [R.stateAfter_done h, R.stateAfter_done h, R.stateAfter_done h]
    | emit as s' =>
      rw [show m + 1 + k = (m + k) + 1 by omega, R.stateAfter_succ_emit h,
        R.stateAfter_succ_emit h, stateAfter_add s' m k]

/-- A run of `n + 1` steps reports that it is done exactly when one of the
first `n + 1` states steps to `done`. -/
theorem halts_succ_iff : ∀ (n : Nat) (s : R.State),
    R.Halts s (n + 1) ↔ ∃ k ≤ n, R.step (R.stateAfter s k) = .done
  | 0, s => by
    unfold Halts
    cases h : R.step s with
    | done => rw [R.run_succ_done h]; exact ⟨fun _ => ⟨0, le_rfl, h⟩, fun _ => rfl⟩
    | emit as s' =>
      rw [R.run_succ_emit h]
      constructor
      · intro h'; cases h'
      · rintro ⟨k, hk, h'⟩
        rw [Nat.le_zero.1 hk] at h'
        simp only [stateAfter] at h'
        rw [h] at h'; cases h'
  | n + 1, s => by
    unfold Halts
    cases h : R.step s with
    | done => rw [R.run_succ_done h]; exact ⟨fun _ => ⟨0, Nat.zero_le _, h⟩, fun _ => rfl⟩
    | emit as s' =>
      rw [R.run_succ_emit h]
      have ih := halts_succ_iff n s'
      unfold Halts at ih
      rw [ih]
      constructor
      · rintro ⟨k, hk, h'⟩
        exact ⟨k + 1, by omega, by rw [R.stateAfter_succ_emit h]; exact h'⟩
      · rintro ⟨k, hk, h'⟩
        cases k with
        | zero => simp only [stateAfter] at h'; rw [h] at h'; cases h'
        | succ k =>
          rw [R.stateAfter_succ_emit h] at h'
          exact ⟨k, by omega, h'⟩

/-- A run halts exactly when it reaches a state that steps to `done`. -/
theorem halts_iff_stateAfter (s : R.State) :
    (∃ n, R.Halts s n) ↔ ∃ k, R.step (R.stateAfter s k) = .done := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [Halts, run] at h
    | succ n => obtain ⟨k, -, hk⟩ := (R.halts_succ_iff n s).1 h; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, (R.halts_succ_iff k s).2 ⟨k, le_rfl, hk⟩⟩

/-! ## Traces -/

theorem trace_succ_emit {s s' : R.State} {as : List Span} (h : R.step s = .emit as s') (n : Nat) :
    R.trace s (n + 1) = as :: R.trace s' n := by
  simp only [trace, h]

theorem trace_succ_done {s : R.State} (h : R.step s = .done) (n : Nat) : R.trace s (n + 1) = [] := by
  simp only [trace, h]

/-- What a run emitted is its trace, concatenated. -/
theorem emitted_eq_flatten_trace : ∀ (n : Nat) (s : R.State), R.emitted s n = (R.trace s n).flatten
  | 0, _ => rfl
  | n + 1, s => by
    unfold emitted
    cases h : R.step s with
    | done => rw [R.run_succ_done h, R.trace_succ_done h]; rfl
    | emit as s' =>
      rw [R.run_succ_emit h, R.trace_succ_emit h, List.flatten_cons]
      exact congrArg (as ++ ·) (emitted_eq_flatten_trace n s')

/-- A run of `n` steps has reported that it is done exactly when its trace
stopped early. -/
theorem halts_iff_trace_length : ∀ (n : Nat) (s : R.State), R.Halts s n ↔ (R.trace s n).length < n
  | 0, _ => by simp [Halts, run, trace]
  | n + 1, s => by
    unfold Halts
    cases h : R.step s with
    | done => rw [R.run_succ_done h, R.trace_succ_done h]; simp
    | emit as s' =>
      rw [R.run_succ_emit h, R.trace_succ_emit h]
      have ih := halts_iff_trace_length n s'
      unfold Halts at ih
      simp only [List.length_cons, Nat.add_lt_add_iff_right]
      exact ih

end Runtime

end RwLog
