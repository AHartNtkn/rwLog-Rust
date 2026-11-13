/-
# Runs of any runtime

Facts about `Runtime.run`, `emitted`, `final`, `Halts`, `trace` and `Answers`
that hold for every runtime and every type of answers, so no rung proves them
again.

* A run only appends: what is emitted within `m` steps is a prefix of what is
  emitted within `m + j` (`run_prefix`, `emitted_subset`), and nothing is
  emitted after the run reports that it is done (`emitted_of_halts`). The
  final report does not change either (`final_of_halts`).
* `stateAfter s n` is the state after `n` steps, a finished state staying
  put. A run halts exactly when some `stateAfter` state steps to `done`
  (`halts_iff_stateAfter`).
* The answers of a halting run are the answers emitted when it halts
  (`answers_eq_of_halts`).
* `emitted` is the answers of the `trace`, concatenated
  (`emitted_eq_flatMap_trace`), and a run has halted exactly when its trace
  stopped early (`halts_iff_trace_length`).
* A certificate is the step a state takes (`certifies_iff`).
-/
import RwLog.Trusted.Engine
import Mathlib.Data.Set.Finite.Basic

namespace RwLog

/-- The answers a step shows as emitted: those of an emitting step, and none
for a certificate or a final report. -/
def Shown.emits {A : Type} : Shown A → List A
  | .answers as => as
  | .level _ => []
  | .final _ => []

namespace Runtime

variable (R : Runtime)

/-! ## Running -/

theorem run_zero (s : R.State) : R.run s 0 = ([], none) := rfl

theorem run_succ_emit {s s' : R.State} {as : List R.Ans} (h : R.step s = .emit as s') (n : Nat) :
    R.run s (n + 1) = (as ++ (R.run s' n).1, (R.run s' n).2) := by
  simp only [run, h]

theorem run_succ_progress {s s' : R.State} {k : Nat} (h : R.step s = .progress k s') (n : Nat) :
    R.run s (n + 1) = R.run s' n := by
  simp only [run, h]

theorem run_succ_done {s : R.State} {fin : List R.Ans} (h : R.step s = .done fin) (n : Nat) :
    R.run s (n + 1) = ([], some fin) := by
  simp only [run, h]

theorem halts_zero (s : R.State) : ¬ R.Halts s 0 := by simp [Halts, final, run]

theorem halts_succ_emit {s s' : R.State} {as : List R.Ans} (h : R.step s = .emit as s') (n : Nat) :
    R.Halts s (n + 1) ↔ R.Halts s' n := by
  simp only [Halts, final, R.run_succ_emit h]

theorem halts_succ_progress {s s' : R.State} {k : Nat} (h : R.step s = .progress k s') (n : Nat) :
    R.Halts s (n + 1) ↔ R.Halts s' n := by
  simp only [Halts, final, R.run_succ_progress h]

theorem halts_succ_done {s : R.State} {fin : List R.Ans} (h : R.step s = .done fin) (n : Nat) :
    R.Halts s (n + 1) := by
  simp only [Halts, final, R.run_succ_done h, Option.isSome_some]

/-- After the run has reported that it is done, running longer changes
nothing. -/
theorem run_halted : ∀ {n : Nat} {s : R.State}, R.Halts s n → ∀ m, R.run s (n + m) = R.run s n
  | 0, s, h, _ => absurd h (R.halts_zero s)
  | n + 1, s, h, m => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    cases hs : R.step s with
    | emit as s' =>
      rw [R.run_succ_emit hs, R.run_succ_emit hs, run_halted ((R.halts_succ_emit hs n).1 h) m]
    | progress k s' =>
      rw [R.run_succ_progress hs, R.run_succ_progress hs,
        run_halted ((R.halts_succ_progress hs n).1 h) m]
    | done fin => rw [R.run_succ_done hs, R.run_succ_done hs]

theorem run_halted_eq {s : R.State} {n m : Nat} (hn : R.Halts s n) (hm : R.Halts s m) :
    R.run s n = R.run s m := by
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact (R.run_halted hn k).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact R.run_halted hm k

/-- Emitting only appends. -/
theorem run_prefix : ∀ (m j : Nat) (s : R.State), ∃ r, (R.run s (m + j)).1 = (R.run s m).1 ++ r
  | 0, j, s => ⟨(R.run s j).1, by simp [run]⟩
  | m + 1, j, s => by
    rw [show m + 1 + j = (m + j) + 1 by omega]
    cases hs : R.step s with
    | emit as s' =>
      obtain ⟨r, hr⟩ := run_prefix m j s'
      exact ⟨r, by rw [R.run_succ_emit hs, R.run_succ_emit hs, hr, List.append_assoc]⟩
    | progress k s' =>
      obtain ⟨r, hr⟩ := run_prefix m j s'
      exact ⟨r, by rw [R.run_succ_progress hs, R.run_succ_progress hs, hr]⟩
    | done fin => exact ⟨[], by rw [R.run_succ_done hs, R.run_succ_done hs]; simp⟩

theorem emitted_prefix (s : R.State) {m n : Nat} (h : m ≤ n) : R.emitted s m <+: R.emitted s n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨r, hr⟩ := R.run_prefix m j s
  exact ⟨r, hr.symm⟩

theorem emitted_subset (s : R.State) {m n : Nat} (h : m ≤ n) {a : R.Ans}
    (ha : a ∈ R.emitted s m) : a ∈ R.emitted s n :=
  (R.emitted_prefix s h).subset ha

theorem Halts.mono {s : R.State} {m n : Nat} (hm : R.Halts s m) (h : m ≤ n) : R.Halts s n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold Halts final at hm ⊢
  rw [R.run_halted hm j]; exact hm

/-- Nothing is emitted after the run reports that it is done. -/
theorem emitted_of_halts {s : R.State} {n : Nat} (hn : R.Halts s n) (m : Nat) {a : R.Ans}
    (ha : a ∈ R.emitted s m) : a ∈ R.emitted s n := by
  rcases le_total m n with h | h
  · exact R.emitted_subset s h ha
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    unfold emitted at ha ⊢
    rwa [R.run_halted hn j] at ha

/-- The final report does not change once it is made. -/
theorem final_of_halts {s : R.State} {n m : Nat} (hn : R.Halts s n) (h : n ≤ m) :
    R.final s m = R.final s n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold final
  rw [R.run_halted hn j]

theorem halts_iff_final {s : R.State} {n : Nat} : R.Halts s n ↔ ∃ fin, R.final s n = some fin :=
  Option.isSome_iff_exists

/-! ## Answers -/

theorem mem_answers {P : Program} {q : Rel} {a : R.Ans} :
    a ∈ R.Answers P q ↔ ∃ n, a ∈ R.emitted (R.init P q) n := Iff.rfl

/-- The answers of a halting run are those emitted when it halts. -/
theorem answers_eq_of_halts {P : Program} {q : Rel} {n : Nat} (hn : R.Halts (R.init P q) n) :
    R.Answers P q = {a | a ∈ R.emitted (R.init P q) n} :=
  Set.ext fun _ => ⟨fun ⟨m, ha⟩ => R.emitted_of_halts hn m ha, fun ha => ⟨n, ha⟩⟩

/-- A halting run has finitely many answers. This holds of every runtime, so
it is a fact and not an obligation. -/
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
    | .progress _ s' => stateAfter s' n
    | .done _ => s

theorem stateAfter_done {s : R.State} {fin : List R.Ans} (h : R.step s = .done fin) :
    ∀ k, R.stateAfter s k = s
  | 0 => rfl
  | k + 1 => by simp only [stateAfter, h]

theorem stateAfter_succ_emit {s s' : R.State} {as : List R.Ans} (h : R.step s = .emit as s')
    (k : Nat) : R.stateAfter s (k + 1) = R.stateAfter s' k := by
  simp only [stateAfter, h]

theorem stateAfter_succ_progress {s s' : R.State} {j : Nat} (h : R.step s = .progress j s')
    (k : Nat) : R.stateAfter s (k + 1) = R.stateAfter s' k := by
  simp only [stateAfter, h]

theorem stateAfter_add (s : R.State) :
    ∀ m k, R.stateAfter s (m + k) = R.stateAfter (R.stateAfter s m) k
  | 0, k => by simp [stateAfter]
  | m + 1, k => by
    cases h : R.step s with
    | done fin => rw [R.stateAfter_done h, R.stateAfter_done h, R.stateAfter_done h]
    | emit as s' =>
      rw [show m + 1 + k = (m + k) + 1 by omega, R.stateAfter_succ_emit h,
        R.stateAfter_succ_emit h, stateAfter_add s' m k]
    | progress j s' =>
      rw [show m + 1 + k = (m + k) + 1 by omega, R.stateAfter_succ_progress h,
        R.stateAfter_succ_progress h, stateAfter_add s' m k]

/-- A run of `n + 1` steps reports that it is done exactly when one of the
first `n + 1` states steps to `done`. -/
theorem halts_succ_iff : ∀ (n : Nat) (s : R.State),
    R.Halts s (n + 1) ↔ ∃ k ≤ n, ∃ fin, R.step (R.stateAfter s k) = .done fin
  | 0, s => by
    cases h : R.step s with
    | done fin =>
      exact ⟨fun _ => ⟨0, le_rfl, fin, h⟩, fun _ => R.halts_succ_done h 0⟩
    | emit as s' =>
      rw [R.halts_succ_emit h]
      constructor
      · intro h'; exact absurd h' (R.halts_zero s')
      · rintro ⟨k, hk, fin, h'⟩
        rw [Nat.le_zero.1 hk] at h'
        simp only [stateAfter] at h'
        rw [h] at h'; cases h'
    | progress j s' =>
      rw [R.halts_succ_progress h]
      constructor
      · intro h'; exact absurd h' (R.halts_zero s')
      · rintro ⟨k, hk, fin, h'⟩
        rw [Nat.le_zero.1 hk] at h'
        simp only [stateAfter] at h'
        rw [h] at h'; cases h'
  | n + 1, s => by
    cases h : R.step s with
    | done fin =>
      exact ⟨fun _ => ⟨0, Nat.zero_le _, fin, h⟩, fun _ => R.halts_succ_done h (n + 1)⟩
    | emit as s' =>
      rw [R.halts_succ_emit h, halts_succ_iff n s']
      constructor
      · rintro ⟨k, hk, fin, h'⟩
        exact ⟨k + 1, by omega, fin, by rw [R.stateAfter_succ_emit h]; exact h'⟩
      · rintro ⟨k, hk, fin, h'⟩
        cases k with
        | zero => simp only [stateAfter] at h'; rw [h] at h'; cases h'
        | succ k =>
          rw [R.stateAfter_succ_emit h] at h'
          exact ⟨k, by omega, fin, h'⟩
    | progress j s' =>
      rw [R.halts_succ_progress h, halts_succ_iff n s']
      constructor
      · rintro ⟨k, hk, fin, h'⟩
        exact ⟨k + 1, by omega, fin, by rw [R.stateAfter_succ_progress h]; exact h'⟩
      · rintro ⟨k, hk, fin, h'⟩
        cases k with
        | zero => simp only [stateAfter] at h'; rw [h] at h'; cases h'
        | succ k =>
          rw [R.stateAfter_succ_progress h] at h'
          exact ⟨k, by omega, fin, h'⟩

/-- A run halts exactly when it reaches a state that steps to `done`. -/
theorem halts_iff_stateAfter (s : R.State) :
    (∃ n, R.Halts s n) ↔ ∃ k fin, R.step (R.stateAfter s k) = .done fin := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => exact absurd h (R.halts_zero s)
    | succ n => obtain ⟨k, -, hk⟩ := (R.halts_succ_iff n s).1 h; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, (R.halts_succ_iff k s).2 ⟨k, le_rfl, hk⟩⟩

/-! ## Traces -/

theorem trace_succ_emit {s s' : R.State} {as : List R.Ans} (h : R.step s = .emit as s')
    (n : Nat) : R.trace s (n + 1) = .answers as :: R.trace s' n := by
  simp only [trace, h]

theorem trace_succ_progress {s s' : R.State} {k : Nat} (h : R.step s = .progress k s')
    (n : Nat) : R.trace s (n + 1) = .level k :: R.trace s' n := by
  simp only [trace, h]

theorem trace_succ_done {s : R.State} {fin : List R.Ans} (h : R.step s = .done fin) (n : Nat) :
    R.trace s (n + 1) = [.final fin] := by
  simp only [trace, h]

/-- What a run emitted is the answers of its trace, concatenated. -/
theorem emitted_eq_flatMap_trace :
    ∀ (n : Nat) (s : R.State), R.emitted s n = (R.trace s n).flatMap Shown.emits
  | 0, _ => rfl
  | n + 1, s => by
    unfold emitted
    cases h : R.step s with
    | done fin => rw [R.run_succ_done h, R.trace_succ_done h]; rfl
    | emit as s' =>
      rw [R.run_succ_emit h, R.trace_succ_emit h, List.flatMap_cons]
      exact congrArg (as ++ ·) (emitted_eq_flatMap_trace n s')
    | progress k s' =>
      rw [R.run_succ_progress h, R.trace_succ_progress h, List.flatMap_cons]
      exact emitted_eq_flatMap_trace n s'

theorem trace_length_le : ∀ (n : Nat) (s : R.State), (R.trace s n).length ≤ n
  | 0, _ => le_rfl
  | n + 1, s => by
    cases h : R.step s with
    | done fin => rw [R.trace_succ_done h]; simp
    | emit as s' => rw [R.trace_succ_emit h]; simpa using trace_length_le n s'
    | progress k s' => rw [R.trace_succ_progress h]; simpa using trace_length_le n s'

/-- A run of `n` steps has reported that it is done exactly when its trace
ends with a final report. -/
theorem final_eq_some_iff : ∀ (n : Nat) (s : R.State) (fin : List R.Ans),
    R.final s n = some fin ↔ (R.trace s n).getLast? = some (.final fin)
  | 0, _, _ => by simp [final, run, trace]
  | n + 1, s, fin => by
    unfold final
    cases h : R.step s with
    | done fin' => rw [R.run_succ_done h, R.trace_succ_done h]; simp
    | emit as s' =>
      rw [R.run_succ_emit h, R.trace_succ_emit h]
      have ih := final_eq_some_iff n s' fin
      unfold final at ih
      rw [ih]
      cases ht : R.trace s' n with
      | nil => simp
      | cons x xs => simp [List.getLast?_cons_cons]
    | progress k s' =>
      rw [R.run_succ_progress h, R.trace_succ_progress h]
      have ih := final_eq_some_iff n s' fin
      unfold final at ih
      rw [ih]
      cases ht : R.trace s' n with
      | nil => simp
      | cons x xs => simp [List.getLast?_cons_cons]

/-! ## Certificates -/

/-- The step taken after `k` steps certifies level `n` exactly when the state
after `k` steps takes that step. -/
theorem certifies_iff : ∀ (k : Nat) (s : R.State) (n : Nat),
    R.Certifies s k n ↔ ∃ s', R.step (R.stateAfter s k) = .progress n s'
  | 0, s, n => by
    unfold Certifies
    cases h : R.step s with
    | done fin => rw [R.trace_succ_done h]; simp [stateAfter, h]
    | emit as s' => rw [R.trace_succ_emit h]; simp [stateAfter, h]
    | progress j s' => rw [R.trace_succ_progress h]; simp [stateAfter, h]
  | k + 1, s, n => by
    unfold Certifies
    cases h : R.step s with
    | done fin =>
      rw [R.trace_succ_done h, R.stateAfter_done h]
      simp [h]
    | emit as s' =>
      rw [R.trace_succ_emit h, R.stateAfter_succ_emit h, List.getElem?_cons_succ]
      exact certifies_iff k s' n
    | progress j s' =>
      rw [R.trace_succ_progress h, R.stateAfter_succ_progress h, List.getElem?_cons_succ]
      exact certifies_iff k s' n

end Runtime

end RwLog
