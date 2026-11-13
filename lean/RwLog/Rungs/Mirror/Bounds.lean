/-
# What the mirrored machine costs

Started with the leader at `x` and the other run at `y`, `g` steps behind,
the first `n` steps of the mirrored machine cost at most `2 n + g` rounds,
each of at most one tick more than 14 times the cheaper of what `C` pays for
`n` steps from `x` and for `g + n` steps from `y` (`spent_le`): each round
advances one of the two runs or both, the leader takes `n` steps, and the
other run at most `g + n`; a round is one race, or two when the runs are
level.

Every step of the machine costs at least a tick (`step_pos`).

Neither fact depends on what the runs emit.
-/
import RwLog.Rungs.Mirror.Trace

namespace RwLog

namespace Mirror

open Cost

variable {C : CostedRuntime}

theorem step_ticks_le (x : C.State) (n : Nat) : (C.step x).ticks ≤ C.spent x (n + 1) := by
  unfold CostedRuntime.spent; omega

/-- Every step of the mirrored machine costs at least a tick. -/
theorem go_pos : ∀ (g : Nat) (f : Bool) (x y : C.State), 1 ≤ (go C g f x y).ticks
  | 0, f, x, y => by rw [go_zero]; show 1 ≤ 1 + raced x y + raced y x; omega
  | g + 1, f, x, y => by
    unfold go
    simp only [bind_ticks, tick_ticks]
    omega

theorem step_pos (s : (machine C).State) : 1 ≤ ((machine C).step s).ticks :=
  go_pos s.gap s.fwd s.lead s.lag

/-- What the machine has spent when the other run catches up by one: the
race, and what it spends from there. -/
theorem spent_catch {x y y' : C.State} {as : List Span} (g : Nat) (f : Bool) (n : Nat)
    (hw : wins x y = false) (hy : (C.step y).val = .emit as y') :
    (machine C).spent ⟨x, y, f, g + 1⟩ (n + 1) =
      1 + raced x y + (machine C).spent ⟨x, y', f, g⟩ (n + 1) := by
  have h : (machine C).step ⟨x, y, f, g + 1⟩ =
      ⟨((machine C).step ⟨x, y', f, g⟩).val,
        1 + raced x y + ((machine C).step ⟨x, y', f, g⟩).ticks⟩ := go_catch g f hw hy
  have ht : ((machine C).step ⟨x, y, f, g + 1⟩).ticks =
      1 + raced x y + ((machine C).step ⟨x, y', f, g⟩).ticks := by rw [h]
  cases hv : ((machine C).step ⟨x, y', f, g⟩).val with
  | emit bs s' =>
    have hv' : ((machine C).step ⟨x, y, f, g + 1⟩).val = .emit bs s' := by rw [h]; exact hv
    rw [(machine C).spent_succ_emit hv', (machine C).spent_succ_emit hv, ht]
    omega
  | done =>
    have hv' : ((machine C).step ⟨x, y, f, g + 1⟩).val = .done := by rw [h]; exact hv
    rw [(machine C).spent_succ_done hv', (machine C).spent_succ_done hv, ht]

/-! ## From above -/

/-- The statement of `spent_le` for one number of steps. -/
def SpentLe (C : CostedRuntime) (n g : Nat) (f : Bool) (x y : C.State) : Prop :=
  (machine C).spent ⟨x, y, f, g⟩ n ≤
    (2 * n + g) * (1 + 14 * min (C.spent x n) (C.spent y (g + n)))

theorem spent_le_level {n : Nat} (ih : ∀ g f x y, SpentLe C n g f x y)
    (f : Bool) (x y : C.State) : SpentLe C (n + 1) 0 f x y := by
  unfold SpentLe
  generalize hK : 1 + 14 * min (C.spent x (n + 1)) (C.spent y (0 + (n + 1))) = K
  have hx1 : (C.step x).ticks ≤ C.spent x (n + 1) := step_ticks_le x n
  have hy1 : (C.step y).ticks ≤ C.spent y (0 + (n + 1)) := by
    rw [Nat.zero_add]; exact step_ticks_le y n
  have hr : 1 + raced x y + raced y x ≤ K := by
    have h1 : raced x y ≤ 7 * min (C.step x).ticks (C.step y).ticks := raceCost_le _ _
    have h1' : raced y x ≤ 7 * min (C.step y).ticks (C.step x).ticks := raceCost_le _ _
    rw [Nat.min_comm] at h1'
    have h2 : min (C.step x).ticks (C.step y).ticks ≤
        min (C.spent x (n + 1)) (C.spent y (0 + (n + 1))) := min_le_min hx1 hy1
    omega
  have h3 : (2 * (n + 1) + 0) * K = 2 * n * K + K + K := by
    rw [show 2 * (n + 1) + 0 = (2 * n + 1) + 1 by omega, Nat.succ_mul, Nat.succ_mul]
  have hdone : (machine C).step ⟨x, y, f, 0⟩ = ⟨.done, 1 + raced x y + raced y x⟩ →
      (machine C).spent ⟨x, y, f, 0⟩ (n + 1) ≤ (2 * (n + 1) + 0) * K := by
    intro hs
    rw [(machine C).spent_succ_done (congrArg Cost.val hs), hs, h3]
    show 1 + raced x y + raced y x ≤ _
    omega
  -- what follows a step that leaves the runs at `x'` and `y'`, `g'` apart
  have hnext : ∀ (bs : List Span) (x' y' : C.State) (f' : Bool) (g' : Nat), g' ≤ 1 →
      (machine C).step ⟨x, y, f, 0⟩ =
        ⟨.emit bs ⟨x', y', f', g'⟩, 1 + raced x y + raced y x⟩ →
      1 + 14 * min (C.spent x' n) (C.spent y' (g' + n)) ≤ K →
      (machine C).spent ⟨x, y, f, 0⟩ (n + 1) ≤ (2 * (n + 1) + 0) * K := by
    intro bs x' y' f' g' hg hs hK'
    have e : (machine C).spent ⟨x, y, f, 0⟩ (n + 1) =
        1 + raced x y + raced y x + (machine C).spent ⟨x', y', f', g'⟩ n := by
      rw [(machine C).spent_succ_emit (congrArg Cost.val hs), hs]
    have h1 := ih g' f' x' y'
    unfold SpentLe at h1
    have h2 := Nat.mul_le_mul_left (2 * n + g') hK'
    have h4 : (2 * n + g') * K ≤ 2 * n * K + K := by
      have h5 : (2 * n + g') * K ≤ (2 * n + 1) * K := Nat.mul_le_mul_right K (by omega)
      have h6 : (2 * n + 1) * K = 2 * n * K + K := by rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [e, h3]
    omega
  have alone : wins x y = true → wins y x = false →
      (machine C).spent ⟨x, y, f, 0⟩ (n + 1) ≤ (2 * (n + 1) + 0) * K := by
    intro w1 w2
    cases hx : (C.step x).val with
    | emit as x' =>
      refine hnext _ x' y f 1 (Nat.le_refl 1) (go_alone_emit f w1 w2 hx) ?_
      have hx2 : C.spent x' n ≤ C.spent x (n + 1) := by rw [C.spent_succ_emit hx]; omega
      have : min (C.spent x' n) (C.spent y (1 + n)) ≤
          min (C.spent x (n + 1)) (C.spent y (0 + (n + 1))) :=
        min_le_min hx2 (by rw [show 1 + n = 0 + (n + 1) by omega])
      omega
    | done => exact hdone (go_alone_done f w1 w2 hx)
  have over : wins x y = false → wins y x = true →
      (machine C).spent ⟨x, y, f, 0⟩ (n + 1) ≤ (2 * (n + 1) + 0) * K := by
    intro w1 w2
    cases hy : (C.step y).val with
    | emit bs y' =>
      refine hnext _ y' x (!f) 1 (Nat.le_refl 1) (go_overtake f w1 w2 hy) ?_
      have hy2 : C.spent y' n ≤ C.spent y (0 + (n + 1)) := by
        rw [Nat.zero_add, C.spent_succ_emit hy]; omega
      have : min (C.spent y' n) (C.spent x (1 + n)) ≤
          min (C.spent x (n + 1)) (C.spent y (0 + (n + 1))) := by
        rw [Nat.min_comm]
        exact min_le_min (by rw [show 1 + n = n + 1 by omega]) hy2
      omega
    | done => exact hdone (go_overtake_done f w1 w2 hy)
  have both : wins x y = wins y x →
      (machine C).spent ⟨x, y, f, 0⟩ (n + 1) ≤ (2 * (n + 1) + 0) * K := by
    intro w
    cases hx : (C.step x).val with
    | emit as x' =>
      cases hy : (C.step y).val with
      | emit bs y' =>
        refine hnext _ x' y' f 0 (Nat.zero_le 1) (go_both_emit f w hx hy) ?_
        have hx2 : C.spent x' n ≤ C.spent x (n + 1) := by rw [C.spent_succ_emit hx]; omega
        have hy2 : C.spent y' (0 + n) ≤ C.spent y (0 + (n + 1)) := by
          rw [Nat.zero_add, Nat.zero_add, C.spent_succ_emit hy]; omega
        have : min (C.spent x' n) (C.spent y' (0 + n)) ≤
            min (C.spent x (n + 1)) (C.spent y (0 + (n + 1))) := min_le_min hx2 hy2
        omega
      | done => exact hdone (go_both_done f w (.inr hy))
    | done => exact hdone (go_both_done f w (.inl hx))
  cases h1 : wins x y <;> cases h2 : wins y x
  · exact both (by rw [h1, h2])
  · exact over h1 h2
  · exact alone h1 h2
  · exact both (by rw [h1, h2])

theorem spent_le_behind {n : Nat} (ih : ∀ g f x y, SpentLe C n g f x y)
    (g : Nat) (f : Bool) (x y : C.State)
    (hc : ∀ as y', (C.step y).val = .emit as y' → SpentLe C (n + 1) g f x y') :
    SpentLe C (n + 1) (g + 1) f x y := by
  unfold SpentLe
  generalize hK : 1 + 14 * min (C.spent x (n + 1)) (C.spent y (g + 1 + (n + 1))) = K
  have hx1 : (C.step x).ticks ≤ C.spent x (n + 1) := step_ticks_le x n
  have hy1 : (C.step y).ticks ≤ C.spent y (g + 1 + (n + 1)) := step_ticks_le y (g + 1 + n)
  have hr : 1 + raced x y ≤ K := by
    have h1 : raced x y ≤ 7 * min (C.step x).ticks (C.step y).ticks := raceCost_le _ _
    have h2 : min (C.step x).ticks (C.step y).ticks ≤
        min (C.spent x (n + 1)) (C.spent y (g + 1 + (n + 1))) := min_le_min hx1 hy1
    omega
  have hone : 1 + raced x y ≤ (2 * (n + 1) + (g + 1)) * K :=
    le_trans hr (Nat.le_mul_of_pos_left K (by omega))
  by_cases hw : wins x y = true
  · cases hx : (C.step x).val with
    | emit as x' =>
      have hs : (machine C).step ⟨x, y, f, g + 1⟩ =
          ⟨.emit (orient f as) ⟨x', y, f, g + 2⟩, 1 + raced x y⟩ := go_lead_emit g f hw hx
      have e : (machine C).spent ⟨x, y, f, g + 1⟩ (n + 1) =
          1 + raced x y + (machine C).spent ⟨x', y, f, g + 2⟩ n := by
        rw [(machine C).spent_succ_emit (congrArg Cost.val hs), hs]
      have h1 := ih (g + 2) f x' y
      unfold SpentLe at h1
      have hx2 : C.spent x' n ≤ C.spent x (n + 1) := by
        rw [C.spent_succ_emit hx]; omega
      have hK' : 1 + 14 * min (C.spent x' n) (C.spent y (g + 2 + n)) ≤ K := by
        have : min (C.spent x' n) (C.spent y (g + 2 + n)) ≤
            min (C.spent x (n + 1)) (C.spent y (g + 1 + (n + 1))) :=
          min_le_min hx2 (by rw [show g + 2 + n = g + 1 + (n + 1) by omega])
        omega
      have h2 := Nat.mul_le_mul_left (2 * n + (g + 2)) hK'
      have h3 : (2 * (n + 1) + (g + 1)) * K = (2 * n + (g + 2)) * K + K := by
        rw [show 2 * (n + 1) + (g + 1) = (2 * n + (g + 2)) + 1 by omega, Nat.succ_mul]
      rw [e, h3]
      omega
    | done =>
      have hs : (machine C).step ⟨x, y, f, g + 1⟩ = ⟨.done, 1 + raced x y⟩ :=
        go_lead_done g f hw hx
      rw [(machine C).spent_succ_done (congrArg Cost.val hs), hs]
      exact hone
  · have hw : wins x y = false := by simpa using hw
    cases hy : (C.step y).val with
    | done =>
      have hs : (machine C).step ⟨x, y, f, g + 1⟩ = ⟨.done, 1 + raced x y⟩ :=
        go_lag_done g f hw hy
      rw [(machine C).spent_succ_done (congrArg Cost.val hs), hs]
      exact hone
    | emit bs y' =>
      have h1 := hc bs y' hy
      unfold SpentLe at h1
      have hy2 : C.spent y' (g + (n + 1)) ≤ C.spent y (g + 1 + (n + 1)) := by
        rw [show g + 1 + (n + 1) = (g + (n + 1)) + 1 by omega, C.spent_succ_emit hy]; omega
      have hK' : 1 + 14 * min (C.spent x (n + 1)) (C.spent y' (g + (n + 1))) ≤ K := by
        have : min (C.spent x (n + 1)) (C.spent y' (g + (n + 1))) ≤
            min (C.spent x (n + 1)) (C.spent y (g + 1 + (n + 1))) := min_le_min le_rfl hy2
        omega
      have h2 := Nat.mul_le_mul_left (2 * (n + 1) + g) hK'
      have h3 : (2 * (n + 1) + (g + 1)) * K = (2 * (n + 1) + g) * K + K := by
        rw [show 2 * (n + 1) + (g + 1) = (2 * (n + 1) + g) + 1 by omega, Nat.succ_mul]
      rw [spent_catch g f n hw hy, h3]
      omega

/-- The first `n` steps of the mirrored machine cost at most `2 n + g`
rounds, each of at most one tick more than 14 times the cheaper of the two
runs. -/
theorem spent_le : ∀ (n g : Nat) (f : Bool) (x y : C.State), SpentLe C n g f x y := by
  intro n
  induction n with
  | zero => intro g f x y; exact Nat.zero_le _
  | succ n ih =>
    intro g
    induction g with
    | zero => intro f x y; exact spent_le_level ih f x y
    | succ g ihg =>
      intro f x y
      exact spent_le_behind ih g f x y fun as y' _ => ihg f x y'

end Mirror

end RwLog
