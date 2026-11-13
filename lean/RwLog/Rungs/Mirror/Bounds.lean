/-
# What the mirrored machine costs

Started with the leader at `x` and the other run at `y`, `g` steps behind,
the first `n` steps of the mirrored machine cost

* at most `(2 n + g)` races, each of at most one tick more than 7 times the
  cheaper of what `C` pays for `n` steps from `x` and for `g + n` steps from
  `y` (`spent_le`): each race advances one of the two runs, the leader takes
  `n` steps, and the other run at most `g + n`;
* at least the cheaper of those two, and at least `n` ticks, when the machine
  has not stopped (`le_spent`): a race costs at least what its winner costs,
  and one of the two runs has taken all its steps.

Neither bound depends on what the runs emit.
-/
import RwLog.Rungs.Mirror.Trace

namespace RwLog

namespace Mirror

open Cost

variable {C : CostedRuntime}

theorem step_ticks_le (x : C.State) (n : Nat) : (C.step x).ticks ≤ C.spent x (n + 1) := by
  unfold CostedRuntime.spent; omega

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
    (2 * n + g) * (1 + 7 * min (C.spent x n) (C.spent y (g + n)))

theorem spent_le_step {n : Nat} (ih : ∀ g f x y, SpentLe C n g f x y)
    (g : Nat) (f : Bool) (x y : C.State)
    (hc : ∀ g' as y', g = g' + 1 → (C.step y).val = .emit as y' → SpentLe C (n + 1) g' f x y') :
    SpentLe C (n + 1) g f x y := by
  unfold SpentLe
  generalize hK : 1 + 7 * min (C.spent x (n + 1)) (C.spent y (g + (n + 1))) = K
  have hx1 : (C.step x).ticks ≤ C.spent x (n + 1) := step_ticks_le x n
  have hy1 : (C.step y).ticks ≤ C.spent y (g + (n + 1)) := step_ticks_le y (g + n)
  have hr : 1 + raced x y ≤ K := by
    have h1 : raced x y ≤ 7 * min (C.step x).ticks (C.step y).ticks := raceCost_le _ _
    have h2 : min (C.step x).ticks (C.step y).ticks ≤
        min (C.spent x (n + 1)) (C.spent y (g + (n + 1))) := min_le_min hx1 hy1
    omega
  have hone : 1 + raced x y ≤ (2 * (n + 1) + g) * K :=
    le_trans hr (Nat.le_mul_of_pos_left K (by omega))
  by_cases hw : wins x y = true
  · cases hx : (C.step x).val with
    | emit as x' =>
      have hs : (machine C).step ⟨x, y, f, g⟩ =
          ⟨.emit (orient f as) ⟨x', y, f, g + 1⟩, 1 + raced x y⟩ := go_lead_emit g f hw hx
      have e : (machine C).spent ⟨x, y, f, g⟩ (n + 1) =
          1 + raced x y + (machine C).spent ⟨x', y, f, g + 1⟩ n := by
        rw [(machine C).spent_succ_emit (congrArg Cost.val hs), hs]
      have h1 := ih (g + 1) f x' y
      unfold SpentLe at h1
      have hx2 : C.spent x' n ≤ C.spent x (n + 1) := by
        rw [C.spent_succ_emit hx]; omega
      have hK' : 1 + 7 * min (C.spent x' n) (C.spent y (g + 1 + n)) ≤ K := by
        have : min (C.spent x' n) (C.spent y (g + 1 + n)) ≤
            min (C.spent x (n + 1)) (C.spent y (g + (n + 1))) :=
          min_le_min hx2 (by rw [show g + 1 + n = g + (n + 1) by omega])
        omega
      have h2 := Nat.mul_le_mul_left (2 * n + (g + 1)) hK'
      have h3 : (2 * (n + 1) + g) * K = (2 * n + (g + 1)) * K + K := by
        rw [show 2 * (n + 1) + g = (2 * n + (g + 1)) + 1 by omega, Nat.succ_mul]
      rw [e, h3]
      omega
    | done =>
      have hs : (machine C).step ⟨x, y, f, g⟩ = ⟨.done, 1 + raced x y⟩ := go_lead_done g f hw hx
      rw [(machine C).spent_succ_done (congrArg Cost.val hs), hs]
      exact hone
  · have hw : wins x y = false := by simpa using hw
    cases hy : (C.step y).val with
    | done =>
      have hs : (machine C).step ⟨x, y, f, g⟩ = ⟨.done, 1 + raced x y⟩ := go_lag_done g f hw hy
      rw [(machine C).spent_succ_done (congrArg Cost.val hs), hs]
      exact hone
    | emit bs y' =>
      cases g with
      | zero =>
        have hs : (machine C).step ⟨x, y, f, 0⟩ =
            ⟨.emit (orient (!f) bs) ⟨y', x, !f, 1⟩, 1 + raced x y⟩ := go_overtake f hw hy
        have e : (machine C).spent ⟨x, y, f, 0⟩ (n + 1) =
            1 + raced x y + (machine C).spent ⟨y', x, !f, 1⟩ n := by
          rw [(machine C).spent_succ_emit (congrArg Cost.val hs), hs]
        have h1 := ih 1 (!f) y' x
        unfold SpentLe at h1
        have hy2 : C.spent y' n ≤ C.spent y (0 + (n + 1)) := by
          rw [Nat.zero_add, C.spent_succ_emit hy]; omega
        have hK' : 1 + 7 * min (C.spent y' n) (C.spent x (1 + n)) ≤ K := by
          have : min (C.spent y' n) (C.spent x (1 + n)) ≤
              min (C.spent x (n + 1)) (C.spent y (0 + (n + 1))) := by
            rw [min_comm]
            exact min_le_min (by rw [show 1 + n = n + 1 by omega]) hy2
          omega
        have h2 := Nat.mul_le_mul_left (2 * n + 1) hK'
        have h3 : (2 * (n + 1) + 0) * K = (2 * n + 1) * K + K := by
          rw [show 2 * (n + 1) + 0 = (2 * n + 1) + 1 by omega, Nat.succ_mul]
        rw [e, h3]
        omega
      | succ g =>
        have h1 := hc g bs y' rfl hy
        unfold SpentLe at h1
        have hy2 : C.spent y' (g + (n + 1)) ≤ C.spent y (g + 1 + (n + 1)) := by
          rw [show g + 1 + (n + 1) = (g + (n + 1)) + 1 by omega, C.spent_succ_emit hy]; omega
        have hK' : 1 + 7 * min (C.spent x (n + 1)) (C.spent y' (g + (n + 1))) ≤ K := by
          have : min (C.spent x (n + 1)) (C.spent y' (g + (n + 1))) ≤
              min (C.spent x (n + 1)) (C.spent y (g + 1 + (n + 1))) := min_le_min le_rfl hy2
          omega
        have h2 := Nat.mul_le_mul_left (2 * (n + 1) + g) hK'
        have h3 : (2 * (n + 1) + (g + 1)) * K = (2 * (n + 1) + g) * K + K := by
          rw [show 2 * (n + 1) + (g + 1) = (2 * (n + 1) + g) + 1 by omega, Nat.succ_mul]
        rw [spent_catch g f n hw hy, h3]
        omega

/-- The first `n` steps of the mirrored machine cost at most `2 n + g` races,
each of at most one tick more than 7 times the cheaper of the two runs. -/
theorem spent_le : ∀ (n g : Nat) (f : Bool) (x y : C.State), SpentLe C n g f x y := by
  intro n
  induction n with
  | zero => intro g f x y; exact Nat.zero_le _
  | succ n ih =>
    intro g
    induction g with
    | zero => intro f x y; exact spent_le_step ih 0 f x y fun g' _ _ h _ => by omega
    | succ g ihg =>
      intro f x y
      refine spent_le_step ih (g + 1) f x y fun g' as y' hg _ => ?_
      have hg' : g = g' := by omega
      subst hg'
      exact ihg f x y'

/-! ## From below -/

/-- The statement of `le_spent` for one number of steps. -/
def LeSpent (C : CostedRuntime) (n g : Nat) (f : Bool) (x y : C.State) : Prop :=
  ((machine C).runtime.trace ⟨x, y, f, g⟩ n).length = n →
    min (C.spent x n) (C.spent y (g + n)) ≤ (machine C).spent ⟨x, y, f, g⟩ n ∧
      n ≤ (machine C).spent ⟨x, y, f, g⟩ n

theorem le_spent_step {n : Nat} (ih : ∀ g f x y, LeSpent C n g f x y)
    (g : Nat) (f : Bool) (x y : C.State)
    (hc : ∀ g' as y', g = g' + 1 → (C.step y).val = .emit as y' → LeSpent C (n + 1) g' f x y') :
    LeSpent C (n + 1) g f x y := by
  unfold LeSpent
  intro hlen
  have hwin := winner_le_raceCost (C.step x).ticks (C.step y).ticks
  by_cases hw : wins x y = true
  · have hwx : (C.step x).ticks ≤ raced x y := by
      have : firstWins (C.step x).ticks (C.step y).ticks = true := hw
      rw [this] at hwin; exact hwin
    cases hx : (C.step x).val with
    | emit as x' =>
      have hs : (machine C).step ⟨x, y, f, g⟩ =
          ⟨.emit (orient f as) ⟨x', y, f, g + 1⟩, 1 + raced x y⟩ := go_lead_emit g f hw hx
      have e : (machine C).spent ⟨x, y, f, g⟩ (n + 1) =
          1 + raced x y + (machine C).spent ⟨x', y, f, g + 1⟩ n := by
        rw [(machine C).spent_succ_emit (congrArg Cost.val hs), hs]
      rw [(machine C).runtime.trace_succ_emit (congrArg Cost.val hs)] at hlen
      obtain ⟨h1, h2⟩ := ih (g + 1) f x' y (by simpa using hlen)
      rw [e, C.spent_succ_emit hx, show g + (n + 1) = g + 1 + n by omega]
      refine ⟨?_, by omega⟩
      rcases Nat.le_total (C.spent x' n) (C.spent y (g + 1 + n)) with h | h
      · rw [Nat.min_eq_left h] at h1
        exact le_trans (Nat.min_le_left _ _) (by omega)
      · rw [Nat.min_eq_right h] at h1
        exact le_trans (Nat.min_le_right _ _) (by omega)
    | done =>
      have hs : (machine C).step ⟨x, y, f, g⟩ = ⟨.done, 1 + raced x y⟩ := go_lead_done g f hw hx
      rw [(machine C).runtime.trace_succ_done (congrArg Cost.val hs)] at hlen
      simp at hlen
  · have hw : wins x y = false := by simpa using hw
    have hwy : (C.step y).ticks ≤ raced x y := by
      have : firstWins (C.step x).ticks (C.step y).ticks = false := hw
      rw [this] at hwin; exact hwin
    cases hy : (C.step y).val with
    | done =>
      have hs : (machine C).step ⟨x, y, f, g⟩ = ⟨.done, 1 + raced x y⟩ := go_lag_done g f hw hy
      rw [(machine C).runtime.trace_succ_done (congrArg Cost.val hs)] at hlen
      simp at hlen
    | emit bs y' =>
      cases g with
      | zero =>
        have hs : (machine C).step ⟨x, y, f, 0⟩ =
            ⟨.emit (orient (!f) bs) ⟨y', x, !f, 1⟩, 1 + raced x y⟩ := go_overtake f hw hy
        have e : (machine C).spent ⟨x, y, f, 0⟩ (n + 1) =
            1 + raced x y + (machine C).spent ⟨y', x, !f, 1⟩ n := by
          rw [(machine C).spent_succ_emit (congrArg Cost.val hs), hs]
        have hs' : (machine C).runtime.step ⟨x, y, f, 0⟩ =
            .emit (orient (!f) bs) ⟨y', x, !f, 1⟩ := congrArg Cost.val hs
        rw [(machine C).runtime.trace_succ_emit hs'] at hlen
        obtain ⟨h1, h2⟩ := ih 1 (!f) y' x (by simpa using hlen)
        rw [e, Nat.zero_add, C.spent_succ_emit hy]
        rw [show 1 + n = n + 1 by omega] at h1
        refine ⟨?_, by omega⟩
        rcases Nat.le_total (C.spent y' n) (C.spent x (n + 1)) with h | h
        · rw [Nat.min_eq_left h] at h1
          exact le_trans (Nat.min_le_right _ _) (by omega)
        · rw [Nat.min_eq_right h] at h1
          exact le_trans (Nat.min_le_left _ _) (by omega)
      | succ g =>
        have hs : (machine C).runtime.step ⟨x, y, f, g + 1⟩ =
            (machine C).runtime.step ⟨x, y', f, g⟩ := by
          show (go C (g + 1) f x y).val = (go C g f x y').val
          rw [go_catch g f hw hy]
        rw [(machine C).runtime.trace_congr hs] at hlen
        obtain ⟨h1, h2⟩ := hc g bs y' rfl hy hlen
        rw [spent_catch g f n hw hy, show g + 1 + (n + 1) = (g + (n + 1)) + 1 by omega,
          C.spent_succ_emit hy]
        refine ⟨?_, by omega⟩
        rcases Nat.le_total (C.spent x (n + 1)) (C.spent y' (g + (n + 1))) with h | h
        · rw [Nat.min_eq_left h] at h1
          exact le_trans (Nat.min_le_left _ _) (by omega)
        · rw [Nat.min_eq_right h] at h1
          exact le_trans (Nat.min_le_right _ _) (by omega)

/-- While the mirrored machine has not stopped, its first `n` steps cost at
least the cheaper of the two runs, and at least `n` ticks. -/
theorem le_spent : ∀ (n g : Nat) (f : Bool) (x y : C.State), LeSpent C n g f x y := by
  intro n
  induction n with
  | zero => intro g f x y _; exact ⟨by simp, Nat.zero_le _⟩
  | succ n ih =>
    intro g
    induction g with
    | zero => intro f x y; exact le_spent_step ih 0 f x y fun g' _ _ h _ => by omega
    | succ g ihg =>
      intro f x y
      refine le_spent_step ih (g + 1) f x y fun g' as y' hg _ => ?_
      have hg' : g = g' := by omega
      subst hg'
      exact ihg f x y'

end Mirror

end RwLog
