/-
# R002 simulates R001 within a cubic polynomial

Both machines are the tabled round machine with their own oracle, and the two
oracles return the same answers, so the machines go through the same states.
A round of either spends one tick, then what its incomplete tables spend
asking the oracle, then what the rest of the round spends on the oracle's
answers (`Tabled.round_split`). Only the middle part differs.

Each incomplete table is charged the size of its goal before it asks, so by
`onDemand_dominated` what a table spends in R002 is at most `F N x`, where
`x` is what it spends in R001, `N` the size of the input and

    F N x = 4 x³ (N + 2)³ + x.

`F N` is superadditive, so the bound adds up over the tables of a round and
over the rounds of a run, and `F N c ≤ 5 c³ (N + 2)³`.
-/
import RwLog.Rungs.R002.Proofs.Dominated
import RwLog.Rungs.R002.Proofs.Same
import RwLog.Rungs.Framework.Latency

namespace RwLog

namespace R002

open Cost R001

/-! ## The bound and its arithmetic -/

/-- What R002 spends where R001 spends `x`, on an input of size `N`. -/
def F (N x : Nat) : Nat := 4 * x ^ 3 * (N + 2) ^ 3 + x

theorem F_zero (N : Nat) : F N 0 = 0 := by
  unfold F; simp

theorem self_le_F (N x : Nat) : x ≤ F N x := Nat.le_add_left _ _

theorem F_add (N x y : Nat) : F N x + F N y ≤ F N (x + y) := by
  unfold F
  have h : x ^ 3 + y ^ 3 ≤ (x + y) ^ 3 := by
    have : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y * (x + y)) := by ring
    omega
  have := Nat.mul_le_mul_right ((N + 2) ^ 3) (Nat.mul_le_mul_left 4 h)
  rw [Nat.mul_add, Nat.add_mul] at this
  omega

theorem F_sum {α : Type} (N : Nat) (x : α → Nat) (xs : List α) :
    (xs.map fun t => F N (x t)).sum ≤ F N (xs.map x).sum := by
  induction xs with
  | nil => simp [F_zero]
  | cons t xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.le_trans (Nat.add_le_add_left ih _) (F_add N _ _)

theorem F_le (N c : Nat) : F N c ≤ 5 * c ^ 3 * (N + 2) ^ 3 := by
  unfold F
  have h1 : c ≤ c ^ 3 := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · calc c = c * 1 := (Nat.mul_one c).symm
        _ ≤ c * c ^ 2 := Nat.mul_le_mul_left c (Nat.one_le_pow _ _ hc)
        _ = c ^ 3 := by ring
  have h2 : c ^ 3 ≤ c ^ 3 * (N + 2) ^ 3 :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  have h3 : 5 * c ^ 3 * (N + 2) ^ 3 = 4 * c ^ 3 * (N + 2) ^ 3 + c ^ 3 * (N + 2) ^ 3 := by ring
  omega

/-- One table: it pays the size `g` of its goal and then asks the oracle. -/
theorem F_table {N p g e o : Nat} (hg : 1 ≤ g) (hp : p ≤ N) (ho : o ≤ 4 * (e + p + g + 1) ^ 3) :
    g + o ≤ F N (g + e) := by
  unfold F
  have h1 : e + p + g + 1 ≤ (g + e) * (N + 2) := by nlinarith
  have h2 : (e + p + g + 1) ^ 3 ≤ (g + e) ^ 3 * (N + 2) ^ 3 := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left h1 3
  have h3 := Nat.mul_le_mul_left 4 h2
  rw [← Nat.mul_assoc] at h3
  omega

theorem goalSize_pos (g : Goal) : 1 ≤ goalSize g := by
  have := Rel.size_pos g.e
  unfold goalSize
  omega

/-! ## A round, split at the oracle -/

theorem ask_val (st : State) (t : Table) : (Tabled.ask onDemand st t).val = (Tabled.ask eager st t).val := by
  unfold Tabled.ask
  simp only [ite_val, pure_val, bind_val, onDemand_exact st.P st.depth t.goal,
    eager_exact st.P st.depth t.goal]

theorem ask_ticks {N : Nat} (st : State) (hP : st.P.size ≤ N) (t : Table) :
    (Tabled.ask onDemand st t).ticks ≤ F N (Tabled.ask eager st t).ticks := by
  unfold Tabled.ask
  simp only [ite_ticks, pure_ticks, bind_ticks, tick_ticks]
  split
  · exact Nat.zero_le _
  · exact F_table (goalSize_pos t.goal) hP (onDemand_dominated st.P st.depth t.goal)

theorem round_ticks {N : Nat} (st : State) (hP : st.P.size ≤ N) :
    (Tabled.round onDemand st).ticks ≤ F N (Tabled.round eager st).ticks := by
  obtain ⟨K, hK⟩ := Tabled.round_split st
  have hv : (mapL (Tabled.ask onDemand st) st.tables).val = (mapL (Tabled.ask eager st) st.tables).val := by
    rw [mapL_val, mapL_val]
    exact List.map_congr_left fun t _ => ask_val st t
  have ht : (mapL (Tabled.ask onDemand st) st.tables).ticks ≤
      F N (mapL (Tabled.ask eager st) st.tables).ticks := by
    rw [mapL_ticks, mapL_ticks]
    exact Nat.le_trans (sum_map_le fun t _ => ask_ticks st hP t) (F_sum N _ _)
  rw [hK onDemand, hK eager]
  simp only [bind_ticks, tick_ticks, hv]
  have h1 := self_le_F N (1 + (K (mapL (Tabled.ask eager st) st.tables).val).ticks)
  have h2 := F_add N (mapL (Tabled.ask eager st) st.tables).ticks
    (1 + (K (mapL (Tabled.ask eager st) st.tables).val).ticks)
  refine Nat.le_trans ?_ (Nat.le_trans h2 (Nat.le_of_eq (congrArg (F N) (by omega))))
  omega

theorem step_ticks {N : Nat} (st : State) (hP : st.P.size ≤ N) :
    (costed.step st).ticks ≤ F N (baseline.step st).ticks := by
  show (Tabled.step onDemand st).ticks ≤ F N (Tabled.step eager st).ticks
  unfold Tabled.step
  simp only [ite_ticks, pure_ticks, bind_ticks, Nat.add_zero]
  split
  · exact Nat.zero_le _
  · exact round_ticks st hP

theorem costed_step_val (st : State) : (costed.step st).val = R001.step st :=
  Tabled.step_val onDemand onDemand_exact st

theorem baseline_step_val (st : State) : (baseline.step st).val = R001.step st :=
  Tabled.step_val eager eager_exact st

/-! ## A run -/

/-- What R002 has spent after any number of steps, against what R001 has. -/
theorem spent_le (N : Nat) : ∀ (n : Nat) (st : State), st.P.size ≤ N →
    costed.spent st n ≤ F N (baseline.spent st n)
  | 0, _, _ => Nat.zero_le _
  | n + 1, st, hP => by
    have hs := step_ticks st hP
    cases h : R001.step st with
    | done =>
      rw [costed.spent_succ_done ((costed_step_val st).trans h),
        baseline.spent_succ_done ((baseline_step_val st).trans h)]
      exact hs
    | emit as st' =>
      have hP' : st'.P.size ≤ N := by
        unfold R001.step at h
        split at h
        · cases h
        · simp only [Step.emit.injEq] at h
          rw [← h.2, round_P]
          exact hP
      rw [costed.spent_succ_emit ((costed_step_val st).trans h),
        baseline.spent_succ_emit ((baseline_step_val st).trans h)]
      exact Nat.le_trans (Nat.add_le_add hs (spent_le N n st' hP')) (F_add N _ _)

/-- R002 simulates R001 within `5 c³ (n + 2)³`, where `c` is what R001 has
paid and `n` the size of the program and the query. -/
theorem simulates : Obligation.simulates := by
  refine Simulates.of_steps ?_
  intro P q _ n
  have hc : costed.runtime = R001.runtime := runtime_eq
  have hb : baseline.runtime = R001.runtime := baseline_exact
  refine ⟨n, ?_, ?_, ?_⟩
  · exact Nat.le_trans
      (spent_le (P.size + q.size) n (State.ofGoal P ⟨none, q, none⟩) (Nat.le_add_right _ _))
      (F_le _ _)
  · show ∀ a ∈ baseline.runtime.emitted (baseline.runtime.init P q) n,
      ∃ b ∈ costed.runtime.emitted (costed.runtime.init P q) n, b.CoversLive P.theory a
    rw [hc, hb]
    exact fun a ha => ⟨a, ha, Span.CoversLive.refl _ a⟩
  · show baseline.runtime.Halts (baseline.runtime.init P q) n →
      costed.runtime.Halts (costed.runtime.init P q) n
    rw [hc, hb]
    exact id

end R002

end RwLog
