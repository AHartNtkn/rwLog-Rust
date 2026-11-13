/-
# R002: what a round of R001 costs at least

While its root table is open, a round of the costed R001 asks the eager
unfolder about the root goal, and the eager unfolder builds the goal's
unfolding level by level, paying one tick per node of every level
(`Eager.unfoldN_ticks_nodes`). So the round costs at least the number of nodes of
the unfolding to any earlier depth: obligation `baseline_lower`.
-/
import RwLog.Rungs.R002.Proofs.Eager

namespace RwLog

namespace R002

open Cost

namespace Eager

/-- Unfolding once costs one tick per node. -/
theorem unfold_ticks_nodes (P : Program) (e : Rel) : (unfold P e).ticks = nodes e := by
  induction e with
  | zero => rfl
  | span s => rfl
  | or a b iha ihb => simp [unfold, nodes, iha, ihb]; omega
  | and a b iha ihb => simp [unfold, nodes, iha, ihb]; omega
  | seq a b iha ihb => simp [unfold, nodes, iha, ihb]; omega
  | conv a iha => simp [unfold, nodes, iha]
  | call n => rfl

/-- Unfolding to depth `d` pays for every level before `d`. -/
theorem unfoldN_ticks_nodes (P : Program) {i d : Nat} (h : i < d) (e : Rel) :
    nodes (R000.unfoldN P i e) ≤ (unfoldN P d e).ticks := by
  induction d generalizing i e with
  | zero => omega
  | succ d ih =>
    simp only [unfoldN, bind_ticks, unfold_ticks_nodes, unfold_val]
    cases i with
    | zero => exact Nat.le_add_right _ _
    | succ i =>
      have := ih (i := i) (by omega) (R000.unfold P e)
      have e' : R000.unfoldN P (i + 1) e = R000.unfoldN P i (R000.unfold P e) := rfl
      rw [e']
      omega

end Eager

theorem eager_ticks_ge (P : Program) {i d : Nat} (h : i < d) (g : R001.Goal) :
    nodes (R000.unfoldN P i g.rel) ≤ (eager P d g).ticks := by
  have := Eager.unfoldN_ticks_nodes P h g.rel
  simp only [eager, bind_ticks]
  omega

/-- A round costs at least what the oracle costs on the root goal, when the
root table is open. -/
theorem Tabled.round_ticks_ge (U : Oracle) (st : R001.State) (t : R001.Table)
    (ht : st.tables.head? = some t) (hd : t.done = false) :
    (U st.P st.depth t.goal).ticks ≤ (Tabled.round U st).ticks := by
  obtain ⟨P, ts, flip, d⟩ := st
  cases ts with
  | nil => simp at ht
  | cons t' ts =>
    obtain rfl : t' = t := by simpa using ht
    simp only [Tabled.round, bind_ticks, mapL, hd, Bool.false_eq_true, ↓reduceIte, tick_ticks]
    omega

theorem baseline_lower : Obligation.baseline_lower := by
  intro st t ht hd i hi
  have hfin : st.finished = false := by simp [R001.State.finished, ht, hd]
  have h1 := eager_ticks_ge st.P hi t.goal
  have h2 := Tabled.round_ticks_ge eager st t ht hd
  have : (baseline.step st).ticks = (Tabled.round eager st).ticks := by
    show (Tabled.step eager st).ticks = _
    simp [Tabled.step, hfin]
  omega

end R002

end RwLog
