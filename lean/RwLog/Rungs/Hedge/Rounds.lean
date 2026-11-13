/-
# What the hedge asks of a machine, for the tabled machines

`Hedge.follows_first` and `Hedge.follows_second` ask of each machine that the
sizes of the answers a step emits are at most the ticks of the step. A round
of the tabled machine (`Tabled.round`) and of the goal-directed machine
(`Directed.round`) emits what the first table gained, and a table pays for
what it gains: `Tabled.fresh` compares each candidate it keeps with itself
(`fresh_sizes_le`). A round also costs at least one tick.
-/
import RwLog.Rungs.Hedge.Filters
import RwLog.Rungs.Directed.Machine
import RwLog.Rungs.Framework.TraverseStd

namespace RwLog

open Cost R001

namespace Hedge

theorem sizes_map_swap (xs : List Span) : sizes (xs.map Span.swap) = sizes xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, Span.size_swap]

theorem sizes_orient (f : Bool) (xs : List Span) : sizes (orient f xs) = sizes xs := by
  cases f
  · rfl
  · exact sizes_map_swap xs

/-- What the first table gains when every table adds its fresh candidates
costs at least its size. -/
theorem gained_sizes_le (ts : Tables) (outs : List (List Span × List Goal)) (t t' : Table)
    (ht : ts.head? = some t)
    (ht' : ((mapL (fun p : Table × List Span × List Goal => do
        let f ← Tabled.fresh p.1.answers p.2.1
        pure (⟨p.1.goal, p.1.answers ++ f, p.1.done⟩ : Table)) (ts.zip outs)).val).head? = some t') :
    sizes (t'.answers.drop t.answers.length) ≤
    (mapL (fun p : Table × List Span × List Goal => do
        let f ← Tabled.fresh p.1.answers p.2.1
        pure (⟨p.1.goal, p.1.answers ++ f, p.1.done⟩ : Table)) (ts.zip outs)).ticks := by
  cases ts with
  | nil => cases ht
  | cons t₀ ts =>
    cases outs with
    | nil => cases ht'
    | cons o outs =>
      have h := fresh_sizes_le t₀.answers o.1
      simp only [List.head?_cons, Option.some.injEq] at ht
      subst ht
      simp only [List.zip_cons_cons, mapL, bind_val, pure_val, List.head?_cons,
        Option.some.injEq] at ht'
      subst ht'
      simp only [List.zip_cons_cons, mapL, bind_ticks, pure_ticks, List.drop_left']
      omega

/-- The answers a round of the tabled machine emits are no larger than what
the round costs. -/
theorem tabled_round_sizes (U : Oracle) (st : R001.State) :
    sizes (Tabled.round U st).val.2 ≤ (Tabled.round U st).ticks := by
  unfold Tabled.round
  simp only [bind_val, bind_ticks, pure_val, pure_ticks, sizes_orient]
  split
  · next t t' ht ht' =>
    exact le_trans (gained_sizes_le _ _ t t' ht ht') (le_trans (Nat.le_add_right _ _)
      (le_trans (Nat.le_add_left _ _) (le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _))))
  · exact Nat.zero_le _

theorem tabled_step_sizes (U : Oracle) (s : R001.State) (as : List Span) (s' : R001.State)
    (h : ((Tabled.machine U).step s).val = .emit as s') :
    sizes as ≤ ((Tabled.machine U).step s).ticks := by
  have h' : (Tabled.step U s).val = .emit as s' := h
  show sizes as ≤ (Tabled.step U s).ticks
  unfold Tabled.step at h' ⊢
  by_cases hf : s.finished = true
  · simp [hf] at h'
  · simp only [hf, Bool.false_eq_true, ite_false, bind_val, pure_val, StepOf.emit.injEq] at h'
    simp only [hf, Bool.false_eq_true, ite_false, bind_ticks, pure_ticks]
    rw [← h'.1]
    have := tabled_round_sizes U s
    omega

/-- The answers a round of the goal-directed machine emits are no larger than
what the round costs. -/
theorem directed_round_sizes (st : R001.State) :
    sizes (Directed.round st).val.2 ≤ (Directed.round st).ticks := by
  unfold Directed.round
  simp only [bind_val, bind_ticks, pure_val, pure_ticks, sizes_orient]
  split
  · next t t' ht ht' =>
    exact le_trans (gained_sizes_le _ _ t t' ht ht') (le_trans (Nat.le_add_right _ _)
      (le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _)))
  · exact Nat.zero_le _

theorem directed_step_sizes (s : R001.State) (as : List Span) (s' : R001.State)
    (h : (Directed.machine.step s).val = .emit as s') :
    sizes as ≤ (Directed.machine.step s).ticks := by
  have h' : (Directed.step s).val = .emit as s' := h
  show sizes as ≤ (Directed.step s).ticks
  unfold Directed.step at h' ⊢
  simp only [bind_val, pure_val, StepOf.emit.injEq] at h'
  simp only [bind_ticks, pure_ticks]
  rw [← h'.1]
  have := directed_round_sizes s
  omega

/-- A round of the goal-directed machine costs at least one tick. -/
theorem directed_step_pos (s : R001.State) : 1 ≤ (Directed.machine.step s).ticks := by
  show 1 ≤ (Directed.step s).ticks
  unfold Directed.step Directed.round
  simp only [bind_ticks, tick_ticks]
  omega

end Hedge

end RwLog
