/-
# The separating family: one round

A round of R002 takes the state `st k d` to `st k (d + 1)`, emits `z -> z` in
round `k + 3` and nothing otherwise, and costs at most `roundBound k d`, which
is cubic in the number of tables. The stages are those of `Stages.lean`,
`NewTables.lean` and `Completion.lean`, put together in the order the machine
runs them.
-/
import RwLog.Rungs.R002.Proofs.Separation.Completion

namespace RwLog

namespace R002

namespace Sep

open Cost R001

/-! ## The tables after the round -/

theorem isDone_mono (k d : Nat) (s : Slot) (h : isDone k d s = true) : isDone k (d + 1) s = true := by
  cases s with
  | root => rw [isDone_root] at h ⊢; omega
  | c j => rw [isDone_c] at h ⊢; omega
  | w => rw [isDone_w] at h ⊢; omega
  | z => rw [isDone_z] at h ⊢; omega

/-- Marking the tables that complete gives the tables of the next state. -/
theorem mark_done (k d : Nat) (s : Slot) :
    (if completes k d s = true then { tab1 k d s with done := true } else tab1 k d s) =
      tab k (d + 1) s := by
  unfold completes tab1 tab
  cases h : isDone k d s
  · cases h' : isDone k (d + 1) s <;> simp
  · simp [isDone_mono k d s h]

theorem ts2_eq (k d : Nat) (R : List Nat)
    (hR : ∀ i (h : i < (slots k d).length), R.contains i = completes k d (slots k d)[i]) :
    (ts1 k d).mapIdx (fun i t => if R.contains i then { t with done := true } else t) =
      (slots k d).map (tab k (d + 1)) := by
  refine List.ext_getElem (by simp [ts1]) fun i h1 h2 => ?_
  have h : i < (slots k d).length := by simpa using h2
  simp only [List.getElem_mapIdx, ts1, List.getElem_map, hR i h]
  exact mark_done k d _

/-- A table created in a round is empty and open. -/
theorem new_tab (k d : Nat) {s : Slot} (hs : s ∈ newSlots k d) :
    (⟨goal k s, [], false⟩ : Table) = tab k (d + 1) s := by
  obtain ⟨h1, h2⟩ := mem_newSlots.1 hs
  have ha : ¬ hasAns k (d + 1) s = true := by
    cases s with
    | root => exact absurd trivial h2
    | c j => simp only [Slot.inAt] at h1 h2; rw [hasAns_c]; omega
    | w => simp
    | z => simp only [Slot.inAt] at h1 h2; rw [hasAns_z]; omega
  have hd : ¬ isDone k (d + 1) s = true := by
    cases s with
    | root => exact absurd trivial h2
    | c j => simp only [Slot.inAt] at h1 h2; rw [isDone_c]; omega
    | w => simp only [Slot.inAt] at h1 h2; rw [isDone_w]; omega
    | z => simp only [Slot.inAt] at h1 h2; rw [isDone_z]; omega
  simp only [tab, ans_of_not ha, Bool.not_eq_true] at hd ⊢
  rw [hd]

theorem ts3_eq (k d : Nat) (R : List Nat)
    (hR : ∀ i (h : i < (slots k d).length), R.contains i = completes k d (slots k d)[i]) :
    (ts1 k d).mapIdx (fun i t => if R.contains i then { t with done := true } else t) ++
        ((newSlots k d).map (goal k)).map (fun g => (⟨g, [], false⟩ : Table)) =
      tabs k (d + 1) := by
  rw [ts2_eq k d R hR, tabs, slots, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun s hs => new_tab k d hs

theorem slots_head (k : Nat) : ∀ d, ∃ l, slots k d = .root :: l
  | 0 => ⟨[], rfl⟩
  | d + 1 => by
    obtain ⟨l, hl⟩ := slots_head k d
    exact ⟨l ++ newSlots k d, by rw [slots, hl]; rfl⟩

/-- The answers the root gains in the round. -/
theorem rootNew_eq (k d : Nat) :
    (match (tabs k d).head?, (ts1 k d).head? with
      | some t, some t' => t'.answers.drop t.answers.length
      | _, _ => []) = emit k d := by
  obtain ⟨l, hl⟩ := slots_head k d
  simp only [tabs, ts1, hl, List.map_cons, List.head?_cons, tab, tab1, emit]
  by_cases h1 : hasAns k d .root = true
  · have h2 := hasAns_mono k d .root h1
    rw [ans_of_has h1, ans_of_has h2]
    rw [hasAns_root] at h1
    simp; omega
  · by_cases h2 : hasAns k (d + 1) .root = true
    · rw [ans_of_not h1, ans_of_has h2]
      rw [hasAns_root] at h1 h2
      simp; omega
    · rw [ans_of_not h1, ans_of_not h2]
      rw [hasAns_root] at h1 h2
      simp; omega

/-! ## The round -/

/-- What a round costs at most, by stage: the tick of the round, the oracle,
the candidates, the fresh answers, the keys of the goals asked for, the new
tables, and the completion check. -/
def roundBound (k d : Nat) : Nat :=
  let n := (slots k d).length
  1 + (n * (2 * d + k + 8) + (n * (12 * n + 6) + (n * 96 + (n * 6 + (36 * (n * n) +
    (n * (n * (24 * n + 12)) + 0))))))

theorem round_costs (k d : Nat) :
    Costs (Tabled.round onDemand (st k d)) (st k (d + 1), emit k d) (roundBound k d) := by
  obtain ⟨R, hR, hmem⟩ := completing_costs k d
  simp only [Tabled.round]
  unfold roundBound
  refine Costs.bind (Costs.tick 1) ?_
  refine Costs.bind (us_costs k d) ?_
  refine Costs.bind (outs_costs k d) ?_
  refine Costs.bind (ts1_costs k d) ?_
  refine Costs.bind (reqs_costs k d) ?_
  refine Costs.bind (newGoals_costs k d) ?_
  refine Costs.bind hR ?_
  refine Costs.congr_val (Costs.pure _) ?_
  have h3 := ts3_eq k d R hmem
  have hr := rootNew_eq k d
  simp only [ts1] at h3 hr
  simp only [st, h3, orient, Bool.false_eq_true, ↓reduceIte]
  exact congrArg (Prod.mk _) hr

end Sep

end R002

end RwLog
