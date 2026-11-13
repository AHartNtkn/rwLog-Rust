/-
# Tier 0 proofs, part 7: one round

The round is restated through named pieces: `outOf` is what a table computes,
`upd` the table with its fresh answers, `compl` the tables that complete and
`newGoalsOf` the tables the round creates. Then the tables after a round are
the old ones, updated in place, followed by the new ones.
-/
import RwLog.Rungs.R001.Proofs.Tier0.Cands

namespace RwLog

namespace R001

namespace Tier0

/-- What a table computes in a round: its candidates and the goals it reads. -/
def outOf (st : State) (t : Table) : List Span × List Goal :=
  if t.done then ([], []) else produce st.P st.depth st.tables t.goal

/-- A table with this round's fresh answers. -/
def upd (st : State) (t : Table) : Table :=
  { t with answers := t.answers ++ fresh t.answers (outOf st t).1 }

/-- The goals the tables read this round, as table keys. -/
def reqsOf (st : State) : List Goal :=
  ((st.tables.map (outOf st)).flatMap Prod.snd).map fun g => g.norm.2

/-- The tables this round creates. -/
def newGoalsOf (st : State) : List Goal :=
  (reqsOf st).foldl
    (fun acc g => if st.tables.any (fun t => t.goal.same g) || acc.any (fun h => h.same g) then acc
      else acc ++ [g]) []

/-- The tables that complete this round. -/
def compl (st : State) : List Nat := completing st.P st.depth st.tables (st.tables.map (upd st))

/-- An old table after the round. -/
def after (st : State) (i : Nat) (t : Table) : Table :=
  if (compl st).contains i then { upd st t with done := true } else upd st t

theorem round_tables (st : State) :
    (round st).1.tables = (st.tables.mapIdx (after st)) ++ (newGoalsOf st).map fun g => ⟨g, [], false⟩ := by
  simp only [round, map_zip_map_self]
  congr 1
  rw [List.mapIdx_eq_iff]
  intro i
  simp only [List.getElem?_mapIdx, List.getElem?_map]
  cases st.tables[i]? <;> rfl

theorem after_goal (st : State) (i : Nat) (t : Table) : (after st i t).goal = t.goal := by
  unfold after; split <;> rfl

theorem after_answers (st : State) (i : Nat) (t : Table) :
    (after st i t).answers = t.answers ++ fresh t.answers (outOf st t).1 := by
  unfold after; split <;> rfl

theorem after_done (st : State) (i : Nat) (t : Table) :
    (after st i t).done = (t.done || (compl st).contains i) := by
  unfold after; split <;> simp_all [upd]

theorem outOf_done {st : State} {t : Table} (h : t.done = true) : outOf st t = ([], []) := by
  simp [outOf, h]

theorem outOf_not_done {st : State} {t : Table} (h : t.done = false) :
    outOf st t = produce st.P st.depth st.tables t.goal := by
  simp [outOf, h]

/-- Every table after a round is an old table updated in place, or a new
table. -/
theorem mem_round {st : State} {t' : Table} (h : t' ∈ (round st).1.tables) :
    (∃ i, ∃ hi : i < st.tables.length, t' = after st i st.tables[i]) ∨
      ∃ g ∈ newGoalsOf st, t' = ⟨g, [], false⟩ := by
  rw [round_tables, List.mem_append] at h
  rcases h with h | h
  · left
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
    rw [List.length_mapIdx] at hi
    exact ⟨i, hi, by simp⟩
  · right
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h
    exact ⟨g, hg, rfl⟩

theorem round_getElem (st : State) (i : Nat) (hi : i < st.tables.length) :
    (round st).1.tables[i]? = some (after st i st.tables[i]) := by
  rw [round_tables, List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem round_length (st : State) : st.tables.length ≤ (round st).1.tables.length := by
  rw [round_tables]; simp

theorem round_goals (st : State) :
    (round st).1.tables.map TableOf.goal = st.tables.map TableOf.goal ++ newGoalsOf st := by
  rw [round_tables, List.map_append, List.map_map]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro i h₁ _; simp [after_goal]
  · simp [Function.comp_def]

/-! ## The tables a round creates -/

theorem foldl_new_mem (P : Goal → List Goal → Bool) :
    ∀ (l acc : List Goal) {g : Goal},
      g ∈ l.foldl (fun acc g => if P g acc then acc else acc ++ [g]) acc → g ∈ acc ∨ g ∈ l
  | [], _, _, h => .inl h
  | x :: l, acc, g, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_new_mem P l _ h with h | h
    · split at h
      · exact .inl h
      · rcases List.mem_append.1 h with h | h
        · exact .inl h
        · exact .inr (by simp_all)
    · exact .inr (List.mem_cons_of_mem _ h)

theorem foldl_new_sup (P : Goal → List Goal → Bool) :
    ∀ (l acc : List Goal), ∀ g ∈ acc,
      g ∈ l.foldl (fun acc g => if P g acc then acc else acc ++ [g]) acc
  | [], _, _, h => h
  | x :: l, acc, g, h => by
    simp only [List.foldl_cons]
    apply foldl_new_sup P l
    split
    · exact h
    · exact List.mem_append_left _ h

theorem foldl_new_cover (p : Goal → Bool) (q : Goal → Goal → Bool) (hq : ∀ g, q g g = true) :
    ∀ (l acc : List Goal), ∀ g ∈ l,
      p g = true ∨ ∃ h ∈ l.foldl (fun acc g => if p g || acc.any (fun h => q h g) then acc
        else acc ++ [g]) acc, q h g = true
  | [], _, _, h => by simp at h
  | x :: l, acc, g, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · by_cases hp : p g = true
      · exact .inl hp
      · right
        have : ∃ h ∈ (if p g || acc.any (fun h => q h g) then acc else acc ++ [g]), q h g = true := by
          split
          · rename_i hc
            simp only [hp, Bool.false_or, List.any_eq_true] at hc
            exact hc
          · exact ⟨g, List.mem_append_right _ (List.mem_singleton_self g), hq g⟩
        obtain ⟨h, hm, hh⟩ := this
        exact ⟨h, foldl_new_sup _ l _ h hm, hh⟩
    · exact foldl_new_cover p q hq l _ g h

/-- Every goal the round reads has a table afterwards: an old one or a new
one. -/
theorem reqs_covered {st : State} {g : Goal} (h : g ∈ reqsOf st) :
    (∃ t ∈ st.tables, t.goal.same g = true) ∨ ∃ h ∈ newGoalsOf st, h.same g = true := by
  rcases foldl_new_cover (fun g => st.tables.any fun t => t.goal.same g) GoalOf.same GoalOf.same_refl
    (reqsOf st) [] g h with h | h
  · exact .inl (List.any_eq_true.1 h)
  · exact .inr h

theorem mem_newGoals {st : State} {g : Goal} (h : g ∈ newGoalsOf st) : g ∈ reqsOf st := by
  rcases foldl_new_mem _ _ [] h with h | h
  · simp at h
  · exact h

theorem mem_reqs {st : State} {g : Goal} (h : g ∈ reqsOf st) :
    ∃ t ∈ st.tables, t.done = false ∧ ∃ d ∈ (produce st.P st.depth st.tables t.goal).2, g = d.norm.2 := by
  simp only [reqsOf, List.mem_map, List.mem_flatMap] at h
  obtain ⟨d, ⟨_, ⟨t, ht, rfl⟩, hd⟩, rfl⟩ := h
  cases hdn : t.done
  · rw [outOf_not_done hdn] at hd; exact ⟨t, ht, hdn, d, hd, rfl⟩
  · rw [outOf_done hdn] at hd; simp at hd

/-! ## Finding tables -/

theorem indexOf_find {ts : Tables} {g : Goal} {j : Nat} (h : indexOf ts g = some j) :
    ∃ hj : j < ts.length, findTable ts g = some ts[j] ∧ ts[j].goal.same g = true := by
  obtain ⟨hj, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  refine ⟨hj, ?_, hp⟩
  have h2 := (List.findIdx?_eq_some_iff_findIdx_eq.1 h).2
  unfold findTable
  rw [List.find?_eq_getElem?_findIdx, h2, List.getElem?_eq_getElem hj]

theorem find_indexOf {ts : Tables} {g : Goal} {t : Table} (h : findTable ts g = some t) :
    ∃ j, indexOf ts g = some j ∧ ∃ hj : j < ts.length, ts[j] = t := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  have hlt : ts.findIdx (fun t => t.goal.same g) < ts.length :=
    List.findIdx_lt_length_of_exists ⟨t, hm, hp⟩
  refine ⟨_, List.findIdx?_eq_some_iff_findIdx_eq.2 ⟨hlt, rfl⟩, hlt, ?_⟩
  unfold findTable at h
  rw [List.find?_eq_getElem?_findIdx, List.getElem?_eq_getElem hlt] at h
  exact Option.some.inj h

theorem findTable_isSome {ts : Tables} {g : Goal} :
    (findTable ts g).isSome ↔ ∃ t ∈ ts, t.goal.same g = true := by
  unfold findTable
  rw [List.find?_isSome]

theorem indexOf_eq_goals (ts : Tables) (g : Goal) :
    indexOf ts g = (ts.map TableOf.goal).findIdx? fun h => h.same g := by
  unfold indexOf
  rw [List.findIdx?_map]
  rfl

/-- A table found before a round is found at the same place after it. -/
theorem indexOf_round {st : State} {g : Goal} {j : Nat} (h : indexOf st.tables g = some j) :
    indexOf (round st).1.tables g = some j := by
  rw [indexOf_eq_goals, round_goals, List.findIdx?_append, ← indexOf_eq_goals, h]
  rfl

theorem findTable_round {st : State} {g : Goal} {t : Table} (h : findTable st.tables g = some t) :
    ∃ j, ∃ hj : j < st.tables.length, st.tables[j] = t ∧
      findTable (round st).1.tables g = some (after st j t) := by
  obtain ⟨j, hj, hjl, rfl⟩ := find_indexOf h
  obtain ⟨hj', hf, -⟩ := indexOf_find (indexOf_round hj)
  refine ⟨j, hjl, rfl, ?_⟩
  rw [hf]
  have := round_getElem st j hjl
  rw [List.getElem?_eq_getElem hj'] at this
  exact congrArg some (Option.some.inj this)

/-- Every goal a round reads has a table after the round. -/
theorem reqs_found {st : State} {g : Goal} (h : g ∈ reqsOf st) :
    (findTable (round st).1.tables g).isSome := by
  rw [findTable_isSome]
  rcases reqs_covered h with ⟨t, ht, hs⟩ | ⟨h, hh, hs⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
    refine ⟨after st i st.tables[i], ?_, by rw [after_goal]; exact hs⟩
    have := round_getElem st i hi
    exact List.mem_of_getElem? this
  · refine ⟨⟨h, [], false⟩, ?_, hs⟩
    rw [round_tables]
    exact List.mem_append_right _ (List.mem_map_of_mem hh)

/-! ## Completion -/

/-- A table that completes in a round was incomplete, gained nothing, and has
a strategy each of whose goals has a table that gained nothing and is
complete or completes too. -/
theorem mem_compl {st : State} {i : Nat} (h : i ∈ compl st) :
    ∃ hi : i < st.tables.length, st.tables[i].done = false ∧
      (upd st st.tables[i]).answers.length = st.tables[i].answers.length ∧
      ∃ deps ∈ strategies st.P st.depth st.tables st.tables[i].goal, ∀ d ∈ deps,
        ∃ j, indexOf st.tables d.norm.2 = some j ∧ ∃ hj : j < st.tables.length,
          (upd st st.tables[j]).answers.length = st.tables[j].answers.length ∧
          (st.tables[j].done = true ∨ j ∈ compl st) := by
  unfold compl completing at h
  simp only at h
  obtain ⟨h0, hok⟩ := gfpFrom_closed _ _ _ le_rfl i h
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, Decidable.not_not] at h0
  obtain ⟨hi, hd, hg⟩ := h0
  refine ⟨hi, ?_, ?_, ?_⟩
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hd
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_map] using hg
  · obtain ⟨deps, hdeps, hall⟩ := List.any_eq_true.1 hok
    refine ⟨deps, by simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hdeps,
      fun d hd => ?_⟩
    have hx := List.all_eq_true.1 hall d hd
    revert hx
    cases hj : indexOf st.tables d.norm.2 with
    | none => simp
    | some j =>
      intro hx
      obtain ⟨hjl, -, -⟩ := indexOf_find hj
      rw [Bool.and_eq_true] at hx
      obtain ⟨hg, hdn⟩ := hx
      rw [Bool.or_eq_true] at hdn
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
        Decidable.not_not, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl,
        List.getElem?_map, Option.map_some, Option.getD_some] at hg
      refine ⟨j, rfl, hjl, hg, ?_⟩
      rcases hdn with hdn | hdn
      · left; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl] using hdn
      · exact .inr (List.contains_iff_mem.1 hdn)

end Tier0

end R001

end RwLog
