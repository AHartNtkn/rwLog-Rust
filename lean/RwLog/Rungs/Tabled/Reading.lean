/-
# A round of the tabled machine, read goal by goal

What the tables hold after a round, in terms of the goal of a table and not
of its position: which goals have a table (`idx_next_cases`, `idx_next_new`),
what the table of a goal holds (`ansOf_next`), which candidates enter a table
(`fresh_max`, `fresh_of_max`) and which answers are maximal (`maxima_max`,
`maxima_of_max`), and that every set of tables closed under the condition of
completion completes (`closing_of_closed`).

No two tables have the same goal (`GoalsNodup`, `nodup_next`).
-/
import RwLog.Rungs.Tabled.Invariant

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## No two tables have the same goal -/

/-- No two tables have the same goal. -/
def GoalsNodup (ts : List (TableOf R Rel (Ans D P))) : Prop := (ts.map (·.goal)).Nodup

omit [Answer R] in
theorem nodup_addG {acc : List (GoalOf R Rel)} (h : acc.Nodup) (p : GoalOf R Rel × Option Nat) :
    (addG acc p).Nodup := by
  obtain ⟨d, o⟩ := p
  cases o with
  | some j => exact h
  | none =>
    simp only [addG]
    split
    · exact h
    · next hn =>
      refine List.nodup_append.2 ⟨h, List.nodup_singleton _, fun a ha c hc => ?_⟩
      obtain rfl : c = d := by simpa using hc
      rintro rfl
      exact hn (List.any_eq_true.2 ⟨a, ha, by simp⟩)

omit [Answer R] in
theorem nodup_foldl_addG : ∀ (l : List (GoalOf R Rel × Option Nat)) (acc : List (GoalOf R Rel)),
    acc.Nodup → (l.foldl addG acc).Nodup
  | [], _, h => h
  | p :: l, _, h => nodup_foldl_addG l _ (nodup_addG h p)

section

variable {ts : List (TableOf R Rel (Ans D P))} {g : GoalOf R Rel}

theorem idx_getElem (h : GoalsNodup ts) {i : Nat} (hi : i < ts.length) :
    idx ts ts[i].goal = some i := by
  refine idx_some.2 ⟨hi, rfl, fun j hj e => ?_⟩
  have hj' : j < (ts.map (·.goal)).length := by simp; omega
  have hi' : i < (ts.map (·.goal)).length := by simpa using hi
  have := (List.Nodup.getElem_inj_iff h (hi := hj') (hj := hi')).1 (by simpa using e)
  omega

theorem idx_of_mem (h : GoalsNodup ts) {t : TableOf R Rel (Ans D P)} (ht : t ∈ ts) :
    ∃ i, ∃ hi : i < ts.length, idx ts t.goal = some i ∧ ts[i] = t := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  exact ⟨i, hi, idx_getElem h hi, rfl⟩

theorem idx_isSome : (∃ i, idx ts g = some i) ↔ ∃ t ∈ ts, t.goal = g := by
  constructor
  · rintro ⟨i, h⟩
    obtain ⟨hi, hg, -⟩ := idx_some.1 h
    exact ⟨_, List.getElem_mem hi, hg⟩
  · rintro ⟨t, ht, hg⟩
    cases h : idx ts g with
    | some i => exact ⟨i, rfl⟩
    | none => exact absurd hg (idx_none.1 h t ht)

theorem lookup_none (h : idx ts g = none) : lookup ts g = none := by
  unfold lookup
  rw [List.find?_eq_none]
  intro t ht
  simpa using idx_none.1 h t ht

theorem ansOf_none (h : idx ts g = none) : ansOf ts g = [] := by
  unfold ansOf; rw [lookup_none h]

theorem isDone_none (h : idx ts g = none) : isDone ts g = false := by
  unfold isDone; rw [lookup_none h]

/-- A goal with an answer has a table. -/
theorem idx_of_ans {a : Ans D P} (h : a ∈ ansOf ts g) : ∃ i, idx ts g = some i := by
  cases hi : idx ts g with
  | some i => exact ⟨i, rfl⟩
  | none => rw [ansOf_none hi] at h; cases h

/-- A complete goal has a table. -/
theorem idx_of_done (h : isDone ts g = true) : ∃ i, idx ts g = some i := by
  cases hi : idx ts g with
  | some i => exact ⟨i, rfl⟩
  | none => rw [isDone_none hi] at h; cases h

end

variable (K : Kernel R Cost) (hK : K.Refines D) (U : GOracle R Rel (Ans D P) Cost)
  (ts : List (TableOf R Rel (Ans D P))) (depth : Nat)

theorem nodup_newGoals : (newGoals K hK U ts depth).Nodup :=
  nodup_foldl_addG _ _ List.nodup_nil

theorem next_goals :
    (nextTables K hK U ts depth).map (·.goal) =
      ts.map (·.goal) ++ newGoals K hK U ts depth := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < ts.length
  · rw [List.getElem?_map, next_getElem? hi,
      List.getElem?_append_left (by simpa using hi)]
    simp [List.getElem?_eq_getElem hi]
  · have hle : ts.length ≤ i := Nat.le_of_not_lt hi
    unfold nextTables
    rw [List.map_append, List.getElem?_append_right (by simpa using hle),
      List.getElem?_append_right (by simpa using hle)]
    simp [List.map_map, Function.comp_def]

variable {K hK U ts depth}

theorem nodup_next (h : GoalsNodup ts) : GoalsNodup (nextTables K hK U ts depth) := by
  unfold GoalsNodup
  rw [next_goals]
  refine List.nodup_append.2 ⟨h, nodup_newGoals K hK U ts depth, fun a ha c hc => ?_⟩
  rintro rfl
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
  obtain ⟨-, -, -, -, -, hn⟩ := (mem_newGoals K hK U ts depth _).1 hc
  exact idx_none.1 hn t ht rfl

/-! ## The table of a goal after a round -/

/-- A goal with a table after the round had one, or got one in the round. -/
theorem idx_next_cases {g : GoalOf R Rel} {j : Nat}
    (h : idx (nextTables K hK U ts depth) g = some j) :
    (∃ i, idx ts g = some i) ∨ (idx ts g = none ∧ g ∈ newGoals K hK U ts depth) := by
  cases hi : idx ts g with
  | some i => exact .inl ⟨i, rfl⟩
  | none =>
    refine .inr ⟨rfl, ?_⟩
    obtain ⟨t', ht', hg⟩ := idx_isSome.1 ⟨j, h⟩
    rcases mem_next.1 ht' with ⟨i, hi', rfl⟩ | ⟨g', hg', rfl⟩
    · exact absurd hg (idx_none.1 hi ts[i] (List.getElem_mem hi'))
    · exact hg ▸ hg'

/-- A goal that gets a table in the round: the table is empty and
incomplete. -/
theorem idx_next_new {g : GoalOf R Rel} (h : idx ts g = none)
    (hg : g ∈ newGoals K hK U ts depth) :
    (∃ j, idx (nextTables K hK U ts depth) g = some j) ∧
      ansOf (nextTables K hK U ts depth) g = [] ∧
      isDone (nextTables K hK U ts depth) g = false := by
  have hex : ∃ j, idx (nextTables K hK U ts depth) g = some j :=
    idx_isSome.2 ⟨⟨g, [], false⟩, mem_next.2 (.inr ⟨g, hg, rfl⟩), rfl⟩
  refine ⟨hex, ?_⟩
  obtain ⟨j, hj⟩ := hex
  obtain ⟨hjl, hl⟩ := lookup_of_idx hj
  have hmem := List.getElem_mem hjl
  obtain ⟨_, hgoal, -⟩ := idx_some.1 hj
  rcases mem_next.1 hmem with ⟨i, hi', e⟩ | ⟨g', hg', e⟩
  · rw [e] at hgoal
    exact absurd hgoal (idx_none.1 h ts[i] (List.getElem_mem hi'))
  · unfold ansOf isDone
    rw [hl, e]
    exact ⟨rfl, rfl⟩

/-- The table of a goal that had one, after the round. -/
theorem ansOf_next {g : GoalOf R Rel} {i : Nat} (h : idx ts g = some i) :
    ∃ hi : i < ts.length,
      ansOf (nextTables K hK U ts depth) g = ts[i].answers ++ gainOf K hK U ts depth ts[i] ∧
      isDone (nextTables K hK U ts depth) g =
        (ts[i].done || (closing K hK U ts depth).contains i) := by
  obtain ⟨hi, -, -⟩ := idx_some.1 h
  obtain ⟨hi', e⟩ := next_getElem (K := K) (hK := hK) (U := U) (depth := depth) hi
  have hn := next_idx (K := K) (hK := hK) (U := U) (depth := depth) h
  obtain ⟨_, ea⟩ := ansOf_of_idx hn
  obtain ⟨_, ed⟩ := isDone_of_idx hn
  exact ⟨hi, by rw [ea, e], by rw [ed, e]⟩

/-! ## What a table computes, by its goal -/

variable (K hK U ts depth)

/-- The candidates and the strategies of an incomplete table, by its goal. -/
def prodG (g : GoalOf R Rel) : List (Ans D P) × List (List (GoalOf R Rel)) :=
  (produce (K := DerivationKernel.over D K hK P) ts g (U depth g).val).val

theorem outOf_live {t : TableOf R Rel (Ans D P)} (h : t.done = false) :
    outOf K hK U ts depth t = prodG K hK U ts depth t.goal := by
  unfold outOf askOf prodG
  simp [h]

theorem outOf_done {t : TableOf R Rel (Ans D P)} (h : t.done = true) :
    outOf K hK U ts depth t = ([], []) := by
  unfold outOf
  simp [h]

theorem mem_prodG_fst (g : GoalOf R Rel) (c : Ans D P) :
    c ∈ (prodG K hK U ts depth g).1 ↔
      c ∈ (U depth g).val.2 ∨
        c ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1 := by
  unfold prodG
  rw [produce_val]
  exact List.mem_append

theorem mem_prodG_snd (g : GoalOf R Rel) (strat : List (GoalOf R Rel)) :
    strat ∈ (prodG K hK U ts depth g).2 ↔
      ((U depth g).val.1 = true ∧ strat = []) ∨
        strat ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.2 := by
  unfold prodG
  rw [produce_val]
  simp only [List.mem_append]
  refine or_congr ?_ Iff.rfl
  cases (U depth g).val.1 <;> simp

/-- A complete table gains nothing. -/
theorem gain_done {t : TableOf R Rel (Ans D P)} (h : t.done = true) :
    gainOf K hK U ts depth t = [] := by
  unfold gainOf
  rw [outOf_done K hK U ts depth h, fresh_val]
  rfl

/-! ## Which candidates enter a table -/

variable {K hK}

omit [DecidableEq R] in
/-- A maximal answer covers every answer that covers it. -/
theorem maxima_max {xs : List (Ans D P)} {x y : Ans D P} (h : x ∈ xs.maximaBy (covB D P))
    (hy : y ∈ xs) (hyx : covB D P y x = true) : covB D P x y = true :=
  (List.mem_tops.1 (List.mem_thin h)).2 y hy hyx

omit [DecidableEq R] in
/-- An answer that covers every answer that covers it has the representative
of a maximal answer. -/
theorem maxima_of_max (hL : D.Lawful P.sorts.interp) {xs : List (Ans D P)} {c : Ans D P}
    (hc : c ∈ xs) (hmax : ∀ y ∈ xs, covB D P y c = true → covB D P c y = true) :
    ∃ z ∈ xs.maximaBy (covB D P), z.span = c.span := by
  obtain ⟨z, hz, hzc⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) hc
  exact ⟨z, hz, hL.covers_antisymm hzc (hmax z (List.mem_maximaBy hz) hzc)⟩

/-- An answer that enters a table covers every candidate that covers it and
that no answer of the table covers. -/
theorem fresh_max {old cands : List (Ans D P)} {a c : Ans D P}
    (h : a ∈ (fresh (K := DerivationKernel.over D K hK P) old cands).val) (hc : c ∈ cands)
    (hco : ∀ t ∈ old, covB D P t c = false) (hca : covB D P c a = true) :
    covB D P a c = true := by
  rw [fresh_val] at h
  refine maxima_max h (List.mem_filter.2 ⟨hc, ?_⟩) hca
  simpa using hco

/-- A candidate that no answer of the table covers, and that covers every
such candidate that covers it, has the representative of an answer that
enters the table. -/
theorem fresh_of_max (hL : D.Lawful P.sorts.interp) {old cands : List (Ans D P)} {c : Ans D P}
    (hc : c ∈ cands) (hco : ∀ t ∈ old, covB D P t c = false)
    (hmax : ∀ c₂ ∈ cands, (∀ t ∈ old, covB D P t c₂ = false) → covB D P c₂ c = true →
      covB D P c c₂ = true) :
    ∃ a ∈ (fresh (K := DerivationKernel.over D K hK P) old cands).val, a.span = c.span := by
  rw [fresh_val]
  refine maxima_of_max hL (List.mem_filter.2 ⟨hc, by simpa using hco⟩) fun y hy hyc => ?_
  obtain ⟨hy₁, hy₂⟩ := List.mem_filter.1 hy
  exact hmax y hy₁ (by simpa using hy₂) hyc

/-! ## Tables that complete -/

variable {U ts depth}

/-- Every set of incomplete tables that gained nothing and each have a
strategy all of whose goals have a table that was complete or is in the set,
completes. -/
theorem closing_of_closed (S : List Nat)
    (hS : ∀ i ∈ S, ∃ hi : i < ts.length, ts[i].done = false ∧
      gainOf K hK U ts depth ts[i] = [] ∧
      ∃ strat ∈ (outOf K hK U ts depth ts[i]).2, ∀ d ∈ strat, ∃ j, idx ts d = some j ∧
        ((∃ hj : j < ts.length, ts[j].done = true) ∨ j ∈ S)) :
    ∀ i ∈ S, i ∈ closing K hK U ts depth := by
  have hgain : ∀ j, ((∃ hj : j < ts.length, ts[j].done = true) ∨ j ∈ S) →
      (gainedOf K hK U ts depth).getD j true = false := by
    intro j hj
    have key : ∃ hj : j < ts.length, gainOf K hK U ts depth ts[j] = [] := by
      rcases hj with ⟨hjl, hd⟩ | hjS
      · exact ⟨hjl, gain_done K hK U ts depth hd⟩
      · obtain ⟨hjl, -, hg, -⟩ := hS j hjS
        exact ⟨hjl, hg⟩
    obtain ⟨hjl, hg⟩ := key
    simp [gainedOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, grow, hg]
  unfold closing completing
  dsimp only
  refine subset_gfpFrom ?_ S ?_ _ _ ?_
  · intro S₁ S₂ hsub i hok
    obtain ⟨strat, hs, hall⟩ := List.any_eq_true.1 hok
    refine List.any_eq_true.2 ⟨strat, hs, List.all_eq_true.2 fun o ho => ?_⟩
    have := List.all_eq_true.1 hall o ho
    cases o with
    | none => exact this
    | some j =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at this ⊢
      exact ⟨this.1, this.2.imp id (hsub j)⟩
  · intro i hi
    obtain ⟨hil, -, -, strat, hs, hdeps⟩ := hS i hi
    refine List.any_eq_true.2 ⟨strat.map (idx ts), ?_, List.all_eq_true.2 fun o ho => ?_⟩
    · simp only [reqsOf, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hil, Option.map_some, Option.getD_some, List.map_map,
        List.mem_map, Function.comp_def]
      exact ⟨strat, hs, rfl⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ho
      obtain ⟨j, hj, hc⟩ := hdeps d hd
      rw [hj]
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_eq_eq_not,
        Bool.not_true]
      refine ⟨hgain j hc, hc.imp (fun ⟨hjl, hd⟩ => ?_) id⟩
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, hd]
  · intro i hi
    obtain ⟨hil, hd, -, -⟩ := hS i hi
    simp only [List.mem_filter, List.mem_range, List.length_map, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨hil, ?_, hgain i (.inr hi)⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, hd]

end Tabled

end RwLog
