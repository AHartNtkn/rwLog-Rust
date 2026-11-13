/-
# What a round of the tabled machine does

The tables after a round, read off the text of `Tabled.round`
(`round_val`): what each incomplete table is told by the unfolding race
(`askOf`), its candidates and strategies (`outOf`), the table with the
answers that enter it (`grow`), the goals that get a table (`newGoals`) and
the tables that complete (`closing`).
-/
import RwLog.Rungs.Tabled.Strategies

namespace RwLog

namespace Tabled

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

omit [Answer R] [DecidableEq R] in
theorem zip_map_self {α β : Type} (f : α → β) :
    ∀ l : List α, l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp [zip_map_self f l]

theorem ite_val {α : Type} (c : Prop) [Decidable c] (a b : Cost α) :
    (if c then a else b).val = if c then a.val else b.val := by
  split <;> rfl

/-- Add a goal unless it has a table or is already there. -/
def addG (acc : List (GoalOf R Rel)) (p : GoalOf R Rel × Option Nat) : List (GoalOf R Rel) :=
  match p.2 with
  | some _ => acc
  | none => if acc.any fun h => decide (h = p.1) then acc else acc ++ [p.1]

variable (K : Kernel R Cost) (hK : K.Refines D)

theorem addGoal_val (acc : List (GoalOf R Rel)) (p : GoalOf R Rel × Option Nat) :
    (addGoal (K := DerivationKernel.over D K hK P) acc p).val = addG acc p := by
  have hs := fun h : GoalOf R Rel => same_val (P := P) K hK h p.1
  at_cost K hK
  obtain ⟨g, i⟩ := p
  cases i <;> simp [addGoal, addG, anyL_std, hs]

variable (U : GOracle R Rel (Ans D P) Cost) (ts : List (TableOf R Rel (Ans D P))) (depth : Nat)

/-- What the unfolding race says of a table in the round. -/
def askOf (t : TableOf R Rel (Ans D P)) : Bool × List (Ans D P) :=
  if t.done then (false, []) else (U depth t.goal).val

/-- The candidates and the strategies of a table in the round. -/
def outOf (t : TableOf R Rel (Ans D P)) : List (Ans D P) × List (List (GoalOf R Rel)) :=
  if t.done then ([], [])
  else (produce (K := DerivationKernel.over D K hK P) ts t.goal (askOf U depth t)).val

/-- The answers that enter a table in the round. -/
def gainOf (t : TableOf R Rel (Ans D P)) : List (Ans D P) :=
  (fresh (K := DerivationKernel.over D K hK P) t.answers (outOf K hK U ts depth t).1).val

/-- A table with the answers that enter it in the round. -/
def grow (t : TableOf R Rel (Ans D P)) : TableOf R Rel (Ans D P) :=
  { t with answers := t.answers ++ gainOf K hK U ts depth t }

/-- The position of the table of a goal. -/
def idx (ts : List (TableOf R Rel (Ans D P))) (d : GoalOf R Rel) : Option Nat :=
  ts.findIdx? fun t => decide (t.goal = d)

/-- The goals the strategies of each table depend on, with the positions of
their tables. -/
def reqsOf : List (List (List (GoalOf R Rel × Option Nat))) :=
  ts.map fun t => (outOf K hK U ts depth t).2.map fun strat => strat.map fun d => (d, idx ts d)

/-- The goals that get a table in the round. -/
def newGoals : List (GoalOf R Rel) :=
  (reqsOf K hK U ts depth).flatten.flatten.foldl addG []

/-- Which tables gained an answer in the round. -/
def gainedOf : List Bool :=
  ts.map fun t => decide ((grow K hK U ts depth t).answers.length ≠ t.answers.length)

/-- The tables that complete in the round. -/
def closing : List Nat :=
  completing (ts.map (·.done)) (gainedOf K hK U ts depth)
    ((reqsOf K hK U ts depth).map fun o => o.map fun s => s.map Prod.snd)

/-- The tables after the round. -/
def nextTables : List (TableOf R Rel (Ans D P)) :=
  ((ts.map (grow K hK U ts depth)).mapIdx fun i t =>
      if (closing K hK U ts depth).contains i then { t with done := true } else t) ++
    (newGoals K hK U ts depth).map fun g => ⟨g, [], false⟩

/-- The answers the root table gains in the round. -/
def rootGain : List (Ans D P) :=
  match ts.head?, (ts.map (grow K hK U ts depth)).head? with
  | some t, some t' => t'.answers.drop t.answers.length
  | _, _ => []

/-- A round. -/
theorem round_val (st : StateOf R Rel (Ans D P)) :
    (round (K := DerivationKernel.over D K hK P) U st).val =
      (⟨nextTables K hK U st.tables st.depth, st.depth + 1⟩, rootGain K hK U st.tables st.depth) := by
  have ea := fun acc p => addGoal_val (P := P) K hK acc p
  have ei := indexOf_val (P := P) K hK st.tables
  unfold nextTables rootGain closing gainedOf newGoals reqsOf grow gainOf outOf askOf idx
  at_cost K hK
  simp only [round, Cost.bind_val, mapL_std, Cost.mapL_val, Cost.pure_val, foldL_std,
    Cost.foldL_val, ea, ei, ite_val, zip_map_self, List.map_map, Function.comp_def]
  congr!
  funext motive a b h₁ h₂
  cases a <;> cases b <;> rfl

/-! ## Positions of tables -/

section idx

variable {ts : List (TableOf R Rel (Ans D P))} {g : GoalOf R Rel} {i : Nat}

theorem idx_some : idx ts g = some i ↔
    ∃ h : i < ts.length, ts[i].goal = g ∧ ∀ j (hj : j < i), ts[j].goal ≠ g := by
  unfold idx
  rw [List.findIdx?_eq_some_iff_getElem]
  simp

theorem idx_none : idx ts g = none ↔ ∀ t ∈ ts, t.goal ≠ g := by
  simp [idx, List.findIdx?_eq_none_iff]

theorem lookup_of_idx (h : idx ts g = some i) : ∃ hi : i < ts.length, lookup ts g = some ts[i] := by
  obtain ⟨hi, hg, hlt⟩ := idx_some.1 h
  refine ⟨hi, ?_⟩
  unfold lookup
  rw [List.find?_eq_some_iff_getElem]
  exact ⟨by simpa using hg, i, hi, rfl, fun j hj => by simpa using hlt j hj⟩

theorem ansOf_of_idx (h : idx ts g = some i) : ∃ hi : i < ts.length, ansOf ts g = ts[i].answers := by
  obtain ⟨hi, hl⟩ := lookup_of_idx h
  exact ⟨hi, by unfold ansOf; rw [hl]⟩

theorem isDone_of_idx (h : idx ts g = some i) : ∃ hi : i < ts.length, isDone ts g = ts[i].done := by
  obtain ⟨hi, hl⟩ := lookup_of_idx h
  exact ⟨hi, by unfold isDone; rw [hl]⟩

end idx

/-! ## The tables after a round -/

section next

variable {K hK U ts depth}

theorem next_getElem? {i : Nat} (hi : i < ts.length) :
    (nextTables K hK U ts depth)[i]? =
      some ⟨ts[i].goal, ts[i].answers ++ gainOf K hK U ts depth ts[i],
        ts[i].done || (closing K hK U ts depth).contains i⟩ := by
  unfold nextTables
  rw [List.getElem?_append_left (by simpa using hi)]
  simp only [List.getElem?_mapIdx, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    grow]
  cases (closing K hK U ts depth).contains i <;> simp

theorem next_length :
    (nextTables K hK U ts depth).length = ts.length + (newGoals K hK U ts depth).length := by
  simp [nextTables]

theorem next_getElem {i : Nat} (hi : i < ts.length) :
    ∃ h : i < (nextTables K hK U ts depth).length,
      (nextTables K hK U ts depth)[i] =
        ⟨ts[i].goal, ts[i].answers ++ gainOf K hK U ts depth ts[i],
          ts[i].done || (closing K hK U ts depth).contains i⟩ := by
  obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.1 (next_getElem? (K := K) (hK := hK) (U := U)
    (depth := depth) hi)
  exact ⟨h, e⟩

theorem mem_next {t' : TableOf R Rel (Ans D P)} :
    t' ∈ nextTables K hK U ts depth ↔
      (∃ i, ∃ hi : i < ts.length, t' = ⟨ts[i].goal, ts[i].answers ++ gainOf K hK U ts depth ts[i],
        ts[i].done || (closing K hK U ts depth).contains i⟩) ∨
      ∃ g ∈ newGoals K hK U ts depth, t' = ⟨g, [], false⟩ := by
  constructor
  · intro h
    obtain ⟨i, e⟩ := List.getElem?_of_mem h
    by_cases hlt : i < ts.length
    · rw [next_getElem? hlt] at e
      exact .inl ⟨i, hlt, (Option.some.inj e).symm⟩
    · right
      unfold nextTables at e
      rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hlt)] at e
      obtain ⟨g, hg, e'⟩ := List.mem_map.1 (List.mem_of_getElem? e)
      exact ⟨g, hg, e'.symm⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩)
    · exact List.mem_of_getElem? (next_getElem? hi)
    · unfold nextTables
      exact List.mem_append_right _ (List.mem_map_of_mem hg)

/-- A goal keeps the position of its table. -/
theorem next_idx {g : GoalOf R Rel} {i : Nat} (h : idx ts g = some i) :
    idx (nextTables K hK U ts depth) g = some i := by
  obtain ⟨hi, hg, hlt⟩ := idx_some.1 h
  obtain ⟨hi', e⟩ := next_getElem (K := K) (hK := hK) (U := U) (depth := depth) hi
  refine idx_some.2 ⟨hi', by rw [e]; exact hg, fun j hj => ?_⟩
  obtain ⟨_, e'⟩ := next_getElem (K := K) (hK := hK) (U := U) (depth := depth) (Nat.lt_trans hj hi)
  rw [e']; exact hlt j hj

end next

/-! ## The goals that get a table -/

omit [Answer R] in
theorem mem_addG (acc : List (GoalOf R Rel)) (p : GoalOf R Rel × Option Nat) (g : GoalOf R Rel) :
    g ∈ addG acc p ↔ g ∈ acc ∨ (p.1 = g ∧ p.2 = none) := by
  obtain ⟨d, o⟩ := p
  cases o with
  | some j => simp [addG]
  | none =>
    simp only [addG, and_true]
    split
    · next h =>
      obtain ⟨x, hx, e⟩ := List.any_eq_true.1 h
      have : d ∈ acc := by rw [← of_decide_eq_true e]; exact hx
      constructor
      · exact .inl
      · rintro (h | rfl) <;> assumption
    · simp [eq_comm]

omit [Answer R] in
theorem mem_foldl_addG : ∀ (l : List (GoalOf R Rel × Option Nat)) (acc : List (GoalOf R Rel))
    (g : GoalOf R Rel), g ∈ l.foldl addG acc ↔ g ∈ acc ∨ ∃ p ∈ l, p.1 = g ∧ p.2 = none
  | [], acc, g => by simp
  | p :: l, acc, g => by
    rw [List.foldl_cons, mem_foldl_addG l, mem_addG]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_reqs (p : GoalOf R Rel × Option Nat) :
    p ∈ (reqsOf K hK U ts depth).flatten.flatten ↔
      ∃ t ∈ ts, ∃ strat ∈ (outOf K hK U ts depth t).2, ∃ d ∈ strat, p = (d, idx ts d) := by
  simp only [reqsOf, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨l, ⟨L, ⟨t, ht, rfl⟩, hl⟩, hp⟩
    obtain ⟨strat, hs, rfl⟩ := List.mem_map.1 hl
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
    exact ⟨t, ht, strat, hs, d, hd, rfl⟩
  · rintro ⟨t, ht, strat, hs, d, hd, rfl⟩
    exact ⟨_, ⟨_, ⟨t, ht, rfl⟩, List.mem_map_of_mem hs⟩, List.mem_map_of_mem hd⟩

/-- The goals that get a table: the goals of the strategies of the tables
that have none. -/
theorem mem_newGoals (g : GoalOf R Rel) :
    g ∈ newGoals K hK U ts depth ↔
      ∃ t ∈ ts, ∃ strat ∈ (outOf K hK U ts depth t).2, g ∈ strat ∧ idx ts g = none := by
  unfold newGoals
  rw [mem_foldl_addG]
  simp only [List.not_mem_nil, false_or]
  constructor
  · rintro ⟨p, hp, rfl, h2⟩
    obtain ⟨t, ht, strat, hs, d, hd, rfl⟩ := (mem_reqs K hK U ts depth p).1 hp
    exact ⟨t, ht, strat, hs, hd, h2⟩
  · rintro ⟨t, ht, strat, hs, hd, h2⟩
    exact ⟨(g, idx ts g), (mem_reqs K hK U ts depth _).2 ⟨t, ht, strat, hs, g, hd, rfl⟩, rfl, h2⟩

/-! ## The tables that complete -/

omit [Answer R] [DecidableEq R] in
/-- What `completing` returns. -/
theorem mem_completing {done gained : List Bool} {deps : List (List (List (Option Nat)))} {i : Nat}
    (h : i ∈ completing done gained deps) :
    i < done.length ∧ done.getD i false = false ∧ gained.getD i true = false ∧
      ∃ strat ∈ deps.getD i [], ∀ o ∈ strat, ∃ j, o = some j ∧
        (done.getD j false = true ∨ j ∈ completing done gained deps) := by
  unfold completing at h ⊢
  dsimp only at h ⊢
  obtain ⟨hS, hok⟩ := gfpFrom_closed _ _ _ (Nat.le_refl _) i h
  generalize gfpFrom _ _ _ = C at hok ⊢
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hS
  refine ⟨hS.1, hS.2.1, hS.2.2, ?_⟩
  obtain ⟨strat, hs, hall⟩ := List.any_eq_true.1 hok
  refine ⟨strat, hs, fun o ho => ?_⟩
  have := List.all_eq_true.1 hall o ho
  cases o with
  | none => cases this
  | some j =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at this
    exact ⟨j, rfl, this.2⟩

/-- A table that completes was incomplete, gained nothing, and has a
strategy all of whose goals have a table that was complete or completes. -/
theorem mem_closing {i : Nat} (h : i ∈ closing K hK U ts depth) :
    ∃ hi : i < ts.length, ts[i].done = false ∧ gainOf K hK U ts depth ts[i] = [] ∧
      ∃ strat ∈ (outOf K hK U ts depth ts[i]).2, ∀ d ∈ strat, ∃ j, idx ts d = some j ∧
        ((∃ hj : j < ts.length, ts[j].done = true) ∨ j ∈ closing K hK U ts depth) := by
  obtain ⟨hi, hd, hg, strat', hs, hall⟩ := mem_completing h
  rw [List.length_map] at hi
  refine ⟨hi, ?_⟩
  simp only [gainedOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some, decide_eq_false_iff_not, ne_eq, not_not, grow,
    List.length_append] at hd hg
  refine ⟨hd, List.length_eq_zero_iff.1 (by omega), ?_⟩
  simp only [reqsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some, List.map_map, List.mem_map, Function.comp_def] at hs
  obtain ⟨strat, hs, rfl⟩ := hs
  refine ⟨strat, hs, fun d hd => ?_⟩
  obtain ⟨j, hj, hc⟩ := hall (idx ts d) (List.mem_map.2 ⟨d, hd, rfl⟩)
  refine ⟨j, hj, ?_⟩
  rcases hc with hdone | hC
  · left
    obtain ⟨hjl, -, -⟩ := idx_some.1 hj
    exact ⟨hjl, by simpa [List.getElem?_eq_getElem hjl] using hdone⟩
  · exact .inr hC

end Tabled

end RwLog
