/-
# The separating family: the tables a round creates

Each open table asks for the tables it reads. The round at depth `d` finds
that exactly the goals of `newSlots k d` have no table yet, in that order, and
creates them: the two branches of the query in the first round, then one more
link of the chain per round, then `@z`.
-/
import RwLog.Rungs.R002.Proofs.Separation.Stages

namespace RwLog

namespace R002

namespace Sep

open Cost R001

/-! ## The goals asked for -/

/-- The tables the open tables read, in the order they are asked for. -/
def activeDeps (k d : Nat) : List Slot :=
  (slots k d).flatMap fun s => if isDone k d s then [] else dep k s

theorem reqG_size (k : Nat) (s : Slot) : ∀ g ∈ reqG k s, goalSize g ≤ 3 := by
  intro g hg
  cases s with
  | root =>
    simp only [reqG, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact goalSize_goal k (.c k)
    · exact goalSize_goal k .w
  | c j =>
    cases j with
    | zero => simp only [reqG, List.mem_singleton] at hg; subst hg; exact goalSize_goal k .z
    | succ j => simp only [reqG, List.mem_singleton] at hg; subst hg; exact goalSize_goal k (.c j)
  | w => simp only [reqG, List.mem_singleton] at hg; subst hg; exact goalSize_wBody
  | z => simp [reqG] at hg

theorem reqG_norm (k : Nat) (s : Slot) :
    (reqG k s).map (fun g => g.norm.2) = (dep k s).map (goal k) := by
  cases s with
  | root => simp [reqG, dep, goal, norm_gC, norm_gW]
  | c j => cases j <;> simp [reqG, dep, goal, norm_gC, norm_gZ]
  | w => simp [reqG, dep, goal, norm_wBody]
  | z => rfl

theorem reqG_length (k : Nat) (s : Slot) : (reqG k s).length ≤ 2 := by
  cases s with
  | c j => cases j <;> simp [reqG]
  | _ => simp [reqG]

theorem outV_snd (k d : Nat) (s : Slot) :
    (outV k d s).2 = if isDone k d s then [] else reqG k s := by
  unfold outV; split <;> rfl

theorem length_flatMap_le {α β : Type} (f : α → List β) (c : Nat) :
    ∀ l : List α, (∀ x ∈ l, (f x).length ≤ c) → (l.flatMap f).length ≤ l.length * c
  | [], _ => by simp
  | x :: l, h => by
    have h1 := h x (by simp)
    have h2 := length_flatMap_le f c l fun y hy => h y (by simp [hy])
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- The goals asked for in a round. -/
def reqList (k d : Nat) : List Goal := ((slots k d).map (outV k d)).flatMap Prod.snd

theorem reqList_length (k d : Nat) : (reqList k d).length ≤ (slots k d).length * 2 := by
  unfold reqList
  rw [List.flatMap_map]
  refine length_flatMap_le _ 2 _ fun s _ => ?_
  rw [outV_snd]; split
  · simp
  · exact reqG_length k s

theorem reqs_costs (k d : Nat) :
    Costs (mapL (fun g => do
        let n ← Tabled.norm g
        pure n.2) (reqList k d))
      ((activeDeps k d).map (goal k)) ((slots k d).length * 6) := by
  have h := Costs.mapL (xs := reqList k d) (g := fun g => g.norm.2) (c := 3)
    (f := fun g => do
      let n ← Tabled.norm g
      pure n.2) (by
      intro g hg
      unfold reqList at hg
      rw [List.flatMap_map, List.mem_flatMap] at hg
      obtain ⟨s, _, hg⟩ := hg
      rw [outV_snd] at hg
      split at hg
      · simp at hg
      · exact ⟨rfl, by
          show goalSize g + 0 ≤ 3
          have := reqG_size k s g hg; omega⟩)
  refine Costs.congr_val (h.mono ?_) ?_
  · have := reqList_length k d; omega
  · unfold reqList activeDeps
    rw [List.flatMap_map, List.map_flatMap, List.map_flatMap]
    congr 1
    funext s
    rw [outV_snd]; split
    · rfl
    · exact reqG_norm k s

theorem activeDeps_length (k d : Nat) : (activeDeps k d).length ≤ (slots k d).length * 2 := by
  refine length_flatMap_le _ 2 _ fun s _ => ?_
  split
  · simp
  · cases s with
    | c j => cases j <;> simp [dep]
    | _ => simp [dep]

/-! ## The new tables -/

/-- One step of collecting the goals that have no table yet. -/
def sstep (S : List Slot) (acc : List Slot) (r : Slot) : List Slot :=
  if r ∈ S ∨ r ∈ acc then acc else acc ++ [r]

theorem sstep_length (S acc : List Slot) (r : Slot) : (sstep S acc r).length ≤ acc.length + 1 := by
  unfold sstep; split <;> simp

theorem any_same_tabs (k d : Nat) (r : Slot) :
    ((tabs k d).any fun t => t.goal.same (goal k r)) = decide (r ∈ slots k d) := by
  simp only [tabs, List.any_map, Function.comp_def, tab, goal_same]
  by_cases h : r ∈ slots k d
  · simp only [h, decide_true, List.any_eq_true, decide_eq_true_eq]
    exact ⟨r, h, rfl⟩
  · simp only [h, decide_false, List.any_eq_false, decide_eq_true_eq]
    rintro x hx rfl; exact h hx

theorem any_same_map (k : Nat) (l : List Slot) (r : Slot) :
    ((l.map (goal k)).any fun h => h.same (goal k r)) = decide (r ∈ l) := by
  simp only [List.any_map, Function.comp_def, goal_same]
  by_cases h : r ∈ l
  · simp only [h, decide_true, List.any_eq_true, decide_eq_true_eq]
    exact ⟨r, h, rfl⟩
  · simp only [h, decide_false, List.any_eq_false, decide_eq_true_eq]
    rintro x hx rfl; exact h hx

/-- The charged collection of new goals, on goals named by slots. -/
theorem collect_costs (k d : Nat) : ∀ (rs l : List Slot),
    Costs (foldL (fun acc g => do
        let b ← anyL (fun t : Table => Tabled.same t.goal g) (tabs k d)
        if b then pure acc else do
          let b' ← anyL (fun h => Tabled.same h g) acc
          pure (if b' then acc else acc ++ [g])) (l.map (goal k)) (rs.map (goal k)))
      ((rs.foldl (sstep (slots k d)) l).map (goal k))
      (rs.length * (6 * (slots k d).length + 6 * (l.length + rs.length)))
  | [], l => ⟨rfl, by simp [foldL]⟩
  | r :: rs, l => by
    have hstep : Costs (do
        let b ← anyL (fun t : Table => Tabled.same t.goal (goal k r)) (tabs k d)
        if b then pure (l.map (goal k)) else do
          let b' ← anyL (fun h => Tabled.same h (goal k r)) (l.map (goal k))
          pure (if b' then l.map (goal k) else l.map (goal k) ++ [goal k r]))
        ((sstep (slots k d) l r).map (goal k)) (6 * (slots k d).length + 6 * l.length) := by
      have h1 := Costs.anyL (xs := tabs k d) (c := 6)
        (f := fun t : Table => Tabled.same t.goal (goal k r)) (g := fun t => t.goal.same (goal k r))
        fun t ht => same_costs k d (goalSize_goal k r) ht
      rw [any_same_tabs, tabs, List.length_map] at h1
      have h2 := Costs.anyL (xs := l.map (goal k)) (c := 6)
        (f := fun h => Tabled.same h (goal k r)) (g := fun h => h.same (goal k r))
        (by
          intro h hh
          obtain ⟨x, _, rfl⟩ := List.mem_map.1 hh
          refine ⟨rfl, ?_⟩
          have := goalSize_goal k x; have := goalSize_goal k r
          show goalSize (goal k x) + goalSize (goal k r) ≤ 6
          omega)
      rw [any_same_map, List.length_map] at h2
      refine Costs.mono (c := (slots k d).length * 6 + (l.length * 6 + 0)) ?_ (by omega)
      refine Costs.bind h1 ?_
      by_cases hS : r ∈ slots k d
      · simp only [hS, decide_true, ↓reduceIte, sstep, true_or]
        exact (Costs.pure _).mono (Nat.zero_le _)
      · simp only [hS, decide_false, Bool.false_eq_true, ↓reduceIte, sstep, false_or]
        refine Costs.congr_val (Costs.bind h2 (Costs.pure _)) ?_
        by_cases hl : r ∈ l <;> simp [hl]
    have ih := collect_costs k d rs (sstep (slots k d) l r)
    have hlen := sstep_length (slots k d) l r
    refine Costs.mono (Costs.bind hstep ih) ?_
    have hmul : rs.length * (6 * (slots k d).length + 6 * ((sstep (slots k d) l r).length + rs.length)) ≤
        rs.length * (6 * (slots k d).length + 6 * (l.length + (rs.length + 1))) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-! ## Which goals are new -/

theorem fold_keep (S : List Slot) (x : Slot) : ∀ rs : List Slot, (∀ r ∈ rs, r ∈ S ∨ r = x) →
    rs.foldl (sstep S) [x] = [x]
  | [], _ => rfl
  | r :: rs, h => by
    have hr : sstep S [x] r = [x] := by
      rcases h r (by simp) with h | h <;> simp [sstep, h]
    rw [List.foldl_cons, hr]
    exact fold_keep S x rs fun y hy => h y (by simp [hy])

theorem fold_one (S : List Slot) (x : Slot) (hx : x ∉ S) : ∀ rs : List Slot,
    (∀ r ∈ rs, r ∈ S ∨ r = x) → rs.foldl (sstep S) [] = if x ∈ rs then [x] else []
  | [], _ => by simp
  | r :: rs, h => by
    have ih := fold_one S x hx rs fun y hy => h y (by simp [hy])
    rcases h r (by simp) with hr | hr
    · have hne : x ≠ r := fun e => hx (e ▸ hr)
      have : sstep S [] r = [] := by simp [sstep, hr]
      rw [List.foldl_cons, this, ih]
      simp [hne]
    · subst hr
      have : sstep S [] r = [r] := by simp [sstep, hx]
      rw [List.foldl_cons, this, fold_keep S r rs fun y hy => h y (by simp [hy])]
      simp

theorem fold_none (S : List Slot) : ∀ rs : List Slot, (∀ r ∈ rs, r ∈ S) →
    rs.foldl (sstep S) [] = []
  | [], _ => rfl
  | r :: rs, h => by
    have : sstep S [] r = [] := by simp [sstep, h r (by simp)]
    rw [List.foldl_cons, this]
    exact fold_none S rs fun y hy => h y (by simp [hy])

/-- A table that is read exists after the round. -/
theorem dep_inAt {k d : Nat} {s r : Slot} (hs : s.inAt k d) (hr : r ∈ dep k s) : r.inAt k (d + 1) := by
  cases s with
  | root =>
    simp only [dep, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [Slot.inAt] <;> omega
  | c j =>
    simp only [Slot.inAt] at hs
    cases j with
    | zero => simp only [dep, List.mem_singleton] at hr; subst hr; simp only [Slot.inAt]; omega
    | succ j => simp only [dep, List.mem_singleton] at hr; subst hr; simp only [Slot.inAt]; omega
  | w =>
    simp only [Slot.inAt] at hs
    simp only [dep, List.mem_singleton] at hr; subst hr; simp only [Slot.inAt]; omega
  | z => simp [dep] at hr

theorem mem_activeDeps {k d : Nat} {r : Slot} :
    r ∈ activeDeps k d ↔ ∃ s, s.inAt k d ∧ ¬ isDone k d s = true ∧ r ∈ dep k s := by
  unfold activeDeps
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hr⟩
    split at hr
    · simp at hr
    · exact ⟨s, mem_slots.1 hs, by assumption, hr⟩
  · rintro ⟨s, hs, hd, hr⟩
    exact ⟨s, mem_slots.2 hs, by simp [hd, hr]⟩

/-- Every new table is asked for by an open table. -/
theorem newSlots_asked {k d : Nat} (hd : 1 ≤ d) {x : Slot} (hx : x ∈ newSlots k d) :
    x ∈ activeDeps k d := by
  unfold newSlots at hx
  rw [mem_activeDeps]
  split_ifs at hx with h0 h1 h2
  · omega
  · simp only [List.mem_singleton] at hx; subst hx
    refine ⟨.c (k - d + 1), ⟨by omega, by omega⟩, ?_, by simp [dep]⟩
    rw [isDone_c]; omega
  · simp only [List.mem_singleton] at hx; subst hx
    refine ⟨.c 0, ⟨by omega, by omega⟩, ?_, by simp [dep]⟩
    rw [isDone_c]; omega
  · simp at hx

theorem newSlots_length {k d : Nat} (hd : 1 ≤ d) : (newSlots k d).length ≤ 1 := by
  unfold newSlots; split_ifs <;> first | omega | simp

/-- The goals without a table, in the order they are asked for, are the new
tables of the round. -/
theorem collect_new (k d : Nat) :
    (activeDeps k d).foldl (sstep (slots k d)) [] = newSlots k d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [activeDeps, slots, newSlots, dep, sstep]
  · have hin : ∀ r ∈ activeDeps k d, r ∈ slots k d ∨ r ∈ newSlots k d := by
      intro r hr
      obtain ⟨s, hs, _, hr⟩ := mem_activeDeps.1 hr
      have := dep_inAt hs hr
      by_cases h : r.inAt k d
      · exact Or.inl (mem_slots.2 h)
      · exact Or.inr (mem_newSlots.2 ⟨this, h⟩)
    have hlen := newSlots_length (k := k) hd
    match hN : newSlots k d with
    | [] =>
      refine fold_none _ _ fun r hr => ?_
      rcases hin r hr with h | h
      · exact h
      · rw [hN] at h; simp at h
    | [x] =>
      have hx : x ∈ newSlots k d := by rw [hN]; simp
      have hxS : x ∉ slots k d := fun h => (mem_newSlots.1 hx).2 (mem_slots.1 h)
      rw [fold_one _ x hxS _ fun r hr => by
        rcases hin r hr with h | h
        · exact Or.inl h
        · rw [hN] at h; exact Or.inr (by simpa using h)]
      simp [newSlots_asked hd hx]
    | _ :: _ :: _ => rw [hN] at hlen; simp at hlen

theorem newGoals_costs (k d : Nat) :
    Costs (foldL (fun acc g => do
        let b ← anyL (fun t : Table => Tabled.same t.goal g) (tabs k d)
        if b then pure acc else do
          let b' ← anyL (fun h => Tabled.same h g) acc
          pure (if b' then acc else acc ++ [g])) [] ((activeDeps k d).map (goal k)))
      ((newSlots k d).map (goal k)) (36 * ((slots k d).length * (slots k d).length)) := by
  have h := collect_costs k d (activeDeps k d) []
  rw [collect_new] at h
  refine h.mono ?_
  have hl := activeDeps_length k d
  have h1 : (activeDeps k d).length * (6 * (slots k d).length + 6 * (0 + (activeDeps k d).length)) ≤
      ((slots k d).length * 2) * (18 * (slots k d).length) :=
    Nat.mul_le_mul hl (by omega)
  have h2 : (slots k d).length * 2 * (18 * (slots k d).length) =
      36 * ((slots k d).length * (slots k d).length) := by ring
  simp only [List.length_nil] at h1 ⊢
  omega

end Sep

end R002

end RwLog
