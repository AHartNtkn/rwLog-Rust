/-
# The separating family: reading the tables

What the charged table operations return and spend on the tables of the run:
finding the table of a goal, its answers, and its position. Every goal of the
run has size at most three, so comparing two keys costs at most six and a
lookup at most six per table.
-/
import RwLog.Rungs.R002.Proofs.Separation.Race
import RwLog.Rungs.Tabled.Exact

namespace RwLog

namespace R002

namespace Sep

open Cost R001

/-! ## Lists -/

theorem find?_beq {α : Type} [DecidableEq α] (a : α) :
    ∀ l : List α, l.find? (fun x => x == a) = if a ∈ l then some a else none
  | [] => by simp
  | x :: l => by
    by_cases h : x = a
    · simp [h]
    · have h' : ¬ a = x := fun e => h e.symm
      simp [h, h', find?_beq a l]

theorem findIdx?_beq {α : Type} [DecidableEq α] (a : α) (l : List α) :
    l.findIdx? (fun x => x == a) = if a ∈ l then some (l.idxOf a) else none := by
  split
  · rename_i h
    rw [List.findIdx?_eq_some_iff_findIdx_eq]
    exact ⟨List.idxOf_lt_length_iff.2 h, rfl⟩
  · rename_i h
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    simp only [beq_eq_false_iff_ne, ne_eq]
    rintro rfl; exact h hx

/-! ## Sizes -/

theorem goalSize_goal (k : Nat) (s : Slot) : goalSize (goal k s) ≤ 3 := by
  cases s <;> simp [goal, goalSize, RelOf.size, Span.size, Store.size, Term.size]

/-- The goal the table of `w` asks for: the body of `w`. -/
abbrev wBody : Goal := ⟨none, .or (.call "w") (.call "w"), none⟩

theorem goalSize_wBody : goalSize wBody ≤ 3 := by
  simp [goalSize, RelOf.size]

theorem goal_open (k : Nat) (s : Slot) : (goal k s).lb = none ∧ (goal k s).rb = none := by
  cases s <;> exact ⟨rfl, rfl⟩

theorem same_costs (k d : Nat) (r : Slot) {t : Table} (ht : t ∈ tabs k d) :
    Costs (Tabled.same t.goal (goal k r)) (t.goal.same (goal k r)) 6 := by
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 ht
  refine ⟨Tabled.same_val _ _, ?_⟩
  have := goalSize_goal k s
  have := goalSize_goal k r
  show (Tabled.same (goal k s) (goal k r)).ticks ≤ 6
  rw [Tabled.same_ticks_of_none (goal_open k s) (goal_open k r)]
  omega

/-! ## Lookups -/

theorem findTable_tabs (k d : Nat) (s : Slot) :
    R001.findTable (tabs k d) (goal k s) = if s ∈ slots k d then some (tab k d s) else none := by
  have e : ((fun t : Table => t.goal.same (goal k s)) ∘ tab k d) = fun x => x == s := by
    funext x; exact goal_same k x s
  rw [R001.findTable, tabs, List.find?_map, e, find?_beq]
  split <;> rfl

theorem indexOf_tabs (k d : Nat) (s : Slot) :
    R001.indexOf (tabs k d) (goal k s) =
      if s ∈ slots k d then some ((slots k d).idxOf s) else none := by
  have e : ((fun t : Table => t.goal.same (goal k s)) ∘ tab k d) = fun x => x == s := by
    funext x; exact goal_same k x s
  rw [R001.indexOf, tabs, List.findIdx?_map, e, findIdx?_beq]

theorem findTable_costs (k d : Nat) (r : Slot) :
    Costs (Tabled.findTable (tabs k d) (goal k r)) (R001.findTable (tabs k d) (goal k r))
      ((slots k d).length * 6) := by
  have := Costs.findL (f := fun t : Table => Tabled.same t.goal (goal k r))
    (g := fun t => t.goal.same (goal k r))
    (xs := tabs k d) (c := 6) fun t ht => same_costs k d r ht
  rw [tabs, List.length_map] at this
  exact this

/-- The answers of a goal whose key is the goal of `s`. -/
theorem answersOf_costs (k d : Nat) {g : Goal} (s : Slot) (hg : goalSize g ≤ 3)
    (hn : g.norm = (false, goal k s)) :
    Costs (Tabled.answersOf (tabs k d) g) (if s ∈ slots k d then ans k d s else [])
      (3 + (slots k d).length * 6) := by
  unfold Tabled.answersOf
  refine Costs.bind (v := g.norm) ⟨rfl, hg⟩ ?_
  rw [hn]
  have hf := findTable_costs k d s
  rw [findTable_tabs] at hf
  refine Costs.congr_val (Costs.mono (c' := (slots k d).length * 6)
    (Costs.bind hf (Costs.pure _)) (by omega)) ?_
  by_cases h : s ∈ slots k d <;> simp [h, orient, tab]

theorem indexFrom_ticks (g : Goal) (c : Nat) : ∀ (ts : Tables) (i : Nat),
    (∀ t ∈ ts, (Tabled.same t.goal g).ticks ≤ c) → (Tabled.indexFrom g i ts).ticks ≤ ts.length * c
  | [], _, _ => by simp [Tabled.indexFrom]
  | t :: ts, i, h => by
    have ht := h t (by simp)
    have ih := indexFrom_ticks g c ts (i + 1) fun t' ht' => h t' (by simp [ht'])
    simp only [Tabled.indexFrom, bind_ticks, ite_ticks, pure_ticks, List.length_cons, Nat.succ_mul]
    split <;> omega

/-- The position of the table of `s`. -/
theorem indexOf_costs (k d : Nat) (s : Slot) :
    Costs (Tabled.indexOf (tabs k d) (goal k s))
      (if s ∈ slots k d then some ((slots k d).idxOf s) else none) ((slots k d).length * 6) := by
  refine ⟨?_, ?_⟩
  · rw [Tabled.indexOf_val, indexOf_tabs]
  · have := indexFrom_ticks (goal k s) 6 (tabs k d) 0 fun t ht =>
      (same_costs k d s ht).2
    rw [tabs, List.length_map] at this
    exact this

end Sep

end R002

end RwLog
