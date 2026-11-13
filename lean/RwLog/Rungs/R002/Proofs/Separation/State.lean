/-
# The separating family: the state after every round

On `sepFam k` both machines hold, after `d` rounds, the tables described here
(`tabs k d`): the root, the links of the chain reached so far, `w`, and `@z`,
each with at most the one answer `z -> z`. This file only describes the
states; `Round.lean` proves that a round takes each to the next.

A table is named by a `Slot`. The tables are created in the order of
`slots k d`: the root; in the first round `c k` and `w`; then one link of the
chain per round down to `c 0`; then `@z`.

* The root never unfolds to a final expression, since `w` never does. It
  reads its answer from `c k` in round `k + 3` and completes in round `k + 4`.
* `c j` gets its answer from the unfolding race as soon as the depth exceeds
  `j` and its table exists, and completes one round later.
* `w` has no answer and completes in the second round, depending only on
  itself.
* `@z` is created in round `k + 2`, answers in the next round and completes
  in the one after.
-/
import RwLog.Rungs.R002.Proofs.Separation.Family

namespace RwLog

namespace R002

namespace Sep

open R001

/-- The name of a table of the run. -/
inductive Slot where
  | root
  | c (j : Nat)
  | w
  | z
  deriving DecidableEq

/-- The goal of a table. -/
def goal (k : Nat) : Slot → Goal
  | .root => gR k
  | .c j => gC j
  | .w => gW
  | .z => gZ

theorem goal_same (k : Nat) (a b : Slot) : (goal k a).same (goal k b) = decide (a = b) := by
  have hw := chainName_ne_w
  have hw' : ∀ i, "w" ≠ chainName i := fun i h => hw i h.symm
  cases a <;> cases b <;> simp [goal, GoalOf.same, boundEq, hw, hw']
  exact ⟨chainName_inj, fun h => h ▸ rfl⟩

theorem norm_goal (k : Nat) (s : Slot) : (goal k s).norm = (false, goal k s) := by
  cases s
  · exact norm_gR k
  · exact norm_gC _
  · exact norm_gW
  · exact norm_gZ

/-- The tables created by the round at depth `d`. -/
def newSlots (k d : Nat) : List Slot :=
  if d = 0 then [.c k, .w] else if d ≤ k then [.c (k - d)] else if d = k + 1 then [.z] else []

/-- The tables after `d` rounds, in the order of their creation. -/
def slots (k : Nat) : Nat → List Slot
  | 0 => [.root]
  | d + 1 => slots k d ++ newSlots k d

/-- Which tables exist after `d` rounds. -/
def Slot.inAt (k d : Nat) : Slot → Prop
  | .root => True
  | .c j => j ≤ k ∧ k < d + j
  | .w => 1 ≤ d
  | .z => k + 2 ≤ d

theorem mem_newSlots {k d : Nat} {s : Slot} :
    s ∈ newSlots k d ↔ s.inAt k (d + 1) ∧ ¬ s.inAt k d := by
  unfold newSlots
  cases s <;> simp only [Slot.inAt] <;> split_ifs <;>
    simp only [List.mem_cons, List.not_mem_nil, Slot.c.injEq, reduceCtorEq, or_false, false_or,
      or_self, not_true, and_false, false_iff, true_iff] <;>
    omega

theorem mem_slots {k : Nat} : ∀ {d : Nat} {s : Slot}, s ∈ slots k d ↔ s.inAt k d
  | 0, s => by cases s <;> simp [slots, Slot.inAt]
  | d + 1, s => by
    rw [slots, List.mem_append, mem_slots, mem_newSlots]
    have mono : s.inAt k d → s.inAt k (d + 1) := by
      cases s <;> simp [Slot.inAt] <;> omega
    by_cases h : s.inAt k d <;> simp [h, mono]

theorem nodup_newSlots (k d : Nat) : (newSlots k d).Nodup := by
  unfold newSlots; split_ifs <;> simp

theorem nodup_slots (k : Nat) : ∀ d, (slots k d).Nodup
  | 0 => by simp [slots]
  | d + 1 => by
    rw [slots, List.nodup_append]
    refine ⟨nodup_slots k d, nodup_newSlots k d, ?_⟩
    intro a ha b hb hab
    subst hab
    exact (mem_newSlots.1 hb).2 (mem_slots.1 ha)

theorem length_slots (k : Nat) : ∀ d, (slots k d).length ≤ d + 2
  | 0 => by simp [slots]
  | 1 => by simp [slots, newSlots]
  | d + 2 => by
    have := length_slots k (d + 1)
    have hn : (newSlots k (d + 1)).length ≤ 1 := by
      unfold newSlots; split_ifs <;> first | contradiction | simp
    rw [slots, List.length_append]
    omega

/-- The table has its answer after `d` rounds. -/
def hasAns (k d : Nat) : Slot → Bool
  | .root => decide (k + 3 ≤ d)
  | .c j => decide (j + 2 ≤ d ∧ k + 2 ≤ d + j)
  | .w => false
  | .z => decide (k + 3 ≤ d)

/-- The table is complete after `d` rounds. -/
def isDone (k d : Nat) : Slot → Bool
  | .root => decide (k + 4 ≤ d)
  | .c j => decide (j + 3 ≤ d ∧ k + 3 ≤ d + j)
  | .w => decide (2 ≤ d)
  | .z => decide (k + 4 ≤ d)

@[simp] theorem hasAns_root (k d : Nat) : hasAns k d .root = true ↔ k + 3 ≤ d := by simp [hasAns]
@[simp] theorem hasAns_c (k d j : Nat) :
    hasAns k d (.c j) = true ↔ j + 2 ≤ d ∧ k + 2 ≤ d + j := by simp [hasAns]
@[simp] theorem hasAns_w (k d : Nat) : hasAns k d .w = false := rfl
@[simp] theorem hasAns_z (k d : Nat) : hasAns k d .z = true ↔ k + 3 ≤ d := by simp [hasAns]

@[simp] theorem isDone_root (k d : Nat) : isDone k d .root = true ↔ k + 4 ≤ d := by simp [isDone]
@[simp] theorem isDone_c (k d j : Nat) :
    isDone k d (.c j) = true ↔ j + 3 ≤ d ∧ k + 3 ≤ d + j := by simp [isDone]
@[simp] theorem isDone_w (k d : Nat) : isDone k d .w = true ↔ 2 ≤ d := by simp [isDone]
@[simp] theorem isDone_z (k d : Nat) : isDone k d .z = true ↔ k + 4 ≤ d := by simp [isDone]

/-- The answers of a table after `d` rounds. -/
def ans (k d : Nat) (s : Slot) : List Span := if hasAns k d s then [zz] else []

theorem ans_eq_nil (k d : Nat) (s : Slot) : ans k d s = [] ↔ ¬ hasAns k d s = true := by
  unfold ans; cases hasAns k d s <;> simp

theorem ans_of_not {k d : Nat} {s : Slot} (h : ¬ hasAns k d s = true) : ans k d s = [] :=
  (ans_eq_nil k d s).2 h

theorem ans_of_has {k d : Nat} {s : Slot} (h : hasAns k d s = true) : ans k d s = [zz] := by
  simp [ans, h]

/-- The table of a slot after `d` rounds. -/
def tab (k d : Nat) (s : Slot) : Table := ⟨goal k s, ans k d s, isDone k d s⟩

def tabs (k d : Nat) : Tables := (slots k d).map (tab k d)

/-- The state after `d` rounds. -/
def st (k d : Nat) : State := ⟨prog k, tabs k d, false, d⟩

/-- What the unfolding race says about a goal at depth `d`. -/
def uval (d : Nat) : Slot → Bool × List Span
  | .root => (false, [])
  | .c j => if j + 1 ≤ d then (true, [zz]) else (false, [])
  | .w => (false, [])
  | .z => (true, [zz])

/-- The tables a table reads. -/
def dep (k : Nat) : Slot → List Slot
  | .root => [.c k, .w]
  | .c (j + 1) => [.c j]
  | .c 0 => [.z]
  | .w => [.w]
  | .z => []

/-- The answers the root gains in the round at depth `d`. -/
def emit (k d : Nat) : List Span := if d = k + 2 then [zz] else []

end Sep

end R002

end RwLog
