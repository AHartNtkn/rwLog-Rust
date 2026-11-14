/-
# The run of the tabled machine, read off its tables

The root table is the first table, round after round (`rootAns`,
`rootDone`). A step of the machine on the tables after `r` rounds emits what
the root table gains in the next round, or, when the root table is complete,
reports its maximal answers (`step_live`, `step_done`).
-/
import RwLog.Rungs.Tabled.Eventually

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D) (U : GOracle R Rel (Ans D P) Cost) (root : Rel)

/-- A step of the machine. -/
theorem step_val (st : StateOf R Rel (Ans D P)) :
    (step (K := DerivationKernel.over D K hK P) U st).val =
      match st.tables.head? with
      | none => .done []
      | some t =>
        if t.done then .done (t.answers.maximaBy (covB D P))
        else .emit (rootGain K hK U st.tables st.depth)
          ⟨nextTables K hK U st.tables st.depth, st.depth + 1⟩ := by
  have em := maxima_val (P := P) K hK
  have er := round_val (P := P) K hK U st
  at_cost K hK
  unfold step
  cases st.tables.head? with
  | none => simp only [Cost.pure_val]
  | some t =>
    cases hd : t.done <;>
      simp only [hd, Cost.bind_val, Cost.pure_val, em, er, Bool.false_eq_true, ite_false, ite_true]

/-- The answers of the root table after `r` rounds. -/
def rootAns (r : Nat) : List (Ans D P) :=
  match (tablesAt K hK U root r).head? with
  | some t => t.answers
  | none => []

/-- The root table is complete after `r` rounds. -/
def rootDone (r : Nat) : Bool :=
  match (tablesAt K hK U root r).head? with
  | some t => t.done
  | none => false

variable {K hK U root}

theorem root_pos (r : Nat) : 0 < (tablesAt K hK U root r).length :=
  (at_mono (Nat.zero_le r) (by simp [tablesAt] : 0 < (tablesAt K hK U root 0).length)).1

theorem root_head (r : Nat) :
    (tablesAt K hK U root r).head? = some ((tablesAt K hK U root r)[0]'(root_pos r)) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (root_pos r)]

theorem rootAns_eq (r : Nat) :
    rootAns K hK U root r = ((tablesAt K hK U root r)[0]'(root_pos r)).answers := by
  unfold rootAns; rw [root_head]

theorem rootDone_eq (r : Nat) :
    rootDone K hK U root r = ((tablesAt K hK U root r)[0]'(root_pos r)).done := by
  unfold rootDone; rw [root_head]

/-- The goal of the root table. -/
theorem root_goal (r : Nat) :
    ((tablesAt K hK U root r)[0]'(root_pos r)).goal = ⟨none, root, none⟩ :=
  (at_mono (Nat.zero_le r) (by simp [tablesAt] : 0 < (tablesAt K hK U root 0).length)).2.1

/-- What the root table gains in round `r`. -/
theorem rootAns_succ (r : Nat) :
    rootAns K hK U root (r + 1) = rootAns K hK U root r ++
      gainOf K hK U (tablesAt K hK U root r) r ((tablesAt K hK U root r)[0]'(root_pos r)) := by
  obtain ⟨h, e⟩ := next_getElem (K := K) (hK := hK) (U := U) (depth := r) (root_pos (root := root) r)
  rw [rootAns_eq, rootAns_eq]
  show ((nextTables K hK U (tablesAt K hK U root r) r)[0]'h).answers = _
  rw [e]

theorem step_live {r : Nat} (h : rootDone K hK U root r = false) :
    (step (K := DerivationKernel.over D K hK P) U ⟨tablesAt K hK U root r, r⟩).val =
      .emit (gainOf K hK U (tablesAt K hK U root r) r ((tablesAt K hK U root r)[0]'(root_pos r)))
        ⟨tablesAt K hK U root (r + 1), r + 1⟩ := by
  rw [rootDone_eq] at h
  rw [step_val]
  simp only [root_head, h, Bool.false_eq_true, ite_false]
  congr 1
  unfold rootGain
  simp only [root_head, List.head?_map, Option.map_some, grow, List.drop_left]

theorem step_done {r : Nat} (h : rootDone K hK U root r = true) :
    (step (K := DerivationKernel.over D K hK P) U ⟨tablesAt K hK U root r, r⟩).val =
      .done ((rootAns K hK U root r).maximaBy (covB D P)) := by
  rw [rootDone_eq] at h
  rw [step_val, rootAns_eq]
  simp only [root_head, h, ite_true]

end Tabled

end RwLog
