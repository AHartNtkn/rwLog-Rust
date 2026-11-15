/-
# The symmetric engine is complete, and honest when it reports that it is done

`stateAt K hK P root r` is the state of the engine after `r` requests from
its first state. These states are a run of requests (`isRun`), so the run
is fair (`IsRun.fair`, `Fair.lean`) and holds, for every span the root
derives, an answer of the root table that covers it
(`Saturation.Fair.complete`).

The machine `engine.costedAt dom K hK` makes one request a step while the
root table is not complete, emits what the root table gained, and then
reports that it is done (`run_cases`). A complete table gains nothing more,
so everything the run of requests ever holds for the root the machine has
emitted, at the latest when it reports that it is done. Hence

* the machine is complete span by span (`complete`);
* when it reports that it is done, its answers relate every pair the query
  relates (`honestExhaustion`);
* it emits no progress certificate (`honestProgress`);
* no answer it emits is covered by an earlier one (`noSubsumed`), since no
  answer of a table covers a later one (`nocov_stateAt`);
* its final report is the maximal emitted answers (`finalMaximal`);
* on first-order input with a root that is its own converse it shows answers
  that are their own converses rearranged (`engine_selfConverse`), so run on
  one orientation it has `ConvTrace` and `DualTrace` (`oriented_convTrace`,
  `oriented_dualTrace`).

The engine is the engine of any unfolding race that meets its specification
(`RwLog.Good`).
-/
import RwLog.Rungs.Symmetric.Fair
import RwLog.Rungs.Symmetric.SelfConverse
import RwLog.Rungs.Symmetric.Edge
import RwLog.Rungs.Framework.Runtime

namespace RwLog

namespace Symmetric

open Answer Saturation

section kernel

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} (K : Kernel R Cost)
  (hK : K.Refines D) (P : Program) (root : Rel) (U : GOracle R Rel (Ans D P) Cost)

/-- The state of the engine after `r` requests. -/
def stateAt : Nat → StateOf R Rel (Ans D P)
  | 0 => (init (K := DerivationKernel.over D K hK P) root).val
  | r + 1 => (request (K := DerivationKernel.over D K hK P) U (stateAt r)).val.1

variable {K hK P root U}

/-- The first state: the table of the root goal alone, with no groups and
not complete, and the depth 1. -/
theorem init_shape : ∃ self, stateAt K hK P root U 0 =
    ⟨[⟨⟨none, root, none⟩, self, [], false, none, 0, 0, 0, none, 0, 0, 0⟩], 0, 0, [], 1⟩ := by
  unfold stateAt
  at_cost K hK
  simp only [init, Cost.bind_val, Cost.pure_val]
  exact ⟨_, rfl⟩

theorem root_goal0 : goalAt (stateAt K hK P root U 0) 0 = some ⟨none, root, none⟩ := by
  obtain ⟨self, e⟩ := init_shape (K := K) (hK := hK) (P := P) (root := root) (U := U)
  rw [e]
  rfl

theorem good_dated (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
    (hn : Normal root) (hfo : root.FO) : ∀ r, Good (stateAt K hK P root U r) ∧ Dated (stateAt K hK P root U r)
  | 0 => by
    refine ⟨good_init hn hfo, ?_⟩
    obtain ⟨self, e⟩ := init_shape (K := K) (hK := hK) (P := P) (root := root) (U := U)
    rw [e]
    intro k t ht
    obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? ht)
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | r + 1 => by
    obtain ⟨hg, hd⟩ := good_dated hL hP hU hn hfo r
    exact ⟨good_request hL (readOk hL hP) hP U hU hg,
      (req_request hL (readOk hL hP) hP U hU hg hd).dated⟩

/-- **The states of the engine are a run of requests.** -/
theorem isRun (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
    (hn : Normal root) (hfo : root.FO) : IsRun U (stateAt K hK P root U) := by
  obtain ⟨self, e⟩ := init_shape (K := K) (hK := hK) (P := P) (root := root) (U := U)
  have gd := good_dated (K := K) (hK := hK) hL hP hU hn hfo
  refine ⟨⟨fun r => req_request hL (readOk hL hP) hP U hU (gd r).1 (gd r).2, fun k t ht => ?_⟩,
    fun r => (gd r).1, ?_, fun k t ht => ?_⟩
  · rw [e] at ht
    obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? ht)
    rfl
  · rw [e]
    exact Nat.one_pos
  · rw [e] at ht
    obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? ht)
    rfl

/-- Every answer of the root table has been emitted. -/
theorem shown_stateAt : ∀ r, (stateAt K hK P root U r).shown =
    ((stateAt K hK P root U r).answers 0).length
  | 0 => by
    obtain ⟨self, e⟩ := init_shape (K := K) (hK := hK) (P := P) (root := root) (U := U)
    rw [e]
    rfl
  | r + 1 => by
    obtain ⟨st', -, e⟩ := reach_request (K := K) (hK := hK) (P := P) U (stateAt K hK P root U r)
    show (request (K := DerivationKernel.over D K hK P) U (stateAt K hK P root U r)).val.1.shown =
      ((request (K := DerivationKernel.over D K hK P) U
        (stateAt K hK P root U r)).val.1.answers 0).length
    rw [e]
    rfl

/-- A request emits what the root table gains. -/
theorem emits (r : Nat) : (stateAt K hK P root U (r + 1)).answers 0 =
    (stateAt K hK P root U r).answers 0 ++
      (request (K := DerivationKernel.over D K hK P) U (stateAt K hK P root U r)).val.2 := by
  obtain ⟨st', hre, e⟩ := reach_request (K := K) (hK := hK) (P := P) U (stateAt K hK P root U r)
  have hsh := reach_shown hre
  obtain ⟨l, hl⟩ := (stable_request (K := K) (hK := hK) U (stateAt K hK P root U r)).answers 0
  have e1 : (stateAt K hK P root U (r + 1)).answers 0 = st'.answers 0 := by
    show (request (K := DerivationKernel.over D K hK P) U
      (stateAt K hK P root U r)).val.1.answers 0 = _
    rw [e]
    rfl
  have e2 : (request (K := DerivationKernel.over D K hK P) U (stateAt K hK P root U r)).val.2 =
      (st'.answers 0).drop st'.shown := by rw [e]
  have hl' : (stateAt K hK P root U r).answers 0 ++ l = st'.answers 0 := by rw [← e1]; exact hl
  rw [e2, e1, hsh, shown_stateAt r, ← hl', List.drop_left]

/-! ## No answer of a table covers a later one -/

/-- In every table, no answer covers a later one. -/
def NoCovAt (st : StateOf R Rel (Ans D P)) : Prop :=
  ∀ j, NoCov D ((st.answers j).map Ans.span)

omit [DecidableEq R] in
theorem answers_eq_cores (st : StateOf R Rel (Ans D P)) (j : Nat) :
    st.answers j = ((st.cores[j]?).map (·.2.2)).getD [] := by
  unfold StateOf.answers StateOf.cores
  rw [List.getElem?_map]
  cases st.tables[j]? <;> rfl

omit [DecidableEq R] in
theorem nocov_app {st : StateOf R Rel (Ans D P)} (h : NoCovAt st) (i : Nat) (a : Ans D P)
    (ha : ∀ y ∈ (st.answers i).map Ans.span, D.covers y a.span = false) :
    NoCovAt (st.modify i (app [a])) := by
  intro j
  by_cases hj : j = i
  · subst hj
    cases ht : st.tables[j]? with
    | none =>
      have e : (st.modify j (app [a])).answers j = st.answers j := by
        unfold StateOf.answers StateOf.modify
        simp [ht]
      rw [e]
      exact h j
    | some t =>
      rw [answers_modify_app st j [a] ht, List.map_append]
      exact (h j).snoc ha
  · have e : (st.modify i (app [a])).answers j = st.answers j := by
      rw [answers_eq_cores, answers_eq_cores, cores_modify_ne _ _ (Ne.symm hj)]
    rw [e]
    exact h j

/-- Whatever the engine does, no answer of a table covers a later one. -/
theorem nocov_reach {st st' : StateOf R Rel (Ans D P)} (h : Reach K hK st st') :
    NoCovAt st → NoCovAt st' := by
  induction h with
  | refl st => exact id
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)
  | same e _ =>
    intro h j
    rw [answers_eq_cores, e, ← answers_eq_cores]
    exact h j
  | @opened st st' g' self e _ =>
    intro h j
    rw [answers_eq_cores, e]
    by_cases hj : j < st.cores.length
    · rw [List.getElem?_append_left hj, ← answers_eq_cores]
      exact h j
    · rw [List.getElem?_append_right (by omega)]
      cases hx : j - st.cores.length with
      | zero => exact List.Pairwise.nil
      | succ m => exact List.Pairwise.nil
  | add st i a =>
    intro h
    rw [addAnswer_val]
    split
    · exact h
    · rename_i hna
      have h1 := nocov_app h i a (any_covB_false hna)
      split
      · split
        · exact h1
        · rename_i hnb
          exact nocov_app h1 i _ (any_covB_false hnb)
      · exact h1

theorem nocov_stateAt : ∀ r, NoCovAt (stateAt K hK P root U r)
  | 0 => by
    obtain ⟨self, e⟩ := init_shape (K := K) (hK := hK) (P := P) (root := root) (U := U)
    rw [e]
    intro j
    cases j with
    | zero => exact List.Pairwise.nil
    | succ j => exact List.Pairwise.nil
  | r + 1 => by
    obtain ⟨st', hre, e⟩ := reach_request (K := K) (hK := hK) (P := P) U (stateAt K hK P root U r)
    have h := nocov_reach hre (nocov_stateAt r)
    show NoCovAt (request (K := DerivationKernel.over D K hK P) U (stateAt K hK P root U r)).val.1
    rw [e]
    exact h

end kernel

section run

variable (U : Unfolder) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
  (P : Program) (root : Rel)

/-- The machine. -/
abbrev Rt : Runtime := ((engine @U).costedAt dom K hK).runtime

/-- The state of the engine after `r` requests, at the kernel of the
program. -/
abbrev sAt (r : Nat) : StateOf (R P.sorts) Rel (Ans (dom P.sorts) P) :=
  stateAt (K P.sorts) (hK P.sorts) P root (UAt @U dom K hK P) r

/-- The state of the machine after `r` requests. -/
abbrev stAt (r : Nat) : (engine @U).StateAt dom := ⟨P, root, sAt @U dom K hK P root r⟩

/-- An answer as the machine reports it. -/
def sp (a : Ans (dom P.sorts) P) : (Rt @U dom K hK).Ans :=
  (⟨P.sorts, a.span⟩ : (S : Sorts) × R S)

theorem init_eq (q : Rel) : (Rt @U dom K hK).init P q = stAt @U dom K hK P q.norm 0 := rfl

theorem map_sp (l : List (Ans (dom P.sorts) P)) :
    (l.map Ans.span).map (Sigma.mk P.sorts) = l.map (sp @U dom K hK P) :=
  List.map_map

variable {U dom K hK P root}
variable (hI : IsRun (UAt @U dom K hK P) (sAt @U dom K hK P root))
include hI

theorem root_at (r : Nat) : goalAt (sAt @U dom K hK P root r) 0 = some ⟨none, root, none⟩ :=
  hI.goal_le (Nat.zero_le r) root_goal0

/-- The answers of the root table are answers of the root goal. -/
theorem rootAns_goal {r : Nat} {a : Ans (dom P.sorts) P}
    (ha : a ∈ (sAt @U dom K hK P root r).answers 0) : a.goal = ⟨none, root, none⟩ := by
  obtain ⟨t, ht, hg⟩ := table_of_goalAt (root_at hI r)
  unfold StateOf.answers at ha
  rw [ht] at ha
  have := ((hI.good r).inv.core 0 t ht).2.2 a ha
  rw [this, hg]

/-- A step while the root table is not complete. -/
theorem rt_step_live {r : Nat} (h : (sAt @U dom K hK P root r).isDone 0 = false) :
    ∃ l, (sAt @U dom K hK P root (r + 1)).answers 0 = (sAt @U dom K hK P root r).answers 0 ++ l ∧
      (Rt @U dom K hK).step (stAt @U dom K hK P root r) =
        .emit (l.map (sp @U dom K hK P)) (stAt @U dom K hK P root (r + 1)) := by
  refine ⟨_, emits r, ?_⟩
  obtain ⟨t, ht, -⟩ := table_of_goalAt (root_at hI r)
  have hhead : (stOf @U dom (stAt @U dom K hK P root r)).tables.head? = some t := by
    rw [List.head?_eq_getElem?]; exact ht
  have hs := costed_step_val @U dom K hK (stAt @U dom K hK P root r) hhead
  have hd : t.done = false := by rw [← isDone_of_table ht]; exact h
  rw [hd] at hs
  simp only [Bool.false_eq_true, ite_false] at hs
  rw [filterMap_rootSpan (fun a ha => rootAns_goal hI (r := r + 1)
    (by rw [emits]; exact List.mem_append_right _ ha))] at hs
  exact hs.trans (congrArg (fun x => (StepOf.emit x (stAt @U dom K hK P root (r + 1)) :
    StepOf ((S : Sorts) × R S) ((engine @U).StateAt dom))) (map_sp @U dom K hK P _))

/-- The step when the root table is complete. -/
theorem rt_step_done {r : Nat} (h : (sAt @U dom K hK P root r).isDone 0 = true) :
    (Rt @U dom K hK).step (stAt @U dom K hK P root r) =
      .done ((((sAt @U dom K hK P root r).answers 0).maximaBy (covB (dom P.sorts) P)).map
        (sp @U dom K hK P)) := by
  obtain ⟨t, ht, -⟩ := table_of_goalAt (root_at hI r)
  have hhead : (stOf @U dom (stAt @U dom K hK P root r)).tables.head? = some t := by
    rw [List.head?_eq_getElem?]; exact ht
  have hs := costed_step_val @U dom K hK (stAt @U dom K hK P root r) hhead
  have hd : t.done = true := by rw [← isDone_of_table ht]; exact h
  have ea : (sAt @U dom K hK P root r).answers 0 = t.answers := by
    unfold StateOf.answers; rw [ht]
  rw [hd] at hs
  simp only [ite_true] at hs
  rw [filterMap_rootSpan (fun a ha => rootAns_goal hI (r := r)
    (by rw [ea]; exact List.mem_maximaBy ha))] at hs
  rw [ea]
  exact hs.trans (congrArg (fun x => (StepOf.done x :
    StepOf ((S : Sorts) × R S) ((engine @U).StateAt dom))) (map_sp @U dom K hK P _))

/-- A run while the root table is not complete emits what the root table
gains. -/
theorem run_live : ∀ (j r m : Nat), (∀ i < j, (sAt @U dom K hK P root (r + i)).isDone 0 = false) →
    ∃ l, (sAt @U dom K hK P root (r + j)).answers 0 = (sAt @U dom K hK P root r).answers 0 ++ l ∧
      (Rt @U dom K hK).run (stAt @U dom K hK P root r) (j + m) =
        ((l.map (sp @U dom K hK P) : List (Rt @U dom K hK).Ans) ++
            ((Rt @U dom K hK).run (stAt @U dom K hK P root (r + j)) m).1,
          ((Rt @U dom K hK).run (stAt @U dom K hK P root (r + j)) m).2)
  | 0, r, m, _ => ⟨[], by simp, by rw [Nat.zero_add]; rfl⟩
  | j + 1, r, m, h => by
    have h0' := h 0 (Nat.succ_pos j)
    rw [Nat.add_zero] at h0'
    obtain ⟨l₁, h₁, hs⟩ := rt_step_live hI h0'
    obtain ⟨l₂, h₂, hr⟩ := run_live j (r + 1) m fun i hi => by
      have := h (i + 1) (Nat.succ_lt_succ hi)
      rwa [show r + (i + 1) = r + 1 + i by omega] at this
    refine ⟨l₁ ++ l₂, ?_, ?_⟩
    · rw [show r + (j + 1) = r + 1 + j by omega, h₂, h₁, List.append_assoc]
    · rw [show j + 1 + m = (j + m) + 1 by omega, (Rt @U dom K hK).run_succ_emit hs, hr,
        show r + (j + 1) = r + 1 + j by omega]
      refine Prod.ext ?_ rfl
      show _ ++ (_ ++ _) = _
      rw [List.map_append, List.append_assoc]

/-- A run from the first state: while the root table is not complete it has
emitted the answers of the root table; once the root table is complete it
has emitted them and reported the maximal ones. -/
theorem run_cases (n : Nat) :
    ((∀ j < n, (sAt @U dom K hK P root j).isDone 0 = false) ∧
      (Rt @U dom K hK).run (stAt @U dom K hK P root 0) n =
        (((sAt @U dom K hK P root n).answers 0).map (sp @U dom K hK P), none)) ∨
    ∃ j < n, (sAt @U dom K hK P root j).isDone 0 = true ∧
      (Rt @U dom K hK).run (stAt @U dom K hK P root 0) n =
        (((sAt @U dom K hK P root j).answers 0).map (sp @U dom K hK P),
          some ((((sAt @U dom K hK P root j).answers 0).maximaBy (covB (dom P.sorts) P)).map
            (sp @U dom K hK P))) := by
  have h0 : (sAt @U dom K hK P root 0).answers 0 = [] := by
    obtain ⟨self, e⟩ := init_shape (K := K P.sorts) (hK := hK P.sorts) (P := P) (root := root)
      (U := UAt @U dom K hK P)
    have e' : sAt @U dom K hK P root 0 = _ := e
    rw [e']
    rfl
  by_cases h : ∃ j, j < n ∧ (sAt @U dom K hK P root j).isDone 0 = true
  · right
    classical
    obtain ⟨j, hj, hmin'⟩ : ∃ j, (j < n ∧ (sAt @U dom K hK P root j).isDone 0 = true) ∧
        ∀ i < j, ¬(i < n ∧ (sAt @U dom K hK P root i).isDone 0 = true) :=
      ⟨Nat.find h, Nat.find_spec h, fun i hi => Nat.find_min h hi⟩
    have hmin : ∀ i < j, (sAt @U dom K hK P root (0 + i)).isDone 0 = false := fun i hi => by
      rw [Nat.zero_add]
      cases hd : (sAt @U dom K hK P root i).isDone 0 with
      | false => rfl
      | true => exact absurd ⟨Nat.lt_trans hi hj.1, hd⟩ (hmin' i hi)
    obtain ⟨m, hm⟩ : ∃ m, n = j + (m + 1) := ⟨n - j - 1, by omega⟩
    subst hm
    obtain ⟨l, hl, hr⟩ := run_live hI j 0 (m + 1) hmin
    rw [Nat.zero_add] at hl hr
    rw [h0, List.nil_append] at hl
    refine ⟨j, hj.1, hj.2, ?_⟩
    rw [hr, (Rt @U dom K hK).run_succ_done (rt_step_done hI hj.2), hl]
    simp
  · left
    have hall : ∀ j < n, (sAt @U dom K hK P root j).isDone 0 = false := fun j hj => by
      cases hd : (sAt @U dom K hK P root j).isDone 0 with
      | false => rfl
      | true => exact absurd ⟨j, hj, hd⟩ h
    refine ⟨hall, ?_⟩
    obtain ⟨l, hl, hr⟩ := run_live hI n 0 0 fun i hi => by rw [Nat.zero_add]; exact hall i hi
    rw [Nat.zero_add, Nat.add_zero] at hr
    rw [Nat.zero_add, h0, List.nil_append] at hl
    rw [hr, hl]
    simp [Runtime.run]

/-- An answer the root table ever has is emitted, at the latest when the
machine reports that it is done. -/
theorem emitted_of_root {r : Nat} {y : Ans (dom P.sorts) P}
    (hy : y ∈ (sAt @U dom K hK P root r).answers 0) :
    (∃ n, sp @U dom K hK P y ∈ (Rt @U dom K hK).emitted (stAt @U dom K hK P root 0) n) ∧
      ∀ n, (Rt @U dom K hK).Halts (stAt @U dom K hK P root 0) n →
        sp @U dom K hK P y ∈ (Rt @U dom K hK).emitted (stAt @U dom K hK P root 0) n := by
  constructor
  · refine ⟨r, ?_⟩
    rcases run_cases hI r with ⟨-, hr⟩ | ⟨j, -, hd, hr⟩
    · rw [show (Rt @U dom K hK).emitted (stAt @U dom K hK P root 0) r = _ from congrArg Prod.fst hr]
      exact List.mem_map_of_mem hy
    · rw [show (Rt @U dom K hK).emitted (stAt @U dom K hK P root 0) r = _ from congrArg Prod.fst hr]
      exact List.mem_map_of_mem (hI.done_answers hd r hy)
  · intro n hn
    rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, -, hd, hr⟩
    · simp [Runtime.Halts, Runtime.final, hr] at hn
    · rw [show (Rt @U dom K hK).emitted (stAt @U dom K hK P root 0) n = _ from congrArg Prod.fst hr]
      exact List.mem_map_of_mem (hI.done_answers hd r hy)

/-- The machine emits no progress certificate. -/
theorem trace_no_level : ∀ (n r : Nat),
    ∀ x ∈ (Rt @U dom K hK).trace (stAt @U dom K hK P root r) n, ∀ k, x ≠ .level k
  | 0, _, x, hx, _ => by simp [Runtime.trace] at hx
  | n + 1, r, x, hx, k => by
    cases hd : (sAt @U dom K hK P root r).isDone 0 with
    | false =>
      obtain ⟨l, -, hs⟩ := rt_step_live hI hd
      rw [(Rt @U dom K hK).trace_succ_emit hs] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact fun h => by cases h
      · exact trace_no_level n (r + 1) x hx k
    | true =>
      rw [(Rt @U dom K hK).trace_succ_done (rt_step_done hI hd)] at hx
      obtain rfl : x = _ := by simpa using hx
      exact fun h => by cases h

end run

/-! ## The theorems -/

section theorems

variable {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}
  {U : Unfolder}
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp) (hG : RwLog.Good @U)
include hD hG

/-- The states of the engine on a well-formed query are a run of
requests. -/
theorem isRun_of_wf {P : Program} {q : Rel} (wf : P.WellFormed q) :
    IsRun (UAt @U dom K hK P) (sAt @U dom K hK P q.norm) :=
  isRun (hD _ wf.2.2.1) (fun s hs => wf.2.2.2 s (List.mem_append_right _ hs))
    (hG (dom P.sorts) P (K P.sorts) (hK P.sorts) (hD _ wf.2.2.1)
      fun s hs => wf.2.2.2 s (List.mem_append_right _ hs)) (normal_norm q)
    (RelOf.FO.norm fun s hs => wf.2.2.2 s (List.mem_append_left _ hs))

/-- **The symmetric engine is complete**: every derivable span that relates
a pair is covered by one emitted answer. -/
theorem complete : (Rt @U dom K hK).Complete := fun P q wf s hs => by
  by_cases hne : (s.denAt P.sorts.interp).Nonempty
  · right
    have hI := isRun_of_wf (K := K) (hK := hK) hD hG wf
    obtain ⟨a, ha, hsub⟩ := hI.fair.complete (hD _ wf.2.2.1) (hI.root_opened root_goal0) hs hne
    obtain ⟨r, y, hy, rfl⟩ := (hI.held_iff root_goal0 a).1 ha
    obtain ⟨n, hn⟩ := (emitted_of_root hI hy).1
    exact ⟨n, _, hn, hsub⟩
  · exact .inl (Set.not_nonempty_iff_eq_empty.1 hne)

/-- **When the symmetric engine reports that it is done, its answers relate
every pair the query relates.** -/
theorem honestExhaustion : (Rt @U dom K hK).HonestExhaustion := fun P q wf n hn => by
  have hI := isRun_of_wf (K := K) (hK := hK) hD hG wf
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨a, ha, hpa⟩ := hI.fair.covers_pair (hD _ wf.2.2.1) (hI.root_opened root_goal0) hp
    obtain ⟨r, y, hy, rfl⟩ := (hI.held_iff root_goal0 a).1 ha
    exact Set.mem_iUnion₂.2 ⟨sp @U dom K hK P y, (emitted_of_root hI hy).2 n hn, hpa⟩
  · intro p hp
    obtain ⟨a, ha, hpa⟩ := Set.mem_iUnion₂.1 hp
    exact Engine.sound (engine @U) dom K hK hD P q wf n a ha hpa

/-- **The symmetric engine emits no progress certificate**, so every one it
emits is true. -/
theorem honestProgress : (Rt @U dom K hK).HonestProgress := fun P q wf k n hc => by
  have hI := isRun_of_wf (K := K) (hK := hK) hD hG wf
  exact absurd rfl (trace_no_level hI (k + 1) 0 _ (List.mem_of_getElem? hc) n)

/-- What a run has emitted is the answers of the root table after some
number of requests. -/
theorem emitted_eq {P : Program} {q : Rel} (wf : P.WellFormed q) (n : Nat) :
    ∃ j, (Rt @U dom K hK).emitted ((Rt @U dom K hK).init P q) n =
      ((sAt @U dom K hK P q.norm j).answers 0).map (sp @U dom K hK P) := by
  have hI := isRun_of_wf (K := K) (hK := hK) hD hG wf
  rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, -, -, hr⟩
  · exact ⟨n, congrArg Prod.fst hr⟩
  · exact ⟨j, congrArg Prod.fst hr⟩

/-- **No answer the symmetric engine emits is covered by an earlier one.** -/
theorem noSubsumed : (Rt @U dom K hK).NoSubsumed := fun P q wf n => by
  obtain ⟨j, hj⟩ := emitted_eq (K := K) (hK := hK) hD hG wf n
  rw [hj, List.pairwise_map]
  have := nocov_stateAt (K := K P.sorts) (hK := hK P.sorts) (P := P) (root := q.norm)
    (U := UAt @U dom K hK P) j 0
  rw [NoCov, List.pairwise_map] at this
  refine this.imp fun {y x} h hc => ?_
  have := (covB_iff (hD _ wf.2.2.1) y x).2 hc
  rw [covB, h] at this
  cases this

/-- **The final report of the symmetric engine is the maximal emitted
answers.** -/
theorem finalMaximal : (Rt @U dom K hK).FinalMaximal := fun P q wf n fin hfin => by
  have hI := isRun_of_wf (K := K) (hK := hK) hD hG wf
  have hL := hD _ wf.2.2.1
  rw [init_eq] at hfin ⊢
  rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, -, -, hr⟩
  · rw [show (Rt @U dom K hK).final (stAt @U dom K hK P q.norm 0) n = _ from
      congrArg Prod.snd hr] at hfin
    cases hfin
  · rw [show (Rt @U dom K hK).final (stAt @U dom K hK P q.norm 0) n = _ from
      congrArg Prod.snd hr] at hfin
    obtain rfl := Option.some.inj hfin
    rw [show (Rt @U dom K hK).emitted (stAt @U dom K hK P q.norm 0) n = _ from
      congrArg Prod.fst hr]
    refine ⟨fun a ha => ?_, fun a ha => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact List.mem_map_of_mem (List.mem_maximaBy hx)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨z, hz, hzx⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) hx
      exact ⟨_, List.mem_map_of_mem hz, (covB_iff hL z x).1 hzx⟩
    · rw [List.pairwise_map]
      refine (List.maximaBy_pairwise (cov := covB (dom P.sorts) P) _).imp fun {y x} h => ?_
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · have := (covB_iff hL y x).2 hc
        rw [h.1] at this; cases this
      · have := (covB_iff hL x y).2 hc
        rw [h.2] at this; cases this

/-- **On first-order input with a root node that is its own converse the
symmetric engine shows, at every step, answers that are their own converses
rearranged.** So run on one orientation (`CostedRuntime.oriented`) it shows
on the converse of a query, and on the mirror image of an input, the run on
the query with every answer swapped (`oriented_convTrace`,
`oriented_dualTrace`). -/
theorem engine_selfConverse : ((engine @U).costedAt dom K hK).SelfConverse := by
  refine selfConverse_of hD
    (fun s => s.P.sorts.WellFormed ∧ ProgFO s.P ∧ Good (stOf @U dom s) ∧
      goalAt (stOf @U dom s) 0 = some ⟨none, s.root, none⟩)
    (fun s hs => hs.2.2.1.inv.answers hs.2.2.2) (fun P root hwf hP _ hfo => ?_)
    (fun s as s' hs he => ?_)
  · exact ⟨hwf, hP, good_init (K := K P.sorts) (hK := hK P.sorts) (P := P) (normal_norm root)
      hfo.norm, (inv_init (K := K P.sorts) (hK := hK P.sorts) (P := P) (normal_norm root)).2⟩
  · obtain ⟨hwf, hP, hI, hg⟩ := hs
    have hL := hD _ hwf
    have hlt := lt_of_goalAt hg
    have hhead : (stOf @U dom s).tables.head? = some (stOf @U dom s).tables[0] := by
      rw [List.head?_eq_getElem?]; exact List.getElem?_eq_getElem hlt
    rw [costed_step_val @U dom K hK s hhead] at he
    split at he
    · cases he
    · cases he
      obtain ⟨st', hre, hreq⟩ := reach_request (K := K s.P.sorts) (hK := hK s.P.sorts)
        (UAt @U dom K hK s.P) (stOf @U dom s)
      refine ⟨hwf, hP, good_request hL (readOk hL hP) hP _
        (hG (dom s.P.sorts) s.P (K s.P.sorts) (hK s.P.sorts) hL hP) hI, ?_⟩
      show goalAt (request (K := DerivationKernel.over (dom s.P.sorts) (K s.P.sorts)
        (hK s.P.sorts) s.P) (UAt @U dom K hK s.P) (stOf @U dom s)).val.1 0 = _
      rw [hreq]
      exact hre.ext _ _ hg

/-- **The converse, for the symmetric engine on one orientation.** The run
on the converse of a query is the run on the query with every answer
swapped, step for step. -/
theorem oriented_convTrace : ((engine @U).costedAt dom K hK).oriented.runtime.ConvTrace :=
  CostedRuntime.oriented_convTrace (engine_selfConverse hD hG)

/-- **The mirror image, for the symmetric engine on one orientation.** The
run on the mirrored query in the mirrored program is the run on the query
with every answer swapped, step for step. -/
theorem oriented_dualTrace : ((engine @U).costedAt dom K hK).oriented.runtime.DualTrace :=
  CostedRuntime.oriented_dualTrace (engine_selfConverse hD hG)

end theorems

end Symmetric

end RwLog
