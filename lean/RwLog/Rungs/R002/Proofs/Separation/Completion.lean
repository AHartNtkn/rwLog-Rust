/-
# The separating family: the charged completion check

`Tabled.completing` on the tables of the run. Its value is the set of
positions of the tables that complete in the round (`Closure.lean`), and it
spends at most a pass per member of the starting set, a test per member in
each pass, and two lookups per test: cubic in the number of tables. This
cubic term, summed over the rounds, is what makes the whole run quartic.
-/
import RwLog.Rungs.R002.Proofs.Separation.Closure

namespace RwLog

namespace R002

namespace Sep

open Cost R001

/-! ## The tables by position -/

/-- The table the machine reads at a position past the end. -/
abbrev dflt : Table := ⟨⟨none, .zero, none⟩, [], false⟩

/-- The tables after this round's answers were added. -/
def ts1 (k d : Nat) : Tables := (slots k d).map (tab1 k d)

/-- The oracle's verdicts, by position. -/
def finals (k d : Nat) : List Bool := ((slots k d).map (usV k d)).map Prod.fst

theorem getD_tabs (k d : Nat) {i : Nat} (h : i < (slots k d).length) :
    (tabs k d).getD i dflt = tab k d (slots k d)[i] := by
  simp [tabs, List.getD_eq_getElem?_getD, h]

theorem getD_ts1 (k d : Nat) {i : Nat} (h : i < (slots k d).length) :
    (ts1 k d).getD i dflt = tab1 k d (slots k d)[i] := by
  simp [ts1, List.getD_eq_getElem?_getD, h]

theorem getD_finals (k d : Nat) {i : Nat} (h : i < (slots k d).length) :
    (finals k d).getD i false = (usV k d (slots k d)[i]).1 := by
  simp [finals, List.getD_eq_getElem?_getD, h]

theorem idxOf_lt {k d : Nat} {r : Slot} (h : r ∈ slots k d) :
    (slots k d).idxOf r < (slots k d).length := List.idxOf_lt_length_iff.2 h

/-! ## The test of one dependency -/

/-- The charged test of one dependency, as `Tabled.completing` writes it. -/
def chk (k d : Nat) (S : List Nat) (g : Goal) : Cost Bool := do
  let n ← Tabled.norm g
  let j ← Tabled.indexOf (tabs k d) n.2
  pure (match j with
    | none => false
    | some j =>
      !decide (((ts1 k d).getD j dflt).answers.length ≠ ((tabs k d).getD j dflt).answers.length) &&
        (((tabs k d).getD j dflt).done || S.contains j))

def chkV (k d : Nat) (S : List Nat) (r : Slot) : Bool :=
  decide (r ∈ slots k d) && !gainedS k d r && (isDone k d r || S.contains ((slots k d).idxOf r))

theorem chk_costs (k d : Nat) (S : List Nat) {g : Goal} (r : Slot) (hg : goalSize g ≤ 3)
    (hn : g.norm = (false, goal k r)) :
    Costs (chk k d S g) (chkV k d S r) (3 + (slots k d).length * 6) := by
  unfold chk
  refine Costs.bind (v := g.norm) ⟨rfl, hg⟩ ?_
  rw [hn]
  refine Costs.congr_val (Costs.mono (c' := (slots k d).length * 6)
    (Costs.bind (indexOf_costs k d r) (Costs.pure _)) (by omega)) ?_
  by_cases h : r ∈ slots k d
  · have hi := idxOf_lt h
    have hr : (slots k d)[(slots k d).idxOf r] = r := List.getElem_idxOf hi
    simp only [h, ↓reduceIte, getD_tabs k d hi, getD_ts1 k d hi, hr, tab, tab1, chkV, gainedS,
      decide_true, Bool.true_and]
  · simp [h, chkV]

/-- The goals a table asks for are keyed by the tables it reads. -/
theorem reqG_dep (k : Nat) (s : Slot) :
    List.Forall₂ (fun g r => goalSize g ≤ 3 ∧ g.norm = (false, goal k r)) (reqG k s) (dep k s) := by
  cases s with
  | root =>
    exact .cons ⟨goalSize_goal k (.c k), norm_goal k (.c k)⟩
      (.cons ⟨goalSize_goal k .w, norm_goal k .w⟩ .nil)
  | c j =>
    cases j with
    | zero => exact .cons ⟨goalSize_goal k .z, norm_goal k .z⟩ .nil
    | succ j => exact .cons ⟨goalSize_goal k (.c j), norm_goal k (.c j)⟩ .nil
  | w => exact .cons ⟨goalSize_wBody, norm_wBody⟩ .nil
  | z => exact .nil

theorem all_forall₂ {α β : Type} {R : α → β → Prop} {f : α → Bool} {g : β → Bool}
    (h : ∀ a b, R a b → f a = g b) : ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      xs.all f = ys.all g
  | _, _, .nil => rfl
  | _, _, .cons hab t => by simp [h _ _ hab, all_forall₂ h t]

theorem exists_of_forall₂ {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β},
    List.Forall₂ R xs ys → ∀ a ∈ xs, ∃ b, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab t, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, hab⟩
    · exact exists_of_forall₂ t a h

theorem deps_costs (k d : Nat) (S : List Nat) (s : Slot) :
    Costs (allL (chk k d S) (reqG k s)) ((dep k s).all (chkV k d S))
      (2 * (3 + (slots k d).length * 6)) := by
  have hf := reqG_dep k s
  have h := Costs.allL (xs := reqG k s) (f := chk k d S) (g := fun g => (chk k d S g).val)
    (c := 3 + (slots k d).length * 6) (by
      intro g hg
      obtain ⟨r, hr⟩ := exists_of_forall₂ hf g hg
      exact ⟨rfl, (chk_costs k d S r hr.1 hr.2).2⟩)
  refine Costs.congr_val (h.mono ?_) ?_
  · have := reqG_length k s
    exact Nat.mul_le_mul_right _ this
  · exact all_forall₂ (fun g r hgr => (chk_costs k d S r hgr.1 hgr.2).1) hf

/-! ## The test of one table -/

/-- The charged completion test of the table at position `i`, as
`Tabled.completing` writes it. -/
def okC (k d : Nat) (S : List Nat) (i : Nat) : Cost Bool := do
  let strats ← Tabled.strategies (prog k) ((finals k d).getD i false) (tabs k d)
    ((tabs k d).getD i dflt).goal
  anyL (fun deps => allL (chk k d S) deps) strats

/-- The starting set: the open tables that gained nothing. -/
def S0 (k d : Nat) : List Nat :=
  (List.range (tabs k d).length).filter fun i =>
    !((tabs k d).getD i dflt).done &&
      !decide (((ts1 k d).getD i dflt).answers.length ≠ ((tabs k d).getD i dflt).answers.length)

theorem completing_eq (k d : Nat) :
    Tabled.completing (prog k) (finals k d) (tabs k d) (ts1 k d) =
      Tabled.gfpFrom (okC k d) (S0 k d).length (S0 k d) := rfl

theorem mem_S0 {k d i : Nat} : i ∈ S0 k d ↔
    ∃ h : i < (slots k d).length,
      ¬ isDone k d (slots k d)[i] = true ∧ ¬ gainedS k d (slots k d)[i] = true := by
  unfold S0
  rw [List.mem_filter, List.mem_range]
  have hl : (tabs k d).length = (slots k d).length := by simp [tabs]
  rw [hl]
  have key : ∀ h : i < (slots k d).length,
      ((!((tabs k d).getD i dflt).done &&
        !decide (((ts1 k d).getD i dflt).answers.length ≠
          ((tabs k d).getD i dflt).answers.length)) = true) ↔
      (¬ isDone k d (slots k d)[i] = true ∧ ¬ gainedS k d (slots k d)[i] = true) := by
    intro h
    rw [getD_tabs k d h, getD_ts1 k d h]
    show (!isDone k d _ && !gainedS k d _) = true ↔ _
    simp
  constructor
  · rintro ⟨h, hb⟩; exact ⟨h, (key h).1 hb⟩
  · rintro ⟨h, hb⟩; exact ⟨h, (key h).2 hb⟩

theorem strategies_costs (k d : Nat) (f : Bool) {s : Slot} (hs : s.inAt k d) :
    Costs (Tabled.strategies (prog k) f (tabs k d) (goal k s))
      ((if f then [[]] else []) ++ [reqG k s]) 0 := by
  cases s with
  | root =>
    exact ⟨by simp [Tabled.strategies, Tabled.tableStrategies, goal, reqG, orLeaves, orBranches],
      by simp [Tabled.strategies, Tabled.tableStrategies, goal]⟩
  | c j =>
    cases j with
    | zero =>
      exact ⟨by simp [Tabled.strategies, Tabled.tableStrategies, goal, reqG, callGoal, body_zero],
        by simp [Tabled.strategies, Tabled.tableStrategies, goal]⟩
    | succ j =>
      have hb := body_succ (k := k) (i := j) (Nat.lt_of_succ_le hs.1)
      exact ⟨by simp [Tabled.strategies, Tabled.tableStrategies, goal, reqG, callGoal, hb],
        by simp [Tabled.strategies, Tabled.tableStrategies, goal]⟩
  | w =>
    exact ⟨by simp [Tabled.strategies, Tabled.tableStrategies, goal, reqG, callGoal, body_w],
      by simp [Tabled.strategies, Tabled.tableStrategies, goal]⟩
  | z =>
    exact ⟨by simp [Tabled.strategies, Tabled.tableStrategies, goal, reqG],
      by simp [Tabled.strategies, Tabled.tableStrategies, goal]⟩

/-- The set of positions, read as a set of tables. -/
def asSlots (k d : Nat) (S : List Nat) (r : Slot) : Bool := S.contains ((slots k d).idxOf r)

theorem chkV_eq (k d : Nat) (S : List Nat) :
    chkV k d S = fun r => decide (r ∈ slots k d) && !gainedS k d r && (isDone k d r || asSlots k d S r) :=
  rfl

theorem okC_costs (k d : Nat) (S : List Nat) {i : Nat} (h : i < (slots k d).length)
    (hd : ¬ isDone k d (slots k d)[i] = true) :
    Costs (okC k d S i) (okS k d (asSlots k d S) (slots k d)[i])
      (2 * (2 * (3 + (slots k d).length * 6))) := by
  have hin : ((slots k d)[i]).inAt k d := mem_slots.1 (List.getElem_mem h)
  have hdeps := deps_costs k d S (slots k d)[i]
  unfold okC
  rw [getD_finals k d h, getD_tabs k d h]
  have hst := strategies_costs k d (usV k d (slots k d)[i]).1 hin
  refine Costs.mono (c := 0 + 2 * (3 + (slots k d).length * 6)) (Costs.bind hst ?_) (by omega)
  have hu : (usV k d (slots k d)[i]).1 = (uval d (slots k d)[i]).1 := by simp [usV, hd]
  rw [hu]
  unfold okS
  rw [← chkV_eq]
  cases hf : (uval d (slots k d)[i]).1
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, anyL, Bool.false_or]
    refine Costs.congr_val (Costs.mono (c := 2 * (3 + (slots k d).length * 6) + 0)
      (Costs.bind hdeps ?_) (by omega)) rfl
    cases (dep k (slots k d)[i]).all (chkV k d S)
    · exact Costs.pure _
    · exact Costs.pure _
  · exact ⟨by simp [anyL, allL], by simp [anyL, allL]⟩

/-! ## The fixpoint -/

theorem gfpFrom_costs {ok : List Nat → Nat → Cost Bool} {okV : List Nat → Nat → Bool} {c : Nat}
    {T : List Nat} (h : ∀ S i, i ∈ T → Costs (ok S i) (okV S i) c) :
    ∀ (n : Nat) (S : List Nat), S.Sublist T →
      Costs (Tabled.gfpFrom ok n S) (RwLog.gfpFrom okV n S) (n * (T.length * c))
  | 0, S, _ => ⟨rfl, by simp [Tabled.gfpFrom]⟩
  | n + 1, S, hS => by
    have hf := Costs.filterL (xs := S) (f := ok S) (g := okV S) (c := c)
      fun i hi => h S i (hS.subset hi)
    have hlen := hS.length_le
    simp only [Tabled.gfpFrom, RwLog.gfpFrom]
    refine Costs.mono (c := S.length * c + n * (T.length * c)) (Costs.bind hf ?_) ?_
    · by_cases e : (S.filter (okV S)).length = S.length
      · simp only [e, ↓reduceIte]
        exact (Costs.pure S).mono (Nat.zero_le _)
      · simp only [e, ↓reduceIte]
        exact gfpFrom_costs h n _ (List.filter_sublist.trans hS)
    · have := Nat.mul_le_mul_right c hlen
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The completion test by position, as a function on sets. -/
def okV (k d : Nat) (S : List Nat) (i : Nat) : Bool :=
  okS k d (asSlots k d S) ((slots k d).getD i .root)

theorem getD_slots (k d : Nat) {i : Nat} (h : i < (slots k d).length) :
    (slots k d).getD i .root = (slots k d)[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem okV_mono (k d : Nat) : OkMono (okV k d) := by
  intro S S' hsub i hi
  refine okS_mono k d (fun r hr => ?_) _ hi
  simp only [asSlots, List.contains_iff_mem] at hr ⊢
  exact hsub _ hr

/-- The positions of the tables that complete in the round. -/
def doneSet (k d : Nat) : List Nat :=
  (List.range (slots k d).length).filter fun i => completes k d ((slots k d).getD i .root)

theorem mem_doneSet {k d i : Nat} : i ∈ doneSet k d ↔
    ∃ h : i < (slots k d).length, completes k d (slots k d)[i] = true := by
  unfold doneSet
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h, hc⟩; rw [getD_slots k d h] at hc; exact ⟨h, hc⟩
  · rintro ⟨h, hc⟩; rw [← getD_slots k d h] at hc; exact ⟨h, hc⟩

/-- The completion check on the tables of the run: it returns the positions of
the tables that complete, and its cost is cubic in the number of tables. -/
theorem completing_costs (k d : Nat) : ∃ R : List Nat,
    Costs (Tabled.completing (prog k) (finals k d) (tabs k d) (ts1 k d)) R
      ((slots k d).length * ((slots k d).length * (24 * (slots k d).length + 12))) ∧
    ∀ i (h : i < (slots k d).length), R.contains i = completes k d (slots k d)[i] := by
  refine ⟨RwLog.gfpFrom (okV k d) (S0 k d).length (S0 k d), ?_, ?_⟩
  · rw [completing_eq]
    have hc := gfpFrom_costs (ok := okC k d) (okV := okV k d) (T := S0 k d)
      (c := 2 * (2 * (3 + (slots k d).length * 6))) (by
        intro S i hi
        obtain ⟨h, hd, _⟩ := mem_S0.1 hi
        unfold okV
        rw [getD_slots k d h]
        exact okC_costs k d S h hd) (S0 k d).length (S0 k d) (List.Sublist.refl _)
    refine hc.mono ?_
    have hl : (S0 k d).length ≤ (slots k d).length := by
      unfold S0
      refine le_trans (List.length_filter_le _ _) ?_
      simp [tabs]
    have e : 2 * (2 * (3 + (slots k d).length * 6)) = 24 * (slots k d).length + 12 := by ring
    rw [e]
    exact Nat.mul_le_mul hl (Nat.mul_le_mul_right _ hl)
  · intro i h
    have hnd := nodup_slots k d
    rw [Bool.eq_iff_iff, List.contains_iff_mem]
    constructor
    · intro hi
      -- a member of the fixpoint completes
      have hclosed := gfpFrom_closed (okV k d) (S0 k d).length (S0 k d) le_rfl
      refine closed_completes k d (asSlots k d (RwLog.gfpFrom (okV k d) (S0 k d).length (S0 k d)))
        ?_ _ (mem_slots.1 (List.getElem_mem h)) ?_
      · intro s hs hx
        have hmem := mem_slots.2 hs
        have hj := idxOf_lt hmem
        have hsj : (slots k d)[(slots k d).idxOf s] = s := List.getElem_idxOf hj
        simp only [asSlots, List.contains_iff_mem] at hx
        obtain ⟨hS0, hok⟩ := hclosed _ hx
        obtain ⟨_, hd, hg⟩ := mem_S0.1 hS0
        rw [hsj] at hd hg
        refine ⟨hd, hg, ?_⟩
        unfold okV at hok
        rw [getD_slots k d hj, hsj] at hok
        exact hok
      · simp only [asSlots, List.contains_iff_mem]
        rw [hnd.idxOf_getElem i h]
        exact hi
    · intro hc
      -- a table that completes is in the fixpoint
      refine subset_gfpFrom (okV_mono k d) (doneSet k d) ?_ _ _ ?_ i (mem_doneSet.2 ⟨h, hc⟩)
      · intro j hj
        obtain ⟨hj', hcj⟩ := mem_doneSet.1 hj
        unfold okV
        rw [getD_slots k d hj']
        refine completes_closed k d _ ?_ _ (mem_slots.1 (List.getElem_mem hj')) hcj
        intro s hs hcs
        have hmem := mem_slots.2 hs
        have hi := idxOf_lt hmem
        have hsi : (slots k d)[(slots k d).idxOf s] = s := List.getElem_idxOf hi
        simp only [asSlots, List.contains_iff_mem]
        exact mem_doneSet.2 ⟨hi, by rw [hsi]; exact hcs⟩
      · intro j hj
        obtain ⟨hj', hcj⟩ := mem_doneSet.1 hj
        exact mem_S0.2 ⟨hj', ((completes_iff k d _).1 hcj).1, completes_not_gained k d _ hcj⟩

end Sep

end R002

end RwLog
