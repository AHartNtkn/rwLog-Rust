/-
# A request keeps what the cursors mean

`Base st` says the goals of the tables are goals a run may open (boundaries
that pass as boundaries, first-order spans), no two tables have the same
goal, and every edge the state keeps is right about the program. `ProgAll
st` says `Prog` of every strategy of every table. A request keeps both.
-/
import RwLog.Rungs.Symmetric.Progress
import RwLog.Kernel.NormalFormSpans

namespace RwLog

namespace Symmetric

open Traverse Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- A goal a run may open: its boundaries pass as boundaries and its node has
first-order spans. -/
def GoodG (D : Domain R) (g : GoalOf R Rel) : Prop :=
  IsBound D g.lb ∧ IsBound D g.rb ∧ g.node.FO

/-- The goals of the tables are goals a run may open, each the goal of one
table, and the edges kept are right about the program. -/
structure Base (st : StateOf R Rel (Ans D P)) : Prop where
  good : ∀ j g, goalAt st j = some g → GoodG D g
  nodup : ∀ i j g, goalAt st i = some g → goalAt st j = some g → i = j
  edges : EdgesOk st

/-- The same goals at the same places, and the same edges. -/
def SameG (st st' : StateOf R Rel (Ans D P)) : Prop :=
  (∀ j, goalAt st' j = goalAt st j) ∧ st'.edges = st.edges

omit [DecidableEq R] in
theorem SameG.refl (st : StateOf R Rel (Ans D P)) : SameG st st := ⟨fun _ => rfl, rfl⟩

omit [DecidableEq R] in
theorem SameG.trans {a b c : StateOf R Rel (Ans D P)} (h₁ : SameG a b) (h₂ : SameG b c) :
    SameG a c := ⟨fun j => (h₂.1 j).trans (h₁.1 j), h₂.2.trans h₁.2⟩

omit [DecidableEq R] in
theorem Base.same {st st' : StateOf R Rel (Ans D P)} (hB : Base st) (h : SameG st st') :
    Base st' := by
  refine ⟨fun j g hg => hB.good j g ?_, fun i j g hi hj => hB.nodup i j g ?_ ?_, fun e he => ?_⟩
  · rw [← h.1 j]; exact hg
  · rw [← h.1 i]; exact hi
  · rw [← h.1 j]; exact hj
  · rw [h.2] at he; exact hB.edges e he

omit [DecidableEq R] in
theorem sameG_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hf : ∀ t, (f t).goal = t.goal) :
    SameG st (st.modify i f) := ⟨fun j => goalAt_modify st i j f hf, rfl⟩

omit [DecidableEq R] in
/-- The goals of a state with one more table. -/
theorem goalAt_snoc (st : StateOf R Rel (Ans D P)) (t : Table R Rel (Ans D P)) (j : Nat) :
    goalAt ({ st with tables := st.tables ++ [t] } : StateOf R Rel (Ans D P)) j =
      if j < st.tables.length then goalAt st j
      else if j = st.tables.length then some t.goal else none := by
  unfold goalAt
  simp only
  split
  · next h => rw [List.getElem?_append_left h]
  · next h =>
    rw [List.getElem?_append_right (Nat.le_of_not_lt h)]
    split
    · next e => subst e; simp
    · next e =>
      have : j - st.tables.length = (j - st.tables.length - 1) + 1 := by omega
      rw [this]
      simp

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- Opening a goal a run may open keeps the base. -/
theorem base_openGoal {st : StateOf R Rel (Ans D P)} (hB : Base st) (h : GoalOf R Rel)
    (hg : GoodG D h) : Base (openGoal (K := DerivationKernel.over D K hK P) st h).val.1 := by
  have hv := indexFrom_val (P := P) K hK (fun t : Table R Rel (Ans D P) => t.goal) h st.tables 0
  at_cost K hK
  simp only [openGoal, Cost.bind_val]
  split
  · exact hB
  · next hnone =>
    rw [hv] at hnone
    have hno : ∀ j, goalAt st j ≠ some h := by
      intro j hj
      simp only [Option.map_eq_none_iff, List.findIdx?_eq_none_iff] at hnone
      unfold goalAt at hj
      cases ht : st.tables[j]? with
      | none => rw [ht] at hj; cases hj
      | some t =>
        rw [ht] at hj
        have := hnone t (List.mem_of_getElem? ht)
        simp only [decide_eq_false_iff_not] at this
        exact this (Option.some.inj hj)
    have hlt : ∀ j g, goalAt st j = some g → j < st.tables.length := fun j g hj => lt_of_goalAt hj
    simp only [Cost.bind_val, Cost.pure_val]
    refine ⟨fun j g hj => ?_, fun i j g hi hj => ?_, hB.edges⟩
    · rw [goalAt_snoc] at hj
      split at hj
      · exact hB.good j g hj
      · split at hj
        · cases hj; exact hg
        · cases hj
    · rw [goalAt_snoc] at hi hj
      split at hi
      · split at hj
        · exact hB.nodup i j g hi hj
        · split at hj
          · cases hj; exact absurd hi (hno i)
          · cases hj
      · split at hi
        · cases hi
          split at hj
          · exact absurd hj (hno j)
          · split at hj
            · omega
            · cases hj
        · cases hi

theorem sameG_addOption (st : StateOf R Rel (Ans D P)) (i : Nat) (o : Option (Ans D P)) :
    SameG st (addOption (K := DerivationKernel.over D K hK P) i st o).val := by
  have hv := fun a => addAnswer_val (P := P) K hK i st a
  at_cost K hK
  cases o with
  | none => exact SameG.refl st
  | some a =>
    show SameG st (addAnswer (K := DerivationKernel.over D _ hK P) i st a).val
    rw [hv]
    split
    · exact SameG.refl st
    · split
      · split
        · exact sameG_modify st i (app [a]) fun _ => rfl
        · exact (sameG_modify st i (app [a]) fun _ => rfl).trans
            (sameG_modify _ i (app [(Ans.swapA D P a).val]) fun _ => rfl)
      · exact sameG_modify st i (app [a]) fun _ => rfl

theorem sameG_copyFrom (i : Nat) (g : GoalOf R Rel) (isCall : Bool) (m : Nat)
    (st : StateOf R Rel (Ans D P)) (as : List (Ans D P)) :
    SameG st (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val := by
  have h := fun st o => sameG_addOption (K := K) (hK := hK) (P := P) st i o
  at_cost K hK
  refine foldL_inv (fun b => SameG st b) _ as (fun b a _ hb => ?_) st (SameG.refl st)
  dsimp only
  split <;> (rw [Cost.bind_val]; exact hb.trans (h _ _))

theorem sameG_joinPairs (i : Nat) (k : Kind) (xs ys : List (Ans D P))
    (st : StateOf R Rel (Ans D P)) (ps : List (Nat × Nat)) :
    SameG st (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val := by
  have h := fun st o => sameG_addOption (K := K) (hK := hK) (P := P) st i o
  at_cost K hK
  refine foldL_inv (fun b => SameG st b) _ ps (fun b p _ hb => ?_) st (SameG.refl st)
  split
  · rw [Cost.bind_val]; exact hb.trans (h _ _)
  · exact hb

theorem sameG_pushTake (i : Nat) (k : Kind) (left : Bool) (x : Ans D P)
    (st : StateOf R Rel (Ans D P)) (ys : List (Ans D P)) :
    SameG st (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val := by
  have h := fun st o => sameG_addOption (K := K) (hK := hK) (P := P) st i o
  at_cost K hK
  refine foldL_inv (fun b => SameG st b) _ ys (fun b y _ hb => ?_) st (SameG.refl st)
  rw [Cost.bind_val]
  exact hb.trans (h _ _)

omit [DecidableEq R] in
/-- The goal opened for an answer that is pushed is a goal a run may open. -/
theorem good_pushG (hL : D.Lawful P.sorts.interp) {g : GoalOf R Rel} (hg : GoodG D g)
    {other : Rel} (ho : other.FO) (k : Kind) (left : Bool) (x : Ans D P) :
    GoodG D (pushG D g other k left x) := by
  have hr : ∀ a : R, IsBound D (D.rightBound a) := fun a r h => hL.rightBound_isBound a r h
  have hl : ∀ a : R, IsBound D (D.leftBound a) := fun a => hr _
  cases k <;> cases left
  · exact ⟨hg.1, hl _, ho⟩
  · exact ⟨hr _, hg.2.1, ho⟩
  · exact ⟨hl _, hr _, ho⟩
  · exact ⟨hl _, hr _, ho⟩

theorem base_pushOpen (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (hB : Base st) {g : GoalOf R Rel} (hg : GoodG D g) {other : Rel} (ho : other.FO) (k : Kind)
    (left : Bool) (xs : List (Ans D P)) :
    Base (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1 := by
  have hp := pushGoal_val (K := K) (hK := hK) (P := P) g other k left
  have hop := fun st hB h hg => base_openGoal (K := K) (hK := hK) (P := P) (st := st) hB h hg
  at_cost K hK
  refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Ans D P × Nat × Nat) =>
    Base acc.1) _ xs (fun b x _ hb => ?_) (st, []) hB
  simp only [Cost.bind_val, Cost.pure_val, hp]
  exact hop _ hb _ (good_pushG hL hg ho k left x)

theorem base_checkOpen {st : StateOf R Rel (Ans D P)} (hB : Base st) {g : GoalOf R Rel}
    (hg : GoodG D g) {other : Rel} (ho : other.FO) (left : Bool) (ps : List R)
    (hps : ∀ p ∈ ps, D.isBound p = true) :
    Base (checkOpen (K := DerivationKernel.over D K hK P) g left other st ps).val.1 := by
  have hop := fun st hB h hg => base_openGoal (K := K) (hK := hK) (P := P) (st := st) hB h hg
  at_cost K hK
  refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × List Nat => Base acc.1) _ ps
    (fun b p hp hb => ?_) (st, []) hB
  simp only [Cost.bind_val, Cost.pure_val]
  refine hop _ hb _ ?_
  have hpb : IsBound D (some p) := fun r h => by cases h; exact hps p hp
  split
  · exact ⟨hpb, hg.2.1, ho⟩
  · exact ⟨hg.1, hpb, ho⟩

theorem base_edgeOf (hR : ReadOk D P K hK) {st : StateOf R Rel (Ans D P)} (hB : Base st)
    (last : Bool) (n : Rel) :
    Base (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1 := by
  obtain ⟨h1, h2, -⟩ := edgeOf_spec hR hB.edges last n
  have hg : ∀ j, goalAt (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1 j =
      goalAt st j := fun j => by unfold goalAt; rw [h2]
  refine ⟨fun j g hj => hB.good j g ?_, fun i j g hi hj => hB.nodup i j g ?_ ?_, h1⟩
  · rw [← hg j]; exact hj
  · rw [← hg i]; exact hi
  · rw [← hg j]; exact hj

omit [DecidableEq R] [Answer R] in
/-- The nodes of the two sides of a split of a node with first-order spans
have first-order spans. -/
theorem SplitAt.fo {g L Rg : GoalOf R Rel} {k : Kind} (h : SplitAt g k L Rg) (hg : g.node.FO) :
    L.node.FO ∧ Rg.node.FO := by
  cases k with
  | seq =>
    obtain ⟨xs, i, l, r, -, -, -, hl, hr, rfl, rfl⟩ := h
    exact ⟨hg.interval hl, hg.interval hr⟩
  | and =>
    obtain ⟨xs, i, x, r, hv, hx, hr, rfl, rfl⟩ := h
    refine ⟨hg.view_members ?_, hg.without hr⟩
    rw [hv]
    exact List.mem_of_getElem? hx

/-- The work of a strategy keeps the base. -/
theorem base_work (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    {st : StateOf R Rel (Ans D P)} (hB : Base st) (whole : Bool) (i : Nat) (g : GoalOf R Rel)
    (s : Strat Rel (Ans D P)) (hg : GoodG D g) (hs : Prog st i g s) :
    Base (work (K := DerivationKernel.over D K hK P) whole i g st s).val.1 := by
  have h1 := fun st o => sameG_addOption (K := K) (hK := hK) (P := P) st i o
  have h2 := fun (isCall : Bool) (m : Nat) st as =>
    sameG_copyFrom (K := K) (hK := hK) (P := P) i g isCall m st as
  have h3 := fun k xs ys st ps => sameG_joinPairs (K := K) (hK := hK) (P := P) i k xs ys st ps
  have h4 := fun k left x st ys => sameG_pushTake (K := K) (hK := hK) (P := P) i k left x st ys
  have h5 := fun (other : Rel) (ho : other.FO) k left xs =>
    base_pushOpen (K := K) (hK := hK) hL hB hg ho k left xs
  have h6 := fun left n => edgeOf_spec hR hB.edges left n
  have h7 := fun left n => base_edgeOf hR hB left n
  have h8 := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') (other : Rel) (ho : other.FO)
      left ps hps =>
    base_checkOpen (K := K) (hK := hK) hB' hg ho left ps hps
  clear hR
  at_cost K hK
  cases s with
  | span ran =>
    cases ran
    · simp only [work, Cost.bind_val, Cost.pure_val]
      exact hB.same (h1 _ _)
    · exact hB
  | copy isCall subs =>
    simp only [work]
    split
    · simp only [Cost.bind_val, Cost.pure_val]
      exact hB.same (foldL_inv (fun b => SameG st b) _ _
        (fun b p _ hb => hb.trans (h2 isCall p.2 _ _)) st (SameG.refl st))
    · split
      · exact hB
      · simp only [Cost.bind_val, Cost.pure_val]
        exact hB.same (h2 isCall _ _ _)
  | join k a b c =>
    simp only [work]
    split
    · simp only [Cost.bind_val, Cost.pure_val]
      exact hB.same (h3 _ _ _ _ _)
    · split
      · exact hB
      · simp only [Cost.bind_val, Cost.pure_val]
        exact hB.same (h3 _ _ _ _ _)
  | push k left side other todo subs =>
    dsimp only [Prog] at hs
    obtain ⟨L, Rg, s1, -, s3, -, -⟩ := hs
    have ho : other.FO := by
      rw [s3]
      split
      · exact (s1.fo hg.2.2).2
      · exact (s1.fo hg.2.2).1
    simp only [work]
    split
    · exact hB
    · split
      · cases todo <;>
        · erw [Cost.bind_val]
          simp only [Cost.bind_val, Cost.pure_val]
          exact foldL_inv (fun b => Base b) _ _ (fun b e _ hb => hb.same (h4 _ _ _ _ _)) _
            (h5 other ho k left _)
      · split
        · simp only [Cost.bind_val, Cost.pure_val]
          exact hB
        · simp only [Cost.bind_val, Cost.pure_val]
          exact h5 other ho k left _
        · split
          · exact hB
          · simp only [Cost.bind_val, Cost.pure_val]
            exact hB.same (h4 _ _ _ _ _)
  | check left side other c =>
    dsimp only [Prog] at hs
    obtain ⟨L, Rg, s1, -, s3, -⟩ := hs
    have ho : other.FO := by
      rw [s3]
      split
      · exact (s1.fo hg.2.2).2
      · exact (s1.fo hg.2.2).1
    cases c with
    | reading =>
      simp only [work, Cost.bind_val]
      split
      · exact h7 _ _
      · exact h7 _ _
      · next ps heq =>
        simp only [Cost.bind_val, Cost.pure_val]
        exact h8 _ (h7 _ _) other ho left ps ((h6 left side).2.2 ps heq).1
    | off => exact hB
    | opened subs => exact hB

end kernel

end Symmetric

end RwLog
