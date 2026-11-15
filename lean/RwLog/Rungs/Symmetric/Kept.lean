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
    obtain ⟨xs, i, x, r, hv, -, hx, hr, rfl, rfl⟩ := h
    refine ⟨hg.view_members ?_, hg.without hr⟩
    rw [hv]
    exact List.mem_of_getElem? hx

/-- The work of a strategy keeps the base. -/
theorem base_work (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    {st : StateOf R Rel (Ans D P)} (hB : Base st) (i : Nat) (g : GoalOf R Rel)
    (s : Strat Rel (Ans D P)) (hg : GoodG D g) (hs : Prog st i g s) :
    Base (work (K := DerivationKernel.over D K hK P) i g st s).val.1 := by
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
    · exact hB
    · simp only [Cost.bind_val, Cost.pure_val]
      exact hB.same (h2 isCall _ _ _)
  | join k a b c =>
    simp only [work]
    split
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
        exact h8 _ (h7 _ _) other ho left ps ((h6 left side).2.2.1 ps heq).1
    | off => exact hB
    | opened subs => exact hB

/-! ## The strategies of a goal start right -/

theorem prog_splitGroup {st : StateOf R Rel (Ans D P)} (hB : Base st) (w : Nat) (k : Kind)
    (L Rg g : GoalOf R Rel) (hL' : GoodG D L) (hR' : GoodG D Rg) (hs : SplitAt g k L Rg) :
    Frame w st (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 ∧
      Base (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 ∧
      (∀ s ∈ (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.2.strats,
        Prog (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 w g s) ∧
      ∃ a b, (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.2.strats =
          [.join k a b Cursor.start, .push k true a Rg.node none [],
            .push k false b L.node none []] ∧
        goalAt (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 a = some L ∧
        goalAt (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 b = some Rg := by
  have hF := (inner_splitGroup (K := K) (hK := hK) (P := P) (w := w) k L Rg st).frame
  have hB1 := base_openGoal (K := K) (hK := hK) hB L hL'
  have hB2 := base_openGoal (K := K) (hK := hK) hB1 Rg hR'
  have hg1 := openGoal_goalAt (K := K) (hK := hK) (P := P) st L
  have hg2 := openGoal_goalAt (K := K) (hK := hK) (P := P)
    (openGoal (K := DerivationKernel.over D K hK P) st L).val.1 Rg
  have hg1' := (reach_openGoal (K := K) (hK := hK) _ Rg).ext _ _ hg1
  at_cost K hK
  simp only [splitGroup, Cost.bind_val, Cost.pure_val] at hF ⊢
  refine ⟨hF, hB2, fun s hs' => ?_, _, _, rfl, hg1', hg2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
  rcases hs' with rfl | rfl | rfl
  · dsimp only [Prog]
    exact ⟨L, Rg, hs, hg1', hg2, Cursor.ok_start _ _,
      fun p q x y hb => absurd hb (Cursor.before_start p q)⟩
  · dsimp only [Prog]
    exact ⟨L, Rg, hs, hg1', rfl, (fun l hl => by cases hl), (fun e he => by cases he),
      fun _ => rfl⟩
  · dsimp only [Prog]
    exact ⟨L, Rg, hs, hg2, rfl, (fun l hl => by cases hl), (fun e he => by cases he),
      fun _ => rfl⟩

theorem prog_checkOf (hR : ReadOk D P K hK) {st : StateOf R Rel (Ans D P)} (hB : Base st)
    (w : Nat) (left : Bool) (side other : Rel) :
    Frame w st (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.1 ∧
      Base (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.1 ∧
      (∀ s ∈ (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.2,
        s = .check left side other .reading) ∧
      (Reads D P side left none ∨ .check left side other .reading ∈
        (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.2) := by
  have hF := (inner_checkOf (K := K) (hK := hK) (P := P) (w := w) st left side other).frame
  have h := base_edgeOf hR hB left side
  have hrd := (edgeOf_spec hR hB.edges left side).2.2.2
  clear hR
  at_cost K hK
  simp only [checkOf, Cost.bind_val, Cost.pure_val] at hF ⊢
  refine ⟨hF, h, fun s hs => ?_, ?_⟩
  · split at hs
    · cases hs
    · exact List.mem_singleton.1 hs
  · split
    · next he => exact .inl (hrd _ he)
    · exact .inr (List.mem_singleton.2 rfl)

/-- What the groups of a chain have when the places `done` have been
passed. -/
def ChainDone (w : Nat) (g : GoalOf R Rel) (n : Nat) (st : StateOf R Rel (Ans D P))
    (done : List Nat) (acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) ×
      List (Strat Rel (Ans D P))) : Prop :=
  Frame w st acc.1 ∧ Base acc.1 ∧ (∀ gr ∈ acc.2.1, ∀ s ∈ gr.strats, Prog acc.1 w g s) ∧
    (∀ s ∈ acc.2.2, Prog acc.1 w g s) ∧
    ∀ i ∈ done, ∀ l r, g.node.interval 0 i = some l → g.node.interval i n = some r →
      (∃ gr ∈ acc.2.1, ∃ a b, goalAt acc.1 a = some ⟨g.lb, l, none⟩ ∧
        goalAt acc.1 b = some ⟨none, r, g.rb⟩ ∧ .join .seq a b Cursor.start ∈ gr.kinds ∧
        .push .seq true a r none [] ∈ gr.kinds ∧ .push .seq false b l none [] ∈ gr.kinds) ∧
      (Reads D P l true none ∨ .check true l r .reading ∈ acc.2.2) ∧
      (Reads D P r false none ∨ .check false r l .reading ∈ acc.2.2)

theorem mem_range_drop_one {i n : Nat} (h0 : 0 < i) (hi : i < n) :
    i ∈ (List.range n).drop 1 := by
  rw [List.mem_iff_getElem?]
  refine ⟨i - 1, ?_⟩
  rw [List.getElem?_drop, List.getElem?_range (by omega)]
  congr 1
  omega

theorem ChainDone.out {w : Nat} {g : GoalOf R Rel} {xs : List Rel} {st : StateOf R Rel (Ans D P)}
    {acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) × List (Strat Rel (Ans D P))}
    (h : ChainDone w g xs.length st ((List.range xs.length).drop 1) acc)
    (hv : g.node.view = .chain xs) :
    Base acc.1 ∧ (∀ gr ∈ acc.2.1, ∀ s ∈ gr.strats, Prog acc.1 w g s) ∧
      (∀ s ∈ acc.2.2, Prog acc.1 w g s) ∧
      ∀ L Rg, SplitAt g .seq L Rg →
        (∃ gr ∈ acc.2.1, ∃ a b, goalAt acc.1 a = some L ∧ goalAt acc.1 b = some Rg ∧
          .join .seq a b Cursor.start ∈ gr.kinds ∧ .push .seq true a Rg.node none [] ∈ gr.kinds ∧
          .push .seq false b L.node none [] ∈ gr.kinds) ∧
        ∀ left : Bool, Reads D P (if left then L.node else Rg.node) left none ∨
          .check left (if left then L.node else Rg.node) (if left then Rg.node else L.node)
            .reading ∈ acc.2.2 := by
  obtain ⟨-, k1, k2, k3, k4⟩ := h
  refine ⟨k1, k2, k3, fun L Rg hsp => ?_⟩
  obtain ⟨xs', i, l, r, hv', h0, hi, hl, hr, rfl, rfl⟩ := hsp
  rw [hv] at hv'
  cases hv'
  obtain ⟨hgrp, c1, c2⟩ := k4 i (mem_range_drop_one h0 hi) l r hl hr
  refine ⟨hgrp, fun left => ?_⟩
  cases left
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact c2
  · simp only [↓reduceIte]
    exact c1

theorem prog_chainGroups (hR : ReadOk D P K hK) {st : StateOf R Rel (Ans D P)} (hB : Base st)
    (w : Nat) (ho : Open st w) (g : GoalOf R Rel) (hg : GoodG D g) {xs : List Rel}
    (hv : g.node.view = .chain xs) :
    ChainDone w g xs.length st ((List.range xs.length).drop 1)
      (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val := by
  have hsg := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') l r hl hr hs =>
    prog_splitGroup (K := K) (hK := hK) hB' w .seq ⟨g.lb, l, none⟩ ⟨none, r, g.rb⟩ g hl hr hs
  have hco := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') left side other =>
    prog_checkOf hR hB' w left side other
  clear hR
  at_cost K hK
  refine foldL_done (ChainDone w g xs.length st) _ _ (fun done acc i _ hb => ?_)
    (st, [], []) ⟨Frame.refl w st, hB, (fun gr hgr => by cases hgr), (fun s hs => by cases hs),
      fun i hi => by cases hi⟩
  obtain ⟨hf, hbase, hpg, hpc, hdone⟩ := hb
  simp only [Cost.bind_val]
  split
  · next l r hl hr =>
    simp only [Cost.bind_val, Cost.pure_val]
    have hl' : g.node.interval 0 i = some l := hl
    have hr' : g.node.interval i xs.length = some r := hr
    have h0 : 0 < i := by
      unfold RelOf.interval at hl'
      split at hl'
      · rename_i c; exact c.1
      · cases hl'
    have hi : i < xs.length := by
      unfold RelOf.interval at hr'
      split at hr'
      · rename_i c; exact c.1
      · cases hr'
    have hsplit : SplitAt g .seq ⟨g.lb, l, none⟩ ⟨none, r, g.rb⟩ :=
      ⟨xs, i, l, r, hv, h0, hi, hl', hr', rfl, rfl⟩
    have hfo := hsplit.fo hg.2.2
    have ho1 := hf.isOpen ho
    obtain ⟨f1, b1, p1, a, b', hstr, hga, hgb⟩ := hsg acc.1 hbase l r
      ⟨hg.1, isBound_none D, hfo.1⟩ ⟨isBound_none D, hg.2.1, hfo.2⟩ hsplit
    obtain ⟨f2, b2, c2, r2⟩ := hco _ b1 true l r
    obtain ⟨f3, b3, c3, r3⟩ := hco _ b2 false r l
    have S1 := f1.stable ho1
    have ho2 := f1.isOpen ho1
    have S2 := f2.stable ho2
    have S3 := f3.stable (f2.isOpen ho2)
    refine ⟨hf.trans (f1.trans (f2.trans f3)), b3, fun gr hgr s hs => ?_, fun s hs => ?_,
      fun i' hi' l' r' hl'' hr'' => ?_⟩
    · rcases List.mem_append.1 hgr with hgr | hgr
      · exact (hpg gr hgr s hs).mono (S1.trans (S2.trans S3))
      · obtain rfl := List.mem_singleton.1 hgr
        exact (p1 s hs).mono (S2.trans S3)
    · rcases List.mem_append.1 hs with hs | hs
      · rcases List.mem_append.1 hs with hs | hs
        · exact (hpc s hs).mono (S1.trans (S2.trans S3))
        · rw [c2 s hs]
          dsimp only [Prog]
          exact ⟨_, _, hsplit, rfl, rfl, trivial⟩
      · rw [c3 s hs]
        dsimp only [Prog]
        exact ⟨_, _, hsplit, rfl, rfl, trivial⟩
    · rcases List.mem_append.1 hi' with hi' | hi'
      · obtain ⟨⟨gr, hgr, a0, b0, ha0, hb0, k1, k2, k3⟩, d1, d2⟩ := hdone i' hi' l' r' hl'' hr''
        exact ⟨⟨gr, List.mem_append_left _ hgr, a0, b0, (S1.trans (S2.trans S3)).ext _ _ ha0,
            (S1.trans (S2.trans S3)).ext _ _ hb0, k1, k2, k3⟩,
          d1.imp id (fun h => List.mem_append_left _ (List.mem_append_left _ h)),
          d2.imp id (fun h => List.mem_append_left _ (List.mem_append_left _ h))⟩
      · obtain rfl := List.mem_singleton.1 hi'
        rw [hl'] at hl''
        rw [hr'] at hr''
        cases hl''
        cases hr''
        refine ⟨⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), a, b',
          (S2.trans S3).ext _ _ hga, (S2.trans S3).ext _ _ hgb, ?_, ?_, ?_⟩, ?_, ?_⟩
        · simp [Group.kinds, hstr, Strat.kind]
        · simp [Group.kinds, hstr, Strat.kind]
        · simp [Group.kinds, hstr, Strat.kind]
        · exact r2.imp id (fun h => List.mem_append_left _ (List.mem_append_right _ h))
        · exact r3.imp id (fun h => List.mem_append_right _ h)
  · next hneg =>
    refine ⟨hf, hbase, hpg, hpc, fun i' hi' l' r' hl'' hr'' => ?_⟩
    rcases List.mem_append.1 hi' with hi' | hi'
    · exact hdone i' hi' l' r' hl'' hr''
    · obtain rfl := List.mem_singleton.1 hi'
      exact (hneg l' r' hl'' hr'').elim

/-- What the groups of a meet have when the members `done` have been
passed. -/
def MeetDone (w : Nat) (g : GoalOf R Rel) (xs : List Rel) (st : StateOf R Rel (Ans D P))
    (done : List Nat) (acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P))) : Prop :=
  Frame w st acc.1 ∧ Base acc.1 ∧ (∀ gr ∈ acc.2, ∀ s ∈ gr.strats, Prog acc.1 w g s) ∧
    ∀ i ∈ done, ∀ l r, xs[i]? = some l → g.node.without i = some r →
      ∃ gr ∈ acc.2, ∃ a b, goalAt acc.1 a = some ⟨g.lb, l, g.rb⟩ ∧
        goalAt acc.1 b = some ⟨g.lb, r, g.rb⟩ ∧ .join .and a b Cursor.start ∈ gr.kinds ∧
        .push .and true a r none [] ∈ gr.kinds ∧ .push .and false b l none [] ∈ gr.kinds

omit [DecidableEq R] [Answer R] in
theorem no_split {g : GoalOf R Rel}
    (h : ∀ xs, g.node.view ≠ .chain xs ∧ g.node.view ≠ .meet xs) {k : Kind}
    {L Rg : GoalOf R Rel} (hs : SplitAt g k L Rg) : False := by
  rcases hs.view with ⟨-, xs, e⟩ | ⟨-, xs, e⟩
  · exact (h xs).1 e
  · exact (h xs).2 e

theorem MeetDone.out {w : Nat} {g : GoalOf R Rel} {xs : List Rel} {st : StateOf R Rel (Ans D P)}
    {acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P))}
    (h : MeetDone w g xs st (andSplits xs.length) acc) (hv : g.node.view = .meet xs) :
    Base acc.1 ∧ (∀ gr ∈ acc.2, ∀ s ∈ gr.strats, Prog acc.1 w g s) ∧ Full acc.1 g acc.2 := by
  obtain ⟨-, k1, k2, k3⟩ := h
  refine ⟨k1, k2, Full.of_view hv (fun _ e => by cases e) (fun _ _ e => by cases e)
    (fun _ e => by cases e) (fun k L Rg hsp => ?_) (fun L Rg hsp => ?_)⟩
  · cases k with
    | seq =>
      obtain ⟨xs', i, l, r, hv', -⟩ := hsp
      rw [hv] at hv'
      cases hv'
    | and =>
      obtain ⟨xs', i, l, r, hv', hi, hl, hr, rfl, rfl⟩ := hsp
      rw [hv] at hv'
      cases hv'
      exact k3 i hi l r hl hr
  · obtain ⟨xs', i, l, r, hv', -⟩ := hsp
    rw [hv] at hv'
    cases hv'

/-- **The strategies made for a goal start right, and there is one for
every way to answer it**; making them keeps the base. -/
theorem prog_expand (hR : ReadOk D P K hK) (hP : ProgFO P) {st : StateOf R Rel (Ans D P)}
    (hB : Base st) (w : Nat) (ho : Open st w) (g : GoalOf R Rel) (hg : GoodG D g)
    (hn : Normal g.node) :
    Base (expand (K := DerivationKernel.over D K hK P) g st).val.1 ∧
      (∀ gr ∈ (expand (K := DerivationKernel.over D K hK P) g st).val.2, ∀ s ∈ gr.strats,
        Prog (expand (K := DerivationKernel.over D K hK P) g st).val.1 w g s) ∧
      Full (expand (K := DerivationKernel.over D K hK P) g st).val.1 g
        (expand (K := DerivationKernel.over D K hK P) g st).val.2 := by
  have hop := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') h hg' =>
    base_openGoal (K := K) (hK := hK) hB' h hg'
  have hog := fun st' h => openGoal_goalAt (K := K) (hK := hK) (P := P) st' h
  have hin := fun st' h =>
    (inner_openGoal (K := K) (hK := hK) (P := P) (w := 0) st' h).reach.ext
  have hcg := fun xs (hv : g.node.view = .chain xs) =>
    (prog_chainGroups hR hB w ho g hg hv).out hv
  have hsg := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') l r hl hr hs =>
    prog_splitGroup (K := K) (hK := hK) hB' w .and ⟨g.lb, l, g.rb⟩ ⟨g.lb, r, g.rb⟩ g hl hr hs
  have one : ∀ (st' : StateOf R Rel (Ans D P)) (s : Strat Rel (Ans D P)) (V : NodeView Span Rel),
      g.node.view = V → (∀ xs, V ≠ .chain xs ∧ V ≠ .meet xs) →
      (∀ s0, V = .span s0 → s.kind = .span false) →
      (∀ n f, V = .call n f → s.kind = .copy true []) →
      (∀ xs, V = .union xs → s.kind = .copy false []) → Full st' g [⟨0, [s], []⟩] := by
    intro st' s V hv hns h1 h2 h3
    have hmem : ∀ x, s.kind = x → ∃ gr ∈ [(⟨0, [s], []⟩ : Group Rel (Ans D P))], x ∈ gr.kinds :=
      fun x e => ⟨_, List.mem_singleton.2 rfl, by simp [Group.kinds, e]⟩
    exact Full.of_view hv (fun s0 e => hmem _ (h1 s0 e)) (fun n f e => hmem _ (h2 n f e))
      (fun xs e => hmem _ (h3 xs e))
      (fun k L Rg hsp => (no_split (fun xs => by rw [hv]; exact hns xs) hsp).elim)
      (fun L Rg hsp => (no_split (fun xs => by rw [hv]; exact hns xs) hsp).elim)
  clear hR
  at_cost K hK
  simp only [expand, Cost.bind_val]
  split
  · next hv =>
    have hspan : ∃ s, g.node = .span s := forget_span hv
    obtain ⟨s0, hs0⟩ := hspan
    refine ⟨hB, fun gr hgr s hs => ?_, one _ _ (.span s0) (by rw [hs0]; rfl)
      (fun _ => ⟨nofun, nofun⟩) (fun _ _ => rfl) (fun _ _ e => by cases e)
      (fun _ e => by cases e)⟩
    obtain rfl := List.mem_singleton.1 hgr
    obtain rfl := List.mem_singleton.1 hs
    dsimp only [Prog]
    exact ⟨⟨s0, hs0⟩, fun h => by cases h⟩
  · next f fl hv =>
    have hvc := forget_call_view hv
    simp only [Cost.bind_val]
    split
    · next hb =>
      have hb' : Charged.bodyOf P g.node = none := hb
      refine ⟨hB, fun gr hgr s hs => ?_, one _ _ _ hvc (fun _ => ⟨nofun, nofun⟩)
        (fun _ e => by cases e) (fun _ _ _ => rfl) (fun _ e => by cases e)⟩
      obtain rfl := List.mem_singleton.1 hgr
      obtain rfl := List.mem_singleton.1 hs
      dsimp only [Prog]
      obtain ⟨b, hb''⟩ := forget_call (P := P) hv
      rw [hb'] at hb''
      cases hb''
    · next b hb =>
      have hb' : Charged.bodyOf P g.node = some b := hb
      simp only [Cost.bind_val, Cost.pure_val]
      refine ⟨hop _ hB _ ⟨hg.1, hg.2.1, bodyOf_fo hP hb'⟩, fun gr hgr s hs => ?_,
        one _ _ _ hvc (fun _ => ⟨nofun, nofun⟩) (fun _ e => by cases e) (fun _ _ _ => rfl)
          (fun _ e => by cases e)⟩
      obtain rfl := List.mem_singleton.1 hgr
      obtain rfl := List.mem_singleton.1 hs
      dsimp only [Prog]
      refine ⟨fun _ => ⟨b, hb'⟩, (fun h => by cases h), by simp [copyMembers, hb'],
        fun m j pos hm => ?_⟩
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact ⟨b, by simp [copyMembers, hb'], hog _ _, Read.zero _ _ _ _⟩
      | succ m => simp at hm
  · next xs hv =>
    simp only [Cost.bind_val, Cost.pure_val]
    have hvu := forget_union hv
    have hparts := hn.view_union_eq hvu
    have keyB := foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Nat × Nat) => Base acc.1)
      (fun acc x => do
        let (st, j) ← openGoal (K := DerivationKernel.over D _ hK P) acc.1 ⟨g.lb, x, g.rb⟩
        pure (st, acc.2 ++ [(j, 0)])) xs (fun b x hx hb => by
          simp only [Cost.bind_val, Cost.pure_val]
          exact hop _ hb _ ⟨hg.1, hg.2.1, hg.2.2.view_members (by rw [hvu]; exact hx)⟩)
      (st, []) hB
    obtain ⟨-, es, hes, hall⟩ := foldL_open
      (fun (acc : StateOf R Rel (Ans D P) × List (Nat × Nat)) x => do
        let (st, j) ← openGoal (K := DerivationKernel.over D _ hK P) acc.1 ⟨g.lb, x, g.rb⟩
        pure (st, acc.2 ++ [(j, 0)]))
      (fun st' x (e : Nat × Nat) => e.2 = 0 ∧ goalAt st' e.1 = some ⟨g.lb, x, g.rb⟩)
      (fun acc x => by
        simp only [Cost.bind_val, Cost.pure_val]
        exact ⟨hin _ _, _, rfl, rfl, hog _ _⟩)
      (fun _ _ _ _ hE h => ⟨h.1, hE _ _ h.2⟩) xs (st, [])
    rw [List.nil_append] at hes
    refine ⟨keyB, fun gr hgr s hs => ?_, one _ _ _ hvu (fun _ => ⟨nofun, nofun⟩)
      (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ => rfl)⟩
    obtain rfl := List.mem_singleton.1 hgr
    obtain rfl := List.mem_singleton.1 hs
    dsimp only [Prog]
    rw [hes]
    refine ⟨(fun h => by cases h), fun _ => ⟨xs, hvu⟩,
      by simp only [copyMembers, ← hparts]; exact hall.length_eq.symm,
      fun m j pos hm => ?_⟩
    obtain ⟨x, hx, h0, hgx⟩ := forall₂_getElem? hall.flip hm
    simp only at h0
    subst h0
    exact ⟨x, by simp only [copyMembers, ← hparts]; exact hx, hgx, Read.zero _ _ _ _⟩
  · next xs hv =>
    simp only [Cost.bind_val, Cost.pure_val]
    have hvc := forget_chain hv
    obtain ⟨h1, h2, h3, h4⟩ := hcg xs hvc
    generalize (chainGroups (K := DerivationKernel.over D _ hK P) g xs.length st).val = r
      at h1 h2 h3 h4 ⊢
    have hin' : ∀ gr ∈ r.2.1, gr ∈ (if r.2.2.isEmpty then r.2.1 else r.2.1 ++ [⟨0, r.2.2, []⟩]) :=
      fun gr h => by
        split
        · exact h
        · exact List.mem_append_left _ h
    have hck : ∀ s ∈ r.2.2, (⟨0, r.2.2, []⟩ : Group Rel (Ans D P)) ∈
        (if r.2.2.isEmpty then r.2.1 else r.2.1 ++ [⟨0, r.2.2, []⟩]) := fun s hs => by
      split
      · next he => rw [List.isEmpty_iff.1 he] at hs; cases hs
      · exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    refine ⟨h1, fun gr hgr s hs => ?_, Full.of_view hvc (fun _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ e => by cases e) (fun k L Rg hsp => ?_)
      (fun L Rg hsp left => ?_)⟩
    · split at hgr
      · exact h2 gr hgr s hs
      · rcases List.mem_append.1 hgr with hgr | hgr
        · exact h2 gr hgr s hs
        · obtain rfl := List.mem_singleton.1 hgr
          exact h3 s hs
    · cases k with
      | seq =>
        obtain ⟨gr, hgr, rest⟩ := (h4 L Rg hsp).1
        exact ⟨gr, hin' gr hgr, rest⟩
      | and =>
        obtain ⟨xs', i, l, r', hv', -⟩ := hsp
        rw [hvc] at hv'
        cases hv'
    · rcases (h4 L Rg hsp).2 left with h | h
      · exact .inl (.inl h)
      · exact .inr ⟨_, hck _ h, List.mem_map.2 ⟨_, h, rfl⟩⟩
  · next xs hv =>
    have hvm := forget_meet hv
    refine MeetDone.out (foldL_done (MeetDone w g xs st) _ _ (fun done acc i hi hb => ?_)
      (st, []) ⟨Frame.refl w st, hB, (fun gr hgr => by cases hgr), fun i hi => by cases hi⟩) hvm
    obtain ⟨hf, hbase, hpg, hdone⟩ := hb
    simp only [Cost.bind_val]
    split
    · next l r hl hr =>
      simp only [Cost.bind_val, Cost.pure_val]
      have hr' : g.node.without i = some r := hr
      have hsplit : SplitAt g .and ⟨g.lb, l, g.rb⟩ ⟨g.lb, r, g.rb⟩ :=
        ⟨xs, i, l, r, hvm, hi, hl, hr', rfl, rfl⟩
      have hfo := hsplit.fo hg.2.2
      obtain ⟨f1, b1, p1, a, b', hstr, hga, hgb⟩ := hsg acc.1 hbase l r ⟨hg.1, hg.2.1, hfo.1⟩
        ⟨hg.1, hg.2.1, hfo.2⟩ hsplit
      have S1 := f1.stable (hf.isOpen ho)
      refine ⟨hf.trans f1, b1, fun gr hgr s hs => ?_, fun i' hi' l' r' hl'' hr'' => ?_⟩
      · rcases List.mem_append.1 hgr with hgr | hgr
        · exact (hpg gr hgr s hs).mono S1
        · obtain rfl := List.mem_singleton.1 hgr
          exact p1 s hs
      · rcases List.mem_append.1 hi' with hi' | hi'
        · obtain ⟨gr, hgr, a0, b0, ha0, hb0, k1, k2, k3⟩ := hdone i' hi' l' r' hl'' hr''
          exact ⟨gr, List.mem_append_left _ hgr, a0, b0, S1.ext _ _ ha0, S1.ext _ _ hb0,
            k1, k2, k3⟩
        · obtain rfl := List.mem_singleton.1 hi'
          rw [hl] at hl''
          rw [hr'] at hr''
          cases hl''
          cases hr''
          refine ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), a, b', hga, hgb,
            ?_, ?_, ?_⟩
          · simp [Group.kinds, hstr, Strat.kind]
          · simp [Group.kinds, hstr, Strat.kind]
          · simp [Group.kinds, hstr, Strat.kind]
    · next hneg =>
      refine ⟨hf, hbase, hpg, fun i' hi' l' r' hl'' hr'' => ?_⟩
      rcases List.mem_append.1 hi' with hi' | hi'
      · exact hdone i' hi' l' r' hl'' hr''
      · obtain rfl := List.mem_singleton.1 hi'
        exact (hneg l' r' hl'' hr'').elim

/-! ## A whole request -/

/-- Every strategy of every table has cursors that mean what `Prog` says. -/
def ProgAll (st : StateOf R Rel (Ans D P)) : Prop :=
  ∀ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t → ∀ gs, t.groups = some gs →
    ∀ gr ∈ gs, ∀ s ∈ gr.strats, Prog st i t.goal s

/-- Whether a goal has a race: its node is a chain. -/
def hasRace (g : GoalOf R Rel) : Bool :=
  match g.node.view.forget with
  | .chain _ => true
  | _ => false

/-- The race a goal starts with. -/
theorem raceOf_val (g : GoalOf R Rel) :
    (raceOf (K := DerivationKernel.over D K hK P) g).val =
      if hasRace g then some ⟨0, 0, 0⟩ else none := by
  at_cost K hK
  simp only [raceOf, Cost.bind_val, Cost.pure_val, hasRace]
  have e2 : (DerivationKernel.view R (Ans D P) (self := DerivationKernel.over D _ hK P) g.node).val =
      g.node.view.forget := rfl
  rw [e2]
  split
  · next xs h => simp [h]
  · simp

/-- A table with a race has a goal that has one. -/
def RaceAll (st : StateOf R Rel (Ans D P)) : Prop :=
  ∀ (j : Nat) (t : Table R Rel (Ans D P)), st.tables[j]? = some t → t.race.isSome = true →
    hasRace t.goal = true

/-- What a run keeps: the invariant of the goals, the base, the meaning of
every cursor, a strategy for every way to answer a goal, and that only a
goal with a race has a table with one. -/
structure Good (st : StateOf R Rel (Ans D P)) : Prop where
  inv : Inv st
  base : Base st
  prog : ProgAll st
  full : FullAll st
  race : RaceAll st

omit [DecidableEq R] in
theorem getElem?_modify_cases (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) {j : Nat} {t' : Table R Rel (Ans D P)}
    (h : (st.modify i f).tables[j]? = some t') :
    (j ≠ i ∧ st.tables[j]? = some t') ∨ (j = i ∧ ∃ t, st.tables[i]? = some t ∧ t' = f t) := by
  unfold StateOf.modify at h
  simp only [List.getElem?_modify] at h
  split at h
  · next e =>
    subst e
    cases ht : st.tables[i]? with
    | none => rw [ht] at h; cases h
    | some t => rw [ht] at h; cases h; exact .inr ⟨rfl, t, rfl, rfl⟩
  · next e => exact .inl ⟨fun e' => e e'.symm, by rwa [id_map'] at h⟩

omit [DecidableEq R] in
theorem stable_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hf : ∀ t, st.tables[i]? = some t → (f t).goal = t.goal ∧ (f t).born = t.born ∧
      (f t).answers = t.answers ∧ (t.done = true → (f t).done = true)) :
    Stable st (st.modify i f) := by
  intro k t hk
  unfold StateOf.modify
  simp only [List.getElem?_modify, hk]
  by_cases e : i = k
  · subst e
    obtain ⟨h1, h2, h3, h4⟩ := hf t hk
    exact ⟨f t, by simp, h1, h2, by rw [h3], fun hd => ⟨h4 hd, h3⟩⟩
  · exact ⟨t, by simp [e], rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩⟩

theorem ProgAll.modify {st : StateOf R Rel (Ans D P)} (hA : ProgAll st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hgoal : ∀ t, (f t).goal = t.goal)
    (hS : Stable st (st.modify i f))
    (hg : ∀ t, st.tables[i]? = some t → ∀ gs, (f t).groups = some gs → ∀ gr ∈ gs,
      ∀ s ∈ gr.strats, Prog st i t.goal s) : ProgAll (st.modify i f) := by
  intro j t' h gs hgs gr hgr s hs
  rcases getElem?_modify_cases st i f h with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
  · exact (hA j t' h gs hgs gr hgr s hs).mono hS
  · rw [hgoal]
    exact (hg t ht gs hgs gr hgr s hs).mono hS

/-- The work of the strategies of an open table leaves every cursor its
meaning. -/
theorem ProgAll.frame {st st' : StateOf R Rel (Ans D P)} (hA : ProgAll st) {j : Nat}
    (h : Frame j st st') (ho : Open st j) : ProgAll st' := by
  intro k t' hk gs hgs gr hgr s hs
  cases hst : st.tables[k]? with
  | none => rw [(h.2.2 k t' hk hst).1] at hgs; cases hgs
  | some t =>
    obtain ⟨t'', h'', e1, -, -, -, e5, -⟩ := h.2.1 k t hst
    rw [hk] at h''
    cases h''
    rw [e1]
    rw [e5] at hgs
    exact (hA k t hst gs hgs gr hgr s hs).mono (h.stable ho)

theorem FullAll.modify {st : StateOf R Rel (Ans D P)} (hA : FullAll st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hgoal : ∀ t, (f t).goal = t.goal)
    (hS : Stable st (st.modify i f))
    (hg : ∀ t, st.tables[i]? = some t → ∀ gs, (f t).groups = some gs → Full st t.goal gs) :
    FullAll (st.modify i f) := by
  intro j t' h gs hgs
  rcases getElem?_modify_cases st i f h with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
  · exact (hA j t' h gs hgs).mono hS
  · rw [hgoal]
    exact (hg t ht gs hgs).mono hS

/-- The work of the strategies of an open table leaves every table its
strategies. -/
theorem FullAll.frame {st st' : StateOf R Rel (Ans D P)} (hA : FullAll st) {j : Nat}
    (h : Frame j st st') (ho : Open st j) : FullAll st' := by
  intro k t' hk gs hgs
  cases hst : st.tables[k]? with
  | none => rw [(h.2.2 k t' hk hst).1] at hgs; cases hgs
  | some t =>
    obtain ⟨t'', h'', e1, -, -, -, e5, -⟩ := h.2.1 k t hst
    rw [hk] at h''
    cases h''
    rw [e1]
    rw [e5] at hgs
    exact (hA k t hst gs hgs).mono (h.stable ho)

/-- Only a check can be dead, and one that is can never show its goal
empty. -/
theorem dead_gone {st : StateOf R Rel (Ans D P)} {i : Nat} {g : GoalOf R Rel}
    {s : Strat Rel (Ans D P)} (hp : Prog st i g s) (hd : s.dead st = true) :
    ∃ l side o c, s = .check l side o c ∧ CheckGone st g l side o := by
  cases s with
  | check l side o c => exact ⟨l, side, o, c, rfl, prog_dead_gone hp hd⟩
  | _ => simp [Strat.dead] at hd

theorem prog_of_groupsAt {st : StateOf R Rel (Ans D P)} (hA : ProgAll st) {i k j : Nat}
    {g : GoalOf R Rel} {s : Strat Rel (Ans D P)} (hg : goalAt st i = some g)
    (h : ((groupsAt st i)[k]?).bind (·.strats[j]?) = some s) : Prog st i g s := by
  unfold goalAt at hg
  unfold groupsAt at h
  cases ht : st.tables[i]? with
  | none => rw [ht] at h; simp at h
  | some t =>
    rw [ht] at h hg
    cases hg
    simp only at h
    cases hgs : t.groups with
    | none => rw [hgs] at h; simp at h
    | some gs =>
      rw [hgs] at h
      simp only [Option.getD_some] at h
      cases hgr : gs[k]? with
      | none => rw [hgr] at h; simp at h
      | some gr =>
        rw [hgr] at h
        exact hA i t ht gs hgs gr (List.mem_of_getElem? hgr) s (List.mem_of_getElem? h)

omit [DecidableEq R] in
theorem RaceAll.of_tables {st st' : StateOf R Rel (Ans D P)} (hA : RaceAll st)
    (h : ∀ (j : Nat) (t' : Table R Rel (Ans D P)), st'.tables[j]? = some t' →
      t'.race.isSome = true → hasRace t'.goal = true ∨
        ∃ t, st.tables[j]? = some t ∧ t.goal = t'.goal ∧ t.race.isSome = true) :
    RaceAll st' := by
  intro j t' ht' hr
  rcases h j t' ht' hr with e | ⟨t, ht, eg, er⟩
  · exact e
  · rw [← eg]
    exact hA j t ht er

omit [DecidableEq R] in
/-- Changing one table keeps that only a goal with a race has a table with
one, if the goal of the table stays and it gains a race only if its goal
has one. -/
theorem RaceAll.modify {st : StateOf R Rel (Ans D P)} (hA : RaceAll st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hg : ∀ t, (f t).goal = t.goal)
    (hr : ∀ t, st.tables[i]? = some t → (f t).race.isSome = true →
      t.race.isSome = true ∨ hasRace t.goal = true) : RaceAll (st.modify i f) :=
  hA.of_tables fun j t' ht' hs => by
    rcases getElem?_modify_cases st i f ht' with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
    · exact .inr ⟨t', h, rfl, hs⟩
    · rcases hr t ht hs with e | e
      · exact .inr ⟨t, ht, (hg t).symm, e⟩
      · exact .inl (by rw [hg]; exact e)

/-- The work of a strategy gives no table a race. -/
theorem RaceAll.inner {st st' : StateOf R Rel (Ans D P)} {j : Nat} (hA : RaceAll st)
    (h : Inner K hK j st st') : RaceAll st' := by
  induction h with
  | refl st => exact hA
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hA)
  | @same st st' e _ _ _ =>
    refine hA.of_tables fun k t' ht' hs => .inr ?_
    have hf : st.frames[k]? = st'.frames[k]? := by rw [e]
    simp only [StateOf.frames, List.getElem?_map, ht', Option.map_some] at hf
    cases ht : st.tables[k]? with
    | none => rw [ht] at hf; cases hf
    | some t =>
      rw [ht] at hf
      simp only [Option.map_some, Option.some.injEq, Table.frame, Prod.mk.injEq] at hf
      exact ⟨t, rfl, hf.1, by rw [hf.2.2.2.2.2.2.2.1]; exact hs⟩
  | @opened st st' g self e _ _ _ =>
    refine hA.of_tables fun k t' ht' hs => .inr ?_
    have hf : st'.frames[k]? =
        (st.frames ++ [(g, self, [], false, st.round, 0, none, none, 0, 0)])[k]? := by rw [e]
    have hl : st.frames.length = st.tables.length := by simp [StateOf.frames]
    by_cases hlt : k < st.tables.length
    · rw [List.getElem?_append_left (by omega)] at hf
      simp only [StateOf.frames, List.getElem?_map, ht', Option.map_some,
        List.getElem?_eq_getElem hlt, Option.some.injEq, Table.frame, Prod.mk.injEq] at hf
      exact ⟨st.tables[k], List.getElem?_eq_getElem hlt, hf.1.symm,
        by rw [← hf.2.2.2.2.2.2.2.1]; exact hs⟩
    · rw [List.getElem?_append_right (by omega)] at hf
      cases hk : k - st.frames.length with
      | zero =>
        rw [hk] at hf
        simp only [StateOf.frames, List.getElem?_map, ht', Option.map_some,
          List.getElem?_cons_zero, Option.some.injEq, Table.frame, Prod.mk.injEq] at hf
        rw [hf.2.2.2.2.2.2.2.1] at hs
        cases hs
      | succ n =>
        rw [hk] at hf
        simp [StateOf.frames, ht'] at hf
  | add st a =>
    rw [addAnswer_val]
    split
    · exact hA
    · split
      · split
        · exact hA.modify j _ (fun _ => rfl) fun _ _ h => .inl h
        · exact RaceAll.modify (RaceAll.modify hA j (app [a]) (fun _ => rfl) fun _ _ h => .inl h)
            j (app [(Ans.swapA D P a).val]) (fun _ => rfl) fun _ _ h => .inl h
      · exact hA.modify j _ (fun _ => rfl) fun _ _ h => .inl h

/-- Changing one table keeps what a run keeps, if its goal, its mark, its
answers, its strategies and its race stay, and it stays complete if it
was. -/
theorem Good.modify {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hcore : ∀ t, (f t).core = t.core)
    (hgr : ∀ t, (f t).groups = t.groups) (hb : ∀ t, (f t).born = t.born)
    (hd : ∀ t, t.done = true → (f t).done = true)
    (hr : ∀ t, (f t).race = t.race) : Good (st.modify i f) := by
  have e : ∀ t, (f t).goal = t.goal ∧ (f t).self = t.self ∧ (f t).answers = t.answers :=
    fun t => by
      have := hcore t
      simp only [Table.core, Prod.mk.injEq] at this
      exact this
  refine ⟨hG.inv.modify_same i f hcore hgr, hG.base.same (sameG_modify st i f fun t => (e t).1),
    hG.prog.modify i f (fun t => (e t).1)
      (stable_modify st i f fun t _ => ⟨(e t).1, hb t, (e t).2.2, hd t⟩) fun t ht gs hgs => ?_,
    hG.full.modify i f (fun t => (e t).1)
      (stable_modify st i f fun t _ => ⟨(e t).1, hb t, (e t).2.2, hd t⟩) fun t ht gs hgs => ?_,
    hG.race.modify i f (fun t => (e t).1) fun t _ h => .inl (by rw [← hr]; exact h)⟩
  · rw [hgr] at hgs
    exact hG.prog i t ht gs hgs
  · rw [hgr] at hgs
    exact hG.full i t ht gs hgs

/-- Removing groups of one table whose strategies are all dead keeps what a
run keeps. -/
theorem Good.dropGroups {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat)
    (p : Group Rel (Ans D P) → Bool)
    (hp : ∀ gr, p gr = false → ∀ s ∈ gr.strats, s.dead st = true) :
    Good (st.modify i fun t => { t with groups := t.groups.map fun gs => gs.filter p }) := by
  refine ⟨hG.inv.dropGroups i p, hG.base.same (sameG_modify st i _ fun _ => rfl),
    hG.prog.modify i _ (fun _ => rfl)
      (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
      fun t ht gs hgs gr hgr s hs => ?_,
    hG.full.modify i _ (fun _ => rfl)
      (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
      fun t ht gs hgs => ?_,
    hG.race.modify i _ (fun _ => rfl) fun _ _ h => .inl h⟩
  · cases hg : t.groups with
    | none => rw [hg] at hgs; cases hgs
    | some gs' =>
      rw [hg] at hgs
      cases hgs
      exact hG.prog i t ht gs' hg gr (List.mem_of_mem_filter hgr) s hs
  · cases hg : t.groups with
    | none => rw [hg] at hgs; cases hgs
    | some gs' =>
      rw [hg] at hgs
      cases hgs
      refine (hG.full i t ht gs' hg).keep (Stable.refl st) fun gr hgr => ?_
      cases hpg : p gr with
      | true => exact .inl ⟨gr, List.mem_filter.2 ⟨hgr, hpg⟩, rfl⟩
      | false => exact .inr fun s hs => dead_gone (hG.prog i t ht gs' hg gr hgr s hs) (hp gr hpg s hs)

/-- Changing a group of a table keeps what a run keeps, if each strategy of
the group stays or fits with cursors that mean what they should. -/
theorem Good.setGroup {st : StateOf R Rel (Ans D P)} (hG : Good st) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P))
    (hf : ∀ g gr, goalAt st i = some g → ∀ s ∈ (f gr).strats,
      s ∈ gr.strats ∨ (StratOk st g s ∧ Prog st i g s))
    (hk : ∀ gr, (groupsAt st i)[k]? = some gr → (f gr).kinds = gr.kinds) :
    Good (setGroup st i k f) := by
  refine ⟨inv_setGroup hG.inv i k f fun g gr hg h s hs => (hf g gr hg s hs).elim (h s) (·.1),
    hG.base.same (sameG_modify st i _ fun _ => rfl),
    hG.prog.modify i _ (fun _ => rfl)
      (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
      fun t ht gs hgs gr hgr s hs => ?_,
    hG.full.modify i _ (fun _ => rfl)
      (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
      fun t ht gs hgs => ?_,
    hG.race.modify i _ (fun _ => rfl) fun _ _ h => .inl h⟩
  · have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
    simp only at hgs
    cases hgs' : t.groups with
    | none => rw [hgs'] at hgs; cases hgs
    | some gs' =>
      rw [hgs'] at hgs
      cases hgs
      rcases mem_modify hgr with hgr | ⟨gr', hgr', rfl⟩
      · exact hG.prog i t ht gs' hgs' gr hgr s hs
      · rcases hf t.goal gr' hg s hs with h | h
        · exact hG.prog i t ht gs' hgs' gr' hgr' s h
        · exact h.2
  · simp only at hgs
    cases hgs' : t.groups with
    | none => rw [hgs'] at hgs; cases hgs
    | some gs' =>
      rw [hgs'] at hgs
      cases hgs
      have hga : groupsAt st i = gs' := by simp only [groupsAt, ht, hgs', Option.getD_some]
      refine (hG.full i t ht gs' hgs').keep (Stable.refl st) fun gr hgr => .inl ?_
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hgr
      by_cases e : k = n
      · subst e
        exact ⟨f gr, List.mem_of_getElem? (i := k) (by rw [List.getElem?_modify, hn]; simp),
          hk gr (by rw [hga]; exact hn)⟩
      · exact ⟨gr, List.mem_of_getElem? (i := n) (by rw [List.getElem?_modify, hn]; simp [e]),
          rfl⟩

/-- A change of the tables that keeps of each its goal, its mark, its
answers and its strategies, and leaves a complete table complete, keeps what
a run keeps. -/
theorem Good.of_map {st st' : StateOf R Rel (Ans D P)} (hG : Good st)
    (F : Nat → Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hget : ∀ j, st'.tables[j]? = (st.tables[j]?).map (F j))
    (hcore : ∀ j t, (F j t).core = t.core) (hgr : ∀ j t, (F j t).groups = t.groups)
    (hb : ∀ j t, (F j t).born = t.born) (hd : ∀ j t, t.done = true → (F j t).done = true)
    (hr : ∀ j t, (F j t).race = t.race) (he : st'.edges = st.edges) : Good st' := by
  have e : ∀ j t, (F j t).goal = t.goal ∧ (F j t).self = t.self ∧ (F j t).answers = t.answers :=
    fun j t => by
      have := hcore j t
      simp only [Table.core, Prod.mk.injEq] at this
      exact this
  have hS : Stable st st' := fun k t hk =>
    ⟨F k t, by rw [hget, hk]; rfl, (e k t).1, hb k t, by rw [(e k t).2.2],
      fun h => ⟨hd k t h, (e k t).2.2⟩⟩
  refine ⟨hG.inv.of_map F hget hcore hgr, hG.base.same ⟨fun j => ?_, he⟩,
    fun j t' h gs hgs gr hgr' s hs => ?_, fun j t' h gs hgs => ?_,
    hG.race.of_tables fun j t' h hs => .inr ?_⟩
  · unfold goalAt
    rw [hget]
    cases st.tables[j]? with
    | none => rfl
    | some t => exact congrArg some (e j t).1
  · rw [hget] at h
    cases ht : st.tables[j]? with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      cases h
      rw [(e j t).1]
      rw [hgr] at hgs
      exact (hG.prog j t ht gs hgs gr hgr' s hs).mono hS
  · rw [hget] at h
    cases ht : st.tables[j]? with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      cases h
      rw [(e j t).1]
      rw [hgr] at hgs
      exact (hG.full j t ht gs hgs).mono hS
  · rw [hget] at h
    cases ht : st.tables[j]? with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      cases h
      exact ⟨t, rfl, (e j t).1.symm, by rw [← hr]; exact hs⟩

/-- The work of a strategy moves its cursors and nothing else. -/
theorem work_kind (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) :
    (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1.kind = s.kind := by
  at_cost K hK
  cases s with
  | span ran => cases ran <;> rfl
  | copy c subs =>
    simp only [work]
    split <;> rfl
  | join k a b c =>
    simp only [work]
    split <;> rfl
  | push k l side o todo subs =>
    simp only [work]
    split
    · rfl
    · split
      · rfl
      · rfl
      · split <;> rfl
  | check l side o c =>
    cases c with
    | reading =>
      simp only [work, Cost.bind_val]
      split <;> rfl
    | off => rfl
    | opened subs => rfl

/-- What a unit of the work of the strategy `s0` of the open table at `i`
keeps, from the state `st0`. -/
structure UnitOk (K : Kernel R Cost) (hK : K.Refines D) (i : Nat) (g : GoalOf R Rel)
    (st0 : StateOf R Rel (Ans D P)) (s0 : Strat Rel (Ans D P)) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) : Prop where
  inv : Inv st
  base : Base st
  goal : goalAt st i = some g
  isOpen : Open st i
  ok : StratOk st g s
  prog : Prog st i g s
  kind : s.kind = s0.kind
  inner : Inner K hK i st0 st

theorem UnitOk.work (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) {i : Nat}
    {g : GoalOf R Rel} {st0 st : StateOf R Rel (Ans D P)} {s0 s : Strat Rel (Ans D P)}
    (hg : GoodG D g) (h : UnitOk K hK i g st0 s0 st s) :
    UnitOk K hK i g st0 s0 (work (K := DerivationKernel.over D K hK P) i g st s).val.1
      (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1 where
  inv := (inv_work h.inv i g s h.goal h.ok).1
  base := base_work hL hR h.base i g s hg h.prog
  goal := (reach_work (K := K) (hK := hK) i g st s).ext _ _ h.goal
  isOpen := (inner_work (K := K) (hK := hK) i g st s).frame.isOpen h.isOpen
  ok := (inv_work h.inv i g s h.goal h.ok).2
  prog := prog_work hL hR h.inv h.base.edges i g s h.isOpen ⟨hg.1, hg.2.1⟩ h.ok h.prog
  kind := (work_kind (K := K) (hK := hK) (P := P) i g st s).trans h.kind
  inner := h.inner.trans (inner_work (K := K) (hK := hK) i g st s)

/-- One strategy has its turn and is put back. -/
theorem good_workStep (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat) (g : GoalOf R Rel)
    (k j : Nat) (s : Strat Rel (Ans D P)) (f left c : Nat) (ow : List Nat → List Nat)
    (hg : goalAt st i = some g) (hb : Busy st i)
    (hs : ((groupsAt st i)[k]?).bind (·.strats[j]?) = some s) :
    Good (setGroup (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.1 i k
      fun gr => { gr with
        strats := gr.strats.set j
          (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.2.1,
        owed := ow gr.owed }) := by
  have hok := strat_of_groupsAt hG.inv hg hs
  have hp := prog_of_groupsAt hG.prog hg hs
  have hgood := hG.base.good i g hg
  have hU := turn_ind (K := K) (hK := hK) (P := P) i g (UnitOk K hK i g st s)
    (fun _ _ h => h.work hL hR hgood) f left st s c
    ⟨hG.inv, hG.base, hg, hb.isOpen, hok, hp, rfl, Inner.refl st⟩
  have hfr := hU.inner.frame
  have hA1 := hG.prog.frame hfr hb.isOpen
  have hF1 := hG.full.frame hfr hb.isOpen
  refine Good.setGroup ⟨hU.inv, hU.base, hA1, hF1, hG.race.inner hU.inner⟩ i k _
    (fun g' gr hg'' s' hs' => ?_) fun gr hgk => ?_
  · obtain rfl : g' = g := Option.some.inj (hg''.symm.trans hU.goal)
    rcases List.mem_or_eq_of_mem_set hs' with h' | rfl
    · exact .inl h'
    · exact .inr ⟨hU.ok, hU.prog⟩
  · have hga : groupsAt (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.1 i =
        groupsAt st i := by
      obtain ⟨t, ht, -⟩ := hb
      obtain ⟨t', ht', -, -, -, -, e5, -⟩ := hfr.2.1 i t ht
      simp only [groupsAt, ht, ht', e5]
    rw [hga] at hgk
    rw [hgk] at hs
    exact map_set_same Strat.kind hs hU.kind

theorem good_workGroup (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Good st → Good (adv h st).val.1)
    (hadvK : ∀ h st, Keep st (adv h st).val.1) {st : StateOf R Rel (Ans D P)}
    (hG : Good st) (i : Nat) (g : GoalOf R Rel) (k : Nat)
    (hg : goalAt st i = some g) (hb : Busy st i) :
    Good (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1 := by
  have hstep := fun (st : StateOf R Rel (Ans D P)) hG j s f left c ow hg hb hs =>
    good_workStep (K := K) (hK := hK) hL hR (st := st) hG i g k j s f left c ow hg hb hs
  have hkw := fun (st : StateOf R Rel (Ans D P)) s f left c hb =>
    keep_turn (K := K) (hK := hK) (P := P) i g f left st s c hb
  have hf := fun X d hX => feedGroup_keeps (K := K) (hK := hK) (P := P) adv
    (fun X => Good X ∧ goalAt X i = some g ∧ Busy X i)
    (fun h X hX => ⟨hadv h X hX.1, (hadvK h X).stable.ext _ _ hX.2.1, (hadvK h X).busy hX.2.2⟩)
    (fun h c X hX => ⟨Good.modify hX.1 h (fun t => { t with fed := t.fed + c }) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ h => h) (fun _ => rfl),
      (goalAt_modify X h i (fun t => { t with fed := t.fed + c }) fun _ => rfl).trans hX.2.1,
      (keep_modify X h (fun t => { t with fed := t.fed + c }) fun _ _ =>
        ⟨rfl, rfl, rfl, fun h => h, fun h => ⟨h, fun h => h⟩⟩).busy hX.2.2⟩) i k X d hX
  clear hR
  at_cost K hK
  simp only [workGroup, workStrats, Cost.bind_val, Cost.pure_val]
  refine Good.modify ?_ i _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ h => h)
    (fun _ => rfl)
  refine Good.setGroup ?_ _ _ _ (fun g' gr _ s hs => .inl hs) (fun _ _ => rfl)
  refine (hf _ _ ?_).1
  · refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × Nat × Bool =>
      Good acc.1 ∧ goalAt acc.1 i = some g ∧ Busy acc.1 i) _ _ (fun b j _ hb => ?_)
      (st, 0, false) ⟨hG, hg, hb⟩
    split
    · exact hb
    · next s o hs =>
      simp only [Cost.bind_val, Cost.pure_val]
      refine ⟨hstep b.1 hb.1 j s _ _ 0
        (fun l => setOwed l j (o + (turn (K := DerivationKernel.over D _ hK P) i g
          (turnTicks * weight b.1 s - o) (turnTicks * weight b.1 s - o) b.1 s 0).val.2.2 -
            turnTicks * weight b.1 s)) hb.2.1 hb.2.2 (pick_strat hs).1, ?_, ?_⟩
      · exact ((hkw b.1 s _ _ 0 hb.2.2).trans (keep_setGroup _ i k _)).stable.ext _ _ hb.2.1
      · exact ((hkw b.1 s _ _ 0 hb.2.2).trans (keep_setGroup _ i k _)).busy hb.2.2

theorem good_workLevel (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Good st → Good (adv h st).val.1)
    (hadvK : ∀ h st, Keep st (adv h st).val.1) {st : StateOf R Rel (Ans D P)}
    (hG : Good st) (i : Nat) (g : GoalOf R Rel) (lv : Nat)
    (hg : goalAt st i = some g) (hb : Busy st i) :
    Good (workLevel (K := DerivationKernel.over D K hK P) adv i g lv st).val.1 := by
  have hwg := fun (st : StateOf R Rel (Ans D P)) hG k hg hb =>
    good_workGroup (K := K) (hK := hK) hL hR adv hadv hadvK (st := st) hG i g k hg hb
  have hkg := fun k (st : StateOf R Rel (Ans D P)) hb =>
    keep_workGroup (K := K) (hK := hK) (P := P) adv hadvK i g k st hb
  clear hR
  at_cost K hK
  refine (foldL_inv (fun acc : StateOf R Rel (Ans D P) × Bool =>
    Good acc.1 ∧ goalAt acc.1 i = some g ∧ Busy acc.1 i) _ _ (fun b p _ hb => ?_) (st, false)
    ⟨hG, hg, hb⟩).1
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    have hk := hkg p.2 b.1 hb.2.2
    exact ⟨hwg b.1 hb.1 p.2 hb.2.1 hb.2.2, hk.stable.ext _ _ hb.2.1, hk.busy hb.2.2⟩
  · exact hb

theorem good_prepare (hR : ReadOk D P K hK) (hP : ProgFO P) {st : StateOf R Rel (Ans D P)}
    (hG : Good st) (i : Nat) (t : Table R Rel (Ans D P)) (ht : st.tables[i]? = some t)
    (hd : t.done = false) :
    Good (prepare (K := DerivationKernel.over D K hK P) i t st).val := by
  have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
  have ho : Open st i := ⟨t, ht, hd⟩
  have hI := inv_prepare (K := K) (hK := hK) hG.inv i t ht
  obtain ⟨b1, p1, q1⟩ := prog_expand hR hP hG.base i ho t.goal (hG.base.good i _ hg)
    (hG.inv.core i t ht).1
  have hfr := (inner_expand (K := K) (hK := hK) (P := P) (w := i) t.goal st).frame
  have hA1 := hG.prog.frame hfr ho
  have hF1 := hG.full.frame hfr ho
  have hE := (hfr.stable ho).ext
  have hR1 := hG.race.inner (inner_expand (K := K) (hK := hK) (P := P) (w := i) t.goal st)
  have hrv := raceOf_val (K := K) (hK := hK) (P := P) t.goal
  suffices h : Base (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
      ProgAll (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
      FullAll (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
      RaceAll (prepare (K := DerivationKernel.over D K hK P) i t st).val from
    ⟨hI, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  clear hI hR
  at_cost K hK
  unfold prepare
  cases t.groups with
  | some _ =>
    simp only [Cost.bind_val, Cost.pure_val]
    exact ⟨hG.base.same (sameG_modify st i _ fun _ => rfl),
      hG.prog.modify i _ (fun _ => rfl)
        (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
        fun t' ht' gs hgs => hG.prog i t' ht' gs hgs,
      hG.full.modify i _ (fun _ => rfl)
        (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
        fun t' ht' gs hgs => hG.full i t' ht' gs hgs,
      hG.race.modify i _ (fun _ => rfl) fun _ _ h => .inl h⟩
  | none =>
    simp only [Cost.bind_val, Cost.pure_val]
    have hA2 : ProgAll ((expand (K := DerivationKernel.over D _ hK P) t.goal st).val.1.modify i
        fun t' => { t' with race := (raceOf (K := DerivationKernel.over D _ hK P) t.goal).val,
                            groups := some (expand (K := DerivationKernel.over D _ hK P) t.goal
          st).val.2 }) := by
      refine hA1.modify i _ (fun _ => rfl)
        (stable_modify _ i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
        fun t' ht' gs hgs gr hgr s hs => ?_
      cases hgs
      have : t'.goal = t.goal := by
        have := hE _ _ hg
        unfold goalAt at this
        rw [ht'] at this
        exact Option.some.inj this
      rw [this]
      exact p1 gr hgr s hs
    have hF2 : FullAll ((expand (K := DerivationKernel.over D _ hK P) t.goal st).val.1.modify i
        fun t' => { t' with race := (raceOf (K := DerivationKernel.over D _ hK P) t.goal).val,
                            groups := some (expand (K := DerivationKernel.over D _ hK P) t.goal
          st).val.2 }) := by
      refine hF1.modify i _ (fun _ => rfl)
        (stable_modify _ i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
        fun t' ht' gs hgs => ?_
      cases hgs
      have : t'.goal = t.goal := by
        have := hE _ _ hg
        unfold goalAt at this
        rw [ht'] at this
        exact Option.some.inj this
      rw [this]
      exact q1
    have hB2 : Base ((expand (K := DerivationKernel.over D _ hK P) t.goal st).val.1.modify i
        fun t' => { t' with race := (raceOf (K := DerivationKernel.over D _ hK P) t.goal).val,
                            groups := some (expand (K := DerivationKernel.over D _ hK P) t.goal
          st).val.2 }) := b1.same (sameG_modify _ i _ fun _ => rfl)
    refine ⟨hB2.same (sameG_modify _ i _ fun _ => rfl),
      hA2.modify i _ (fun _ => rfl)
        (stable_modify _ i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
        fun t' ht' gs hgs => hA2 i t' ht' gs hgs,
      hF2.modify i _ (fun _ => rfl)
        (stable_modify _ i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
        fun t' ht' gs hgs => hF2 i t' ht' gs hgs, ?_⟩
    have hR2 : RaceAll ((expand (K := DerivationKernel.over D _ hK P) t.goal st).val.1.modify i
        fun t' => { t' with race := (raceOf (K := DerivationKernel.over D _ hK P) t.goal).val,
                            groups := some (expand (K := DerivationKernel.over D _ hK P) t.goal
          st).val.2 }) := by
      refine RaceAll.modify hR1 i _ (fun _ => rfl) fun t' ht' h => .inr ?_
      have e : t'.goal = t.goal := by
        have := hE _ _ hg
        unfold goalAt at this
        rw [ht'] at this
        exact Option.some.inj this
      rw [e]
      rw [hrv] at h
      cases hh : hasRace t.goal with
      | true => rfl
      | false => rw [hh] at h; cases h
    exact RaceAll.modify hR2 i _ (fun _ => rfl) fun _ _ h => .inl h

theorem sameG_askRace (U : GOracle R Rel (Ans D P) Cost) (i : Nat) (g : GoalOf R Rel)
    (st : StateOf R Rel (Ans D P)) :
    SameG st (askRace (K := DerivationKernel.over D K hK P) U i g st).val.1 := by
  have hadd := fun (b : StateOf R Rel (Ans D P)) a =>
    sameG_addOption (K := K) (hK := hK) (P := P) b i (some a)
  have hall : ∀ xs : List (Ans D P),
      SameG st (foldL (addAnswer (K := DerivationKernel.over D K hK P) i) st xs).val := by
    intro xs
    at_cost K hK
    exact foldL_inv (fun b => SameG st b) _ _ (fun b x _ hb => hb.trans (hadd b x)) st
      (SameG.refl st)
  rw [askRace_val]
  split
  · exact SameG.refl st
  · split
    · exact SameG.refl st
    · split
      · exact SameG.refl st
      · split
        · split
          · exact (hall _).trans (sameG_modify _ i _ fun _ => rfl)
          · exact sameG_modify _ i _ fun _ => rfl
        · exact sameG_modify _ i _ fun _ => rfl

/-- **The race of an open table keeps** what a run keeps: its answers are
answers of the goal, by its specification on a goal a run may open. -/
theorem good_askRace (U : GOracle R Rel (Ans D P) Cost) (hU : UOk D P U)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat) (g : GoalOf R Rel)
    (hg : goalAt st i = some g) (ho : Open st i) :
    Good (askRace (K := DerivationKernel.over D K hK P) U i g st).val.1 := by
  have hfr := frame_askRace (K := K) (hK := hK) (P := P) U i g st
  have hgood := hG.base.good i g hg
  have hn : Normal g.node := by
    obtain ⟨t, ht, -⟩ := ho
    have e : t.goal = g := by
      unfold goalAt at hg
      rw [ht] at hg
      exact Option.some.inj hg
    rw [← e]
    exact (hG.inv.core i t ht).1
  have hok : GoalOk D g := ⟨hgood.1, hgood.2.1, hn, hgood.2.2⟩
  refine ⟨inv_askRace U hG.inv i g hg fun n a ha => hU.goal n g hok a ha,
    hG.base.same (sameG_askRace U i g st), hG.prog.frame hfr ho, hG.full.frame hfr ho, ?_⟩
  rw [askRace_val]
  cases ht : st.tables[i]? with
  | none => exact hG.race
  | some t =>
    dsimp only
    cases hr : t.race with
    | none => exact hG.race
    | some r =>
      have hrt : hasRace t.goal = true := hG.race i t ht (by rw [hr]; rfl)
      dsimp only
      split
      · exact hG.race
      · split
        · split
          · have hin := inner_addAll (K := K) (hK := hK) (P := P) i st (U r.depth g).val.2
            refine (hG.race.inner hin).modify i _ (fun _ => rfl) fun t' ht' _ => .inr ?_
            obtain ⟨u, hu, e1, -⟩ := hin.frame.2.1 i t ht
            rw [ht'] at hu
            cases hu
            rw [e1]
            exact hrt
          · exact hG.race.modify i _ (fun _ => rfl) fun t' ht' _ => .inr (by
              rw [ht] at ht'; cases ht'; exact hrt)
        · exact hG.race.modify i _ (fun _ => rfl) fun t' ht' _ => .inr (by
            rw [ht] at ht'; cases ht'; exact hrt)

/-- **A round keeps** the invariant of the goals, the base, and the meaning
of every cursor. -/
theorem good_advance (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) (hP : ProgFO P)
    (U : GOracle R Rel (Ans D P) Cost) (hU : UOk D P U) :
    ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)), Good st →
      Good (advance (K := DerivationKernel.over D K hK P) U fuel i st).val.1
  | 0, _, st, hG => by
    clear hR
    at_cost K hK
    exact hG
  | fuel + 1, i, st, hG => by
    have ih := fun h st => good_advance hL hR hP U hU fuel h st
    have ihK := fun h st => keep_advance (K := K) (hK := hK) (P := P) U fuel h st
    have hrace := fun g (st : StateOf R Rel (Ans D P)) hG hg ho =>
      good_askRace (K := K) (hK := hK) U hU (st := st) hG i g hg ho
    have hprep := fun t ht hd => good_prepare (K := K) (hK := hK) hR hP hG i t ht hd
    have hprepK := fun t ht hd => keep_prepare (K := K) (hK := hK) (P := P) i t st ht hd
    have hlev := fun g lv (st : StateOf R Rel (Ans D P)) hG hg hb =>
      good_workLevel (K := K) (hK := hK) hL hR _ ih ihK (st := st) hG i g lv hg hb
    have hlevK := fun g lv st hb =>
      keep_workLevel (K := K) (hK := hK) (P := P) _ ihK i g lv st hb
    clear hR
    at_cost K hK
    simp only [advance]
    split
    · exact hG
    · next t ht =>
      split
      · exact hG
      · next hd =>
        split
        · exact hG
        · split
          · exact hG
          · simp only [Cost.bind_val, Cost.pure_val]
            have hd' : t.done = false := by simpa using hd
            have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
            obtain ⟨hk, hb⟩ := hprepK t ht hd'
            refine Good.modify ?_ i _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
              (fun _ h => by simp [h]) (fun _ => rfl)
            have key : ∀ X : StateOf R Rel (Ans D P),
                Good X ∧ goalAt X i = some t.goal ∧ Busy X i →
                Good (askRace (K := DerivationKernel.over D _ hK P) U i t.goal
                  (X.modify i fun t =>
                    { t with
                      groups := t.groups.map fun gs =>
                        gs.filter fun gr => !gr.strats.all (Strat.dead X) })).val.1 := by
              rintro X ⟨hGX, hgX, hbX⟩
              refine hrace _ _ (Good.dropGroups hGX i _ (fun gr hp s hs =>
                List.all_eq_true.1 (by simpa using hp) s hs)) ?_ ?_
              · refine Eq.trans ?_ hgX
                exact goalAt_modify _ i i _ fun _ => rfl
              · refine Busy.isOpen (Keep.busy ?_ hbX)
                exact keep_modify _ i _ fun _ _ =>
                  ⟨rfl, rfl, rfl, fun h => h, fun h => ⟨h, fun h => h⟩⟩
            refine key _ (foldL_inv (fun acc : StateOf R Rel (Ans D P) × Bool =>
              Good acc.1 ∧ goalAt acc.1 i = some t.goal ∧ Busy acc.1 i) _ _
              (fun b lv _ hb => ?_) _ ⟨hprep t ht hd', hk.stable.ext _ _ hg, hb⟩)
            split
            · exact hb
            · exact ⟨hlev _ _ b.1 hb.1 hb.2.1 hb.2.2,
                (hlevK _ lv b.1 hb.2.2).stable.ext _ _ hb.2.1,
                (hlevK _ lv b.1 hb.2.2).busy hb.2.2⟩

/-- **A request keeps** the invariant of the goals, the base, and the
meaning of every cursor. -/
theorem good_request (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) (hP : ProgFO P)
    (U : GOracle R Rel (Ans D P) Cost) (hU : UOk D P U)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) :
    Good (request (K := DerivationKernel.over D K hK P) U st).val.1 := by
  have h := fun (st : StateOf R Rel (Ans D P)) hG =>
    good_advance (K := K) (hK := hK) hL hR hP U hU st.tables.length 0 st hG
  clear hR
  at_cost K hK
  simp only [request, Cost.bind_val, Cost.pure_val]
  have h0 : Good ({ st with round := st.round + 1 } : StateOf R Rel (Ans D P)) :=
    hG.of_map (fun _ t => t) (fun j => by simp) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ h => h) (fun _ _ => rfl) rfl
  refine (h _ h0).of_map _ (fun j => List.getElem?_mapIdx) (fun j t => ?_) (fun j t => ?_)
    (fun j t => ?_) (fun j t hd => ?_) (fun j t => ?_) rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split
    · rfl
    · exact hd
  · split <;> rfl

/-- The first state has what a run keeps. -/
theorem good_init {root : Rel} (hn : Normal root) (hfo : root.FO) :
    Good (init (K := DerivationKernel.over D K hK P) root).val := by
  have hI := (inv_init (K := K) (hK := hK) (P := P) hn).1
  suffices h : Base (init (K := DerivationKernel.over D K hK P) root).val ∧
      ProgAll (init (K := DerivationKernel.over D K hK P) root).val ∧
      FullAll (init (K := DerivationKernel.over D K hK P) root).val ∧
      RaceAll (init (K := DerivationKernel.over D K hK P) root).val from
    ⟨hI, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  clear hI
  at_cost K hK
  simp only [init, Cost.bind_val, Cost.pure_val]
  have key : ∀ (j : Nat) (g : GoalOf R Rel) (t : Table R Rel (Ans D P)),
      goalAt (⟨[t], 0, 0, [], 1⟩ : StateOf R Rel (Ans D P)) j = some g → j = 0 ∧ g = t.goal := by
    intro j g t h
    unfold goalAt at h
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at h
              exact ⟨rfl, h.symm⟩
    | succ j => simp at h
  refine ⟨⟨fun j g h => ?_, fun i j g hi hj => ?_, fun e he => by cases he⟩,
    fun j t h gs hgs => ?_, fun j t h gs hgs => ?_, fun j t h hs => ?_⟩
  · obtain ⟨-, rfl⟩ := key j g _ h
    exact ⟨isBound_none D, isBound_none D, hfo⟩
  · rw [(key i g _ hi).1, (key j g _ hj).1]
  · obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? h)
    cases hgs
  · obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? h)
    cases hgs
  · obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? h)
    cases hs

end kernel

end Symmetric

end RwLog
