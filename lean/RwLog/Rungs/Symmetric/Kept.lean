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

/-! ## The strategies of a goal start right -/

theorem prog_splitGroup {st : StateOf R Rel (Ans D P)} (hB : Base st) (w : Nat) (k : Kind)
    (L Rg g : GoalOf R Rel) (hL' : GoodG D L) (hR' : GoodG D Rg) (hs : SplitAt g k L Rg) :
    Frame w st (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 ∧
      Base (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 ∧
      ∀ s ∈ (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.2.strats,
        Prog (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 w g s := by
  have hF := (inner_splitGroup (K := K) (hK := hK) (P := P) (w := w) k L Rg st).frame
  have hB1 := base_openGoal (K := K) (hK := hK) hB L hL'
  have hB2 := base_openGoal (K := K) (hK := hK) hB1 Rg hR'
  have hg1 := openGoal_goalAt (K := K) (hK := hK) (P := P) st L
  have hg2 := openGoal_goalAt (K := K) (hK := hK) (P := P)
    (openGoal (K := DerivationKernel.over D K hK P) st L).val.1 Rg
  have hg1' := (reach_openGoal (K := K) (hK := hK) _ Rg).ext _ _ hg1
  at_cost K hK
  simp only [splitGroup, Cost.bind_val, Cost.pure_val] at hF ⊢
  refine ⟨hF, hB2, fun s hs' => ?_⟩
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
      ∀ s ∈ (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.2,
        s = .check left side other .reading := by
  have hF := (inner_checkOf (K := K) (hK := hK) (P := P) (w := w) st left side other).frame
  have h := base_edgeOf hR hB left side
  clear hR
  at_cost K hK
  simp only [checkOf, Cost.bind_val, Cost.pure_val] at hF ⊢
  refine ⟨hF, h, fun s hs => ?_⟩
  split at hs
  · cases hs
  · exact List.mem_singleton.1 hs

theorem prog_chainGroups (hR : ReadOk D P K hK) {st : StateOf R Rel (Ans D P)} (hB : Base st)
    (w : Nat) (ho : Open st w) (g : GoalOf R Rel) (hg : GoodG D g) {xs : List Rel}
    (hv : g.node.view = .chain xs) :
    Base (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.1 ∧
      (∀ gr ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1,
        ∀ s ∈ gr.strats,
          Prog (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.1 w g s) ∧
      ∀ s ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.2,
        Prog (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.1 w g s := by
  have hsg := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') l r hl hr hs =>
    prog_splitGroup (K := K) (hK := hK) hB' w .seq ⟨g.lb, l, none⟩ ⟨none, r, g.rb⟩ g hl hr hs
  have hco := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') left side other =>
    prog_checkOf hR hB' w left side other
  clear hR
  at_cost K hK
  refine (foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) ×
      List (Strat Rel (Ans D P)) =>
    Frame w st acc.1 ∧ Base acc.1 ∧ (∀ gr ∈ acc.2.1, ∀ s ∈ gr.strats, Prog acc.1 w g s) ∧
      ∀ s ∈ acc.2.2, Prog acc.1 w g s) _ _ (fun b i _ hb => ?_)
    (st, [], []) ⟨Frame.refl w st, hB, (fun gr hgr => by cases hgr), fun s hs => by cases hs⟩).2
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
    have ho1 := hb.1.isOpen ho
    obtain ⟨f1, b1, p1⟩ := hsg b.1 hb.2.1 l r ⟨hg.1, isBound_none D, hfo.1⟩
      ⟨isBound_none D, hg.2.1, hfo.2⟩ hsplit
    obtain ⟨f2, b2, c2⟩ := hco _ b1 true l r
    obtain ⟨f3, b3, c3⟩ := hco _ b2 false r l
    have S1 := f1.stable ho1
    have ho2 := f1.isOpen ho1
    have S2 := f2.stable ho2
    have S3 := f3.stable (f2.isOpen ho2)
    refine ⟨hb.1.trans (f1.trans (f2.trans f3)), b3, fun gr hgr s hs => ?_, fun s hs => ?_⟩
    · rcases List.mem_append.1 hgr with hgr | hgr
      · exact (hb.2.2.1 gr hgr s hs).mono (S1.trans (S2.trans S3))
      · obtain rfl := List.mem_singleton.1 hgr
        exact (p1 s hs).mono (S2.trans S3)
    · rcases List.mem_append.1 hs with hs | hs
      · rcases List.mem_append.1 hs with hs | hs
        · exact (hb.2.2.2 s hs).mono (S1.trans (S2.trans S3))
        · rw [c2 s hs]
          dsimp only [Prog]
          exact ⟨_, _, hsplit, rfl, rfl, trivial⟩
      · rw [c3 s hs]
        dsimp only [Prog]
        exact ⟨_, _, hsplit, rfl, rfl, trivial⟩
  · exact hb

/-- **The strategies made for a goal start right**, and making them keeps
the base. -/
theorem prog_expand (hR : ReadOk D P K hK) (hP : ProgFO P) {st : StateOf R Rel (Ans D P)}
    (hB : Base st) (w : Nat) (ho : Open st w) (g : GoalOf R Rel) (hg : GoodG D g)
    (hn : Normal g.node) :
    Base (expand (K := DerivationKernel.over D K hK P) g st).val.1 ∧
      ∀ gr ∈ (expand (K := DerivationKernel.over D K hK P) g st).val.2, ∀ s ∈ gr.strats,
        Prog (expand (K := DerivationKernel.over D K hK P) g st).val.1 w g s := by
  have hop := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') h hg' =>
    base_openGoal (K := K) (hK := hK) hB' h hg'
  have hog := fun st' h => openGoal_goalAt (K := K) (hK := hK) (P := P) st' h
  have hin := fun st' h =>
    (inner_openGoal (K := K) (hK := hK) (P := P) (w := 0) st' h).reach.ext
  have hcg := fun xs (hv : g.node.view = .chain xs) =>
    prog_chainGroups hR hB w ho g hg hv
  have hsg := fun (st' : StateOf R Rel (Ans D P)) (hB' : Base st') l r hl hr hs =>
    prog_splitGroup (K := K) (hK := hK) hB' w .and ⟨g.lb, l, g.rb⟩ ⟨g.lb, r, g.rb⟩ g hl hr hs
  clear hR
  at_cost K hK
  simp only [expand, Cost.bind_val]
  split
  · next hv =>
    have hspan : ∃ s, g.node = .span s := forget_span hv
    refine ⟨hB, fun gr hgr s hs => ?_⟩
    obtain rfl := List.mem_singleton.1 hgr
    obtain rfl := List.mem_singleton.1 hs
    dsimp only [Prog]
    exact ⟨hspan, fun h => by cases h⟩
  · next f fl hv =>
    simp only [Cost.bind_val]
    split
    · next hb =>
      have hb' : Charged.bodyOf P g.node = none := hb
      refine ⟨hB, fun gr hgr s hs => ?_⟩
      obtain rfl := List.mem_singleton.1 hgr
      obtain rfl := List.mem_singleton.1 hs
      dsimp only [Prog]
      obtain ⟨b, hb''⟩ := forget_call (P := P) hv
      rw [hb'] at hb''
      cases hb''
    · next b hb =>
      have hb' : Charged.bodyOf P g.node = some b := hb
      simp only [Cost.bind_val, Cost.pure_val]
      refine ⟨hop _ hB _ ⟨hg.1, hg.2.1, bodyOf_fo hP hb'⟩, fun gr hgr s hs => ?_⟩
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
    refine ⟨keyB, fun gr hgr s hs => ?_⟩
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
    obtain ⟨h1, h2, h3⟩ := hcg xs (forget_chain hv)
    refine ⟨h1, fun gr hgr s hs => ?_⟩
    split at hgr
    · exact h2 gr hgr s hs
    · rcases List.mem_append.1 hgr with hgr | hgr
      · exact h2 gr hgr s hs
      · obtain rfl := List.mem_singleton.1 hgr
        exact h3 s hs
  · next xs hv =>
    have hvm := forget_meet hv
    refine (foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) =>
      Frame w st acc.1 ∧ Base acc.1 ∧ ∀ gr ∈ acc.2, ∀ s ∈ gr.strats, Prog acc.1 w g s) _ _
      (fun b i _ hb => ?_) (st, []) ⟨Frame.refl w st, hB, fun gr hgr => by cases hgr⟩).2
    simp only [Cost.bind_val]
    split
    · next l r hl hr =>
      simp only [Cost.bind_val, Cost.pure_val]
      have hr' : g.node.without i = some r := hr
      have hsplit : SplitAt g .and ⟨g.lb, l, g.rb⟩ ⟨g.lb, r, g.rb⟩ :=
        ⟨xs, i, l, r, hvm, hl, hr', rfl, rfl⟩
      have hfo := hsplit.fo hg.2.2
      obtain ⟨f1, b1, p1⟩ := hsg b.1 hb.2.1 l r ⟨hg.1, hg.2.1, hfo.1⟩ ⟨hg.1, hg.2.1, hfo.2⟩
        hsplit
      refine ⟨hb.1.trans f1, b1, fun gr hgr s hs => ?_⟩
      rcases List.mem_append.1 hgr with hgr | hgr
      · exact (hb.2.2 gr hgr s hs).mono (f1.stable (hb.1.isOpen ho))
      · obtain rfl := List.mem_singleton.1 hgr
        exact p1 s hs
    · exact hb

/-! ## A whole request -/

/-- Every strategy of every table has cursors that mean what `Prog` says. -/
def ProgAll (st : StateOf R Rel (Ans D P)) : Prop :=
  ∀ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t → ∀ gs, t.groups = some gs →
    ∀ gr ∈ gs, ∀ s ∈ gr.strats, Prog st i t.goal s

/-- What a run keeps: the invariant of the goals, the base, and the meaning
of every cursor. -/
structure Good (st : StateOf R Rel (Ans D P)) : Prop where
  inv : Inv st
  base : Base st
  prog : ProgAll st

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

omit [DecidableEq R] in
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

omit [DecidableEq R] in
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

omit [DecidableEq R] in
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
/-- Changing one table keeps what a run keeps, if its goal, its mark, its
answers and its strategies stay, and it stays complete if it was. -/
theorem Good.modify {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hcore : ∀ t, (f t).core = t.core)
    (hgr : ∀ t, (f t).groups = t.groups) (hb : ∀ t, (f t).born = t.born)
    (hd : ∀ t, t.done = true → (f t).done = true) : Good (st.modify i f) := by
  have e : ∀ t, (f t).goal = t.goal ∧ (f t).self = t.self ∧ (f t).answers = t.answers :=
    fun t => by
      have := hcore t
      simp only [Table.core, Prod.mk.injEq] at this
      exact this
  refine ⟨hG.inv.modify_same i f hcore hgr, hG.base.same (sameG_modify st i f fun t => (e t).1),
    hG.prog.modify i f (fun t => (e t).1)
      (stable_modify st i f fun t _ => ⟨(e t).1, hb t, (e t).2.2, hd t⟩) fun t ht gs hgs => ?_⟩
  rw [hgr] at hgs
  exact hG.prog i t ht gs hgs

omit [DecidableEq R] in
/-- Removing groups of one table keeps what a run keeps. -/
theorem Good.dropGroups {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat)
    (p : Group Rel (Ans D P) → Bool) :
    Good (st.modify i fun t => { t with groups := t.groups.map fun gs => gs.filter p }) := by
  refine ⟨hG.inv.dropGroups i p, hG.base.same (sameG_modify st i _ fun _ => rfl),
    hG.prog.modify i _ (fun _ => rfl)
      (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
      fun t ht gs hgs gr hgr s hs => ?_⟩
  cases hg : t.groups with
  | none => rw [hg] at hgs; cases hgs
  | some gs' =>
    rw [hg] at hgs
    cases hgs
    exact hG.prog i t ht gs' hg gr (List.mem_of_mem_filter hgr) s hs

omit [DecidableEq R] in
/-- Changing a group of a table keeps what a run keeps, if each strategy of
the group stays or fits with cursors that mean what they should. -/
theorem Good.setGroup {st : StateOf R Rel (Ans D P)} (hG : Good st) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P))
    (hf : ∀ g gr, goalAt st i = some g → ∀ s ∈ (f gr).strats,
      s ∈ gr.strats ∨ (StratOk st g s ∧ Prog st i g s)) : Good (setGroup st i k f) := by
  refine ⟨inv_setGroup hG.inv i k f fun g gr hg h s hs => (hf g gr hg s hs).elim (h s) (·.1),
    hG.base.same (sameG_modify st i _ fun _ => rfl),
    hG.prog.modify i _ (fun _ => rfl)
      (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
      fun t ht gs hgs gr hgr s hs => ?_⟩
  have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
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

omit [DecidableEq R] in
/-- A change of the tables that keeps of each its goal, its mark, its
answers and its strategies, and leaves a complete table complete, keeps what
a run keeps. -/
theorem Good.of_map {st st' : StateOf R Rel (Ans D P)} (hG : Good st)
    (F : Nat → Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hget : ∀ j, st'.tables[j]? = (st.tables[j]?).map (F j))
    (hcore : ∀ j t, (F j t).core = t.core) (hgr : ∀ j t, (F j t).groups = t.groups)
    (hb : ∀ j t, (F j t).born = t.born) (hd : ∀ j t, t.done = true → (F j t).done = true)
    (he : st'.edges = st.edges) : Good st' := by
  have e : ∀ j t, (F j t).goal = t.goal ∧ (F j t).self = t.self ∧ (F j t).answers = t.answers :=
    fun j t => by
      have := hcore j t
      simp only [Table.core, Prod.mk.injEq] at this
      exact this
  have hS : Stable st st' := fun k t hk =>
    ⟨F k t, by rw [hget, hk]; rfl, (e k t).1, hb k t, by rw [(e k t).2.2],
      fun h => ⟨hd k t h, (e k t).2.2⟩⟩
  refine ⟨hG.inv.of_map F hget hcore hgr, hG.base.same ⟨fun j => ?_, he⟩,
    fun j t' h gs hgs gr hgr' s hs => ?_⟩
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

/-- One strategy works and is put back. -/
theorem good_workStep (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (whole : Bool) (i : Nat) (g : GoalOf R Rel)
    (k j : Nat) (s : Strat Rel (Ans D P)) (hg : goalAt st i = some g) (hb : Busy st i)
    (hs : ((groupsAt st i)[k]?).bind (·.strats[j]?) = some s) :
    Good (setGroup (work (K := DerivationKernel.over D K hK P) whole i g st s).val.1 i k
      fun gr => { gr with
        strats := gr.strats.set j
          (work (K := DerivationKernel.over D K hK P) whole i g st s).val.2.1 }) := by
  have hok := strat_of_groupsAt hG.inv hg hs
  have hp := prog_of_groupsAt hG.prog hg hs
  have hgood := hG.base.good i g hg
  obtain ⟨h1, h2⟩ := inv_work (K := K) (hK := hK) hG.inv whole i g s hg hok
  have hB1 := base_work hL hR hG.base whole i g s hgood hp
  have hP1 := prog_work hL hR hG.inv hG.base.edges whole i g s hb.isOpen
    ⟨hgood.1, hgood.2.1⟩ hok hp
  have hA1 := hG.prog.frame (inner_work (K := K) (hK := hK) whole i g st s).frame hb.isOpen
  have hg' := (reach_work (K := K) (hK := hK) whole i g st s).ext _ _ hg
  refine Good.setGroup ⟨h1, hB1, hA1⟩ i k _ fun g' gr hg'' s' hs' => ?_
  obtain rfl : g' = g := Option.some.inj (hg''.symm.trans hg')
  rcases List.mem_or_eq_of_mem_set hs' with h' | rfl
  · exact .inl h'
  · exact .inr ⟨h2, hP1⟩

theorem good_workGroup (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Good st → Good (adv h st).val.1)
    (hadvK : ∀ h st, Keep st (adv h st).val.1) {st : StateOf R Rel (Ans D P)}
    (hG : Good st) (whole : Bool) (i : Nat) (g : GoalOf R Rel) (k : Nat)
    (hg : goalAt st i = some g) (hb : Busy st i) :
    Good (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1 := by
  have hstep := fun (st : StateOf R Rel (Ans D P)) hG j s hg hb hs =>
    good_workStep (K := K) (hK := hK) hL hR (st := st) hG whole i g k j s hg hb hs
  have hkw := fun (st : StateOf R Rel (Ans D P)) s hb =>
    keep_work (K := K) (hK := hK) (P := P) whole i g st s hb
  clear hR
  at_cost K hK
  simp only [workGroup, workStrats, feedAll, Cost.bind_val, Cost.pure_val]
  refine Good.setGroup ?_ _ _ _ (fun g' gr _ s hs => .inl hs)
  refine (foldL_inv (fun acc : StateOf R Rel (Ans D P) × Nat =>
    Good acc.1 ∧ goalAt acc.1 i = some g ∧ Busy acc.1 i) _ _ (fun b h _ hb => ?_) _ ?_).1
  · simp only [Cost.bind_val, Cost.pure_val]
    exact ⟨hadv _ _ hb.1, (hadvK _ _).stable.ext _ _ hb.2.1, (hadvK _ _).busy hb.2.2⟩
  · refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × Nat × Bool =>
      Good acc.1 ∧ goalAt acc.1 i = some g ∧ Busy acc.1 i) _ _ (fun b j _ hb => ?_)
      (st, 0, false) ⟨hG, hg, hb⟩
    split
    · exact hb
    · next s hs =>
      simp only [Cost.bind_val, Cost.pure_val]
      refine ⟨hstep b.1 hb.1 j s hb.2.1 hb.2.2 hs, ?_, ?_⟩
      · exact ((hkw b.1 s hb.2.2).trans (keep_setGroup _ i k _)).stable.ext _ _ hb.2.1
      · exact ((hkw b.1 s hb.2.2).trans (keep_setGroup _ i k _)).busy hb.2.2

theorem good_workLevel (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Good st → Good (adv h st).val.1)
    (hadvK : ∀ h st, Keep st (adv h st).val.1) {st : StateOf R Rel (Ans D P)}
    (hG : Good st) (whole : Bool) (i : Nat) (g : GoalOf R Rel) (lv : Nat)
    (hg : goalAt st i = some g) (hb : Busy st i) :
    Good (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv st).val.1 := by
  have hwg := fun (st : StateOf R Rel (Ans D P)) hG k hg hb =>
    good_workGroup (K := K) (hK := hK) hL hR adv hadv hadvK (st := st) hG whole i g k hg hb
  have hkg := fun k (st : StateOf R Rel (Ans D P)) hb =>
    keep_workGroup (K := K) (hK := hK) (P := P) adv hadvK whole i g k st hb
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
  obtain ⟨b1, p1⟩ := prog_expand hR hP hG.base i ho t.goal (hG.base.good i _ hg)
    (hG.inv.core i t ht).1
  have hfr := (inner_expand (K := K) (hK := hK) (P := P) (w := i) t.goal st).frame
  have hA1 := hG.prog.frame hfr ho
  have hE := (hfr.stable ho).ext
  suffices h : Base (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
      ProgAll (prepare (K := DerivationKernel.over D K hK P) i t st).val from ⟨hI, h.1, h.2⟩
  clear hI hR
  at_cost K hK
  unfold prepare
  cases t.groups with
  | some _ =>
    simp only [Cost.bind_val, Cost.pure_val]
    exact ⟨hG.base.same (sameG_modify st i _ fun _ => rfl),
      hG.prog.modify i _ (fun _ => rfl)
        (stable_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
        fun t' ht' gs hgs => hG.prog i t' ht' gs hgs⟩
  | none =>
    simp only [Cost.bind_val, Cost.pure_val]
    have hA2 : ProgAll ((expand (K := DerivationKernel.over D _ hK P) t.goal st).val.1.modify i
        fun t' => { t' with groups := some (expand (K := DerivationKernel.over D _ hK P) t.goal
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
    have hB2 : Base ((expand (K := DerivationKernel.over D _ hK P) t.goal st).val.1.modify i
        fun t' => { t' with groups := some (expand (K := DerivationKernel.over D _ hK P) t.goal
          st).val.2 }) := b1.same (sameG_modify _ i _ fun _ => rfl)
    exact ⟨hB2.same (sameG_modify _ i _ fun _ => rfl),
      hA2.modify i _ (fun _ => rfl)
        (stable_modify _ i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h⟩)
        fun t' ht' gs hgs => hA2 i t' ht' gs hgs⟩

/-- **A round keeps** the invariant of the goals, the base, and the meaning
of every cursor. -/
theorem good_advance (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) (hP : ProgFO P) :
    ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)), Good st →
      Good (advance (K := DerivationKernel.over D K hK P) fuel i st).val.1
  | 0, _, st, hG => by
    clear hR
    at_cost K hK
    exact hG
  | fuel + 1, i, st, hG => by
    have ih := fun h st => good_advance hL hR hP fuel h st
    have ihK := fun h st => keep_advance (K := K) (hK := hK) (P := P) fuel h st
    have hprep := fun t ht hd => good_prepare (K := K) (hK := hK) hR hP hG i t ht hd
    have hprepK := fun t ht hd => keep_prepare (K := K) (hK := hK) (P := P) i t st ht hd
    have hlev := fun whole g lv (st : StateOf R Rel (Ans D P)) hG hg hb =>
      good_workLevel (K := K) (hK := hK) hL hR _ ih ihK (st := st) hG whole i g lv hg hb
    have hlevK := fun whole g lv st hb =>
      keep_workLevel (K := K) (hK := hK) (P := P) _ ihK whole i g lv st hb
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
              (fun _ h => by simp [h])
            refine Good.dropGroups ?_ i _
            refine (foldL_inv (fun acc : StateOf R Rel (Ans D P) × Bool =>
              Good acc.1 ∧ goalAt acc.1 i = some t.goal ∧ Busy acc.1 i) _ _
              (fun b lv _ hb => ?_) _ ⟨hprep t ht hd', hk.stable.ext _ _ hg, hb⟩).1
            split
            · exact hb
            · exact ⟨hlev _ _ _ b.1 hb.1 hb.2.1 hb.2.2,
                (hlevK _ _ lv b.1 hb.2.2).stable.ext _ _ hb.2.1,
                (hlevK _ _ lv b.1 hb.2.2).busy hb.2.2⟩

/-- **A request keeps** the invariant of the goals, the base, and the
meaning of every cursor. -/
theorem good_request (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) (hP : ProgFO P)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) :
    Good (request (K := DerivationKernel.over D K hK P) st).val.1 := by
  have h := fun (st : StateOf R Rel (Ans D P)) hG =>
    good_advance (K := K) (hK := hK) hL hR hP st.tables.length 0 st hG
  clear hR
  at_cost K hK
  simp only [request, Cost.bind_val, Cost.pure_val]
  have h0 : Good ({ st with round := st.round + 1 } : StateOf R Rel (Ans D P)) :=
    hG.of_map (fun _ t => t) (fun j => by simp) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ h => h) rfl
  refine (h _ h0).of_map _ (fun j => List.getElem?_mapIdx) (fun j t => ?_) (fun j t => ?_)
    (fun j t => ?_) (fun j t hd => ?_) rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split
    · rfl
    · exact hd

/-- The first state has what a run keeps. -/
theorem good_init {root : Rel} (hn : Normal root) (hfo : root.FO) :
    Good (init (K := DerivationKernel.over D K hK P) root).val := by
  have hI := (inv_init (K := K) (hK := hK) (P := P) hn).1
  suffices h : Base (init (K := DerivationKernel.over D K hK P) root).val ∧
      ProgAll (init (K := DerivationKernel.over D K hK P) root).val from ⟨hI, h.1, h.2⟩
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
    fun j t h gs hgs => ?_⟩
  · obtain ⟨-, rfl⟩ := key j g _ h
    exact ⟨isBound_none D, isBound_none D, hfo⟩
  · rw [(key i g _ hi).1, (key j g _ hj).1]
  · obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? h)
    cases hgs

end kernel

end Symmetric

end RwLog
