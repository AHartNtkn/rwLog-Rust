/-
# What a run has paid before a marked table has its first round

A lower bound on what the symmetric engine pays, along its text. Some edges
are dear (`Exp`): reading one costs `B` ticks or more. Some goals are marked
(`Mark`, by their node): the first round of a marked goal reads a dear edge
unless one has been read (`Dear`).

A state is cheap (`Cheap`) when it has read no dear edge and no marked table
has had a round: a marked table has no groups and no answers. A request
keeps a state cheap or costs `B` ticks or more (`cheap_request`). So a run
whose state is not cheap has paid `B` (`spent_of_not_cheap`).

With the bodies of a name `h` marked, a state that holds an answer of the
body of `h` is not cheap, so a run that has covered a pair that needs pairs
of a call of `h` has paid `B` (`covered_paid`, `covered_paid_ctx`).
-/
import RwLog.Rungs.Symmetric.LightRun
import RwLog.Rungs.Framework.PaidOr

namespace RwLog

namespace Symmetric

open Traverse Cost

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
variable {rd : EdgeReader}

section defs

variable (Exp : Rel → Bool → Prop) (Mark : Rel → Prop)

/-- The state has read no dear edge, and reads edges to a depth of one or
more. -/
def CheapE (st : StateOf R Rel (Ans D P)) : Prop :=
  (∀ e ∈ st.edges, ¬ Exp e.1 e.2.1) ∧ 1 ≤ st.depth

/-- No marked table has had a round: it has no groups and no answers. -/
def CheapT (st : StateOf R Rel (Ans D P)) : Prop :=
  ∀ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t → Mark t.goal.node →
    t.groups = none ∧ t.answers = []

/-- The state is cheap: it has read no dear edge and no marked table has had
a round. -/
def Cheap (st : StateOf R Rel (Ans D P)) : Prop := CheapE Exp st ∧ CheapT Mark st

/-- The second state has the edges and the depth of the first. -/
def SameE (st st' : StateOf R Rel (Ans D P)) : Prop :=
  st'.edges = st.edges ∧ st'.depth = st.depth

end defs

variable {Exp : Rel → Bool → Prop} {Mark : Rel → Prop} {B : Nat}

omit [DecidableEq R] in
theorem SameE.refl (st : StateOf R Rel (Ans D P)) : SameE st st := ⟨rfl, rfl⟩

omit [DecidableEq R] in
theorem SameE.trans {a b c : StateOf R Rel (Ans D P)} (h₁ : SameE a b) (h₂ : SameE b c) :
    SameE a c := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

omit [DecidableEq R] in
theorem CheapE.same {st st' : StateOf R Rel (Ans D P)} (h : CheapE Exp st) (he : SameE st st') :
    CheapE Exp st' := by
  unfold CheapE
  rw [he.1, he.2]
  exact h

omit [DecidableEq R] in
theorem sameE_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) : SameE st (st.modify i f) := ⟨rfl, rfl⟩

omit [DecidableEq R] in
/-- Changing one table keeps the marked tables without a round, if the goal
stays and a table with no groups and no answers is left so. -/
theorem CheapT.modify {st : StateOf R Rel (Ans D P)} (h : CheapT Mark st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hg : ∀ t, (f t).goal = t.goal)
    (hk : ∀ t, t.groups = none → t.answers = [] → (f t).groups = none ∧ (f t).answers = []) :
    CheapT Mark (st.modify i f) := by
  intro j t' ht' hm
  rcases getElem?_modify_cases st i f ht' with ⟨-, ht⟩ | ⟨rfl, t, ht, rfl⟩
  · exact h j t' ht hm
  · rw [hg] at hm
    obtain ⟨h1, h2⟩ := h j t ht hm
    exact hk t h1 h2

omit [DecidableEq R] in
/-- Changing a table that is not marked keeps the marked tables without a
round, if the goal stays. -/
theorem CheapT.modify_un {st : StateOf R Rel (Ans D P)} (h : CheapT Mark st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hg : ∀ t, (f t).goal = t.goal)
    (hun : ∀ t, st.tables[i]? = some t → ¬ Mark t.goal.node) : CheapT Mark (st.modify i f) := by
  intro j t' ht' hm
  rcases getElem?_modify_cases st i f ht' with ⟨-, ht⟩ | ⟨rfl, t, ht, rfl⟩
  · exact h j t' ht hm
  · rw [hg] at hm
    exact absurd hm (hun t ht)

omit [DecidableEq R] in
theorem Cheap.modify {st : StateOf R Rel (Ans D P)} (h : Cheap Exp Mark st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hg : ∀ t, (f t).goal = t.goal)
    (hk : ∀ t, t.groups = none → t.answers = [] → (f t).groups = none ∧ (f t).answers = []) :
    Cheap Exp Mark (st.modify i f) :=
  ⟨h.1.same (sameE_modify st i f), h.2.modify i f hg hk⟩

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- The work of the strategies of a table that is not marked keeps the
marked tables without a round. -/
theorem CheapT.inner {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : CheapT Mark st)
    (hI : Inner K hK j st st') {g : GoalOf R Rel} (hj : goalAt st j = some g)
    (hg : ¬ Mark g.node) : CheapT Mark st' := by
  obtain ⟨tj, htj, rfl⟩ := table_of_goalAt hj
  intro k t' ht' hm
  cases hs : st.tables[k]? with
  | some t =>
    obtain ⟨u, hu, e1, -, -, -, e5, e6, -⟩ := hI.frame.2.1 k t hs
    rw [ht'] at hu
    cases hu
    rw [e1] at hm
    by_cases e : k = j
    · subst e
      rw [htj] at hs
      cases hs
      exact absurd hm hg
    · rw [e5, e6 e]
      exact h k t hs hm
  | none =>
    refine ⟨(hI.frame.2.2 k t' ht' hs).1, hI.fresh k t' ht' hs fun e => ?_⟩
    subst e
    rw [htj] at hs
    cases hs

/-- Work that could be the work of the strategies of either of two tables
keeps the marked tables without a round. -/
theorem CheapT.quiet {w1 w2 : Nat} {st st' : StateOf R Rel (Ans D P)} (h : CheapT Mark st)
    (h1 : Inner K hK w1 st st') (h2 : Inner K hK w2 st st') (hne : w1 ≠ w2) : CheapT Mark st' := by
  intro k t' ht' hm
  cases hs : st.tables[k]? with
  | some t =>
    obtain ⟨u, hu, e1, -, -, -, e5, e6, -⟩ := h1.frame.2.1 k t hs
    obtain ⟨u2, hu2, -, -, -, -, -, f6, -⟩ := h2.frame.2.1 k t hs
    rw [ht'] at hu hu2
    cases hu
    cases hu2
    rw [e1] at hm
    rw [e5]
    by_cases e : k = w1
    · rw [f6 (fun e' => hne (e.symm.trans e'))]
      exact h k t hs hm
    · rw [e6 e]
      exact h k t hs hm
  | none =>
    refine ⟨(h1.frame.2.2 k t' ht' hs).1, ?_⟩
    by_cases e : k = w1
    · exact h2.fresh k t' ht' hs (fun e' => hne (e.symm.trans e'))
    · exact h1.fresh k t' ht' hs e

/-! ## Changes that read no edge -/

theorem sameE_openGoal (st : StateOf R Rel (Ans D P)) (g : GoalOf R Rel) :
    SameE st (openGoal (K := DerivationKernel.over D K hK P) st g).val.1 := by
  at_cost K hK
  simp only [openGoal, Cost.bind_val]
  split
  · exact SameE.refl _
  · exact ⟨rfl, rfl⟩

theorem sameE_addAnswer (st : StateOf R Rel (Ans D P)) (i : Nat) (a : Ans D P) :
    SameE st (addAnswer (K := DerivationKernel.over D K hK P) i st a).val := by
  rw [addAnswer_val]
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem sameE_addOption (st : StateOf R Rel (Ans D P)) (i : Nat) (o : Option (Ans D P)) :
    SameE st (addOption (K := DerivationKernel.over D K hK P) i st o).val := by
  have hv := fun a => sameE_addAnswer (K := K) (hK := hK) (P := P) st i a
  at_cost K hK
  cases o with
  | none => exact SameE.refl st
  | some a => exact hv a

theorem sameE_copyFrom (i : Nat) (g : GoalOf R Rel) (isCall : Bool) (m : Nat)
    (st : StateOf R Rel (Ans D P)) (as : List (Ans D P)) :
    SameE st (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val := by
  have h := fun st o => sameE_addOption (K := K) (hK := hK) (P := P) st i o
  at_cost K hK
  refine foldL_inv (fun b => SameE st b) _ as (fun b a _ hb => ?_) st (SameE.refl st)
  dsimp only
  split <;> (rw [Cost.bind_val]; exact hb.trans (h _ _))

theorem sameE_joinPairs (i : Nat) (k : Kind) (xs ys : List (Ans D P))
    (st : StateOf R Rel (Ans D P)) (ps : List (Nat × Nat)) :
    SameE st (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val := by
  have h := fun st o => sameE_addOption (K := K) (hK := hK) (P := P) st i o
  at_cost K hK
  refine foldL_inv (fun b => SameE st b) _ ps (fun b p _ hb => ?_) st (SameE.refl st)
  split
  · rw [Cost.bind_val]; exact hb.trans (h _ _)
  · exact hb

theorem sameE_pushTake (i : Nat) (k : Kind) (left : Bool) (x : Ans D P)
    (st : StateOf R Rel (Ans D P)) (ys : List (Ans D P)) :
    SameE st (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val := by
  have h := fun st o => sameE_addOption (K := K) (hK := hK) (P := P) st i o
  at_cost K hK
  refine foldL_inv (fun b => SameE st b) _ ys (fun b y _ hb => ?_) st (SameE.refl st)
  rw [Cost.bind_val]
  exact hb.trans (h _ _)

theorem sameE_pushOpen (g : GoalOf R Rel) (other : Rel) (k : Kind) (left : Bool)
    (st : StateOf R Rel (Ans D P)) (xs : List (Ans D P)) :
    SameE st (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1 := by
  have h := fun st g => sameE_openGoal (K := K) (hK := hK) (P := P) st g
  at_cost K hK
  refine foldL_inv (fun b : StateOf R Rel (Ans D P) × List (Ans D P × Nat × Nat) =>
    SameE st b.1) _ xs (fun b x _ hb => ?_) (st, []) (SameE.refl st)
  simp only [Cost.bind_val]
  exact hb.trans (h _ _)

theorem sameE_checkOpen (g : GoalOf R Rel) (left : Bool) (other : Rel)
    (st : StateOf R Rel (Ans D P)) (ps : List R) :
    SameE st (checkOpen (K := DerivationKernel.over D K hK P) g left other st ps).val.1 := by
  have h := fun st g => sameE_openGoal (K := K) (hK := hK) (P := P) st g
  at_cost K hK
  refine foldL_inv (fun b : StateOf R Rel (Ans D P) × List Nat => SameE st b.1) _ ps
    (fun b x _ hb => ?_) (st, []) (SameE.refl st)
  simp only [Cost.bind_val]
  exact hb.trans (h _ _)

theorem sameE_splitGroup (k : Kind) (L Rg : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    SameE st (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 := by
  have h := fun st g => sameE_openGoal (K := K) (hK := hK) (P := P) st g
  at_cost K hK
  simp only [splitGroup, Cost.bind_val]
  exact (h _ _).trans (h _ _)

/-! ## Reading an edge -/

/-- What is asked of the dear edges and the marked goals: a reading of a dear
edge that returns something costs `B` ticks or more, and so does the first
round of a marked goal in a state that has read no dear edge. -/
structure Dear (rd : EdgeReader) (K : Kernel R Cost) (hK : K.Refines D) (P : Program)
    (Exp : Rel → Bool → Prop) (Mark : Rel → Prop) (B : Nat) : Prop where
  read : ∀ (last : Bool) (depth : Nat) (n : Rel) (e : Option (List R)), Exp n last →
    (@rd R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) last depth n).val = some e →
    B ≤ (@rd R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) last depth n).ticks
  expand : ∀ (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P)), Mark g.node → CheapE Exp st →
    B ≤ (expand @rd (K := DerivationKernel.over D K hK P) g st).ticks

theorem e_edgeOf (hD : Dear @rd K hK P Exp Mark B) {st : StateOf R Rel (Ans D P)}
    (h : CheapE Exp st) (last : Bool) (n : Rel) :
    PaidOr B (edgeOf @rd (K := DerivationKernel.over D K hK P) st last n)
      (fun r => CheapE Exp r.1) := by
  have hread := hD.read last st.depth n
  clear hD
  at_cost K hK
  unfold edgeOf
  refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
  split
  · exact .of_val h
  · refine PaidOr.bind (Q := fun r => ∀ e, r = some e → ¬ Exp n last) ?_ fun hr => ?_
    · by_cases hE : Exp n last
      · cases hv : (@rd R Rel (Ans D P) Cost (DerivationKernel.over D _ hK P) last st.depth n).val with
        | none => exact .inr fun e he => by rw [hv] at he; cases he
        | some e => exact .inl (hread e hE hv)
      · exact .of_val fun _ _ => hE
    · refine .of_val ?_
      simp only [Cost.pure_val]
      split
      · next e he =>
        refine ⟨fun x hx => ?_, h.2⟩
        rcases List.mem_append.1 hx with hx | hx
        · exact h.1 x hx
        · obtain rfl := List.mem_singleton.1 hx
          exact hr e he
      · exact ⟨h.1, Nat.le_trans h.2 (Nat.le_mul_of_pos_left _ (by decide))⟩


theorem e_checkOf (hD : Dear @rd K hK P Exp Mark B) {st : StateOf R Rel (Ans D P)}
    (h : CheapE Exp st) (left : Bool) (side other : Rel) :
    PaidOr B (checkOf @rd (K := DerivationKernel.over D K hK P) st left side other)
      (fun r => CheapE Exp r.1) := by
  have hE := e_edgeOf (rd := @rd) hD h left side
  clear hD
  at_cost K hK
  unfold checkOf
  exact PaidOr.bind hE fun h' => .of_val h'

theorem e_chainGroups (hD : Dear @rd K hK P Exp Mark B) {st : StateOf R Rel (Ans D P)}
    (h : CheapE Exp st) (g : GoalOf R Rel) (k : Nat) :
    PaidOr B (chainGroups @rd (K := DerivationKernel.over D K hK P) g k st)
      (fun r => CheapE Exp r.1) := by
  have hck := fun (st : StateOf R Rel (Ans D P)) h left side other =>
    e_checkOf (rd := @rd) hD (st := st) h left side other
  have hsg := fun k L Rg st => sameE_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  clear hD
  at_cost K hK
  unfold chainGroups
  refine paidOr_foldL (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) ×
    List (Strat Rel (Ans D P)) => CheapE Exp acc.1) _ _ (fun b i _ hb => ?_) (st, [], []) h
  refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
  refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
  split
  · refine PaidOr.bind (Q := fun r => CheapE Exp r.1) (.of_val (hb.same (hsg _ _ _ _))) fun h1 => ?_
    refine PaidOr.bind (hck _ h1 _ _ _) fun h2 => ?_
    exact PaidOr.bind (hck _ h2 _ _ _) fun h3 => .of_val h3
  · exact .of_val hb

/-- The groups of a goal are made: no dear edge is read, or `B` is paid. -/
theorem e_expand (hD : Dear @rd K hK P Exp Mark B) {st : StateOf R Rel (Ans D P)}
    (h : CheapE Exp st) (g : GoalOf R Rel) :
    PaidOr B (expand @rd (K := DerivationKernel.over D K hK P) g st)
      (fun r => CheapE Exp r.1) := by
  have hcg := fun k => e_chainGroups (rd := @rd) hD h g k
  have hsg := fun k L Rg st => sameE_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  have hog := fun st g => sameE_openGoal (K := K) (hK := hK) (P := P) st g
  clear hD
  at_cost K hK
  unfold expand
  refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
  split
  · exact .of_val h
  · refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
    split
    · exact .of_val h
    · exact PaidOr.bind (Q := fun r => CheapE Exp r.1) (.of_val (h.same (hog _ _))) fun h1 =>
        .of_val h1
  · refine PaidOr.bind (Q := fun r => CheapE Exp r.1) ?_ fun h1 => .of_val h1
    refine paidOr_foldL (fun acc : StateOf R Rel (Ans D P) × List (Nat × Nat) =>
      CheapE Exp acc.1) _ _ (fun b x _ hb => ?_) (st, []) h
    exact PaidOr.bind (Q := fun r => CheapE Exp r.1) (.of_val (hb.same (hog _ _))) fun h1 =>
      .of_val h1
  · exact PaidOr.bind (hcg _) fun h1 => .of_val h1
  · refine paidOr_foldL (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) =>
      CheapE Exp acc.1) _ _ (fun b x _ hb => ?_) (st, []) h
    refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
    split
    · exact PaidOr.bind (Q := fun r => CheapE Exp r.1) (.of_val (hb.same (hsg _ _ _ _))) fun h1 =>
        .of_val h1
    · exact .of_val hb

/-! ## The work of a strategy -/

/-- The work of a strategy that reads no edge. -/
theorem sameE_work (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (hs : ∀ left side other, s ≠ .check left side other .reading) :
    SameE st (work @rd (K := DerivationKernel.over D K hK P) i g st s).val.1 := by
  have hao := fun st o => sameE_addOption (K := K) (hK := hK) (P := P) st i o
  have hcf := fun g isCall m st as => sameE_copyFrom (K := K) (hK := hK) (P := P) i g isCall m st as
  have hjp := fun k xs ys st ps => sameE_joinPairs (K := K) (hK := hK) (P := P) i k xs ys st ps
  have hpo := fun g other k left st xs =>
    sameE_pushOpen (K := K) (hK := hK) (P := P) g other k left st xs
  have hpt := fun k left x st ys => sameE_pushTake (K := K) (hK := hK) (P := P) i k left x st ys
  at_cost K hK
  cases s with
  | span ran =>
    cases ran
    · simp only [work, Cost.bind_val, Cost.pure_val]
      exact hao _ _
    · exact SameE.refl _
  | copy isCall subs =>
    simp only [work]
    split
    · exact SameE.refl _
    · simp only [Cost.bind_val, Cost.pure_val]
      exact (hcf _ _ _ _ _).trans (sameE_modify _ _ _)
  | join k a b c =>
    simp only [work]
    split
    · exact SameE.refl _
    · simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      exact (hjp _ _ _ _ _).trans (sameE_modify _ _ _)
  | push k left side other subs dead reads c fc =>
    simp only [work, Cost.bind_val]
    split
    · exact SameE.refl _
    · split
      · simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
        exact hpo _ _ _ _ _ _
      · simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
        exact (hpt _ _ _ _ _).trans (sameE_modify _ _ _)
      · exact SameE.refl _
  | check left side other c =>
    cases c with
    | reading => exact absurd rfl (hs left side other)
    | off => exact SameE.refl _
    | opened subs => exact SameE.refl _

theorem e_work (hD : Dear @rd K hK P Exp Mark B) {st : StateOf R Rel (Ans D P)}
    (h : CheapE Exp st) (i : Nat) (g : GoalOf R Rel) (s : Strat Rel (Ans D P)) :
    PaidOr B (work @rd (K := DerivationKernel.over D K hK P) i g st s)
      (fun r => CheapE Exp r.1) := by
  by_cases hs : ∀ left side other, s ≠ .check left side other .reading
  · exact .of_val (h.same (sameE_work i g st s hs))
  · have hs' : ∃ left side other, s = .check left side other .reading := by
      by_contra hne
      exact hs fun l si o e => hne ⟨l, si, o, e⟩
    obtain ⟨left, side, other, rfl⟩ := hs'
    have hE := e_edgeOf (rd := @rd) hD h left side
    have hco := fun g left other st ps =>
      sameE_checkOpen (K := K) (hK := hK) (P := P) g left other st ps
    clear hD hs
    at_cost K hK
    unfold work
    refine PaidOr.bind' hE ?_
    rintro ⟨st', e⟩ h1
    dsimp only at h1 ⊢
    split
    · exact .of_val h1
    · exact .of_val h1
    · exact PaidOr.bind (Q := fun r => CheapE Exp r.1) (.of_val (h1.same (hco _ _ _ _ _)))
        fun h2 => .of_val h2

/-- One unit of the work of a strategy of a table that is not marked keeps
the state cheap, or costs `B`. -/
theorem cheap_work (hD : Dear @rd K hK P Exp Mark B) {st : StateOf R Rel (Ans D P)}
    (h : Cheap Exp Mark st) (i : Nat) (g : GoalOf R Rel) (s : Strat Rel (Ans D P))
    {g0 : GoalOf R Rel} (hj : goalAt st i = some g0) (hg : ¬ Mark g0.node) :
    PaidOr B (work @rd (K := DerivationKernel.over D K hK P) i g st s)
      (fun r => Cheap Exp Mark r.1 ∧ goalAt r.1 i = some g0) :=
  (e_work hD h.1 i g s).mono fun he =>
    ⟨⟨he, h.2.inner (inner_work i g st s) hj hg⟩, (reach_work i g st s).ext _ _ hj⟩

/-- A turn of a strategy of a table that is not marked keeps the state
cheap, or costs `B`. -/
theorem cheap_turn (hD : Dear @rd K hK P Exp Mark B) (i : Nat) (g : GoalOf R Rel)
    {g0 : GoalOf R Rel} (hg : ¬ Mark g0.node) :
    ∀ (f left : Nat) (st : StateOf R Rel (Ans D P)) (s : Strat Rel (Ans D P)) (c : Nat),
      Cheap Exp Mark st → goalAt st i = some g0 →
      PaidOr B (turn @rd (K := DerivationKernel.over D K hK P) i g f left st s c)
        (fun r => Cheap Exp Mark r.1 ∧ goalAt r.1 i = some g0) := by
  have hw := fun (st : StateOf R Rel (Ans D P)) h s hj =>
    cheap_work (rd := @rd) hD (st := st) h i g s hj hg
  clear hD
  at_cost K hK
  intro f
  induction f with
  | zero => exact fun left st s c h hj => .of_val ⟨h, hj⟩
  | succ f ih =>
    intro left st s c h hj
    unfold turn
    split
    · exact .of_val ⟨h, hj⟩
    · refine PaidOr.bind'
        (Q := fun rt : (StateOf R Rel (Ans D P) × Strat Rel (Ans D P) × Bool) × Nat =>
          Cheap Exp Mark rt.1.1 ∧ goalAt rt.1.1 i = some g0)
        (show PaidOr B (Cost.metered _) _ from PaidOr.metered (hw st h s hj)) ?_
      rintro ⟨r, t⟩ hr
      dsimp only at hr ⊢
      split
      · exact PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ih _ _ _ _ hr.1 hr.2
      · exact .of_val hr


/-! ## A round -/

section feed

variable (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))

theorem cheap_feed
    (hadv : ∀ h st, Cheap Exp Mark st → PaidOr B (adv h st) (fun r => Cheap Exp Mark r.1))
    (h : Nat) {st : StateOf R Rel (Ans D P)} (hc : Cheap Exp Mark st) :
    PaidOr B (feed (K := DerivationKernel.over D K hK P) adv h st)
      (fun r => Cheap Exp Mark r.1) := by
  at_cost K hK
  unfold feed
  refine PaidOr.bind'
    (Q := fun rc : (StateOf R Rel (Ans D P) × Nat) × Nat => Cheap Exp Mark rc.1.1)
    (show PaidOr B (Cost.metered _) _ from PaidOr.metered (hadv h st hc)) ?_
  rintro ⟨r, c⟩ hr
  exact .of_val (hr.modify _ _ (fun _ => rfl) fun t h1 h2 => ⟨h1, h2⟩)

theorem cheap_feedToks
    (step : ∀ h X, Cheap Exp Mark X →
      PaidOr B (feed (K := DerivationKernel.over D K hK P) adv h X) (fun r => Cheap Exp Mark r.1))
    (subs : List (Ans D P × Option (Nat × Nat))) (f : Nat) (st : StateOf R Rel (Ans D P))
    (d : Nat) (fc : Cursor) (h : Cheap Exp Mark st) :
    PaidOr B (feedToks (K := DerivationKernel.over D K hK P) adv subs f st d fc)
      (fun r => Cheap Exp Mark r.1) := by
  at_cost K hK
  induction f generalizing st d fc with
  | zero => exact .of_val h
  | succ f ih =>
    unfold feedToks
    split
    · exact .of_val h
    · split
      · exact ih _ _ _ h
      · refine PaidOr.bind (step _ _ h) fun hr => ?_
        split
        · exact .of_val hr
        · exact ih _ _ _ hr

theorem cheap_feedPush
    (step : ∀ h X, Cheap Exp Mark X →
      PaidOr B (feed (K := DerivationKernel.over D K hK P) adv h X) (fun r => Cheap Exp Mark r.1))
    (st : StateOf R Rel (Ans D P)) (d : Nat) (s : Strat Rel (Ans D P)) (h : Cheap Exp Mark st) :
    PaidOr B (feedPush (K := DerivationKernel.over D K hK P) adv st d s)
      (fun r => Cheap Exp Mark r.1) := by
  have hT := fun subs f fc =>
    cheap_feedToks (K := K) (hK := hK) (P := P) adv step subs f st d fc h
  at_cost K hK
  cases s with
  | push k left side other subs dead reads c fc =>
    unfold feedPush
    exact PaidOr.bind (hT _ _ _) fun hr => .of_val hr
  | _ => exact .of_val h

theorem cheap_feedPushes
    (step : ∀ h X, Cheap Exp Mark X →
      PaidOr B (feed (K := DerivationKernel.over D K hK P) adv h X) (fun r => Cheap Exp Mark r.1))
    (ss : List (Strat Rel (Ans D P))) (st : StateOf R Rel (Ans D P)) (d : Nat)
    (h : Cheap Exp Mark st) :
    PaidOr B (feedPushes (K := DerivationKernel.over D K hK P) adv st d ss)
      (fun r => Cheap Exp Mark r.1) := by
  have hT := fun X d s hX => cheap_feedPush (K := K) (hK := hK) (P := P) adv step X d s hX
  at_cost K hK
  induction ss generalizing st d with
  | nil => exact .of_val h
  | cons s rest ih =>
    unfold feedPushes
    refine PaidOr.bind (hT st d s h) fun h1 => ?_
    exact PaidOr.bind (ih _ _ h1) fun h2 => .of_val h2

/-- The rounds of the tables a group reads keep the state cheap, or cost
`B`, if a round does. -/
theorem cheap_feedGroup
    (hadv : ∀ h st, Cheap Exp Mark st → PaidOr B (adv h st) (fun r => Cheap Exp Mark r.1))
    (i k : Nat) (st : StateOf R Rel (Ans D P)) (d : Nat) (h0 : Cheap Exp Mark st) :
    PaidOr B (feedGroup (K := DerivationKernel.over D K hK P) adv i k st d)
      (fun r => Cheap Exp Mark r.1) := by
  have step := fun h (X : StateOf R Rel (Ans D P)) hX =>
    cheap_feed (K := K) (hK := hK) (P := P) adv hadv h (st := X) hX
  have hT := fun ss X d hX =>
    cheap_feedPushes (K := K) (hK := hK) (P := P) adv step ss X d hX
  at_cost K hK
  unfold feedGroup
  dsimp only
  split
  · refine PaidOr.bind (Q := fun r => Cheap Exp Mark r.1) ?_ fun h1 => .of_val h1
    unfold feedFirst
    refine PaidOr.bind (Q := fun r => Cheap Exp Mark r.1) ?_ fun h1 => .of_val h1
    refine paidOr_foldL (fun acc : StateOf R Rel (Ans D P) × Nat × Bool =>
      Cheap Exp Mark acc.1) _ _ (fun b h _ hb => ?_) _ h0
    split
    · exact .of_val hb
    · exact PaidOr.bind (step _ _ hb) fun h1 => .of_val h1
  · refine PaidOr.bind (Q := fun r => Cheap Exp Mark r.1) ?_ fun h1 => hT _ _ _ h1
    unfold feedAll
    refine paidOr_foldL (fun acc : StateOf R Rel (Ans D P) × Nat => Cheap Exp Mark acc.1) _ _
      (fun b h _ hb => ?_) _ h0
    exact PaidOr.bind (step _ _ hb) fun h1 => .of_val h1

end feed

omit [DecidableEq R] in
theorem Cheap.setGroup {st : StateOf R Rel (Ans D P)} (h : Cheap Exp Mark st) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P)) : Cheap Exp Mark (setGroup st i k f) :=
  h.modify i _ (fun _ => rfl) fun t h1 h2 => ⟨by simp [h1], h2⟩

/-- The work of a group of a table that is not marked keeps the state cheap,
or costs `B`, if a round does. -/
theorem cheap_workGroup (hD : Dear @rd K hK P Exp Mark B)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Cheap Exp Mark st → PaidOr B (adv h st) (fun r => Cheap Exp Mark r.1))
    {st : StateOf R Rel (Ans D P)} (h : Cheap Exp Mark st) (i : Nat) (g : GoalOf R Rel) (k : Nat)
    {g0 : GoalOf R Rel} (hj : goalAt st i = some g0) (hg : ¬ Mark g0.node) :
    PaidOr B (workGroup @rd (K := DerivationKernel.over D K hK P) adv i g k st)
      (fun r => Cheap Exp Mark r.1) := by
  have hturn := fun f left (st : StateOf R Rel (Ans D P)) s c hc hj =>
    cheap_turn (rd := @rd) hD i g hg f left st s c hc hj
  have hf := fun X d (hX : Cheap Exp Mark X) =>
    cheap_feedGroup (K := K) (hK := hK) (P := P) adv hadv i k X d hX
  have hsg : ∀ (X : StateOf R Rel (Ans D P)) f, goalAt (setGroup X i k f) i = goalAt X i :=
    fun X f => goalAt_modify _ i i _ fun _ => rfl
  clear hD
  at_cost K hK
  unfold workGroup
  refine PaidOr.bind (Q := fun r => Cheap Exp Mark r.1) ?_ fun h1 => ?_
  · unfold workStrats
    dsimp only
    refine (paidOr_foldL (fun acc : StateOf R Rel (Ans D P) × Nat × Bool =>
      Cheap Exp Mark acc.1 ∧ goalAt acc.1 i = some g0) _ _ (fun b j _ hb => ?_) (st, 0, false)
      ⟨h, hj⟩).mono fun hc => hc.1
    split
    · exact .of_val hb
    · refine PaidOr.bind (hturn _ _ b.1 _ _ hb.1 hb.2) fun hr => ?_
      exact .of_val ⟨hr.1.setGroup _ _ _, (hsg _ _).trans hr.2⟩
  · refine PaidOr.bind (hf _ _ h1) fun h2 => ?_
    exact .of_val ((h2.setGroup _ _ _).modify _ _ (fun _ => rfl) fun t h1 h2 => ⟨h1, h2⟩)

theorem cheap_workLevel (hD : Dear @rd K hK P Exp Mark B)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Cheap Exp Mark st → PaidOr B (adv h st) (fun r => Cheap Exp Mark r.1))
    (hadvR : ∀ h st, Reach K hK st (adv h st).val.1)
    {st : StateOf R Rel (Ans D P)} (h : Cheap Exp Mark st) (i : Nat) (g : GoalOf R Rel) (lv : Nat)
    {g0 : GoalOf R Rel} (hj : goalAt st i = some g0) (hg : ¬ Mark g0.node) :
    PaidOr B (workLevel @rd (K := DerivationKernel.over D K hK P) adv i g lv st)
      (fun r => Cheap Exp Mark r.1) := by
  have hwg := fun (st : StateOf R Rel (Ans D P)) hc k hj =>
    cheap_workGroup (rd := @rd) hD adv hadv (st := st) hc i g k hj hg
  have hwgR := fun k st => reach_workGroup (rd := @rd) (K := K) (hK := hK) (P := P) adv hadvR i g k st
  clear hD
  at_cost K hK
  unfold workLevel
  refine (paidOr_foldL (fun acc : StateOf R Rel (Ans D P) × Bool =>
    Cheap Exp Mark acc.1 ∧ goalAt acc.1 i = some g0) _ _ (fun b p _ hb => ?_) (st, false)
    ⟨h, hj⟩).mono fun hc => hc.1
  split
  · refine PaidOr.bind'
      (Q := fun r : StateOf R Rel (Ans D P) × Nat × Bool =>
        Cheap Exp Mark r.1 ∧ goalAt r.1 i = some g0)
      ((hwg b.1 hb.1 _ hb.2).mono fun hc => ⟨hc, (hwgR _ b.1).ext _ _ hb.2⟩) ?_
    rintro ⟨st', d, did⟩ h1
    exact .of_val h1
  · exact .of_val hb

/-- Before the round of a table: its groups are made. If the table is marked
that costs `B`. -/
theorem cheap_prepare (hD : Dear @rd K hK P Exp Mark B) {st : StateOf R Rel (Ans D P)}
    (h : Cheap Exp Mark st) (i : Nat) (t : Table R Rel (Ans D P)) (ht : st.tables[i]? = some t) :
    PaidOr B (prepare @rd (K := DerivationKernel.over D K hK P) i t st)
      (fun st' => Cheap Exp Mark st' ∧ ¬ Mark t.goal.node) := by
  have hexp := hD.expand t.goal st
  have hE := e_expand (rd := @rd) hD h.1 t.goal
  have hT := h.2.quiet (inner_expand (rd := @rd) (K := K) (hK := hK) (w := 0) t.goal st)
    (inner_expand (rd := @rd) (K := K) (hK := hK) (w := 1) t.goal st) (by decide)
  have hgoal : goalAt (expand @rd (K := DerivationKernel.over D K hK P) t.goal st).val.1 i =
      some t.goal := (reach_expand t.goal st).ext _ _ (by unfold goalAt; rw [ht]; rfl)
  have hmk := h.2 i t ht
  clear hD
  at_cost K hK
  unfold prepare
  by_cases hm : Mark t.goal.node
  · have hg := (hmk hm).1
    rw [hg]
    dsimp only
    exact .of_ticks (le_bind_ticks (hexp hm h.1))
  · cases t.groups with
    | some _ =>
      dsimp only
      exact PaidOr.bind (Q := fun X => Cheap Exp Mark X) (.of_val h) fun h1 =>
        .of_val ⟨h1.modify _ _ (fun _ => rfl) fun t h1 h2 => ⟨h1, h2⟩, hm⟩
    | none =>
      dsimp only
      refine PaidOr.bind'
        (Q := fun r : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) =>
          Cheap Exp Mark r.1 ∧ goalAt r.1 i = some t.goal)
        (hE.mono fun he => ⟨⟨he, hT⟩, hgoal⟩) ?_
      rintro ⟨st', gs⟩ h1
      dsimp only at h1 ⊢
      refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
      refine PaidOr.bind (Q := fun X => Cheap Exp Mark X) (.of_val ?_) fun h2 =>
        .of_val ⟨h2.modify _ _ (fun _ => rfl) fun t h1 h2 => ⟨h1, h2⟩, hm⟩
      refine ⟨h1.1.1.same (sameE_modify _ _ _), h1.1.2.modify_un i _ (fun _ => rfl) fun t' ht' => ?_⟩
      obtain ⟨u, hu, e⟩ := table_of_goalAt h1.2
      rw [ht'] at hu
      cases hu
      rw [e]
      exact hm

/-- The race of a table that is not marked keeps the state cheap. -/
theorem cheap_askRace (U : GOracle R Rel (Ans D P) Cost) {st : StateOf R Rel (Ans D P)}
    (h : Cheap Exp Mark st) (i : Nat) (g : GoalOf R Rel) {g0 : GoalOf R Rel}
    (hj : goalAt st i = some g0) (hg : ¬ Mark g0.node) :
    Cheap Exp Mark (askRace (K := DerivationKernel.over D K hK P) U i g st).val.1 := by
  have hadd : ∀ xs : List (Ans D P),
      Cheap Exp Mark (Traverse.foldL (addAnswer (K := DerivationKernel.over D K hK P) i) st xs).val := fun xs =>
    (Traverse.foldL_inv (fun b : StateOf R Rel (Ans D P) => Cheap Exp Mark b ∧ goalAt b i = some g0) _ _
      (fun b x _ hb => ⟨⟨hb.1.1.same (sameE_addAnswer b i x),
        hb.1.2.inner (Inner.add (K := K) (hK := hK) b x) hb.2 hg⟩,
        (Reach.add (K := _) (hK := hK) b i x).ext _ _ hb.2⟩) st ⟨h, hj⟩).1
  have hmod : ∀ (X : StateOf R Rel (Ans D P)) (r : Race), Cheap Exp Mark X →
      Cheap Exp Mark (X.modify i fun t => { t with race := some r }) := fun X r hX =>
    hX.modify _ _ (fun _ => rfl) fun t h1 h2 => ⟨h1, h2⟩
  rw [askRace_val]
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · split
        · split
          · exact hmod _ _ (hadd _)
          · exact hmod _ _ h
        · exact hmod _ _ h

/-- **A round keeps the state cheap, or costs `B`.** -/
theorem cheap_advance (hD : Dear @rd K hK P Exp Mark B) (U : GOracle R Rel (Ans D P) Cost) :
    ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)), Cheap Exp Mark st →
      PaidOr B (advance @rd (K := DerivationKernel.over D K hK P) U fuel i st)
        (fun r => Cheap Exp Mark r.1)
  | 0, _, st, h => by
    clear hD
    at_cost K hK
    exact .of_val h
  | fuel + 1, i, st, h => by
    have ih := fun h st => cheap_advance hD U fuel h st
    have ihR := fun h st => reach_advance (rd := @rd) (K := K) (hK := hK) (P := P) U fuel h st
    have hrace := fun g (st : StateOf R Rel (Ans D P)) hc g0 hj hg =>
      cheap_askRace (K := K) (hK := hK) (Exp := Exp) (Mark := Mark) U (st := st) hc i g (g0 := g0)
        hj hg
    have hprep := fun t ht => cheap_prepare (rd := @rd) hD h i t ht
    have hprepR := fun t => reach_prepare (rd := @rd) (K := K) (hK := hK) i t st
    have hlev := fun g lv (st : StateOf R Rel (Ans D P)) hc g0 hj hg =>
      cheap_workLevel (rd := @rd) hD _ ih ihR (st := st) hc i g lv (g0 := g0) hj hg
    have hlevR := fun g lv st =>
      reach_workLevel (rd := @rd) (K := K) (hK := hK) (P := P) _ ihR i g lv st
    clear hD
    at_cost K hK
    unfold advance
    split
    · exact .of_val h
    · next t ht =>
      split
      · exact .of_val h
      · split
        · exact .of_val h
        · split
          · exact .of_val h
          · have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
            refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
            refine PaidOr.bind (hprep t ht) fun hp => ?_
            dsimp only
            refine PaidOr.bind'
              (Q := fun acc : StateOf R Rel (Ans D P) × Bool =>
                Cheap Exp Mark acc.1 ∧ goalAt acc.1 i = some t.goal)
              (paidOr_foldL _ _ _ (fun b lv _ hb => ?_) _ ⟨hp.1, (hprepR t).ext _ _ hg⟩) ?_
            · split
              · exact .of_val hb
              · exact (hlev _ lv b.1 hb.1 _ hb.2 hp.2).mono fun hc =>
                  ⟨hc, (hlevR _ lv b.1).ext _ _ hb.2⟩
            · rintro ⟨X, b⟩ hf
              dsimp only at hf ⊢
              refine PaidOr.bind' (Q := fun r => Cheap Exp Mark r.1) (.of_val ?_) ?_
              · refine hrace _ _ (hf.1.modify _ _ (fun _ => rfl) fun t h1 h2 =>
                  ⟨by simp [h1], h2⟩) t.goal ?_ hp.2
                refine Eq.trans ?_ hf.2
                exact goalAt_modify _ i i _ fun _ => rfl
              · rintro ⟨Y, raced⟩ hr
                exact .of_val (hr.modify _ _ (fun _ => rfl) fun t h1 h2 => ⟨h1, h2⟩)

omit [DecidableEq R] in
/-- A change of the tables that keeps the goal, the groups and the answers
of each keeps the state cheap. -/
theorem Cheap.of_map {st st' : StateOf R Rel (Ans D P)} (h : Cheap Exp Mark st)
    (F : Nat → Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hget : ∀ j, st'.tables[j]? = (st.tables[j]?).map (F j)) (he : SameE st st')
    (hF : ∀ j t, (F j t).goal = t.goal ∧ (F j t).groups = t.groups ∧
      (F j t).answers = t.answers) : Cheap Exp Mark st' := by
  refine ⟨h.1.same he, fun j t' ht' hm => ?_⟩
  rw [hget] at ht'
  cases ht : st.tables[j]? with
  | none => rw [ht] at ht'; cases ht'
  | some t =>
    rw [ht] at ht'
    cases ht'
    obtain ⟨e1, e2, e3⟩ := hF j t
    rw [e1] at hm
    rw [e2, e3]
    exact h.2 j t ht hm

/-- **A request keeps the state cheap, or costs `B`.** -/
theorem cheap_request (hD : Dear @rd K hK P Exp Mark B) (U : GOracle R Rel (Ans D P) Cost)
    {st : StateOf R Rel (Ans D P)} (h : Cheap Exp Mark st) :
    PaidOr B (request @rd (K := DerivationKernel.over D K hK P) U st)
      (fun r => Cheap Exp Mark r.1) := by
  have hadv := fun (st : StateOf R Rel (Ans D P)) hc =>
    cheap_advance (rd := @rd) hD U st.tables.length 0 st hc
  clear hD
  at_cost K hK
  unfold request
  refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
  have h0 : Cheap Exp Mark ({ st with round := st.round + 1 } : StateOf R Rel (Ans D P)) := h
  refine PaidOr.bind' (hadv _ h0) ?_
  rintro ⟨X, d⟩ hX
  refine .of_val (hX.of_map _ (fun j => List.getElem?_mapIdx) ⟨rfl, rfl⟩ fun j t => ?_)
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The first state is cheap. -/
theorem cheap_init (root : Rel) :
    Cheap Exp Mark (init (K := DerivationKernel.over D K hK P) root).val := by
  at_cost K hK
  simp only [init, Cost.bind_val, Cost.pure_val]
  refine ⟨⟨fun e he => (by cases he), Nat.le_refl 1⟩, fun i t ht _ => ?_⟩
  obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? ht)
  exact ⟨rfl, rfl⟩


/-- A step of the engine whose root table is not complete spends what its
request spends. -/
theorem step_ticks (U : GOracle R Rel (Ans D P) Cost) (st : StateOf R Rel (Ans D P))
    {t : Table R Rel (Ans D P)} (h : st.tables.head? = some t) (hd : t.done = false) :
    (request @rd (K := DerivationKernel.over D K hK P) U st).ticks ≤
      (step @rd (K := DerivationKernel.over D K hK P) U st).ticks := by
  at_cost K hK
  unfold step
  rw [h]
  dsimp only
  rw [hd]
  simp only [Bool.false_eq_true, ↓reduceIte, Cost.bind_ticks, Cost.pure_ticks]
  omega

end kernel

/-! ## A run -/

section run

variable {U : Unfolder} {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}
  {P : Program} {root : Rel}

variable (hI : IsRun (rd := @rd) (UAt @U dom K hK P) (sAt @U @rd dom K hK P root))
  (hD : Dear @rd (K P.sorts) (hK P.sorts) P Exp Mark B)
include hI hD

/-- **A run is cheap, or has paid `B`.** While the root table is not
complete, the machine has spent `B` ticks or its state is cheap. -/
theorem spent_or_cheap : ∀ (m a : Nat),
    (∀ i < m, (sAt @U @rd dom K hK P root (a + i)).isDone 0 = false) →
    Cheap Exp Mark (sAt @U @rd dom K hK P root a) →
    B ≤ ((engine @U @rd).costedAt dom K hK).spent (stAt @U @rd dom K hK P root a) m ∨
      Cheap Exp Mark (sAt @U @rd dom K hK P root (a + m))
  | 0, a, _, h => .inr h
  | m + 1, a, hlive, h => by
    have h0 := hlive 0 (Nat.succ_pos m)
    rw [Nat.add_zero] at h0
    obtain ⟨l, -, hs⟩ := rt_step_live hI h0
    have hs' : (((engine @U @rd).costedAt dom K hK).step (stAt @U @rd dom K hK P root a)).val =
        .emit (l.map (sp @U @rd dom K hK P)) (stAt @U @rd dom K hK P root (a + 1)) := hs
    rw [CostedRuntime.spent_succ_emit _ hs']
    obtain ⟨t, ht, -⟩ := table_of_goalAt (root_at hI a)
    have hhead : (sAt @U @rd dom K hK P root a).tables.head? = some t := by
      rw [List.head?_eq_getElem?]; exact ht
    have hd : t.done = false := by rw [← isDone_of_table ht]; exact h0
    have hst := step_ticks (rd := @rd) (K := K P.sorts) (hK := hK P.sorts) (UAt @U dom K hK P)
      (sAt @U @rd dom K hK P root a) hhead hd
    have hle : (request @rd (K := DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P)
        (UAt @U dom K hK P) (sAt @U @rd dom K hK P root a)).ticks ≤
        (((engine @U @rd).costedAt dom K hK).step (stAt @U @rd dom K hK P root a)).ticks :=
      Nat.le_trans hst (Nat.le_add_right _ _)
    rcases cheap_request (rd := @rd) hD (UAt @U dom K hK P) h with hp | hc
    · exact .inl (Nat.le_trans (Nat.le_trans hp hle) (Nat.le_add_right _ _))
    · rcases spent_or_cheap m (a + 1) (fun i hi => by
          have := hlive (i + 1) (Nat.succ_lt_succ hi)
          rwa [show a + (i + 1) = a + 1 + i by omega] at this) hc with hp | hc'
      · exact .inl (Nat.le_trans hp (Nat.le_add_left _ _))
      · exact .inr (by rwa [show a + (m + 1) = a + 1 + m by omega])

/-- A run that has come to a state that is not cheap, before its root table
was complete, has paid `B`. -/
theorem spent_of_not_cheap {r n : Nat} (hr : r ≤ n)
    (hlive : ∀ i < r, (sAt @U @rd dom K hK P root i).isDone 0 = false)
    (hn : ¬ Cheap Exp Mark (sAt @U @rd dom K hK P root r)) :
    B ≤ ((engine @U @rd).costedAt dom K hK).spent (stAt @U @rd dom K hK P root 0) n := by
  rcases spent_or_cheap hI hD r 0 (fun i hi => by rw [Nat.zero_add]; exact hlive i hi)
    (cheap_init root) with hp | hc
  · exact Nat.le_trans hp (CostedRuntime.spent_mono _ _ hr)
  · rw [Nat.zero_add] at hc
    exact absurd hc hn

end run

section body

variable {h : Name}

/-- The node is the body of `h`, read in one of the two directions. -/
def BodyNode (P : Program) (h : Name) (n : Rel) : Prop :=
  Charged.bodyOf P (.call h) = some n ∨ Charged.bodyOf P (.conv (.call h)) = some n

/-- A state with a table that holds an answer of the body of `h` is not
cheap, when the bodies of `h` are the marked goals. -/
theorem not_cheap_of_holdsBody {st : StateOf R Rel (Ans D P)} (hG : Good (rd := @rd) st)
    (hb : HoldsBody P h st) : ¬ Cheap Exp (BodyNode P h) st := by
  rintro ⟨-, hT⟩
  obtain ⟨i, t, ht, a, ha, hon, -⟩ := hb
  have hg : a.goal = ⟨t.goal.lb, t.goal.node, t.goal.rb⟩ := (hG.inv.core i t ht).2.2 a ha
  have hm : BodyNode P h t.goal.node := by
    have e : a.goal.node = t.goal.node := by rw [hg]
    rw [← e]; exact hon
  rw [(hT i t ht hm).2] at ha
  cases ha

end body

section covered

variable (rd : EdgeReader) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp) (hRd : GoodReader @rd)
variable {h c : Name} {ξ : Nat → Span} {τ : Nat → GTerm} {Exp : Rel → Bool → Prop} {B : Nat}

include hD hRd in
/-- **A run that has covered a pair the input does not relate where `h`
derives nothing has paid `B`**, when reading a dear edge costs `B` and the
first round of a body of `h` reads one. -/
theorem covered_paid {P : Program} {q : Rel} (wf : P.WellFormed q)
    (hT : Unfold.Tags (orient P q).P c ξ τ)
    (hneed : ∀ s, ¬ Derives ((orient P q).P.withBody c .zero) ((orient P q).P.body h) s)
    (hDear : Dear @rd (K (orient P q).P.sorts) (hK (orient P q).P.sorts) (orient P q).P Exp
      (BodyNode (orient P q).P h) B)
    {y : GTerm × GTerm} (hy : y ∉ (P.withBody h .zero).pairs q) {n : Nat}
    (hc : ((engine Unfold.raced @rd).costedAt dom K hK).oriented.Covered P q P.sorts.interp y n) :
    B ≤ ((engine Unfold.raced @rd).costedAt dom K hK).oriented.paid P q n := by
  obtain ⟨r, hr, hlive, hbody⟩ := covered_body @rd dom K hK hD hRd wf hT hneed hy hc
  have hI := isRun_of_wf (U := Unfold.raced) (rd := @rd) (dom := dom) (K := K) (hK := hK) hD
    good_raced hRd (wf_orient wf)
  rw [(normal_orient_root P q).norm_eq] at hI
  have hs := spent_of_not_cheap hI hDear hr hlive (not_cheap_of_holdsBody (hI.good r) hbody)
  unfold CostedRuntime.paid
  rw [CostedRuntime.oriented_start, CostedRuntime.oriented_spent]
  have hinit := init_eq Unfold.raced @rd dom K hK (orient P q).P (orient P q).root
  rw [(normal_orient_root P q).norm_eq] at hinit
  exact Nat.le_trans hs (Nat.le_trans (Nat.le_of_eq (by rw [← hinit]; rfl)) (Nat.le_add_left _ _))

include hD hRd in
/-- **In a context**: a run on the context's input that has covered a pair
that needs pairs of a call of `h` has paid `B`. -/
theorem covered_paid_ctx {P : Program} (Kc : Context)
    (wf : (Kc.program P).WellFormed (Kc.query (.call h)))
    (hT : Unfold.Tags (orient (Kc.program P) (Kc.query (.call h))).P c ξ τ)
    (hneed : ∀ s, ¬ Derives ((orient (Kc.program P) (Kc.query (.call h))).P.withBody c .zero)
      ((orient (Kc.program P) (Kc.query (.call h))).P.body h) s)
    (hDear : Dear @rd (K (orient (Kc.program P) (Kc.query (.call h))).P.sorts)
      (hK (orient (Kc.program P) (Kc.query (.call h))).P.sorts)
      (orient (Kc.program P) (Kc.query (.call h))).P Exp
      (BodyNode (orient (Kc.program P) (Kc.query (.call h))).P h) B)
    {X : PRel} {y : GTerm × GTerm} (hd : Kc.Demands P (.call h) P.sorts.interp X y) {n : Nat}
    (hc : ((engine Unfold.raced @rd).costedAt dom K hK).oriented.Covered (Kc.program P)
      (Kc.query (.call h)) P.sorts.interp y n) :
    B ≤ ((engine Unfold.raced @rd).costedAt dom K hK).oriented.paid (Kc.program P)
      (Kc.query (.call h)) n :=
  covered_paid @rd dom K hK hD hRd wf hT hneed hDear (not_demands_zero P h Kc hd) hc

end covered

end Symmetric

end RwLog
