/-
# Every answer of a table is an answer of the goal of the table

The invariant of the symmetric engine that says what its tables and its
strategies are for (`Inv`): the node of every goal is a node of the normal
form, a table marked as its own converse is, every answer of a table has the
goal of the table, and every strategy of a table reads tables whose answers
its rule turns into answers of the goal. The work of the strategies keeps
it; the race of a table keeps it when its answers are answers of the goal
(`inv_askRace`), which the specification of a race says of the goals a run
may open, so a round keeps it together with what says that the goals are
such goals (`good_advance`, `Kept.lean`).
-/
import RwLog.Rungs.Symmetric.SelfConverse
import RwLog.Rungs.Symmetric.PushFile
import RwLog.Rungs.Framework.Rules
import RwLog.Kernel.NormalFormSplit

namespace RwLog

namespace Symmetric

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## The goals of the tables -/

/-- The goal of the table at a position. -/
def goalAt {S N A : Type} (st : StateOf S N A) (j : Nat) : Option (GoalOf S N) :=
  st.tables[j]?.map (·.goal)

theorem goalAt_cores {S N A : Type} (st : StateOf S N A) (j : Nat) :
    goalAt st j = st.cores[j]?.map (·.1) := by
  unfold goalAt StateOf.cores
  rw [List.getElem?_map]
  cases st.tables[j]? <;> rfl

theorem lt_of_goalAt {S N A : Type} {st : StateOf S N A} {j : Nat} {g : GoalOf S N}
    (h : goalAt st j = some g) : j < st.tables.length := by
  unfold goalAt at h
  cases ht : st.tables[j]? with
  | none => rw [ht] at h; cases h
  | some t => exact (List.getElem?_eq_some_iff.1 ht).1

/-- Every table of the first state is a table of the second, with its
goal. -/
def Ext {S N A : Type} (st st' : StateOf S N A) : Prop :=
  ∀ j g, goalAt st j = some g → goalAt st' j = some g

theorem goalAt_modify {S N A : Type} (st : StateOf S N A) (i j : Nat)
    (f : Table S N A → Table S N A) (hf : ∀ t, (f t).goal = t.goal) :
    goalAt (st.modify i f) j = goalAt st j := by
  unfold goalAt StateOf.modify
  simp only [List.getElem?_modify]
  split
  · cases st.tables[j]? with
    | none => rfl
    | some t => exact congrArg some (hf t)
  · cases st.tables[j]? <;> rfl

theorem ext_modify {S N A : Type} (st : StateOf S N A) (i : Nat)
    (f : Table S N A → Table S N A) (hf : ∀ t, (f t).goal = t.goal) : Ext st (st.modify i f) :=
  fun j g h => by rw [goalAt_modify st i j f hf]; exact h

section

variable {K : Kernel R Cost} {hK : K.Refines D}

theorem Reach.ext {st st' : StateOf R Rel (Ans D P)} (h : Reach K hK st st') : Ext st st' := by
  induction h with
  | refl => exact fun _ _ h => h
  | trans _ _ a b => exact fun j g h => b j g (a j g h)
  | same e _ =>
    intro j g h
    rw [goalAt_cores] at h ⊢
    rw [e]; exact h
  | opened g' self e _ =>
    intro j g h
    have hlt := lt_of_goalAt h
    rw [goalAt_cores] at h ⊢
    rw [e, List.getElem?_append_left (by simpa [StateOf.cores] using hlt)]
    exact h
  | add st i a =>
    intro j g h
    rw [addAnswer_val]
    split
    · exact h
    · split
      · split
        · exact ext_modify _ _ (app _) (fun _ => rfl) j g h
        · exact ext_modify _ _ (app _) (fun _ => rfl) j g (ext_modify _ _ (app _) (fun _ => rfl) j g h)
      · exact ext_modify _ _ (app _) (fun _ => rfl) j g h

end

/-! ## What a strategy is for -/

/-- The goal is its own converse. -/
def SelfG (g : GoalOf R Rel) : Prop := g.node.normConv = g.node ∧ g.lb = g.rb

/-- The answer is an answer of the goal. -/
def GoalIs (g : GoalOf R Rel) (a : Ans D P) : Prop := a.goal = ⟨g.lb, g.node, g.rb⟩

/-- The goals of the two sides of a split of the goal `g`. -/
def SplitOk (g ga gb : GoalOf R Rel) : Kind → Prop
  | .seq => ga.lb = g.lb ∧ gb.rb = g.rb ∧ comb .seq ga.node gb.node = g.node
  | .and => ga.lb = g.lb ∧ ga.rb = g.rb ∧ comb .and ga.node gb.node = g.node

/-- The goal `gs` of the side whose answers are pushed into the node
`other`, in a split of the goal `g`. -/
def PushOk (g gs : GoalOf R Rel) (other : Rel) : Kind → Bool → Prop
  | .seq, true => gs.lb = g.lb ∧ comb .seq gs.node other = g.node
  | .seq, false => gs.rb = g.rb ∧ comb .seq other gs.node = g.node
  | .and, _ => gs.lb = g.lb ∧ gs.rb = g.rb ∧ comb .and gs.node other = g.node

/-- The goal opened for an answer that is pushed. -/
def pushG (D : Domain R) (g : GoalOf R Rel) (other : Rel) : Kind → Bool → Ans D P → GoalOf R Rel
  | .seq, true, x => ⟨D.rightBound x.span, other, g.rb⟩
  | .seq, false, x => ⟨g.lb, other, D.leftBound x.span⟩
  | .and, _, x => ⟨D.leftBound x.span, other, D.rightBound x.span⟩

/-- The strategy of a table of the goal `g` reads tables whose answers its
rule turns into answers of `g`. -/
def StratOk (st : StateOf R Rel (Ans D P)) (g : GoalOf R Rel) : Strat Rel (Ans D P) → Prop
  | .span _ => True
  | .copy _ subs => ∀ p ∈ subs.map Prod.fst, ∃ h, goalAt st p = some h ∧ h.lb = g.lb ∧ h.rb = g.rb
  | .join k a b _ => ∃ ga gb, goalAt st a = some ga ∧ goalAt st b = some gb ∧ SplitOk g ga gb k
  | .push k left side other subs _ _ _ =>
    ∃ gs, goalAt st side = some gs ∧ PushOk g gs other k left ∧ Normal other ∧
      ∀ e ∈ subs, GoalIs gs e.1 ∧
        ∀ t, e.2 = some t → goalAt st t.1 = some (pushG D g other k left e.1)
  | .check _ _ other _ => Normal other

omit [DecidableEq R] in
theorem StratOk.mono {st st' : StateOf R Rel (Ans D P)} (h : Ext st st') {g : GoalOf R Rel}
    {s : Strat Rel (Ans D P)} (hs : StratOk st g s) : StratOk st' g s := by
  cases s with
  | span _ => trivial
  | copy _ subs =>
    intro p hp
    obtain ⟨x, hx, hl⟩ := hs p hp
    exact ⟨x, h _ _ hx, hl⟩
  | join k a b _ =>
    obtain ⟨ga, gb, ha, hb, hk⟩ := hs
    exact ⟨ga, gb, h _ _ ha, h _ _ hb, hk⟩
  | push k left side other subs dead reads c =>
    obtain ⟨gs, h1, h2, h3, h5⟩ := hs
    exact ⟨gs, h _ _ h1, h2, h3, fun e he => ⟨(h5 e he).1, fun t ht => h _ _ ((h5 e he).2 t ht)⟩⟩
  | check _ _ _ _ => exact hs

/-- The invariant: the goals are goals of the normal form, a table marked as
its own converse is, every answer of a table has the goal of the table, and
every strategy fits its goal. -/
structure Inv (st : StateOf R Rel (Ans D P)) : Prop where
  core : ∀ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t →
    Normal t.goal.node ∧ (t.self = true → SelfG t.goal) ∧ ∀ a ∈ t.answers, GoalIs t.goal a
  strat : ∀ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t →
    ∀ gs, t.groups = some gs → ∀ gr ∈ gs,
    ∀ s ∈ gr.strats, StratOk st t.goal s

omit [DecidableEq R] in
/-- Changing one table keeps the invariant, if its goal and its mark stay,
its answers are answers of its goal, and its strategies fit. -/
theorem Inv.modify {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hgoal : ∀ t, (f t).goal = t.goal)
    (hself : ∀ t, (f t).self = t.self)
    (hans : ∀ t, st.tables[i]? = some t → ∀ a ∈ (f t).answers, GoalIs t.goal a)
    (hg : ∀ t, st.tables[i]? = some t → ∀ gs, (f t).groups = some gs → ∀ gr ∈ gs,
      ∀ s ∈ gr.strats, StratOk st t.goal s) : Inv (st.modify i f) := by
  have hE := ext_modify st i f hgoal
  have key : ∀ j t', (st.modify i f).tables[j]? = some t' →
      (j ≠ i ∧ st.tables[j]? = some t') ∨ (j = i ∧ ∃ t, st.tables[i]? = some t ∧ t' = f t) := by
    intro j t' h
    unfold StateOf.modify at h
    simp only [List.getElem?_modify] at h
    split at h
    · next e =>
      subst e
      cases ht : st.tables[i]? with
      | none => rw [ht] at h; cases h
      | some t => rw [ht] at h; cases h; exact .inr ⟨rfl, t, rfl, rfl⟩
    · next e => exact .inl ⟨fun e' => e e'.symm, by rwa [id_map'] at h⟩
  constructor
  · intro j t' h
    rcases key j t' h with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
    · exact hI.core j t' h
    · obtain ⟨h1, h2, -⟩ := hI.core _ t ht
      rw [hgoal, hself]
      exact ⟨h1, h2, hans t ht⟩
  · intro j t' h gs hgs gr hgr s hs
    rcases key j t' h with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
    · exact (hI.strat j t' h gs hgs gr hgr s hs).mono hE
    · rw [hgoal]
      exact (hg t ht gs hgs gr hgr s hs).mono hE

/-! ## What the machine computes -/

section kernel

variable (K : Kernel R Cost) (hK : K.Refines D)

theorem same_iff (g h : GoalOf R Rel) :
    (same (K := DerivationKernel.over D K hK P) g h).val = true ↔ g = h := by
  rw [same_val]; exact decide_eq_true_iff

theorem selfConverse_spec (g : GoalOf R Rel)
    (h : (selfConverse (K := DerivationKernel.over D K hK P) g).val = true) : SelfG g := by
  have hb := sameBound_val (P := P) K hK g.lb g.rb
  at_cost K hK
  simp only [selfConverse, Cost.bind_val, over_eqNode, over_convNode, Charged.eqNode,
    Charged.convNode, Charged.op] at *
  by_cases e : g.node.normConv = g.node <;> simp_all [SelfG]

theorem indexFrom_some (g : GoalOf R Rel) (ts : List (Table R Rel (Ans D P))) (k i : Nat) :
    (indexFrom (K := DerivationKernel.over D K hK P) (·.goal) g k ts).val = some i →
      k ≤ i ∧ ∃ t, ts[i - k]? = some t ∧ t.goal = g := by
  have hs := fun t : Table R Rel (Ans D P) => same_iff (P := P) K hK t.goal g
  at_cost K hK
  induction ts generalizing k with
  | nil => intro h; cases h
  | cons t ts ih =>
    intro h
    simp only [indexFrom, Cost.bind_val] at h
    split at h
    · next e =>
      cases h
      exact ⟨Nat.le_refl _, t, by simp, (hs t).1 e⟩
    · obtain ⟨hk, t', ht', hg⟩ := ih (k + 1) h
      refine ⟨by omega, t', ?_, hg⟩
      have : i - k = (i - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact ht'

theorem pushGoal_val (g : GoalOf R Rel) (other : Rel) (k : Kind) (left : Bool) (x : Ans D P) :
    (pushGoal (K := DerivationKernel.over D K hK P) g other k left x).val =
      pushG D g other k left x := by
  at_cost K hK
  have hr := hK.rightBound
  have hl := hK.leftBound
  cases k <;> cases left <;> unfold pushGoal pushG <;> dsimp only <;>
    simp only [← hr, ← hl] <;> rfl

variable {K hK}

/-- Opening a goal of the normal form keeps the invariant, and the position
returned is the table of that goal. -/
theorem inv_openGoal {st : StateOf R Rel (Ans D P)} (hI : Inv st) (g : GoalOf R Rel)
    (hn : Normal g.node) :
    Inv (openGoal (K := DerivationKernel.over D K hK P) st g).val.1 ∧
      goalAt (openGoal (K := DerivationKernel.over D K hK P) st g).val.1
        (openGoal (K := DerivationKernel.over D K hK P) st g).val.2 = some g := by
  have hidx := indexFrom_some (P := P) K hK g st.tables 0
  have hself := selfConverse_spec (P := P) K hK g
  at_cost K hK
  simp only [openGoal, Cost.bind_val]
  split
  · next i hi =>
    obtain ⟨-, t, ht, hg⟩ := hidx i hi
    refine ⟨hI, ?_⟩
    simp only [Cost.pure_val]
    unfold goalAt
    rw [Nat.sub_zero] at ht
    rw [ht]; exact congrArg some hg
  · show Inv ({ st with tables := st.tables ++
        [⟨g, (selfConverse (K := DerivationKernel.over D _ hK P) g).val, [], false, none,
          st.round, 0, 0, none, 0, 0, 0, []⟩] } : StateOf R Rel (Ans D P)) ∧
      goalAt ({ st with tables := st.tables ++
        [⟨g, (selfConverse (K := DerivationKernel.over D _ hK P) g).val, [], false, none,
          st.round, 0, 0, none, 0, 0, 0, []⟩] } : StateOf R Rel (Ans D P)) st.tables.length = some g
    have hE : Ext st { st with tables := st.tables ++
        [⟨g, (selfConverse (K := DerivationKernel.over D _ hK P) g).val, [], false, none,
          st.round, 0, 0, none, 0, 0, 0, []⟩] } := by
      intro j g' h
      have hlt := lt_of_goalAt h
      unfold goalAt at h ⊢
      simp only
      rw [List.getElem?_append_left hlt]; exact h
    have key : ∀ (j : Nat) (t' : Table R Rel (Ans D P)), (st.tables ++
        [(⟨g, (selfConverse (K := DerivationKernel.over D _ hK P) g).val, [], false, none,
          st.round, 0, 0, none, 0, 0, 0, []⟩ : Table R Rel (Ans D P))])[j]? = some t' →
        st.tables[j]? = some t' ∨
          t' = ⟨g, (selfConverse (K := DerivationKernel.over D _ hK P) g).val, [], false, none,
            st.round, 0, 0, none, 0, 0, 0, []⟩ := by
      intro j t' h
      rcases Nat.lt_or_ge j st.tables.length with hlt | hge
      · rw [List.getElem?_append_left hlt] at h; exact .inl h
      · rw [List.getElem?_append_right hge] at h
        exact .inr (List.mem_singleton.1 (List.mem_of_getElem? h))
    refine ⟨⟨fun j t' h => ?_, fun j t' h gs hgs gr hgr s hs => ?_⟩, ?_⟩
    · rcases key j t' h with h | rfl
      · exact hI.core j t' h
      · exact ⟨hn, hself, fun a ha => by cases ha⟩
    · rcases key j t' h with h | rfl
      · exact (hI.strat j t' h gs hgs gr hgr s hs).mono hE
      · cases hgs
    · unfold goalAt
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Option.map_some]

/-- Putting an answer of the goal of a table into the table keeps the
invariant. -/
theorem inv_addAnswer {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat) (a : Ans D P)
    (ha : ∀ g, goalAt st i = some g → GoalIs g a) :
    Inv (addAnswer (K := DerivationKernel.over D K hK P) i st a).val := by
  rw [addAnswer_val]
  have h1 : Inv (st.modify i (app [a])) :=
    hI.modify i _ (fun _ => rfl) (fun _ => rfl) (fun t ht x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact (hI.core i t ht).2.2 x hx
      · obtain rfl := List.mem_singleton.1 hx
        exact ha _ (by unfold goalAt; rw [ht]; rfl))
      (fun t ht gs hgs => hI.strat i t ht gs hgs)
  split
  · exact hI
  · split
    · rename_i hself
      split
      · exact h1
      · refine h1.modify i _ (fun _ => rfl) (fun _ => rfl) (fun t ht x hx => ?_)
          (fun t ht gs hgs => h1.strat i t ht gs hgs)
        rcases List.mem_append.1 hx with hx | hx
        · exact (h1.core i t ht).2.2 x hx
        · obtain rfl := List.mem_singleton.1 hx
          have hs : t.self = true := by
            unfold StateOf.isSelf at hself; rw [ht] at hself; exact hself
          obtain ⟨hn, hb⟩ := (h1.core i t ht).2.1 hs
          have hga : GoalIs t.goal a := ha t.goal (by
            rw [← goalAt_modify st i i (app [a]) (fun _ => rfl)]
            unfold goalAt; rw [ht]; rfl)
          unfold GoalIs at hga ⊢
          show (⟨a.goal.rb, a.goal.node.normConv, a.goal.lb⟩ : Goal R) = _
          rw [hga]
          simp only
          rw [hn, hb]
    · exact h1

theorem inv_addOption {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat)
    (a : Option (Ans D P)) (ha : ∀ c, a = some c → ∀ g, goalAt st i = some g → GoalIs g c) :
    Inv (addOption (K := DerivationKernel.over D K hK P) i st a).val := by
  cases a with
  | none => at_cost K hK; exact hI
  | some c =>
    have := inv_addAnswer (K := K) (hK := hK) hI i c (ha c rfl)
    at_cost K hK
    exact this

/-- The answer of the rule of a split is an answer of the goal that was
split. -/
theorem both_goal {k : Kind} {x y c : Ans D P} {g ga gb : GoalOf R Rel}
    (h : (both (K := DerivationKernel.over D K hK P) k x y).val = some c) (hx : GoalIs ga x)
    (hy : GoalIs gb y) (hk : SplitOk g ga gb k) : GoalIs g c := by
  unfold GoalIs at *
  cases k with
  | seq =>
    obtain ⟨-, -, hg⟩ := (Ans.join_val K hK).1 h
    obtain ⟨h1, h2, h3⟩ := hk
    simp only [comb] at h3
    rw [hg, hx, hy]
    simp only
    rw [h1, h2, h3]
  | and =>
    obtain ⟨-, -, hg⟩ := (Ans.meetA_val K hK).1 h
    obtain ⟨h1, h2, h3⟩ := hk
    simp only [comb] at h3
    rw [hg, hx, hy]
    simp only
    rw [h1, h2, h3]

/-- The answer made of an answer that was pushed and an answer of the goal
opened for it is an answer of the goal that was split. -/
theorem pushed_goal {k : Kind} {left : Bool} {x y c : Ans D P} {g gs : GoalOf R Rel}
    {other : Rel} (h : (pushed (K := DerivationKernel.over D K hK P) k left x y).val = some c)
    (hx : GoalIs gs x) (hy : GoalIs (pushG D g other k left x) y)
    (hk : PushOk g gs other k left) : GoalIs g c := by
  unfold GoalIs at *
  cases k with
  | seq =>
    cases left with
    | true =>
      obtain ⟨-, -, hg⟩ := (Ans.join_val K hK).1 h
      obtain ⟨h1, h3⟩ := hk
      simp only [comb] at h3
      rw [hg, hx, hy]
      simp only [pushG]
      rw [h1, h3]
    | false =>
      obtain ⟨-, -, hg⟩ := (Ans.join_val K hK).1 h
      obtain ⟨h1, h3⟩ := hk
      simp only [comb] at h3
      rw [hg, hx, hy]
      simp only [pushG]
      rw [h1, h3]
  | and =>
    obtain ⟨-, -, hg⟩ := (Ans.meetA_val K hK).1 h
    obtain ⟨h1, h2, h3⟩ := hk
    simp only [comb] at h3
    rw [hg, hx, hy]
    simp only [pushG]
    rw [h1, h2, h3]

/-! ## The work of the strategies -/

theorem inv_copyFrom {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat) (g : GoalOf R Rel)
    (isCall : Bool) (m : Nat) (as : List (Ans D P)) (hg : goalAt st i = some g)
    (has : ∀ a ∈ as, a.goal.lb = g.lb ∧ a.goal.rb = g.rb) :
    Inv (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val := by
  at_cost K hK
  refine (foldL_inv (fun b : StateOf R Rel (Ans D P) => Inv b ∧ goalAt b i = some g) _ as
    (fun b a ha hb => ?_) st ⟨hI, hg⟩).1
  dsimp only
  split
  · rw [Cost.bind_val]
    refine ⟨inv_addOption hb.1 i _ (fun c hc g' hg' => ?_), (reach_addOption _ _ _).ext _ _ hb.2⟩
    obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hb.2)
    obtain ⟨-, -, e⟩ := Ans.unfold_val.1 hc
    unfold GoalIs; rw [e, (has a ha).1, (has a ha).2]
  · rw [Cost.bind_val]
    refine ⟨inv_addOption hb.1 i _ (fun c hc g' hg' => ?_), (reach_addOption _ _ _).ext _ _ hb.2⟩
    obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hb.2)
    obtain ⟨-, -, e⟩ := Ans.inj_val.1 hc
    unfold GoalIs; rw [e, (has a ha).1, (has a ha).2]

theorem inv_joinPairs {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat) (k : Kind)
    (xs ys : List (Ans D P)) (ps : List (Nat × Nat)) {g ga gb : GoalOf R Rel}
    (hg : goalAt st i = some g) (hx : ∀ x ∈ xs, GoalIs ga x) (hy : ∀ y ∈ ys, GoalIs gb y)
    (hk : SplitOk g ga gb k) :
    Inv (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val := by
  at_cost K hK
  refine (foldL_inv (fun b : StateOf R Rel (Ans D P) => Inv b ∧ goalAt b i = some g) _ ps
    (fun b p _ hb => ?_) st ⟨hI, hg⟩).1
  split
  · next x y ex ey =>
    rw [Cost.bind_val]
    refine ⟨inv_addOption hb.1 i _ (fun c hc g' hg' => ?_), (reach_addOption _ _ _).ext _ _ hb.2⟩
    obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hb.2)
    exact both_goal hc (hx x (List.mem_of_getElem? ex)) (hy y (List.mem_of_getElem? ey)) hk
  · exact hb

omit [DecidableEq R] in
theorem pushG_node (g : GoalOf R Rel) (other : Rel) (k : Kind) (left : Bool) (x : Ans D P) :
    (pushG D g other k left x).node = other := by
  cases k <;> cases left <;> rfl

theorem inv_pushOpen {st : StateOf R Rel (Ans D P)} (hI : Inv st) (g : GoalOf R Rel)
    (other : Rel) (k : Kind) (left : Bool) (xs : List (Ans D P)) (hn : Normal other) :
    Inv (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1 ∧
      ∀ e ∈ (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.2,
        e.1 ∈ xs ∧ goalAt (pushOpen (K := DerivationKernel.over D K hK P) g other k left st
          xs).val.1 e.2.1 = some (pushG D g other k left e.1) := by
  have hp := pushGoal_val (P := P) K hK g other k left
  at_cost K hK
  refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Ans D P × Nat × Nat) =>
    Inv acc.1 ∧ ∀ e ∈ acc.2, e.1 ∈ xs ∧ goalAt acc.1 e.2.1 = some (pushG D g other k left e.1))
    _ xs (fun b x hx hb => ?_) (st, []) ⟨hI, fun e he => by cases he⟩
  simp only [Cost.bind_val, Cost.pure_val, hp]
  obtain ⟨h1, h2⟩ := inv_openGoal (K := _) (hK := hK) hb.1 (pushG D g other k left x)
    (by rw [pushG_node]; exact hn)
  refine ⟨h1, fun e he => ?_⟩
  rcases List.mem_append.1 he with he | he
  · exact ⟨(hb.2 e he).1, (reach_openGoal _ _).ext _ _ (hb.2 e he).2⟩
  · obtain rfl := List.mem_singleton.1 he
    exact ⟨hx, h2⟩

theorem inv_pushTake {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat) (k : Kind)
    (left : Bool) (x : Ans D P) (ys : List (Ans D P)) {g gs : GoalOf R Rel} {other : Rel}
    (hg : goalAt st i = some g) (hx : GoalIs gs x)
    (hy : ∀ y ∈ ys, GoalIs (pushG D g other k left x) y) (hk : PushOk g gs other k left) :
    Inv (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val := by
  at_cost K hK
  refine (foldL_inv (fun b : StateOf R Rel (Ans D P) => Inv b ∧ goalAt b i = some g) _ ys
    (fun b y hy' hb => ?_) st ⟨hI, hg⟩).1
  simp only [Cost.bind_val]
  refine ⟨inv_addOption hb.1 i _ (fun c hc g' hg' => ?_), (reach_addOption _ _ _).ext _ _ hb.2⟩
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hb.2)
  exact pushed_goal hc hx (hy y hy') hk

/-! ## The strategies of a goal -/

/-- The goals of the two sides of a split of `g`, as its group needs
them. -/
def SplitGoals (g L Rg : GoalOf R Rel) : Kind → Prop
  | .seq => L.lb = g.lb ∧ Rg.rb = g.rb ∧ comb .seq L.node Rg.node = g.node
  | .and => L.lb = g.lb ∧ L.rb = g.rb ∧ Rg.lb = g.lb ∧ Rg.rb = g.rb ∧
      comb .and L.node Rg.node = g.node ∧ comb .and Rg.node L.node = g.node

theorem inv_splitGroup {st : StateOf R Rel (Ans D P)} (hI : Inv st) (k : Kind)
    (L Rg g : GoalOf R Rel) (hL : Normal L.node) (hR : Normal Rg.node)
    (hk : SplitGoals g L Rg k) :
    Inv (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 ∧
      ∀ s ∈ (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.2.strats,
        StratOk (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 g s := by
  obtain ⟨hI1, hg1⟩ := inv_openGoal (K := K) (hK := hK) hI L hL
  obtain ⟨hI2, hg2⟩ := inv_openGoal (K := K) (hK := hK) hI1 Rg hR
  have hg1' := (reach_openGoal (K := K) (hK := hK) _ Rg).ext _ _ hg1
  at_cost K hK
  simp only [splitGroup, Cost.bind_val, Cost.pure_val]
  refine ⟨hI2, fun s hs => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · refine ⟨L, Rg, hg1', hg2, ?_⟩
    cases k
    · exact ⟨hk.1, hk.2.1, hk.2.2⟩
    · exact ⟨hk.1, hk.2.1, hk.2.2.2.2.1⟩
  · refine ⟨L, hg1', ?_, hR, fun e he => by cases he⟩
    cases k
    · exact ⟨hk.1, hk.2.2⟩
    · exact ⟨hk.1, hk.2.1, hk.2.2.2.2.1⟩
  · refine ⟨Rg, hg2, ?_, hL, fun e he => by cases he⟩
    cases k
    · exact ⟨hk.2.1, hk.2.2⟩
    · exact ⟨hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.2⟩

omit [Answer R] [DecidableEq R] in
theorem normal_bodyOf {n b : Rel} (h : Charged.bodyOf P n = some b) : Normal b := by
  unfold Charged.bodyOf at h
  split at h
  · cases h; exact normal_norm _
  · cases h; exact normal_normConv _
  · cases h

omit [Answer R] [DecidableEq R] in
/-- The two sides of a split of a chain, as the kernel returns them, join to
the chain. -/
theorem chain_split_of {e l r : Rel} {xs : List Rel} {i : Nat} (hn : Normal e)
    (hv : e.view = .chain xs) (hl : e.interval 0 i = some l)
    (hr : e.interval i xs.length = some r) : mkSeq (seqParts l ++ seqParts r) = e := by
  obtain ⟨h2, hmem, hmk⟩ := hn.view_chain hv
  have hne : xs ≠ [] := by intro h; rw [h] at h2; simp at h2
  have hparts : seqParts e = xs := by
    rw [← hmk]; exact seqParts_mkSeq hne fun x hx => (hmem x hx).2
  have h0 : 0 < i := by
    unfold RelOf.interval at hl
    split at hl
    · rename_i c; exact c.1
    · cases hl
  have hi : i < xs.length := by
    unfold RelOf.interval at hr
    split at hr
    · rename_i c; exact c.1
    · cases hr
  obtain ⟨-, l', r', hl', hr', e', -, -⟩ := hn.chain_split hv h0 hi
  rw [hl] at hl'; rw [hr] at hr'
  cases hl'; cases hr'
  exact e'

omit [Answer R] [DecidableEq R] in
/-- A member of a meet and the meet of the others, as the kernel returns
them, meet to the meet, in either order. -/
theorem meet_split_of {e l r : Rel} {xs : List Rel} {i : Nat} (hn : Normal e)
    (hv : e.view = .meet xs) (hl : xs[i]? = some l) (hr : e.without i = some r) :
    mkAnd (sortedParts (andParts l ++ andParts r)) = e ∧
      mkAnd (sortedParts (andParts r ++ andParts l)) = e := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.1 hl).1
  obtain ⟨-, l', r', hl', hr', e1, e2, -, -⟩ := hn.meet_split hv hi
  rw [hl] at hl'; rw [hr] at hr'
  cases hl'; cases hr'
  exact ⟨e1, e2⟩

omit [DecidableEq R] in
/-- A change of the state that leaves its tables alone keeps the
invariant. -/
theorem Inv.of_tables {st st' : StateOf R Rel (Ans D P)} (hI : Inv st)
    (h : st'.tables = st.tables) : Inv st' := by
  have hE : Ext st st' := fun j g hg => by
    unfold goalAt at hg ⊢
    rw [h]; exact hg
  exact ⟨fun i t ht => hI.core i t (h ▸ ht), fun i t ht gs hgs gr hgr s hs =>
    (hI.strat i t (h ▸ ht) gs hgs gr hgr s hs).mono hE⟩

theorem inv_edgeOf {st : StateOf R Rel (Ans D P)} (hI : Inv st) (last : Bool) (n : Rel) :
    Inv (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1 := by
  at_cost K hK
  simp only [edgeOf, Cost.bind_val]
  split
  · exact hI
  · simp only [Cost.bind_val, Cost.pure_val]
    split
    · exact hI.of_tables rfl
    · exact hI.of_tables rfl

theorem inv_checkOf {st : StateOf R Rel (Ans D P)} (hI : Inv st) (left : Bool)
    (side other : Rel) (g : GoalOf R Rel) (hn : Normal other) :
    Inv (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.1 ∧
      ∀ s ∈ (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.2,
        ∀ st' : StateOf R Rel (Ans D P), StratOk st' g s := by
  have h := inv_edgeOf (K := K) (hK := hK) hI left side
  at_cost K hK
  simp only [checkOf, Cost.bind_val, Cost.pure_val]
  refine ⟨h, fun s hs st' => ?_⟩
  split at hs
  · cases hs
  · obtain rfl := List.mem_singleton.1 hs
    exact hn

/-- Making the groups of a chain goal keeps the invariant, and they fit the
goal. -/
theorem inv_chainGroups {st : StateOf R Rel (Ans D P)} (hI : Inv st) (g : GoalOf R Rel)
    (hn : Normal g.node) {xs : List Rel} (hvc : g.node.view = .chain xs) :
    Inv (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.1 ∧
      (∀ gr ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1,
        ∀ s ∈ gr.strats,
          StratOk (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.1 g s) ∧
      ∀ s ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.2,
        StratOk (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.1 g s := by
  at_cost K hK
  refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) ×
      List (Strat Rel (Ans D P)) =>
    Inv acc.1 ∧ (∀ gr ∈ acc.2.1, ∀ s ∈ gr.strats, StratOk acc.1 g s) ∧
      ∀ s ∈ acc.2.2, StratOk acc.1 g s) _ _ (fun b i _ hb => ?_)
    (st, [], []) ⟨hI, (fun gr hgr => by cases hgr), fun s hs => by cases hs⟩
  simp only [Cost.bind_val]
  split
  · next l r hl hr =>
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨h1, h2⟩ := inv_splitGroup (K := _) (hK := hK) hb.1 .seq ⟨g.lb, l, none⟩
      ⟨none, r, g.rb⟩ g (hn.interval hl) (hn.interval hr)
      ⟨rfl, rfl, chain_split_of hn hvc hl hr⟩
    have hE1 := (reach_splitGroup (K := _) (hK := hK) .seq ⟨g.lb, l, none⟩ ⟨none, r, g.rb⟩ b.1).ext
    obtain ⟨h3, h4⟩ := inv_checkOf (K := _) (hK := hK) h1 true l r g (hn.interval hr)
    have hE2 := (reach_checkOf (K := _) (hK := hK) (P := P) (splitGroup
      (K := DerivationKernel.over D _ hK P) .seq ⟨g.lb, l, none⟩ ⟨none, r, g.rb⟩ b.1).val.1
      true l r).ext
    obtain ⟨h5, h6⟩ := inv_checkOf (K := _) (hK := hK) h3 false r l g (hn.interval hl)
    have hE3 := (reach_checkOf (K := _) (hK := hK) (P := P) (checkOf
      (K := DerivationKernel.over D _ hK P) (splitGroup
        (K := DerivationKernel.over D _ hK P) .seq ⟨g.lb, l, none⟩ ⟨none, r, g.rb⟩ b.1).val.1
      true l r).val.1 false r l).ext
    refine ⟨h5, fun gr hgr s hs => ?_, fun s hs => ?_⟩
    · rcases List.mem_append.1 hgr with hgr | hgr
      · exact (hb.2.1 gr hgr s hs).mono fun j g' h => hE3 _ _ (hE2 _ _ (hE1 _ _ h))
      · obtain rfl := List.mem_singleton.1 hgr
        exact (h2 s hs).mono fun j g' h => hE3 _ _ (hE2 _ _ h)
    · rcases List.mem_append.1 hs with hs | hs
      · rcases List.mem_append.1 hs with hs | hs
        · exact (hb.2.2 s hs).mono fun j g' h => hE3 _ _ (hE2 _ _ (hE1 _ _ h))
        · exact h4 s hs _
      · exact h6 s hs _
  · exact hb

/-- Making the strategies of a goal keeps the invariant, and they fit the
goal. -/
theorem inv_expand {st : StateOf R Rel (Ans D P)} (hI : Inv st) (g : GoalOf R Rel)
    (hn : Normal g.node) :
    Inv (expand (K := DerivationKernel.over D K hK P) g st).val.1 ∧
      ∀ gr ∈ (expand (K := DerivationKernel.over D K hK P) g st).val.2, ∀ s ∈ gr.strats,
        StratOk (expand (K := DerivationKernel.over D K hK P) g st).val.1 g s := by
  at_cost K hK
  simp only [expand, Cost.bind_val]
  split
  · refine ⟨hI, fun gr hgr s hs => ?_⟩
    obtain rfl := List.mem_singleton.1 hgr
    obtain rfl := List.mem_singleton.1 hs
    trivial
  · simp only [Cost.bind_val]
    split
    · refine ⟨hI, fun gr hgr s hs => ?_⟩
      obtain rfl := List.mem_singleton.1 hgr
      obtain rfl := List.mem_singleton.1 hs
      intro p hp; cases hp
    · next b hb =>
      simp only [Cost.bind_val, Cost.pure_val]
      obtain ⟨h1, h2⟩ := inv_openGoal (K := _) (hK := hK) hI ⟨g.lb, b, g.rb⟩
        (normal_bodyOf (P := P) hb)
      refine ⟨h1, fun gr hgr s hs => ?_⟩
      obtain rfl := List.mem_singleton.1 hgr
      obtain rfl := List.mem_singleton.1 hs
      intro p hp
      obtain rfl := List.mem_singleton.1 hp
      exact ⟨_, h2, rfl, rfl⟩
  · next xs hv =>
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨hmem, -, -⟩ := hn.view_union (forget_union hv)
    have key := foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Nat × Nat) =>
      Inv acc.1 ∧ ∀ p ∈ acc.2.map Prod.fst, ∃ h, goalAt acc.1 p = some h ∧ h.lb = g.lb ∧
        h.rb = g.rb) (fun acc x => do
          let (st, j) ← openGoal (K := DerivationKernel.over D _ hK P) acc.1 ⟨g.lb, x, g.rb⟩
          pure (st, acc.2 ++ [(j, 0)])) xs (fun b x hx hb => by
        simp only [Cost.bind_val, Cost.pure_val]
        obtain ⟨h1, h2⟩ := inv_openGoal (K := _) (hK := hK) hb.1 ⟨g.lb, x, g.rb⟩ (hmem x hx).1
        refine ⟨h1, fun p hp => ?_⟩
        rw [List.map_append] at hp
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨h, e1, e2⟩ := hb.2 p hp
          exact ⟨h, (reach_openGoal _ _).ext _ _ e1, e2⟩
        · obtain rfl := List.mem_singleton.1 hp
          exact ⟨_, h2, rfl, rfl⟩) (st, []) ⟨hI, fun p hp => by cases hp⟩
    refine ⟨key.1, fun gr hgr s hs => ?_⟩
    obtain rfl := List.mem_singleton.1 hgr
    obtain rfl := List.mem_singleton.1 hs
    exact key.2
  · next xs hv =>
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨h1, h2, h3⟩ := inv_chainGroups (K := _) (hK := hK) hI g hn (forget_chain hv)
    refine ⟨h1, fun gr hgr s hs => ?_⟩
    split at hgr
    · exact h2 gr hgr s hs
    · rcases List.mem_append.1 hgr with hgr | hgr
      · exact h2 gr hgr s hs
      · obtain rfl := List.mem_singleton.1 hgr
        exact h3 s hs
  · next xs hv =>
    have hvm := forget_meet hv
    obtain ⟨-, hmem, -, -⟩ := hn.view_meet hvm
    refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) =>
      Inv acc.1 ∧ ∀ gr ∈ acc.2, ∀ s ∈ gr.strats, StratOk acc.1 g s) _ _ (fun b i _ hb => ?_)
      (st, []) ⟨hI, fun gr hgr => by cases hgr⟩
    simp only [Cost.bind_val]
    split
    · next l r hl hr =>
      simp only [Cost.bind_val, Cost.pure_val]
      obtain ⟨e1, e2⟩ := meet_split_of hn hvm hl hr
      obtain ⟨h1, h2⟩ := inv_splitGroup (K := _) (hK := hK) hb.1 .and ⟨g.lb, l, g.rb⟩
        ⟨g.lb, r, g.rb⟩ g (hmem l (List.mem_of_getElem? hl)).1 (hn.without hr)
        ⟨rfl, rfl, rfl, rfl, e1, e2⟩
      refine ⟨h1, fun gr hgr s hs => ?_⟩
      rcases List.mem_append.1 hgr with hgr | hgr
      · exact (hb.2 gr hgr s hs).mono (reach_splitGroup _ _ _ _).ext
      · obtain rfl := List.mem_singleton.1 hgr
        exact h2 s hs
    · exact hb

/-! ## The work of one strategy -/

omit [DecidableEq R] in
theorem Inv.answers {st : StateOf R Rel (Ans D P)} (hI : Inv st) {j : Nat} {h : GoalOf R Rel}
    (hj : goalAt st j = some h) : ∀ a ∈ st.answers j, GoalIs h a := by
  unfold goalAt at hj
  unfold StateOf.answers
  cases ht : st.tables[j]? with
  | none => rw [ht] at hj; cases hj
  | some t =>
    rw [ht] at hj
    cases hj
    exact (hI.core j t ht).2.2

theorem mem_maxima {xs : List (Ans D P)} {x : Ans D P}
    (h : x ∈ (maxima (K := DerivationKernel.over D K hK P) xs).val) : x ∈ xs := by
  rw [maxima_val] at h
  exact List.mem_maximaBy h

theorem inv_checkOpen {st : StateOf R Rel (Ans D P)} (hI : Inv st) (g : GoalOf R Rel)
    (left : Bool) (other : Rel) (ps : List R) (hn : Normal other) :
    Inv (checkOpen (K := DerivationKernel.over D K hK P) g left other st ps).val.1 := by
  at_cost K hK
  refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × List Nat => Inv acc.1) _ ps
    (fun b p _ hb => ?_) (st, []) hI
  simp only [Cost.bind_val, Cost.pure_val]
  refine (inv_openGoal (K := _) (hK := hK) hb _ ?_).1
  split <;> exact hn

omit [DecidableEq R] in
/-- Changing one table keeps the invariant, if its goal, its mark, its
answers and its strategies stay. -/
theorem Inv.modify_same {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hcore : ∀ t, (f t).core = t.core)
    (hgr : ∀ t, (f t).groups = t.groups) : Inv (st.modify i f) := by
  have e : ∀ t, (f t).goal = t.goal ∧ (f t).self = t.self ∧ (f t).answers = t.answers :=
    fun t => by
      have := hcore t
      simp only [Table.core, Prod.mk.injEq] at this
      exact this
  refine hI.modify i f (fun t => (e t).1) (fun t => (e t).2.1) (fun t ht => ?_)
    (fun t ht gs hgs => ?_)
  · rw [(e t).2.2]; exact (hI.core i t ht).2.2
  · rw [hgr] at hgs; exact hI.strat i t ht gs hgs

/-- The work of a strategy that fits its goal keeps the invariant, and the
strategy it leaves fits the goal in any state that extends the state it was
given. -/
theorem inv_work_aux {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat)
    (g : GoalOf R Rel) (s : Strat Rel (Ans D P)) (hg : goalAt st i = some g)
    (hs : StratOk st g s) :
    Inv (work (K := DerivationKernel.over D K hK P) i g st s).val.1 ∧
      (Ext st (work (K := DerivationKernel.over D K hK P) i g st s).val.1 →
        StratOk (work (K := DerivationKernel.over D K hK P) i g st s).val.1 g
          (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1) := by
  at_cost K hK
  cases s with
  | span ran =>
    cases ran
    · simp only [work, Cost.bind_val, Cost.pure_val]
      refine ⟨inv_addOption hI i _ (fun c hc g' hg' => ?_), fun _ => trivial⟩
      obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
      obtain ⟨sp, e, -, -, -, hc'⟩ := (Ans.leaf_val _ hK).1 hc
      unfold GoalIs; rw [hc', e]
    · exact ⟨hI, fun _ => trivial⟩
  | copy isCall subs =>
    have hsub : ∀ p ∈ subs.zipIdx, ∀ a ∈ st.answers p.1.1,
        a.goal.lb = g.lb ∧ a.goal.rb = g.rb := by
      intro p hp a ha
      obtain ⟨h, hj, hl, hr⟩ := hs p.1.1
        (List.mem_map_of_mem (List.fst_mem_of_mem_zipIdx hp))
      have := hI.answers hj a ha
      unfold GoalIs at this
      rw [this]; exact ⟨hl, hr⟩
    simp only [work]
    split
    · exact ⟨hI, fun _ => hs⟩
    · next p hp =>
      simp only [Cost.bind_val, Cost.pure_val]
      refine ⟨(inv_copyFrom hI i g isCall p.2 _ hg (fun a ha =>
        hsub p (mem_of_leastBy hp) a
          (List.mem_of_mem_drop (List.mem_of_mem_take ha)))).modify_same i _ (fun _ => rfl)
            (fun _ => rfl), fun hE => ?_⟩
      refine StratOk.mono hE ?_
      intro q hq
      rw [map_modify_eq Prod.fst (fun q : Nat × Nat => (q.1, q.2 + 1)) (fun _ => rfl)] at hq
      exact hs q hq
  | join k a b c =>
    obtain ⟨ga, gb, ha, hb, hk⟩ := hs
    have hs' : ∀ c', StratOk st g (.join k a b c') := fun _ => ⟨ga, gb, ha, hb, hk⟩
    simp only [work]
    split
    · exact ⟨hI, fun _ => hs' _⟩
    · simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      exact ⟨(inv_joinPairs hI i k _ _ _ hg (hI.answers ha) (hI.answers hb) hk).modify_same i _
        (fun _ => rfl) (fun _ => rfl), fun hE => (hs' _).mono hE⟩
  | push k left side other subs dead reads c =>
    obtain ⟨gs, h1, hk, hno, hsubs⟩ := hs
    simp only [work, Cost.bind_val]
    generalize (supersede (K := DerivationKernel.over D _ hK P) _ _ dead).val = dead'
    have hss := seeSide_subs (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
      reads c
    generalize seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
      reads c = f0 at hss ⊢
    have hfe := pushFile_getElem? st dead' f0.1 0 f0.2.1 (f0.2.2.kill dead')
    generalize pushFile st dead' 0 f0.2.1 (f0.2.2.kill dead') f0.1 = f at hfe ⊢
    have hf : ∀ e ∈ f.1, GoalIs gs e.1 ∧
        ∀ t, e.2 = some t → goalAt st t.1 = some (pushG D g other k left e.1) := by
      intro e he
      obtain ⟨n, hn⟩ := List.getElem?_of_mem he
      rw [hfe] at hn
      cases h0 : f0.1[n]? with
      | none => rw [h0] at hn; cases hn
      | some e0 =>
        rw [h0] at hn
        cases hn
        have hm := List.mem_of_getElem? h0
        rw [hss] at hm
        rcases List.mem_append.1 hm with hm | hm
        · refine ⟨(hsubs e0 hm).1, fun t ht => ?_⟩
          rcases e0 with ⟨x, _ | t0⟩
          · cases ht
          · cases ht
            exact (hsubs _ hm).2 t0 rfl
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
          refine ⟨hI.answers h1 _ (List.of_mem_zip (List.mem_of_mem_drop hy)).1, fun t ht => ?_⟩
          cases ht
    have hok : ∀ c', StratOk st g (.push k left side other f.1 dead' f.2.1 c') := fun _ =>
      ⟨gs, h1, hk, hno, hf⟩
    split
    · exact ⟨hI, fun _ => hok _⟩
    · next p hp =>
      split
      · next x _ hx _ =>
        simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
        obtain ⟨hI1, hnew⟩ := inv_pushOpen (K := _) (hK := hK) hI g other k left [x] hno
        have hE01 := (reach_pushOpen (K := _) (hK := hK) g other k left st [x]).ext
        refine ⟨hI1, fun _ => ⟨gs, hE01 _ _ h1, hk, hno, fun e he => ?_⟩⟩
        rcases List.mem_or_eq_of_mem_set he with he | rfl
        · exact ⟨(hf e he).1, fun t ht => hE01 _ _ ((hf e he).2 t ht)⟩
        · refine ⟨(hf _ (List.mem_of_getElem? hx)).1, fun t ht => ?_⟩
          unfold openedAt at ht
          cases hh : (pushOpen (K := DerivationKernel.over D _ hK P) g other k left st
            [x]).val.2.head? with
          | none => rw [hh] at ht; cases ht
          | some e' =>
            rw [hh] at ht
            cases ht
            obtain ⟨hm, hgo⟩ := hnew e' (List.mem_of_mem_head? hh)
            obtain rfl := List.mem_singleton.1 hm
            exact hgo
      · next x tb _ r hx _ =>
        simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
        have hp' := hf _ (List.mem_of_getElem? hx)
        exact ⟨(inv_pushTake hI i k left x _ hg hp'.1 (fun y hy =>
          hI.answers (hp'.2 tb rfl) y (List.mem_of_mem_drop (List.mem_of_mem_take hy)))
            hk).modify_same i _ (fun _ => rfl) (fun _ => rfl), fun hE => (hok _).mono hE⟩
      · exact ⟨hI, fun _ => hok _⟩
  | check left side other c =>
    have hno : Normal other := hs
    have hI1 := inv_edgeOf (K := _) (hK := hK) hI left side
    have hopen := fun ps => inv_checkOpen (K := _) (hK := hK) hI1 g left other ps hno
    cases c with
    | reading =>
      simp only [work, Cost.bind_val]
      split
      · exact ⟨hI1, fun _ => hno⟩
      · exact ⟨hI1, fun _ => hno⟩
      · simp only [Cost.bind_val, Cost.pure_val]
        exact ⟨hopen _, fun _ => hno⟩
    | off => exact ⟨hI, fun _ => hno⟩
    | opened subs => exact ⟨hI, fun _ => hno⟩

/-- The work of a strategy that fits its goal keeps the invariant, and the
strategy it leaves fits the goal. -/
theorem inv_work {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat)
    (g : GoalOf R Rel) (s : Strat Rel (Ans D P)) (hg : goalAt st i = some g)
    (hs : StratOk st g s) :
    Inv (work (K := DerivationKernel.over D K hK P) i g st s).val.1 ∧
      StratOk (work (K := DerivationKernel.over D K hK P) i g st s).val.1 g
        (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1 :=
  ⟨(inv_work_aux hI i g s hg hs).1,
    (inv_work_aux hI i g s hg hs).2 (reach_work _ _ _ _).ext⟩

/-- A turn of a strategy that fits its goal keeps the invariant, and the
strategy it leaves fits the goal. -/
theorem inv_turn {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat)
    (g : GoalOf R Rel) (f left : Nat) (s : Strat Rel (Ans D P)) (c : Nat)
    (hg : goalAt st i = some g) (hs : StratOk st g s) :
    Inv (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.1 ∧
      StratOk (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.1 g
        (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.2.1 := by
  have h := turn_ind (K := K) (hK := hK) (P := P) i g
    (fun st' s' => Inv st' ∧ goalAt st' i = some g ∧ StratOk st' g s')
    (fun st' s' h => ⟨(inv_work h.1 i g s' h.2.1 h.2.2).1,
      (reach_work (K := K) (hK := hK) i g st' s').ext _ _ h.2.1,
      (inv_work h.1 i g s' h.2.1 h.2.2).2⟩) f left st s c ⟨hI, hg, hs⟩
  exact ⟨h.1, h.2.2⟩

/-! ## A round -/

omit [DecidableEq R] in
omit [DecidableEq R] in
/-- Removing groups of one table keeps the invariant. -/
theorem Inv.dropGroups {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat)
    (p : Group Rel (Ans D P) → Bool) :
    Inv (st.modify i fun t => { t with groups := t.groups.map fun gs => gs.filter p }) := by
  refine hI.modify i _ (fun _ => rfl) (fun _ => rfl) (fun t ht => (hI.core i t ht).2.2)
    (fun t ht gs hgs gr hgr s hs => ?_)
  cases hg : t.groups with
  | none => rw [hg] at hgs; cases hgs
  | some gs' =>
    rw [hg] at hgs
    cases hgs
    exact hI.strat i t ht gs' hg gr (List.mem_of_mem_filter hgr) s hs

omit [DecidableEq R] in
/-- A change of the tables that keeps the goal, the mark, the answers and
the strategies of each keeps the invariant. -/
theorem Inv.of_map {st st' : StateOf R Rel (Ans D P)} (hI : Inv st)
    (F : Nat → Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hget : ∀ j, st'.tables[j]? = (st.tables[j]?).map (F j))
    (hcore : ∀ j t, (F j t).core = t.core) (hgr : ∀ j t, (F j t).groups = t.groups) :
    Inv st' := by
  have hgoal : ∀ j t, (F j t).goal = t.goal := fun j t => congrArg (·.1) (hcore j t)
  have hE : Ext st st' := by
    intro j g h
    unfold goalAt at h ⊢
    rw [hget]
    cases ht : st.tables[j]? with
    | none => rw [ht] at h; cases h
    | some t => rw [ht] at h; cases h; exact congrArg some (hgoal j t)
  have key : ∀ j t', st'.tables[j]? = some t' → ∃ t, st.tables[j]? = some t ∧ t' = F j t := by
    intro j t' h
    rw [hget] at h
    cases ht : st.tables[j]? with
    | none => rw [ht] at h; cases h
    | some t => rw [ht] at h; cases h; exact ⟨t, rfl, rfl⟩
  constructor
  · intro j t' h
    obtain ⟨t, ht, rfl⟩ := key j t' h
    have e := hcore j t
    simp only [Table.core, Prod.mk.injEq] at e
    rw [e.1, e.2.1, e.2.2]
    exact hI.core j t ht
  · intro j t' h gs hgs gr hgr' s hs
    obtain ⟨t, ht, rfl⟩ := key j t' h
    rw [hgoal]
    rw [hgr] at hgs
    exact (hI.strat j t ht gs hgs gr hgr' s hs).mono hE

omit [DecidableEq R] in
/-- Changing a group of a table keeps the invariant if the strategies of the
group still fit. -/
theorem inv_setGroup {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P))
    (hf : ∀ g gr, goalAt st i = some g → (∀ s ∈ gr.strats, StratOk st g s) →
      ∀ s ∈ (f gr).strats, StratOk st g s) : Inv (setGroup st i k f) := by
  refine hI.modify i _ (fun _ => rfl) (fun _ => rfl) (fun t ht => (hI.core i t ht).2.2)
    (fun t ht gs hgs gr hgr s hs => ?_)
  have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
  simp only at hgs
  cases hgs' : t.groups with
  | none => rw [hgs'] at hgs; cases hgs
  | some gs' =>
    rw [hgs'] at hgs
    cases hgs
    rcases mem_modify hgr with hgr | ⟨gr', hgr', rfl⟩
    · exact hI.strat i t ht gs' hgs' gr hgr s hs
    · exact hf t.goal gr' hg (hI.strat i t ht gs' hgs' gr' hgr') s hs

omit [DecidableEq R] in
theorem strat_of_groupsAt {st : StateOf R Rel (Ans D P)} (hI : Inv st) {i k j : Nat}
    {g : GoalOf R Rel} {s : Strat Rel (Ans D P)} (hg : goalAt st i = some g)
    (h : ((groupsAt st i)[k]?).bind (·.strats[j]?) = some s) : StratOk st g s := by
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
        exact hI.strat i t ht gs hgs gr (List.mem_of_getElem? hgr) s (List.mem_of_getElem? h)

theorem inv_workGroup (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Inv st → Inv (adv h st).val.1)
    (hadvR : ∀ h st, Reach K hK st (adv h st).val.1) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (i : Nat) (g : GoalOf R Rel) (k : Nat)
    (hg : goalAt st i = some g) :
    Inv (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1 := by
  have hturn := fun (st : StateOf R Rel (Ans D P)) hI f left s c hg hs =>
    inv_turn (K := K) (hK := hK) (st := st) hI i g f left s c hg hs
  have hrt := fun f left st s c => reach_turn (K := K) (hK := hK) (P := P) i g f left st s c
  have hf := fun X d hX => feedGroup_keeps (K := K) (hK := hK) (P := P) adv
    (fun X => Inv X ∧ goalAt X i = some g)
    (fun h X hX => ⟨hadv h X hX.1, (hadvR h X).ext _ _ hX.2⟩)
    (fun h c X hX => ⟨hX.1.modify_same h _ (fun _ => rfl) (fun _ => rfl),
      (goalAt_modify X h i (fun t => { t with fed := t.fed + c }) fun _ => rfl).trans hX.2⟩)
    i k X d hX
  at_cost K hK
  simp only [workGroup, workStrats, Cost.bind_val, Cost.pure_val]
  refine Inv.modify_same ?_ i _ (fun _ => rfl) (fun _ => rfl)
  refine inv_setGroup ?_ _ _ _ (fun g' gr _ h => h)
  refine (hf _ _ ?_).1
  · refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × Nat × Bool =>
      Inv acc.1 ∧ goalAt acc.1 i = some g) _ _ (fun b j _ hb => ?_) (st, 0, false) ⟨hI, hg⟩
    split
    · exact hb
    · next s o hs =>
      simp only [Cost.bind_val, Cost.pure_val]
      generalize turnTicks * weight b.1 s - o = fl
      obtain ⟨h1, h2⟩ := hturn b.1 hb.1 fl fl s 0 hb.2
        (strat_of_groupsAt hb.1 hb.2 (pick_strat hs).1)
      have hg' := (hrt fl fl b.1 s 0).ext _ _ hb.2
      refine ⟨inv_setGroup h1 _ _ _ (fun g' gr hg'' h s' hs' => ?_), ?_⟩
      · obtain rfl : g' = g := Option.some.inj (hg''.symm.trans hg')
        rcases List.mem_or_eq_of_mem_set hs' with h' | rfl
        · exact h s' h'
        · exact h2
      · unfold setGroup
        exact Eq.trans (goalAt_modify _ i i _ fun _ => rfl) hg'

theorem inv_workLevel (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Inv st → Inv (adv h st).val.1)
    (hadvR : ∀ h st, Reach K hK st (adv h st).val.1) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (i : Nat) (g : GoalOf R Rel) (lv : Nat)
    (hg : goalAt st i = some g) :
    Inv (workLevel (K := DerivationKernel.over D K hK P) adv i g lv st).val.1 := by
  at_cost K hK
  refine (foldL_inv (fun acc : StateOf R Rel (Ans D P) × Bool =>
    Inv acc.1 ∧ goalAt acc.1 i = some g) _ _ (fun b p _ hb => ?_) (st, false) ⟨hI, hg⟩).1
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    exact ⟨inv_workGroup adv hadv hadvR hb.1 _ _ _ hb.2,
      (reach_workGroup adv hadvR _ _ _ _).ext _ _ hb.2⟩
  · exact hb

theorem inv_prepare {st : StateOf R Rel (Ans D P)} (hI : Inv st) (i : Nat)
    (t : Table R Rel (Ans D P)) (ht : st.tables[i]? = some t) :
    Inv (prepare (K := DerivationKernel.over D K hK P) i t st).val := by
  have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
  obtain ⟨h1, h2⟩ := inv_expand (K := K) (hK := hK) hI t.goal (hI.core i t ht).1
  have hE := (reach_expand (K := K) (hK := hK) t.goal st).ext
  at_cost K hK
  unfold prepare
  cases t.groups with
  | some _ =>
    exact hI.modify i _ (fun _ => rfl) (fun _ => rfl) (fun t' ht' => (hI.core i t' ht').2.2)
      (fun t' ht' gs hgs => hI.strat i t' ht' gs hgs)
  | none =>
    simp only [Cost.bind_val, Cost.pure_val]
    refine Inv.modify_same ?_ i _ (fun _ => rfl) (fun _ => rfl)
    refine h1.modify i _ (fun _ => rfl) (fun _ => rfl) (fun t' ht' => (h1.core i t' ht').2.2)
      (fun t' ht' gs hgs gr hgr s hs => ?_)
    cases hgs
    have : t'.goal = t.goal := by
      have := hE _ _ hg
      unfold goalAt at this
      rw [ht'] at this
      exact Option.some.inj this
    rw [this]
    exact h2 gr hgr s hs

/-- The race of a table keeps the invariant, if its answers are answers of
the goal. -/
theorem inv_askRace (U : GOracle R Rel (Ans D P) Cost) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (i : Nat) (g : GoalOf R Rel) (hg : goalAt st i = some g)
    (hU : ∀ n, ∀ a ∈ (U n g).val.2, GoalIs g a) :
    Inv (askRace (K := DerivationKernel.over D K hK P) U i g st).val.1 := by
  have hadd : ∀ n, Inv (foldL (addAnswer (K := DerivationKernel.over D K hK P) i) st
      (U n g).val.2).val := fun n =>
    (foldL_inv (fun b : StateOf R Rel (Ans D P) => Inv b ∧ goalAt b i = some g) _ _
      (fun b x hx hb => ⟨inv_addAnswer hb.1 i x fun g' hg' => by
          obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hb.2)
          exact hU _ x hx,
        (Reach.add (K := _) (hK := hK) b i x).ext _ _ hb.2⟩) st ⟨hI, hg⟩).1
  rw [askRace_val]
  split
  · exact hI
  · split
    · exact hI
    · split
      · exact hI
      · split
        · split
          · exact Inv.modify_same (hadd _) i _ (fun _ => rfl) (fun _ => rfl)
          · exact hI.modify_same i _ (fun _ => rfl) (fun _ => rfl)
        · exact hI.modify_same i _ (fun _ => rfl) (fun _ => rfl)

/-- The first state has the invariant, and its first table is the table of
the root goal. -/
theorem inv_init {root : Rel} (hn : Normal root) :
    Inv (init (K := DerivationKernel.over D K hK P) root).val ∧
      goalAt (init (K := DerivationKernel.over D K hK P) root).val 0 = some ⟨none, root, none⟩ := by
  have hself := selfConverse_spec (P := P) K hK ⟨none, root, none⟩
  at_cost K hK
  simp only [init, Cost.bind_val, Cost.pure_val]
  refine ⟨⟨fun j t h => ?_, fun j t h gs hgs => ?_⟩, rfl⟩
  · obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? h)
    exact ⟨hn, hself, fun a ha => by cases ha⟩
  · obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? h)
    cases hgs

end kernel

end Symmetric

end RwLog
