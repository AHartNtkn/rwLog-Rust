/-
# How the tables of the symmetric engine change

Whatever the engine does, the goal of a table and whether it is its own
converse never change, a table is opened with no answer, and an answer goes
into a table by `addAnswer` and in no other way (`Reach`, and `reach_request`
for a whole request). Every invariant of the answers of a table is proved
from this.
-/
import RwLog.Rungs.Symmetric.Machine
import RwLog.Rungs.Framework.KernelAt
import RwLog.Rungs.Framework.TraverseStd

namespace RwLog

namespace Symmetric

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- What never changes of a table, and its answers. -/
def Table.core {S N A : Type} (t : Table S N A) : GoalOf S N × Bool × List A :=
  (t.goal, t.self, t.answers)

/-- The tables of a state, each as its goal, whether the goal is its own
converse, and its answers. -/
def StateOf.cores {S N A : Type} (st : StateOf S N A) : List (GoalOf S N × Bool × List A) :=
  st.tables.map Table.core

theorem cores_modify {S N A : Type} (st : StateOf S N A) (i : Nat) (f : Table S N A → Table S N A)
    (hf : ∀ t, (f t).core = t.core) : (st.modify i f).cores = st.cores := by
  unfold StateOf.cores StateOf.modify
  simp only
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp only [List.getElem_map, List.getElem_modify]
    split
    · exact hf _
    · rfl

section

variable (K : Kernel R Cost) (hK : K.Refines D)

/-- One state is reached from another: by changes that leave every goal and
every answer as they are, by opening a table with no answer, and by putting
an answer into a table with `addAnswer`. -/
inductive Reach : StateOf R Rel (Ans D P) → StateOf R Rel (Ans D P) → Prop
  | refl (st) : Reach st st
  | trans {a b c} : Reach a b → Reach b c → Reach a c
  | same {st st'} : st'.cores = st.cores → Reach st st'
  | opened {st st'} (g : GoalOf R Rel) (self : Bool) :
      st'.cores = st.cores ++ [(g, self, [])] → Reach st st'
  | add (st) (i : Nat) (a : Ans D P) :
      Reach st (addAnswer (K := DerivationKernel.over D K hK P) i st a).val

variable {K hK}

theorem reach_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hf : ∀ t, (f t).core = t.core) :
    Reach K hK st (st.modify i f) := .same (cores_modify st i f hf)

theorem reach_openGoal (st : StateOf R Rel (Ans D P)) (g : GoalOf R Rel) :
    Reach K hK st (openGoal (K := DerivationKernel.over D K hK P) st g).val.1 := by
  at_cost K hK
  simp only [openGoal, Cost.bind_val]
  split
  · exact .refl _
  · refine .opened g (selfConverse (K := DerivationKernel.over D _ hK P) g).val ?_
    simp [StateOf.cores, Table.core]

theorem reach_addOption (st : StateOf R Rel (Ans D P)) (i : Nat) (a : Option (Ans D P)) :
    Reach K hK st (addOption (K := DerivationKernel.over D K hK P) i st a).val := by
  at_cost K hK
  cases a with
  | none => exact Reach.refl st
  | some a => exact Reach.add st i a

/-- A fold of steps each of which reaches the next state reaches the last. -/
theorem reach_foldL {α β : Type} (π : β → StateOf R Rel (Ans D P)) (f : β → α → Cost β)
    (hf : ∀ b x, Reach K hK (π b) (π (f b x).val)) :
    ∀ (xs : List α) (b : β), Reach K hK (π b) (π (foldL f b xs).val)
  | [], b => Reach.refl _
  | x :: xs, b => by
    simp only [foldL, Cost.bind_val]
    exact (hf b x).trans (reach_foldL π f hf xs _)

/-- The same, from a state already reached. -/
theorem reach_foldL_from {α β : Type} (π : β → StateOf R Rel (Ans D P)) (f : β → α → Cost β)
    (hf : ∀ b x, Reach K hK (π b) (π (f b x).val)) (xs : List α) (b : β)
    {s₀ : StateOf R Rel (Ans D P)} (h₀ : Reach K hK s₀ (π b)) :
    Reach K hK s₀ (π (foldL f b xs).val) :=
  h₀.trans (reach_foldL π f hf xs b)

theorem reach_copyFrom (i : Nat) (g : GoalOf R Rel) (isCall : Bool) (m : Nat)
    (st : StateOf R Rel (Ans D P)) (as : List (Ans D P)) :
    Reach K hK st (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val := by
  at_cost K hK
  refine reach_foldL (fun st => st) _ (fun b x => ?_) as st
  dsimp only
  split <;> (erw [Cost.bind_val]; exact reach_addOption _ _ _)

theorem reach_joinPairs (i : Nat) (k : Kind) (xs ys : List (Ans D P))
    (st : StateOf R Rel (Ans D P)) (ps : List (Nat × Nat)) :
    Reach K hK st (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val := by
  at_cost K hK
  refine reach_foldL (fun st => st) _ (fun b p => ?_) ps st
  split
  · erw [Cost.bind_val]
    exact reach_addOption _ _ _
  · exact Reach.refl _

theorem reach_pushOpen (g : GoalOf R Rel) (other : Rel) (k : Kind) (left : Bool)
    (st : StateOf R Rel (Ans D P)) (xs : List (Ans D P)) :
    Reach K hK st (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1 := by
  at_cost K hK
  refine reach_foldL (fun acc : StateOf R Rel (Ans D P) × List (Ans D P × Nat × Nat) => acc.1) _
    (fun b x => ?_) xs (st, [])
  simp only [Cost.bind_val]
  exact reach_openGoal _ _

theorem reach_pushTake (i : Nat) (k : Kind) (left : Bool) (x : Ans D P)
    (st : StateOf R Rel (Ans D P)) (ys : List (Ans D P)) :
    Reach K hK st (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val := by
  at_cost K hK
  refine reach_foldL (fun st => st) _ (fun b y => ?_) ys st
  simp only [Cost.bind_val]
  exact reach_addOption _ _ _

theorem reach_splitGroup (k : Kind) (L Rg : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 := by
  at_cost K hK
  simp only [splitGroup, Cost.bind_val]
  exact (reach_openGoal _ _).trans (reach_openGoal _ _)

theorem reach_expand (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (expand (K := DerivationKernel.over D K hK P) g st).val.1 := by
  at_cost K hK
  simp only [expand, Cost.bind_val]
  split
  · exact Reach.refl _
  · simp only [Cost.bind_val]
    split
    · exact Reach.refl _
    · simp only [Cost.bind_val]
      exact reach_openGoal _ _
  · simp only [Cost.bind_val]
    refine reach_foldL (fun acc : StateOf R Rel (Ans D P) × List (Nat × Nat) => acc.1) _
      (fun b x => ?_) _ (st, [])
    simp only [Cost.bind_val]
    exact reach_openGoal _ _
  · refine reach_foldL (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) => acc.1) _
      (fun b x => ?_) _ (st, [])
    simp only [Cost.bind_val]
    split
    · simp only [Cost.bind_val]
      exact reach_splitGroup .seq _ _ b.1
    · exact Reach.refl _
  · refine reach_foldL (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) => acc.1) _
      (fun b x => ?_) _ (st, [])
    simp only [Cost.bind_val]
    split
    · simp only [Cost.bind_val]
      exact reach_splitGroup .and _ _ b.1
    · exact Reach.refl _

theorem reach_work (whole : Bool) (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) :
    Reach K hK st (work (K := DerivationKernel.over D K hK P) whole i g st s).val.1 := by
  at_cost K hK
  cases s with
  | span ran =>
    cases ran
    · simp only [work, Cost.bind_val, Cost.pure_val]
      exact reach_addOption _ _ _
    · exact Reach.refl _
  | copy isCall subs =>
    simp only [work]
    split
    · simp only [Cost.bind_val, Cost.pure_val]
      exact reach_foldL (fun st => st) _ (fun b p => reach_copyFrom _ _ _ _ _ _) _ st
    · split
      · exact Reach.refl _
      · simp only [Cost.bind_val, Cost.pure_val]
        exact reach_copyFrom _ _ _ _ _ _
  | join k a b c =>
    simp only [work]
    split
    · simp only [Cost.bind_val, Cost.pure_val]
      exact reach_joinPairs _ _ _ _ _ _
    · split
      · exact Reach.refl _
      · simp only [Cost.bind_val, Cost.pure_val]
        exact reach_joinPairs _ _ _ _ _ _
  | push k left side other todo subs =>
    simp only [work]
    split
    · exact Reach.refl _
    · split
      · cases todo <;>
        · erw [Cost.bind_val]
          simp only [Cost.bind_val, Cost.pure_val]
          exact Reach.trans (reach_pushOpen g other k left st _)
            (reach_foldL (fun st => st) _ (fun b e => reach_pushTake _ _ _ _ _ _) _ _)
      · split
        · simp only [Cost.bind_val, Cost.pure_val]
          exact Reach.refl _
        · simp only [Cost.bind_val, Cost.pure_val]
          exact reach_pushOpen _ _ _ _ _ _
        · split
          · exact Reach.refl _
          · simp only [Cost.bind_val, Cost.pure_val]
            exact reach_pushTake _ _ _ _ _ _

theorem reach_setGroup (st : StateOf R Rel (Ans D P)) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P)) : Reach K hK st (setGroup st i k f) :=
  reach_modify st i _ fun _ => rfl

theorem reach_workGroup (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Reach K hK st (adv h st).val.1) (whole : Bool) (i : Nat) (g : GoalOf R Rel)
    (k : Nat) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1 := by
  at_cost K hK
  simp only [workGroup, Cost.bind_val, Cost.pure_val]
  refine Reach.trans ?_ (reach_setGroup _ _ _ _)
  refine reach_foldL_from (fun acc : StateOf R Rel (Ans D P) × Nat => acc.1) _ (fun b h => ?_) _ _ ?_
  · simp only [Cost.bind_val, Cost.pure_val]
    exact hadv _ _
  · refine reach_foldL (fun acc : StateOf R Rel (Ans D P) × Nat × Bool => acc.1) _ (fun b j => ?_) _
      (st, 0, false)
    split
    · exact Reach.refl _
    · simp only [Cost.bind_val, Cost.pure_val]
      exact (reach_work _ _ _ _ _).trans (reach_setGroup _ _ _ _)

theorem reach_workLevel (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Reach K hK st (adv h st).val.1) (whole : Bool) (i : Nat) (g : GoalOf R Rel)
    (lv : Nat) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv st).val.1 := by
  at_cost K hK
  refine reach_foldL (fun acc : StateOf R Rel (Ans D P) × Bool => acc.1) _ (fun b p => ?_) _
    (st, false)
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    exact reach_workGroup adv hadv _ _ _ _ _
  · exact Reach.refl _

theorem reach_prepare (i : Nat) (t : Table R Rel (Ans D P)) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (prepare (K := DerivationKernel.over D K hK P) i t st).val := by
  at_cost K hK
  unfold prepare
  cases t.groups with
  | some _ => exact reach_modify _ _ _ fun _ => rfl
  | none =>
    simp only [Cost.bind_val, Cost.pure_val]
    refine Reach.trans ?_ (reach_modify _ _ _ fun _ => rfl)
    refine Reach.trans ?_ (reach_modify _ _ _ fun _ => rfl)
    exact reach_expand _ _

theorem reach_advance : ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)),
    Reach K hK st (advance (K := DerivationKernel.over D K hK P) fuel i st).val.1
  | 0, _, st => by
    at_cost K hK
    exact Reach.refl st
  | fuel + 1, i, st => by
    have ih := fun h st => reach_advance fuel h st
    at_cost K hK
    simp only [advance]
    split
    · exact Reach.refl st
    · split
      · exact Reach.refl st
      · split
        · exact Reach.refl st
        · split
          · exact Reach.refl st
          · simp only [Cost.bind_val, Cost.pure_val]
            refine Reach.trans ?_ (reach_modify _ _ _ fun _ => rfl)
            refine reach_foldL_from (fun acc : StateOf R Rel (Ans D P) × Bool => acc.1) _
              (fun b lv => ?_) _ _ (reach_prepare _ _ _)
            split
            · exact Reach.refl _
            · exact reach_workLevel _ ih _ _ _ _ _

omit [DecidableEq R] in
theorem cores_mapIdx (st : StateOf R Rel (Ans D P))
    (f : Nat → Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hf : ∀ i t, (f i t).core = t.core) :
    ({ st with tables := st.tables.mapIdx f } : StateOf R Rel (Ans D P)).cores = st.cores := by
  unfold StateOf.cores
  simp only
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp only [List.getElem_map, List.getElem_mapIdx]
    exact hf _ _

/-- A request reaches its state: nothing goes into a table but by
`addAnswer`. -/
theorem reach_request (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (request (K := DerivationKernel.over D K hK P) st).val.1 := by
  have h := fun st => reach_advance (K := K) (hK := hK) (P := P) st.tables.length 0 st
  at_cost K hK
  simp only [request, Cost.bind_val, Cost.pure_val]
  refine Reach.trans (Reach.trans (Reach.same (st' := { st with round := st.round + 1 }) rfl)
    (h { st with round := st.round + 1 })) ?_
  refine Reach.trans (Reach.same (cores_mapIdx _ _ fun i t => ?_)) (Reach.same rfl)
  split <;> rfl

end

end Symmetric

end RwLog
