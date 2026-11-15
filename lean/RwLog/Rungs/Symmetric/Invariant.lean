/-
# How the tables of the symmetric engine change

Whatever the engine does, the goal of a table and whether it is its own
converse never change, a table is opened with no answer, an answer goes
into a table by `addAnswer` and in no other way, and the position the answers
of the root table were emitted to moves only at the end of a request
(`Reach`, and `reach_request` for a whole request). Every invariant of the
answers of a table is proved from this.

`Inner i` is the finer account of what the strategies of the table at `i` do
by themselves, between the rounds they give to other tables: no table is
marked complete, no table but the one at `i` gains an answer, and the number
of requests stays.
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

/-- What the work of a strategy leaves of a table, unless it puts an answer
in: its goal, whether the goal is its own converse, its answers, whether it
is complete, the requests it was opened in and last had a round in, and its
groups (the strategy that worked is put back by `setGroup`, after its
work), its race, the number of its rounds and what it has been fed. -/
def Table.frame {S N A : Type} (t : Table S N A) :
    GoalOf S N × Bool × List A × Bool × Nat × Nat × Option (List (Group N A)) × Option Race × Nat ×
      Nat :=
  (t.goal, t.self, t.answers, t.done, t.born, t.stamp, t.groups, t.race, t.rounds, t.fed)

/-- The tables of a state, each as its frame. -/
def StateOf.frames {S N A : Type} (st : StateOf S N A) :
    List (GoalOf S N × Bool × List A × Bool × Nat × Nat × Option (List (Group N A)) ×
      Option Race × Nat × Nat) :=
  st.tables.map Table.frame

theorem frames_modify {S N A : Type} (st : StateOf S N A) (i : Nat) (f : Table S N A → Table S N A)
    (hf : ∀ t, (f t).frame = t.frame) : (st.modify i f).frames = st.frames := by
  unfold StateOf.frames StateOf.modify
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
  | same {st st'} : st'.cores = st.cores → st'.shown = st.shown → Reach st st'
  | opened {st st'} (g : GoalOf R Rel) (self : Bool) :
      st'.cores = st.cores ++ [(g, self, [])] → st'.shown = st.shown → Reach st st'
  | add (st) (i : Nat) (a : Ans D P) :
      Reach st (addAnswer (K := DerivationKernel.over D K hK P) i st a).val

/-- One state is reached from another by the work of the strategies of the
table at `i` alone: by changes that leave of every table its goal, its
answers, whether it is complete, the requests it was opened and last served
in, and its groups; by opening a table, with no answer, not complete and
with no groups yet; and by putting an answer into the table at `i`. The
number of requests and the position the root's answers are emitted to stay,
and the depth edges are read to does not fall. -/
inductive Inner (i : Nat) : StateOf R Rel (Ans D P) → StateOf R Rel (Ans D P) → Prop
  | refl (st) : Inner i st st
  | trans {a b c} : Inner i a b → Inner i b c → Inner i a c
  | same {st st'} : st'.frames = st.frames → st'.round = st.round → st'.shown = st.shown →
      st.depth ≤ st'.depth → Inner i st st'
  | opened {st st'} (g : GoalOf R Rel) (self : Bool) :
      st'.frames = st.frames ++ [(g, self, [], false, st.round, 0, none, none, 0, 0)] →
      st'.round = st.round →
      st'.shown = st.shown → st.depth ≤ st'.depth → Inner i st st'
  | add (st) (a : Ans D P) :
      Inner i st (addAnswer (K := DerivationKernel.over D K hK P) i st a).val

variable {K hK}

omit [DecidableEq R] in
theorem cores_of_frames (st : StateOf R Rel (Ans D P)) :
    st.cores = st.frames.map fun f => (f.1, f.2.1, f.2.2.1) := by
  simp [StateOf.cores, StateOf.frames, Table.core, Table.frame]

/-- The work of the strategies of one table is a way to reach a state. -/
theorem Inner.reach {i : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK i st st') :
    Reach K hK st st' := by
  induction h with
  | refl st => exact .refl st
  | trans _ _ a b => exact a.trans b
  | same e _ es _ => exact .same (by rw [cores_of_frames, cores_of_frames, e]) es
  | opened g self e _ es _ =>
    exact .opened g self (by rw [cores_of_frames, cores_of_frames, e]; simp) es
  | add st a => exact .add st _ a

theorem inner_modify {w : Nat} (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hf : ∀ t, (f t).frame = t.frame) :
    Inner K hK w st (st.modify i f) :=
  .same (frames_modify st i f hf) rfl rfl (Nat.le_refl _)

theorem reach_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hf : ∀ t, (f t).core = t.core) :
    Reach K hK st (st.modify i f) := .same (cores_modify st i f hf) rfl

theorem inner_openGoal {w : Nat} (st : StateOf R Rel (Ans D P)) (g : GoalOf R Rel) :
    Inner K hK w st (openGoal (K := DerivationKernel.over D K hK P) st g).val.1 := by
  at_cost K hK
  simp only [openGoal, Cost.bind_val]
  split
  · exact .refl _
  · refine .opened g (selfConverse (K := DerivationKernel.over D _ hK P) g).val ?_ rfl rfl
      (Nat.le_refl _)
    simp [StateOf.frames, Table.frame]

theorem inner_addOption (st : StateOf R Rel (Ans D P)) (i : Nat) (a : Option (Ans D P)) :
    Inner K hK i st (addOption (K := DerivationKernel.over D K hK P) i st a).val := by
  at_cost K hK
  cases a with
  | none => exact Inner.refl st
  | some a => exact Inner.add st a

/-- A fold of steps each of which reaches the next state reaches the last. -/
theorem inner_foldL {w : Nat} {α β : Type} (π : β → StateOf R Rel (Ans D P)) (f : β → α → Cost β)
    (hf : ∀ b x, Inner K hK w (π b) (π (f b x).val)) :
    ∀ (xs : List α) (b : β), Inner K hK w (π b) (π (foldL f b xs).val)
  | [], b => Inner.refl _
  | x :: xs, b => by
    simp only [foldL, Cost.bind_val]
    exact (hf b x).trans (inner_foldL π f hf xs _)

theorem inner_copyFrom (i : Nat) (g : GoalOf R Rel) (isCall : Bool) (m : Nat)
    (st : StateOf R Rel (Ans D P)) (as : List (Ans D P)) :
    Inner K hK i st (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val := by
  at_cost K hK
  refine inner_foldL (fun st => st) _ (fun b x => ?_) as st
  dsimp only
  split <;> (erw [Cost.bind_val]; exact inner_addOption _ _ _)

theorem inner_joinPairs (i : Nat) (k : Kind) (xs ys : List (Ans D P))
    (st : StateOf R Rel (Ans D P)) (ps : List (Nat × Nat)) :
    Inner K hK i st (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val := by
  at_cost K hK
  refine inner_foldL (fun st => st) _ (fun b p => ?_) ps st
  split
  · erw [Cost.bind_val]
    exact inner_addOption _ _ _
  · exact Inner.refl _

theorem inner_pushOpen {w : Nat} (g : GoalOf R Rel) (other : Rel) (k : Kind) (left : Bool)
    (st : StateOf R Rel (Ans D P)) (xs : List (Ans D P)) :
    Inner K hK w st (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1 := by
  at_cost K hK
  refine inner_foldL (fun acc : StateOf R Rel (Ans D P) × List (Ans D P × Nat × Nat) => acc.1) _
    (fun b x => ?_) xs (st, [])
  simp only [Cost.bind_val]
  exact inner_openGoal _ _

theorem inner_pushTake (i : Nat) (k : Kind) (left : Bool) (x : Ans D P)
    (st : StateOf R Rel (Ans D P)) (ys : List (Ans D P)) :
    Inner K hK i st (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val := by
  at_cost K hK
  refine inner_foldL (fun st => st) _ (fun b y => ?_) ys st
  simp only [Cost.bind_val]
  exact inner_addOption _ _ _

theorem inner_splitGroup {w : Nat} (k : Kind) (L Rg : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    Inner K hK w st (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 := by
  at_cost K hK
  simp only [splitGroup, Cost.bind_val]
  exact (inner_openGoal _ _).trans (inner_openGoal _ _)

theorem inner_edgeOf {w : Nat} (st : StateOf R Rel (Ans D P)) (last : Bool) (n : Rel) :
    Inner K hK w st (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1 := by
  at_cost K hK
  simp only [edgeOf, Cost.bind_val]
  split
  · exact Inner.refl _
  · simp only [Cost.bind_val, Cost.pure_val]
    split
    · exact .same rfl rfl rfl (Nat.le_refl _)
    · exact .same rfl rfl rfl (Nat.le_mul_of_pos_left _ (by decide))

theorem inner_checkOf {w : Nat} (st : StateOf R Rel (Ans D P)) (left : Bool) (side other : Rel) :
    Inner K hK w st (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.1 := by
  at_cost K hK
  simp only [checkOf, Cost.bind_val, Cost.pure_val]
  exact inner_edgeOf _ _ _

theorem inner_chainGroups {w : Nat} (g : GoalOf R Rel) (k : Nat) (st : StateOf R Rel (Ans D P)) :
    Inner K hK w st (chainGroups (K := DerivationKernel.over D K hK P) g k st).val.1 := by
  at_cost K hK
  refine inner_foldL (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) ×
    List (Strat Rel (Ans D P)) => acc.1) _ (fun b x => ?_) _ (st, [], [])
  simp only [Cost.bind_val]
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    exact ((inner_splitGroup .seq _ _ b.1).trans (inner_checkOf _ _ _ _)).trans
      (inner_checkOf _ _ _ _)
  · exact Inner.refl _

theorem inner_expand {w : Nat} (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    Inner K hK w st (expand (K := DerivationKernel.over D K hK P) g st).val.1 := by
  at_cost K hK
  simp only [expand, Cost.bind_val]
  split
  · exact Inner.refl _
  · simp only [Cost.bind_val]
    split
    · exact Inner.refl _
    · simp only [Cost.bind_val]
      exact inner_openGoal _ _
  · simp only [Cost.bind_val]
    refine inner_foldL (fun acc : StateOf R Rel (Ans D P) × List (Nat × Nat) => acc.1) _
      (fun b x => ?_) _ (st, [])
    simp only [Cost.bind_val]
    exact inner_openGoal _ _
  · simp only [Cost.bind_val, Cost.pure_val]
    exact inner_chainGroups (K := _) (hK := hK) g _ st
  · refine inner_foldL (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) => acc.1) _
      (fun b x => ?_) _ (st, [])
    simp only [Cost.bind_val]
    split
    · simp only [Cost.bind_val]
      exact inner_splitGroup .and _ _ b.1
    · exact Inner.refl _

theorem inner_checkOpen {w : Nat} (g : GoalOf R Rel) (left : Bool) (other : Rel)
    (st : StateOf R Rel (Ans D P)) (ps : List R) :
    Inner K hK w st (checkOpen (K := DerivationKernel.over D K hK P) g left other st ps).val.1 := by
  at_cost K hK
  refine inner_foldL (fun acc : StateOf R Rel (Ans D P) × List Nat => acc.1) _
    (fun b x => ?_) ps (st, [])
  simp only [Cost.bind_val]
  exact inner_openGoal _ _

theorem inner_stamp {w : Nat} (i n : Nat) (pth : Path) (st : StateOf R Rel (Ans D P)) :
    Inner K hK w st (stamp i n pth st) :=
  inner_modify st i _ fun _ => rfl

theorem inner_work (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) :
    Inner K hK i st (work (K := DerivationKernel.over D K hK P) i g st s).val.1 := by
  at_cost K hK
  cases s with
  | span ran =>
    cases ran
    · simp only [work, Cost.bind_val, Cost.pure_val]
      exact inner_addOption _ _ _
    · exact Inner.refl _
  | copy isCall subs =>
    simp only [work]
    split
    · exact Inner.refl _
    · simp only [Cost.bind_val, Cost.pure_val]
      exact (inner_copyFrom _ _ _ _ _ _).trans (inner_stamp _ _ _ _)
  | join k a b c =>
    simp only [work]
    split
    · exact Inner.refl _
    · simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      exact (inner_joinPairs _ _ _ _ _ _).trans (inner_stamp _ _ _ _)
  | push k left side other todo subs =>
    simp only [work]
    split
    · exact Inner.refl _
    · split
      · simp only [Cost.bind_val, Cost.pure_val]
        exact Inner.refl _
      · simp only [Cost.bind_val, Cost.pure_val]
        exact inner_pushOpen _ _ _ _ _ _
      · split
        · exact Inner.refl _
        · simp only [Cost.bind_val, Cost.pure_val]
          exact (inner_pushTake _ _ _ _ _ _).trans (inner_stamp _ _ _ _)
  | check left side other c =>
    cases c with
    | reading =>
      simp only [work, Cost.bind_val]
      split
      · exact inner_edgeOf _ _ _
      · exact inner_edgeOf _ _ _
      · simp only [Cost.bind_val, Cost.pure_val]
        exact (inner_edgeOf _ _ _).trans (inner_checkOpen _ _ _ _ _)
    | off => exact Inner.refl _
    | opened subs => exact Inner.refl _

/-! What the work of one table does, as a way to reach a state. -/

theorem reach_openGoal (st : StateOf R Rel (Ans D P)) (g : GoalOf R Rel) :
    Reach K hK st (openGoal (K := DerivationKernel.over D K hK P) st g).val.1 :=
  (inner_openGoal (w := 0) st g).reach

theorem reach_addOption (st : StateOf R Rel (Ans D P)) (i : Nat) (a : Option (Ans D P)) :
    Reach K hK st (addOption (K := DerivationKernel.over D K hK P) i st a).val :=
  (inner_addOption st i a).reach

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
    Reach K hK st (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val :=
  (inner_copyFrom i g isCall m st as).reach

theorem reach_joinPairs (i : Nat) (k : Kind) (xs ys : List (Ans D P))
    (st : StateOf R Rel (Ans D P)) (ps : List (Nat × Nat)) :
    Reach K hK st (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val :=
  (inner_joinPairs i k xs ys st ps).reach

theorem reach_pushOpen (g : GoalOf R Rel) (other : Rel) (k : Kind) (left : Bool)
    (st : StateOf R Rel (Ans D P)) (xs : List (Ans D P)) :
    Reach K hK st (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1 :=
  (inner_pushOpen (w := 0) g other k left st xs).reach

theorem reach_pushTake (i : Nat) (k : Kind) (left : Bool) (x : Ans D P)
    (st : StateOf R Rel (Ans D P)) (ys : List (Ans D P)) :
    Reach K hK st (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val :=
  (inner_pushTake i k left x st ys).reach

theorem reach_splitGroup (k : Kind) (L Rg : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.1 :=
  (inner_splitGroup (w := 0) k L Rg st).reach

theorem reach_edgeOf (st : StateOf R Rel (Ans D P)) (last : Bool) (n : Rel) :
    Reach K hK st (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1 :=
  (inner_edgeOf (w := 0) st last n).reach

theorem reach_checkOf (st : StateOf R Rel (Ans D P)) (left : Bool) (side other : Rel) :
    Reach K hK st (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.1 :=
  (inner_checkOf (w := 0) st left side other).reach

theorem reach_chainGroups (g : GoalOf R Rel) (k : Nat) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (chainGroups (K := DerivationKernel.over D K hK P) g k st).val.1 :=
  (inner_chainGroups (w := 0) g k st).reach

theorem reach_expand (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (expand (K := DerivationKernel.over D K hK P) g st).val.1 :=
  (inner_expand (w := 0) g st).reach

theorem reach_checkOpen (g : GoalOf R Rel) (left : Bool) (other : Rel)
    (st : StateOf R Rel (Ans D P)) (ps : List R) :
    Reach K hK st (checkOpen (K := DerivationKernel.over D K hK P) g left other st ps).val.1 :=
  (inner_checkOpen (w := 0) g left other st ps).reach

theorem reach_work (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) :
    Reach K hK st (work (K := DerivationKernel.over D K hK P) i g st s).val.1 :=
  (inner_work i g st s).reach

/-- The strategy `workStrats` picks, with what it owes, is the strategy at
its place in its group. -/
theorem pick_strat {N A : Type} {go : Option (Group N A)} {j : Nat} {s : Strat N A} {o : Nat}
    (h : (go.bind fun gr => gr.strats[j]?.map fun s => (s, gr.owed.getD j 0)) = some (s, o)) :
    go.bind (·.strats[j]?) = some s ∧ ∃ gr, go = some gr ∧ o = gr.owed.getD j 0 := by
  cases go with
  | none => cases h
  | some gr =>
    simp only [Option.bind_some] at h ⊢
    cases hs : gr.strats[j]? with
    | none => rw [hs] at h; cases h
    | some s' =>
      rw [hs] at h
      cases h
      exact ⟨rfl, gr, rfl, rfl⟩

theorem getD_setOwed_self (l : List Nat) (j v : Nat) : (setOwed l j v).getD j 0 = v := by
  have h : j < l.length + (j + 1 - l.length) := by omega
  simp [setOwed, List.getD_eq_getElem?_getD, h]

theorem getD_setOwed_ne (l : List Nat) {j m : Nat} (v : Nat) (h : m ≠ j) :
    (setOwed l j v).getD m 0 = l.getD m 0 := by
  simp only [setOwed, List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h, ite_false]
  by_cases hm : m < l.length
  · rw [List.getElem?_append_left hm]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (Nat.le_of_not_lt hm),
      List.getElem?_replicate]
    split <;> rfl

/-! ## A turn

A turn is unit after unit of the work of one strategy, so what every unit
keeps a turn keeps (`turn_ind`), and a turn with ticks left begins with a
unit (`turn_succ`). -/

theorem turn_fuel_zero (i : Nat) (g : GoalOf R Rel) (left : Nat) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (c : Nat) :
    (turn (K := DerivationKernel.over D K hK P) i g 0 left st s c).val = (st, s, c) := by
  at_cost K hK
  rfl

theorem turn_zero (i : Nat) (g : GoalOf R Rel) (f : Nat) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (c : Nat) :
    (turn (K := DerivationKernel.over D K hK P) i g f 0 st s c).val = (st, s, c) := by
  at_cost K hK
  cases f <;> simp [turn]

/-- A turn with ticks left: one unit, and if it did anything the rest of
the turn. -/
theorem turn_succ (i : Nat) (g : GoalOf R Rel) (f left : Nat) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (c : Nat) (hl : left ≠ 0) :
    (turn (K := DerivationKernel.over D K hK P) i g (f + 1) left st s c).val =
      if (work (K := DerivationKernel.over D K hK P) i g st s).val.2.2 then
        (turn (K := DerivationKernel.over D K hK P) i g f
          (left - ((work (K := DerivationKernel.over D K hK P) i g st s).ticks + 1))
          (work (K := DerivationKernel.over D K hK P) i g st s).val.1
          (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1
          (c + (work (K := DerivationKernel.over D K hK P) i g st s).ticks + 1)).val
      else ((work (K := DerivationKernel.over D K hK P) i g st s).val.1,
        (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1, c) := by
  at_cost K hK
  simp only [turn, hl, ↓reduceIte, Cost.bind_val]
  split
  · next h => simp only [Kernel.metered, Cost.metered_val] at h ⊢; simp [h]
  · next h => simp only [Kernel.metered, Cost.metered_val] at h ⊢; simp [h]

/-- What every unit of the work of a strategy keeps, a turn keeps. -/
theorem turn_ind (i : Nat) (g : GoalOf R Rel)
    (Q : StateOf R Rel (Ans D P) → Strat Rel (Ans D P) → Prop)
    (hw : ∀ st s, Q st s → Q (work (K := DerivationKernel.over D K hK P) i g st s).val.1
      (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1) :
    ∀ (f left : Nat) (st : StateOf R Rel (Ans D P)) (s : Strat Rel (Ans D P)) (c : Nat), Q st s →
      Q (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.1
        (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.2.1
  | 0, left, st, s, c, h => by
    rw [turn_fuel_zero]
    exact h
  | f + 1, left, st, s, c, h => by
    by_cases hl : left = 0
    · subst hl
      rw [turn_zero]
      exact h
    · rw [turn_succ i g f left st s c hl]
      split
      · exact turn_ind i g Q hw f _ _ _ _ (hw st s h)
      · exact hw st s h

theorem inner_turn (i : Nat) (g : GoalOf R Rel) (f left : Nat) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (c : Nat) :
    Inner K hK i st (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.1 :=
  turn_ind i g (fun st' _ => Inner K hK i st st')
    (fun st' s' h => h.trans (inner_work i g st' s')) f left st s c (Inner.refl st)

theorem reach_turn (i : Nat) (g : GoalOf R Rel) (f left : Nat) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (c : Nat) :
    Reach K hK st (turn (K := DerivationKernel.over D K hK P) i g f left st s c).val.1 :=
  (inner_turn i g f left st s c).reach

theorem reach_setGroup (st : StateOf R Rel (Ans D P)) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P)) : Reach K hK st (setGroup st i k f) :=
  reach_modify st i _ fun _ => rfl

/-- The rounds of the tables a group reads keep what a round keeps and a
change to what a table has been fed keeps. -/
theorem feedGroup_keeps (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (I : StateOf R Rel (Ans D P) → Prop) (hadv : ∀ h st, I st → I (adv h st).val.1)
    (hfed : ∀ h c st, I st → I (st.modify h fun t => { t with fed := t.fed + c }))
    (i k : Nat) (st : StateOf R Rel (Ans D P)) (d : Nat) (h0 : I st) :
    I (feedGroup (K := DerivationKernel.over D K hK P) adv i k st d).val.1 := by
  at_cost K hK
  have step : ∀ h X, I X → I (feed (K := DerivationKernel.over D _ hK P) adv h X).val.1 := by
    intro h X hX
    simp only [feed, Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
    exact hfed _ _ _ (hadv _ _ hX)
  simp only [feedGroup]
  split
  · simp only [feedFirst, Cost.bind_val, Cost.pure_val]
    refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × Nat × Bool => I acc.1) _ _
      (fun b h _ hb => ?_) _ h0
    split
    · exact hb
    · simp only [Cost.bind_val, Cost.pure_val]
      exact step _ _ hb
  · simp only [feedAll]
    refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × Nat => I acc.1) _ _
      (fun b h _ hb => ?_) _ h0
    simp only [Cost.bind_val, Cost.pure_val]
    exact step _ _ hb

theorem reach_workGroup (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Reach K hK st (adv h st).val.1) (i : Nat) (g : GoalOf R Rel)
    (k : Nat) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1 := by
  have ht := fun f left st s c => reach_turn (K := K) (hK := hK) (P := P) i g f left st s c
  have hf := fun X d hX => feedGroup_keeps (K := K) (hK := hK) (P := P) adv (Reach K hK st)
    (fun h X hX => hX.trans (hadv h X))
    (fun h c X hX => hX.trans (reach_modify X h _ fun _ => rfl)) i k X d hX
  at_cost K hK
  simp only [workGroup, workStrats, Cost.bind_val, Cost.pure_val]
  refine Reach.trans ?_ (reach_modify _ _ _ fun _ => rfl)
  refine Reach.trans ?_ (reach_setGroup _ _ _ _)
  refine hf _ _ ?_
  refine reach_foldL (fun acc : StateOf R Rel (Ans D P) × Nat × Bool => acc.1) _ (fun b j => ?_) _
    (st, 0, false)
  split
  · exact Reach.refl _
  · simp only [Cost.bind_val, Cost.pure_val]
    exact (ht _ _ _ _ _).trans (reach_setGroup _ _ _ _)

theorem reach_workLevel (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Reach K hK st (adv h st).val.1) (i : Nat) (g : GoalOf R Rel)
    (lv : Nat) (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (workLevel (K := DerivationKernel.over D K hK P) adv i g lv st).val.1 := by
  at_cost K hK
  refine reach_foldL (fun acc : StateOf R Rel (Ans D P) × Bool => acc.1) _ (fun b p => ?_) _
    (st, false)
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    exact reach_workGroup adv hadv _ _ _ _
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
    exact reach_expand (K := _) (hK := hK) t.goal st

/-- The answers a race gives are put into the table at `i` as the strategies
of the table put theirs. -/
theorem inner_addAll (i : Nat) (st : StateOf R Rel (Ans D P)) (xs : List (Ans D P)) :
    Inner K hK i st (foldL (addAnswer (K := DerivationKernel.over D K hK P) i) st xs).val :=
  inner_foldL (fun s : StateOf R Rel (Ans D P) => s) _ (fun b a => Inner.add b a) _ _

/-- What the race of the table at `i` does: nothing; or it gives up an ask
and records what the ask was allowed; or it puts answers into the table and
records what it has spent; or it records that and a depth one greater. -/
theorem askRace_val (U : GOracle R Rel (Ans D P) Cost) (i : Nat) (g : GoalOf R Rel)
    (st : StateOf R Rel (Ans D P)) :
    (askRace (K := DerivationKernel.over D K hK P) U i g st).val =
      match st.tables[i]? with
      | none => (st, false)
      | some t =>
        match t.race with
        | none => (st, false)
        | some r =>
          if t.own + t.rounds - r.spent < max 1 (2 * r.gaveUp) then (st, false)
          else if (U r.depth g).ticks ≤ t.own + t.rounds - r.spent then
            if (U r.depth g).val.1 then
              ((foldL (addAnswer (K := DerivationKernel.over D K hK P) i) st
                  (U r.depth g).val.2).val.modify i fun t =>
                { t with race := some ⟨r.depth, r.spent + (U r.depth g).ticks, 0⟩ }, true)
            else
              (st.modify i fun t =>
                { t with race := some ⟨r.depth + 1, r.spent + (U r.depth g).ticks, 0⟩ }, false)
          else
            (st.modify i fun u =>
              { u with race := some ⟨r.depth, r.spent + (t.own + t.rounds - r.spent),
                t.own + t.rounds - r.spent⟩ }, false) := by
  at_cost K hK
  unfold askRace
  cases st.tables[i]? with
  | none => rfl
  | some t =>
    dsimp only
    cases t.race with
    | none => rfl
    | some r =>
      dsimp only
      by_cases hb : t.own + t.rounds - r.spent < max 1 (2 * r.gaveUp)
      · simp only [hb, ↓reduceIte]
        rfl
      · simp only [hb, ↓reduceIte]
        by_cases hc : (U r.depth g).ticks ≤ t.own + t.rounds - r.spent
        · simp only [hc, ↓reduceIte, Cost.bind_val, Kernel.metered, Kernel.within,
            Cost.metered_val, Cost.within]
          cases hv : (U r.depth g).val.1 with
          | false => simp
          | true => simp
        · simp only [hc, ↓reduceIte, Cost.bind_val, Kernel.metered, Kernel.within,
            Cost.metered_val, Cost.within, Cost.pure_val]

/-- The race of a table reaches a state. -/
theorem reach_askRace (U : GOracle R Rel (Ans D P) Cost) (i : Nat) (g : GoalOf R Rel)
    (st : StateOf R Rel (Ans D P)) :
    Reach K hK st (askRace (K := DerivationKernel.over D K hK P) U i g st).val.1 := by
  rw [askRace_val]
  split
  · exact Reach.refl st
  · split
    · exact Reach.refl st
    · split
      · exact Reach.refl st
      · split
        · split
          · exact (inner_addAll i st _).reach.trans (reach_modify _ _ _ fun _ => rfl)
          · exact reach_modify _ _ _ fun _ => rfl
        · exact reach_modify _ _ _ fun _ => rfl

theorem reach_advance (U : GOracle R Rel (Ans D P) Cost) :
    ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)),
    Reach K hK st (advance (K := DerivationKernel.over D K hK P) U fuel i st).val.1
  | 0, _, st => by
    at_cost K hK
    exact Reach.refl st
  | fuel + 1, i, st => by
    have ih := fun h st => reach_advance U fuel h st
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
            refine Reach.trans ?_ (reach_askRace U _ _ _)
            refine Reach.trans ?_ (reach_modify _ _ _ fun _ => rfl)
            refine reach_foldL_from (fun acc : StateOf R Rel (Ans D P) × Bool => acc.1) _
              (fun b lv => ?_) _ _ (reach_prepare _ _ _)
            split
            · exact Reach.refl _
            · exact reach_workLevel _ ih _ _ _ _

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

/-- A request reaches a state, by nothing but `addAnswer` into the tables,
and returns what the root table holds from the position the answers were
emitted to, which it moves to the end. -/
theorem reach_request (U : GOracle R Rel (Ans D P) Cost) (st : StateOf R Rel (Ans D P)) :
    ∃ st' : StateOf R Rel (Ans D P), Reach K hK st st' ∧
      (request (K := DerivationKernel.over D K hK P) U st).val =
        ({ st' with shown := (st'.answers 0).length }, (st'.answers 0).drop st'.shown) := by
  have h := fun st => reach_advance (K := K) (hK := hK) (P := P) U st.tables.length 0 st
  at_cost K hK
  simp only [request, Cost.bind_val, Cost.pure_val]
  refine ⟨_, Reach.trans (Reach.trans (Reach.same (st' := { st with round := st.round + 1 }) rfl rfl)
    (h { st with round := st.round + 1 })) (Reach.same (cores_mapIdx _ _ fun i t => ?_) rfl), rfl⟩
  split <;> rfl

end

end Symmetric

end RwLog
