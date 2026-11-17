/-
# Where the answers of the tables come from

The symmetric engine makes an answer in two ways only: by a rule of the
derivation kernel, from answers its tables hold, and by the unfolding race
of a table. So a property of answers that every rule keeps and every answer
of a race has is a property of every answer of every table.

This file says so with one way out. `Q` is the property. A rule may fail to
keep it in one place: unfolding an answer of the body of a call onto the
call, when `EA` marks the answer unfolded. A race may give answers that `EA`
marks, and is asked for nothing about a goal that `BadG` marks. Then a run
keeps `Prov`: either the run has escaped (`Esc`: a table has a goal that
`BadG` marks, or holds an answer that `EA` marks), or every answer of every
table, and every answer a strategy holds to push, has `Q` (`Lit`).

It is for lower bounds on what the engine pays. With `Q` the answers that
are valid in a program in which one definition is emptied, and `EA` the
answers of the body of that definition, it says a run holds no answer that
needs the definition before a table of its body holds one.
-/
import RwLog.Rungs.Symmetric.Kept

namespace RwLog

namespace Symmetric

open Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
variable {rd : EdgeReader}

/-- The answers a strategy holds: those a push has seen of its side. -/
def Strat.held {N A : Type} : Strat N A → List A
  | .push _ _ _ _ subs _ _ _ _ => subs.map (·.1)
  | _ => []

theorem Strat.held_core {N A : Type} {s s' : Strat N A} (h : s'.core = s.core) :
    s'.held = s.held := by
  cases s <;> cases s' <;> cases h <;> rfl

/-- What is asked of the rules of the kernel: each keeps `Q`, but that an
answer that `EA` marks need not have it once it is unfolded. -/
structure Rules (K : Kernel R Cost) (hK : K.Refines D) (Q EA : Ans D P → Prop) : Prop where
  leaf : ∀ {lb rb : Option R} {n : Rel} {c : Ans D P},
    (Ans.leaf D P K hK lb n rb).val = some c → Q c
  both : ∀ {k : Kind} {x y c : Ans D P}, Q x → Q y →
    (both (K := DerivationKernel.over D K hK P) k x y).val = some c → Q c
  pushed : ∀ {k : Kind} {left : Bool} {x y c : Ans D P}, Q x → Q y →
    (pushed (K := DerivationKernel.over D K hK P) k left x y).val = some c → Q c
  unfold : ∀ {a c : Ans D P} {n : Rel}, Q a → (Ans.unfold D P a n).val = some c → EA a ∨ Q c
  inj : ∀ {a c : Ans D P} {u : Rel} {i : Nat}, Q a → (Ans.inj D P a u i).val = some c → Q c
  swap : ∀ a : Ans D P, Q a → Q (Ans.swapA D P a).val

section defs

variable (Q EA : Ans D P → Prop) (BadG : GoalOf R Rel → Prop)

/-- Every answer of every table, and every answer a strategy holds, has
`Q`. -/
structure Lit (st : StateOf R Rel (Ans D P)) : Prop where
  ans : ∀ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t → ∀ a ∈ t.answers, Q a
  held : ∀ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t →
    ∀ gs, t.groups = some gs → ∀ gr ∈ gs, ∀ s ∈ gr.strats, ∀ a ∈ s.held, Q a

/-- The run has escaped: a table has a goal that `BadG` marks, or holds an
answer that `EA` marks. -/
def Esc (st : StateOf R Rel (Ans D P)) : Prop :=
  ∃ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t ∧
    (BadG t.goal ∨ ∃ a ∈ t.answers, EA a)

/-- What a run keeps: it has escaped, or everything it holds has `Q`. -/
def Prov (st : StateOf R Rel (Ans D P)) : Prop := Esc EA BadG st ∨ Lit Q st

end defs

variable {Q EA : Ans D P → Prop} {BadG : GoalOf R Rel → Prop}

omit [DecidableEq R] in
theorem held_nil_Q {s : Strat Rel (Ans D P)} (h : s.held = []) : ∀ a ∈ s.held, Q a := by
  rw [h]; intro a ha; cases ha

omit [DecidableEq R] in
theorem goalAt_some {st : StateOf R Rel (Ans D P)} {i : Nat} {g : GoalOf R Rel}
    (h : goalAt st i = some g) : ∃ t, st.tables[i]? = some t ∧ t.goal = g := by
  unfold goalAt at h
  cases ht : st.tables[i]? with
  | none => rw [ht] at h; cases h
  | some t => rw [ht] at h; exact ⟨t, rfl, Option.some.inj h⟩

/-! ## An escape stays -/

omit [DecidableEq R] in
theorem Esc.of_cores {st st' : StateOf R Rel (Ans D P)}
    (h : ∀ (i : Nat) c, st.cores[i]? = some c → st'.cores[i]? = some c) (hE : Esc EA BadG st) :
    Esc EA BadG st' := by
  obtain ⟨i, t, ht, hb⟩ := hE
  have hc : st.cores[i]? = some (t.goal, t.self, t.answers) := by
    unfold StateOf.cores; rw [List.getElem?_map, ht]; rfl
  obtain ⟨t', ht', e1, -, e3⟩ := cores_get st' (h i _ hc)
  exact ⟨i, t', ht', by rw [e1, e3]; exact hb⟩

omit [DecidableEq R] in
theorem Esc.modify {st : StateOf R Rel (Ans D P)} (hE : Esc EA BadG st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hg : ∀ t, (f t).goal = t.goal)
    (ha : ∀ t, ∀ a ∈ t.answers, a ∈ (f t).answers) : Esc EA BadG (st.modify i f) := by
  obtain ⟨j, t, ht, hb⟩ := hE
  by_cases e : i = j
  · subst e
    refine ⟨i, f t, ?_, ?_⟩
    · unfold StateOf.modify; simp [ht]
    · rw [hg]; exact hb.imp id (fun ⟨a, h1, h2⟩ => ⟨a, ha t a h1, h2⟩)
  · refine ⟨j, t, ?_, hb⟩
    unfold StateOf.modify; simp [ht, e]

omit [DecidableEq R] in
theorem Esc.of_tables {st st' : StateOf R Rel (Ans D P)} (h : st'.tables = st.tables)
    (hE : Esc EA BadG st) : Esc EA BadG st' := by
  unfold Esc at hE ⊢; rw [h]; exact hE

section reach

variable {K : Kernel R Cost} {hK : K.Refines D}

theorem Esc.reach {st st' : StateOf R Rel (Ans D P)} (h : Reach K hK st st')
    (hE : Esc EA BadG st) : Esc EA BadG st' := by
  induction h with
  | refl => exact hE
  | trans _ _ a b => exact b (a hE)
  | same e _ => exact hE.of_cores (fun i c h => by rw [e]; exact h)
  | opened g self e _ =>
    refine hE.of_cores (fun i c h => ?_)
    rw [e, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h
  | add st i a =>
    have happ : ∀ (X : StateOf R Rel (Ans D P)) (b : Ans D P), Esc EA BadG X →
        Esc EA BadG (X.modify i (app [b])) :=
      fun X b hX => hX.modify i _ (fun _ => rfl) (fun t a h => List.mem_append_left _ h)
    rw [addAnswer_val]
    split
    · exact hE
    · split
      · split
        · exact happ _ _ hE
        · exact happ _ _ (happ _ _ hE)
      · exact happ _ _ hE

end reach

/-! ## What changes of the state keep -/

omit [DecidableEq R] in
theorem Lit.modify {st : StateOf R Rel (Ans D P)} (hL : Lit Q st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hans : ∀ t, st.tables[i]? = some t → ∀ a ∈ (f t).answers, Q a)
    (hheld : ∀ t, st.tables[i]? = some t → ∀ gs, (f t).groups = some gs → ∀ gr ∈ gs,
      ∀ s ∈ gr.strats, ∀ a ∈ s.held, Q a) : Lit Q (st.modify i f) := by
  constructor
  · intro j t' h
    rcases getElem?_modify_cases st i f h with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
    · exact hL.ans j t' h
    · exact hans t ht
  · intro j t' h
    rcases getElem?_modify_cases st i f h with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
    · exact hL.held j t' h
    · exact hheld t ht

omit [DecidableEq R] in
theorem Lit.answers {st : StateOf R Rel (Ans D P)} (hL : Lit Q st) (j : Nat) :
    ∀ a ∈ st.answers j, Q a := by
  unfold StateOf.answers
  cases ht : st.tables[j]? with
  | none => intro a ha; cases ha
  | some t => exact hL.ans j t ht

omit [DecidableEq R] in
theorem Lit.of_tables {st st' : StateOf R Rel (Ans D P)} (h : st'.tables = st.tables)
    (hL : Lit Q st) : Lit Q st' :=
  ⟨fun i t ht => hL.ans i t (h ▸ ht), fun i t ht => hL.held i t (h ▸ ht)⟩

omit [DecidableEq R] in
/-- Changing one table keeps `Prov`, if its goal and its answers stay and
the answers its strategies hold have `Q`. -/
theorem Prov.modify {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hg : ∀ t, (f t).goal = t.goal)
    (ha : ∀ t, (f t).answers = t.answers)
    (hheld : Esc EA BadG st ∨ ∀ t, st.tables[i]? = some t → ∀ gs, (f t).groups = some gs →
      ∀ gr ∈ gs, ∀ s ∈ gr.strats, ∀ a ∈ s.held, Q a) : Prov Q EA BadG (st.modify i f) := by
  have hesc : Esc EA BadG st → Esc EA BadG (st.modify i f) :=
    fun hE => hE.modify i f hg (fun t a h => by rw [ha]; exact h)
  rcases hP with hE | hL
  · exact .inl (hesc hE)
  · rcases hheld with hE | hheld
    · exact .inl (hesc hE)
    · exact .inr (hL.modify i f (fun t ht => by rw [ha]; exact hL.ans i t ht) hheld)

omit [DecidableEq R] in
/-- Changing one table keeps `Prov`, if its goal, its answers and its
strategies stay. -/
theorem Prov.modify_same {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hcore : ∀ t, (f t).core = t.core)
    (hgr : ∀ t, (f t).groups = t.groups) : Prov Q EA BadG (st.modify i f) := by
  have e : ∀ t, (f t).goal = t.goal ∧ (f t).self = t.self ∧ (f t).answers = t.answers :=
    fun t => by
      have := hcore t
      simp only [Table.core, Prod.mk.injEq] at this
      exact this
  refine hP.modify i f (fun t => (e t).1) (fun t => (e t).2.2) ?_
  rcases hP with hE | hL
  · exact .inl hE
  · exact .inr fun t ht gs hgs => by rw [hgr] at hgs; exact hL.held i t ht gs hgs

omit [DecidableEq R] in
theorem Prov.of_tables {st st' : StateOf R Rel (Ans D P)} (h : st'.tables = st.tables)
    (hP : Prov Q EA BadG st) : Prov Q EA BadG st' :=
  hP.imp (Esc.of_tables h) (Lit.of_tables h)

omit [DecidableEq R] in
/-- Removing groups of one table keeps `Prov`. -/
theorem Prov.dropGroups {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) (i : Nat)
    (p : Group Rel (Ans D P) → Bool) :
    Prov Q EA BadG (st.modify i fun t =>
      { t with groups := t.groups.map fun gs => gs.filter p }) := by
  refine hP.modify i _ (fun _ => rfl) (fun _ => rfl) ?_
  rcases hP with hE | hL
  · exact .inl hE
  · refine .inr fun t ht gs hgs gr hgr s hs => ?_
    cases hg : t.groups with
    | none => rw [hg] at hgs; cases hgs
    | some gs' =>
      rw [hg] at hgs
      cases hgs
      exact hL.held i t ht gs' hg gr (List.mem_of_mem_filter hgr) s hs

omit [DecidableEq R] in
/-- Changing a group of a table keeps `Prov` if the answers its strategies
hold still have `Q`. -/
theorem Prov.setGroup {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P))
    (hf : Esc EA BadG st ∨ ∀ gr, (∀ s ∈ gr.strats, ∀ a ∈ s.held, Q a) →
      ∀ s ∈ (f gr).strats, ∀ a ∈ s.held, Q a) : Prov Q EA BadG (setGroup st i k f) := by
  refine hP.modify i _ (fun _ => rfl) (fun _ => rfl) ?_
  rcases hP with hE | hL
  · exact .inl hE
  rcases hf with hE | hf
  · exact .inl hE
  refine .inr fun t ht gs hgs gr hgr s hs => ?_
  simp only at hgs
  cases hgs' : t.groups with
  | none => rw [hgs'] at hgs; cases hgs
  | some gs' =>
    rw [hgs'] at hgs
    cases hgs
    rcases mem_modify hgr with hgr | ⟨gr', hgr', rfl⟩
    · exact hL.held i t ht gs' hgs' gr hgr s hs
    · exact hf gr' (hL.held i t ht gs' hgs' gr' hgr') s hs

omit [DecidableEq R] in
/-- A change of the tables that keeps the goal, the answers and the
strategies of each keeps `Prov`. -/
theorem Prov.of_map {st st' : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st)
    (F : Nat → Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hget : ∀ j, st'.tables[j]? = (st.tables[j]?).map (F j))
    (hcore : ∀ j t, (F j t).core = t.core) (hgr : ∀ j t, (F j t).groups = t.groups) :
    Prov Q EA BadG st' := by
  have e : ∀ j t, (F j t).goal = t.goal ∧ (F j t).self = t.self ∧
      (F j t).answers = t.answers := fun j t => by
    have := hcore j t
    simp only [Table.core, Prod.mk.injEq] at this
    exact this
  have key : ∀ j t', st'.tables[j]? = some t' → ∃ t, st.tables[j]? = some t ∧ t' = F j t := by
    intro j t' h
    rw [hget] at h
    cases ht : st.tables[j]? with
    | none => rw [ht] at h; cases h
    | some t => rw [ht] at h; cases h; exact ⟨t, rfl, rfl⟩
  rcases hP with ⟨j, t, ht, hb⟩ | hL
  · refine .inl ⟨j, F j t, by rw [hget, ht]; rfl, ?_⟩
    rw [(e j t).1, (e j t).2.2]; exact hb
  · refine .inr ⟨fun j t' h => ?_, fun j t' h gs hgs => ?_⟩
    · obtain ⟨t, ht, rfl⟩ := key j t' h
      rw [(e j t).2.2]; exact hL.ans j t ht
    · obtain ⟨t, ht, rfl⟩ := key j t' h
      rw [hgr] at hgs; exact hL.held j t ht gs hgs

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-! ## Work that puts no answer in a table -/

/-- A table that the work of the strategies of another table opens has no
answer. -/
theorem Inner.fresh {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK j st st') :
    ∀ (k : Nat) (t' : Table R Rel (Ans D P)), st'.tables[k]? = some t' →
      st.tables[k]? = none → k ≠ j → t'.answers = [] := by
  induction h with
  | refl st => intro k t' h h'; rw [h] at h'; cases h'
  | @trans a b c h1 h2 ih1 ih2 =>
    intro k t' h hn hk
    cases hb : b.tables[k]? with
    | none => exact ih2 k t' h hb hk
    | some tb =>
      obtain ⟨u, hu, -, -, -, -, -, e6, -⟩ := h2.frame.2.1 k tb hb
      rw [h] at hu; cases hu
      rw [e6 hk]; exact ih1 k tb hb hn hk
  | @same st st' e _ _ _ =>
    intro k t' h hn
    have hl : st'.tables.length = st.tables.length := by
      have := congrArg List.length e
      simpa [StateOf.frames] using this
    have h1 := (List.getElem?_eq_some_iff.1 h).1
    have h2 := List.getElem?_eq_none_iff.1 hn
    omega
  | @opened st st' g self e _ _ _ =>
    intro k t' h hn _
    have hf : st'.frames[k]? = some t'.frame := by
      unfold StateOf.frames; rw [List.getElem?_map, h]; rfl
    rw [e, List.getElem?_append_right (by
      unfold StateOf.frames; rw [List.length_map]; exact List.getElem?_eq_none_iff.1 hn)] at hf
    have := List.mem_singleton.1 (List.mem_of_getElem? hf)
    exact congrArg (fun f => f.2.2.1) this
  | add st a =>
    intro k t' h hn
    have hl : (addAnswer (K := DerivationKernel.over D K hK P) j st a).val.tables.length =
        st.tables.length := by
      rw [addAnswer_val]
      repeat' split
      all_goals simp [StateOf.modify]
    have h1 := (List.getElem?_eq_some_iff.1 h).1
    have h2 := List.getElem?_eq_none_iff.1 hn
    omega

/-- Work that could be the work of the strategies of either of two tables
puts no answer in a table and changes no strategy: `Lit` is kept. -/
theorem Lit.quiet {w1 w2 : Nat} {st st' : StateOf R Rel (Ans D P)}
    (h1 : Inner K hK w1 st st') (h2 : Inner K hK w2 st st') (hne : w1 ≠ w2) (hL : Lit Q st) :
    Lit Q st' := by
  have key : ∀ (k : Nat) (t' : Table R Rel (Ans D P)), st'.tables[k]? = some t' →
      (∃ t, st.tables[k]? = some t ∧ t'.answers = t.answers ∧ t'.groups = t.groups) ∨
        (t'.answers = [] ∧ t'.groups = none) := by
    intro k t' h
    cases hs : st.tables[k]? with
    | some t =>
      left
      obtain ⟨u, hu, -, -, -, -, e5, e6, -⟩ := h1.frame.2.1 k t hs
      obtain ⟨u2, hu2, -, -, -, -, -, f6, -⟩ := h2.frame.2.1 k t hs
      rw [h] at hu hu2; cases hu; cases hu2
      refine ⟨t, rfl, ?_, e5⟩
      by_cases e : k = w1
      · exact f6 (fun e' => hne (e.symm.trans e'))
      · exact e6 e
    | none =>
      right
      refine ⟨?_, (h1.frame.2.2 k t' h hs).1⟩
      by_cases e : k = w1
      · exact h2.fresh k t' h hs (fun e' => hne (e.symm.trans e'))
      · exact h1.fresh k t' h hs e
  constructor
  · intro k t' h a ha
    rcases key k t' h with ⟨t, ht, e, -⟩ | ⟨e, -⟩
    · rw [e] at ha; exact hL.ans k t ht a ha
    · rw [e] at ha; cases ha
  · intro k t' h gs hgs
    rcases key k t' h with ⟨t, ht, -, e⟩ | ⟨-, e⟩
    · rw [e] at hgs; exact hL.held k t ht gs hgs
    · rw [e] at hgs; cases hgs

theorem Prov.quiet {w1 w2 : Nat} {st st' : StateOf R Rel (Ans D P)}
    (h1 : Inner K hK w1 st st') (h2 : Inner K hK w2 st st') (hne : w1 ≠ w2)
    (hP : Prov Q EA BadG st) : Prov Q EA BadG st' :=
  hP.imp (Esc.reach h1.reach) (Lit.quiet h1 h2 hne)

/-! ## Putting an answer in a table -/

/-- Putting an answer in a table keeps `Prov`, if the answer has `Q` or is
marked. -/
theorem prov_addAnswer (hR : Rules K hK Q EA) {st : StateOf R Rel (Ans D P)}
    (hP : Prov Q EA BadG st) (i : Nat) (a : Ans D P) (ha : Q a ∨ EA a) :
    Prov Q EA BadG (addAnswer (K := DerivationKernel.over D K hK P) i st a).val := by
  rcases hP with hE | hL
  · exact .inl (hE.reach (Reach.add st i a))
  rcases ha with ha | hb
  · right
    rw [addAnswer_val]
    have h1 : Lit Q (st.modify i (app [a])) :=
      hL.modify i _ (fun t ht x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hL.ans i t ht x hx
        · obtain rfl := List.mem_singleton.1 hx
          exact ha) (fun t ht gs hgs => hL.held i t ht gs hgs)
    split
    · exact hL
    · split
      · split
        · exact h1
        · exact h1.modify i _ (fun t ht x hx => by
            rcases List.mem_append.1 hx with hx | hx
            · exact h1.ans i t ht x hx
            · obtain rfl := List.mem_singleton.1 hx
              exact hR.swap a ha) (fun t ht gs hgs => h1.held i t ht gs hgs)
      · exact h1
  · cases ht : st.tables[i]? with
    | none =>
      have hno : ∀ (X : StateOf R Rel (Ans D P)) (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)),
          X.tables[i]? = none → Lit Q X → Lit Q (X.modify i f) ∧ (X.modify i f).tables[i]? = none :=
        fun X f hX hLX => ⟨hLX.modify i f (fun t ht' => by rw [hX] at ht'; cases ht')
          (fun t ht' => by rw [hX] at ht'; cases ht'), by
            unfold StateOf.modify; simp [hX]⟩
      right
      rw [addAnswer_val]
      split
      · exact hL
      · split
        · split
          · exact (hno _ _ ht hL).1
          · exact (hno _ _ (hno _ _ ht hL).2 (hno _ _ ht hL).1).1
        · exact (hno _ _ ht hL).1
    | some t =>
      rw [addAnswer_val]
      have h1 : Esc EA BadG (st.modify i (app [a])) :=
        ⟨i, app [a] t, by unfold StateOf.modify; simp [ht],
          .inr ⟨a, List.mem_append_right _ List.mem_cons_self, hb⟩⟩
      split
      · exact .inr hL
      · left
        split
        · split
          · exact h1
          · exact h1.modify i _ (fun _ => rfl) (fun t a h => List.mem_append_left _ h)
        · exact h1

theorem prov_addOption (hR : Rules K hK Q EA) {st : StateOf R Rel (Ans D P)}
    (hP : Prov Q EA BadG st) (i : Nat) (a : Option (Ans D P))
    (ha : ∀ c, a = some c → Q c ∨ EA c) :
    Prov Q EA BadG (addOption (K := DerivationKernel.over D K hK P) i st a).val := by
  cases a with
  | none => at_cost K hK; exact hP
  | some c =>
    have := prov_addAnswer (K := K) (hK := hK) hR hP i c (ha c rfl)
    at_cost K hK
    exact this

/-! ## The work of the strategies -/

omit [DecidableEq R] in
theorem esc_of_answer {st : StateOf R Rel (Ans D P)} {j : Nat} {a : Ans D P}
    (ha : a ∈ st.answers j) (he : EA a) : Esc EA BadG st := by
  unfold StateOf.answers at ha
  cases ht : st.tables[j]? with
  | none => rw [ht] at ha; cases ha
  | some t => rw [ht] at ha; exact ⟨j, t, ht, .inr ⟨a, ha, he⟩⟩

theorem prov_copyFrom (hR : Rules K hK Q EA) {st : StateOf R Rel (Ans D P)}
    (hP : Prov Q EA BadG st) (i : Nat) (g : GoalOf R Rel) (isCall : Bool) (m : Nat)
    (as : List (Ans D P)) (has : ∀ a ∈ as, Q a) (hin : ∀ a ∈ as, ∃ j, a ∈ st.answers j) :
    Prov Q EA BadG (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val := by
  by_cases hex : ∃ a ∈ as, EA a
  · obtain ⟨a, ha, he⟩ := hex
    obtain ⟨j, hj⟩ := hin a ha
    exact .inl ((esc_of_answer hj he).reach (reach_copyFrom i g isCall m st as))
  clear hin
  at_cost K hK
  refine foldL_inv (fun b : StateOf R Rel (Ans D P) => Prov Q EA BadG b) _ as
    (fun b a ha hb => ?_) st hP
  dsimp only
  split
  · rw [Cost.bind_val]
    refine prov_addOption hR hb i _ (fun c hc => ?_)
    rcases hR.unfold (has a ha) hc with h | h
    · exact absurd ⟨a, ha, h⟩ hex
    · exact .inl h
  · rw [Cost.bind_val]
    exact prov_addOption hR hb i _ (fun c hc => .inl (hR.inj (has a ha) hc))

theorem prov_joinPairs (hR : Rules K hK Q EA) {st : StateOf R Rel (Ans D P)}
    (hP : Prov Q EA BadG st) (i : Nat) (k : Kind) (xs ys : List (Ans D P))
    (ps : List (Nat × Nat)) (hx : ∀ x ∈ xs, Q x) (hy : ∀ y ∈ ys, Q y) :
    Prov Q EA BadG (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val := by
  at_cost K hK
  refine foldL_inv (fun b : StateOf R Rel (Ans D P) => Prov Q EA BadG b) _ ps
    (fun b p _ hb => ?_) st hP
  split
  · next x y ex ey =>
    rw [Cost.bind_val]
    exact prov_addOption hR hb i _ (fun c hc =>
      .inl (hR.both (hx x (List.mem_of_getElem? ex)) (hy y (List.mem_of_getElem? ey)) hc))
  · exact hb

theorem prov_pushTake (hR : Rules K hK Q EA) {st : StateOf R Rel (Ans D P)}
    (hP : Prov Q EA BadG st) (i : Nat) (k : Kind) (left : Bool) (x : Ans D P)
    (ys : List (Ans D P)) (hx : Q x) (hy : ∀ y ∈ ys, Q y) :
    Prov Q EA BadG (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val := by
  at_cost K hK
  refine foldL_inv (fun b : StateOf R Rel (Ans D P) => Prov Q EA BadG b) _ ys
    (fun b y hy' hb => ?_) st hP
  simp only [Cost.bind_val]
  exact prov_addOption hR hb i _ (fun c hc => .inl (hR.pushed hx (hy y hy') hc))

/-! ## The strategies of a goal hold nothing -/

theorem fresh_splitGroup (k : Kind) (L Rg : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    ∀ s ∈ (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.2.strats,
      s.held = [] := by
  at_cost K hK
  simp only [splitGroup, Cost.bind_val, Cost.pure_val]
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> rfl

theorem fresh_checkOf (st : StateOf R Rel (Ans D P)) (left : Bool) (side other : Rel) :
    ∀ s ∈ (checkOf @rd (K := DerivationKernel.over D K hK P) st left side other).val.2,
      s.held = [] := by
  at_cost K hK
  simp only [checkOf, Cost.bind_val, Cost.pure_val]
  intro s hs
  split at hs
  · cases hs
  · obtain rfl := List.mem_singleton.1 hs
    rfl

theorem fresh_chainGroups (g : GoalOf R Rel) (k : Nat) (st : StateOf R Rel (Ans D P)) :
    (∀ gr ∈ (chainGroups @rd (K := DerivationKernel.over D K hK P) g k st).val.2.1,
        ∀ s ∈ gr.strats, s.held = []) ∧
      ∀ s ∈ (chainGroups @rd (K := DerivationKernel.over D K hK P) g k st).val.2.2,
        s.held = [] := by
  have hsg := fun k L Rg st => fresh_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  have hck := fun st left side other =>
    fresh_checkOf (rd := @rd) (K := K) (hK := hK) (P := P) st left side other
  at_cost K hK
  refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) ×
      List (Strat Rel (Ans D P)) =>
    (∀ gr ∈ acc.2.1, ∀ s ∈ gr.strats, s.held = []) ∧ ∀ s ∈ acc.2.2, s.held = []) _ _
    (fun b i _ hb => ?_) (st, [], []) ⟨fun gr hgr => (by cases hgr), fun s hs => (by cases hs)⟩
  simp only [Cost.bind_val]
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    refine ⟨fun gr hgr s hs => ?_, fun s hs => ?_⟩
    · rcases List.mem_append.1 hgr with hgr | hgr
      · exact hb.1 gr hgr s hs
      · obtain rfl := List.mem_singleton.1 hgr
        exact hsg _ _ _ _ s hs
    · rcases List.mem_append.1 hs with hs | hs
      · rcases List.mem_append.1 hs with hs | hs
        · exact hb.2 s hs
        · exact hck _ _ _ _ s hs
      · exact hck _ _ _ _ s hs
  · exact hb

/-- The strategies a goal is given hold no answer. -/
theorem fresh_expand (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    ∀ gr ∈ (expand @rd (K := DerivationKernel.over D K hK P) g st).val.2, ∀ s ∈ gr.strats,
      s.held = [] := by
  have hsg := fun k L Rg st => fresh_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  have hcg := fun k st => fresh_chainGroups (rd := @rd) (K := K) (hK := hK) (P := P) g k st
  at_cost K hK
  simp only [expand, Cost.bind_val]
  split
  · intro gr hgr s hs
    obtain rfl := List.mem_singleton.1 hgr
    obtain rfl := List.mem_singleton.1 hs
    rfl
  · simp only [Cost.bind_val]
    split
    · intro gr hgr s hs
      obtain rfl := List.mem_singleton.1 hgr
      obtain rfl := List.mem_singleton.1 hs
      rfl
    · simp only [Cost.bind_val, Cost.pure_val]
      intro gr hgr s hs
      obtain rfl := List.mem_singleton.1 hgr
      obtain rfl := List.mem_singleton.1 hs
      rfl
  · simp only [Cost.bind_val, Cost.pure_val]
    intro gr hgr s hs
    obtain rfl := List.mem_singleton.1 hgr
    obtain rfl := List.mem_singleton.1 hs
    rfl
  · next xs hv =>
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨h2, h3⟩ := hcg xs.length st
    intro gr hgr s hs
    split at hgr
    · exact h2 gr hgr s hs
    · rcases List.mem_append.1 hgr with hgr | hgr
      · exact h2 gr hgr s hs
      · obtain rfl := List.mem_singleton.1 hgr
        exact h3 s hs
  · refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) =>
      ∀ gr ∈ acc.2, ∀ s ∈ gr.strats, s.held = []) _ _ (fun b i _ hb => ?_)
      (st, []) (fun gr hgr => by cases hgr)
    simp only [Cost.bind_val]
    split
    · simp only [Cost.bind_val, Cost.pure_val]
      intro gr hgr s hs
      rcases List.mem_append.1 hgr with hgr | hgr
      · exact hb gr hgr s hs
      · obtain rfl := List.mem_singleton.1 hgr
        exact hsg _ _ _ _ s hs
    · exact hb

/-! ## The work of one strategy -/

omit [DecidableEq R] in
theorem held_of_groupsAt {st : StateOf R Rel (Ans D P)} (hL : Lit Q st) {i k j : Nat}
    {s : Strat Rel (Ans D P)} (h : ((groupsAt st i)[k]?).bind (·.strats[j]?) = some s) :
    ∀ a ∈ s.held, Q a := by
  unfold groupsAt at h
  cases ht : st.tables[i]? with
  | none => rw [ht] at h; simp at h
  | some t =>
    rw [ht] at h
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
        exact hL.held i t ht gs hgs gr (List.mem_of_getElem? hgr) s (List.mem_of_getElem? h)

/-- One unit of the work of a strategy keeps `Prov`, and the strategy it
leaves holds answers that have `Q`, unless the run has escaped. -/
theorem prov_work (hR : Rules K hK Q EA) {st : StateOf R Rel (Ans D P)}
    (hP : Prov Q EA BadG st) (i : Nat) (g : GoalOf R Rel) (s : Strat Rel (Ans D P))
    (hs : Esc EA BadG st ∨ ∀ a ∈ s.held, Q a) :
    Prov Q EA BadG (work @rd (K := DerivationKernel.over D K hK P) i g st s).val.1 ∧
      (Esc EA BadG (work @rd (K := DerivationKernel.over D K hK P) i g st s).val.1 ∨
        ∀ a ∈ (work @rd (K := DerivationKernel.over D K hK P) i g st s).val.2.1.held, Q a) := by
  have hesc : Esc EA BadG st →
      Esc EA BadG (work @rd (K := DerivationKernel.over D K hK P) i g st s).val.1 :=
    Esc.reach (reach_work (rd := @rd) (K := K) (hK := hK) i g st s)
  rcases hs with hE | hs
  · exact ⟨.inl (hesc hE), .inl (hesc hE)⟩
  rcases hP with hE | hL
  · exact ⟨.inl (hesc hE), .inl (hesc hE)⟩
  clear hesc
  have hP : Prov Q EA BadG st := .inr hL
  at_cost K hK
  cases s with
  | span ran =>
    cases ran
    · simp only [work, Cost.bind_val, Cost.pure_val]
      exact ⟨prov_addOption hR hP i _ (fun c hc => .inl (hR.leaf hc)), .inr (held_nil_Q rfl)⟩
    · exact ⟨hP, .inr (held_nil_Q rfl)⟩
  | copy isCall subs =>
    simp only [work]
    split
    · exact ⟨hP, .inr (held_nil_Q rfl)⟩
    · next p hp =>
      simp only [Cost.bind_val, Cost.pure_val]
      exact ⟨(prov_copyFrom hR hP i g isCall p.2 _ (fun a ha =>
        hL.answers _ a (List.mem_of_mem_drop (List.mem_of_mem_take ha))) (fun a ha =>
        ⟨_, List.mem_of_mem_drop (List.mem_of_mem_take ha)⟩)).modify_same i _
          (fun _ => rfl) (fun _ => rfl), .inr (held_nil_Q rfl)⟩
  | join k a b c =>
    simp only [work]
    split
    · exact ⟨hP, .inr (held_nil_Q rfl)⟩
    · simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      exact ⟨(prov_joinPairs hR hP i k _ _ _ (hL.answers a) (hL.answers b)).modify_same i _
        (fun _ => rfl) (fun _ => rfl), .inr (held_nil_Q rfl)⟩
  | push k left side other subs dead reads c fc =>
    simp only [work, Cost.bind_val]
    generalize (superseded (K := DerivationKernel.over D _ hK P) st side dead).val = dead0
    generalize dead0.getD [] = dead'
    have hss := seeSide_subs (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
      reads c
    generalize seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
      reads c = f0 at hss ⊢
    have hfe := pushFile_getElem? st dead' f0.1 0 f0.2.1 (f0.2.2.kill dead')
    generalize pushFile st dead' 0 f0.2.1 (f0.2.2.kill dead') f0.1 = f at hfe ⊢
    have hf : ∀ e ∈ f.1, Q e.1 := by
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
        · exact hs e0.1 (List.mem_map.2 ⟨e0, hm, rfl⟩)
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
          exact hL.answers side _ (List.of_mem_zip (List.mem_of_mem_drop hy)).1
    have hheld : ∀ c' : Cursor, ∀ a ∈ (Strat.push k left side other f.1 dead0 f.2.1 c' fc).held,
        Q a := by
      intro c' a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact hf e he
    split
    · exact ⟨hP, .inr (hheld _)⟩
    · next p hp =>
      split
      · next x _ hx _ =>
        simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
        refine ⟨hP.quiet (inner_pushOpen (w := 0) _ _ _ _ _ _) (inner_pushOpen (w := 1) _ _ _ _ _ _)
          (by decide), .inr fun a ha => ?_⟩
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        rcases List.mem_or_eq_of_mem_set he with he | rfl
        · exact hf e he
        · exact hf (x, none) (List.mem_of_getElem? hx)
      · next x tb _ r hx _ =>
        simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
        exact ⟨(prov_pushTake hR hP i k left x _ (hf _ (List.mem_of_getElem? hx)) (fun y hy =>
          hL.answers tb.1 y (List.mem_of_mem_drop (List.mem_of_mem_take hy)))).modify_same i _
            (fun _ => rfl) (fun _ => rfl), .inr (hheld _)⟩
      · exact ⟨hP, .inr (hheld _)⟩
  | check left side other c =>
    have h1 : Prov Q EA BadG (edgeOf @rd (K := DerivationKernel.over D _ hK P) st left side).val.1 :=
      hP.quiet (inner_edgeOf (w := 0) _ _ _) (inner_edgeOf (w := 1) _ _ _) (by decide)
    cases c with
    | reading =>
      simp only [work, Cost.bind_val]
      split
      · exact ⟨h1, .inr (held_nil_Q rfl)⟩
      · exact ⟨h1, .inr (held_nil_Q rfl)⟩
      · simp only [Cost.bind_val, Cost.pure_val]
        exact ⟨h1.quiet (inner_checkOpen (w := 0) _ _ _ _ _) (inner_checkOpen (w := 1) _ _ _ _ _)
          (by decide), .inr (held_nil_Q rfl)⟩
    | off => exact ⟨hP, .inr (held_nil_Q rfl)⟩
    | opened subs => exact ⟨hP, .inr (held_nil_Q rfl)⟩

/-- A turn of a strategy keeps `Prov`, and the strategy it leaves holds
answers that have `Q`, unless the run has escaped. -/
theorem prov_turn (hR : Rules K hK Q EA) {st : StateOf R Rel (Ans D P)}
    (hP : Prov Q EA BadG st) (i : Nat) (g : GoalOf R Rel) (f left : Nat)
    (s : Strat Rel (Ans D P)) (c : Nat) (hs : Esc EA BadG st ∨ ∀ a ∈ s.held, Q a) :
    Prov Q EA BadG (turn @rd (K := DerivationKernel.over D K hK P) i g f left st s c).val.1 ∧
      (Esc EA BadG (turn @rd (K := DerivationKernel.over D K hK P) i g f left st s c).val.1 ∨
        ∀ a ∈ (turn @rd (K := DerivationKernel.over D K hK P) i g f left st s c).val.2.1.held,
          Q a) := by
  have h := turn_ind (rd := @rd) (K := K) (hK := hK) (P := P) i g
    (fun st' s' => Prov Q EA BadG st' ∧ (Esc EA BadG st' ∨ ∀ a ∈ s'.held, Q a))
    (fun st' s' h => prov_work (rd := @rd) hR h.1 i g s' h.2) f left st s c ⟨hP, hs⟩
  exact h

/-! ## A round -/

/-- The tables a group reads have their rounds, and its pushes are given
their feed cursors: `Prov` is kept. -/
theorem prov_feedGroup (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Prov Q EA BadG st → Prov Q EA BadG (adv h st).val.1)
    {X : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG X) (i k d : Nat) :
    Prov Q EA BadG (setGroup (feedGroup (K := DerivationKernel.over D K hK P) adv i k X d).val.1 i k
      fun gr => { gr with
        level := gr.level + (feedGroup (K := DerivationKernel.over D K hK P) adv i k X d).val.2.1,
        strats := reFeed gr.strats
          (feedGroup (K := DerivationKernel.over D K hK P) adv i k X d).val.2.2 }) := by
  have hf := feedGroup_keeps (K := K) (hK := hK) (P := P) adv (Prov Q EA BadG) hadv
    (fun h c Y hY => hY.modify_same h _ (fun _ => rfl) (fun _ => rfl)) i k X d hP
  refine hf.setGroup _ _ _ (.inr fun gr h s' hs' => ?_)
  obtain ⟨s, hs, e⟩ := mem_reFeed hs'
  rw [Strat.held_core e]
  exact h s hs

theorem prov_workGroup (hR : Rules K hK Q EA)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Prov Q EA BadG st → Prov Q EA BadG (adv h st).val.1)
    {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) (i : Nat) (g : GoalOf R Rel) (k : Nat) :
    Prov Q EA BadG (workGroup @rd (K := DerivationKernel.over D K hK P) adv i g k st).val.1 := by
  have hturn := fun (st : StateOf R Rel (Ans D P)) hP f left s c hs =>
    prov_turn (rd := @rd) (K := K) (hK := hK) (BadG := BadG) hR (st := st) hP i g f left s c hs
  have hf := fun X d (hX : Prov Q EA BadG X) =>
    prov_feedGroup (K := K) (hK := hK) (P := P) adv hadv hX i k d
  clear hR
  at_cost K hK
  simp only [workGroup, workStrats, Cost.bind_val, Cost.pure_val]
  refine Prov.modify_same ?_ i _ (fun _ => rfl) (fun _ => rfl)
  refine hf _ _ ?_
  · refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × Nat × Bool =>
      Prov Q EA BadG acc.1) _ _ (fun b j _ hb => ?_) (st, 0, false) hP
    split
    · exact hb
    · next s o hs =>
      simp only [Cost.bind_val, Cost.pure_val]
      generalize turnTicks * weight b.1 s - o = fl
      have hheld : Esc EA BadG b.1 ∨ ∀ a ∈ s.held, Q a := by
        rcases hb with hE | hL
        · exact .inl hE
        · exact .inr (held_of_groupsAt hL (pick_strat hs).1)
      obtain ⟨h1, h2⟩ := hturn b.1 hb fl fl s 0 hheld
      refine h1.setGroup _ _ _ ?_
      rcases h2 with h2 | h2
      · exact .inl h2
      · refine .inr fun gr h s' hs' => ?_
        rcases List.mem_or_eq_of_mem_set hs' with h' | rfl
        · exact h s' h'
        · exact h2

theorem prov_workLevel (hR : Rules K hK Q EA)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Prov Q EA BadG st → Prov Q EA BadG (adv h st).val.1)
    {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) (i : Nat) (g : GoalOf R Rel)
    (lv : Nat) :
    Prov Q EA BadG (workLevel @rd (K := DerivationKernel.over D K hK P) adv i g lv st).val.1 := by
  have hwg := fun (st : StateOf R Rel (Ans D P)) hP k =>
    prov_workGroup (rd := @rd) (K := K) (hK := hK) (BadG := BadG) hR adv hadv (st := st) hP i g k
  clear hR
  at_cost K hK
  refine foldL_inv (fun acc : StateOf R Rel (Ans D P) × Bool => Prov Q EA BadG acc.1) _ _
    (fun b p _ hb => ?_) (st, false) hP
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    exact hwg b.1 hb _
  · exact hb

theorem prov_prepare {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) (i : Nat)
    (t : Table R Rel (Ans D P)) :
    Prov Q EA BadG (prepare @rd (K := DerivationKernel.over D K hK P) i t st).val := by
  have h1 : Prov Q EA BadG (expand @rd (K := DerivationKernel.over D K hK P) t.goal st).val.1 :=
    hP.quiet (inner_expand (w := 0) _ _) (inner_expand (w := 1) _ _) (by decide)
  have h2 := fresh_expand (rd := @rd) (K := K) (hK := hK) (P := P) t.goal st
  at_cost K hK
  unfold prepare
  cases t.groups with
  | some _ => exact hP.modify_same i _ (fun _ => rfl) (fun _ => rfl)
  | none =>
    simp only [Cost.bind_val, Cost.pure_val]
    refine Prov.modify_same ?_ i _ (fun _ => rfl) (fun _ => rfl)
    refine h1.modify i _ (fun _ => rfl) (fun _ => rfl) (.inr fun t' _ gs hgs gr hgr s hs => ?_)
    cases hgs
    exact held_nil_Q (h2 gr hgr s hs)

/-- The race of a table keeps `Prov`, if the answers of a final verdict have
`Q` or are marked, when `BadG` does not mark the goal. -/
theorem prov_askRace (hR : Rules K hK Q EA) (U : GOracle R Rel (Ans D P) Cost)
    {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) (i : Nat) (g : GoalOf R Rel)
    (hg : goalAt st i = some g)
    (hU : ∀ n, ¬ BadG g → (U n g).val.1 = true → ∀ a ∈ (U n g).val.2, Q a ∨ EA a) :
    Prov Q EA BadG (askRace (K := DerivationKernel.over D K hK P) U i g st).val.1 := by
  obtain ⟨t, ht, hgt⟩ := goalAt_some hg
  by_cases hbad : BadG g
  · have hE : Esc EA BadG st := ⟨i, t, ht, .inl (by rw [hgt]; exact hbad)⟩
    exact .inl (hE.reach (reach_askRace U i g st))
  have hadd : ∀ n, (U n g).val.1 = true →
      Prov Q EA BadG (foldL (addAnswer (K := DerivationKernel.over D K hK P) i) st
        (U n g).val.2).val := fun n hfin =>
    (foldL_inv (fun b : StateOf R Rel (Ans D P) => Prov Q EA BadG b ∧ goalAt b i = some g) _ _
      (fun b x hx hb => ⟨prov_addAnswer hR hb.1 i x (hU n hbad hfin x hx),
        (Reach.add (K := _) (hK := hK) b i x).ext _ _ hb.2⟩) st ⟨hP, hg⟩).1
  rw [askRace_val]
  split
  · exact hP
  · split
    · exact hP
    · split
      · exact hP
      · split
        · split
          · next hfin => exact Prov.modify_same (hadd _ hfin) i _ (fun _ => rfl) (fun _ => rfl)
          · exact hP.modify_same i _ (fun _ => rfl) (fun _ => rfl)
        · exact hP.modify_same i _ (fun _ => rfl) (fun _ => rfl)

/-- **A round keeps `Prov`.** -/
theorem prov_advance (hR : Rules K hK Q EA) (U : GOracle R Rel (Ans D P) Cost)
    (hU : ∀ n g, ¬ BadG g → (U n g).val.1 = true → ∀ a ∈ (U n g).val.2, Q a ∨ EA a) :
    ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)), Prov Q EA BadG st →
      Prov Q EA BadG (advance @rd (K := DerivationKernel.over D K hK P) U fuel i st).val.1
  | 0, _, st, hP => by
    clear hR
    at_cost K hK
    exact hP
  | fuel + 1, i, st, hP => by
    have ih := fun h st => prov_advance hR U hU fuel h st
    have ihR := fun h st => reach_advance (rd := @rd) (K := K) (hK := hK) (P := P) U fuel h st
    have hrace := fun g (st : StateOf R Rel (Ans D P)) hP hg =>
      prov_askRace (K := K) (hK := hK) (BadG := BadG) hR U (st := st) hP i g hg (fun n => hU n g)
    have hprep := fun t => prov_prepare (rd := @rd) (K := K) (hK := hK) hP i t
    have hprepR := fun t => reach_prepare (rd := @rd) (K := K) (hK := hK) i t st
    have hlev := fun g lv (st : StateOf R Rel (Ans D P)) hP =>
      prov_workLevel (rd := @rd) (K := K) (hK := hK) (BadG := BadG) hR _ ih (st := st) hP i g lv
    have hlevR := fun g lv st =>
      reach_workLevel (rd := @rd) (K := K) (hK := hK) (P := P) _ ihR i g lv st
    clear hR
    at_cost K hK
    simp only [advance]
    split
    · exact hP
    · next t ht =>
      split
      · exact hP
      · split
        · exact hP
        · split
          · exact hP
          · simp only [Cost.bind_val, Cost.pure_val]
            have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
            refine Prov.modify_same ?_ i _ (fun _ => rfl) (fun _ => rfl)
            have key : ∀ X : StateOf R Rel (Ans D P),
                Prov Q EA BadG X ∧ goalAt X i = some t.goal →
                Prov Q EA BadG (askRace (K := DerivationKernel.over D _ hK P) U i t.goal
                  (X.modify i fun t =>
                    { t with
                      groups := t.groups.map fun gs =>
                        gs.filter fun gr => !gr.strats.all (Strat.dead X) })).val.1 := by
              rintro X ⟨hPX, hgX⟩
              refine hrace _ _ (Prov.dropGroups hPX i _) ?_
              refine Eq.trans ?_ hgX
              exact goalAt_modify _ i i _ fun _ => rfl
            refine key _ (foldL_inv (fun acc : StateOf R Rel (Ans D P) × Bool =>
              Prov Q EA BadG acc.1 ∧ goalAt acc.1 i = some t.goal) _ _
              (fun b lv _ hb => ?_) _ ⟨hprep t, (hprepR t).ext _ _ hg⟩)
            split
            · exact hb
            · exact ⟨hlev _ _ b.1 hb.1, (hlevR _ lv b.1).ext _ _ hb.2⟩

/-- **A request keeps `Prov`.** -/
theorem prov_request (hR : Rules K hK Q EA) (U : GOracle R Rel (Ans D P) Cost)
    (hU : ∀ n g, ¬ BadG g → (U n g).val.1 = true → ∀ a ∈ (U n g).val.2, Q a ∨ EA a)
    {st : StateOf R Rel (Ans D P)} (hP : Prov Q EA BadG st) :
    Prov Q EA BadG (request @rd (K := DerivationKernel.over D K hK P) U st).val.1 := by
  have h := fun (st : StateOf R Rel (Ans D P)) hP =>
    prov_advance (rd := @rd) (K := K) (hK := hK) hR U hU st.tables.length 0 st hP
  clear hR
  at_cost K hK
  simp only [request, Cost.bind_val, Cost.pure_val]
  have h0 : Prov Q EA BadG ({ st with round := st.round + 1 } : StateOf R Rel (Ans D P)) :=
    Prov.of_tables (st := st) rfl hP
  refine (h _ h0).of_map _ (fun j => List.getElem?_mapIdx) (fun j t => ?_) (fun j t => ?_)
  · split <;> rfl
  · split <;> rfl

/-- The first state has `Prov`: its table holds nothing. -/
theorem prov_init (root : Rel) :
    Prov Q EA BadG (init (K := DerivationKernel.over D K hK P) root).val := by
  at_cost K hK
  simp only [init, Cost.bind_val, Cost.pure_val]
  refine .inr ⟨fun j t h a ha => ?_, fun j t h gs hgs => ?_⟩
  · obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? h)
    cases ha
  · obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? h)
    cases hgs

end kernel

end Symmetric

end RwLog
