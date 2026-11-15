/-
# The table of a goal that is its own converse

The table of a goal that is its own converse holds the converse of every
answer it holds, at every moment, and no answer of a table covers a later
one (`root_reach`, from `Reach`). So what a request adds to the root table,
and the maximal answers of the table, are each a list of representatives
without repeats that holds the converse of each of its members: a list that
is a rearrangement of its own converses (`perm_map_swap`).

On a root node that is its own converse the machine therefore shows, at
every step, answers that are their own converses rearranged
(`selfConverse_of`): this is `CostedRuntime.SelfConverse`, what running on
one orientation asks of a machine (`Framework/Oriented.lean`). The theorem
is stated under one condition on the run, that every answer of the root
table is an answer of the root goal; the machine reports the answers of the
root goal only, and the converse of an answer of another goal could be one.
`Goals.lean` proves the condition.
-/
import RwLog.Rungs.Symmetric.Invariant
import RwLog.Rungs.Framework.Oriented
import RwLog.Rungs.Framework.Derivation
import RwLog.Kernel.DomainLaws
import RwLog.Rungs.Framework.GoalsVal

namespace RwLog

namespace Symmetric

open Traverse

export Goals (sameBound_val same_val indexFrom_val covB coversA_val maxima_val comb both_some
  covB_iff covB_refl covB_trans maxima_max maxima_same)

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## Lists of representatives -/

/-- No member of the list covers a later one. -/
def NoCov (D : Domain R) (L : List R) : Prop := L.Pairwise fun y x => D.covers y x = false

/-- The list holds the converse of each of its members. -/
def SwapClosed (L : List R) : Prop := ∀ y ∈ L, Answer.swap y ∈ L

omit [DecidableEq R] in
theorem SwapClosed.append {L L' : List R} (h : SwapClosed L) (h' : SwapClosed L') :
    SwapClosed (L ++ L') := fun y hy =>
  (List.mem_append.1 hy).elim (fun m => List.mem_append_left _ (h y m))
    fun m => List.mem_append_right _ (h' y m)

omit [Answer R] [DecidableEq R] in
/-- A new member that no member covers. -/
theorem NoCov.snoc {L : List R} {a : R} (h : NoCov D L) (ha : ∀ y ∈ L, D.covers y a = false) :
    NoCov D (L ++ [a]) :=
  List.pairwise_append.2 ⟨h, List.pairwise_singleton _ _, fun y hy x hx => by
    obtain rfl := List.mem_singleton.1 hx
    exact ha y hy⟩

section lawful

variable {M : Interp} (hL : D.Lawful M)
include hL

omit [DecidableEq R] in
theorem swap_swap (a : R) : Answer.swap (Answer.swap a) = a :=
  hL.canon _ _ (by rw [Answer.den_swap, Answer.den_swap]; rfl)

omit [DecidableEq R] in
theorem NoCov.nodup {L : List R} (h : NoCov D L) : L.Nodup :=
  h.imp fun {y x} hc e => by
    subst e
    rw [hL.covers_refl] at hc
    cases hc

omit [DecidableEq R] in
/-- A list without repeats that holds the converse of each member is a
rearrangement of the converses of its members. -/
theorem perm_map_swap {L : List R} (hn : L.Nodup) (hc : SwapClosed L) :
    L.Perm (L.map Answer.swap) := by
  have hinj : Function.Injective (Answer.swap : R → R) := fun a b e => by
    rw [← swap_swap hL a, e, swap_swap hL]
  refine (List.perm_ext_iff_of_nodup hn (hn.map hinj)).2 fun a => ?_
  rw [List.mem_map]
  constructor
  · exact fun h => ⟨_, hc a h, swap_swap hL a⟩
  · rintro ⟨b, hb, rfl⟩
    exact hc b hb

omit [DecidableEq R] in
/-- In a list that holds the converse of each member, a new member that no
member covers and whose converse is covered is its own converse. -/
theorem swap_eq_of_covered {L : List R} {a : R} (hc : SwapClosed L)
    (ha : ∀ y ∈ L, D.covers y a = false) (h : ∃ y ∈ L ++ [a], D.covers y (Answer.swap a) = true) :
    Answer.swap a = a := by
  obtain ⟨y, hy, hya⟩ := h
  rcases List.mem_append.1 hy with hy | hy
  · have := hL.covers_swap y (Answer.swap a)
    rw [swap_swap hL, hya, ha _ (hc y hy)] at this
    cases this
  · obtain rfl := List.mem_singleton.1 hy
    have h2 := hL.covers_swap y (Answer.swap y)
    rw [swap_swap hL, hya] at h2
    exact hL.covers_antisymm h2 hya

end lawful

omit [Answer R] [DecidableEq R] in
/-- What such a list shows is what its converses show. -/
theorem stepEquiv_swap {S : Sorts → Type} [∀ T, Answer (S T)] (T : Sorts) (M' : Interp)
    {L : List (S T)} (hp : L.Perm (L.map Answer.swap)) :
    StepEquiv M' (L.map (Sigma.mk T)) ((L.map (Sigma.mk T)).map Answer.swap) := by
  refine ⟨L.map (Sigma.mk T), ?_, List.forall₂_same.2 fun a _ => ⟨subset_rfl, subset_rfl⟩⟩
  rw [List.map_map]
  have := hp.map (Sigma.mk T)
  rw [List.map_map] at this
  exact this

/-! ## What the machine computes -/

/-- Put answers at the end of a table. -/
def app {S N A : Type} (blk : List A) (t : Table S N A) : Table S N A :=
  { t with answers := t.answers ++ blk }

theorem cores_get {S N A : Type} (st : StateOf S N A) {i : Nat} {g : GoalOf S N} {s : Bool}
    {L : List A} (h : st.cores[i]? = some (g, s, L)) :
    ∃ t, st.tables[i]? = some t ∧ t.goal = g ∧ t.self = s ∧ t.answers = L := by
  unfold StateOf.cores at h
  rw [List.getElem?_map] at h
  cases ht : st.tables[i]? with
  | none => rw [ht] at h; cases h
  | some t =>
    rw [ht] at h
    simp only [Option.map_some, Option.some.injEq, Table.core, Prod.mk.injEq] at h
    exact ⟨t, rfl, h.1, h.2.1, h.2.2⟩

theorem cores_modify_ne {S N A : Type} (st : StateOf S N A) {i j : Nat}
    (f : Table S N A → Table S N A) (h : i ≠ j) : (st.modify i f).cores[j]? = st.cores[j]? := by
  unfold StateOf.cores StateOf.modify
  simp only [List.getElem?_map, List.getElem?_modify, ite_eq_right h, id_map']

theorem cores_modify_app {S N A : Type} (st : StateOf S N A) (i : Nat) (blk : List A)
    {g : GoalOf S N} {s : Bool} {L : List A} (h : st.cores[i]? = some (g, s, L)) :
    (st.modify i (app blk)).cores[i]? = some (g, s, L ++ blk) := by
  obtain ⟨t, ht, rfl, rfl, rfl⟩ := cores_get st h
  unfold StateOf.cores StateOf.modify
  simp only [List.getElem?_map, List.getElem?_modify, ite_true, ht]
  rfl

section

variable (K : Kernel R Cost) (hK : K.Refines D)

theorem addOne_val (i : Nat) (st : StateOf R Rel (Ans D P)) (a : Ans D P) :
    (addOne (K := DerivationKernel.over D K hK P) i st a).val =
      if (st.answers i).any (fun y => covB D P y a) then (st, false)
      else (st.modify i (app [a]), true) := by
  have hc := coversA_val (P := P) K hK
  at_cost K hK
  simp only [addOne, Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val, hc]
  rfl

theorem addAnswer_val (i : Nat) (st : StateOf R Rel (Ans D P)) (a : Ans D P) :
    (addAnswer (K := DerivationKernel.over D K hK P) i st a).val =
      if (st.answers i).any (fun y => covB D P y a) then st
      else if (st.modify i (app [a])).isSelf i then
        (if ((st.modify i (app [a])).answers i).any (fun y => covB D P y (Ans.swapA D P a).val)
          then st.modify i (app [a])
          else (st.modify i (app [a])).modify i (app [(Ans.swapA D P a).val]))
      else st.modify i (app [a]) := by
  have h1 := addOne_val (P := P) K hK
  at_cost K hK
  unfold addAnswer
  simp only [Cost.bind_val, h1]
  split
  · rfl
  · simp only [Bool.true_and]
    split
    · simp only [Cost.bind_val, h1]
      split
      · rename_i h; exact (ite_eq_left h).symm
      · rename_i h; exact (ite_eq_right h).symm
    · rfl

/-! ## The table of a goal that is its own converse -/

omit [DecidableEq R] in
theorem any_covB_false {L : List (Ans D P)} {a : Ans D P}
    (h : ¬(L.any fun y => covB D P y a) = true) :
    ∀ y ∈ L.map Ans.span, D.covers y a.span = false := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  cases hc : D.covers z.span a.span with
  | false => rfl
  | true => exact absurd (List.any_eq_true.2 ⟨z, hz, hc⟩) h

variable {K hK}

/-- What `addAnswer` does to the table of a goal that is its own converse:
it puts at its end a list that holds the converse of each of its members,
and no answer of the table covers a later one. -/
theorem root_add {M : Interp} (hL : D.Lawful M) (st : StateOf R Rel (Ans D P)) (i : Nat)
    (a : Ans D P) {g : GoalOf R Rel} {L : List (Ans D P)} (h0 : st.cores[0]? = some (g, true, L))
    (hc : SwapClosed (L.map Ans.span)) (hn : NoCov D (L.map Ans.span)) :
    ∃ ext, (addAnswer (K := DerivationKernel.over D K hK P) i st a).val.cores[0]? =
        some (g, true, L ++ ext) ∧ SwapClosed (ext.map Ans.span) ∧
      NoCov D ((L ++ ext).map Ans.span) := by
  have hnil : ∃ ext, st.cores[0]? = some (g, true, L ++ ext) ∧ SwapClosed (ext.map Ans.span) ∧
      NoCov D ((L ++ ext).map Ans.span) :=
    ⟨[], by simpa using h0, (fun y hy => by cases hy), by simpa using hn⟩
  rw [addAnswer_val]
  by_cases hi : i = 0
  · subst hi
    obtain ⟨t, ht, -, hs, hA⟩ := cores_get st h0
    have eA : st.answers 0 = L := by unfold StateOf.answers; rw [ht]; exact hA
    have h1 := cores_modify_app st 0 [a] h0
    obtain ⟨t1, ht1, -, hs1, hA1⟩ := cores_get _ h1
    have eS1 : (st.modify 0 (app [a])).isSelf 0 = true := by
      unfold StateOf.isSelf; rw [ht1]; exact hs1
    have eA1 : (st.modify 0 (app [a])).answers 0 = L ++ [a] := by
      unfold StateOf.answers; rw [ht1]; exact hA1
    rw [eA, eS1, eA1]
    split
    · exact hnil
    · rename_i hna
      have hna' := any_covB_false hna
      have n1 : NoCov D ((L ++ [a]).map Ans.span) := by
        rw [List.map_append]; exact hn.snoc hna'
      simp only [ite_true]
      split
      · rename_i hcov
        obtain ⟨y, hy, hya⟩ := List.any_eq_true.1 hcov
        have e : Answer.swap a.span = a.span :=
          swap_eq_of_covered hL hc hna' ⟨y.span, by
            have := List.mem_map_of_mem (f := Ans.span) hy
            rwa [List.map_append] at this, hya⟩
        refine ⟨[a], h1, fun y hy => ?_, n1⟩
        obtain rfl := List.mem_singleton.1 hy
        rw [e]; exact hy
      · rename_i hncov
        refine ⟨[a, (Ans.swapA D P a).val], ?_, fun y hy => ?_, ?_⟩
        · have := cores_modify_app _ 0 [(Ans.swapA D P a).val] h1
          rwa [List.append_assoc] at this
        · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
          rcases hy with rfl | rfl
          · exact .inr rfl
          · exact .inl (swap_swap hL a.span)
        · have := n1.snoc (a := Answer.swap a.span) (by
            have := any_covB_false hncov
            exact this)
          have e : (L ++ [a, (Ans.swapA D P a).val]).map Ans.span =
              (L ++ [a]).map Ans.span ++ [Answer.swap a.span] := by
            simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.cons_append, List.nil_append]
            rfl
          rw [e]; exact this
  · split
    · exact hnil
    · split
      · split
        · rw [cores_modify_ne _ _ hi]; exact hnil
        · rw [cores_modify_ne _ _ hi, cores_modify_ne _ _ hi]; exact hnil
      · rw [cores_modify_ne _ _ hi]; exact hnil

/-- Whatever the engine does, the table of a goal that is its own converse
gains a list that holds the converse of each of its members, and no answer
of the table covers a later one. -/
theorem root_reach {M : Interp} (hL : D.Lawful M) {st st' : StateOf R Rel (Ans D P)}
    (h : Reach K hK st st') : ∀ (g : GoalOf R Rel) (L : List (Ans D P)),
      st.cores[0]? = some (g, true, L) → SwapClosed (L.map Ans.span) →
      NoCov D (L.map Ans.span) →
      ∃ ext, st'.cores[0]? = some (g, true, L ++ ext) ∧ SwapClosed (ext.map Ans.span) ∧
        NoCov D ((L ++ ext).map Ans.span) := by
  induction h with
  | refl st =>
    intro g L h0 hc hn
    exact ⟨[], by simpa using h0, (fun y hy => by cases hy), by simpa using hn⟩
  | trans _ _ ih₁ ih₂ =>
    intro g L h0 hc hn
    obtain ⟨e₁, h1, c1, n1⟩ := ih₁ g L h0 hc hn
    obtain ⟨e₂, h2, c2, n2⟩ := ih₂ g (L ++ e₁) h1 (by rw [List.map_append]; exact hc.append c1) n1
    exact ⟨e₁ ++ e₂, by rw [← List.append_assoc]; exact h2,
      by rw [List.map_append]; exact c1.append c2, by rw [← List.append_assoc]; exact n2⟩
  | same e _ =>
    intro g L h0 hc hn
    exact ⟨[], by rw [e]; simpa using h0, (fun y hy => by cases hy), by simpa using hn⟩
  | opened g' self e _ =>
    intro g L h0 hc hn
    refine ⟨[], ?_, (fun y hy => by cases hy), by simpa using hn⟩
    rw [e, List.getElem?_append_left (by
      rcases Nat.eq_zero_or_pos (StateOf.cores _).length with h | h
      · rw [List.length_eq_zero_iff.1 h] at h0; cases h0
      · exact h)]
    simpa using h0
  | add st i a =>
    intro g L h0 hc hn
    exact root_add hL st i a h0 hc hn

/-- The position the answers of the root table were emitted to does not move
within a request. -/
theorem reach_shown {st st' : StateOf R Rel (Ans D P)} (h : Reach K hK st st') :
    st'.shown = st.shown := by
  induction h with
  | refl => rfl
  | trans _ _ a b => exact b.trans a
  | same _ e => exact e
  | opened _ _ _ e => exact e
  | add st i a =>
    rw [addAnswer_val]
    split
    · rfl
    · split
      · split <;> rfl
      · rfl

/-! ## The maximal answers -/

omit [DecidableEq R] in
/-- The maximal answers of a table that holds the converse of each answer:
their representatives have no repeats and hold the converse of each. -/
theorem maxima_swapClosed {M : Interp} (hL : D.Lawful M) {L : List (Ans D P)}
    (hc : SwapClosed (L.map Ans.span)) :
    ((L.maximaBy (covB D P)).map Ans.span).Nodup ∧
      SwapClosed ((L.maximaBy (covB D P)).map Ans.span) := by
  have hr : ∀ a : Ans D P, covB D P a a = true := fun a => hL.covers_refl _
  constructor
  · refine List.pairwise_map.2 ((List.maximaBy_pairwise (cov := covB D P) L).imp ?_)
    rintro y x ⟨h, -⟩ e
    rw [covB, e, hL.covers_refl] at h
    cases h
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    have hxt := List.mem_tops.1 (List.mem_thin (cov := covB D P) hx)
    obtain ⟨z, hz, ez⟩ := List.mem_map.1 (hc _ (List.mem_map_of_mem hxt.1))
    have hzt : z ∈ List.tops (covB D P) L := by
      refine List.mem_tops.2 ⟨hz, fun y hy hyz => ?_⟩
      obtain ⟨y', hy', ey⟩ := List.mem_map.1 (hc _ (List.mem_map_of_mem (f := Ans.span) hy))
      have h1 : covB D P y' x = true := by
        have := hL.covers_swap (Answer.swap y.span) x.span
        rw [swap_swap hL, ← ez] at this
        rw [covB, ey, ← this]; exact hyz
      have h2 := hxt.2 y' hy' h1
      have := hL.covers_swap x.span (Answer.swap y.span)
      rw [swap_swap hL, ← ez, ← ey] at this
      rw [covB, this]; exact h2
    obtain ⟨w, hw, hwz⟩ := List.thin_covers hr hzt
    have hzw := (List.mem_tops.1 hzt).2 w (List.mem_maximaBy hw) hwz
    have e : w.span = z.span := hL.covers_antisymm hwz hzw
    rw [← ez, ← e]
    exact List.mem_map_of_mem hw

/-! ## A step -/

variable (K hK)

theorem step_val (U : GOracle R Rel (Ans D P) Cost) (st : StateOf R Rel (Ans D P))
    {t : Table R Rel (Ans D P)} (h : st.tables.head? = some t) :
    (step (K := DerivationKernel.over D K hK P) U st).val =
      if t.done then .done (t.answers.maximaBy (covB D P))
      else .emit (request (K := DerivationKernel.over D K hK P) U st).val.2
        (request (K := DerivationKernel.over D K hK P) U st).val.1 := by
  have hm := maxima_val (P := P) K hK
  at_cost K hK
  unfold step
  rw [h]
  dsimp only
  split
  · simp only [Cost.bind_val, Cost.pure_val, hm]
  · simp only [Cost.bind_val, Cost.pure_val]

/-- The first state on a root that is its own converse. -/
theorem init_cores {root : Rel} (h : root.normConv = root) :
    (init (K := DerivationKernel.over D K hK P) root).val.cores[0]? =
        some (⟨none, root, none⟩, true, []) ∧
      (init (K := DerivationKernel.over D K hK P) root).val.shown = 0 := by
  at_cost K hK
  have e : (Charged.eqNode (Charged.convNode root).val root).val = true := decide_eq_true h
  simp [init, selfConverse, sameBound, Cost.bind_val, Cost.pure_val, StateOf.cores, Table.core]
  exact e

theorem filterMap_rootSpan {root : Rel} {L : List (Ans D P)}
    (h : ∀ a ∈ L, a.goal = ⟨none, root, none⟩) :
    L.filterMap (Ans.rootSpan root) = L.map Ans.span := by
  rw [List.filterMap_congr (g := some ∘ Ans.span) fun a ha => by
    simp only [Ans.rootSpan, h a ha, ite_true, Function.comp]]
  rw [List.filterMap_eq_map]

end

/-! ## What the machine shows -/

section run

variable (U : Unfolder) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))

/-- The unfolding race at the kernel of a program. -/
abbrev UAt (P : Program) : GOracle (R P.sorts) Rel (Ans (dom P.sorts) P) Cost :=
  @U (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
    (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P)

/-- The state of the engine in a state of the machine. -/
abbrev stOf (s : (engine @U).StateAt dom) : StateOf (R s.P.sorts) Rel (Ans (dom s.P.sorts) s.P) := s.st

/-- The root table is the table of a goal that is its own converse, it holds
the converse of each of its answers, none of them covers a later one, and
all of them have been emitted. -/
def RootSelf (s : (engine @U).StateAt dom) : Prop :=
  ∃ g L, (stOf @U dom s).cores[0]? = some (g, true, L) ∧ SwapClosed (L.map Ans.span) ∧
    NoCov (dom s.P.sorts) (L.map Ans.span) ∧ (stOf @U dom s).shown = L.length

/-- Every answer of the root table is an answer of the root goal. -/
def RootGoals (s : (engine @U).StateAt dom) : Prop :=
  ∀ a ∈ (stOf @U dom s).answers 0, a.goal = ⟨none, s.root, none⟩

theorem costed_step_val (s : (engine @U).StateAt dom)
    {t : Table (R s.P.sorts) Rel (Ans (dom s.P.sorts) s.P)}
    (h : (stOf @U dom s).tables.head? = some t) :
    (((engine @U).costedAt dom K hK).step s).val =
      if t.done then
        .done (((t.answers.maximaBy (covB (dom s.P.sorts) s.P)).filterMap
          (Ans.rootSpan s.root)).map (Sigma.mk s.P.sorts))
      else
        .emit (((request (K := DerivationKernel.over (dom s.P.sorts) (K s.P.sorts) (hK s.P.sorts)
            s.P) (UAt @U dom K hK s.P) (stOf @U dom s)).val.2.filterMap (Ans.rootSpan s.root)).map (Sigma.mk s.P.sorts))
          ⟨s.P, s.root, (request (K := DerivationKernel.over (dom s.P.sorts) (K s.P.sorts)
            (hK s.P.sorts) s.P) (UAt @U dom K hK s.P) (stOf @U dom s)).val.1⟩ := by
  rw [Engine.costedAt_step_val]
  have := step_val (K s.P.sorts) (hK s.P.sorts) (P := s.P) (UAt @U dom K hK s.P) (stOf @U dom s) h
  cases hd : t.done <;> rw [hd] at this <;> erw [this] <;> rfl

variable {U dom K hK}

/-- From a state whose root table is the table of a goal that is its own
converse, every step shows a list of answers that is a rearrangement of its
converses. `Good` is any property of the states of a run under which every
answer of the root table is an answer of the root goal. -/
theorem trace_selfConverse (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
    (Good : (engine @U).StateAt dom → Prop) (hroot : ∀ s, Good s → RootGoals @U dom s)
    (hstep : ∀ s as s', Good s → (((engine @U).costedAt dom K hK).step s).val = .emit as s' →
      Good s') :
    ∀ (n : Nat) (s : (engine @U).StateAt dom), s.P.sorts.WellFormed → Good s → RootSelf @U dom s →
      TraceEquiv s.P.sorts.interp (((engine @U).costedAt dom K hK).runtime.trace s n)
        ((((engine @U).costedAt dom K hK).runtime.trace s n).map Shown.swap)
  | 0, _, _, _, _ => List.Forall₂.nil
  | n + 1, s, hwf, hg, hr => by
    have hL := hD _ hwf
    obtain ⟨g, L, h0, hc, hn, hsh⟩ := hr
    obtain ⟨t, ht, -, -, hA⟩ := cores_get _ h0
    have hhead : (stOf @U dom s).tables.head? = some t := by rw [List.head?_eq_getElem?]; exact ht
    have hs := costed_step_val @U dom K hK s hhead
    have eA : (stOf @U dom s).answers 0 = L := by unfold StateOf.answers; rw [ht]; exact hA
    cases hd : t.done with
    | true =>
      rw [hd] at hs
      simp only [ite_true] at hs
      subst hA
      have hm := maxima_swapClosed (P := s.P) hL hc
      have hgoal : ∀ a ∈ t.answers.maximaBy (covB (dom s.P.sorts) s.P),
          a.goal = ⟨none, s.root, none⟩ := fun a ha =>
        hroot s hg a (by rw [eA]; exact List.mem_maximaBy ha)
      rw [filterMap_rootSpan hgoal] at hs
      have e : ((engine @U).costedAt dom K hK).runtime.trace s (n + 1) =
          [.final (((t.answers.maximaBy (covB (dom s.P.sorts) s.P)).map Ans.span).map
            (Sigma.mk s.P.sorts))] := by
        have hs' : ((engine @U).costedAt dom K hK).runtime.step s = _ := hs
        simp only [Runtime.trace, hs']
        rfl
      rw [e]
      exact List.Forall₂.cons (stepEquiv_swap _ _ (perm_map_swap hL hm.1 hm.2)) .nil
    | false =>
      rw [hd] at hs
      simp only [Bool.false_eq_true, ite_false] at hs
      obtain ⟨st', hre, hreq⟩ := reach_request (K := K s.P.sorts) (hK := hK s.P.sorts)
        (UAt @U dom K hK s.P) (stOf @U dom s)
      rw [hreq] at hs
      obtain ⟨ext, h1, c1, n1⟩ := root_reach hL hre g L h0 hc hn
      have hsh' := reach_shown hre
      obtain ⟨t', ht', -, -, hA'⟩ := cores_get _ h1
      have eA' : st'.answers 0 = L ++ ext := by unfold StateOf.answers; rw [ht']; exact hA'
      have enew : (st'.answers 0).drop st'.shown = ext := by
        rw [eA', hsh', hsh, List.drop_left]
      have hg' := hstep s _ _ hg hs
      have hgoal : ∀ a ∈ ext, a.goal = ⟨none, s.root, none⟩ := fun a ha =>
        hroot _ hg' a (by
          show a ∈ st'.answers 0
          rw [eA']; exact List.mem_append_right _ ha)
      simp only [enew, filterMap_rootSpan hgoal] at hs hg'
      have hr' : RootSelf @U dom ⟨s.P, s.root, { st' with shown := (st'.answers 0).length }⟩ :=
        ⟨g, L ++ ext, h1, by rw [List.map_append]; exact hc.append c1, n1, by
          show (st'.answers 0).length = _
          rw [eA']⟩
      have ih := trace_selfConverse hD Good hroot hstep n
        ⟨s.P, s.root, { st' with shown := (st'.answers 0).length }⟩ hwf hg' hr'
      have e : ((engine @U).costedAt dom K hK).runtime.trace s (n + 1) =
          .answers ((ext.map Ans.span).map (Sigma.mk s.P.sorts)) ::
            ((engine @U).costedAt dom K hK).runtime.trace
              ⟨s.P, s.root, { st' with shown := (st'.answers 0).length }⟩ n := by
        have hs' : ((engine @U).costedAt dom K hK).runtime.step s = _ := hs
        simp only [Runtime.trace, hs']
        rfl
      rw [e]
      have hnd : (ext.map Ans.span).Nodup := by
        have := NoCov.nodup hL n1
        rw [List.map_append] at this
        exact this.of_append_right
      exact List.Forall₂.cons (stepEquiv_swap _ _ (perm_map_swap hL hnd c1)) ih

/-- **The run on a root that is its own converse.** If every answer of the
root table is an answer of the root goal throughout a run (`Good`), then on a
root node that is its own converse the symmetric engine shows, at every
step, a list of answers that is a rearrangement of its converses. -/
theorem selfConverse_of (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
    (Good : (engine @U).StateAt dom → Prop) (hroot : ∀ s, Good s → RootGoals @U dom s)
    (hinit : ∀ (P : Program) (root : Rel), P.sorts.WellFormed → ProgFO P → Normal root →
      root.FO → Good (((engine @U).costedAt dom K hK).start P root))
    (hstep : ∀ s as s', Good s → (((engine @U).costedAt dom K hK).step s).val = .emit as s' →
      Good s') :
    ((engine @U).costedAt dom K hK).SelfConverse := by
  intro P root hwf hP hN hfo hself n
  refine trace_selfConverse hD Good hroot hstep n _ hwf (hinit P root hwf hP hN hfo) ?_
  have h := init_cores (P := P) (K P.sorts) (hK P.sorts) (root := root.norm)
    (by rw [hN.norm_eq]; exact hself)
  exact ⟨_, [], h.1, (fun y hy => by cases hy), List.Pairwise.nil, h.2⟩

end run

end Symmetric

end RwLog
