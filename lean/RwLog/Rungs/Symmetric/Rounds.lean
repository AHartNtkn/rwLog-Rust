/-
# A complete table never changes again

What a round of the symmetric engine keeps (`Keep`): the number of requests;
every table, with its goal and the request it was opened in; the answers a
table has, to which more may be added at the end; a complete table, which
stays complete and gains no answer; and a table that has had its round in
this request and is not complete, which is not marked complete by anyone
else's round. The last is what lets the strategies of a table put answers
into it during its round: nothing nested in the round completes it.

`Stable` is the part of this that holds from one request to the next, and
`stable_request` is the theorem for a whole request.
-/
import RwLog.Rungs.Symmetric.Goals
import RwLog.Rungs.Symmetric.SelfConverse

namespace RwLog

namespace Symmetric

open Traverse

section pure

variable {S N A : Type}

/-- The second state has the tables of the first, each with the same goal,
the same marks, the same requests and the same groups, and with the same
answers except that the table at `j` may have gained some at its end. A
table the first state does not have is new: opened in this request, not
complete, and with no groups yet. -/
def Frame (j : Nat) (st st' : StateOf S N A) : Prop :=
  st'.round = st.round ∧
  (∀ (k : Nat) (t : Table S N A), st.tables[k]? = some t →
    ∃ t' : Table S N A, st'.tables[k]? = some t' ∧
    t'.goal = t.goal ∧ t'.done = t.done ∧ t'.stamp = t.stamp ∧ t'.born = t.born ∧
    t'.groups = t.groups ∧ (k ≠ j → t'.answers = t.answers) ∧ t.answers <+: t'.answers) ∧
  ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → st.tables[k]? = none →
    t'.groups = none ∧ t'.born = st.round ∧ t'.done = false

theorem Frame.refl (j : Nat) (st : StateOf S N A) : Frame j st st :=
  ⟨rfl, fun _ t h => ⟨t, h, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, List.prefix_refl _⟩,
    fun _ _ h h' => by rw [h] at h'; cases h'⟩

theorem Frame.trans {j : Nat} {a b c : StateOf S N A} (h₁ : Frame j a b) (h₂ : Frame j b c) :
    Frame j a c := by
  refine ⟨h₂.1.trans h₁.1, fun k t h => ?_, fun k t'' h'' hn => ?_⟩
  · obtain ⟨t', h', e1, e2, e3, e4, e5, e6, e7⟩ := h₁.2.1 k t h
    obtain ⟨t'', h'', f1, f2, f3, f4, f5, f6, f7⟩ := h₂.2.1 k t' h'
    exact ⟨t'', h'', f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5,
      fun hk => (f6 hk).trans (e6 hk), e7.trans f7⟩
  · cases hb : b.tables[k]? with
    | none =>
      obtain ⟨g1, g2, g3⟩ := h₂.2.2 k t'' h'' hb
      exact ⟨g1, g2.trans h₁.1, g3⟩
    | some t' =>
      obtain ⟨g1, g2, g3⟩ := h₁.2.2 k t' hb hn
      obtain ⟨u, hu, -, f2, -, f4, f5, -, -⟩ := h₂.2.1 k t' hb
      rw [h''] at hu
      cases hu
      exact ⟨f5.trans g1, f4.trans g2, f2.trans g3⟩

/-- Tables with the same frame. -/
theorem frame_eq {t t' : Table S N A} (e : t'.frame = t.frame) :
    t'.goal = t.goal ∧ t'.done = t.done ∧ t'.stamp = t.stamp ∧ t'.born = t.born ∧
      t'.groups = t.groups ∧ t'.answers = t.answers := by
  simp only [Table.frame, Prod.mk.injEq] at e
  exact ⟨e.1, e.2.2.2.1, e.2.2.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2.2, e.2.2.1⟩

/-- States with the same frames. -/
theorem Frame.of_frames {j : Nat} {st st' : StateOf S N A} (h : st'.frames = st.frames)
    (hr : st'.round = st.round) : Frame j st st' := by
  have e : ∀ k, (st'.tables[k]?).map Table.frame = (st.tables[k]?).map Table.frame := fun k => by
    rw [← List.getElem?_map, ← List.getElem?_map]
    show st'.frames[k]? = st.frames[k]?
    rw [h]
  refine ⟨hr, fun k t hk => ?_, fun k t' hk hn => ?_⟩
  · have := e k
    rw [hk] at this
    cases ht : st'.tables[k]? with
    | none => rw [ht] at this; cases this
    | some t' =>
      rw [ht] at this
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := frame_eq (Option.some.inj this)
      exact ⟨t', rfl, e1, e2, e3, e4, e5, fun _ => e6, by rw [e6]⟩
  · have := e k
    rw [hk, hn] at this
    cases this

/-- A state with one more table, opened in this request. -/
theorem Frame.of_opened {j : Nat} {st st' : StateOf S N A} {g : GoalOf S N} {self : Bool}
    (h : st'.frames = st.frames ++ [(g, self, [], false, st.round, 0, none)])
    (hr : st'.round = st.round) : Frame j st st' := by
  have e : ∀ k, (st'.tables[k]?).map Table.frame =
      (st.frames ++ [(g, self, [], false, st.round, 0, none)])[k]? := fun k => by
    rw [← List.getElem?_map]
    show st'.frames[k]? = _
    rw [h]
  have hlen : st.frames.length = st.tables.length := by simp [StateOf.frames]
  refine ⟨hr, fun k t hk => ?_, fun k t' hk hn => ?_⟩
  · have hlt : k < st.frames.length := by
      rw [hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
    have := e k
    rw [List.getElem?_append_left hlt] at this
    unfold StateOf.frames at this
    rw [List.getElem?_map, hk] at this
    cases ht : st'.tables[k]? with
    | none => rw [ht] at this; cases this
    | some t' =>
      rw [ht] at this
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := frame_eq (Option.some.inj this)
      exact ⟨t', rfl, e1, e2, e3, e4, e5, fun _ => e6, by rw [e6]⟩
  · have hge : st.frames.length ≤ k := by
      rw [hlen]; exact List.getElem?_eq_none_iff.1 hn
    have := e k
    rw [hk, List.getElem?_append_right hge] at this
    cases hx : ([(g, self, ([] : List A), false, st.round, 0,
        (none : Option (List (Group N A))))])[k - st.frames.length]? with
    | none => rw [hx] at this; cases this
    | some x =>
      rw [hx] at this
      obtain rfl := List.mem_singleton.1 (List.mem_of_getElem? hx)
      simp only [Option.map_some, Option.some.injEq, Table.frame, Prod.mk.injEq] at this
      exact ⟨this.2.2.2.2.2.2, this.2.2.2.2.1, this.2.2.2.1⟩

/-- Answers put at the end of the table at `j`. -/
theorem Frame.of_app (j : Nat) (st : StateOf S N A) (blk : List A) :
    Frame j st (st.modify j (app blk)) := by
  refine ⟨rfl, fun k t hk => ?_, fun k t' hk hn => ?_⟩
  · unfold StateOf.modify
    simp only [List.getElem?_modify, hk]
    by_cases e : j = k
    · subst e
      exact ⟨app blk t, by simp, rfl, rfl, rfl, rfl, rfl, fun h => absurd rfl h,
        List.prefix_append _ _⟩
    · exact ⟨t, by simp [e], rfl, rfl, rfl, rfl, rfl, fun _ => rfl, List.prefix_refl _⟩
  · unfold StateOf.modify at hk
    simp only [List.getElem?_modify, hn] at hk
    cases hk

/-- What a round keeps. -/
def Keep (st st' : StateOf S N A) : Prop :=
  st'.round = st.round ∧
  (∀ (k : Nat) (t : Table S N A), st.tables[k]? = some t →
    ∃ t' : Table S N A, st'.tables[k]? = some t' ∧
    t'.goal = t.goal ∧ t'.born = t.born ∧ t.answers <+: t'.answers ∧
    (t.done = true → t'.done = true ∧ t'.answers = t.answers) ∧
    (t.stamp = st.round → t'.stamp = st.round ∧ (t.done = false → t'.done = false))) ∧
  ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → st.tables[k]? = none →
    t'.born = st.round

theorem Keep.refl (st : StateOf S N A) : Keep st st :=
  ⟨rfl, fun _ t h => ⟨t, h, rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩,
    fun h => ⟨h, fun h => h⟩⟩, fun _ _ h h' => by rw [h] at h'; cases h'⟩

theorem Keep.trans {a b c : StateOf S N A} (h₁ : Keep a b) (h₂ : Keep b c) : Keep a c := by
  refine ⟨h₂.1.trans h₁.1, fun k t h => ?_, fun k t'' h'' hn => ?_⟩
  · obtain ⟨t', h', e1, e2, e3, e4, e5⟩ := h₁.2.1 k t h
    obtain ⟨t'', h'', f1, f2, f3, f4, f5⟩ := h₂.2.1 k t' h'
    refine ⟨t'', h'', f1.trans e1, f2.trans e2, e3.trans f3, fun hd => ?_, fun hs => ?_⟩
    · obtain ⟨d1, a1⟩ := e4 hd
      obtain ⟨d2, a2⟩ := f4 d1
      exact ⟨d2, a2.trans a1⟩
    · obtain ⟨s1, o1⟩ := e5 hs
      obtain ⟨s2, o2⟩ := f5 (by rw [s1, h₁.1])
      exact ⟨by rw [s2, h₁.1], fun hd => o2 (o1 hd)⟩
  · cases hb : b.tables[k]? with
    | none => exact (h₂.2.2 k t'' h'' hb).trans h₁.1
    | some t' =>
      obtain ⟨u, hu, -, f2, -, -, -⟩ := h₂.2.1 k t' hb
      rw [h''] at hu
      cases hu
      exact f2.trans (h₁.2.2 k t' hb hn)

/-- Work that adds answers to an open table only keeps what a round keeps. -/
theorem Frame.keep {j : Nat} {st st' : StateOf S N A} (h : Frame j st st')
    (hj : ∀ t, st.tables[j]? = some t → t.done = false) : Keep st st' := by
  refine ⟨h.1, fun k t hk => ?_, fun k t' hk hn => (h.2.2 k t' hk hn).2.1⟩
  obtain ⟨t', h', e1, e2, e3, e4, -, e5, e6⟩ := h.2.1 k t hk
  refine ⟨t', h', e1, e4, e6, fun hd => ⟨by rw [e2, hd], e5 fun e => ?_⟩,
    fun hs => ⟨by rw [e3, hs], fun hd => by rw [e2, hd]⟩⟩
  subst e
  rw [hj t hk] at hd
  cases hd

/-- The table at `i` has had its round in this request and is not complete. -/
def Busy (st : StateOf S N A) (i : Nat) : Prop :=
  ∃ t, st.tables[i]? = some t ∧ t.stamp = st.round ∧ t.done = false

theorem Keep.busy {st st' : StateOf S N A} (h : Keep st st') {i : Nat} (hb : Busy st i) :
    Busy st' i := by
  obtain ⟨t, ht, hs, hd⟩ := hb
  obtain ⟨t', h', -, -, -, -, e5⟩ := h.2.1 i t ht
  exact ⟨t', h', by rw [(e5 hs).1, h.1], (e5 hs).2 hd⟩

theorem Busy.open {st : StateOf S N A} {i : Nat} (hb : Busy st i) :
    ∀ t, st.tables[i]? = some t → t.done = false := by
  obtain ⟨t, ht, -, hd⟩ := hb
  intro t' ht'
  rw [ht] at ht'
  cases ht'
  exact hd

/-- What holds from one request to the next: every table stays, with its
goal and the request it was opened in; its answers stay, with more at the
end; a complete table stays complete and gains none. -/
def Stable (st st' : StateOf S N A) : Prop :=
  ∀ (k : Nat) (t : Table S N A), st.tables[k]? = some t →
    ∃ t' : Table S N A, st'.tables[k]? = some t' ∧
    t'.goal = t.goal ∧ t'.born = t.born ∧ t.answers <+: t'.answers ∧
    (t.done = true → t'.done = true ∧ t'.answers = t.answers)

theorem Keep.stable {st st' : StateOf S N A} (h : Keep st st') : Stable st st' := fun k t hk => by
  obtain ⟨t', h', e1, e2, e3, e4, -⟩ := h.2.1 k t hk
  exact ⟨t', h', e1, e2, e3, e4⟩

theorem Stable.refl (st : StateOf S N A) : Stable st st :=
  fun _ t h => ⟨t, h, rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩⟩

theorem Stable.trans {a b c : StateOf S N A} (h₁ : Stable a b) (h₂ : Stable b c) :
    Stable a c := fun k t h => by
  obtain ⟨t', h', e1, e2, e3, e4⟩ := h₁ k t h
  obtain ⟨t'', h'', f1, f2, f3, f4⟩ := h₂ k t' h'
  refine ⟨t'', h'', f1.trans e1, f2.trans e2, e3.trans f3, fun hd => ?_⟩
  obtain ⟨d1, a1⟩ := e4 hd
  obtain ⟨d2, a2⟩ := f4 d1
  exact ⟨d2, a2.trans a1⟩

/-- Changing one table keeps what a round keeps, if the change does. -/
theorem keep_modify (st : StateOf S N A) (i : Nat) (f : Table S N A → Table S N A)
    (hf : ∀ t, st.tables[i]? = some t → (f t).goal = t.goal ∧ (f t).born = t.born ∧
      (f t).answers = t.answers ∧ (t.done = true → (f t).done = true) ∧
      (t.stamp = st.round → (f t).stamp = st.round ∧ (t.done = false → (f t).done = false))) :
    Keep st (st.modify i f) := by
  refine ⟨rfl, fun k t hk => ?_, fun k t' hk hn => ?_⟩
  · unfold StateOf.modify
    simp only [List.getElem?_modify, hk]
    by_cases e : i = k
    · subst e
      obtain ⟨h1, h2, h3, h4, h5⟩ := hf t hk
      exact ⟨f t, by simp, h1, h2, by rw [h3], fun hd => ⟨h4 hd, h3⟩, h5⟩
    · exact ⟨t, by simp [e], rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩,
        fun h => ⟨h, fun h => h⟩⟩
  · unfold StateOf.modify at hk
    simp only [List.getElem?_modify, hn] at hk
    cases hk

/-- After a round, the table that had it may be marked: it had not had its
round before, so nothing is promised of its mark. -/
theorem keep_mark {st mid : StateOf S N A} (h : Keep st mid) {i : Nat} {t : Table S N A}
    (ht : st.tables[i]? = some t) (hs : t.stamp ≠ st.round) (hd : t.done = false)
    (f : Table S N A → Table S N A)
    (hf : ∀ t, (f t).goal = t.goal ∧ (f t).born = t.born ∧ (f t).answers = t.answers ∧
      (f t).stamp = t.stamp ∧ (t.done = true → (f t).done = true)) :
    Keep st (mid.modify i f) := by
  refine ⟨h.1, fun k u hk => ?_, fun k u' hk hn => ?_⟩
  · obtain ⟨u', hu', e1, e2, e3, e4, e5⟩ := h.2.1 k u hk
    unfold StateOf.modify
    simp only [List.getElem?_modify, hu']
    by_cases e : i = k
    · subst e
      rw [ht] at hk
      cases hk
      obtain ⟨h1, h2, h3, -, -⟩ := hf u'
      exact ⟨f u', by simp, h1.trans e1, h2.trans e2, by rw [h3]; exact e3,
        (fun h => by rw [hd] at h; cases h), fun h => absurd h hs⟩
    · exact ⟨u', by simp [e], e1, e2, e3, e4, e5⟩
  · unfold StateOf.modify at hk
    simp only [List.getElem?_modify] at hk
    cases hm : mid.tables[k]? with
    | none => rw [hm] at hk; cases hk
    | some m =>
      rw [hm] at hk
      have hb := h.2.2 k m hm hn
      by_cases e : i = k
      · subst e
        rw [ht] at hn
        cases hn
      · simp only [e, ite_false] at hk
        rw [id_map'] at hk
        cases hk
        exact hb

end pure

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- The work of the strategies of the table at `j` changes the answers of
that table alone, and no mark. -/
theorem Inner.frame {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK j st st') :
    Frame j st st' := by
  induction h with
  | refl st => exact Frame.refl j st
  | trans _ _ a b => exact a.trans b
  | same e er _ => exact Frame.of_frames e er
  | opened g self e er _ => exact Frame.of_opened e er
  | add st a =>
    rw [addAnswer_val]
    split
    · exact Frame.refl j st
    · split
      · split
        · exact Frame.of_app j st _
        · exact (Frame.of_app j st _).trans (Frame.of_app j _ _)
      · exact Frame.of_app j st _

omit [DecidableEq R] in
/-- A fold of steps each of which keeps what a round keeps, while the table
at `i` is in its round. -/
theorem keep_foldL {α β : Type} (π : β → StateOf R Rel (Ans D P)) (f : β → α → Cost β) (i : Nat)
    (hf : ∀ b x, Busy (π b) i → Keep (π b) (π (f b x).val)) :
    ∀ (xs : List α) (b : β), Busy (π b) i → Keep (π b) (π (foldL f b xs).val)
  | [], b, _ => Keep.refl _
  | x :: xs, b, hb => by
    simp only [foldL, Cost.bind_val]
    exact (hf b x hb).trans (keep_foldL π f i hf xs _ ((hf b x hb).busy hb))

omit [DecidableEq R] in
/-- The same, from a state already reached. -/
theorem keep_foldL_from {α β : Type} (π : β → StateOf R Rel (Ans D P)) (f : β → α → Cost β)
    (i : Nat) (hf : ∀ b x, Busy (π b) i → Keep (π b) (π (f b x).val)) (xs : List α) (b : β)
    {s₀ : StateOf R Rel (Ans D P)} (h₀ : Keep s₀ (π b)) (hb : Busy s₀ i) :
    Keep s₀ (π (foldL f b xs).val) :=
  h₀.trans (keep_foldL π f i hf xs b (h₀.busy hb))

theorem keep_work (whole : Bool) (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (hb : Busy st i) :
    Keep st (work (K := DerivationKernel.over D K hK P) whole i g st s).val.1 :=
  (inner_work (K := K) (hK := hK) whole i g st s).frame.keep hb.open

omit [DecidableEq R] in
theorem keep_setGroup (st : StateOf R Rel (Ans D P)) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P)) : Keep st (setGroup st i k f) :=
  keep_modify st i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h, fun h => ⟨h, fun h => h⟩⟩

theorem keep_workGroup (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Keep st (adv h st).val.1) (whole : Bool) (i : Nat) (g : GoalOf R Rel)
    (k : Nat) (st : StateOf R Rel (Ans D P)) (hb : Busy st i) :
    Keep st (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1 := by
  have hw := fun whole g st s hb => keep_work (K := K) (hK := hK) (P := P) whole i g st s hb
  at_cost K hK
  simp only [workGroup, Cost.bind_val, Cost.pure_val]
  refine Keep.trans ?_ (keep_setGroup _ _ _ _)
  refine keep_foldL_from (fun acc : StateOf R Rel (Ans D P) × Nat => acc.1) _ i
    (fun b h _ => ?_) _ _ ?_ hb
  · simp only [Cost.bind_val, Cost.pure_val]
    exact hadv _ _
  · refine keep_foldL (fun acc : StateOf R Rel (Ans D P) × Nat × Bool => acc.1) _ i
      (fun b j hb => ?_) _ (st, 0, false) hb
    split
    · exact Keep.refl _
    · simp only [Cost.bind_val, Cost.pure_val]
      exact (hw _ _ _ _ hb).trans (keep_setGroup _ _ _ _)

theorem keep_workLevel (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (hadv : ∀ h st, Keep st (adv h st).val.1) (whole : Bool) (i : Nat) (g : GoalOf R Rel)
    (lv : Nat) (st : StateOf R Rel (Ans D P)) (hb : Busy st i) :
    Keep st (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv st).val.1 := by
  have hw := fun whole g k st hb =>
    keep_workGroup (K := K) (hK := hK) (P := P) adv hadv whole i g k st hb
  at_cost K hK
  refine keep_foldL (fun acc : StateOf R Rel (Ans D P) × Bool => acc.1) _ i (fun b p hb => ?_) _
    (st, false) hb
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    exact hw _ _ _ _ hb
  · exact Keep.refl _

theorem keep_prepare (i : Nat) (t : Table R Rel (Ans D P)) (st : StateOf R Rel (Ans D P))
    (ht : st.tables[i]? = some t) (hd : t.done = false) :
    Keep st (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
      Busy (prepare (K := DerivationKernel.over D K hK P) i t st).val i := by
  have hopen : ∀ t', st.tables[i]? = some t' → t'.done = false := fun t' h => by
    rw [ht] at h; cases h; exact hd
  have hfr := (inner_expand (K := K) (hK := hK) (P := P) (w := i) t.goal st).frame
  have hexp := hfr.keep hopen
  at_cost K hK
  unfold prepare
  have fin : ∀ st' : StateOf R Rel (Ans D P), Keep st st' →
      (∃ t', st'.tables[i]? = some t' ∧ t'.done = false) →
      Keep st (st'.modify i fun t => { t with stamp := st'.round, delta := 0 }) ∧
        Busy (st'.modify i fun t => { t with stamp := st'.round, delta := 0 }) i := by
    intro st' hf ⟨t', ht', hd'⟩
    refine ⟨hf.trans (keep_modify st' i
      (fun t => { t with stamp := st'.round, delta := 0 }) fun t'' h'' => by
        rw [ht'] at h''; cases h''
        exact ⟨rfl, rfl, rfl, fun h => h, fun _ => ⟨rfl, fun h => h⟩⟩),
      { t' with stamp := st'.round, delta := 0 }, ?_, rfl, hd'⟩
    unfold StateOf.modify
    simp [ht']
  cases t.groups with
  | some _ => exact fin st (Keep.refl st) ⟨t, ht, hd⟩
  | none =>
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨t1, ht1, -, d1, -⟩ := hfr.2.1 i t ht
    generalize some (expand (K := DerivationKernel.over D _ hK P) t.goal st).val.2 = gs
    refine fin _ (hexp.trans (keep_modify _ _ _ fun _ _ =>
      ⟨rfl, rfl, rfl, fun h => h, fun h => ⟨h, fun h => h⟩⟩))
      ⟨{ t1 with groups := gs }, ?_, d1.trans hd⟩
    unfold StateOf.modify
    simp [ht1]

/-- **A round keeps** every table with its goal and its answers, every
complete table as it is, and every open table that has had its round in this
request open. -/
theorem keep_advance : ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)),
    Keep st (advance (K := DerivationKernel.over D K hK P) fuel i st).val.1
  | 0, _, st => by
    at_cost K hK
    exact Keep.refl st
  | fuel + 1, i, st => by
    have ih := fun h st => keep_advance fuel h st
    have hprep := fun t ht hd => keep_prepare (K := K) (hK := hK) (P := P) i t st ht hd
    have hlev := fun whole g lv st hb =>
      keep_workLevel (K := K) (hK := hK) (P := P) _ ih whole i g lv st hb
    at_cost K hK
    simp only [advance]
    split
    · exact Keep.refl st
    · next t ht =>
      split
      · exact Keep.refl st
      · next hd =>
        split
        · exact Keep.refl st
        · next hs =>
          split
          · exact Keep.refl st
          · simp only [Cost.bind_val, Cost.pure_val]
            obtain ⟨hk, hb⟩ := hprep t ht (by simpa using hd)
            have hmid := keep_foldL_from (fun acc : StateOf R Rel (Ans D P) × Bool => acc.1)
              (fun (acc : StateOf R Rel (Ans D P) × Bool) lv =>
                if acc.2 then pure acc
                else workLevel (K := DerivationKernel.over D _ hK P)
                  (advance (K := DerivationKernel.over D _ hK P) fuel)
                  (decide ((groupsAt (prepare (K := DerivationKernel.over D _ hK P) i t st).val
                    i).length ≤ 1)) i t.goal lv acc.1) i
              (fun b lv hb => by
                split
                · exact Keep.refl _
                · exact hlev _ _ _ _ hb)
              (levelsOf (groupsAt (prepare (K := DerivationKernel.over D _ hK P) i t st).val i))
              (_, false) (Keep.refl _) hb
            have hall := hk.trans hmid
            have hd' : t.done = false := by simpa using hd
            refine keep_mark (keep_mark hall ht hs hd' _ ?_) ht hs hd' _ ?_
            · exact fun _ => ⟨rfl, rfl, rfl, rfl, fun h => h⟩
            · exact fun t'' => ⟨rfl, rfl, rfl, rfl, fun h => by simp [h]⟩

/-- **A complete table never changes again**: over a request every table
stays, its answers stay with more at the end, and a complete table stays
complete and gains none. -/
theorem stable_request (st : StateOf R Rel (Ans D P)) :
    Stable st (request (K := DerivationKernel.over D K hK P) st).val.1 := by
  have h := fun st => keep_advance (K := K) (hK := hK) (P := P) st.tables.length 0 st
  at_cost K hK
  simp only [request, Cost.bind_val, Cost.pure_val]
  have h1 := (h { st with round := st.round + 1 }).stable
  intro k t hk
  obtain ⟨t', ht', e1, e2, e3, e4⟩ := h1 k t hk
  refine ⟨_, by simp only [List.getElem?_mapIdx, ht']; rfl, ?_⟩
  split
  · exact ⟨e1, e2, e3, fun hd => ⟨rfl, (e4 hd).2⟩⟩
  · exact ⟨e1, e2, e3, e4⟩

end kernel

end Symmetric

end RwLog
