/-
# The separating family: the stages of a round

What each stage of a round returns and spends while the root table is open:
the races, the candidates, the fresh answers, the keys of the goals asked
for, and the new tables. The races may return the two spans with or without
repeats, so the stages are described by what their results satisfy
(`Cost.Spends`) and not by their exact value.
-/
import RwLog.Rungs.R003.Proofs.Separation.Tables

namespace RwLog

namespace R003

namespace Sep

open Cost R001

/-! ## The races -/

/-- What a race says about a goal of the run: final; copies of the two spans,
at most `ansBound k` of them; `$x -> z` among them on a member of the
family. -/
def UOK (k : Nat) (g : Goal) (u : Bool × List Span) : Prop :=
  u.1 = true ∧ (∀ x ∈ u.2, Good x) ∧ u.2.length ≤ ansBound k ∧ ((∃ j, g = gC j) → xz ∈ u.2)

/-- What one race costs at most. -/
def raceBound (k : Nat) : Nat := 7 * sharedBound k

theorem gS_ne_gC {s : Span} (hs : Good s) (j : Nat) : gS s ≠ gC j :=
  fun h => cRel_ne_span j hs (congrArg Goal.e h).symm

theorem unfolder_slot (k d : Nat) {g : Goal} (h : Slot k g) :
    (unfolder P0 d g).ticks ≤ raceBound k ∧ UOK k g (unfolder P0 d g).val := by
  have hC : ∀ j, j ≤ k → (unfolder P0 d (gC j)).ticks ≤ raceBound k ∧
      UOK k (gC j) (unfolder P0 d (gC j)).val := by
    intro j hj
    obtain ⟨h1, h2, h3, h4, h5⟩ := unfolder_gC d j
    have := sharedBound_mono hj
    have := ansBound_mono hj
    exact ⟨by unfold raceBound; omega, h2, h3, by omega, fun _ => h4⟩
  have hS : ∀ s, Good s → (unfolder P0 d (gS s)).ticks ≤ raceBound k ∧
      UOK k (gS s) (unfolder P0 d (gS s)).val := by
    intro s hs
    obtain ⟨h1, h2⟩ := unfolder_gS d hs
    have hb : 104 ≤ sharedBound k := by unfold sharedBound; omega
    have := two_le_ansBound k
    refine ⟨by unfold raceBound; omega, ?_⟩
    rw [h2]
    refine ⟨rfl, ?_, by simp; omega, ?_⟩
    · intro x hx; rw [List.mem_singleton.1 hx]; exact hs
    · rintro ⟨j, hj⟩; exact absurd hj (gS_ne_gC hs j)
  rcases h with rfl | ⟨j, hj, rfl⟩ | rfl | rfl
  · exact hC k le_rfl
  · exact hC j (by omega)
  · exact hS xz good_xz
  · exact hS zz good_zz

theorem us_spends {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) (d : Nat) :
    Spends (mapL (fun t : Table => if t.done then pure (false, []) else do
        tick (goalSize t.goal)
        unfolder P0 d t.goal) (tabs k a0 rest))
      ((tabs k a0 rest).length * (keyBound k + raceBound k))
      (List.Forall₂ (fun t u => UOK k t.goal u) (tabs k a0 rest)) := by
  refine Spends.mapL fun t ht => ?_
  have hd := open_of_mem hr ht
  have hsl := slot_of_mem hr ht
  obtain ⟨h1, h2⟩ := unfolder_slot k d hsl
  have := goalSize_slot hsl
  simp only [hd, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by simp only [bind_ticks, tick_ticks]; omega, h2⟩

/-! ## The strategies that read other tables -/

theorem slot_cases {k : Nat} {g : Goal} (h : Slot k g) :
    g = gC 0 ∨ (∃ j, j < k ∧ g = gC (j + 1)) ∨ ∃ s, Good s ∧ g = gS s := by
  have hC : ∀ j, j ≤ k → gC j = gC 0 ∨ (∃ i, i < k ∧ gC j = gC (i + 1)) ∨
      ∃ s, Good s ∧ gC j = gS s := by
    intro j hj
    cases j with
    | zero => exact Or.inl rfl
    | succ i => exact Or.inr (Or.inl ⟨i, by omega, rfl⟩)
  rcases h with rfl | ⟨j, hj, rfl⟩ | rfl | rfl
  · exact hC k le_rfl
  · exact hC j (by omega)
  · exact Or.inr (Or.inr ⟨xz, good_xz, rfl⟩)
  · exact Or.inr (Or.inr ⟨zz, good_zz, rfl⟩)

theorem spanAnswer_eq (s : Span) : Tabled.spanAnswer [] none s none = Tabled.live [] s := by
  refine Cost.ext ?_ ?_ <;> simp [Tabled.spanAnswer]

/-- The candidates a goal of the run gets from other tables, and the goals it
asks for: nothing from the tables, which are empty; a span answers itself. -/
theorem strat_costs {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : Slot k g) : ∃ (ex : List Span) (ds : List Goal),
    Costs (Tabled.produceStrategies P0 (tabs k a0 rest) g) (ex, ds)
        (4 * lookBound k (tabs k a0 rest).length) ∧
      (∀ x ∈ ex, Good x) ∧ ex.length ≤ 1 ∧ (∀ g' ∈ ds, Sub k g') ∧ ds.length ≤ 2 := by
  rcases slot_cases hg with rfl | ⟨j, hj, rfl⟩ | ⟨s, hs, rfl⟩
  · have hsub : ∀ g' ∈ [gS xz, gS zz], Sub k g' := by
      intro g' hg'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hf := Costs.flatMapL (f := Tabled.answersOf (tabs k a0 rest)) (g := fun _ => [])
      (c := lookBound k (tabs k a0 rest).length) (xs := [gS xz, gS zz])
      fun x hx => answersOf_costs hr (hsub x hx)
    refine ⟨[], [gS xz, gS zz], ?_, by simp, by simp, hsub, by simp⟩
    show Costs (Tabled.produceStrategies P0 (tabs k a0 rest) ⟨none, .or (.span xz) (.span zz), none⟩)
      _ _
    simp only [Tabled.produceStrategies, orLeaves, orBranches, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil]
    refine Costs.mono (c := [gS xz, gS zz].length * lookBound k (tabs k a0 rest).length + 0) ?_
      (by simp only [List.length_cons, List.length_nil]; omega)
    refine Costs.bind hf ?_
    exact Costs.pure _
  · have hL : Sub k (gC 0) := Or.inl ⟨0, by omega, rfl⟩
    have hR : Sub k (gC j) := Or.inl ⟨j, hj, rfl⟩
    refine ⟨[], [gC 0, gC j], ?_, by simp, by simp, ?_, by simp⟩
    · show Costs (Tabled.produceStrategies P0 (tabs k a0 rest) ⟨none, .seq tw (cRel j), none⟩) _ _
      simp only [Tabled.produceStrategies, seqLeft, seqRight]
      refine Costs.mono (c := lookBound k (tabs k a0 rest).length +
        (lookBound k (tabs k a0 rest).length + (0 + (lookBound k (tabs k a0 rest).length +
        (0 + (lookBound k (tabs k a0 rest).length + (0 + (0 + (0 + 0))))))))) ?_ (by omega)
      refine Costs.bind (answersOf_costs hr hL) ?_
      refine Costs.bind (answersOf_costs hr hR) ?_
      refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
      refine Costs.bind (doneOf_costs hr hL) ?_
      refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
      refine Costs.bind (doneOf_costs hr hR) ?_
      refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
      refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
      refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
      exact Costs.pure _
    · intro g' hg'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl
      · exact hL
      · exact hR
  · refine ⟨[s], [], ?_, ?_, by simp, by simp, by simp⟩
    · show Costs (Tabled.produceStrategies P0 (tabs k a0 rest) ⟨none, .span s, none⟩) _ _
      simp only [Tabled.produceStrategies, spanAnswer_eq]
      have : 7 ≤ lookBound k (tabs k a0 rest).length := by
        unfold lookBound keyBound
        exact le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      refine Costs.mono (c := 3 + 0) ?_ (by omega)
      refine Costs.bind (live_good hs) ?_
      exact Costs.pure _
    · intro x hx; rw [List.mem_singleton.1 hx]; exact hs

/-- The strategies of a goal of the run that read other tables: one, and the
goals it depends on were asked for. -/
theorem tstrat_costs {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : Slot k g) : ∃ ds : List Goal,
    Costs (Tabled.tableStrategies P0 (tabs k a0 rest) g) [ds]
        (2 * lookBound k (tabs k a0 rest).length) ∧
      (∀ g' ∈ ds, Sub k g') ∧ ds.length ≤ 2 := by
  rcases slot_cases hg with rfl | ⟨j, hj, rfl⟩ | ⟨s, hs, rfl⟩
  · refine ⟨[gS xz, gS zz], ⟨rfl, Nat.zero_le _⟩, ?_, by simp⟩
    intro g' hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · have hL : Sub k (gC 0) := Or.inl ⟨0, by omega, rfl⟩
    have hR : Sub k (gC j) := Or.inl ⟨j, hj, rfl⟩
    refine ⟨[gC 0, gC j], ?_, ?_, by simp⟩
    · show Costs (Tabled.tableStrategies P0 (tabs k a0 rest) ⟨none, .seq tw (cRel j), none⟩) _ _
      simp only [Tabled.tableStrategies, seqLeft, seqRight]
      refine Costs.mono (c := lookBound k (tabs k a0 rest).length +
        (0 + (lookBound k (tabs k a0 rest).length + (0 + 0)))) ?_ (by omega)
      refine Costs.bind (doneOf_costs hr hL) ?_
      refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
      refine Costs.bind (doneOf_costs hr hR) ?_
      refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
      exact Costs.pure _
    · intro g' hg'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl
      · exact hL
      · exact hR
  · exact ⟨[], ⟨rfl, Nat.zero_le _⟩, by simp, by simp⟩

/-! ## The candidates -/

/-- What a table's candidates and requests satisfy. -/
def OOK (k : Nat) (g : Goal) (o : List Span × List Goal) : Prop :=
  (∀ x ∈ o.1, Good x) ∧ o.1.length ≤ ansBound k + 1 ∧ ((∃ j, g = gC j) → xz ∈ o.1) ∧
    (∀ g' ∈ o.2, Sub k g') ∧ o.2.length ≤ 2

theorem out_spends {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {t : Table}
    {u : Bool × List Span} (ht : t ∈ tabs k a0 rest) (hu : UOK k t.goal u) :
    Spends (if t.done then pure ([], []) else Tabled.produce P0 (tabs k a0 rest) t.goal u)
      (4 * lookBound k (tabs k a0 rest).length) (OOK k t.goal) := by
  obtain ⟨ex, ds, ⟨hv, htk⟩, h1, h2, h3, h4⟩ := strat_costs (a0 := a0) hr (slot_of_mem hr ht)
  obtain ⟨-, u2, u3, u4⟩ := hu
  simp only [open_of_mem hr ht, Bool.false_eq_true, ↓reduceIte, Tabled.produce]
  refine ⟨by simpa using htk, ?_⟩
  simp only [bind_val, pure_val, hv]
  refine ⟨?_, by simp; omega, fun h => List.mem_append_left _ (u4 h), h3, h4⟩
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact u2 x h
  · exact h1 x h

/-! ## The fresh answers -/

/-- What a table looks like once its fresh answers are added: on a member of
the family, `$x -> z` and nothing else. -/
def T1OK (t t1 : Table) : Prop :=
  t1.goal = t.goal ∧ t1.done = t.done ∧
    ((∃ j, t.goal = gC j) → t.answers = [] ∨ t.answers = [xz] → t1.answers = [xz])

theorem ts1_spends {k : Nat} {t : Table} {o : List Span × List Goal}
    (ha : t.answers = [] ∨ t.answers = [xz]) (ho : OOK k t.goal o) :
    Spends (do
        let f ← Tabled.fresh t.answers o.1
        pure { t with answers := t.answers ++ f })
      (freshBound (ansBound k + 1)) (T1OK t) := by
  obtain ⟨o1, o2, o3, -, -⟩ := ho
  refine ⟨?_, rfl, rfl, fun hj _ => ?_⟩
  · have := fresh_ticks ha o1
    have := freshBound_mono o2
    simp only [bind_ticks, pure_ticks, Nat.add_zero]
    omega
  · simp only [bind_val, pure_val, Tabled.fresh_val]
    rcases ha with h | h
    · rw [h, fresh_nil_good o1 (o3 hj)]; rfl
    · rw [h, fresh_xz_good o1]; rfl

/-! ## The goals asked for -/

theorem forall₂_right {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β},
    List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab t, y, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨x, hx, hxy⟩ := forall₂_right t y h
      exact ⟨x, by simp [hx], hxy⟩

theorem reqs_spends {k : Nat} {ts : Tables} {outs : List (List Span × List Goal)}
    (ho : List.Forall₂ (fun t o => OOK k t.goal o) ts outs) :
    Spends (mapL (fun g => do
        let n ← Tabled.norm g
        pure n.2) (outs.flatMap Prod.snd))
      (2 * ts.length * keyBound k)
      (fun reqs => (∀ g ∈ reqs, Sub k g) ∧ reqs.length ≤ 2 * ts.length) := by
  have hsub : ∀ g ∈ outs.flatMap Prod.snd, Sub k g := by
    intro g hg
    obtain ⟨o, ho', hgo⟩ := List.mem_flatMap.1 hg
    obtain ⟨t, -, hto⟩ := forall₂_right ho o ho'
    exact hto.2.2.2.1 g hgo
  have hlen : (outs.flatMap Prod.snd).length ≤ 2 * ts.length := by
    have := R002.Sep.length_flatMap_le (Prod.snd : List Span × List Goal → List Goal) 2 outs
      fun o ho' => by
        obtain ⟨t, -, hto⟩ := forall₂_right ho o ho'
        exact hto.2.2.2.2
    rw [ho.length_eq]
    omega
  have hm := Costs.mapL (f := fun g => do
      let n ← Tabled.norm g
      pure n.2) (g := id) (c := keyBound k) (xs := outs.flatMap Prod.snd) fun g hg => by
    refine ⟨?_, ?_⟩
    · simp only [bind_val, pure_val, Tabled.norm_val, norm_sub (hsub g hg)]; rfl
    · have := goalSize_sub (hsub g hg)
      show goalSize g + 0 ≤ _
      omega
  rw [List.map_id] at hm
  refine ⟨le_trans hm.2 (Nat.mul_le_mul_right _ hlen), ?_⟩
  rw [hm.1]
  exact ⟨hsub, hlen⟩

/-! ## The new tables -/

theorem step_spends {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest)
    {acc : List Goal} {g : Goal} (hacc : ∀ h ∈ acc, Key k h)
    (hg : Key k g) :
    Spends (do
        let b ← anyL (fun t : Table => Tabled.same t.goal g) (tabs k a0 rest)
        if b then pure acc else do
          let b' ← anyL (fun h => Tabled.same h g) acc
          pure (if b' then acc else acc ++ [g]))
      (((tabs k a0 rest).length + acc.length) * (2 * keyBound k))
      (fun a' => a'.length ≤ acc.length + 1 ∧ ∀ h ∈ a', h ∈ acc ∨ h = g) := by
  have h1 : (anyL (fun t : Table => Tabled.same t.goal g) (tabs k a0 rest)).ticks ≤
      (tabs k a0 rest).length * (2 * keyBound k) :=
    anyL_ticks_le_mul fun t ht => same_ticks (key_slot (slot_of_mem hr ht)) hg
  have h2 : (anyL (fun h => Tabled.same h g) acc).ticks ≤ acc.length * (2 * keyBound k) :=
    anyL_ticks_le_mul fun h hh => same_ticks (hacc h hh) hg
  rw [Nat.add_mul]
  refine ⟨?_, ?_⟩
  · simp only [bind_ticks, ite_ticks, pure_ticks, Nat.add_zero]
    split <;> omega
  · simp only [bind_val, ite_val, pure_val]
    split
    · exact ⟨by omega, fun h hh => Or.inl hh⟩
    · split
      · exact ⟨by omega, fun h hh => Or.inl hh⟩
      · refine ⟨by simp, fun h hh => ?_⟩
        rcases List.mem_append.1 hh with hh | hh
        · exact Or.inl hh
        · exact Or.inr (List.mem_singleton.1 hh)

theorem newGoals_spends {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) :
    ∀ (reqs acc : List Goal), (∀ g ∈ reqs, Key k g) →
      (∀ g ∈ acc, Key k g) →
      Spends (foldL (fun acc g => do
          let b ← anyL (fun t : Table => Tabled.same t.goal g) (tabs k a0 rest)
          if b then pure acc else do
            let b' ← anyL (fun h => Tabled.same h g) acc
            pure (if b' then acc else acc ++ [g])) acc reqs)
        (reqs.length * (((tabs k a0 rest).length + acc.length + reqs.length) * (2 * keyBound k)))
        (fun ng => ng.length ≤ acc.length + reqs.length ∧ ∀ g ∈ ng, g ∈ acc ∨ g ∈ reqs)
  | [], acc, _, _ => ⟨by simp [foldL], by simp [foldL]⟩
  | g :: reqs, acc, hreqs, hacc => by
    have hs := step_spends (a0 := a0) hr hacc (hreqs g (by simp))
    simp only [foldL]
    have e : (reqs.length + 1) * (((tabs k a0 rest).length + acc.length + (reqs.length + 1)) *
          (2 * keyBound k)) =
        ((tabs k a0 rest).length + acc.length) * (2 * keyBound k) +
          reqs.length * (((tabs k a0 rest).length + (acc.length + 1) + reqs.length) *
            (2 * keyBound k)) + (reqs.length + 1) * (2 * keyBound k) := by ring
    refine Spends.mono (c := ((tabs k a0 rest).length + acc.length) * (2 * keyBound k) +
      reqs.length * (((tabs k a0 rest).length + (acc.length + 1) + reqs.length) *
        (2 * keyBound k))) (Spends.bind hs fun a' ha' => ?_)
      (by simp only [List.length_cons] at e ⊢; omega) fun _ h => h
    · have hacc' : ∀ h ∈ a', Key k h := by
        intro h hh
        rcases ha'.2 h hh with hh | rfl
        · exact hacc h hh
        · exact hreqs _ (by simp)
      have ih := newGoals_spends (a0 := a0) hr reqs a' (fun g hg => hreqs g (by simp [hg])) hacc'
      refine Spends.mono ih ?_ ?_
      · refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_)
        have := ha'.1
        omega
      · intro ng hng
        refine ⟨by have := ha'.1; simp only [List.length_cons]; omega, fun x hx => ?_⟩
        rcases hng.2 x hx with h | h
        · rcases ha'.2 x h with h | rfl
          · exact Or.inl h
          · exact Or.inr (by simp)
        · exact Or.inr (by simp [h])

end Sep

end R003

end RwLog
