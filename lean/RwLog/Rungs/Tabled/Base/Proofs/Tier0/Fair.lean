/-
# Tier 0 proofs, part 11: fairness

Along the rounds, every derivation of a table's goal is eventually covered by
the table, unless it is dead. The induction is on the same measure as
completion: an incomplete table reads its sub-goals every round, each
sub-goal has a table one round later, those tables eventually cover the
lighter derivations of their goals, and from then on the join strategies
compute a candidate covering the derivation, which the table keeps or covers.
-/
import RwLog.Rungs.Tabled.Base.Proofs.Tier0.Runs

namespace RwLog

namespace R001

namespace Tier0

/-- A table that is incomplete in a round covers, one round later, whatever
its candidates in that round cover. -/
theorem cover_next (st : State) (k i : Nat) (hi : i < (iter st k).tables.length)
    (hnd : (iter st k).tables[i].done = false) {X : GRel}
    (h : DC (iter st k).P.theory
      (produce (iter st k).P (iter st k).depth (iter st k).tables (iter st k).tables[i].goal).1 X) :
    ∃ hi' : i < (iter st (k + 1)).tables.length, DC (iter st k).P.theory (iter st (k + 1)).tables[i].answers X := by
  obtain ⟨hi', e⟩ := iter_getElem_succ st k i hi
  refine ⟨hi', ?_⟩
  rw [e, after_answers, outOf_not_done hnd]
  exact h.covers fun c hc => fresh_cover hc

/-- A goal an incomplete table reads has a table one round later. -/
theorem dep_found (st : State) (k i : Nat) (hi : i < (iter st k).tables.length)
    (hnd : (iter st k).tables[i].done = false) {d : Goal}
    (hd : d ∈ (produce (iter st k).P (iter st k).depth (iter st k).tables
      (iter st k).tables[i].goal).2) :
    ∃ j, indexOf (iter st (k + 1)).tables d.norm.2 = some j := by
  have hr : d.norm.2 ∈ reqsOf (iter st k) := by
    simp only [reqsOf, List.mem_map, List.mem_flatMap]
    exact ⟨d, ⟨_, ⟨_, List.getElem_mem hi, rfl⟩, by rwa [outOf_not_done hnd]⟩, rfl⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (reqs_found hr)
  obtain ⟨j, hj, -⟩ := find_indexOf ht
  exact ⟨j, hj⟩

section

/-- Every derivation of a table's goal is eventually covered by the table,
for good. -/
theorem fair {st : State} (hwf : ∀ ρ ∈ st.P.theory, ρ.WellFormed) (hI : TInv st.P st.tables) :
    ∀ m, ∀ k i (hi : i < (iter st k).tables.length) (w : Nat) (s : Span),
      DW st.P w (iter st k).tables[i].goal.e s → 2 * w + isOr (iter st k).tables[i].goal.e ≤ m →
      ∃ k₀, ∀ k' ≥ k₀, ∃ hi' : i < (iter st k').tables.length,
        DC st.P.theory (iter st k').tables[i].answers (GDen (iter st k).tables[i].goal s.den) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro k i hi w s hw hm
  have hIk := tinv_iter hwf hI
  have hP := iter_P st
  -- once covered, covered for good
  suffices hev : ∃ k₁, ∃ hi₁ : i < (iter st k₁).tables.length, k ≤ k₁ ∧
      DC st.P.theory (iter st k₁).tables[i].answers (GDen (iter st k).tables[i].goal s.den) by
    obtain ⟨k₁, hi₁, -, hdc⟩ := hev
    refine ⟨k₁, fun k' hk' => ?_⟩
    obtain ⟨hi', ⟨-, ⟨r, hr⟩, -⟩⟩ := iter_ext_le st hk' i hi₁
    exact ⟨hi', hdc.mono fun a ha => by rw [hr]; exact List.mem_append_left _ ha⟩
  -- the table is complete, or eventually its candidates cover the derivation
  have hG := hI.good
  have hgG : GoodG (iter st k).tables[i].goal := (hIk k).good _ (List.getElem_mem hi)
  suffices hc : (iter st k).tables[i].done = true ∨ ∃ K ≥ k, ∃ hiK : i < (iter st K).tables.length,
      (iter st K).tables[i].done = true ∨
      DC st.P.theory (produce st.P (iter st K).depth (iter st K).tables (iter st k).tables[i].goal).1
        (GDen (iter st k).tables[i].goal s.den) by
    rcases hc with hd | ⟨K, hK, hiK, hd | hdc⟩
    · exact ⟨k, hi, le_rfl, (hIk k).comp _ (List.getElem_mem hi) hd s hw.derives⟩
    · obtain ⟨hg, -, -⟩ := (iter_ext_le st hK i hi).2
      refine ⟨K, hiK, hK, ?_⟩
      have := (hIk K).comp _ (List.getElem_mem hiK) hd s (by rw [hg]; exact hw.derives)
      rwa [hg] at this
    · obtain ⟨hg, -, -⟩ := (iter_ext_le st hK i hi).2
      cases hdn : (iter st K).tables[i].done
      · rw [← hg, ← hP K] at hdc
        obtain ⟨hi', hdc'⟩ := cover_next st K i hiK hdn hdc
        rw [hP] at hdc'
        exact ⟨K + 1, hi', by omega, by rw [← hg]; exact hdc'⟩
      · refine ⟨K, hiK, hK, ?_⟩
        have := (hIk K).comp _ (List.getElem_mem hiK) hdn s (by rw [hg]; exact hw.derives)
        rwa [hg] at this
  by_cases hdk : (iter st k).tables[i].done = true
  · exact .inl hdk
  right
  have hnd : (iter st k).tables[i].done = false := by simpa using hdk
  -- a goal the table reads is eventually covered on lighter derivations
  have hD : ∀ d ∈ (produce st.P (iter st k).depth (iter st k).tables (iter st k).tables[i].goal).2,
      ∀ w' s', DW st.P w' d.e s' → 2 * w' + isOr d.e < 2 * w + isOr (iter st k).tables[i].goal.e →
      ∃ k₀, ∀ k' ≥ k₀, DC st.P.theory (answersOf (iter st k').tables d) (GDen d s'.den) := by
    intro d hd w' s' hw' hlt
    have hgd := deps_good hgG hd
    obtain ⟨j, hj⟩ := dep_found st k i hi hnd (by rw [hP]; exact hd)
    obtain ⟨_, hf, hs⟩ := indexOf_find hj
    obtain ⟨w'', s'', h1, hmeas, h4⟩ := norm_meas d hw'
    rw [← same_e hs] at h1 hmeas
    obtain ⟨k₀, hk₀⟩ := IH _ (by omega) (k + 1) j _ w'' s'' h1 le_rfl
    refine ⟨max k₀ (k + 1), fun k' hk' => ?_⟩
    obtain ⟨hjl', hf', -⟩ := indexOf_find (indexOf_iter st (le_of_max_le_right hk') hj)
    obtain ⟨_, hdc⟩ := hk₀ k' (le_of_max_le_left hk')
    obtain ⟨hg, -, -⟩ := (iter_ext_le st (le_of_max_le_right hk') j (by assumption)).2
    refine dc_from_key hf' hgd ?_ h4 ?_
    · rw [hg]; exact (hIk (k + 1)).good _ (List.getElem_mem _)
    · rw [hg]; exact hdc
  clear IH hm
  generalize (iter st k).tables[i].goal = G at *
  obtain ⟨lb, e, rb⟩ := G
  cases e with
  | zero => cases hw
  | span s₀ => cases hw with | span => exact ⟨k, le_rfl, hi, .inr (dc_span hwf lb rb _)⟩
  | or a b =>
    obtain ⟨l, hl, hwl⟩ := (dw_orBranches _).1 hw
    obtain ⟨k₀, hk₀⟩ := hD ⟨lb, l, rb⟩
      (by simp only [produce, produce.produceStrategies, orLeaves, List.mem_map]; exact ⟨l, hl, rfl⟩)
      w s hwl (by rw [isOr_zero (orBranches_not_or _ l hl)]; simp [isOr])
    obtain ⟨hiK, -⟩ := iter_ext_le st (le_max_right k₀ k) i hi
    exact ⟨max k₀ k, le_max_right _ _, hiK, .inr (dc_or hl (hk₀ _ (le_max_left _ _)))⟩
  | call n =>
    cases hw with
    | call hw =>
      obtain ⟨k₀, hk₀⟩ := hD (callGoal st.P ⟨lb, .call n, rb⟩ n)
        (by simp [produce, produce.produceStrategies]) _ s hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl)
      obtain ⟨hiK, -⟩ := iter_ext_le st (le_max_right k₀ k) i hi
      exact ⟨max k₀ k, le_max_right _ _, hiK, .inr (dc_call (hk₀ _ (le_max_left _ _)))⟩
  | conv a =>
    cases hw with
    | conv hw =>
      obtain ⟨k₀, hk₀⟩ := hD (convGoal ⟨lb, .conv a, rb⟩ a)
        (by simp [produce, produce.produceStrategies]) _ _ hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl)
      obtain ⟨hiK, -⟩ := iter_ext_le st (le_max_right k₀ k) i hi
      exact ⟨max k₀ k, le_max_right _ _, hiK, .inr (dc_conv (hk₀ _ (le_max_left _ _)))⟩
  | seq a b =>
    cases hw with
    | seq hw₁ hw₂ hc =>
      rw [compose_some hc]
      obtain ⟨k₁, hk₁⟩ := hD ⟨lb, a, none⟩ (by simp [produce, produce.produceStrategies, seqLeft])
        _ _ hw₁ (meas_lt _ _ (by omega) rfl)
      obtain ⟨k₂, hk₂⟩ := hD ⟨none, b, rb⟩ (by simp [produce, produce.produceStrategies, seqRight])
        _ _ hw₂ (meas_lt _ _ (by omega) rfl)
      have hK : k ≤ max (max k₁ k₂) k := le_max_right _ _
      obtain ⟨hiK, -⟩ := iter_ext_le st hK i hi
      exact ⟨_, hK, hiK, .inr (dc_seq_join hwf
        (hk₁ _ (le_trans (le_max_left _ _) (le_max_left _ _)))
        (hk₂ _ (le_trans (le_max_right _ _) (le_max_left _ _))))⟩
  | and a b =>
    cases hw with
    | and hw₁ hw₂ hc =>
      rw [meet_some hc]
      obtain ⟨k₁, hk₁⟩ := hD ⟨lb, a, rb⟩ (by simp [produce, produce.produceStrategies, andLeft])
        _ _ hw₁ (meas_lt _ _ (by omega) rfl)
      obtain ⟨k₂, hk₂⟩ := hD ⟨lb, b, rb⟩ (by simp [produce, produce.produceStrategies, andRight])
        _ _ hw₂ (meas_lt _ _ (by omega) rfl)
      have hK : k ≤ max (max k₁ k₂) k := le_max_right _ _
      obtain ⟨hiK, -⟩ := iter_ext_le st hK i hi
      exact ⟨_, hK, hiK, .inr (dc_and_join hwf hgG
        (hk₁ _ (le_trans (le_max_left _ _) (le_max_left _ _)))
        (hk₂ _ (le_trans (le_max_right _ _) (le_max_left _ _))))⟩

end

end Tier0

end R001

end RwLog
