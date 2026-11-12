/-
# Tier 0 proofs, part 9: completion is sound

A table the round marks complete covers every derivation of its goal. The
proof is by induction on the weight of the derivation (`DW`), where `|` is
free and every other step costs one, refined so that a `|` goal comes after
its branches: the strategy a completing table relies on reads goals whose
derivations weigh less, and each such goal's table is complete already or
completes in the same round.
-/
import RwLog.Rungs.R001.Proofs.Tier0.Inv

namespace RwLog

namespace R001

namespace Tier0

variable {P : Program}

/-- One for a `|`, zero otherwise. -/
def isOr : Rel → Nat
  | .or _ _ => 1
  | _ => 0

theorem isOr_le (e : Rel) : isOr e ≤ 1 := by cases e <;> simp [isOr]

theorem isOr_zero {e : Rel} (h : ∀ a b, e ≠ .or a b) : isOr e = 0 := by
  cases e <;> first | rfl | exact absurd rfl (h _ _)

theorem orBranches_not_or : ∀ (e : Rel), ∀ l ∈ orBranches e, ∀ a b, l ≠ .or a b
  | .or a b, l, hl => by
    simp only [orBranches, List.mem_append] at hl
    rcases hl with hl | hl
    · exact orBranches_not_or a l hl
    · exact orBranches_not_or b l hl
  | .zero, l, hl => by simp only [orBranches, List.mem_singleton] at hl; subst hl; simp
  | .span _, l, hl => by simp only [orBranches, List.mem_singleton] at hl; subst hl; simp
  | .and _ _, l, hl => by simp only [orBranches, List.mem_singleton] at hl; subst hl; simp
  | .seq _ _, l, hl => by simp only [orBranches, List.mem_singleton] at hl; subst hl; simp
  | .conv _, l, hl => by simp only [orBranches, List.mem_singleton] at hl; subst hl; simp
  | .call _, l, hl => by simp only [orBranches, List.mem_singleton] at hl; subst hl; simp

/-- A goal's answers cover a derivation once its table covers the derivations
of the table's goal that weigh no more. -/
theorem dc_via_table {ts : Tables} {d : Goal} {t : Table} (hf : findTable ts d.norm.2 = some t)
    (hgd : GoodG d) (hgt : GoodG t.goal) {w : Nat} {s : Span} (hdw : DW P w d.e s)
    (H : ∀ w' s', DW P w' t.goal.e s' → 2 * w' + isOr t.goal.e ≤ 2 * w + isOr d.e →
      DC P.theory t.answers (GDen t.goal s'.den)) :
    DC P.theory (answersOf ts d) (GDen d s.den) := by
  obtain ⟨w', s', h1, h2, h3, h4⟩ := norm_fwd d hdw
  have hs := (findTable_spec hf).2
  have he := same_e hs
  rw [← he] at h1
  have hm : 2 * w' + isOr t.goal.e ≤ 2 * w + isOr d.e := by
    by_cases hor : ∃ a b, d.e = .or a b
    · obtain ⟨a, b, hab⟩ := hor
      have h1 : isOr d.e = 1 := by rw [hab]; rfl
      rw [h1]; have := isOr_le t.goal.e; omega
    · simp only [not_exists] at hor
      rw [isOr_zero hor]
      rcases h3 hor with h3 | h3
      · have := isOr_le t.goal.e; omega
      · rw [he, isOr_zero h3]; omega
  have hdc := dc_orient d.norm.1 (H w' s' h1 hm)
  rw [same_gden hs hgt (goodG_norm hgd), ← h4, ← answersOf_eq hf] at hdc
  exact hdc

/-- A complete table's goal is covered on every derivation. -/
theorem dc_done {ts : Tables} (hI : TInv P ts) {d : Goal} (hgd : GoodG d)
    (hd : doneOf ts d = true) {s : Span} (h : Derives P d.e s) :
    DC P.theory (answersOf ts d) (GDen d s.den) := by
  unfold doneOf at hd
  cases hf : findTable ts d.norm.2 with
  | none => rw [hf] at hd; simp at hd
  | some t =>
    rw [hf] at hd
    simp only at hd
    obtain ⟨w, hw⟩ := dw_of_derives h
    have ht := (findTable_spec hf).1
    exact dc_via_table hf hgd (hI.good t ht) hw fun _ s' h' _ => hI.comp t ht hd s' h'.derives

theorem dc_conv {dd : Nat} {ts : Tables} {lb rb : Option Span} {a : Rel} {s : Span}
    (h : DC P.theory (answersOf ts (convGoal ⟨lb, .conv a, rb⟩ a))
      (GDen (convGoal ⟨lb, .conv a, rb⟩ a) s.den)) :
    DC P.theory (produce P dd ts ⟨lb, .conv a, rb⟩).1 (GDen ⟨lb, .conv a, rb⟩ s.swap.den) := by
  have h' := h.swap
  rw [← gden_conv ⟨lb, .conv a, rb⟩ a, ← swap_den] at h'
  exact cands_of_strat (by simpa [produce.produceStrategies] using h')

theorem meas_lt {w₁ w : Nat} (e e' : Rel) (h : w₁ < w) (he' : isOr e' = 0) :
    2 * w₁ + isOr e < 2 * w + isOr e' := by
  have := isOr_le e; omega

section
variable (hSE : Obligation.simplify_exact)
include hSE

/-- A table that completes in a round covers every derivation of its goal. -/
theorem compl_dc {st : State} (hwf : ∀ ρ ∈ st.P.theory, ρ.WellFormed) (hI : TInv st.P st.tables) :
    ∀ m, ∀ i ∈ compl st, ∀ (hi : i < st.tables.length) (w : Nat) (s : Span),
      DW st.P w st.tables[i].goal.e s → 2 * w + isOr st.tables[i].goal.e ≤ m →
      DC st.P.theory st.tables[i].answers (GDen st.tables[i].goal s.den) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro i hmem hi w s hw hm
  obtain ⟨_, hnd, hng, deps, hdeps, hdep⟩ := mem_compl hmem
  have hgG := hI.good _ (List.getElem_mem hi)
  -- the table gained nothing, so its candidates are covered by its answers
  suffices hc : DC st.P.theory (produce st.P st.depth st.tables st.tables[i].goal).1
      (GDen st.tables[i].goal s.den) by
    refine hc.covers fun c hc' => ?_
    rw [← outOf_not_done hnd] at hc'
    obtain ⟨y, hy, hyc⟩ := fresh_cover (old := st.tables[i].answers) hc'
    have hnil : fresh st.tables[i].answers (outOf st st.tables[i]).1 = [] := by
      have := hng
      simp only [upd, List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil, List.append_nil] at hy
    exact ⟨y, hy, hyc⟩
  -- the goals of the strategy are covered on lighter derivations
  have hD : ∀ d ∈ deps, GoodG d → ∀ w' s', DW st.P w' d.e s' →
      2 * w' + isOr d.e < 2 * w + isOr st.tables[i].goal.e →
      DC st.P.theory (answersOf st.tables d) (GDen d s'.den) := by
    intro d hd hgd w' s' hw' hlt
    obtain ⟨j, hj, hjl, -, hjd⟩ := hdep d hd
    obtain ⟨_, hf, _⟩ := indexOf_find hj
    have hgt := hI.good _ (List.getElem_mem hjl)
    refine dc_via_table hf hgd hgt hw' fun w'' s'' h'' hle => ?_
    rcases hjd with hjd | hjd
    · exact hI.comp _ (List.getElem_mem hjl) hjd s'' h''.derives
    · exact IH _ (by omega) j hjd hjl w'' s'' h'' le_rfl
  clear hdep hng IH hm hmem
  generalize st.tables[i] = t at *
  obtain ⟨⟨lb, e, rb⟩, ans, dn⟩ := t
  simp only at *
  simp only [strategies, List.mem_append] at hdeps
  rcases hdeps with hdeps | hdeps
  · by_cases hf : unfoldFinal st.P st.depth ⟨lb, e, rb⟩ = true
    · exact dc_unfold hSE hwf hf hw.derives
    · simp [hf] at hdeps
  cases e with
  | zero => cases hw
  | span s₀ => cases hw with | span => exact dc_span hSE hwf lb rb _
  | or a b =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    obtain ⟨l, hl, hwl⟩ := (dw_orBranches _).1 hw
    have hl' := orBranches_not_or _ l hl
    refine dc_or hl (hD ⟨lb, l, rb⟩ ?_ hgG w s hwl ?_)
    · simp only [orLeaves, List.mem_map]; exact ⟨l, hl, rfl⟩
    · rw [isOr_zero hl']; simp [isOr]
  | call n =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    cases hw with
    | call hw =>
      exact dc_call (hD _ (List.mem_singleton_self _) hgG _ s hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl))
  | conv a =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    cases hw with
    | conv hw =>
      exact dc_conv (hD _ (List.mem_singleton_self _) (goodG_convGoal hgG a) _ _ hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl))
  | seq a b =>
    cases hw with
    | seq hw₁ hw₂ hc =>
      rw [compose_some hc]
      have hL : GoodG ⟨lb, a, none⟩ := ⟨hgG.1, trivial⟩
      have hR : GoodG ⟨none, b, rb⟩ := ⟨trivial, hgG.2⟩
      simp only [strategies.tableStrategies, List.mem_append, List.mem_singleton] at hdeps
      rcases hdeps with (rfl | hp) | hp
      · exact dc_seq_join hSE hwf
          (hD _ (by simp [seqLeft]) hL _ _ hw₁ (meas_lt _ _ (by omega) rfl))
          (hD _ (by simp [seqRight]) hR _ _ hw₂ (meas_lt _ _ (by omega) rfl))
      · by_cases hdL : doneOf st.tables ⟨lb, a, none⟩ = true
        · simp only [seqLeft, hdL, ite_true, List.mem_singleton] at hp
          subst hp
          exact dc_seq_pushL hSE hwf hdL (dc_done hI hL hdL hw₁.derives) fun x hx =>
            hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx)) (goodG_pushL hgG b x) _ _ hw₂
              (meas_lt _ _ (by omega) rfl)
        · simp [seqLeft, hdL] at hp
      · by_cases hdR : doneOf st.tables ⟨none, b, rb⟩ = true
        · simp only [seqRight, hdR, ite_true, List.mem_singleton] at hp
          subst hp
          exact dc_seq_pushR hSE hwf hdR (dc_done hI hR hdR hw₂.derives) fun y hy =>
            hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) (goodG_pushR hgG a y) _ _ hw₁
              (meas_lt _ _ (by omega) rfl)
        · simp [seqRight, hdR] at hp
  | and a b =>
    cases hw with
    | and hw₁ hw₂ hc =>
      rw [meet_some hc]
      simp only [strategies.tableStrategies, List.mem_append, List.mem_singleton] at hdeps
      rcases hdeps with (rfl | hp) | hp
      · exact dc_and_join hSE hwf hgG
          (hD ⟨lb, a, rb⟩ (by simp [andLeft]) hgG _ _ hw₁ (meas_lt _ _ (by omega) rfl))
          (hD ⟨lb, b, rb⟩ (by simp [andRight]) hgG _ _ hw₂ (meas_lt _ _ (by omega) rfl))
      · by_cases hdL : doneOf st.tables ⟨lb, a, rb⟩ = true
        · simp only [andLeft, hdL, ite_true, List.mem_singleton] at hp
          subst hp
          exact dc_and_pushL hSE hwf hgG hdL (dc_done hI (d := ⟨lb, a, rb⟩) hgG hdL hw₁.derives) fun x hx =>
            hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx)) (goodG_andPush b x) _ _ hw₂
              (meas_lt _ _ (by omega) rfl)
        · simp [andLeft, hdL] at hp
      · by_cases hdR : doneOf st.tables ⟨lb, b, rb⟩ = true
        · simp only [andRight, hdR, ite_true, List.mem_singleton] at hp
          subst hp
          exact dc_and_pushR hSE hwf hgG hdR (dc_done hI (d := ⟨lb, b, rb⟩) hgG hdR hw₂.derives) fun y hy =>
            hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) (goodG_andPush a y) _ _ hw₁
              (meas_lt _ _ (by omega) rfl)
        · simp [andRight, hdR] at hp

end

/-! ## The invariant holds on every reachable state -/

theorem tinv_ofGoal {g : Goal} (hg : GoodG g) (hb : BU P.theory g) :
    TInv P (State.ofGoal P g).tables := by
  constructor <;> simp only [State.ofGoal, List.mem_singleton] <;> rintro t rfl <;>
    simp [goodG_norm hg, bu_norm hb]

section
variable (hSE : Obligation.simplify_exact) (hSS : Obligation.simplify_stable)
  (hRM : Obligation.refutes_mono)
include hSE hSS hRM

theorem tinv_round {st : State} (hwf : ∀ ρ ∈ st.P.theory, ρ.WellFormed) (hI : TInv st.P st.tables) :
    TInv st.P (round st).1.tables := by
  have key : ∀ t' ∈ (round st).1.tables,
      (∃ t ∈ st.tables, t'.goal = t.goal ∧ t'.answers = t.answers ++ fresh t.answers (outOf st t).1 ∧
        (t'.done = true → t.done = true ∨
          ∀ s, Derives st.P t.goal.e s → DC st.P.theory t.answers (GDen t.goal s.den))) ∨
      (t'.answers = [] ∧ t'.done = false ∧ ∃ t ∈ st.tables,
        ∃ d ∈ (produce st.P st.depth st.tables t.goal).2, t'.goal = d.norm.2) := by
    intro t' ht'
    rcases mem_round ht' with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · refine .inl ⟨_, List.getElem_mem hi, after_goal _ _ _, after_answers _ _ _, fun hd => ?_⟩
      rw [after_done, Bool.or_eq_true] at hd
      rcases hd with hd | hd
      · exact .inl hd
      · right
        intro s hs
        obtain ⟨w, hw⟩ := dw_of_derives hs
        exact compl_dc hSE hwf hI _ i (List.contains_iff_mem.1 hd) hi w s hw le_rfl
    · obtain ⟨t, ht, -, d, hd, rfl⟩ := mem_reqs (mem_newGoals hg)
      exact .inr ⟨rfl, rfl, t, ht, d, hd, rfl⟩
  have cand : ∀ t ∈ st.tables, ∀ a ∈ fresh t.answers (outOf st t).1,
      a ∈ (produce st.P st.depth st.tables t.goal).1 := by
    intro t _ a ha
    have ha' := (fresh_sub ha).1
    cases hdn : t.done
    · rwa [outOf_not_done hdn] at ha'
    · rw [outOf_done hdn] at ha'; simp at ha'
  constructor
  · intro t' ht'
    rcases key t' ht' with ⟨t, ht, hg, -, -⟩ | ⟨-, -, t, ht, d, hd, hg⟩
    · rw [hg]; exact hI.good t ht
    · rw [hg]; exact goodG_norm (deps_good (hI.good t ht) hd)
  · intro t' ht'
    rcases key t' ht' with ⟨t, ht, hg, -, -⟩ | ⟨-, -, t, ht, d, hd, hg⟩
    · rw [hg]; exact hI.bu t ht
    · rw [hg]; exact bu_norm (deps_bu hRM hwf hI (hI.bu t ht) hd)
  · intro t' ht' a ha
    rcases key t' ht' with ⟨t, ht, -, hans, -⟩ | ⟨hans, -⟩
    · rw [hans, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hI.unref t ht a ha
      · exact cands_unref hSS hwf hI (cand t ht a ha)
    · rw [hans] at ha; simp at ha
  · intro t' ht' a ha
    rcases key t' ht' with ⟨t, ht, hg, hans, -⟩ | ⟨hans, -⟩
    · rw [hg]
      rw [hans, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hI.ref t ht a ha
      · exact cands_ref hSE hwf (ansRef_of hI) (hI.good t ht) (cand t ht a ha)
    · rw [hans] at ha; simp at ha
  · intro t' ht'
    rcases key t' ht' with ⟨t, ht, -, hans, -⟩ | ⟨hans, -⟩
    · rw [hans]; exact pw_fresh (hI.pw t ht)
    · rw [hans]; exact List.Pairwise.nil
  · intro t' ht' hd s hs
    rcases key t' ht' with ⟨t, ht, hg, hans, hdone⟩ | ⟨-, hdn, -⟩
    · rw [hg] at hs ⊢
      rcases hdone hd with hd' | hc
      · rw [hans, outOf_done hd', fresh_nil, List.append_nil]
        exact hI.comp t ht hd' s hs
      · rw [hans]
        exact (hc s hs).mono fun a ha => List.mem_append_left _ ha
    · rw [hdn] at hd; exact absurd hd Bool.false_ne_true

end

end Tier0

end R001

end RwLog
