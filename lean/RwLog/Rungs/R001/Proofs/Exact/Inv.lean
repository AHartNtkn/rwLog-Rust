/-
# Exact coverage, part 3: what every table holds

The exact invariant of reachable tables (`XInv`): goals have interface
boundaries, every answer lies under one derivation of its goal, and a
complete table covers, after simplification, every derivation of its goal.
A round preserves it; the proof that a completing table covers its goal is the
weighted induction of Tier 0 (`Tier0.compl_dc`), with the exact strategy
lemmas.
-/
import RwLog.Rungs.R001.Proofs.Exact.Cands

namespace RwLog

namespace R001

namespace Exact


open Tier0

variable {P : Program}

/-- The exact invariant of the tables of a reachable state. -/
structure XInv (P : Program) (ts : Tables) : Prop where
  good : ∀ t ∈ ts, GoodG t.goal
  sub : ∀ t ∈ ts, ∀ a ∈ t.answers, ∃ s, Derives P t.goal.e s ∧ Under P.theory (GDen t.goal s.den) a
  comp : ∀ t ∈ ts, t.done = true → ∀ s, Derives P t.goal.e s →
    XC P.theory t.answers (GDen t.goal s.den)

section
variable (hL : SimpLaws P.theory)
include hL

theorem sub_oS {X : GRel} {a : Span} (f : Bool) (h : Under P.theory X a) :
    Under P.theory (oR f X) (oS f a) := by
  cases f
  · exact h
  · exact sub_swap hL h

theorem xc_orient {A : List Span} {X : GRel} (f : Bool) (h : XC P.theory A X) :
    XC P.theory (orient f A) (oR f X) := by
  cases f
  · exact h
  · exact xc_swap hL h

/-- Reading answers through the table of an equivalent key. -/
theorem ansSub_of {ts : Tables} (hgood : ∀ t ∈ ts, GoodG t.goal)
    (hsub : ∀ t ∈ ts, ∀ a ∈ t.answers, ∃ s, Derives P t.goal.e s ∧ Under P.theory (GDen t.goal s.den) a) :
    AnsSub P ts := by
  intro d hd a ha
  obtain ⟨t, hf, a₀, ha₀, rfl⟩ := answersOf_mem ha
  obtain ⟨ht, hs⟩ := findTable_spec hf
  obtain ⟨s, hds, hr⟩ := hsub t ht a₀ ha₀
  rw [same_e hs] at hds
  obtain ⟨hd', heq⟩ := norm_back d hds
  refine ⟨oS d.norm.1 s, hd', ?_⟩
  rw [heq, ← same_gden hs (hgood t ht) (goodG_norm hd)]
  exact sub_oS hL _ hr

/-- A goal's answers cover a derivation once its table covers the matching
derivation of its key. -/
theorem xc_from_key {ts : Tables} {d : Goal} {t : Table} (hf : findTable ts d.norm.2 = some t)
    (hgd : GoodG d) (hgt : GoodG t.goal) {s s' : Span}
    (h4 : GDen d s.den = oR d.norm.1 (GDen d.norm.2 s'.den))
    (H : XC P.theory t.answers (GDen t.goal s'.den)) :
    XC P.theory (answersOf ts d) (GDen d s.den) := by
  have hdc := xc_orient hL d.norm.1 H
  rw [same_gden (findTable_spec hf).2 hgt (goodG_norm hgd), ← h4, ← answersOf_eq hf] at hdc
  exact hdc

/-- A goal's answers cover a derivation once its table covers the derivations
of the table's goal that weigh no more. -/
theorem xc_via_table {ts : Tables} {d : Goal} {t : Table} (hf : findTable ts d.norm.2 = some t)
    (hgd : GoodG d) (hgt : GoodG t.goal) {w : Nat} {s : Span} (hdw : DW P w d.e s)
    (H : ∀ w' s', DW P w' t.goal.e s' → 2 * w' + isOr t.goal.e ≤ 2 * w + isOr d.e →
      XC P.theory t.answers (GDen t.goal s'.den)) :
    XC P.theory (answersOf ts d) (GDen d s.den) := by
  obtain ⟨w', s', h1, hm, h4⟩ := norm_meas d hdw
  have he := same_e (findTable_spec hf).2
  rw [← he] at h1 hm
  exact xc_from_key hL hf hgd hgt h4 (H w' s' h1 hm)

/-- A complete table's goal is covered on every derivation. -/
theorem xc_done {ts : Tables} (hI : XInv P ts) {d : Goal} (hgd : GoodG d)
    (hd : doneOf ts d = true) {s : Span} (h : Derives P d.e s) :
    XC P.theory (answersOf ts d) (GDen d s.den) := by
  unfold doneOf at hd
  cases hf : findTable ts d.norm.2 with
  | none => rw [hf] at hd; simp at hd
  | some t =>
    rw [hf] at hd
    simp only at hd
    obtain ⟨w, hw⟩ := dw_of_derives h
    have ht := (findTable_spec hf).1
    exact xc_via_table hL hf hgd (hI.good t ht) hw fun _ s' h' _ => hI.comp t ht hd s' h'.derives

end

/-- A table that completes in a round covers every derivation of its goal. -/
theorem compl_xc {st : State} (hL : SimpLaws st.P.theory) (hI : XInv st.P st.tables) :
    ∀ m, ∀ i ∈ compl st, ∀ (hi : i < st.tables.length) (w : Nat) (s : Span),
      DW st.P w st.tables[i].goal.e s → 2 * w + isOr st.tables[i].goal.e ≤ m →
      XC st.P.theory st.tables[i].answers (GDen st.tables[i].goal s.den) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro i hmem hi w s hw hm
  obtain ⟨_, hnd, hng, deps, hdeps, hdep⟩ := mem_compl hmem
  have hgG := hI.good _ (List.getElem_mem hi)
  -- the table gained nothing, so its candidates are covered by its answers
  suffices hc : XC st.P.theory (produce st.P st.depth st.tables st.tables[i].goal).1
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
      XC st.P.theory (answersOf st.tables d) (GDen d s'.den) := by
    intro d hd hgd w' s' hw' hlt
    obtain ⟨j, hj, hjl, -, hjd⟩ := hdep d hd
    obtain ⟨_, hf, _⟩ := indexOf_find hj
    have hgt := hI.good _ (List.getElem_mem hjl)
    refine xc_via_table hL hf hgd hgt hw' fun w'' s'' h'' hle => ?_
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
    · exact xc_unfold hL hf hw.derives
    · simp [hf] at hdeps
  cases e with
  | zero => cases hw
  | span s₀ => cases hw with | span => exact xc_span hL lb rb _
  | or a b =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    obtain ⟨l, hl, hwl⟩ := (dw_orBranches _).1 hw
    have hl' := orBranches_not_or _ l hl
    refine xc_or hl (hD ⟨lb, l, rb⟩ ?_ hgG w s hwl ?_)
    · simp only [orLeaves, List.mem_map]; exact ⟨l, hl, rfl⟩
    · rw [isOr_zero hl']; simp [isOr]
  | call n =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    cases hw with
    | call hw =>
      exact xc_call (hD _ (List.mem_singleton_self _) hgG _ s hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl))
  | conv a =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    cases hw with
    | conv hw =>
      exact xc_conv hL (hD _ (List.mem_singleton_self _) (goodG_convGoal hgG a) _ _ hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl))
  | seq a b =>
    cases hw with
    | seq hw₁ hw₂ hc =>
      rw [compose_some hc]
      have hL' : GoodG ⟨lb, a, none⟩ := ⟨hgG.1, trivial⟩
      have hR : GoodG ⟨none, b, rb⟩ := ⟨trivial, hgG.2⟩
      simp only [strategies.tableStrategies, List.mem_append, List.mem_singleton] at hdeps
      rcases hdeps with (rfl | hp) | hp
      · exact xc_seq_join hL
          (hD _ (by simp [seqLeft]) hL' _ _ hw₁ (meas_lt _ _ (by omega) rfl))
          (hD _ (by simp [seqRight]) hR _ _ hw₂ (meas_lt _ _ (by omega) rfl))
      · by_cases hdL : doneOf st.tables ⟨lb, a, none⟩ = true
        · simp only [seqLeft, hdL, ite_true, List.mem_singleton] at hp
          subst hp
          exact xc_seq_pushL hL hdL (xc_done hL hI hL' hdL hw₁.derives) fun x hx =>
            hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx)) (goodG_pushL hgG b x) _ _ hw₂
              (meas_lt _ _ (by omega) rfl)
        · simp [seqLeft, hdL] at hp
      · by_cases hdR : doneOf st.tables ⟨none, b, rb⟩ = true
        · simp only [seqRight, hdR, ite_true, List.mem_singleton] at hp
          subst hp
          exact xc_seq_pushR hL hdR (xc_done hL hI hR hdR hw₂.derives) fun y hy =>
            hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) (goodG_pushR hgG a y) _ _ hw₁
              (meas_lt _ _ (by omega) rfl)
        · simp [seqRight, hdR] at hp
  | and a b =>
    cases hw with
    | and hw₁ hw₂ hc =>
      rw [meet_some hc]
      simp only [strategies.tableStrategies, List.mem_append, List.mem_singleton] at hdeps
      rcases hdeps with (rfl | hp) | hp
      · exact xc_and_join hL hgG
          (hD ⟨lb, a, rb⟩ (by simp [andLeft]) hgG _ _ hw₁ (meas_lt _ _ (by omega) rfl))
          (hD ⟨lb, b, rb⟩ (by simp [andRight]) hgG _ _ hw₂ (meas_lt _ _ (by omega) rfl))
      · by_cases hdL : doneOf st.tables ⟨lb, a, rb⟩ = true
        · simp only [andLeft, hdL, ite_true, List.mem_singleton] at hp
          subst hp
          exact xc_and_pushL hL hgG hdL (xc_done hL hI (d := ⟨lb, a, rb⟩) hgG hdL hw₁.derives)
            fun x hx => hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx)) (goodG_andPush b x)
              _ _ hw₂ (meas_lt _ _ (by omega) rfl)
        · simp [andLeft, hdL] at hp
      · by_cases hdR : doneOf st.tables ⟨lb, b, rb⟩ = true
        · simp only [andRight, hdR, ite_true, List.mem_singleton] at hp
          subst hp
          exact xc_and_pushR hL hgG hdR (xc_done hL hI (d := ⟨lb, b, rb⟩) hgG hdR hw₂.derives)
            fun y hy => hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) (goodG_andPush a y)
              _ _ hw₁ (meas_lt _ _ (by omega) rfl)
        · simp [andRight, hdR] at hp

/-! ## The invariant holds on every reachable state -/

theorem xinv_ofGoal {g : Goal} (hg : GoodG g) : XInv P (State.ofGoal P g).tables := by
  constructor <;> simp only [State.ofGoal, List.mem_singleton] <;> rintro t rfl <;>
    simp [goodG_norm hg]

theorem xinv_round {st : State} (hL : SimpLaws st.P.theory) (hI : XInv st.P st.tables) :
    XInv st.P (round st).1.tables := by
  have key : ∀ t' ∈ (round st).1.tables,
      (∃ t ∈ st.tables, t'.goal = t.goal ∧ t'.answers = t.answers ++ fresh t.answers (outOf st t).1 ∧
        (t'.done = true → t.done = true ∨
          ∀ s, Derives st.P t.goal.e s → XC st.P.theory t.answers (GDen t.goal s.den))) ∨
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
        exact compl_xc hL hI _ i (List.contains_iff_mem.1 hd) hi w s hw le_rfl
    · obtain ⟨t, ht, -, d, hd, rfl⟩ := mem_reqs (mem_newGoals hg)
      exact .inr ⟨rfl, rfl, t, ht, d, hd, rfl⟩
  constructor
  · intro t' ht'
    rcases key t' ht' with ⟨t, ht, hg, -, -⟩ | ⟨-, -, t, ht, d, hd, hg⟩
    · rw [hg]; exact hI.good t ht
    · rw [hg]; exact goodG_norm (deps_good (hI.good t ht) hd)
  · intro t' ht' a ha
    rcases key t' ht' with ⟨t, ht, hg, hans, -⟩ | ⟨hans, -⟩
    · rw [hg]
      rw [hans, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hI.sub t ht a ha
      · exact cands_sub hL (ansSub_of hL hI.good hI.sub) (hI.good t ht) (fresh_cand st ha)
    · rw [hans] at ha; simp at ha
  · intro t' ht' hd s hs
    rcases key t' ht' with ⟨t, ht, hg, hans, hdone⟩ | ⟨-, hdn, -⟩
    · rw [hg] at hs ⊢
      rcases hdone hd with hd' | hc
      · rw [hans, outOf_done hd', fresh_nil, List.append_nil]
        exact hI.comp t ht hd' s hs
      · rw [hans]
        exact (hc s hs).mono fun a ha => List.mem_append_left _ ha
    · rw [hdn] at hd; exact absurd hd Bool.false_ne_true

theorem xinv_iter {st : State} (hL : SimpLaws st.P.theory) (hI : XInv st.P st.tables) :
    ∀ k, XInv st.P (iter st k).tables
  | 0 => hI
  | k + 1 => by
    have h := xinv_iter hL hI k
    have hP := iter_P st k
    rw [← hP] at h hL
    have := xinv_round hL h
    rw [hP] at this
    exact this

end Exact

end R001

end RwLog
