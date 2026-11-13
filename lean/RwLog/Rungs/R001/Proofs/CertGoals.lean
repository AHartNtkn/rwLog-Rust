/-
# Rung R001: certificates goal by goal

Rules that give a goal a certificate from certificates of the goals it reads:
a span goal always has one, a call has one when its body does, a `|` when
every branch does, and a sequence when both halves do. With the push rules of
`CertCombine` these let a termination proof follow the shape of a program.

They rest on `pre_add`: a goal can be added to a rootless certificate that
lists the goals of one of its strategies. Its cover is built from what the
strategy computes from the listed covers, which covers everything the goal
derives because every listed table is complete (`xc_of_done`).
-/
import RwLog.Rungs.R001.Proofs.Tabling

namespace RwLog

namespace R001

namespace Combine

open Tier0 Exact CertHalts CertOfHalt Symmetry

variable {P : Program}

/-- A goal with a certificate. -/
def HasCert (P : Program) (g : Goal) : Prop := ∃ C D, Cert.Valid P C D g

theorem HasCert.of_norm {g h : Goal} (hg : HasCert P g) (e : g.norm = h.norm) : HasCert P h :=
  let ⟨C, D, hC⟩ := hg; ⟨C, D, valid_root_eq hC e⟩

theorem listed_of_done {C : List CertEntry} {d : Goal} (h : doneOf (certTables C) d = true) :
    ∃ e ∈ C, e.goal.same d.norm.2 = true := by
  unfold doneOf at h
  rw [findTable_certTables] at h
  cases hf : C.find? (fun e => e.goal.same d.norm.2) with
  | none => rw [hf] at h; cases h
  | some e =>
    exact ⟨e, List.mem_of_find?_eq_some hf,
      List.find?_some (p := fun e : CertEntry => e.goal.same d.norm.2) hf⟩

section Laws

variable (hL : SimpLaws P.theory)
include hL

/-- A strategy whose goals all have complete tables computes candidates that
cover every derivation of the goal. -/
theorem xc_of_done {ts : Tables} (hI : XInv P ts) {g : Goal} (hgG : GoodG g) {deps : List Goal}
    (hdeps : deps ∈ strategies.tableStrategies P ts g) (hall : ∀ d ∈ deps, doneOf ts d = true)
    (D : Nat) {s : Span} (hs : Derives P g.e s) : XC P.theory (produce P D ts g).1 (GDen g s.den) := by
  have hD : ∀ d ∈ deps, GoodG d → ∀ s', Derives P d.e s' →
      XC P.theory (answersOf ts d) (GDen d s'.den) :=
    fun d hd hgd s' h' => xc_done hL hI hgd (hall d hd) h'
  obtain ⟨w, hw⟩ := dw_of_derives hs
  obtain ⟨lb, e, rb⟩ := g
  cases e with
  | zero => cases hw
  | span s₀ => cases hw with | span => exact xc_span hL lb rb _
  | or a b =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    obtain ⟨l, hl, hwl⟩ := (dw_orBranches _).1 hw
    refine xc_or hl (hD ⟨lb, l, rb⟩ ?_ hgG s hwl.derives)
    simp only [orLeaves, List.mem_map]; exact ⟨l, hl, rfl⟩
  | call n =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    cases hw with
    | call hw => exact xc_call (hD _ (List.mem_singleton_self _) hgG s hw.derives)
  | conv a =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    cases hw with
    | conv hw =>
      exact xc_conv hL (hD _ (List.mem_singleton_self _) (goodG_convGoal hgG a) _ hw.derives)
  | seq a b =>
    cases hw with
    | seq hw₁ hw₂ hc =>
      rw [compose_some hc]
      have hL' : GoodG ⟨lb, a, none⟩ := ⟨hgG.1, trivial⟩
      have hR : GoodG ⟨none, b, rb⟩ := ⟨trivial, hgG.2⟩
      simp only [strategies.tableStrategies, List.mem_append, List.mem_singleton] at hdeps
      rcases hdeps with (rfl | hp) | hp
      · exact xc_seq_join hL (hD _ (by simp [seqLeft]) hL' _ hw₁.derives)
          (hD _ (by simp [seqRight]) hR _ hw₂.derives)
      · by_cases hdL : doneOf ts ⟨lb, a, none⟩ = true
        · simp only [seqLeft, hdL, ite_true, List.mem_singleton] at hp
          subst hp
          exact xc_seq_pushL hL hdL (xc_done hL hI hL' hdL hw₁.derives) fun x hx =>
            hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx)) (goodG_pushL hgG b x) _
              hw₂.derives
        · simp [seqLeft, hdL] at hp
      · by_cases hdR : doneOf ts ⟨none, b, rb⟩ = true
        · simp only [seqRight, hdR, ite_true, List.mem_singleton] at hp
          subst hp
          exact xc_seq_pushR hL hdR (xc_done hL hI hR hdR hw₂.derives) fun y hy =>
            hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) (goodG_pushR hgG a y) _
              hw₁.derives
        · simp [seqRight, hdR] at hp
  | and a b =>
    cases hw with
    | and hw₁ hw₂ hc =>
      rw [meet_some hc]
      simp only [strategies.tableStrategies, List.mem_append, List.mem_singleton] at hdeps
      rcases hdeps with (rfl | hp) | hp
      · exact xc_and_join hL hgG (hD ⟨lb, a, rb⟩ (by simp [andLeft]) hgG _ hw₁.derives)
          (hD ⟨lb, b, rb⟩ (by simp [andRight]) hgG _ hw₂.derives)
      · by_cases hdL : doneOf ts ⟨lb, a, rb⟩ = true
        · simp only [andLeft, hdL, ite_true, List.mem_singleton] at hp
          subst hp
          exact xc_and_pushL hL hgG hdL (xc_done hL hI (d := ⟨lb, a, rb⟩) hgG hdL hw₁.derives)
            fun x hx => hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx)) (goodG_andPush b x)
              _ hw₂.derives
        · simp [andLeft, hdL] at hp
      · by_cases hdR : doneOf ts ⟨lb, b, rb⟩ = true
        · simp only [andRight, hdR, ite_true, List.mem_singleton] at hp
          subst hp
          exact xc_and_pushR hL hgG hdR (xc_done hL hI (d := ⟨lb, b, rb⟩) hgG hdR hw₂.derives)
            fun y hy => hD _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) (goodG_andPush a y)
              _ hw₁.derives
        · simp [andRight, hdR] at hp

/-- A goal can be added to a rootless certificate that lists the goals of one
of its strategies. -/
theorem pre_add {C' : List CertEntry} {D : Nat} (h : Pre P C' D) {k : Goal} (hk : GoodG k)
    {deps : List Goal} (hdeps : deps ∈ strategies.tableStrategies P (certTables C') k)
    (hall : ∀ d ∈ deps, ∃ e ∈ C', e.goal.same d.norm.2 = true) :
    ∃ F ρ, Pre P (C' ++ [⟨k, F, ρ⟩]) D := by
  have hI := xinv_certTables hL h.1
  obtain ⟨F, hF1, hF2⟩ := cover_exists hL hk (produce P D (certTables C') k).1 fun a ha =>
    cands_sub hL (ansSub_of hL hI.good hI.sub) hk ha
  refine ⟨F, (C'.map CertEntry.rank).sum + 1, ?_⟩
  have hgk : GoodE P ⟨k, F, (C'.map CertEntry.rank).sum + 1⟩ :=
    ⟨hk, hF1, fun s hs =>
      (xc_of_done hL hI hk hdeps (fun d hd => doneOf_certTables (hall d hd)) D hs).covers hF2⟩
  have hg : ∀ e ∈ C' ++ [⟨k, F, (C'.map CertEntry.rank).sum + 1⟩], GoodE P e := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact h.1 e he
    · cases List.mem_singleton.1 he; exact hgk
  refine ⟨hg, fun e he => ?_⟩
  rcases List.mem_append.1 he with he | he
  · exact (h.2 e he).imp id fun ⟨_, hst, hall'⟩ =>
      strat_transfer hL (fun _ => List.mem_append_left _) hg hst hall'
  · cases List.mem_singleton.1 he
    refine .inr (strat_cert (certTables C') _ k
      (fun d => ∃ e ∈ C', e.goal.same d.norm.2 = true) ?_ ?_ ?_ hdeps hall)
    · rintro d ⟨e', he', hs'⟩
      exact ⟨e', List.mem_append_left _ he', hs', by
        have := rank_le_sum he'
        simp only [Bool.false_eq_true, ite_false]; omega⟩
    · rintro d ⟨e', he', hs'⟩ -
      exact ⟨e', List.mem_append_left _ he', hs', by
        have := rank_le_sum he'
        simp only [ite_true]; omega⟩
    · intro L hdn x hx
      rw [answersOf_certTables]
      obtain ⟨eL, heL, hsL⟩ := listed_of_done hdn
      exact maxima_transfer hL h.1 hg ⟨eL, heL, hsL⟩ ⟨eL, List.mem_append_left _ heL, hsL⟩ x hx

/-- Certificates for finitely many goals, put together. -/
theorem pre_goals : ∀ l : List Goal, (∀ d ∈ l, HasCert P d) →
    ∃ C D, Pre P C D ∧ ∀ d ∈ l, ∃ e ∈ C, e.goal.same d.norm.2 = true
  | [], _ => ⟨[], 0, pre_nil P 0, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, h => by
    obtain ⟨C₁, D₁, hC₁⟩ := h x List.mem_cons_self
    obtain ⟨C₂, D₂, hp, hl⟩ := pre_goals l fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨C₁ ++ C₂, max D₁ D₂, pre_append hL (pre_mono (pre_of_valid hL hC₁) (le_max_left _ _))
      (pre_mono hp (le_max_right _ _)), fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · obtain ⟨e, he, hs⟩ := hC₁.1
      exact ⟨e, List.mem_append_left _ he, hs⟩
    · obtain ⟨e, he, hs⟩ := hl y hy
      exact ⟨e, List.mem_append_right _ he, hs⟩

/-- A goal has a certificate when the goals of a strategy of its key that does
not push have certificates. -/
theorem hasCert_of_deps {g : Goal} (hg : GoodG g) {deps : List Goal}
    (hdeps : ∀ ts, deps ∈ strategies.tableStrategies P ts g.norm.2)
    (hall : ∀ d ∈ deps, HasCert P d) : HasCert P g := by
  obtain ⟨C', D, hpre, hl⟩ := pre_goals hL deps hall
  obtain ⟨F, ρ, hfin⟩ := pre_add hL hpre (goodG_norm hg) (hdeps _) hl
  exact ⟨_, D, valid_of_pre hL hfin
    ⟨⟨g.norm.2, F, ρ⟩, List.mem_append_right _ (List.mem_singleton_self _), Goal.same_refl _⟩⟩

theorem hasCert_span {lb rb : Option Span} {s : Span} (hg : GoodG ⟨lb, .span s, rb⟩) :
    HasCert P ⟨lb, .span s, rb⟩ := by
  refine hasCert_of_deps hL hg (deps := []) (fun ts => ?_) (fun _ h => absurd h List.not_mem_nil)
  rw [show (⟨lb, .span s, rb⟩ : Goal).norm.2 = ⟨lb, .span s, rb⟩ by
    simp only [Goal.norm, canon]; rw [strip_nc _ (by simp)]]
  simp [strategies.tableStrategies]

theorem hasCert_call {lb rb : Option Span} {n : Name} (hg : GoodG ⟨lb, .call n, rb⟩)
    (h : HasCert P ⟨lb, P.body n, rb⟩) : HasCert P ⟨lb, .call n, rb⟩ := by
  refine hasCert_of_deps hL hg (deps := [⟨lb, P.body n, rb⟩]) (fun ts => ?_) (fun d hd => ?_)
  · rw [show (⟨lb, .call n, rb⟩ : Goal).norm.2 = ⟨lb, .call n, rb⟩ by
      simp only [Goal.norm, canon]; rw [strip_nc _ (by simp)]]
    simp [strategies.tableStrategies, callGoal]
  · cases List.mem_singleton.1 hd; exact h

theorem hasCert_seq {lb rb : Option Span} {a b : Rel} (hg : GoodG ⟨lb, .seq a b, rb⟩)
    (ha : HasCert P ⟨lb, a, none⟩) (hb : HasCert P ⟨none, b, rb⟩) :
    HasCert P ⟨lb, .seq a b, rb⟩ := by
  refine hasCert_of_deps hL hg (deps := [⟨lb, canon a, none⟩, ⟨none, canon b, rb⟩])
    (fun ts => ?_) (fun d hd => ?_)
  · rw [norm_seq_root]
    simp [strategies.tableStrategies, seqLeft, seqRight]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ha.of_norm (norm_canon _ _ _).symm
    · exact hb.of_norm (norm_canon _ _ _).symm

/-- A `|` has a certificate when each of its branches does. -/
theorem hasCert_or {lb rb : Option Span} {a b : Rel} (hg : GoodG ⟨lb, .or a b, rb⟩)
    (h : ∀ l ∈ orBranches (.or a b), HasCert P ⟨lb, l, rb⟩) : HasCert P ⟨lb, .or a b, rb⟩ := by
  have hraw : ∀ z ∈ sortedBranches (orBranches (canon a) ++ orBranches (canon b)),
      ∃ l ∈ orBranches (.or a b), canon l = z := by
    intro z hz
    obtain ⟨hz1, hz0⟩ := mem_sortedBranches.1 hz
    rcases List.mem_append.1 hz1 with h | h
    · obtain ⟨l, hl, e⟩ := (mem_orBranches_canon a hz0).1 h
      exact ⟨l, by simp [orBranches, hl], e⟩
    · obtain ⟨l, hl, e⟩ := (mem_orBranches_canon b hz0).1 h
      exact ⟨l, by simp [orBranches, hl], e⟩
  have hno : ∀ x ∈ sortedBranches (orBranches (canon a) ++ orBranches (canon b)), NotOr x :=
    notOr_sorted fun x hx => (List.mem_append.1 hx).elim notOr_of_mem_orBranches
      notOr_of_mem_orBranches
  have hnorm : (⟨lb, .or a b, rb⟩ : Goal).norm =
      Goal.stripConv ⟨lb, mkOr (sortedBranches (orBranches (canon a) ++ orBranches (canon b))), rb⟩ :=
    rfl
  generalize hbs : sortedBranches (orBranches (canon a) ++ orBranches (canon b)) = bs at *
  match bs, hbs with
  | [], _ =>
    refine hasCert_of_deps hL hg (deps := []) (fun ts => ?_) (fun _ h => absurd h List.not_mem_nil)
    rw [hnorm, show mkOr [] = Rel.zero from rfl, strip_nc _ (by simp)]
    simp [strategies.tableStrategies]
  | [c], _ =>
    obtain ⟨l, hl, rfl⟩ := hraw c (by simp)
    exact (h l hl).of_norm (by rw [hnorm]; rfl)
  | c₁ :: c₂ :: rest, _ =>
    refine hasCert_of_deps hL hg (deps := (c₁ :: c₂ :: rest).map fun z => ⟨lb, z, rb⟩)
      (fun ts => ?_) (fun d hd => ?_)
    · rw [hnorm, show mkOr (c₁ :: c₂ :: rest) = .or c₁ (mkOr (c₂ :: rest)) from rfl,
        strip_nc _ (by simp)]
      simp only [strategies.tableStrategies, List.mem_singleton, orLeaves]
      rw [show Rel.or c₁ (mkOr (c₂ :: rest)) = mkOr (c₁ :: c₂ :: rest) from rfl,
        orBranches_mkOr_eq hno (by simp)]
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hd
      obtain ⟨l, hl, rfl⟩ := hraw z hz
      exact (h l hl).of_norm (norm_canon _ _ _).symm

end Laws

end Combine

end R001

end RwLog
