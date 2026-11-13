/-
# Exact coverage, part 5: derivable answers and certificates

* `gderives_sub`: every derivable answer of a goal (`GDerives`) lies under one
  derivation of the goal's expression.
* `realise`: conversely, whatever lies under a derivation is covered by a
  derivable answer, built with the joining constructors alone.
* `cert_xc`: the covers of a valid certificate cover, exactly, every
  derivation of their goals.
-/
import RwLog.Rungs.R001.Proofs.Exact.Inv
import RwLog.Rungs.R001.Proofs.TerminationBasics

namespace RwLog

namespace R001

namespace Exact

open Lifting (LCov bden PId)
open Tier0

variable {P : Program} (hL : SimpLaws P.theory)
include hL

/-- A derivable answer lies under one derivation of the goal. -/
theorem gderives_sub {g : Goal} {y : Span} (h : GDerives P g y) :
    GoodG g → ∃ s, Derives P g.e s ∧ Sub P.theory (GDen g s.den) y := by
  induction h with
  | unfold hx => exact fun _ => unfold_sub hx
  | @span lb rb s x hx =>
    intro _
    obtain ⟨w, hw, hwd⟩ := spanAnswer_den hx
    exact ⟨s, .span s, (live_sub hw).of_eq hwd⟩
  | @or g a b h x he hh _ ih =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    simp only [orLeaves, List.mem_map] at hh
    obtain ⟨l, hl, rfl⟩ := hh
    obtain ⟨s, hs, hr⟩ := ih hg
    exact ⟨s, Lifting.derives_of_branch hl hs, hr⟩
  | @call g n x he _ ih =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    obtain ⟨s, hs, hr⟩ := ih hg
    exact ⟨s, .call hs, hr⟩
  | @conv g a x he _ ih =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    obtain ⟨s, hs, hr⟩ := ih (goodG_convGoal hg a)
    refine ⟨s.swap, .conv hs, ?_⟩
    rw [swap_den]
    exact (sub_swap hL hr).of_eq (gden_conv ⟨lb, .conv a, rb⟩ a s.den).symm
  | @seq g a b x y z he _ _ hc ih₁ ih₂ =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    obtain ⟨s₁, hs₁, hr₁⟩ := ih₁ ⟨hg.1, trivial⟩
    obtain ⟨s₂, hs₂, hr₂⟩ := ih₂ ⟨trivial, hg.2⟩
    have hr := composeLive_sub hL hr₁ hr₂ hc
    rw [seqLeft, seqRight, gden_seq lb rb a b (.seq a b)] at hr
    obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty hr.nonempty)
    exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
  | @seqPushL g a b x y z he _ _ hc ih₁ ih₂ =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    obtain ⟨s₁, hs₁, hr₁⟩ := ih₁ ⟨hg.1, trivial⟩
    obtain ⟨s₂, hs₂, hr₂⟩ := ih₂ (goodG_pushL hg b x)
    have hne : ((s₂.den).comp (bden rb)).Nonempty := by
      have := hr₂.nonempty
      simp only [seqPushL, GDen] at this
      exact GRel.comp_nonempty_right this
    obtain ⟨u, hu⟩ := rep_right hne
    have hr := push_comp_subL hL (u := u) (Q := GDen ⟨lb, .seq a b, rb⟩ ((s₁.den).comp s₂.den))
      hr₁ hr₂ (by rw [hu]; simp only [seqPushL]; rw [gden_pushL]; exact LCov.refl _)
      (fun w hw => by
        rw [hu, ← gden_seqL lb rb a (.seq a b)]
        exact hw.comp (LCov.refl _)) hc
    obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty hr.nonempty)
    exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
  | @seqPushR g a b x y z he _ _ hc ih₂ ih₁ =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    obtain ⟨s₂, hs₂, hr₂⟩ := ih₂ ⟨trivial, hg.2⟩
    obtain ⟨s₁, hs₁, hr₁⟩ := ih₁ (goodG_pushR hg a y)
    have hne : ((bden lb).comp s₁.den).Nonempty := by
      have := hr₁.nonempty
      simp only [seqPushR, GDen] at this
      rw [← GRel.comp_assoc] at this
      exact GRel.comp_nonempty_left this
    obtain ⟨u, hu⟩ := rep_left hne
    have hr := push_comp_subR hL (u := u) (Q := GDen ⟨lb, .seq a b, rb⟩ ((s₁.den).comp s₂.den))
      hr₁ hr₂ (by rw [hu]; simp only [seqPushR]; rw [gden_pushR]; exact LCov.refl _)
      (fun w hw => by
        rw [hu, ← gden_seqR lb rb b (.seq a b)]
        exact (LCov.refl _).comp hw) hc
    obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty hr.nonempty)
    exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
  | @and g a b x y z he _ _ hc ih₁ ih₂ =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    obtain ⟨s₁, hs₁, hr₁⟩ := ih₁ hg
    obtain ⟨s₂, hs₂, hr₂⟩ := ih₂ hg
    have hr := meetLive_sub hL hr₁ hr₂ hc
    rw [andLeft, andRight, gden_and hg a b (.and a b)] at hr
    obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty hr.nonempty)
    exact ⟨s, .and hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
  | @andPushL g a b x y z he _ _ hc ih₁ ih₂ =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    have pB := pid_of_goodBO hg.1
    have pC := pid_of_goodBO hg.2
    obtain ⟨s₁, hs₁, hr₁⟩ := ih₁ hg
    obtain ⟨s₂, hs₂, hr₂⟩ := ih₂ (goodG_andPush b x)
    have hr := push_meet_subL hL (u := s₂) (Q := GDen ⟨lb, .and a b, rb⟩ ((s₁.den).meet s₂.den))
      hr₁ hr₂ (by rw [gden_andPush]; exact LCov.refl _)
      (fun w hw => by
        rw [← gden_and hg a b (.and a b)]
        exact and_dom pB pC hw) hc
    obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty hr.nonempty)
    exact ⟨s, .and hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
  | @andPushR g a b x y z he _ _ hc ih₂ ih₁ =>
    intro hg
    obtain ⟨lb, e, rb⟩ := g
    simp only at he; subst he
    have pB := pid_of_goodBO hg.1
    have pC := pid_of_goodBO hg.2
    obtain ⟨s₂, hs₂, hr₂⟩ := ih₂ hg
    obtain ⟨s₁, hs₁, hr₁⟩ := ih₁ (goodG_andPush a y)
    have hr := push_meet_subR hL (u := s₁) (Q := GDen ⟨lb, .and a b, rb⟩ ((s₁.den).meet s₂.den))
      hr₁ hr₂ (by
        rw [Lifting.meet_comm (GDen (andPush a y) s₁.den), gden_andPush, Lifting.meet_comm]
        exact LCov.refl _)
      (fun w hw => by
        rw [← gden_and hg a b (.and a b), Lifting.meet_comm, Lifting.meet_comm (s₁.den)]
        exact and_dom pB pC hw) hc
    obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty hr.nonempty)
    exact ⟨s, .and hs₁ hs₂ hs, by rw [hsd]; exact hr⟩

/-- Whatever lies under a derivation of a goal is covered by a derivable
answer of the goal. -/
theorem realise : ∀ m, ∀ g : Goal, GoodG g → ∀ (w : Nat) (s : Span), DW P w g.e s →
    2 * w + isOr g.e ≤ m → ∀ v v' : Span, Dom (GDen g s.den) v.den →
      P.theory.simplify v = some v' → ∃ y, GDerives P g y ∧ y.Covers v' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro g hg w s hw hm v v' hv hs
  obtain ⟨lb, e, rb⟩ := g
  cases e with
  | zero => cases hw
  | span s₀ =>
    cases hw with
    | span =>
      obtain ⟨u, hub, hu⟩ := spanBoth_of_nonempty (hv.nonempty v.den_nonempty)
      obtain ⟨u', hu', hc⟩ := simp_mono hL (covers_of_dom (by rw [hu]; exact hv)) hs
      refine ⟨u', .span ?_, hc⟩
      rw [spanAnswer_eq, hub]
      simp [live, hu']
  | or a b =>
    obtain ⟨l, hl, hwl⟩ := (dw_orBranches _).1 hw
    have hl' := orBranches_not_or _ l hl
    obtain ⟨y, hy, hc⟩ := IH (2 * w + isOr l) (by rw [isOr_zero hl']; simp only [isOr] at hm ⊢; omega)
      ⟨lb, l, rb⟩ hg w s hwl le_rfl v v' hv hs
    exact ⟨y, .or (g := ⟨lb, .or a b, rb⟩) rfl (List.mem_map.2 ⟨l, hl, rfl⟩) hy, hc⟩
  | call n =>
    cases hw with
    | @call w₀ _ _ hw₀ =>
      have := isOr_le (P.body n)
      obtain ⟨y, hy, hc⟩ := IH (2 * w₀ + isOr (P.body n)) (by simp only [isOr] at hm; omega)
        (callGoal P ⟨lb, .call n, rb⟩ n) hg w₀ s hw₀ le_rfl v v' hv hs
      exact ⟨y, .call (g := ⟨lb, .call n, rb⟩) rfl hy, hc⟩
  | conv a =>
    cases hw with
    | @conv w₀ _ s₀ hw₀ =>
      have := isOr_le a
      have hv' : Dom (GDen (convGoal ⟨lb, .conv a, rb⟩ a) s₀.den) v.swap.den := by
        rw [swap_den] at hv ⊢
        rw [gden_conv ⟨lb, .conv a, rb⟩ a] at hv
        exact hv.inv
      have hs' : P.theory.simplify v.swap = some v'.swap := by rw [hL.swap, hs]; rfl
      obtain ⟨y, hy, hc⟩ := IH (2 * w₀ + isOr a) (by simp only [isOr] at hm; omega)
        (convGoal ⟨lb, .conv a, rb⟩ a) (goodG_convGoal hg a) w₀ s₀ hw₀ le_rfl _ _ hv' hs'
      exact ⟨y.swap, .conv (g := ⟨lb, .conv a, rb⟩) rfl hy, covers_swap hc⟩
  | seq a b =>
    cases hw with
    | @seq w₁ w₂ _ _ s₁ s₂ _ hw₁ hw₂ hcs =>
      have := isOr_le a
      have := isOr_le b
      rw [compose_some hcs, ← gden_seq lb rb a b (.seq a b)] at hv
      have hne := hv.nonempty v.den_nonempty
      have hgL : GoodG ⟨lb, a, none⟩ := ⟨hg.1, trivial⟩
      have hgR : GoodG ⟨none, b, rb⟩ := ⟨trivial, hg.2⟩
      obtain ⟨u₁, hu₁⟩ := rep_gden (g := ⟨lb, a, none⟩) (GRel.comp_nonempty_left hne)
      obtain ⟨u₂, hu₂⟩ := rep_gden (g := ⟨none, b, rb⟩) (GRel.comp_nonempty_right hne)
      obtain ⟨u, hu, hud⟩ := compose_isSome (s₁ := u₁) (s₂ := u₂) (by rw [hu₁, hu₂]; exact hne)
      obtain ⟨u', hu', hcu⟩ := simp_mono hL (covers_of_dom (by rw [hud, hu₁, hu₂]; exact hv)) hs
      obtain ⟨a', b', z', c', ha', hb', hz', hc', he⟩ := simp_comp_both hL hu hu'
      obtain ⟨x, hx, hcx⟩ := IH (2 * w₁ + isOr a) (by simp only [isOr] at hm; omega)
        ⟨lb, a, none⟩ hgL w₁ s₁ hw₁ le_rfl u₁ a' (by rw [hu₁]; exact LCov.refl _) ha'
      obtain ⟨y, hy, hcy⟩ := IH (2 * w₂ + isOr b) (by simp only [isOr] at hm; omega)
        ⟨none, b, rb⟩ hgR w₂ s₂ hw₂ le_rfl u₂ b' (by rw [hu₂]; exact LCov.refl _) hb'
      obtain ⟨z'', hz'', hcz⟩ := compose_mono hcx hcy hz'
      obtain ⟨c'', hc'', hcc⟩ := simp_mono hL hcz hc'
      refine ⟨c'', .seq (g := ⟨lb, .seq a b, rb⟩) rfl hx hy ?_, (hcc.trans he.1).trans hcu⟩
      unfold composeLive
      rw [hz'']
      simp [live, hc'']
  | and a b =>
    cases hw with
    | @and w₁ w₂ _ _ s₁ s₂ _ hw₁ hw₂ hcs =>
      have := isOr_le a
      have := isOr_le b
      rw [meet_some hcs, ← gden_and (g := ⟨lb, .and a b, rb⟩) hg a b (.and a b)] at hv
      have hne := hv.nonempty v.den_nonempty
      have hgL : GoodG ⟨lb, a, rb⟩ := hg
      have hgR : GoodG ⟨lb, b, rb⟩ := hg
      obtain ⟨u₁, hu₁⟩ := rep_gden (g := ⟨lb, a, rb⟩) (meet_nonempty_left hne)
      obtain ⟨u₂, hu₂⟩ := rep_gden (g := ⟨lb, b, rb⟩) (meet_nonempty_right hne)
      obtain ⟨u, hu, hud⟩ := meet_isSome (s₁ := u₁) (s₂ := u₂) (by rw [hu₁, hu₂]; exact hne)
      obtain ⟨u', hu', hcu⟩ := simp_mono hL (covers_of_dom (by rw [hud, hu₁, hu₂]; exact hv)) hs
      obtain ⟨a', b', z', c', ha', hb', hz', hc', he⟩ := simp_meet_both hL hu hu'
      obtain ⟨x, hx, hcx⟩ := IH (2 * w₁ + isOr a) (by simp only [isOr] at hm; omega)
        ⟨lb, a, rb⟩ hgL w₁ s₁ hw₁ le_rfl u₁ a' (by rw [hu₁]; exact LCov.refl _) ha'
      obtain ⟨y, hy, hcy⟩ := IH (2 * w₂ + isOr b) (by simp only [isOr] at hm; omega)
        ⟨lb, b, rb⟩ hgR w₂ s₂ hw₂ le_rfl u₂ b' (by rw [hu₂]; exact LCov.refl _) hb'
      obtain ⟨z'', hz'', hcz⟩ := meet_mono hcx hcy hz'
      obtain ⟨c'', hc'', hcc⟩ := simp_mono hL hcz hc'
      refine ⟨c'', .and (g := ⟨lb, .and a b, rb⟩) rfl hx hy ?_, (hcc.trans he.1).trans hcu⟩
      unfold meetLive
      rw [hz'']
      simp [live, hc'']

/-- An answer under a derivation of a goal is covered by a derivable answer of
the goal. -/
theorem realise_sub {g : Goal} (hg : GoodG g) {s a : Span} (hs : Derives P g.e s)
    (ha : Sub P.theory (GDen g s.den) a) : ∃ y, GDerives P g y ∧ y.Covers a := by
  obtain ⟨w, hw⟩ := dw_of_derives hs
  obtain ⟨v, hv, v', hv', hc⟩ := ha
  obtain ⟨y, hy, hcy⟩ := realise hL _ g hg w s hw le_rfl v v' hv hv'
  exact ⟨y, hy, hcy.trans hc⟩

/-- Every cover of a valid certificate covers, exactly, every derivation of
its goal. -/
theorem cert_xc {C : List CertEntry} {D : Nat} {root : Goal} (hC : Cert.Valid P C D root) :
    ∀ m, ∀ e ∈ C, ∀ (w : Nat) (s : Span), DW P w e.goal.e s → 2 * w + isOr e.goal.e ≤ m →
      XC P.theory e.cover (GDen e.goal s.den) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro e he w s hw hm
  obtain ⟨hint, -, hclos, hstrat⟩ := hC.2 e he
  have hgG : GoodG e.goal := goodG_of_interfaced hint
  suffices hc : XC P.theory (produce P D (certTables C) e.goal).1 (GDen e.goal s.den) from
    hc.covers hclos
  have hD : ∀ d : Goal, (∃ e' ∈ C, e'.goal.same d.norm.2 = true) → GoodG d → ∀ w' s',
      DW P w' d.e s' → 2 * w' + isOr d.e < 2 * w + isOr e.goal.e →
      XC P.theory (answersOf (certTables C) d) (GDen d s'.den) := by
    intro d hd hgd w' s' hw' hlt
    obtain ⟨e'', he'', hf⟩ := certTables_found hd
    have hgt : GoodG e''.goal := goodG_of_interfaced (hC.2 e'' he'').1
    exact xc_via_table hL hf hgd hgt hw' fun w'' s'' h'' hle =>
      IH _ (by simp only at hle; omega) e'' he'' w'' s'' h'' le_rfl
  clear IH hm hclos
  rcases hstrat with hf | ⟨st, hst, hdeps⟩
  · exact xc_unfold hL hf hw.derives
  have hfound : ∀ d ∈ st, ∃ e' ∈ C, e'.goal.same d.1.norm.2 = true :=
    fun d hd => let ⟨e', he', hs, _⟩ := hdeps d hd; ⟨e', he', hs⟩
  clear hdeps
  generalize e.goal = G at *
  obtain ⟨lb, e, rb⟩ := G
  cases e with
  | zero => cases hw
  | span s₀ => cases hw with | span => exact xc_span hL lb rb _
  | or a b =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    obtain ⟨l, hl, hwl⟩ := (dw_orBranches _).1 hw
    have hl' := orBranches_not_or _ l hl
    refine xc_or hl (hD ⟨lb, l, rb⟩ ?_ hgG w s hwl ?_)
    · exact hfound (⟨lb, l, rb⟩, false) (by simp only [orLeaves, List.mem_map]; exact ⟨_, ⟨l, hl, rfl⟩, rfl⟩)
    · rw [isOr_zero hl']; simp [isOr]
  | call n =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    cases hw with
    | call hw =>
      exact xc_call (hD _ (hfound _ (List.mem_singleton_self _)) hgG _ s hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl))
  | conv a =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    cases hw with
    | conv hw =>
      exact xc_conv hL (hD _ (hfound _ (List.mem_singleton_self _)) (goodG_convGoal hgG a) _ _ hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl))
  | seq a b =>
    cases hw with
    | seq hw₁ hw₂ hc =>
      rw [compose_some hc]
      have hLg : GoodG ⟨lb, a, none⟩ := ⟨hgG.1, trivial⟩
      have hR : GoodG ⟨none, b, rb⟩ := ⟨trivial, hgG.2⟩
      simp only [certStrategies, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl | rfl
      · exact xc_seq_join hL
          (hD _ (hfound (seqLeft ⟨lb, .seq a b, rb⟩ a, false) (by simp)) hLg _ _ hw₁ (meas_lt _ _ (by omega) rfl))
          (hD _ (hfound (seqRight ⟨lb, .seq a b, rb⟩ b, false) (by simp)) hR _ _ hw₂ (meas_lt _ _ (by omega) rfl))
      · have hLf := hfound _ (List.mem_cons_self ..)
        refine xc_seq_pushL hL (doneOf_certTables hLf)
          (hD _ hLf hLg _ _ hw₁ (meas_lt _ _ (by omega) rfl)) fun x hx => ?_
        rw [answersOf_certTables] at hx
        exact hD _ (hfound (seqPushL ⟨lb, .seq a b, rb⟩ b x, false)
            (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩)))
          (Tier0.goodG_pushL hgG b x) _ _ hw₂ (meas_lt _ _ (by omega) rfl)
      · have hRf := hfound _ (List.mem_cons_self ..)
        refine xc_seq_pushR hL (doneOf_certTables hRf)
          (hD _ hRf hR _ _ hw₂ (meas_lt _ _ (by omega) rfl)) fun y hy => ?_
        rw [answersOf_certTables] at hy
        exact hD _ (hfound (seqPushR ⟨lb, .seq a b, rb⟩ a y, false)
            (List.mem_cons_of_mem _ (List.mem_map.2 ⟨y, hy, rfl⟩)))
          (Tier0.goodG_pushR hgG a y) _ _ hw₁ (meas_lt _ _ (by omega) rfl)
  | and a b =>
    cases hw with
    | and hw₁ hw₂ hc =>
      rw [meet_some hc]
      simp only [certStrategies, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl | rfl
      · exact xc_and_join hL hgG
          (hD ⟨lb, a, rb⟩ (hfound (andLeft ⟨lb, .and a b, rb⟩ a, false) (by simp)) hgG _ _ hw₁ (meas_lt _ _ (by omega) rfl))
          (hD ⟨lb, b, rb⟩ (hfound (andRight ⟨lb, .and a b, rb⟩ b, false) (by simp)) hgG _ _ hw₂ (meas_lt _ _ (by omega) rfl))
      · have hLf := hfound _ (List.mem_cons_self ..)
        refine xc_and_pushL hL hgG (doneOf_certTables hLf)
          (hD ⟨lb, a, rb⟩ hLf hgG _ _ hw₁ (meas_lt _ _ (by omega) rfl)) fun x hx => ?_
        rw [answersOf_certTables] at hx
        exact hD _ (hfound (andPush b x, false) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩)))
          (goodG_andPush b x) _ _ hw₂ (meas_lt _ _ (by omega) rfl)
      · have hRf := hfound _ (List.mem_cons_self ..)
        refine xc_and_pushR hL hgG (doneOf_certTables hRf)
          (hD ⟨lb, b, rb⟩ hRf hgG _ _ hw₂ (meas_lt _ _ (by omega) rfl)) fun y hy => ?_
        rw [answersOf_certTables] at hy
        exact hD _ (hfound (andPush a y, false) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨y, hy, rfl⟩)))
          (goodG_andPush a y) _ _ hw₁ (meas_lt _ _ (by omega) rfl)

/-- Every cover of a valid certificate covers every answer under a derivation
of its goal. -/
theorem cert_cover_sub {C : List CertEntry} {D : Nat} {root : Goal} (hC : Cert.Valid P C D root)
    {e : CertEntry} (he : e ∈ C) {s a : Span} (hs : Derives P e.goal.e s)
    (ha : Sub P.theory (GDen e.goal s.den) a) : ∃ f ∈ e.cover, f.Covers a := by
  obtain ⟨w, hw⟩ := dw_of_derives hs
  exact (cert_xc hL hC _ e he w s hw le_rfl).cover ha

end Exact

end R001

end RwLog
