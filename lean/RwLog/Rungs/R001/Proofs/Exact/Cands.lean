/-
# Exact coverage, part 2: the candidates of one goal

`cands_sub`: if every answer the tables give a goal lies under one derivation
of that goal (`AnsSub`), so does every candidate the goal computes.

The `xc_*` lemmas: if the dependencies of a strategy cover the pieces of a
derivation, the goal's candidates cover the derivation. They are the exact
counterparts of the Tier 0 `dc_*` lemmas, with coverage by `Span.Covers`
after simplification in place of coverage up to the theory.
-/
import RwLog.Rungs.R001.Proofs.Exact.Basic

namespace RwLog

namespace R001

namespace Exact

open Lifting (LCov bden PId)
open Tier0

variable {P : Program}

/-! ## Boundaries only restrict -/

theorem dom_gden {g : Goal} (hg : GoodG g) (R : GRel) : Dom R (GDen g R) :=
  Lifting.lcov_wrap_pid (pid_of_goodBO hg.1) (pid_of_goodBO hg.2)

/-- Conjoining with what runs between sub-identity boundaries, when the other
side already lies between them. -/
theorem and_dom {B C A A' xd : GRel} (hB : PId B) (hC : PId C) (h : Dom (B.comp (A.comp C)) xd) :
    Dom ((B.comp (A.comp C)).meet (B.comp (A'.comp C))) (xd.meet A') := by
  rw [dom_iff] at h ⊢
  rintro u v S ⟨S₁, S₂, h₁, h₂, hS⟩
  obtain ⟨S₁', h₁', hsub⟩ := h u v S₁ h₁
  obtain ⟨m, Sb, Sac, hb, ⟨n, Sa, Sc, ha, hc, e₂⟩, e₁⟩ := h₁'
  simp only at hb ha hc e₁ e₂ hS
  obtain rfl := hB _ _ _ hb
  obtain rfl := hC _ _ _ hc
  refine ⟨S₁' ∪ (Sb ∪ (S₂ ∪ Sc)), ⟨S₁', Sb ∪ (S₂ ∪ Sc), ⟨_, Sb, Sac, hb, ⟨_, Sa, Sc, ha, hc, e₂⟩, e₁⟩,
    ⟨_, Sb, S₂ ∪ Sc, hb, ⟨_, S₂, Sc, h₂, hc, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  rw [hS]
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  subst e₁ e₂
  rcases hx with hx | hx | hx | hx
  · exact Or.inl (hsub hx)
  · exact Or.inl (hsub (by simp [hx]))
  · exact Or.inr hx
  · exact Or.inl (hsub (by simp [hx]))

/-! ## Answers of the unfolding strategy -/

theorem unfold_sub {d : Nat} {g : Goal} {c : Span} (h : c ∈ unfoldAnswers P d g) :
    ∃ s, Derives P g.e s ∧ Sub P.theory (GDen g s.den) c := by
  unfold unfoldAnswers at h
  split at h
  · simp only [List.mem_flatMap] at h
    obtain ⟨a, ha, hc⟩ := h
    obtain ⟨z, hz, hza⟩ := Lifting.roundSpans_derives ha
    obtain ⟨s, hs, hzs⟩ := rel_split hz
    exact ⟨s, hs, (live_sub hc).of_eq (by rw [hza, hzs])⟩
  · simp at h

section
variable (hL : SimpLaws P.theory)
include hL

theorem unfold_xc {d : Nat} {g : Goal} {s : Span} (hf : unfoldFinal P d g = true)
    (h : Derives P g.e s) : XC P.theory (unfoldAnswers P d g) (GDen g s.den) := by
  by_cases hne : (GDen g s.den).Nonempty
  · obtain ⟨z, hz, hzd⟩ := rel_join h hne
    obtain ⟨m, hm⟩ := derives_iff_derivesN.1 hz
    obtain ⟨a, ha, hsub⟩ := R000.roundSpans_cover (k := d) (n := m) (hm.mono (by omega))
      (by rw [hzd]; exact hne) (.inr hf)
    refine (live_xc hL (z := a) (dom_of_subset (by rw [← hzd]; exact hsub))).mono fun c hc => ?_
    unfold unfoldAnswers
    simp only [hf, ite_true]
    exact List.mem_flatMap.2 ⟨a, ha, hc⟩
  · exact XC.of_empty (Set.not_nonempty_iff_eq_empty.1 hne)

end

/-! ## Candidates lie under derivations -/

/-- Every answer the tables give a goal with interface boundaries lies under
one derivation of the goal. -/
def AnsSub (P : Program) (ts : Tables) : Prop :=
  ∀ d : Goal, GoodG d → ∀ a ∈ answersOf ts d, ∃ s, Derives P d.e s ∧ Sub P.theory (GDen d s.den) a

theorem spanBoth_of_nonempty {lb rb : Option Span} {s : Span}
    (h : (GDen ⟨lb, .span s, rb⟩ s.den).Nonempty) :
    ∃ u, spanBoth lb s rb = some u ∧ u.den = GDen ⟨lb, .span s, rb⟩ s.den := by
  cases hu : spanBoth lb s rb with
  | none => rw [spanBoth_none hu] at h; exact absurd h Set.not_nonempty_empty
  | some u => exact ⟨u, rfl, spanBoth_some hu⟩

/-- A span denoting `R ; rb`, when it relates something. -/
theorem rep_right {rb : Option Span} {s : Span} (h : ((s.den).comp (bden rb)).Nonempty) :
    ∃ u : Span, u.den = (s.den).comp (bden rb) := by
  obtain ⟨u, -, hu⟩ := spanBoth_of_nonempty (lb := none) (rb := rb) (s := s)
    (by simpa [GDen, bden, GRel.id_comp] using h)
  exact ⟨u, by rw [hu]; simp [GDen, bden, GRel.id_comp]⟩

/-- A span denoting `lb ; R`, when it relates something. -/
theorem rep_left {lb : Option Span} {s : Span} (h : ((bden lb).comp s.den).Nonempty) :
    ∃ u : Span, u.den = (bden lb).comp s.den := by
  obtain ⟨u, -, hu⟩ := spanBoth_of_nonempty (lb := lb) (rb := none) (s := s)
    (by simpa [GDen, bden, GRel.comp_id] using h)
  exact ⟨u, by rw [hu]; simp [GDen, bden, GRel.comp_id]⟩

/-- A span denoting `lb ; R ; rb`, when it relates something. -/
theorem rep_gden {g : Goal} {s : Span} (h : (GDen g s.den).Nonempty) :
    ∃ u : Span, u.den = GDen g s.den := by
  obtain ⟨u, -, hu⟩ := spanBoth_of_nonempty (lb := g.lb) (rb := g.rb) (s := s) h
  exact ⟨u, hu⟩

section
variable (hL : SimpLaws P.theory)
include hL

theorem cands_sub {dd : Nat} {ts : Tables} (hA : AnsSub P ts) {h : Goal} (hg : GoodG h) {c : Span}
    (hc : c ∈ (produce P dd ts h).1) : ∃ s, Derives P h.e s ∧ Sub P.theory (GDen h s.den) c := by
  simp only [produce, List.mem_append] at hc
  rcases hc with hc | hc
  · exact unfold_sub hc
  obtain ⟨lb, e, rb⟩ := h
  cases e with
  | zero => simp [produce.produceStrategies] at hc
  | span s =>
    simp only [produce.produceStrategies] at hc
    obtain ⟨w, hw, hwd⟩ := spanAnswer_den hc
    exact ⟨s, .span s, (live_sub hw).of_eq hwd⟩
  | or a b =>
    simp only [produce.produceStrategies, List.mem_flatMap] at hc
    obtain ⟨d, hd, hc⟩ := hc
    simp only [orLeaves, List.mem_map] at hd
    obtain ⟨l, hl, rfl⟩ := hd
    obtain ⟨s, hs, hr⟩ := hA ⟨lb, l, rb⟩ hg c hc
    exact ⟨s, Lifting.derives_of_branch hl hs, hr⟩
  | call n =>
    simp only [produce.produceStrategies] at hc
    obtain ⟨s, hs, hr⟩ := hA (callGoal P ⟨lb, .call n, rb⟩ n) hg c hc
    exact ⟨s, .call hs, hr⟩
  | conv a =>
    simp only [produce.produceStrategies, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨s, hs, hr⟩ := hA _ (goodG_convGoal hg a) c' hc'
    refine ⟨s.swap, .conv hs, ?_⟩
    rw [swap_den]
    exact (sub_swap hL hr).of_eq (gden_conv ⟨lb, .conv a, rb⟩ a s.den).symm
  | seq a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_flatMap] at hc
    have hL' : GoodG (seqLeft ⟨lb, .seq a b, rb⟩ a) := ⟨hg.1, trivial⟩
    have hR : GoodG (seqRight ⟨lb, .seq a b, rb⟩ b) := ⟨trivial, hg.2⟩
    rcases hc with (⟨x, hx, y, hy, hc⟩ | ⟨p, hp, y, hy, hc⟩) | ⟨p, hp, x, hx, hc⟩
    · obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hL' x hx
      obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hR y hy
      have hr := composeLive_sub hL hr₁ hr₂ hc
      rw [seqLeft, seqRight, gden_seq lb rb a b (.seq a b)] at hr
      obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty hr.nonempty)
      exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hL' x (maxima_sub hx)
        obtain ⟨s₂, hs₂, hr₂⟩ := hA _ (goodG_pushL hg b x) y hy
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
      · simp at hp
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨y, hy, rfl⟩ := hp
        obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hR y (maxima_sub hy)
        obtain ⟨s₁, hs₁, hr₁⟩ := hA _ (goodG_pushR hg a y) x hx
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
      · simp at hp
  | and a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_flatMap] at hc
    have hLa : GoodG (andLeft ⟨lb, .and a b, rb⟩ a) := hg
    have hRa : GoodG (andRight ⟨lb, .and a b, rb⟩ b) := hg
    have pB := pid_of_goodBO hg.1
    have pC := pid_of_goodBO hg.2
    rcases hc with (⟨x, hx, y, hy, hc⟩ | ⟨p, hp, y, hy, hc⟩) | ⟨p, hp, x, hx, hc⟩
    · obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hLa x hx
      obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hRa y hy
      have hr := meetLive_sub hL hr₁ hr₂ hc
      rw [andLeft, andRight, gden_and hg a b (.and a b)] at hr
      obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty hr.nonempty)
      exact ⟨s, .and hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hLa x (maxima_sub hx)
        obtain ⟨s₂, hs₂, hr₂⟩ := hA _ (goodG_andPush b x) y hy
        have hr := push_meet_subL hL (u := s₂) (Q := GDen ⟨lb, .and a b, rb⟩ ((s₁.den).meet s₂.den))
          hr₁ hr₂ (by rw [gden_andPush]; exact LCov.refl _)
          (fun w hw => by
            rw [← gden_and hg a b (.and a b)]
            exact and_dom pB pC hw) hc
        obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty hr.nonempty)
        exact ⟨s, .and hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
      · simp at hp
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨y, hy, rfl⟩ := hp
        obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hRa y (maxima_sub hy)
        obtain ⟨s₁, hs₁, hr₁⟩ := hA _ (goodG_andPush a y) x hx
        have hr := push_meet_subR hL (u := s₁) (Q := GDen ⟨lb, .and a b, rb⟩ ((s₁.den).meet s₂.den))
          hr₁ hr₂ (by
            rw [Lifting.meet_comm (GDen (andPush a y) s₁.den), gden_andPush, Lifting.meet_comm]
            exact LCov.refl _)
          (fun w hw => by
            rw [← gden_and hg a b (.and a b), Lifting.meet_comm, Lifting.meet_comm (s₁.den)]
            exact and_dom pB pC hw) hc
        obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty hr.nonempty)
        exact ⟨s, .and hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
      · simp at hp

end

/-! ## Candidates cover what the dependencies cover -/

theorem meet_nonempty_right {R S : GRel} (h : (R.meet S).Nonempty) : S.Nonempty := by
  obtain ⟨⟨u, v, _⟩, S₁, S₂, _, h₂, _⟩ := h
  exact ⟨_, h₂⟩

theorem meet_nonempty_left {R S : GRel} (h : (R.meet S).Nonempty) : R.Nonempty := by
  obtain ⟨⟨u, v, _⟩, S₁, S₂, h₁, _, _⟩ := h
  exact ⟨_, h₁⟩

/-- The candidates of the table strategies are candidates. -/
theorem xc_of_strat {dd : Nat} {ts : Tables} {g : Goal} {X : GRel}
    (h : XC P.theory (produce.produceStrategies P ts g).1 X) : XC P.theory (produce P dd ts g).1 X :=
  h.mono fun c hc => by simp only [produce, List.mem_append]; exact Or.inr hc

theorem xc_or {dd : Nat} {ts : Tables} {lb rb : Option Span} {a b l : Rel} {X : GRel}
    (hl : l ∈ orBranches (.or a b)) (h : XC P.theory (answersOf ts ⟨lb, l, rb⟩) X) :
    XC P.theory (produce P dd ts ⟨lb, .or a b, rb⟩).1 X :=
  xc_of_strat (h.mono fun c hc => by
    simp only [produce.produceStrategies, List.mem_flatMap, orLeaves, List.mem_map]
    exact ⟨_, ⟨l, hl, rfl⟩, hc⟩)

theorem xc_call {dd : Nat} {ts : Tables} {lb rb : Option Span} {n : Name} {X : GRel}
    (h : XC P.theory (answersOf ts (callGoal P ⟨lb, .call n, rb⟩ n)) X) :
    XC P.theory (produce P dd ts ⟨lb, .call n, rb⟩).1 X :=
  xc_of_strat (by simpa [produce.produceStrategies] using h)

section
variable (hL : SimpLaws P.theory)
include hL

theorem xc_unfold {dd : Nat} {ts : Tables} {g : Goal} {s : Span} (hf : unfoldFinal P dd g = true)
    (h : Derives P g.e s) : XC P.theory (produce P dd ts g).1 (GDen g s.den) :=
  (unfold_xc hL hf h).mono fun c hc => by
    simp only [produce, List.mem_append]; exact Or.inl hc

theorem xc_span {dd : Nat} {ts : Tables} (lb rb : Option Span) (s : Span) :
    XC P.theory (produce P dd ts ⟨lb, .span s, rb⟩).1 (GDen ⟨lb, .span s, rb⟩ s.den) := by
  refine xc_of_strat ?_
  simp only [produce.produceStrategies]
  rw [spanAnswer_eq]
  cases hw : spanBoth lb s rb with
  | none => exact XC.of_empty (spanBoth_none hw)
  | some w => exact live_xc hL (dom_of_eq (spanBoth_some hw))

theorem xc_conv {dd : Nat} {ts : Tables} {lb rb : Option Span} {a : Rel} {s : Span}
    (h : XC P.theory (answersOf ts (convGoal ⟨lb, .conv a, rb⟩ a))
      (GDen (convGoal ⟨lb, .conv a, rb⟩ a) s.den)) :
    XC P.theory (produce P dd ts ⟨lb, .conv a, rb⟩).1 (GDen ⟨lb, .conv a, rb⟩ s.swap.den) := by
  have h' := xc_swap hL h
  rw [← gden_conv ⟨lb, .conv a, rb⟩ a, ← swap_den] at h'
  exact xc_of_strat (by simpa [produce.produceStrategies] using h')

theorem xc_seq_join {dd : Nat} {ts : Tables} {lb rb : Option Span} {a b : Rel} {s₁ s₂ : Span}
    (h₁ : XC P.theory (answersOf ts ⟨lb, a, none⟩) (GDen ⟨lb, a, none⟩ s₁.den))
    (h₂ : XC P.theory (answersOf ts ⟨none, b, rb⟩) (GDen ⟨none, b, rb⟩ s₂.den)) :
    XC P.theory (produce P dd ts ⟨lb, .seq a b, rb⟩).1
      (GDen ⟨lb, .seq a b, rb⟩ ((s₁.den).comp s₂.den)) := by
  rw [← gden_seq lb rb a b (.seq a b)]
  by_cases hne : ((GDen ⟨lb, a, none⟩ s₁.den).comp (GDen ⟨none, b, rb⟩ s₂.den)).Nonempty
  · obtain ⟨u₁, hu₁⟩ := rep_gden (GRel.comp_nonempty_left hne)
    obtain ⟨u₂, hu₂⟩ := rep_gden (GRel.comp_nonempty_right hne)
    rw [← hu₁, ← hu₂] at hne ⊢
    obtain ⟨u, hu, hud⟩ := compose_isSome hne
    rw [← hud]
    have h := join_comp_xc hL (h₁.of_eq hu₁.symm) (h₂.of_eq hu₂.symm) hu
    refine xc_of_strat (h.mono fun c hc => ?_)
    simp only [produce.produceStrategies, seqLeft, seqRight, List.mem_append]
    exact Or.inl (Or.inl hc)
  · exact XC.of_empty (Set.not_nonempty_iff_eq_empty.1 hne)

theorem xc_seq_pushL {dd : Nat} {ts : Tables} {lb rb : Option Span} {a b : Rel} {s₁ s₂ : Span}
    (hd : doneOf ts ⟨lb, a, none⟩ = true)
    (h₁ : XC P.theory (answersOf ts ⟨lb, a, none⟩) (GDen ⟨lb, a, none⟩ s₁.den))
    (h₂ : ∀ x ∈ maxima (answersOf ts ⟨lb, a, none⟩),
      XC P.theory (answersOf ts (seqPushL ⟨lb, .seq a b, rb⟩ b x))
        (GDen (seqPushL ⟨lb, .seq a b, rb⟩ b x) s₂.den)) :
    XC P.theory (produce P dd ts ⟨lb, .seq a b, rb⟩).1
      (GDen ⟨lb, .seq a b, rb⟩ ((s₁.den).comp s₂.den)) := by
  rw [← gden_seqL lb rb a (.seq a b)]
  by_cases hne : ((GDen ⟨lb, a, none⟩ s₁.den).comp ((s₂.den).comp (bden rb))).Nonempty
  · obtain ⟨u₁, hu₁⟩ := rep_gden (GRel.comp_nonempty_left hne)
    obtain ⟨u₂, hu₂⟩ := rep_right (GRel.comp_nonempty_right hne)
    rw [← hu₁, ← hu₂] at hne ⊢
    obtain ⟨u, hu, hud⟩ := compose_isSome hne
    refine xc_of_rep hL (u := u) (dom_of_eq hud) fun u' hu' => ?_
    obtain ⟨v₁, z₁, c₁, hv₁, hz₁, hc₁, he₁⟩ := simp_compL_rev hL hu hu'
    obtain ⟨x₀, hx₀, hcx₀⟩ := h₁ u₁ (dom_of_eq hu₁.symm) v₁ hv₁
    obtain ⟨x, hx, hcx⟩ := maxima_cover hx₀
    obtain ⟨z₂, hz₂, hzc₂⟩ := compose_mono (hcx.trans hcx₀) (Span.Covers.refl u₂) hz₁
    obtain ⟨c₂, hc₂, hcc₂⟩ := simp_mono hL hzc₂ hc₁
    have e : (x.den).comp u₂.den =
        (x.den).comp (GDen (seqPushL ⟨lb, .seq a b, rb⟩ b x) s₂.den) := by
      rw [hu₂]; simp only [seqPushL]; rw [gden_pushL]
    have hz₂n : ((x.den).comp (GDen (seqPushL ⟨lb, .seq a b, rb⟩ b x) s₂.den)).Nonempty := by
      rw [← e, ← compose_some hz₂]; exact z₂.den_nonempty
    obtain ⟨u₂', hu₂'⟩ := rep_gden (GRel.comp_nonempty_right hz₂n)
    rw [← hu₂'] at e hz₂n
    obtain ⟨z₃, hz₃, hz₃d⟩ := compose_isSome hz₂n
    obtain ⟨c₃, hc₃, hcc₃⟩ := simp_mono hL
      (covers_of_dom (by rw [hz₃d, ← e, ← compose_some hz₂]; exact LCov.refl _)) hc₂
    obtain ⟨v₂, z₄, c₄, hv₂, hz₄, hc₄, he₄⟩ := simp_compR_rev hL hz₃ hc₃
    obtain ⟨y, hy, hcy⟩ := h₂ x hx u₂' (dom_of_eq hu₂'.symm) v₂ hv₂
    obtain ⟨z₅, hz₅, hzc₅⟩ := compose_mono (Span.Covers.refl x) hcy hz₄
    obtain ⟨c₅, hc₅, hcc₅⟩ := simp_mono hL hzc₅ hc₄
    refine ⟨c₅, ?_, hcc₅.trans (he₄.1.trans (hcc₃.trans (hcc₂.trans he₁.1)))⟩
    simp only [produce, produce.produceStrategies, seqLeft, hd, ite_true, List.mem_append,
      List.mem_flatMap, List.mem_map]
    exact Or.inr (Or.inl (Or.inr ⟨_, ⟨x, hx, rfl⟩, y, hy, by simp [composeLive, hz₅, live, hc₅]⟩))
  · exact XC.of_empty (Set.not_nonempty_iff_eq_empty.1 hne)

theorem xc_seq_pushR {dd : Nat} {ts : Tables} {lb rb : Option Span} {a b : Rel} {s₁ s₂ : Span}
    (hd : doneOf ts ⟨none, b, rb⟩ = true)
    (h₂ : XC P.theory (answersOf ts ⟨none, b, rb⟩) (GDen ⟨none, b, rb⟩ s₂.den))
    (h₁ : ∀ y ∈ maxima (answersOf ts ⟨none, b, rb⟩),
      XC P.theory (answersOf ts (seqPushR ⟨lb, .seq a b, rb⟩ a y))
        (GDen (seqPushR ⟨lb, .seq a b, rb⟩ a y) s₁.den)) :
    XC P.theory (produce P dd ts ⟨lb, .seq a b, rb⟩).1
      (GDen ⟨lb, .seq a b, rb⟩ ((s₁.den).comp s₂.den)) := by
  rw [← gden_seqR lb rb b (.seq a b)]
  by_cases hne : (((bden lb).comp s₁.den).comp (GDen ⟨none, b, rb⟩ s₂.den)).Nonempty
  · obtain ⟨u₁, hu₁⟩ := rep_left (GRel.comp_nonempty_left hne)
    obtain ⟨u₂, hu₂⟩ := rep_gden (GRel.comp_nonempty_right hne)
    rw [← hu₁, ← hu₂] at hne ⊢
    obtain ⟨u, hu, hud⟩ := compose_isSome hne
    refine xc_of_rep hL (u := u) (dom_of_eq hud) fun u' hu' => ?_
    obtain ⟨v₂, z₁, c₁, hv₂, hz₁, hc₁, he₁⟩ := simp_compR_rev hL hu hu'
    obtain ⟨y₀, hy₀, hcy₀⟩ := h₂ u₂ (dom_of_eq hu₂.symm) v₂ hv₂
    obtain ⟨y, hy, hcy⟩ := maxima_cover hy₀
    obtain ⟨z₂, hz₂, hzc₂⟩ := compose_mono (Span.Covers.refl u₁) (hcy.trans hcy₀) hz₁
    obtain ⟨c₂, hc₂, hcc₂⟩ := simp_mono hL hzc₂ hc₁
    have e : (u₁.den).comp y.den =
        (GDen (seqPushR ⟨lb, .seq a b, rb⟩ a y) s₁.den).comp y.den := by
      rw [hu₁]; simp only [seqPushR]; rw [gden_pushR]
    have hz₂n : ((GDen (seqPushR ⟨lb, .seq a b, rb⟩ a y) s₁.den).comp y.den).Nonempty := by
      rw [← e, ← compose_some hz₂]; exact z₂.den_nonempty
    obtain ⟨u₁', hu₁'⟩ := rep_gden (GRel.comp_nonempty_left hz₂n)
    rw [← hu₁'] at e hz₂n
    obtain ⟨z₃, hz₃, hz₃d⟩ := compose_isSome hz₂n
    obtain ⟨c₃, hc₃, hcc₃⟩ := simp_mono hL
      (covers_of_dom (by rw [hz₃d, ← e, ← compose_some hz₂]; exact LCov.refl _)) hc₂
    obtain ⟨v₁, z₄, c₄, hv₁, hz₄, hc₄, he₄⟩ := simp_compL_rev hL hz₃ hc₃
    obtain ⟨x, hx, hcx⟩ := h₁ y hy u₁' (dom_of_eq hu₁'.symm) v₁ hv₁
    obtain ⟨z₅, hz₅, hzc₅⟩ := compose_mono hcx (Span.Covers.refl y) hz₄
    obtain ⟨c₅, hc₅, hcc₅⟩ := simp_mono hL hzc₅ hc₄
    refine ⟨c₅, ?_, hcc₅.trans (he₄.1.trans (hcc₃.trans (hcc₂.trans he₁.1)))⟩
    simp only [produce, produce.produceStrategies, seqRight, hd, ite_true, List.mem_append,
      List.mem_flatMap, List.mem_map]
    exact Or.inr (Or.inr ⟨_, ⟨y, hy, rfl⟩, x, hx, by simp [composeLive, hz₅, live, hc₅]⟩)
  · exact XC.of_empty (Set.not_nonempty_iff_eq_empty.1 hne)

theorem xc_and_join {dd : Nat} {ts : Tables} {lb rb : Option Span} (hg : GoodG ⟨lb, .zero, rb⟩)
    {a b : Rel} {s₁ s₂ : Span}
    (h₁ : XC P.theory (answersOf ts ⟨lb, a, rb⟩) (GDen ⟨lb, a, rb⟩ s₁.den))
    (h₂ : XC P.theory (answersOf ts ⟨lb, b, rb⟩) (GDen ⟨lb, b, rb⟩ s₂.den)) :
    XC P.theory (produce P dd ts ⟨lb, .and a b, rb⟩).1
      (GDen ⟨lb, .and a b, rb⟩ ((s₁.den).meet s₂.den)) := by
  rw [← gden_and hg a b (.and a b)]
  by_cases hne : ((GDen ⟨lb, a, rb⟩ s₁.den).meet (GDen ⟨lb, b, rb⟩ s₂.den)).Nonempty
  · obtain ⟨u₁, hu₁⟩ := rep_gden (meet_nonempty_left hne)
    obtain ⟨u₂, hu₂⟩ := rep_gden (meet_nonempty_right hne)
    rw [← hu₁, ← hu₂] at hne ⊢
    obtain ⟨u, hu, hud⟩ := meet_isSome hne
    rw [← hud]
    have h := join_meet_xc hL (h₁.of_eq hu₁.symm) (h₂.of_eq hu₂.symm) hu
    refine xc_of_strat (h.mono fun c hc => ?_)
    simp only [produce.produceStrategies, andLeft, andRight, List.mem_append]
    exact Or.inl (Or.inl hc)
  · exact XC.of_empty (Set.not_nonempty_iff_eq_empty.1 hne)

theorem xc_and_pushL {dd : Nat} {ts : Tables} {lb rb : Option Span} (hg : GoodG ⟨lb, .zero, rb⟩)
    {a b : Rel} {s₁ s₂ : Span}
    (hd : doneOf ts ⟨lb, a, rb⟩ = true)
    (h₁ : XC P.theory (answersOf ts ⟨lb, a, rb⟩) (GDen ⟨lb, a, rb⟩ s₁.den))
    (h₂ : ∀ x ∈ maxima (answersOf ts ⟨lb, a, rb⟩),
      XC P.theory (answersOf ts (andPush b x)) (GDen (andPush b x) s₂.den)) :
    XC P.theory (produce P dd ts ⟨lb, .and a b, rb⟩).1
      (GDen ⟨lb, .and a b, rb⟩ ((s₁.den).meet s₂.den)) := by
  rw [← gden_and hg a b (.and a b)]
  by_cases hne : ((GDen ⟨lb, a, rb⟩ s₁.den).meet (GDen ⟨lb, b, rb⟩ s₂.den)).Nonempty
  · obtain ⟨u₁, hu₁⟩ := rep_gden (meet_nonempty_left hne)
    obtain ⟨u₂, hu₂⟩ := rep_gden (meet_nonempty_right hne)
    rw [← hu₁, ← hu₂] at hne ⊢
    obtain ⟨u, hu, hud⟩ := meet_isSome hne
    refine xc_of_rep hL (u := u) (dom_of_eq hud) fun u' hu' => ?_
    obtain ⟨v₁, z₁, c₁, hv₁, hz₁, hc₁, he₁⟩ := simp_meetL_rev hL hu hu'
    obtain ⟨x₀, hx₀, hcx₀⟩ := h₁ u₁ (dom_of_eq hu₁.symm) v₁ hv₁
    obtain ⟨x, hx, hcx⟩ := maxima_cover hx₀
    obtain ⟨z₂, hz₂, hzc₂⟩ := meet_mono (hcx.trans hcx₀) (Span.Covers.refl u₂) hz₁
    obtain ⟨c₂, hc₂, hcc₂⟩ := simp_mono hL hzc₂ hc₁
    have hD : Dom ((x.den).meet (GDen (andPush b x) s₂.den)) z₂.den := by
      rw [gden_andPush, meet_some hz₂, hu₂]
      exact (LCov.refl _).meet (dom_gden hg s₂.den)
    obtain ⟨u₂', hu₂'⟩ := rep_gden (meet_nonempty_right (hD.nonempty z₂.den_nonempty))
    rw [← hu₂'] at hD
    obtain ⟨z₃, hz₃, hz₃d⟩ := meet_isSome (hD.nonempty z₂.den_nonempty)
    obtain ⟨c₃, hc₃, hcc₃⟩ := simp_mono hL (covers_of_dom (by rw [hz₃d]; exact hD)) hc₂
    obtain ⟨v₂, z₄, c₄, hv₂, hz₄, hc₄, he₄⟩ := simp_meetR_rev hL hz₃ hc₃
    obtain ⟨y, hy, hcy⟩ := h₂ x hx u₂' (dom_of_eq hu₂'.symm) v₂ hv₂
    obtain ⟨z₅, hz₅, hzc₅⟩ := meet_mono (Span.Covers.refl x) hcy hz₄
    obtain ⟨c₅, hc₅, hcc₅⟩ := simp_mono hL hzc₅ hc₄
    refine ⟨c₅, ?_, hcc₅.trans (he₄.1.trans (hcc₃.trans (hcc₂.trans he₁.1)))⟩
    simp only [produce, produce.produceStrategies, andLeft, hd, ite_true, List.mem_append,
      List.mem_flatMap, List.mem_map]
    exact Or.inr (Or.inl (Or.inr ⟨_, ⟨x, hx, rfl⟩, y, hy, by simp [meetLive, hz₅, live, hc₅]⟩))
  · exact XC.of_empty (Set.not_nonempty_iff_eq_empty.1 hne)

theorem xc_and_pushR {dd : Nat} {ts : Tables} {lb rb : Option Span} (hg : GoodG ⟨lb, .zero, rb⟩)
    {a b : Rel} {s₁ s₂ : Span}
    (hd : doneOf ts ⟨lb, b, rb⟩ = true)
    (h₂ : XC P.theory (answersOf ts ⟨lb, b, rb⟩) (GDen ⟨lb, b, rb⟩ s₂.den))
    (h₁ : ∀ y ∈ maxima (answersOf ts ⟨lb, b, rb⟩),
      XC P.theory (answersOf ts (andPush a y)) (GDen (andPush a y) s₁.den)) :
    XC P.theory (produce P dd ts ⟨lb, .and a b, rb⟩).1
      (GDen ⟨lb, .and a b, rb⟩ ((s₁.den).meet s₂.den)) := by
  rw [← gden_and hg a b (.and a b)]
  by_cases hne : ((GDen ⟨lb, a, rb⟩ s₁.den).meet (GDen ⟨lb, b, rb⟩ s₂.den)).Nonempty
  · obtain ⟨u₁, hu₁⟩ := rep_gden (meet_nonempty_left hne)
    obtain ⟨u₂, hu₂⟩ := rep_gden (meet_nonempty_right hne)
    rw [← hu₁, ← hu₂] at hne ⊢
    obtain ⟨u, hu, hud⟩ := meet_isSome hne
    refine xc_of_rep hL (u := u) (dom_of_eq hud) fun u' hu' => ?_
    obtain ⟨v₂, z₁, c₁, hv₂, hz₁, hc₁, he₁⟩ := simp_meetR_rev hL hu hu'
    obtain ⟨y₀, hy₀, hcy₀⟩ := h₂ u₂ (dom_of_eq hu₂.symm) v₂ hv₂
    obtain ⟨y, hy, hcy⟩ := maxima_cover hy₀
    obtain ⟨z₂, hz₂, hzc₂⟩ := meet_mono (Span.Covers.refl u₁) (hcy.trans hcy₀) hz₁
    obtain ⟨c₂, hc₂, hcc₂⟩ := simp_mono hL hzc₂ hc₁
    have hD : Dom ((GDen (andPush a y) s₁.den).meet y.den) z₂.den := by
      rw [Lifting.meet_comm, gden_andPush, meet_some hz₂, hu₁, Lifting.meet_comm]
      exact (dom_gden hg s₁.den).meet (LCov.refl _)
    obtain ⟨u₁', hu₁'⟩ := rep_gden (meet_nonempty_left (hD.nonempty z₂.den_nonempty))
    rw [← hu₁'] at hD
    obtain ⟨z₃, hz₃, hz₃d⟩ := meet_isSome (hD.nonempty z₂.den_nonempty)
    obtain ⟨c₃, hc₃, hcc₃⟩ := simp_mono hL (covers_of_dom (by rw [hz₃d]; exact hD)) hc₂
    obtain ⟨v₁, z₄, c₄, hv₁, hz₄, hc₄, he₄⟩ := simp_meetL_rev hL hz₃ hc₃
    obtain ⟨x, hx, hcx⟩ := h₁ y hy u₁' (dom_of_eq hu₁'.symm) v₁ hv₁
    obtain ⟨z₅, hz₅, hzc₅⟩ := meet_mono hcx (Span.Covers.refl y) hz₄
    obtain ⟨c₅, hc₅, hcc₅⟩ := simp_mono hL hzc₅ hc₄
    refine ⟨c₅, ?_, hcc₅.trans (he₄.1.trans (hcc₃.trans (hcc₂.trans he₁.1)))⟩
    simp only [produce, produce.produceStrategies, andRight, hd, ite_true, List.mem_append,
      List.mem_flatMap, List.mem_map]
    exact Or.inr (Or.inr ⟨_, ⟨y, hy, rfl⟩, x, hx, by simp [meetLive, hz₅, live, hc₅]⟩)
  · exact XC.of_empty (Set.not_nonempty_iff_eq_empty.1 hne)

end

end Exact

end R001

end RwLog
