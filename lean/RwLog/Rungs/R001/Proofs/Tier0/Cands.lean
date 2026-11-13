/-
# Tier 0 proofs, part 6: the candidates of one goal

`cands_ref`: if every answer the tables give a goal stands for one derivation
of that goal (`AnsRef`), so does every candidate a goal computes from them.

The `dc_*` lemmas: if the dependencies of a strategy cover a derivation's
pieces, the goal's candidates cover the derivation.
-/
import RwLog.Rungs.R001.Proofs.Tier0.Unfold

namespace RwLog

namespace R001

namespace Tier0



variable {P : Program}

/-- Every answer the tables give a goal with interface boundaries stands, up
to the theory, for one derivation of the goal. -/
def AnsRef (P : Program) (ts : Tables) : Prop :=
  ∀ d : Goal, GoodG d → ∀ a ∈ answersOf ts d, ∃ s, Derives P d.e s ∧ Ref P.theory a (GDen d s.den)

theorem gden_nonempty {g : Goal} {R : GRel} (h : (GDen g R).Nonempty) : R.Nonempty :=
  GRel.comp_nonempty_left (GRel.comp_nonempty_right h)

/-! ## Relations of the sub-goals -/

theorem gden_seq (lb rb : Option Span) (a b e : Rel) (R₁ R₂ : GRel) :
    (GDen ⟨lb, a, none⟩ R₁).comp (GDen ⟨none, b, rb⟩ R₂) = GDen ⟨lb, e, rb⟩ (R₁.comp R₂) := by
  simp only [GDen, bden, GRel.comp_id, GRel.id_comp, GRel.comp_assoc]

theorem gden_seqL (lb rb : Option Span) (a e : Rel) (R₁ R₂ : GRel) :
    (GDen ⟨lb, a, none⟩ R₁).comp (R₂.comp (bden rb)) = GDen ⟨lb, e, rb⟩ (R₁.comp R₂) := by
  simp only [GDen, bden, GRel.comp_id, GRel.comp_assoc]

theorem gden_seqR (lb rb : Option Span) (b e : Rel) (R₁ R₂ : GRel) :
    ((bden lb).comp R₁).comp (GDen ⟨none, b, rb⟩ R₂) = GDen ⟨lb, e, rb⟩ (R₁.comp R₂) := by
  simp only [GDen, bden, GRel.id_comp, GRel.comp_assoc]

theorem gden_pushL (x : Span) (b : Rel) (rb : Option Span) (R : GRel) :
    (x.den).comp (GDen (⟨bound x.rightIface, b, rb⟩ : Goal) R) = (x.den).comp (R.comp (bden rb)) := by
  simp only [GDen, Lifting.bden_bound (rfl : x.rightIface.l = x.rightIface.r), ← GRel.comp_assoc,
    comp_rightIface]

theorem gden_pushR (y : Span) (a : Rel) (lb : Option Span) (R : GRel) :
    (GDen (⟨lb, a, bound y.leftIface⟩ : Goal) R).comp y.den = ((bden lb).comp R).comp y.den := by
  simp only [GDen, Lifting.bden_bound (rfl : y.leftIface.l = y.leftIface.r), GRel.comp_assoc,
    leftIface_comp]

theorem gden_andPush (x : Span) (e : Rel) (R : GRel) :
    (x.den).meet (GDen (andPush e x) R) = (x.den).meet R := by
  simp only [GDen, andPush, Lifting.bden_bound (rfl : x.leftIface.l = x.leftIface.r),
    Lifting.bden_bound (rfl : x.rightIface.l = x.rightIface.r), meet_ifaces]

theorem gden_and {g : Goal} (hg : GoodG g) (a b e : Rel) (R₁ R₂ : GRel) :
    (GDen ⟨g.lb, a, g.rb⟩ R₁).meet (GDen ⟨g.lb, b, g.rb⟩ R₂) = GDen ⟨g.lb, e, g.rb⟩ (R₁.meet R₂) :=
  meet_bound (bnd_fn hg.1) (bnd_fn hg.2) R₁ R₂

theorem goodG_pushL {g : Goal} (hg : GoodG g) (b : Rel) (x : Span) : GoodG (seqPushL g b x) :=
  ⟨goodBO_bound (bnd_rightIface x), hg.2⟩

theorem goodG_pushR {g : Goal} (hg : GoodG g) (a : Rel) (y : Span) : GoodG (seqPushR g a y) :=
  ⟨hg.1, goodBO_bound (bnd_leftIface y)⟩

theorem goodG_andPush (e : Rel) (x : Span) : GoodG (andPush e x) :=
  ⟨goodBO_bound (bnd_leftIface x), goodBO_bound (bnd_rightIface x)⟩

/-! ## Candidates stand for derivations -/

theorem spanBoth_some {lb rb : Option Span} {s w : Span} (h : spanBoth lb s rb = some w) :
    w.den = GDen ⟨lb, .span s, rb⟩ s.den := by
  cases lb with
  | none =>
    cases rb with
    | none =>
      simp only [spanBoth, Option.bind_some, Option.some.injEq] at h
      subst h; simp [GDen, bden, GRel.id_comp, GRel.comp_id]
    | some r =>
      simp only [spanBoth, Option.bind_some] at h
      rw [compose_some h]; simp [GDen, bden, GRel.id_comp]
  | some l =>
    cases rb with
    | none =>
      simp only [spanBoth, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨u, hu, rfl⟩ := h
      rw [compose_some hu]; simp [GDen, bden, GRel.comp_id]
    | some r =>
      simp only [spanBoth, Option.bind_eq_some_iff] at h
      obtain ⟨u, hu, hw⟩ := h
      rw [compose_some hw, compose_some hu]; simp [GDen, bden, GRel.comp_assoc]

theorem spanBoth_none {lb rb : Option Span} {s : Span} (h : spanBoth lb s rb = none) :
    GDen ⟨lb, .span s, rb⟩ s.den = ∅ := by
  cases lb with
  | none =>
    cases rb with
    | none => simp [spanBoth] at h
    | some r =>
      simp only [spanBoth, Option.bind_some] at h
      simp only [GDen, bden, GRel.id_comp]; exact compose_none h
  | some l =>
    simp only [GDen, bden]
    cases hu : l.compose s with
    | none => rw [← GRel.comp_assoc]; rw [compose_none hu]; exact empty_comp _
    | some u =>
      cases rb with
      | none => simp [spanBoth, hu] at h
      | some r =>
        simp only [spanBoth, hu, Option.bind_some] at h
        rw [← GRel.comp_assoc, ← compose_some hu]; exact compose_none h

theorem spanAnswer_den {T : Theory} {lb rb : Option Span} {s z : Span}
    (h : z ∈ spanAnswer T lb s rb) : ∃ w, z ∈ live T w ∧ w.den = GDen ⟨lb, .span s, rb⟩ s.den := by
  rw [spanAnswer_eq] at h
  cases hw : spanBoth lb s rb with
  | none => rw [hw] at h; simp [liveO] at h
  | some w => rw [hw] at h; exact ⟨w, h, spanBoth_some hw⟩

theorem spanAnswer_dc {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed)
    (lb rb : Option Span) (s : Span) :
    DC T (spanAnswer T lb s rb) (GDen ⟨lb, .span s, rb⟩ s.den) := by
  rw [spanAnswer_eq]
  cases hw : spanBoth lb s rb with
  | none =>
    left; intro M _
    rw [spanBoth_none hw]; exact at_empty M
  | some w =>
    exact live_dc hwf (lcov_of_subset (spanBoth_some hw).ge)

section
variable (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
include hwf

theorem cands_ref {dd : Nat} {ts : Tables} (hA : AnsRef P ts) {h : Goal} (hg : GoodG h) {c : Span}
    (hc : c ∈ (produce P dd ts h).1) : ∃ s, Derives P h.e s ∧ Ref P.theory c (GDen h s.den) := by
  simp only [produce, List.mem_append] at hc
  rcases hc with hc | hc
  · exact unfold_ref hwf hc
  obtain ⟨lb, e, rb⟩ := h
  cases e with
  | zero => simp [produce.produceStrategies] at hc
  | span s =>
    simp only [produce.produceStrategies] at hc
    obtain ⟨w, hw, hwd⟩ := spanAnswer_den hc
    exact ⟨s, .span s, (live_ref hwf hw).of_eq hwd⟩
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
    exact hr.swap.of_eq (gden_conv ⟨lb, .conv a, rb⟩ a s.den).symm
  | seq a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_flatMap] at hc
    have hL : GoodG (seqLeft ⟨lb, .seq a b, rb⟩ a) := ⟨hg.1, trivial⟩
    have hR : GoodG (seqRight ⟨lb, .seq a b, rb⟩ b) := ⟨trivial, hg.2⟩
    rcases hc with (⟨x, hx, y, hy, hc⟩ | ⟨p, hp, y, hy, hc⟩) | ⟨p, hp, x, hx, hc⟩
    · obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hL x hx
      obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hR y hy
      have hr := composeLive_ref hwf hr₁ hr₂ hc
      rw [seqLeft, seqRight, gden_seq lb rb a b (.seq a b)] at hr
      obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty (hr.nonempty))
      exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hL x (maxima_sub hx)
        obtain ⟨s₂, hs₂, hr₂⟩ := hA _ (goodG_pushL hg b x) y hy
        have hr := composeLive_ref hwf (Ref.self x) hr₂ hc
        simp only [seqPushL] at hr
        rw [gden_pushL] at hr
        have hr' := hr.trans (Backed.comp hr₁.1 (Backed.refl _)) (hr₁.2.comp (LCov.refl _))
        rw [seqLeft, gden_seqL lb rb a (.seq a b)] at hr'
        obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty (hr'.nonempty))
        exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr'⟩
      · simp at hp
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨y, hy, rfl⟩ := hp
        obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hR y (maxima_sub hy)
        obtain ⟨s₁, hs₁, hr₁⟩ := hA _ (goodG_pushR hg a y) x hx
        have hr := composeLive_ref hwf hr₁ (Ref.self y) hc
        simp only [seqPushR] at hr
        rw [gden_pushR] at hr
        have hr' := hr.trans (Backed.comp (Backed.refl _) hr₂.1) ((LCov.refl _).comp hr₂.2)
        rw [seqRight, gden_seqR lb rb b (.seq a b)] at hr'
        obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty (hr'.nonempty))
        exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr'⟩
      · simp at hp
  | and a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_flatMap] at hc
    have hL : GoodG (andLeft ⟨lb, .and a b, rb⟩ a) := hg
    have hR : GoodG (andRight ⟨lb, .and a b, rb⟩ b) := hg
    have fB := bnd_fn hg.1
    have fC := bnd_fn hg.2
    rcases hc with (⟨x, hx, y, hy, hc⟩ | ⟨p, hp, y, hy, hc⟩) | ⟨p, hp, x, hx, hc⟩
    · obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hL x hx
      obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hR y hy
      have hr := meetLive_ref hwf hr₁ hr₂ hc
      rw [andLeft, andRight, gden_and hg a b (.and a b)] at hr
      obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty (hr.nonempty))
      exact ⟨s, .and hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hL x (maxima_sub hx)
        obtain ⟨s₂, hs₂, hr₂⟩ := hA _ (goodG_andPush b x) y hy
        have hr := meetLive_ref hwf (Ref.self x) hr₂ hc
        rw [gden_andPush] at hr
        have hr' := hr.trans (andPush_backed fB fC hr₁.1) (andPush_dom fB fC hr₁.2)
        have e₁ := gden_and hg a b (.and a b) s₁.den s₂.den
        simp only [GDen] at e₁ hr'
        rw [e₁] at hr'
        obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty (g := ⟨lb, .and a b, rb⟩) (hr'.nonempty))
        exact ⟨s, .and hs₁ hs₂ hs, by rw [GDen, hsd]; exact hr'⟩
      · simp at hp
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨y, hy, rfl⟩ := hp
        obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hR y (maxima_sub hy)
        obtain ⟨s₁, hs₁, hr₁⟩ := hA _ (goodG_andPush a y) x hx
        have hr := meetLive_ref hwf hr₁ (Ref.self y) hc
        rw [meet_comm, gden_andPush] at hr
        have hr' := hr.trans (andPush_backed fB fC hr₂.1) (andPush_dom fB fC hr₂.2)
        have e₁ := gden_and hg a b (.and a b) s₁.den s₂.den
        simp only [GDen] at e₁ hr'
        rw [meet_comm, e₁] at hr'
        obtain ⟨s, hs, hsd⟩ := meet_isSome (gden_nonempty (g := ⟨lb, .and a b, rb⟩) (hr'.nonempty))
        exact ⟨s, .and hs₁ hs₂ hs, by rw [GDen, hsd]; exact hr'⟩
      · simp at hp

/-! ## Candidates cover what the dependencies cover -/

omit hwf in
/-- The candidates of the table strategies are candidates. -/
theorem cands_of_strat {dd : Nat} {ts : Tables} {g : Goal} {X : GRel}
    (h : DC P.theory (produce.produceStrategies P ts g).1 X) : DC P.theory (produce P dd ts g).1 X :=
  h.mono fun c hc => by simp only [produce, List.mem_append]; exact Or.inr hc

theorem dc_unfold {dd : Nat} {ts : Tables} {g : Goal} {s : Span} (hf : unfoldFinal P dd g = true)
    (h : Derives P g.e s) : DC P.theory (produce P dd ts g).1 (GDen g s.den) :=
  (unfold_dc hwf hf h).mono fun c hc => by
    simp only [produce, List.mem_append]; exact Or.inl hc

theorem dc_span {dd : Nat} {ts : Tables} (lb rb : Option Span) (s : Span) :
    DC P.theory (produce P dd ts ⟨lb, .span s, rb⟩).1 (GDen ⟨lb, .span s, rb⟩ s.den) :=
  cands_of_strat (spanAnswer_dc hwf lb rb s)

omit hwf in
theorem dc_or {dd : Nat} {ts : Tables} {lb rb : Option Span} {a b l : Rel} {X : GRel}
    (hl : l ∈ orBranches (.or a b)) (h : DC P.theory (answersOf ts ⟨lb, l, rb⟩) X) :
    DC P.theory (produce P dd ts ⟨lb, .or a b, rb⟩).1 X :=
  cands_of_strat (h.mono fun c hc => by
    simp only [produce.produceStrategies, List.mem_flatMap, orLeaves, List.mem_map]
    exact ⟨_, ⟨l, hl, rfl⟩, hc⟩)

omit hwf in
theorem dc_call {dd : Nat} {ts : Tables} {lb rb : Option Span} {n : Name} {X : GRel}
    (h : DC P.theory (answersOf ts (callGoal P ⟨lb, .call n, rb⟩ n)) X) :
    DC P.theory (produce P dd ts ⟨lb, .call n, rb⟩).1 X :=
  cands_of_strat (by simpa [produce.produceStrategies] using h)

theorem dc_seq_join {dd : Nat} {ts : Tables} {lb rb : Option Span} {a b : Rel} {R₁ R₂ : GRel}
    (h₁ : DC P.theory (answersOf ts ⟨lb, a, none⟩) (GDen ⟨lb, a, none⟩ R₁))
    (h₂ : DC P.theory (answersOf ts ⟨none, b, rb⟩) (GDen ⟨none, b, rb⟩ R₂)) :
    DC P.theory (produce P dd ts ⟨lb, .seq a b, rb⟩).1 (GDen ⟨lb, .seq a b, rb⟩ (R₁.comp R₂)) := by
  have h := join_comp_dc hwf h₁ h₂
  rw [gden_seq lb rb a b (.seq a b)] at h
  refine cands_of_strat (h.mono fun c hc => ?_)
  simp only [produce.produceStrategies, seqLeft, seqRight, List.mem_append]
  exact Or.inl (Or.inl hc)

theorem dc_seq_pushL {dd : Nat} {ts : Tables} {lb rb : Option Span} {a b : Rel} {R₁ R₂ : GRel}
    (hd : doneOf ts ⟨lb, a, none⟩ = true)
    (h₁ : DC P.theory (answersOf ts ⟨lb, a, none⟩) (GDen ⟨lb, a, none⟩ R₁))
    (h₂ : ∀ x ∈ maxima (answersOf ts ⟨lb, a, none⟩),
      DC P.theory (answersOf ts (seqPushL ⟨lb, .seq a b, rb⟩ b x))
        (GDen (seqPushL ⟨lb, .seq a b, rb⟩ b x) R₂)) :
    DC P.theory (produce P dd ts ⟨lb, .seq a b, rb⟩).1 (GDen ⟨lb, .seq a b, rb⟩ (R₁.comp R₂)) := by
  rw [← gden_seqL lb rb a (.seq a b)]
  rcases h₁ with h₁ | ⟨x₀, hx₀, h₁⟩
  · exact Or.inl h₁.comp_left
  obtain ⟨x, hx, hcov⟩ := maxima_cover hx₀
  have hdx : LCov P.theory x.den (GDen ⟨lb, a, none⟩ R₁) := (lcov_of_covers hcov).trans h₁
  have hD : LCov P.theory ((x.den).comp (R₂.comp (bden rb)))
      ((GDen ⟨lb, a, none⟩ R₁).comp (R₂.comp (bden rb))) := hdx.comp (LCov.refl _)
  rcases h₂ x hx with h₂ | ⟨y, hy, h₂⟩
  · refine Or.inl (DeadR.of_dom hD ?_)
    have := (h₂.comp_right (X := x.den))
    simp only [seqPushL] at this
    rwa [gden_pushL] at this
  · have h := composeLive_dc hwf (LCov.refl x.den) h₂
    simp only [seqPushL] at h
    rw [gden_pushL] at h
    refine cands_of_strat ((h.dom hD).mono fun c hc => ?_)
    simp only [produce.produceStrategies, seqLeft, hd, ite_true, List.mem_append,
      List.mem_flatMap, List.mem_map]
    exact Or.inl (Or.inr ⟨_, ⟨x, hx, rfl⟩, y, hy, hc⟩)

theorem dc_seq_pushR {dd : Nat} {ts : Tables} {lb rb : Option Span} {a b : Rel} {R₁ R₂ : GRel}
    (hd : doneOf ts ⟨none, b, rb⟩ = true)
    (h₂ : DC P.theory (answersOf ts ⟨none, b, rb⟩) (GDen ⟨none, b, rb⟩ R₂))
    (h₁ : ∀ y ∈ maxima (answersOf ts ⟨none, b, rb⟩),
      DC P.theory (answersOf ts (seqPushR ⟨lb, .seq a b, rb⟩ a y))
        (GDen (seqPushR ⟨lb, .seq a b, rb⟩ a y) R₁)) :
    DC P.theory (produce P dd ts ⟨lb, .seq a b, rb⟩).1 (GDen ⟨lb, .seq a b, rb⟩ (R₁.comp R₂)) := by
  rw [← gden_seqR lb rb b (.seq a b)]
  rcases h₂ with h₂ | ⟨y₀, hy₀, h₂⟩
  · exact Or.inl h₂.comp_right
  obtain ⟨y, hy, hcov⟩ := maxima_cover hy₀
  have hdy : LCov P.theory y.den (GDen ⟨none, b, rb⟩ R₂) := (lcov_of_covers hcov).trans h₂
  have hD : LCov P.theory (((bden lb).comp R₁).comp y.den)
      (((bden lb).comp R₁).comp (GDen ⟨none, b, rb⟩ R₂)) := (LCov.refl _).comp hdy
  rcases h₁ y hy with h₁ | ⟨x, hx, h₁⟩
  · refine Or.inl (DeadR.of_dom hD ?_)
    have := (h₁.comp_left (Y := y.den))
    simp only [seqPushR] at this
    rwa [gden_pushR] at this
  · have h := composeLive_dc hwf h₁ (LCov.refl y.den)
    simp only [seqPushR] at h
    rw [gden_pushR] at h
    refine cands_of_strat ((h.dom hD).mono fun c hc => ?_)
    simp only [produce.produceStrategies, seqRight, hd, ite_true, List.mem_append,
      List.mem_flatMap, List.mem_map]
    exact Or.inr ⟨_, ⟨y, hy, rfl⟩, x, hx, hc⟩

theorem dc_and_join {dd : Nat} {ts : Tables} {lb rb : Option Span} (hg : GoodG ⟨lb, .zero, rb⟩)
    {a b : Rel} {R₁ R₂ : GRel}
    (h₁ : DC P.theory (answersOf ts ⟨lb, a, rb⟩) (GDen ⟨lb, a, rb⟩ R₁))
    (h₂ : DC P.theory (answersOf ts ⟨lb, b, rb⟩) (GDen ⟨lb, b, rb⟩ R₂)) :
    DC P.theory (produce P dd ts ⟨lb, .and a b, rb⟩).1 (GDen ⟨lb, .and a b, rb⟩ (R₁.meet R₂)) := by
  have h := join_meet_dc hwf h₁ h₂
  rw [gden_and hg a b (.and a b)] at h
  refine cands_of_strat (h.mono fun c hc => ?_)
  simp only [produce.produceStrategies, andLeft, andRight, List.mem_append]
  exact Or.inl (Or.inl hc)

theorem dc_and_pushL {dd : Nat} {ts : Tables} {lb rb : Option Span} (hg : GoodG ⟨lb, .zero, rb⟩)
    {a b : Rel} {R₁ R₂ : GRel}
    (hd : doneOf ts ⟨lb, a, rb⟩ = true)
    (h₁ : DC P.theory (answersOf ts ⟨lb, a, rb⟩) (GDen ⟨lb, a, rb⟩ R₁))
    (h₂ : ∀ x ∈ maxima (answersOf ts ⟨lb, a, rb⟩),
      DC P.theory (answersOf ts (andPush b x)) (GDen (andPush b x) R₂)) :
    DC P.theory (produce P dd ts ⟨lb, .and a b, rb⟩).1 (GDen ⟨lb, .and a b, rb⟩ (R₁.meet R₂)) := by
  rw [← gden_and hg a b (.and a b)]
  rcases h₁ with h₁ | ⟨x₀, hx₀, h₁⟩
  · exact Or.inl h₁.meet_left
  obtain ⟨x, hx, hcov⟩ := maxima_cover hx₀
  have hdx : LCov P.theory x.den (GDen ⟨lb, a, rb⟩ R₁) := (lcov_of_covers hcov).trans h₁
  have hD : LCov P.theory ((x.den).meet R₂) ((GDen ⟨lb, a, rb⟩ R₁).meet (GDen ⟨lb, b, rb⟩ R₂)) :=
    andPush_dom (bnd_fn hg.1) (bnd_fn hg.2) hdx
  rcases h₂ x hx with h₂ | ⟨y, hy, h₂⟩
  · refine Or.inl (DeadR.of_dom hD ?_)
    have := (h₂.meet_right (X := x.den))
    rwa [gden_andPush] at this
  · have h := meetLive_dc hwf (LCov.refl x.den) h₂
    rw [gden_andPush] at h
    refine cands_of_strat ((h.dom hD).mono fun c hc => ?_)
    simp only [produce.produceStrategies, andLeft, hd, ite_true, List.mem_append,
      List.mem_flatMap, List.mem_map]
    exact Or.inl (Or.inr ⟨_, ⟨x, hx, rfl⟩, y, hy, hc⟩)

theorem dc_and_pushR {dd : Nat} {ts : Tables} {lb rb : Option Span} (hg : GoodG ⟨lb, .zero, rb⟩)
    {a b : Rel} {R₁ R₂ : GRel}
    (hd : doneOf ts ⟨lb, b, rb⟩ = true)
    (h₂ : DC P.theory (answersOf ts ⟨lb, b, rb⟩) (GDen ⟨lb, b, rb⟩ R₂))
    (h₁ : ∀ y ∈ maxima (answersOf ts ⟨lb, b, rb⟩),
      DC P.theory (answersOf ts (andPush a y)) (GDen (andPush a y) R₁)) :
    DC P.theory (produce P dd ts ⟨lb, .and a b, rb⟩).1 (GDen ⟨lb, .and a b, rb⟩ (R₁.meet R₂)) := by
  rw [← gden_and hg a b (.and a b), meet_comm]
  rcases h₂ with h₂ | ⟨y₀, hy₀, h₂⟩
  · exact Or.inl h₂.meet_left
  obtain ⟨y, hy, hcov⟩ := maxima_cover hy₀
  have hdy : LCov P.theory y.den (GDen ⟨lb, b, rb⟩ R₂) := (lcov_of_covers hcov).trans h₂
  have hD : LCov P.theory ((y.den).meet R₁) ((GDen ⟨lb, b, rb⟩ R₂).meet (GDen ⟨lb, a, rb⟩ R₁)) :=
    andPush_dom (bnd_fn hg.1) (bnd_fn hg.2) hdy
  rcases h₁ y hy with h₁ | ⟨x, hx, h₁⟩
  · refine Or.inl (DeadR.of_dom hD ?_)
    have := (h₁.meet_right (X := y.den))
    rwa [gden_andPush] at this
  · have h := meetLive_dc hwf h₁ (LCov.refl y.den)
    rw [meet_comm, gden_andPush] at h
    refine cands_of_strat ((h.dom hD).mono fun c hc => ?_)
    simp only [produce.produceStrategies, andRight, hd, ite_true, List.mem_append,
      List.mem_flatMap, List.mem_map]
    exact Or.inr ⟨_, ⟨y, hy, rfl⟩, x, hx, hc⟩

end

end Tier0

end R001

end RwLog
