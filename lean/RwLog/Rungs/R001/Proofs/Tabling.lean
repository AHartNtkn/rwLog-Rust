/-
# Rung R001: tabling termination

If the goals that can arise from a query fall into finitely many classes of
equal table keys, and each has a finite cover of its derivable answers, the
query has a certificate: one entry per class, with the key of a
representative as its goal, the finite cover moved onto the key as its cover,
and rank zero. Every entry takes the strategy that reads the key's direct
goals, which needs no ranks. The key of a reachable goal has direct goals
whose keys are again keys of reachable goals (`key_direct`): taking a key
strips converses and flattens a `|` nest, and both stay inside the goals a
goal reads directly.
-/
import RwLog.Rungs.R001.Proofs.CertCombine
import RwLog.Rungs.R001.Proofs.SymmetryProduce

namespace RwLog

namespace R001

namespace Tabling

open Tier0 Exact CertHalts CertOfHalt Combine Symmetry

variable {P : Program}

/-! ## Reachable goals -/

theorem direct_good {g d : Goal} (hg : GoodG g) (hd : d ∈ directGoals P g) : GoodG d := by
  obtain ⟨lb, e, rb⟩ := g
  cases e with
  | zero => simp [directGoals] at hd
  | span _ => simp [directGoals] at hd
  | or a b =>
    simp only [directGoals, orLeaves, List.mem_map] at hd
    obtain ⟨c, -, rfl⟩ := hd
    exact hg
  | call n =>
    simp only [directGoals, List.mem_singleton] at hd
    subst hd; exact hg
  | conv a =>
    simp only [directGoals, List.mem_singleton] at hd
    subst hd; exact goodG_convGoal hg a
  | seq a b =>
    simp only [directGoals, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hg.1, trivial⟩
    · exact ⟨trivial, hg.2⟩
  | and a b =>
    simp only [directGoals, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> exact hg

theorem reach_good {root g : Goal} (hr : GoodG root) (h : Reach P root g) : GoodG g := by
  induction h with
  | root => exact hr
  | direct _ hd ih => exact direct_good ih hd
  | seqPushL _ _ _ ih => exact goodG_pushL ih _ _
  | seqPushR _ _ _ ih => exact goodG_pushR ih _ _
  | andPushL _ _ _ _ => exact goodG_andPush _ _
  | andPushR _ _ _ _ => exact goodG_andPush _ _

/-- The direct goals of a reachable goal's key have the keys of reachable
goals. -/
theorem key_direct {root : Goal} : ∀ (n : Nat) (g : Goal), sizeOf g.e ≤ n → Reach P root g →
    ∀ d ∈ directGoals P g.norm.2, ∃ g', Reach P root g' ∧ g'.norm = d.norm := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro g hn hr d hd
  obtain ⟨lb, e, rb⟩ := g
  cases e with
  | zero =>
    rw [show (⟨lb, .zero, rb⟩ : Goal).norm.2 = ⟨lb, .zero, rb⟩ by
      simp only [Goal.norm, canon]; rw [strip_nc _ (by simp)]] at hd
    simp [directGoals] at hd
  | span s =>
    rw [show (⟨lb, .span s, rb⟩ : Goal).norm.2 = ⟨lb, .span s, rb⟩ by
      simp only [Goal.norm, canon]; rw [strip_nc _ (by simp)]] at hd
    simp [directGoals] at hd
  | call m =>
    rw [show (⟨lb, .call m, rb⟩ : Goal).norm.2 = ⟨lb, .call m, rb⟩ by
      simp only [Goal.norm, canon]; rw [strip_nc _ (by simp)]] at hd
    exact ⟨d, .direct hr hd, rfl⟩
  | seq a b =>
    rw [show (⟨lb, .seq a b, rb⟩ : Goal).norm.2 = ⟨lb, .seq (canon a) (canon b), rb⟩ by
      simp only [Goal.norm, canon]; rw [strip_nc _ (by simp)]] at hd
    simp only [directGoals, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨seqLeft ⟨lb, .seq a b, rb⟩ a, .direct hr (by simp [directGoals]),
        (norm_canon _ _ _).symm⟩
    · exact ⟨seqRight ⟨lb, .seq a b, rb⟩ b, .direct hr (by simp [directGoals]),
        (norm_canon _ _ _).symm⟩
  | and a b =>
    rw [show (⟨lb, .and a b, rb⟩ : Goal).norm.2 = ⟨lb, .and (canon a) (canon b), rb⟩ by
      simp only [Goal.norm, canon]; rw [strip_nc _ (by simp)]] at hd
    simp only [directGoals, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨andLeft ⟨lb, .and a b, rb⟩ a, .direct hr (by simp [directGoals]),
        (norm_canon _ _ _).symm⟩
    · exact ⟨andRight ⟨lb, .and a b, rb⟩ b, .direct hr (by simp [directGoals]),
        (norm_canon _ _ _).symm⟩
  | conv a =>
    have hk : (⟨lb, .conv a, rb⟩ : Goal).norm.2 = (convGoal ⟨lb, .conv a, rb⟩ a).norm.2 := by
      simp only [Goal.norm, canon, convGoal]; rw [strip_conv]
    rw [hk] at hd
    exact IH (sizeOf a) (by simp at hn; omega) (convGoal ⟨lb, .conv a, rb⟩ a) le_rfl
      (.direct hr (by simp [directGoals])) d hd
  | or a b =>
    have hraw : ∀ z ∈ sortedBranches (orBranches (canon a) ++ orBranches (canon b)),
        ∃ l ∈ orBranches (.or a b), canon l = z := by
      intro z hz
      obtain ⟨hz1, hz0⟩ := Symmetry.mem_sortedBranches.1 hz
      rcases List.mem_append.1 hz1 with h | h
      · obtain ⟨l, hl, e⟩ := (mem_orBranches_canon a hz0).1 h
        exact ⟨l, by simp [orBranches, hl], e⟩
      · obtain ⟨l, hl, e⟩ := (mem_orBranches_canon b hz0).1 h
        exact ⟨l, by simp [orBranches, hl], e⟩
    have hno : ∀ x ∈ sortedBranches (orBranches (canon a) ++ orBranches (canon b)), NotOr x :=
      notOr_sorted fun x hx => (List.mem_append.1 hx).elim notOr_of_mem_orBranches
        notOr_of_mem_orBranches
    have hleaf : ∀ l ∈ orBranches (.or a b), Reach P root ⟨lb, l, rb⟩ := fun l hl =>
      .direct hr (by simp only [directGoals, orLeaves, List.mem_map]; exact ⟨l, hl, rfl⟩)
    have hnorm : (⟨lb, .or a b, rb⟩ : Goal).norm =
        Goal.stripConv ⟨lb, mkOr (sortedBranches (orBranches (canon a) ++ orBranches (canon b))), rb⟩ :=
      rfl
    rw [hnorm] at hd
    generalize hbs : sortedBranches (orBranches (canon a) ++ orBranches (canon b)) = bs at *
    match bs, hbs with
    | [], _ =>
      rw [show mkOr [] = Rel.zero from rfl, strip_nc _ (by simp)] at hd
      simp [directGoals] at hd
    | [c], _ =>
      obtain ⟨l, hl, rfl⟩ := hraw c (by simp)
      have hsz := sizeOf_lt_of_mem_orBranches hl
      exact IH (sizeOf l) (by simp only at hn; omega) ⟨lb, l, rb⟩ le_rfl (hleaf l hl) d hd
    | c₁ :: c₂ :: rest, _ =>
      rw [show mkOr (c₁ :: c₂ :: rest) = .or c₁ (mkOr (c₂ :: rest)) from rfl,
        strip_nc _ (by simp)] at hd
      simp only [directGoals, orLeaves, List.mem_map] at hd
      obtain ⟨z, hz, rfl⟩ := hd
      rw [show Rel.or c₁ (mkOr (c₂ :: rest)) = mkOr (c₁ :: c₂ :: rest) from rfl,
        orBranches_mkOr_eq hno (by simp)] at hz
      obtain ⟨l, hl, rfl⟩ := hraw z hz
      exact ⟨⟨lb, l, rb⟩, hleaf l hl, (norm_canon _ _ _).symm⟩

/-! ## The certificate -/

theorem covers_oS (f : Bool) {a b : Span} (h : a.Covers b) : (oS f a).Covers (oS f b) := by
  cases f
  · exact h
  · exact covers_swap h

theorem oS_oS (f : Bool) (a : Span) : oS f (oS f a) = a := by cases f <;> rfl

theorem oR_oR (f : Bool) (R : GRel) : oR f (oR f R) = R := by
  cases f
  · rfl
  · exact GRel.inv_inv R

/-- The strategy that reads a goal's direct goals. -/
theorem direct_strat (C : List CertEntry) (g : Goal) :
    (directGoals P g).map (fun d => (d, false)) ∈ certStrategies P C g := by
  obtain ⟨lb, e, rb⟩ := g
  cases e <;> simp [directGoals, certStrategies]

/-- One reachable goal for each class of keys that a reachable goal has. -/
theorem reps {root : Goal} : ∀ Gs : List Goal, ∃ Ks : List Goal, (∀ k ∈ Ks, Reach P root k) ∧
    ∀ g, Reach P root g → (∃ h ∈ Gs, h.same g.norm.2 = true) →
      ∃ k ∈ Ks, k.norm.2.same g.norm.2 = true
  | [] => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | h :: Gs => by
    obtain ⟨Ks, h1, h2⟩ := reps (root := root) Gs
    by_cases hex : ∃ g, Reach P root g ∧ h.same g.norm.2 = true
    · obtain ⟨g₀, hr₀, hs₀⟩ := hex
      refine ⟨g₀ :: Ks, fun k hk => ?_, ?_⟩
      · rcases List.mem_cons.1 hk with rfl | hk
        · exact hr₀
        · exact h1 k hk
      · rintro g hr ⟨h', hh', hs⟩
        rcases List.mem_cons.1 hh' with rfl | hh'
        · exact ⟨g₀, List.mem_cons_self, Goal.same_trans (Goal.same_symm hs₀) hs⟩
        · obtain ⟨k, hk, hks⟩ := h2 g hr ⟨h', hh', hs⟩
          exact ⟨k, List.mem_cons_of_mem _ hk, hks⟩
    · refine ⟨Ks, h1, ?_⟩
      rintro g hr ⟨h', hh', hs⟩
      rcases List.mem_cons.1 hh' with rfl | hh'
      · exact absurd ⟨g, hr, hs⟩ hex
      · exact h2 g hr ⟨h', hh', hs⟩

section Laws

variable (hL : SimpLaws P.theory)
include hL

/-- A finite cover of a goal's derivable answers, moved onto the goal's key. -/
theorem goodE_of_finiteCover {g : Goal} (hg : GoodG g) (hF : FiniteCover P g) :
    ∃ F, GoodE P ⟨g.norm.2, F, 0⟩ := by
  obtain ⟨F₀, hF₀1, hF₀2⟩ := hF
  have hk := goodG_norm hg
  obtain ⟨F, hF1, hF2⟩ := cover_exists hL hk (F₀.map (oS g.norm.1)) (by
    intro a ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
    obtain ⟨s, hd, hsub⟩ := gderives_sub hL (hF₀1 f hf) hg
    obtain ⟨w, hw⟩ := dw_of_derives hd
    obtain ⟨w', s', h1, -, h4⟩ := norm_meas g hw
    rw [h4] at hsub
    have := sub_oS hL g.norm.1 hsub
    rw [oR_oR] at this
    exact ⟨s', h1.derives, this⟩)
  refine ⟨F, hk, hF1, fun s' hs' w hdom w' hsimp => ?_⟩
  obtain ⟨hder, hden⟩ := norm_back g hs'
  have hsub : Under P.theory (GDen g.norm.2 s'.den) w' := ⟨w, hdom, w', hsimp, Span.Covers.refl _⟩
  have hsub' := sub_oS hL g.norm.1 hsub
  rw [← hden] at hsub'
  obtain ⟨y₀, hy₀, hy₀c⟩ := realise_sub hL hg hder hsub'
  obtain ⟨f, hf, hfc⟩ := hF₀2 y₀ hy₀
  obtain ⟨y, hy, hyc⟩ := hF2 (oS g.norm.1 f) (List.mem_map.2 ⟨f, hf, rfl⟩)
  refine ⟨y, hy, hyc.trans ?_⟩
  have := covers_oS g.norm.1 (hfc.trans hy₀c)
  rwa [oS_oS] at this

/-- Good entries of rank zero for the keys of finitely many reachable
goals. -/
theorem entries {root : Goal} (hr : GoodG root) (hfc : ∀ g, Reach P root g → FiniteCover P g) :
    ∀ Ks : List Goal, (∀ k ∈ Ks, Reach P root k) →
    ∃ C : List CertEntry, (∀ e ∈ C, GoodE P e ∧ e.rank = 0 ∧ ∃ k ∈ Ks, e.goal = k.norm.2) ∧
      ∀ k ∈ Ks, ∃ e ∈ C, e.goal = k.norm.2
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | k :: Ks, h => by
    obtain ⟨C, h1, h2⟩ := entries hr hfc Ks fun k hk => h k (List.mem_cons_of_mem _ hk)
    have hrk := h k List.mem_cons_self
    obtain ⟨F, hF⟩ := goodE_of_finiteCover hL (reach_good hr hrk) (hfc k hrk)
    refine ⟨⟨k.norm.2, F, 0⟩ :: C, fun e he => ?_, fun k' hk' => ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨hF, rfl, k, List.mem_cons_self, rfl⟩
      · obtain ⟨a, b, k', hk', e'⟩ := h1 e he
        exact ⟨a, b, k', List.mem_cons_of_mem _ hk', e'⟩
    · rcases List.mem_cons.1 hk' with rfl | hk'
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨e, he, e'⟩ := h2 k' hk'
        exact ⟨e, List.mem_cons_of_mem _ he, e'⟩

/-- Finitely many keys and finite covers give a certificate. -/
theorem tabling_cert {root : Goal} (hroot : GoodG root)
    (hG : ∃ Gs : List Goal, ∀ g, Reach P root g → ∃ h ∈ Gs, h.same g.norm.2 = true)
    (hfc : ∀ g, Reach P root g → FiniteCover P g) : ∃ C, Cert.Valid P C 0 root := by
  obtain ⟨Gs, hGs⟩ := hG
  obtain ⟨Ks, hK1, hK2⟩ := reps (P := P) (root := root) Gs
  obtain ⟨C, hC1, hC2⟩ := entries hL hroot hfc Ks hK1
  have listed : ∀ g, Reach P root g → ∃ e ∈ C, e.goal.same g.norm.2 = true := by
    intro g hr
    obtain ⟨k, hk, hks⟩ := hK2 g hr (hGs g hr)
    obtain ⟨e, he, heq⟩ := hC2 k hk
    exact ⟨e, he, by rw [heq]; exact hks⟩
  refine ⟨C, valid_of_pre hL ⟨fun e he => (hC1 e he).1, fun e he =>
    .inr ⟨_, direct_strat C e.goal, ?_⟩⟩ (listed root .root)⟩
  rintro ⟨d, fl⟩ hd
  obtain ⟨d', hd', heq⟩ := List.mem_map.1 hd
  cases heq
  obtain ⟨-, -, k, hk, hek⟩ := hC1 e he
  rw [hek] at hd'
  obtain ⟨g', hr', hn⟩ := key_direct _ k le_rfl (hK1 k hk) _ hd'
  obtain ⟨e', he', hs'⟩ := listed g' hr'
  exact ⟨e', he', by rw [← hn]; exact hs', by simp [(hC1 e' he').2.1]⟩

end Laws

end Tabling

end R001

end RwLog
