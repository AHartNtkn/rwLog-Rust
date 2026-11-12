/-
# Correctness of rung zero's unfolding and normalization
-/
import RwLog.Rungs.R000.Normalize

namespace RwLog

namespace R000

variable {P : Program}

/-! ## Unfolding -/

theorem sem_unfold (e : Rel) : denote P.meaning (unfold P e) = denote P.meaning e := by
  induction e with
  | zero => rfl
  | span s => rfl
  | or a b iha ihb => simp [unfold, denote, iha, ihb]
  | and a b iha ihb => simp [unfold, denote, iha, ihb]
  | seq a b iha ihb => simp [unfold, denote, iha, ihb]
  | conv a iha => simp [unfold, denote, iha]
  | call n => simp [unfold, denote, P.meaning_eq n]

theorem sem_unfoldN (k : Nat) (e : Rel) : P.sem (unfoldN P k e) = P.sem e := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    rw [unfoldN, Function.iterate_succ_apply]
    exact (ih _).trans (sem_unfold e)

theorem derivesN_unfold {k e s} (h : DerivesN P k e s) :
    ∀ {n}, k = n + 1 → DerivesN P n (unfold P e) s := by
  induction h with
  | span _ s => intro n _; exact .span n s
  | orl _ ih => intro n hk; exact .orl (ih hk)
  | orr _ ih => intro n hk; exact .orr (ih hk)
  | seq _ _ hc ih₁ ih₂ => intro n hk; exact .seq (ih₁ hk) (ih₂ hk) hc
  | and _ _ hc ih₁ ih₂ => intro n hk; exact .and (ih₁ hk) (ih₂ hk) hc
  | conv _ ih => intro n hk; exact .conv (ih hk)
  | call h _ => intro n hk; cases hk; exact h

theorem derivesN_unfoldN {e s} : ∀ (k n : Nat), DerivesN P (n + k) e s →
    DerivesN P n (unfoldN P k e) s
  | 0, n, h => h
  | k + 1, n, h => by
    rw [unfoldN, Function.iterate_succ_apply]
    exact derivesN_unfoldN k n (derivesN_unfold h (by omega))

/-! ## Derivations without unfolding -/

theorem mem_derivs {e s} : s ∈ derivs e ↔ DerivesN P 0 e s := by
  induction e generalizing s with
  | zero => simp [derivs]; intro h; cases h
  | span t =>
    simp only [derivs, List.mem_singleton]
    constructor
    · rintro rfl; exact .span 0 _
    · intro h; cases h; rfl
  | or a b iha ihb =>
    simp only [derivs, List.mem_append, iha, ihb]
    constructor
    · rintro (h | h)
      · exact .orl h
      · exact .orr h
    · intro h; cases h with
      | orl h => exact Or.inl h
      | orr h => exact Or.inr h
  | and a b iha ihb =>
    simp only [derivs, List.mem_flatMap, List.mem_filterMap, iha, ihb]
    constructor
    · rintro ⟨s₁, h₁, s₂, h₂, hc⟩; exact .and h₁ h₂ hc
    · intro h; cases h with
      | and h₁ h₂ hc => exact ⟨_, h₁, _, h₂, hc⟩
  | seq a b iha ihb =>
    simp only [derivs, List.mem_flatMap, List.mem_filterMap, iha, ihb]
    constructor
    · rintro ⟨s₁, h₁, s₂, h₂, hc⟩; exact .seq h₁ h₂ hc
    · intro h; cases h with
      | seq h₁ h₂ hc => exact ⟨_, h₁, _, h₂, hc⟩
  | conv a iha =>
    simp only [derivs, List.mem_map, iha]
    constructor
    · rintro ⟨t, h, rfl⟩; exact .conv h
    · intro h; cases h with
      | conv h => exact ⟨_, h, rfl⟩
  | call n => simp [derivs]; intro h; cases h

theorem derivesN_zero_of_callFree {n e s} (h : DerivesN P n e s) (hc : e.calls = []) :
    DerivesN P 0 e s := by
  induction h with
  | span _ s => exact .span 0 s
  | orl _ ih => simp [Rel.calls] at hc; exact .orl (ih hc.1)
  | orr _ ih => simp [Rel.calls] at hc; exact .orr (ih hc.2)
  | seq _ _ hcs ih₁ ih₂ => simp [Rel.calls] at hc; exact .seq (ih₁ hc.1) (ih₂ hc.2) hcs
  | and _ _ hcs ih₁ ih₂ => simp [Rel.calls] at hc; exact .and (ih₁ hc.1) (ih₂ hc.2) hcs
  | conv _ ih => simp [Rel.calls] at hc; exact .conv (ih hc)
  | call _ _ => simp [Rel.calls] at hc

/-! ## Joining chains -/

theorem denote_toRel_snoc (ρ : Name → GRel) (p : List Rel) (x : Rel) :
    denote ρ (toRel (p ++ [x])) = (denote ρ (toRel p)).comp (denote ρ x) := by
  rw [denote_toRel_append]; rfl

theorem joinSeq_sound (ρ : Name → GRel) {p q r : List Rel} (h : joinSeq p q = some r) :
    denote ρ (toRel r) ⊆ (denote ρ (toRel p)).comp (denote ρ (toRel q)) := by
  unfold joinSeq at h
  split at h
  · rename_i a b q' hl
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
    have hp : p = p.dropLast ++ [.span a] := (List.dropLast_append_getLast? _ hl).symm
    conv_rhs => rw [hp]
    rw [denote_toRel_snoc, denote_toRel_cons, denote_toRel_append, denote_toRel_cons]
    simp only [denote]
    rw [compose_some hc, GRel.comp_assoc (Span.den a), GRel.comp_assoc (denote ρ (toRel p.dropLast))]
  · cases h; rw [denote_toRel_append]

theorem derivesN_toRel_single {n x s} (h : DerivesN P n (toRel [x]) s) : DerivesN P n x s := h

theorem joinSeq_complete {n p q s₁ s₂} (h₁ : DerivesN P n (toRel p) s₁)
    (h₂ : DerivesN P n (toRel q) s₂) (hne : ((s₁.den).comp s₂.den).Nonempty) :
    ∃ r, joinSeq p q = some r ∧ ∃ s, DerivesN P n (toRel r) s ∧ (s₁.den).comp s₂.den ⊆ s.den := by
  unfold joinSeq
  split
  · rename_i a b q' hl
    have hp : p = p.dropLast ++ [.span a] := (List.dropLast_append_getLast? _ hl).symm
    rw [hp] at h₁
    obtain ⟨sp, sa, hsp, hsa, hs₁⟩ := chain_split _ _ h₁ (GRel.comp_nonempty_left hne)
    obtain ⟨sb, sq, hsb, hsq, hs₂⟩ := chain_cons_split h₂
    obtain rfl : sa = a := by cases hsa; rfl
    obtain rfl : sb = b := by cases hsb; rfl
    have hsub : (s₁.den).comp s₂.den ⊆ (sp.den).comp (((sa.den).comp sb.den).comp sq.den) := by
      calc (s₁.den).comp s₂.den
          ⊆ ((sp.den).comp sa.den).comp ((sb.den).comp sq.den) := GRel.comp_mono hs₁ hs₂
        _ = (sp.den).comp (((sa.den).comp sb.den).comp sq.den) := by
          simp only [GRel.comp_assoc]
    have hne' := hne.mono hsub
    obtain ⟨c, hc, hcd⟩ := compose_isSome
      (GRel.comp_nonempty_left (GRel.comp_nonempty_right hne'))
    refine ⟨_, by rw [hc]; rfl, ?_⟩
    rw [← hcd] at hsub hne'
    obtain ⟨t, ht, ht'⟩ := chain_cons_join (.span n c) hsq (GRel.comp_nonempty_right hne')
    obtain ⟨u, hu, hu'⟩ := chain_join _ _ hsp ht (hne'.mono (GRel.comp_mono le_rfl ht'))
    exact ⟨u, hu, hsub.trans ((GRel.comp_mono le_rfl ht').trans hu')⟩
  · exact ⟨_, rfl, chain_join _ _ h₁ h₂ hne⟩

/-! ## Conjoining products -/

theorem mkAnd_sound (ρ : Name → GRel) {p q r : List Rel} (h : mkAnd p q = some r) :
    denote ρ (toRel r) ⊆ (denote ρ (toRel p)).meet (denote ρ (toRel q)) := by
  unfold mkAnd at h
  split at h
  · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
    show c.den ⊆ _
    rw [meet_some hc]; exact le_rfl
  · cases h; exact le_rfl

theorem mkAnd_complete {n p q s₁ s₂} (h₁ : DerivesN P n (toRel p) s₁)
    (h₂ : DerivesN P n (toRel q) s₂) (hne : ((s₁.den).meet s₂.den).Nonempty) :
    ∃ r, mkAnd p q = some r ∧ ∃ s, DerivesN P n (toRel r) s ∧ (s₁.den).meet s₂.den ⊆ s.den := by
  unfold mkAnd
  split
  · rename_i a b
    cases h₁; cases h₂
    obtain ⟨c, hc, hcd⟩ := meet_isSome hne
    exact ⟨_, by rw [hc]; rfl, c, .span n c, hcd.ge⟩
  · obtain ⟨s, hc, hs⟩ := meet_isSome hne
    exact ⟨_, rfl, s, .and h₁ h₂ hc, hs.ge⟩

/-! ## Normalization -/

theorem denote_orient (ρ : Name → GRel) (neg : Bool) (e : Rel) :
    denote ρ (orient neg e) = if neg then (denote ρ e).inv else denote ρ e := by
  cases neg <;> rfl

theorem norm_sound (ρ : Name → GRel) :
    ∀ (neg : Bool) (e : Rel), ∀ p ∈ norm neg e, denote ρ (toRel p) ⊆ denote ρ (orient neg e)
  | _, .zero, p, hp => by simp [norm] at hp
  | neg, .span s, p, hp => by
    simp only [norm, List.mem_singleton] at hp; subst hp
    cases neg
    · exact le_rfl
    · show s.swap.den ⊆ _; rw [swap_den]; exact le_rfl
  | neg, .or a b, p, hp => by
    simp only [norm, List.mem_append] at hp
    rw [denote_orient]
    rcases hp with hp | hp
    · have := norm_sound ρ neg a p hp; rw [denote_orient] at this
      cases neg
      · exact this.trans Set.subset_union_left
      · exact this.trans (GRel.inv_mono Set.subset_union_left)
    · have := norm_sound ρ neg b p hp; rw [denote_orient] at this
      cases neg
      · exact this.trans Set.subset_union_right
      · exact this.trans (GRel.inv_mono Set.subset_union_right)
  | false, .seq a b, p, hp => by
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    exact (joinSeq_sound ρ hj).trans
      (GRel.comp_mono (norm_sound ρ false a p₁ hp₁) (norm_sound ρ false b p₂ hp₂))
  | true, .seq a b, p, hp => by
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    refine (joinSeq_sound ρ hj).trans ?_
    show _ ⊆ (GRel.comp _ _).inv
    rw [GRel.inv_comp]
    exact GRel.comp_mono (norm_sound ρ true b p₁ hp₁) (norm_sound ρ true a p₂ hp₂)
  | neg, .and a b, p, hp => by
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    refine (mkAnd_sound ρ hj).trans ?_
    have h₁ := norm_sound ρ neg a p₁ hp₁
    have h₂ := norm_sound ρ neg b p₂ hp₂
    rw [denote_orient] at h₁ h₂ ⊢
    cases neg
    · exact GRel.meet_mono h₁ h₂
    · show _ ⊆ (GRel.meet _ _).inv
      rw [GRel.inv_meet]; exact GRel.meet_mono h₁ h₂
  | neg, .conv a, p, hp => by
    simp only [norm] at hp
    have := norm_sound ρ (!neg) a p hp
    rw [denote_orient] at this ⊢
    cases neg
    · exact this
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at this ⊢
      show _ ⊆ (GRel.inv _).inv
      rw [GRel.inv_inv]; exact this
  | neg, .call n, p, hp => by
    simp only [norm, List.mem_singleton] at hp; subst hp
    cases neg <;> exact le_rfl

theorem orientS_den (neg : Bool) (s : Span) :
    (orientS neg s).den = if neg then (s.den).inv else s.den := by
  cases neg
  · rfl
  · exact swap_den s

theorem norm_complete {n e s} (h : DerivesN P n e s) :
    ∀ neg, ((orientS neg s).den).Nonempty →
      ∃ p ∈ norm neg e, ∃ s', DerivesN P n (toRel p) s' ∧ (orientS neg s).den ⊆ s'.den := by
  induction h with
  | span n s =>
    intro neg _
    cases neg
    · exact ⟨[.span s], by simp [norm], s, .span n s, le_rfl⟩
    · exact ⟨[.span s.swap], by simp [norm], s.swap, .span n _, le_rfl⟩
  | orl _ ih =>
    intro neg hne
    obtain ⟨p, hp, s', h', hs⟩ := ih neg hne
    exact ⟨p, by simp [norm, hp], s', h', hs⟩
  | orr _ ih =>
    intro neg hne
    obtain ⟨p, hp, s', h', hs⟩ := ih neg hne
    exact ⟨p, by simp [norm, hp], s', h', hs⟩
  | @seq n a b s₁ s₂ s _ _ hc ih₁ ih₂ =>
    intro neg hne
    rw [orientS_den, compose_some hc] at hne ⊢
    cases neg
    · simp only [Bool.false_eq_true, ite_false] at hne ⊢
      obtain ⟨p₁, hp₁, t₁, ht₁, hs₁⟩ := ih₁ false (by simpa [orientS] using GRel.comp_nonempty_left hne)
      obtain ⟨p₂, hp₂, t₂, ht₂, hs₂⟩ := ih₂ false (by simpa [orientS] using GRel.comp_nonempty_right hne)
      have hsub := GRel.comp_mono hs₁ hs₂
      obtain ⟨r, hr, u, hu, hu'⟩ := joinSeq_complete ht₁ ht₂ (hne.mono hsub)
      exact ⟨r, by simp only [norm, List.mem_flatMap, List.mem_filterMap]; exact ⟨p₁, hp₁, p₂, hp₂, hr⟩,
        u, hu, hsub.trans hu'⟩
    · simp only [ite_true] at hne ⊢
      rw [GRel.inv_comp] at hne ⊢
      obtain ⟨p₂, hp₂, t₂, ht₂, hs₂⟩ := ih₂ true (by rw [orientS_den]; exact GRel.comp_nonempty_left hne)
      obtain ⟨p₁, hp₁, t₁, ht₁, hs₁⟩ := ih₁ true (by rw [orientS_den]; exact GRel.comp_nonempty_right hne)
      rw [orientS_den] at hs₁ hs₂
      have hsub := GRel.comp_mono hs₂ hs₁
      obtain ⟨r, hr, u, hu, hu'⟩ := joinSeq_complete ht₂ ht₁ (hne.mono hsub)
      exact ⟨r, by simp only [norm, List.mem_flatMap, List.mem_filterMap]; exact ⟨p₂, hp₂, p₁, hp₁, hr⟩,
        u, hu, hsub.trans hu'⟩
  | @and n a b s₁ s₂ s _ _ hc ih₁ ih₂ =>
    intro neg hne
    have heq : (orientS neg s).den = ((orientS neg s₁).den).meet (orientS neg s₂).den := by
      rw [orientS_den, orientS_den, orientS_den, meet_some hc]
      cases neg
      · rfl
      · simp only [ite_true]; rw [GRel.inv_meet]
    rw [heq] at hne ⊢
    have hn1 : ((orientS neg s₁).den).Nonempty := by
      obtain ⟨x, A, B, ha, _, _⟩ := hne; exact ⟨_, ha⟩
    have hn2 : ((orientS neg s₂).den).Nonempty := by
      obtain ⟨x, A, B, _, hb, _⟩ := hne; exact ⟨_, hb⟩
    obtain ⟨p₁, hp₁, t₁, ht₁, hs₁⟩ := ih₁ neg hn1
    obtain ⟨p₂, hp₂, t₂, ht₂, hs₂⟩ := ih₂ neg hn2
    have hsub := GRel.meet_mono hs₁ hs₂
    obtain ⟨r, hr, u, hu, hu'⟩ := mkAnd_complete ht₁ ht₂ (hne.mono hsub)
    exact ⟨r, by simp only [norm, List.mem_flatMap, List.mem_filterMap]; exact ⟨p₁, hp₁, p₂, hp₂, hr⟩,
      u, hu, hsub.trans hu'⟩
  | @conv n a s _ ih =>
    intro neg hne
    have heq : orientS neg s.swap = orientS (!neg) s := by
      cases neg <;> rfl
    rw [heq] at hne ⊢
    obtain ⟨p, hp, s', h', hs⟩ := ih (!neg) hne
    exact ⟨p, by simpa [norm] using hp, s', h', hs⟩
  | @call n m s h _ =>
    intro neg _
    cases neg
    · exact ⟨[.call m], by simp [norm], s, .call h, le_rfl⟩
    · exact ⟨[.conv (.call m)], by simp [norm], s.swap, .conv (.call h), le_rfl⟩

end R000

end RwLog
