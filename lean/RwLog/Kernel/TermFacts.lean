/-
# Facts about terms and one-way matching

Lemmas the kernel's definitions rely on (the closure's termination in
`Kernel/Refute.lean`) and the proofs share: how variables and symbols move
under substitution, and what a successful match guarantees.
-/
import RwLog.Kernel.Match

namespace RwLog

namespace Term

variable {V W : Type}

theorem vars_bind_mem {σ : V → Term W} {u : W} :
    ∀ {t : Term V}, u ∈ (t.bind σ).vars → ∃ v ∈ t.vars, u ∈ (σ v).vars
  | .var v, h => ⟨v, by simp [vars], h⟩
  | .sym _, h => by simp [vars] at h
  | .app t t', h => by
    simp only [bind_app, vars, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨v, hv, hu⟩ := vars_bind_mem h; exact ⟨v, by simp [vars, hv], hu⟩
    · obtain ⟨v, hv, hu⟩ := vars_bind_mem h; exact ⟨v, by simp [vars, hv], hu⟩

theorem vars_sub_bind {σ : V → Term W} {v : V} :
    ∀ {t : Term V}, v ∈ t.vars → ∀ u ∈ (σ v).vars, u ∈ (t.bind σ).vars
  | .var w, h, u, hu => by simp [vars] at h; subst h; simpa using hu
  | .sym _, h, _, _ => by simp [vars] at h
  | .app t t', h, u, hu => by
    simp only [vars, List.mem_append] at h
    simp only [bind_app, vars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (vars_sub_bind h u hu)
    · exact Or.inr (vars_sub_bind h u hu)

theorem syms_bind_sub {σ : V → Term W} {t : Term V} {f : Sym} (h : f ∈ (t.bind σ).syms) :
    f ∈ t.syms ∨ ∃ v ∈ t.vars, f ∈ (σ v).syms := by
  induction t with
  | var v => exact .inr ⟨v, by simp [Term.vars], h⟩
  | sym g => exact .inl (by simpa [Term.syms] using h)
  | app t u iht ihu =>
    simp only [bind_app, Term.syms, List.mem_append] at h
    rcases h with h | h
    · rcases iht h with h | ⟨v, hv, h⟩
      · exact .inl (by simp [Term.syms, h])
      · exact .inr ⟨v, by simp [Term.vars, hv], h⟩
    · rcases ihu h with h | ⟨v, hv, h⟩
      · exact .inl (by simp [Term.syms, h])
      · exact .inr ⟨v, by simp [Term.vars, hv], h⟩

theorem syms_var_sub {σ : V → Term W} {t : Term V} {v : V} (hv : v ∈ t.vars) {f : Sym}
    (h : f ∈ (σ v).syms) : f ∈ (t.bind σ).syms := by
  induction t with
  | var w => simp [Term.vars] at hv; subst hv; exact h
  | sym g => simp [Term.vars] at hv
  | app t u iht ihu =>
    simp only [Term.vars, List.mem_append] at hv
    simp only [bind_app, Term.syms, List.mem_append]
    rcases hv with hv | hv
    · exact .inl (iht hv)
    · exact .inr (ihu hv)

end Term

namespace Matching

open Term


/-- `θ'` keeps every binding of `θ`. -/
def Ext (θ θ' : PSubst) : Prop := ∀ v x, θ.lookup v = some x → θ'.lookup v = some x

theorem Ext.refl (θ : PSubst) : Ext θ θ := fun _ _ h => h

theorem Ext.trans {a b c : PSubst} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c :=
  fun v x h => h₂ v x (h₁ v x h)

theorem lookup_cons (v w : Nat) (t : Pat) (θ : PSubst) :
    List.lookup w ((v, t) :: θ) = if w = v then some t else θ.lookup w := by
  by_cases h : w = v
  · subst h; simp [List.lookup]
  · have hb : (w == v) = false := by simpa using h
    simp [List.lookup, hb, h]

/-- What a successful match guarantees. -/
theorem matchInto_sound :
    ∀ (p t : Pat) (θ θ' : PSubst), matchInto p t θ = some θ' →
      Ext θ θ' ∧ (∀ v ∈ p.vars, ∃ x, θ'.lookup v = some x) ∧
      ∀ θ'', Ext θ' θ'' → p.bind θ''.apply = t
  | .var v, t, θ, θ', h => by
    simp only [matchInto] at h
    cases hl : θ.lookup v with
    | some u =>
      rw [hl] at h
      by_cases hu : u = t
      · simp [hu] at h; subst h; subst hu
        refine ⟨Ext.refl _, fun w hw => ?_, fun θ'' h'' => ?_⟩
        · simp [vars] at hw; subst hw; exact ⟨_, hl⟩
        · simp [PSubst.apply, h'' v u hl]
      · simp [hu] at h
    | none =>
      rw [hl] at h; simp at h; subst h
      refine ⟨fun w x hw => ?_, fun w hw => ?_, fun θ'' h'' => ?_⟩
      · rw [lookup_cons]; by_cases hwv : w = v
        · subst hwv; rw [hl] at hw; cases hw
        · simp [hwv, hw]
      · simp [vars] at hw; subst hw; exact ⟨t, by simp [List.lookup]⟩
      · simp [PSubst.apply, h'' v t (by simp [List.lookup])]
  | .sym f, .sym g, θ, θ', h => by
    simp only [matchInto] at h
    by_cases hfg : f = g
    · simp [hfg] at h; subst h; subst hfg
      exact ⟨Ext.refl _, fun w hw => by simp [vars] at hw, fun _ _ => rfl⟩
    · simp [hfg] at h
  | .app p q, .app t u, θ, θ', h => by
    simp only [matchInto, Option.bind_eq_some_iff] at h
    obtain ⟨θ₁, h₁, h₂⟩ := h
    obtain ⟨e₁, b₁, k₁⟩ := matchInto_sound p t θ θ₁ h₁
    obtain ⟨e₂, b₂, k₂⟩ := matchInto_sound q u θ₁ θ' h₂
    refine ⟨e₁.trans e₂, fun w hw => ?_, fun θ'' h'' => ?_⟩
    · simp only [vars, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨x, hx⟩ := b₁ w hw; exact ⟨x, e₂ w x hx⟩
      · exact b₂ w hw
    · simp [k₁ θ'' (e₂.trans h''), k₂ θ'' h'']
  | .sym _, .var _, _, _, h => by simp [matchInto] at h
  | .sym _, .app _ _, _, _, h => by simp [matchInto] at h
  | .app _ _, .var _, _, _, h => by simp [matchInto] at h
  | .app _ _, .sym _, _, _, h => by simp [matchInto] at h


theorem matchAll_sound :
    ∀ (ps ts : List Pat) (θ : PSubst) (r : PSubst × List Pat), r ∈ matchAll ps ts θ →
      Ext θ r.1 ∧ (∀ p ∈ ps, ∀ v ∈ p.vars, ∃ x, r.1.lookup v = some x) ∧
      (∀ t ∈ r.2, t ∈ ts) ∧ ∀ θ'', Ext r.1 θ'' → ps.map (Term.bind θ''.apply) = r.2
  | [], ts, θ, r, h => by
    simp [matchAll] at h; subst h
    exact ⟨Ext.refl _, by simp, by simp, fun _ _ => rfl⟩
  | p :: ps, ts, θ, r, h => by
    simp only [matchAll, List.mem_flatMap] at h
    obtain ⟨t, ht, h⟩ := h
    cases hm : matchInto p t θ with
    | none => rw [hm] at h; simp at h
    | some θ₁ =>
      rw [hm] at h
      simp only [List.mem_map] at h
      obtain ⟨r', hr', rfl⟩ := h
      obtain ⟨e₁, b₁, k₁⟩ := matchInto_sound p t θ θ₁ hm
      obtain ⟨e₂, b₂, m₂, k₂⟩ := matchAll_sound ps ts θ₁ r' hr'
      refine ⟨e₁.trans e₂, ?_, ?_, fun θ'' h'' => ?_⟩
      · intro q hq v hv
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · obtain ⟨x, hx⟩ := b₁ v hv; exact ⟨x, e₂ v x hx⟩
        · exact b₂ q hq v hv
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact ht
        · exact m₂ u hu
      · simp [k₁ θ'' (e₂.trans h''), k₂ θ'' h'']

theorem matchAll_mono {ts ts' : List Pat} (hs : ∀ t ∈ ts, t ∈ ts') :
    ∀ (ps : List Pat) (θ : PSubst) (r : PSubst × List Pat),
      r ∈ matchAll ps ts θ → r ∈ matchAll ps ts' θ
  | [], θ, r, h => by simpa [matchAll] using h
  | p :: ps, θ, r, h => by
    simp only [matchAll, List.mem_flatMap] at h ⊢
    obtain ⟨t, ht, hr⟩ := h
    refine ⟨t, hs t ht, ?_⟩
    cases h₁ : matchInto p t θ with
    | none => rw [h₁] at hr; simp at hr
    | some θ₁ =>
      rw [h₁] at hr
      simp only [List.mem_map] at hr ⊢
      obtain ⟨r', hr', rfl⟩ := hr
      exact ⟨r', matchAll_mono hs ps θ₁ r' hr', rfl⟩

end Matching

end RwLog
