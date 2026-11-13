/-
# Facts about one-way matching

`matchInto p t θ` extends the bindings `θ` so that `p` becomes `t`.

* `matchInto_bound`: when every variable of `p` is already bound, matching is
  a comparison: it succeeds, with the same bindings, exactly when `p` under
  the bindings is `t`.
* `matchInto_ext`: a successful match keeps the bindings it was given, binds
  every variable of `p`, and makes `p` equal to `t`.
-/
import RwLog.Kernel.Covers

namespace RwLogVerified

open RwLog RwLog.Term RwLog.Matching

/-- Every variable of `p` is bound. -/
def Bound (θ : PSubst) (p : Pat) : Prop := ∀ v ∈ p.vars, (θ.lookup v).isSome

theorem matchInto_bound : ∀ (p t : Pat) (θ : PSubst), Bound θ p →
    matchInto p t θ = if p.bind θ.apply = t then some θ else none := by
  intro p
  induction p with
  | var v =>
    intro t θ hb
    have h := hb v (by simp [Term.vars])
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h
    simp [matchInto, hu, PSubst.apply]
  | sym f =>
    intro t θ _
    cases t <;> simp [matchInto]
  | app p q ihp ihq =>
    intro t θ hb
    have hp : Bound θ p := fun v hv => hb v (by simp [Term.vars, hv])
    have hq : Bound θ q := fun v hv => hb v (by simp [Term.vars, hv])
    cases t with
    | var w => simp [matchInto]
    | sym g => simp [matchInto]
    | app t u =>
      simp only [matchInto, ihp t θ hp, Term.bind_app, Term.app.injEq]
      by_cases h1 : p.bind θ.apply = t
      · simp [h1, ihq u θ hq]
      · simp [h1]

/-- Later bindings that keep the earlier ones read a bound term the same. -/
theorem bound_ext {θ θ' : PSubst} {p : Pat} (hb : Bound θ p)
    (hext : ∀ v u, θ.lookup v = some u → θ'.lookup v = some u) :
    Bound θ' p ∧ p.bind θ'.apply = p.bind θ.apply := by
  refine ⟨fun v hv => ?_, Term.bind_congr fun v hv => ?_⟩
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hb v hv)
    rw [hext v u hu]; rfl
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hb v hv)
    simp [PSubst.apply, hu, hext v u hu]

theorem matchInto_ext : ∀ (p t : Pat) (θ θ' : PSubst), matchInto p t θ = some θ' →
    (∀ v u, θ.lookup v = some u → θ'.lookup v = some u) ∧ Bound θ' p ∧ p.bind θ'.apply = t := by
  intro p
  induction p with
  | var v =>
    intro t θ θ' h
    cases hl : θ.lookup v with
    | none =>
      simp only [matchInto, hl, Option.some.injEq] at h
      subst h
      refine ⟨fun w u hw => ?_, fun w hw => ?_, ?_⟩
      · have : w ≠ v := by rintro rfl; rw [hl] at hw; cases hw
        rw [lookup_cons_ne this]; exact hw
      · simp only [Term.vars, List.mem_singleton] at hw
        subst hw
        rw [lookup_cons_eq]; rfl
      · simp [PSubst.apply]
    | some u =>
      simp only [matchInto, hl] at h
      by_cases hut : u = t
      · simp only [hut, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨fun _ _ h => h, fun w hw => ?_, ?_⟩
        · simp only [Term.vars, List.mem_singleton] at hw
          subst hw
          rw [hl]; rfl
        · simp [PSubst.apply, hl, hut]
      · simp [hut] at h
  | sym f =>
    intro t θ θ' h
    cases t with
    | var w => simp [matchInto] at h
    | app a b => simp [matchInto] at h
    | sym g =>
      simp only [matchInto] at h
      by_cases hfg : f = g
      · simp only [hfg, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨fun _ _ h => h, fun w hw => by simp [Term.vars] at hw, by simp [hfg]⟩
      · simp [hfg] at h
  | app p q ihp ihq =>
    intro t θ θ' h
    cases t with
    | var w => simp [matchInto] at h
    | sym g => simp [matchInto] at h
    | app t u =>
      simp only [matchInto] at h
      cases h1 : matchInto p t θ with
      | none => simp [h1] at h
      | some θ1 =>
        simp only [h1, Option.bind_some] at h
        obtain ⟨e1, b1, r1⟩ := ihp t θ θ1 h1
        obtain ⟨e2, b2, r2⟩ := ihq u θ1 θ' h
        obtain ⟨b1', r1'⟩ := bound_ext b1 e2
        refine ⟨fun v w hv => e2 v w (e1 v w hv), fun v hv => ?_, ?_⟩
        · simp only [Term.vars, List.mem_append] at hv
          rcases hv with hv | hv
          · exact b1' v hv
          · exact b2 v hv
        · simp only [Term.bind_app, r1', r1, r2]

end RwLogVerified
