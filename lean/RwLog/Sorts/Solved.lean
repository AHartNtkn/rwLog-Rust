/-
# Every exclusion has a normal form

Take equations over the variables of a raw store that some substitution in
the sorts satisfies and some does not. Then there is a normal exclusion that
removes exactly the substitutions in the sorts that satisfy the equations
(`exists_normalBinds`).

The proof takes, among the solved exclusions that the equations imply, one
with the fewest free variables. If it removed more than the equations do, the
most general unifier of the equations under it would bind a further variable,
and if it left a variable free that the equations force to one value, that
variable could be bound to the value; either way it could be extended
(`ext`), against the choice.
-/
import RwLog.Sorts.UniqueExcl
import RwLog.Sorts.FO

namespace RwLog
namespace Sorts

open Function

/-- A solved exclusion with one more binding `x := p`, substituted into the
values of the others. -/
def ext (k : Nat) (θ : Binds) (x : Nat) (p : Pat) : Binds :=
  (List.range k).filterMap fun v =>
    if v = x then some (x, p) else (θ.lookup v).map fun q => (v, q.bind (Term.single x p))

/-- The free variables of a solved exclusion. -/
def frees (k : Nat) (θ : Binds) : Finset Nat :=
  (Finset.range k).filter fun v => ∀ b ∈ θ, b.1 ≠ v

section ext

variable {k : Nat} {θ : Binds} {x : Nat} {p : Pat}

theorem mem_ext (hθ : Pre k θ) (hx : x < k) (hfree : ∀ b ∈ θ, b.1 ≠ x) {b : Nat × Pat} :
    b ∈ ext k θ x p ↔ b = (x, p) ∨ ∃ q, (b.1, q) ∈ θ ∧ b.2 = q.bind (Term.single x p) := by
  simp only [ext, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨v, -, h⟩
    by_cases hv : v = x
    · simp only [hv, ite_true, Option.some.injEq] at h
      exact Or.inl h.symm
    · simp only [hv, ite_false, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      exact Or.inr ⟨q, mem_of_lookup hq, rfl⟩
  · rintro (rfl | ⟨q, hq, hb⟩)
    · exact ⟨x, hx, by simp⟩
    · refine ⟨b.1, hθ.dom (b.1, q) hq, ?_⟩
      have hne : b.1 ≠ x := hfree (b.1, q) hq
      have hl := lookup_of_sorted hθ.sorted _ hq
      simp only at hl
      simp only [hne, ite_false, hl, Option.map_some, Option.some.injEq]
      exact Prod.ext rfl hb.symm

theorem sorted_ext : (ext k θ x p).Pairwise fun a b => a.1 < b.1 := by
  refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
  intro v w hvw b hb b' hb'
  have e : ∀ {u : Nat} {c : Nat × Pat},
      c ∈ (if u = x then some (x, p) else (θ.lookup u).map fun q => (u, q.bind (Term.single x p))) →
      c.1 = u := by
    intro u c hc
    by_cases hu : u = x
    · simp only [hu, ite_true, Option.mem_def, Option.some.injEq] at hc
      rw [← hc, hu]
    · simp only [hu, ite_false, Option.mem_def, Option.map_eq_some_iff] at hc
      obtain ⟨q, -, rfl⟩ := hc; rfl
  rw [e hb, e hb']; exact hvw

/-- Adding a binding keeps the exclusion solved. -/
theorem pre_ext (hθ : Pre k θ) (hx : x < k) (hfree : ∀ b ∈ θ, b.1 ≠ x)
    (hfo : p.firstOrder = true)
    (hvars : ∀ v ∈ p.vars, v < k ∧ v ≠ x ∧ ∀ b ∈ θ, b.1 ≠ v)
    (hlater : ∀ y, p = .var y → y < x) : Pre k (ext k θ x p) := by
  have hm := @mem_ext k θ x p hθ hx hfree
  have hkey : ∀ b ∈ ext k θ x p, b.1 = x ∨ ∃ b₀ ∈ θ, b₀.1 = b.1 := by
    intro b hb
    rcases hm.1 hb with rfl | ⟨q, hq, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, hq, rfl⟩
  have hfree' : ∀ v, v ≠ x → (∀ b ∈ θ, b.1 ≠ v) → ∀ b ∈ ext k θ x p, b.1 ≠ v := by
    intro v hvx hv b hb e
    rcases hkey b hb with h | ⟨b₀, hb₀, h⟩
    · exact hvx (e.symm.trans h)
    · exact hv b₀ hb₀ (h.trans e)
  refine ⟨sorted_ext, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rcases hm.1 hb with rfl | ⟨q, hq, -⟩
    · exact hx
    · exact hθ.dom (b.1, q) hq
  · intro b hb
    rcases hm.1 hb with rfl | ⟨q, hq, hb2⟩
    · exact hfo
    · rw [hb2]
      refine Term.fo_bind (hθ.fo _ hq) fun v _ => ?_
      unfold Term.single; split
      · exact hfo
      · rfl
  · intro b hb v hv
    rcases hm.1 hb with rfl | ⟨q, hq, hb2⟩
    · exact ⟨(hvars v hv).1, hfree' v (hvars v hv).2.1 (hvars v hv).2.2⟩
    · rw [hb2] at hv
      rcases Term.vars_bind_single v hv with ⟨hvq, hvx⟩ | hvp
      · exact ⟨(hθ.ran _ hq v hvq).1, hfree' v hvx (hθ.ran _ hq v hvq).2⟩
      · exact ⟨(hvars v hvp).1, hfree' v (hvars v hvp).2.1 (hvars v hvp).2.2⟩
  · intro b hb y hy
    rcases hm.1 hb with rfl | ⟨q, hq, hb2⟩
    · exact hlater y hy
    · rw [hb2] at hy
      cases q with
      | var z =>
        have hz : z < b.1 := hθ.later _ hq z rfl
        by_cases hzx : z = x
        · subst hzx
          simp only [Term.bind_var, Term.single, ite_true] at hy
          have := hlater y hy
          omega
        · simp only [Term.bind_var, Term.single, hzx, ite_false, Term.var.injEq] at hy
          omega
      | sym f => simp at hy
      | app a c => simp at hy

/-- The extended exclusion asks for the old equations and the new one. -/
theorem unifies_ext (hθ : Pre k θ) (hx : x < k) (hfree : ∀ b ∈ θ, b.1 ≠ x) (σ : Nat → GTerm) :
    Eqns.Unifies σ (eqnsOf (ext k θ x p)) ↔
      Eqns.Unifies σ (eqnsOf θ) ∧ σ x = p.bind σ := by
  have hm := @mem_ext k θ x p hθ hx hfree
  constructor
  · intro hu
    have hxp : σ x = p.bind σ :=
      hu (Term.var x, p) (List.mem_map.2 ⟨(x, p), hm.2 (Or.inl rfl), rfl⟩)
    refine ⟨?_, hxp⟩
    intro e he
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    have := hu (Term.var b.1, b.2.bind (Term.single x p))
      (List.mem_map.2 ⟨(b.1, b.2.bind (Term.single x p)), hm.2 (Or.inr ⟨b.2, hb, rfl⟩), rfl⟩)
    rw [bind_single_bind hxp] at this
    exact this
  · rintro ⟨hu, hxp⟩ e he
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    rcases hm.1 hb with rfl | ⟨q, hq, hb2⟩
    · exact hxp
    · show σ b.1 = b.2.bind σ
      rw [hb2, bind_single_bind hxp]
      exact hu (Term.var b.1, q) (List.mem_map.2 ⟨(b.1, q), hq, rfl⟩)

/-- The extended exclusion has fewer free variables. -/
theorem frees_ext (hθ : Pre k θ) (hx : x < k) (hfree : ∀ b ∈ θ, b.1 ≠ x) :
    (frees k (ext k θ x p)).card < (frees k θ).card := by
  have hm := @mem_ext k θ x p hθ hx hfree
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, hfree⟩, ?_⟩
    simp only [frees, Finset.mem_filter, Finset.mem_range, not_and, not_forall]
    intro _
    exact ⟨(x, p), hm.2 (Or.inl rfl), fun h => h rfl⟩
  · intro v hv
    simp only [frees, Finset.mem_filter, Finset.mem_range] at hv ⊢
    refine ⟨hv.1, fun b hb e => ?_⟩
    exact hv.2 (b.1, b.2.bind (Term.single x p)) (hm.2 (Or.inr ⟨b.2, hb, rfl⟩)) e

end ext

/-- Equations under a substitution of patterns. -/
def trEqns (θ : Binds) (E : Eqns Nat) : Eqns Nat :=
  E.map fun p => (p.1.bind (PSubst.apply θ), p.2.bind (PSubst.apply θ))

theorem unifies_trEqns (θ : Binds) (E : Eqns Nat) (τ : Nat → GTerm) :
    Eqns.Unifies τ (trEqns θ E) ↔ Eqns.Unifies (fun v => (PSubst.apply θ v).bind τ) E := by
  simp only [Eqns.Unifies, trEqns, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h p hp
    have := h _ p hp rfl
    simpa [Term.bind_bind] using this
  · rintro h _ p hp rfl
    have := h p hp
    simpa [Term.bind_bind] using this

/-- Equations over the variables of a raw store that some substitution in the
sorts satisfies and some does not have a normal exclusion: it removes exactly
the substitutions in the sorts that satisfy them. -/
theorem exists_normalBinds {S : Sorts} (r : Raw) (E : Eqns Nat) (hE : E.FO)
    (hEv : ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, v < r.c.length)
    (hsat : ∃ σ ∈ r.store.Pos S, Eqns.Unifies σ E)
    (hprop : ∃ σ ∈ r.store.Pos S, ¬ Eqns.Unifies σ E) :
    ∃ θ, NormalBinds S r θ ∧ r.Ex S θ = {σ | σ ∈ r.store.Pos S ∧ Eqns.Unifies σ E} := by
  classical
  let Q : Binds → Prop := fun θ =>
    Pre r.c.length θ ∧ ∀ σ ∈ r.store.Pos S, Eqns.Unifies σ E → Eqns.Unifies σ (eqnsOf θ)
  have hQ0 : Q [] :=
    ⟨⟨List.Pairwise.nil, by simp, by simp, by simp, by simp⟩,
      fun σ _ _ p hp => by simp [eqnsOf] at hp⟩
  have hex : ∃ m, ∃ θ, Q θ ∧ (frees r.c.length θ).card = m := ⟨_, [], hQ0, rfl⟩
  obtain ⟨θ, hθQ, hθm⟩ := Nat.find_spec hex
  have hmin : ∀ θ', Q θ' → (frees r.c.length θ).card ≤ (frees r.c.length θ').card := by
    intro θ' h'; rw [hθm]; exact Nat.find_min' hex ⟨θ', h', rfl⟩
  obtain ⟨hpre, himp⟩ := hθQ
  have hF := unifies_eqnsOf hpre.sorted
  -- the exclusion cannot be extended by a binding the equations imply
  have noext : ∀ (x : Nat) (p : Pat), x < r.c.length → (∀ b ∈ θ, b.1 ≠ x) →
      p.firstOrder = true → (∀ v ∈ p.vars, v < r.c.length ∧ v ≠ x ∧ ∀ b ∈ θ, b.1 ≠ v) →
      (∀ y, p = .var y → y < x) →
      (∀ σ ∈ r.store.Pos S, Eqns.Unifies σ E → σ x = p.bind σ) → False := by
    intro x p hx hfree hfo hvars hlater himp'
    have h₁ := hmin (ext r.c.length θ x p) ⟨pre_ext hpre hx hfree hfo hvars hlater,
      fun σ hσ hu => (unifies_ext hpre hx hfree σ).2 ⟨himp σ hσ hu, himp' σ hσ hu⟩⟩
    have h₂ := frees_ext (p := p) hpre hx hfree
    omega
  obtain ⟨σ₀, hσ₀, hu₀⟩ := hsat
  have claim1 : ∀ σ ∈ r.store.Pos S, Eqns.Unifies σ (eqnsOf θ) → Eqns.Unifies σ E := by
    intro σ₁ hσ₁ hu₁
    by_contra hnot
    have htr : ∀ σ : Nat → GTerm, Eqns.Unifies σ (eqnsOf θ) →
        (Eqns.Unifies σ (trEqns θ E) ↔ Eqns.Unifies σ E) := by
      intro σ h
      have hfix : (fun v => (PSubst.apply θ v).bind σ) = σ :=
        funext fun v => ((hF σ).1 h v).symm
      rw [unifies_trEqns, hfix]
    have hu₀' : Eqns.Unifies σ₀ (trEqns θ E) := (htr σ₀ (himp σ₀ hσ₀ hu₀)).2 hu₀
    have hE' : (trEqns θ E).FO := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨Term.fo_bind (hE q hq).1 fun v _ => hpre.apply_fo v,
        Term.fo_bind (hE q hq).2 fun v _ => hpre.apply_fo v⟩
    have hvE : ∀ p ∈ trEqns θ E, ∀ v ∈ p.1.vars ++ p.2.vars,
        v < r.c.length ∧ ∀ b ∈ θ, b.1 ≠ v := by
      intro p hp v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      rcases List.mem_append.1 hv with hv | hv
      · obtain ⟨z, hz, hvz⟩ := Term.vars_bind_mem hv
        exact ⟨hpre.apply_lt (hEv q hq z (List.mem_append_left _ hz)) v hvz,
          hpre.apply_free z v hvz⟩
      · obtain ⟨z, hz, hvz⟩ := Term.vars_bind_mem hv
        exact ⟨hpre.apply_lt (hEv q hq z (List.mem_append_right _ hz)) v hvz,
          hpre.apply_free z v hvz⟩
    cases hsol : solve (trEqns θ E) with
    | none => exact solve_none hsol σ₀ hu₀'
    | some μ =>
      obtain ⟨hμu, hμg⟩ := solve_some hsol
      have hmoved : ∃ p ∈ trEqns θ E, ∃ y ∈ p.1.vars ++ p.2.vars, μ y ≠ .var y := by
        by_contra hno
        have hno' : ∀ p ∈ trEqns θ E, ∀ y ∈ p.1.vars ++ p.2.vars, μ y = .var y := by
          intro p hp y hy
          by_contra h
          exact hno ⟨p, hp, y, hy, h⟩
        apply hnot
        rw [← htr σ₁ hu₁]
        intro p hp
        have e₁ : p.1.bind μ = p.1 := by
          conv_rhs => rw [← Term.bind_var_id p.1]
          exact Term.bind_congr fun v hv => hno' p hp v (List.mem_append_left _ hv)
        have e₂ : p.2.bind μ = p.2 := by
          conv_rhs => rw [← Term.bind_var_id p.2]
          exact Term.bind_congr fun v hv => hno' p hp v (List.mem_append_right _ hv)
        have := hμu p hp
        rw [e₁, e₂] at this
        rw [this]
      obtain ⟨p₀, hp₀, y, hy, hmy⟩ := hmoved
      have hyk := (hvE p₀ hp₀ y hy).1
      have hyfree := (hvE p₀ hp₀ y hy).2
      have hq_eq : ∀ τ : Nat → GTerm, Eqns.Unifies τ (trEqns θ E) → τ y = (μ y).bind τ :=
        fun τ h => (hμg τ h y).symm
      have hidem : (μ y).bind μ = μ y := hμg μ hμu y
      have hy_notin : y ∉ (μ y).vars := by
        intro hyin
        by_cases hvar : ∃ w, μ y = .var w
        · obtain ⟨w, hw⟩ := hvar
          rw [hw] at hyin
          simp only [Term.vars, List.mem_singleton] at hyin
          subst hyin; exact hmy hw
        · exact Term.occurs_ne μ hyin (fun w hw => hvar ⟨w, hw⟩) hidem.symm
      have hq_vars : ∀ w ∈ (μ y).vars, w < r.c.length ∧ w ≠ y ∧ ∀ b ∈ θ, b.1 ≠ w := by
        intro w hw
        have hwy : w ≠ y := fun e => hy_notin (e ▸ hw)
        have hwE : ∃ p ∈ trEqns θ E, w ∈ p.1.vars ++ p.2.vars := by
          by_contra hno
          obtain ⟨g', hg'⟩ := exists_ne (σ₀ w)
          have hu' : Eqns.Unifies (update σ₀ w g') (trEqns θ E) :=
            unifies_congr (fun p hp v hv => by
              have : v ≠ w := fun e => hno ⟨p, hp, e ▸ hv⟩
              simp [update, this]) hu₀'
          have h₁ := hq_eq _ hu'
          have h₂ := hq_eq _ hu₀'
          have hyw : update σ₀ w g' y = σ₀ y := by simp [update, hwy.symm]
          have e : (μ y).bind (update σ₀ w g') = (μ y).bind σ₀ := by rw [← h₁, ← h₂, hyw]
          have := bind_agree e w hw
          simp only [update_self] at this
          exact hg' this
        obtain ⟨p, hp, hwp⟩ := hwE
        exact ⟨(hvE p hp w hwp).1, hwy, (hvE p hp w hwp).2⟩
      have hq_fo : (μ y).firstOrder = true := solve_fo _ hE' μ hsol y
      by_cases hsw : ∃ w, μ y = .var w ∧ y < w
      · obtain ⟨w, hw, hyw⟩ := hsw
        have hwv := hq_vars w (by rw [hw]; simp [Term.vars])
        refine noext w (.var y) hwv.1 hwv.2.2 rfl ?_ ?_ ?_
        · intro v hv
          simp only [Term.vars, List.mem_singleton] at hv
          subst hv; exact ⟨hyk, Nat.ne_of_lt hyw, hyfree⟩
        · intro y' hy'
          simp only [Term.var.injEq] at hy'
          omega
        · intro σ hσ hu
          have := hq_eq σ ((htr σ (himp σ hσ hu)).2 hu)
          rw [hw] at this
          simpa using this.symm
      · refine noext y (μ y) hyk hyfree hq_fo hq_vars ?_ ?_
        · intro w hw
          have hwv := hq_vars w (by rw [hw]; simp [Term.vars])
          by_contra hlt
          exact hsw ⟨w, hw, by have := hwv.2.1; omega⟩
        · intro σ hσ hu
          exact hq_eq σ ((htr σ (himp σ hσ hu)).2 hu)
  have hEx : r.Ex S θ = {σ | σ ∈ r.store.Pos S ∧ Eqns.Unifies σ E} := by
    ext σ
    exact ⟨fun h => ⟨h.1, claim1 σ h.1 h.2⟩, fun h => ⟨h.1, himp σ h.1 h.2⟩⟩
  refine ⟨θ, ⟨hpre, ?_, ⟨σ₀, hσ₀, himp σ₀ hσ₀ hu₀⟩, ?_⟩, hEx⟩
  · rintro rfl
    obtain ⟨σ₁, hσ₁, hn⟩ := hprop
    exact hn (claim1 σ₁ hσ₁ fun p hp => by simp [eqnsOf] at hp)
  · intro y hy hfree
    by_contra hno
    have hconst : ∀ σ ∈ r.Ex S θ, σ y = σ₀ y := by
      intro σ hσ
      by_contra hne
      exact hno ⟨σ, hσ, σ₀, ⟨hσ₀, himp σ₀ hσ₀ hu₀⟩, hne⟩
    refine noext y (Term.lift (σ₀ y)) hy hfree (Term.lift_fo _) (by simp [Term.lift_vars]) ?_ ?_
    · intro w hw
      have := Term.lift_vars (σ₀ y)
      rw [hw] at this
      simp [Term.vars] at this
    · intro σ hσ hu
      rw [Term.lift_bind]
      exact hconst σ ⟨hσ, himp σ hσ hu⟩

end Sorts
end RwLog
