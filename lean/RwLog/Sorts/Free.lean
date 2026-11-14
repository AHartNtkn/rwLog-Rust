/-
# Free subterms, decided

Whether a subterm of a store is free (`Free`, `Fold.lean`) is decided on the
store, without unfolding it. This file has the two facts the decision rests
on, for a store determined by its pattern and what it denotes in which every
variable has infinitely many values in its sorts (`Raw.Roomy`):

* the variables of a free subterm take their values freely among their sorts
  (`Free.vary`);
* no exclusion mentions a variable of a free subterm (`Free.not_excl`).
-/
import RwLog.Sorts.Fold

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts} {r : Raw}

/-- Two substitutions that give a term the same instance agree on its
variables. -/
theorem Term.eq_of_bind_eq {t : Pat} {σ τ : Nat → GTerm} (h : t.bind σ = t.bind τ) :
    ∀ v ∈ t.vars, σ v = τ v := by
  induction t with
  | var x =>
    intro v hv
    simp only [Term.vars, List.mem_singleton] at hv
    subst hv
    exact h
  | sym f => intro v hv; simp [Term.vars] at hv
  | app a b iha ihb =>
    simp only [Term.bind, Term.app.injEq] at h
    intro v hv
    simp only [Term.vars, List.mem_append] at hv
    rcases hv with hv | hv
    · exact iha h.1 v hv
    · exact ihb h.2 v hv

/-- What the fold is computed on: a store determined by its pattern and what
it denotes, with a solution, in which every variable has infinitely many
values in its sorts. -/
structure Raw.Roomy (S : Sorts) (r : Raw) : Prop where
  shaped : r.Shaped S
  sol : (r.store.Sol S).Nonempty
  inf : ∀ v, v < r.c.length → {g | MemC S (r.conj v) g}.Infinite

/-- The variables of a free subterm take their values freely among their
sorts: a solution changed on them to other values of their sorts is a
solution. -/
theorem Free.vary (hr : r.Shaped S) {u : Pat} (hfo : u.firstOrder = true)
    (huv : ∀ y ∈ u.vars, y < r.c.length) (hf : Free S r.store u) {σ σ₁ : Nat → GTerm}
    (hσ : σ ∈ r.store.Sol S) (hout : ∀ y, y ∉ u.vars → σ₁ y = σ y)
    (hin : ∀ y ∈ u.vars, MemC S (r.conj y) (σ₁ y)) : σ₁ ∈ r.store.Sol S := by
  obtain ⟨C, hC₁, hC₂⟩ := hf.sem
  have hmem : MemC S C (u.bind σ₁) := by
    intro n hn
    have hσn := hC₁ σ hσ n hn
    cases hp : push S n u with
    | none =>
      have := push_none hfo hp σ
      rw [hσn] at this
      cases this
    | some as =>
      refine (push_some hfo hp σ₁).2 fun a ha => ?_
      have hall : ∀ σ' ∈ r.store.Sol S, mem S a.2 (σ' a.1) = true :=
        fun σ' hσ' => (push_some hfo hp σ').1 (hC₁ σ' hσ' n hn) a ha
      by_cases hy : a.1 ∈ u.vars
      · refine hin a.1 hy a.2 ((hr.up a.1 (huv _ hy) a.2).2 ⟨?_, hall⟩)
        by_contra hn'
        have := mem_false_of_not_names hn' (σ a.1)
        rw [hall σ hσ] at this
        cases this
      · rw [hout a.1 hy]
        exact hall σ hσ
  obtain ⟨σ', hσ', e, hag⟩ := hC₂ σ hσ _ hmem
  refine hr.sol_congr (fun v hv => ?_) hσ'
  by_cases hy : v ∈ u.vars
  · exact (Term.eq_of_bind_eq e v hy).symm
  · rw [hout v hy]
    exact (hag v ((hr.len v).2 hv) hy).symm

/-- No exclusion mentions a variable of a free subterm. -/
theorem Free.not_excl (hS : S.WellFormed) (hR : r.Roomy S) {u : Pat} (hfo : u.firstOrder = true)
    (huv : ∀ y ∈ u.vars, y < r.c.length) (hf : Free S r.store u) :
    ∀ θ ∈ r.x, ∀ y ∈ u.vars, y ∉ (eqnsOf θ).vars := by
  intro θ hθ y₀ hy₀ hmem
  have hr := hR.shaped
  have hN := hr.ex θ hθ
  -- a substitution the exclusion removes and no other exclusion does
  have hstar : ∃ σs ∈ r.Ex S θ, ∀ θ₂ ∈ r.x, θ₂ ≠ θ → ¬ Eqns.Unifies σs (eqnsOf θ₂) := by
    by_contra hno
    push Not at hno
    obtain ⟨θ₂, hθ₂, hsub⟩ := hN.irreducible hS (r.x.erase θ).toList
      (fun θ₂ h => hr.ex θ₂ (Finset.mem_of_mem_erase (Finset.mem_toList.1 h)))
      (fun σ hσ => by
        obtain ⟨θ₂, h1, h2, h3⟩ := hno σ hσ
        exact ⟨θ₂, Finset.mem_toList.2 (Finset.mem_erase.2 ⟨h2, h1⟩), h3⟩)
    have hm := Finset.mem_erase.1 (Finset.mem_toList.1 hθ₂)
    exact hm.1 (hr.anti θ hθ θ₂ hm.2 hsub).symm
  obtain ⟨σs, hσs, hoth⟩ := hstar
  -- changed at the variable, it is a solution
  obtain ⟨τ, hτ, hag, -⟩ := r.store.rich (S := S) [y₀]
    (fun h hh => by
      rw [List.mem_singleton.1 hh]
      exact hR.inf y₀ (huv y₀ hy₀))
    σs (fun v _ => hσs.1 v) []
    (by
      intro E hE
      obtain ⟨θ₂, hθ₂, rfl⟩ := Raw.mem_store_x.1 hE
      by_cases e : θ₂ = θ
      · subst e
        obtain ⟨g', hg'⟩ := exists_ne (σs y₀)
        refine ⟨update σs y₀ g', fun v hv => update_of_ne (by simpa using hv) _ _, fun hu => ?_⟩
        obtain ⟨p, hp, hv⟩ := List.mem_flatMap.1 hmem
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
        have h1 := hu _ (List.mem_map_of_mem hb)
        have h2 := hσs.2 _ (List.mem_map_of_mem hb)
        simp only [Term.bind] at h1 h2
        simp only [Term.vars, List.cons_append, List.nil_append, List.mem_cons] at hv
        rcases hv with rfl | hv
        · have hnot : b.1 ∉ b.2.vars := fun hc => (hN.ran b hb _ hc).2 b hb rfl
          rw [update_self, bind_update_of_not_mem hnot, ← h2] at h1
          exact hg' h1
        · have hne : b.1 ≠ y₀ := (hN.ran b hb _ hv).2 b hb
          rw [update_of_ne hne, h2] at h1
          have := Term.eq_of_bind_eq h1 y₀ hv
          rw [update_self] at this
          exact hg' this.symm
      · exact ⟨σs, fun _ _ => rfl, hoth θ₂ hθ₂ e⟩)
    (by simp)
  have hσs' : σs ∈ r.store.Sol S :=
    hf.vary hr hfo huv hτ
      (fun y hy => (hag y (by simpa using fun e : y = y₀ => hy (e ▸ hy₀))).symm)
      (fun y _ => hσs.1 y)
  exact hσs'.2 _ (Raw.mem_store_x.2 ⟨θ, hθ, rfl⟩) hσs.2

end Sorts
end RwLog
