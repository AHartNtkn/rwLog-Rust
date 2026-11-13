/-
# Disequations are independent over infinite sets

An equation between two terms, read as a condition on the value of one
variable with all the others fixed, holds for every value, for no value, or
for exactly one (`eq_one_var`). So a disequation that can be satisfied at all
forbids at most one value of that variable.

`avoid` is the consequence the constraint domain rests on. Take finitely many
disequations and a list of variables each ranging over an infinite set. If
every disequation can be satisfied by some choice of those variables, then one
choice, inside the sets, satisfies them all. This is why a store with sorts
that all have infinitely many members is alive as soon as each disequation is
separately satisfiable, and why a variable that occurs in neither side of a
span can be forgotten together with every disequation that mentions it.
-/
import RwLog.Trusted.Syntax
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Logic.Function.Basic

namespace RwLog
namespace Sorts

open Function

/-- Changing the value of a variable that does not occur changes nothing. -/
theorem bind_update_of_not_mem {t : Pat} {σ : Nat → GTerm} {h : Nat} (hh : h ∉ t.vars)
    (u : GTerm) : t.bind (update σ h u) = t.bind σ := by
  apply Term.bind_congr
  intro v hv
  have : v ≠ h := fun e => hh (e ▸ hv)
  simp [update, this]

/-- A term that contains `h` and is not `h` is larger than the value of `h`. -/
theorem size_lt_bind_update {t : Pat} {σ : Nat → GTerm} {h : Nat} (hh : h ∈ t.vars)
    (hne : t ≠ .var h) (u : GTerm) : u.size < (t.bind (update σ h u)).size := by
  induction t with
  | var v =>
    simp only [Term.vars, List.mem_singleton] at hh
    subst hh; exact absurd rfl hne
  | sym f => simp [Term.vars] at hh
  | app a b iha ihb =>
    simp only [Term.vars, List.mem_append] at hh
    simp only [Term.bind_app, Term.size]
    rcases hh with hh | hh
    · by_cases e : a = .var h
      · subst e; simp [update]; omega
      · have := iha hh e; omega
    · by_cases e : b = .var h
      · subst e; simp [update]; omega
      · have := ihb hh e; omega

/-- With every variable but `h` fixed, an equation between two terms holds for
every value of `h` or for at most one. -/
theorem eq_one_var (σ : Nat → GTerm) (h : Nat) : ∀ s t : Pat,
    (∀ u, s.bind (update σ h u) = t.bind (update σ h u)) ∨
      ∀ u₁ u₂, s.bind (update σ h u₁) = t.bind (update σ h u₁) →
        s.bind (update σ h u₂) = t.bind (update σ h u₂) → u₁ = u₂ := by
  -- one side does not contain `h`
  have const : ∀ (g : GTerm) (t : Pat),
      (∀ u, t.bind (update σ h u) = g) ∨
        ∀ u₁ u₂, t.bind (update σ h u₁) = g → t.bind (update σ h u₂) = g → u₁ = u₂ := by
    intro g t
    induction t generalizing g with
    | var v =>
      by_cases e : v = h
      · subst e; right; intro u₁ u₂ h1 h2; simp [update] at h1 h2; rw [h1, h2]
      · by_cases e' : σ v = g
        · left; intro u; simp [update, e, e']
        · right; intro u₁ _ h1 _; simp [update, e] at h1; exact absurd h1 e'
    | sym f =>
      by_cases e : (Term.sym f : GTerm) = g
      · left; intro u; simpa using e
      · right; intro u₁ _ h1 _; simp at h1; exact absurd h1 e
    | app a b iha ihb =>
      cases g with
      | var v => exact v.elim
      | sym f => right; intro u₁ _ h1 _; simp at h1
      | app g₁ g₂ =>
        rcases iha g₁ with ha | ha
        · rcases ihb g₂ with hb | hb
          · left; intro u; simp [ha u, hb u]
          · right; intro u₁ u₂ h1 h2
            simp only [Term.bind_app, Term.app.injEq] at h1 h2
            exact hb u₁ u₂ h1.2 h2.2
        · right; intro u₁ u₂ h1 h2
          simp only [Term.bind_app, Term.app.injEq] at h1 h2
          exact ha u₁ u₂ h1.1 h2.1
  -- one side is `h` itself
  have self : ∀ t : Pat,
      (∀ u, u = t.bind (update σ h u)) ∨
        ∀ u₁ u₂, u₁ = t.bind (update σ h u₁) → u₂ = t.bind (update σ h u₂) → u₁ = u₂ := by
    intro t
    by_cases e : t = .var h
    · subst e; left; intro u; simp [update]
    · right
      by_cases hh : h ∈ t.vars
      · intro u₁ _ h1 _
        have := size_lt_bind_update (σ := σ) hh e u₁
        rw [← h1] at this; omega
      · intro u₁ u₂ h1 h2
        rw [bind_update_of_not_mem hh] at h1 h2
        rw [h1, h2]
  intro s
  induction s with
  | var v =>
    intro t
    by_cases e : v = h
    · subst e
      rcases self t with ht | ht
      · left; intro u; simpa [update] using ht u
      · right; intro u₁ u₂ h1 h2
        exact ht u₁ u₂ (by simpa [update] using h1) (by simpa [update] using h2)
    · rcases const (σ v) t with ht | ht
      · left; intro u; simp [update, e, ht u]
      · right; intro u₁ u₂ h1 h2
        simp only [Term.bind_var, update, e, dite_false] at h1 h2
        exact ht u₁ u₂ h1.symm h2.symm
  | sym f =>
    intro t
    rcases const (.sym f) t with ht | ht
    · left; intro u; simp [ht u]
    · right; intro u₁ u₂ h1 h2
      exact ht u₁ u₂ (by simpa using h1.symm) (by simpa using h2.symm)
  | app a b iha ihb =>
    intro t
    cases t with
    | var v =>
      by_cases e : v = h
      · subst e
        rcases self (.app a b) with ht | ht
        · left; intro u; simpa [update] using (ht u).symm
        · right; intro u₁ u₂ h1 h2
          exact ht u₁ u₂ (by simpa [update] using h1.symm) (by simpa [update] using h2.symm)
      · rcases const (σ v) (.app a b) with ht | ht
        · left; intro u; simpa [update, e] using ht u
        · right; intro u₁ u₂ h1 h2
          exact ht u₁ u₂ (by simpa [update, e] using h1) (by simpa [update, e] using h2)
    | sym f => right; intro u₁ _ h1 _; simp at h1
    | app c d =>
      rcases iha c with ha | ha
      · rcases ihb d with hb | hb
        · left; intro u; simp [ha u, hb u]
        · right; intro u₁ u₂ h1 h2
          simp only [Term.bind_app, Term.app.injEq] at h1 h2
          exact hb u₁ u₂ h1.2 h2.2
      · right; intro u₁ u₂ h1 h2
        simp only [Term.bind_app, Term.app.injEq] at h1 h2
        exact ha u₁ u₂ h1.1 h2.1

/-- Finitely many disequations, each satisfiable by some choice of the
variables `H`, are satisfied together by one choice that takes every variable
of `H` from its infinite set. -/
theorem avoid (A : Nat → Set GTerm) : ∀ (H : List Nat), (∀ h ∈ H, (A h).Infinite) →
    ∀ (D : List (Pat × Pat)) (σ : Nat → GTerm),
      (∀ p ∈ D, ∃ τ : Nat → GTerm, (∀ v, v ∉ H → τ v = σ v) ∧ p.1.bind τ ≠ p.2.bind τ) →
      ∃ τ : Nat → GTerm, (∀ v, v ∉ H → τ v = σ v) ∧ (∀ h ∈ H, τ h ∈ A h) ∧
        ∀ p ∈ D, p.1.bind τ ≠ p.2.bind τ
  | [], _, D, σ, hD => by
    refine ⟨σ, fun _ _ => rfl, by simp, fun p hp => ?_⟩
    obtain ⟨τ, hτ, hne⟩ := hD p hp
    have : τ = σ := funext fun v => hτ v (by simp)
    exact this ▸ hne
  | h :: H, hA, D, σ, hD => by
    have : Nonempty (Nat → GTerm) := ⟨σ⟩
    choose! w hw using hD
    -- the values of `h` that make some disequation unsatisfiable afterwards
    let B : Set GTerm := ⋃ p ∈ {p | p ∈ D},
      {u | p.1.bind (update (w p) h u) = p.2.bind (update (w p) h u)}
    have hB : B.Finite := by
      apply Set.Finite.biUnion (List.finite_toSet D)
      intro p hp
      apply Set.Subsingleton.finite
      intro u₁ h1 u₂ h2
      rcases eq_one_var (w p) h p.1 p.2 with hall | hone
      · exfalso
        have := hall (w p h)
        rw [update_eq_self] at this
        exact (hw p hp).2 this
      · exact hone u₁ u₂ h1 h2
    obtain ⟨u, huA, huB⟩ := ((hA h (by simp)).sdiff hB).nonempty
    have ih := avoid A H (fun k hk => hA k (List.mem_cons_of_mem _ hk)) D (update σ h u)
      (fun p hp => by
        refine ⟨update (w p) h u, fun v hv => ?_, ?_⟩
        · by_cases e : v = h
          · subst e; simp
          · simp only [update, e, dite_false]
            exact (hw p hp).1 v (by simp [e, hv])
        · intro heq
          apply huB
          simp only [B, Set.mem_iUnion, Set.mem_ofPred_eq]
          exact ⟨p, hp, heq⟩)
    obtain ⟨τ, hτ, hτA, hτD⟩ := ih
    refine ⟨τ, fun v hv => ?_, fun k hk => ?_, hτD⟩
    · simp only [List.mem_cons, not_or] at hv
      rw [hτ v hv.2]; simp [update, hv.1]
    · by_cases hkH : k ∈ H
      · exact hτA k hkH
      · have : k = h := by
          rcases List.mem_cons.mp hk with e | e
          · exact e
          · exact absurd e hkH
        subst this
        rw [hτ k hkH]; simpa using huA

end Sorts
end RwLog
