/-
# What `tighten` returns is tight

In a store that satisfies `Inv`, a variable takes every value of its sorts
that the exclusions do not exclude it from (`Inv.exists_sol`): the other
variables have infinitely many values, and every exclusion that is not one
of those can be avoided by changing another variable. So when no variable
has values with one root, every variable takes values with two different
roots, which is `Store.Tight` (`tight_of_sole`).
-/
import RwLog.Sorts.Loop

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-- A variable takes every value of its sorts that it is not excluded
from. -/
theorem Inv.exists_sol (hS : S.WellFormed) {s : CStore} (hI : Inv S s) (v : Nat) {t : GTerm}
    (ht : MemC S (s.conj v) t) (hg : t ∉ gone s.x v) : ∃ τ ∈ s.store.Sol S, τ v = t := by
  let extra : List Nat := s.x.flatMap fun E =>
    match solve E with
    | some θ => (θ v).vars
    | none => []
  let H : List Nat := (List.range s.c.length ++ extra).filter (· ≠ v)
  let σ₀ : Nat → GTerm := update (fun _ => .sym "") v t
  have hvH : v ∉ H := by simp [H]
  have hmemH : ∀ w, w ≠ v → (w < s.c.length ∨ w ∈ extra) → w ∈ H := by
    intro w hw h
    simp only [H, List.mem_filter, List.mem_append, List.mem_range, decide_eq_true_eq]
    exact ⟨h, hw⟩
  obtain ⟨σ, hσ, hag, -⟩ := s.store.rich (S := S) H (fun h _ => hI.infinite hS h) σ₀
    (fun w hw => by
      show MemC S (s.conj w) (σ₀ w)
      by_cases e : w = v
      · subst e; simpa [σ₀] using ht
      · have : s.c.length ≤ w := by
          by_contra hlt
          exact hw (hmemH w e (Or.inl (Nat.lt_of_not_le hlt)))
        rw [s.conj_of_ge this]; intro n hn; simp at hn)
    []
    (fun E hE => by
      cases hθ : solve E with
      | none => exact ⟨σ₀, fun _ _ => rfl, solve_none hθ σ₀⟩
      | some θ =>
        by_cases hb : ∃ w ∈ E.vars, w ≠ v ∧ θ w ≠ .var w
        · obtain ⟨w, hw, hwv, hne⟩ := hb
          obtain ⟨u, hu⟩ := falsify_bound hθ hne σ₀
          refine ⟨update σ₀ w u, fun z hz => ?_, hu⟩
          have : z ≠ w := fun e =>
            hz (e ▸ hmemH w hwv (Or.inl (hI.tv w (hI.xv E hE w hw))))
          simp [update, this]
        · push Not at hb
          have hall : E.vars.all (fun w => decide (w = v ∨ θ w = .var w)) = true := by
            rw [List.all_eq_true]
            intro w hw
            rw [decide_eq_true_eq]
            by_cases e : w = v
            · exact Or.inl e
            · exact Or.inr (hb w hw e)
          have hunit : unitOn v E = ground? (θ v) := by
            simp only [unitOn, hθ, hall, ↓reduceIte]
          have hv : θ v ≠ .var v := by
            have hopen := hI.open_ E hE
            simp only [always, hθ] at hopen
            rw [List.all_eq_false] at hopen
            obtain ⟨w, hw, hne⟩ := hopen
            rw [decide_eq_true_eq] at hne
            by_cases e : w = v
            · exact e ▸ hne
            · exact absurd (hb w hw e) hne
          cases hgr : ground? (θ v) with
          | some g =>
            rw [hgr] at hunit
            refine ⟨σ₀, fun _ _ => rfl, fun hun => hg ?_⟩
            have : σ₀ v = g := (unitOn_iff hunit σ₀).1 hun
            have e : t = g := by simpa [σ₀] using this
            rw [e]
            exact List.mem_filterMap.2 ⟨E, hE, hunit⟩
          | none =>
            obtain ⟨w, hw, hwv, hno⟩ := falsify_open hθ hv hgr σ₀
            refine ⟨_, fun z hz => ?_, hno⟩
            have hwe : w ∈ extra :=
              List.mem_flatMap.2 ⟨E, hE, by simpa only [hθ] using hw⟩
            have : z ≠ w := fun e => hz (e ▸ hmemH w hwv (Or.inr hwe))
            simp [update, this])
    (by simp)
  exact ⟨σ, hσ, by rw [hag v hvH]; simp [σ₀]⟩

/-- When no variable has values with one root, the store is tight. -/
theorem tight_of_sole (hS : S.WellFormed) {s : CStore} (hI : Inv S s)
    (hsole : ∀ v ∈ s.t.vars, sole S (s.conj v) (gone s.x v) = none) : s.store.Tight S := by
  intro v hv
  obtain ⟨σ, hσ⟩ := hI.sol hS
  obtain ⟨t₁, t₂, h₁, g₁, h₂, g₂, hne⟩ :=
    sole_none hS (hsole v hv) (hσ.1 v) (not_mem_gone hσ.2 v)
  obtain ⟨τ₁, hτ₁, e₁⟩ := hI.exists_sol hS v h₁ g₁
  obtain ⟨τ₂, hτ₂, e₂⟩ := hI.exists_sol hS v h₂ g₂
  exact ⟨τ₁, hτ₁, τ₂, hτ₂, by rw [e₁, e₂]; exact hne⟩

end Sorts
end RwLog
