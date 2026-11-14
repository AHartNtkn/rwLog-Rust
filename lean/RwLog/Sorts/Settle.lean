/-
# Variables with one value

A variable whose sorts have one member is replaced by that member, and the
store denotes what it did (`setStore_den`).
-/
import RwLog.Sorts.Gone
import RwLog.Trusted.Cost

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

theorem toPat_bind (g : GTerm) (σ : Nat → GTerm) : (GTerm.toPat g).bind σ = g := by
  induction g with
  | var v => exact v.elim
  | sym f => rfl
  | app a b iha ihb =>
    simp only [GTerm.toPat, Term.rename, Term.bind] at iha ihb ⊢
    rw [iha, ihb]

/-- The store with the variable `v` replaced by the ground term `g`. -/
def setStore (s : Store) (v : Nat) (g : GTerm) : Store :=
  ⟨s.t.bind (Term.single v (GTerm.toPat g)), fun w => if w = v then ∅ else s.c w,
    s.x.map (Eqns.subst v (GTerm.toPat g))⟩

/-- A variable whose sorts have one member is replaced by it. -/
theorem setStore_den {s : Store} {v : Nat} {g : GTerm} (h₁ : MemC S (s.c v) g)
    (h₂ : ∀ u, MemC S (s.c v) u → u = g) : (setStore s v g).Den S = s.Den S := by
  have hb : ∀ (τ : Nat → GTerm) (q : Pat),
      q.bind (fun w => (Term.single v (GTerm.toPat g) w).bind τ) =
        (q.bind (Term.single v (GTerm.toPat g))).bind τ :=
    fun τ q => (Term.bind_bind _ _ q).symm
  have hv : ∀ τ : Nat → GTerm, (Term.single v (GTerm.toPat g) v).bind τ = g := by
    intro τ; simp [Term.single, toPat_bind]
  have hw : ∀ (τ : Nat → GTerm) w, w ≠ v → (Term.single v (GTerm.toPat g) w).bind τ = τ w := by
    intro τ w hw; simp [Term.single, hw]
  ext t
  constructor
  · rintro ⟨σ', hσ', rfl⟩
    refine ⟨fun w => (Term.single v (GTerm.toPat g) w).bind σ', ⟨?_, ?_⟩, (hb σ' s.t).symm⟩
    · intro w
      by_cases e : w = v
      · subst e
        show MemC S (s.c w) ((Term.single w (GTerm.toPat g) w).bind σ')
        rw [hv]; exact h₁
      · show MemC S (s.c w) ((Term.single v (GTerm.toPat g) w).bind σ')
        rw [hw σ' w e]
        have := hσ'.1 w
        simpa [setStore, e] using this
    · intro E hE hu
      refine hσ'.2 _ (List.mem_map.2 ⟨E, hE, rfl⟩) ?_
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      show (q.1.bind _).bind σ' = (q.2.bind _).bind σ'
      rw [← hb, ← hb]; exact hu q hq
  · rintro ⟨σ, hσ, rfl⟩
    have hσv : σ v = g := h₂ _ (hσ.1 v)
    have e : (fun w => (Term.single v (GTerm.toPat g) w).bind σ) = σ := by
      funext w
      by_cases e : w = v
      · subst e; rw [hv, hσv]
      · exact hw σ w e
    refine ⟨σ, ⟨?_, ?_⟩, ?_⟩
    · intro w
      show MemC S (if w = v then ∅ else s.c w) (σ w)
      by_cases e : w = v
      · simp only [e, ↓reduceIte]; intro m hm; simp at hm
      · simp only [e, ↓reduceIte]; exact hσ.1 w
    · intro E' hE' hu
      obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
      refine hσ.2 E hE ?_
      intro q hq
      have := hu _ (List.mem_map.2 ⟨q, hq, rfl⟩)
      change (q.1.bind _).bind σ = (q.2.bind _).bind σ at this
      rwa [← hb, ← hb, e] at this
    · show s.t.bind σ = (s.t.bind _).bind σ
      rw [← hb, e]

end Sorts
end RwLog
