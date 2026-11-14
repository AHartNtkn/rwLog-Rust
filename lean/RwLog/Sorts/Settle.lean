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

theorem toPat_vars (g : GTerm) : (GTerm.toPat g).vars = [] := by
  induction g with
  | var v => exact v.elim
  | sym f => rfl
  | app a b iha ihb =>
    simp only [GTerm.toPat, Term.rename, Term.bind, Term.vars] at iha ihb ⊢
    rw [iha, ihb]; rfl

theorem toPat_fo (g : GTerm) : (GTerm.toPat g).firstOrder = true := by
  induction g with
  | var v => exact v.elim
  | sym f => rfl
  | app a b iha ihb =>
    cases a with
    | var v => exact v.elim
    | sym f =>
      simp only [GTerm.toPat, Term.rename, Term.bind, Term.firstOrder] at ihb ⊢
      simpa using ihb
    | app a₁ a₂ =>
      simp only [GTerm.toPat, Term.rename, Term.bind, Term.firstOrder] at iha ihb ⊢
      simp [iha, ihb]

section

variable {s : Store} {N v : Nat} {g : GTerm}

theorem setStore_fin (hfin : s.Fin N) : (setStore s v g).Fin N := by
  have hsfo : ∀ w, (Term.single v (GTerm.toPat g) w).firstOrder = true := by
    intro w; unfold Term.single; split
    · exact toPat_fo g
    · rfl
  have h₀ : ∀ (u : Pat) (w : Nat), (∀ z ∈ u.vars, z < N) →
      w ∈ (u.bind (Term.single v (GTerm.toPat g))).vars → w < N := by
    intro u w hu hwu
    rcases Term.vars_bind_single w hwu with ⟨hw', -⟩ | hw'
    · exact hu w hw'
    · rw [toPat_vars] at hw'; cases hw'
  refine ⟨Term.fo_bind hfin.fo fun w _ => hsfo w, fun w hw => h₀ s.t w hfin.tv hw, ?_, ?_, ?_⟩
  · intro w hw
    show (if w = v then ∅ else s.c w) = ∅
    split
    · rfl
    · exact hfin.cv w hw
  · intro E' hE'
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    exact Eqns.fo_subst (hfin.xfo E hE) (toPat_fo g)
  · intro E' hE' p hp w hw
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    rcases List.mem_append.1 hw with hw | hw
    · exact h₀ q.1 w (fun z hz => hfin.xv E hE q hq z (List.mem_append_left _ hz)) hw
    · exact h₀ q.2 w (fun z hz => hfin.xv E hE q hq z (List.mem_append_right _ hz)) hw

theorem setStore_full (hfull : s.Full) : (setStore s v g).Full := by
  have hkeep : ∀ w, w ∈ s.t.vars → w ≠ v →
      w ∈ (s.t.bind (Term.single v (GTerm.toPat g))).vars := by
    intro w hw hwv
    exact Term.vars_sub_bind hw w (by simp [Term.single, hwv, Term.vars])
  have h₀ : ∀ (u : Pat) (w : Nat), (∀ z ∈ u.vars, z ∈ s.t.vars) →
      w ∈ (u.bind (Term.single v (GTerm.toPat g))).vars →
      w ∈ (s.t.bind (Term.single v (GTerm.toPat g))).vars := by
    intro u w hu hwu
    rcases Term.vars_bind_single w hwu with ⟨hw', hwv⟩ | hw'
    · exact hkeep w (hu w hw') hwv
    · rw [toPat_vars] at hw'; cases hw'
  refine ⟨?_, ?_⟩
  · intro w hw
    show (if w = v then ∅ else s.c w) = ∅
    split
    · rfl
    · rename_i hwv
      exact hfull.cs w fun hwt => hw (hkeep w hwt hwv)
  · intro E' hE' p hp w hw
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    rcases List.mem_append.1 hw with hw | hw
    · exact h₀ q.1 w (fun z hz => hfull.xs E hE q hq z (List.mem_append_left _ hz)) hw
    · exact h₀ q.2 w (fun z hz => hfull.xs E hE q hq z (List.mem_append_right _ hz)) hw

/-- The variable replaced is no longer in the pattern. -/
theorem setStore_not_mem : v ∉ (setStore s v g).t.vars := by
  intro h
  rcases Term.vars_bind_single v h with ⟨-, h'⟩ | h'
  · exact h' rfl
  · rw [toPat_vars] at h'; cases h'

end

end Sorts
end RwLog
