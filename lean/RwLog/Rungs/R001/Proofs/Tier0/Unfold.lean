/-
# Tier 0 proofs, part 5: the unfolding strategy

Every goal races rung zero's unfolding of `lb ; e ; rb`. Every span rung zero
produces *is* the denotation of a derivation of the query
(`Lifting.roundSpans_derives`), which is what lets an answer of the unfolding
strategy refine a single derivation (P3.0).
-/
import RwLog.Rungs.R001.Proofs.Tier0.Canon
import RwLog.Rungs.R001.Proofs.Derivations

namespace RwLog

namespace R001

namespace Tier0

open Lifting (bden)

open R000

variable {P : Program}

theorem rel_split {g : Goal} {z : Span} (h : Derives P g.rel z) :
    ∃ s, Derives P g.e s ∧ z.den = GDen g s.den := by
  obtain ⟨s, hs, hz⟩ := Lifting.derives_rel h
  exact ⟨s, hs, by rw [hz, gden_W]⟩

theorem rel_join {g : Goal} {s : Span} (h : Derives P g.e s) (hne : (GDen g s.den).Nonempty) :
    ∃ z, Derives P g.rel z ∧ z.den = GDen g s.den := by
  obtain ⟨lb, e, rb⟩ := g
  cases lb with
  | none =>
    cases rb with
    | none => exact ⟨s, h, by simp [GDen, bden, GRel.id_comp, GRel.comp_id]⟩
    | some r =>
      simp only [GDen, bden, GRel.id_comp] at hne ⊢
      obtain ⟨z, hz, hzd⟩ := compose_isSome hne
      exact ⟨z, .seq h (.span r) hz, hzd⟩
  | some l =>
    cases rb with
    | none =>
      simp only [GDen, bden, GRel.comp_id] at hne ⊢
      obtain ⟨z, hz, hzd⟩ := compose_isSome hne
      exact ⟨z, .seq (.span l) h hz, hzd⟩
    | some r =>
      simp only [GDen, bden] at hne ⊢
      obtain ⟨y, hy, hyd⟩ := compose_isSome (GRel.comp_nonempty_right hne)
      rw [← hyd] at hne ⊢
      obtain ⟨z, hz, hzd⟩ := compose_isSome hne
      exact ⟨z, .seq (.span l) (.seq h (.span r) hy) hz, hzd⟩

/-! ## Answers of the unfolding strategy -/

section
variable (hSE : Obligation.simplify_exact) (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
include hSE hwf

theorem unfold_ref {d : Nat} {g : Goal} {c : Span} (h : c ∈ unfoldAnswers P d g) :
    ∃ s, Derives P g.e s ∧ Ref P.theory c (GDen g s.den) := by
  unfold unfoldAnswers at h
  split at h
  · simp only [List.mem_flatMap] at h
    obtain ⟨a, ha, hc⟩ := h
    obtain ⟨z, hz, hza⟩ := Lifting.roundSpans_derives ha
    obtain ⟨s, hs, hzs⟩ := rel_split hz
    exact ⟨s, hs, (live_ref hSE hwf hc).of_eq (by rw [hza, hzs])⟩
  · simp at h

theorem unfold_dc {d : Nat} {g : Goal} {s : Span} (hf : unfoldFinal P d g = true)
    (h : Derives P g.e s) : DC P.theory (unfoldAnswers P d g) (GDen g s.den) := by
  by_cases hd : DeadR P.theory (GDen g s.den)
  · exact Or.inl hd
  have hne : (GDen g s.den).Nonempty := by
    by_contra hn
    apply hd
    intro M _
    exact Set.eq_empty_of_forall_notMem fun _ ⟨_, hx, _⟩ => hn ⟨_, hx⟩
  obtain ⟨z, hz, hzd⟩ := rel_join h hne
  obtain ⟨m, hm⟩ := derives_iff_derivesN.1 hz
  obtain ⟨a, ha, hsub⟩ := roundSpans_cover (k := d) (n := m) (hm.mono (by omega))
    (by rw [hzd]; exact hne) (.inr hf)
  have hdc := live_dc hSE hwf (T := P.theory) (z := a) (X := GDen g s.den)
    (by rw [← hzd]; exact lcov_of_subset hsub)
  refine hdc.mono fun c hc => ?_
  unfold unfoldAnswers
  simp only [hf, ite_true]
  exact List.mem_flatMap.2 ⟨a, ha, hc⟩

end

end Tier0

end R001

end RwLog
