/-
# Rung R001, theory monotonicity (P2.3)

Adding rules to a theory only removes answers: every answer the machine emits
under the larger theory `T` either relates nothing in any model of `T`, or is
covered, in every model of `T`, by an answer the machine emits under the
smaller theory.

The proof is semantic and goes through the span layer. Derivations do not
read the theory, so the derivation behind an answer under `T`
(`derivation_general`) is also a derivation under the smaller theory, where
`complete` covers it in every model of the smaller theory. Every model of `T`
is a model of the smaller theory, since `T` contains its rules.

Termination is not monotone in the theory (the counterexample is in
`Spec.lean`), so there is no termination half.
-/
import RwLog.Rungs.R001.Proofs.Tier0

namespace RwLog

namespace R001

/-- Every model of a larger theory is a model of a smaller one. -/
theorem Theory.Model.of_subset {T T' : Theory} (h : ∀ ρ ∈ T, ρ ∈ T') {M : Interp}
    (hM : T'.Model M) : T.Model M :=
  fun ρ hρ => hM ρ (h ρ hρ)

/-- Derivations read only the definitions, never the theory. -/
theorem derives_theory {P : Program} {T : Theory} {e : Rel} {s : Span}
    (h : Derives { P with theory := T } e s) : Derives P e s := by
  induction h with
  | span s => exact .span s
  | orl _ ih => exact .orl ih
  | orr _ ih => exact .orr ih
  | seq _ _ hc ih₁ ih₂ => exact .seq ih₁ ih₂ hc
  | and _ _ hc ih₁ ih₂ => exact .and ih₁ ih₂ hc
  | conv _ ih => exact .conv ih
  | call _ ih => exact .call ih

/-- P2.3: adding rules only removes answers. -/
theorem theory_mono_answers : Obligation.theory_mono_answers := by
  intro P T q hwf hT hsub a ha
  have hwf' : Program.WellFormed { P with theory := T } q := ⟨hwf.1, hwf.2.1, hT⟩
  obtain ⟨s, hs, hrefine⟩ := derivation_general _ q hwf' a ha
  rcases complete P q hwf s (derives_theory hs) with hdead | ⟨n, b, hb, hcov⟩
  · left
    intro M hM
    rw [hrefine M hM]
    exact hdead M (Theory.Model.of_subset hsub hM)
  · right
    refine ⟨b, ⟨n, hb⟩, fun M hM => ?_⟩
    rw [hrefine M hM]
    exact hcov M (Theory.Model.of_subset hsub hM)

end R001

end RwLog
