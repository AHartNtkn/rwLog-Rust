/-
# Tier 0 for any runtime, from a certificate

`Trusted/Runtime.lean` states soundness, completeness and honest exhaustion
against the specification, in every model of the theory and for any type of
answers. A rung proves them by giving a `Tier0Cert`:

* `sound`: in every model, the query relates every pair an emitted answer
  relates;
* `cover`: every derivation of the query is eventually dead or covered by an
  emitted answer;
* `exhaust`: when the run reports that it is done, every derivation is dead
  or covered by what has been emitted.

`Tier0Cert.tier0` turns the certificate into the three trusted statements, so
the bridge from derivations to the ground semantics is crossed once, here
(`HonestExhaustion.of_cover`). A machine whose answers are spans states the
three facts on ground triples, in the vocabulary of `SpanLayer/Modulo.lean`,
and passes to this form with `coversLive_iff` and `deadR_den`.

Also for every runtime:

* `derivationGeneral_of_refines`: answers that each stand for a derivation
  are derivation-general, and sound.
* `theory_mono_answers`: adding rules to the theory only removes answers, for
  any runtime that is complete with derivation-general answers.
* `Complete.pointwise`: completeness pair by pair, the form that survives a
  preprocessor (`Rung.pointComplete`).
-/
import RwLog.Rungs.Framework.Runtime
import RwLog.Rungs.Framework.Answer
import RwLog.Trusted.Properties
import RwLog.SpanLayer.Modulo

namespace RwLog

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

/-- In every interpretation, a derivable span relates only pairs the query
relates. -/
theorem Derives.denAt_subset {P : Program} {e : Rel} {s : Span} (h : Derives P e s) (M : Interp) :
    s.denAt M ⊆ P.semAt M e := by
  rw [Span.denAt_eq, ProgramOf.semAt_eq]
  exact GRel.at_mono h.den_subset M

/-- In every interpretation, a pair the query relates is related by a
derivable span. -/
theorem ProgramOf.exists_derives {P : Program} {e : Rel} {M : Interp} {p : GTerm × GTerm}
    (hp : p ∈ P.semAt M e) : ∃ s, Derives P e s ∧ p ∈ s.denAt M := by
  rw [ProgramOf.semAt_eq] at hp
  obtain ⟨S, hS, hSM⟩ := hp
  rw [sem_eq_derivable, mem_derivable] at hS
  obtain ⟨s, hs, hx⟩ := hS
  exact ⟨s, hs, by rw [Span.denAt_eq]; exact ⟨S, hx, hSM⟩⟩

namespace Runtime

variable (R : Runtime)

/-- The three Tier 0 properties every rung proves. -/
structure Tier0 : Prop where
  sound : R.Sound
  complete : R.Complete
  honest : R.HonestExhaustion

/-- What a rung proves about its answers. -/
structure Tier0Cert : Prop where
  sound : R.Sound
  cover : R.Complete
  exhaust : ∀ P q, P.WellFormed q → ∀ n, R.Halts (R.init P q) n → ∀ s, Derives P q s →
    Answer.Dead P.theory s ∨ ∃ a ∈ R.emitted (R.init P q) n, Answer.CoversLive P.theory a s

variable {R}

/-- Honest exhaustion from soundness and coverage of every derivation by what
has been emitted when the run halts. -/
theorem HonestExhaustion.of_cover (hs : R.Sound)
    (h : ∀ P q, P.WellFormed q → ∀ n, R.Halts (R.init P q) n → ∀ s, Derives P q s →
      Answer.Dead P.theory s ∨ ∃ a ∈ R.emitted (R.init P q) n, Answer.CoversLive P.theory a s) :
    R.HonestExhaustion := by
  intro P q hP n hh M hM
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨s, hs', hps⟩ := ProgramOf.exists_derives hp
    rcases h P q hP n hh s hs' with hdead | ⟨a, ha, hcov⟩
    · have := hdead M hM
      change s.denAt M = ∅ at this
      rw [this] at hps; exact absurd hps (Set.notMem_empty _)
    · exact Set.mem_iUnion₂.2 ⟨a, ha, hcov M hM hps⟩
  · exact Set.iUnion₂_subset fun a ha => hs P q hP n a ha M hM

/-- A certificate gives the three trusted Tier 0 statements. -/
theorem Tier0Cert.tier0 (c : R.Tier0Cert) : R.Tier0 :=
  ⟨c.sound, c.cover, HonestExhaustion.of_cover c.sound c.exhaust⟩

/-- Answers that each refine the span of a derivation are sound. -/
theorem sound_of_refines
    (h : ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
      ∃ s, Derives P q s ∧ Answer.Refines P.theory a s) : R.Sound := by
  intro P q hP n a ha M hM
  obtain ⟨s, hs, hr⟩ := h P q hP n a ha
  rw [hr M hM]
  exact hs.denAt_subset M

/-- Answers that each refine the span of a derivation are
derivation-general. -/
theorem derivationGeneral_of_refines
    (h : ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
      ∃ s, Derives P q s ∧ Answer.Refines P.theory a s) : R.DerivationGeneral :=
  fun P q hP a ⟨n, ha⟩ => h P q hP n a ha

/-- Completeness gives completeness pair by pair. -/
theorem Complete.pointwise (h : R.Complete) : R.PointComplete := by
  intro P q hP M hM p hp
  obtain ⟨s, hs, hps⟩ := ProgramOf.exists_derives hp
  rcases h P q hP s hs with hdead | ⟨n, a, ha, hcov⟩
  · have := hdead M hM
    change s.denAt M = ∅ at this
    rw [this] at hps; exact absurd hps (Set.notMem_empty _)
  · exact ⟨n, a, ha, hcov M hM hps⟩

/-- P2.3 for every runtime: adding rules only removes answers. In every model
of the larger theory `T`, each answer under it relates only pairs that one
answer under the smaller theory relates, unless it relates nothing in any such
model. Derivations do not read the theory, so the derivation behind an answer
under `T` is one under the smaller theory, where completeness covers it. -/
theorem theory_mono_answers (hgen : R.DerivationGeneral) (hcomp : R.Complete) :
    R.TheoryMonoAnswers := by
  intro P T q hwf hT hsub a ha
  have hwf' : ProgramOf.WellFormed { P with theory := T } q := ⟨hwf.1, hwf.2.1, hT⟩
  obtain ⟨s, hs, hrefine⟩ := hgen _ q hwf' a ha
  rcases hcomp P q hwf s (derives_theory hs) with hdead | ⟨n, b, hb, hcov⟩
  · left
    intro M hM
    rw [hrefine M hM]
    exact hdead M (Theory.Model.of_subset hsub hM)
  · right
    refine ⟨b, ⟨n, hb⟩, fun M hM => ?_⟩
    rw [hrefine M hM]
    exact hcov M (Theory.Model.of_subset hsub hM)

end Runtime

end RwLog
