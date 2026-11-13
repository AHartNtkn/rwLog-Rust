/-
# Tier 0 for any runtime, from a certificate on ground triples

`Trusted/Engine.lean` states soundness, completeness and honest exhaustion
against the specification, in every model of the theory. A rung proves them
by giving a `Tier0Cert`, three facts about the ground triples of what it
emits, in the vocabulary of `SpanLayer/Modulo.lean`:

* `sound`: in every model, the query relates every pair an emitted answer
  relates (`LCov`);
* `cover`: every derivation of the query is eventually dead or covered by an
  emitted answer (`DC`);
* `exhaust`: when the run reports that it is done, every derivation is dead
  or covered by what has been emitted.

`Tier0Cert.tier0` turns the certificate into the three trusted statements, so
the bridge to the specification is crossed once, here.

Also for every runtime:

* `DerivationGeneral`: every answer refines the span of one derivation.
  `Tier0Cert.sound_of_ref` gives the `sound` field from it.
* `theory_mono_answers`: adding rules to the theory only removes answers, for
  any runtime that is complete with derivation-general answers.
* `Complete.pointwise`: completeness pair by pair, the form that survives a
  preprocessor (`Rung.pointComplete`).
-/
import RwLog.Rungs.Framework.Runtime
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

namespace Runtime

variable (R : Runtime)

/-- The three Tier 0 properties every rung proves. -/
structure Tier0 : Prop where
  sound : R.Sound
  complete : R.Complete
  honest : R.HonestExhaustion

/-- P3.0: every emitted answer refines the span of one derivation: it is that
span, instantiated only by equations the theory forces, so no answer is less
general than its derivation. -/
def DerivationGeneral : Prop :=
  ∀ P q, P.WellFormed q → ∀ a ∈ R.Answers P q, ∃ s, Derives P q s ∧ a.Refines P.theory s

/-- Completeness pair by pair: in every model, every pair the query relates is
related by some emitted answer. -/
def PointComplete : Prop :=
  ∀ P q, P.WellFormed q → ∀ M, P.theory.Model M → ∀ p ∈ P.semAt M q,
    ∃ n, ∃ a ∈ R.emitted (R.init P q) n, p ∈ a.denAt M

/-- What a rung proves about the ground triples of its answers. -/
structure Tier0Cert : Prop where
  sound : ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
    LCov P.theory (P.sem q) a.den
  cover : ∀ P q, P.WellFormed q → ∀ s, Derives P q s →
    ∃ n, DC P.theory (R.emitted (R.init P q) n) s.den
  exhaust : ∀ P q, P.WellFormed q → ∀ n, R.Halts (R.init P q) n → ∀ s, Derives P q s →
    DC P.theory (R.emitted (R.init P q) n) s.den

variable {R}

/-- The `sound` field from answers that each stand for a derivation. -/
theorem Tier0Cert.sound_of_ref
    (h : ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
      ∃ s, Derives P q s ∧ Ref P.theory a s.den) :
    ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n, LCov P.theory (P.sem q) a.den := by
  intro P q hP n a ha
  obtain ⟨s, hs, hr⟩ := h P q hP n a ha
  exact (hr.1.trans (Backed.of_subset hs.den_subset)).1

/-- Answers that each stand for a derivation are derivation-general. -/
theorem derivationGeneral_of_ref
    (h : ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
      ∃ s, Derives P q s ∧ Ref P.theory a s.den) : R.DerivationGeneral := by
  intro P q hP a ⟨n, ha⟩
  obtain ⟨s, hs, hr⟩ := h P q hP n a ha
  refine ⟨s, hs, fun M hM => ?_⟩
  rw [Span.denAt_eq, Span.denAt_eq]
  exact Set.Subset.antisymm (hr.1.1 M hM) (hr.2 M hM)

theorem Tier0Cert.toSound (c : R.Tier0Cert) : R.Sound := by
  intro P q hP n a ha M hM
  rw [Span.denAt_eq, Program.semAt_eq]
  exact c.sound P q hP n a ha M hM

theorem Tier0Cert.toComplete (c : R.Tier0Cert) : R.Complete := by
  intro P q hP s hs
  obtain ⟨n, hdc⟩ := c.cover P q hP s hs
  rcases hdc with hd | ⟨a, ha, hdom⟩
  · exact .inl (deadR_den.1 hd)
  · exact .inr ⟨n, a, ha, coversLive_iff.2 hdom⟩

theorem Tier0Cert.toHonest (c : R.Tier0Cert) : R.HonestExhaustion := by
  intro P q hP n hh M hM
  ext ⟨u, v⟩
  rw [Program.semAt_eq]
  constructor
  · rintro ⟨S, hS, hSM⟩
    rw [sem_eq_derivable, mem_derivable] at hS
    obtain ⟨s, hs, hx⟩ := hS
    rcases c.exhaust P q hP n hh s hs with hdead | ⟨a, ha, hdom⟩
    · have := hdead M hM
      exact absurd (show (u, v) ∈ s.den.at M from ⟨S, hx, hSM⟩) (this ▸ Set.notMem_empty _)
    · refine Set.mem_iUnion₂.2 ⟨a, ha, ?_⟩
      rw [Span.denAt_eq]
      exact hdom M hM ⟨S, hx, hSM⟩
  · intro h
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 h
    rw [Span.denAt_eq] at hx
    exact c.sound P q hP n a ha M hM hx

/-- A certificate gives the three trusted Tier 0 statements. -/
theorem Tier0Cert.tier0 (c : R.Tier0Cert) : R.Tier0 := ⟨c.toSound, c.toComplete, c.toHonest⟩

/-- Completeness gives completeness pair by pair. -/
theorem Complete.pointwise (h : R.Complete) : R.PointComplete := by
  intro P q hP M hM p hp
  rw [Program.semAt_eq] at hp
  obtain ⟨S, hS, hSM⟩ := hp
  rw [sem_eq_derivable, mem_derivable] at hS
  obtain ⟨s, hs, hx⟩ := hS
  have hps : p ∈ s.denAt M := by rw [Span.denAt_eq]; exact ⟨S, hx, hSM⟩
  rcases h P q hP s hs with hdead | ⟨n, a, ha, hcov⟩
  · rw [hdead M hM] at hps; exact absurd hps (Set.notMem_empty _)
  · exact ⟨n, a, ha, hcov M hM hps⟩

/-- P2.3 for every runtime: adding rules only removes answers. In every model
of the larger theory `T`, each answer under it relates only pairs that one
answer under the smaller theory relates, unless it relates nothing in any such
model. Derivations do not read the theory, so the derivation behind an answer
under `T` is one under the smaller theory, where completeness covers it. -/
theorem theory_mono_answers (hgen : R.DerivationGeneral) (hcomp : R.Complete)
    (P : Program) (T : Theory) (q : Rel) (hwf : P.WellFormed q) (hT : ∀ ρ ∈ T, ρ.WellFormed)
    (hsub : ∀ ρ ∈ P.theory, ρ ∈ T) :
    ∀ a ∈ R.Answers { P with theory := T } q,
      a.Dead T ∨ ∃ b ∈ R.Answers P q, b.CoversLive T a := by
  intro a ha
  have hwf' : Program.WellFormed { P with theory := T } q := ⟨hwf.1, hwf.2.1, hT⟩
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
