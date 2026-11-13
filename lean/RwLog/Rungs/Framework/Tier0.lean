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
* `Complete.pointwise`: completeness pair by pair, the form that survives a
  preprocessor (`Rung.pointComplete`).
-/
import RwLog.Rungs.Framework.Runtime
import RwLog.Rungs.Framework.Answer
import RwLog.Trusted.Properties
import RwLog.SpanLayer.Modulo

namespace RwLog

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
    Answer.Dead P.sorts.interp s ∨
      ∃ a ∈ R.emitted (R.init P q) n, Answer.Covers P.sorts.interp a s

variable {R}

/-- Honest exhaustion from soundness and coverage of every derivation by what
has been emitted when the run halts. -/
theorem HonestExhaustion.of_cover (hs : R.Sound)
    (h : ∀ P q, P.WellFormed q → ∀ n, R.Halts (R.init P q) n → ∀ s, Derives P q s →
      Answer.Dead P.sorts.interp s ∨
        ∃ a ∈ R.emitted (R.init P q) n, Answer.Covers P.sorts.interp a s) :
    R.HonestExhaustion := by
  intro P q hP n hh
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨s, hs', hps⟩ := ProgramOf.exists_derives hp
    rcases h P q hP n hh s hs' with hdead | ⟨a, ha, hcov⟩
    · have : s.denAt P.sorts.interp = ∅ := hdead
      rw [this] at hps; exact absurd hps (Set.notMem_empty _)
    · exact Set.mem_iUnion₂.2 ⟨a, ha, hcov hps⟩
  · exact Set.iUnion₂_subset fun a ha => hs P q hP n a ha

/-- A certificate gives the three trusted Tier 0 statements. -/
theorem Tier0Cert.tier0 (c : R.Tier0Cert) : R.Tier0 :=
  ⟨c.sound, c.cover, HonestExhaustion.of_cover c.sound c.exhaust⟩

/-- Answers that each refine the span of a derivation are sound. -/
theorem sound_of_refines
    (h : ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
      ∃ s, Derives P q s ∧ Answer.Refines P.sorts.interp a s) : R.Sound := by
  intro P q hP n a ha
  obtain ⟨s, hs, hr⟩ := h P q hP n a ha
  have hr' : Answer.den P.sorts.interp a = s.denAt P.sorts.interp := hr
  rw [hr']
  exact hs.denAt_subset _

/-- Answers that each refine the span of a derivation are
derivation-general. -/
theorem derivationGeneral_of_refines
    (h : ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
      ∃ s, Derives P q s ∧ Answer.Refines P.sorts.interp a s) : R.DerivationGeneral :=
  fun P q hP a ⟨n, ha⟩ => h P q hP n a ha

/-- Completeness gives completeness pair by pair. -/
theorem Complete.pointwise (h : R.Complete) : R.PointComplete := by
  intro P q hP p hp
  obtain ⟨s, hs, hps⟩ := ProgramOf.exists_derives hp
  rcases h P q hP s hs with hdead | ⟨n, a, ha, hcov⟩
  · have : s.denAt P.sorts.interp = ∅ := hdead
    rw [this] at hps; exact absurd hps (Set.notMem_empty _)
  · exact ⟨n, a, ha, hcov hps⟩

end Runtime

end RwLog
