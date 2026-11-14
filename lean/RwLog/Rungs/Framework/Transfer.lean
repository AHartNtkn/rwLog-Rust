/-
# Carrying Tier 0 from one runtime to another, and through a preprocessor

A rung that improves an earlier one need not prove Tier 0 from scratch. It
shows how its answers relate to the earlier rung's and uses one of:

* `SameRun R' R`: after every number of steps the two have emitted the same
  answers up to order and equivalence, and they halt together. Everything
  transfers (`SameRun.tier0`, `.derivationGeneral`, `.terminatesOn`).
  `SameRun.of_sim` gets it from a lockstep simulation of the states.
* Answer-level refinement, when the runs are not in step:
  `Sound.of_covered` (each new answer is covered by an old one),
  `Complete.of_covering` (each old answer is dead or covered by a new one),
  `HonestExhaustion.transfer` (when the new run halts it has covered every
  old answer), `TerminatesOn.transfer`.
* `HonestExhaustion.of_cover`: honest exhaustion from soundness and coverage
  of every derivation at the halting step, for a runtime on its own.

A rung is a preprocessor followed by a runtime. `Rung.sound`,
`Rung.pointComplete` and `Rung.honest` state what the pipeline guarantees
about the *original* program and query, given the runtime's Tier 0 and that
the preprocessor's output is well formed. Completeness is pair by pair here:
a preprocessor keeps the meaning, not the derivations, so "one answer covers
each derivable span of the original query" is not something it preserves.
-/
import RwLog.Rungs.Framework.Tier0
import RwLog.Rungs.Framework.Trace

namespace RwLog

/-- Equivalent answers relate the same pairs. -/
theorem Answer.Equiv.refines {A B : Type} [Answer A] [Answer B] {M : Interp} {a : A} {b : B}
    (h : Answer.Equiv M a b) : Answer.Refines M a b :=
  h.den_eq

namespace Runtime

variable {R R' : Runtime}

/-! ## Answer-level refinement -/

/-- If every answer of `R'` is covered by an answer of a
sound `R`, then `R'` is sound. -/
theorem Sound.of_covered (hs : R.Sound)
    (h : ∀ P q, P.WellFormed q → ∀ a' ∈ R'.Answers P q,
      ∃ a ∈ R.Answers P q, Answer.Covers P.sorts.interp a a') : R'.Sound := by
  intro P q hP n a' ha'
  obtain ⟨a, ⟨m, ha⟩, hc⟩ := h P q hP a' ⟨n, ha'⟩
  exact Set.Subset.trans hc (hs P q hP m a ha)

/-- If every answer of a complete `R` is dead or covered by
an answer of `R'`, then `R'` is complete. -/
theorem Complete.of_covering (hc : R.Complete)
    (h : ∀ P q, P.WellFormed q → ∀ a ∈ R.Answers P q,
      Answer.Dead P.sorts.interp a ∨ ∃ a' ∈ R'.Answers P q, Answer.Covers P.sorts.interp a' a) :
    R'.Complete := by
  intro P q hP s hs
  rcases hc P q hP s hs with hd | ⟨n, a, ha, hcov⟩
  · exact .inl hd
  · rcases h P q hP a ⟨n, ha⟩ with hd | ⟨a', ⟨m, ha'⟩, hc'⟩
    · exact .inl (Set.subset_empty_iff.1 (Set.Subset.trans hcov (Eq.subset hd)))
    · exact .inr ⟨m, a', ha', Set.Subset.trans hcov hc'⟩

/-- If `R'` is sound and, when it halts, has covered every answer of a
complete `R`, then `R'` exhausts honestly. -/
theorem HonestExhaustion.transfer (hs : R'.Sound) (hc : R.Complete)
    (h : ∀ P q, P.WellFormed q → ∀ n, R'.Halts (R'.init P q) n → ∀ a ∈ R.Answers P q,
      Answer.Dead P.sorts.interp a ∨
        ∃ a' ∈ R'.emitted (R'.init P q) n, Answer.Covers P.sorts.interp a' a) :
    R'.HonestExhaustion := by
  refine HonestExhaustion.of_cover hs fun P q hP n hh s hs' => ?_
  rcases hc P q hP s hs' with hd | ⟨m, a, ha, hcov⟩
  · exact .inl hd
  · rcases h P q hP n hh a ⟨m, ha⟩ with hd | ⟨a', ha', hc'⟩
    · exact .inl (Set.subset_empty_iff.1 (Set.Subset.trans hcov (Eq.subset hd)))
    · exact .inr ⟨a', ha', Set.Subset.trans hcov hc'⟩

/-- `R'` halts wherever `R` does, so it terminates on every class `R` does. -/
theorem TerminatesOn.transfer {C : Program → Rel → Prop} (ht : R.TerminatesOn C)
    (h : ∀ P q, P.WellFormed q → R.Terminates P q → R'.Terminates P q) : R'.TerminatesOn C :=
  fun P q hP hC => h P q hP (ht P q hP hC)

/-! ## The same run -/

/-- `R'` runs like `R`: after every number of steps the two have emitted the
same answers up to order and equivalence, and they halt together. -/
structure SameRun (R' R : Runtime) : Prop where
  emitted : ∀ P q, P.WellFormed q → ∀ n,
    StepEquiv P.sorts.interp (R'.emitted (R'.init P q) n) (R.emitted (R.init P q) n)
  halts : ∀ P q, P.WellFormed q → ∀ n, R'.Halts (R'.init P q) n ↔ R.Halts (R.init P q) n

/-- A lockstep simulation of the states, started from the initial states,
makes the runs the same. -/
theorem SameRun.of_sim (Sim : Interp → R'.State → R.State → Prop)
    (hinit : ∀ P q, P.WellFormed q → Sim P.sorts.interp (R'.init P q) (R.init P q))
    (hstep : ∀ M s' s, Sim M s' s → StepOf.Rel (StepEquiv M) (Sim M) (R'.step s') (R.step s)) :
    SameRun R' R :=
  ⟨fun P q hP n => emitted_of_sim (hstep _) n (hinit P q hP),
    fun P q hP n => halts_iff_of_sim (hstep _) n (hinit P q hP)⟩

theorem SameRun.refl (R : Runtime) : SameRun R R :=
  ⟨fun _ _ _ _ => StepEquiv.refl _, fun _ _ _ _ => Iff.rfl⟩

/-- Equal runtimes run the same. With `SameRun.tier0` and the other transfer
theorems this carries a rung's results to a machine proved equal to it. -/
theorem SameRun.of_eq (h : R' = R) : SameRun R' R := h ▸ SameRun.refl R'

theorem SameRun.symm (h : SameRun R' R) : SameRun R R' :=
  ⟨fun P q hP n => (h.emitted P q hP n).symm, fun P q hP n => (h.halts P q hP n).symm⟩

theorem SameRun.answer (h : SameRun R' R) {P : Program} {q : Rel} (hP : P.WellFormed q) {n : Nat}
    {a' : R'.Ans} (ha' : a' ∈ R'.emitted (R'.init P q) n) :
    ∃ a ∈ R.emitted (R.init P q) n, Answer.Equiv P.sorts.interp a' a :=
  (h.emitted P q hP n).mem ha'

theorem SameRun.sound (h : SameRun R' R) (hs : R.Sound) : R'.Sound :=
  hs.of_covered fun _ _ hP _ ⟨n, ha'⟩ =>
    let ⟨a, ha, e⟩ := h.answer hP ha'
    ⟨a, ⟨n, ha⟩, e.2⟩

theorem SameRun.complete (h : SameRun R' R) (hc : R.Complete) : R'.Complete :=
  hc.of_covering fun _ _ hP _ ⟨n, ha⟩ =>
    let ⟨a', ha', e⟩ := h.symm.answer hP ha
    .inr ⟨a', ⟨n, ha'⟩, e.2⟩

theorem SameRun.honest (h : SameRun R' R) (t : R.Tier0) : R'.HonestExhaustion :=
  HonestExhaustion.transfer (h.sound t.sound) t.complete fun P q hP n hh a ⟨m, ha⟩ =>
    have ha : a ∈ R.emitted (R.init P q) n := R.emitted_of_halts ((h.halts P q hP n).1 hh) m ha
    let ⟨a', ha', e⟩ := h.symm.answer hP ha
    .inr ⟨a', ha', e.2⟩

/-- Tier 0 transfers between runtimes that run the same. -/
theorem SameRun.tier0 (h : SameRun R' R) (t : R.Tier0) : R'.Tier0 :=
  ⟨h.sound t.sound, h.complete t.complete, h.honest t⟩

theorem SameRun.derivationGeneral (h : SameRun R' R) (hg : R.DerivationGeneral) :
    R'.DerivationGeneral := by
  intro P q hP a' ⟨n, ha'⟩
  obtain ⟨a, ha, e⟩ := h.answer hP ha'
  obtain ⟨s, hs, hr⟩ := hg P q hP a ⟨n, ha⟩
  exact ⟨s, hs, e.refines.trans hr⟩

theorem SameRun.terminatesOn (h : SameRun R' R) {C : Program → Rel → Prop}
    (ht : R.TerminatesOn C) : R'.TerminatesOn C :=
  ht.transfer fun P q hP ⟨n, hn⟩ => ⟨n, (h.halts P q hP n).2 hn⟩

end Runtime

/-! ## The whole rung, on the original program -/

namespace Rung

variable (G : Rung) (κ : KernelRung)

/-- The program and query the runtime is run on. -/
def prog (A : ArtifactStore) (P : Program) (q : Rel) : Program := (G.pre.run κ A P q).val.1
def query (A : ArtifactStore) (P : Program) (q : Rel) : Rel := (G.pre.run κ A P q).val.2.1

theorem pairs_pre {A : ArtifactStore} {P : Program} {q : Rel} (hP : P.WellFormed q) :
    (G.prog κ A P q).pairs (G.query κ A P q) = P.pairs q :=
  G.pre.equiv κ A P q hP

/-- The sorts the runtime is run on extend the sorts of the program. -/
theorem sorts_pre {A : ArtifactStore} {P : Program} {q : Rel} (hP : P.WellFormed q) :
    P.sorts.Extends (G.prog κ A P q).sorts :=
  G.pre.adds κ A P q hP

/-- The rung runs its machine: from the same state the two runs are the
same. -/
theorem run_runtime (A : ArtifactStore) :
    ∀ (n : Nat) (s : G.rt.State), (G.runtime κ A).run s n = G.rt.run s n
  | 0, _ => rfl
  | n + 1, s => by
    cases h : G.rt.step s with
    | emit as s' =>
      have h' : (G.runtime κ A).step s = .emit as s' := h
      rw [Runtime.run_succ_emit _ h, Runtime.run_succ_emit _ h', run_runtime A n s']
      rfl
    | progress k s' =>
      have h' : (G.runtime κ A).step s = .progress k s' := h
      rw [Runtime.run_succ_progress _ h, Runtime.run_succ_progress _ h', run_runtime A n s']
    | done fin =>
      have h' : (G.runtime κ A).step s = .done fin := h
      rw [Runtime.run_succ_done _ h, Runtime.run_succ_done _ h']
      rfl

theorem trace_runtime (A : ArtifactStore) :
    ∀ (n : Nat) (s : G.rt.State), (G.runtime κ A).trace s n = G.rt.trace s n
  | 0, _ => rfl
  | n + 1, s => by
    cases h : G.rt.step s with
    | emit as s' =>
      have h' : (G.runtime κ A).step s = .emit as s' := h
      rw [Runtime.trace_succ_emit _ h, Runtime.trace_succ_emit _ h', trace_runtime A n s']
      rfl
    | progress k s' =>
      have h' : (G.runtime κ A).step s = .progress k s' := h
      rw [Runtime.trace_succ_progress _ h, Runtime.trace_succ_progress _ h',
        trace_runtime A n s']
      rfl
    | done fin =>
      have h' : (G.runtime κ A).step s = .done fin := h
      rw [Runtime.trace_succ_done _ h, Runtime.trace_succ_done _ h']
      rfl

theorem emitted_runtime (A : ArtifactStore) (P : Program) (q : Rel) (n : Nat) :
    (G.runtime κ A).emitted ((G.runtime κ A).init P q) n =
      G.rt.emitted (G.rt.init (G.prog κ A P q) (G.query κ A P q)) n :=
  congrArg Prod.fst (G.run_runtime κ A n _)

theorem halts_runtime (A : ArtifactStore) (P : Program) (q : Rel) (n : Nat) :
    (G.runtime κ A).Halts ((G.runtime κ A).init P q) n ↔
      G.rt.Halts (G.rt.init (G.prog κ A P q) (G.query κ A P q)) n :=
  iff_of_eq (congrArg (fun r : List G.rt.Ans × Option (List G.rt.Ans) => r.2.isSome = true)
    (G.run_runtime κ A n (G.rt.init (G.prog κ A P q) (G.query κ A P q))))

theorem certifies_runtime (A : ArtifactStore) (P : Program) (q : Rel) (k n : Nat) :
    (G.runtime κ A).Certifies ((G.runtime κ A).init P q) k n ↔
      G.rt.Certifies (G.rt.init (G.prog κ A P q) (G.query κ A P q)) k n :=
  iff_of_eq (congrArg (fun t => t[k]? = some (Shown.level n)) (G.trace_runtime κ A (k + 1) _))

/-! The machine is run on the preprocessed program, whose sorts may declare
more than the program's. Its theorems are about its answers read in the
sorts it was run on, so they are theorems about the rung when its answers
say how they are read (`Answer.SelfRead`), as the answers of an engine
do. -/

/-- Every answer of the rung relates only pairs the original query relates. -/
theorem sound (hA : Answer.SelfRead G.rt.Ans) (hs : G.rt.Sound) (A : ArtifactStore) :
    (G.runtime κ A).Sound := by
  intro P q hP n a ha
  rw [G.emitted_runtime κ] at ha
  rw [← G.pairs_pre κ (A := A) hP]
  have h := hs _ _ (G.pre.wf κ A P q hP) n a ha
  rwa [hA _ P.sorts.interp a] at h

/-- Every pair the original query relates is related by some answer of the
rung. -/
theorem pointComplete (hA : Answer.SelfRead G.rt.Ans) (hc : G.rt.PointComplete)
    (A : ArtifactStore) : (G.runtime κ A).PointComplete := by
  intro P q hP p hp
  rw [← G.pairs_pre κ hP] at hp
  obtain ⟨n, a, ha, hpa⟩ := hc _ _ (G.pre.wf κ A P q hP) p hp
  rw [hA _ P.sorts.interp a] at hpa
  exact ⟨n, a, by rw [G.emitted_runtime κ]; exact ha, hpa⟩

/-- When the rung reports that it is done, its answers cover the original
query exactly. -/
theorem honest (hA : Answer.SelfRead G.rt.Ans) (hh : G.rt.HonestExhaustion)
    (A : ArtifactStore) : (G.runtime κ A).HonestExhaustion := by
  intro P q hP n hn
  rw [← G.pairs_pre κ (A := A) hP, G.emitted_runtime]
  exact (hh _ _ (G.pre.wf κ A P q hP) n ((G.halts_runtime κ A P q n).1 hn)).trans
    (Set.iUnion₂_congr fun a _ => hA _ _ a)

/-- A progress certificate of the rung is true of the original query. -/
theorem honestProgress (hA : Answer.SelfRead G.rt.Ans) (hh : G.rt.HonestProgress)
    (A : ArtifactStore) : (G.runtime κ A).HonestProgress := by
  intro P q hP k n hc p hp
  rw [← G.pairs_pre κ hP] at hp
  intro h1 h2
  rw [G.emitted_runtime κ]
  obtain ⟨a, ha, hpa⟩ :=
    hh _ _ (G.pre.wf κ A P q hP) k n ((G.certifies_runtime κ A P q k n).1 hc) p hp h1 h2
  rw [hA _ P.sorts.interp a] at hpa
  exact ⟨a, ha, hpa⟩

/-- The rung with the identity preprocessor is its machine. -/
theorem runtime_id (R : Runtime) (A : ArtifactStore) : (Rung.mk .id R).runtime κ A = R := by
  have h : ∀ P q, (Preprocessor.id.run κ A P q).val = (P, q, A) := fun P q =>
    congrArg Cost.val ((κ.refines P.sorts).pure_eq _)
  unfold Rung.runtime
  simp only [h]

/-- A machine that keeps every property is a rung that keeps them, with the
identity preprocessor. -/
theorem Keeps.of_id {R Base : Runtime} (h : R.Keeps Base) : (Rung.mk .id R).Keeps κ Base :=
  fun A => (runtime_id κ R A).symm ▸ h.toKeepsPointwise

end Rung

end RwLog
