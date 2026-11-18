/-
# Carrying Tier 0 from one runtime to another, and through a preprocessor

A rung that improves an earlier one need not prove Tier 0 from scratch. It
shows how its answers relate to the earlier rung's and uses one of:

* `SameRun R' R`: after every number of steps the two have emitted the same
  answers up to order and equivalence, and they halt together. Everything
  transfers (`SameRun.tier0`, `.terminatesOn`).
  `SameRun.of_sim` gets it from a lockstep simulation of the states.
* Answer-level refinement, when the runs are not in step:
  `Sound.of_covered` (each new answer is covered by an old one),
  `Complete.of_covering` (each old answer is dead or covered by a new one),
  `HonestExhaustion.transfer` (when the new run halts it has covered every
  old answer), `TerminatesOn.transfer`.
* `HonestExhaustion.of_cover`: honest exhaustion from soundness and coverage
  of every derivation at the halting step, for a runtime on its own.

A rung is a list of preprocessors followed by a runtime. The laws of the list
follow from the laws of its members (`Preprocessor.runAll_wf`,
`runAll_equiv`, `runAll_adds`). `Rung.sound`, `Rung.pointComplete` and
`Rung.honest` state what the rung guarantees about the *original* program
and query, given the same law of the runtime, and `Rung.laws` is the three
together. Completeness is pair
by pair here: a preprocessor keeps the meaning, not the derivations, so "one
answer covers each derivable span of the original query" is not something it
preserves.
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

theorem SameRun.terminatesOn (h : SameRun R' R) {C : Program → Rel → Prop}
    (ht : R.TerminatesOn C) : R'.TerminatesOn C :=
  ht.transfer fun P q hP ⟨n, hn⟩ => ⟨n, (h.halts P q hP n).2 hn⟩

end Runtime

/-! ## Preprocessors one after another

The laws of a list of preprocessors follow from the laws of its members,
because each member is run at the kernel of the sorts of the program it is
handed (`Preprocessor.runAll`, `Trusted/Engine.lean`). A rung that adds a
rewrite proves the three laws of that rewrite and nothing about the list. -/

/-- Extending sorts twice extends them. -/
theorem Sorts.Extends.trans {S S' S'' : Sorts} (h : S.Extends S') (h' : S'.Extends S'') :
    S.Extends S'' :=
  ⟨h.1.trans h'.1, fun n hn t =>
    (h'.2 n ((h.1.map Prod.fst).subset hn) t).trans (h.2 n hn t)⟩

namespace Preprocessor

variable (κ : KernelRung)

/-- No preprocessor costs nothing. -/
theorem runAll_nil_ticks (A : ArtifactStore) (P : Program) (q : Rel) :
    (runAll κ [] A P q).ticks = 0 := rfl

/-- A list of preprocessors costs what its members cost, each on what the
ones before it returned. -/
theorem runAll_cons_ticks (p : Preprocessor) (rest : List Preprocessor) (A : ArtifactStore)
    (P : Program) (q : Rel) :
    (runAll κ (p :: rest) A P q).ticks = (p.run κ A P q).ticks +
      (runAll κ rest (p.run κ A P q).val.2.2 (p.run κ A P q).val.1
        (p.run κ A P q).val.2.1).ticks := rfl

/-- What a list of preprocessors returns on a well-formed input is well
formed. -/
theorem runAll_wf : ∀ (ps : List Preprocessor) (A : ArtifactStore) (P : Program) (q : Rel),
    P.WellFormed q → (runAll κ ps A P q).val.1.WellFormed (runAll κ ps A P q).val.2.1
  | [], _, _, _, h => h
  | p :: rest, A, P, q, h => runAll_wf rest _ _ _ (p.wf κ A P q h)

/-- What a list of preprocessors returns relates the pairs the input
relates. -/
theorem runAll_equiv : ∀ (ps : List Preprocessor) (A : ArtifactStore) (P : Program) (q : Rel),
    P.WellFormed q →
      (runAll κ ps A P q).val.1.pairs (runAll κ ps A P q).val.2.1 = P.pairs q
  | [], _, _, _, _ => rfl
  | p :: rest, A, P, q, h =>
    (runAll_equiv rest _ _ _ (p.wf κ A P q h)).trans (p.equiv κ A P q h)

/-- The sorts a list of preprocessors returns extend the sorts of the
input. -/
theorem runAll_adds : ∀ (ps : List Preprocessor) (A : ArtifactStore) (P : Program) (q : Rel),
    P.WellFormed q → P.sorts.Extends (runAll κ ps A P q).val.1.sorts
  | [], _, _, _, _ => Sorts.Extends.refl _
  | p :: rest, A, P, q, h =>
    (p.adds κ A P q h).trans (runAll_adds rest _ _ _ (p.wf κ A P q h))

end Preprocessor

/-! ## Answers that say how they are read, in two interpretations -/

section
variable {A : Type} [Answer A]

theorem Answer.SelfRead.covers (hA : Answer.SelfRead A) (M M' : Interp) {a b : A} :
    Answer.Covers M a b ↔ Answer.Covers M' a b := by
  unfold Answer.Covers
  rw [hA M M' a, hA M M' b]

theorem Answer.SelfRead.equiv (hA : Answer.SelfRead A) (M M' : Interp) {a b : A}
    (h : Answer.Equiv M a b) : Answer.Equiv M' a b :=
  ⟨(hA.covers M M').1 h.1, (hA.covers M M').1 h.2⟩

end

/-! ## The whole rung, on the original program -/

namespace Rung

variable (G : Rung) (κ : KernelRung)

/-- The program and query the runtime is run on. -/
def prog (A : ArtifactStore) (P : Program) (q : Rel) : Program :=
  (Preprocessor.runAll κ G.pre A P q).val.1
def query (A : ArtifactStore) (P : Program) (q : Rel) : Rel :=
  (Preprocessor.runAll κ G.pre A P q).val.2.1

/-- What the runtime is run on is well formed. -/
theorem wf_pre {A : ArtifactStore} {P : Program} {q : Rel} (hP : P.WellFormed q) :
    (G.prog κ A P q).WellFormed (G.query κ A P q) :=
  Preprocessor.runAll_wf κ G.pre A P q hP

theorem pairs_pre {A : ArtifactStore} {P : Program} {q : Rel} (hP : P.WellFormed q) :
    (G.prog κ A P q).pairs (G.query κ A P q) = P.pairs q :=
  Preprocessor.runAll_equiv κ G.pre A P q hP

/-- The sorts the runtime is run on extend the sorts of the program. -/
theorem sorts_pre {A : ArtifactStore} {P : Program} {q : Rel} (hP : P.WellFormed q) :
    P.sorts.Extends (G.prog κ A P q).sorts :=
  Preprocessor.runAll_adds κ G.pre A P q hP

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
    | done fin =>
      have h' : (G.runtime κ A).step s = .done fin := h
      rw [Runtime.trace_succ_done _ h, Runtime.trace_succ_done _ h']
      rfl

/-- The trace of the rung is the trace of its machine on the preprocessed
input. -/
theorem trace_init (A : ArtifactStore) (P : Program) (q : Rel) (n : Nat) :
    (G.runtime κ A).trace ((G.runtime κ A).init P q) n =
      G.rt.trace (G.rt.init (G.prog κ A P q) (G.query κ A P q)) n :=
  G.trace_runtime κ A n _

theorem emitted_runtime (A : ArtifactStore) (P : Program) (q : Rel) (n : Nat) :
    (G.runtime κ A).emitted ((G.runtime κ A).init P q) n =
      G.rt.emitted (G.rt.init (G.prog κ A P q) (G.query κ A P q)) n :=
  congrArg Prod.fst (G.run_runtime κ A n _)

theorem halts_runtime (A : ArtifactStore) (P : Program) (q : Rel) (n : Nat) :
    (G.runtime κ A).Halts ((G.runtime κ A).init P q) n ↔
      G.rt.Halts (G.rt.init (G.prog κ A P q) (G.query κ A P q)) n :=
  iff_of_eq (congrArg (fun r : List G.rt.Ans × Option (List G.rt.Ans) => r.2.isSome = true)
    (G.run_runtime κ A n (G.rt.init (G.prog κ A P q) (G.query κ A P q))))

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
  have h := hs _ _ (G.wf_pre κ hP) n a ha
  rwa [hA _ P.sorts.interp a] at h

/-- Every pair the original query relates is related by some answer of the
rung. -/
theorem pointComplete (hA : Answer.SelfRead G.rt.Ans) (hc : G.rt.PointComplete)
    (A : ArtifactStore) : (G.runtime κ A).PointComplete := by
  intro P q hP p hp
  rw [← G.pairs_pre κ hP] at hp
  obtain ⟨n, a, ha, hpa⟩ := hc _ _ (G.wf_pre κ hP) p hp
  rw [hA _ P.sorts.interp a] at hpa
  exact ⟨n, a, by rw [G.emitted_runtime κ]; exact ha, hpa⟩

/-- When the rung reports that it is done, its answers cover the original
query exactly. -/
theorem honest (hA : Answer.SelfRead G.rt.Ans) (hh : G.rt.HonestExhaustion)
    (A : ArtifactStore) : (G.runtime κ A).HonestExhaustion := by
  intro P q hP n hn
  rw [← G.pairs_pre κ (A := A) hP, G.emitted_runtime]
  exact (hh _ _ (G.wf_pre κ hP) n ((G.halts_runtime κ A P q n).1 hn)).trans
    (Set.iUnion₂_congr fun a _ => hA _ _ a)

/-- **A rung has the laws if its machine has them**, whatever its rewrites:
each keeps the relation, and that is all the laws need of it. -/
theorem laws (hA : Answer.SelfRead G.rt.Ans) (h : G.rt.Laws) (A : ArtifactStore) :
    (G.runtime κ A).Laws :=
  ⟨G.sound κ hA h.sound A, G.pointComplete κ hA h.complete A, G.honest κ hA h.honest A⟩

/-- The rung with no preprocessor is its machine. -/
theorem runtime_nil (R : Runtime) (A : ArtifactStore) : (Rung.mk [] R).runtime κ A = R := rfl

end Rung

end RwLog
