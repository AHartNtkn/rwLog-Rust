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

/-- Equivalent answers relate the same pairs in every model. -/
theorem Answer.Equiv.refines {A B : Type} [Answer A] [Answer B] {a : A} {b : B}
    (h : Answer.Equiv a b) (T : Theory) : Answer.Refines T a b :=
  fun M _ => h.den_eq M

namespace Runtime

variable {R R' : Runtime}

/-! ## Answer-level refinement -/

/-- If every answer of `R'` is covered, up to the theory, by an answer of a
sound `R`, then `R'` is sound. -/
theorem Sound.of_covered (hs : R.Sound)
    (h : ∀ P q, P.WellFormed q → ∀ a' ∈ R'.Answers P q,
      ∃ a ∈ R.Answers P q, Answer.CoversLive P.theory a a') : R'.Sound := by
  intro P q hP n a' ha' M hM
  obtain ⟨a, ⟨m, ha⟩, hc⟩ := h P q hP a' ⟨n, ha'⟩
  exact (hc M hM).trans (hs P q hP m a ha M hM)

/-- If every answer of a complete `R` is dead or covered, up to the theory, by
an answer of `R'`, then `R'` is complete. -/
theorem Complete.of_covering (hc : R.Complete)
    (h : ∀ P q, P.WellFormed q → ∀ a ∈ R.Answers P q,
      Answer.Dead P.theory a ∨ ∃ a' ∈ R'.Answers P q, Answer.CoversLive P.theory a' a) :
    R'.Complete := by
  intro P q hP s hs
  rcases hc P q hP s hs with hd | ⟨n, a, ha, hcov⟩
  · exact .inl hd
  · rcases h P q hP a ⟨n, ha⟩ with hd | ⟨a', ⟨m, ha'⟩, hc'⟩
    · exact .inl fun M hM => Set.subset_empty_iff.1 ((hcov M hM).trans (hd M hM).subset)
    · exact .inr ⟨m, a', ha', fun M hM => (hcov M hM).trans (hc' M hM)⟩

/-- If `R'` is sound and, when it halts, has covered every answer of a
complete `R`, then `R'` exhausts honestly. -/
theorem HonestExhaustion.transfer (hs : R'.Sound) (hc : R.Complete)
    (h : ∀ P q, P.WellFormed q → ∀ n, R'.Halts (R'.init P q) n → ∀ a ∈ R.Answers P q,
      Answer.Dead P.theory a ∨
        ∃ a' ∈ R'.emitted (R'.init P q) n, Answer.CoversLive P.theory a' a) :
    R'.HonestExhaustion := by
  refine HonestExhaustion.of_cover hs fun P q hP n hh s hs' => ?_
  rcases hc P q hP s hs' with hd | ⟨m, a, ha, hcov⟩
  · exact .inl hd
  · rcases h P q hP n hh a ⟨m, ha⟩ with hd | ⟨a', ha', hc'⟩
    · exact .inl fun M hM => Set.subset_empty_iff.1 ((hcov M hM).trans (hd M hM).subset)
    · exact .inr ⟨a', ha', fun M hM => (hcov M hM).trans (hc' M hM)⟩

/-- `R'` halts wherever `R` does, so it terminates on every class `R` does. -/
theorem TerminatesOn.transfer {C : Program → Rel → Prop} (ht : R.TerminatesOn C)
    (h : ∀ P q, P.WellFormed q → R.Terminates P q → R'.Terminates P q) : R'.TerminatesOn C :=
  fun P q hP hC => h P q hP (ht P q hP hC)

/-! ## The same run -/

/-- `R'` runs like `R`: after every number of steps the two have emitted the
same answers up to order and equivalence, and they halt together. -/
structure SameRun (R' R : Runtime) : Prop where
  emitted : ∀ P q, P.WellFormed q → ∀ n,
    StepEquiv (R'.emitted (R'.init P q) n) (R.emitted (R.init P q) n)
  halts : ∀ P q, P.WellFormed q → ∀ n, R'.Halts (R'.init P q) n ↔ R.Halts (R.init P q) n

/-- A lockstep simulation of the states, started from the initial states,
makes the runs the same. -/
theorem SameRun.of_sim (Sim : R'.State → R.State → Prop)
    (hinit : ∀ P q, P.WellFormed q → Sim (R'.init P q) (R.init P q))
    (hstep : ∀ s' s, Sim s' s → StepOf.Rel StepEquiv Sim (R'.step s') (R.step s)) : SameRun R' R :=
  ⟨fun P q hP n => emitted_of_sim hstep n (hinit P q hP),
    fun P q hP n => halts_iff_of_sim hstep n (hinit P q hP)⟩

theorem SameRun.refl (R : Runtime) : SameRun R R :=
  ⟨fun _ _ _ _ => StepEquiv.refl _, fun _ _ _ _ => Iff.rfl⟩

/-- Equal runtimes run the same. With `SameRun.tier0` and the other transfer
theorems this carries a rung's results to a machine proved equal to it. -/
theorem SameRun.of_eq (h : R' = R) : SameRun R' R := h ▸ SameRun.refl R'

theorem SameRun.symm (h : SameRun R' R) : SameRun R R' :=
  ⟨fun P q hP n => (h.emitted P q hP n).symm, fun P q hP n => (h.halts P q hP n).symm⟩

theorem SameRun.answer (h : SameRun R' R) {P : Program} {q : Rel} (hP : P.WellFormed q) {n : Nat}
    {a' : R'.Ans} (ha' : a' ∈ R'.emitted (R'.init P q) n) :
    ∃ a ∈ R.emitted (R.init P q) n, Answer.Equiv a' a :=
  (h.emitted P q hP n).mem ha'

theorem SameRun.sound (h : SameRun R' R) (hs : R.Sound) : R'.Sound :=
  hs.of_covered fun _ _ hP _ ⟨n, ha'⟩ =>
    let ⟨a, ha, e⟩ := h.answer hP ha'
    ⟨a, ⟨n, ha⟩, e.2.live⟩

theorem SameRun.complete (h : SameRun R' R) (hc : R.Complete) : R'.Complete :=
  hc.of_covering fun _ _ hP _ ⟨n, ha⟩ =>
    let ⟨a', ha', e⟩ := h.symm.answer hP ha
    .inr ⟨a', ⟨n, ha'⟩, e.2.live⟩

theorem SameRun.honest (h : SameRun R' R) (t : R.Tier0) : R'.HonestExhaustion :=
  HonestExhaustion.transfer (h.sound t.sound) t.complete fun P q hP n hh a ⟨m, ha⟩ =>
    have ha : a ∈ R.emitted (R.init P q) n := R.emitted_of_halts ((h.halts P q hP n).1 hh) m ha
    let ⟨a', ha', e⟩ := h.symm.answer hP ha
    .inr ⟨a', ha', e.2.live⟩

/-- Tier 0 transfers between runtimes that run the same. -/
theorem SameRun.tier0 (h : SameRun R' R) (t : R.Tier0) : R'.Tier0 :=
  ⟨h.sound t.sound, h.complete t.complete, h.honest t⟩

theorem SameRun.derivationGeneral (h : SameRun R' R) (hg : R.DerivationGeneral) :
    R'.DerivationGeneral := by
  intro P q hP a' ⟨n, ha'⟩
  obtain ⟨a, ha, e⟩ := h.answer hP ha'
  obtain ⟨s, hs, hr⟩ := hg P q hP a ⟨n, ha⟩
  exact ⟨s, hs, fun M hM => (e.refines P.theory M hM).trans (hr M hM)⟩

theorem SameRun.terminatesOn (h : SameRun R' R) {C : Program → Rel → Prop}
    (ht : R.TerminatesOn C) : R'.TerminatesOn C :=
  ht.transfer fun P q hP ⟨n, hn⟩ => ⟨n, (h.halts P q hP n).2 hn⟩

end Runtime

/-! ## The whole rung, on the original program -/

namespace Rung

variable (G : Rung)

/-- The program and query the runtime is run on. -/
def prog (A : ArtifactStore) (P : Program) (q : Rel) : Program := (G.pre.run A P q).val.1
def query (A : ArtifactStore) (P : Program) (q : Rel) : Rel := (G.pre.run A P q).val.2.1

theorem semAt_pre {A : ArtifactStore} {P : Program} {q : Rel} (hP : P.WellFormed q) {M : Interp}
    (hM : P.theory.Model M) : (G.prog A P q).semAt M (G.query A P q) = P.semAt M q :=
  G.pre.equiv A P q hP M hM

theorem model_pre {A : ArtifactStore} {P : Program} {q : Rel} {M : Interp}
    (hM : P.theory.Model M) : (G.prog A P q).theory.Model M := by
  unfold prog; rw [G.pre.theory_eq]; exact hM

/-- The rung runs its machine: from the same state the two runs are the
same. -/
theorem run_runtime (A : ArtifactStore) :
    ∀ (n : Nat) (s : G.rt.State), (G.runtime A).run s n = G.rt.run s n
  | 0, _ => rfl
  | n + 1, s => by
    cases h : G.rt.step s with
    | emit as s' =>
      have h' : (G.runtime A).step s = .emit as s' := h
      rw [Runtime.run_succ_emit _ h, Runtime.run_succ_emit _ h', run_runtime A n s']
      rfl
    | progress k s' =>
      have h' : (G.runtime A).step s = .progress k s' := h
      rw [Runtime.run_succ_progress _ h, Runtime.run_succ_progress _ h', run_runtime A n s']
    | done fin =>
      have h' : (G.runtime A).step s = .done fin := h
      rw [Runtime.run_succ_done _ h, Runtime.run_succ_done _ h']
      rfl

theorem trace_runtime (A : ArtifactStore) :
    ∀ (n : Nat) (s : G.rt.State), (G.runtime A).trace s n = G.rt.trace s n
  | 0, _ => rfl
  | n + 1, s => by
    cases h : G.rt.step s with
    | emit as s' =>
      have h' : (G.runtime A).step s = .emit as s' := h
      rw [Runtime.trace_succ_emit _ h, Runtime.trace_succ_emit _ h', trace_runtime A n s']
      rfl
    | progress k s' =>
      have h' : (G.runtime A).step s = .progress k s' := h
      rw [Runtime.trace_succ_progress _ h, Runtime.trace_succ_progress _ h',
        trace_runtime A n s']
      rfl
    | done fin =>
      have h' : (G.runtime A).step s = .done fin := h
      rw [Runtime.trace_succ_done _ h, Runtime.trace_succ_done _ h']
      rfl

theorem emitted_runtime (A : ArtifactStore) (P : Program) (q : Rel) (n : Nat) :
    (G.runtime A).emitted ((G.runtime A).init P q) n =
      G.rt.emitted (G.rt.init (G.prog A P q) (G.query A P q)) n :=
  congrArg Prod.fst (G.run_runtime A n _)

theorem halts_runtime (A : ArtifactStore) (P : Program) (q : Rel) (n : Nat) :
    (G.runtime A).Halts ((G.runtime A).init P q) n ↔
      G.rt.Halts (G.rt.init (G.prog A P q) (G.query A P q)) n :=
  iff_of_eq (congrArg (fun r : List G.rt.Ans × Option (List G.rt.Ans) => r.2.isSome = true)
    (G.run_runtime A n (G.rt.init (G.prog A P q) (G.query A P q))))

theorem certifies_runtime (A : ArtifactStore) (P : Program) (q : Rel) (k n : Nat) :
    (G.runtime A).Certifies ((G.runtime A).init P q) k n ↔
      G.rt.Certifies (G.rt.init (G.prog A P q) (G.query A P q)) k n :=
  iff_of_eq (congrArg (fun t => t[k]? = some (Shown.level n)) (G.trace_runtime A (k + 1) _))

/-- Every answer of the rung relates only pairs the original query relates. -/
theorem sound (hs : G.rt.Sound) (A : ArtifactStore) : (G.runtime A).Sound := by
  intro P q hP n a ha M hM
  rw [G.emitted_runtime] at ha
  rw [← G.semAt_pre hP hM]
  exact hs _ _ (G.pre.wf A P q hP) n a ha M (G.model_pre hM)

/-- Every pair the original query relates is related by some answer of the
rung. -/
theorem pointComplete (hc : G.rt.PointComplete) (A : ArtifactStore) :
    (G.runtime A).PointComplete := by
  intro P q hP M hM p hp
  rw [← G.semAt_pre hP hM] at hp
  obtain ⟨n, a, ha, hpa⟩ := hc _ _ (G.pre.wf A P q hP) M (G.model_pre hM) p hp
  exact ⟨n, a, by rw [G.emitted_runtime]; exact ha, hpa⟩

/-- When the rung reports that it is done, its answers cover the original
query exactly. -/
theorem honest (hh : G.rt.HonestExhaustion) (A : ArtifactStore) :
    (G.runtime A).HonestExhaustion := by
  intro P q hP n hn M hM
  rw [← G.semAt_pre hP hM, G.emitted_runtime]
  exact hh _ _ (G.pre.wf A P q hP) n ((G.halts_runtime A P q n).1 hn) M (G.model_pre hM)

/-- A progress certificate of the rung is true of the original query. -/
theorem honestProgress (hh : G.rt.HonestProgress) (A : ArtifactStore) :
    (G.runtime A).HonestProgress := by
  intro P q hP k n hc M hM p hp
  rw [← G.semAt_pre hP hM] at hp
  rw [G.emitted_runtime]
  exact hh _ _ (G.pre.wf A P q hP) k n ((G.certifies_runtime A P q k n).1 hc) M
    (G.model_pre hM) p hp

/-- The rung with the identity preprocessor is its machine. -/
theorem runtime_id (R : Runtime) (A : ArtifactStore) : (Rung.mk .id R).runtime A = R := rfl

/-- A machine that keeps every property is a rung that keeps them, with the
identity preprocessor. -/
theorem Keeps.of_id {R Base : Runtime} (h : R.Keeps Base) : (Rung.mk .id R).Keeps Base :=
  fun A => (runtime_id R A).symm ▸ h.toKeepsPointwise

end Rung

end RwLog
