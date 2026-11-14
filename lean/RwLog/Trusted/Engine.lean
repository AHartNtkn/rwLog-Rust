/-
# The interface every rung implements

A rung is a *preprocessor* followed by a *runtime*.

* The preprocessor turns a program and a query into an ordinary program and
  query with the same meaning. It may read and extend a store of proven
  artifacts that is shared across programs. It is written against the kernel
  (`Trusted/Kernel.lean`) and for any type of spans, which it can read only
  as the kernel reads a span of the program (`rep`), so it is a charged
  computation, and its cost is recorded apart from the cost of running. It
  can arrange the spans it is given and cannot make one: no operation of a
  constraint domain writes a representative out as a span. Rung zero's
  preprocessor is the identity and its store is empty.
* The runtime is a deterministic small-step machine with its type of
  answers (`Trusted/Runtime.lean`, where the properties every machine must
  prove against the specification are stated).
-/
import RwLog.Trusted.Runtime
import RwLog.Trusted.Kernel

namespace RwLog

/-! ## Rungs -/

/-- The cross-program store of proven artifacts. It is reserved for later
rungs (for example cached preprocessing results); rung zero leaves it
empty. -/
structure ArtifactStore where
  /-- No artifact kinds are defined yet. -/
  artifacts : List Empty := []

def ArtifactStore.empty : ArtifactStore := {}

/-- A preprocessor: produces an ordinary program and query with an
equivalent meaning, and may extend the artifact store. It is a charged
computation, so what preprocessing costs is recorded; it is reported next to
a rung's run-time claim and is not part of the run-time cost. Its output is
well formed whenever its input is, so the runtime's theorems apply to it. -/
structure Preprocessor where
  /-- The preprocessor, written against an arbitrary kernel
  (`Trusted/Kernel.lean`) and an arbitrary type `Sp` of spans with the way
  to read one as a representative, so that what it costs is not its own to
  declare. -/
  gen : {Sp R : Type} → {M : Type → Type} → [Kernel R M] → (Sp → M (Option R)) →
    ArtifactStore → ProgramOf Sp → RelOf Sp → M (ProgramOf Sp × RelOf Sp × ArtifactStore)
  sorts_eq : ∀ (κ : KernelRung) A (P : Program) (q : Rel),
    (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep A P q).val.1.sorts =
      P.sorts
  wf : ∀ (κ : KernelRung) A (P : Program) (q : Rel), P.WellFormed q →
    (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep A P q).val.1.WellFormed
      (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep A P q).val.2.1
  equiv : ∀ (κ : KernelRung) A (P : Program) (q : Rel), P.WellFormed q →
    (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep A P q).val.1.pairs
        (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep A P q).val.2.1 =
      P.pairs q

/-- The preprocessor at a kernel rung: at the kernel of the sorts of the
program, reading a span as that kernel does. -/
@[reducible] def Preprocessor.run (p : Preprocessor) (κ : KernelRung) (A : ArtifactStore)
    (P : Program) (q : Rel) : Cost (Program × Rel × ArtifactStore) :=
  @Preprocessor.gen p Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep A P q

def Preprocessor.id : Preprocessor where
  gen _ A P q := pure (P, q, A)
  sorts_eq κ A P q := by rw [(κ.refines P.sorts).pure_eq]; rfl
  wf κ A P q h := by rw [(κ.refines P.sorts).pure_eq]; exact h
  equiv κ A P q _ := by rw [(κ.refines P.sorts).pure_eq]; rfl

structure Rung where
  pre : Preprocessor
  rt : Runtime

end RwLog
