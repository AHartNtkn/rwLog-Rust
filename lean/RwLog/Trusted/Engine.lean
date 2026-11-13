/-
# The interface every rung implements

A rung is a *preprocessor* followed by a *runtime*.

* The preprocessor turns a program and a query into an ordinary program and
  query with the same meaning. It may read and extend a store of proven
  artifacts that is shared across programs. It is written against the kernel
  (`Trusted/Kernel.lean`), so it is a charged computation, and its cost is
  recorded apart from the cost of running. Rung zero's
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
  (`Trusted/Kernel.lean`), so that what it costs is not its own to declare. -/
  gen : {S : Type} → {M : Type → Type} → [Kernel S M] →
    ArtifactStore → ProgramOf S → RelOf S → M (ProgramOf S × RelOf S × ArtifactStore)
  theory_eq : ∀ A (P : Program) (q : Rel), (gen (M := Cost) A P q).val.1.theory = P.theory
  wf : ∀ A (P : Program) (q : Rel), P.WellFormed q →
    (gen (M := Cost) A P q).val.1.WellFormed (gen (M := Cost) A P q).val.2.1
  equiv : ∀ A (P : Program) (q : Rel), P.WellFormed q →
    MEquiv P.theory
      (fun M => (gen (M := Cost) A P q).val.1.semAt M (gen (M := Cost) A P q).val.2.1)
      (fun M => P.semAt M q)

/-- The preprocessor at the kernel of the language. -/
@[reducible] def Preprocessor.run (p : Preprocessor) (A : ArtifactStore) (P : Program) (q : Rel) :
    Cost (Program × Rel × ArtifactStore) := p.gen A P q

def Preprocessor.id : Preprocessor where
  gen A P q := pure (P, q, A)
  theory_eq _ _ _ := rfl
  wf _ _ _ h := h
  equiv _ _ _ _ _ _ := rfl

structure Rung where
  pre : Preprocessor
  rt : Runtime

end RwLog
