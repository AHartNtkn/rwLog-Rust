/-
# The interface every rung implements

A rung is a *preprocessor* followed by a *runtime*.

* The preprocessor turns a program and a query into an ordinary program and
  query with the same meaning. It may read and extend a store of proven
  artifacts that is shared across programs. It is written against the kernel
  (`Trusted/Kernel.lean`) and for any type of spans, which it can read only
  as the kernel reads a span of the program (`rep`), so it is a charged
  computation, and its cost is recorded apart from the cost of running.
  A rung has a list of them, run one after another (`Preprocessor.runAll`);
  rung zero's list is empty and so is its store.

  What a preprocessor may add is this, and nothing else.

  * *Definitions.* The program it returns may define other names, with
    bodies arranged from the spans it was given. It cannot make a span: no
    operation of a constraint domain writes a representative out as a span.
  * *Sort declarations.* The sorts of the program it returns extend the
    sorts of the program it was given (`Sorts.Extends`,
    `Trusted/Semantics.lean`): the declarations it was given come first and
    unchanged, further ones may follow, and every sort that was declared
    keeps its members. It may not take a declaration away or change one,
    and it may not declare a name that a declaration it was given uses
    without declaring, since that would give members to a sort that had
    none.
  * *A sort on an end of a span.* The one thing it may do to a span is hold
    one of its ends to a sort by name (`Span.sorted`), so that a relation it
    has specialised comes with the sort it was specialised to. This adds a
    constraint and can only take pairs away from the span.

  The engine is then run at the kernel of the extended sorts, and its
  answers are representatives for those sorts, carried with them
  (`Trusted/Runtime.lean`): an answer that names an added sort is read with
  the declarations the preprocessor added. Because the declared sorts keep
  their members, a name the user declared means in an answer what the user
  said it means.
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
well formed whenever its input is, so the runtime's theorems apply to it,
and its sorts extend the sorts of its input. -/
structure Preprocessor where
  /-- The preprocessor, written against an arbitrary kernel
  (`Trusted/Kernel.lean`) and an arbitrary type `Sp` of spans with the way
  to read one as a representative and the way to hold an end of one to a
  sort, so that what it costs is not its own to declare and the spans it
  returns are the spans it was given, with ends held to sorts. -/
  gen : {Sp R : Type} → {M : Type → Type} → [Kernel R M] → (Sp → M (Option R)) →
    (Sp → Bool → Name → Sp) →
    ArtifactStore → ProgramOf Sp → RelOf Sp → M (ProgramOf Sp × RelOf Sp × ArtifactStore)
  /-- What it adds to the sorts: declarations behind the ones it was given,
  with every declared sort keeping its members. -/
  adds : ∀ (κ : KernelRung) A (P : Program) (q : Rel), P.WellFormed q →
    P.sorts.Extends
      (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep Span.sorted
        A P q).val.1.sorts
  wf : ∀ (κ : KernelRung) A (P : Program) (q : Rel), P.WellFormed q →
    (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep Span.sorted
        A P q).val.1.WellFormed
      (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep Span.sorted
        A P q).val.2.1
  equiv : ∀ (κ : KernelRung) A (P : Program) (q : Rel), P.WellFormed q →
    (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep Span.sorted
          A P q).val.1.pairs
        (@gen Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep Span.sorted
          A P q).val.2.1 =
      P.pairs q

/-- The preprocessor at a kernel rung: at the kernel of the sorts of the
program, reading a span as that kernel does. -/
@[reducible] def Preprocessor.run (p : Preprocessor) (κ : KernelRung) (A : ArtifactStore)
    (P : Program) (q : Rel) : Cost (Program × Rel × ArtifactStore) :=
  @Preprocessor.gen p Span (κ.Rep P.sorts) Cost (κ.kernel P.sorts) (κ.kernel P.sorts).rep
    Span.sorted A P q

/-- A list of sorts extends itself. -/
theorem Sorts.Extends.refl (S : Sorts) : S.Extends S := ⟨List.prefix_refl S, fun _ _ _ => Iff.rfl⟩

/-! ## Rewrites one after another

A rung has a list of preprocessors, and they are run in order, each on the
program and query the one before it returned. Each is run at the kernel of
the sorts of the program it is handed, since the one before it may have
added sorts: that is the kernel its laws (`adds`, `wf`, `equiv`) are stated
at, so the laws of a list follow from the laws of its members
(`Preprocessor.runAll_wf`, `runAll_equiv`, `runAll_adds`,
`Rungs/Framework/Transfer.lean`). One preprocessor written as two run one
after the other at the kernel of the first program would not have the laws
of the second. The empty list is no preprocessing, at no cost. A rung that
adds a rewrite to the rung below it adds a member to this list. -/

/-- The preprocessors of a list, run in order, each at the kernel of the
sorts of the program it is handed. What each costs is added up. -/
def Preprocessor.runAll (κ : KernelRung) :
    List Preprocessor → ArtifactStore → Program → Rel → Cost (Program × Rel × ArtifactStore)
  | [], A, P, q => pure (P, q, A)
  | p :: rest, A, P, q => do
    let r ← p.run κ A P q
    Preprocessor.runAll κ rest r.2.2 r.1 r.2.1

structure Rung where
  /-- The rewrites before execution, in the order they are run. -/
  pre : List Preprocessor
  rt : Runtime

end RwLog
