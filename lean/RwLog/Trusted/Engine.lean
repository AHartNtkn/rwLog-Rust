/-
# The interface every rung implements

A rung is a *preprocessor* followed by a *runtime*.

* The preprocessor turns a program and a query into an ordinary program and
  query with the same meaning. It may read and extend a store of proven
  artifacts that is shared across programs. It is written against the kernel
  (`Trusted/Kernel.lean`), so it is a charged computation, and its cost is
  recorded apart from the cost of running. Rung zero's
  preprocessor is the identity and its store is empty.
* The runtime is a deterministic small-step machine: each step emits a
  finite list of answer spans (possibly empty), or reports that it is done.
  A step may emit several answers at once: an engine that advances many
  independent pieces of work in one step, such as rung R001, produces their
  answers together, and the order inside one step carries no meaning.

The properties every rung must prove (soundness, completeness, honest
exhaustion) are stated here against the specification, so a rung cannot
weaken them.
-/
import RwLog.SpanLayer.Derives
import RwLog.Trusted.Semantics
import RwLog.Trusted.Kernel

namespace RwLog

/-- What a step does: it emits answers and moves to a new state, or reports
that it is done. `A` is the type of answers. -/
inductive StepOf (A : Type) (S : Type) where
  | emit (as : List A) (s : S)
  | done

/-- A step of a machine of the language: its answers are spans. -/
abbrev Step := StepOf Span

/-- A runtime: a deterministic small-step answer enumerator. -/
structure Runtime where
  State : Type
  init : Program → Rel → State
  step : State → Step State

namespace Runtime

variable (R : Runtime)

/-- Run for `n` steps: the answers emitted, and whether the run reported
that it is done. -/
def run : R.State → Nat → List Span × Bool
  | _, 0 => ([], false)
  | s, n + 1 =>
    match R.step s with
    | .emit as s' => let r := run s' n; (as ++ r.1, r.2)
    | .done => ([], true)

/-- The observable trace of the first `n` steps: what each step emitted,
in order, ending at the step that reported it is done. -/
def trace : R.State → Nat → List (List Span)
  | _, 0 => []
  | s, n + 1 =>
    match R.step s with
    | .emit as s' => as :: trace s' n
    | .done => []

/-- Answers emitted within the first `n` steps. -/
def emitted (s : R.State) (n : Nat) : List Span := (R.run s n).1

/-- The run reported that it is done within `n` steps. -/
def Halts (s : R.State) (n : Nat) : Prop := (R.run s n).2 = true

theorem run_halted {s : R.State} {n : Nat} (h : R.Halts s n) :
    ∀ m, R.run s (n + m) = R.run s n := by
  induction n generalizing s with
  | zero => simp [Halts, run] at h
  | succ n ih =>
    intro m
    unfold Halts run at h
    rw [show n + 1 + m = (n + m) + 1 by omega]
    unfold run
    cases hs : R.step s with
    | emit as s' => simp only [hs] at h ⊢; rw [ih h m]
    | done => rfl

theorem run_halted_eq {s : R.State} {n m : Nat} (hn : R.Halts s n) (hm : R.Halts s m) :
    R.run s n = R.run s m := by
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact (R.run_halted hn k).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact R.run_halted hm k

end Runtime

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

/-! ## Properties every rung proves (Tier 0)

They are stated for the runtime against the program and query it is run on,
which is the output of the rung's preprocessor, and against the
specification in every model of the program's theory. -/

namespace Runtime

variable (R : Runtime)

/-- In every model, every emitted answer relates only pairs the query
relates. -/
def Sound : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n,
    ∀ M, P.theory.Model M → a.denAt M ⊆ P.semAt M q

/-- Every derivable span is covered by a single emitted answer after
finitely many steps: in every model, the answer relates every pair the span
relates. A span that relates nothing in any model needs no answer, so an
engine may prune it. Because one answer must cover the whole span, an engine
that only emits ground answers cannot be complete. -/
def Complete : Prop :=
  ∀ P q, P.WellFormed q → ∀ s, Derives P q s →
    (∀ M, P.theory.Model M → s.denAt M = ∅) ∨
      ∃ n, ∃ a ∈ R.emitted (R.init P q) n, ∀ M, P.theory.Model M → s.denAt M ⊆ a.denAt M

/-- If the runtime reports it is done, the answers it emitted cover the
query exactly, in every model. -/
def HonestExhaustion : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, R.Halts (R.init P q) n →
    ∀ M, P.theory.Model M → P.semAt M q = ⋃ a ∈ R.emitted (R.init P q) n, a.denAt M

/-- The runtime reports it is done on every query of a class. -/
def TerminatesOn (C : Program → Rel → Prop) : Prop :=
  ∀ P q, P.WellFormed q → C P q → ∃ n, R.Halts (R.init P q) n

/-! ## Observing a whole run

Properties that compare runs (duality, order independence) are stated on
everything a run ever emits and on whether it ever reports that it is done. -/

/-- Every answer the run on `q` emits at some point. -/
def Answers (P : Program) (q : Rel) : Set Span := {a | ∃ n, a ∈ R.emitted (R.init P q) n}

/-- The run on `q` reports that it is done at some point. -/
def Terminates (P : Program) (q : Rel) : Prop := ∃ n, R.Halts (R.init P q) n

end Runtime

end RwLog
