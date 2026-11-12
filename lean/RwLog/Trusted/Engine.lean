/-
# The interface every rung implements

A rung is a *preprocessor* followed by a *runtime*.

* The preprocessor turns a program and a query into an ordinary program and
  query with the same meaning. It may read and extend a store of proven
  artifacts that is shared across programs. Rung zero's preprocessor is the
  identity and its store is empty.
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

namespace RwLog

inductive Step (S : Type) where
  | emit (as : List Span) (s : S)
  | done

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
equivalent meaning, and may extend the artifact store. -/
structure Preprocessor where
  run : ArtifactStore → Program → Rel → Program × Rel × ArtifactStore
  theory_eq : ∀ A P q, (run A P q).1.theory = P.theory
  equiv : ∀ A P q, P.WellFormed q →
    GRel.Equiv P.theory ((run A P q).1.sem (run A P q).2.1) (P.sem q)

def Preprocessor.id : Preprocessor where
  run A P q := (P, q, A)
  theory_eq _ _ _ := rfl
  equiv _ P q _ := GRel.Equiv.refl _ (P.sem q)

structure Rung where
  pre : Preprocessor
  rt : Runtime

/-! ## Properties every rung proves (Tier 0)

They are stated for the runtime against the program and query it is run on,
which is the output of the rung's preprocessor. -/

namespace Runtime

variable (R : Runtime)

/-- Every emitted answer claims only what the query does: each of its ground
triples is backed by a triple of the query with the same pair and a store no
stronger under the program's theory (`GRel.Backed`). An engine may therefore
rewrite an answer's store by the theory. -/
def Sound : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n, (a.den).Backed P.theory (P.sem q)

/-- Every derivable span is covered by a single emitted answer after
finitely many steps, unless every ground instance of it carries a store the
theory refutes (such a span is observably empty, so an engine may prune it).
Coverage is up to refutation (`Span.CoversLive`): each ground triple of the
span whose store the theory cannot refute is matched by a triple of the answer
with the same pair and a store that is no larger. An engine may therefore
instantiate an answer by an equation its theory forces. -/
def Complete : Prop :=
  ∀ P q, P.WellFormed q → ∀ s, Derives P q s →
    s.Dead P.theory ∨ ∃ n, ∃ a ∈ R.emitted (R.init P q) n, a.CoversLive P.theory s

/-- If the runtime reports it is done, the answers it emitted cover the
query: they are equivalent to it under the program's theory
(`GRel.Equiv`), so they carry the same pairs within every store the theory
cannot refute. -/
def HonestExhaustion : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, R.Halts (R.init P q) n →
    GRel.Equiv P.theory (P.sem q) (⋃ a ∈ R.emitted (R.init P q) n, a.den)

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
