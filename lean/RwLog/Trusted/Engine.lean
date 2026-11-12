/-
# The interface every rung implements

A rung is a *preprocessor* followed by a *runtime*.

* The preprocessor turns a program and a query into an ordinary program and
  query with the same meaning. It may read and extend a store of proven
  artifacts that is shared across programs. Rung zero's preprocessor is the
  identity and its store is empty.
* The runtime is a deterministic small-step machine: each step emits an
  answer span, takes a silent step, or reports that it is done.

The properties every rung must prove (soundness, completeness, honest
exhaustion) are stated here against the specification, so a rung cannot
weaken them.
-/
import RwLog.SpanLayer.Derives

namespace RwLog

inductive Step (S : Type) where
  | emit (a : Span) (s : S)
  | tau (s : S)
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
    | .emit a s' => let r := run s' n; (a :: r.1, r.2)
    | .tau s' => run s' n
    | .done => ([], true)

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
    | emit a s' => simp only [hs] at h ⊢; rw [ih h m]
    | tau s' => simp only [hs] at h ⊢; exact ih h m
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

/-- Every emitted answer denotes only triples of the query. -/
def Sound : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, ∀ a ∈ R.emitted (R.init P q) n, a.den ⊆ P.sem q

/-- Every derivable span is covered by a single emitted answer after
finitely many steps. -/
def Complete : Prop :=
  ∀ P q, P.WellFormed q → ∀ s, Derives P q s →
    ∃ n, ∃ a ∈ R.emitted (R.init P q) n, s.den ⊆ a.den

/-- If the runtime reports it is done, the answers it emitted cover the
query exactly. -/
def HonestExhaustion : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, R.Halts (R.init P q) n →
    P.sem q = ⋃ a ∈ R.emitted (R.init P q) n, a.den

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
