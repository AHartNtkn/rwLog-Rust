/-
# Rung zero: the naive baseline

Round `k` unfolds every call of the query `k` times, normalizes the result
into products, and emits every span the products derive without further
unfolding. If no product still contains a call, the round is final and the
machine reports that it is done. Otherwise it starts round `k + 1` from the
query again.

This is deliberately naive: each round redoes all earlier work, and answers
found in one round are emitted again in later rounds. Order and multiplicity
carry no meaning, so this is correct; avoiding the waste is work for later
rungs.
-/
import RwLog.Rungs.R000.NormalizeCorrect
import RwLog.Trusted.Engine

namespace RwLog

namespace R000

/-- The products of round `k`. -/
def products (P : Program) (q : Rel) (k : Nat) : List (List Rel) :=
  norm false (unfoldN P k q)

/-- The spans emitted in round `k`. -/
def roundSpans (P : Program) (q : Rel) (k : Nat) : List Span :=
  (products P q k).flatMap fun p => derivs (toRel p)

/-- Round `k` is final when no product contains a call. -/
def roundFinal (P : Program) (q : Rel) (k : Nat) : Bool :=
  (products P q k).all fun p => (toRel p).calls.isEmpty

structure State where
  P : Program
  q : Rel
  round : Nat
  queue : List Span

def State.start (P : Program) (q : Rel) (k : Nat) : State := ⟨P, q, k, roundSpans P q k⟩

def step (st : State) : Step State :=
  match st.queue with
  | a :: rest => .emit a { st with queue := rest }
  | [] => if roundFinal st.P st.q st.round then .done else .tau (State.start st.P st.q (st.round + 1))

def runtime : Runtime where
  State := State
  init P q := State.start P q 0
  step := step

/-- Rung zero: no preprocessing, an empty artifact store, and the naive
runtime. -/
def rung : Rung where
  pre := Preprocessor.id
  rt := runtime

/-- The class of queries rung zero finishes on: some number of rounds of
unfolding leaves, after normalization, a finite union of spans (no product
still contains a call). This is phrased through rung zero's own normalizer;
`RwLog.R000.Termination` proves it contains every query whose call tree is
finite, in particular every recursion-free query. -/
def FinitelyNormalising (P : Program) (q : Rel) : Prop :=
  ∃ k, ∀ p ∈ norm false (unfoldN P k q), (toRel p).calls = []

end R000

end RwLog
