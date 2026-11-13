/-
# Two machines side by side

`Hedge.machine A B` runs two costed machines on the same query and advances
one of them at each step: it races the next step of `A` against the next step
of `B` (`Cost.race`) and takes the step that finishes first. Whichever took
the last steps is handicapped by the length of its streak, so neither machine
can keep the other waiting by taking cheap steps for ever.

It reports what both machines find:

* an answer of `A` is emitted unless an answer of `B` emitted earlier covers
  it;
* an answer of `B` is emitted when it carries no constraints (`plain`) and no
  answer emitted earlier covers it. A coverage test in which either span has
  no constraints costs only the two sizes, so every comparison between the two
  machines' answers is bounded by what has been spent. An answer of `B` with
  constraints is not reported: `A` finds an answer covering it in its own
  time.

Only the two steps are raced. The comparisons are made after the race, by
whichever machine took the step, so a machine's side of the race costs what
that machine alone decides.

It is done when `A` is done. `B` is a second way of finding answers sooner and
is never relied on to find them all. When `B` is done the machine goes on
with `A` alone.
-/
import RwLog.Rungs.Tabled.Machine
import RwLog.Rungs.Framework.Race

namespace RwLog

open Cost

namespace Hedge

/-- The state of the pair: the two machines, whether `B` is still running,
which machine took the last step and how many it has taken in a row, every
answer emitted, and those of them that came from `B`. -/
structure State (α β : Type) where
  a : α
  b : β
  live : Bool
  last : Bool
  streak : Nat
  seen : List Span
  seenB : List Span

/-- The span carries no constraints: conjoined with itself it does not grow.
The test is made on the span and on its converse, so that it returns the same
and costs the same for a span and for its converse. -/
def plain (x : Span) : Cost Bool := do
  let z ← Charged.meet x x
  let z' ← Charged.meet x.swap x.swap
  pure ((match z with
      | some z => decide (z.size ≤ x.size)
      | none => false) &&
    (match z' with
      | some z => decide (z.size ≤ x.size)
      | none => false))

/-- The spans that no span of `old` covers. -/
def dropCovered (old xs : List Span) : Cost (List Span) :=
  filterL (fun x => do
    let b ← anyL (fun t => Charged.covers t x) old
    pure !b) xs

variable (A B : CostedRuntime)

/-- What a race returns: a step of `A`, or a step of `B` with its plain
answers (`none` when `B` is done). -/
abbrev Won := Step A.State ⊕ Option (List Span × B.State)

/-- The handicap of `A`: its streak, when it took the last step. -/
def padA (st : State A.State B.State) : Nat := if st.last then st.streak else 0

/-- The handicap of `B`. -/
def padB (st : State A.State B.State) : Nat := if st.last then 0 else st.streak

def sideA (st : State A.State B.State) : Cost (Won A B) := do
  tick (padA A B st)
  let r ← A.step st.a
  pure (.inl r)

def sideB (st : State A.State B.State) : Cost (Won A B) := do
  tick (padB A B st)
  let r ← B.step st.b
  match r with
  | .done => pure (.inr none)
  | .emit bs b' => do
    let ps ← filterL plain bs
    pure (.inr (some (ps, b')))

/-- A step of `A` was taken. -/
def afterA (st : State A.State B.State) (r : Step A.State) :
    Cost (Step (State A.State B.State)) :=
  match r with
  | .done => pure .done
  | .emit as a' => do
    let out ← dropCovered st.seenB as
    pure (.emit out { st with a := a', last := true,
                              streak := if st.last then st.streak + 1 else 1,
                              seen := st.seen ++ out })

/-- A step of `B` was taken. -/
def afterB (st : State A.State B.State) (r : Option (List Span × B.State)) :
    Cost (Step (State A.State B.State)) :=
  match r with
  | none => pure (.emit [] { st with live := false })
  | some (ps, b') => do
    let out ← Tabled.fresh st.seen ps
    pure (.emit out { st with b := b', last := false,
                              streak := if st.last then 1 else st.streak + 1,
                              seen := st.seen ++ out, seenB := st.seenB ++ out })

def step (st : State A.State B.State) : Cost (Step (State A.State B.State)) :=
  if st.live then do
    let r ← race (sideA A B st) (sideB A B st)
    match r with
    | .inl r => afterA A B st r
    | .inr r => afterB A B st r
  else do
    let r ← A.step st.a
    afterA A B st r

def init (P : Program) (q : Rel) : Cost (State A.State B.State) := do
  let a ← A.init P q
  let b ← B.init P q
  pure ⟨a, b, true, true, 0, [], []⟩

/-- The two machines side by side. -/
def machine : CostedRuntime where
  State := State A.State B.State
  init := init A B
  step := step A B

end Hedge

end RwLog
