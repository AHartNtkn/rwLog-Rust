/-
# Rung R003: what must be proved

Every property is stated here as a `Prop` in the `R003.Obligation` namespace
and nothing in this file is proved: an obligation is discharged by a theorem
`R003.<name> : Obligation.<name>` in another file, and `AxiomAudit.lean` lists
the discharged ones.

R003 is judged against R002 by cost (`Trusted/Cost.lean`).

* **Racing two computations.** `Cost.race` returns the result of one of the
  two (`race_val`) and spends at most 7 times what the cheaper one needs
  (`race_ticks`).
* **Same machine.** The shared evaluation computes R001's unfolding race with
  the repeated answers removed (`shared_exact`), so R003's unfolder gives
  R001's verdict and R001's answers, with or without the repeats
  (`unfolder_exact`). The tabled machine drops repeats itself, so R003's
  runtime *is* R001's (`runtime_eq`): the same states, the same steps, the
  same trace. Every theorem about `R001.runtime` is then a theorem about
  `R003.runtime` by rewriting; the three every rung must state are stated
  (`sound`, `complete`, `honest_exhaustion`).
* **Never much worse.** R003 simulates R002 within a factor of 7, step for
  step (`simulates`): every pair R002 has covered, R003 covers at no more than
  7 times the cost, whether or not the query ever halts.
* **Exponentially better on a family.** On `sepFam k`, a sequence of `k + 1`
  choices between two spans that lead to the same place, the query relates
  every term to `z`. R003 covers every such pair within a polynomial of `k`,
  while R002 has paid at least `2 ^ k` before it emits any answer
  (`separates`): its walk follows every one of the `2 ^ (k + 1)` ways through.
  The family happens to halt, and the same bounds hold for the report of
  exhaustion (`separates_exhaustion`).
-/
import RwLog.Rungs.R002.Engine
import RwLog.Rungs.R003.Engine

namespace RwLog

namespace R003

/-! ### The separating family

`twoWays` is `@z | $x -> z`: two spans that both end in `z`. A sequence of
`k + 1` of them has `2 ^ (k + 1)` products, which are two distinct spans, and
one answer, `$x -> z`, which covers the other. There are no definitions and no
theory. -/

def twoWays : Rel := .or (.at_ (.sym "z")) (.rw (.var 0) (.sym "z"))

def sepRel : Nat → Rel
  | 0 => twoWays
  | k + 1 => .seq twoWays (sepRel k)

def sepFam (k : Nat) : Program × Rel := (⟨[], []⟩, sepRel k)

/-- The pairs whose arrival is timed on `sepFam`: every term against `z`,
which is every pair the query relates. -/
def sepTarget : PRel := {x | x.2 = .sym "z"}

namespace Obligation

/-! ### Racing two computations -/

/-- The race returns the result of one of the two. -/
def race_val : Prop :=
  ∀ (α : Type) (x y : Cost α), (Cost.race x y).val = x.val ∨ (Cost.race x y).val = y.val

/-- The race spends at most 7 times what the cheaper of the two needs. -/
def race_ticks : Prop :=
  ∀ (α : Type) (x y : Cost α), (Cost.race x y).ticks ≤ 7 * min x.ticks y.ticks

/-! ### Same machine -/

/-- The shared evaluation computes R001's unfolding race: the same verdict,
and the same spans in the same order with the repeats of earlier ones
removed. -/
def shared_exact : Prop :=
  ∀ P d g, (shared P d g).val =
    (R001.unfoldFinal P d g, (R001.unfoldAnswers P d g).eraseDups)

/-- R003's unfolder gives R001's verdict and R001's answers, with or without
the repeats. -/
def unfolder_exact : Prop :=
  ∀ P d g, (unfolder P d g).val.1 = R001.unfoldFinal P d g ∧
    ((unfolder P d g).val.2 = R001.unfoldAnswers P d g ∨
      (unfolder P d g).val.2 = (R001.unfoldAnswers P d g).eraseDups)

/-- R003's runtime is R001's. -/
def runtime_eq : Prop := runtime = R001.runtime

/-- P0.1 to P0.3 for R003. -/
def sound : Prop := runtime.Sound
def complete : Prop := runtime.Complete
def honest_exhaustion : Prop := runtime.HonestExhaustion

/-! ### Never much worse -/

/-- One race of R003 costs at most 7 times the walk, and at most 7 times the
shared evaluation. -/
def unfolder_ticks : Prop :=
  ∀ P d g, (unfolder P d g).ticks ≤ 7 * min (R002.onDemand P d g).ticks (shared P d g).ticks

/-- R003 simulates R002 within a factor of 7. -/
def simulates : Prop := Simulates R002.costed costed fun c _ => 7 * c

/-! ### Exponentially better on a family -/

/-- `sepFam k` has size at most `8 k + 7`. On it, R003 has covered every pair `(t, z)` within `2000 (k + 2)³`
ticks, and R002 has paid at least `2 ^ k` at any step at which it has covered
one. -/
def separates : Prop :=
  Separates R002.costed costed sepFam (fun _ => sepTarget) (fun k => 8 * k + 7) (fun k => 2 ^ k)
    fun k => 2000 * (k + 2) ^ 3

/-- The same bounds for the report of exhaustion: R003 halts within
`2000 (k + 2)³` ticks, and R002 has paid at least `2 ^ k` whenever it has
halted. -/
def separates_exhaustion : Prop :=
  SeparatesExhaustion R002.costed costed sepFam (fun k => 8 * k + 7) (fun k => 2 ^ k)
    fun k => 2000 * (k + 2) ^ 3

/-- The numerals R003 is admitted with: simulation within `7 (c + n + 1)`,
the `k`-th input of size at most `8 (k + 1)`, covered within `16000 (k + 1)³`
ticks. -/
def bounds : Bounds := ⟨7, 1, 8, 1, 16000, 3⟩

/-- The admission statement: R003 improves on R002 with these numerals, on
`sepFam` and the pairs `(t, z)`. -/
def improves : Prop := Improves R002.costed costed bounds sepFam fun _ => sepTarget

/-- The admission of the rung: R003 above R002, neither with any
preprocessing, so preprocessing is recorded to cost nothing. -/
def admits : Prop :=
  Admits ⟨Preprocessor.id, R002.costed⟩ ⟨Preprocessor.id, costed⟩ bounds (fun _ => 0) sepFam
    fun _ => sepTarget

end Obligation

end R003

end RwLog
