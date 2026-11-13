/-
# Rung R004: what must be proved

Every property is stated here as a `Prop` in the `R004.Obligation` namespace
and nothing in this file is proved: an obligation is discharged by a theorem
`R004.<name> : Obligation.<name>` in another file, and `AxiomAudit.lean` lists
the discharged ones.

R004 is judged against R003 by cost (`Trusted/Cost.lean`).

* **Same machine.** The evaluation pruned from the right computes R001's
  unfolding race with the repeated answers removed (`pruned_exact`), so
  R004's unfolder gives R001's verdict and R001's answers, with or without the
  repeats (`unfolder_exact`). The tabled machine drops repeats itself, so
  R004's runtime *is* R001's (`runtime_eq`): the same states, the same steps,
  the same trace. Every theorem about `R001.runtime` is then a theorem about
  `R004.runtime` by rewriting; the three every rung must state are stated
  (`sound`, `complete`, `honest_exhaustion`).
* **Never much worse.** R004 simulates R003 within a factor of 7: every pair
  R003 has covered, R004 covers at no more than 7 times the cost, and likewise
  for exhaustion (`simulates`).
* **Exponentially better on a family.** `sepFam k` is `@a | (gen k ; @q)`:
  one answer, beside a sequence of `k + 1` choices between two wrappers
  followed by a test that no wrapped term passes. R004 emits the answer
  within a linear bound, while R003 has paid at least `2 ^ k` before it emits
  anything (`separates`): its walk and its shared evaluation both build all
  `2 ^ (k + 1)` wrapped terms before the test is reached.

## What is not claimed

* **No mirror bound.** The pruning this rung adds works from the right end of
  a sequence only, and what it races against (R002's walk) prunes from the
  left by a different test, so the cost of a query and the cost of its
  converse are not claimed to be within a polynomial of each other, and no
  such obligation is stated.
* **Only the unfolding race is improved.** The race yields answers only for a
  goal whose unfolding is final. A goal that never becomes final is answered
  by the tables, which this rung leaves as they are in R001: they still
  evaluate the unconstrained side of a sequence in full.
-/
import RwLog.Rungs.R003.Engine
import RwLog.Rungs.R004.Engine

namespace RwLog

namespace R004

/-! ### The separating family

`bit` is `$x -> (0 $x) | $x -> (1 $x)`: wrap the term in one of two symbols.
`gen k` is `k + 1` of them in a row, which relates every term to its
`2 ^ (k + 1)` wrappings, all different. `gen k ; @q` follows it by a test
that no wrapped term passes, so it has no answers; the query is that beside
`@a`, whose one answer `a -> a` is the target. There are no definitions and
no theory. -/

/-- `$x -> (f $x)`. -/
def wrap (f : Sym) : Span := ⟨.var 0, .app (.sym f) (.var 0), []⟩

def bit : Rel := .or (.span (wrap "0")) (.span (wrap "1"))

def gen : Nat → Rel
  | 0 => bit
  | k + 1 => .seq bit (gen k)

def sepRel (k : Nat) : Rel := .or (.at_ (.sym "a")) (.seq (gen k) (.at_ (.sym "q")))

def sepFam (k : Nat) : Program × Rel := (⟨[], []⟩, sepRel k)

/-- The pair the answer `a -> a` relates. -/
def sepTarget : PRel := {(.sym "a", .sym "a")}

namespace Obligation

/-! ### Same machine -/

/-- The evaluation pruned from the right computes R001's unfolding race: the
same verdict, and the same spans in the same order with the repeats of
earlier ones removed. -/
def pruned_exact : Prop :=
  ∀ P d g, (pruned P d g).val =
    (R001.unfoldFinal P d g, (R001.unfoldAnswers P d g).eraseDups)

/-- R004's unfolder gives R001's verdict and R001's answers, with or without
the repeats. -/
def unfolder_exact : Prop :=
  ∀ P d g, (unfolder P d g).val.1 = R001.unfoldFinal P d g ∧
    ((unfolder P d g).val.2 = R001.unfoldAnswers P d g ∨
      (unfolder P d g).val.2 = (R001.unfoldAnswers P d g).eraseDups)

/-- R004's runtime is R001's. -/
def runtime_eq : Prop := runtime = R001.runtime

/-- P0.1 to P0.3 for R004. -/
def sound : Prop := runtime.Sound
def complete : Prop := runtime.Complete
def honest_exhaustion : Prop := runtime.HonestExhaustion

/-! ### Never much worse -/

/-- One race of R004 costs at most 7 times R003's unfolder, and at most 7
times the evaluation pruned from the right. -/
def unfolder_ticks : Prop :=
  ∀ P d g, (unfolder P d g).ticks ≤ 7 * min (R003.unfolder P d g).ticks (pruned P d g).ticks

/-- R004 simulates R003 within a factor of 7. -/
def simulates : Prop := Simulates R003.costed costed fun c _ => 7 * c

/-! ### Exponentially better on a family -/

/-- On `sepFam k`, an input of size at most `12 (k + 2)`, R004 has covered
the pair `(a, a)` within `1000 (k + 2)` ticks, and R003 has paid at least
`2 ^ k` at any step at which it has covered it. -/
def separates : Prop :=
  Separates R003.costed costed sepFam (fun _ => sepTarget) (fun k => 12 * (k + 2))
    (fun k => 2 ^ k) fun k => 1000 * (k + 2)

end Obligation

end R004

end RwLog
