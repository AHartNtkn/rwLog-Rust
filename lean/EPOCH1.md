# Epoch 1 of the ladder

The git tag `epoch-1` (commit `7909828`) is the last commit at which rungs R000 to R005 all build
together, with every theorem named below proved and listed in
`AxiomAudit.lean` (three standard axioms only, `lake build --wfail`). The
commit after it removes R000 to R004 from the build. This file says what the
theorems at the tag are about, so nobody reads them as claims about a later
cost model or a later admission rule.

To read or build epoch 1: `git checkout epoch-1`, then `lake build --wfail` in
`lean/`. Paths below are paths at the tag.

Epoch 1 is frozen. Its rungs keep their theorems. They are not repaired when a
trusted statement changes, and they are not judged again against a later
requirement.

## What the theorems are about

### The cost model: sizes, charged by postulate

`Trusted/Charged.lean` gives every operation on spans a charge that is a fixed
function of the sizes of its arguments, and of its result when it builds one.
These charges are definitions. Nothing derives them from a machine.

| Operation | Charge at the tag |
|---|---|
| `compose`, `meet` | sizes of both spans and of the result |
| `composable` (chain test) | sizes of the spans in the chain |
| `eq`, `eqRel` | sizes of both arguments |
| `canon` | size of the expression |
| `rightBound`, `leftBound` | size of the span |
| `covers` | sizes of both spans, plus the matching search (`coversWork`) |
| `simplify` | per stage, theory size times span and closure size, plus the firing search (`simplifyCharge`) |
| swapping a span, reading a size | free |

A term costs its size wherever it is used, so sharing is never credited.
An engine (`Trusted/Cost.lean`, `Engine`) is written against the abstract
kernel of `Trusted/Kernel.lean` and its cost is its text read at `Kernel.std`,
whose operations are these charged primitives. Cost is coverage latency: the
ticks a machine has spent by the first step at which an emitted answer relates
a given ground pair (`CoversWithin`). It never depends on a query halting.

Every cost theorem of epoch 1 is a statement about this model and no other.

What is known to be wrong with it, found before the tag and left as found:

* The charges are below what a machine spends. PR 42 derived the term
  operations on a Rust store (`verified/`): the worked composition costs 257
  ticks there against 38 postulated.
* `composable` is charged without the compositions it performs.
* `canon` is charged its argument's size although it sorts the branches of `|`
  (roadmap L03).
* Each machine from R002 on is written twice, as an engine and as a copy in
  `Cost` on which the proofs run, joined by a `Reading.lean` (roadmap L04).

`Trusted/KernelRung.lean` and `rustKernel` (PR 42) are at the tag too, but no
epoch 1 rung is proved at a kernel other than `Kernel.std`.

### The admission rule

`Trusted/Cost.lean`, as it stood:

* `Simulates Old New p`: whatever `Old` has covered after paying `c` on an
  input of size `n`, `New` covers within `p c n`, and likewise for exhaustion.
* `Separates Old New fam tgt size lo hi`: on one family of inputs `fam k` of
  size at most `size k`, `New` covers the targets within `hi k` while `Old` has
  paid at least `lo k` before covering any.
* `Improves` is both with explicit numerals (`Bounds`): the simulation and
  `hi` polynomial, `lo = 2 ^ k`. `Advances` is `Improves` for a whole rung,
  with a recorded cost of preprocessing.
* `DirectionFree C p`: `C` on a query, on its converse and on its mirror image
  simulate one another within `p`.
* `Admits` is `Advances` together with `DirectionFree`.

So epoch 1 knows one kind of win, exponential in time. The separation is on
one hand-picked family, not on a decidable class of programs, and nothing says
it survives inside a larger program (roadmap L02). Space is not measured.

### The kept properties

`Trusted/Properties.lean`: `Runtime.Keeps Base` collects soundness,
completeness, honest exhaustion, derivation generality, termination wherever
`Base` terminates, the trace laws for `|`, converse and the mirror image,
empty sides, theory monotonicity and no subsumed answer. All are stated for
answers that are spans. Rungs from R002 on prove `Keeps R001.runtime`.

## The rungs and their headline theorems

Each rung's statements are in `Rungs/R00N/Spec.lean`, namespace
`R00N.Obligation`; the theorem `R00N.<name>` discharges `Obligation.<name>`.

### R000, the naive baseline

Round `k` unfolds every call `k` times, normalises, and emits what the
products derive. `Rungs/R000/`.

* `R000.sound`, `complete`, `honest_exhaustion` (from `R000.cert`).
* `R000.terminates` with `terminates_recursionFree` and
  `terminates_callTreeFinite`.
* Answers and termination are unchanged by the mirror image, by swapping and
  regrouping `|`, and under a larger theory (`dual_answers`,
  `or_comm_answers`, `or_assoc_answers`, `theory_answers` and the matching
  `_terminates`).

### R001, the proper baseline: tables

Goals with boundaries, one table per goal, an unfolding race, completion.
`Rungs/R001/`. It has no cost statement of its own: its cost is
`R002.baseline`.

* Tier 0: `R001.sound`, `complete`, `honest_exhaustion`,
  `derivation_general`, `no_subsumed`, `prompt_pruning`,
  `theory_mono_answers`.
* Tables: `table_sound`, `completion_sound`, `table_fair`, `gderives_same`.
* Termination: `terminates_iff_cert` (the termination class exactly),
  `tabling_termination`, `terminates_finitelyNormalising`,
  `addition_fixed_modes`, `empty_side`, `finite_side_seq_left`,
  `finite_side_seq_right`, `finite_side_and`.
* Traces, step for step: `conv_trace`, `dual_trace`, `or_comm_trace`,
  `or_assoc`.
* `R001.keeps : runtime.Keeps runtime`.
* `R001.finite_answers` holds of every runtime and obliges nothing (roadmap
  L05). It is removed after the tag.

### R002, unfolding on demand

`R002.runtime_eq`: the runtime is R001's. Against R001 (`R002.baseline`):

* `R002.simulates`: within `5 * c ^ 3 * (n + 2) ^ 3`.
* `R002.separates`: on `sepFam`, the pair `(z, z)` within `500 * (k + 5) ^ 4`
  while R001 has paid `2 ^ k`. Also `separates_exhaustion`.
* `R002.advances` with `bounds = ⟨40, 6, 11, 1, 312500, 4⟩`, `R002.keeps`,
  `R002.costed_engine`.

### R003, a shared evaluation raced against the walk

`R003.runtime_eq`: the runtime is R001's. Against R002:

* `R003.simulates`: within `7 * c`.
* `R003.separates`: on `k + 1` choices that lead to the same place, within
  `2000 * (k + 2) ^ 3` while R002 has paid `2 ^ k`. Also
  `separates_exhaustion`.
* `R003.advances` with `bounds = ⟨7, 1, 8, 1, 16000, 3⟩`, `R003.keeps`,
  `R003.costed_engine`.

### R004, an evaluation pruned from the right, raced against R003's unfolder

`R004.runtime_eq`: the runtime is R001's. Against R003:

* `R004.simulates`: within `7 * c`.
* `R004.separates`: on `@a | (gen k ; @q)`, within `1000 * (k + 2)` while R003
  has paid `2 ^ k`.
* `R004.advances` with `bounds = ⟨7, 1, 24, 1, 2000, 1⟩`, `R004.keeps`,
  `R004.costed_engine`.

R002, R003 and R004 advance and are not admitted: their cost depends on the
direction a query is written in (`R005.r004_forward` and `r004_mirror` show it
for R004).

### R005, R004 on the query and on its mirror image, side by side

`Engine.mirrored` of R004 (`Rungs/Mirror/`). The only admitted rung of epoch 1.

* `R005.same_trace`: it emits what R004 emits, step for step.
* `R005.keeps`, with `sound`, `complete`, `honest_exhaustion`.
* `R005.mirror_exact`, `conv_exact`, `direction_free` (within `c + 2`).
* `R005.simulates`: within `Mirror.bound`.
* `R005.separates`: on `bit ; (bit ; … ; (bit ; $x -> c))`, the pair `(z, c)`
  within a cubic bound while R004 has paid `2 ^ k`.
* `R005.admits` with `bounds = ⟨29, 2, 15, 1, 22400032, 3⟩` and
  `dirBound = ⟨2, 1⟩`, and `R005.costed_engine`.

### Shared libraries at the tag

`Rungs/Framework`, `Rungs/Tabled`, `Rungs/Mirror`, `Rungs/Directed` and
`Rungs/Hedge` are not rungs. `Rungs/Framework` stays on master; the tabled
and the mirrored machine are rewritten there against the derivation kernel,
and `Rungs/Directed` and `Rungs/Hedge` exist only at the tag. `STRUCTURE.md`
describes master.

## What master keeps after the tag

Master keeps the specification, the kernel, the shared libraries, and the
text of the machines R005 is made of (the unfolding of R000, the tabled
machine of R001, the unfolders of R002 to R004), with the theorems about them
that the shared libraries use. It keeps no proof that any rung advances on or
is admitted over another: those are at the tag. R005 is ported once, as the
yardstick the next engine is measured against (roadmap M4). `STRUCTURE.md`
says where each kept file went.
