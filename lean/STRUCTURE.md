# Structure of the Lean development

The development is layered so that a new rung proves only what is new about
its machine. Everything below `Rungs/R00N/` is shared; a rung imports it and
never restates it.

```
Trusted/        the specification: syntax, semantics, Runtime, Rung, the Tier-0 properties,
                the properties every rung keeps (Properties.lean), the cost monad (CostMonad.lean),
                the charged primitives (Charged.lean), the kernel an engine is written
                against (Kernel.lean), what another kernel must prove to stand in for
                it (KernelRung.lean),
                and the cost model (Cost.lean) by which rungs from R002 on are judged:
                cost is coverage latency, the ticks until an emitted answer covers a
                ground pair, and never depends on a query halting
Theory/         constraint theories and firing
Kernel/         the executable kernel (match, solve, span, refute) and its proofs
SpanLayer/      span-level semantics, derivations, coverage vocabulary
Lib/            facts about lists and greatest fixpoints that mention no rwlog type
Rungs/Framework generic theorems about any Runtime / Rung
Rungs/Tabled/   the tabled round machine, open in its unfolding oracle: written against the
                kernel (Gen.lean) and read in the cost monad (Machine.lean)
Rungs/Mirror/   a machine run on a query and on its mirror image side by side, for any machine:
                written against the kernel (Gen.lean) and read in the cost monad (Machine.lean)
Rungs/Directed/ goal-directed tables: the tabled machine with no unfolding race and no
                completion, pushing boundaries as answers arrive. Sound, not complete; not a rung
Rungs/Hedge/    two machines run side by side, balanced by ticks, for any two machines; not a rung
Rungs/R00N/     one rung: Engine, (Spec), proofs
Conformance/    behaviours pinned against the Rust implementation
AxiomAudit.lean every headline and shared theorem, checked to use only the three standard axioms
Tests/          executable runs per rung
```

`SYMMETRIC_ENGINE.md` is the design note for the engine of milestone M6: what it
is, what was measured, and what the trusted files and the kernel must provide
for it. `Tests/MiddleRuns.lean` holds its measurements on R004 and R005.

## What is shared, and where to look first

| You need | It is in | Entry points |
|---|---|---|
| The coverage checker is exact | `Kernel/Covers.lean` | `Span.covers?_iff`, `covers?_refl/trans/swap/congr`, `Span.Equiv.*`, `matchAll_complete` |
| Interfaces of a span | `Kernel/Iface.lean` | `Span.storeOn`, `rightIface`, `leftIface`, `comp_rightIface`, `rightIface_covers` |
| Refutation and simplification are exact | `Kernel/RefuteCorrect.lean` | `Theory.refutes?_sound`, `Theory.simplify_exact`, `Theory.present_exact`, `Theory.simplify_stable` |
| Simplification respects coverage and converse | `Kernel/SimplifyMono.lean` | `SimpLaws`, `simpLaws_of_wf`, `SimpLaws.respects`, `simplify_swap` |
| Live spans, live compose and meet | `Kernel/Live.lean` | `live`, `liveO`, `composeLive`, `meetLive`, `liveO_spec`, `live_swap` |
| Maximal answers and freshness | `Kernel/Maxima.lean` | `maxima`, `fresh` and their lemmas |
| Exact covers under composition | `Kernel/ExactCover.lean` | `Under`, `XC`, `compose_mono` |
| Coverage modulo a theory | `SpanLayer/Modulo.lean` | `LCov`, `LEq`, `Live`, `DeadR`, `Backed`, `Ref`, `DC`, `GCov`, `GEq`, `Dom` |
| Chains of spans | `Kernel/Chain.lean` | `Span.denO_chain`, `Span.chain_isSome_iff`, `chain_isSome_fuse`, `chain_eq_none_of_compose`, `GRel.chain` |
| Unfolding equations | `Rungs/R000/Unfold.lean` | `unfoldN_succ`, `unfoldN_succ'`, `unfoldN_call`, `unfoldN_add`, `unfoldN_or/and/seq/conv`, `unfoldN_dual` |
| Shape of normal-form products | `Rungs/R000/Products.lean` | `joinSeq_cases`, `joinSeq_ne_nil`, `mkAnd_ne_nil`, `norm_ne_nil` |
| Sizes charged by the cost model | `Kernel/Size.lean` (and `Term.size_pos` in `Kernel/Solve.lean`) | `Span.size_pos`, `Span.size_swap`, `Rel.size_pos` |
| Sums over lists | `Lib/List.lean` | `sum_flatMap_map`, `sum_filterMap_map`, `le_sum_map_of_mem`, `sum_map_le` |
| Converse of a program | `SpanLayer/Dual.lean` | `Program.sem_dual` |
| Greatest fixpoints by iteration | `Lib/Gfp.lean` | `gfpFrom`, `gfpFrom_closed`, `subset_gfpFrom` |
| Insertion sort by a strict order | `Lib/Insert.lean` | `insertBy`, `sortBy`, `sortBy_eq` (a duplicate-free list sorts to the ordered list with the same members) |
| First occurrences of a list | `Lib/Firsts.lean` | `addNew`, `addAll`, `firsts`, `firsts_eq_eraseDups`, `addAll_firsts`, `addAll_flatMap_firsts`, `addAll_flatMap_congr` |

## The rung framework

`Rungs/Framework/` is about an arbitrary `Runtime`, so it applies to every
rung unchanged.

* `Runtime.lean`: runs, prefixes, halting, `stateAfter`, traces.
  `Runtime.finite_answers`, `halts_iff_stateAfter`, `emitted_eq_flatten_trace`.
* `Trace.lean`: `StepEquiv` / `TraceEquiv`, and simulation.
  Give a relation `Sim` on states with `Step.Rel E Sim (R.step s) (R'.step s')`
  and get `Runtime.trace_of_sim`, `halts_iff_of_sim`, `emitted_of_sim`.
  This is how the symmetry theorems (converse, `or` commutativity) are proved.
* `Tier0.lean`: `Runtime.Tier0Cert`. A rung proves three facts about its own
  machine (each emitted answer is covered by the semantics; each derivation is
  eventually dominated by an emitted answer; at halt the answers dominate
  everything) and receives `Sound`, `Complete` and `HonestExhaustion` from
  `Tier0Cert.tier0`. `derivationGeneral_of_ref` and `theory_mono_answers` are
  generic too.
* `Transfer.lean`: moving theorems between rungs. `SameRun R' R` says two
  runtimes emit equivalent answers and halt together; it carries `Tier0`,
  `DerivationGeneral` and `TerminatesOn` from `R` to `R'`
  (`SameRun.tier0`, `SameRun.terminatesOn`), and `SameRun.of_sim` builds it
  from a simulation. `Rung.sound`, `Rung.pointComplete` and `Rung.honest`
  carry runtime theorems through a preprocessor.

* `Cost.lean`: the cost monad of `Trusted/Cost.lean` is a lawful monad; the
  value of each free traversal is the list function of the same name
  (`Cost.mapL_val`, `filterL_val`, `anyL_val`, `foldL_val`, ...); the ticks of
  the total traversals are sums (`mapL_ticks`, ...) and of the early-exit ones
  are bounded by the sum; `CostedRuntime.spent_mono`, `spent_of_halts`.

* `CostCalculus.lean`: `Cost.Costs m v c` (`m` returns `v` and spends at most
  `c`), with one rule per monad operation and per traversal (`Costs.bind`,
  `Costs.mapL`, `Costs.foldL`, ...), so the value and a cost bound of a long
  `do` block are derived together.

* `CostSpec.lean`: `Cost.Spends m c Q` (`m` spends at most `c` and its value
  satisfies `Q`), for a computation whose value is only described, with the
  same rules (`Spends.bind`, `Spends.mapL`, `Spends.mapL_zip`), and bounds on
  the ticks of each traversal from a bound on each member
  (`anyL_ticks_le_mul`, ...).

* `Latency.lean`: how the improvement statements of `Trusted/Cost.lean`, which
  measure the ticks until an answer covers a ground pair, are established.
  `Simulates.of_steps` (the new machine covers each answer of the old one,
  step by step, at a bounded cost), `CostedRuntime.coversWithin_of_halts` (on
  an input that halts, an honest machine has covered every pair of the query
  by the time it halts, so a separating family that halts needs only its
  target pairs to be in the denotation), and
  `CostedRuntime.le_spent_of_covered` (a machine that has emitted nothing in
  `N` steps has paid for `N + 1` before it covers anything).

`Rungs/Tabled/` is the base for costed rungs that keep R001's tables and change
something else. `Machine.lean` is R001's machine written in the cost monad
with the unfolding race left to an `Oracle`; `Tabled.round_split` isolates
what a round spends asking the oracle. `Exact.lean` proves
`Tabled.machine_runtime`: with any oracle whose value is R001's unfolding race
(`Oracle.Exact`), the machine's runtime is `R001.runtime`, so all of R001's
theorems apply. A rung that changes only the oracle (as R002 does) proves its
oracle exact and bounds its ticks; nothing about tables is reproved.
`Repeats.lean` covers an oracle that returns the same answers with some
repeats of earlier spans left out (`Oracle.SkipsRepeats`, in particular
`Oracle.ExactModRepeats`: R001's answers or their `eraseDups`). The tables
drop repeats themselves, so the machine is still `R001.runtime`
(`Tabled.machine_runtime_modRepeats`), the rest of a round costs no more
(`Tabled.rest_skips`), and a per-call bound on the oracle becomes a bound on
the whole run (`Tabled.spent_le_of_skips`). R003 uses it.

`Rungs/Framework/Race.lean` defines `Cost.race` and proves what it returns and spends
(`Cost.race_val`, `Cost.race_ticks`, and from below `Cost.le_race_ticks`), for
any two computations. A rung that adds one more way to answer the unfolding
race races it against the previous rung's unfolder, as R004 does: simulation
within 7 times is then `Tabled.spent_le_of_skips`, and a lower bound on the
previous rung's first round is `le_race_ticks` on its two halves.

`Rungs/Framework/RaceWinner.lean` says which computation a race returns and
what it costs as functions of the two costs alone (`Cost.firstWins`,
`Cost.raceCost`, `Cost.race_eq`), with `raceCost_le` (at most 7 times the
cheaper) and `winner_le_raceCost`. Use it when the proof must follow which
side won.

`Rungs/Framework/Direction.lean` is how `DirectionFree` (`Trusted/Cost.lean`)
is established. `CostBisim A B E rel`: two machines go through related states,
every step at the same cost, emitting answers related by `E`; it gives equal
`spent`, related traces, and `CostBisim.simulates` (simulation within what the
first states cost more). `ConvBisim C rel` and `DualBisim C rel` are that for
one machine's runs on `conv q` and `q`, and on the mirror image and the query;
`DirectionFree.of_bisim` turns the two into `DirectionFree`.
`simulates_of_trace` gives a simulation from traces that agree step for step
and a bound on what the new machine has paid by the old one's step. The file
also has the facts about `dual` (`RelOf.dual_dual`, `size_dual`,
`ProgramOf.WellFormed.dual`).

`Rungs/Mirror/` is the mirrored machine of any machine `C`: `C` on the query
and `C` on the mirror image, raced step by step (`Gen.lean` says what a step
does). It asks of `C`: `Runtime.DualTrace`, a `ConvBisim`, and equal first
states for swapped and regrouped `|`. It gives:
`Mirror.trace_go` / `trace_start` (it emits what `C` emits, step for step, up
to order and equivalence), `Mirror.spent_le` / `paid_le_min` (the first `n`
steps cost at most `2 n` rounds of at most 14 times the cheaper run),
`Mirror.spent_ge` / `paid_ge_min` (and at least the cheaper run),
`Mirror.dualBisim` and `convBisim` (its runs on the mirror image and on the
converse cost exactly what its run on the query costs, step for step),
`Mirror.directionFree`, `Mirror.simulates` (it simulates `C` within
`Mirror.bound`), `Mirror.keeps` (it has every property of `Runtime.Keeps`
that `C` has), `Mirror.step_from` (each step emits what one step of one of
the two runs emits, at no less than its cost) and `Mirror.covered_first`.
`Rungs/Tabled/Direction.lean` supplies what it asks for the tabled machine
with any oracle (`Tabled.convBisim`, `start_or_comm`, `start_or_assoc`,
`init_ticks`, `step_pos`). R005 is the mirrored machine of R004; a later rung
that mirrors another machine, or runs something beside a mirrored machine,
reuses all of it.

`Rungs/Directed/` is the goal-directed tabled machine (`Gen.lean` says what
it does): a sequence restricted at one end (a boundary, or a factor that is a
span) is evaluated from that end, each answer's interface pushed into the
other factor as it arrives, with no join against the free factor, no
unfolding race and no completion. It is written against the kernel and read
in the cost monad (`Directed.engine_costed`). It is sound and
derivation-general (`Directed.emitted_ref`, `sound`, `derivationGeneral`),
it is not complete and never reports exhaustion, so it is a component and
not a rung. `Tests/DirectedRuns.lean` measures it beside R004: constant cost
on a family where R004's free factor costs `4 ^ k`, and hundreds of times
R004's cost on a family where driving from the restricted end is the wrong
order. The second is why it cannot stand alone.

`Rungs/Hedge/` is `Hedge.machine A B` for any two machines: each step races
the next step of `A` against the next step of `B`, the machine that took the
last steps handicapped by the length of its streak, emits `A`'s answers not
covered by what `B` gave and `B`'s answers that are plain (conjoined with
themselves they do not grow) and new, and halts only when `A` does. It asks that a step's
ticks bound the sizes of what it emits (`Hedge.tabled_step_sizes`,
`directed_step_sizes` supply this for the tabled and the goal-directed
machines). It gives: `Hedge.follows_first` and `follows_second` (whatever
`A`, or `B`, has emitted is covered within an explicit polynomial of what
that machine paid, and exhaustion follows `A`), the baseline properties that
do not mention traces from `A`'s alone plus soundness and derivation
generality of `B` (`Hedge.sound`, `derivationGeneral`, `noSubsumed`,
`honest`, `complete`, `terminatesWhere`, `emptySide`), and the trace laws
from costed bisimulations of `A` and of `B` (`Hedge.step_sim`,
`convTrace_of`, `dualTrace_of`). `Framework/Reach.lean` is the runs of any
runtime as a relation between states, which these proofs induct on.

An engine cannot declare its own cost. `Trusted/Kernel.lean` is the class
`Kernel S M`: an abstract type of spans, an abstract monad, and the operations
on spans, each returning in the monad. An `Engine` (`Trusted/Cost.lean`) is a
machine written for every kernel, so it can only touch a span through those
operations and can only spend what they charge; `Engine.costed` is the engine
at `Kernel.std`, the kernel of the language, where each operation is the
charged primitive of `Trusted/Charged.lean`. `Advances` and `Admits` are
stated on engines.

`Kernel.std` is the specification kernel: its values are the specification
and its charges are postulated. A kernel rung (`Trusted/KernelRung.lean`) is
another `Kernel Span Cost` that returns the same values (`Kernel.Refines`)
and whose charges are theorems about a machine; `Engine.costedAt` is an
engine at such a kernel. The first one is `rustKernel`
(`verified/lean/RwLogVerified/Kernel.lean`): the charge of each operation on
terms is the tick bound proved of the Rust function on the store of
`verified/rust/src/store.rs`. See `verified/README.md`.

Each machine is therefore written twice, in the same words. `Gen.lean`
(`Rungs/Tabled/`, `Rungs/Mirror/`, `Rungs/R002/` to `R004/`) is the engine,
against the kernel.
`Machine.lean`, `Unfold.lean`, `Shared.lean` and `Pruned.lean` are the same
text in `Cost` with the charged primitives written out, and all proofs are
carried out on them. `Reading.lean` next to each proves the two equal,
definition by definition (`Tabled.engine_costed`, `Mirror.mirrored_costed`,
`R00N.engine_std`), by
unfolding both and rewriting with the equalities already proved; the tactic
`same_text` (`Rungs/Framework/TraverseStd.lean`) closes what is left. A new
rung writes its oracle in both forms, proves them equal the same way, and
states `costed_engine` and `admits` on its engine.

A rung whose machine is equal to an earlier one as a `Runtime` (R002 against
R001) uses `SameRun.of_eq`, or simply rewrites.

One caveat for rungs with a real preprocessor: `Complete` (one emitted answer
covers the derived span) does not survive preprocessing in general, only
`PointComplete` does. State completeness of the whole rung pointwise.

## Adding rung R00N

1. Put the machine in `Rungs/R00N/Engine.lean` and its tests in
   `Tests/R00NRuns.lean`. Touch nothing outside `Rungs/R00N/` except the
   import list in `RwLog.lean`, the audit lines in `AxiomAudit.lean`, and
   genuinely rung-independent lemmas, which go in the shared layer.
2. If the rung is an optimisation of an earlier rung, prove a simulation and
   use `SameRun.of_sim`; Tier 0 and termination then come from the earlier
   rung with no further work.
3. Otherwise build a `Tier0Cert`. `R000/Correct.lean` (`R000.cert`) is the
   small example, `R001/Proofs/Tier0.lean` (`R001.cert`) the large one.
4. Use kernel theorems by name. If a proof needs a fact about `covers?`,
   `simplify`, `compose`, `meet` or lists that is not rung-specific, add it to
   `Kernel/`, `SpanLayer/` or `Lib/`, not to the rung.
5. The shared layers never import a rung: `Kernel/`, `SpanLayer/`, `Lib/` and
   `Rungs/Framework/` import nothing under `Rungs/R00N/`. A generic definition
   a rung needs goes in the shared layer, with its lemmas.
6. A rung from R002 on is admitted by these statements in its `Spec.lean`,
   and by nothing weaker:
   * `keeps : runtime.Keeps R001.runtime` (`Trusted/Properties.lean`): every
     property of the proper baseline, stated for any runtime, and termination
     wherever R001 terminates. Properties about one machine's internals
     (prompt pruning, table invariants) are not in that list; a rung whose
     machine is not R001's restates and proves them for its own state.
   * `costed_engine : engine.costed = costed`: the machine the proofs are about
     is the rung's engine at the kernel of the language.
   * `admits : Admits Old New bounds dirBound pre fam tgt`
     (`Trusted/Cost.lean`), on the engines. It has two parts.
     `Advances`: the rung as a whole (machine run on the preprocessed input)
     simulates its predecessor within `bounds.sim`, on a family of size at
     most `bounds.size k` it covers the targets within `bounds.hi k` while
     the predecessor has paid `2 ^ k`, and preprocessing costs at most `pre`.
     `bounds` is six numerals written in the Spec. Prove `Simulates` and
     `Separates` with whatever bounds are natural and bring them to this form
     with `Simulates.mono` and `Separates.mono`.
     `direction`: the rung's cost does not depend on the direction a query is
     written in (`DirectionFree`): on the mirror image of a query in the
     mirrored program, and on its converse, it covers the same pairs within
     `dirBound.fn` of what it pays on the query, and the other way round.
     `Admits.of_id` covers a rung without preprocessing, after rewriting both
     engines to their readings.
     R002 to R004 state only `advances : Advances ...`: their cost depends on
     direction, so they are not admitted. R005 is the first rung that is. A
     rung that is not built on a mirrored machine proves `DirectionFree` for
     its own machine, with `DirectionFree.of_bisim` if its runs from the two
     ends cost the same step for step.
   * Building the first state (`CostedRuntime.init`) and preprocessing
     (`Preprocessor.run`) are charged computations. A coverage test and a
     simplification are charged for their search (`Charged.coversWork`,
     `Theory.saturateWork`), which is nothing when the covering span has no
     store and when the theory is empty.
7. Add each headline theorem to `AxiomAudit.lean`. The build is
   `lake build --wfail`: no `sorry`, no warnings, no new axioms.
