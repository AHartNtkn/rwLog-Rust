# Structure of the Lean development

The development is layered so that a new rung proves only what is new about
its machine. Everything below `Rungs/R00N/` is shared; a rung imports it and
never restates it.

```
Trusted/        the specification: syntax, semantics, Runtime, Rung, the Tier-0 properties,
                and the cost model (Cost.lean) by which rungs from R002 on are judged:
                cost is coverage latency, the ticks until an emitted answer covers a
                ground pair, and never depends on a query halting
Theory/         constraint theories and firing
Kernel/         the executable kernel (match, solve, span, refute) and its proofs
SpanLayer/      span-level semantics, derivations, coverage vocabulary
Lib/            facts about lists and greatest fixpoints that mention no rwlog type
Rungs/Framework generic theorems about any Runtime / Rung
Rungs/Tabled/   the tabled round machine in the cost monad, open in its unfolding oracle
Rungs/R00N/     one rung: Engine, (Spec), proofs
Conformance/    behaviours pinned against the Rust implementation
AxiomAudit.lean every headline and shared theorem, checked to use only the three standard axioms
Tests/          executable runs per rung
```

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
(`Cost.race_val`, `Cost.race_ticks`), for any two computations.

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
6. Add each headline theorem to `AxiomAudit.lean`. The build is
   `lake build --wfail`: no `sorry`, no warnings, no new axioms.
