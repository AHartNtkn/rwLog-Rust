# Structure of the Lean development

The development is layered so that a new rung proves only what is new about
its machine. Everything below `Rungs/R00N/` is shared; a rung imports it and
never restates it.

```
Trusted/        the specification: syntax, semantics, Runtime, Rung, the Tier-0 properties,
                and the cost model (Cost.lean) by which rungs from R002 on are judged
Theory/         constraint theories and firing
Kernel/         the executable kernel (match, solve, span, refute) and its proofs
SpanLayer/      span-level semantics, derivations, coverage vocabulary
Lib/            facts about lists and greatest fixpoints that mention no rwlog type
Rungs/Framework generic theorems about any Runtime / Rung
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
| Converse of a program | `SpanLayer/Dual.lean` | `Program.sem_dual` |
| Greatest fixpoints by iteration | `Lib/Gfp.lean` | `gfpFrom`, `gfpFrom_closed`, `subset_gfpFrom` |

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
5. Add each headline theorem to `AxiomAudit.lean`. The build is
   `lake build --wfail`: no `sorry`, no warnings, no new axioms.
