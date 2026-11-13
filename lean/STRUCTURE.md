# Structure of the Lean development

The development is layered so that a new rung proves only what is new about
its machine.

**Master is between epochs.** Epoch 1 of the ladder (rungs R000 to R005, on
the size-charged cost model) is frozen at the git tag `epoch-1`; `EPOCH1.md`
says what its theorems are about. The directories `Rungs/R000` to `Rungs/R004`,
their tests and every proof about R005 exist only at the tag. Master has the
specification, the kernel, the shared libraries, and R005's machine written
once against the derivation kernel (`Rungs/Tabled/`, `Rungs/Mirror/`,
`Rungs/R005/Engine.lean`), built and run on the conformance cases
(`Tests/R005Runs.lean`). Its kept properties are not re-established yet
(roadmap M3 part B and M4), so no rung is admitted on master. `PARKED.md`
lists the files still out of the build: the proofs of epoch 1 about the tabled
machine, the mirrored machine and the naive machine, written against the old
kernel and the old step. What this file says about them describes them as
they are at the tag.

```
Trusted/        the specification: syntax with sort declarations, semantics (what a sort
                and a span mean, Semantics.lean), answers, steps and runtimes with the
                Tier-0 properties (Runtime.lean), what a constraint system gives an
                engine and the laws it satisfies (Domain.lean), Rung and Preprocessor
                (Engine.lean),
                the properties every machine and every whole rung keeps and the fairness
                bound (Properties.lean), the cost monad (CostMonad.lean),
                the charged primitives (Charged.lean), the kernel an engine is written
                against (Kernel.lean), what another kernel must prove to stand in for
                it (KernelRung.lean),
                and the cost model (Cost.lean) by which rungs from R002 on are judged:
                cost is coverage latency, the ticks until an emitted answer covers a
                ground pair, and never depends on a query halting
Kernel/         the executable kernel of spans as written (match, solve, span) and its proofs;
                the normal form of expressions (NormalForm.lean, NormalFormCorrect.lean,
                NormalFormStable.lean, Order.lean), the derivation kernel's rules over any
                constraint domain (Derivation.lean) and the algebra of a lawful domain
                (DomainLaws.lean)
SpanLayer/      span-level semantics, derivations, coverage vocabulary
Lib/            facts about lists and greatest fixpoints that mention no rwlog type
Rungs/Framework generic theorems about any Runtime / Rung
Rungs/Tabled/   the tabled round machine for any way of unfolding a call (Machine.lean), and
                the ways R005 races: unfolding to a depth, a walk between boundaries, and
                the walk with shared sub-chains (Unfold.lean). Written once, against the
                derivation kernel. `Exact`, `Repeats`, `Direction` and `Base/` are parked
Rungs/Mirror/   a machine run on a query and on its converse side by side, for any engine
                (Machine.lean). `Direction`, `Bounds`, `Keeps`, `Trace` are parked
Rungs/Naive/    normalisation, unfolding to a depth, and their correctness (namespace `R000`).
                `Engine`, `Correct`, `Properties` (the naive machine of epoch 1) are parked
Rungs/R005/     the engines: `R001.engine` (tables, unfolding to a depth), `R004.engine` (tables,
                the race of all three ways), `R005.engine` (`R004.engine` mirrored)
AxiomAudit.lean every headline and shared theorem, checked to use only the three standard axioms
Tests/          executable runs: the charges of the kernel (ChargeRuns), the three engines on
                the conformance cases and on each other (R005Runs); the runs of the naive
                and the tabled machine of epoch 1 (parked)
```

`SYMMETRIC_ENGINE.md` is the design note for the engine of milestone M6: what it
is, what was measured, and what the trusted files and the kernel must provide
for it. Its measurements on R004 and R005 are in `Tests/MiddleRuns.lean` at the tag `epoch-1`.

The constraint system is sorts with a built-in disequality (roadmap L48, L51).
The trusted files have no rules, theories or models: `Trusted/Semantics.lean`
says what a sort and a constraint mean, and `Trusted/Domain.lean` says what
any constraint system gives an engine (`Domain`) and what it satisfies
(`Domain.Lawful`). The instance for sorts is not on master yet (roadmap M5,
design in `SORTS.md`); until it is, `Engine.costed` runs at the domain of
spans as written (`Domain.written`), which looks at no constraint and is not
lawful.

## What is shared, and where to look first

| You need | It is in | Entry points |
|---|---|---|
| The coverage checker is exact | `Kernel/Covers.lean` | `Span.covers?_iff`, `covers?_refl/trans/swap/congr`, `Span.Equiv.*`, `matchAll_complete` |
| Interfaces of a span | `Kernel/Iface.lean` | `Span.storeOn`, `rightIface`, `leftIface`, `comp_rightIface`, `rightIface_covers` |
| The algebra of a lawful constraint domain | `Kernel/DomainLaws.lean` | `Domain.denO`, `Lawful.denO_inj`, `swap_swap`, `rep_swap`, `compose_swap`, `meet_swap`, `swap_of_isBound`, `covers_swap`, `compose_assoc`, `meet_comm`, `meet_assoc`, `meet_self`, `covers_antisymm` |
| No sorts are well-formed sorts; first-order spans | `SpanLayer/Sorts.lean` | `Sorts.wellFormed_nil`, `Sorts.not_mem_nil`, `GTerm.univ_infinite`, `Span.firstOrder_swap` |
| Maximal answers and freshness | `Kernel/Maxima.lean` | `maxima`, `fresh` and their lemmas |
| Coverage in the interpretations of a class | `SpanLayer/Modulo.lean` | `LCov`, `LEq`, `Live`, `DeadR`, `Backed`, `Ref`, `DC`, `GCov`, `GEq`, `Dom` |
| Chains of spans | `Kernel/Chain.lean` | `Span.denO_chain`, `Span.chain_isSome_iff`, `chain_isSome_fuse`, `chain_eq_none_of_compose`, `GRel.chain` |
| Unfolding equations | `Rungs/Naive/Unfold.lean` | `unfoldN_succ`, `unfoldN_succ'`, `unfoldN_call`, `unfoldN_add`, `unfoldN_or/and/seq/conv`, `unfoldN_dual` |
| The normal form of an expression and its nodes | `Kernel/NormalForm.lean` | `normB`, `RelOf.norm`, `RelOf.normConv`, `NodeView`, `RelOf.view`, `interval`, `without`, `mkSeq`, `mkAnd` |
| The normal form means what the expression means | `Kernel/NormalFormCorrect.lean` | `gd_normB`, `derives_norm_iff`, `sem_norm`, `sem_normConv`; equal normal forms: `normB_seq_assoc`, `normB_and_comm`, `normB_and_assoc`, `normB_or_comm`, `normB_or_assoc`, `normB_or_self`; derivations as ground relations: `DerivesG`, `GD` |
| The normal form is stable: which expressions are nodes, and every node the kernel reads or makes is one | `Kernel/NormalFormStable.lean` | `Normal`, `normal_normB`, `Normal.norm_eq`, `normal_iff_norm_eq`, `normB_normB`, `Normal.normConv_normConv`, `Normal.view_members`, `view_chain`, `view_meet`, `view_union`, `Normal.interval`, `without`, `join`, `meet`; a node is its members rebuilt: `Normal.mkSeq_seqParts`, `mkAnd_andParts`, `mkOr_unionParts`; sorted lists: `sortedParts_of_sorted`, `sortedBranches_of_strict`, `eq_of_perm_of_sorted`, `eq_of_mem_iff_of_strict` |
| The structural order is linear; sorted lists are determined by their members | `Kernel/Order.lean` | `relCmp_trans`, `relCmp_eq`, `sortedBranches_eq`, `pairwise_sortedBranches` |
| Valid answers of a goal and the rules that make them | `Kernel/Derivation.lean` | `Goal`, `Valid`, `Valid.leaf`, `join`, `meet`, `inj`, `unfold`, `unfoldConv`, `swap`, `Valid.sound`, `Valid.general` |
| Sizes charged by the cost model | `Kernel/Size.lean` (and `Term.size_pos` in `Kernel/Solve.lean`) | `Span.size_pos`, `Span.size_swap`, `Rel.size_pos` |
| Sums over lists | `Lib/List.lean` | `sum_flatMap_map`, `sum_filterMap_map`, `le_sum_map_of_mem`, `sum_map_le` |
| Converse of a program | `SpanLayer/Dual.lean` | `Program.sem_dual` |
| Greatest fixpoints by iteration | `Lib/Gfp.lean` | `gfpFrom`, `gfpFrom_closed`, `subset_gfpFrom` |
| Insertion sort by a strict order | `Lib/Insert.lean` | `insertBy`, `sortBy`, `sortBy_eq` (a duplicate-free list sorts to the ordered list with the same members) |
| First occurrences of a list | `Lib/Firsts.lean` | `addNew`, `addAll`, `firsts`, `firsts_eq_eraseDups`, `addAll_firsts`, `addAll_flatMap_firsts`, `addAll_flatMap_congr` |

## The rung framework

`Rungs/Framework/` is about an arbitrary `Runtime`, so it applies to every
rung unchanged.

* `Runtime.lean`: runs, prefixes, halting, the final report, `stateAfter`,
  traces, certificates. `halts_iff_stateAfter`, `emitted_eq_flatMap_trace`,
  `final_eq_some_iff`, `certifies_iff`.
* `Answer.lean`: `Answer.Covers` and `Answer.Equiv` are a preorder and an
  equivalence on answers of any types and converse respects them. On spans
  they are the coverage the kernel decides (`Span.covers_iff`,
  `Span.equiv_iff`).
* `Trace.lean`: `StepEquiv` / `ShownEquiv` / `TraceEquiv`, and simulation.
  Give a relation `Sim` on states with
  `StepOf.Rel E Sim (R.step s) (R'.step s')` and get `Runtime.trace_of_sim`,
  `halts_iff_of_sim`, `traceEquiv_of_sim`, `emitted_of_sim`. The two runtimes
  may have different types of answers.
* `Tier0.lean`: `Runtime.Tier0Cert`. A rung proves that it is sound, that each
  derivation is eventually dead or covered by an emitted answer, and that at
  halt every derivation is, and receives `HonestExhaustion` from
  `Tier0Cert.tier0` (`HonestExhaustion.of_cover`). `sound_of_refines`,
  `derivationGeneral_of_refines` and `Complete.pointwise` are generic too.
* `Transfer.lean`: moving theorems between rungs. `SameRun R' R` says two
  runtimes emit equivalent answers and halt together; it carries `Tier0`,
  `DerivationGeneral` and `TerminatesOn` from `R` to `R'`
  (`SameRun.tier0`, `SameRun.terminatesOn`), and `SameRun.of_sim` builds it
  from a simulation. A rung is one runtime on the original input
  (`Rung.runtime`, `Trusted/Properties.lean`); `Rung.sound`,
  `Rung.pointComplete`, `Rung.honest` and `Rung.honestProgress` carry the
  machine's theorems through the preprocessor, and `Rung.Keeps.of_id` is
  `Rung.Keeps` for a machine with the identity preprocessor.
* `Fairness.lean`: what the fairness bound of `Trusted/Properties.lean` means
  (`Alternative.semAt_subset`, `Fair.flat_ticks`,
  `Runtime.FinalMaximal.maximal`), and `firstWording_false`: a bound
  polynomial in the size of an answer's derivation and of the input is false
  for every sound machine that emits spans and pays a tick for each.

* `Derivation.lean`: every engine is sound and derivation-general, at every
  kernel of a constraint domain that is lawful at well-formed sorts
  (`Engine.sound`, `Engine.derivationGeneral`). An answer exists only with the proof that it
  is valid, so the two theorems use nothing about the engine.

* `Cost.lean`: the cost monad of `Trusted/CostMonad.lean` is a lawful monad; the
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

* `Admission.lean`: what the classes and contexts of the admission rule
  (`Trusted/Cost.lean`, reasons in `ADMISSION.md`) mean, and an inhabitant of
  each. `Ctx.denAt_fill` (the meaning of a context applied to the meaning of
  an expression is the meaning of the plugged expression), `Ctx.denAt_union`,
  `denoteAt_ofPairs`, `Context.demands_alone` (the member alone demands
  exactly its targets), `demands_orL`, `Demands.related_ofPairs` (the residue
  is the cost of a pair its query relates), `Ctx.open_wrap`, and the proper
  class `ProgClass.points`.

* `Latency.lean`: how the improvement statements of `Trusted/Cost.lean`, which
  measure the ticks until an answer covers a ground pair, are established.
  `Simulates.of_steps` (the new machine covers each answer of the old one,
  step by step, at a bounded cost), `CostedRuntime.coversWithin_of_halts` (on
  an input that halts, an honest machine has covered every pair of the query
  by the time it halts, so a separating family that halts needs only its
  target pairs to be in the denotation), and
  `CostedRuntime.le_spent_of_covered` (a machine that has emitted nothing in
  `N` steps has paid for `N + 1` before it covers anything).

`Rungs/Tabled/Machine.lean` is the tabled machine as an engine for every
derivation kernel, with the way a call is unfolded left to an `Unfolder`
(`Tabled.engine u`). A goal is an interval of a chain or a set of members of a
meet, between two boundaries; a round produces every goal's answers from its
splits and from the unfolder, then marks as complete the largest set of goals
that gained nothing and depend only on each other. `Rungs/Tabled/Unfold.lean`
has the unfolders: `eagerRace` (unfold every call to a depth, then evaluate),
`walkRace` (the same answers, walking a chain from a boundary and pruning as
it goes, from either end) and `sharedRace` (the walk with equal sub-chains
evaluated once); `raced` races them with `K.race`. Each machine exists once
and nothing is proved of a second copy (roadmap L04).

`Rungs/Framework/Writing.lean` proves what holds of every engine because an
engine is handed the normal form of the query: `Engine.orComm`, `orAssoc`,
`seqAssoc`, `andComm`, `andAssoc`. `Rungs/Framework/ConvTrace.lean` proves
that `Runtime.ConvTrace` as stated holds of no engine
(`Engine.not_convTrace`), so neither does `Runtime.Keeps` (`Engine.not_keeps`;
roadmap L57).

`Rungs/Framework/Race.lean` defines `Cost.race` and proves what it returns and spends
(`Cost.race_val`, `Cost.race_ticks`, and from below `Cost.le_race_ticks`), for
any two computations. A rung that adds one more way to answer the unfolding
race races it against the previous rung's unfolder, as R004 did: simulation
within 7 times is then `Tabled.spent_le_of_skips`, and a lower bound on the
previous rung's first round is `le_race_ticks` on its two halves.

`Rungs/Framework/RaceWinner.lean` says which computation a race returns and
what it costs as functions of the two costs alone (`Cost.firstWins`,
`Cost.raceCost`, `Cost.race_val_eq`, `Cost.race_ticks_eq`), with `raceCost_le` (at most 7 times the
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

`Rungs/Mirror/Machine.lean` is the mirrored machine of any engine `E`
(`Engine.mirrored`): `E` on the root and `E` on its converse (`K.convNode`),
stepped by level so that neither run is ever more than one doubling ahead in
ticks, with the converse run's answers swapped (`K.swapA`). R005 is
`R004.engine.mirrored`. The theorems of epoch 1 about it (`Mirror.trace_go`,
`paid_le_min`, `paid_ge_min`, `directionFree`, `keeps`) are in the parked
files and are not restated yet.

The goal-directed machine and the hedge of two machines (`Rungs/Directed/`,
`Rungs/Hedge/`) are not on master; they are at the tag `epoch-1`.

An engine cannot declare its own cost and cannot make up an answer.
`Trusted/Kernel.lean` has two classes. `Kernel S M` is an abstract type of
representatives of spans with their stores, an abstract monad, and the
operations of a constraint domain on them (`Trusted/Domain.lean`), each
returning in the monad, with `metered` (run a computation and return what it
spent). There is no simplification: every operation returns a
representative, or nothing when the result relates no pair.
`DerivationKernel S N A M` extends it with abstract types of nodes of the
normal form and of answers: reading a node, and the rules that make an answer
(`leaf`, `join`, `meetA`, `inj`, `unfold`, `swapA`). An `Engine`
(`Trusted/Cost.lean`) is a machine written for every derivation kernel: it is
handed the root node of the query's normal form, can touch a span, a node or
an answer only through those operations, and can only spend what they charge.
`Engine.costedAt` is the engine at a constraint domain and a kernel that
returns what the domain returns (`Kernel.Refines`). The type of
representatives, the domain and the kernel are given for the sorts of each
program, because which values are canonical depends on the sorts declared: an answer is a goal and a representative with the proof that
the representative is a valid answer of the goal (`Ans D P`), and the answers
reported are those of the root goal with no boundary. `Engine.costed` is the
engine at `DerivationKernel.std P`, the kernel of spans as written, where
each operation is the charged primitive of `Trusted/Charged.lean`. `Advances` and `Admits` are stated on engines.

The cost monad (`Trusted/CostMonad.lean`) counts ticks and space: `peak` is
the most cells live at once and `held` the cells still live at the end. Cells
are released only when a computation is abandoned (`Cost.within`, and so
`Cost.race`). `CostedRuntime.space P q n` is the peak of the first `n` steps.

`Kernel.std` is the kernel of spans as written: its values are those of
`Domain.written` and its charges are postulated. A kernel rung
(`Trusted/KernelRung.lean`) is another kernel that returns what a domain
returns (`Kernel.Refines`, in `Trusted/Kernel.lean`) and whose charges are
theorems about a machine;
`Engine.costedAt` is an engine at the derivation kernel over such a kernel
(`DerivationKernel.over`). The first one is `rustKernel`
(`verified/lean/RwLogVerified/Kernel.lean`): the charge of each operation on
terms is the tick bound proved of the Rust function on the store of
`verified/rust/src/store.rs`. See `verified/README.md`. The operations on
nodes and the interning of answers are charged as postulated at every kernel
rung so far (roadmap L45).

In epoch 1 each machine was written twice, in the same words: once against
the kernel (`Gen.lean`) and once in `Cost`, with a `Reading.lean` proving the
two equal. That ended with the port (roadmap L04): each machine exists once,
as an engine, and proofs are carried out on that text at
`DerivationKernel.over`.

A rung whose machine is equal to an earlier one as a `Runtime` (as R002 was
to R001) uses `SameRun.of_eq`, or simply rewrites.

## Where epoch 1 went

| At the tag `epoch-1` | On master |
|---|---|
| `Rungs/R000/` Chain, Normalize, NormalizeCorrect, Unfold, Engine, Correct, Properties | `Rungs/Naive/`, same file names |
| `Rungs/R000/` Products, Termination | removed |
| `Rungs/R001/Engine.lean`, `Spec.lean` | `Rungs/Tabled/Base/` (parked); the Spec keeps only the statements whose proofs are kept |
| `Rungs/R001/Proofs/` Kernel, Base, Derivations, Tier0 and `Tier0/`, Symmetry, SymmetryLists, SymmetryGoals | `Rungs/Tabled/Base/Proofs/` (parked), same file names |
| the rest of `Rungs/R001/Proofs/` (termination certificates, exact tables, the mirror trace, `R001.keeps`) | removed |
| `Rungs/R002/` to `Rungs/R004/` (unfolders, their `Gen`, `Spec`, `Reading`, `Proofs/`) | removed; the three ways of unfolding are rewritten in `Rungs/Tabled/Unfold.lean` |
| `Rungs/R005/` Spec, Family, `Proofs/` | removed; `Rungs/R005/Engine.lean` is the engine |
| `Rungs/Directed/`, `Rungs/Hedge/`, `Tests/DirectedRuns.lean`, `MiddleRuns.lean` | removed |
| `Tests/R000Runs.lean`, `R001Runs.lean` | `Tests/NaiveRuns.lean`, `TabledRuns.lean` (parked) |
| `Tests/R002Runs.lean` to `R005Runs.lean` | removed; `Tests/R005Runs.lean` is new |
| `R001.Obligation.finite_answers` and its proof | removed: it holds of every runtime (`Runtime.finite_answers`), so it obliged nothing (roadmap L05) |

Declarations keep their epoch 1 namespaces (`R000` to `R005`), so a name on
master is the same name at the tag.

## Rules that hold in every epoch

1. Use kernel theorems by name. If a proof needs a fact about `covers?`,
   `compose`, `meet` or lists that is not specific to one machine,
   add it to `Kernel/`, `SpanLayer/` or `Lib/`, not to the machine.
2. The shared layers never import a machine: `Kernel/`, `SpanLayer/`, `Lib/`
   and `Rungs/Framework/` import nothing else under `Rungs/`.
3. `Complete` (one emitted answer covers the derived span) does not survive
   preprocessing in general, only `PointComplete` does. State completeness of
   a whole rung pointwise.
4. Add each headline theorem to `AxiomAudit.lean`. The build is
   `lake build --wfail`: no `sorry`, no warnings, no new axioms.

How a rung is admitted is being restated (roadmap M3 part A: `Keeps` for a
whole rung, admission for three kinds of win on a decidable class). The rule
of epoch 1 is in `EPOCH1.md`.
