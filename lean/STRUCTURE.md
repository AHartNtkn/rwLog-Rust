# Structure of the Lean development

The development is layered so that a new rung proves only what is new about
its machine.

**Master is between epochs.** Epoch 1 of the ladder (rungs R000 to R005, on
the size-charged cost model) is frozen at the git tag `epoch-1`; `EPOCH1.md`
says what its theorems are about. The directories `Rungs/R000` to `Rungs/R004`,
their tests and every proof of epoch 1 exist only at the tag. Master has the
specification, the kernel, the shared libraries, the constraint domain of
sorts (`Sorts/`), and R005 as the yardstick the next engine is measured
against: its machine written once against the derivation kernel
(`Rungs/Tabled/`, `Rungs/Mirror/`, `Rungs/R005/Engine.lean`), its kept
properties at every kernel that refines a lawful constraint domain
(`Rungs/R005/Keeps.lean`) and at the domain of sorts with no hypothesis left
(`Rungs/R005/Sorts.lean`), the lower bounds a separation from it will need,
stated (`Rungs/R005/Bounds.lean`), and its manifest (`Manifest/R005.lean`).
Nothing is re-proved about how R005 or its predecessors were admitted: those
theorems are at the tag. No file is out of the build.

```
Trusted/        the specification: syntax with sort declarations, semantics (what a sort
                and a span mean, Semantics.lean), answers, steps and runtimes with the
                Tier-0 properties (Runtime.lean), what a constraint system gives an
                engine and the laws it satisfies (Domain.lean), Rung and Preprocessor
                (Engine.lean),
                the properties every machine and every whole rung keeps and the fairness
                bound (Properties.lean), the cost monad (CostMonad.lean),
                the charged primitives on nodes (Charged.lean), the kernel an engine is
                written against and what a kernel rung is (Kernel.lean),
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
                derivation kernel. The rest is what is proved of it: the round and its
                invariant, completeness and honesty (Correct.lean), that it runs the same
                on a converse, on the mirrored program and with any exact race
                (Symmetry.lean), that a table done in one run is done in a run that asks
                for its goal (Host.lean), the empty side (EmptySide.lean), and the same
                for the mirrored machine (Mirrored.lean, MirrorKeeps.lean)
Rungs/Mirror/   a machine run on a query and on its converse side by side, for any engine
                (Machine.lean); what a step of it shows (Trace.lean) and what it costs
                from below (Bounds.lean)
Rungs/Symmetric/ the symmetric engine of `SYMMETRIC_ENGINE.md` (Machine.lean): a table for
                every goal, every split of a chain and of a meet as a group of strategies
                (join, push from either side), groups balanced by their levels, one
                request a step. A level rises by what was spent, and the engine charges
                itself one tick for a unit of work that did something, so a group that
                worked has risen at every kernel (`workGroup_did`). Run in `Tests/SymmetricRuns.lean`. The table of a
                goal that is its own converse holds the converse of everything it holds;
                with the choice of one orientation where the input is loaded
                (`CostedRuntime.oriented`, `Trusted/Cost.lean`) that is what makes the run
                on the mirror image the run swapped. Proved so far: an answer enters a
                table by `addAnswer` and in no other way (Invariant.lean, `Reach`), and on
                a root that is its own converse every step shows answers that are their
                own converses rearranged (SelfConverse.lean, `selfConverse_of`), given
                that every answer of the root table is an answer of the root goal; the
                invariant that every answer of a table is an answer of the goal of the
                table and every strategy fits its goal (Goals.lean, `Inv`, `inv_request`),
                which gives that condition, so the engine run on one orientation has
                `ConvTrace` and `DualTrace` (`Symmetric.oriented_convTrace`,
                `Symmetric.oriented_dualTrace`). A complete table never changes again, and
                nothing nested in the round of a table completes it (Rounds.lean, `Keep`,
                `stable_request`). The interface check (a chain goal is
                complete with no answer when the other side fails under every interface
                one side can show, read from the program) is a strategy of its own; the
                invariant and the mirror criterion cover it. Towards completeness:
                the cursor of a join visits every pair once (Cursor.lean,
                `Cursor.all_spec`); what the cursors of every strategy mean (Progress.lean,
                `Prog`: the table covers what its rule makes of everything a cursor has
                passed) holds of the strategies made for a goal and is kept by a whole
                request, with the goals of the tables distinct and good (Kept.lean,
                `Good`, `good_request`); and the interfaces read from the program are
                right about it (Edge.lean, `readOk`). Towards fairness: the cursor of
                a join reaches every pair that is there, by a rank that falls
                (Cursor.lean, `Cursor.all_rank`, `rankLt_wf`); and the record of a
                request (Turns.lean, `Req`, `req_request`): the groups of a table change
                in its own round only, where each strategy moves on, a group all of whose
                checks are dead is removed, one group works with the tables it reads
                settled, and the round is balanced: a group worked, or it stands as it
                stood while a lower one rose (`Turn`, `Balanced`); of the groups a goal begins with one has a span, a call, a
                union or a join, and one that has none is all checks (`shaped_expand`); a table
                marked complete has a strategy with nothing left to do that reads complete
                tables only; and an edge is read in the end, from a depth that the node
                and the program give (ReadLive.lean, `readEdge_some`); and of a table that
                has rounds for ever every group works for ever, with as many groups from
                some request on (Lines.lean, `Requests.lines`). Fairness and
                completeness: a run of requests (`IsRun`) holds for each goal the answers
                of its table (`held`) and does not neglect the tables that are complete at
                some time or have rounds for ever (`opened`); a complete table is served by
                the strategy that completed it (Served.lean, `IsRun.served_done`), a table
                with rounds for ever by a strategy of the group that works for ever
                (Fair.lean, `IsRun.served_live`), so the run is fair (`IsRun.fair`); the
                states of the engine are such a run, and the machine is complete, honest
                when it reports that it is done, and emits no progress certificate
                (Correct.lean, `Symmetric.complete`, `honestExhaustion`,
                `honestProgress`); no answer of a table covers a later one, so no
                answer emitted is covered by an earlier one, and the final report is the
                maximal emitted answers (`noSubsumed`, `finalMaximal`). Not proved yet:
                `TerminatesWhere`, `EmptySide` and with them `Keeps`; the cost bound. A goal and its converse do not share a
                table (not owed by any property; billboard SIM12)
Rungs/Naive/    normalisation, unfolding to a depth, and their correctness (namespace `R000`)
Rungs/R005/     the engines: `R001.engine` (tables, unfolding to a depth), `R004.engine` (tables,
                the race of all three ways), `R005.engine` (`R004.engine` mirrored);
                what they keep (Tables.lean, Keeps.lean, Sorts.lean) and the stated lower
                bounds (Bounds.lean)
Sorts/          the constraint domain of sorts and the proof that it is lawful
Manifest/       R005's manifest: headline statements, bounds, trusted files, axioms and a
                space report, all checked by the build
AxiomAudit.lean every headline and shared theorem, checked to use only the three standard axioms
Tests/          executable runs at the domain of sorts with nothing charged: the three engines on
                the conformance cases and on each other (R005Runs), the cases about
                constraints at the domain of sorts (SortsConformance), R005 on the inputs
                of the simulation note (SimulationRuns), the sorts (SortsRuns)
```

`SYMMETRIC_ENGINE.md` is the design note for the engine of milestone M6: what it
is, what was measured, and what the trusted files and the kernel must provide
for it. Its measurements on R004 and R005 are in `Tests/MiddleRuns.lean` at the tag `epoch-1`.
`SYMMETRIC_ENGINE_SIMULATION.md` is the attack on that design's main risk, whether
the engine stays within a polynomial of R005: the inputs on which the first
design fails, the changes measured, and the lemmas still open. Its prototype is
`scripts/symmetric_engine_tables.py`, and R005's side of each comparison is
`Tests/SimulationRuns.lean` (on master it runs R005 as it is written now; the figures
of the note are those of the tag). `scripts/r005_interpreter.py`
is R005 at the tag `epoch-1` outside Lean, counting the same ticks (`check` compares it
with every number Lean guards for those inputs); it is what decides the inputs Lean does
not evaluate in reasonable time. `scripts/symmetric_engine_halting.py` runs random small
programs on both and compares where each halts.

The constraint system is sorts with a built-in disequality (roadmap L48, L51).
The trusted files have no rules, theories or models: `Trusted/Semantics.lean`
says what a sort and a constraint mean, and `Trusted/Domain.lean` says what
any constraint system gives an engine (`Domain`) and what it satisfies
(`Domain.Lawful`). The instance for sorts is `Sorts.dom` (`Sorts/Dom.lean`),
with `Sorts.dom_lawful : S.WellFormed → (dom S).Lawful S.interp`; `SORTS.md`
section 6 lists its files. An engine's cost is taken at a kernel rung
(`KernelRung`, `Trusted/Kernel.lean`): a lawful domain and a kernel of it for
the sorts of each program. The rung engines are judged at is `sortsRung`
(`verified/lean/RwLogVerified/SortsRung.lean`), the domain of sorts with
every charge derived from the Rust. No domain of spans as written is left
(roadmap L55).

## What is shared, and where to look first

| You need | It is in | Entry points |
|---|---|---|
| The coverage checker is exact | `Kernel/Covers.lean` | `Span.covers?_iff`, `covers?_refl/trans/swap/congr`, `Span.Equiv.*`, `matchAll_complete` |
| Interfaces of a span | `Kernel/Iface.lean` | `Span.storeOn`, `rightIface`, `leftIface`, `comp_rightIface`, `rightIface_covers` |
| The constraint domain of sorts | `Sorts/Dom.lean`, `Sorts/Rep.lean`, `Sorts/Gaps.lean` | `Sorts.Rep`, `Sorts.dom`, `dom_lawful`, `Rep.ext_rel`, `exists_rep`, `Prob.normal`, `Raw.Normal.eq`, `Rep.no_hidden`, `Raw.toSpan_den` |
| The algebra of a lawful constraint domain | `Kernel/DomainLaws.lean` | `Domain.denO`, `Lawful.denO_inj`, `swap_swap`, `rep_swap`, `compose_swap`, `meet_swap`, `swap_of_isBound`, `covers_swap`, `compose_assoc`, `meet_comm`, `meet_assoc`, `meet_self`, `covers_antisymm` |
| No sorts are well-formed sorts; first-order spans | `SpanLayer/Sorts.lean` | `Sorts.wellFormed_nil`, `Sorts.not_mem_nil`, `GTerm.univ_infinite`, `Span.firstOrder_swap` |
| Maximal answers and freshness | `Kernel/Maxima.lean` | `maxima`, `fresh` and their lemmas |
| Coverage in the interpretations of a class | `SpanLayer/Modulo.lean` | `LCov`, `LEq`, `Live`, `DeadR`, `Backed`, `Ref`, `DC`, `GCov`, `GEq`, `Dom` |
| Unfolding equations | `Rungs/Naive/Unfold.lean` | `unfoldN_succ`, `unfoldN_succ'`, `unfoldN_call`, `unfoldN_add`, `unfoldN_or/and/seq/conv`, `unfoldN_dual` |
| The normal form of an expression and its nodes | `Kernel/NormalForm.lean` | `normB`, `RelOf.norm`, `RelOf.normConv`, `NodeView`, `RelOf.view`, `interval`, `without`, `mkSeq`, `mkAnd` |
| The normal form means what the expression means | `Kernel/NormalFormCorrect.lean` | `gd_normB`, `derives_norm_iff`, `sem_norm`, `sem_normConv`; equal normal forms: `normB_seq_assoc`, `normB_and_comm`, `normB_and_assoc`, `normB_or_comm`, `normB_or_assoc`, `normB_or_self`; derivations as ground relations: `DerivesG`, `GD` |
| The normal form is stable: which expressions are nodes, and every node the kernel reads or makes is one | `Kernel/NormalFormStable.lean` | `Normal`, `normal_normB`, `Normal.norm_eq`, `normal_iff_norm_eq`, `normB_normB`, `Normal.normConv_normConv`, `Normal.view_members`, `view_chain`, `view_meet`, `view_union`, `Normal.interval`, `without`, `join`, `meet`; a node is its members rebuilt: `Normal.mkSeq_seqParts`, `mkAnd_andParts`, `mkOr_unionParts`; sorted lists: `sortedParts_of_sorted`, `sortedBranches_of_strict`, `eq_of_perm_of_sorted`, `eq_of_mem_iff_of_strict` |
| The structural order is linear; sorted lists are determined by their members | `Kernel/Order.lean` | `relCmp_trans`, `relCmp_eq`, `sortedBranches_eq`, `pairwise_sortedBranches` |
| Valid answers of a goal and the rules that make them | `Kernel/Derivation.lean` | `Goal`, `Valid`, `Valid.leaf`, `join`, `meet`, `inj`, `unfold`, `unfoldConv`, `swap`, `Valid.sound`, `Valid.general` |
| Sizes charged by the cost model | `Kernel/Size.lean` (and `Term.size_pos` in `Kernel/Solve.lean`) | `Span.size_pos`, `Span.size_swap`, `Rel.size_pos` |
| Sums over lists | `Lib/List.lean` | `sum_flatMap_map`, `sum_filterMap_map`, `le_sum_map_of_mem`, `sum_map_le`, `sum_map_le_mul`, `sum_range_getD`, `sum_le_sum_of_getElem`, `sum_lt_sum_of_getElem` |
| A sorted list with its duplicates erased is strictly sorted | `Lib/List.lean` | `pairwise_lt_eraseDups` |
| Lists related member by member, one member changed, conditionals | `Lib/List.lean` | `forall₂_mem_left`, `forall₂_mem_right`, `forall₂_getElem?`, `forall₂_getLast?`, `map_modify_eq`, `mem_modify`, `two_le_length_of_mem`, `drop_take_reverse`, `ite_of_pos`, `ite_of_neg` |
| Goals, the same goal, maximal answers, the rule of a split, for any machine that tables | `Rungs/Framework/Goals.lean`, `GoalsVal.lean` | `GoalOf`, `Kind`, `same`, `indexFrom`, `coversA`, `maxima`, `fresh`, `both`; their values: `same_val`, `indexFrom_val`, `coversA_val`, `maxima_val`, `fresh_val`, `both_some` |
| A fold in `Cost` keeps an invariant | `Rungs/Framework/Cost.lean`, `TraverseStd.lean` | `Cost.foldL_inv`, `Traverse.foldL_inv`, `Traverse.foldL_done` (may speak of the members passed), `Traverse.foldL_split` (and knows the members to come) |
| Well-formed queries built from a well-formed one | `Rungs/Framework/SameTrace.lean`, `Direction.lean` | `ProgramOf.WellFormed.of_sub`, `.conv`, `.seq_left`, `.seq_swap`, `.and_of_seq`, `.dual` |
| Converse of a program | `SpanLayer/Dual.lean` | `Program.sem_dual` |
| Greatest fixpoints by iteration | `Lib/Gfp.lean` | `gfpFrom`, `gfpFrom_closed`, `subset_gfpFrom` |
| Insertion sort by a strict order | `Lib/Insert.lean` | `insertBy`, `sortBy`, `sortBy_eq` (a duplicate-free list sorts to the ordered list with the same members) |
| First occurrences of a list | `Lib/Firsts.lean` | `addNew`, `addAll`, `firsts`, `firsts_eq_eraseDups`, `addAll_firsts`, `addAll_flatMap_firsts`, `addAll_flatMap_congr`, `firsts_map`, `firsts_spec` |
| An antichain that covers a list | `Lib/Antichain.lean` | `antichain`, `antichain_spec` |
| Sequences that cannot go on for ever | `Lib/Sequences.lean` | `eventually_const`, `no_descent`, `infinitely_often_fin` |
| Lookup by sorted key; the values of a list of options | `Lib/List.lean` | `lookup_sorted`, `gather`, `gather_eq_some`, `gather_range`, `gather_isSome` |

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
  `Rung.Keeps` for a machine with the identity preprocessor. A preprocessor
  may add sort declarations (`Preprocessor.adds`, `Sorts.Extends`), so the
  machine is run on sorts that may declare more than the program's. Its
  theorems are about its answers read in those sorts, and the four theorems
  ask that the answers say how they are read (`Answer.SelfRead`,
  `Framework/Answer.lean`), which the answers of every engine do
  (`Answer.selfRead_sigma`): each is a representative carried with its
  sorts. `Span.denAt_sorted` and `Span.firstOrder_sorted`
  (`SpanLayer/Sorts.lean`) say what holding an end of a span to a sort does.
* `SameTrace.lean`: the whole of `Runtime.Keeps` along a trace.
  `SameTrace R' R` says the two machines show the same thing at every step,
  up to the order of the answers of a step and up to equivalent answers. It
  gives `SameRun`, and the two certify and halt together. `SameTrace.keeps`:
  `R'` keeps every property `R` keeps, with the same base, given the laws of
  `|` of `R'` (free for an engine) and that the answers `R` shows in one step
  do not cover each other (`StepAntichain`). Each property has its own
  transfer (`SameTrace.honestProgress`, `emptySide`, `convTrace`,
  `dualTrace`, `noSubsumed`). `HonestProgress.of_never` is honest progress of
  a machine that emits no certificate. The mirrored tabled machine gets
  `mirror_keeps` this way (`Rungs/Tabled/MirrorKeeps.lean`).
* `Goals.lean`, `GoalsVal.lean`: the text every machine that tables shares
  (the goal, the same goal, the position of a goal's table, the cover test
  on answers, maximal and fresh answers, the rule of a split) and what each
  returns at the kernel of a program. A machine takes the names with
  `export Goals (…)`, constructors included, so its own files read as
  before. The tabled machine and the symmetric engine do.
* `Saturation.lean`: the completeness every engine on the normal form
  shares (roadmap L30). A run is what it ever holds for each goal
  (`Saturation.Tables`) and the goals it opens. `Saturation.Served` lists the
  strategies of a node (a span, a call, a union, a chain split anywhere and
  joined or pushed from either side, a meet split at any member and
  conjoined or pushed either way) and says one of them is carried out on
  everything the run ever holds, up to coverage. `Saturation.Fair` is every
  opened goal served. `Fair.covers`: a fair run covers the pairs of every
  ground relation the node of an opened goal derives, by induction on the
  depth of the derivation and then on the node. `Fair.complete` is
  completeness at the query, `Fair.covers_pair` the same pair by pair, and
  `Fair.covers_valid` says a valid answer
  found by any schedule is covered by every fair run that opens its goal.
  Nothing is assumed of the order of work or of tables growing. A machine
  proves `Fair` of its runs and receives completeness.
  `Served.checkL` and `checkR` serve a chain that has no answer by the
  interface check.
* `Oriented.lean`: a machine run on one orientation of its input
  (`CostedRuntime.oriented`, `Trusted/Cost.lean`). The choice made from the
  converse of a query, and from the mirror image of an input, is the choice
  made from the input the other way round, or the same choice of a node that
  is its own converse (`orient_conv`, `orient_dual`). So a machine that
  shows, on a root that is its own converse, sets of answers that are their
  own converse (`CostedRuntime.SelfConverse`) has `ConvTrace` and `DualTrace`
  when run on one orientation (`oriented_convTrace`, `oriented_dualTrace`),
  and any machine pays the same on an input and on its mirror image
  (`oriented_paid_dual`).
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
  `N` steps has paid for `N + 1` before it covers anything). For the record
  of wins (`ADMISSION.md` section 6): `Improves.keptBy` (a machine keeps the
  win it improves by), `Admits.keptBy`, and `Ladder.keeps` (every rung of a
  ladder keeps every win on its record).

* `RecordWitness.lean`: `Admits` and `Ladder` have inhabitants. Two toy
  engines, admitted one above the other over a base that never answers, the
  second for an exponential gain over the record that holds the polynomial
  win of the first (`Witness.ladder`). They are not machines for the
  language. On the way: when the normal form of an expression is one span
  (`normB_or_span`, `normB_dual`, `normB_fill`).

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

The theorems about the tabled machine are proved on that text, for any
unfolding race that meets a specification (`Tabled.UOk` in
`Rungs/Tabled/Invariant.lean`: its answers are answers of the goal, and when
it says the unfolding is final they cover every derivation of the goal).
`Rungs/Tabled/Correct.lean` has them for a race that meets it at every lawful
domain (`Tabled.Good`): `complete`, `pointComplete`, `honestExhaustion`,
`honestProgress`, `noSubsumed`, `finalMaximal`. The files before it are the
steps: what the rules of the derivation kernel return (`Framework/Rules.lean`),
the tables read as values (`Tables`, `Round`), what the candidates of a goal
cover (`Semantics`, `Covers`, `Candidates`, `Strategies`), the invariant of a
round (`Invariant`), and that every derivation is covered in the end
(`Eventually`, `Run`). They use derivations bounded by depth
(`Kernel/NormalFormDepth.lean`) and the reading of a node by its kind
(`Kernel/NormalFormSplit.lean`, `NormalFormSpans.lean`, `NormalFormSize.lean`).

`Rungs/Tabled/Unfolding/` proves that each race meets the specification.
`Sem.lean` says what an unfolding to a depth stands for (`GR P d`: the
derivations on which every node is read). For each evaluation one file reads
its text as a value (`EagerVal`, `WalkVal`, `SharedVal`) and one proves the
specification of what it builds (`Eager`: `POk`, `eagerRace_ok`; `Dir`,
`WalkChain`, `Walk`: `WOk`, `walkRace_ok` in both directions; `Shared`:
`SmOk` with the memo's invariant `MemoOk`, `sharedRace_ok`). `Races.lean`
has `Tabled.good_eagerRace`, `good_walkRace`, `good_sharedRace`, `UOk.race`
(two races side by side), and `good_raced` for the race of R004 and R005.
`Rungs/R005/Tables.lean` puts these together: `R001.tableKeeps` and
`R004.tableKeeps`, which do not use that an interface is exact. What R005 is
held to beyond that list does (roadmap L58).

The tabled machine runs the same from either end and with any exact race.
`Kernel/NormalFormMap.lean` has the map on nodes (`nmap b t`: the converse
when `b`, read in the mirrored program when `t`), and
`Rungs/Tabled/Unfolding/ModelMap.lean` that the model of an unfolding says of
the image of a node what it says of the node (`final_nmap`,
`closedPart_nmap`). On the machine: `Rungs/Tabled/Reading.lean` reads a round
table by table (`ansOf_next`, `idx_next_cases`, `prodG`); `MapGoal.lean` has
the map on goals and representatives, what links two programs and their races
(`Link`, `Twin`) and what two sets of tables have of each other (`Fwd`,
`Tied`); `MapSplit.lean` and `MapNode.lean` carry each candidate of a goal to
a candidate of its image (`cand_fwd`, `strat_fwd`); `MapRound.lean` that a
round keeps two runs in correspondence (`tied_next`); `MapRun.lean` that the
root tables gain corresponding answers and complete together (`rootGain_map`,
`rootDone_map`, `rootMax_map`), and that exact races link (`Link.of_ex`).
`Symmetry.lean` has the theorems for races that say what the unfolding is
(`Tabled.Exact`, which the races of R001 and R004 are): `sameRun` and
`halts_iff` (two tabled machines that differ in the race show the same thing
step for step and halt together), `convTrace` and `dualTrace`.

`Kernel/ExactIface.lean` has the set of terms a boundary lets through and
what it is for an interface, which is exact by the laws of a domain (`bset`,
`bset_rightBound`, `bset_leftBound`).
`Rungs/Tabled/Unfolding/Model.lean` says what an unfolding to a depth relates,
product by product, with no machine in it (`SE`, `Final`), and has the algebra
of sequencing sets of products in either direction (`seqSets`, `chainS`,
`chainD`, `pushSet`, `seqI_iff_push_ext`). `EagerExact.lean` proves that the
whole unfolding builds exactly those products (`eager_ex`), so the unfolding
race is final exactly when the model has no open product (`eagerRace_final`).
`WalkExact.lean` proves, under exact interfaces, that what a walk holds of the
items it hands on is what a walk holds of exactly those products (`walk_ex`,
in either direction and under whatever was pushed), so a walk gives the same
verdict (`walkRace_final`).

`SharedExact.lean` proves the same of the evaluation that shares the suffixes
of a chain and remembers what it has evaluated: a summary holds exactly the
products of its node (`evalS_ex`, with the memo holding that of every entry),
so the shared evaluation gives the same verdict (`sharedRace_final`).

`RacesExact.lean` says what it is for an unfolding race to be exact (`UEx`:
its verdict is the model's and its answers are the closed products), proves
it of each evaluation and of two exact races side by side (`raced_ex` for the
race of R004 and R005), and that two exact races give the same verdict and
the same representatives (`UEx.agree`).

`Kernel/NormalFormMap.lean` reads a node as the node of its converse, of its
mirror image in the mirrored program, or as itself (`nmap b t`): the mapped
node is a node of the same kind with the members mapped, and the map is its
own inverse. `Unfolding/ModelMap.lean` proves that the unfolding of the
mapped node has the products of the unfolding of the node, turned round when
the converse is taken (`se_nmap`, `final_nmap`, `closedPart_nmap`).

`Rungs/Framework/Writing.lean` proves what holds of every engine because an
engine is handed the normal form of the query: `Engine.orComm`, `orAssoc`,
`seqAssoc`, `andComm`, `andAssoc`. `Rungs/Framework/ConvTrace.lean` proves
that no engine has the trace of a converse as an equation, in order
(`Engine.not_convTraceInOrder`), which is why `Runtime.ConvTrace` is stated
up to the order of the answers of a step and up to equivalent answers
(roadmap L57).

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
`R004.engine.mirrored`. `Mirror.go_val` says a step of it shows the same step
of one of the two runs, and `Mirror.paid_ge_min` that it has paid at least the
cheaper of the two (`Rungs/Mirror/Trace.lean`, `Bounds.lean`). For the tabled
machine with an exact race the two runs gain the same answers in the same
round, so the mirrored machine shows what the tabled machine shows
(`Tabled.mirror_trace`) and keeps what it keeps (`Tabled.mirror_keeps`). The
upper bounds of epoch 1 (`paid_le_min`, `directionFree`) are at the tag and
are not restated: they were how R005 was admitted.

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
reported are those of the root goal with no boundary. `Engine.costed E κ` is
the engine at a kernel rung `κ`. `Advances` and `Admits` are stated on engines
at a kernel rung, and `Admits` is over the record of the wins admitted below
(`Win`, `Ladder`).

The cost monad (`Trusted/CostMonad.lean`) counts ticks and space: `peak` is
the most cells live at once and `held` the cells still live at the end. Cells
are released only when a computation is abandoned (`Cost.within`, and so
`Cost.race`). `CostedRuntime.space P q n` is the peak of the first `n` steps.

A kernel rung (`KernelRung`, `Trusted/Kernel.lean`) gives, for the sorts of
each program, a type of representatives, a constraint domain on it that is
lawful when the sorts are well formed, and a kernel that returns what the
domain returns (`Kernel.Refines`). No charge of an operation on
representatives is postulated: the trusted files fix no kernel.
`Engine.costedAt` is an engine at the derivation kernel over a kernel
(`DerivationKernel.over`). Three rungs exist. `sortsRung`
(`verified/lean/RwLogVerified/SortsRung.lean`) is the one engines are judged
at: the charge of each operation of the domain of sorts is the tick bound
proved of the Rust function on the store of `verified/rust/src/store.rs`
(see `verified/README.md`); its charges are not computable. `Sorts.uncharged`
(`Rungs/R005/Sorts.lean`) charges nothing for the domain and is what the
tests run. `Witness.sized` (`Rungs/Framework/RecordWitness.lean`) is a toy
for the proof that the admission rule has inhabitants. The operations on
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
| `Rungs/R000/` Chain, Normalize, NormalizeCorrect, Unfold | `Rungs/Naive/`, same file names |
| `Rungs/R000/` Engine, Correct, Properties (the naive machine) | removed |
| `Rungs/R000/` Products, Termination | removed |
| `Rungs/R001/Engine.lean`, `Spec.lean` | removed; `R001.engine` is `Tabled.engine Tabled.Unfold.eagerRace` |
| `Rungs/R001/Proofs/` Kernel, Base, Derivations, Tier0 and `Tier0/`, Symmetry, SymmetryLists, SymmetryGoals | removed; proved again on the one machine in `Rungs/Tabled/` |
| the rest of `Rungs/R001/Proofs/` (termination certificates, exact tables, the mirror trace, `R001.keeps`) | removed |
| `Rungs/R002/` to `Rungs/R004/` (unfolders, their `Gen`, `Spec`, `Reading`, `Proofs/`) | removed; the three ways of unfolding are rewritten in `Rungs/Tabled/Unfold.lean` |
| `Rungs/R005/` Spec, Family, `Proofs/` | removed; `Rungs/R005/Engine.lean` is the engine, `Keeps.lean` what it keeps, `Bounds.lean` the families |
| `Rungs/Directed/`, `Rungs/Hedge/`, `Tests/DirectedRuns.lean`, `MiddleRuns.lean` | removed |
| `Tests/R000Runs.lean`, `R001Runs.lean` | removed; `R001.engine` runs in `Tests/R005Runs.lean` |
| `Tests/R002Runs.lean` to `R005Runs.lean` | removed; `Tests/R005Runs.lean` is new |
| `R001.Obligation.finite_answers` and its proof | removed: it holds of every runtime (`Runtime.finite_answers`), so it obliged nothing (roadmap L05) |

Declarations keep their epoch 1 namespaces (`R000` to `R005`), so a name on
master is the same name at the tag.

## Proving a new engine

An engine is written once against the derivation kernel
(`Trusted/Kernel.lean`), in any monad, and proved at
`DerivationKernel.over D K hK P` in `Cost`. The parts of `Runtime.Keeps`
come from these places.

1. Free for every engine: `Engine.sound`, `Engine.derivationGeneral`
   (`Framework/Derivation.lean`), `Engine.orComm`, `Engine.orAssoc`
   (`Framework/Writing.lean`). `Engine.Obligations` (`Framework/EngineKeeps.lean`)
   names the eight parts that are the engine's own, and `Obligations.keeps`
   fills in the free ones and returns `Runtime.Keeps`.
2. Reading the text as values: open the goal with `at_cost K hK`
   (`Framework/KernelAt.lean`), rewrite the traversals with the `_std`
   lemmas and `Cost.*_val` (`Framework/TraverseStd.lean`,
   `Framework/Cost.lean`), the rules with `Ans.leaf_val`, `join_val`,
   `meetA_val`, `inj_val`, `unfold_val` (`Framework/Rules.lean`), and the
   goal operations with `Framework/GoalsVal.lean`. `rw [Cost.bind_val]`
   works on a bind of the kernel's monad after `at_cost`; `erw` is not
   needed.
3. Completeness: describe the run as `Saturation.Tables` and the goals it
   opens, prove `Saturation.Fair`, and take `Fair.complete`
   (`Framework/Saturation.lean`). Honest exhaustion follows from
   `Tier0Cert` (`Framework/Tier0.lean`), or pair by pair from
   `Fair.covers_pair` once everything the run holds for the query is
   emitted when the machine reports that it is done.
4. The converse and the mirrored program: run the machine on one
   orientation and prove `CostedRuntime.SelfConverse`
   (`Framework/Oriented.lean`).
5. A machine that shows what a proved machine shows, step for step up to
   order and equivalence: prove `Runtime.SameTrace` by a simulation
   (`Runtime.trace_of_sim`, `TraceEquiv.of_perm`) and take
   `SameTrace.keeps`. A machine that only emits the same answers:
   `SameRun` (`Framework/Transfer.lean`).
6. Cost: `Framework/CostCalculus.lean` and `CostSpec.lean` for the ticks of
   the traversals, `Framework/Race.lean` for races, `Framework/Admission.lean`
   and `Latency.lean` for the statement a rung is admitted by.

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
