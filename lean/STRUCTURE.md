# Structure of the Lean development

The development is layered so that a new rung proves only what is new about
its machine.

The engine on master is rung 1, the symmetric engine (`Rungs/Symmetric/`) run
on one orientation of its input. It has the three laws, is the base of the
ladder, and costs the same whichever direction a query is written in
(`Symmetric.rung1_lawful`, `rung1_ladder`, `rung1_directionFree`,
`Manifest/Rung1.lean`). Master also has the specification,
the kernel, the shared libraries and the constraint domain of sorts
(`Sorts/`). The machines before it are in the history
(see "Where the earlier machines went"). No file is out of the build.

```
Trusted/        the specification: syntax with sort declarations, semantics (what a sort
                and a span mean, Semantics.lean), answers, steps and runtimes with the
                Tier-0 properties (Runtime.lean), what a constraint system gives an
                engine and the laws it satisfies (Domain.lean), Rung and Preprocessor
                (Engine.lean),
                the three laws (sound, complete pair by pair, honest when done) and the
                ladder (Properties.lean),
                the cost monad (CostMonad.lean),
                the charged primitives on nodes (Charged.lean), the kernel an engine is
                written against and what a kernel rung is (Kernel.lean),
                and the cost model (Cost.lean) by which rungs are judged:
                cost is coverage latency, the ticks until an emitted answer covers a
                ground pair, and never depends on a query halting
Kernel/         the executable kernel of spans as written (match, solve, span) and its proofs;
                the normal form of expressions (NormalForm.lean, NormalFormCorrect.lean,
                NormalFormStable.lean, Order.lean), the derivation kernel's rules over any
                constraint domain (Derivation.lean) and the algebra of a lawful domain
                (DomainLaws.lean)
SpanLayer/      span-level semantics, derivations, coverage vocabulary
Lib/            facts about lists and greatest fixpoints that mention no rwlog type
Rungs/Framework generic theorems about any Runtime / Rung; and the unfolding race: what a
                race is and its specification (RaceSpec.lean), the ways of unfolding,
                written once against the derivation kernel: unfolding to a depth, a walk
                between boundaries, and the walk with shared sub-chains (Unfold.lean), and
                the proofs that each meets the specification (Unfolding/)
Rungs/Symmetric/ the symmetric engine of `SYMMETRIC_ENGINE.md` (Machine.lean): a table for
                every goal, every split of a chain and of a meet as a group of strategies
                (join, push from either side), groups balanced by their levels, one
                request a step; every strategy of a group that works has a turn of
                bounded work (`turn`: `turnTicks` ticks times its `weight`, one more than
                the number of strategies upstream of the tables it reads), does one
                unit at a time, and owes in later turns what its last unit cost beyond
                the turn (`Group.owed`); and beside the groups of a chain goal an unfolding race
                (`askRace`; `engine` takes the `Unfolder`), asked at the end of a round of
                the goal at its next depth with what is left of the rounds and work of
                the goal as its limit (`Kernel.within`, `Trusted/Kernel.lean`): an ask
                that costs more is given up and charged, and the next waits until twice
                as much is left; a final verdict completes the table. A level rises by what was spent, and the engine charges
                itself one tick for a unit of work that did something, so a group that
                worked has risen at every kernel (`workGroup_did`). The table of a
                goal that is its own converse holds the converse of everything it holds
                (SelfConverse.lean, `root_reach`). Proved so far: an answer enters a
                table by `addAnswer` and in no other way (Invariant.lean, `Reach`); the
                invariant that every answer of a table is an answer of the goal of the
                table and every strategy fits its goal (Goals.lean, `Inv`; kept by a
                request as part of `Good`, Kept.lean, since an answer of a race is an
                answer of its goal by the specification of the race, on first-order
                input). A complete table never changes again, and
                nothing nested in the round of a table completes it (Rounds.lean, `Keep`,
                `stable_request`). The interface check (a chain goal is
                complete with no answer when the other side fails under every interface
                one side can show, read from the program) is a strategy of its own; the
                invariant and the mirror criterion cover it. Towards completeness:
                the cursor of a join combines a pair once (Cursor.lean,
                `Cursor.next_spec`); what the cursors of every strategy mean (Progress.lean,
                `Prog`: the table covers what its rule makes of everything a cursor has
                passed) holds of the strategies made for a goal and is kept by a whole
                request, with the goals of the tables distinct and good (Kept.lean,
                `Good`, `good_request`); and the interfaces read from the program are
                right about it (Edge.lean, `readEdge_sound`). The reading is a part the
                engine is given (`EdgeReader`, Machine.lean): what the proofs need of one
                is `ReadOk` (Progress.lean), that it is right about the program and does
                not give up for ever, and the reading of rung 1 has it (ReadLive.lean,
                `readOk`, `good_runsReader`). How the ticks are shared: the cursor of
                a join shares its ticks among its pairs by the unions their answers came
                from and still reaches every pair it has filed, by a measure that falls
                (Cursor.lean, `Cursor.rank_fall`, `rankLt_wf`); and the record of a
                request (Turns.lean, `Req`, `req_request`), which takes what a race means
                as a parameter (`RaceSem`, for the engine `raceSem`): a table completes by
                a strategy with nothing left to do or by a final verdict of its race
                (`Raced`, `askRace_spec`), and a round of a table leaves its race blocked
                with fewer rounds than it has spent and needs for its next ask, or one
                depth further, or having given up an ask that costs more than it was
                allowed, when it was allowed more than twice what it gave up before, or
                the table complete (`Asked`), so a table that has rounds for ever and a
                race with a final verdict at some depth completes (Lines.lean,
                `Requests.race_done`);
                the groups of a table change
                in its own round only, where each strategy moves on, a group all of whose
                checks are dead is removed, one group works with the tables it reads
                settled, or, where it is a union, with every member settled or some
                member fed that has been fed no more than this one (`Fed`; a union gives
                a round to the member its rounds have cost the least, `feedGroup`, so
                that its members share the ticks), and the round is balanced: a group worked, each of its
                strategies having worked or owing less than it did (`GrStep`, `OStep`), or
                it stands as it stood, its strategies the same and owing what they owed, while a lower one rose
                (`Turn`, `Balanced`); of the groups a goal begins with one has a span, a call, a
                union or a join, and one that has none is all checks (`shaped_expand`); a table
                marked complete has a strategy with nothing left to do that reads complete
                tables only, and the complete tables stand in an order in which tables that
                complete together stand together and a table whose answers are pushed
                stands lower (`Founded`, `IsRun.founded`); a push that works sees every
                answer of its side, drops those a later one covers once the side is complete, and is nearer to every
                unit left: opening the goal of an answer, or combining an answer of an
                opened goal (`SStep.push`, `step_work_push`); the goals a push opened share
                their rounds by where the pushed answers came from, through a second cursor
                of the push that its own work never touches (`feedPush`, `work_feedOf`,
                FeedCursor.lean, `feedGroup_fits`), and in a round where its group worked
                each unit of that cursor is taken, with its table settled, or is of an
                answer superseded, or is nearer to its turn (`FedP`, `turn_feedToks`), so
                the table opened for an answer never superseded is settled again and again
                (Turns.lean); and an edge is read in the end, from a depth that the node
                and the program give (ReadLive.lean, `readEdge_some`); and of a table that
                has rounds for ever every strategy of every group works for ever, since
                what it owes cannot fall for ever, with as many groups from
                some request on (Lines.lean, `Requests.lines`, `Line.step`), and every member of a union
                that works for ever is settled again and again
                (`Requests.union_settled`). Towards
                completeness: a run of requests (`IsRun`) holds for each goal the answers
                of its table (`held`) and does not neglect the tables that are complete at
                some time or have rounds for ever (`opened`); a complete table is served by
                the strategy that completed it (Served.lean, `IsRun.served_done`), a table
                with rounds for ever by a strategy of the group that works for ever
                (Saturated.lean, `IsRun.served_live`), so the run is saturated (`IsRun.saturated`); the
                states of the engine are such a run, and the machine is complete, honest
                when it reports that it is done, and emits no progress certificate
                (Correct.lean, `Symmetric.complete`, `honestExhaustion`,
                `honestProgress`); no answer of a table covers a later one, and the final report is the
                maximal emitted answers (`finalMaximal`). So the engine has the three laws
                (`Symmetric.pointComplete`, `Symmetric.laws`), and on a root that is its own
                converse every step shows answers that are their own converses rearranged
                (SelfConverse.lean, `selfConverse_of`; Correct.lean, `engine_selfConverse`).
                With no rewrite before it and run on one orientation it is a rung that has
                the laws at every kernel rung, the base of a ladder, and its cost does not
                depend on the direction a query is written in (Rung.lean,
                `Symmetric.rung_lawful`, `rung_ladder`, `rung_direction`,
                `rung_directionFree`, for any unfolding race and any reading of edges
                that meet their specifications; `rung1` is the one with the raced
                unfolding and the reading `runsReader`). A second reading reads an
                edge from the far end of the node and carries interfaces only (`faces`,
                Machine.lean), and `bothReader` runs the two side by side; it is right
                about the program and does not give up for ever (Faces.lean, `faces_ok`,
                `faces_some`, `good_bothReader`), so the engine with it, `bothWays`, has
                the laws and the bound on direction (Rung.lean). It is not a rung of the
                ladder until it is admitted. Every answer a table holds was made
                by a rule of the kernel from answers the tables hold, or by the
                unfolding race: a property of answers that the rules keep, but for
                the unfolding of marked answers, and that the answers of the race
                have, is a property of everything a run holds until a table holds
                a marked answer (Provenance.lean, `prov_request`, `prov_init`).
                Owing nothing to a name `h` is such a property, marked the
                answers of the body of `h`, when the body of `h` needs a name the
                unfolding race never reads whole (Light.lean, `rules_light`,
                `light_raced`, `prov_light`). Not
                proved yet: any bound on the cost of either in the size of the input.
Sorts/          the constraint domain of sorts and the proof that it is lawful
Manifest/       rung 1's manifest (Rung1.lean): headline statements, trusted files and
                axioms, all checked by the build
AxiomAudit.lean every declaration of the library, checked to use only the three standard axioms;
                every file under RwLog/ is in the build; the shared layers import no machine
                (the commands are in RwLog/Lib/Audit.lean; nothing is listed by hand)
`SYMMETRIC_ENGINE.md` is the design note for the engine of rung 1.
`SYMMETRIC_ENGINE_SIMULATION.md` records measurements of that design against
R005, taken once with `scripts/symmetric_engine_tables.py` and
`scripts/r005_interpreter.py` (R005 at the tag `epoch-1` outside Lean); staying
within a polynomial of an earlier machine is not asked of a rung. The build
runs nothing on concrete inputs: what a machine does is proved.

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
| Coverage in the interpretations of a class | `SpanLayer/Modulo.lean` | `LCov`, `LEq`, `Live`, `DeadR`, `Backed`, `Ref`, `DC`, `GCov`, `GEq`, `Dom` |
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
| Well-formed queries built from a well-formed one | `Rungs/Framework/Direction.lean` | `ProgramOf.WellFormed.of_sub`, `.conv`, `.seq_left`, `.seq_swap`, `.and_of_seq`, `.dual` |
| Converse of a program | `SpanLayer/Dual.lean` | `Program.sem_dual` |
| Greatest fixpoints by iteration | `Lib/Gfp.lean` | `gfpFrom`, `gfpFrom_closed`, `subset_gfpFrom` |
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
 and `Complete.pointwise` are generic too.
* `RunProperties.lean`: what proofs use beside the laws and no rung is asked:
  `StepEquiv` / `ShownEquiv` / `TraceEquiv`, and `FinalMaximal` (the final
  report is the maximal emitted answers: the filter that leaves out an answer
  another answer covers).
* `Transfer.lean`: moving theorems between runtimes and through rewrites.
  `SameRun R' R` says two runtimes emit equivalent answers and halt together;
  it carries `Tier0` and `TerminatesOn` from `R` to `R'` (`SameRun.tier0`,
  `SameRun.terminatesOn`), and `SameRun.of_sim` builds it from a simulation.
  A rung is one runtime on the original input (`Rung.runtime`,
  `Trusted/Properties.lean`); `Rung.sound`, `Rung.pointComplete` and
  `Rung.honest` carry the machine's laws through the preprocessors, and
  `Rung.laws` is the three together. A rung has a list of preprocessors, run
  one after another, each at the kernel of the sorts of the program it is
  handed (`Preprocessor.runAll`, `Trusted/Engine.lean`), so the laws of the
  list follow from the laws of its members (`Preprocessor.runAll_wf`,
  `runAll_equiv`, `runAll_adds`) and a rung that adds a rewrite proves the
  laws of that rewrite only. A preprocessor
  may add sort declarations (`Preprocessor.adds`, `Sorts.Extends`), so the
  machine is run on sorts that may declare more than the program's. Its
  theorems are about its answers read in those sorts, and the three theorems
  ask that the answers say how they are read (`Answer.SelfRead`,
  `Framework/Answer.lean`), which the answers of every engine do
  (`Answer.selfRead_sigma`): each is a representative carried with its
  sorts. `Span.denAt_sorted` and `Span.firstOrder_sorted`
  (`SpanLayer/Sorts.lean`) say what holding an end of a span to a sort does.
* `Void.lean`: goals that relate nothing. The pairs a goal and a derivation
  of its node stand for (`pairsOf`); a goal no derivation of whose node
  relates a pair between its boundaries (`Void`) has no answer
  (`void_no_ans`); the goal of a query that relates nothing is void
  (`void_of_pairs`), and so is a chain or a meet with no boundary one part
  of which is void (`void_mkSeq_left`, `void_mkSeq_right`, `void_mkAnd`).
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
  everything the run ever holds, up to coverage. `Saturation.Saturated` is every
  opened goal served. `Saturated.covers`: a saturated run covers the pairs of every
  ground relation the node of an opened goal derives, by induction on the
  depth of the derivation and then on the node. `Saturated.complete` is
  completeness at the query, `Saturated.covers_pair` the same pair by pair, and
  `Saturated.covers_valid` says a valid answer
  found by any schedule is covered by every saturated run that opens its goal.
  Nothing is assumed of the order of work or of tables growing. A machine
  proves `Saturated` of its runs and receives completeness.
  `Served.checkL` and `checkR` serve a chain that has no answer by the
  interface check.
* `Oriented.lean`: a machine run on one orientation of its input
  (`CostedRuntime.oriented`, `Trusted/Cost.lean`). The choice made from the
  converse of a query, and from the mirror image of an input, is the choice
  made from the input the other way round, or the same choice of a node that
  is its own converse (`orient_conv`, `orient_dual`), and the program and
  the node chosen from a well-formed input are first-order (`progFO_orient`,
  `fo_orient_root`). A machine that shows, on first-order input with a root
  that is its own converse, sets of answers that are their own converse
  (`CostedRuntime.SelfConverse`) shows the same from two choices that are
  each the other way round (`trace_of_mirrors`), and any machine run so pays
  the same on an input and on its mirror image (`oriented_paid_dual`).
* `GroundMirror.lean`, `OrientedSem.lean`, `OrientedLaws.lean`: a machine run
  on one orientation has the laws. In the mirrored program the mirror image
  of an expression derives the converses (`gd_dual`), and the program in
  normal form derives what the program derives (`gd_normed`); so the input
  chosen relates the same pairs, or the converses when the run is swapped
  (`orient_pairs`), and is well formed (`wf_orient`, with
  `Kernel/NormalFormCalls.lean`: the normal form calls no new name). Hence
  `CostedRuntime.oriented_sound`, `oriented_complete`, `oriented_honest` and
  `oriented_laws`.
* `OrientedDirection.lean`: a machine run on one orientation that has
  `SelfConverse` costs the same in both directions. Its runs on an input, on
  the converse and on the mirror image show the same the right way round
  (`oriented_trace_conv`, `oriented_trace_dual`) and pay the same from the
  first step on, with `8 * n + 12` ticks more for choosing the input on a
  converse (`oriented_paid_conv`); so it has `DirectionFree`
  (`oriented_directionFree`, and `oriented_directionFree_bound` within
  `12 * (c + n + 1)`).
* `Derivation.lean`: every engine is sound, at every kernel of a constraint
  domain that is lawful at well-formed sorts (`Engine.sound`). An answer
  exists only with the proof that it is valid, so the theorem uses nothing
  about the engine.

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
  ladder keeps every win on its record). `Ladder.lawful`: every rung of a
  ladder has the laws (`CostedRung.Lawful`, `Trusted/Properties.lean`), which
  the ladder asks of the base and of every rung put on top.

* `Holding.lean`: saying what a state holds. `Pack S N A α` lists a value of
  `α` as representatives, nodes, answers and numbers so that the listing can
  be told apart from whatever follows it (`Pack.cancel`), which makes the
  listing of a pair, a list or an alternative one to one from the listings of
  its parts (`Pack.inj`); `Pack.ofInj` lists a structure through its fields.
  This is how an engine meets `Engine.held_inj`.

* `RecordWitness.lean`: `Admits` has inhabitants. Two toy
  engines, admitted one above the other over a base that never answers, the
  second for an exponential gain over the record that holds the polynomial
  win of the first. They are not a `Ladder`, which asks for the laws. They are not machines for the
  language. On the way: when the normal form of an expression is one span
  (`normB_or_span`, `normB_dual`, `normB_fill`).

`Rungs/Framework/Unfold.lean` has the unfolders, each written once against
the derivation kernel: `eagerRace` (unfold every call to a depth, then
evaluate), `walkRace` (the same answers, walking a chain from a boundary),
`sharedRace` (the walk with shared sub-chains), and the races of them side
by side (`walkShared`, `raced`). `Rungs/Framework/Unfolding/` proves that
each meets the specification of a race (`UOk`, `Framework/RaceSpec.lean`).
`Sem.lean` says what an unfolding to a depth stands for (`GR P d`: the
derivations on which every node is read). For each evaluation one file reads
its text as a value (`EagerVal`, `WalkVal`, `SharedVal`) and one proves the
specification of what it builds (`Eager`: `POk`, `eagerRace_ok`; `Dir`,
`WalkChain`, `Walk`: `WOk`, `walkRace_ok` in both directions; `Shared`:
`SmOk` with the memo's invariant `MemoOk`, `sharedRace_ok`). `Races.lean`
has `good_eagerRace`, `good_walkRace`, `good_sharedRace`, `UOk.race`
(two races side by side), and `good_raced`, the race rung 1 uses.

The walk and the shared evaluation are proved for whatever the nodes are
taken to derive, so long as a call derives what its body does and a union, a
chain and a meet what their members do (`OLaws`, `Sem.lean`). So a final
unfolding has read whole every derivation that relates a pair between the
boundaries, of the program and of any larger program with those equations
(`Whole`, `whole_raced`, `Races.lean`). `Never.lean` uses that for a name
that is never read whole, such as `c := id | c ; id`: given spans that stand
for its derivations and carry constraints that are all different (`Tags`),
an answer of a final unfolding is an answer of the goal in the program where
the name derives nothing (`light_of_final`), because only finitely many
relations are read whole at a depth (`gr_finite`).

`Rungs/Framework/Race.lean` defines `Cost.race` and proves what it returns and spends
(`Cost.race_val`, `Cost.race_ticks`, and from below `Cost.le_race_ticks`), for
any two computations.

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
the most cells a computation had live at once and `held` the cells it
allocated and did not abandon (`Cost.within`, and so `Cost.race`, abandon).
Both are about one step. Between two steps what is live is the state: a
machine has the cells of each of its states (`CostedRuntime.live`), and
`CostedRuntime.space P q n` is the most cells live at one moment of the first
`n` steps, the state a step starts from together with the peak of the step.
An engine lists what its state holds (`Engine.held`) and proves the state is
determined by the listing (`Engine.held_inj`); the cells of the listing are
counted by `Engine.liveAt`, with representatives of the size the kernel rung
gives them (`KernelRung.cells`). `Rungs/Framework/Holding.lean` builds such a
listing piece by piece (`Pack`), and the symmetric engine's is `heldOf`
(`Rungs/Symmetric/Machine.lean`). A gain is stated for a resource
(`Resource`, time or space): in a larger program the residue for space is
taken after the same amount of work (`CostedRuntime.MeetsIn`), and a rung
admitted by a win in space keeps the time of the rung below (`Admits.time`).

A kernel rung (`KernelRung`, `Trusted/Kernel.lean`) gives, for the sorts of
each program, a type of representatives, a constraint domain on it that is
lawful when the sorts are well formed, and a kernel that returns what the
domain returns (`Kernel.Refines`). No charge of an operation on
representatives is postulated: the trusted files fix no kernel.
`Engine.costedAt` is an engine at the derivation kernel over a kernel
(`DerivationKernel.over`). Two rungs exist. `sortsRung`
(`verified/lean/RwLogVerified/SortsRung.lean`) is the one engines are judged
at: the charge of each operation of the domain of sorts is the tick bound
proved of the Rust function on the store of `verified/rust/src/store.rs`
(see `verified/README.md`); its charges are not computable. `Witness.sized` (`Rungs/Framework/RecordWitness.lean`) is a toy
for the proof that the admission rule has inhabitants. The operations on
nodes and the interning of answers are charged as postulated at every kernel
rung so far (roadmap L45).

In epoch 1 each machine was written twice, in the same words: once against
the kernel (`Gen.lean`) and once in `Cost`, with a `Reading.lean` proving the
two equal. That ended with the port (roadmap L04): each machine exists once,
as an engine, and proofs are carried out on that text at
`DerivationKernel.over`.

## Where the earlier machines went

Epoch 1 (rungs R000 to R005 on the size-charged cost model) is at the git
tag `epoch-1`; `EPOCH1.md` says what its theorems are about. The tabled
machine, the mirrored machine, R005 as an engine for every kernel, and the
proofs of the properties that are no longer asked of a rung (equal traces of
two writings, of the converse and of the mirror image; halting where another
machine halts; the lower bounds on R005) were on master up to the commit
`3c03bb3` and are in its history.

## Proving a new engine

An engine is written once against the derivation kernel
(`Trusted/Kernel.lean`), in any monad, and proved at
`DerivationKernel.over D K hK P` in `Cost`. A rung owes the three laws
(`Runtime.Laws`, `Trusted/Properties.lean`); they come from these places.

1. Sound, free for every engine: `Engine.sound`
   (`Framework/Derivation.lean`).
2. Reading the text as values: open the goal with `at_cost K hK`
   (`Framework/KernelAt.lean`), rewrite the traversals with the `_std`
   lemmas and `Cost.*_val` (`Framework/TraverseStd.lean`,
   `Framework/Cost.lean`), the rules with `Ans.leaf_val`, `join_val`,
   `meetA_val`, `inj_val`, `unfold_val` (`Framework/Rules.lean`), and the
   goal operations with `Framework/GoalsVal.lean`. `rw [Cost.bind_val]`
   works on a bind of the kernel's monad after `at_cost`; `erw` is not
   needed.
3. Complete, and honest when done: describe the run as `Saturation.Tables`
   and the goals it opens, prove `Saturation.Saturated`, and take
   `Saturated.covers_pair` (`Framework/Saturation.lean`): every pair the
   relation relates is related by an answer the run holds. Both laws follow
   once everything the run holds for the root is emitted, at the latest when
   the machine reports that it is done (`Symmetric.pointComplete`,
   `honestExhaustion`).
4. The rung: run on one orientation the machine keeps the laws
   (`CostedRuntime.oriented_laws`, `Framework/OrientedLaws.lean`), and
   `CostedRung.Lawful` for the engine with no rewrite is that
   (`Symmetric.rung_lawful`); with rewrites, `Rung.laws`
   (`Framework/Transfer.lean`) carries them through.
5. Cost forward and backward: prove `CostedRuntime.SelfConverse` and take
   `oriented_directionFree` (`Framework/OrientedDirection.lean`).
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
4. Nothing is added to `AxiomAudit.lean` by hand: it checks every
   declaration of the library, that every file is imported by `RwLog.lean`,
   and rule 2. The build is `lake build --wfail`: no `sorry`, no warnings,
   no new axioms. A manifest (`Manifest/`) names its headline theorems with
   `#assert_axioms` and what it trusts with `#trusted_files`
   (`RwLog/Lib/Audit.lean`); every file under `Manifest/` is built.

A rung is admitted by `Admits` (`Trusted/Cost.lean`); `ADMISSION.md` says what
it asks.
