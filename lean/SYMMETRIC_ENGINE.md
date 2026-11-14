# The symmetric engine: design note

Written 2026-11-13 against master `ffaac8a`, for roadmap milestone M3 part A (the engine design note) and milestone M6 (ledger L01, L20, L29). It confirms the early verdict in `symmetric-engine/lineage-verdict.md` of the project files and reverses nothing in it.

Everything marked *measured* was run and is reproducible from this repository. Everything marked *argued* is an argument on paper. Nothing here is proved in Lean.

## 1. Decision

M6 builds one new machine, with these five properties.

1. **It evaluates a normal form, not the syntax tree.** Before the first step, program and query are rewritten so that `;` is a flat list, `&` is a multiset, `|` is a set, and converse occurs only on calls. Two inputs that differ in the bracketing of `;`, in the order or bracketing of `&` or `|`, give the same first state.
2. **It picks one orientation of the whole input.** The normal form of the input and the normal form of its mirror image are both built and the smaller, in a fixed structural order, is run; answers are swapped back if the mirror image was chosen. A query and its mirror image are then the same run.
3. **A goal and its converse share one table.**
4. **A chain goal is a table on an interval of a flat chain.** Every split of the interval is a strategy of that table, and so is pushing the answers of a complete side into the other side, from either end. The strategies of a table are balanced by the ticks they have spent (since the fourth revision of section 3: the splits of a table are balanced by their levels). No strategy is chosen by syntax.
5. **Nothing runs beside the tables.** There is no unfolding race, no mirror race and no hedge of whole machines.

Points 1 to 3 give the exact properties (mirror image step for step at equal ticks, `SeqAssoc`, `AndComm`, `AndAssoc`). Points 4 and 5 give the cost. The two are separate, and section 3 explains why that separation is the main finding.

**Revision, 2026-11-14: points 2 and 3 as built.** Point 2 as written leaves two things open, and point 3 does not close them.

*The engine cannot make the choice.* An engine is handed the root node and reads bodies through the kernel. It cannot build the mirrored program, so it cannot compare the input with its mirror image. The first form of the machine, run on `add ; @2` and on its mirror image, shows different traces even at a kernel that charges nothing, because it visits members in their stored order. So the choice is made where the input is loaded (`orient` and `CostedRuntime.oriented`, `Trusted/Cost.lean`), and a rung says whether it is run that way (`CostedRung.oriented`).

*An input can be its own mirror image.* Then there is nothing to choose between, the run is one run, and the criterion asks that this run shows, at every step, a set of answers that is its own converse. Take `u = a -> b | b -> a` and `w = b -> c | c -> b`, and the query `u ; w ; w ; u`. Program and query are their own mirror images. The splits `u | w ; w ; u` and `u ; w ; w | u` are mirror images of each other, and they are balanced by the ticks they spend. A kernel may charge an operation and its mirror image differently (nothing in `Kernel.Refines` says otherwise, and the 2026-11-13 revision of section 6 withdrew the request that it should not), so the two splits get different levels and an answer can arrive requests before its converse. Sharing a table between a goal and its converse does not help: the converse of `u ; w ; w` is `w° ; w° ; u°`, a different node from `w ; w ; u`, and only the program being its own mirror image makes them the same relation.

What is built:

1. *Four inputs, not two.* An input stands with its mirror image (the mirrored query in the mirrored program), with its converse (the converse query in the same program), and with the converse of its mirror image. The loader compares the program with the mirrored program body by body in normal form and runs the lesser; the candidates for the root are the query and its converse, and in a program that is its own mirror image the mirrored query and its converse too. The least candidate is run, and what the run shows is swapped when that candidate relates the pairs the other way round. The choice reads normal forms only, and it is the same from each of the four. This gives the criterion on the mirrored input and on the converse query at once, with equal ticks on the mirrored input, for any kernel.
2. *When the least candidate stands both ways round*, the relation is its own converse, and the run is of the union of that node with its converse. That node is its own converse.
3. *The table of a goal that is its own converse holds the converse of everything it holds.* Whenever an answer goes in, its converse goes in with it (`addAnswer`, `Rungs/Symmetric/Machine.lean`). So a run whose root is its own converse shows, at every step, a set of answers that is its own converse, whatever the kernel charges and whatever order the machine visits things in.

Point 3 of the decision (a goal and its converse share one table) is then no part of any exact property. It remains a saving and is not built. Whether it is one is not known: the kernel gives equality of nodes and no order, so every opening of a goal would also look for the converse goal, which doubles the comparisons of every lookup, against at most a factor of two on runs that open both a goal and its converse. It is on the billboard as SIM12 and is not owed by any criterion of M6.

Two ways not taken. Asking every kernel to charge an operation and its mirror image the same would make the machine symmetric with no choice of orientation, but only if the machine never reads a stored order: every request would have to read what the tables held when it started, which costs requests in every recursion, and every later rung would owe the same proof. Balancing by the number of operations instead of their ticks is symmetric at any kernel and gives up the cost bound, since one operation can cost any amount.

F1 below stands as corrected here: the orientation makes the mirror image the same run, except where the input is its own mirror image, and there the exact property comes from item 3.

Not chosen: full direction-free nets, the old engine's two-ended alternation as an evaluation order, and any hedge. Section 4 compares them.

## 2. What the exit criteria force

Three facts follow from M6's exit criteria alone, before any design.

**F1. Exact symmetry is a property of the representation, not of the search policy.** *Argued.* No total order on spans is preserved by swapping (for `l ≠ r`, the spans `l -> r` and `r -> l` would each have to be below the other). So a machine that visits tables, answers or branches in any stored order cannot have its mirror-image run be literally its run reflected, and a proof of equal ticks for it has to show every traversal is insensitive to order. A machine that is given the same state for both writings needs no such proof. That is why the decision normalises and orients the input instead of asking the policy to be symmetric.

**F2. With F1 in place, cost-based choices are free.** `r005/design-notes.md` finding 2 says a hedge must preempt by actual cost, and that this breaks step-for-step `DualTrace` unless a run and its mirror image cost exactly the same. Under points 1 and 2 they cost exactly the same for every policy, because they are the same run. So the M6 engine and every rung above it may schedule by ticks.

**F3. The engine must be within a polynomial of the yardstick on the cheapest writing of the input.** *Argued.* The engine's run does not depend on the writing. `Simulates` must hold against the yardstick (R005) on every writing. So the engine's cost is bounded by a polynomial of the least cost R005 has over all bracketings, both directions and all orders of `&`. There are exponentially many writings, so this cannot be had by racing them. It is the theorem M6 has to prove and its main risk (section 7).

A consequence of F3: an engine that picks one bracketing by a rule, however symmetric the rule, fails, because R005 run on a better bracketing beats it. The choice has to be made by cost, per goal, while running.

## 3. The machine

### Normal form

A node is one of: a span; a call, with an orientation bit; a chain (a list of at least two nodes, none of them a chain); a meet (a multiset of at least two nodes, none of them a meet); a union (a set of nodes, none of them a union; the empty union is `zero`). Converse is pushed inward: it reverses a chain, maps over a meet or a union, swaps a span, and flips the bit of a call. A call with its bit set reads the converse of the definition's body.

Nodes are interned, so equal nodes are one identifier. Every sub-interval of a chain is a node too, so equal stretches of two different bodies share their tables. Sets and multisets are ordered by a fixed structural order when they are interned; the order is used for nothing else.

Adjacent spans are **not** fused during normalisation. Fusing them would make the first state depend on composition and simplification being associative up to equivalence in every theory, which is not known before M5. The interval tables compose them anyway.

### Goals and tables

A goal is `⟨lb, node, rb⟩` with optional boundaries, as in R001. Its key is the node's identifier and the canonical representatives of the two boundaries (M5). The goal `⟨rbᵒ, nodeᵒ, lbᵒ⟩` has the same table, read swapped. A table holds answers, a completion flag, and what each of its strategies has spent.

### Strategies

| Node | Strategies of `⟨lb, node, rb⟩` |
|---|---|
| span | Compose with the boundaries. |
| call | The body's goal with the same boundaries. |
| union | The members' goals with the same boundaries. All run; a union is not a choice. |
| chain `[i, j)` | For each split `k`: join the answers of `⟨lb, [i,k), none⟩` and `⟨none, [k,j), rb⟩`. For each split `k` and each end: once that side's table is complete, push each maximal answer's interface into the other side as a boundary (R001's push, and the rung 6 thread's push without join, `Directed.Gen.seqCandidates`). |
| meet | For each member: its goal with both boundaries, then push each answer's two interfaces into the remaining members as one meet goal. Join of two halves for every split of the multiset into two is **not** offered (there are exponentially many); see open point O3. |

### Balance

Work is done one kernel operation at a time. A goal that is asked to work passes the request to the strategy of its table that has spent least; where several are level, each of them is advanced. A strategy that has a pair of answers not yet combined combines one pair. A strategy with nothing to combine passes the request to the sub-goal it has fed less. A strategy charges itself with everything spent below it on its behalf. A request to the root goal is one step of the machine.

A table is complete when one of its strategies has combined everything from complete sub-tables (for a union, when all members are complete), and by R001's exact check on the whole state for goals that depend on themselves. Nothing more is spent on a complete table, and its other strategies are dropped.

**Revision, 2026-11-13: requests alternate between two rules.** The rule above (the *share* rule) halves a goal's share at every level of nesting, so an answer under `k` nested choices that each have a member which never finishes arrives after about `2^k` requests (section 5.4). So every second request is instead one *flat round*: each opened goal that is not complete does one unit of its own work. The flat round alone is slow when many goals are open, which is where the share rule is good; alternating costs at most twice the better of the two. A strategy's spent ticks count work done under either rule.

**Revision, 2026-11-13 (third): the interface check, whole rounds, and no claim about alternating.** From the attack on O1 (`SYMMETRIC_ENGINE_SIMULATION.md`, which has the measurements). Three changes.

1. *A new strategy, the interface check.* For each split of a chain goal and each side: the first (or last) span of every answer of that side is one of finitely many spans known from the program text, found by following the edge of the node inwards, composing adjacent spans, through unions and through each call once. The other side is opened under the interface of each of those spans, as ordinary goals with a boundary. If all of them complete with no answer, the chain goal is complete and empty. Without it the engine never halts on `p ; q` when every answer of `p` ends in a constructor that no answer of `q` begins with and both have infinitely many answers; R005 halts there in its second round, by unfolding, so the engine as first designed neither simulated R005 nor halted wherever R001 halts. The check reads no bracketing.
2. *The flat round is a whole round:* each strategy of each open goal does everything its inputs allow. With one unit per goal, a table can gain answers faster than its reader reads them, and the fair OR family with three members that never finish takes 12, 39, 304 requests for `k = 2, 4, 6`; with whole rounds every fair OR family measured takes `2k + 7`. A whole round is a round of R005's machine on every split at once that repeats no pair.
3. *The sentence "alternating costs at most twice the better of the two" is withdrawn.* It is false by requests (a flat round costs as many ticks as there are goals) and false when the rules are balanced by ticks, because both rules write the same tables: counting down halts at 10398 ticks for `k = 8` under whole rounds alone and at 979757 when they are balanced with the share rule. Which rule serves a request is therefore open again (O6 below). The share rule alone is exponential to halt on counting down, where R005 is polynomial; whole rounds alone are exponential on the middle-restricted family with pushes, where the share rule is polynomial.

What this forces to be redone: nothing built. Section 5.4 measured a model of the rules and is superseded by tables 4 to 6b of the simulation note. The freeze list of section 6 is unchanged: the interface check uses goals, boundaries and `join` as they are, and its conclusion (a chain is empty because every interface of one side fails on the other) is a completion, not an answer, so the derivation kernel needs no new rule.

**Revision, 2026-11-13 (fourth): the split balance replaces the share rule and the flat round, and the interface check is narrowed.** From the second attack on O1 (`SYMMETRIC_ENGINE_SIMULATION.md`, section 9, which has the measurements).

*Why.* R005 was ported out of Lean (`scripts/r005_interpreter.py`, which reproduces the 57 numbers Lean guards for the inputs of the simulation note) and run on the ladder family. R005 is polynomial on it (about the third power of `n`, to `n = 34`). The engine of the third revision is exponential on it under whole rounds, under the share rule, under unit rounds and under both rules that had been left untried. The cause is a split that the cheap writing does not have: `G ; F | r` has a left side that completes, its answers are pushed into `r`, and each pushed goal has the same split again, which is a forward search with `2^d` goals at depth `d`. Whole rounds serve all of it; the share rule halves the useful line at every level. So reading every split, which is what gives `SeqAssoc`, does cost more than a polynomial under those rules. It is not yet a conflict between `SeqAssoc` and `Simulates`, because the rule below repairs it and reads no bracketing.

*The request rule.* Everything said above under "Balance" about which strategy gets a request, and both earlier revisions of it, are replaced by this.

1. The strategies of one split of a chain goal (its join and its two pushes) are a *group*. The interface checks of a chain goal are one more group. A goal that is not a chain has one group.
2. Every group has a *level*, a number kept in the goal's table. The level of a goal is the lowest level among its groups.
3. A request to the root is a round. In its round a goal lets only its lowest groups work; if none of them can do anything, the next lowest, and so on. A group works by doing its own work and giving a round to every goal it reads. A goal has at most one round per request, whoever asks.
4. The level of a group rises by the ticks of its own work and by how much the levels of the goals it reads rose in the round. A goal met again below itself adds nothing.
5. Where a goal has one group, the group does everything its inputs allow. Where it has several, each strategy of a working group does one unit.

A split is charged for the *lowest* group of each goal it reads, not for everything spent there. So the hedging done below a split is not charged to it, the allowance of its competitors does not grow by a factor per level of nesting, and a search that only one split starts is held to the level of the cheapest split. A request is not divided among the goals a group reads, so nothing is starved by a sibling that never finishes.

*Measured* on the prototype (table 8 of the simulation note): polynomial on the ladder (to `n = 64`), on counting down, on the middle-restricted family with pushes (about the sixth power to `k = 14`, where the share rule had the fourth and R005 triples per step), and on fair OR with one and with three members that never finish, where the answer arrives in `2k + 4` requests. It is the first rule that has both the middle-restricted family and fair OR with three such members. Nothing is proved.

*The interface check is narrowed.* It is offered only for a side that contains a call, and its goals are opened when it first runs, at one tick each. Offered for every side it is exponential on the middle-restricted family under every round rule (9346012 ticks and 253966 goals at `k = 7`), which the third revision did not measure far enough to see; the prototype also opened its goals at no charge. A side with no call has finitely many answers, its table completes, and the push from it opens the other side under exact interfaces, so the check adds nothing there. With the checks as a group of their own, a check is held to the level of the cheapest split. `p ; q` halts at 128 ticks and its variant with identity spans at 342.

What this forces to be redone: nothing built. Levels are numbers in tables and are read with `metered`; the freeze list of section 6 is unchanged. The L36 row's sentence about two request rules giving one bound each is superseded: one rule, measured against the flat bound only (section 9.7 of the simulation note). The share bound (the product of live alternatives along the nesting) is no longer claimed by any rule of the design; whether the split balance has it was not measured.

The balance takes one weight per strategy and uses equal weights. Other weights are roadmap item L32 and need no new machine.

**Revision, 2026-11-14 (second): the interface check as built.** It is in `Rungs/Symmetric/Machine.lean` (`runs`, `readEdge`, the strategy `check`), tested in `Tests/SymmetricRuns.lean`, and covered by the invariant and the mirror criterion (`Goals.lean`). Five points differ from, or add to, the fourth revision and the prototype.

1. *The reading has no bound to run under, and needs no new kernel operation.* A node is an identifier and the kernel does not tell an engine how deep the program is, so a traversal of the text cannot be written as one total computation. A reading is given a depth and says when the depth was not enough. The state holds the depth readings are tried at, starting at 1, and doubles it whenever a reading fails. A depth larger than needed costs nothing, and a failed reading is at a depth below the depth of the program, so the depth held is always less than twice that. A check whose reading failed tries again in its next unit of work. The alternative was a trusted operation giving a bound on the nesting of the program. It would have made the reading immediate, and it would have added to the trusted interface for one engine.
2. *What is read is kept* per node and end, so a side is read once however many goals stand on its node, and once the depth of the program has been reached every side is read when the groups of its goal are made, as in the prototype. Until then a chain goal carries checks that are still reading.
3. *The reading is charged.* The prototype read an edge at no charge. Here it costs what the kernel charges for the views, the leaves and the compositions it does, and that goes to the level of the group of checks.
4. *A group of checks none of which can do anything more is removed from its table.* A check is dead when it is not offered or when one of its goals has an answer. The prototype keeps such a group, with its level frozen; the level of the goal is the lowest level of its groups, so there the goal's level stops rising, and whoever reads the goal is no longer charged for it. The fourth revision did not choose between the two. Measured on the prototype with the option `drop_dead`: no change on the middle-restricted family, on fair OR or on `p ; q`; a fifth more ticks on counting down, with the same requests; on the ladder 1196396 ticks against 632782 at `n = 32`, 593720 against 331597 at `n = 24` and 182590 against 158004 at `n = 16`, so between the second and the third power either way. Removal is kept: with the group frozen, a goal whose checks are dead is free to everything that reads it, which is what the ladder gains from, and it is the balance switched off for those goals, not a rule.
5. *A side with no product at all completes its chain.* If the reading finds that no product of the side exists (adjacent spans at its edge do not compose), the check has no goal to open and is complete at once. The prototype made no check there. A meet is not read: a check on a side that is a meet, or whose edge is one, is not offered.

Measured on the engine at the domain of sorts with only the node operations charged: `p ; q` halts at request 10, and its variant with identity spans at request 4 (the prototype: 6 and 6). Counting down answers at request `2k + 10` and halts after `7k + 12`; without the check the engine had `2k + 7` and `5k + 9`, and the prototype with the check has `2k + 7` and `6k + 8`. The three requests on the first answer are the learning of the depth. The slope of the halt differs from the prototype's because the levels are in different ticks. Fair OR with one and with three endless members answers no later than counting down alone. The ladder and the middle-restricted family have not been run on the engine itself; the prototype's numbers for them are for readings at no charge.

What this forces to be redone: nothing. O7 is unchanged: that the check covers the unfolding race is still not proved.

### What a step is

A step is one request to the root and emits the answers the root table gained, usually none. Two writings of one input give the same sequence of steps, so the trace properties hold with equality and not only up to `TraceEquiv`.

## 4. The candidates compared

Against M6's exit criteria. "Exact" means the property holds by construction; "no" means it fails on a stated input.

| | Mirror race (R005, kept) | Two-ended alternation (old engine, R6) | Full nets (H3) | **Normal form with balanced intervals** |
|---|---|---|---|---|
| Mirror image, step for step, equal ticks | Exact, by racing two copies | No: the first step takes the front (`src/work/pipe.rs`, `flip: false`) | Only with an order-insensitive proof of every traversal (F1) | Exact (points 1, 2) |
| `SeqAssoc` | No: the tables split at the written node | Exact for `;` (the pipe is flat) | Exact | Exact |
| `AndComm`, `AndAssoc` | No | No: `&` is separate machinery (`and_group.rs`) | Exact | Exact |
| One machine, no race | No | Yes | Yes | Yes |
| Cost where the cheap order is not from an end | Exponential, *measured* (5.1) | Exponential, *measured* (5.2) | Depends on the policy, which H3 leaves open | Polynomial on the measured families (5.3) |
| Table key | Goal on the syntax tree | Call key with boundaries | Net up to isomorphism: canonical labelling of a hypergraph with terms | Interned tree node and two canonical spans |
| New kernel work | None | None | Canonical form of nets; sub-goals with more than two interfaces | Canonical spans only (already owed by M5) |

**Keeping a hedge.** Rejected. It cannot give L29: there are exponentially many bracketings, and a hedge against a machine that reads the written bracketing does not have `SeqAssoc`. It is also not needed for symmetry once F1 is used.

**Two-ended alternation.** The flat pipe with a boundary at each end is the right data structure and is point 1 of the decision for `;`. As an evaluation order it is rejected. It is driving from the ends, which `r005/design-notes.md` finding 1 and the rung 6 thread's `digits d` family (over 100 times R004) show loses to joining tables on some inputs, and section 5.2 shows it is exponential when the restriction is in the middle. This is the recorded outcome for row R6 of the old engine's optimization inventory (ledger L25): the flattening is carried into the verified engine, the alternation is superseded by the balance.

**Full nets.** Rejected for M6, for three reasons. No end-state item needs more than associativity and commutativity, which the tree normal form gives. A sub-net of a net can have more than two interfaces, so tables would stop being binary relations. And the table key would be a net up to isomorphism, which makes canonical labelling of hypergraphs a kernel operation that must be costed on the base machine; the tree normal form is canonical by sorting. What nets would add (full reducers S15, many-sided meets S39, residual calls in answers for S22) is uncommitted, and the generic answer type of L28 keeps the last of these open.

## 5. Measurements

### 5.1 The top rung on a chain restricted in the middle

Family `mid k`: `bit ; … ; bit ; ($x -> t_k) ; unbit ; … ; unbit`, `k` factors each side, one answer. Ticks until the machine halts, on master. Checked by the build at the tag `epoch-1` (`lean/Tests/MiddleRuns.lean`).

| k | R004 right-nested | left-nested | balanced | middle-out | R005 right-nested | left-nested | balanced | middle-out |
|---|---|---|---|---|---|---|---|---|
| 0 | 129 | 129 | 129 | 129 | 969 | 969 | 969 | 969 |
| 1 | 4497 | 4756 | 4497 | 4497 | 33540 | 34064 | 33540 | 33540 |
| 2 | 13708 | 15755 | 14775 | 13950 | 126308 | 133287 | 131045 | 126619 |
| 3 | 43112 | 50907 | 46355 | 43556 | 276012 | 562939 | 280358 | 276661 |
| 4 | 138816 | 156667 | 156610 | 139806 | 397884 | 1123954 | 1071841 | 398622 |
| 5 | 323318 | 392393 | 353034 | 325942 | | | | |

R004 from the middle outwards continues 1247506, 3508066 for k = 6, 7. Growth is about three times per step of `k` in every bracketing. The cost is in the unfolding race, which does not read the bracketing, and the mirror race does not help because neither end is the cheap one. R005's cost depends on the bracketing by up to 3 times here.

### 5.2 The old engine on the same shapes

Engine steps and compositions attempted, counted by `perf_counters`, through the REPL.

| k | `bit^k ; @t_k` | mirror image | `bit^k ; $x -> t_k ; unbit^k` |
|---|---|---|---|
| 2 | 3 / 2 | 3 / 2 | 25 / 16 |
| 4 | 3 / 4 | 3 / 4 | 61 / 108 |
| 6 | 3 / 6 | 3 / 6 | 205 / 572 |
| 8 | 3 / 8 | 3 / 8 | 781 / 2812 |
| 10 | 3 / 10 | 3 / 10 | 3085 / 13308 |

Restricted at an end the old engine is linear from both ends. Restricted in the middle it doubles with `k`.

### 5.3 A prototype of the balance

`scripts/symmetric_engine_prototype.py`: call-free flat chains, empty theory, join strategies only (no push), cost counted as the sizes of the two spans of each composition attempted. Fixed bracketings are given the benefit of joining each pair once and of no unfolding race, so they are cheaper than R004 would be. Selected rows; the script prints all of them.

| Family | k | right-nested | left-nested | balanced | balanced intervals: first answer | halt |
|---|---|---|---|---|---|---|
| A. `bit^k ; @t_k` | 12 | 1032 | 524272 | 5460 | 1492 | 28964 |
| B. mirror image of A | 12 | 524272 | 1032 | 10640 | 1718 | 22908 |
| C. `bit^k ; $x -> t_k ; unbit^k` | 6 | 3640 | 3724 | 2960 | 982 | 27288 |
| C | 12 | 426112 | 426424 | 239152 | 7344 | 891712 |
| E. `bit^k`, 2^k answers owed | 10 | 45040 | 45040 | 25760 | 584 | 256038 |
| F. `@t_k ; unbit^k ; bit^k ; @t_k` | 8 | 35276 | 35276 | 3324 | 3210 | 19686 |

Reading:
- On A and B the first answer arrives within 1.7 times the best fixed bracketing, and the run halts within 28 times, where the worst fixed bracketing is 500 times worse and doubling.
- On C every fixed bracketing doubles per step. The balance's first answer grows polynomially. Its halting cost also grows polynomially (the ratio between successive `k` falls from 2.0 to 1.64), at about the fifth power of `k`, which is too high and is open point O2.
- On E, where the output is exponential, the balance costs about `k` times the best fixed bracketing.

What the prototype does not cover: recursion, constraints, push strategies, `&`. So it says nothing about F3 in general.

### 5.4 Nested choices with a member that never finishes

`q = inf | ((s $x) -> $x ; q) | (z -> z)` asked at `s^k z`, with `inf` distinct at each level and never finishing (the roadmap thread's example for the fairness bound L36). `scripts/symmetric_engine_fair_or.py` is a model of the two request rules on this shape only, one tick per unit of work; it is not the prototype of 5.3 and has no terms in it. Ticks until the answer:

| k | share rule alone | share rule alternating with a flat round |
|---|---|---|
| 4 | 46 | 17 |
| 8 | 766 | 41 |
| 12 | 12286 | 73 |
| 16 | 196606 | 113 |
| 20 | 3145726 | 161 |

The share rule alone is `3 * 2^k - 2`. With the flat round it is quadratic in `k`. This is why section 3 alternates the two.

## 6. What milestones 3 and 5 must freeze

### Milestone 3, part A

| Item | Requirement from this design |
|---|---|
| **L27 base machine** | (a) Interning of terms, spans and normal-form nodes is an operation of the base machine whose charge depends on the size of the thing interned and on nothing else: not on which identifier it gets, not on what is already stored. Comparing two identifiers is one tick. (b) Indexed read and append on a table are one tick each (strategies keep cursors into answer lists). (c) *Withdrawn 2026-11-13, see the revision below the table.* (d) The one structural comparison that orients the input costs the same with its two arguments exchanged. Reading both arguments entirely gives that. |
| **`Kernel`** | One new operation: run a computation and return what it spent (`metered : M α → M (α × Nat)`). The balance cannot be written without reading what a strategy cost. `race` and `within` are not used by the M6 engine; they stay only as long as R005 is the yardstick. `canon` is replaced by the normalisation above, and `eqRel` by identifier equality. |
| **L28 answer type** | The answer type has a converse with `den (swap a) = (den a)ᵒ`, and composition and meet stated on denotations. A table read through its converse depends on it. Nothing else is asked; spans are the instance M6 uses. |
| **L30 derivation kernel** | Answers are indexed by a goal of the normal form (node identifier and boundaries), not by a `RelOf`. The rules are: a span leaf; joining two adjacent intervals of a chain, which is where associativity is built in; meeting members of a multiset; membership in a union; unfolding a call; converse. That the normal form of an expression denotes what the expression denotes is one proved theorem under the kernel, and the trusted soundness statement stays about the source expression. |
| **L31 cost monad** | With `metered`, nothing in the lineage abandons a computation, so "what an abandoned computation holds live" has no instance above R005. Space of the M6 engine is the tables plus one cursor pair per strategy. The symmetric race of H23 and a resumable budget are not needed and should not be built. |
| **L29 statements** | `SeqAssoc`, `AndComm`, `AndAssoc` as equality of traces, like `OrComm`. For R005 they are to be recorded as refuted or proved; section 5.1 shows the cost differs with the bracketing; the traces of the four bracketings of `mid 2` agree, and no refuting input was looked for. |
| **L36 fairness statement** | Decided by Anthony on 2026-11-13 and recorded in the roadmap's L36 row: an answer an alternative would emit within `n` ticks as the query alone is emitted within a constant times the smaller of `n` times the product of live alternatives along the nesting, and `n` times the number of live goals opened so far. The two request rules of section 3 are meant to give one bound each, at a constant of two (section 5.4); neither is proved. A bound polynomial in derivation size alone is false for every machine (`bit^k` has `2^k` incomparable answers of derivation size `O(k)`). |
| **L24 Rust subset** | The engine is single-threaded and needs: vectors indexed by integers for nodes, tables and strategies; one map from structure to identifier for interning; loops over indices; plain recursion. No shared ownership, no interior mutability, no stored closures, no trait objects. Confirmed by the Aeneas spike (Aeneas `5a392f4b`, 2026-11-13): all of that translates to ordinary Lean definitions, with these limits. `std` maps come out as axioms, so the interning map is hand-written. It must be a trie over vectors and not an open-addressing table: a probe sequence costs more the fuller the table is, which breaks the size-only charge L27 needs, while a trie lookup costs the length of the key. Sorting, iterator adaptors, `Vec::pop` and `Vec::truncate` are axioms too, so sets are sorted by a hand-written loop and stacks are indexed. A loop may contain one early `return`, not several. |

**Revision, 2026-11-13.** The first version of this table asked that every derived charge be invariant under swapping spans. That is not needed and is withdrawn. Under point 2 of the decision a query and its mirror image are the same run after the first state is built, so no operation is ever compared with its swapped form. Building the first state normalises the same two inputs in both cases, and the only step that sees them in a different order is the comparison in (d). The base machine thread had offered to meet the withdrawn requirement by charging every operation its worst case for its size; that padding should not be built. Nothing else in this note changes. The base machine's store is hash-consed with allocation at one tick, which gives (a) directly; normal-form nodes are encoded as nodes of that store.

### Milestone 5

| Item | Requirement from this design |
|---|---|
| **Canonical spans** | The canonical representative commutes with swapping: `canon (sᵒ) = (canon s)ᵒ`. Without it a goal and its converse do not share a table. |
| **Interfaces** | `leftBound` and `rightBound` return canonical representatives, and the left interface of `s` is the right interface of `sᵒ`. A boundary carries the part of the store that mentions its variables. |
| **Nothing for nets** | No canonical form of anything larger than a span is needed. Table keys are interned tree nodes. |
| **Confluence (L11)** | Not required by the first state, because spans are not fused at normalisation. It is what makes two strategies that reach the same answer by different bracketings store one answer instead of two equivalent ones, so the engine's cost depends on it. M5 should state and prove: under a well-formed theory, composition followed by simplification is associative up to `Span.Equiv`, and meet is commutative and associative up to `Span.Equiv`. |
| **Constraints** | From the example programs and notebooks (`equality_constraints.txt`, `range_sets.txt`, SK, program_synth, Lambda, SimpleLam, SubstConstr, ProofSynth, theory_demos): a constraint sits on a span and restricts a variable that may be at one end of a long chain while the test that fails is at the other (`$x {(no_c $x)} -> (f $x (c z)) ; app ; … ; @(c z)`), or inside one branch of a `&` (`(app $x $y) {(norm $x)} -> $y ; lamRW ; …`). Those queries are restricted at both ends, which is the case the balance is for. The design asks nothing of the rule language beyond the two rows above. Defined predicates as store atoms (L17) are compatible with it and not needed by it. |

## 7. Open points and risks

**O1. The simulation theorem (F3).** *Attacked twice on 2026-11-13. False for the engine as first designed. False for the engine of the third revision too: the ladder family is polynomial for R005 and exponential for that engine under every request rule it had (simulation note 9.2). Open for the engine of the fourth revision, which is polynomial on every family measured. For it O1 reduces to: the written line is charged additively (G1, argued), what a group really spends is polynomial in its level (G2, open: in the worst case the factor is the number of splits per level of nesting, and no family was found that realises it), and the interface check finishes what R005's unfolding race finishes (Lemma U, open). The text below is the statement as it first stood.* With shared tables, a strategy can be delayed by answers that another strategy of a sub-goal produced earlier than R005 would have. The direct proof bounds that delay by a polynomial per level of the derivation, which compounds with depth and is not a polynomial. Whether a fixed polynomial holds is not known. Three facts make it plausible: a complete table stops its other strategies; R005's cost is dominated by its unfolding race, which reads no bracketing, so "the cheapest writing" varies by a constant on the families measured; and the prototype is within a polynomial of the best fixed bracketing on every family tried. If it fails, the hedge is not a fallback (section 4), and the conflict between `SeqAssoc` and `Simulates` goes to Anthony under roadmap rule 3 with the counterexample. M6 should attack O1 first, on paper and on a prototype with recursion, before any Lean.

**O2. Cost of exhaustion.** *Measured 2026-11-13: on family C without pushes at `k = 10` the share rule halts at 348149 ticks (exponent about 4.8) and the flat round at 56043 (about 3.3). With pushes the flat round is exponential and the share rule is not (simulation note 3.3).* The prototype halts at about the fifth power of the chain length on family C. Completion is reached only through a strategy whose sub-tables are complete, and every interval's share is divided again at each level. A direct share for every opened goal is the first thing to try.

**O3. Meets.** The strategies for `&` are pushes only. A join of two groups of members for every grouping is exponential in the number of members. Whether pushes alone simulate R005's join of two written sides is not checked.

**O4. Push strategies open one goal per answer.** The balance among a goal's strategies is then over a growing set. R001 has the same growth; its effect on the balance is not measured.

**O5. The orientation in point 2 is arbitrary.** It makes mirror cost exact and adds nothing to cost robustness, which comes only from the balance. If the balance were dropped, the engine would still pass the mirror criterion and would be bad on half its inputs. The admission requirement that catches this is `Simulates` against R005, not `DirectionFree`.

**O6. The request rule.** *Settled by measurement on 2026-11-13 (fourth revision), not by proof.* The split balance is polynomial on the middle-restricted family with pushes, on fair OR with several members that never finish, on counting down and on the ladder. The two rules that had been left untried were tried and fail (simulation note 9.3). What stays open about the rule: G2 above; the fairness bound in ticks on a table that grows exponentially with no boundary (the strings family: `2k + 4` requests, but ticks grow six times per two steps, as for whole rounds; no rule measured has the tick form on both that family and fair OR with three endless members); its cost on the middle-restricted family (the sixth power, where the share rule had the fourth); and what the bookkeeping of levels costs, which the prototype does not charge. *Decided by Anthony on 2026-11-13: the fairness bound is stated in requests, not ticks, so the strings family is no longer an open point about the rule.*

**O7. The interface check is not proved to cover the unfolding race** (Lemma U of the simulation note). Its recursion guard unfolds each call once. Since the fourth revision it is offered only for a side that contains a call; that this loses nothing is argued, not proved. On 200 random small programs the engine halts wherever R005 halts within its budget (138 of them) and on 35 more; none of those programs needs the check, so this says more about `TerminatesWhere` than about the check (`scripts/symmetric_engine_halting.py`).

**Revision, 2026-11-13: what the restated kernel provides.** The `Kernel`, L30 and L31 rows are delivered in `Trusted/Kernel.lean`, `Trusted/CostMonad.lean`, `Kernel/NormalForm.lean` and `Kernel/Derivation.lean`. Five points differ from, or add to, what the table says.

1. Two classes. `Kernel S M` keeps the operations on spans, with `metered`, and without `canon`, `eqRel`, `size` and `idSpan`. `DerivationKernel S N A M` extends it with nodes and answers. An engine is written against the second.
2. `size` and `idSpan` leave the kernel (L44). On a hash-consed store the size of a term as a tree is not a word the machine holds, and storing it at allocation would need unbounded arithmetic per node. The balance reads costs with `metered`. An absent boundary is the identity and a chain has at least two members, so no identity span is needed.
3. Nodes of the normal form are expressions in a fixed shape (`RelOf.norm`): chains flattened, meets sorted as multisets, unions sorted as sets, converse only on calls. Adjacent spans of a chain are not fused. The converse of a node is `normConv`, and a call node carries a flag for the converse of its body. `sem_norm` is the theorem that the normal form denotes what the expression denotes.
4. The rules are `leaf`, `simp`, `join`, `meetA`, `inj`, `unfold`, `swapA`. `join` takes an answer of a stretch with its right boundary absent and an answer of the next stretch whose left boundary is absent or the right interface of the first (a push), or the mirror image of that. `meetA` takes the second answer between the same boundaries or between the interfaces of the first. `simp` is a rule because simplification by the theory is how a dead answer is recognised; it does not change what the answer denotes among the pairs the theory allows.
5. Space is `peak` and `held` in `Cost`. Only `within` releases cells (the abandoned side of a race), so an engine that never abandons has `peak = held` growing with its tables, as the L31 row expects. There is no depth component: stacks are explicit and live in the store (L43), so depth is space.

Provided since (roadmap L47, `Kernel/NormalFormStable.lean`): the normal form is stable (`norm` of a node is the node, and the converse of the converse of a node is the node), which is what lets a goal and its converse share one table. Not provided, and needed by this design before M6: charges for the operations on nodes that are derived on the store instead of postulated (roadmap L45).

## 8. What this replaces

- Rung 6 as a rung (a hedge of R005 and goal-directed tables). Its push-without-join strategy, its balancing lemmas (`Rungs/Hedge` at the tag `epoch-1`) and its two families are reused.
- Cost-fair scheduling as a separate rung (L16): it is the balance.
- The weighted hedge of whole engines (L32): it becomes the weights of the balance.
- Billboard H23 and H24 (a cheaper symmetric race; direction per goal): the first is moot, the second is the design.
- Billboard S14 (choosing where to split a chain): built in.
