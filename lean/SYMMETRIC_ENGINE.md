# The symmetric engine: design note

Written 2026-11-13 against master `ffaac8a`, for roadmap milestone M3 part A (the engine design note) and milestone M6 (ledger L01, L20, L29). It confirms the early verdict in `symmetric-engine/lineage-verdict.md` of the project files and reverses nothing in it.

Everything marked *measured* was run and is reproducible from this repository. Everything marked *argued* is an argument on paper. Nothing here is proved in Lean.

## 1. Decision

M6 builds one new machine, with these five properties.

1. **It evaluates a normal form, not the syntax tree.** Before the first step, program and query are rewritten so that `;` is a flat list, `&` is a multiset, `|` is a set, and converse occurs only on calls. Two inputs that differ in the bracketing of `;`, in the order or bracketing of `&` or `|`, give the same first state.
2. **It picks one orientation of the whole input.** The normal form of the input and the normal form of its mirror image are both built and the smaller, in a fixed structural order, is run; answers are swapped back if the mirror image was chosen. A query and its mirror image are then the same run.
3. **A goal and its converse share one table.**
4. **A chain goal is a table on an interval of a flat chain.** Every split of the interval is a strategy of that table, and so is pushing the answers of a complete side into the other side, from either end. The strategies of a table are balanced by the ticks they have spent. No strategy is chosen by syntax.
5. **Nothing runs beside the tables.** There is no unfolding race, no mirror race and no hedge of whole machines.

Points 1 to 3 give the exact properties (mirror image step for step at equal ticks, `SeqAssoc`, `AndComm`, `AndAssoc`). Points 4 and 5 give the cost. The two are separate, and section 3 explains why that separation is the main finding.

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

The balance takes one weight per strategy and uses equal weights. Other weights are roadmap item L32 and need no new machine.

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

Family `mid k`: `bit ; … ; bit ; ($x -> t_k) ; unbit ; … ; unbit`, `k` factors each side, one answer. Ticks until the machine halts, on master. Build-checked in `lean/Tests/MiddleRuns.lean`.

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

**O1. The simulation theorem (F3).** *Open.* With shared tables, a strategy can be delayed by answers that another strategy of a sub-goal produced earlier than R005 would have. The direct proof bounds that delay by a polynomial per level of the derivation, which compounds with depth and is not a polynomial. Whether a fixed polynomial holds is not known. Three facts make it plausible: a complete table stops its other strategies; R005's cost is dominated by its unfolding race, which reads no bracketing, so "the cheapest writing" varies by a constant on the families measured; and the prototype is within a polynomial of the best fixed bracketing on every family tried. If it fails, the hedge is not a fallback (section 4), and the conflict between `SeqAssoc` and `Simulates` goes to Anthony under roadmap rule 3 with the counterexample. M6 should attack O1 first, on paper and on a prototype with recursion, before any Lean.

**O2. Cost of exhaustion.** The prototype halts at about the fifth power of the chain length on family C. Completion is reached only through a strategy whose sub-tables are complete, and every interval's share is divided again at each level. A direct share for every opened goal is the first thing to try.

**O3. Meets.** The strategies for `&` are pushes only. A join of two groups of members for every grouping is exponential in the number of members. Whether pushes alone simulate R005's join of two written sides is not checked.

**O4. Push strategies open one goal per answer.** The balance among a goal's strategies is then over a growing set. R001 has the same growth; its effect on the balance is not measured.

**O5. The orientation in point 2 is arbitrary.** It makes mirror cost exact and adds nothing to cost robustness, which comes only from the balance. If the balance were dropped, the engine would still pass the mirror criterion and would be bad on half its inputs. The admission requirement that catches this is `Simulates` against R005, not `DirectionFree`.

## 8. What this replaces

- Rung 6 as a rung (a hedge of R005 and goal-directed tables). Its push-without-join strategy, its balancing lemmas in `Rungs/Hedge` and its two families are reused.
- Cost-fair scheduling as a separate rung (L16): it is the balance.
- The weighted hedge of whole engines (L32): it becomes the weights of the balance.
- Billboard H23 and H24 (a cheaper symmetric race; direction per goal): the first is moot, the second is the design.
- Billboard S14 (choosing where to split a chain): built in.
