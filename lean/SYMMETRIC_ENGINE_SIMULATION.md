# The simulation theorem for the symmetric engine: what was found

2026-11-13. This is the attack on open point O1 of `SYMMETRIC_ENGINE.md` (roadmap M6, brief item 8): is the engine within a polynomial of R005 on the cheapest writing of every query? Everything here is on paper and in a prototype. No Lean engine exists.

The prototype is `scripts/symmetric_engine_tables.py`. It is the engine of the design note with recursion through tables, pushes that open one goal per answer (O4), R001's exact completion check, and the request rules as options. `python3 scripts/symmetric_engine_tables.py 2` prints table 2, and so on. The numbers for R005 are evaluated in Lean by `Tests/SimulationRuns.lean`, at commit `326b608` (the file is parked with R005, `PARKED.md`). Ticks of the prototype and ticks of R005 are not the same unit; only growth is compared, except where one side does not halt.

**Revision, 2026-11-13 (second attack): section 9.** It decides the ladder, and with it reverses points 2 and 3 of the verdict below for the engine of sections 4 and 5: Lemma G is false for that engine under every request rule of sections 3 to 6. It gives a request rule that is polynomial on every family measured, the ladder included, and narrows the interface check. Sections 1 to 8 are left as they were written.

## 1. Verdict

1. **The engine as designed does not simulate R005.** There are three separate failures (section 3). On the first the engine never halts where R005 halts in its second round, so it also fails `TerminatesWhere`.
2. **None of the failures comes from bracketing independence.** Each is repaired, on the families measured, by a change that reads no bracketing (section 4). So there is no conflict between `SeqAssoc` and `Simulates` to put to Anthony today.
3. **O1 is not proved for the revised engine, and not refuted.** It is reduced to three stated lemmas (section 5), two of them open. One family (the ladder) is where the open lemma would fail if it fails; R005 cannot be evaluated far enough on it to decide.
4. **The claim "alternating costs at most twice the better of the two rules" is false**, by requests and by ticks, because the two rules write the same tables (section 3.4). No request rule measured is good on every family (section 6). This is the main open design question.

## 2. What R005 pays

Read from `Rungs/R001/Engine.lean` and the R005 files, for a query as written (a writing `w`).

- R005 on `w` runs synchronous rounds. In round `r` it recomputes every incomplete table from the tables as they stood. The goals are the ones reached from the query by the written splits of `;`, with a push from a side once that side is complete, one goal per answer.
- Each round it also runs the unfolding race at depth `r`. The race gives answers only if the unfolding to depth `r` is final (no call is left), and then the goal is complete.
- It does all this twice, for the query and its mirror image, and pays for both until one halts.

Three consequences.

**Fact A (pushes do not cover earlier).** In R005 a push from a complete side gives no answer in an earlier round than the join at the same split. Pushes matter for completion, not for coverage. *Argued from the definitions, not formalised.*

**Fact B (rounds repeat).** A round costs at least the number of pairs already joined in every incomplete table. So R005's payment by round `r` is at least the sum over rounds of the work of a machine that joins each pair once.

**Fact C (the unfolding race is a second source of completion).** A goal whose unfolding is final at depth `r` is complete in round `r` whatever its tables look like. The designed engine has nothing that corresponds to this.

## 3. The failures of the engine as designed

"share" is the share rule of the design note, "flat" the flat round with one unit of work for each open goal, "in turn" the alternation the note adopted.

### 3.1 No strategy sees a clash across two calls

```
gen = (z -> z) | gen ; ($x -> (s $x))
p   = gen ; ($x -> (t $x))
q   = ((u $x) -> $x) ; gen
query: p ; q
```

`p ; q` is empty because `t` meets `u`. Both `p` and `q` have infinitely many answers, so no side is ever complete, no push ever starts, and the join composes pairs for ever.

| | halts | ticks | goals |
|---|---|---|---|
| R005 | round 2 | 3571 | |
| engine: share, flat, in turn | never (300,000 ticks spent) | | 12 |
| R005, with an identity span at the end of `p` and the start of `q` | round 3 | 27340 | |
| engine on that variant | never | | 19 |

R005 halts by Fact C. The engine reads every bracketing and it does not help: the chain has two members, both calls. The cause is that calls are not inlined and nothing else looks through them.

### 3.2 The share rule is exponential to halt on counting down

`q = ((s $x) -> $x) ; q | (z -> z)`, query `@(s^k z) ; q` (table 2).

| k | 2 | 4 | 6 | 8 | 12 | 16 |
|---|---|---|---|---|---|---|
| R005 halts | 135988 | 537596 | 821008 | 2329233 | | |
| share | 901 | 16137 | 359051 | over 3,000,000 | | |
| flat | 639 | 2321 | 5649 | 11175 | 31029 | 66299 |
| in turn | 869 | 3243 | 7837 | 15331 | 42969 | 91421 |

R005 grows about as `k^2`. The share rule multiplies by about 20 for each two steps. The table of `q` with no boundary has an answer for every number, the share rule keeps feeding it, and the boundaried goals that would complete get an exponentially small share.

### 3.3 The flat round is exponential when pushes open goals

`bit^k ; ($x -> t_k) ; unbit^k` with pushes (table 5b), ticks to halt:

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| share | 1089 | 4263 | 9883 | 22144 | 41488 | 60099 | 120061 |
| flat | 2903 | 16227 | 65069 | 207381 | 347035 | 906345 | 2103949 |
| in turn | 3310 | 20671 | 89925 | 306490 | 708039 | 1804911 | over 3,000,000 |
| goals opened, flat | 98 | 355 | 1040 | 2578 | 4356 | 9636 | 19920 |

The goals double with `k` and a flat round serves all of them. R005 is exponential on this family too (design note 5.1), so this alone is not a counterexample to O1. It is the family on which the engine is meant to be admitted over R005, and there only the share rule is polynomial.

### 3.4 Alternating does not cost "at most twice the better"

By requests it fails on 3.3: a flat round costs as many ticks as there are goals, so half the requests is nearly all the ticks. Balancing the two rules by ticks spent repairs that family (185565 at `k = 8`) and counting down with one unit per goal (255903 at `k = 16`, against 66299 for flat alone, so four times and growing). With whole rounds (section 4.2) it does not: counting down halts at 10398 for `k = 8` under whole rounds alone and at 979757 when whole rounds are balanced by ticks with the share rule. The reason is that the rules share tables. What the share rule puts into the unbounded table of `q`, the round must then read.

### 3.5 One unit per goal dilutes

On `q = inf | ((b0 $x) -> $x ; q) | ((b1 $x) -> $x ; q) | (nil -> nil)` asked at a string of `k` bits (table 4d), requests until the answer are 13, 25, 50, 82, 157 for `k = 2 … 10` with one unit per goal and 12, 24, 42, 62, 82 with one unit per strategy.

## 4. Changes measured

### 4.1 The interface check (repairs 3.1)

A new strategy of a chain goal, for each split and each side. The first (or last) span of every answer of a side is one of finitely many spans known from the program text: follow the edge of the node inwards, composing adjacent spans, through unions and through a call once. Open the other side under the interface of each of those spans, as ordinary boundaried goals. If all of them complete with no answer, the chain goal is complete and empty. The side read from the text need not be complete or even opened. It reads no bracketing: it is a strategy of every split.

| | halts at | goals |
|---|---|---|
| `p ; q`, in turn with the check | 148 | 27 |
| the identity variant | 252 | 45 |
| `p ; q`, whole rounds with the check | 99 (4 requests) | 22 |
| the identity variant, whole rounds | 88 (4 requests) | 41 |

Cost elsewhere: counting down is unchanged within 1% (table 2, last column); the ladder (section 5) pays up to twice; `bit^k ; … ; unbit^k` with pushes under whole rounds pays up to six times and more goals (table 7).

The alternative "open each call of a chain in place, as one more strategy" also halts both inputs (2512 and 14886 ticks) and is rejected: it opens 14299, 99810 and 140844 goals on the ladder for `n = 2, 3, 4` (table 3b).

A first version that looked at one span only failed on the identity variant. That is why the edge is composed inwards.

### 4.2 Whole rounds (repairs 3.2 and 3.5, and gives the flat fairness bound in steps)

In a flat round, each strategy of each open goal does everything its inputs allow, instead of one unit. A whole round is then one round of R005's machine on every split at once, without repeating any pair.

Requests until the answer on the three fair OR families (tables 6, 4c, 4e):

| k | 2 | 4 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|
| whole rounds, all three families | 11 | 15 | 19 | 23 | 27 | 31 |
| the alternative alone (requests) | 5 to 8 | 6 to 8 | 6 to 10 | 6 to 10 | 6 to 10 | 6 |

That is `2k + 7` exactly, whatever the number of members that never finish. With one unit per goal or per strategy, the family with three such members (table 4b) takes 12, 39, 304 and 11, 30, 222 requests for `k = 2, 4, 6` and is past 3,000,000 ticks at `k = 8`.

Whole rounds halt counting down at 612, 2156, 10398, 62618 for `k = 2, 4, 8, 16`.

What whole rounds cost: ticks. On the strings family the table of `q` with no boundary has `2^i` answers of length `i`, and a whole round reads all of them: 630, 4778, 31671, 189275, 949503 ticks to the answer for `k = 2 … 10`, against 572, 3931, 16933, 47113, 99943 with one unit per strategy. On 3.3 whole rounds are exponential, like the unit rounds.

### 4.3 Open-point answers

- **O2 (exhaustion at about the fifth power).** Measured on `bit^k ; ($x -> t_k) ; unbit^k` without pushes (table 5), `k = 10`: share 348149 (exponent about 4.8), flat 56043 (about 3.3), in turn 54751. The flat round removes the fifth power. With pushes see 3.3.
- **E1 (one cursor per producing strategy).** Tried first, as the brief asks. No measurable effect on the ladder or on counting down. It does not address any failure above. Kept as an option of the prototype (`e1=True`).
- **O4 (pushes open a goal per answer).** This is 3.3: the fan-out defeats every rule that serves each goal once per request.

## 5. What O1 reduces to for the revised engine

The revised engine: the design note's engine with the interface check and whole rounds. Fix a query and a writing `w` of it.

**Lemma 1 (rounds).** After `a·r + b` whole rounds, every goal that R005 on `w` has opened by its round `r` is open in the engine, and holds every answer R005's tables have given it by round `r`. Here `b` is the nesting depth of the program text and `a` a constant. *Argued:* the engine has the join and both pushes at the written split among its strategies, and a whole round lets each of them catch up. Measured as `2k + 7` on the fair families. Not formalised.

**Lemma 2 (no repeated work).** On the goals that R005 on `w` opens, the engine's ticks over those rounds are at most R005's. *Argued* from Fact B.

**Lemma U (the interface check finishes what the unfolding race finishes).** *Open.* If R005's unfolding of a goal is final at depth `r`, the engine completes that goal within a polynomial of R005's payment. The check sees a clash between runs of spans at the two edges of a split, through unions and one unfolding of each call. Believed because a final unfolding means every branch dies at a clash of adjacent spans, and every such adjacency is a split of some opened goal. Not proved: the recursion guard unfolds a call once, and beyond that the check relies on boundaries pushed through tables. Both inputs of 3.1 pass.

**Lemma G (the other splits are not too many).** *Open, and this is the content of O1.* The goals the engine opens that R005 on `w` does not (other splits, their pushes, the interface checks) cost within a polynomial of what R005 pays on `w`. The hazard is concrete: a split that `w` does not have can leave a sub-chain with no boundary, and its table can have exponentially many answers within `r` rounds. A complete table stops its other strategies, which is why it holds on the families measured.

**The test family for Lemma G: the ladder.** `r_0 = (nil -> nil)`, `r_i = G ; (F ; r_(i-1))`, query `@(st nil) ; r_n` (table 3 and 7). Every rule's halting cost on the engine grows by a factor between 1.5 and 2.1 for each two steps (whole rounds: 2796, 6698, 25196, 61456, 140675, 299086 for `n = 2 … 12`, goals 117 to 2942). R005 halts at 12788, 265798, 1304050, 1400644, 2975637 for `n = 0 … 4` and does not evaluate in Lean in reasonable time beyond that, because a race is evaluated to the end on both sides. So the ladder is not established as a counterexample and not cleared. Deciding it needs R005's cost in closed form on this family, or an interpreter for R005 outside Lean.

**A lemma the direct proof would need, and why it compounds.** In a shared table a reader meets answers that a strategy other than the written one produced first ("junk"). Bounding the delay per level of the derivation gives a polynomial per level, which compounds with depth. Whole rounds remove the delay in rounds (Lemma 1) and move the question to ticks, which is Lemma G.

**A bound that does hold, and is too weak.** A race over the uniform split policies (always leftmost, always rightmost, and so on) is within a factor exponential only in the number of members of the chains of the text, not in the size of the answers. It is recorded on the billboard, not adopted.

## 6. Which rule is good where

Ticks, growth with `k`. "poly" and "exp" are read from the measured ratios, not proved.

| family | share | flat, unit per goal | flat, unit per strategy | whole rounds | share and unit flat by ticks | R005 |
|---|---|---|---|---|---|---|
| counting down, halt (2) | exp | poly | | poly | poly (four times flat at 16) | poly |
| middle restriction with pushes, halt (5b) | poly | exp | | exp | poly | exp |
| fair OR, one endless member, answer (4) | poly | poly | poly | poly | poly | |
| fair OR, three endless members, answer (4b) | exp | exp | exp | poly | exp | |
| strings, answer (4d) | exp | poly | poly | exp | poly | exp, argued: its join reads the same `2^i` answers |
| ladder, halt (3) | undecided | undecided | | undecided | undecided | unknown past `n = 4` |

The exponential growth of the share rule on 4b and 4d is what the share bound allows (its factor is `5^k` and `4^k` there).

No column is polynomial on every row. Balancing the share rule and unit flat rounds by ticks is polynomial on every row but 4b. Whole rounds are the only rule that is polynomial on 4b. The combination of both is not within twice the better (3.4).

## 7. Fairness (roadmap L36)

Measured against the statement of `Fair` in `Trusted/Properties.lean` (branch of the runtime restatement), where a step is one request to the root.

- **The flat bound in steps** holds on all three families with whole rounds (`2k + 7` steps against an alternative that costs 88 to 2695 ticks alone). With unit rounds it holds on 4 and 4d and, by the trend, fails on 4b.
- **The flat bound in ticks**, as the roadmap row words it (`n` times the number of live goals opened), is not met by any single rule on both 4b and 4d. Whole rounds meet it on 4b (89499 ticks at `k = 12` against `2695 × 160`) and by the trend fail it on 4d (949503 at `k = 10` against `5197 × 77`, growing five times per two steps against 1.5). One unit per strategy meets it on 4d and fails on 4b.
- **The share bound** holds for the share rule on every family, and is weak: its factor is exponential in `k` on all of them.
- An engine that uses two rules does not inherit both bounds, for the reason in 3.4.

Why three endless members break the unit rounds and one does not is not explained. The hypothesis, not checked, is that a table then gains answers faster than its one reader reads them, and the lag multiplies per level.

## 8. What the design must change, and what stays open

Adopted in the design note as the revision of 2026-11-13 (third):

1. The interface check is a strategy of every chain goal.
2. The flat round is a whole round.
3. The sentence "alternating costs at most twice the better of the two" is withdrawn.

Open, in order of risk:

1. **The request rule.** No rule measured is polynomial on both the family the engine must win on (5b, where it needs the share rule or the tick balance with unit rounds) and the fair OR family with several endless members (4b, where it needs whole rounds). The candidates not yet tried: whole rounds restricted to goals that carry a boundary, with the share rule for the rest; a balance in which each rule has its own tables. If none works, the conflict is between two requirements Anthony set (the flat fairness bound, and admission over R005 on the middle-restricted family), and it goes to him with tables 4b and 5b.
2. **Lemma G**, with the ladder as its test.
3. **Lemma U.**
4. `TerminatesWhere` for the revised engine: it must halt wherever R001 halts. Follows from Lemma 1 for completion by tables; completion by the unfolding race does not arise in R001.

What the revision forces to be redone: nothing built. Section 5.4 of the design note measured a model of the two rules, not the engine; its numbers are replaced by tables 4 to 4e and 6 here. The trusted statement of `Fair` should say that a step is a request to the root and that a round may cost any number of ticks, or state the flat bound in ticks and accept that it is open.

## 9. Second attack (2026-11-13): the ladder decided, a rule that passes every family, the check narrowed

New tools: `scripts/r005_interpreter.py` (R005 outside Lean), `scripts/symmetric_engine_halting.py` (random programs on both machines), and tables 8 to 12 of `scripts/symmetric_engine_tables.py`. Everything is still on paper and in prototypes.

### 9.1 R005 outside Lean

`scripts/r005_interpreter.py` is the text of R005 at the tag `epoch-1`, definition for definition: the charges of `Trusted/Charged.lean`, `Cost.within` and `Cost.race`, the tabled round machine (`Rungs/Tabled/Gen.lean`), the three unfolders and their two races (R002, R003, R004), and the mirror race (`Rungs/Mirror/Gen.lean`). It covers programs with an empty theory and no stores. Variables are numbered as Lean numbers them, because R003 compares spans as written.

Lean evaluates both sides of a race to the end. The interpreter runs a race under the same doubling budgets and abandons a side at its budget, keeping what it learned, so it counts Lean's ticks in time proportional to them.

*Checked:* `python3 scripts/r005_interpreter.py check` reproduces all 57 numbers that Lean guards for these inputs: the 13 of `Tests/SimulationRuns.lean` (ticks and number of rounds), and the 24 R004 runs and 20 R005 runs of the four bracketings of `mid k` in `Tests/MiddleRuns.lean`. It ran right the first time; there was no fitting.

### 9.2 The ladder is decided: Lemma G is false for the engine of sections 4 and 5

R005 on `@(st nil) ; r_n`, bodies written `G ; (F ; r_(i-1))` as in section 5, ticks to halt. It halts in `n + 4` rounds.

| n | 4 | 8 | 12 | 16 | 20 | 24 | 28 | 32 | 34 |
|---|---|---|---|---|---|---|---|---|---|
| R005, millions of ticks | 3.0 | 40 | 86 | 210 | 300 | 1073 | 881 | 2650 | 1904 |

From 10 to 20 the cost grows 4.5 times and from 20 to 34 it grows 6.4 times: between the second and the fourth power of `n`, with jumps where a race doubles its budget. With the bodies written `(G ; F) ; r_(i-1)` R005 pays more and grows faster (108 million at 10, 1999 million at 20, 7015 million at 24).

The engine of sections 4 and 5 on the same input (table 12, and table 3 for small `n`):

| n | 4 | 8 | 12 | 16 | 20 | 24 | 28 |
|---|---|---|---|---|---|---|---|
| whole rounds, ticks to halt | 6698 | 61456 | 299086 | 957932 | 2535512 | 7745263 | 21356619 |
| goals opened | 208 | 1014 | 2942 | 7371 | 16236 | 49560 | 117693 |
| share, ticks to halt | 4505 | 34863 | 176496 | 1170696 | 4116287 | over 30,000,000 | |
| flat, a unit per goal | 7838 | 44829 | 248457 | 867997 | 2757932 | 7518855 | 19744161 |

Under whole rounds the cost grows 2.65, 3.05 and 2.76 times per four steps from 16 on, where a third power would give 1.95, 1.73 and 1.59. The share rule grows between 3.5 and 6.6 times per four steps. Read as growth: exponential, against a polynomial for R005. *Measured, not proved.*

**The cause.** A goal `<b, G ; F ; r_(j-1)>` has two splits. The split `G | F ; r_(j-1)` is the one R005 has on the cheap writing: `<b, G>` never completes, so nothing is pushed from the left, and `F ; r_(j-1)` is solved once from the right under two general boundaries. The other split, `G ; F | r_(j-1)`, has a left side that completes with two answers, and each answer is pushed into `r_(j-1)` as a new goal, which has the same two splits. That is a search forward from `st nil` with `2^d` goals at depth `d`, and it is a search R005 on the cheap writing never starts. Whole rounds serve every goal of it once a round. The share rule does not starve it either, and halves the share of the useful line at every level.

**So verdict 2 of section 1 is withdrawn.** This failure does come from reading every split, which is how the engine gets bracketing independence. It is not a conflict between `SeqAssoc` and `Simulates` yet, because a rule that reads no bracketing repairs it on every family measured (9.4).

### 9.3 The two rules that had not been tried

**Each rule with its own tables (billboard SIM2).** Two copies of the machine balanced by ticks cost between once and twice the cheaper copy plus a constant, so no run is needed: it is exponential wherever both rules are. Both are on the ladder (9.2). It is rejected.

**Whole rounds only for goals that carry a boundary, the share rule for the rest (SIM3)**, table 11. A request is one whole round of every open goal with a boundary and one request by the share rule that stops at goals with a boundary.

| family | 2 | 4 | 6 or 8 | larger |
|---|---|---|---|---|
| counting down, halt | 227 | 741 | 3253 (8) | 19209 (16), 132635 (32) |
| the ladder, halt | | 65248 | 385720 (8) | over 5,000,000 at 12 |
| middle restriction with pushes, halt | 3395 | 214068 | over 5,000,000 at 6 | |
| fair OR, three endless members, requests to the answer | 17 | 203 | 508 (6) | not within 5,000,000 ticks at 8 |

It is exponential on the ladder, on the middle family and on fair OR. It is rejected.

### 9.4 The split balance

A rule that is neither of the two. It keeps whole rounds, and changes which goals take part in a round.

- The strategies of one split of a chain goal (its join, its two pushes) are a *group*. A goal that is not a chain has one group.
- Every group has a *level*. The level of a goal is the lowest level among its groups.
- A request is a round, started at the root. In its round a goal lets only its lowest groups work. If none of them can do anything, the next lowest work, and so on. A group works by doing its own work and giving a round to every goal it reads. A goal has at most one round per request, whoever asks.
- The level of a group rises by the ticks of its own work and by how much the levels of the goals it reads rose in the round. A goal met again below itself adds nothing.
- Where a goal has one group, the group does everything its inputs allow, as in a whole round. Where it has several, each strategy of a working group does one unit, so that the balance can react.

Two things distinguish it from the share rule. A request is not divided: every goal that a working group reads has its round, so a goal is not starved by a sibling that never finishes, and nothing is halved per level. And a group is charged the rise of the *lowest* group of each goal it reads, not what all the groups of that goal spent. So a split is not charged for the hedging done below it, and the allowance of its competitors does not grow by a factor per level of nesting. On the ladder the forward search is held to the level of the useful line.

It reads no bracketing: the groups of a goal are all the splits of its interval.

Table 8 (`python3 scripts/symmetric_engine_tables.py 8`), ticks to halt, or to the answer where the input does not halt:

| family | values | growth |
|---|---|---|
| counting down, k = 2, 4, 8, 16, 32 | 264, 718, 2698, 13410, 81554 | about `k^2.6`; `2k + 4` requests |
| the ladder, n = 8, 16, 24, 32, 40, 48, 56, 64 | 39395, 298820, 801570, 2100922, 3981533, 5356797, 8078357, 9940348 | 20 to 40: 8 times; 40 to 64: 2.5 times. About `n^3` falling to `n^2` |
| middle restriction with pushes, k = 4, 6, 8, 10, 12, 13, 14 | 77297, 605975, 2558268, 10597431, 36382011, 51666591, 76605167 | 7 to 14: 63 times; 10 to 14: 7.2 times. About `k^6` |
| fair OR, one endless member, k = 2 … 12, to the answer | 818, 3454, …, 81758 | `2k + 4` requests |
| fair OR, three endless members | 1644, 7880, 24148, 57664, 117564, 214904 | `2k + 4` requests, about `k^3.3` ticks |
| strings of k bits, to the answer | 1344, 10170, 66892, 406478, 2322080 | `2k + 4` requests; ticks about six times per two steps, as whole rounds |

It is the first rule that is polynomial on both the middle family with pushes and fair OR with three endless members, and it is polynomial on the ladder. On the middle family it is far dearer than the share rule (531532 at `k = 12` against 36382011): about the sixth power against the fourth. R005 pays three times more for each step there (130823042 at `k = 10`, right-nested), so the family still separates.

On the strings family it reads the table of `q` without a boundary, like whole rounds. R005 pays 16859736 and 106703299 for `k = 2, 4` there (13 and 19 rounds), which grows as fast; it was not run further.

Variants measured and rejected: one unit of work everywhere (fair OR with three endless members is then exponential again: 17 and 161 requests at `k = 2, 4`, no answer within 5,000,000 ticks at 6); whole work everywhere (the middle family is exponential: all groups stand level at the start and the first rounds do everything); every strategy a group of its own (fair OR takes 45, 213, 515, 1126 requests and counting down costs 2949515 at `k = 32`).

### 9.5 The interface check costs more than section 4.1 measured, and is narrowed

**A correction to the prototype.** The check opened its goals when its goal was first looked at, at no charge. It now opens them when it first runs and pays one tick for each. The figures of 4.1 move a little (114 and 258 in turn; 106 and 115 under whole rounds).

**The check on every side is exponential on the middle family** (table 10), ticks to halt:

| k | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|
| split balance, check on every side | 3361 | 18901 | 91195 | 431036 | 2008920 | 9346012 |
| whole rounds, check on every side | 6163 | 43047 | 241436 | 1145735 | 5123463 | 22128137 |
| goals opened, either | 154 | 764 | 3455 | 14851 | 61960 | 253966 |

Every interval of the chain has two interfaces at each edge, the goals opened under them have intervals and edges of their own, and the boundaries nest. Section 4.1 reported "up to six times" at the sizes it ran. Under the share rule the same check stays cheap in ticks (1607010 at `k = 12`) and still opens 641758 goals. On the ladder the check on every side costs the split balance 908036, 3354548, 7815065 and 22666494 ticks for `n = 24, 32, 40, 48`, against 466658, 962956 and 1622539 for the narrowed check below at 24, 32, 40: about the fifth power where the narrowed check has the second, and not decided as a polynomial.

**Narrowed: the check is offered only for a side that contains a call, and the checks of a goal are one group of their own.** A side with no call has finitely many answers and its table completes; the push from the complete side then opens the other side under the interface of each answer, which is at least as exact as the interfaces read from the text. So the check adds nothing there. *Argued, not proved.* The middle family has no call, so its figures are those of table 8. With the checks as a group of their own, a check is held to the level of the cheapest split.

| | halts at | goals |
|---|---|---|
| `p ; q` | 128 | 27 |
| the identity variant | 342 | 48 |
| counting down, k = 2 … 32 | 428, 1058, 3532, 15576, 85968 | 32 … 242 |
| the ladder, n = 8, 16, 24, 32, 40 | 44785, 176925, 466658, 962956, 1622539 | 1334 … 24867 |
| fair OR, three endless members, to the answer | 1748 … 215088, `2k + 4` requests | |

The ladder grows 4.5 times from 20 to 40: about the second power.

### 9.6 What O1 reduces to now

The engine: the design note's engine with the split balance and the narrowed check.

**Lemma 1 (rounds)** and **Lemma 2 (no repeated work)** of section 5 are about the goals R005 opens on a writing `w`. Under the split balance a goal does not work in every round, so Lemma 1 needs a new form: the group of the written split of a goal on `w` works whenever it is among the lowest. Not restated precisely.

**Lemma G is replaced by two.**

- **G1 (the written line is charged additively).** Fix `w`. The level of the group of the written split of a goal is at most its own work plus the levels of the goals it reads, and the level of each of those is at most the level of its own written group. So the level of the root's written group is at most the work R005 on `w` does on its goals, counted once for each reader. *Argued from the definition.* This is the step that failed for the share rule (a factor per level) and for whole rounds (no bound at all).
- **G2 (what a group really spends is polynomial in its level).** *Open, and it is now the content of O1.* A group's level counts the lowest group of each goal it reads. What those goals really spend is the sum over their groups. Each group of a goal is within one unit of the lowest when it last worked, so a goal with `m` groups spends about `m` times its level on its own work; but the goals below it are different for different groups, and in the worst case the factor is `m` per level of nesting. Two things keep it small on the families measured: a push that opens many goals divides its level among them (the ladder), and intervals are shared between splits (the middle family). No family was found on which the factor compounds. None was looked for by search.

**Lemma U (the check finishes what the unfolding race finishes).** *Open.* New evidence, `scripts/symmetric_engine_halting.py`: 200 random programs (one to three definitions, each a union of chains of up to three spans and calls over two unary constructors, and a query that is a chain of two or three). R005 halts within 8 rounds and 1,000,000 ticks on 138 of them. The engine halts on all 138, and on 35 more, within 150,000 ticks. 14 gave no verdict in the time and memory allowed. So no counterexample to Lemma U or to `TerminatesWhere` was found. The test is weaker than it looks: the engine with no check at all also halts on all 138, so none of these programs needs the check, and `p ; q` of 3.1 remains the only input known that does.

The recursion guard (each call is unfolded once when an edge is read) is unchanged, and so is the doubt about it.

### 9.7 Fairness

Against `Fair` as it is stated (a step is a request to the root): the answer of each of the three fair OR families arrives in `2k + 4` requests under the split balance, whatever the number of endless members. So the flat bound in steps holds on what was measured.

In ticks, with `n` the cost of the alternative alone and the bound `n` times the goals opened:

| family, at the largest k | the alternative alone | goals | bound | split balance |
|---|---|---|---|---|
| one endless member, k = 12 | 2695 | 144 | 388080 | 81758 |
| three endless members, k = 12 | 2695 | 174 | 468930 | 214904 |
| strings, k = 10 | 5197 | 148 | 769156 | 2322080, and growing six times per two steps |

So the split balance meets the flat bound in ticks on the two families with numbers and misses it on strings, as whole rounds do. One unit per strategy meets it on strings and loses fair OR with three endless members. No rule measured has the tick form on all three. On strings the cost is in the join of the root, which reads the table of `q` with no boundary; R005 reads the same table.

### 9.8 Adopted, and what stays open

Adopted in the design note as the revision of 2026-11-13 (fourth):

1. The request rule is the split balance (9.4). The share rule, the flat round and their alternation are withdrawn.
2. The interface check is offered only for a side that contains a call, its goals are opened when it first runs, and the checks of a goal are a group of their own (9.5).

Open, in order of risk:

1. **G2.** A proof, or a family with nested goals whose splits read different goals at every level.
2. **Lemma U**, and with it `TerminatesWhere`.
3. **The fairness bound in ticks** on a table that grows exponentially with no boundary (strings). Either `Fair` stays in steps, or a rule is found that has both tick bounds.
4. **The cost of the split balance on the middle family** is about the sixth power; the share rule had the fourth. Whether a finer unit of work or weights (roadmap L32) lowers it is not tried.
5. **Bookkeeping.** The prototype does not charge for finding the lowest groups or for a round that reaches a goal and does nothing. An engine pays for both; the charge has to be bounded by the work done.

Nothing built has to be redone. The freeze list of the design note is unchanged: levels are numbers kept in tables, read through `metered`.
