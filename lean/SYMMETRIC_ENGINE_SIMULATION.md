# The simulation theorem for the symmetric engine: what was found

2026-11-13. This is the attack on open point O1 of `SYMMETRIC_ENGINE.md` (roadmap M6, brief item 8): is the engine within a polynomial of R005 on the cheapest writing of every query? Everything here is on paper and in a prototype. No Lean engine exists.

The prototype is `scripts/symmetric_engine_tables.py`. It is the engine of the design note with recursion through tables, pushes that open one goal per answer (O4), R001's exact completion check, and the request rules as options. `python3 scripts/symmetric_engine_tables.py 2` prints table 2, and so on. The numbers for R005 are evaluated in Lean by `Tests/SimulationRuns.lean`, at commit `326b608` (the file is parked with R005, `PARKED.md`). Ticks of the prototype and ticks of R005 are not the same unit; only growth is compared, except where one side does not halt.

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
