# Query-bounded Dataflow Engine: Full Implementation Plan

This document specifies a complete redesign of the evaluation engine as a **query-bounded, goal-directed, incremental dataflow system** with **suspension/resumption** and **canonicalized deduplication**. It is written to make behavioral tests like:

- Treecalc `@(f (f (b l) l) l) ; app` **exhaust after one answer**
- Peano addition queries **exhaust after one answer**

both correct and implementable, even when underlying recursive relations have infinite global denotations.

The design is **behavior-first**: observable behavior is defined in terms of query answer streams (`next()`), not internal structure.

---

## 0. Scope and non-goals

### In scope
- Correctness of relational semantics for `Atom`, `Or`, `And`, `Seq`, `Fix`, `Call`.
- **Query-bounded exhaustion**: returning `None` when the query has no more answers, even if some `Fix` relation is infinite in general.
- Deterministic termination behavior under a step/fuel bound.
- A precise scheduler/fairness policy for joins and recursion.
- Sound and stable deduplication (including constraints) via canonicalization.
- Deletion-first replacement of the current `Node/Work/PipeWork/ReplayOnly` model.

### Non-goals
- Computing the full denotation of infinite relations.
- Preserving existing internal evaluation order. Tests must not rely on specific ordering unless explicitly stated.
- Parallelism. (The engine is single-threaded and uses an explicit scheduler.)

---

## 1. Definitions

### 1.1 Normal Forms (NF)
An `NF` represents a (possibly constrained) rewrite span, factored as:

- `match_pats`: patterns matched against input
- `drop_fresh`: wiring plus constraints
- `build_pats`: patterns constructed as output

Existing kernel operators are used:
- `compose_nf(a, b) -> Option<NF>`
- `meet_nf(a, b) -> Option<NF>`
- `dual_nf(nf) -> NF`


### 1.1.1 Matching only (no unification)

The system must **not** implement or rely on *full unification* (a single substitution over a shared variable scope).
Every place that “looks like unification” in the kernel (composition, intersection/meet, etc.) is actually **matching** because the two inputs do **not** share variable scope.

#### Variable scope rule (α-invariance)
Variables are scoped to the syntactic object they originate from (rule/NF/tensor).
A variable index/name has **no meaning across** two different objects.
Any operation that compares terms from two different objects must first α‑rename one side (or tag variables by scope) so that the variable sets are disjoint.

This is a correctness requirement: renaming variables in one operand must not change observable results.

#### Definition: matching
A **matching** of two terms `s` and `t` is a pair of substitutions `(θ_s, θ_t)` such that:

- `s[θ_s] = t[θ_t]`.

Variables in `s` and `t` are in disjoint namespaces; equality is purely syntactic after substitution.

#### Definition: most‑general matching
A matching `(θ_s, θ_t)` is **most general** if for any other matching `(λ_s, λ_t)` of the same two terms, there exist substitutions `(μ_s, μ_t)` such that:

- `λ_s = θ_s ∘ μ_s` and `λ_t = θ_t ∘ μ_t`.

Operationally: compute one most‑general matching, then every other solution is obtained by further instantiating the remaining variables on each side.

#### Implementation requirement
Implement a “two‑scope” matching primitive:

- input: two terms (or term lists) with separate variable scopes
- output: a most‑general matching `(θ_left, θ_right)` in *solved / idempotent form* (ranges mention no variables that are further substituted on that same side)
- failure: `None` if the terms cannot be made equal

**Allowed implementation:** run a standard first‑order unification algorithm on the *disjoint union* of the two variable sets (after α‑renaming one side), but keep it encapsulated behind a matching API so the system never performs unification over a shared scope.

### 1.2 Canonical NF (`CanonNF`)
All set membership, equality, and deduplication are performed on a canonical representation:

**CanonNF invariants**
1. Constraints are normalized **syntactically** into a canonical form and may be rejected as unsatisfiable by *local* checks (e.g., `diseq(t,t)` if the constraint language includes disequality).
2. CanonNF performs **no general equality solving / unification**. The only substitutions ever applied are those produced by explicit **matching** steps in kernel operators (e.g., `meet_nf` / `compose_nf`) and by explicit α‑renamings; constraint normalization never generates new substitutions.
3. Remaining free variables are alpha-normalized deterministically (`v0, v1, ...`) by first-occurrence order across:
   - substituted term patterns (match/build)
   - residual constraints (in a fixed traversal order)
4. Residual constraints are stored in a canonical ordering.
5. Hashing and equality are structural equality of the canonical form.

**Implementation note**
- This is not optional. Without canonicalization, dedup in cyclic graphs is not sound and leads to churn or missed termination.

### 1.3 Deltas
Every node’s output is an append-only set with a delta stream:

- `out_set :: HashSet<CanonNF>`
- `out_vec :: Vec<CanonNF>` (stable insertion order for indexing)
- `out_delta :: VecDeque<CanonNF>` (unconsumed newly-added outputs, optional)

Edges propagate **deltas**. No node ever reprocesses a dependency’s entire set once it has processed a prefix of `out_vec`.

### 1.4 Quiescence and exhaustion
The engine maintains a global worklist of runnable tasks.

- **Quiescent**: the global worklist is empty.
- **Root has unread answers**: `root_read_idx < out_vec[root].len()`.
- **Exhausted (`None`)**: root has no unread answers **and** the engine is quiescent.

There is no observable “temporarily blocked” state. A node may be waiting for future dependency growth, but that is represented by the absence of runnable tasks (and therefore contributes to quiescence).

**Crucial invariant Q1**
> If a node has pending internal work that can produce new output using only already-known inputs, the node must be runnable (scheduled).

With Q1, quiescence implies no further output can ever be produced for the demanded computation.

### 1.5 Fuel / step bound API
The public iterator must be testable without wall-clock timeouts:

- `next_with_fuel(fuel_steps) -> Result<Option<Answer>, OutOfFuel>`

Semantics:
1. Return `Ok(Some(ans))` when the next unseen root answer becomes available.
2. Return `Ok(None)` when exhausted (per §1.4).
3. Return `Err(OutOfFuel)` when fuel reaches 0 before (1) or (2).

Fuel is an operational bound; it is not part of denotational semantics.

---

## 2. High-level architecture

### 2.1 Replace search trees with a dataflow graph
The entire query is compiled into a **dataflow graph** of nodes. Nodes produce NFs incrementally. Cycles arise only from `Fix`/`Call`.

### 2.2 Demand restriction (goal-directed evaluation)
To satisfy query-bounded exhaustion, recursion cannot compute global fixpoints. The engine evaluates only what is demanded by the query.

Demand restriction is implemented by **goal sets** attached to `Fix` binders:

- A `Fix` binder owns a `Table` with:
  - `answers`: deduped `CanonNF`
  - `goals`: deduped `CallGoal` instances representing demanded call contexts
- A `Call` site **registers goals** with the corresponding binder’s table.
- The binder’s table runs **only** for registered goals; without goals, it produces no answers.

This is tabling with suspension/resumption, but the table identity is **one per binder instance** (lexical scope), not one per boundary/context. Context is represented as a goal *inside* the table, not as a table key.

This prevents infinite table proliferation while remaining query-bounded.

### 2.3 Demand propagation (all nodes, not just Call/Table)

**Every node is demand‑driven by its consumers**, not just `Call`/tables.

Operational rule:

- A node is allowed to step / ingest / pair / emit **only if at least one downstream consumer is currently demanding additional outputs from it**.
- If a node has no demanded consumers, it is **inactive** and must not schedule itself or its dependencies.

This is required for “`next_with_fuel` returns `None` when the demanded computation is complete” to be meaningful without computing global denotations.

---

## 3. Core runtime data structures

### 3.1 Scheduler
Single global scheduler:

- `worklist :: VecDeque<TaskId>`
- `scheduled :: HashSet<TaskId>` (or bitset) to avoid duplicates

`enqueue(task)` adds task to worklist iff not already scheduled.

### 3.2 Node outputs
Each node `n` owns:

- `out_set :: HashSet<CanonNF>`
- `out_vec :: Vec<CanonNF>`
- optional `out_delta` if convenient

### 3.3 Reverse dependencies (subscriptions)
To propagate deltas, maintain reverse edges:

- `dependents[n] :: Vec<NodeId>`

When a node’s output grows, schedule dependents’ tasks.

### 3.4 Call goals
A `CallGoal` is a canonical representation of the **boundary patterns** that a `Fix` relation is demanded to relate.

**Required properties**
- Canonical under alpha-renaming and constraint normalization (use same canonicalization machinery as `CanonNF`).
- Stable under irrelevant arity drift: goals must not distinguish contexts that differ only by existentially fresh, unused variables.

**Concrete representation**
Represent the goal as two optional canonical boundary pattern lists (not full context NFs):

- `goal = (L: Option<Boundary>, R: Option<Boundary>)`

Where:
- `L` is the **call-input boundary** (a list of patterns)
- `R` is the **call-output boundary** (a list of patterns)

These boundaries are derived from full **call-site context NFs**:

- `ctxL`: composed NF of everything to the left of the call in the current `Seq` context
- `ctxR`: composed NF of everything to the right of the call in the current `Seq` context

Derive the goal boundaries from those contexts:

- `L = canonBoundary(buildPats(ctxL))`
- `R = canonBoundary(matchPats(ctxR))`

**Goal canonicalization**
- Canonicalize each boundary to the same canonicalization used by `CanonNF` (alpha-normalization + canonical ordering).
- Apply an additional minimization pass to eliminate existential garbage:
  - remove unused RHS-only variables that do not flow into any match/build position of the call interface
  - normalize variable numbering to the minimal equivalent

(Implementation detail: compute a reachability set of vars from the boundary’s interface, drop the rest, then alpha-normalize.)

### 1.6 Call-goal context propagation and `And` barrier

**Rule: `And` is a context barrier for call-goal construction.**

For a `Call` that occurs *syntactically inside an `And` branch*, **do not** include any **outer sequential context** (the enclosing `Seq` prefix/suffix outside that `And`) in the call’s `(ctxL, ctxR)` goal.

**Contexts are scoped to the branch only (stop at `And`).**

Outer sequential context is applied **at the `And` node itself**, after (and only after) the two branches have been combined by the `And` meet.

#### Why propagating outer sequential context into `And` branches is wrong (under matching)

`And` combines branch outputs by a **meet** that computes a **matching** between branch outputs. That meet can introduce substitutions that relate information coming from *both* branches.

If you push the enclosing `Seq` context into a `Call` inside a branch, you are requiring that branch to satisfy constraints that are only derivable **after** the meet has been performed (because those constraints depend on the matching between branch outputs). This over‑constrains the call.

In treecalc, rules 5/7 rely on `And`. Passing the outer sequential context into both branches can prevent any branch‑local `Call` from producing the partial NFs that are necessary for the meet to succeed, so the whole computation emits no first answer.

#### Structural context propagation rules

1. **Seq**
   Context propagates through `Seq` bidirectionally as intended:
   a `Call`’s context may depend on both the left prefix and right suffix **within the same sequential region**.

2. **Or**
   Both branches inherit the same context (no barrier).

3. **And**
   `And` splits the world into three context regions:
   - The `And` node itself lives in the enclosing region and is subject to the enclosing region’s sequential context.
   - Each branch is evaluated in its **own branch region**, and **call-goal contexts inside a branch must be computed using only the sequential structure inside that branch region**.
   - No call-goal context may include any atoms/rels that are outside the nearest enclosing `And`.

Equivalently: **when computing `(ctxL, ctxR)` for a call, do not cross an `And` boundary.**

#### Structural reference definition (context extraction stops at `And`)

```haskell
data Rel
  = Atom String
  | Call String
  | Seq [Rel]
  | Or  Rel Rel
  | And Rel Rel
  deriving (Eq, Show)

-- A "context region" is any subtree not crossing an And boundary.
-- We compute, for each Call, the Seq prefix/suffix *within its nearest region*.
type Ctx = ([Rel], [Rel])  -- (prefix, suffix) as lists, interpreted as Seq
type CallCtxs = [(String, Ctx)]  -- (callName, (prefix, suffix))

collect :: Rel -> CallCtxs
collect rel = go [] [] rel
  where
    -- go pre suf r: traverse r knowing the region-local prefix/suffix lists
    go :: [Rel] -> [Rel] -> Rel -> CallCtxs
    go pre suf (Call f) = [(f, (pre, suf))]

    go pre suf (Atom a) = []  -- atoms aren't calls

    go pre suf (Or a b) =
      go pre suf a ++ go pre suf b

    -- And is a barrier: branch-local context resets to empty on entry.
    go pre suf (And a b) =
      go [] [] a ++ go [] [] b

    -- Seq distributes region-local prefix/suffix within the Seq itself.
    go pre suf (Seq xs) =
      concat [ go (pre ++ take i xs) (drop (i+1) xs ++ suf) x
             | (i, x) <- zip [0..] xs
             ]
```

#### Where the outer sequential context is applied

Outer sequential context is still enforced, but **at the `And` node itself**, after the branch results are combined:

- The enclosing `Seq` composes its prefix/suffix with the **output of the `And` node** (not with the internals of each branch).
- The `And` node combines branch results via meet (matching-based), producing an NF that can then legitimately be constrained by outer context.

This preserves pruning without applying constraints before the matchings that justify them exist.

---

## 4. Node types and exact operational semantics

All nodes are incremental, delta-driven, and deduped by canonical forms.

### 4.1 Atom node
- Output is the singleton set containing the canonical form of the given NF.
- Emits once; then idle forever.

### 4.2 Or (Union) node
Inputs: `A`, `B` nodes.

State:
- `a_pos :: usize` (how many items consumed from `A.out_vec`)
- `b_pos :: usize`
- `turn :: bool` (alternate which side to pull from when both have unread)

Step:
- Consume at most 1 new item per step (or a small bounded batch).
- On ingest of a new item, insert into output (dedup); if inserted, schedule dependents.

Fairness:
- If both sides keep producing, `turn` alternation guarantees neither side is starved.

### 4.3 Join node (binary): Compose or Meet
This single node type replaces all of:
- `ComposeWork`, `MeetWork`, `AndGroup`, `AndJoiner`, queue/wakers.

Parameters:
- `op ∈ {Compose, Meet}`
- `combine(left, right) = compose_nf(...)` or `meet_nf(...)`

Inputs: `L`, `R` nodes.

#### 4.3.1 Join state
- `L_pos :: usize` (consumed prefix of `L.out_vec`)
- `R_pos :: usize`
- Task queues:
  - `QL :: VecDeque<Task>` tasks created by new left items
  - `QR :: VecDeque<Task>` tasks created by new right items
- `turn :: Side` (`Left`/`Right`) controls which queue to service next when both non-empty.

A `Task` is finite and never waits on future growth:

```
Task {
  side: Side,    // Left or Right
  i: usize,      // fixed index into the side's vec
  j: usize,      // next index into the other vec
  other_len: usize // snapshot length of other vec at creation
}
```

#### 4.3.2 Task creation (delta-driven, semi-naive)
When ingesting new left item `l` at index `i`:
- enqueue `Task{side=Left, i, j=0, other_len=R.out_vec.len()}` into `QL`.

When ingesting new right item `r` at index `i`:
- enqueue `Task{side=Right, i, j=0, other_len=L.out_vec.len()}` into `QR`.

This ensures each pair `(l,r)` is processed exactly once, when the second of `{l,r}` arrives.

#### 4.3.3 Join stepping and fairness
Each Join step performs at most `K` pairings total (constant), using round-robin:

1. If both `QL` and `QR` empty:
   - Join is idle (no runnable work) **unless** new inputs are available (see ingestion below).
2. Otherwise:
   - Choose queue by `turn` if non-empty else the other.
   - Pop front task; perform up to `min(K, remainingPairs(task))` pairings.
   - If task incomplete, push it to the back of the same queue.
   - Toggle `turn` after servicing one task.

In parallel (within the same step), Join may ingest at most 1 new input from `L` or `R` if `L_pos < L.len` or `R_pos < R.len`.
- Ingestion is also bounded and alternates to avoid starvation.

#### 4.3.4 Idleness definition
Join is idle iff `QL` and `QR` are empty **and** there are no unread inputs available at `L_pos`/`R_pos`.
There are no “waiting cursors”: tasks snapshot `other_len` and are runnable until completion.

#### 4.3.5 Demand policy for Join/And when a side is empty or blocked

**Join/And are demand‑driven by consumers**, and **must not pull from a non‑empty side when the other side is empty and not yet exhausted**.

For **binary meet nodes** (`And` and any Join‑like node, including the join that implements `Seq` composition), the rule is:

- If one side currently has **zero available items** and is **not known exhausted**, the meet node is **blocked on that side** and must:
  - **demand only the empty side**, and
  - **suspend demand for the non‑empty side** (so it cannot keep ingesting indefinitely).

Reason: while one input set is empty, the meet output set is necessarily empty; pulling more from the other side cannot produce any meet outputs until the empty side produces at least one item.

If one side is **exhausted** (will never produce any items under the current demand), then after the meet node has processed all already‑available cross pairs (if any), it becomes **exhausted** too and stops demanding both sides.

**Demand policy for a meet node (precise):**

Model the meet node state as:

```haskell
data MeetState a b = MeetState
  { ls   :: [a]      -- left items seen so far
  , rs   :: [b]      -- right items seen so far
  , lexh :: Bool     -- left exhausted under current demand
  , rexh :: Bool     -- right exhausted under current demand
  , cur  :: (Int,Int) -- next cross-product cursor (implementation detail)
  }
```

Given downstream demand `needOut :: Bool`, the **input-demand decision** is:

```haskell
demandMeet :: Bool -> MeetState a b -> (Bool, Bool)  -- (demandLeft, demandRight)
demandMeet needOut st
  | not needOut = (False, False)

  -- hard block: empty side demanded exclusively
  | null (ls st) && not (lexh st) = (True,  False)
  | null (rs st) && not (rexh st) = (False, True)

  -- once both sides non-empty, demand is for producing/finishing pairs
  | hasUnprocessedPairs st        = (True,  True)

  -- no pairs left to process:
  | lexh st && rexh st            = (False, False)  -- meet itself exhausted
  | rexh st                       = (True,  False)  -- only left can still grow pair space
  | lexh st                       = (False, True)   -- only right can still grow pair space
  | otherwise                     = alternate st     -- symmetric fairness when both can still grow
```

The crucial blocked behavior is exactly the first two “hard block” guards:

- **If `rs` is empty, do not demand left.**
- **If `ls` is empty, do not demand right.**

That is the plan‑level requirement: **suspend** the non‑empty side until the empty side produces at least one item (or is proven exhausted).

### 4.4 And (n-ary) node
Build `And(a,b,c,...)` as a balanced tree of binary Join(Meet) nodes.
This yields deterministic, bounded incremental behavior with the same fairness guarantees as the binary join.

### 4.5 Seq (n-ary) node
Build `Seq([x0..xn])` as a left-associated chain of binary Join(Compose) nodes, optionally balanced for performance.
Correctness is set-based; associativity is ensured by kernel correctness and canonicalization, not by evaluation order.

### 4.6 Fix binder: Table + Body runner + Goal-directed activation

A `Fix(id, body)` compiles to a `Table` object scoped by a unique binder instance `(rel_id, bind_id)`.

There are two conceptual components:
- **Table node**: stores answers and provides them to call sites.
- **Body evaluator**: generates candidate answers **per goal** and adds them to the table.

#### 4.6.1 Table identity and scoping
- Table identity is `(rel_id, bind_id)` where `bind_id` is a unique id for the lexical `Fix` binder instance.
- `Call(id)` resolves to the nearest enclosing binder `(id, bind_id)` via the environment created during graph build.

This pins lexical scoping and avoids cross-scope pollution.

#### 4.6.2 Table state
- `answers_set :: HashSet<CanonNF>`
- `answers_vec :: Vec<CanonNF>`
- `goals_set :: HashSet<CallGoal>`
- `goals_queue :: VecDeque<CallGoal>` (newly registered goals to process)
- `goal_states :: HashMap<CallGoal, GoalRunnerState>` where each goal has an incremental runner.

#### 4.6.3 Call node: goal registration + answer consumption
A `Call` site does not “run” the recursive relation directly. Instead it:
1. Computes its **call-site context NFs** `ctxL` and `ctxR` from surrounding composition structure in the graph.
2. Derives the goal boundaries:
   - `L = canonBoundary(buildPats(ctxL))`
   - `R = canonBoundary(matchPats(ctxR))`
3. Registers the goal `(L,R)` with the table:
   - if new, enqueue it in `goals_queue` and schedule the table runner task.
4. Consumes **table answers for that goal** and composes at the call site:
   - `ctxL ; answer ; ctxR`
   using join nodes in the surrounding graph.

**Important**: table answers are **body-only** (constrained to the boundary `(L,R)`), and call-site context is applied **exactly once** via composition.

##### Goal membership under matching (Option B; no unification)

Rigid boundary equality (Option A) is **not** valid, because composing `idNF(L)` with the body can specialize `L` to `L[θ]`.

Let a goal be `(L, R)` (lists of patterns, in a single shared goal scope), and let an answer NF be `A` with:
- `A.matchPats = L'`
- `A.buildPats = R'`

Then **A belongs to goal (L, R)** iff there exists a **single substitution on goal variables only**:

- `θ : Vars(L ∪ R) -> Pat`

such that:
- `L[θ] = L'` and `R[θ] = R'`

Key points:
- This is **one‑sided matching** (instantiate only goal vars), **not unification**.
- Answer‑side variables are treated as opaque atoms (or equivalently: answer vars are alpha‑renamed to be disjoint from goal vars, then never substituted).
- The same `θ` is shared across `L` and `R` (so shared goal variables are enforced consistently).

**Plan rule update:** replace “answer belongs to goal (L,R) iff `matchPats(answer) == L` and `buildPats(answer) == R`” with the match‑based definition above.

##### Haskell‑like reference implementation (goal → answer matching; no unification)

```haskell
{-# LANGUAGE DeriveFunctor #-}

import qualified Data.Map.Strict as M
import Control.Monad (foldM)

newtype Var = Var Int deriving (Eq, Ord, Show)

data Pat
  = PVar Var
  | PCon String [Pat]
  deriving (Eq, Ord, Show)

type Subst = M.Map Var Pat

-- One-sided match: instantiate only variables on the LEFT (pattern side).
match1 :: Subst -> Pat -> Pat -> Maybe Subst
match1 env (PVar v) t =
  case M.lookup v env of
    Nothing  -> Just (M.insert v t env)
    Just t0  -> if t0 == t then Just env else Nothing
match1 env (PCon c ps) (PCon d qs)
  | c == d && length ps == length qs =
      foldM (\e (p,q) -> match1 e p q) env (zip ps qs)
  | otherwise = Nothing
match1 _ (PCon _ _) (PVar _) =
  -- Right-side vars are opaque; you can't erase a constructor by binding right vars.
  Nothing

matchPats1 :: Subst -> [Pat] -> [Pat] -> Maybe Subst
matchPats1 env ps ts
  | length ps == length ts = foldM (\e (p,t) -> match1 e p t) env (zip ps ts)
  | otherwise              = Nothing

data Goal = Goal { goalL :: [Pat], goalR :: [Pat] } deriving (Eq, Show)

data NF = NF { nfMatch :: [Pat], nfBuild :: [Pat] } deriving (Eq, Show)

-- Membership test: exists ONE substitution θ over goal vars such that
-- goalL[θ] = nfMatch and goalR[θ] = nfBuild.
belongs :: Goal -> NF -> Bool
belongs (Goal l r) (NF l' r') =
  case matchPats1 M.empty l l' >>= \env -> matchPats1 env r r' of
    Just _  -> True
    Nothing -> False
```

#### 4.6.4 Goal runners (incremental per-goal evaluation)
Each goal `g = (L, R)` has a `GoalRunnerState` that incrementally evaluates `body` under **boundary constraints**, not call-site context.

Define an identity NF over a boundary:

```hs
idNF :: Boundary -> CanonNF
idNF b = CanonNF { matchPats = b, dropFresh = mempty, buildPats = b }
```

Mechanically:
- Construct a graph fragment for `body` with **boundary-identity atoms**:
  - `Seq([Atom(idNF L)] ++ body_factors ++ [Atom(idNF R)])`
- The body fragment includes `Call` nodes that register further goals (possibly for the same or mutually recursive tables).
- The goal runner consumes outputs of the body fragment and inserts them into `answers_set/vec`.

**Key property**
- The body fragment is **demanded** only by this goal runner. No goals ⇒ no body evaluation ⇒ no global fixpoint.

#### 4.6.5 Incremental scheduling of goal runners
The table has a runnable task whenever either:
- `goals_queue` is non-empty (new goal to initialize), or
- some initialized goal runner has pending runnable work in its fragment graph, or
- new answers were added and downstream dependents need scheduling (handled via reverse deps).

Goal runners use the same node/task scheduling mechanisms as the main graph; they are not “special threads.”

#### 4.6.6 Duplicates and cycles
When a goal runner derives an answer already in `answers_set`, it is dropped and does not schedule dependents.
This is required to prevent duplicate-driven churn in cyclic recursion.

---

## 5. Duplicate handling and rescheduling rules (global)

These rules apply to **every** node type.

### 5.1 Output insertion rule
On candidate output `x`:
1. Canonicalize to `CanonNF` (`canon(x)`), rejecting if unsatisfiable.
2. If `canon(x) ∈ out_set`: drop and do **not** schedule dependents.
3. Else insert into `out_set`, append to `out_vec`, and schedule dependents.

### 5.2 Input ingestion rule
When ingesting a dependency’s new output, the consumer:
- must not enqueue any work derived solely from an already-seen input item.
- This is achieved by processing dependency outputs by index (`*_pos` cursors), not by event callbacks.

### 5.3 Scheduling rule
A node is runnable iff it has any of:
- unread dependency outputs (`pos < dep.out_vec.len()`), or
- non-empty internal task queues, or
- a local pending queue to emit downstream (optional), or
- for tables: new goals to initialize or active goal runners with runnable work.

---

## 6. Normalization

There are two separate normalization layers.

### 6.1 Structural Rel normalization (before graph build)
Perform once per stored program component:
- every `rel` body
- the query Rel

Rules:
- Flatten nested `Seq` and `And` structures.
- Constant-fold `Zero` through `Seq/And/Or`.
- Fuse adjacent `Atom` nodes in `Seq` via `compose_nf`; if composition fails, replace entire Seq with `Zero`.
- Fuse all-atomic `And` groups via `meet_nf`; if meet fails, replace with `Zero`.

This affects only graph size/performance. It must not change semantics.

### 6.2 CanonNF normalization (continuous)
As specified in §1.2 and §8, canonicalization must run at every dedup boundary.
This affects correctness and termination.

---

## 7. Constraint integration and canonicalization details

Deduplication is only sound if constraints are canonical.

### 7.1 Constraint normalization (no unification)

Canonicalization requires `Constraint` values to have a stable, deterministic syntax and to support early rejection of *trivially* inconsistent constraints.

Required operations:

- `normalize(C, terms) -> Option<C>`
  - Canonicalize associative structure (`And` flattening), sort conjuncts deterministically, and deduplicate identical conjuncts.
  - Apply purely syntactic rewrites that do not require solving equalities (e.g., `And(True, c) -> c`).
  - Detect contradictions that are decidable by local syntax (e.g., `diseq(t,t)`).
  - **MUST NOT** introduce new substitutions by solving equality constraints. The system has no general unification.

- `remap_vars(C, f, terms) -> C`
  - Rename variables inside constraints using a total renaming function `f: Var -> Var`.
  - Used by α‑normalization and by the “shift right operand” step before matching.

- `vars(C) -> BTreeSet<Var>`
  - Enumerate variables referenced by the constraint.

### 7.2 CanonNF equality and hashing
Two NFs are equal for dedup iff their canonical forms are structurally equal:
- canonical match/build term lists
- canonical drop-fresh wiring (after eliminating irrelevant existentials)
- canonical normalized constraints

---

## 8. Observable behavior, ordering, and fairness

### 8.1 What answer order is guaranteed?
The engine guarantees only:
- **set semantics** (no duplicates)
- **eventual completeness** for finite answer sets under sufficient fuel
- **fairness** constraints specified for Or and Join nodes

It does **not** guarantee a particular DFS/BFS order.

If tests need ordering, they must specify it explicitly; otherwise tests must compare sets.

### 8.2 Fairness guarantees (exact)
- **Or**: if both sides continue to produce, neither is starved (alternating pull).
- **Join**: if both `QL` and `QR` are non-empty infinitely often, each queue is serviced infinitely often (round-robin with turn flip).
- **Pair completeness**: for any specific pair `(l,r)` where both elements are inserted at finite times, that pair is processed after the second insertion (modulo fuel, via resumable tasks).

---

## 9. Why this satisfies “query-bounded exhaustion”

### 9.1 Ground addition query
For `@(cons (s z) (s z)) ; add`:
- The call registers a **ground goal** (tight prefix/suffix).
- The table only runs goal runners reachable from that goal.
- In Peano addition, recursion structurally decreases, producing finitely many subgoals and finitely many answers for that goal.
- When all goal runners become idle and no new goals/answers are produced, the scheduler is quiescent and root has no unread answers ⇒ `None`.

### 9.2 Infinite global denotation does not matter
`add` is infinite as a global relation, but the table is not evaluating “add on all inputs,” only “add under the demanded call goal(s).” Therefore the engine can exhaust for ground queries.

### 9.3 If a query truly induces infinite demand, it will not exhaust
If the user queries `@(cons $x $y) ; add` (nonground), the demand may generate infinitely many goals/answers; the engine will keep producing and will not return `None`. Under fuel, it may return `OutOfFuel` between answers.

This matches the intended semantics: `None` means “no more answers,” not “I got tired.”

---

## 10. Implementation phases (deletion-first)

### Phase 1: Canonicalization foundation
1. Implement `CanonNF` construction:
   - canonical constraint normalization (no unification)
   - alpha normalization
   - stable serialization/hash
2. Add tests:
   - alpha-equivalent NFs dedup
   - constraint ordering differences dedup
   - unsat constraint rejects

### Phase 2: Scheduler + simple graph (Atom/Or/Join)
1. Implement `Scheduler`, node storage, reverse deps.
2. Implement node types:
   - Atom
   - Or
   - Join(op=Compose/Meet)
3. Implement `Engine::next_with_fuel`:
   - produce root answers by index
   - step scheduler until root grows or quiescent or fuel exhausted
4. Add tests:
   - Or fairness singleton-not-starved
   - join correctness + no duplicates
   - join “empty branch short-circuits”

### Phase 3: Compile `Rel` into graph (no Fix yet)
1. Structural normalization on `Rel` (pre-graph).
2. Compile `Seq` and `And` into join trees.
3. Add tests for associativity/distribution as set equalities.

### Phase 4: Fix/Call with goal tables
1. Implement binder scoping (`bind_id`) and resolution of `Call`.
2. Implement table object:
   - answers_set/vec
   - goals_set/queue
   - per-goal runner fragments
3. Implement Call goal registration and goal canonicalization/minimization.
4. Ensure no “blocked” state leaks: idle means no runnable tasks.
5. Add regression tests:
   - treecalc app example exhausts after one answer
   - add ground queries exhaust after one answer
   - self-loop fixpoint empty exhausts quickly
   - base+loop emits once then exhausts

### Phase 5: Remove old engine
Delete:
- `Node`, `Work`, `PipeWork`, `ReplayOnly`, `Tables/FixWork` producer iteration model
- queue/waker code used only for join scheduling

Keep:
- kernel (`compose_nf`, `meet_nf`, `dual_nf`)
- `NF` factoring/formatting
- parser

### Phase 6: Performance and observability
- Add deterministic counters behind a feature flag:
  - steps executed
  - tasks enqueued/dequeued
  - goal counts per table
  - outputs per node/table
- Add guardrails:
  - max tasks per step (fuel)
  - memory growth monitoring (optional)

---

## 11. Test suite mapping (what this plan is designed to pass)

The plan is designed to pass tests with these behavioral requirements:

- Treecalc `app` query emits one answer then exhausts.
- Peano addition ground queries emit one answer then exhaust.
- Nonground/infinite-demand queries do not falsely exhaust (they may run indefinitely; fuel yields OutOfFuel).
- No hangs: every `next_with_fuel` returns within the bound.
- No duplicates in observed output.
- Fairness: no starvation in Or/Join under bounded stepping.

---

## 12. Notes on integrating with existing codebase

- Keep the existing `TermStore`, `NF` structure, and kernel operations.
- Build a new module (suggested) `src/df_engine/` containing:
  - canonicalization (`canon_nf.rs`)
  - scheduler (`sched.rs`)
  - node implementations (`nodes.rs`)
  - rel compiler (`compile.rs`)
  - engine API (`engine.rs`)
  - table/goals (`table.rs`)

The replacement should be staged such that existing tests can be ported one-by-one, and the old engine can be deleted once parity is achieved.

---

## Appendix A: Precise answers to the 8 clarification questions (embedded)

1) Exhausted when root “blocked”?  
- Exhausted iff quiescent and root has no unread answers (§1.4). No blocked state is observable.

2) Exact Join scheduling/fairness?  
- Task-based semi-naive join with round-robin queues and bounded K pairings (§4.3).

3) Meaning of Join idle?  
- Idle iff no unread inputs and both task queues empty; no waiting cursors exist (§4.3.4).

4) Duplicates across cycles?  
- Duplicates never reschedule; only genuinely new canonical outputs schedule dependents (§5).

5) Meaning of union-like table nodes?  
- Tables are monotone sets with delta emission; no re-emission of old answers; goal-driven activation (§4.6).

6) Normalization boundary?  
- Structural Rel normalization pre-build (§6.1); CanonNF normalization continuously for dedup (§6.2).

7) Global termination with infinite growth?  
- `None` only at quiescence; infinite-demand computations never quiesce, so do not exhaust (§7, §9.3).

8) Constraints and NF dedup?  
- CanonNF includes solved form + residuals in canonical order with alpha normalization (§1.2, §7).
