# Design Notes: Simplifying the Dataflow Engine

These notes capture insights from reviewing `PLAN_CONSOLIDATED.md` and the current implementation.

---

## Background: Tensor Relations

Relations in rwlog are **tensor relations** - they relate **lists** of terms to **lists** of terms:

```
TRel = [Term] -> [Term] -> Prop
```

An NF has:
- `match_pats: SmallVec<[TermId; 1]>` - list of input patterns (arity n)
- `build_pats: SmallVec<[TermId; 1]>` - list of output patterns (arity m)
- `drop_fresh` - variable routing between the two sides

A relation can have different input and output arities. For example:
- `[pair $x $y] -> [$x, $y]` has arity (1, 2) - splits a pair
- `[$x, $y] -> [pair $x $y]` has arity (2, 1) - constructs a pair
- `[cons $x $y] -> [$y]` has arity (1, 1) - extracts tail

Sequential composition `R ; S` requires the output arity of R to match the input arity of S.

The `@term` syntax is shorthand for a relation `[] -> [term]` (arity 0 to 1), which "injects" a term as a query input.

---

## Key Realizations

### 1. Evaluation Must Be Perfectly Symmetric (Duality Invariance)

**This is a fundamental requirement.** A relation and its dual must have identical termination behavior.

If `R` is a relation `[A] -> [B]`, then `dual(R)` is `[B] -> [A]`. The engine must ensure:
- If `R` terminates for some query, `dual(R)` terminates for the dual query
- If `R` produces n answers, `dual(R)` produces n (dual) answers
- The evaluation strategy must not favor "forward" over "backward" or vice versa

This rules out any evaluation strategy that has inherent directional bias. For example:
- Always composing from the left would break symmetry
- Always trying the "input side" first would break symmetry
- Any optimization that treats match_pats differently from build_pats would break symmetry

The dual operation swaps match_pats and build_pats and inverts the drop_fresh wiring. The engine must be oblivious to which "direction" a relation is being used.

**Implication for lazy evaluation:** Laziness strategies must be symmetric. If we're lazy about exploring Or branches, the laziness must not depend on whether we're in "forward" or "backward" mode - there is no such mode.

### 2. Termination is Not Guaranteed (and Shouldn't Be)

Infinite relations are valid. `add` alone produces answers forever - that's correct behavior, not a bug.

A ground input does NOT guarantee termination. Example:
```
loop:
  [$x] -> [$x]
  [$x] -> [(f $x)] ; loop
```
`@(cons z z) ; loop` produces `[cons z z]`, `[f (cons z z)]`, `[f (f (cons z z))]`, ... forever despite the ground input.

Termination depends on the **relation's structure** (e.g., well-founded recursion), not on groundness of queries. The engine cannot and should not try to detect or guarantee termination.

The engine's job:
1. Produce correct answers
2. Not produce duplicates
3. Be fair (don't starve branches)
4. Return `None` only when genuinely exhausted (no more runnable work)

### 3. Or Nodes are Lazy Search Trees

Or nodes represent choice points, not eager unions:
- Each step: take from current branch, then rotate
- Pattern: A, B, A, B, A, B... (miniKanren-style interleaving)
- Nested Ors form a tree explored with fair rotation

Implications:
- Or nodes have state (current branch, rotation state)
- They cannot be flattened into a single union
- Exploration is lazy - branches explored on demand
- **Rotation is structural, not directional** - it's about fairness between Or branches, not about input/output sides of relations

### 4. Late Distribution / Lazy Evaluation

`(A | B) ; C` should NOT eagerly become `(A ; C) | (B ; C)`.

Instead:
- Keep the structure `(A | B) ; C`
- When an answer is needed, try `A ; C` first
- Only explore `B ; C` when needed

Similarly:
- Fix bodies unfold only when goals are registered
- Composition happens on demand, not eagerly

### 5. Pruning Happens During Composition, Not Before

Branches that can't contribute fail during composition. Example with `add`:

```
add = (base_case | recursive_case)

base_case:     [cons z $y]      -> [$y]
recursive_case: [cons (s $x) $y] -> [s $r] where $r from add applied to [cons $x $y]
```

Query: `@(cons z z) ; add`
- This composes `[] -> [cons z z]` with `add`
- Try base_case: `[cons z z]` matches `[cons z $y]` with `$y = z` → outputs `[z]` ✓
- Try recursive_case: `[cons z z]` vs `[cons (s $x) $y]` → pattern mismatch, fails immediately

The irrelevant branch isn't "predicted" to be irrelevant - it fails fast when tried. This is simpler than computing precise goals upfront.

Note: Boundaries are **lists of patterns**, not single terms. A goal `(L, R)` where `L` and `R` are both pattern lists.

---

## Problems with PLAN_CONSOLIDATED.md

### 1. The idNF Prohibition is Stated but Violated

Section 4.6.4.0.3 says:
> Do **not** wrap the goal runner body with `idNF` atoms.

But the implementation does exactly this. The plan is right; the implementation diverged.

### 2. The "Hole NF" Machinery is Overengineered

Section 4.6.3.1 introduces:
- A "hole" NF with disjoint variables and no wiring
- A 4-equation matching system
- MGM (most-general matching) + projection
- 150+ lines of Haskell pseudocode

This is for computing what goals to **register**. But `goal_matches` already filters what answers **belong** to a goal. The complex registration machinery optimizes for "don't register goals that can't possibly help" - but at enormous complexity cost.

### 3. Three Concerns are Conflated

1. **Scheduling demand**: "run this node because someone wants its outputs"
2. **Boundary demand**: "outputs must match this pattern to be useful"
3. **Goal registration**: "what goals should a Call register with its table"

These are mixed together throughout the plan. The `demand_prefix`/`demand_suffix` mechanism in code is this conflation - wrapping boundaries in `idNF`, building nodes, evaluating them, then extracting boundaries back out.

### 4. The Plan is 1184 Lines

Too long for a specification. The implementation diverged from it, suggesting it's too complex to follow correctly.

---

## The idNF Construct

### What idNF Does

`id_nf(boundary)` creates an NF where:
- `match_pats = boundary` (a list of patterns)
- `build_pats = boundary` (same list)
- `drop_fresh = identity` (each variable position maps to itself)

For a boundary `[cons $0 $1]` (a single-element list), `idNF` produces the relation `[cons $0 $1] -> [cons $0 $1]` - the identity restricted to terms matching that pattern list.

This is just `NF::factor(boundary, boundary, ...)` - the identity relation on a specific boundary shape.

### Current (Wasteful) Usage

In `spawn_goal_runner`:
1. Create `idNF(L)` and `idNF(R)`
2. Wrap body: `Seq(idNF(L), body, idNF(R))`
3. Also create demand_prefix/suffix as idNF wrapped in nodes
4. Evaluate the whole thing
5. Filter results with `goal_matches` anyway

The idNF composition is redundant - `goal_matches` does the actual filtering.

### For Demand Propagation

Current flow:
1. `demand_prefix = idNF(L)` wrapped in `Rel::Atom`
2. Build a node for it
3. Pass through the tree
4. At Call node, "evaluate" it (trivially returns L)
5. Extract `build_pats` → get L back
6. Use L

Simpler flow:
1. Take boundary L
2. Pass L through the tree as data
3. Use L

---

## Proposed Simpler Model

```
                    ┌─────────────────┐
                    │   Search Layer  │  Or nodes, interleaving, rotation
                    │   (lazy tree)   │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │ Composition     │  Seq, And - lazy, on-demand
                    │ (lazy combine)  │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │ Tabling Layer   │  Fix/Call - stores answers
                    │ (memoization)   │  Keys: branch-local context only
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │ Boundary Layer  │  goal_matches - late filtering
                    │ (filter)        │  Applied at consumption
                    └─────────────────┘
```

### Key Simplifications

| Complex (current) | Simple (proposed) |
|-------------------|-------------------|
| Compute precise goals via MGM+projection | Register branch-local goals |
| Apply boundaries via idNF composition | Apply boundaries via `goal_matches` filter |
| `demand_prefix: Option<Arc<Rel<C>>>` (nodes) | `demand_left: Option<Boundary>` (data) |
| Wrap goal runner in `idNF(L) ; body ; idNF(R)` | Just evaluate `body` |
| And-barrier + boundary-demand propagation | Context stops at And, boundaries are just data |

### Symmetry Preservation

The simplified design must preserve duality invariance. Key considerations:

1. **Or interleaving is structural** - rotation is about the Or tree shape, not about input/output direction
2. **Composition via `compose_nf`** - must operate on NFs without directional bias
3. **No special-casing of match_pats vs build_pats** - the engine must not treat these differently

The dual of a relation swaps match_pats/build_pats and inverts drop_fresh. The engine must process R and dual(R) identically - there's no "forward mode" vs "backward mode."

**Open question:** Does the current engine actually preserve symmetry? This needs verification through testing: for any relation R and query Q, the answers from `Q ; R` should be the duals of answers from `dual(R) ; dual(Q)`.

### What `goal_matches` Already Does

```rust
fn goal_matches(
    goal: &CallGoal,          // Goal has left: Option<Boundary>, right: Option<Boundary>
    answer_left: &[TermId],   // List of match patterns from answer NF
    answer_right: &[TermId],  // List of build patterns from answer NF
    terms: &mut TermStore,
) -> bool
```

A `Boundary` is a list of term patterns: `SmallVec<[TermId; 1]>`.

This directly checks if an answer's boundary lists match a goal's boundary lists via pattern matching. It's O(pattern size). The idNF composition approach does far more work for the same result.

---

## The And Barrier (Simplified)

The core rule is simple:
- Sequential context (`ctxL`/`ctxR`) stops at And
- Boundary data propagates through And unchanged

A Call inside an And branch:
1. Computes its goal from branch-local context only
2. Receives boundary data from parent (for filtering, not goal registration)
3. Registers branch-local goal with table
4. Answers filtered by `goal_matches` at consumption

The plan's 200+ lines explaining this can be reduced to: "context stops at And."

---

## Summary

The current design is correct but overengineered. The machinery for computing precise goals solves an optimization problem (don't do unnecessary work) at the cost of:
- Correctness (implementation diverged from spec)
- Maintainability (1184-line spec)
- Simplicity (hard to understand and modify)

The simpler approach:
- Or nodes interleave lazily (miniKanren style)
- Composition happens on demand
- Tabling uses simple keys (branch-local context)
- Boundaries filter via `goal_matches` at consumption
- Pruning happens during composition failure, not goal prediction

Performance concern: imprecise goals might cause extra work. But:
1. That's a performance issue, not correctness
2. Lazy exploration mitigates it (irrelevant branches fail fast)
3. Simple code that works > complex code that's broken
