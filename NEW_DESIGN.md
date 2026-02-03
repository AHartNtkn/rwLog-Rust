Got it - you want an immediate response. I've updated the task accordingly.


# Goal‑Directed, Dual‑Invariant Dataflow Engine

## Requirements

1. **No groundness assumption**

   * Any relation is a valid query.
   * Example: `add` alone must stream

     * `Rw [cons z $x] [$x]`
     * `Rw [cons (s z) $x] [s $x]`
     * `Rw [cons (s (s z)) $x] [s (s $x)]`
     * … forever.

2. **Duality invariance is a semantic constraint**

   * Let `dual` swap input/output arity and direction:

     * `dual(Rw L R) = Rw R L`
     * `dual(A ; B) = dual(B) ; dual(A)`
     * `dual(A | B) = dual(A) | dual(B)`
     * `dual(A & B) = dual(A) & dual(B)`
   * Required property (stream equivalence):

     * For any program `P` and query `Q`,

       * `answers(P, Q)` is exhausted iff `answers(dual(P), dual(Q))` is exhausted
       * and their answer streams correspond under `dual` (answer‑by‑answer, up to alpha‑equivalence).

3. **Correctness obligations**

   * Produce only correct answers.
   * No duplicates (alpha‑equivalent NFs count as duplicates).
   * Fairness: Or/joins must not starve branches forever (modulo nontermination inherent to the relation).
   * `next()` returns `None` **only** when the demanded search space is genuinely exhausted.

4. **Termination is not guaranteed**

   * Infinite relations and infinite streams are valid.
   * The engine does not attempt to prove termination.

---

## Core model

### Tensor relations and boundaries

A relation denotes a tensor relation between *lists* of terms:

```haskell
type Boundary = [Term]
type TRel = Boundary -> Boundary -> Prop
```

The runtime representation of a produced answer is an NF:

```haskell
data NF = Rw { match :: Boundary, build :: Boundary, ...kernelFields }
```

In the prototype, `NF` includes only `match` and `build` lists; in Rust you also have wiring (`drop_fresh`) and constraints—those live in the kernel and are treated opaquely by the scheduler except where stated.

Sequential composition requires arity alignment:

```haskell
(;) :: (a -> b -> Prop) -> (b -> c -> Prop) -> (a -> c -> Prop)
```

---

## Kernel interface (opaque, but required)

The engine assumes these kernel operations exist and are **self‑dual**:

```haskell
compose_nf :: NF -> NF -> Maybe NF
meet_nf    :: NF -> NF -> Maybe NF
dual_nf    :: NF -> NF
canon_nf   :: NF -> NF         -- alpha-normalize for dedup
```

Required algebraic laws (semantic, not implementation detail):

```haskell
dual_nf (fromJust (compose_nf a b))  == fromJust (compose_nf (dual_nf b) (dual_nf a))
dual_nf (fromJust (meet_nf a b))     == fromJust (meet_nf (dual_nf a) (dual_nf b))
canon_nf (dual_nf x)                == dual_nf (canon_nf x)
```

---

## Goals: the missing “hard part” (demand + pruning)

### Goal = boundary constraints, not wrapper relations

A consumer demands *a subset* of a node’s NF stream via a **Goal**:

```haskell
data Goal = Goal { gMatch :: Maybe Boundary
                 , gBuild :: Maybe Boundary }
```

* `Nothing` means unconstrained on that side.
* Goal sets are **monotone**: they only grow.

### Compatibility is two‑scope matching (not one‑sided)

A node must be able to decide: “can this NF contribute to any demanded goal?”

Define:

```haskell
compatible :: Goal -> NF -> Bool
```

`compatible (Goal (Just m) (Just b)) (Rw L R)` means:

* there exists a two‑scope match between `m` and `L`, and between `b` and `R`,
* where variables in the goal and variables in the NF start in disjoint namespaces,
* i.e. it is matching/unification in a disjoint union of variable scopes.

This is the same *kind* of matching you need for `compose_nf` and `meet_nf`; using a different matching semantics here breaks symmetry and causes “phantom nontermination” via goal filters that are too strict.

---

## Graph + scheduler

The program is compiled to a graph of nodes. Each node maintains:

* `goals : Set Goal` (monotone)
* `outs : Set NF` + `out_vec : [NF]` (deduped by `canon_nf`)
* `exhausted : Bool` (with respect to current goal set)
* `dependents : Set NodeId` (for scheduling notifications)

A **worklist** scheduler repeatedly steps runnable nodes until:

* root emits a new unseen answer → return it
* worklist becomes empty → root is exhausted → return `None`
* fuel hits 0 with nonempty worklist → `OutOfFuel`

No part of the system assumes groundness.

---

## Node semantics

### Atom

An Atom node represents a single NF.

Rule:

* If `goals` is empty: do nothing (undemanded).
* Else:

  * If the atom NF is compatible with at least one goal: emit it exactly once.
  * Then mark exhausted.

This is the **first place** pruning happens and it must be present; otherwise dead branches still emit and can trigger recursive tables.

---

### Or (lazy choice)

State: `(turn, lpos, rpos)`.

Rules:

* Propagate the same `goals` to both children (monotone union).
* Emit answers by interleaving child outputs structurally:

  * each step tries to pull one unseen output from one child, then flips `turn`.
* Exhausted when both children exhausted and all their outputs are consumed.

No eager distribution, no flattening.

---

### Compose (the critical piece)

Compose node represents `A ; B`.

It must do **three things**:

1. **Project external goal constraints**

   * If output goal constrains `match`, that constrains `A`’s `match`.
   * If output goal constrains `build`, that constrains `B`’s `build`.

2. **Synthesize internal join‑key demands**

   * Composition additionally requires `A.build` to match `B.match`.
   * The engine must *discover* what `B.match` shapes are needed from actual `A` outputs (and symmetrically the other way).

3. **Avoid unconstrained unfolding**

   * If neither side has any constraints yet, seeding the wrong side can unfold recursion unnecessarily (and can break duality invariance operationally).
   * Seeding must be symmetric under dual.

#### Goal propagation rules (compose)

Let the compose node have goal set `G`.

**Projection:**

* For each `Goal (Just m) _` in `G`, add goal `Goal (Just m) Nothing` to left child.
* For each `Goal _ (Just b)` in `G`, add goal `Goal Nothing (Just b)` to right child.

**Join‑key synthesis from new outputs:**

* When a **new left output** `Rw L R` arrives:

  * for each `Goal _ gb` in `G` (or `Goal Nothing Nothing` if `G` is empty, but in practice root demands `⊤`):

    * demand right child goal: `Goal (Just R) gb`
* When a **new right output** `Rw L R` arrives:

  * for each `Goal gm _` in `G`:

    * demand left child goal: `Goal gm (Just L)`

This is the minimal mechanism that:

* constrains internal `Call` nodes *without* MGM/hole machinery
* prevents table bodies from computing irrelevant fixpoints
* is symmetric under dual because dual swaps left/right and swaps match/build while reversing Seq

#### Seeding (dual‑invariant)

If neither child has any goals yet, seed exactly one side with `⊤ = Goal Nothing Nothing`.

To preserve duality invariance and avoid unfolding recursive tables unnecessarily:

* Prefer seeding an **Atom** side (Atoms are finite and do not unfold tables).
* Otherwise alternate left/right (structural fairness).

This rule is symmetric under dual because `dual(Atom)` is still an Atom node (its NF is swapped but node kind is unchanged), and `dual` swaps which side the Atom sits on in a sequence.

#### Output generation (semi‑naive join)

Maintain tasks pairing newly‑seen left items with all previously‑seen right items (and vice‑versa), process a bounded amount per step, and for each pair:

* compute `compose_nf(leftNF, rightNF)`
* if `Just out` and `out` is compatible with at least one goal in `G`, emit it (deduped)

#### Compose failure pruning

If, under the propagated goals, the left side becomes exhausted with zero outputs, the composed node is exhausted immediately (cross product empty) and the right side is never demanded beyond what it already has.

This is exactly what makes the `@nil ; listlen` test exhaust.

---

### Meet / And

Meet node represents `A & B` (intersection / conjunction at NF level), implemented as a join.

Goal propagation:

* Output constraints apply to **both** sides (because meet output boundaries must unify with both inputs).
* Join‑key synthesis:

  * from a new left output `Rw L R`, demand right goal `Goal (Just L) (Just R)`
  * from a new right output `Rw L R`, demand left goal `Goal (Just L) (Just R)`
* Seeding rule identical to compose.

Output generation: for pairs, compute `meet_nf(a,b)`.

---

## Tabling and recursion

### Table

A table node represents a recursive definition’s memo table.

State:

* `registered_goals : Set Goal`
* `answers : Set NF`
* `body_root : NodeId`
* `body_pos : Int` (how much of body output has been consumed into the table)

Rules:

* When table receives a new goal, register it and propagate it to `body_root`.
* Consume new outputs from `body_root` into the table answer set (dedup).
* Exhaust when `body_root` is exhausted and fully consumed.

This is **goal‑directed tabling**: the table computes only the portion of its fixpoint demanded by registered goals.

### Call

A call node is a filtered view of the table.

State: `pos` into table’s `out_vec`.

Rules:

* Propagate call’s goals into the table (register).
* Emit table answers that are compatible with call’s goals.
* Exhaust when table exhausted and fully consumed.

---

## Why this fixes the `listlen` exhaustion bug

Relation:

```
listlen =
  Or(
    nil -> z,
    (cons h t -> t) ; listlen ; (n -> s n)
  )
```

Query: `(nil -> nil) ; listlen`.

Key steps:

1. Root is `compose(Atom(nil->nil), Call(listlen))`.
2. Root seeds the Atom side (finite), gets left output `nil->nil`.
3. Compose join‑key synthesis demands right goal `match = [nil]`.
4. Call registers `match=[nil]` with the table.
5. Table propagates `match=[nil]` into body `Or(base, recursive)`.
6. In recursive branch, first atom has `match=[cons h t]`.

   * Atom pruning checks compatibility with goal `match=[nil]` → incompatible → emits nothing and exhausts.
7. That compose becomes exhausted without demanding the recursive call.
8. Only base case contributes (`nil->z`), then the whole computation quiesces.
9. Second `next()` returns `None`, not fuel exhaustion, because there is no runnable work.

No groundness is used anywhere.

---

[Download `df_engine_proto_lazy.py`](sandbox:/mnt/data/df_engine_proto_lazy.py)

Key refinements (all implemented in the file above):

1. **Query-bounded exhaustion for recursion (`listlen` bug)**

   * `TableNode` only records answers that match at least one registered goal:

     * `TableNode.step`: `if any(goal_compatible(g, nf) for g in self.goals_set): self.emit(nf)`
   * `JoinNode` has the “empty exhausted side ⇒ join exhausted” rule:

     * `JoinNode._update_exhausted`: if `left.exhausted and len(left.out_vec)==0` (or right) ⇒ exhausted.
   * Runnable proof: `test_listlen_exhaustion()` in the file.

2. **Fix: calls must be driven by table answers**

   * Compiler now wires `Table -> Call` so new table answers schedule dependent calls:

     * In `build_engine.compile_rel` for `CallRel`: `eng.add_edge(tables[r.name], nid)`.

3. **Lazy, dual-invariant seeding for `compose`**

   * Avoid deadlock on top goal without seeding, and avoid “seed the recursive side first” (breaks dual termination).
   * Implemented in `JoinNode._propagate_goal_projection`:

     * If goal constrains `match`, seed left with `Goal(match,None)`.
     * If goal constrains `build`, seed right with `Goal(None,build)`.
     * If goal is unconstrained (top), seed **exactly one** child chosen by a structural rank (`Atom < Or < Join < Call < Table`).
   * Runnable proof: `test_dual_listlen()`.

4. **Goal refinement preserves structure (prevents “vacuous goals”)**

   * `compose` right-goal synthesis refines join keys by unifying `left.match` with `goal.match` and applying the resulting substitution to `left.build` (and to `goal.build` if present):

     * `JoinNode._derive_right_goal_from` (compose branch).
   * Symmetric refinement from `right.build` vs `goal.build` when deriving left goals:

     * `JoinNode._derive_left_goal_from` (compose branch).

5. **Semi-naive + throttled goal synthesis (lazier than eager cross-product)**

   * Goal synthesis and pairing are both delta-driven via task queues:

     * `GoalTask` and `PairTask`.
   * Join does **pairing first**, and only expands demands aggressively when blocked:

     * `JoinNode.step` runs `_process_pair_tasks(budget=8)` then `_process_goal_tasks(budget=8 if blocked else 2)`.

6. **Minimal normalization-only constraints**

   * `NoCon(name, term)` implemented with purely structural satisfiability (`contains_con`) and “drop when ground” rule.
   * This is enough to model `{no_c $x}` as a constraint carrier in NFs (if you represent it as `constraints=(NoCon("c", ...),)` in an `AtomRel` NF).

To run the included tests:

```bash
python df_engine_proto_lazy.py
```

