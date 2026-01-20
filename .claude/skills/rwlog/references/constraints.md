<overview>
Constraint Handling Rules (CHR) in rwlog. CHR provides extensible constraints that can simplify, propagate, and interact with each other during evaluation.
</overview>

<what_are_constraints>
## What Are Constraints?

Constraints are declarative assertions that must hold. Unlike rewrite rules that transform terms, constraints:
- Accumulate in a constraint store
- Can trigger simplification rules
- Can propagate to add new constraints
- Can detect contradictions (failure)

Constraints extend rwlog's expressive power for problems like equality reasoning, type checking, and domain-specific logic.
</what_are_constraints>

<defining_theories>
## Defining Constraint Theories

A theory declares constraints and their handling rules:

```
theory theory_name {
    constraint pred1/arity
    constraint pred2/arity

    rule1.
    rule2.
}
```

<example name="Equality theory">
```
theory eq_neq {
    constraint eq/2
    constraint neq/2

    # Reflexivity: X = X always succeeds
    (eq $x $x) <=> .

    # Contradiction: z ≠ (s X)
    (eq z (s $x)) <=> fail.
    (eq (s $x) z) <=> fail.

    # Structural: (s X) = (s Y) iff X = Y
    (eq (s $x) (s $y)) <=> (eq $x $y).

    # Inequality with equal terms fails
    (neq $x $x) <=> fail.
}
```
</example>
</defining_theories>

<rule_types>
## Rule Types

<simplification>
**Simplification (`<=>`)**

Replaces the constraint with a simpler form (or removes it):

```
(constraint args) <=> body.
```

- If body is `.` (empty), the constraint is removed (satisfied)
- If body is `fail`, evaluation fails
- If body is another constraint, it replaces the original

```
# X = X is trivially true, remove it
(eq $x $x) <=> .

# Reduce structural equality
(eq (s $x) (s $y)) <=> (eq $x $y).

# Contradiction
(eq z (s $x)) <=> fail.
```
</simplification>

<propagation>
**Propagation (`==>`)**

Adds new constraints without removing the original:

```
(constraint args) ==> new_constraints.
```

Useful for deriving consequences:

```
# If X = Y, also Y = X (symmetry)
(eq $x $y) ==> (eq $y $x).

# Transitivity: X = Y and Y = Z implies X = Z
(eq $x $y), (eq $y $z) ==> (eq $x $z).
```
</propagation>

<guards>
**Guarded Rules**

Rules can have guards that must hold before firing:

```
(constraint args) <=> guard | body.
```

The guard is checked first; if it fails, the rule doesn't apply.

```
# Guarded nonzero check - different behavior based on guard
(nonzero $x) <=> (eq $x z) | fail.    # If x = z, fail
(nonzero $x) <=> (neq $x z) | true.   # If x ≠ z, succeed
```
</guards>

<multi_head>
**Multi-Head Rules**

Rules can match multiple constraints simultaneously:

```
(constraint1 args1), (constraint2 args2) <=> body.
```

This fires when both constraints are present:

```
# X = Y and X ≠ Y is a contradiction
(eq $x $y), (neq $x $y) <=> fail.

# X = Y and Y = Z simplifies to X = Z
(eq $x $y), (eq $y $z) <=> (eq $x $z).
```
</multi_head>
</rule_types>

<using_constraints>
## Using Constraints in Relations

Constraints are used as **guards** in rewrite rules, appearing in curly braces `{ }` between the pattern and arrow:

```
pattern { constraint1, constraint2 } -> result
```

The rule only fires if all constraints in the guard are satisfiable.

<example name="Equality guard">
```
rel same {
    (pair $x $y) { (eq $x $y) } -> $x
}
```
Only matches pairs where `$x` equals `$y`.
</example>

<example name="Inequality guard">
```
rel different {
    (pair $x $y) { (neq $x $y) } -> (pair $x $y)
}
```
Only matches pairs where `$x` does not equal `$y`.
</example>

<example name="Multiple constraints">
```
(range (closed $lo) (closed $hi)) { (lt $hi $lo) } -> z
```
Multiple constraints are comma-separated: `{ (leq $lo $x), (leq $x $hi) }`.
</example>

<example name="Guard in composition">
```
[$x { (no_c $x) } -> (f $x (c z))] ; app ; @(c z)
```
Guards work within bracketed compositions too.
</example>
</using_constraints>

<constraint_store>
## The Constraint Store

During evaluation, constraints accumulate in a store:

1. **Adding constraints:** When a constraint is encountered, it's added to the store
2. **Rule matching:** CHR rules check if their heads match constraints in the store
3. **Firing:** When a rule matches, it transforms/removes/adds constraints
4. **Propagation:** Continues until no more rules fire
5. **Final state:** Either failure (contradiction) or a simplified constraint store

The store represents the accumulated knowledge about the computation.
</constraint_store>

<common_patterns>
## Common Constraint Patterns

<equality>
**Equality constraints:**
```
theory equality {
    constraint eq/2

    (eq $x $x) <=> .
    (eq (s $x) (s $y)) <=> (eq $x $y).
    (eq (cons $h1 $t1) (cons $h2 $t2)) <=> (eq $h1 $h2), (eq $t1 $t2).
    (eq z (s $x)) <=> fail.
    (eq nil (cons $h $t)) <=> fail.
}
```
</equality>

<disequality>
**Disequality constraints:**
```
theory diseq {
    constraint neq/2

    (neq $x $x) <=> fail.
    (neq z (s $x)) <=> .
    (neq (s $x) z) <=> .
}
```
</disequality>

<domain>
**Domain constraints:**
```
theory nat_domain {
    constraint nat/1

    (nat z) <=> .
    (nat (s $x)) <=> (nat $x).
}
```
</domain>
</common_patterns>

<interaction_with_relations>
## Interaction with Relations

Constraints and relations work together. First load or define a theory, then use its constraints as guards:

```
load equality_constraints.txt

rel same {
    (pair $x $y) { (eq $x $y) } -> $x
}

rel different {
    (pair $x $y) { (neq $x $y) } -> (pair $x $y)
}

rel nonzero_ok {
    $x { (nonzero $x) } -> $x
}
```

Example with ordering constraints:

```
load range_sets.txt

rel card_range {
    empty -> z
    |
    (range (closed $x) (closed $x)) -> (s z)
    |
    (range (closed $lo) (closed $hi)) { (lt $hi $lo) } -> z
    |
    [(range (closed $lo) (closed $hi)) { (lt $lo $hi) }
        -> (range (closed (s $lo)) (closed $hi)) ; card_range ; $n -> (s $n)]
}

rel member {
    (pair $x (rcons $range $rest)) { (between $x $range) } -> $x
    |
    (pair $x (rcons $range $rest)) -> (pair $x $rest) ; member
}
```

The constraints act as filters/guards while the relation structure handles transformation.
</interaction_with_relations>

<debugging_constraints>
## Debugging Constraints

**Constraint not firing:**
- Check that constraint matches rule head exactly
- Verify guard conditions are satisfiable
- Check for typos in predicate names

**Unexpected failure:**
- A simplification rule may be producing `fail`
- Multi-head rule may be detecting contradiction
- Check rule order (first matching rule fires)

**Infinite loop:**
- Propagation rules may be generating unbounded constraints
- Ensure rules make progress (simplify, don't just propagate)
</debugging_constraints>

<residual_constraints>
## Residual Constraints in Output

When a query completes, answers may include **residual constraints** - constraints that couldn't be fully resolved:

```
?- [$x { (no_c $x) } -> (f $x (c z))] ; app ; @(c z)
> (f (b (b l)) (f l $0)) { (no_c $0) } -> (c z)
```

The output `{ (no_c $0) }` indicates that `$0` is constrained but not fully determined. Any value satisfying `(no_c $0)` would work.
</residual_constraints>

<when_to_use>
## When to Use Constraints

**Use constraints when:**
- You need to accumulate and reason about properties
- Equality/disequality relationships matter
- Domain restrictions should be checked
- Multiple assertions must be consistent

**Use plain relations when:**
- Simple input/output transformation
- No need for accumulated state
- Pattern matching suffices
</when_to_use>

<syntax_summary>
## Syntax Summary

| Syntax | Meaning |
|--------|---------|
| `theory name { ... }` | Define a constraint theory |
| `constraint pred/arity` | Declare a constraint predicate |
| `(pred args) <=> body.` | Simplification rule |
| `(pred args) ==> body.` | Propagation rule |
| `(pred args) <=> guard \| body.` | Guarded CHR rule |
| `(c1), (c2) <=> body.` | Multi-head rule |
| `load file.txt` | Load theory from file |
| `pattern { constraints } -> result` | Guard in rewrite rule |
| `{ (c1), (c2) }` | Multiple constraints (comma-separated) |
</syntax_summary>
