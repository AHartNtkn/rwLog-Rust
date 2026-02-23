<overview>
Complete syntax reference for rwlog. Covers terms, variables, rules, relation definitions, and parameterized macros.
</overview>

<terms>
## Terms

Terms are the data structures rwlog manipulates.

<term_type name="Atoms">
Simple identifiers without arguments.

```
z        # Often used for zero in Peano arithmetic
nil      # Empty list
true
false
leaf
```

**Rules:** Lowercase, no special characters, no arguments.
</term_type>

<term_type name="Compound Terms">
A functor applied to arguments, written in parentheses.

```
(s z)              # Successor of zero (represents 1)
(cons a b)         # Cons cell with a and b
(f x y z)          # Functor f with three arguments
(cons (s z) nil)   # Nested: cons of 1 and nil
```

**Rules:**
- Functor comes first: `(functor arg1 arg2 ...)`
- Arguments separated by spaces
- Can nest arbitrarily deep
</term_type>

<term_type name="Variables">
Identifiers starting with `$`. Used for pattern matching (matching-only; no cross-side unification).

```
$x
$y
$result
$head
$tail
```

**Rules:**
- Must start with `$`
- Lowercase after `$` by convention
- Scoped to a single rule (same name in different rules = different variables)
</term_type>
</terms>

<rules>
## Rewrite Rules

A rule transforms an input pattern to an output pattern.

```
pattern -> pattern
```

<example name="Simple rule">
```
a -> b
```
Transforms `a` into `b`.
</example>

<example name="Rule with compound terms">
```
(cons $x $y) -> $x
```
Extracts the first element of a cons cell.
</example>

<example name="Rule with nested patterns">
```
(cons (s $x) $y) -> (cons $x $y)
```
Decrements the first element of a cons cell.
</example>

<example name="Rule preserving structure">
```
(pair $x $y) -> (pair $y $x)
```
Swaps elements of a pair.
</example>

<example name="Rule with constraint guard">
```
(pair $x $y) { (eq $x $y) } -> $x
```
The guard `{ (eq $x $y) }` requires the constraint to be satisfied. See `constraints.md` for details.
</example>
</rules>

<guards>
## Constraint Guards

Rules can have **guards** - constraints that must be satisfied for the rule to fire:

```
pattern { constraint1, constraint2 } -> result
```

The guard appears in curly braces `{ }` between the pattern and arrow.

<example name="Equality guard">
```
rel same {
    (pair $x $y) { (eq $x $y) } -> $x
}
```
Only matches pairs where `$x` equals `$y`.
</example>

<example name="Ordering guard">
```
(range (closed $lo) (closed $hi)) { (lt $lo $hi) } -> ...
```
Only matches ranges where `$lo < $hi`.
</example>

<example name="Multiple constraints">
```
(triple $x $lo $hi) { (leq $lo $x), (leq $x $hi) } -> $x
```
Multiple constraints are comma-separated. All must be satisfied.
</example>

Guards require a constraint theory to be loaded. See `constraints.md` for defining and using theories.
</guards>

<grouping>
## Grouping with Brackets

Use `[...]` to group expressions and control precedence.

```
[a -> b ; c -> d]           # Sequence of two rules
[(s $x) -> $x ; countdown]  # Rule followed by recursive call
[rule1 | rule2]             # Explicit grouping of alternatives
```

**When to use:**
- Creating sequences of rules and calls
- Overriding default operator precedence
- Making complex expressions readable
</grouping>

<relations>
## Relation Definitions

Named relations group multiple rules with disjunction.

```
rel name {
    rule1
    |
    rule2
    |
    rule3
}
```

<example name="Peano addition">
```
rel add {
    # Base case: 0 + y = y
    (cons z $y) -> $y
    |
    # Recursive case: (1+x) + y = 1 + (x + y)
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
```
</example>

<example name="List length">
```
rel length {
    # Empty list has length 0
    nil -> z
    |
    # Non-empty: length is 1 + length of tail
    [(cons $h $t) -> $t ; length ; $n -> (s $n)]
}
```
</example>
</relations>

<macros>
## Parameterized Relation Macros

Macros define relation templates with relation-valued parameters. Expansion happens at parse time — the result is always a plain relation tree.

```
rel name(param1, param2) {
    body using param1 and param2
}
```

**Arity is part of identity:** `fold`, `fold(x)`, and `fold(x, y)` are completely different, unrelated declarations. Bare `fold` does NOT refer to `fold(x)`.

<example name="Non-recursive macro">
```
rel double(r) {
    r ; r
}

rel inc { $x -> (s $x) }
```

`@z ; double(inc)` expands `double(inc)` to `inc ; inc`, producing `(s (s z))`.
</example>

<example name="Macro with two parameters">
```
rel then(first, second) {
    first ; second
}
```

`@z ; then(inc, wrap)` expands to `inc ; wrap`.
</example>

<example name="Recursive macro">
```
rel peel(base) {
    (s $x) -> $x ; peel(base)
    | base
}
```

`peel(base)` inside the body is a recursive self-call (same params in same order). This strips `(s ...)` layers and applies `base` at the bottom.

`@(s (s z)) ; peel(z -> done)` produces `done`.
</example>

<example name="Cross-macro call">
```
rel compose(f, g) { f ; g }
rel double(r) { compose(r, r) }
```

`double(inc)` expands to `compose(inc, inc)` which expands to `inc ; inc`.
</example>

**Rules:**
- Parameters must be lowercase identifiers
- Macro arguments can be any relation expression: rules, sequences, alternatives, conjunctions, bracketed groups, or calls to other macros/relations
- Recursive self-calls must pass the original parameters unchanged (identity self-call)
- Macros can reference other macros defined later in the same file (forward references work)
</macros>

<term_literals>
## Term Literals with @

The `@` prefix creates an identity relation at a specific term.

```
@term
```

This means: input must equal `term`, output equals `term`.

<example name="Filter input">
```
@(cons z z) ; some_relation
```
Only accepts `(cons z z)` as input, then passes to relation.
</example>

<example name="Assert output">
```
some_relation ; @expected_result
```
Runs relation, then asserts output equals `expected_result`.
</example>

<example name="Test specific computation">
```
@(cons (s (s z)) (s z)) ; add
```
Computes 2 + 1.
</example>
</term_literals>

<queries>
## Query Syntax

Queries are expressions evaluated by the REPL:

```
expression
```

<example name="Run relation forward">
```
@(cons z (s z)) ; add
```
</example>

<example name="Run relation backward">
```
add ; @(s (s z))
```
Find pairs that sum to 2.
</example>

<example name="Inline rule">
```
@(pair a b) ; [(pair $x $y) -> (pair $y $x)]
```
</example>
</queries>

<precedence>
## Operator Precedence

From lowest to highest:

| Precedence | Operator | Name |
|------------|----------|------|
| Lowest | `\|` | Disjunction (Or) |
| Middle | `;` | Composition (Seq) |
| Highest | `&` | Conjunction (And) |

**Example:**
```
a | b ; c & d
```
Parses as:
```
a | (b ; (c & d))
```

Use `[...]` to override precedence.
</precedence>
