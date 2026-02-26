<overview>
Complete syntax reference for rwlog. Covers terms, variables, pattern spans, relation definitions, and parameterized macros.
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
- Scoped to a single pattern span (same name in different spans = different variables)
</term_type>
</terms>

<spans>
## Pattern Spans

A pattern span relates a left-side pattern to a right-side pattern.

```
pattern -> pattern
```

Variables on the left side are bound by matching. Variables appearing on both sides transfer values left-to-right. Variables appearing only on the right side are existentially quantified (fresh).

<example name="Simple span">
```
a -> b
```
Relates `a` to `b`.
</example>

<example name="Span with compound terms">
```
(cons $x $y) -> $x
```
Relates any cons cell to its first element.
</example>

<example name="Span with nested patterns">
```
(cons (s $x) $y) -> (cons $x $y)
```
Decrements the first element of a cons cell.
</example>

<example name="Span preserving structure">
```
(pair $x $y) -> (pair $y $x)
```
Swaps elements of a pair.
</example>

<example name="Span with constraint guard">
```
(pair $x $y) { (eq $x $y) } -> $x
```
The guard `{ (eq $x $y) }` requires the constraint to be satisfied. See `constraints.md` for details.
</example>
</spans>

<guards>
## Constraint Guards

Pattern spans can have **guards** — constraints that must be satisfied for the span to apply:

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
[a -> b ; c -> d]           # Sequence of two spans
[(s $x) -> $x ; countdown]  # Span followed by recursive call
[span1 | span2]             # Explicit grouping of alternatives
```

**When to use:**
- Creating sequences of spans and calls
- Overriding default operator precedence
- Making complex expressions readable
</grouping>

<relations>
## Relation Definitions

Named relations group multiple alternatives with disjunction. Each alternative is a relation expression (a pattern span, a named relation call, a composition, a conjunction, etc.).

```
rel name {
    alternative1
    |
    alternative2
    |
    alternative3
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

<pattern_matching_macros>
## Pattern-Matching Macros

The `@` prefix on a definition parameter marks it as **term-valued**: the argument is matched structurally against the pattern rather than substituted as a relation. Multiple definitions with the same name/arity add equations; the first definition establishes which positions are term-valued.

```
rel fmap(@unit, f) { $x -> $x }
rel fmap(@xvar, f) { f }
rel fmap(@(sum $a $b), f) {
    [(inl $x) -> $x ; fmap($a, f) ; $y -> (inl $y)]
  | [(inr $x) -> $x ; fmap($b, f) ; $y -> (inr $y)]
}
```

**Meta-variables** (`$a`, `$b`) in term patterns bind sub-terms. These are available only in macro call term arguments within the body — not in pattern span left/right sides (spans are NF-factored at parse time).

**Call syntax:** At call sites, no `@` is needed. The parser knows which positions are term-valued from the definition:
```
fmap((sum unit xvar), [$x -> (s $x)])
```

**Expansion-time structural recursion:** Recursive calls with structurally smaller term args (e.g., `fmap($a, f)` inside `fmap(@(sum $a $b), f)`) are expanded at macro-expansion time, not wrapped in Fix/Call. This terminates because terms have finite depth.

**Identity self-calls** pass the same term pattern and relation params unchanged — these produce Fix/Call for runtime recursion:
```
rel repeat_fmap(@(sum $a $b), f) {
    fmap((sum $a $b), f)           # identity → Fix/Call
  | fmap($a, f)                    # structural → expanded at expansion time
}
```

<example name="Polynomial functor map">
```
rel fmap(@unit, f) { $x -> $x }
rel fmap(@xvar, f) { f }
rel fmap(@(sum $a $b), f) {
    [(inl $x) -> $x ; fmap($a, f) ; $y -> (inl $y)]
  | [(inr $x) -> $x ; fmap($b, f) ; $y -> (inr $y)]
}
```

`fmap((sum unit xvar), inc)` expands to:
```
[(inl $x) -> $x ; $x -> $x ; $y -> (inl $y)]    # unit: identity
| [(inr $x) -> $x ; inc ; $y -> (inr $y)]        # xvar: apply inc
```
</example>

**Rules:**
- The `@` positions must be consistent across all equations for the same macro
- Term arguments at call sites must be ground (no `$`-variables)
- Term arguments inside macro bodies may reference meta-variables from enclosing term patterns
- Expansion depth is limited to 128 levels to catch non-structural recursion
- Forward references work: macro A can call pattern-matching macro B defined later
</pattern_matching_macros>

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

<example name="Inline span">
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
