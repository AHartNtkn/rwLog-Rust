<overview>
How variables and terms work in rwlog. Variables are logical variables used in matching, not assignment variables.
</overview>

<variables>
## Variables

Variables in rwlog are **logical variables** - they represent unknown values that get determined through matching.

<naming>
**Naming:**
- Must start with `$`
- Followed by lowercase identifier
- Examples: `$x`, `$head`, `$tail`, `$result`
</naming>

<scoping>
**Scoping:**
- Variables are scoped to a **single pattern span** — one `pat -> pat` or `pat { guard } -> pat`
- The same variable name in different spans is a different variable each time
- Within a span, the same variable name always refers to the same value (equality enforced by matching)

```
rel example {
    (pair $x $y) -> (pair $y $x)   # $x, $y local to this span
    |
    (triple $x $y $z) -> $x        # Different $x, $y — new span, new scope
}
```

When composing spans with `;`, each span has fully independent variables. There is no mechanism for a value from one span to be "carried" to a later span — the only connection is through matching between adjacent sides. If you need to combine a value from one computation with the result of another, use conjunction (`&`).

Variable scoping is per-span and **symmetric**: both left and right sides of a span follow the same rule. The same variable name appearing in the right side of two different spans has no more connection than the same name in the left side of two different spans — none at all. When writing conjunction (`&`), reusing the same variable names in the right sides of parallel branches is perfectly valid and means exactly the same as using different names, since scopes never overlap.
</scoping>

<matching>
**Matching:**

When a variable appears multiple times in a span, all occurrences must match the same value.

```
(cons $x $x) -> $x
```
This only matches cons cells where both elements are **identical**.

- `(cons a a)` matches, produces `a`
- `(cons a b)` does NOT match (a ≠ b)
</matching>

<matching_vs_unification>
**Matching vs unification:**

rwlog uses **matching**, not unification across sides. A match between terms `s` and `t` is a pair of substitutions
`(theta1, theta2)` such that `s[theta1] = t[theta2]`. Variable identities are local to each side; the same variable name on both sides
does not imply shared identity.

When the two sides use disjoint variable namespaces, unification and matching coincide.
</matching_vs_unification>
</variables>

<pattern_matching>
## Pattern Matching

The left side of a pattern span is a **pattern** that matches against input.

<simple_patterns>
**Simple patterns:**
```
a -> b                    # Matches exactly 'a'
$x -> $x                  # Matches anything, returns it unchanged
(cons $h $t) -> $h        # Matches cons, extracts head
```
</simple_patterns>

<nested_patterns>
**Nested patterns:**
```
(cons (s $x) $y) -> ...   # Matches cons where first elem is successor
(tree (leaf $v) $r) -> ... # Matches tree with leaf as left child
```
</nested_patterns>

<partial_patterns>
**Partial structure:**
```
(f $x $y $z) -> $y        # Matches 3-arg f, extracts middle
(pair $a $b) -> (pair $b $a)  # Matches pair, swaps
```
</partial_patterns>
</pattern_matching>

<term_construction>
## Term Construction

The right side of a pattern span **constructs** the right-hand term using variables bound on the left.

<building_terms>
**Building terms:**
```
$x -> (wrapped $x)        # Wraps input in constructor
(pair $x $y) -> (pair $y $x)  # Rearranges components
$x -> (cons $x nil)       # Creates new structure
```
</building_terms>

<fresh_variables>
**Fresh (existentially quantified) variables:**

If a variable appears on only ONE side of a span, it's existentially quantified — it can take any value. The language is symmetric: this applies equally to variables only on the left or only on the right.

```
$x -> (pair $x $y)        # $y is fresh - can be anything
```

This creates non-determinism: the span relates `$x` to `(pair $x $y)` for any `$y`.

This property is powerful for representing object-level binders. Using `(var $x)` with rwlog variables as bound-variable names means fresh variables are generated automatically, with `neq` constraints tracking distinctness. See the "Variables as Object-Level Names" section in `core-patterns.md`.
</fresh_variables>

<shared_variables>
**Shared variables (most common):**

Variables appearing on BOTH sides transfer values:

```
(input $x $y) -> (output $y $x)
```
- `$x` bound on left, used on right
- `$y` bound on left, used on right
- Values flow from pattern match to construction
</shared_variables>
</term_construction>

<common_patterns>
## Common Variable Patterns

<identity>
**Identity:**
```
$x -> $x
```
Pass through unchanged.
</identity>

<extraction>
**Extraction:**
```
(cons $h $t) -> $h        # Get head
(cons $h $t) -> $t        # Get tail
(triple $a $b $c) -> $b   # Get middle
```
</extraction>

<wrapping>
**Wrapping:**
```
$x -> (some $x)           # Wrap in constructor
$x -> (s $x)              # Increment (Peano)
$x -> (cons $x nil)       # Singleton list
```
</wrapping>

<restructuring>
**Restructuring:**
```
(pair $x $y) -> (pair $y $x)           # Swap
(triple $a $b $c) -> (pair $a (pair $b $c))  # Reshape
(cons $h (cons $h2 $t)) -> (cons $h2 (cons $h $t))  # Swap first two
```
</restructuring>

<equality_constraint>
**Equality constraint:**
```
(cons $x $x) -> yes       # Both elements must be equal
(pair $a $a) -> same      # Only matches identical pairs
```
</equality_constraint>
</common_patterns>

<bidirectional_variables>
## Variables and Symmetry

The language is fully symmetric: variables work the same on both sides of a span.

<left_constrained>
**Left-constrained:**
```
@(cons a b) ; [(cons $h $t) -> $h]
```
Result span: `(cons a b) -> a`
- Left side `(cons a b)` is matched by `(cons $h $t)`: `$h = a`, `$t = b`
- Right side is `$h = a`
</left_constrained>

<right_constrained>
**Right-constrained:**
```
[(cons $h $t) -> $h] ; @a
```
Result spans: `(cons a $t) -> a` for any `$t`
- Right side must be `a`, so `$h = a`
- Left side is `(cons a $t)` for any `$t`
</right_constrained>
</bidirectional_variables>

<anti_patterns>
## Variable Anti-Patterns

<unused_variable>
**Unused variable:**
```
(cons $h $t) -> result    # $h and $t bound but never used
```
This works but loses information. Usually intentional for "match but ignore" patterns.
</unused_variable>

<typo_different_vars>
**Typo creating different variables:**
```
(cons $head $tail) -> $haed   # Typo! $haed is fresh, not $head
```
This creates a fresh variable instead of using the bound one.
</typo_different_vars>

<overloaded_meaning>
**Same name, different meanings:**
```
rel confusing {
    (a $x) -> (b $x)      # $x means one thing here
    |
    (c $x) -> (d $x)      # $x means something else here (that's fine - different span)
}
```
This is actually fine - each span has its own scope. But be aware when reading code.
</overloaded_meaning>
</anti_patterns>
