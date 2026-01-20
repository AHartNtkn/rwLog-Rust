<overview>
How variables and terms work in rwlog. Variables are logical variables that unify, not assignment variables.
</overview>

<variables>
## Variables

Variables in rwlog are **logical variables** - they represent unknown values that get determined through unification.

<naming>
**Naming:**
- Must start with `$`
- Followed by lowercase identifier
- Examples: `$x`, `$head`, `$tail`, `$result`
</naming>

<scoping>
**Scoping:**
- Variables are scoped to a **single rule**
- Same variable name in different rules = different variables
- Within a rule, same variable name = same value (unification)

```
rel example {
    (pair $x $y) -> (pair $y $x)   # $x and $y are local to this rule
    |
    (triple $x $y $z) -> $x        # Different $x, $y - new rule
}
```
</scoping>

<unification>
**Unification:**

When a variable appears multiple times in a rule, all occurrences must unify to the same value.

```
(cons $x $x) -> $x
```
This only matches cons cells where both elements are **identical**.

- `(cons a a)` matches, produces `a`
- `(cons a b)` does NOT match (a ≠ b)
</unification>
</variables>

<pattern_matching>
## Pattern Matching

The left side of a rule is a **pattern** that matches against input.

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

The right side of a rule **constructs** output using variables bound on the left.

<building_terms>
**Building terms:**
```
$x -> (wrapped $x)        # Wraps input in constructor
(pair $x $y) -> (pair $y $x)  # Rearranges components
$x -> (cons $x nil)       # Creates new structure
```
</building_terms>

<fresh_variables>
**Fresh variables on right side:**

If a variable appears ONLY on the right side, it's existentially quantified (fresh).

```
$x -> (pair $x $y)        # $y is fresh - can be anything
```

This is less common and creates non-determinism.
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
## Variables and Bidirectionality

Variables work the same forwards and backwards because unification is symmetric.

<forward>
**Forward (input on left):**
```
?- @(cons a b) ; [(cons $h $t) -> $h]
```
Result: `a`
- Pattern `(cons $h $t)` matches `(cons a b)`
- `$h` = `a`, `$t` = `b`
- Output: `$h` = `a`
</forward>

<backward>
**Backward (constrain output):**
```
?- [(cons $h $t) -> $h] ; @a
```
Result: `(cons a $t)` for any `$t`
- Output must equal `a`
- So `$h` = `a`
- Input must be `(cons a $t)` for some `$t`
- Generates all cons cells with `a` as head
</backward>
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
    (c $x) -> (d $x)      # $x means something else here (that's fine - different rule)
}
```
This is actually fine - each rule has its own scope. But be aware when reading code.
</overloaded_meaning>
</anti_patterns>
