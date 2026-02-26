<overview>
The three core operators in rwlog: composition (;), disjunction (|), and conjunction (&).
</overview>

<composition>
## Composition: `;` (Seq)

Chains relations through a shared middle term. The right side of each span in `R` is matched with the left side of each span in `S`.

**Semantics:** `(a, c) in R ; S` iff there exists `b` such that `(a, b) in R` and `(b, c) in S`

<example name="Two-step transformation">
```
@a ; [a -> b] ; [b -> c]
```
Result: `c`

1. Start with `a`
2. Transform to `b`
3. Transform to `c`
</example>

<example name="Recursive pattern">
```
[(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
```
This recursive case:
1. Decrements first element: `(cons (s $x) $y) -> (cons $x $y)`
2. Recurses: `add`
3. Increments result: `$z -> (s $z)`
</example>

<example name="Forward then constraint">
```
add ; @(s (s (s z)))
```
Find pairs that sum to 3.
</example>

<patterns>
**Common patterns:**

```
# Preprocess then apply
[normalize] ; [process]

# Apply then postprocess
[process] ; [format_output]

# Filter then transform
@constraint ; [transform]

# Transform then assert
[transform] ; @expected
```
</patterns>

<bidirectional_note>
**Bidirectionality:** When run backwards, composition reverses:
- Forward: `R ; S` means R then S
- Backward: finds inputs to R that produce inputs to S that produce the target
</bidirectional_note>
</composition>

<disjunction>
## Disjunction: `|` (Or)

Creates choice points. Multiple alternatives can be satisfied.

**Semantics:** `R | S` means "R or S (or both)"

<example name="Multiple alternatives">
```
rel color {
    x -> red
    |
    x -> green
    |
    x -> blue
}
```
Query `@x ; color` produces three answers: `red`, `green`, `blue`.
</example>

<example name="Base and recursive cases">
```
rel countdown {
    z -> z
    |
    [(s $x) -> $x ; countdown]
}
```
First alternative handles base case, second handles recursion.
</example>

<example name="Pattern matching">
```
rel process {
    (left $x) -> (result $x left)
    |
    (right $x) -> (result $x right)
}
```
Different spans match different shapes.
</example>

<search_behavior>
**Search behavior:**
- rwlog uses interleaved search (fair)
- Both branches are explored
- Results stream lazily
- Use `next` or `more N` in REPL to get additional results
</search_behavior>
</disjunction>

<conjunction>
## Conjunction: `&` (And)

Both constraints must be satisfied simultaneously.

**Semantics:** `R & S` means "both R and S must hold"

<example name="Multiple constraints">
```
[pattern1 -> pattern1] & [pattern2 -> pattern2]
```
Input must satisfy both patterns.
</example>

<example name="Intersection">
```
rel even_and_small {
    [$x -> $x ; is_even] & [$x -> $x ; less_than_10]
}
```
Must be both even AND less than 10.
</example>

<when_to_use>
**When to use:**
- Enforcing multiple constraints on same value
- Intersection of two relations
- Checking properties without transforming
- Computing multiple values in parallel and combining them
</when_to_use>

<parallel_computation>
**Parallel Computation with Conjunction**

When you need results from two independent computations, use `&` rather than sequential composition. This is the standard approach for parallel work.

<why_conjunction>
**Why use `&` for parallel computation:**

With sequential composition, if the first step runs forever, you never reach the second:
```
# BAD: if process1 is infinite and process2 would fail, this never fails
[$x -> $x ; process1 ; ... ; process2 ; ...]
```

With conjunction, both branches constrain the same span. If either fails, the whole thing fails:
```
# GOOD: if either branch fails, fails immediately
[... ; process1 ; ...] & [... ; process2 ; ...]
```
</why_conjunction>

<combining_results>
**Combining results via matching:**

Variables are scoped to a single pattern span. Use fresh variables as "holes" that get filled by the other branch. Because scoping is per-span and symmetric, you can reuse the same variable names on either side across branches — same names in different spans are always independent.

```
[
    [$x -> $x ; process1 ; $r -> (result $r $s)]
    &
    [$x -> $x ; process2 ; $r -> (result $r $s)]
]
```

The `$r` and `$s` in the two branches are **different variables** (different spans). Left produces `(result R $s)` with fresh `$s`; right produces `(result $r S)` with fresh `$r`. Meet resolves `$r = R` and `$s = S`, giving `(result R S)`.

The fresh variables act as placeholders that get constrained to actual values through matching at the meet.
</combining_results>

<example name="Building a pair from parallel results">
```
[
    [$x -> $x ; left_computation ; $l -> (pair $l $r)]
    &
    [$x -> $x ; right_computation ; $r -> (pair $l $r)]
]
```

- Left produces `(pair L $r)` with fresh `$r` (the `$r` in the left branch)
- Right produces `(pair $l R)` with fresh `$l` (the `$l` in the right branch)
- Meet: `$l` = L, `$r` = R, result is `(pair L R)`

The same variable names `$l` and `$r` appear in both branches — this is fine and idiomatic. The scopes never overlap.
</example>

<contrast_with_threading>
**Why threading does not work:**

Variables are scoped to individual pattern spans. There is no mechanism to carry a variable from one span into a later span via pairing or any other technique — each span's variables are completely independent. Conjunction (`&`) is the correct and only way to combine values from separate computations.
</contrast_with_threading>
</parallel_computation>
</conjunction>

<precedence_examples>
## Precedence in Practice

<example name="Default parsing">
```
a | b ; c & d
```
Parses as: `a | (b ; (c & d))`

Meaning: "a OR (b then (c AND d))"
</example>

<example name="Override with brackets">
```
[a | b] ; c
```
Meaning: "(a OR b) then c"
</example>

<example name="Common recursive pattern">
```
base_case | [step ; recurse]
```
Parses naturally as: `base_case | (step ; recurse)`
</example>

<example name="Chained composition">
```
a ; b ; c ; d
```
Left-associative: `((a ; b) ; c) ; d`
</example>
</precedence_examples>

<decision_tree>
## Choosing the Right Operator

**Use `;` (composition) when:**
- Chaining transformations
- Building pipelines
- Output of one feeds into next

**Use `|` (disjunction) when:**
- Multiple valid transformations exist
- Pattern matching different input shapes
- Base case vs recursive case

**Use `&` (conjunction) when:**
- Multiple constraints must hold
- Intersecting relations
- Checking properties
</decision_tree>
