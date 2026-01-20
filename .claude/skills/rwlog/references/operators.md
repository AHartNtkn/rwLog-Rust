<overview>
The three core operators in rwlog: composition (;), disjunction (|), and conjunction (&).
</overview>

<composition>
## Composition: `;` (Seq)

Chains relations sequentially. Output of first becomes input of second.

**Semantics:** `R ; S` means "apply R, then apply S to the result"

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
Different rules match different input shapes.
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

**Less common than `;` and `|`** - most programs use composition and disjunction primarily.
</when_to_use>
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
