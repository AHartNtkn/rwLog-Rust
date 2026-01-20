# Workflow: Build New Relation

<required_reading>
**Read these reference files NOW before writing a relation:**
1. references/syntax.md - Complete syntax reference
2. references/recursion.md - Recursion patterns
3. references/anti-patterns.md - Common mistakes to avoid
</required_reading>

<process>
## Step 1: Understand the Problem

Ask yourself:
- **Input:** What term structure goes in?
- **Output:** What term structure comes out?
- **Relation:** What is the mathematical relationship?
- **Bidirectional?** Should it work backwards too?

<example>
**Problem:** Add two Peano numbers
- Input: `(cons X Y)` where X and Y are Peano numbers
- Output: Peano number representing X + Y
- Relation: Peano addition
- Bidirectional: Yes - find addends for a given sum
</example>

## Step 2: Identify Cases

Break down into:
1. **Base case(s):** Simplest inputs with direct answers
2. **Recursive case(s):** How to reduce complex inputs to simpler ones

<example>
**Peano addition:**
- Base: `0 + Y = Y` — when first is zero, return second
- Recursive: `(1+X) + Y = 1 + (X + Y)` — peel off one, recurse, add back
</example>

## Step 3: Write Base Case First

Start with the simplest case that terminates.

```
rel name {
    base_pattern -> result
}
```

<example>
```
rel add {
    (cons z $y) -> $y
}
```
</example>

**Test it:**
```
?- @(cons z (s z)) ; add
> (s z)
```

## Step 4: Add Recursive Case

Add the recursive case with `|`:

```
rel name {
    base_pattern -> result
    |
    [progress_step ; name ; post_process]
}
```

The recursive case must:
1. **Progress:** Transform input to something "smaller"
2. **Recurse:** Call the relation by name
3. **Post-process:** Transform the recursive result

<example>
```
rel add {
    (cons z $y) -> $y
    |
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
```

Breaking down the recursive case:
- `(cons (s $x) $y) -> (cons $x $y)` — peel off one `s` from first
- `add` — recurse on smaller problem
- `$z -> (s $z)` — wrap result in `s`
</example>

## Step 5: Test Forward Direction

Test with increasingly complex inputs:

```
# Simplest case
?- @(cons z z) ; add
> z

# One step
?- @(cons (s z) z) ; add
> (s z)

# Two steps
?- @(cons (s (s z)) (s z)) ; add
> (s (s (s z)))
```

## Step 6: Test Backward Direction

Test finding inputs that produce given outputs:

```
# What sums to 2?
?- add ; @(s (s z))
> (cons z (s (s z)))

more 3
> (cons (s z) (s z))
> (cons (s (s z)) z)
> [no more answers]
```

## Step 7: Test Edge Cases

- Empty/nil inputs
- Single-element inputs
- Maximum expected size
- Invalid inputs (should fail gracefully)

## Step 8: Refine if Needed

If tests fail:
1. Check pattern matching
2. Check variable names (typos?)
3. Check recursion makes progress
4. Check base case is reachable
5. Check intermediate types align

</process>

<template>
## Relation Template

```
rel name {
    # Base case: simplest input, direct result
    simple_pattern -> simple_result
    |
    # Recursive case: progress, recurse, post-process
    [complex_pattern -> simpler_input ; name ; intermediate -> final_result]
}
```

For multiple base cases:
```
rel name {
    base1_pattern -> result1
    |
    base2_pattern -> result2
    |
    [recursive_pattern -> smaller ; name ; result -> wrapped]
}
```
</template>

<anti_patterns>
**Avoid:**
- No base case (infinite recursion)
- No progress in recursive case
- Variable typos creating fresh variables
- Forgetting to test backward direction
- Cases that don't cover all valid inputs
</anti_patterns>

<success_criteria>
A well-written relation:
- Has clear base case(s) that terminate
- Has recursive case(s) that make progress
- Works in forward direction for all valid inputs
- Works in backward direction (if intended)
- Handles edge cases gracefully
- Has been tested with multiple inputs
</success_criteria>
