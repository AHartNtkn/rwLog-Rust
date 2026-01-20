# Workflow: Debug Program

<required_reading>
**Read these reference files NOW:**
1. references/anti-patterns.md - Common mistakes
2. references/operators.md - How composition works
3. references/variables-and-terms.md - Variable behavior
</required_reading>

<process>
## Step 1: Identify the Symptom

What's happening?

| Symptom | Likely Cause |
|---------|--------------|
| Hangs/infinite loop | Missing base case or no progress |
| Wrong result | Logic error, variable typo, wrong pattern |
| Fails (no result) | Pattern doesn't match, cases don't cover input |
| Multiple wrong results | Disjunction including wrong case |
| Backward doesn't work | Relation only designed for forward |

## Step 2: Simplify the Input

Find the **simplest input** that exhibits the bug:

```
# Original failing case
@(cons (s (s z)) (s (s (s z)))) ; relation

# Simplify systematically
@(cons z z) ; relation            # Works?
@(cons (s z) z) ; relation        # Works?
@(cons (s z) (s z)) ; relation    # Bug appears here?
```

The simplest failing case reveals the bug pattern.

## Step 3: Test Components Separately

Break the relation into parts and test each:

```
# If relation is: [step1 ; step2 ; step3]

# Test step1 alone
@input ; [step1]

# Test step1 ; step2
@input ; [step1 ; step2]

# Find which step fails
```

## Step 4: Check Pattern Matching

Verify patterns match what you expect:

```
# Does this pattern match?
@(cons a b) ; [(cons $x $y) -> matched]

# Expected: matched
# If fails: pattern is wrong
```

Common pattern issues:
- **Atom vs variable:** `x` (atom) vs `$x` (variable)
- **Wrong structure:** `(cons $x)` vs `(cons $x $y)`
- **Missing nesting:** `(cons $x $y)` vs `(cons (s $x) $y)`

## Step 5: Check Variable Bindings

Make sure variables are:
1. Bound on the left side
2. Used correctly on the right side
3. Not typos (check spelling!)

```
# Suspicious: $result bound but is it used?
(input $x $result) -> (output $x)

# Check for typos
(input $head $tail) -> (output $haed)  # typo: $haed vs $head
```

## Step 6: Check Recursion

For recursive relations, verify:

**Base case exists and is reachable:**
```
# Is there a base case?
@base_input ; relation
# Should return without recursing
```

**Progress toward base case:**
```
# Does the recursive call use smaller input?
[(cons (s $x) $y) -> (cons $x $y) ; relation ; ...]
#      ^^^^                ^^
#      Input has (s $x)    Recursive call has $x (smaller!)
```

**Correct post-processing:**
```
# After recursion, is result transformed correctly?
[... ; relation ; $z -> (s $z)]
#                 ^^^^^^^^^^^^ adds back what was peeled
```

## Step 7: Check Intermediate Types

In a composition, output of each step must match input of next:

```
[step1 ; step2 ; step3]
```

- Output of step1 must match input pattern of step2
- Output of step2 must match input pattern of step3

```
# Debug: what does step1 produce?
@input ; [step1]
> intermediate_value

# Does step2 accept that?
@intermediate_value ; [step2]
```

## Step 8: Check Disjunction Order

For `case1 | case2 | case3`:
- All cases should be mutually exclusive by pattern
- Or if overlapping, order determines priority

```
rel ambiguous {
    $x -> result1           # Matches everything!
    |
    (specific $x) -> result2  # Never reached for (specific ...)
}
```

## Step 9: Common Fixes

<fix name="Missing base case">
```
# Before: infinite loop
rel broken {
    [step ; broken]
}

# After: add base case
rel fixed {
    base_pattern -> result
    |
    [step ; fixed]
}
```
</fix>

<fix name="No progress">
```
# Before: infinite loop
rel broken {
    $x -> result
    |
    [$x -> $x ; broken]  # Same input!
}

# After: make progress
rel fixed {
    base -> result
    |
    [complex -> simpler ; fixed]  # Smaller input
}
```
</fix>

<fix name="Variable typo">
```
# Before: $haed is fresh (unbound), creates garbage
(cons $head $tail) -> (result $haed)

# After: use correct variable
(cons $head $tail) -> (result $head)
```
</fix>

<fix name="Pattern too specific">
```
# Before: doesn't match (cons z z)
[(cons (s $x) $y) -> ...]

# After: add base case for zero
[(cons z $y) -> $y]
|
[(cons (s $x) $y) -> ...]
```
</fix>

<fix name="Wrong intermediate type">
```
# Before: step1 produces X, step2 expects (pair X Y)
[step1 ; step2]

# After: transform to match
[step1 ; [$x -> (pair $x default)] ; step2]
```
</fix>

</process>

<debugging_checklist>
## Quick Debugging Checklist

- [ ] Simplified input to smallest failing case?
- [ ] Tested components separately?
- [ ] Pattern matches expected input?
- [ ] All variables spelled correctly?
- [ ] Base case exists and is reachable?
- [ ] Recursive case makes progress?
- [ ] Intermediate types align in composition?
- [ ] Tested both forward and backward?
</debugging_checklist>

<success_criteria>
Debugging complete when:
- Root cause identified
- Fix applied
- Original failing case now passes
- Other test cases still pass
- Forward direction works
- Backward direction works (if intended)
</success_criteria>
