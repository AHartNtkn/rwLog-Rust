# Workflow: Run Programs Bidirectionally

<required_reading>
**Read these reference files NOW:**
1. references/semantics.md - Tensor relations and duality
2. references/operators.md - How composition reverses
3. references/repl.md - REPL commands for querying
</required_reading>

<process>
## Step 1: Understand Bidirectionality

In rwlog, every relation can potentially run in both directions:

- **Forward:** Given input, compute output
- **Backward:** Given output, find inputs that produce it

This is automatic - no special syntax needed.

## Step 2: Forward Execution

Pass input to a relation:

```
?- @input_term ; relation_name
```

<example name="Addition forward">
```
?- @(cons (s (s z)) (s z)) ; add
> (s (s (s z)))
```
2 + 1 = 3
</example>

## Step 3: Backward Execution

Constrain the output and find inputs:

```
?- relation_name ; @output_term
```

<example name="Addition backward">
```
?- add ; @(s (s (s z)))
> (cons z (s (s (s z))))
```
What + what = 3? First answer: 0 + 3
</example>

## Step 4: Get Multiple Backward Answers

Most backward queries have multiple solutions. Use `next` or `more N`:

```
?- add ; @(s (s (s z)))
> (cons z (s (s (s z))))

next
> (cons (s z) (s (s z)))

next
> (cons (s (s z)) (s z))

next
> (cons (s (s (s z))) z)

next
> [no more answers]
```

All pairs that sum to 3: (0,3), (1,2), (2,1), (3,0).

## Step 5: Partial Constraints

You can constrain just part of the output:

```
# Find all inputs where result starts with (s ...)
?- add ; [(s $n) -> (s $n)]
```

Or use conjunction to add constraints:

```
# Find pairs summing to 3 where first element is at least 1
?- add ; @(s (s (s z))) & [(cons (s $x) $y) -> (cons (s $x) $y)]
```

## Step 6: Enumeration Mode

With no constraints, generate all input/output pairs:

```
?- add
> (cons z z) -> z

next
> (cons z (s z)) -> (s z)

next
> (cons (s z) z) -> (s z)

# ... infinite stream
```

Use this to explore what a relation computes.

## Step 7: Composition Direction

In `R ; S`:
- **Forward:** R first, then S
- **Backward:** Find inputs to R that, when passed through R then S, produce target

<example name="Composition backward">
```
rel double {
    z -> z
    |
    [(s $n) -> $n ; double ; $m -> (s (s $m))]
}

# Forward: double 2
?- @(s (s z)) ; double
> (s (s (s (s z))))

# Backward: what doubles to 4?
?- double ; @(s (s (s (s z))))
> (s (s z))
```
</example>

## Step 8: When Backward Doesn't Terminate

Some relations produce infinite backward results:

```
rel wrap {
    $x -> (wrapped $x)
}

# Forward: finite
?- @a ; wrap
> (wrapped a)

# Backward on (wrapped a): finite
?- wrap ; @(wrapped a)
> a

# But if we had a relation generating all terms...
rel any_term { ... }  # Generates infinite terms

?- any_term ; wrap    # Infinite stream
```

If backward hangs, the relation may be generating infinitely. Use `Ctrl+C` to interrupt.

## Step 9: Testing Both Directions

For every relation, test both directions:

```
# Forward test
?- @(cons (s z) (s z)) ; add
> (s (s z))
# Expected: 1 + 1 = 2 ✓

# Backward test
?- add ; @(s (s z))
> (cons z (s (s z)))
more 2
> (cons (s z) (s z))
> (cons (s (s z)) z)
# Expected: all pairs summing to 2 ✓

# Verify round-trip
?- @(cons (s z) (s z)) ; add ; add
# This finds: what pairs sum to a number that is the sum of (1,1)?
# i.e., what pairs sum to 2?
```

## Step 10: Leveraging Bidirectionality

**Generate test cases:**
```
?- add ; @(s (s (s (s (s z)))))
# All pairs summing to 5 - automatic test generation!
```

**Invert functions:**
```
# Encode: string -> encoded
# Decode: just run backward
?- encode ; @encoded_value
```

**Solve constraints:**
```
# Find X such that f(X) = target
?- f ; @target
```

**Program synthesis:**
```
# What program transforms A to B?
?- @A ; program ; @B
# (if program is defined relationally)
```

</process>

<direction_patterns>
## Direction Patterns

| Pattern | Meaning |
|---------|---------|
| `@input ; R` | Forward: compute R(input) |
| `R ; @output` | Backward: find R⁻¹(output) |
| `R` | Enumerate: all (input, output) pairs |
| `@a ; R ; @b` | Check: does R relate a to b? |
| `R ; S ; @target` | Backward through composition |
</direction_patterns>

<termination_notes>
## Termination Notes

Termination is symmetric - the same principles apply forward and backward.

**A query terminates if:**
- Recursive structure decreases toward base cases
- The constrained end (input or output) bounds the search
- The relation is deterministic or finitely nondeterministic

**A query may not terminate if:**
- The relation generates infinitely many results
- Neither input nor output is constrained
- Nondeterminism creates unbounded branching

**Safe pattern:** Constrain at least one end. Use `next` to explore infinite streams incrementally.
</termination_notes>

<success_criteria>
Successfully using bidirectionality:
- Can run relation forward for specific inputs
- Can run relation backward to find inputs for specific outputs
- Understands when backward is finite vs infinite
- Uses `next`/`more` to explore multiple solutions
- Tests both directions for correctness
- Leverages bidirectionality for testing/generation/inversion
</success_criteria>
