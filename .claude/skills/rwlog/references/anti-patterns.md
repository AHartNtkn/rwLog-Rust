<overview>
Common mistakes and anti-patterns when programming in rwlog, and how to avoid them.
</overview>

<syntax_mistakes>
## Syntax Mistakes

<missing_dollar>
**Missing $ on variables:**
```
# WRONG
(cons x y) -> x

# RIGHT
(cons $x $y) -> $x
```
Without `$`, `x` is an atom (constant), not a variable.
</missing_dollar>

<wrong_grouping>
**Wrong grouping in sequences:**
```
# WRONG - ambiguous
a -> b ; c -> d ; recursive_call

# RIGHT - explicit grouping
[a -> b ; c -> d ; recursive_call]
```
Use brackets to make sequence structure clear.
</wrong_grouping>

<mismatched_parens>
**Mismatched parentheses:**
```
# WRONG
(cons $x (cons $y $z) -> ...

# RIGHT
(cons $x (cons $y $z)) -> ...
```
Every `(` needs a matching `)`.
</mismatched_parens>

<arrow_direction>
**Wrong arrow:**
```
# WRONG
pattern <- result

# RIGHT
pattern -> result
```
rwlog uses `->`, not `<-`.
</arrow_direction>
</syntax_mistakes>

<logic_mistakes>
## Logic Mistakes

<no_base_case>
**Missing base case:**
```
# WRONG - infinite loop
rel countdown {
    [(s $n) -> $n ; countdown]
}

# RIGHT - has termination
rel countdown {
    z -> z
    |
    [(s $n) -> $n ; countdown]
}
```
Every recursive relation needs a base case.
</no_base_case>

<no_progress>
**No progress toward termination:**
```
# WRONG - recursive call with same input
rel stuck {
    $x -> $x
    |
    [$x -> $x ; stuck]
}

# RIGHT - input gets smaller
rel process {
    nil -> done
    |
    [(cons $h $t) -> $t ; process]
}
```
Each recursive call must make progress toward the base case.
</no_progress>

<variable_typo>
**Variable typo creating fresh variable:**
```
# WRONG - $haed is fresh (typo for $head)
(cons $head $tail) -> (result $haed $tail)

# RIGHT
(cons $head $tail) -> (result $head $tail)
```
A typo creates a fresh variable instead of using the bound one. The result will be non-deterministic.
</variable_typo>

<unused_binding>
**Binding variables but not using them:**
```
# Suspicious - why bind $tail if never used?
(cons $head $tail) -> $head

# If intentional, that's fine - just be aware
# The rule ignores the tail
```
This isn't always wrong, but consider whether you meant to use all bound variables.
</unused_binding>

<wrong_case_distinction>
**Cases that don't cover all inputs:**
```
# WRONG - what if input is nil?
rel process {
    (cons $h $t) -> ...
}

# RIGHT - handle all cases
rel process {
    nil -> nil
    |
    (cons $h $t) -> ...
}
```
If an input doesn't match any case, the relation fails for that input.
</wrong_case_distinction>
</logic_mistakes>

<composition_mistakes>
## Composition Mistakes

<wrong_intermediate>
**Wrong intermediate type:**
```
# WRONG - step1 produces (pair ...), step2 expects (triple ...)
[step1 ; step2]

# The types must align!
# Output of step1 must match input pattern of step2
```
Make sure the output shape of each step matches the input pattern of the next.
</wrong_intermediate>

<forgetting_to_thread>
**Forgetting to thread values through:**
```
# WRONG - loses $y
[(pair $x $y) -> $x ; process ; $z -> (result $z)]

# RIGHT - thread $y through
[(pair $x $y) -> (pair $x $y) ;
 [(pair $x $y) -> $x ; process ; $z -> (pair $z $y)] ;
 [(pair $z $y) -> (result $z $y)]]
```
If you need a value later in the pipeline, you must carry it through intermediate steps.
</forgetting_to_thread>

<order_confusion>
**Confusion about composition order:**
```
# This means: R then S
R ; S

# NOT: S then R
```
Composition is left-to-right. `R ; S` applies R first, then S to the result.
</order_confusion>
</composition_mistakes>

<bidirectional_mistakes>
## Bidirectionality Mistakes

<assuming_one_direction>
**Assuming only forward execution:**
```
# This relation looks fine forward...
rel process {
    (input $x) -> (output $x)
}

# But backward, it expects (output $x) as input
# Make sure that makes sense for your use case
```
Always consider whether your relation should work in both directions.
</assuming_one_direction>

<infinite_backward>
**Infinite results backwards:**
```
rel wrap {
    $x -> (wrapped $x)
}

# Forward: finite (one result per input)
# Backward on (wrapped a): finds $x = a, returns a
# Backward on bare 'a': fails (doesn't match (wrapped $x))
```
Backward execution may have different termination properties.
</infinite_backward>

<testing_only_forward>
**Testing only forward direction:**
```
# Tested forward - works!
?- @(cons (s z) (s z)) ; add
> (s (s z))

# But did you test backward?
?- add ; @(s (s z))
> (cons z (s (s z)))
> (cons (s z) (s z))
> (cons (s (s z)) z)

# And edge cases?
?- @(cons z z) ; add
> z
```
Always test both directions and edge cases.
</testing_only_forward>
</bidirectional_mistakes>

<performance_mistakes>
## Performance Mistakes

<exponential_branching>
**Exponential branching:**
```
# Each recursive call creates multiple branches
rel bad {
    base -> result
    |
    [step ; bad ; bad]  # Two recursive calls!
}
```
This creates exponentially many branches. Usually you want linear recursion.
</exponential_branching>

<redundant_computation>
**Redundant computation:**
```
# Computing the same thing twice
[(pair $x $x) -> $x ; expensive ; $r1 ->
 (pair $x $x) -> $x ; expensive ; $r2 ->  # Same computation!
 (result $r1 $r2)]

# Better: compute once, duplicate result
[(pair $x $x) -> $x ; expensive ; $r -> (result $r $r)]
```
</redundant_computation>

<naive_reverse>
**Naive algorithms (O(n²) when O(n) is possible):**
```
# Naive reverse - O(n²)
rel reverse_naive {
    nil -> nil
    |
    [(cons $h $t) -> ... ; append]  # append is O(n)
}

# Better: use accumulator - O(n)
rel reverse_acc {
    (pair nil $acc) -> $acc
    |
    [(pair (cons $h $t) $acc) -> (pair $t (cons $h $acc)) ; reverse_acc]
}
```
</naive_reverse>
</performance_mistakes>

<debugging_tips>
## Debugging Tips

<isolate_the_problem>
**Isolate the problem:**
```
# Test components separately
?- @input ; [step1]
?- @intermediate ; [step2]
?- @input ; [step1 ; step2]
```
Find which step is failing.
</isolate_the_problem>

<check_pattern_match>
**Check pattern matching:**
```
# Does the pattern even match?
?- @(cons a b) ; [(cons $x $y) -> matched]

# If it returns 'matched', pattern works
# If it fails, pattern doesn't match
```
</check_pattern_match>

<trace_variables>
**Trace variable bindings:**
```
# Add identity checkpoints
?- @input ; [step1] ; [$x -> $x] ; [step2]
#                     ^^^^^^^^^^^ see intermediate

# Or output the intermediate explicitly
?- @input ; [step1]
```
</trace_variables>

<simplify>
**Simplify the failing case:**
```
# If complex input fails, try simpler input
?- @(cons z z) ; relation           # Simplest non-trivial
?- @(cons (s z) z) ; relation       # One step more complex
?- @(cons (s (s z)) (s z)) ; relation  # Original failing case
```
Find the simplest input that exhibits the bug.
</simplify>
</debugging_tips>
