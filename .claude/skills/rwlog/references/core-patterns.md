<overview>
Core programming patterns in rwlog. These patterns are the intended way to use the system — constructing relations compositionally, deriving new relations from existing ones, and using backward execution for synthesis. The simpler examples in other reference files (arithmetic, list processing) are pedagogical warmups; the patterns here represent what rwlog was designed for.
</overview>

<constructing_duals>
## Constructing the Dual of a Relation

`dual(R)` is a semantic concept meaning "swap inputs and outputs." There is no `dual` keyword in the language. To construct the dual of a relation, you have two options:

<hand_calculation>
### Option 1: Hand-Calculate Using Algebraic Laws

Apply the dual laws to derive the reversed relation:

- `dual(lhs -> rhs)` = `rhs -> lhs`
- `dual(R ; S)` = `dual(S) ; dual(R)` (reverse order)
- `dual(R | S)` = `dual(R) | dual(S)`
- `dual(R & S)` = `dual(R) & dual(S)`

For simple relations, this is straightforward. For example, `dual((cons $x $y) -> $x)` is just `$x -> (cons $x $y)`.

For recursive relations, apply the laws structurally. The `dual` function exists as an internal API and is used in tests (e.g., the flip synth dual test), but is not exposed in the language surface syntax.
</hand_calculation>

<compositional_construction>
### Option 2: Construct Compositionally

This technique constructs the dual generically for any relation R without manually deriving it.

**Step 1: Lift R into a pair structure**

```
(pair $a $b) -> $a ; R ; $b -> (pair $a $b)
```

This creates a relation where `$b` is free in the input `(pair $a $b) -> $a`, and `$a` is free in the output `$b -> (pair $a $b)`. The result relates pairs where only the A-to-B direction is constrained by R:

```
{((pair a1 b1), (pair a2 b2)) | a1 R b2}
```

**Step 2: Intersect with identity to force input = output**

```
[(pair $a $b) -> $a ; R ; $b -> (pair $a $b)] & $p -> $p
```

The identity intersection `& $p -> $p` forces the input and output pairs to be equal, giving:

```
{((pair a b), (pair a b)) | a R b}
```

**Step 3: Project to extract the reversed direction**

Pre-compose and post-compose to select which component is input and which is output:

```
$b -> (pair $a $b)
  ; [[(pair $a $b) -> $a ; R ; $b -> (pair $a $b)] & $p -> $p]
  ; (pair $a $b) -> $a
```

This takes B as input and produces A as output — the dual of R.
</compositional_construction>
</constructing_duals>

<deriving_relations>
## Deriving New Relations from Existing Ones

The compositional dual construction lets you build new relations from existing ones without reimplementing logic.

<subtraction_from_addition>
### Example: Subtraction from Addition

Given `add` which relates `(cons A B)` to `A + B`, define subtraction (given C and A, find B such that A + B = C):

```
rel sub {
  (pair $c $a) -> (pair (cons $a $b) $c)
     ; [[(pair $a $b) -> $a ; add ; $b -> (pair $a $b)] & $p -> $p]
     ; (pair (cons $a $b) $c) -> $b
}
```

How it works:
1. Input `(pair C A)` is restructured to `(pair (cons A $b) C)` where `$b` is fresh
2. The intersection constrains `(cons A $b)` to pairs where `add` maps `(cons A $b)` to some value, and that value must equal `C` (forced by identity intersection)
3. The projection extracts `$b`, which is the answer

```
@(pair (s (s (s (s (s z))))) (s (s (s z)))) ; sub
> (pair (s (s (s (s (s z))))) (s (s (s z)))) -> (s (s z))
```

5 - 3 = 2.
</subtraction_from_addition>
</deriving_relations>

<identity_intersection>
## The Identity Intersection Pattern: `R & $p -> $p`

Intersecting a relation R with the identity relation `$p -> $p` keeps only the pairs where R maps a value to itself — the fixed points of R.

**This pattern is fundamental.** It appears in:
- Dual construction (forcing input = output of a lifted relation)
- Self-application queries (finding values unchanged by an evaluator)
- Constraining without transforming

<example name="Fixed points of SK evaluation">
Find all SK combinator terms that evaluate to themselves (i.e., are already in normal form and self-apply cleanly):

```
[$p {(no_c $p)} -> (p (a $p $p) nil) ; skEval] & $p -> $p
```

Results include terms like `(a (a s k) s)`, `(a (a s k) k)`, etc.
</example>
</identity_intersection>

<partial_queries>
## Partial Queries with Free Variables in @

The `@` operator can take terms with free variables. This constrains some positions while leaving others open, computing relations with partially-specified inputs or outputs.

<example name="Compute subtraction inline">
Find `$x` such that `$x + 3 = 5` without defining a subtraction relation:

```
@(cons $x (s (s (s z)))) ; add ; @(s (s (s (s (s z)))))
```

Result:
```
> (cons (s (s z)) (s (s (s z)))) -> (s (s (s (s (s z)))))
```

`$x = (s (s z))` — that is, 2.
</example>

<example name="Enumerate with one argument fixed">
Find all sums `3 + $b`:

```
@(cons (s (s (s z))) $b) ; add
```

This produces `(s (s (s $b)))` for each `$b`, generating the infinite family of results.
</example>
</partial_queries>

<non_overlapping_patterns>
## Non-Overlapping Patterns for Deterministic Relations

rwlog does NOT have "first match wins" semantics. All branches of a disjunction `|` are explored. If multiple branches match the same input, the relation produces multiple answers.

This is a feature — non-determinism is essential for relational programming. But when you want a deterministic function (exactly one answer per input), patterns must not overlap.

<example name="Overlapping patterns cause multiple results">
```
# Both cases match (s z)
rel broken {
    $x -> result_a
    |
    (s $n) -> result_b
}
```

`@(s z) ; broken` produces BOTH `result_a` AND `result_b`.
</example>

**Distinguish cases by constructor shape, not catch-all variables.** This is the same situation as in the Curry functional-logic language. For a deterministic evaluator, every input must match exactly one branch.

<example name="Non-overlapping patterns in an evaluator">
```
rel skEval {
    (p (c $i) $spine) -> (p (c $i) $spine) ; skFold
  | (p k nil) -> k
  | (p k (cons $x nil)) -> ...
  | (p k (cons $x (cons $y $spine))) -> ...
  | (p s nil) -> s
  | (p s (cons $x nil)) -> ...
  | (p s (cons $x (cons $y nil))) -> ...
  | (p s (cons $f (cons $g (cons $x $spine)))) -> ...
  | (p (a $x $y) $spine) -> ...
}
```

Each branch matches a distinct combination of head constructor and spine length. No input matches more than one branch.
</example>
</non_overlapping_patterns>

<synthesis>
## Program Synthesis via Backward Execution

Defining an evaluator and running it backward is the core use case for rwlog. This is not a trick or workaround — it is what the system was designed for.

<uninterpreted_constants>
### Uninterpreted Constants as Specification Holes

Use uninterpreted constant symbols like `(c z)`, `(c (s z))` as distinct constants that halt computation. A constraint rejects synthesized programs that contain these constants:

```
theory sk_constraints {
    constraint no_c/1

    (no_c k) <=> .
    (no_c s) <=> .
    (no_c (a $x $y)) <=> (no_c $x), (no_c $y).
    (no_c (c $n)) <=> fail.
}
```

`(no_c $x)` succeeds for any term built from `k`, `s`, and `a`, and fails if the term contains any `(c N)`.
</uninterpreted_constants>

<evaluation_synthesis>
### Synthesis by Backward Evaluation

Given an evaluator `skEval`, run it forward to verify a known program:

```
@(p (a (a (a s k) k) (c z)) nil) ; skEval
> (p (a (a (a s k) k) (c z)) nil) -> (c z)
```

Confirms that `S K K` is the identity combinator.

Run backward to synthesize a program satisfying a behavioral specification. To find a duplication combinator D where D x y = x y y:

```
$p { (no_c $p) } -> (p (a (a $p (c z)) (c (s z))) nil)
  ; skEval
  ; @(a (a (c z) (c (s z))) (c (s z)))
```

- The input is an unknown program `$p` constrained to not contain `c`
- It's applied to two uninterpreted constants `(c z)` and `(c (s z))`
- The output must equal `(a (a (c z) (c (s z))) (c (s z)))` — i.e., `(c z) applied to (c (s z)) applied to (c (s z))`
- This specifies: `D x y = x y y`

First answer: `(a (a s s) (a s k))` — the standard duplication combinator.

Asking for more answers enumerates increasingly complex programs that also satisfy the specification (many are equivalent modulo dead code or eta-expansion).
</evaluation_synthesis>

<type_directed_synthesis>
### Type-Directed Synthesis

Define a type inference relation:

```
rel infer {
    k -> (fun $a (fun $b $a))
  | s -> (fun (fun $a (fun $b $c)) (fun (fun $a $b) (fun $a $c)))
  | [
        [(a $f $x) -> $x ; infer ; $a -> (fun $a $b)]
        &
        [(a $f $x) -> $f ; infer]
        ; (fun $a $b) -> $b
    ]
}
```

Forward: infer the type of a known program.
```
@(a (a s k) k) ; infer
> (a (a s k) k) -> (fun $0 $0)
```

Type: `a -> a` (identity).

Backward: synthesize all programs of a given type. Use uninterpreted constants for type variables to keep the type fully general:

```
infer ; @(fun (fun a (fun a b)) (fun a b))
> (a (a s s) (a s k)) -> (fun (fun a (fun a b)) (fun a b))
```

First answer is the same duplication combinator. Further answers enumerate all typeable programs of that type.
</type_directed_synthesis>

<note_on_conjunction_in_inference>
### Conjunction for Parallel Subexpression Checking

The `infer` relation uses conjunction to check function and argument types in parallel:

```
[(a $f $x) -> $x ; infer ; $a -> (fun $a $b)]
&
[(a $f $x) -> $f ; infer]
; (fun $a $b) -> $b
```

Left branch: infer the argument type and wrap it as `(fun argType $b)` with `$b` fresh.
Right branch: infer the function type.
Meet: the function type `(fun A (fun B C))` must unify with `(fun argType $b)`, determining `$b` as the return type.

This is not just a convenience — it's essential. If function type inference diverges, the conjunction still allows the argument branch to fail early, pruning the search.
</note_on_conjunction_in_inference>
</synthesis>

<conjunction_parallel_eval>
## Conjunction for Parallel Subexpression Evaluation

When evaluating compound expressions with independent subparts, use conjunction rather than sequential composition:

```
[(p $x $y) -> (p (p $x nil) (p $y nil)) ; [
   [(p $x $y) -> $x ; skEval ; $x -> (p $x $y)] &
   [(p $x $y) -> $y ; skEval ; $y -> (p $x $y)]
] ; (p $x $y) -> (a (a s $x) $y)]
```

Both `$x` and `$y` are evaluated independently. If either diverges but the other would fail, the conjunction fails early instead of hanging forever on the first branch. With sequential composition, the second evaluation would never start if the first diverges.
</conjunction_parallel_eval>
