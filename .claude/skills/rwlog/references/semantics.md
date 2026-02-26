<overview>
The semantic foundation of rwlog: tensor relations and bidirectionality. Understanding these concepts helps write correct programs and debug unexpected behavior.
</overview>

<tensor_relations>
## Tensor Relations

The semantic domain of rwlog is **tensor relations**: relations between lists of terms.

```
TRel = [Term] -> [Term] -> Prop
```

A relation R holds between input list `inp` and output list `out`:
```
R inp out  <=>  (inp, out) is in the relation R
```

<key_operations>
**Key operations:**

| Operation | Notation | Meaning |
|-----------|----------|---------|
| Empty | `fail` | The empty relation (no pairs) |
| Union | `R \| S` | Disjunction (R or S) |
| Intersection | `R & S` | Conjunction (R and S) |
| Composition | `R ; S` | Sequential (R then S) |
| Dual | `dual(R)` | Converse (swap inputs/outputs) |
</key_operations>
</tensor_relations>

<span_semantics>
## Span Semantics

A pattern span `lhs -> rhs` denotes a **span relation**:

```
[[lhs -> rhs]] inp out  <=>
    exists sigma.
        lhs[sigma] = inp  AND
        rhs[sigma] = out
```

Where `sigma` is a substitution mapping variables to terms.

<example name="Simple span">
Span: `(cons $x $y) -> $x`

This span relates:
- Left side: any term matching `(cons $x $y)`
- Right side: the value bound to `$x`

So `(cons a b)` relates to `a`, `(cons (s z) nil)` relates to `(s z)`, etc.
</example>

<example name="Bidirectional span">
The same span `(cons $x $y) -> $x` run backwards:
- Output: `a`
- Find all inputs `(cons $x $y)` where `$x = a`
- Answer: `(cons a $y)` for any `$y`

This generates infinitely many inputs that produce output `a`.
</example>
</span_semantics>

<results_are_spans>
## Results Are Spans

A rwlog computation produces a (possibly infinite) stream of **pattern spans** — pairs of terms `lhs -> rhs`. Both sides are always returned together. The language is symmetric: there is no dedicated "input" side or "output" side.

`@term` is the identity relation at `term`: the single span `term -> term`. Composing with `@term` constrains the matching side of all resulting spans.

<left_constrained>
**Left-constrained (colloquially "forward"):**
```
@term ; relation
```
Returns all spans in `relation` whose left side is `term`.
</left_constrained>

<right_constrained>
**Right-constrained (colloquially "backward"):**
```
relation ; @term
```
Returns all spans in `relation` whose right side is `term`.

Note: `@term ; relation` and `relation ; @term` constrain different sides and are generally different queries.
</right_constrained>

<unconstrained>
**Unconstrained:**
```
relation
```
Returns all spans (may be infinite). Use `next` or `more N` in the REPL to stream results.
</unconstrained>
</results_are_spans>

<dual_operation>
## The Dual Operation

The **dual** (or converse) of a relation swaps the two sides of every span:
```
dual(R) a b  <=>  R b a
```

<dual_laws>
**Algebraic laws:**
- `dual(lhs -> rhs)` = `rhs -> lhs`
- `dual(@term)` = `@term`
- `dual(fail)` = `fail`
- `dual(R ; S)` = `dual(S) ; dual(R)` (reverse order!)
- `dual(R | S)` = `dual(R) | dual(S)`
- `dual(R & S)` = `dual(R) & dual(S)`
</dual_laws>

<dual_not_syntax>
**Important:** `dual()` is a semantic concept, not language syntax. There is no `dual` keyword you can write in rwlog. To use a dual relation, either:

1. **Hand-calculate** using the algebraic laws above and write the result as a new relation
2. **Construct compositionally** using the wrap-intersect-project pattern (see `core-patterns.md`)

The dual function exists as an internal API used in tests, but is not exposed in the language surface.
</dual_not_syntax>

<dual_example>
**Example:**
```
rel add { ... }

# Left-constrained: spans with left side (cons (s z) (s z))
@(cons (s z) (s z)) ; add
> (cons (s z) (s z)) -> (s (s z))

# Right-constrained: spans with right side (s (s z))
add ; @(s (s z))
> (cons z (s (s z))) -> (s (s z))    # 0 + 2
> (cons (s z) (s z)) -> (s (s z))    # 1 + 1
> (cons (s (s z)) z) -> (s (s z))    # 2 + 0
```
</dual_example>
</dual_operation>

<internal_representation>
## Internal Representation (Advanced)

Internally, rwlog factors pattern spans into three components:

```
lhs -> rhs  ~=  RwL [patterns] ; DropFresh ; RwR [patterns]
```

<rwl>
**RwL (Left Tensor):** Decomposes input by pattern matching
- Input: terms to match
- Output: extracted variable values

```
RwL [(cons $0 $1)]
```
Matches cons cells, extracts head and tail as outputs.
</rwl>

<rwr>
**RwR (Right Tensor):** Constructs output from variables
- Input: variable values
- Output: constructed terms

```
RwR [(cons $0 $1)]
```
Takes two values, constructs a cons cell.
</rwr>

<dropfresh>
**DropFresh:** Routes variables from LHS to RHS
- Specifies which LHS variables flow to which RHS positions
- Handles fresh variables (on RHS only)
- Handles dropped variables (on LHS only)
</dropfresh>

<duality_of_rwl_rwr>
**Key insight:** RwL and RwR are duals:
```
dual(RwL patterns) = RwR patterns
dual(RwR patterns) = RwL patterns
```

This is what makes bidirectionality work mechanically.
</duality_of_rwl_rwr>
</internal_representation>

<composition_semantics>
## Composition Semantics

`R ; S` relates two terms through a shared middle term:
```
(R ; S) a c  <=>  exists b. R a b AND S b c
```

The right side of each span in R is matched with the left side of each span in S. The resulting spans pair the left side of R with the right side of S.

Duality reverses composition order:
```
dual(R ; S) = dual(S) ; dual(R)
```
</composition_semantics>

<search_semantics>
## Search Semantics

Disjunction `R | S` creates search branches.

<interleaving>
**Interleaving search:**
rwlog uses fair interleaving - it alternates between branches to ensure all solutions are eventually found, even with infinite branches.

```
R | S
```
Explores R and S in an interleaved fashion:
- R step 1
- S step 1
- R step 2
- S step 2
- ...
</interleaving>

<lazy_evaluation>
**Lazy evaluation:**
Solutions are generated on demand. Use `next` or `more N` to get additional solutions without computing all of them upfront.
</lazy_evaluation>
</search_semantics>

<termination_semantics>
## Termination

Bidirectionality means termination behaviors are **symmetric** - any behavior possible in one direction is possible in the other.

<forward_termination>
**Forward termination:**
A query `@input ; relation` terminates if:
- All recursive paths eventually reach base cases
- The recursion makes progress (e.g., list gets shorter, number decreases)
- The relation is deterministic (or finitely nondeterministic) for that input

A nondeterministic relation can generate infinitely many outputs for a single input.
</forward_termination>

<backward_termination>
**Backward termination:**
Symmetrically, `relation ; @output` terminates if:
- All recursive paths eventually reach base cases
- The recursion makes progress
- Finitely many inputs map to that output

For `add`, backward queries on finite Peano numbers DO terminate:
- `add ; @(s (s z))` finds exactly 3 pairs: (0+2), (1+1), (2+0)

Non-termination happens with:
- Relations that generate infinitely many inputs for a given output
- Nondeterministic relations (symmetric to forward case)
- Unconstrained recursive generation (like `nat` generating all naturals)
</backward_termination>

<productive_non_termination>
**Productive non-termination:**
Some queries "don't terminate" but productively generate an infinite stream:
```
nat
```
Generates `z`, `(s z)`, `(s (s z))`, ... forever.

This is useful! Use `next` or `more N` to get as many as needed.
</productive_non_termination>
</termination_semantics>
