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

A rewrite rule `lhs -> rhs` denotes a **span**:

```
[[lhs -> rhs]] inp out  <=>
    exists sigma.
        lhs[sigma] = inp  AND
        rhs[sigma] = out
```

Where `sigma` is a substitution mapping variables to terms.

<example name="Simple span">
Rule: `(cons $x $y) -> $x`

This rule relates:
- Input: any term matching `(cons $x $y)`
- Output: the value bound to `$x`

So `(cons a b)` relates to `a`, `(cons (s z) nil)` relates to `(s z)`, etc.
</example>

<example name="Bidirectional span">
The same rule `(cons $x $y) -> $x` run backwards:
- Output: `a`
- Find all inputs `(cons $x $y)` where `$x = a`
- Answer: `(cons a $y)` for any `$y`

This generates infinitely many inputs that produce output `a`.
</example>
</span_semantics>

<bidirectionality>
## Bidirectionality

Every rwlog relation is inherently bidirectional. The same definition can:
1. Transform inputs to outputs (forward)
2. Find inputs that produce given outputs (backward)
3. Generate all input/output pairs (enumerate)

<forward_mode>
**Forward mode:**
```
@input ; relation
```
Computes: what outputs does `input` produce through `relation`?
</forward_mode>

<backward_mode>
**Backward mode:**

To find inputs that produce a given output, constrain the output:
```
relation ; @output
```
This finds inputs to `relation` that produce `output`.

**Common mistake:** `@output ; relation` does NOT run backward - it passes `output` as input, which runs forward. This usually fails because `output` has the wrong shape for input.
</backward_mode>

<enumeration_mode>
**Enumeration mode:**
```
relation
```
With no constraint, generates all input/output pairs (may be infinite).
</enumeration_mode>
</bidirectionality>

<dual_operation>
## The Dual Operation

`dual(R)` swaps inputs and outputs:
```
dual(R) inp out  <=>  R out inp
```

<dual_of_primitives>
**Dual of primitives:**
- `dual(lhs -> rhs)` = `rhs -> lhs`
- `dual(@term)` = `@term`
- `dual(fail)` = `fail`
</dual_of_primitives>

<dual_of_operators>
**Dual of operators:**
- `dual(R ; S)` = `dual(S) ; dual(R)` (reverse order!)
- `dual(R | S)` = `dual(R) | dual(S)`
- `dual(R & S)` = `dual(R) & dual(S)`
</dual_of_operators>

<dual_example>
**Example:**
```
rel add { ... }

# Forward: compute sum
@(cons (s z) (s z)) ; add
> (s (s z))

# Backward: find addends
add ; @(s (s z))
> (cons z (s (s z)))  # 0 + 2
> (cons (s z) (s z))  # 1 + 1
> (cons (s (s z)) z)  # 2 + 0
```
</dual_example>
</dual_operation>

<internal_representation>
## Internal Representation (Advanced)

Internally, rwlog factors rules into three components:

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

`R ; S` means: for all intermediate values `mid`,
```
(R ; S) inp out  <=>  exists mid. R inp mid AND S mid out
```

<forward_composition>
**Forward execution:**
1. Run R on input, get intermediate
2. Run S on intermediate, get output
</forward_composition>

<backward_composition>
**Backward execution:**
1. Run dual(S) on output, get intermediate
2. Run dual(R) on intermediate, get input

Equivalently:
```
dual(R ; S) = dual(S) ; dual(R)
```
</backward_composition>
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
