<overview>
Writing recursive relations in rwlog. Recursion is the primary mechanism for processing recursive data structures and performing iteration.
</overview>

<basic_structure>
## Basic Recursive Structure

Every recursive relation needs:
1. **Base case(s)** - terminating conditions
2. **Recursive case(s)** - make progress toward base case

```
rel recurse {
    # Base case: terminates
    base_pattern -> result
    |
    # Recursive case: makes progress, calls self
    [progress_step ; recurse ; post_process]
}
```
</basic_structure>

<peano_arithmetic>
## Example: Peano Arithmetic

Peano numbers: `z` = 0, `(s z)` = 1, `(s (s z))` = 2, etc.

<addition>
**Addition:**
```
rel add {
    # Base: 0 + y = y
    (cons z $y) -> $y
    |
    # Recursive: (1+x) + y = 1 + (x + y)
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
```

Trace of `(cons (s (s z)) (s z))` (2 + 1):
1. Match recursive case: `$x` = `(s z)`, `$y` = `(s z)`
2. Produce `(cons (s z) (s z))` (1 + 1)
3. Recurse: match recursive case: `$x` = `z`, `$y` = `(s z)`
4. Produce `(cons z (s z))` (0 + 1)
5. Recurse: match base case
6. Return `(s z)`
7. Post-process: `(s (s z))`
8. Post-process: `(s (s (s z)))` = 3
</addition>

<multiplication>
**Multiplication (using addition):**
```
rel mult {
    # Base: 0 * y = 0
    (cons z $y) -> z
    |
    # Recursive: (1+x) * y = y + (x * y)
    # Left branch recurses to get x*y; right branch extracts y.
    # Meet combines them into (cons y (x*y)); then add computes y + x*y.
    [[(cons (s $x) $y) -> (cons $x $y) ; mult ; $r -> (cons $y $r)]
     &
     (cons (s $x) $y) -> (cons $y $r)]
    ; add
}
```
</multiplication>
</peano_arithmetic>

<list_processing>
## List Processing

Lists: `nil` = empty, `(cons head tail)` = non-empty

<length>
**Length:**
```
rel length {
    # Base: empty list has length 0
    nil -> z
    |
    # Recursive: length of (h:t) = 1 + length(t)
    [(cons $h $t) -> $t ; length ; $n -> (s $n)]
}
```
</length>

<append>
**Append:**
```
rel append {
    # Base: nil ++ ys = ys
    (pair nil $ys) -> $ys
    |
    # Recursive: (x:xs) ++ ys = x : (xs ++ ys)
    # Conjunction: left branch computes xs++ys (fresh $x on right);
    # right branch extracts x (fresh $zs on right).
    # Meet unifies: $x=x, $zs=xs++ys -> (cons x (xs++ys)).
    [(pair (cons $x $xs) $ys) -> (pair $xs $ys) ; append ; $zs -> (cons $x $zs)]
    &
    (pair (cons $x $xs) $ys) -> (cons $x $zs)
}
```
</append>

<reverse>
**Reverse (naive):**
```
rel reverse {
    nil -> nil
    |
    # Left branch reverses the tail; right branch builds the singleton [h].
    # Meet combines them into (pair rt [h]); then append computes rt ++ [h].
    [[(cons $h $t) -> $t ; reverse ; $rt -> (pair $rt $sing)]
     &
     (cons $h $t) -> (pair $rt2 (cons $h nil))]
    ; append
}
```
</reverse>

</list_processing>

<tree_processing>
## Tree Processing

Binary trees: `(leaf $v)` = leaf with value, `(node $l $r)` = internal node

<tree_sum>
**Sum of leaves:**
```
rel tree_sum {
    # Leaf: return value
    (leaf $v) -> $v
    |
    # Left branch sums left subtree; right branch sums right subtree.
    # Meet combines into (cons $sl $sr); then add computes sl + sr.
    [[(node $l $r) -> $l ; tree_sum ; $sl -> (cons $sl $sr)]
     &
     [(node $l $r) -> $r ; tree_sum ; $sr -> (cons $sl $sr)]]
    ; add
}
```
</tree_sum>
</tree_processing>

<recursion_patterns>
## Common Recursion Patterns

<accumulator>
**Accumulator pattern:**
Carry accumulated result through recursion.
```
rel sum_acc {
    # Base: return accumulator
    (pair nil $acc) -> $acc
    |
    # Left branch computes h+acc; right branch extracts the tail.
    # Meet combines into (pair $t $newacc); then sum_acc recurses.
    [[(pair (cons $h $t) $acc) -> (cons $h $acc) ; add ; $newacc -> (pair $t $newacc)]
     &
     (pair (cons $h $t) $acc) -> (pair $t $newacc)]
    ; sum_acc
}
```
</accumulator>

<mutual_recursion>
**Mutual recursion:**
Two relations calling each other.
```
rel even {
    z -> yes
    |
    [(s $n) -> $n ; odd]
}

rel odd {
    z -> no
    |
    [(s $n) -> $n ; even]
}
```
</mutual_recursion>

<generate_and_test>
**Generate and test:**
Generate candidates, filter valid ones.
```
rel valid_pair {
    [generate_pairs ; [(pair $x $y) -> (pair $x $y) ; is_valid]]
}
```
</generate_and_test>
</recursion_patterns>

<termination>
## Termination

<ensuring_termination>
**Ensuring termination:**
1. Base case must be reachable
2. Recursive case must make progress toward base
3. Measure must decrease (e.g., list length, number size)

**Good:**
```
[(cons (s $x) $y) -> (cons $x $y) ; add ; ...]
#      ^^^^^ decreases in each recursive call
```

**Bad (infinite loop):**
```
[(cons $x $y) -> (cons $x $y) ; loop ; ...]
# No progress! Same input forever
```
</ensuring_termination>

<bidirectional_termination>
**Bidirectional termination:**

Termination depends on what's constrained. Consider a nat validator/generator:

```
rel nat {
    z -> z
    |
    [(s $n) -> $n ; nat ; $m -> (s $m)]
}
```

This relation is identity on valid nats, but has different termination behavior:
- `@(s (s z)) ; nat` — terminates: input is bounded
- `nat ; @(s (s z))` — terminates: output is bounded
- `nat` (enumeration) — infinite: generates all nats `z`, `(s z)`, `(s (s z))`, ...

The key insight: constraining either end bounds the search. Leaving both unconstrained allows infinite generation.
</bidirectional_termination>
</termination>

<parameterized_recursion>
## Parameterized Recursion with Macros

Macros let you write recursive patterns parameterized by relation-valued arguments. The recursive self-call uses the full parameterized form.

<peel_example>
**Peeling layers with a custom base case:**
```
rel peel(base) {
    (s $x) -> $x ; peel(base)
    | base
}
```

The recursive call is `peel(base)` — NOT bare `peel`. Bare `peel` would refer to a completely different 0-arity relation.

Usage:
```
@(s (s z)) ; peel(z -> done)
```

Strips two `s` layers, then applies `z -> done`. Result: `(s (s z)) -> done`.
</peel_example>

<double_macro>
**Composing a relation with itself:**
```
rel double(r) {
    r ; r
}

rel inc { $x -> (s $x) }
```

`@z ; double(inc)` applies `inc` twice. Result: `z -> (s (s z))`.

This is non-recursive — no self-call in the body.
</double_macro>

<either_macro>
**Choice between two relations:**
```
rel either(a, b) {
    a | b
}
```

`@z ; either(toa, tob)` tries both `toa` and `tob` on `z`.
</either_macro>

<map_macro>
**Map over a list:**
```
rel map(f) {
    nil -> nil
    |
    # Left applies f to head; right applies map(f) to tail.
    # Meet combines into (cons $h2 $t2).
    [[(cons $h $t) -> $h ; f ; $h2 -> (cons $h2 $t2)]
     &
     [(cons $h $t) -> $t ; map(f) ; $t2 -> (cons $h2 $t2)]]
}
```

`@(cons z (cons (s z) nil)) ; map([$x -> (s $x)])` produces `(cons (s z) (cons (s (s z)) nil))`.
</map_macro>

<tree_map_macro>
**Map over a tree:**
```
rel tree_map(f) {
    [(leaf $v) -> $v ; f ; $v2 -> (leaf $v2)]
    |
    # Left maps left subtree; right maps right subtree.
    # Meet combines into (node $l2 $r2).
    [[(node $l $r) -> $l ; tree_map(f) ; $l2 -> (node $l2 $r2)]
     &
     [(node $l $r) -> $r ; tree_map(f) ; $r2 -> (node $l2 $r2)]]
}
```

`@(node (leaf z) (leaf (s z))) ; tree_map([$x -> (s $x)])` produces `(node (leaf (s z)) (leaf (s (s z))))`.
</tree_map_macro>

<recursion_note>
**Key rules for recursive macros:**
- Recursive self-calls must pass the original parameters unchanged: `peel(base)` inside `peel(base)`'s body
- Permuted or modified relation parameters in self-calls (e.g., `foo(b, a)` inside `foo(a, b)`) are deferred and expanded at call sites
- Cross-macro calls with parameters work: `double(r)` can call `compose(r, r)` even if `compose` is defined later in the same file
</recursion_note>
</parameterized_recursion>

<meta_level_recursion>
## Meta-Level Recursion (Pattern-Matching Macros)

Pattern-matching macros enable **expansion-time structural recursion** on term arguments. This is distinct from runtime recursion (Fix/Call):

| Kind | When it happens | Mechanism | Termination |
|------|----------------|-----------|-------------|
| Runtime recursion | During evaluation | Fix/Call in Rel tree | Depends on input |
| Expansion-time recursion | During parsing | Repeated macro expansion | Guaranteed for structural recursion |

### How it works

When a macro body contains a self-call with a structurally smaller term argument, it is **deferred** during body parsing and **expanded** when the macro is invoked at a call site with concrete term arguments.

```
rel fmap(@(sum $a $b), f) {
    [(inl $x) -> $x ; fmap($a, f) ; $y -> (inl $y)]    # fmap($a, f) deferred
  | [(inr $x) -> $x ; fmap($b, f) ; $y -> (inr $y)]    # fmap($b, f) deferred
}
```

When called as `fmap((sum unit xvar), inc)`:
1. Pattern `(sum $a $b)` matches `(sum unit xvar)` → `$a = unit`, `$b = xvar`
2. Deferred `fmap($a, f)` resolves to `fmap(unit, inc)` → matches `fmap(@unit, f)` → `$x -> $x`
3. Deferred `fmap($b, f)` resolves to `fmap(xvar, inc)` → matches `fmap(@xvar, f)` → `inc`
4. Final result: `[(inl $x) -> $x ; $x -> $x ; $y -> (inl $y)] | [(inr $x) -> $x ; inc ; $y -> (inr $y)]`

### Termination guarantee

Structural recursion on finite-depth terms terminates because each recursive call uses a strict sub-term of the matched pattern. Since terms are hashconsed DAGs built bottom-up, they have finite depth. The expansion depth limit (128) catches non-structural recursion (e.g., mutual bouncing between equations) with a clear error.

### Identity vs structural self-calls

- **Identity:** `fmap((sum $a $b), f)` inside `fmap(@(sum $a $b), f)` — same pattern, same params → becomes `Call(self_id)` for runtime Fix/Call recursion
- **Structural:** `fmap($a, f)` inside `fmap(@(sum $a $b), f)` — sub-term of pattern → deferred, expanded at call site
- **Non-structural:** `inf((s z))` inside `inf(@z)` — term grows, not structurally smaller → hits depth limit
</meta_level_recursion>

<anti_patterns>
## Recursion Anti-Patterns

<no_base_case>
**Missing base case:**
```
rel bad {
    [step ; bad]  # No base case - infinite recursion
}
```
</no_base_case>

<no_progress>
**No progress:**
```
rel stuck {
    $x -> $x
    |
    [$x -> $x ; stuck]  # Recursive call with same input
}
```
</no_progress>

<wrong_order>
**Wrong case order (in some systems):**
rwlog uses fair interleaving so order matters less, but logically base cases should be distinguished from recursive cases by pattern, not by order.
</wrong_order>
</anti_patterns>
