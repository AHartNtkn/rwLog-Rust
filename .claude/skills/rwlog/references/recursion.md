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
    [(cons (s $x) $y) -> (triple $y (cons $x $y) unit) ;
     [(triple $a $b $c) -> $b ; mult ; $r -> (triple $a $b $r)] ;
     [(triple $a $b $r) -> (cons $a $r) ; add]]
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
    [(pair (cons $x $xs) $ys) -> (pair $xs $ys) ; append ; $zs -> (cons $x $zs)]
}
```
</append>

<reverse>
**Reverse (naive):**
```
rel reverse {
    nil -> nil
    |
    [(cons $h $t) -> (pair $t (cons $h nil)) ;
     [(pair $a $b) -> $a ; reverse ; $ra -> (pair $ra $b)] ;
     [(pair $ra $b) -> (pair $ra $b) ; append]]
}
```
</reverse>

<map>
**Map (applying a relation to each element):**
```
rel map_succ {
    nil -> nil
    |
    [(cons $h $t) -> (pair $h $t) ;
     [(pair $h $t) -> $h ; [$x -> (s $x)] ; $h2 -> (pair $h2 $t)] ;
     [(pair $h2 $t) -> $t ; map_succ ; $t2 -> (cons $h2 $t2)]]
}
```
</map>
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
    # Node: sum left + sum right
    [(node $l $r) -> (pair $l $r) ;
     [(pair $l $r) -> $l ; tree_sum ; $sl -> (pair $sl $r)] ;
     [(pair $sl $r) -> $r ; tree_sum ; $sr -> (pair $sl $sr)] ;
     [(pair $sl $sr) -> (cons $sl $sr) ; add]]
}
```
</tree_sum>

<tree_map>
**Map over tree:**
```
rel tree_map_succ {
    (leaf $v) -> (leaf (s $v))
    |
    [(node $l $r) -> (pair $l $r) ;
     [(pair $l $r) -> $l ; tree_map_succ ; $l2 -> (pair $l2 $r)] ;
     [(pair $l2 $r) -> $r ; tree_map_succ ; $r2 -> (node $l2 $r2)]]
}
```
</tree_map>
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
    # Recursive: add head to acc, continue
    [(pair (cons $h $t) $acc) -> (pair $h $acc) ;
     [(pair $h $acc) -> (cons $h $acc) ; add ; $newacc -> (pair $t $newacc)] ;
     [(pair $t $newacc) -> (pair $t $newacc) ; sum_acc]]
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
