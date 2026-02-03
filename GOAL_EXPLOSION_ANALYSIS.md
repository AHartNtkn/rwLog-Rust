# Goal Explosion Analysis: treecalc_forward_execution_is_fast

## The Failing Test

**Location**: `src/tests/repl.rs:724`

**Test name**: `treecalc_forward_execution_is_fast`

### Test Code Summary

```rust
#[test]
fn treecalc_forward_execution_is_fast() {
    // Define app relation with 9 branches, including recursive calls and conjunctions
    let app_rel = r#"rel app {
        (f (c $x) $y) -> (a (c $x) $y)
        | (f (a $x $y) $z) -> (a (a $x $y) $z)
        | (f l $z) -> (b $z)
        | (f (b $y) $z) -> (f $y $z)
        | (f (f l $y) $z) -> $y
        | (f (f (f $w $x) $y) l) -> $w
        | [[(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
           & [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
           ; app]
        | [(f (f (f $w $x) $y) (b $u)) -> (f $x $u) ; app]
        | [(f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
           ; [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)]
             & (f (f $a $b) $c) -> (f $d $c)
           ; app]
    }"#;

    // Query: ground input -> wrap with (c z) -> app -> wrap with (c (s z)) -> app
    let query = r#"@(f (b (f l (b (b (f (b (b l)) (f l l)))))) (b l))
                   ; [$x { (no_c $x) } -> (f $x (c z))]
                   ; app
                   ; [$x -> (f $x (c (s z)))]
                   ; app"#;

    // Should complete in under 1 second
    assert!(elapsed.as_secs() < 1);
}
```

---

## Python Prototype Behavior

The test was ported to Python and run against `df_engine_proto.py`.

### Execution Metrics

| Step | Time | Goals Added | Root Outputs | Worklist |
|------|------|-------------|--------------|----------|
| 500 | 0.58s | 4,753 | 0 | 46 |
| 1000 | 8.68s | 128,973 | 0 | 47 |
| 1500 | 50.50s | 719,894 | 0 | 47 |
| 1600 | 59.58s | 897,322 | 0 | 46 |

**Key observations:**
- Goal count grows super-exponentially
- Zero outputs produced at root after 1600 steps
- Worklist remains small (~46-47) - not a scheduling issue
- Total execution time dominated by goal processing

### Final Statistics (at 1600 steps)

```
Nodes: 51 total
  Atom: 18
  Or: 8
  Join: 16
  Table: 1
  Call: 8

Total goals across all nodes: 49,560
Total outputs across all nodes: 2,108
```

### Sample Goals from APP Table

The `app` table accumulated 1,197 unique goals. Examples:

```
0: match=[(f (a (a $0 $1) (b $2)) $3)] build=[$0]
1: match=[(f $0 (a (a $1 $2) $3))] build=[$3]
2: match=[(f (f $0 l) (b l))] build=[$0]
3: match=[(f (a (a $0 $1) $2) (b $2))] build=[$0]
4: match=[(f $0 (a (a $1 $2) $3))] build=[$1]
5: match=[(f (f $0 $1) (b (b $1)))] build=[$2]
6: match=[(f (b $0) (a (a $1 $2) $0))] build=[$0]
7: match=[(f $0 (a (c $1) (b l)))] build=None
8: match=[(f (a (a (a $0 $1) (b $2)) (a (c $3) (b $2))) (a (a $4 $5) $2))] build=[$6]
9: match=[(f $0 (a (a $1 $2) l))] build=None
```

---

## Rust Implementation Behavior

### Execution Metrics (from earlier debug runs)

| Metric | Value |
|--------|-------|
| Unique goals (10s run) | 11,000+ |
| Total add_demand calls | 135,000+ |
| Duplicate rate | ~90% |

### Sample Goals from Rust

```
[GOAL #0] match=None build=None
[GOAL #1] match=None build=None
[GOAL #2] match=None build=None
[GOAL #3] match=None build=[$0]
[GOAL #4] match=None build=[$0]
```

---

## Comparison: Python vs Rust

| Aspect | Python Prototype | Rust Implementation |
|--------|------------------|---------------------|
| Goal explosion | YES - 897K in 1600 steps | YES - 11K+ in ~10s |
| Goal structure | Rich term structure | Mostly vacuous (None or [$0]) |
| Outputs at root | 0 | 0 (test times out) |
| Time per step | ~37ms | Much faster (Rust speed) |

### Critical Difference: Goal Quality

**Python goals have actual term structure:**
```
match=[(f (a (a $0 $1) (b $2)) $3)] build=[$0]
```

**Rust goals are mostly vacuous:**
```
match=None build=[$0]
```

This suggests the Rust goal synthesis logic may be stripping/losing structure that Python preserves. However, BOTH implementations suffer from goal explosion - the Python goals are more informative but still explode in quantity.

---

## Root Cause

The `app` relation has:
1. **9 alternative branches** (Or nodes)
2. **3 branches with recursive `app` calls**
3. **2 branches with conjunction (`&`)** requiring Meet operations
4. **Nested recursion** - Meet nodes contain Compose nodes containing Call nodes

When a Join node (Meet or Compose) receives an output from one child, it synthesizes goals for the other child. With recursive definitions:

1. `app` table receives goal G
2. Body produces output O
3. Output O triggers goal synthesis for sibling nodes
4. New goals propagate to recursive `app` calls
5. Those calls register goals with `app` table
6. Repeat from step 2

The feedback loop causes exponential goal proliferation.

---

## Conclusion

**Both Python and Rust implementations exhibit goal explosion on this query.** The Python prototype is not immune - it simply runs slower, so fewer steps complete in the same wall-clock time.

The fundamental issue is **eager goal synthesis from outputs** combined with **recursive relation definitions**. This is an algorithmic problem, not an implementation bug.

Lazy goal synthesis - generating goals only when needed to make progress - is required to handle recursive definitions without explosion.
