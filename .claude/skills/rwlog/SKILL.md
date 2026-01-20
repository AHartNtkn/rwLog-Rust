---
name: rwlog
description: Programming in rwlog - the relational/logic programming language based on term rewriting. Helps write relations, understand operators, debug programs, and leverage bidirectionality.
---

<essential_principles>

## What is rwlog?

rwlog is a **relational/logic programming system built on term rewriting**. Programs define relations using rewrite rules that transform input terms into output terms. The key insight: all relations are **bidirectional** - run them forwards or backwards.

### 1. Everything is a Relation

A relation maps input terms to output terms. The same relation can:
- Transform `a` → `b` (forward: `@a ; relation`)
- Find what produces `b` (backward: `relation ; @b`)
- Generate all input/output pairs

### 2. Composition is Sequential

The `;` operator chains relations: output of first becomes input of second.
```
@(cons z (s z)) ; [(cons $x $y) -> (cons $y $x)]
```
This passes a term through a swap rule.

### 3. Variables Unify

Variables (`$x`, `$y`) in rules unify across both sides:
```
(cons $x $x) -> $x
```
This only matches when both elements are identical.

### 4. Recursion via Named Relations

Relations call themselves by name:
```
rel countdown {
    z -> z
    |
    [(s $x) -> $x ; countdown]
}
```

### 5. Test Both Directions

Always verify relations work forwards AND backwards. A correct relation produces correct results in both directions.

</essential_principles>

<intake>
What would you like to do?

1. Write a new relation
2. Debug a program that isn't working
3. Run a program bidirectionally
4. Understand the syntax
5. Learn about operators (; | &)
6. Use constraints (CHR theories)
7. Something else

**Then read the matching workflow from `workflows/` and follow it.**
</intake>

<routing>
| Response | Workflow |
|----------|----------|
| 1, "new", "create", "write", "relation" | `workflows/build-new-relation.md` |
| 2, "debug", "fix", "broken", "wrong", "bug" | `workflows/debug-program.md` |
| 3, "backward", "reverse", "bidirectional", "both directions" | `workflows/run-bidirectional.md` |
| 4, "syntax", "how to write" | Read `references/syntax.md`, explain to user |
| 5, "operators", "composition", "disjunction" | Read `references/operators.md`, explain to user |
| 6, "constraint", "CHR", "theory" | Read `references/constraints.md`, explain to user |
| 7, other | Clarify intent, then select workflow or reference |
</routing>

<verification_loop>
## After Writing Any Relation

```bash
# Test forward direction
@input_term ; relation_name

# Test backward direction
relation_name ; @expected_output

# Test enumeration
relation_name
```

Report:
- "Forward: produces expected output ✓"
- "Backward: finds expected inputs ✓"
- "Edge cases: [list what was tested]"
</verification_loop>

<reference_index>
## Domain Knowledge

All in `references/`:

**Core Language:**
- syntax.md - Complete syntax reference (terms, variables, rules)
- operators.md - Composition (;), disjunction (|), conjunction (&)
- variables-and-terms.md - How variables and terms work
- constraints.md - CHR constraint theories

**Programming:**
- recursion.md - Writing recursive relations
- anti-patterns.md - Mistakes to avoid

**Execution:**
- repl.md - REPL commands and usage
- semantics.md - Tensor relations and bidirectionality
</reference_index>

<workflows_index>
## Workflows

All in `workflows/`:

| File | Purpose |
|------|---------|
| build-new-relation.md | Create a new relation from scratch |
| debug-program.md | Find and fix bugs in relations |
| run-bidirectional.md | Run programs forwards and backwards |
</workflows_index>
