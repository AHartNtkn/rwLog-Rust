<overview>
Using the rwlog REPL (Read-Eval-Print Loop) for interactive programming and testing.
</overview>

<starting>
## Starting the REPL

```bash
cargo run
```

Or if built:
```bash
./target/release/rwlog
```
</starting>

<commands>
## REPL Commands

<query>
**Execute query:**
```
expression
```

Runs the expression and shows the first result.
</query>

<load>
**Load file:**
```
load path/to/file.txt
```

Loads relation definitions from a file. Files contain `rel` definitions.
</load>

<list>
**List relations:**
```
list
```

Shows all currently defined relations.
</list>

<next>
**Get next answer:**
```
next
```

Gets the next answer from the current active query. Use after a query returns one result.
</next>

<more>
**Get multiple answers:**
```
more N
```

Gets the next N answers from the current query.

Example:
```
add ; @(s (s (s z)))
> (cons z (s (s (s z))))
more 5
> (cons (s z) (s (s z)))
> (cons (s (s z)) (s z))
> (cons (s (s (s z))) z)
> [no more answers]
```
</more>

<reset>
**Reset query:**
```
reset
```

Clears the current active query so you can start a new one.
</reset>

<define_relation>
**Define relation (multiline):**
```
rel name {
    rule1
    |
    rule2
}
```

Enter the full relation definition. The REPL accepts multiline input for `rel` blocks.
</define_relation>

<theory>
**Define CHR theory:**
```
theory name {
    constraint pred/arity

    (pred $x $y) <=> body.
}
```

Defines constraint handling rules for extensible constraints.
</theory>

<help>
**Help:**
```
help
```

Shows available commands.
</help>

<quit>
**Exit:**
```
quit
```
or
```
exit
```

Exits the REPL.
</quit>
</commands>

<workflow>
## Typical REPL Workflow

<develop_relation>
**1. Develop a relation:**
```
rel add {
    (cons z $y) -> $y
    |
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
```
</develop_relation>

<test_forward>
**2. Test forward:**
```
@(cons (s (s z)) (s z)) ; add
> (s (s (s z)))
```
2 + 1 = 3 ✓
</test_forward>

<test_backward>
**3. Test backward:**
```
add ; @(s (s (s z)))
> (cons z (s (s (s z))))
more 3
> (cons (s z) (s (s z)))
> (cons (s (s z)) (s z))
> (cons (s (s (s z))) z)
```
All pairs summing to 3 ✓
</test_backward>

<iterate>
**4. Iterate:**
- If results are wrong, redefine the relation
- Old definition is replaced by new one with same name
</iterate>
</workflow>

<tips>
## REPL Tips

<incremental_testing>
**Incremental testing:**
Test small parts before combining:
```
# Test just the rule
@(cons (s z) (s z)) ; [(cons (s $x) $y) -> (cons $x $y)]
> (cons z (s z))

# Then test with recursion
@(cons (s z) (s z)) ; add
```
</incremental_testing>

<debugging_with_identity>
**Debug with identity:**
Insert identity to see intermediate values:
```
@input ; [step1] ; [$x -> $x] ; [step2]
#                     ^^^^^^^^^^^ checkpoint
```
</debugging_with_identity>

<checking_definitions>
**Check what's defined:**
```
list
```
Shows all relations. Useful to verify loading worked.
</checking_definitions>

<file_organization>
**Organize in files:**
Put related definitions in `.txt` files:
```
# arithmetic.txt
rel add { ... }
rel mult { ... }
rel sub { ... }
```

Then:
```
load arithmetic.txt
```
</file_organization>
</tips>

<error_handling>
## Common REPL Errors

<parse_error>
**Parse error:**
```
Error: parse error at line 1, column 5
```
Check syntax - missing parentheses, wrong operator, etc.
</parse_error>

<undefined_relation>
**Undefined relation:**
```
Error: undefined relation 'foo'
```
The relation hasn't been defined. Use `list` to see what's available.
</undefined_relation>

<no_match>
**No match / failure:**
```
> fail
```
The query has no solutions. Check your patterns or input.
</no_match>

<timeout_infinite>
**Timeout / infinite loop:**
If REPL hangs, the query may be non-terminating. Use Ctrl+C to interrupt.

Common causes:
- No base case in recursion
- Backward query on infinite relation
- No progress toward termination
</timeout_infinite>
</error_handling>

<example_session>
## Example Session

```
$ cargo run

rwlog> load examples/addition.txt
Loaded 1 relation(s)

rwlog> list
- add

rwlog> @(cons (s z) (s z)) ; add
> (s (s z))

rwlog> add ; @(s (s z))
> (cons z (s (s z)))

rwlog> next
> (cons (s z) (s z))

rwlog> next
> (cons (s (s z)) z)

rwlog> next
> [no more answers]

rwlog> rel double {
    z -> z
    |
    [(s $n) -> $n ; double ; $m -> (s (s $m))]
}

rwlog> @(s (s z)) ; double
> (s (s (s (s z))))

rwlog> quit
```
</example_session>
