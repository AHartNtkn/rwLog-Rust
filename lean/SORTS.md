# Sorts: the constraint domain

Decided 2026-11-13 (roadmap L51). Replaces rule theories. Background and the
options that were not taken: `/mnt/project-files/constraints/alternatives.md`.
Prototype: `scripts/sorts_prototype.py` (run it with no argument; `--notebooks`
adds two slower queries). Marks: *prototype* means the script checks it,
*to prove* means it is owed in `lean/RwLog/Sorts`.

## 1. What is decided

1. **Constraints are sorts and `!=`.** A program declares sorts. A span's store
   holds `$x : sort` and `t != u`. There are no rules, no theory, no models.
2. **A sort is a set of ground terms given by a grammar decided by the root
   symbol.** For each root symbol and arity the grammar names the sort of each
   argument (or accepts any term there); every other symbol is either rejected
   or accepted with all its arguments in one named sort (or any). Unions such
   as `norm = neut | (lam _ norm)` and indexed sorts such as `depth(3)` are
   expanded by the front end into this form; a union whose two sides disagree
   about one root symbol is rejected when the program is read.
3. **Sorts must be infinite** (Anthony, 2026-11-13). Every conjunction of
   declared sorts is empty, one term, or infinite; this is checked when the
   program is read. A finite choice is written with `|`. See section 4.
4. **`fresh` is not in the first domain.** "The constant `c` does not occur in
   `$x`" is a sort (every other symbol is accepted with its arguments in the
   same sort). "The variable `$a` does not occur in `$t`" works in the
   prototype, but hiding `$t` splits into cases, which the single-answer
   interface excludes. The draft notebook that defines `fresh` never runs it.
5. **The interface** is `Domain R` in `lean/RwLog/Trusted/Domain.lean` (the
   thread "State the constraint-domain interface"): `rep`, `compose`, `meet`
   return `Option R`, with all laws unconditional for well-formed sorts.

## 2. The store and its operations

A store maps each variable to a conjunction of sort states and holds a set of
disequations, each a disjunction of `var != term`.

| Operation | What it does |
|---|---|
| meet of two sorts on one variable | union of the two conjunctions; dead if the intersection is empty |
| binding `$x` to `(f t1 … tn)` | one step of each state of `$x` on `f/n`, pushed on to the arguments; dead if a state rejects `f/n` |
| adding `t != u` | unify `t` and `u` under the sorts: no unifier, the disequation is true and dropped; unifier with no binding, the store is dead; otherwise keep the bindings as the disjunction |
| canonical form | work with the values a variable can still take: its sort without the ground terms it is told to differ from. If they all have one root symbol the variable is expanded to it (so a one-term sort binds its variable, and `$x : nat, $x != z` becomes `(s $y)` with `$y : nat`); otherwise its conjunction becomes every declared sort that holds them all, with the implied ones dropped in a fixed order. Inside the unifier of a disequation a variable left with one value is bound to it. A disequation the rest entails is dropped. A disequation is written as its unifier, with aliased variables named by the first of them |
| projection onto the sides of a span | delete every sort and every disequation that mentions a variable occurring in neither side |
| entailment | inclusion of sorts; a disequation is entailed when adding its unifier kills the store |

Emptiness, finiteness and inclusion of conjunctions are fixpoints over the
finitely many conjunctions reachable from the declared sorts.

## 3. What the prototype shows

- **Dead test and projection are exact** (*prototype*): 400 random stores
  against enumeration of ground instances, including the two extensions.
- **Nothing splits and the canonical form is canonical on the decided domain**
  (*prototype*): 900 random stores rewritten with implied, reordered and
  weakened constraints give the same form, and 220 different forms have
  different ground solutions (three more seeds of 600 agree).
  The first version of this claim was wrong. It treated sorts and
  disequations separately, and `$x : nat, $x != z` and `(s $y), $y : nat` are
  one set with two forms. A stronger random test found it. The fix is the
  "values a variable can still take" rule above, and the reason it is enough
  is the independence lemma (`Sorts/Indep.lean`): a product of infinite sets
  is never covered by finitely many proper solution sets of equations, so the
  only way disequations can shrink the least pattern around a store is by
  removing single ground values from one variable.
- **Why a hidden variable can always be dropped** (*to prove*): its sort is
  infinite, and each disequation forbids at most one value for the variable
  chosen last, so finitely many disequations never exhaust it. This is also
  why the dead test needs no search.
- **The notebooks** (*prototype*, with a small fair search over these store
  operations): SimpleLam and SubstConstr, Lambda, program_synth, SK and
  ProofSynth give the recorded answers. Three differences, all improvements:
  - `S K` in SimpleLam: the notebook's answer carries five `neq` atoms, four of
    them on variables that occur in neither side. Here it carries none that
    mention a hidden variable. `S K K` carries six in the notebook and none here.
  - Lambda: `norm` on `(app $x $z)` gives `$x : neut, $z : norm` at once; the
    rules waited for `$x` to be known. `norm` beside `name` is `name`.
  - ProofSynth's `depth`, never used in the notebook, bounds the search as
    `$t : depth(4)`.

## 4. The finiteness condition, and what it rejects

Three two-valued variables that must all differ is graph colouring, so with
finite sorts the dead test is NP-hard and a canonical store is not polynomial.
Hence decision 3. Its cost: the condition quantifies over every set of declared
sorts, so it also rejects two infinite grammars that share two or more
constants and nothing recursive, such as `sk = k | s | (a sk sk)` beside
`kn = k | s | (succ kn)`. No example or notebook is affected.

The condition can be lifted later without changing the interface: ground the
finite-sorted variables that occur in disequations, solve the rest as above
for each case, and read the canonical store off the table of cases. That is
exact and single-answer, and exponential only in those variables. It is not
built and not promised; it is recorded on the billboard.

## 5. The examples in sorts

```
sort prog = l | (b prog) | (f prog prog)              # no_c in program_synth
sort sk   = k | s | (a sk sk)                         # no_c in SK
sort name = other \ (app _ _) \ (lam _ _)             # var
sort neut = name | (app neut norm)
sort norm = neut | (lam _ norm)                       # norm
sort pos  = (s _)                                     # nonzero
sort depth(z) = none
sort depth((s $n)) = (imp depth($n) depth($n)) | (neg depth($n)) | other   # depth
```

`neq` is `!=`, with `: name` beside it where the notebook meant names only.
`eq` is a shared variable. `lt`, `leq` and `between` in `range_sets.txt` are
relations joined with `&`: "below 3" is a finite set, so it is not a sort.
The surface syntax above is the prototype's and is settled with the parser.

## 6. What the Lean owes (`lean/RwLog/Sorts`)

1. Membership is decidable; emptiness, finiteness and inclusion of conjunctions
   are decided; the well-formedness of section 4 is decided.
2. Unification under sorts is sound and most general.
3. The independence lemma of section 3, and from it: the dead test is exact,
   projection is exact, the canonical form is canonical.
4. The instance: `S.WellFormed → (dom S).Lawful S.interp`.
5. L08 (stores bounded by the span's variables: immediate from projection),
   L09 (no emitted answer relates nothing: the dead test is exact).

One request to the trusted side, still to be agreed: patterns in a program are
first-order (no variable in function position), which the parser guarantees
and substitution preserves. Without it a sort cannot be pushed through
`(app $x t)`.
