# Sorts: the constraint domain

Decided 2026-11-13 (roadmap L51). Replaces rule theories. Background and the
options that were not taken: `/mnt/project-files/constraints/alternatives.md`.
Prototype: `scripts/sorts_prototype.py` (run it with no argument; `--notebooks`
adds two slower queries). Marks: *prototype* means the script checks it,
*to prove* meant it was owed in `lean/RwLog/Sorts` (now proved: section 6).

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
The surface syntax is read by `src/sorts.rs`, whose module comment is its
definition. It turns each declaration into a `SortDef`, and rejects
declarations that are not decided by the root symbol or not well formed, with
the names of the sorts at fault. `other` is the roots no other alternative of
the declaration accepts, so `(neg depth($n)) | other` keeps the case for
`neg`. An instance of an indexed sort is declared and checked when a span
first names it (`SortEnv::resolve`).

## 6. The Lean (`lean/RwLog/Sorts`)

Proved (2026-11-13), for well-formed sorts and with no other hypothesis:

| Statement | Theorem |
|---|---|
| Two normal stores that denote the same terms are equal | `Raw.Normal.eq` (`UniqueExcl.lean`) |
| The normal store of a first-order problem (pattern, equations, sorts of patterns, exclusions) is computed by a function: its result is normal and denotes the problem, it returns nothing exactly when the problem denotes nothing, and it is the only such store | `Prob.norm_some`, `Prob.norm_none`, `Prob.norm_unique` (`Norm.lean`) |
| A hidden variable is dropped, with the exclusions that mention it | `Raw.Normal.proj` (`Hidden.lean`) |
| The domain of sorts satisfies every law of the interface (L51) | `dom_lawful` (`Dom.lean`) |
| No representative relates nothing; an operation returns nothing exactly when its result relates no pair (L09) | `Rep.live`, `compose_eq_none_iff`, `meet_eq_none_iff`, `rep_eq_none_iff` (`Gaps.lean`) |
| A representative mentions no variable outside its two sides and only declared sorts (L08) | `Rep.no_hidden` (`Gaps.lean`) |
| A representative written as a span relates the same pairs | `Raw.toSpan_den` (`Rep.lean`) |
| Whether a conjunction has a member is decided on the conjunctions it reaches: a marking of them that is sound and that no round extends marks exactly those with a member | `live_iff_of_stable`, `Reach`, `reachSet` (`Reach.lean`) |
| The one member of a conjunction is found on the conjunctions it reaches: a table of members that only holds one members and that no round extends holds the member of exactly those with just one | `count_one_iff_of_stable`, `count_ne_one_of_stable`, `OneStep` (`ReachCount.lean`) |
| Whether a conjunction has a member outside a sort is decided on the pairs the pair reaches: a marking of them that is sound and that no round extends marks exactly those with such a member | `out_iff_of_stable`, `ReachOut`, `reachOutSet` (`ReachOut.lean`) |
| The two markings as one, over keys that are a conjunction alone or a conjunction with a sort: a marking of the keys a key reaches that is sound and that no round extends marks exactly the keys that hold | `trueG_iff_of_stable`, `ReachG`, `reachGSet`, `GrowsG` (`ReachOut.lean`) |
| Whether every member of a conjunction but for some terms is in a sort is asked one root at a time, and what the roots ask again is asked of smaller terms | `Hold`, `hold_iff`, `AskKey`, `sum_proj_le` (`ButStep.lean`) |

How it is built. A *normal* store (`Raw.Normal`, `Normal.lean`) is defined by
conditions on its solutions: variables numbered by first occurrence, every
variable taking values with two different head symbols, each variable listed
with every declared sort that holds of all its values, exclusions solved and
irredundant. The sorts of a variable and the exclusions of a store are sets,
so no order on symbols or on names is part of the normal form: a machine
that keeps them as lists is free to choose the order, as long as one set is
always the same list. (`Raw.xs` and `Raw.toSpan` list them, in string order;
nothing in the normal form or in the domain's operations depends on which
order that is.) Uniqueness is proved from those conditions.
Existence is by a function, `Prob.norm` (section 8): solve the equations and
push the sorts down to variables (`Reduce.lean`, `Prob.start`); pair the
pattern with all variables so none is hidden (`Hidden.lean`); extend the
pattern at every variable with one head symbol until none is left
(`Tight.lean`, `Loop.lean`); renumber (`Renum.lean`); close the sorts upward,
bring each exclusion to normal form (`NormEx.lean`), drop the implied ones and
sort them (`Assemble.lean`); project the hidden variables away.

The operations of `dom S` (`Dom.lean`) are programs. Each builds the problem
of its result from the stores it is given (`Raw.prob`, `Raw.prob₂`,
`spanProb`) and returns its normal store by `Prob.norm` (`Rep.of`). Each is
proved to return the one representative of the pairs it is to relate, or
nothing when there is no pair (`dom_rep`, `dom_compose`, `dom_meet`,
`dom_rightBound`, `Rep.conv_eq`, stated with `Rep.mk?`, the representative of
a relation chosen without computing). The laws are proved from those
statements. `Tests/SortsRuns.lean` runs the operations. The Rust of L39 is
correct when it returns a normal store with the right denotation; uniqueness
then makes it equal to `dom S`.

Two things to know about the instance:

- The type of representatives `Rep S` is empty when `S` is not well formed,
  so the converse of a representative needs no hypothesis.
- `Answer.den M ρ` does not depend on `M`: a representative for `S` relates
  the pairs its store denotes under `S`. `Raw.toSpan_den` says that the span
  it is printed as relates the same pairs in `S.interp`.

The read-time check (L56, `WF.lean`): `Sorts.WellFormed` is decided by two
least fixpoints over the conjunctions of declared sorts, `big S` (two
different members) and `fin S` (finitely many members), and the sorts are well
formed exactly when no conjunction is in both (`wellFormed_iff`). With it
`ProgramOf.WellFormed` is decidable; `ProgramOf.check` is the function and
`ProgramOf.check_iff` says it is exact. `Tests/SortsRuns.lean` runs it on the
sorts of section 5 and on the declarations section 4 rejects.

Still owed: `Engine.costed` at `Sorts.dom` (L55) and the operations of the
store in Rust with derived charges (L39); section 7 says what is done.

## 7. The Rust (`verified/rust/src/sorts.rs`) and what its charges depend on

The declarations are lists of the store, so the Rust reads them with the same
charged steps as it reads terms. Proved against section 6
(`verified/lean/RwLogVerified/Sorts.lean`):

| Rust | Specification | Ticks at most |
|---|---|---|
| `sorts::step` | `Sorts.step` | `sortsCost S + 2 m + 2`, `m` the arguments; `sortsCost S` is linear in the written size of the declarations |
| `sorts::member` | `Sorts.mem` | 5, and `sortsCost S + 11 m + 6` for each pair of a declared sort and a distinct subterm with `m` arguments |

Membership is therefore linear in the term for fixed declarations, and a term
with a repeated subterm pays for it once for each sort.

The operations of the store are not of that kind, and the bound that can be
proved for them is not polynomial in the declarations. Emptiness, the count of
members up to two, and inclusion are fixpoints over the conjunctions of
declared sorts that can be reached from the conjunctions the store holds. A
conjunction is a set of declared sorts, and the sets that can be reached are
not bounded by a polynomial in the declarations: sorts that count the length
of a chain modulo distinct primes reach every combination of residues, the
product of the primes, from declarations whose size is their sum. So the
charge of `rep`, `compose` and `meet` at `dom S` is a polynomial in the store
times the number of reachable conjunctions, and that number is a property of
the declarations alone.

For L39 and L55 this fixes the shape of the statement: the charges are stated
with the number of reachable conjunctions as a parameter computed from the
program (the read-time check of L56 already computes that set), not as a
polynomial in the size of the program alone.


## 8. The normal store as a function

`Prob.norm S hS P` (`Norm.lean`) is the normal store of the first-order
problem `P`, for well-formed sorts `S`:

| Statement | Theorem |
|---|---|
| When it returns a store, the store is normal and denotes what the problem denotes | `Prob.norm_some` |
| It returns nothing exactly when the problem denotes nothing | `Prob.norm_none` (and `Prob.norm_some`, since a normal store denotes something) |
| Every normal store that denotes the problem is the one it returns | `Prob.norm_unique` |

The operations in Rust are proved against this function. Because the normal
store is unique, any program whose result is normal and denotes the problem
returns the same store whatever route it takes. `Tests/SortsRuns.lean`
evaluates the function on problems and compares the stores.

The route:

1. `Prob.start` solves the equations and applies the solution (`solve`),
   pushes each sort down its pattern to variables (`pushAll`), and puts the
   pattern beside the tuple of all variables, so that every variable occurs
   in it.
2. `CStore.settle` replaces every variable whose sorts have one member by
   that member. `count` (`Count.lean`) says which: no member, this one, or
   more than one.
3. `tighten` (`Loop.lean`) stops if a variable has no value or an exclusion
   always holds. Otherwise every variable has infinitely many values and
   every exclusion can be avoided, so the store has a solution (`Store.rich`,
   `Inv.nonempty`). While the values left to some variable have one root, it
   replaces the variable by that root applied to new variables and does
   step 2 for the new ones. The values left to `v` are the members of its
   sorts without the terms the exclusions exclude it from (`gone`,
   `Gone.lean`); `sole` (`Roots.lean`) finds the one root or shows two values
   with different roots; `expStore_den` says the replacement keeps what the
   store denotes. Each replacement adds a symbol to the pattern, and the
   pattern has no more symbols than a term it denotes, so the loop ends. It
   is defined by recursion on that bound (`room`), which is not computed; the
   function still evaluates. The result is tight (`tight_of_sole`,
   `Tightened.lean`).
4. `ofTight` numbers the variables as they first occur (`firsts`,
   `Renum.lean`) and gives each every declared sort that holds of all its
   values: `inclBut` (`InclBut.lean`) decides that the members of the sorts
   without the excluded terms are in a sort (`Inv.inclBut_iff`).
5. `normEx` (`NormEx.lean`) brings each exclusion to normal form. It solves
   the equations and turns each alias so that it binds the later variable
   (`Orient.lean`), pushes the sorts of the bound variables onto their
   values, and reads off the sorts this puts on each free variable. What the
   exclusion removes is every choice of values for the free variables in
   those sorts. So it removes nothing when a sort rejects a value outright or
   a free variable has no value, and a free variable with one value is bound
   to it.
6. `covers` decides that one normal exclusion removes everything another
   does, and `antichain` drops the covered ones (`Assemble.lean`,
   `assembled_normal`).
7. `Raw.cut` (`Hidden.lean`) keeps the first part of the pattern, the
   variables in it and the exclusions over them (`Raw.Normal.proj`).

The proofs that a normal store exists without computing it (a store with the
most symbols, an exclusion with the fewest free variables) are deleted;
`Prob.normal` follows from the function.

`count`, `inclBut` and `sole` go through every set of declared sorts. They are
the specification, and the runs in `Tests/SortsRuns.lean` keep to a few sorts
for that reason. The Rust looks only at the sets it reaches.

The operations of `dom S` are defined by `Prob.norm` (section 6), so the
domain runs in Lean.
