# The constraint rule language

Design note for milestone 5 of the roadmap (L11, L12, L09, L08, L10, canonical spans, L17 first part, and the list of algorithms for L39). Written 2026-11-13 and revised the same day (see "Revision" below). No Lean or Rust is changed by this note. A prototype of everything decided here is `scripts/constraint_language_prototype.py`; run it with no argument, and it classifies every example theory as written and checks every claim marked *prototype* below.

Each claim carries one of four marks. *Argued*: a proof is given here on paper and is owed in Lean. *Prototype*: the script checks it on the examples. *Open*: not known. *Impossible*: a counterexample or a reduction is given.

**Revision (2026-11-13, on Anthony's instruction).** Confluence is detected, never enforced. The first version of this note rejected theories that failed its check and asked for three edits to the example theories. This version rejects nothing and edits nothing:

- The check classifies a theory when it is read, as *detected confluent* or not. The user supplies nothing.
- A detected theory runs on the *exact path* (sections 5.1 to 5.4): a normal form, exact refutation, canonical stores.
- Every other theory runs on the *fallback path* (section 5.5), which is the closure that is in the tree today. It is sound and complete for every theory and promises less.
- A guard now holds by entailment, as conformance case 2 asks, and not only when it is an atom of the store. With that, `equality_constraints.txt` is detected confluent as written.
- Six of the seven example theories are detected confluent as written. The seventh, `lamvar_constraints`, runs on the fallback path, and section 13 says why.

## 1. Decisions

1. **Every theory the parser reads is run.** Reading a theory classifies its rules and the theory. Nothing is rejected; what the classification finds is reported, with the rule and the reason.
2. **A theory is detected confluent when every rule that says something defines one atom or restricts, in an order that needs no annotation, and finitely many critical pairs join** (section 4). For a theory that meets the conditions on single rules, the detection is exact: it fails exactly when two orders of firing give two results, and it shows the store and both results.
3. **On a detected theory the engine keeps the normal form of a store.** `refutes?` is "the normal form is `fail`", and that is exact in both directions (section 5.4).
4. **On any other theory the engine keeps the store as written** and uses the theory only forwards: it refutes a store when the closure of the store holds `fail`, and instantiates by the equations the closure forces. This cannot depend on an order, because nothing is removed (section 5.5).
5. **A guard holds when the store entails it.** In `H <=> G | B`, and for every head a rule writes back, the atom holds when adding it to the part of the store below `H` changes nothing (section 5.1).
6. **A body variable that no head binds is existential.** On the exact path it is created as a store-only variable, in the class where nothing can ever bind it. A theory with such a variable outside that class is not detected (section 6).
7. **A canonical representative is a simplified span, reduced to its core, labelled canonically, with one orientation bit.** The converse of a representative flips the bit. This is the same on both paths; only the simplification differs. A representative in a single name space that commutes with exchanging the two sides does not exist (section 8.2).
8. **What holds for every theory and what holds only for a detected one is kept apart** in one table (section 10). Soundness, completeness, determinism, the converse and idempotence hold for every theory. Exact refutation, no dead answer, the algebraic laws, halting with irrelevant atoms and the statement about extensions are stated for detected theories.
9. **A defined predicate is a closed predicate**: one declared `closed`, whose atoms are false unless a case of its definition applies. A preprocessor may add closed predicates under new names and nothing else (section 12).

## 2. What the examples use

Read before anything was decided: `examples/equality_constraints.txt`, `examples/range_sets.txt`, and the notebooks `theory_demos`, `SK`, `program_synth`, `program_synthesis`, `ProofSynth`, `Lambda`, `SimpleLam`, `SubstConstr`, `Untitled`, `polysimp` (the other notebooks use no constraints), with `/mnt/project-files/r001/constraint-redesign-notes.md` and the conformance cases.

| What a theory does | Where | Classified as |
|---|---|---|
| Defines a predicate by cases on constructors, recursing on the parts | `eq`, `neq`, `leq`, `lt`, `no_c`, `depth`, `fresh`, `norm`, `between` | definition without guards |
| Declares a shape impossible | `(var (app $x $y)) <=> fail.`, `(neq $x $x) <=> fail.` | definition with body `fail` |
| Lets one constraint decide another | `(norm (app $x $z)), (var $x) <=> (var $x), (norm $z).` and `(norm $x), (var $x) <=> (var $x).` in `Lambda`; the two guarded rules of `nonzero` | definition with guards |
| Forbids a combination | `(eq $x $y), (neq $x $y) <=> fail.` | restriction |
| Removes a second copy of an atom | `(neq $x $y), (neq $x $y) <=> (neq $x $y).` | inert: a store is a set |
| Makes a predicate symmetric | `(neq $x $y), (neq $y $x) <=> (neq $x $y).` in `SimpleLam`, `SubstConstr` | a definition whose guard is not below it; keeps the theory from being detected (section 13) |

No example has a propagation (`==>` with atoms on the right), a body variable that the heads do not bind, or an equation in a body. Equations come from the conformance cases (`(pin $x) <=> $x = z.`) and from Anthony's decision that a head is kept by writing it back.

How constraints are used matters as much as how they are defined. A constraint sits on a span and restricts a variable (`$x {(no_c $x)} -> (f $x (c z))`), often far from where the test finally fails. Answers keep the constraints that are still undecided (`(a (a k $0) s) {(no_c $0)} -> …`). In `SimpleLam` and `program_synth` the answers also keep atoms on variables that occur in neither side, such as `(neq $3 $2), (neq $3 $1)` and seven separate `(no_c $7)` to `(no_c $13)`. Those store-only variables are where the hard questions of sections 8 and 9 come from.

## 3. The language

### 3.1 Syntax

```
theory name {
    constraint p/n            # an open predicate
    constraint q/n closed     # a closed predicate (section 12)

    H1, ..., Hn <=> body.     # the form every example uses
    K1, ..., Km \ H <=> body. # the same rule with the kept heads named
    H <=> G1, ..., Gk | body. # the same rule with the kept heads as a guard
    H1, ..., Hn ==> body.     # the heads are kept
}
```

A body is `fail`, or a list of atoms and equations `s = t`; the empty list is written `.` or `true`. The surface syntax is the one the parser already reads, so the front end stays. The only addition is the word `closed`.

### 3.2 What a rule means

Unchanged from `Trusted/Semantics.lean`: a rule `H1, …, Hn <=> body` holds in an interpretation when, for every ground instance of the head variables, all heads hold exactly when the body holds for some values of its other variables. Rules are two-way axioms. `K \ H <=> B`, `H <=> K | B` and `H, K <=> K, B` are one axiom. Stores and firing are how an engine computes with them, and both paths below are sound for every rule under this meaning.

### 3.3 How a rule is classified

Let `μ` be the most general unifier of the body's equations. A head `h` is *kept* when it is written as a guard, or when `hμ` is an atom of the body under `μ`; otherwise it is *removed*.

| Kind | Shape | On the exact path |
|---|---|---|
| definition `K \ r <=> eqs, B` | one removed head `r`; `K` the kept heads, `B` the body without them. `H <=> G | fail` is the definition of `H` as false under `G`. | fires (5.1) |
| restriction `K ==> eqs` | no removed head, nothing added, and equations that say something; or a body that is `fail` or has no unifier, with no guard written | fires (5.1) |
| inert | no removed head, nothing added, equations that hold already | never fired; it holds in every interpretation of a set of atoms |
| propagation | no removed head, atoms added | keeps the theory from being detected |
| several removed heads | two or more | keeps the theory from being detected |

So `(pin $x) <=> $x = z, (pin z).` is the restriction `(pin $x) ==> $x = z`, and `(pin $x) <=> $x = z.` is the definition of `(pin $x)` by an equation and nothing else. The fallback path does not use this table: it reads every rule forwards, whatever its kind.

## 4. Detection

A theory is *detected confluent* when the five conditions below hold of its rules, the inert ones left aside. Each condition is decidable. A condition that fails is reported with the rule and the reason, and the theory then runs on the fallback path. Nothing here is an error.

In the first version of this note these were the well-formedness conditions W1 to W4 and W6, and a theory that failed one was rejected. W5 (a rule whose heads the other rules refute) is no longer a condition. It is reported as a note, because such a rule does not harm confluence.

**D1. Shape.** Every rule is a definition, a restriction or inert (3.3). Every variable of an equation occurs in a head.

**D2. Order.** Say that predicate `p` *mentions* `q` when a definition of a `p` atom has a `q` atom among its guards or in its body. For a definition `K \ r <=> eqs, B` and every atom `x` of `K` and `B`: either the predicate of `r` mentions that of `x` and not the other way round, however long the chain; or `xμ` is smaller than `rμ` under every substitution (fewer symbols, and no variable more often). No annotation is needed: the levels are the strongly connected components of "mentions". An atom `a` is *below* an atom `r` when its predicate is at a strictly lower level, or at the same level with `a` smaller than `r`.

**D3. Created variables.** A body atom `b` with a variable that no head binds must have a predicate strictly below the defined one, and no predicate that `b`'s predicate mentions, at any distance or itself, may be a head of a rule that has an equation (section 6). Until the lemma of section 6 is proved in Lean, the stricter form is used: no body atom has such a variable.

**D4. Critical pairs.** For every definition `ρ1` with removed atom `r1`, every definition or restriction `ρ2`, and every head `h` of `ρ2` (kept or removed) that unifies with `r1` after renaming apart: take the store made of all heads of both rules under the unifier, fire each rule once on it, and compare the normal forms of the two results, up to the names of created variables. They must be the same. A rule is also compared with itself.

**D5. Closed predicates.** A definition of a closed predicate has no guards and its body atoms are closed.

For a theory that passes D1 to D3 and D5, D4 is exact (*argued*, 5.3): every pair is a store that two rules really rewrite, so a pair that does not join is a store with two normal forms.

What is reported is meant to be read. For `(link $x $y) <=> .` with `(link $x $y), bad <=> fail.` the prototype prints

```
two results on {(link $x $y), bad}
    (link $x $y) <=> .               gives {bad}
    (link $x $y), bad <=> fail.      gives fail
```

which says that the theory makes `bad` false and no rule says so. A user who wants the exact path adds `bad <=> fail.`; a user who does not care changes nothing and gets the fallback path. In every case found in the examples and the recorded counterexamples, the store of the failing pair is the rule that is missing.

## 5. The two paths

### 5.1 The exact path: one step

A store is a finite set of atoms over the variables of its span. Its variables are rigid: a head matches an atom one way only. Two heads may match the same atom.

- A definition `K \ r <=> eqs, B` applies at an atom `rσ` of the store when every guard holds. When every variable of the guards occurs in `r`, which is the case in every example, a guard *holds when the part of the store below `rσ` entails it*: adding the guard to that part changes neither its normal form nor any variable. A guard that is an atom of the store holds trivially. When a guard has a variable that `r` does not bind, the rule takes all its guards from the store, like the heads of a restriction, since only an atom of the store can bind that variable. Then solve the equations. No unifier: the store is refuted. A unifier `θ`: remove `rσ`, add `Bσ` with a new variable for each created variable, and apply `θ` to the whole span.
- A restriction `K ==> eqs` applies when all its heads are atoms of the store: the same, with nothing removed or added. A step that changes neither the span nor the store is not a step.
- An atom of a closed predicate that unifies with no head of a definition of that predicate refutes the store.

The normal form `nf T c` is the result when no step applies: `fail`, or a store with the substitution its equations forced. The entailment test is well founded: it asks for normal forms of stores made only of atoms below `rσ`, and by D2 every guard is below the atom it guards.

**Why entailment.** Conformance case 2 says that a guard must hold by entailment on the store as it stands: `(nonzero z)` must be refuted by `(nonzero $x) <=> (eq $x z) | fail.` although no `(eq z z)` is in the store, and `(nonzero $x)` must wait. The first version of this note fired a guard only when it was an atom of the store, and so had to ask for two more rules in `equality_constraints.txt`. With entailment the file is detected confluent as written and gives every answer the case asks for (*prototype*): `(nonzero z)` is refuted, `(nonzero (s z))` leaves nothing, `(nonzero $x)` stays, and it is dropped when the store holds `(neq $x z)` or anything whose normal form is that, such as `(neq (s $x) (s z))`.

### 5.2 E1: firing ends (*argued*)

Order atoms by level and then by size, and stores by the multiset extension. A definition replaces `r` by atoms that are lower by D2, so every step without a binding lowers the store. A binding replaces a variable that is not created by a term over variables already present, so it lowers the number of such variables, and by D3 a created variable is never bound. The pair (number of variables that can be bound, store) falls at every step. An entailment test is a normal form of a store strictly below the store it is asked in.

### 5.3 E2: every order of firing gives the same normal form (*argued, prototype*)

**Statement.** For a detected theory, `nf T c` does not depend on the order of steps, up to the names of created variables. Further, `nf (nf A ∪ B) = nf (A ∪ B)` and `nf (cγ) = nf ((nf c)γ)` for every substitution `γ`.

**Why sets need care.** On multisets, a step in a store is a step in every larger store, and joinable critical pairs give confluence by the usual argument. On sets that is false: if a step removes `a` and a later step produces `a` again, a larger store that already held `a` loses it. Counterexample 1 of the redesign notes is this effect with a rule that removes two heads.

**Argument.** Induction on the store in the order of E1; the statement and the three facts below are proved together. Two steps from one store either remove the same atom, or one removes an atom the other needs in the store, or neither.

(a) *A step lifts to a larger store up to one more step of the same rule.* If `S` steps to `S'` by removing `a`, and `C` is any set, then `S ∪ C` steps to `S' ∪ (C \ {a})`, and `S' ∪ C` either is that store or steps to it by the same instance, because the guards of the instance still hold in `S'`. So along any derivation `S0, S1, …, Sn`, the stores `Sj ∪ C` all have the same normal form, by the induction hypothesis.

(b) *The same holds for instances*: a step on `S` gives a step on `Sγ`, up to one more step of the same instance when `γ` identifies the removed atom with another one. A substitution that does not agree with a binding refutes the instance, and it refutes it on the other side of a joined pair too, because both sides end with the same forced substitution.

(c) *Entailment is kept by every step elsewhere.* Let a guard `g` of an instance at `r` be entailed by `L`, the part of the store below `r`. A step at an atom below `r` is a step of `L` itself (its own guards look only further down), so it leaves the normal forms of `L` and of `L ∪ {g}` as they were, by the induction hypothesis. A step at any other atom removes nothing from `L` and can only add atoms to it or instantiate it, and `nf (L ∪ C ∪ {g}) = nf (nf (L ∪ {g}) ∪ C) = nf (L ∪ C)`, with (b) for the instantiation. So a guard that held still holds. This is what a test for the guard being an atom of the store does not give, and it is why a rule that rewrites the support of a guard needs no pair of its own.

With (a), (b) and (c): two steps at different atoms commute up to one repeated step, unless one removes an atom that the other matched in the store (a head of a restriction, or a guard of a definition that takes its guards from the store). That case, and the case of one atom removed by two instances, are instances of the pairs of D4 inside a larger store, except that entailed guards need not be atoms of the store. Add them to both results: each is below an atom that its step removed, so the enlarged results are still below the store the two steps started from, and by the composition law there they have the normal forms of the results themselves. So the joining of the pair carries over. Newman's lemma on the well-founded order gives uniqueness, and (a) gives the two equations. What makes (a) true is that a definition removes one atom and keeps its guards. With two removed heads it fails.

D4 as stated compares more pairs than the argument needs. A pair where `r1` meets a guard that holds by entailment always joins, by (c). The check may skip them; the prototype does not.

**Prototype.** 400 random stores for each of the eleven detected theories (the example files as written, `ranges` extended, both `pin` theories), with three random orders each, and the comparison of `nf (nf A ∪ B)` with `nf (A ∪ B)`. For entailment specifically: a theory in which a guarded rule rewrites the atom another rule's guard rests on is detected and has one normal form on 400 stores; and of 300 random theories of guarded definitions over three levels, the 154 that are detected have no store with two normal forms (about 2,500 detected theories in longer runs, none with two).

### 5.4 E3: refutation is exact (*argued*)

**Statement.** Let `T` be detected and `c` a store with no atom of a closed predicate left in its normal form. Then `nf T c = fail` exactly when no model of `T` contains a ground instance of `c`. If `nf T c = (θ, c')`, then in every model the ground instances of `c` that hold are exactly the instances of `θ` under which `c'` holds.

**Sound direction.** Each step preserves the instances that hold in each model. For a definition this is the rule's axiom read in both directions under its guards, and an entailed guard holds wherever the store does, by the same statement for the smaller store. `Fire.sound` is the forward half today.

**Complete direction.** Let `S` be the normal form with each variable replaced by a distinct symbol that occurs nowhere in the theory (the signature is open, so there always is one). `S` is still normal, because a head cannot tell such a symbol from a rigid variable. Let `M` be the set of ground atoms that occur in some finite set `A` with `nf (S ∪ A) = S`. Then `S ⊆ M`, and `M` is a model:

- Two entailed sets are entailed together, by `nf (nf X ∪ Y) = nf (X ∪ Y)`.
- If the heads of an instance of a definition are in `M`, take `A` containing them. The guards are atoms of the store, so they hold, and the instance fires on `S ∪ A`. The equations hold (otherwise the normal form would be `fail`), and the result still has normal form `S`, so the guards and the body are in `M`. Conversely, if the guards and body are in `M` and the equations hold, add the defined atom: the instance fires and gives back a store whose normal form is `S`, so the atom is in `M`.
- If the heads of a restriction are in `M` and its equations fail, the normal form of `S ∪ A` would be `fail`.

So some model contains an instance of `c`. The proof uses E2 and nothing else.

**With closed predicates** the argument stops, because an unknown symbol under a closed predicate is false. A store whose normal form keeps closed atoms is satisfiable exactly when those atoms have a ground solution that leaves the rest unrefuted, and that is undecidable (9.3). Section 12 says what an engine owes in that case. No example theory has a closed predicate.

### 5.5 The fallback path

For a theory that is not detected, the engine uses the closure of the R001 redesign (`Theory.saturate`, `refutes?`, `bind?`, `simplifyWithin` in `Kernel/Refute.lean`). It is described here because it is now a permanent half of the design and not a stage to be deleted.

- *Closure.* Read every rule forwards: its heads imply its body. The closure of a store adds the body atoms of every instance whose heads are in the closure, until nothing is new. Only *bounded* rules are used: under the unifier of its equations, each body atom is at most the size of some head under every substitution. The closure then stays inside the finitely many atoms of the store's own size over the store's variables and the theory's symbols, so it ends for every theory.
- *Refutation.* The store is refuted when an instance on the closure has body `fail` or equations with no unifier, or the closure holds an atom of a closed predicate that unifies with no head of its definitions.
- *Forced equations.* An instance on the closure whose equations have a unifier that binds something forces that binding. The span is instantiated by all forced bindings together, and the closure is taken again, until none is forced.
- *The store is kept as written*, instantiated, with equal atoms kept once. Nothing is rewritten and nothing is added to it. `Theory.present` may still rewrite an answer for showing.
- *A guard* holds when it is an atom of the closure.
- *Coverage* is coverage as written (`Span.Covers`, decided by `covers?`).

**What it guarantees, for every theory** (*argued*; *prototype* on seven theories that are not detected, 300 random stores each, and against the exact path on six detected theories):

1. *Deterministic.* Simplification is a function of the store as a set and of the theory, and commutes with every renaming of variables. The closure is the least set closed under the forward rules, so no order of firing can change it; the forced bindings are the unifier of all forced equations. So the same goal always gets the same key.
2. *It commutes with the converse at the same charge.* No rule sees the sides of a span, so simplifying a span and simplifying its converse are the same computation on the same store. The representative of 8.1 adds the same labelling work on both.
3. *It loses no live ground triple.* Every atom of the closure holds wherever the store does, because each rule's forward half is half of its axiom, so a forced equation holds wherever the store does.
4. *It refutes only when sound*, for the same reason and by the closed axiom.
5. *The representative used as a table key is idempotent*: simplifying a simplified span changes nothing, since no equation is forced any more, and the core and the labelling are idempotent (8.1).

So no guarantee the roadmap asks of the fallback fails. Two points differ from the Lean as it stands, and both keep its termination proof:

- Today `TRule.bounded` asks for each body atom to be a head or *strictly* smaller than one. Equal size is enough for the closure to stay inside its finite universe, and it lets `(lt $x $y) ==> (leq $x $y).` and `(r $x) <=> (t $x).` fire (*prototype*).
- Today `bind?` takes the first forced equation it finds in the order of the store. Taking all of them, as above, makes guarantee 1 hold by construction. The alternative is a lemma that the first one found does not matter.

**What it does not promise**, each with its example (*prototype*):

- *No rewriting, so no canonical store.* Under `lamvar_constraints`, `{(neq a b), (neq b a)}` is kept as two atoms. Spans that are equal in every model can have different representatives and different tables.
- *Halting with atoms the theory makes irrelevant* (L08). Under `(link $x $y) <=> .` with `(link $x $y), bad <=> fail.`, a `link` atom is never removed, so link chains pile up along a recursion. This is counterexample 4 of the redesign notes, and on the fallback path it stays one.
- *No dead answer.* A store that no model satisfies is emitted when the closure does not find the contradiction.
- *Unbounded rules are not used.* A rule whose body is larger than its heads, or has a variable that no head binds, never fires on this path. It is named when the theory is read ("is not used by the fallback path"), so it is not silent. It costs pruning and nothing else.
- The laws of section 10 marked "detected".

A stronger fallback is possible and not chosen: every subset of the rules that is itself detected confluent can be fired exactly, and all five guarantees hold for it, because firing fewer rules is still sound. What is missing is a choice of subset that is a function of the theory and not of the order of its rules. It is on the billboard.

## 6. Body variables that no head binds (L12)

**Meaning.** As the trusted semantics already says: existential. `(even $x) <=> (double $h $x).` says `(even a)` holds exactly when `(double h a)` holds for some `h`.

**Firing on the exact path.** The rule fires like any other. The variable becomes a new store-only variable of the span, which is already how the span semantics reads a variable that occurs only in a store.

**The complication.** With equations in reach, firing can run for ever on a store that has no solution (*impossible* to fire in general):

```
(a (f $x)) <=> (a $x), (b $x).
(b $x)     <=> (c $y $x).
(c $y $x)  <=> $x = (f $y), (d $y).
```

Every rule passes D1 and D2. On `{(a $v), (b $v)}` the second rule creates `$y`, the third binds `$v` to `(f $y)`, the first peels the `f` and asks `(b $y)` again. The store forces `$v` to be an infinite term, so it has no instance, and firing never says so (*prototype*). The same happens when the created variable is in the equation itself, as in `(nat $x) <=> $x = (s $y), (nat $y).`

**The class that is detected.** D3: a created variable only ever occurs in atoms whose predicates, and everything below them, are never heads of a rule with an equation. Then nothing can bind it, it stays rigid for the whole life of the span, and E1 holds as argued. `(even $x) <=> (double $h $x).` with `double` defined by cases is detected (*prototype*).

**What is owed before the class is in.** Anthony's condition is that created variables are allowed only if proved free of complications. E1 is argued above. E2 and E3 need one more lemma, because a created variable leaves a copy behind: `{(even a), (double b a)}` becomes `{(double $h a), (double b a)}`, which equals `{(double b a)}` only after the core is taken. So E2 and E3 for theories with created variables are stated up to the core on created variables, and the lemma owed is that the core on created variables is kept by every later step (created variables are rigid and never bound, which is why this is expected to hold where the general statement of 8.4 does not).

**What happens when nothing is rejected (L50).** Until the lemma is proved in Lean, and for good if it fails, a theory with a created variable is not detected and runs on the fallback path. There the rule is not bounded, so it is not used, and reading the theory says so. Its meaning is unchanged and the engine stays sound and complete; the rule only prunes nothing. Once the lemma is proved, a theory whose created variables are in the class of D3 is detected and the rule fires. No example theory has a created variable, so this changes no example either way.

## 7. No silent rule, no dead answer (L09)

- **On a detected theory no rule is skipped.** There is no run-time side condition. A rule that says something fires whenever its heads are in the store and its guards hold.
- **On any other theory a rule can go unused, and never silently.** Reading the theory names every rule that the fallback path does not use, every inert rule, and (on a detected theory) every rule whose heads the other rules refute, each with its reason.
- **No rule is lost to the order.** A rule that the old order could not use is now either placed by levels or reported with the cycle shown.
- **No dead answer on a detected theory.** An engine emits only simplified spans. By E3 a simplified span without closed atoms relates a pair in some model. On the fallback path a dead answer can be emitted (5.5).

## 8. Canonical representatives (L08)

### 8.1 Definition

For a span `s`:

1. *Simplify* by the path of the theory: `nf` on a detected theory, the fallback of 5.5 otherwise.
2. *Core.* Remove atoms from the store as long as a substitution of store-only variables maps the store into what is left. The result is unique up to renaming (Chandra and Merlin).
3. *Label.* Name the variables of `l` in order of first occurrence, then the remaining variables of `r`, then the store-only variables by the labelling that makes the sorted list of atoms least in a fixed structural order. The last step is a search over labellings, not a first-occurrence order.
4. *Orient.* Label `s` and its converse as in step 3 and compare the two results with the one structural comparison of the base machine. Keep the smaller one and a bit that says which it was. If they are equal the span is its own converse and the bit is 0.

The representative is the pair of the bit and the labelled span. **The converse of a representative flips the bit**, and leaves a self-converse representative alone. So `canon (s°) = (canon s)°` holds by construction (*prototype*, on both paths), `canon s` and `canon (s°)` do the same work (two labellings and one comparison that reads both arguments), and the converse of a representative costs one tick. The representative of a representative is itself (*prototype*, on both paths). `canon s = canon s'` exactly when the simplified spans are `Span.Equiv` (*argued*: step 2 is the classical theorem, steps 3 and 4 are canonical by construction).

### 8.2 No representative in one name space commutes with exchanging sides (*impossible*)

Take `s = (f $v $w) -> (f $w $v)`. Exchanging its sides gives `(f $w $v) -> (f $v $w)`, which is `s` with its two variables renamed. A canonical representative gives both the same value `L -> R`. Commuting with the exchange gives `L -> R = R -> L`, so `L = R`, so the two variables are one, and the result no longer stands for `s`. This is why the representative carries a bit and why the answer type of the engine (L28) has its own converse. The freeze list's row is met in that form.

### 8.3 Interfaces

`rightBound s` is the canonical representative of `r {c'} -> r`, where `c'` holds the atoms of the simplified store all of whose variables occur in `r`. `leftBound s` is `rightBound (s°)`. On the exact path a subset of a normal store is normal, so nothing is fired; on the fallback path nothing is ever rewritten. A boundary has no store-only variable, so its core is itself, its labelling is a sort, and its representative is computed in polynomial time. A boundary is its own converse.

The freeze list says a boundary carries "the part of the store that mentions its variables". This note reads that as the atoms that mention only its variables, as `storeOn` does today. An atom that also mentions another variable could be carried with that variable existential. That is a tighter boundary and puts store-only variables into table keys, which is where exactness ends. It is on the billboard and is not chosen.

### 8.4 What the core is not (*impossible*, *prototype*)

On the exact path `Span.Equiv` is not kept by simplification. In the theory `(p z) <=> . (p (f $x)) <=> fail.`, the spans `$w {(p z)} -> $w` and `$w {(p z), (p $y)} -> $w` are equivalent as written and simplify to `$w -> $w` and `$w {(p $y)} -> $w`, which are not (redesign notes, counterexample 3). The same happens after the fact: `$l {(no_c $y), (no_c $w)} -> $w` has core `$l {(no_c $w)} -> $w`, and composing each with `@k` gives `$l {(no_c $y)} -> k` and `$l -> k`.

The cause is always the same. The core maps a store-only variable to a term, and a later step rewrites the atom that held the term, so the witness is gone while the variable stays. The two results are equal in every model, and the one that came from the core covers the other. They are not equivalent as written.

So three statements have to be kept apart, all about a detected theory:

- `canon s = canon s'` exactly when the simplified spans are equivalent as written. True.
- Composition followed by simplification is associative, and meet is commutative and associative, up to renaming, when no core is taken in between. True by E2 (*argued, prototype*). This is the roadmap's criterion and it holds exactly, not only up to `Span.Equiv`.
- Replacing an answer by its canonical representative and continuing gives the canonical representative of the result. **False** when a store-only variable's witness is later rewritten away. The two results agree in every model, and one covers the other.

Consequence for milestone 6: two strategies that reach one answer through different splits store one representative, except in that case, where they can store two answers of which one covers the other. Nothing is unsound and no answer is lost. If the engine needs the third statement exactly, it gets it by leaving step 2 out (representatives up to renaming compose exactly, *prototype*) and letting coverage remove the redundant answers. That choice belongs to the engine and is on the billboard. Table keys are not affected: boundaries have no store-only variables.

On the fallback path nothing rewrites, so this failure cannot happen there. The roadmap does not ask for the algebraic laws on that path and this note does not claim them.

### 8.5 Stores along a recursion

On a detected theory:

- An atom the theory makes true is removed by the normal form. With `(link $x $y) <=> .`, the answers of `r = $0 {(link $0 $1)} -> $1 | r ; r` are all `$0 -> $1`, and the query halts (*prototype* for `r ; r`).
- Copies of one atom on different store-only variables are removed by the core: of `(no_c $u), (no_c $v), (no_c $w), (no_c $p)` with `$p` in the span, `(no_c $p)` alone is left (*prototype*).
- A chain of atoms with no rule, `(link $0 $2), (link $2 $1)`, is a different answer for every length, in every model that has such chains. It is not removed and should not be.

On the fallback path only the second holds.

### 8.6 Cost

Steps 1 and 3 on a store without store-only variables, and all of 8.3, are polynomial for a fixed theory. An entailment test is a normal form of a smaller store, so a guard costs what simplifying its support costs; an engine that keeps stores normal pays it once per guard and atom. The core is NP-hard and the labelling is as hard as graph canonisation, in the number of store-only variables. That cannot be avoided by a better algorithm: deciding `Span.Equiv` is the equivalence of conjunctive queries, and `Span.covers?` already decides the containment today. The charge derived for L39 is stated in the number of store-only variables, and is polynomial when there are none.

## 9. Coverage

### 9.1 The test

On the fallback path coverage is coverage as written, as today. On a detected theory, for simplified spans `a` and `s`, `covers a s` holds when there is a substitution `ρ` of the variables of `a` with `aρ` having the sides of `s`, the store-only variables of `a` going to subterms of `s`, and `nf (s.c ∪ a.cρ) = s.c` with no binding: the store of `s` entails the instantiated store of `a`. The rest of this section is about that test.

### 9.2 What holds

- *Sound* (*argued*): `covers a s` implies that `a` covers `s` in every model (`CoversLive`). By E3, entailment is sound.
- *Contains coverage as written* (*argued*): `Span.Covers a s` on simplified spans implies `covers a s`, so `NoSubsumed` as stated in `Trusted/Properties.lean` holds for an engine that drops what the test covers.
- *Exact without store-only variables* (*argued*): if `a` has none and `s` is not dead, `covers a s` holds exactly when `a` covers `s` in every model. The model of 5.4 for the store of `s` is the witness. This is the case of every boundary.
- *Not transitive and not kept by composition in general* (*impossible*). With `(A (g k)) <=> .`: `$u {(A $y)} -> $u` covers `$u {(A (g $u))} -> $u`, which covers `k -> k`, and the first does not pass the test against the third, because the witness `(g k)` occurs nowhere in the third. In every model the first does cover the third.

### 9.3 Why no test is exact (*impossible*)

Take any instance of Post's correspondence problem. Let a term built from the tile symbols `t1, …, tn` and `e` stand for a sequence of tiles, and define, for each tile `i` with top word `u` and bottom word `v`, `(top (ti $y) u$w) <=> (top $y $w).` and `(bot (ti $y) v$w) <=> (bot $y $w).`, with `(top e e) <=> .`, `(bot e e) <=> .`, and `(ne (ti $y)) <=> .`. This theory is detected confluent: no two heads overlap, and every body is smaller. The span `$x {(top $y $w), (bot $y $w), (ne $y)} -> $x` relates the same pairs as `$x -> $x` in every model exactly when the instance has a solution. So no algorithm decides equality in every model, or coverage in every model, for spans with store-only variables, and no canonical representative for equality in every model can be computed. The same theory with `top`, `bot` and `ne` closed shows that satisfiability of a store with closed atoms is undecidable.

### 9.4 What this means for the engine theorems

`simplify_mono` as R001 states it (coverage as written is kept by simplification) is false for any simplification that rewrites: `$w {(no_c $w)} -> $w` covers `k {(no_c k)} -> k`, and after simplification it does not cover `k -> k` as written. With the test of 9.1 it does. On the fallback path nothing rewrites and `simplify_mono` is the right obligation, still unproved, as it was for R001.

An engine is generic in the kernel and must be right on both paths, so its proofs may use only what holds on both: coverage in every model is kept by composition, meet and simplification; the test is sound and contains coverage as written. Completeness of an engine needs only that. A halting theorem that needs "a covered candidate has only covered consequences" for the test itself is `simplify_mono` on the fallback path (coverage as written is transitive and kept by composition without simplification), holds on a detected theory on the fragment without store-only variables, and is *open* beyond it.

## 10. The laws the kernel operations satisfy

With `;` and `&` meaning the operation followed by `simplify`. A law holds for every theory when it holds on both paths.

| Law | Fallback path | Exact path (detected theory) |
|---|---|---|
| `simplify` is a function of the span and the theory, and commutes with renaming | argued, prototype | argued (E2), prototype |
| `simplify` is idempotent, and commutes with the converse at the same charge | argued, prototype | argued (E2; no rule sees the sides) |
| `simplify s` relates the same pairs as `s` in every model; it returns nothing only when `s` is dead | argued | argued |
| `canon` is idempotent; `canon (s°) = (canon s)°`, at the same charge | by construction, prototype | by construction, prototype |
| `leftBound s = rightBound (s°)`, both canonical | by definition | by definition |
| `covers` is sound and contains `Span.Covers` | by definition | argued |
| `canon s = canon s'` exactly when the simplified spans are `Span.Equiv` | argued | argued |
| `simplify` returns nothing exactly when the span is dead (no closed atoms) | not promised | argued (E3) |
| `(a ; b) ; c = a ; (b ; c)`, `a & b = b & a`, `(a & b) & c = a & (b & c)`, up to renaming | not promised | argued (E2), prototype |
| spans that are equal in every model and have no store-only variables have one representative | not promised | argued (E3) |
| `covers` is exact when the covering span has no store-only variables | not promised | argued |
| `canon (canon a ; canon b) = canon (a ; b)` | not promised | false in general (8.4); true without step 2 |
| `covers` is transitive | true (coverage as written) | false in general (9.2) |
| `covers` is kept by `;` and `&` | `simplify_mono`, unproved | false in general (9.2) |

`Keeps` carries the first seven rows for every theory, and the next four under the hypothesis that the theory is detected.

## 11. Extending a theory (L10)

Both recorded counterexamples to "adding rules never causes divergence" are extensions that are not detected (*prototype*):

- `(link $x $y) <=> .` with `(link $x $y), bad <=> fail.`: the pair on `{(link $x $y), bad}` gives `{bad}` and `fail`. The extension says `bad` is false without saying it. With `bad <=> fail.` added it is detected.
- `(link $x $y) <=> .` with `(link (f $x) $y) <=> (k $x $y).`: the pair on `{(link (f $x) $y)}` gives `{}` and `{(k $x $y)}`. The two rules disagree about an atom.

So the class of extensions is: **`T ⊆ T'`, both detected confluent, and `T'` adds no case to a predicate that `T` closes.** For that class:

- (*argued*) `nf T' c = nf T' (nf T c)`, because every step of `T` is a step of `T'` (an entailed guard stays entailed) and `T'` is confluent. Composition and meet under `T'` are therefore the images under `nf T'` of composition and meet under `T`. *Prototype* on `ranges` extended by the two rules the conformance findings ask for, `(lt $x $x) <=> fail.` and `(lt $x $y), (lt $y $x) <=> fail.`
- (*argued*) `TheoryMonoAnswers`: every answer under `T'` is the `T'` normal form of an answer under `T`, so it is covered by it in every model of `T'`.
- (*to prove*) Halting is kept when the goals and answers of the run under `T` have no store-only variables: the tables under `T'` are images of the tables under `T`, and on that fragment coverage is exact, so a candidate that was covered stays covered.
- (*open*) Halting with store-only variables in answers. The test of 9.1 can lose a coverage under `T'` that it found under `T`, for the reason in 9.2. No example of divergence is known. The strongest true statement is the third item unless this is settled.

**What detection without enforcement costs here.** An extension that is not detected moves the program from the exact path to the fallback path, and a query that halted can then diverge. The first counterexample above is exactly that: under `(link $x $y) <=> .` alone the link chains halt, and with the `bad` rule added they do not. Nothing is unsound, and reading the extended theory says what happened and shows the pair. This cannot be avoided while confluence is not enforced, and it is why the statement is about detected pairs.

## 12. Defined predicates and what a preprocessor may add (L17, first part)

Automatic coroutining (S22) turns a relation such as `nat = z -> z | [(s $x) -> $x ; nat ; $y -> (s $y)]` into a constraint. With open predicates that is not an equivalence: `(nat z) <=> .` and `(nat (s $x)) <=> (nat $x).` leave `(nat foo)` true in some models, and the relation never relates `foo`. A defined predicate has to be false wherever no case applies.

**Closed predicates.** `constraint p/n closed` adds one axiom: a ground atom of `p` that is an instance of no head of a definition of `p` is false. Together with the rules this is the completed definition of `p`: `p` holds exactly when one of its cases does. Under D5 a closed predicate is defined without guards from closed predicates, so each ground atom of `p` reduces to true or false, and `p` denotes one fixed set of tuples, the same in every model. Both paths get one more refutation (5.1, 5.5), sound for every theory. Closedness adds only `fail` cases on shapes that no head unifies with, so it adds no critical pair, and E1 and E2 hold unchanged.

**Trusted statement.** A *defined predicate* is a closed predicate whose definitions meet D5 and whose pairs join. `Preprocessor.theory_eq` is replaced by: the output theory is the input theory together with definitions of defined predicates whose symbols do not occur in the input program or query. Then:

- (*argued*) every model of the input theory extends in exactly one way to the new predicates (the truth of a closed atom is computed by the recursion of D2), `equiv` is asked over the models of the output theory, and observable pairs are unchanged;
- (*argued*) the output theory is detected exactly when the input theory is. The new symbols occur in no old rule, so no pair has one old and one new rule, and the levels of the old predicates do not change. A preprocessor therefore never moves a program to the fallback path.

Milestone 8 uses the same statement.

**What the rung owes.** With closed atoms in a simplified store, "not refuted" no longer implies "satisfiable", and satisfiability is undecidable (9.3). So an engine that emits a span whose store keeps closed atoms must hold a ground solution of those atoms, found by running the relation they came from. That is an obligation on the rung of L17's second part (M7), not on the rule language, and it is why E3 is stated with the hypothesis it has. Until that rung exists nothing creates a closed predicate except a user who declares one, and the same obligation applies.

`TheoryMonoAnswers` and section 11 exclude adding a case to a closed predicate, because that makes more atoms true.

## 13. The example theories as written

Classified by the prototype, reading the theories from the files. No file is edited.

| Theory | Files | As written |
|---|---|---|
| `eq_neq` (`eq`, `neq`, `nonzero`) | `equality_constraints.txt` | detected confluent |
| `ranges` (`leq`, `lt`, `between`) | `range_sets.txt` | detected confluent |
| `treecalc_constraints` (`no_c`), both versions | `SK`, `program_synth` | detected confluent |
| `depth_constraints` (`depth`) | `ProofSynth` | detected confluent |
| `bound_vars` (`neq`, `var`, `norm`) | `Lambda`, `polysimp` | detected confluent |
| `fresh_constraints` (`fresh`) | `Untitled` | detected confluent; one inert rule noted |
| `lamvar_constraints` (`neq`) | `SimpleLam`, `SubstConstr` | not detected: fallback path; one inert rule noted |

The three differences the first version of this note put to Anthony are gone:

**`nonzero`.** No rule is added. A guard holds by entailment (5.1), the file is detected as written, and the stores of conformance case 2 come out as the findings file asks (*prototype*).

**Duplicate removal.** `(neq $x $y), (neq $x $y) <=> (neq $x $y).` and the same rule for `fresh` stay in the files. They are classified inert, because on a set of atoms they say nothing, and they do not affect detection.

**Symmetry of `neq`.** `(neq $x $y), (neq $y $x) <=> (neq $x $y).` stays in `lamvar_constraints`. It is a definition of `(neq $y $x)` under the guard `(neq $x $y)`, and the guard is not below the atom it guards, so D2 fails and the theory is not detected. That is the right answer and not a weakness of the check: on `{(neq a b), (neq b a)}` the rule has two results, `{(neq a b)}` and `{(neq b a)}`. On the fallback path `(neq $x $x)` is still refuted, and a symmetric pair is kept as two atoms (*prototype*). The relations of `SimpleLam` write each pair in one orientation, the outer binder first, so the answers shown in the notebook do not change. The theory without that one rule is detected. Whether to support a symmetric predicate on the exact path is on the billboard (C1).

Two notebooks have slips that the parser reports, which is not a classification: `Untitled` has `(fresh $x (a $y $z) <=> …` with a parenthesis missing and uses `neq` without declaring it, and `SubstConstr` has an empty `constraint` line.

## 14. Algorithms to write in Rust (L39)

Each is one function on the store of `verified/rust`, translated and proved against its specification here, with its charge derived. Both paths are needed, so the list is longer than in the first version.

| Algorithm | Specification | Notes |
|---|---|---|
| `classify` | 3.3 | one unification per rule |
| `detect` | D1 to D5, and the notes | read once per program; strongly connected components, the size comparison, one `nf` per critical pair |
| `match_heads` | all matchings of a rule's heads into a store | store indexed by predicate; two heads may take one atom; used by both paths |
| `step`, `nf` | 5.1 | exact path; reuses the verified unifier for the equations |
| `entails` | `nf (c ∪ A) = nf c` with no binding | used by guards and by `covers` |
| `closure`, `refutes`, `forced` | 5.5 | fallback path; the closure of `Kernel/Refute.lean` with the two changes of 5.5 |
| `simplify` | `nf` or the fallback, by the classification | one entry point for the kernel |
| `core` | 8.1 step 2 | search over substitutions of store-only variables; nothing to do without them |
| `label`, `canon` | 8.1 steps 3 and 4 | search over labellings of store-only variables; a sort without them |
| `swap` on representatives | flips the bit | one tick |
| `right_bound`, `left_bound` | 8.3 | filter, sort |
| `covers` | 9.1, or coverage as written | matching of the sides, then search over subterms for store-only variables |

Nothing of the closure is deleted. `Theory.saturate`, `refutes?`, `bind?`, `simplifyWithin` and `TRule.bounded` become the fallback path, and `Kernel/SimplifyMono.lean` is its obligation. Their postulated charges are replaced by derived ones like the others.

## 15. What keeps a theory from being detected, and why

None of these is rejected. Each runs on the fallback path.

- **Propagations** (`K ==> atoms`). On the exact path they would need a closure inside the normal form, a bound on what the closure adds, and an argument that adding and removing do not chase each other (`(p $x) ==> (q $x).` with `(q $x) <=> (p $x).` does). No example uses one. The fallback path fires them.
- **Rules that remove two heads.** Not confluent on sets in general (redesign notes, counterexample 1). The fallback path reads them forwards.
- **A guard or body atom that is not below the atom it defines.** Symmetry written as a simplification is the example.
- **Created variables outside the class of D3**, and all of them until the lemma is proved. See section 6.
- **Two rules that give two results**, shown as the store and both results.

## 16. What this asks of other items

1. **Trusted statements of milestone 5 (L48).** A decidable classification of a theory (`Theory.Detected`, D1 to D5) is added. It is not a condition for running a theory, so it does not replace `TRule.WellFormed`; `Valid` and the engines keep whatever they assume of a rule today, and every statement of section 10 marked "detected" takes `Theory.Detected` as a hypothesis. Closed predicates are added to `Theory` and to `Theory.Model`, with the preprocessor's theory condition of section 12. Under roadmap rule 8 these come before the pass that re-proves against them. None of them waits on anything.
2. **The kernel** needs a canonical representative of a span as an operation, with a type of representatives whose converse is the bit flip, and the laws of section 10 as its obligations, split as the table splits them. `simplify_mono` is not among the laws for every theory.
3. **The answer type** (L28) is the type of representatives, and its converse is not `Span.swap` (8.2). The runtime restatement already allows this.
4. **The yardstick port** (milestone 4) proves against the laws that hold on both paths, the first seven rows of section 10. They hold of the closure as it stands, so the port does not wait for the exact path. Its halting theorems for programs with theories are stated per path: on the fallback path they rest on `simplify_mono`, which is unproved, as they did for R001; on a detected theory they hold on the fragment without store-only variables (9.4).
5. **The engine** (milestone 6) and the simulation theorem should read 8.4 and 9.2: on a detected theory the algebra of representatives is exact without the core, and one-sided with it. Where the engine's cost argument needs two bracketings of a derivation to store one answer, it has that on detected theories only.

## 17. Open points

- **O-C1.** Halting theorems on a detected theory when answers have store-only variables (9.4, 11). The question is whether some decidable relation is transitive, kept by composition, and still lets a rewritten store be compared. Section 9.3 rules out an exact one.
- **O-C2.** The lemma of section 6 for created variables.
- **O-C3.** Whether the engine stores representatives with or without the core (8.4).
- **O-C4.** The E2 argument is on paper and tested at random; fact (c), that entailment is kept by steps elsewhere, is proved together with confluence in one induction, and is the part most likely to need care in Lean.
- **O-C5.** `simplify_mono` for the closure, inherited from R001, on which the halting theorems of the fallback path rest.
