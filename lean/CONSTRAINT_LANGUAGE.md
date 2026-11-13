# The constraint rule language

**Superseded on 2026-11-13.** The constraint system is sorts with a built-in disequality (roadmap L48, L51), stated in `RwLog/Trusted/Semantics.lean` and `RwLog/Trusted/Domain.lean`. No rule language is implemented. This note is kept for its analysis, in particular section 8 on canonical representatives and the orientation bit, which the interface follows.

Design note for milestone 5 of the roadmap (L11, L12, L09, L08, L10, canonical spans, L17 first part, and the list of algorithms for L39). Written 2026-11-13. No Lean or Rust is changed by this note. A prototype of everything decided here is `scripts/constraint_language_prototype.py`; run it with no argument, and it checks every example theory and every claim marked *prototype* below.

Each claim carries one of four marks. *Argued*: a proof is given here on paper and is owed in Lean. *Prototype*: the script checks it on the examples. *Open*: not known. *Impossible*: a counterexample or a reduction is given.

## 1. Decisions

1. **A rule defines one atom.** A rule is either a *definition* `K \ r <=> eqs, B` (while the guards `K` are in the store, the atom `r` holds exactly when the equations and the atoms `B` do) or a *restriction* `K ==> eqs` (the atoms `K` together force the equations; `fail` is the equation that never holds). Nothing else is a rule. There are no propagations and no rule that removes two atoms.
2. **The defined atom is above everything its rule mentions**, in an order that needs no annotation. Every rule then fires whenever its heads are present, and firing always ends.
3. **Confluence is decided when the theory is read**, by joining finitely many critical pairs. The check is exact: a theory in the language is rejected exactly when two orders of firing give two results, and the rejection shows the store and both results.
4. **The normal form of a store is what the engine keeps.** `refutes?` is "the normal form is `fail`". For a well-formed theory this is exact in both directions (section 5).
5. **A body variable that no head binds is existential and is created as a store-only variable.** It is admitted only where the check proves that nothing can ever bind it. Outside that class there is a diverging example, so the rule is rejected with the reason (section 6).
6. **A canonical representative is a normal form, reduced to its core, labelled canonically, with one orientation bit.** The converse of a representative flips the bit. A representative in a single name space that commutes with exchanging the two sides does not exist (section 8.2).
7. **Everything is exact on spans without store-only variables**, which includes every boundary and so every table key. For spans with store-only variables, equivalence in every model is undecidable for this language (section 9.3), so the canonical representative is canonical for equivalence as written, and coverage is a sound test.
8. **A defined predicate is a closed predicate**: one declared `closed`, whose atoms are false unless a case of its definition applies. A preprocessor may add closed predicates under new names and nothing else (section 12).
9. **All eleven acceptance theories are in the language.** Four example files change, in three ways; section 13 lists each change for Anthony.

## 2. What the examples use

Read before anything was decided: `examples/equality_constraints.txt`, `examples/range_sets.txt`, and the notebooks `theory_demos`, `SK`, `program_synth`, `program_synthesis`, `ProofSynth`, `Lambda`, `SimpleLam`, `SubstConstr`, `Untitled`, `polysimp` (the other notebooks use no constraints), with `/mnt/project-files/r001/constraint-redesign-notes.md` and the conformance cases.

| What a theory does | Where | In the language as |
|---|---|---|
| Defines a predicate by cases on constructors, recursing on the parts | `eq`, `neq`, `leq`, `lt`, `no_c`, `depth`, `fresh`, `norm`, `between` | definition without guards |
| Declares a shape impossible | `(var (app $x $y)) <=> fail.`, `(neq $x $x) <=> fail.` | definition with body `fail` |
| Lets one constraint decide another | `(norm (app $x $z)), (var $x) <=> (var $x), (norm $z).` and `(norm $x), (var $x) <=> (var $x).` in `Lambda`; the two guarded rules of `nonzero` | definition with guards |
| Forbids a combination | `(eq $x $y), (neq $x $y) <=> fail.` | restriction |
| Removes a second copy of an atom | `(neq $x $y), (neq $x $y) <=> (neq $x $y).` | nothing: a store is a set |
| Makes a predicate symmetric | `(neq $x $y), (neq $y $x) <=> (neq $x $y).` in `SimpleLam`, `SubstConstr` | not expressible (section 13) |

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
    H1, ..., Hn ==> s = t.    # a restriction; the same as writing the heads back
}
```

A body is `fail`, or a list of atoms and equations `s = t`; the empty list is written `.` or `true`. The three ways of writing a rule mean the same thing: `K \ H <=> B`, `H <=> K | B` and `H, K <=> K, B` are one rule. The surface syntax is the one the parser already reads, so the front end stays.

### 3.2 What a rule means

Unchanged from `Trusted/Semantics.lean`: a rule `H1, …, Hn <=> body` holds in an interpretation when, for every ground instance of the head variables, all heads hold exactly when the body holds for some values of its other variables. Rules are two-way axioms. Stores and firing are how an engine computes with them.

### 3.3 How a rule is classified

Let `μ` be the most general unifier of the body's equations. If the body is `fail` or the equations have no unifier, the rule is the restriction `H1, …, Hn ==> fail`. Otherwise a head `h` is *kept* when `hμ` is an atom of the body under `μ`, and *removed* otherwise.

- No removed head and no atom in the body beyond the kept heads: the restriction `K ==> eqs`. If the equations hold already, the rule says nothing and is rejected.
- No removed head and further body atoms: a propagation. Rejected (section 15).
- One removed head `r`: the definition `K \ r <=> eqs, B`, where `B` is the body without the kept heads.
- Two or more removed heads: rejected. Such a rule states that a conjunction is equivalent to something, and on a set of atoms it cannot be fired without losing consequences (redesign notes, counterexample 1). The same axiom is written as a definition of the body atom from the heads.

So `(pin $x) <=> $x = z, (pin z).` is the restriction `(pin $x) ==> $x = z`, and `(pin $x) <=> $x = z.` is the definition of `(pin $x)` by an equation and nothing else.

## 4. Well-formedness

A theory is well formed when all six conditions hold. Each is decidable, and each rejection names a rule and a reason. This check replaces `TRule.WellFormed` and `TRule.bounded`.

**W1. Shape.** Every rule is a definition or a restriction (3.3). Every variable of an equation occurs in a head.

**W2. Order.** Say that predicate `p` *mentions* `q` when a definition of a `p` atom has a `q` atom among its guards or in its body. For a definition `K \ r <=> eqs, B` and every atom `x` of `K` and `B`: either the predicate of `r` mentions that of `x` and not the other way round, however long the chain; or `xμ` is smaller than `rμ` under every substitution (fewer symbols, and no variable more often). No annotation is needed: the levels are the strongly connected components of "mentions".

This is weaker than the old boundedness. `(r $x) <=> (t $x).` was never fired by the closure design because its body is not smaller than its head; here it is accepted, because `r` mentions `t` and `t` does not mention `r`.

**W3. Created variables.** A body atom `b` with a variable that no head binds must have a predicate strictly below the defined one, and no predicate that `b`'s predicate mentions, at any distance or itself, may be a head of a rule that has an equation (section 6).

**W4. Critical pairs.** For every definition `ρ1` with removed atom `r1`, every rule `ρ2`, and every head `h` of `ρ2` (kept or removed) that unifies with `r1` after renaming apart: take the store made of all heads of both rules under the unifier, fire each rule once on it, and compare the normal forms of the two results, up to the names of created variables. They must be the same. A rule is also compared with itself, since two instances of its guards can define the same atom.

**W5. Liveness.** For every rule that is not a `fail` restriction, the store made of its own heads is not refuted by the other rules. A rule that fails this could only fire on a store that nothing satisfies.

**W6. Closed predicates.** A definition of a closed predicate has no guards and its body atoms are closed.

The rejections are meant to be read. For `equality_constraints.txt` as written the prototype prints:

```
critical pair on {(eq z z), (nonzero z)}
    (eq $x $x) <=> .                      gives {(nonzero z)}
    (nonzero $x) <=> (eq $x z) | fail.    gives fail
```

which says that the theory makes `(nonzero z)` false and no rule says so. Adding `(nonzero z) <=> fail.` joins the pair. In every case found in the examples and the recorded counterexamples, the store of the failing pair is the rule that is missing.

## 5. Firing, normal forms and exactness

### 5.1 One step

A store is a finite set of atoms over the variables of its span. Its variables are rigid: a head matches an atom one way only. Two heads may match the same atom.

- A definition `K \ r <=> eqs, B` with its heads matched by `σ`: solve the equations under `σ`. No unifier: the store is refuted. A unifier `θ`: remove `rσ`, add `Bσ` with a new variable for each created variable, and apply `θ` to the whole span.
- A restriction `K ==> eqs` with its heads matched: the same, with nothing removed or added. A step that changes neither the span nor the store is not a step.
- An atom of a closed predicate that unifies with no head of a definition of that predicate refutes the store.

The normal form `nf T c` is the result when no step applies: `fail`, or a store with the substitution its equations forced. `Theory.simplify` is `nf` applied to a span, and `Theory.refutes? T c` is `nf T c = fail`. `Theory.saturate`, `bind?`, `present` and `normalize` are deleted: there is no longer a difference between the store an answer carries and the store it is shown with.

### 5.2 E1: firing ends (*argued*)

Order atoms by level and then by size, and stores by the multiset extension. A definition replaces `r` by atoms that are lower by W2, so every step without a binding lowers the store. A binding replaces a variable that is not created by a term over variables already present, so it lowers the number of such variables, and by W3 a created variable is never bound. The pair (number of variables that can be bound, store) falls at every step.

### 5.3 E2: every order of firing gives the same normal form (*argued, prototype*)

**Statement.** For a well-formed theory, `nf T c` does not depend on the order of steps, up to the names of created variables. Further, `nf (nf A ∪ B) = nf (A ∪ B)` and `nf (cγ) = nf ((nf c)γ)` for every substitution `γ`.

**Why sets need care.** On multisets, a step in a store is a step in every larger store, and joinable critical pairs give confluence by the usual argument. On sets that is false: if a step removes `a` and a later step produces `a` again, a larger store that already held `a` loses it. Counterexample 1 of the redesign notes is this effect with a rule that removes two heads.

**Argument.** Induction on the store in the order of E1. Two steps from one store either overlap, in which case they are an instance of a critical pair inside a larger store, or they do not. Two facts carry the proof.

(a) *A step lifts to a larger store up to one more step of the same rule.* If `S` steps to `S'` by removing `a`, and `C` is any set, then `S ∪ C` steps to `S' ∪ (C \ {a})`, and `S' ∪ C` either is that store or steps to it by the same instance, because the guards of the instance are kept in `S'`. So along any derivation `S0, S1, …, Sn`, the stores `Sj ∪ C` all have the same normal form, by the induction hypothesis, since all of them are below `S0 ∪ C` from `j = 1` on.

(b) *The same holds for instances*: a step on `S` gives a step on `Sγ`, up to one more step of the same instance when `γ` identifies the removed atom with another one. A substitution that does not agree with a binding refutes the instance, and it refutes it on the other side of a joined pair too, because both sides end with the same forced substitution.

With (a) and (b), a joinable critical pair is joinable in every larger store and every instance, and non-overlapping steps commute up to one repeated step. Newman's lemma on the well-founded order gives uniqueness, and (a) gives the two equations. What makes (a) true is that a definition removes one atom and keeps its guards. With two removed heads it fails.

The prototype runs 400 random stores for each of the eleven accepted theories with three random orders each, and compares `nf (nf A ∪ B)` with `nf (A ∪ B)`. On two theories that fail W4 the same test finds two normal forms.

### 5.4 E3: refutation is exact (*argued*)

**Statement.** Let `T` be well formed and `c` a store with no atom of a closed predicate left in its normal form. Then `nf T c = fail` exactly when no model of `T` contains a ground instance of `c`. If `nf T c = (θ, c')`, then in every model the ground instances of `c` that hold are exactly the instances of `θ` under which `c'` holds.

**Sound direction.** Each step preserves the instances that hold in each model. For a definition this is the rule's axiom read in both directions with the guards present. `Fire.sound` is the forward half today.

**Complete direction.** Let `S` be the normal form with each variable replaced by a distinct symbol that occurs nowhere in the theory (the signature is open, so there always is one). `S` is still normal, because a head cannot tell such a symbol from a rigid variable. Let `M` be the set of ground atoms that occur in some finite set `A` with `nf (S ∪ A) = S`. Then `S ⊆ M`, and `M` is a model:

- Two entailed sets are entailed together, by `nf (nf X ∪ Y) = nf (X ∪ Y)`.
- If the heads of an instance of a definition are in `M`, take `A` containing them. The instance fires on `S ∪ A`, the equations hold (otherwise the normal form would be `fail`), and the result still has normal form `S`, so the guards and the body are in `M`. Conversely, if the guards and body are in `M` and the equations hold, add the defined atom: the instance fires and gives back a store whose normal form is `S`, so the atom is in `M`.
- If the heads of a restriction are in `M` and its equations fail, the normal form of `S ∪ A` would be `fail`.

So some model contains an instance of `c`. The proof uses E2 and nothing else. In particular it does not need the guards to be "really" true anywhere: the critical pairs are what guarantee that a guard which the theory can derive has already had its effect. That is exactly the difference between `(nonzero z)` being refuted or silently kept in section 4.

**With closed predicates** the argument stops, because an unknown symbol under a closed predicate is false. A store whose normal form keeps closed atoms is satisfiable exactly when those atoms have a ground solution that leaves the rest unrefuted, and that is undecidable (9.3). Section 12 says what an engine owes in that case. No example theory has a closed predicate.

## 6. Body variables that no head binds (L12)

**Meaning.** As the trusted semantics already says: existential. `(even $x) <=> (double $h $x).` says `(even a)` holds exactly when `(double h a)` holds for some `h`.

**Firing.** The rule fires like any other. The variable becomes a new store-only variable of the span, which is already how the span semantics reads a variable that occurs only in a store.

**The complication.** With equations in reach, firing can run for ever on a store that has no solution (*impossible* to admit in general):

```
(a (f $x)) <=> (a $x), (b $x).
(b $x)     <=> (c $y $x).
(c $y $x)  <=> $x = (f $y), (d $y).
```

Every rule passes W1 and W2. On `{(a $v), (b $v)}` the second rule creates `$y`, the third binds `$v` to `(f $y)`, the first peels the `f` and asks `(b $y)` again. The store forces `$v` to be an infinite term, so it has no instance, and firing never says so. A language that admits this has no exact `refutes?`. The same happens when the created variable is in the equation itself, as in `(nat $x) <=> $x = (s $y), (nat $y).`

**The class that is admitted.** W3: a created variable only ever occurs in atoms whose predicates, and everything below them, are never heads of a rule with an equation. Then nothing can bind it, it stays rigid for the whole life of the span, and E1 holds as argued. `(even $x) <=> (double $h $x).` with `double` defined by cases is accepted (*prototype*).

**What is owed before the class is in.** Anthony's condition is that created variables are allowed only if proved free of complications. E1 is argued above. E2 and E3 need one more lemma, because a created variable leaves a copy behind: `{(even a), (double b a)}` becomes `{(double $h a), (double b a)}`, which equals `{(double b a)}` only after the core is taken. So E2 and E3 for theories with created variables are stated up to the core on created variables, and the lemma owed is that the core on created variables is kept by every later step (created variables are rigid and never bound, which is why this is expected to hold where the general statement of 8.4 does not). If that lemma fails in Lean, W3 becomes "no created variables", which changes no example. Until it is proved, the Lean of milestone 5 uses the stricter W3.

## 7. No silent rule, no dead answer (L09)

- **No rule is skipped.** The run-time side condition `TRule.bounded` is gone. A rule of a well-formed theory fires whenever its heads are in the store.
- **No rule is dead.** W5 rejects a rule whose heads cannot hold together, and 3.3 rejects a rule that says nothing. Both are read-time errors that name the rule.
- **No rule is lost to the order.** A rule that the old order could not use is now either accepted by levels or rejected with the cycle shown.
- **No dead answer.** An engine emits only simplified spans. By E3 a simplified span without closed atoms relates a pair in some model.

## 8. Canonical representatives (L08)

### 8.1 Definition

For a span `s`:

1. *Normal form.* `simplify T s`.
2. *Core.* Remove atoms from the store as long as a substitution of store-only variables maps the store into what is left. The result is unique up to renaming (Chandra and Merlin).
3. *Label.* Name the variables of `l` in order of first occurrence, then the remaining variables of `r`, then the store-only variables by the labelling that makes the sorted list of atoms least in a fixed structural order. The last step is a search over labellings, not a first-occurrence order.
4. *Orient.* Label `s` and its converse as in step 3 and compare the two results with the one structural comparison of the base machine. Keep the smaller one and a bit that says which it was. If they are equal the span is its own converse and the bit is 0.

The representative is the pair of the bit and the labelled span. **The converse of a representative flips the bit**, and leaves a self-converse representative alone. So `canon (s°) = (canon s)°` holds by construction (*prototype*), `canon s` and `canon (s°)` do the same work (two labellings and one comparison that reads both arguments), and the converse of a representative costs one tick. `canon s = canon s'` exactly when the simplified spans are `Span.Equiv` (*argued*: step 2 is the classical theorem, steps 3 and 4 are canonical by construction).

### 8.2 No representative in one name space commutes with exchanging sides (*impossible*)

Take `s = (f $v $w) -> (f $w $v)`. Exchanging its sides gives `(f $w $v) -> (f $v $w)`, which is `s` with its two variables renamed. A canonical representative gives both the same value `L -> R`. Commuting with the exchange gives `L -> R = R -> L`, so `L = R`, so the two variables are one, and the result no longer stands for `s`. This is why the representative carries a bit and why the answer type of the engine (L28) needs its own converse. The freeze list's row is met in that form.

### 8.3 Interfaces

`rightBound s` is the canonical representative of `r {c'} -> r`, where `c'` holds the atoms of the simplified store all of whose variables occur in `r`. `leftBound s` is `rightBound (s°)`. A subset of a normal store is normal, so nothing is fired. A boundary has no store-only variable, so its core is itself, its labelling is a sort, and its representative is computed in polynomial time. A boundary is its own converse.

The freeze list says a boundary carries "the part of the store that mentions its variables". This note reads that as the atoms that mention only its variables, as `storeOn` does today. An atom that also mentions another variable could be carried with that variable existential. That is a tighter boundary and puts store-only variables into table keys, which is where exactness ends. It is on the billboard and is not chosen.

### 8.4 What the core is not (*impossible*, *prototype*)

`Span.Equiv` is not kept by simplification. In the theory `(p z) <=> . (p (f $x)) <=> fail.`, the spans `$w {(p z)} -> $w` and `$w {(p z), (p $y)} -> $w` are equivalent as written and simplify to `$w -> $w` and `$w {(p $y)} -> $w`, which are not (redesign notes, counterexample 3). The same happens after the fact: `$l {(no_c $y), (no_c $w)} -> $w` has core `$l {(no_c $w)} -> $w`, and composing each with `@k` gives `$l {(no_c $y)} -> k` and `$l -> k`.

The cause is always the same. The core maps a store-only variable to a term, and a later step rewrites the atom that held the term, so the witness is gone while the variable stays. The two results are equal in every model, and the one that came from the core covers the other. They are not equivalent as written.

So three statements have to be kept apart:

- `canon s = canon s'` exactly when the simplified spans are equivalent as written. True.
- Composition followed by simplification is associative, and meet is commutative and associative, up to renaming, when no core is taken in between. True by E2 (*argued, prototype*). This is the roadmap's criterion and it holds exactly, not only up to `Span.Equiv`.
- Replacing an answer by its canonical representative and continuing gives the canonical representative of the result. **False** when a store-only variable's witness is later rewritten away. The two results agree in every model, and one covers the other.

Consequence for milestone 6: two strategies that reach one answer through different splits store one representative, except in that case, where they can store two answers of which one covers the other. Nothing is unsound and no answer is lost. If the engine needs the third statement exactly, it gets it by leaving step 2 out (representatives up to renaming compose exactly, *prototype*) and letting coverage remove the redundant answers. That choice belongs to the engine and is on the billboard. Table keys are not affected: boundaries have no store-only variables.

### 8.5 Stores along a recursion

- An atom the theory makes true is removed by the normal form. With `(link $x $y) <=> .`, the answers of `r = $0 {(link $0 $1)} -> $1 | r ; r` are all `$0 -> $1`, and the query halts (*prototype* for `r ; r`).
- Copies of one atom on different store-only variables are removed by the core: of `(no_c $u), (no_c $v), (no_c $w), (no_c $p)` with `$p` in the span, `(no_c $p)` alone is left (*prototype*).
- A chain of atoms with no rule, `(link $0 $2), (link $2 $1)`, is a different answer for every length, in every model that has such chains. It is not removed and should not be.

### 8.6 Cost

Steps 1 and 3 on a store without store-only variables, and all of 8.3, are polynomial. The core is NP-hard and the labelling is as hard as graph canonisation, in the number of store-only variables. That cannot be avoided by a better algorithm: deciding `Span.Equiv` is the equivalence of conjunctive queries, and `Span.covers?` already decides the containment today. The charge derived for L39 is stated in the number of store-only variables, and is polynomial when there are none.

## 9. Coverage

### 9.1 The test

For simplified spans `a` and `s`, `covers a s` holds when there is a substitution `ρ` of the variables of `a` with `aρ` having the sides of `s`, the store-only variables of `a` going to subterms of `s`, and `nf (s.c ∪ a.cρ) = s.c` with no binding: the store of `s` entails the instantiated store of `a`.

### 9.2 What holds

- *Sound* (*argued*): `covers a s` implies that `a` covers `s` in every model (`CoversLive`). By E3, entailment is sound.
- *Contains coverage as written* (*argued*): `Span.Covers a s` on simplified spans implies `covers a s`, so `NoSubsumed` as stated in `Trusted/Properties.lean` holds for an engine that drops what the test covers.
- *Exact without store-only variables* (*argued*): if `a` has none and `s` is not dead, `covers a s` holds exactly when `a` covers `s` in every model. The model of 5.4 for the store of `s` is the witness. This is the case of every boundary.
- *Not transitive and not kept by composition in general* (*impossible*). With `(A (g k)) <=> .`: `$u {(A $y)} -> $u` covers `$u {(A (g $u))} -> $u`, which covers `k -> k`, and the first does not pass the test against the third, because the witness `(g k)` occurs nowhere in the third. In every model the first does cover the third.

### 9.3 Why no test is exact (*impossible*)

Take any instance of Post's correspondence problem. Let a term built from the tile symbols `t1, …, tn` and `e` stand for a sequence of tiles, and define, for each tile `i` with top word `u` and bottom word `v`, `(top (ti $y) u$w) <=> (top $y $w).` and `(bot (ti $y) v$w) <=> (bot $y $w).`, with `(top e e) <=> .`, `(bot e e) <=> .`, and `(ne (ti $y)) <=> .`. This theory is well formed: no two heads overlap, and every body is smaller. The span `$x {(top $y $w), (bot $y $w), (ne $y)} -> $x` relates the same pairs as `$x -> $x` in every model exactly when the instance has a solution. So no algorithm decides equality in every model, or coverage in every model, for spans with store-only variables, and no canonical representative for equality in every model can be computed. The same theory with `top`, `bot` and `ne` closed shows that satisfiability of a store with closed atoms is undecidable.

### 9.4 What this means for the engine theorems

`simplify_mono` as R001 states it (coverage as written is kept by simplification) is false for any simplification that rewrites: `$w {(no_c $w)} -> $w` covers `k {(no_c k)} -> k`, and after simplification it does not cover `k -> k` as written. With the test of 9.1 it does. What is true for the new operations is: coverage in every model is kept by composition, meet and simplification, always; the test decides it when the covering span has no store-only variables; and the test can miss it otherwise. Completeness of an engine needs only the first. A halting theorem that needs "a covered candidate has only covered consequences" for the test itself holds on the fragment without store-only variables and is *open* beyond it.

## 10. The laws the kernel operations satisfy

For a well-formed theory, with `;` and `&` meaning the operation followed by `simplify`:

| Law | Status |
|---|---|
| `simplify` is idempotent, and commutes with the converse | argued (E2; no rule sees the sides) |
| `(a ; b) ; c = a ; (b ; c)`, `a & b = b & a`, `(a & b) & c = a & (b & c)`, up to renaming | argued (E2), prototype |
| `simplify` returns nothing exactly when the span is dead (no closed atoms) | argued (E3) |
| `simplify s` relates the same pairs as `s` in every model | argued |
| `canon s = canon s'` exactly when `simplify s` and `simplify s'` are `Span.Equiv` | argued |
| `canon (s°) = (canon s)°`, at the same charge | by construction, prototype |
| `leftBound s = rightBound (s°)`, both canonical | by definition |
| `covers` is sound, contains `Span.Covers`, and is exact when the covering span has no store-only variables | argued |
| `canon (canon a ; canon b) = canon (a ; b)` | false in general (8.4); true without step 2 |
| `covers` is transitive and kept by `;` | false in general (9.2) |

## 11. Extending a theory (L10)

Both recorded counterexamples to "adding rules never causes divergence" are theories that W4 rejects (*prototype*):

- `(link $x $y) <=> .` with `(link $x $y), bad <=> fail.`: the pair on `{(link $x $y), bad}` gives `{bad}` and `fail`. The extension says `bad` is false without saying it. With `bad <=> fail.` added it is well formed.
- `(link $x $y) <=> .` with `(link (f $x) $y) <=> (k $x $y).`: the pair on `{(link (f $x) $y)}` gives `{}` and `{(k $x $y)}`. The two rules disagree about an atom.

So the class of extensions is: **`T ⊆ T'`, both well formed, and `T'` adds no case to a predicate that `T` closes.** For that class:

- (*argued*) `nf T' c = nf T' (nf T c)`, because every step of `T` is a step of `T'` and `T'` is confluent. Composition and meet under `T'` are therefore the images under `nf T'` of composition and meet under `T`. *Prototype* on `ranges` extended by the two rules the conformance findings ask for, `(lt $x $x) <=> fail.` and `(lt $x $y), (lt $y $x) <=> fail.`
- (*argued*) `TheoryMonoAnswers`: every answer under `T'` is the `T'` normal form of an answer under `T`, so it is covered by it in every model of `T'`.
- (*to prove*) Halting is kept when the goals and answers of the run under `T` have no store-only variables: the tables under `T'` are images of the tables under `T`, and on that fragment coverage is exact, so a candidate that was covered stays covered.
- (*open*) Halting with store-only variables in answers. The test of 9.1 can lose a coverage under `T'` that it found under `T`, for the reason in 9.2. No example of divergence is known. The strongest true statement is the third item unless this is settled.

## 12. Defined predicates and what a preprocessor may add (L17, first part)

Automatic coroutining (S22) turns a relation such as `nat = z -> z | [(s $x) -> $x ; nat ; $y -> (s $y)]` into a constraint. With open predicates that is not an equivalence: `(nat z) <=> .` and `(nat (s $x)) <=> (nat $x).` leave `(nat foo)` true in some models, and the relation never relates `foo`. A defined predicate has to be false wherever no case applies.

**Closed predicates.** `constraint p/n closed` adds one axiom: a ground atom of `p` that is an instance of no head of a definition of `p` is false. Together with the rules this is the completed definition of `p`: `p` holds exactly when one of its cases does. By W6 a closed predicate is defined without guards from closed predicates, so each ground atom of `p` reduces to true or false, and `p` denotes one fixed set of tuples, the same in every model. Firing gets one more step (5.1). Closedness adds only `fail` cases on shapes that no head unifies with, so it adds no critical pair, and E1 and E2 hold unchanged.

**Trusted statement.** A *defined predicate* is a closed predicate. `Preprocessor.theory_eq` is replaced by: the output theory is the input theory together with rules for closed predicates whose symbols do not occur in the input program or query, and the output theory is well formed. Then every model of the input theory extends in exactly one way to the new predicates (*argued*: the truth of a closed atom is computed by the recursion of W2), `equiv` is asked over the models of the output theory, and observable pairs are unchanged. Milestone 8 uses the same statement.

**What the rung owes.** With closed atoms in a simplified store, "not refuted" no longer implies "satisfiable", and satisfiability is undecidable (9.3). So an engine that emits a span whose store keeps closed atoms must hold a ground solution of those atoms, found by running the relation they came from. That is an obligation on the rung of L17's second part (M7), not on the rule language, and it is why E3 is stated with the hypothesis it has. Until that rung exists nothing creates a closed predicate except a user who declares one, and the same obligation applies.

`TheoryMonoAnswers` and section 11 exclude adding a case to a closed predicate, because that makes more atoms true.

## 13. The example theories in the language

Checked by the prototype, reading the theories from the files.

| Theory | Files | Result |
|---|---|---|
| `ranges` (`leq`, `lt`, `between`) | `range_sets.txt` | accepted as written |
| `treecalc_constraints` (`no_c`), both versions | `SK`, `program_synth` | accepted as written |
| `depth_constraints` (`depth`) | `ProofSynth` | accepted as written |
| `bound_vars` (`neq`, `var`, `norm`) | `Lambda`, `polysimp` | accepted as written |
| `eq_neq` (`eq`, `neq`, `nonzero`) | `equality_constraints.txt` | accepted with difference 1 |
| `lamvar_constraints` (`neq`) | `SimpleLam`, `SubstConstr` | accepted with differences 2 and 3 |
| `fresh_constraints` (`fresh`) | `Untitled` | accepted with difference 3 |

**Difference 1: `nonzero` needs its two cases written out.** A guard is an atom that is in the store. The file's rules `(nonzero $x) <=> (eq $x z) | fail.` and `(nonzero $x) <=> (neq $x z) | true.` are kept, and two rules are added: `(nonzero z) <=> fail.` and `(nonzero (s $x)) <=> .` Without them the check rejects the theory and names exactly these two (section 4). With them every answer of conformance case 2 comes out as the findings file asks: `(nonzero z)` is refuted, `(nonzero (s z))` leaves no residue, `(nonzero $x)` stays, and it is dropped when `(neq $x z)` is in the store (*prototype*). The alternative, a guard that fires when the theory can derive it, was not taken: it needs a second notion of firing inside the first, and the critical pairs already force the theory to say what such a guard would have derived.

**Difference 2: `neq` cannot be declared symmetric.** `(neq $x $y), (neq $y $x) <=> (neq $x $y).` says that `neq` is symmetric. As a rule that removes an atom it has two results on `{(neq a b), (neq b a)}`, and no order puts one orientation below the other. The rule is dropped, so `(neq a b)` and `(neq b a)` are two atoms. The relations of `SimpleLam` write each pair in one orientation (the outer binder first), so the answers shown in the notebook are unchanged; a symmetric pair, if one arises, is kept as two atoms. Supporting symmetric predicates needs propagation or a declared symmetry, and is on the billboard.

**Difference 3: rules that remove a duplicate are deleted.** `(neq $x $y), (neq $x $y) <=> (neq $x $y).` and the same rule for `fresh` say nothing when a store is a set. The check rejects them as rules that say nothing.

Two notebooks also have slips that any parser rejects: `Untitled` has `(fresh $x (a $y $z) <=> …` with a parenthesis missing and uses `neq` without declaring it, and `SubstConstr` has an empty `constraint` line.

Not required, and accepted if added: the two refutation rules for `lt` that the conformance findings mention.

## 14. Algorithms to write in Rust (L39)

Each is one function on the store of `verified/rust`, translated and proved against its specification here, with its charge derived.

| Algorithm | Specification | Notes |
|---|---|---|
| `classify` | 3.3 | one unification per rule |
| `check_theory` | W1 to W6 | read once per program; strongly connected components, the size comparison, one `nf` per critical pair |
| `match_heads` | all matchings of a rule's heads into a store | store indexed by predicate; two heads may take one atom |
| `step`, `nf` | 5.1 | reuses the verified unifier for the equations; `refutes?` and `simplify` are `nf` |
| `entails` | `nf (c ∪ A) = c` with no binding | used by `covers` |
| `core` | 8.1 step 2 | search over substitutions of store-only variables; nothing to do without them |
| `label`, `canon` | 8.1 steps 3 and 4 | search over labellings of store-only variables; a sort without them |
| `swap` on representatives | flips the bit | one tick |
| `right_bound`, `left_bound` | 8.3 | filter, sort |
| `covers` | 9.1 | matching of the sides, then search over subterms for store-only variables |

Deleted with their postulated charges: `Theory.saturate`, `Theory.refutes?` as a separate search, `bind?`, `simplifyWithin`, `present`, `normalize`, `TRule.bounded`, and `Kernel/SimplifyMono.lean` as it stands.

## 15. What is left out, and why

- **Propagations** (`K ==> atoms`). They need a closure instead of a normal form, a bound on what the closure adds, and an argument that adding and removing do not chase each other (`(p $x) ==> (q $x).` with `(q $x) <=> (p $x).` does). No example uses one. Symmetric predicates are the first use that would justify them.
- **Rules that remove two heads.** Not confluent on sets in general (counterexample 1), and every such axiom can be written as a definition.
- **Guards that fire when derivable.** See difference 1.
- **Equations that create variables.** See section 6.

## 16. What this asks of other items

1. **Trusted statements change in milestone 5**: well-formedness of a theory (W1 to W6 in place of `TRule.WellFormed`), closed predicates in `Theory` and in `Theory.Model`, and the preprocessor's theory condition. Under roadmap rule 8 these come before the pass that re-proves against them, so before or with milestone 4's port.
2. **The kernel** (`Trusted/Kernel.lean`, being restated now) needs a canonical representative of a span as an operation, with a type of representatives whose converse is the bit flip, and the laws of section 10 as its obligations. `simplify_mono` is not among them.
3. **The answer type** (L28) is the type of representatives, and its converse is not `Span.swap` (8.2).
4. **The yardstick port** (milestone 4) should prove against the laws of section 10 and not against the closure algorithm, which milestone 5 deletes. Its halting theorems for programs with theories rest on `simplify_mono`; section 9.4 says what replaces it.
5. **The engine** (milestone 6) and the simulation theorem should read 8.4 and 9.2: the algebra of representatives is exact without the core, and one-sided with it.

## 17. Open points

- **O-C1.** Halting theorems when answers have store-only variables (9.4, 11). The question is whether some decidable relation is transitive, kept by composition, and still lets a rewritten store be compared. Section 9.3 rules out an exact one.
- **O-C2.** The lemma of section 6 for created variables.
- **O-C3.** Whether the engine stores representatives with or without the core (8.4).
- **O-C4.** The E2 argument is on paper and tested at random; the Lean proof of fact (a) for instances and for bindings together is the part most likely to need care.
