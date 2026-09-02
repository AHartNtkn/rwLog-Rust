# Rethinking rwlog: relations, constraints, and superposition

Status: design memo, not a plan of record. Written after re-reading the
graphical relational calculus paper (April 2025 draft), the current engine
(`kernel/`, `work/`, `chr/`, `node.rs`), and the example programs.

The two dissatisfactions under examination:

1. Constraints (CHR) feel bolted on. Is the "true" language relational, or is
   it a constraint language in which relations are redundant?
2. Sharing. The `Or`-spine / eager-distribution representation seems wrong
   next to labeled superposition (interaction calculus / HVM). Is there a
   coherent algebraic account, possibly via negation and Peircean duality?

The short version of the conclusions:

* Both dichotomies in (1) are false. Constraints and constructors are the same
  kind of thing (generators of a hypergraph), and the relational calculus is
  the wiring between them. What is currently "tacked on" is not constraints
  but the fact that the two kinds of generator have two separate solvers and a
  substitution-shaped seam between them. The real distinction the language
  needs is *generate* vs *residuate*, which is an evaluation mode, not a
  syntactic category.
* Labeled superposition has a precise relational meaning: a union whose choice
  is a named existential variable of finite type. Two superpositions with the
  same label share that variable. That single idea explains why unlabeled
  "disjunction nodes" never got a coherent semantics, why `R;(S∩T) ≠ R;S ∩ R;T`
  blocks lazy distribution today, and why named superpositions matter for
  efficient evaluation.
* The two problems meet: choice labels are finite-domain constraint variables,
  and a failed coordinate of a superposition is a negative constraint on its
  label. The constraint store is exactly the right mechanism to propagate it.
* Negation earns its place only at the atomic level (disequality on terms,
  exclusion on choices). Peircean cuts of depth two or more mean universal
  quantification over the Herbrand universe, which is not something to build
  an evaluator around.

The rest of this document argues each point and ends with what it would mean
for the Rust codebase.

---

## 1. What rwlog is, algebraically, today

A span with a guard, `{p} s -> t`, denotes

```
{ (s', t') | ∃θ. s[θ] = s' ∧ t[θ] = t' ∧ p[θ] }
```

Read as a hypergraph (paper §3.1–3.2, and the "constraint ring" idea in §3.6):

* one node per constructor occurrence, arity `n+1` (result port plus args);
* one equality (Frobenius) node per variable with more than one occurrence;
* one node per constraint atom in `p`, with one port per argument;
* wires are variables; the two boundary ports are the roots of `s` and `t`.

This is a conjunctive query over the signature `Σ_ctor ∪ Σ_pred`. Composition
is wiring plus existential quantification of the internal wire; intersection
is copy-then-merge on both boundary ports; converse is relabeling which
boundary port is "first". The paper's §3 already says this for the
constructor part. The point to add is that the constraint atoms are *not a
different kind of object*. They are more nodes in the same graph.

The algebraic home for this is the free cartesian bicategory of relations on a
signature (Carboni–Walters), which Bonchi, Seeber and Sobociński showed is
exactly the equational theory of conjunctive-query containment ("Graphical
Conjunctive Queries", CSL 2018). Its string diagrams are hypergraphs and its
laws are the Frobenius laws plus lax naturality of copy/delete. rwlog's
conjunctive fragment (`;`, `&`, spans, fresh variables) is this structure and
nothing more.

### 1.1 Constructors are constraints with a complete theory

The kernel's matching rules are the axioms of the Herbrand constructor theory
stated as graph rewrites:

| kernel behaviour | equation on the graph |
|---|---|
| `f(x̄) = f(ȳ)` decomposes to `x̄ = ȳ` | `f ; f°  =  id` on args (injectivity) |
| `f(x̄) = g(ȳ)` fails, `f ≠ g` | `f° ; g  =  0` (disjointness) |
| `x = f(..x..)` fails | acyclicity / occurs check |
| copy of a constructed term = construct copies | `f ; copy  =  (copy ⊗ … ) ; (f ⊗ f)` (`f` is a map) |

These are the four rewrite rules of paper §3.2 (fuse equality nodes, duplicate
`f` through equality, annihilate `f`/`f`, fail on `f`/`g`). They are also
precisely the rules you would write as CHR simplifications for a predicate
`eq/2` over a free term algebra, which is why the `eq_neq` example theory in
`examples/equality_constraints.txt` looks the way it does. "Unifiability is a
constraint" is therefore literally true: the constructor theory is CLP(H), the
Herbrand constraint domain, and the kernel is its solver.

What makes constructors special is not their kind but their theory: it is
terminating, confluent, decidable, and yields most-general solutions. That is
what lets rwlog present answers as spans, i.e. as patterns that *cover* a
solution set. A user predicate like `neq` or `no_c` has no such normal form,
so it stays in the answer as a residual. This is the only asymmetry between
constructors and predicates that the design needs to preserve, and it is a
property of the theory, not of the syntax.

### 1.2 What CHR actually is in this picture

A CHR simplification rule `(no_c (b $x)) <=> (no_c $x)` is a rewrite between a
predicate node `no_c` and a constructor node `b` that are connected by a wire.
That is an interaction-net rule: two agents meeting on a principal port. A
multi-head rule `(eq $x $y), (neq $x $y) <=> fail` is a rewrite on two
predicate nodes sharing two wires; that is not an interaction-net rule (it
needs a two-node left-hand side) but it is an ordinary DPO hypergraph rewrite.
`$x = $y` in a body is a rewrite that emits a Frobenius node.

So the current architecture is one rewrite system split across two engines:

* `kernel/compose.rs`, `kernel/meet.rs`, `matching.rs` rewrite the constructor
  sub-hypergraph, eagerly, with a fixed rule set;
* `chr/` rewrites the predicate sub-hypergraph, on `normalize`, with a
  user rule set;
* `ConstraintOps::normalize -> (Self, Option<Subst>)`, `apply_subst`,
  `remap_vars`, and the AGENTS.md rule "if a variable is fully instantiated
  the instance gets substituted into the constraint" are the seam: they move
  information across the boundary between the two engines by converting graph
  structure to substitutions and back.

That seam is the "tacked on" feeling. It is not a sign that constraints are
wrong. It is a sign that two rewriters are doing one job.

### 1.3 What constraints do that relations cannot, precisely

The examples use constraints for: `no_c` (prune synthesised programs that
contain holes), `neq` between variables used as object-level names, `norm`
(reject non-normal terms), `lt`/`leq`/`between`. Every one of these is
*definable as a relation*. `no_c` is the identity restricted to hole-free
terms:

```
noC = (l -> l)
    | ((b $x) -> $x ; noC ; $x -> (b $x))
    | (... f case with & ...)
```

and `noC ; app ; @(c z)` has exactly the intended denotation. The difference
is operational. As a relation, `noC` is *generated*: the search unfolds its
definition and enumerates hole-free terms, interleaved with everything else.
As a constraint, `no_c` is *residuated*: it sits on the wire and fires only
when a constructor arrives at its port. Semantically identical; operationally
the difference between a generator and a guard.

The one case that is not merely operational is `neq` between two variables
with no constructors in sight. A generating `neq` would enumerate distinct
instantiations, which is the wrong thing when variables stand for names. What
is wanted is a *negative* atomic constraint, `¬(x = y)`, left residual until
something forces it. This is the first place negation is genuinely required,
and it is atomic negation of the equality node. Section 3 returns to this.

So the honest statement of "what constraints buy" is:

1. **residuation** (suspend until instantiated) as an evaluation strategy, and
2. **atomic negative constraints** on the constructor theory.

Neither requires a separate syntactic category. (1) is a mode; (2) is one
extra generator family (`≠`) with a known solver.

### 1.4 Answer to question 1

Neither "drop constraints" nor "drop relations".

* The relational calculus is the wiring. It cannot be removed; without it
  there is no composition, no intersection, no converse, no existential.
  Everything a "constraint language" does still needs this. CHR-as-a-language
  has it implicitly (shared variables in a flat store) but loses the canonical
  span normal form, which is rwlog's whole value.
* Constraints are the atoms. Constructors are the atoms with the good theory.
  User predicates are atoms with user theories. There is one graph and one
  notion of normal form: no rewrite applies.
* The language-level distinction that should exist is **generate vs
  residuate**, declared per relation (or per call site), not `rel` vs
  `theory`. Under that reading, `no_c` is written once as a relation and used
  as a guard by asking for it to residuate. `theory` blocks become the special
  case of a residuating relation whose rules mention more than one atom on the
  left (multi-head).

Two things to keep in view if this is pursued:

* Completeness of search under residuation. A residuated atom that is never
  woken stays in the answer as a residual. That is already the semantics
  today ("residual constraints in output"), so nothing is lost, but a
  generating relation must never be starved by a residuating one; the
  fairness argument for interleaving has to be re-done with suspended nodes
  in the picture.
* Canonicity. Only theories with most-general solutions may be *solved into*
  the span; everything else stays as residual nodes. The engine should know
  which theories are which; it should not be a property of the constructor
  namespace.

---

## 2. Sharing, superposition, and why disjunction nodes resisted a semantics

### 2.1 Why the conjunctive fragment has no disjunction node

The conjunctive fragment is a cartesian bicategory: one composition, one
tensor, hypergraph string diagrams. Union is not a relation you can compose
with; it is a binary operation on hom-sets. So a "disjunction node" placed
inside a hypergraph has no interpretation as a node of that hypergraph. That
is the formal content of "relation algebra is in the conjunctive fragment".

There are two known ways to add union to string diagrams, and they correspond
to the two things you tried.

**Tape diagrams** (Bonchi, Di Giorgio, Santamaria, POPL 2023). Add a second
monoidal product `⊕` (a biproduct) that `⊗` distributes over. A rig category.
The diagrams are "string diagrams of string diagrams": a tape is a box
carrying a `⊕`-typed boundary, and inside it lives an ordinary hypergraph. `R
∪ S` is

```
Δ_⊕ ; (R ⊕ S) ; ∇_⊕
```

with `Δ_⊕ : X → X ⊕ X` and `∇_⊕ : X ⊕ X → X` the biproduct (co)diagonals.
They prove this is complete for the positive fragment of the calculus of
relations (`∪`, `;`, `∩`, converse, `0`, `id`, `⊤`). The distributivity
isomorphisms `X ⊗ (Y ⊕ Z) ≅ (X ⊗ Y) ⊕ (X ⊗ Z)` are the rules that move a tape
past a node. This is the "disjunction boxes that work but are convoluted and
can be decomposed" experiment. The convolution is real: a tape is non-local,
and decomposing it is copying, which is the `∪ aggressively copies whatever it
is post-composed with` problem from paper §2.2.

**First-order bicategories** (Bonchi, Di Giorgio, Haydon, Sobociński, LICS
2024, "neo-Peircean relations"). Instead of a second tensor, a second
*Frobenius structure* (black) dual to the first (white), related by linear
distributivity laws, with negation as the involution that swaps them. White
composition is relative product; black composition is Peirce's relative sum
`R † S = ¬(¬R ; ¬S)`. Every white axiom has a black dual. This is exactly the
"conjunctive fragment ↔ disjunctive fragment through a negation box, with
the disjunction rules dual to the conjunction rules" picture, worked out and
proven complete for first-order logic. Union is the black analogue of
intersection: black-copy, black composition, black-merge.

What this second result tells you about superposition: a union node *does*
exist, but it composes with its neighbours through the black composition, not
the white one. Put a black node in a white hypergraph and it does not
type-check. The white/black interaction is governed by the linear
distributivity laws, which are inclusions in general and equalities only for
special morphisms. That is the precise reason "disjunction nodes" in a
conjunctive graph kept failing to have a coherent semantics.

### 2.2 What a labeled superposition denotes

Take the interaction-calculus rules at face value and ask what relation they
compute.

* `{a b}_L` is a value that is `a` and `b` "at once"; the final result of a
  program is a tree of superpositions, and each root-to-leaf choice of
  coordinate is a universe.
* `dup_L` meeting `sup_L`: project, coordinate-wise (`x = a`, `y = b`).
* `dup_M` meeting `sup_L`, `M ≠ L`: commute, so each copy is a `sup_L` of
  copies.

The relational reading is: **`{a b}_L` is the relation `{(0, a), (1, b)}`
between a hidden port `L` of type `2` and the value.** If `L` is
existentially closed at the top, this is the plain union `a ∪ b`. If `L` is
shared with another superposition `{c d}_L`, the two make the *same* choice:

```
∃L. {a b}_L × {c d}_L   =   {(a, c), (b, d)}      (correlated)
∃L ∃M. {a b}_L × {c d}_M =  {(a,c),(a,d),(b,c),(b,d)}  (independent)
```

So a superposition is a union **fibered over a named choice variable**, and
the label is the variable's name. Same-label annihilation is "one choice, made
once". Different-label commutation is "independent choices, distribute".
Running out of labels is the need for fresh existentials; alpha-renaming
labels is alpha-renaming bound variables.

In the tape-diagram vocabulary: a wire inside nested tapes `L1, L2, …` has
type `⊕_{L1} ⊕_{L2} … X`, and the label is the name of the tape. Labeled
superposition is a **local, wire-tagged encoding of the `⊕` structure**. It
makes tapes local by having every wire remember which tapes it passes through,
which is exactly what a box does non-locally. This is the coherent account.

### 2.3 Why it fixes the `R;(S∩T)` problem and enables laziness

Paper §2 observes that `R;(S ∩ T) ⊆ (R;S) ∩ (R;T)` is strict, and so the
evaluator may not distribute a composition into an intersection; it has to
wait for `R` to normalise to a span, and §2.2's `↓s_t (R∩S) = ↓s_t (↓t_t R ∩
↓t_t S)` trick works only because `↓t_t ⊆ id`. The counterexample is `R = ↓a_X
∪ …`: distributing copies `R` into both branches and lets the two copies make
*different* choices.

With named choices the copies share the label. When the two branches of the
intersection eventually meet, `sup_L` meets `sup_L` and the match is
coordinate-wise, so the two copies are forced to agree. Distribution becomes
an equality:

```
copy ; (sup_L(R₀,R₁) ⊗ sup_L(R₀,R₁))  =  sup_L(copy;(R₀⊗R₀), copy;(R₁⊗R₁))
```

This is the rig-category distributivity isomorphism, and it is an
isomorphism precisely because the `⊕`-tag is carried on the wire. The
consequence for the evaluator: **the "only distribute `∪` when its leaf is a
span" restriction (§2.2 `rwLeaf`) disappears.** Copying can be deferred
arbitrarily, and performed lazily by the same commutation rule that copies a
constructor through an equality node. That is why named superpositions
matter for efficient evaluation: they are the mechanism that makes lazy
distribution of `∪` sound.

This should be stated and proved as the central theorem of the redesign:
*in the calculus with named choice variables, all rig distributivity laws
hold as equalities, and the evaluator may commute copy past superposition at
any time.* The proof is the standard one for biproducts once labels are
treated as variables with the usual rename-apart discipline; the risk is
entirely in getting that discipline right under recursion (see 2.6).

### 2.4 Where this puts today's engine

`Node::Or` with spine rotation is a single global tape at the root of the
whole relation. `PipeWork::split_or` distributes eagerly into it; `Arc`
sharing makes the copy cheap to *represent* but every branch still redoes
the work on its copy. The only cross-branch sharing is call-context tabling
in `work/fix.rs`, keyed on `(RelId, left boundary, right boundary)`.

What is not shared today: two `Or` branches that both apply `app` to the same
subterm compute it twice. With superposition inside terms, that subterm is
computed once with a `sup` inside it, and the branches are coordinates of the
result. This is also the e-graph relationship: an e-class with `n` members is
`sup_L(m₁ … mₙ)` with `L` fresh and unshared. E-graphs are superpositions with
all labels distinct, which is exactly why they lose correlation between
choices (the classic unsoundness of extracting from an e-graph after
conditional rewrites). Tabling, e-graphs, and interaction-calculus sharing
are three points on one axis: how much choice correlation the representation
keeps.

### 2.5 Choice labels are constraint variables

If a coordinate of a superposition fails, `sup_L(0, b)`, the value is `b`
*and* the fact `L = 1` is now known. Every other `sup_L` in the graph should
eventually drop its coordinate 0. Two observations:

* Not propagating is still sound. The dead coordinate is dropped whenever a
  `sup_L` meets another `sup_L` or at answer extraction. Propagation is an
  optimisation, exactly as constraint propagation is.
* The fact `L ≠ 0` is a constraint on a finite-domain variable, and pushing it
  to every node that mentions `L` is what a constraint store does.

So the "how does a local failure inform the rest of the system" problem of
paper §3.6 has the same answer as question 1: labels are constraint variables
over finite domains; failed coordinates are negative constraints on them;
propagation is the store's job. Both dissatisfactions resolve into one
mechanism.

A union at the relation level is then

```
R ∪ S   :=   ∃L. sup_L(R, S)
```

and an answer with residual choice variables is a compressed family of
answers in exactly the way an answer with residual term variables is.
Enumerating answers is enumerating assignments to choice variables lazily,
which is where interleaving search now lives: inside the term structure rather
than in an `Or` spine.

### 2.6 What is genuinely hard

* **Label freshness under recursion.** Each unfolding of a fixpoint must open
  fresh labels; two copies of a `sup` produced by copying one choice must keep
  the label. HVM's global per-source-site labels are known to be unsound
  outside a "safe" fragment for precisely this reason (the full λ-calculus
  needs Lamping's brackets/croissants or level-indexed labels). rwlog already
  renames term variables apart at every composition; choice variables should
  go through the same `DropFresh`/rename machinery. If they do, "running out
  of labels" is the same non-problem as running out of variable indices. If
  they do not, the design is unsound.
* **Term growth.** Superpositions inside terms duplicate structure, as
  e-classes do. `TermStore` already hash-conses; `sup` nodes must be
  hash-consed too, and coordinates that become equal must collapse
  (`sup_L(a, a) = a` with `L` unconstrained).
* **Fairness.** Completeness of `eval` (every pair in the denotation is
  eventually covered by an emitted span) must be re-proved for enumeration
  over nested superpositions. Paper §4.2's weighting idea is the natural
  place; the label gives you the coordinate to weight.
* **Tabling.** Call keys currently contain spans. With `sup` inside spans a
  key would contain choices. The plausible move is to key on the
  superposition-free skeleton and treat labels as parameters of the table,
  but this is unexplored.

### 2.7 Differential linear logic and the substructural angle

Differential interaction nets (Ehrhard–Regnier) are the right formal home for
"superposition as sum". Cocontraction is the superposition cell, contraction
is the duplicator, and their interaction is the bialgebra law, i.e. the
dup/sup commutation. Sums of nets are the nondeterministic outcome, `!` and
`?` are symmetric, and Ehrhard–Laurent showed the nets encode solos and hence
the π-calculus, which is the "concurrent" in "concurrent relational
programming". The sums there are *unnamed* (a commutative monoid), so DiLL
gives the semantics of unlabeled `∪` with copy commuting through it. Named
superposition is a refinement: sums indexed by a choice variable.

The substructural reading that seems most useful: **term wires are cartesian
(copy and delete freely, Frobenius); choice wires are the resource-sensitive
ones.** A choice may be copied (the copy keeps the label) but each label names
one choice event, and a coordinate is consumed when it fails. Adjoint logic
(Reed; Pruiksma–Pfenning) is the machinery for putting two such modes in one
system with an adjunction between them. This is speculative, but it is the
version of "sub-structural relational programming" that lines up with the
rest of this memo: the substructural discipline is on labels, not on terms.

### 2.8 Negation

Three levels, with sharply different costs:

1. **Atomic negation on constructors**: `x ≠ y`, `x ≠ f(…)`. Needed for
   variables-as-names. Decidable; the standard solver (Chan's constructive
   negation, miniKanren `=/=`) keeps a disequality store where
   `f(x,y) ≠ f(a,b)` becomes `x ≠ a ∨ y ≠ b`, which is itself a superposition
   of atomic disequalities. So negation of a constructor equality *produces*
   `sup` nodes, and lives naturally in the same store as choice variables.
   In the first-order bicategory this is the black merge node applied to a
   single wire.
2. **Atomic negation on choices**: `L ≠ i`. This is 2.5.
3. **Negation of an arbitrary relation** (a Peircean cut of depth ≥ 2). This
   is universal quantification over the Herbrand universe. The first-order
   bicategory gives it a complete axiomatisation, but not an evaluator; over
   an infinite domain there is nothing to enumerate against. Negation as
   failure is the standard compromise and brings stratification with it.

Recommendation: adopt (1) and (2) as generators with fixed solvers, and do
not make (3) a relation-former. The negation box's role in the design is to
give (1) and (2) a principled semantics as duals of the equality and choice
nodes, not to be a general-purpose connective.

---

## 3. What this would mean for the codebase

Not a plan; a map of which structures change and which survive.

**Survives unchanged in role.** `TermStore` hash-consing, `Subst`, matching as
two-sided most-general matching, `NF` as the canonical span form, the
`DropFresh` variable-routing discipline, call-context tabling as the memo
mechanism, the interleaving/fairness contract, the answer-as-span contract,
`dual` as an involution on everything.

**Changes.**

* `TermStore` gains a `Sup(label, children)` node kind. Labels are variables,
  numbered in the same space as term variables but typed (choice vs term) so
  `DropFresh`/`remap_vars` rename them apart per composition. `sup_L(a, a)`
  collapses to `a`.
* `matching.rs` gains three rules: `sup_L(ā)` vs constructor `f(…)` pushes the
  match into each coordinate; `sup_L` vs `sup_L` matches coordinate-wise;
  `sup_L` vs `sup_M` commutes. A failed coordinate records `L ≠ i`.
* `NF` gets a choice-variable arity alongside term arity. An `NF` with free
  choice variables is a family of spans.
* `Node::Or` shrinks to the answer-extraction loop over free choice variables
  (which coordinate to expand next; this is where interleaving and weighting
  live). `PipeWork::split_or` and the `rwLeaf` restriction go away because
  `∪` is `∃L. sup_L(·,·)` and distributes freely.
* `kernel/meet.rs` no longer needs the `↓t_t` pre-composition trick;
  intersection of a superposed span with anything is coordinate-wise on
  shared labels.
* `ChrState` generalises from "multiset of predicate atoms over term
  variables" to "multiset of atoms over term and choice variables", with a
  built-in finite-domain theory for choice variables (`L ≠ i`, and `L`
  fully determined ⇒ substitute) and a built-in disequality theory for term
  variables. This is the same `normalize`/`apply_subst` contract, now also
  carrying choice facts.
* `rel`/`theory` unify: a definition is a relation; a call site or a
  declaration says whether it generates or residuates. Multi-head rules are
  what a residuating relation may use.

**Order of work if pursued**, deletion-first per the repo's own rules:
remove the `Or` spine as the representation of union first, since everything
else is built around not having sharing; then add `Sup` to terms and the three
matching rules; then choice variables in `DropFresh` and `NF`; then the
choice-variable theory in the store; then the generate/residuate mode; then
tabling over superposed keys. Each step has a semantic invariant to test in
both directions (`dual` must remain an involution and answers must be
identical modulo choice-variable renaming).

---

## 4. References

* Bonchi, Seeber, Sobociński. *Graphical Conjunctive Queries*. CSL 2018.
  Cartesian bicategories = conjunctive queries; string diagrams are
  hypergraphs; containment = homomorphism.
* Bonchi, Di Giorgio, Santamaria. *Deconstructing the Calculus of Relations
  with Tape Diagrams*. POPL 2023. Rig categories; `⊕` as union; complete for
  the positive calculus of relations. The "disjunction boxes".
* Bonchi, Di Giorgio, Haydon, Sobociński. *Diagrammatic Algebra of First
  Order Logic*. LICS 2024. First-order bicategories; white/black Frobenius
  structures; negation as the swap; Peirce's existential graphs. The
  "negation box".
* Ehrhard, Regnier. *Differential Interaction Nets*. TCS 2006.
  Cocontraction as superposition, sums as nondeterminism, symmetric
  exponentials. Ehrhard, Laurent, *Acyclic Solos and Differential Interaction
  Nets*, for the concurrency encoding.
* Taelin, *Interaction Calculus* and HVM. Labeled `dup`/`sup`; the safe
  fragment caveat on label management.
* Carboni, Walters. *Cartesian bicategories I*. The base structure.
