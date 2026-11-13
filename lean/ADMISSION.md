# Admission: wins in time and space, on a class, in context

This note settles the design of the admission rule in `RwLog/Trusted/Cost.lean`
(ledger rows L33 and L02 of the roadmap) and records why each choice was made.
The Lean text is the statement; this is the reasoning.

## 1. What had to be decided

Until now a rung was admitted by one hand-picked sequence of inputs on which
its predecessor pays `2 ^ k` ticks and it pays a polynomial. Three things were
missing.

* Only an exponential gain in time could admit a rung (L33).
* The gain was shown on one sequence, not on a class of programs that a
  reader can recognise (L02).
* The gain was shown on the inputs alone. Nothing said it holds when such an
  input is a part of a larger program (L02). The open point was the charge:
  inside `r | s` the new machine also pays for `s`, so its cost is not a
  function of `k`.

## 2. The class

A class is three computable functions on an input (a program and a query):
`mem` decides membership, `rank` is the number the gain is stated in, and
`tgt` lists finitely many ground pairs, the answers the comparison is about.
`ProgClass.Proper` holds the facts about the class that mention no machine:
members are well formed, their size is at most a polynomial in their rank,
the targets are nonempty and are related by the member, and the rank is
unbounded over the members. The last
one is what makes a gain stated in the rank a statement about infinitely many
sizes.

The targets are a finite list, not a set, because the charge of section 4
writes them into a program.

## 3. A context that demands a relation's answers

A context is an expression with one hole and a list of further definitions.
Plugging a member `(P, r)` into it gives the program `P` with the further
definitions and the query with `r` in the hole. The sorts are the member's: a
program has one list of sorts, and a class says for itself which sorts its
members may declare.

Two conditions make a context one that demands the member's answers. They are
separate because they exclude different things.

**The hole is open (`Ctx.Open`, syntactic).** Every operator between the hole
and the root passes each answer of the hole on without restricting the hole:
`|` with anything on the other side, converse, and `;` with a single span
whose pattern on the hole's side is a variable that its store does not
mention (`$x -> (f $x)`, a wrapper or a projection). `&` and `;` with
anything else are not open: there the other side tells the hole which answers
are wanted, and a machine may use that. `r ; @c` asks for the part of `r` that
ends in `c`, which is another relation and may be easy for a machine for
which `r` is hard. No condition on meanings can tell the two apart, since
`r ; @c` needs the pair `(a, c)` of `r` exactly as `r | s` does. So this
condition is on the text.

**The pair needs the targets (`Context.Demands`, semantic).** A pair `y` of
the plugged query is compared when, in the interpretation of the member's sorts, the context relates
`y` with the targets in the hole, and does not relate it with everything the
member relates except the targets in the hole. This excludes `Zero ; r`,
where nothing is demanded, and `r | s` at a pair that `s` relates by itself.
The meaning of a context is a function of the meaning of its hole
(`Ctx.denAt`), so this needs no machine.

A hole occurs once, in the query. A member called from inside a recursion of
the larger program is not covered: there the hole is under `;` with the
recursion, which restricts it.

## 4. What the rest of the context costs

The lower bound needs no accounting: the old machine has paid at least
`lo k` before it covers a demanded pair, in every open context.

The upper bound does. The candidates were:

1. *The cost of the context with the hole empty.* Rejected: with `Zero` in the
   hole the demanded pair is never covered, so there is no point of the run to
   read a cost at, and the run of `s` alone is not the share `s` gets beside
   `r`.
2. *An absolute bound on the class* (billboard H9: latency at most a
   polynomial in the smallest derivation). It survives embedding by
   construction, but it says nothing about the old machine inside the
   context, and it needs sizes of derivations in the trusted files. It stays
   on the billboard as a ceiling a rung may state beside its admission.
3. *The cost of the context with the member's answers given.* Adopted.

The residue of a context at a demanded pair `y` is what the new machine
itself pays to cover `y` when the hole holds the targets written out as a
union of ground spans (`Rel.ofPairs`). That is the context's own work at `y`:
everything the machine does on the plugged query except finding the member's
answers. The requirement is

    cost of y in K[r]  ≤  ctx (hi k) (residue of y in K) (size of K)

for an explicit function `ctx` whose shape depends on the kind of win. The
size is the context's alone, not the plugged input's, so for a fixed context
the bound grows with `k` only through `hi k` and the residue. With a small
residue the gap between `lo k` and `hi k` is the gap in context; with a large
one the context dominates both machines and nothing is claimed, which is the
truth.

The bound is a function of three numbers and not a sum, because a fair
machine multiplies: beside `m` alternatives a branch gets one tick in `m`.
For the kinds whose gain is exponential `ctx` is a polynomial in all three.
For a polynomial gain a polynomial in `hi k` would swallow the gain, so there
`ctx` is linear in `hi k` and in the residue, with a factor polynomial in the
size of the context only.

The member alone is the hole with no further definitions; the bound `hi k`
is also required there directly, so `hi` is what the new machine pays on a
member and not that up to `ctx`.

## 5. The kinds of win, one statement

A kind is a resource (time or space) and the size of the gap (exponential or
polynomial). The size of the gap fixes three functions of the numerals; the
resource fixes what is measured.

| gap | old machine has used at least | simulation of the old machine | in context |
|---|---|---|---|
| exponential | `2 ^ k` | polynomial in what it used and the size | polynomial |
| polynomial | `(k + 1) ^ gain * hi k`, `gain ≥ 1` | `simCoeff * (c + 1)`: a constant factor | linear in `hi k` and the residue |

The separation (`SeparatesOn`) and the simulation (`SimulatesBy`) are written
once, for any resource. `Admits` takes the kind as its first argument, so
every admission says which it is.

**Which resources are simulated.** Time, for every kind. Space too, within
the same bound, for every kind except an exponential gain in time. That
exception is deliberate: the usual exponential gain in time is a table, which
is bought with space; what such a rung uses is reported, not capped.

**Why a constant factor for a polynomial win.** With a polynomial simulation,
one rung could gain `k ^ g` on a class and lose `k ^ g` elsewhere, and the
next could do the reverse, for ever. With a constant factor a gain whose
ratio is unbounded can never be given back by later polynomial rungs: after
`m` of them the loss is at most a constant. The bound has no term in the size
of the input, since on inputs the old machine answers quickly such a term is
an unbounded loss. The factor is required in both resources, because
otherwise a polynomial rung in time and one in space could undo each other's
gains in turn. So polynomial wins in time and in space are admitted on the
same terms.

**What is not protected.** A rung with an exponential gain may lose a
polynomial, so it may give back the gain of an earlier polynomial rung. That
is the priority Anthony set: exponential wins are taken first while there are
any.

## 6. Priority

"Exponential first" is a rule for choosing the next rung (roadmap, section 2),
not a clause of `Admits`: no theorem about two machines can say that no
exponential win is left.
