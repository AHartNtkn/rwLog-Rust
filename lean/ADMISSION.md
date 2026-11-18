# Admission: what a rung must prove

The Lean text is the statement (`RwLog/Trusted/Levels.lean`,
`Trusted/Runtime.lean`, `Trusted/Cost.lean`, `Trusted/Properties.lean`). This
note says what each part is for.

## What is measured

**Weight.** A derivation of a pair weighs: 1 for a span; the sum of its two
sides for `;` and for `&`; what its side weighs for `|` and for converse; and
1 more for each relation definition unfolded.

**Levels.** Level `c` of a relation is the set of pairs with a derivation of
weight at most `c` (`ProgramOf.level`). Levels belong to the program as
written. They mention no machine, no order of answers and no table. Level 0
is empty, the levels grow, and together they are the relation
(`ProgramOf.pairs_eq_iUnion_level`). Weight does not depend on the direction
an expression is written in (`ProgramOf.levelAt_conv`, `levelAt_dual`).

**An example.** In

```
rel length {
    nil -> z
    |
    [(cons $h $t) -> $t ; length ; $n -> (s $n)]
}
```

the pair `nil`, `z` has a derivation of weight 2: one unfolding of `length`
and one span. A list of one element and `(s z)` has a derivation of weight
5: the unfolding, the two spans of the second case, and the weight 2 of the
inner `length`. Each further element adds 3. So level 2 of `length` is the
one pair `nil`, `z`; level 5 adds every pair `(cons h nil)`, `(s z)`, for
every ground term `h`; level 8 adds the lists of two elements; and so on.
Level 5 has infinitely many pairs, and the one answer
`(cons $h nil) -> (s z)` relates all the new ones.

**Covering.** A run has covered level `c` when the answers it has emitted so
far relate every pair of level `c` (`CostedRuntime.Covered`). The machine
says nothing about levels and need not know of them: whether a level is
covered is read off its answers. In the example, a run has covered level 5
of `length` once it has emitted `nil -> z` and `(cons $h nil) -> (s z)`, or
any answers that relate those pairs. The run is one continuing run. The cost
of a level is what the machine has used when it has covered it
(`CostedRuntime.CoversUsing`), in time (ticks paid) or space (most cells
live at one moment). A query that never halts still has a cost at every
level.

## What a rung proves

A ladder (`Ladder`) asks of every rung, the base included, the three laws
(`CostedRung.Lawful`): it is sound, it relates every pair of the relation by
some answer, and when it reports that it is done its answers relate exactly
the pairs of the relation.

Of every rung above the base it asks an admission (`Admits`), which compares
the rung with the rung below it:

* **A strict win on a witness class** (`Advances`, `Improves`, `WinsOn`). A
  class is a decidable set of whole programs with a rank and a level for
  each member. On a member of rank `k` the new rung covers the member's
  level having used at most `hi k`, a polynomial, and the rung below has
  used at least `2 ^ k` (an exponential gain) or `(k + 1) ^ gain * hi k` (a
  polynomial gain) at any step by which it has covered it. The resource is
  time or space. Members have size polynomial in their rank and there are
  members of every rank. The class is the evidence that the gain is real. It
  is not kept or proved again by later rungs.
* **No trade** (`neverWorse`, `NeverWorse`, `Bounds.worse`). On every
  well-formed program and at every level, when the rung below has covered
  the level the new rung covers it, and where the rung below reports that it
  is done so does the new rung, having paid at most a bound on what the rung
  below has paid. The bound depends on the kind of win.
  * A rung admitted by an exponential win may be a written polynomial worse:
    `worseCoeff * (c + n + 1) ^ worseDeg`, for what the rung below paid `c`
    and the size of the input `n` (with the level, for a level).
  * A rung admitted by a polynomial win is not a trade: it pays at most
    `worseCoeff * (c + 1)`, a written factor of what the rung below paid,
    with no term in the size of the input or the level.

  So halting is not lost, and a rung admitted by a win in space does not buy
  it with time beyond that bound.
* **Forward and backward comparable** (`direction`, `DirectionFree`). The
  rung, the rung run on the converse of a query and the rung run on the
  mirror image are each never worse than the other, within a written
  polynomial.

Preprocessing is charged apart and recorded (`Advances.preCost`).

**Why a factor and not an exact overhead.** The factors of the polynomial
rungs of a ladder multiply: after `k` of them the top rung is within the
product of their factors of the base. A bound of the form "what the rung
below paid, plus an overhead that depends on the input only" would add up
and not multiply. It would also refuse every rung that does some
bookkeeping at each step, such as keeping an index, because on a program
where the bookkeeping never pays, the extra cost grows with the length of
the run and not with the size of the input. Those are most polynomial
improvements, so the bound is a factor, each rung writes its own, and the
product over a ladder is the number to watch.

## What is not claimed

* Nothing answer by answer. No clause says when a particular pair is
  covered.
* Nothing about a program that has a member of a class as a part. A machine
  may stop early or drop work in a larger program, and then a gain on a part
  need not show in the whole. A class that is meant to reach larger programs
  has them as members.
* Nothing against the best plan for a program.
* No record of wins that each rung proves again. A gain is carried upward
  by "no trade". Rungs admitted by polynomial wins lose at most their
  written factor each. A rung admitted by an exponential win may lose a
  polynomial, so it may give back the gain of an earlier polynomial rung.
* No report of progress by the machine. A step emits answers or reports
  that the run is done, and nothing else.

## Rung 1

The symmetric engine has the laws and its cost does not depend on direction
(`Symmetric.rung1_lawful`, `rung1_directionFree`). It is the base of the
ladder (`rung1_ladder`). The base is asked for no win: there is no rung
below it.

Two engines run side by side (`Rungs/Framework/Beside*.lean`) are proofs
that later rungs may use. They are not a rung.
