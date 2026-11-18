# Admission: what a rung must prove

The Lean text is the statement (`RwLog/Trusted/Levels.lean`,
`Trusted/Runtime.lean`, `Trusted/Cost.lean`, `Trusted/Properties.lean`). This
note says what each part is for. It replaces the note of 2026-11-16, whose
rule compared machines answer by answer and inside contexts; that rule is in
the history of this file.

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

**Reports.** A machine emits answers in any order and may report a level
(`StepOf.progress`). A report of `c` is true when the answers emitted so far
relate every pair of level `c` (`Runtime.HonestReports`). One answer with
variables may cover a whole level; a level is a set of ground pairs, so this
is credited.

**Finishing.** A machine has finished level `c` when it has reported a level
`c` or higher, or has reported that it is done (`Runtime.Finished`). The run
is one continuing run. The cost of a level is what the machine has used when
it has finished it (`CostedRuntime.FinishesUsing`), in time (ticks paid) or
space (most cells live at one moment).

## What a rung proves

A ladder (`Ladder`) asks of every rung, the base included:

* the three laws (`CostedRung.Lawful`);
* that it reports levels truly (`CostedRung.Honest`). The measure reads the
  machine's reports, so without this it would mean nothing. It is what the
  third law says of the report that a run is done, said of each level. A
  rung need not report any level.

and of every rung above the base an admission (`Admits`):

* **A strict win on a class** (`Advances`, `Improves`, `WinsOn`). A class is
  a decidable set of whole programs with a rank and a level for each member.
  On a member of rank `k` the new rung finishes the member's level having
  used at most `hi k`, a polynomial, and the rung below has used at least
  `2 ^ k` (an exponential gain) or `(k + 1) ^ gain * hi k` (a polynomial
  gain) at any step by which it has finished it. The resource is time or
  space. Members have size polynomial in their rank and there are members of
  every rank.
* **Never worse than the rung below** (`neverWorse`, `NeverWorse`). On every
  well-formed program and at every level, when the rung below has finished
  the level the new rung finishes it having paid at most a written
  polynomial of what the rung below has paid, of the size of the input and
  of the level; and where the rung below reports that it is done so does the
  new rung, within the polynomial. So halting is not lost, and a rung
  admitted by a win in space does not give up more than a polynomial of
  time.
* **Forward and backward comparable** (`direction`, `DirectionFree`). The
  rung, the rung run on the converse of a query and the rung run on the
  mirror image are each never worse than the other, within a written
  polynomial.

Preprocessing is charged apart and recorded (`Advances.preCost`).

## What is not claimed

* Nothing answer by answer. No clause says when a particular pair is
  covered.
* Nothing about a program that has a member of a class as a part. A machine
  may stop early or drop work in a larger program, and then a gain on a part
  need not show in the whole. A class that is meant to reach larger programs
  has them as members.
* Nothing against the best plan for a program.
* No record of wins that each rung proves again. A gain is carried upward by
  "never worse": a rung above is within a polynomial of the rung that made
  the gain, on the members of its class as on every program. A gain that is
  only polynomial is not protected by this.

## Rung 1

The symmetric engine reports no level (`Symmetric.silent`), so it finishes a
level only by reporting that it is done. It has the laws, its reports are
true because there are none, and its cost does not depend on direction
(`Symmetric.rung1_lawful`, `rung1_honest`, `rung1_directionFree`). It is the
base of the ladder (`rung1_ladder`).
