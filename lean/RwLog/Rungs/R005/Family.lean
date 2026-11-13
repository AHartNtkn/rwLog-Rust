/-
# The family on which R004 depends on direction

`chain k` is `bit ; (bit ; … ; (bit ; $x -> c))`, with `k + 1` choices between
two wrappers and, innermost, a span that forgets what was built. Every one of
its `2 ^ (k + 1)` products is the same span, `$x -> c`. There are no
definitions and no theory.

Read from the left, nothing tells the products apart before the last span, so
all three of R004's unfolders go through `2 ^ (k + 1)` of them: the walk and
the walk from the right visit each, and the shared evaluation keeps one
wrapped term per product as the interface to its left.

Read from the right, the forgetting span comes first and every product is the
same span after one step. The mirror image of `chain k` is
`(((c -> $x ; unbit) ; unbit) ; …) ; unbit`, and R004's shared evaluation,
which works from the left, finds one span at every stage.

So R004 pays exponentially more for `chain k` than for its mirror image. The
two statements below are that fact, about R004 alone. They are what the
separation of R005 from R004 needs (`Rungs/R005/Spec.lean`).
-/
import RwLog.Rungs.R004.Spec

namespace RwLog

namespace R005

/-- `$x -> c`: forget the term. -/
def forget : Span := ⟨.var 0, .sym "c", []⟩

/-- `bit ; (bit ; … ; (bit ; $x -> c))`, with `k + 1` choices. -/
def chain : Nat → Rel
  | 0 => .seq R004.bit (.span forget)
  | k + 1 => .seq R004.bit (chain k)

def sepFam (k : Nat) : Program × Rel := (⟨[], []⟩, chain k)

/-- The pair whose arrival is timed: `z` against `c`. -/
def sepTarget : PRel := {(.sym "z", .sym "c")}

/-- What R004's first round on the mirror image of `chain k` is allowed to
cost. -/
def mirrorFirst (k : Nat) : Nat := 100000 * (k + 2) ^ 3

namespace Obligation

/-- From the left: R004 has paid at least `2 ^ k` at any step at which it has
covered anything on `chain k`. -/
def r004_forward : Prop :=
  ∀ k n M x, R004.costed.Covered (sepFam k).1 (sepFam k).2 M x n →
    2 ^ k ≤ R004.costed.paid (sepFam k).1 (sepFam k).2 n

/-- From the right: R004's first round on the mirror image of `chain k` emits
an answer that relates `c` to `z` in every interpretation, and costs at most
`mirrorFirst k`. -/
def r004_mirror : Prop :=
  ∀ k, ∃ as s',
    (R004.costed.step (R004.costed.start (sepFam k).1.dual (sepFam k).2.dual)).val = .emit as s' ∧
    (∃ a ∈ as, ∀ M, ((.sym "c", .sym "z") : GTerm × GTerm) ∈ a.denAt M) ∧
    (R004.costed.step (R004.costed.start (sepFam k).1.dual (sepFam k).2.dual)).ticks ≤
      mirrorFirst k

end Obligation

end R005

end RwLog
