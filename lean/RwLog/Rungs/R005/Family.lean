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

So R004 pays exponentially more for `chain k` than for its mirror image, and
R005 pays the same from both ends. The theorems that say so (`r004_forward`,
`r004_mirror`, `separates`) are at the tag `epoch-1`; `Tests/R005Runs.lean`
measures it here.

`bit` and `gen` are also the building blocks of the families measured in
`Tests/MiddleRuns.lean` and `Tests/DirectedRuns.lean`.
-/
import RwLog.Rungs.R005.Engine

namespace RwLog

namespace R005

/-- `$x -> (f $x)`. -/
def wrap (f : Sym) : Span := ⟨.var 0, .app (.sym f) (.var 0), []⟩

/-- A choice between two wrappers. -/
def bit : Rel := .or (.span (wrap "0")) (.span (wrap "1"))

/-- `bit ; (bit ; … ; bit)`, with `k + 1` choices. -/
def gen : Nat → Rel
  | 0 => bit
  | k + 1 => .seq bit (gen k)

/-- `$x -> c`: forget the term. -/
def forget : Span := ⟨.var 0, .sym "c", []⟩

/-- `bit ; (bit ; … ; (bit ; $x -> c))`, with `k + 1` choices. -/
def chain : Nat → Rel
  | 0 => .seq bit (.span forget)
  | k + 1 => .seq bit (chain k)

def sepFam (k : Nat) : Program × Rel := (⟨[], []⟩, chain k)

/-- The pair whose arrival is timed: `z` against `c`. -/
def sepTarget : PRel := {(.sym "z", .sym "c")}

end R005

end RwLog
