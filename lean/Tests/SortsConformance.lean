import Tests.R005Runs
import RwLog.Rungs.R005.Sorts

/-!
# The conformance cases about constraints

Cases 2 and 4 of the review of the Rust interpreter are about constraints:
a guard holds only when the store entails it, so a constraint on an open
variable stays in the answer, and a span whose own constraint cannot hold
relates nothing, even when it is the whole query. The review wrote them with
the rules `eq` and `neq`; the constraint system is now sorts with a built-in
`!=` (`lean/SORTS.md`), so they are written with `!=` and a sort here.

These checks run R005, R004 and R001 at the domain of sorts
(`Engine.atSorts`) and fail the build if what they emit changes.
-/

namespace RwLog.Tests.SortsConformance

open RwLog.Tests Sorts

/-- A representative, shown as a span: its two sides, the sorts of its
variables, and what it excludes. -/
def showRep (r : Raw) : String :=
  let sorts := r.c.zipIdx.filterMap fun (c, i) =>
    if (c.sort (· ≤ ·)).isEmpty then none
    else some (s!"${i} : " ++ " & ".intercalate (c.sort (· ≤ ·)))
  let excl := r.x.map fun b => " or ".intercalate (b.map fun (v, t) => s!"${v} != {showTerm t}")
  let store := sorts ++ excl
  let sides := match r.t with
    | .app (.app (.sym "") l) r => showTerm l ++ " -> " ++ showTerm r
    | t => showTerm t
  sides ++ (if store.isEmpty then "" else " { " ++ ", ".intercalate store ++ " }")

/-- Run an engine at the domain of sorts for at most `fuel` steps: the answers
it emitted, and its final report if it reported that it is done. -/
def runS (E : Engine) (P : Program) (q : Rel) (fuel : Nat) : List String × Option (List String) :=
  let r := E.atSorts.runtime.run (E.atSorts.start P q) fuel
  (r.1.map fun a => showRep a.2.1, r.2.map (·.map fun a => showRep a.2.1))

/-- `a != b`. -/
def ne (a b : Pat) : Pat := .app (.app (.sym neSym) a) b

/-- `$x : s`. -/
def is (s : Name) (x : Pat) : Pat := .app (.sym s) x

def idq : Rel := .rw (v 0) (v 0)

/-- `rel nonzero_ok { $x { $x != z } -> $x }` -/
def nonzero : Rel := .rw (v 0) (v 0) [ne (v 0) (c "z")]
/-- `rel different { (pair $x $y) { $x != $y } -> (pair $x $y) }` -/
def different : Rel := .rw (ap "pair" [v 0, v 1]) (ap "pair" [v 0, v 1]) [ne (v 0) (v 1)]
/-- `rel never { $x { $x != $x } -> $x }` -/
def never : Rel := .rw (v 0) (v 0) [ne (v 0) (v 0)]

/-- The sort `zero` has the one member `z`. -/
def P : Program :=
  ⟨[("nonzero_ok", nonzero), ("different", different), ("never", never), ("nat", nat)],
    [("zero", ⟨[("z", [])], none⟩)]⟩

#guard decide P.sorts.WellFormed

/-! ## Conformance case 2: a guard holds only when the store entails it -/

#guard engines.all fun E =>
  exact (runS E P (.seq idq (.seq (.call "nonzero_ok") (.at_ (c "z")))) 20) []
#guard engines.all fun E =>
  exact (runS E P (.seq (.call "nonzero_ok") (.seq (.call "nat") (.at_ (c "z")))) 30) []
#guard engines.all fun E =>
  exact (runS E P (.seq idq (.seq (.call "nonzero_ok") (.at_ (num 1)))) 20) ["(s z) -> (s z)"]
-- On an open variable the constraint is not entailed, so it stays in the answer.
#guard engines.all fun E =>
  exact (runS E P (.seq idq (.call "nonzero_ok")) 20) ["$0 -> $0 { $0 != z }"]
#guard engines.all fun E =>
  exact (runS E P (.seq idq (.seq (.call "different") (.at_ (ap "pair" [c "z", c "z"])))) 20) []
-- `nonzero_ok ; nat` relates every number but `z` to itself. A step at the
-- domain of sorts is slow to evaluate here, so the larger numbers are run on
-- R001 alone, and the open query on R005 for twelve steps.
#guard engines.all fun E =>
  exact (runS E P (.seq (.call "nonzero_ok") (.seq (.call "nat") (.at_ (num 1)))) 30)
    ["(s z) -> (s z)"]
#guard exact (runS R001.engine P (.seq (.call "nonzero_ok") (.seq (.call "nat") (.at_ (num 2)))) 30)
  ["(s (s z)) -> (s (s z))"]
#guard exact (runS R001.engine P (.seq (.at_ (num 3)) (.seq (.call "nonzero_ok") (.call "nat"))) 30)
  ["(s (s (s z))) -> (s (s (s z)))"]
#guard
  let r := runS R005.engine P (.seq (.call "nonzero_ok") (.call "nat")) 12
  contains r ["(s z) -> (s z)"] && !("z -> z" ∈ r.1)

/-! ## Conformance case 4: a span whose constraint cannot hold relates nothing -/

#guard engines.all fun E => exact (runS E P never 12) []
#guard engines.all fun E => exact (runS E P (.call "never") 12) []
-- `(pair $x $y) -> $x` with `$x` equal to `$y` and different from it.
#guard engines.all fun E =>
  exact (runS E P (.and (.rw (ap "pair" [v 0, v 0]) (v 0))
    (.rw (ap "pair" [v 0, v 1]) (v 0) [ne (v 0) (v 1)])) 12) []
-- A constraint that always holds leaves nothing behind.
#guard engines.all fun E =>
  exact (runS E P (.rw (ap "s" [v 0]) (v 0) [ne (ap "s" [v 0]) (c "z")]) 12) ["(s $0) -> $0"]
-- A sort with one member pins the variable.
#guard engines.all fun E =>
  exact (runS E P (.rw (ap "pair" [v 0, v 1]) (v 1) [is "zero" (v 0)]) 12) ["(pair z $0) -> $0"]

end RwLog.Tests.SortsConformance
