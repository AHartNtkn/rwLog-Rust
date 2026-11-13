import RwLog.Rungs.R000.Engine

/-!
# Running rung zero

These checks run the rung-zero enumerator itself (the `Runtime` the theorems
are about) on small programs, including the conformance cases that rung zero
is expected to settle, and fail the build if its output changes.
-/

namespace RwLog.Tests

open Term

def v (n : Nat) : Pat := .var n
def c (f : String) : Pat := .sym f
def ap (f : String) (args : List Pat) : Pat := Term.mk f args
def num : Nat → Pat
  | 0 => c "z"
  | n + 1 => ap "s" [num n]

partial def showTerm : Term Nat → String
  | .var n => s!"${n}"
  | t => match t.spine with
    | some (f, []) => f
    | some (f, args) => "(" ++ " ".intercalate (f :: args.map showTerm) ++ ")"
    | none => match t with
      | .app a b => s!"(@ {showTerm a} {showTerm b})"
      | _ => "?"

def showSpan (s : Span) : String :=
  let store := if s.c.isEmpty then "" else " { " ++ ", ".intercalate (s.c.map showTerm) ++ " }"
  showTerm s.l ++ store ++ " -> " ++ showTerm s.r

/-- Run rung zero for at most `fuel` steps: distinct answers, and whether it
reported that it is done. -/
def runR000 (P : Program) (q : Rel) (fuel : Nat) : List String × Bool :=
  let r := R000.runtime.run (R000.runtime.init P q) fuel
  ((r.1.map showSpan).eraseDups, r.2)

def empty : Program := ⟨[], []⟩

def add : Rel :=
  .or (.rw (ap "cons" [c "z", v 0]) (v 0))
    (.seq (.rw (ap "cons" [ap "s" [v 0], v 1]) (ap "cons" [v 0, v 1]))
      (.seq (.call "add") (.rw (v 0) (ap "s" [v 0]))))

def addP : Program := ⟨[("add", add)], []⟩

def prog (defs : List (Name × Rel)) : Program := ⟨defs, []⟩

/-- `rel lr { z -> z | lr ; $x -> (s $x) }` -/
def lr : Rel := .or (.at_ (c "z")) (.seq (.call "lr") (.rw (v 0) (ap "s" [v 0])))
/-- `rel up { z -> z | up ; $x -> (s $x) }` -/
def up : Rel := .or (.at_ (c "z")) (.seq (.call "up") (.rw (v 0) (ap "s" [v 0])))
def callFirst : Rel :=
  .or (.seq (.call "call_first") (.rw (c "a") (c "b")))
    (.or (.at_ (c "a")) (.seq (.at_ (c "z")) (.call "up")))
def nat : Rel :=
  .or (.at_ (c "z")) (.seq (.rw (ap "s" [v 0]) (v 0)) (.seq (.call "nat") (.rw (v 0) (ap "s" [v 0]))))
def nonzeroOk : Rel := .rw (v 0) (v 0) [ap "nonzero" [v 0]]
def eqSpan : Rel := .rw (ap "pair" [v 0, v 1]) (ap "pair" [v 0, v 1]) [ap "eq" [v 0, v 1]]
def neqSpan : Rel := .rw (ap "pair" [v 0, v 1]) (v 0) [ap "neq" [v 0, v 1]]

/-- Every listed answer appears within `fuel` steps. -/
def contains (r : List String × Bool) (xs : List String) : Bool := xs.all (· ∈ r.1)

/-! ## Recursion-free and fixed-mode queries halt with the exact answer set -/

-- Finite terms: `[$x -> (s $x)] & [(s $y) -> $y]` is empty, by the occurs check.
#guard runR000 empty (.and (.rw (v 0) (ap "s" [v 0])) (.rw (ap "s" [v 0]) (v 0))) 40 == ([], true)

-- Addition in both fixed modes.
#guard runR000 addP (.seq (.at_ (ap "cons" [num 2, num 1])) (.call "add")) 40 ==
  (["(cons (s (s z)) (s z)) -> (s (s (s z)))"], true)
#guard runR000 addP (.seq (.call "add") (.at_ (num 2))) 60 ==
  (["(cons z (s (s z))) -> (s (s z))", "(cons (s z) (s z)) -> (s (s z))",
    "(cons (s (s z)) z) -> (s (s z))"], true)

-- The converse runs like the original.
#guard runR000 addP (.seq (.at_ (num 2)) (.conv (.call "add"))) 60 ==
  (["(s (s z)) -> (cons z (s (s z)))", "(s (s z)) -> (cons (s z) (s z))",
    "(s (s z)) -> (cons (s (s z)) z)"], true)

/-! ## Conformance case 1: left recursion keeps its answers -/

#guard contains (runR000 (prog [("lr", lr)]) (.call "lr") 40)
  ["z -> z", "z -> (s z)", "z -> (s (s z))", "z -> (s (s (s z)))", "z -> (s (s (s (s z))))",
   "z -> (s (s (s (s (s z)))))"]
#guard contains (runR000 (prog [("lr", lr)]) (.seq (.at_ (c "z")) (.call "lr")) 40)
  ["z -> z", "z -> (s z)", "z -> (s (s z))", "z -> (s (s (s z)))", "z -> (s (s (s (s z))))",
   "z -> (s (s (s (s (s z)))))"]
#guard runR000 (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 40 == (["z -> (s (s z))"], true)

/-! ## Conformance case 6: recursion beside an infinite branch still fires -/

#guard contains (runR000 (prog [("up", up), ("call_first", callFirst)]) (.call "call_first") 64)
  ["a -> a", "a -> b", "z -> (s (s (s z)))"]

/-! ## Constraint stores ride along and combine

Rung zero never consults the theory; the stores below are what the
specification refutes (see `RwLog.Conformance.Constraints`). -/

#guard runR000 empty (.seq (.rw (v 0) (v 0)) (.seq nonzeroOk (.at_ (c "z")))) 40 ==
  (["z { (nonzero z) } -> z"], true)
#guard runR000 empty (.seq eqSpan neqSpan) 40 ==
  (["(pair $1 $3) { (eq $1 $3), (neq $1 $3) } -> $1"], true)

end RwLog.Tests
