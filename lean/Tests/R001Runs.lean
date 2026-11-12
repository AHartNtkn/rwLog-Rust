import Tests.R000Runs
import RwLog.Rungs.R001.Engine

/-!
# Running rung R001

These checks run the proper-baseline machine (the `Runtime` its theorems are
about) on the conformance cases and on the queries the execution properties
name, and fail the build if its output changes. `runR001` returns the answers
emitted within the step budget and whether the machine reported that it is
done; an `exact` case must report done.
-/

namespace RwLog.Tests

def runR001 (P : Program) (q : Rel) (fuel : Nat) : List String × Bool :=
  let r := R001.runtime.run (R001.runtime.init P q) fuel
  (r.1.map showSpan, r.2)

/-- The answers emitted step by step. -/
def traceR001 (P : Program) (q : Rel) (fuel : Nat) : List (List String) :=
  (R001.runtime.trace (R001.runtime.init P q) fuel).map (·.map showSpan)

def rule (heads : List Pat) (body : Body) : TRule := ⟨heads, body⟩

/-- Equality and disequality over Peano numerals, as refutation rules only. -/
def eqNeq : Theory :=
  [ rule [ap "eq" [v 0, v 0]] (.conj []),
    rule [ap "eq" [c "z", ap "s" [v 0]]] .fail,
    rule [ap "eq" [ap "s" [v 0], c "z"]] .fail,
    rule [ap "eq" [ap "s" [v 0], ap "s" [v 1]]] (.conj [ap "eq" [v 0, v 1]]),
    rule [ap "neq" [v 0, v 0]] .fail,
    rule [ap "neq" [c "z", ap "s" [v 0]]] (.conj []),
    rule [ap "neq" [ap "s" [v 0], c "z"]] (.conj []),
    rule [ap "neq" [ap "s" [v 0], ap "s" [v 1]]] (.conj [ap "neq" [v 0, v 1]]),
    rule [ap "eq" [v 0, v 1], ap "neq" [v 0, v 1]] .fail ]

/-- `no_c` from the SK notebook. -/
def noC : Theory :=
  [ rule [ap "no_c" [c "k"]] (.conj []),
    rule [ap "no_c" [c "s"]] (.conj []),
    rule [ap "no_c" [ap "a" [v 0, v 1]]] (.conj [ap "no_c" [v 0], ap "no_c" [v 1]]),
    rule [ap "no_c" [ap "c" [v 0]]] .fail ]

def upP : Program := prog [("up", up)]
def natP : Program := prog [("nat", nat)]

/-- `rel upr { $x -> $x | [$x -> (s $x) ; upr] }`, the right-recursive `up`
of the properties doc. -/
def upr : Rel := .or (.rw (v 0) (v 0)) (.seq (.rw (v 0) (ap "s" [v 0])) (.call "upr"))
def loopNat : Program := prog [("nat", nat), ("loop", .call "loop")]
def zs : List String :=
  ["z -> z", "z -> (s z)", "z -> (s (s z))", "z -> (s (s (s z)))", "z -> (s (s (s (s z))))",
   "z -> (s (s (s (s (s z)))))"]

/-! ## Fixed-mode and recursion-free queries halt with the exact answer set -/

#guard runR001 empty (.and (.rw (v 0) (ap "s" [v 0])) (.rw (ap "s" [v 0]) (v 0))) 40 == ([], true)
#guard runR001 addP (.seq (.at_ (ap "cons" [num 2, num 1])) (.call "add")) 60 ==
  (["(cons (s (s z)) (s z)) -> (s (s (s z)))"], true)
#guard runR001 addP (.seq (.call "add") (.at_ (num 2))) 60 ==
  (["(cons z (s (s z))) -> (s (s z))", "(cons (s z) (s z)) -> (s (s z))",
    "(cons (s (s z)) z) -> (s (s z))"], true)
#guard runR001 addP (.seq (.at_ (num 2)) (.conv (.call "add"))) 60 ==
  (["(s (s z)) -> (cons z (s (s z)))", "(s (s z)) -> (cons (s z) (s z))",
    "(s (s z)) -> (cons (s (s z)) z)"], true)

/-! ## Conformance case 1: left recursion keeps its answers, and halts in a fixed mode -/

#guard contains (runR001 (prog [("lr", lr)]) (.call "lr") 40) zs
#guard contains (runR001 (prog [("lr", lr)]) (.seq (.at_ (c "z")) (.call "lr")) 40) zs
#guard runR001 (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 60 == (["z -> (s (s z))"], true)

/-! ## Conformance case 4: unsatisfiable stores are pruned (refutation rules only) -/

#guard runR001 ⟨[], eqNeq⟩ (.rw (v 0) (v 0) [ap "neq" [v 0, v 0]]) 20 == ([], true)
#guard runR001 ⟨[], eqNeq⟩ (.rw (ap "pair" [v 0, v 1]) (v 0) [ap "eq" [v 0, v 1], ap "neq" [v 0, v 1]]) 20 ==
  ([], true)
#guard runR001 ⟨[("never", .rw (v 0) (v 0) [ap "neq" [v 0, v 0]])], eqNeq⟩ (.call "never") 20 == ([], true)
-- Stores of different spans combine: `eq` from one span, `neq` from the other.
#guard runR001 ⟨[], eqNeq⟩ (.seq eqSpan neqSpan) 20 == ([], true)
-- A constraint that is not refuted stays on the answer.
#guard runR001 ⟨[], eqNeq⟩ (.seq (.rw (v 0) (v 0)) (.seq neqSpan (.at_ (c "z")))) 20 ==
  (["(pair z $5) { (neq z $5) } -> z"], true)
#guard runR001 ⟨[], eqNeq⟩ (.seq (.at_ (ap "pair" [num 2, num 2])) neqSpan) 20 == ([], true)
-- Pruning inside a structure: `no_c` refutes once a `(c _)` appears anywhere.
#guard runR001 ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", ap "c" [c "z"]]))) 20 ==
  ([], true)
#guard runR001 ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", v 0]))) 20 ==
  (["(a k $1) { (no_c (a k $1)) } -> (a k $1)"], true)

/-! ## Conformance case 5 and P1.3: a finite conjunct restricts the other -/

#guard runR001 natP (.and (.rw (c "b") (c "a")) (.call "nat")) 60 == ([], true)
#guard runR001 natP (.and (.call "nat") (.rw (c "b") (c "a"))) 60 == ([], true)
#guard runR001 natP (.and (.rw (num 1) (num 1)) (.call "nat")) 60 == (["(s z) -> (s z)"], true)
#guard runR001 natP (.and (.rw (num 1) (num 0)) (.call "nat")) 60 == ([], true)
#guard runR001 (prog [("upr", upr)])
  (.and (.rw (c "b") (c "a")) (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo"))))) 60 == ([], true)
#guard runR001 (prog [("upr", upr)])
  (.and (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo")))) (.rw (c "b") (c "a"))) 60 == ([], true)

/-! ## Conformance case 6: recursion beside an infinite branch still fires -/

#guard contains (runR001 (prog [("up", up), ("call_first", callFirst)]) (.call "call_first") 30)
  ["a -> a", "a -> b", "z -> (s (s (s z)))"]

/-! ## P1.2: an empty side makes `;` and `&` fail finitely, in either position -/

#guard runR001 loopNat (.seq (.call "nat") (.call "loop")) 40 == ([], true)
#guard runR001 loopNat (.seq (.call "loop") (.call "nat")) 40 == ([], true)
#guard runR001 loopNat (.and (.call "nat") (.call "loop")) 40 == ([], true)
#guard runR001 loopNat (.and (.call "loop") (.call "nat")) 40 == ([], true)

/-! ## Queries the Rust interpreter diverges on

These have an empty or one-answer meaning, and the interpreter runs forever
on them (properties doc, Experiments). R001 halts: the join over the
recursive table closes even while the pushes keep making new boundaries. -/

#guard runR001 (prog [("upr", upr)]) (.seq (.call "upr") (.at_ (c "foo"))) 40 == (["foo -> foo"], true)
#guard runR001 (prog [("upr", upr)]) (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo")))) 40 ==
  ([], true)
#guard runR001 (prog [("lr", lr)]) (.seq (.at_ (num 1)) (.seq (.call "lr") (.at_ (c "z")))) 40 == ([], true)

/-! ## P1.1 and P1.4: order and direction do not change the trace -/

#guard traceR001 loopNat (.or (.call "nat") (.rw (c "a") (c "b"))) 12 ==
  traceR001 loopNat (.or (.rw (c "a") (c "b")) (.call "nat")) 12
#guard traceR001 addP.dual (Rel.dual (.seq (.call "add") (.at_ (num 2)))) 30 ==
  (R001.runtime.trace (R001.runtime.init addP (.seq (.call "add") (.at_ (num 2)))) 30).map
    (·.map fun a => showSpan a.swap)

end RwLog.Tests
