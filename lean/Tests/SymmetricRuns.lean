import Tests.SortsConformance
import RwLog.Rungs.Symmetric.Machine

/-!
# Running the symmetric engine

These checks run the symmetric engine (`Rungs/Symmetric/Machine.lean`) at
the domain of sorts with nothing charged, and fail the build if what it
emits changes. They are the cases the yardstick is run on
(`Tests/R005Runs.lean`), with the same expected answers, and the families of
the prototype (`scripts/symmetric_engine_tables.py`), with the requests the
prototype takes.
-/

namespace RwLog.Tests

def SE : Engine := Symmetric.engine

/-! ## The cases of the yardstick -/

#guard exact (runE SE empty (.rw (v 0) (v 0)) 5) ["$0 -> $0"]
#guard exact (runE SE empty (.and (.rw (v 0) (ap "s" [v 0])) (.rw (ap "s" [v 0]) (v 0))) 20) []
#guard exact (runE SE addP (.seq (.at_ (ap "cons" [num 2, num 1])) (.call "add")) 40)
  ["(cons (s (s z)) (s z)) -> (s (s (s z)))"]
#guard exact (runE SE addP (.seq (.call "add") (.at_ (num 2))) 60)
  ["(cons z (s (s z))) -> (s (s z))", "(cons (s z) (s z)) -> (s (s z))",
    "(cons (s (s z)) z) -> (s (s z))"]
#guard exact (runE SE addP (.seq (.at_ (num 2)) (.conv (.call "add"))) 60)
  ["(s (s z)) -> (cons z (s (s z)))", "(s (s z)) -> (cons (s z) (s z))",
    "(s (s z)) -> (cons (s (s z)) z)"]

-- Left recursion keeps its answers, and halts in a fixed mode.
#guard contains (runE SE (prog [("lr", lr)]) (.call "lr") 26) zs
#guard contains (runE SE (prog [("lr", lr)]) (.seq (.at_ (c "z")) (.call "lr")) 26) zs
#guard exact (runE SE (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 40) ["z -> (s (s z))"]
#guard contains (runE SE (prog [("lr", lr)]) (.seq (.call "lr") (.rw (v 0) (v 0))) 30) zs

-- A finite conjunct restricts the other.
#guard exact (runE SE natP (.and (.rw (c "b") (c "a")) (.call "nat")) 40) []
#guard exact (runE SE natP (.and (.call "nat") (.rw (c "b") (c "a"))) 40) []
#guard exact (runE SE natP (.and (.rw (num 1) (num 1)) (.call "nat")) 40) ["(s z) -> (s z)"]
#guard exact (runE SE natP (.and (.rw (num 1) (num 0)) (.call "nat")) 40) []

-- Recursion beside an infinite branch still fires.
#guard contains (runE SE callP (.call "call_first") 24) ["a -> a", "a -> b", "z -> (s (s (s z)))"]
#guard contains (runE SE callP (.call "call_last") 24) ["a -> a", "a -> b", "z -> (s (s (s z)))"]

-- An empty side makes `;` and `&` fail finitely, in either position.
#guard exact (runE SE loopNat (.seq (.call "nat") (.call "loop")) 30) []
#guard exact (runE SE loopNat (.seq (.call "loop") (.call "nat")) 30) []
#guard exact (runE SE loopNat (.and (.call "nat") (.call "loop")) 30) []
#guard exact (runE SE loopNat (.and (.call "loop") (.call "nat")) 30) []

-- Queries the Rust interpreter diverges on.
#guard exact (runE SE (prog [("upr", upr)]) (.seq (.call "upr") (.at_ (c "foo"))) 40) ["foo -> foo"]
#guard exact (runE SE (prog [("upr", upr)]) (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo")))) 40)
  []
#guard exact (runE SE (prog [("lr", lr)]) (.seq (.at_ (num 1)) (.seq (.call "lr") (.at_ (c "z")))) 40) []

-- The link chain halts (roadmap L08).
#guard exact (runE SE SortsConformance.linkP (.call "link") 20) ["$0 -> $1"]

/-! ## The writing does not matter

Two queries with the same normal form are the same first state, so the run
is the same run: the order and grouping of `|`, the grouping of `;`, the
order and grouping of `&`. -/

#guard traceE SE (prog [("up", up)])
    (.or (.rw (c "a") (c "b")) (.or (.at_ (c "a")) (.seq (.at_ (c "z")) (.call "up")))) 12 ==
  traceE SE (prog [("up", up)])
    (.or (.or (.seq (.at_ (c "z")) (.call "up")) (.at_ (c "a"))) (.rw (c "a") (c "b"))) 12
#guard traceE SE addP (.seq (.seq (.at_ (ap "cons" [num 1, num 1])) (.call "add")) (.at_ (num 2))) 30 ==
  traceE SE addP (.seq (.at_ (ap "cons" [num 1, num 1])) (.seq (.call "add") (.at_ (num 2)))) 30
#guard traceE SE natP (.and (.call "nat") (.and (.rw (num 1) (num 1)) (.rw (v 0) (v 0)))) 20 ==
  traceE SE natP (.and (.and (.rw (v 0) (v 0)) (.call "nat")) (.rw (num 1) (num 1))) 20

/-! ## The families of the prototype

The requests the prototype takes with the split balance and goals opened in
a request waiting for the next (`lean/SYMMETRIC_ENGINE_SIMULATION.md`,
section 10). -/

/-- `@(s^k z) ; q` with `q = ((s $x) -> $x) ; q | (z -> z)`. -/
def countdown (k : Nat) : Program × Rel :=
  (prog [("q", .or (.seq (.rw (ap "s" [v 0]) (v 0)) (.call "q")) (.at_ (c "z")))],
   .seq (.at_ (num k)) (.call "q"))

/-- `$x -> any number`. -/
def gen : Rel := .or (.rw (v 0) (c "z")) (.seq (.call "gen") (.rw (v 0) (ap "s" [v 0])))

/-- `countdown` with `m` more members of `q` that never finish. -/
def fairOr (k m : Nat) : Program × Rel :=
  let infs := (List.range m).map fun j => RelOf.seq (.call "gen") (.rw (v 0) (ap s!"w{j}" [v 0]))
  let rest : Rel := .or (.seq (.rw (ap "s" [v 0]) (v 0)) (.call "q")) (.at_ (c "z"))
  (prog [("gen", gen), ("q", infs.foldr .or rest)], .seq (.at_ (num k)) (.call "q"))

/-- The request at which the first answer is emitted, and the number of
requests before the final report. -/
def requests (p : Program × Rel) (fuel : Nat) : Option Nat × Option Nat :=
  let tr := traceE SE p.1 p.2 fuel
  ((tr.findIdx? fun l => !l.isEmpty && l.head? != some "final").map (· + 1),
   tr.findIdx? fun l => l.head? == some "final")

-- Counting down: the answer at request `2k + 7`, the halt after `5k + 9`.
#guard requests (countdown 2) 60 == (some 11, some 19)
#guard requests (countdown 4) 60 == (some 15, some 29)
#guard requests (countdown 8) 60 == (some 23, some 49)
#guard exact (runE SE (countdown 4).1 (countdown 4).2 60) ["(s (s (s (s z)))) -> z"]

-- Members that never finish do not delay the answer by more than the
-- prototype's `2k + 7` requests, however many they are.
#guard ((requests (fairOr 2 1) 30).1.getD 100) ≤ 11
#guard ((requests (fairOr 4 1) 30).1.getD 100) ≤ 15
#guard ((requests (fairOr 2 3) 30).1.getD 100) ≤ 11
#guard ((requests (fairOr 4 3) 30).1.getD 100) ≤ 15
#guard contains (runE SE (fairOr 4 3).1 (fairOr 4 3).2 30) ["(s (s (s (s z)))) -> z"]

end RwLog.Tests
