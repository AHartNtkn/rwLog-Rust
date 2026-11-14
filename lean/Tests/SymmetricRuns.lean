import Tests.SortsConformance
import RwLog.Rungs.Symmetric.Machine

/-!
# Running the symmetric engine

These checks run the symmetric engine (`Rungs/Symmetric/Machine.lean`) at
the domain of sorts with nothing charged, and fail the build if what it
emits changes. They are the cases the yardstick is run on
(`Tests/R005Runs.lean`), with the same expected answers, and the families of
the prototype (`scripts/symmetric_engine_tables.py`), with the requests the
engine takes on them.
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

The families the prototype was measured on with the split balance and goals
opened in a request waiting for the next
(`lean/SYMMETRIC_ENGINE_SIMULATION.md`, section 10). -/

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

-- Counting down: the answer at request `2k + 10`, the halt after `7k + 12`.
-- (Without the interface check they were `2k + 7` and `5k + 9`, which are
-- the prototype's numbers without it; with it the prototype has `2k + 7` and
-- `6k + 8`. The prototype reads an edge at no charge and at once. The engine
-- pays for the reading, and learns the depth of the program in its first
-- requests.)
#guard requests (countdown 2) 60 == (some 14, some 26)
#guard requests (countdown 4) 60 == (some 18, some 40)
#guard requests (countdown 8) 80 == (some 26, some 68)
#guard exact (runE SE (countdown 4).1 (countdown 4).2 60) ["(s (s (s (s z)))) -> z"]

-- Members that never finish do not delay the answer beyond the `2k + 10`
-- requests of counting down alone, however many they are.
#guard ((requests (fairOr 2 1) 30).1.getD 100) ≤ 14
#guard ((requests (fairOr 4 1) 30).1.getD 100) ≤ 18
#guard ((requests (fairOr 2 3) 30).1.getD 100) ≤ 14
#guard ((requests (fairOr 4 3) 30).1.getD 100) ≤ 18
#guard contains (runE SE (fairOr 4 3).1 (fairOr 4 3).2 30) ["(s (s (s (s z)))) -> z"]

/-! ## The interface check

`p ; q` where every answer of `p` ends in a constructor no answer of `q`
begins with, and both have infinitely many answers: no side of any split
completes, and the engine halts by the interface check. The second case has
an identity span at the end of `p` and at the start of `q`, which hides
nothing. -/

/-- `p ; q` with `p = gen ; ($x -> t $x)` and `q = (u $x -> $x) ; gen`. -/
def clash (ids : Bool) : Program × Rel :=
  let p : Rel := .seq (.call "gen") (.rw (v 0) (ap "t" [v 0]))
  let q : Rel := .seq (.rw (ap "u" [v 0]) (v 0)) (.call "gen")
  let idS : Rel := .rw (v 0) (v 0)
  (prog [("gen", gen), ("p", if ids then .seq p idS else p), ("q", if ids then .seq idS q else q)],
   .seq (.call "p") (.call "q"))

#guard exact (runE SE (clash false).1 (clash false).2 40) []
#guard exact (runE SE (clash true).1 (clash true).2 40) []
#guard (requests (clash false) 40).2 == some 10
#guard (requests (clash true) 40).2 == some 4
-- The same clash below a union and beside a member that has answers.
#guard exact (runE SE (clash false).1 (.or (clash false).2 (.at_ (c "a"))) 40) ["a -> a"]
-- A side whose every product ends in the same constructor, read through a
-- left recursion and a right recursion.
#guard exact (runE SE (prog [
    ("pa", .or (.rw (c "z") (ap "a" [c "z"])) (.seq (.call "pa") (.rw (ap "a" [v 0]) (ap "a" [ap "s" [v 0]])))),
    ("qb", .or (.rw (ap "b" [c "z"]) (c "z")) (.seq (.rw (ap "b" [ap "s" [v 0]]) (ap "b" [v 0])) (.call "qb")))])
  (.seq (.call "pa") (.call "qb")) 40) []
-- The check does not complete a chain that has answers: the interfaces meet.
#guard contains (runE SE (prog [("gen", gen)])
  (.seq (.seq (.call "gen") (.rw (v 0) (ap "t" [v 0]))) (.seq (.rw (ap "t" [v 0]) (v 0)) (.call "gen"))) 30)
  ["$0 -> z"]

/-! ## The mirror image

The engine run on one orientation of its input (`CostedRuntime.oriented`,
`Trusted/Cost.lean`). On the mirrored query in the mirrored program, and on
the converse of the query, each step shows the converse of what the step
shows on the query, and the mirrored input costs the same ticks. The last
cases are their own mirror image, or their own converse: there one run has to
show, at every step, a set of answers that is its own converse. -/

def SO : CostedRuntime := SE.atSorts.oriented

/-- What a step shows, as a sorted list: a step is compared up to the order
of its answers. -/
def shownSorted : Shown SO.Ans → List String
  | .answers as => (as.map fun a => showRep a.2.1).mergeSort
  | .level n => [s!"level {n}"]
  | .final as => "final" :: (as.map fun a => showRep a.2.1).mergeSort

def traceO (P : Program) (q : Rel) (n : Nat) : List (List String) :=
  (SO.runtime.trace (SO.start P q) n).map shownSorted

def traceSwapped (P : Program) (q : Rel) (n : Nat) : List (List String) :=
  (SO.runtime.trace (SO.start P q) n).map fun x => shownSorted x.swap

/-- The run on the mirror image and the run on the converse are the run
swapped, and the mirror image costs the same. -/
def mirrors (P : Program) (q : Rel) (n : Nat) : Bool :=
  traceO P.dual q.dual n == traceSwapped P q n && traceO P (.conv q) n == traceSwapped P q n &&
    SO.paid P q n == SO.paid P.dual q.dual n

def mutualP : Program := prog [
  ("r", .or (.rw (c "z") (c "z")) (.seq (.call "s") (.rw (v 0) (ap "a" [v 0])))),
  ("s", .or (.rw (c "z") (c "z")) (.seq (.call "r") (.rw (v 0) (ap "b" [v 0]))))]

/-- Two relations that are their own converse, written so that each
definition is its own mirror image. -/
def selfMirror : Program := prog [
  ("u", .or (.rw (c "a") (c "b")) (.rw (c "b") (c "a"))),
  ("w", .or (.rw (c "b") (c "c")) (.rw (c "c") (c "b")))]

#guard mirrors addP (.seq (.call "add") (.at_ (num 2))) 60
#guard mirrors (prog [("lr", lr)]) (.call "lr") 26
#guard mirrors callP (.call "call_first") 24
#guard mirrors natP (.and (.call "nat") (.rw (num 1) (num 1))) 40
#guard mirrors mutualP (.seq (.call "r") (.call "s")) 14
#guard mirrors mutualP (.and (.call "r") (.conv (.call "s"))) 14
#guard mirrors (prog [("up", up)])
  (.or (.rw (c "a") (c "b")) (.or (.at_ (c "a")) (.seq (.at_ (c "z")) (.call "up")))) 12

-- Its own converse: both answers in one step.
#guard mirrors empty (.or (.rw (c "a") (c "b")) (.rw (c "b") (c "a"))) 6
#guard traceO empty (.or (.rw (c "a") (c "b")) (.rw (c "b") (c "a"))) 6 ==
  [[], [], ["a -> b", "b -> a"], ["final", "a -> b", "b -> a"]]

-- Its own mirror image, and not its own converse as a node.
#guard mirrors selfMirror (.seq (.call "u") (.call "w")) 12
#guard mirrors selfMirror (.or (.seq (.call "u") (.call "w")) (.seq (.call "w") (.call "u"))) 12
#guard mirrors selfMirror (.seq (.call "u") (.seq (.call "w") (.seq (.call "w") (.call "u")))) 14

-- With the interface check at work.
#guard mirrors (clash false).1 (clash false).2 40
#guard mirrors (clash true).1 (clash true).2 40

end RwLog.Tests
