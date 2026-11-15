import Tests.SortsConformance
import RwLog.Rungs.Symmetric.Machine

/-!
# Running the symmetric engine

These checks run the symmetric engine (`Rungs/Symmetric/Machine.lean`) with
the raced unfolding (`Unfold.raced`), at
the domain of sorts with nothing charged, and fail the build if what it
emits changes. They are the cases the yardstick is run on
(`Tests/R005Runs.lean`), with the same expected answers, and the families of
the prototype (`scripts/symmetric_engine_tables.py`), with the requests the
engine takes on them.
-/

namespace RwLog.Tests

def SE : Engine := Symmetric.engine Unfold.raced

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

-- Counting down: the answer at request `2k + 9`, the halt at `6k + 11`.
-- (The prototype reads an edge at no charge and at once. The engine pays for
-- the reading, and learns the depth of the program in its first requests.)
#guard requests (countdown 2) 60 == (some 13, some 23)
#guard requests (countdown 4) 60 == (some 17, some 35)
#guard requests (countdown 8) 80 == (some 25, some 59)
#guard requests (countdown 12) 120 == (some 33, some 83)
#guard exact (runE SE (countdown 4).1 (countdown 4).2 60) ["(s (s (s (s z)))) -> z"]

-- Members that never finish do not delay the answer beyond the `2k + 9`
-- requests of counting down alone, however many they are.
#guard ((requests (fairOr 2 1) 30).1.getD 100) ≤ 13
#guard ((requests (fairOr 4 1) 30).1.getD 100) ≤ 17
#guard ((requests (fairOr 2 3) 30).1.getD 100) ≤ 13
#guard ((requests (fairOr 4 3) 30).1.getD 100) ≤ 17
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
#guard (requests (clash false) 40).2 == some 8
#guard (requests (clash true) 40).2 == some 10
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

/-! ## The unfolding race

`p ; q` with `p = (z -> (b z)) | p ; ($x -> (a $x))` and
`q = ((a (e $x)) -> $x) | ((b $x) -> $x) ; q`: the answers of `p` end in
`a^n (b z)` and those of `q` begin with `b^k (a (e _))`, so the chain relates
nothing, and both tables are infinite. The last span of an answer of `p`
alone meets a first span of an answer of `q`, so the interface check does not
complete the chain. Its race does. -/

def deepP : Program := prog [
  ("p", .or (.rw (c "z") (ap "b" [c "z"])) (.seq (.call "p") (.rw (v 0) (ap "a" [v 0])))),
  ("q", .or (.rw (ap "a" [ap "e" [v 0]]) (v 0)) (.seq (.rw (ap "b" [v 0]) (v 0)) (.call "q")))]

-- An ask of the race may cost only what is left of the rounds and the work
-- of the goal, so the race decides after more requests than it would if
-- every ask were paid at once, each of them a bounded piece of work.
#guard exact (runE SE deepP (.seq (.call "p") (.call "q")) 100) []
#guard requests (deepP, .seq (.call "p") (.call "q")) 100 == (none, some 60)
-- Below a union and beside a member that has answers.
#guard exact (runE SE deepP (.or (.seq (.call "p") (.call "q")) (.at_ (c "a"))) 100) ["a -> a"]

/-! ## Units that starve nothing

A strategy works one unit at a time, as many units as its turn allows, and
the tables it reads may grow faster than it reads them. Whatever it has to
do must still be reached. -/

/-- The pairs a join combines in its first `n` units, when its two sides hold
`la t` and `lb t` answers before unit `t`. -/
def joinUnits (la lb : Nat → Nat) (n : Nat) : List (Nat × Nat) :=
  ((List.range n).foldl (fun (acc : List (Nat × Nat) × Symmetric.Cursor) t =>
    match Symmetric.Cursor.next (la t) (lb t) (acc.2.room (la t) (lb t)) acc.2 with
    | (some p, c) => (acc.1 ++ [p], c)
    | (none, c) => (acc.1, c)) ([], Symmetric.Cursor.start)).1

-- Tables that do not grow: every pair, once.
#guard (joinUnits (fun _ => 3) (fun _ => 4) 12).length == 12
#guard (joinUnits (fun _ => 3) (fun _ => 4) 12).eraseDups.length == 12
#guard (joinUnits (fun _ => 3) (fun _ => 4) 20).length == 12
#guard joinUnits (fun _ => 0) (fun _ => 4) 5 == []
#guard joinUnits (fun _ => 1) (fun _ => 1) 5 == [(0, 0)]
-- One side gains an answer with every unit, and the other gains its second
-- answer late: that answer is still combined, on either side.
#guard (joinUnits (fun t => t + 1) (fun t => if t < 3 then 1 else 2) 40).contains (0, 1)
#guard (joinUnits (fun t => if t < 3 then 1 else 2) (fun t => t + 1) 40).contains (1, 0)
#guard (joinUnits (fun t => 2 * t + 1) (fun t => if t < 5 then 2 else 3) 200).contains (0, 2)
-- Both sides gain an answer with every unit: every pair of the first five
-- of each is combined, and no pair twice.
#guard ((List.range 5).all fun i => (List.range 5).all fun j =>
  (joinUnits (fun t => t + 1) (fun t => t + 1) 60).contains (i, j))
#guard (joinUnits (fun t => t + 1) (fun t => t + 1) 60).eraseDups.length == 60
#guard (joinUnits (fun t => t + 1) (fun t => if t < 3 then 1 else 2) 40).eraseDups.length == 40
-- A pair is combined only when both its answers are held.
#guard (joinUnits (fun t => t + 1) (fun t => t / 2 + 1) 50).zipIdx.all fun p =>
  p.1.1 < p.2 + 1 && p.1.2 < p.2 / 2 + 1

-- Of several tables with answers not yet read, the one read least is read
-- next, so none waits for ever behind one that keeps growing.
#guard RwLog.Symmetric.leastBy (fun x : Nat × Nat => x.1) (fun x => x.2 == 1) [(5, 1), (3, 1), (9, 1), (1, 0)] ==
  some (3, 1)
#guard RwLog.Symmetric.leastBy (fun x : Nat × Nat => x.1) (fun x => x.2 == 1) [(5, 0), (3, 0)] == none
#guard RwLog.Symmetric.leastBy (fun x : Nat × Nat => x.1) (fun _ => true) [(2, 7), (2, 8), (4, 9)] == some (2, 7)
#guard RwLog.Symmetric.leastBy (fun x : Nat × Nat => x.1) (fun _ => true) ([] : List (Nat × Nat)) == none

/-! ## Work that is done is counted

The balance lets the groups of the lowest level work, and a level rises by
what was spent. The kernel here charges nothing for an answer, so a group
that only combines answers spends nothing there. If its level did not rise
it would stay lowest for ever and keep every other group of its table from
working. The engine charges itself one tick for a unit of work that did
something, so the level of a group that worked has risen. -/

/-- A number that changes whenever the strategy does a unit of work. -/
def stratMark {N A : Type} : RwLog.Symmetric.Strat N A → Nat
  | .span ran => if ran then 1 else 0
  | .copy _ subs => (subs.map (·.2)).sum
  | .join _ _ _ c => c.na + c.nb + c.inner
  | .push _ _ _ _ todo subs =>
    (match todo with
      | none => 0
      | some l => 1 + l.length) + 2 * subs.length + (subs.map (·.2.2)).sum
  | .check _ _ _ .reading => 0
  | .check _ _ _ .off => 1
  | .check _ _ _ (.opened subs) => 2 + subs.length

/-- The groups of every table, each as its level and the marks of its
strategies. -/
def groupMarks (s : SE.atSorts.State) : List (List (Nat × List Nat)) :=
  s.st.tables.map fun t => (t.groups.getD []).map fun g => (g.level, g.strats.map stratMark)

/-- The first state and the states after each of the first `n` requests. -/
def statesE (P : Program) (q : Rel) (n : Nat) : List SE.atSorts.State :=
  ((List.range n).foldl (fun (acc : List SE.atSorts.State × Option SE.atSorts.State) _ =>
    match acc.2 with
    | none => acc
    | some s =>
      match (SE.atSorts.step s).val with
      | .emit _ s' => (acc.1 ++ [s'], some s')
      | .progress _ s' => (acc.1 ++ [s'], some s')
      | .done _ => (acc.1, none))
    ([SE.atSorts.start P q], some (SE.atSorts.start P q))).1

/-- In every request, a group whose strategies did work has a higher level
after it. A group is found again by its place, in the requests in which no
group of its table is removed. -/
def workCounted (P : Program) (q : Rel) (n : Nat) : Bool :=
  let ss := (statesE P q n).map groupMarks
  (ss.zip (ss.drop 1)).all fun p =>
    (p.1.zip p.2).all fun tt =>
      tt.1.length != tt.2.length || (tt.1.zip tt.2).all fun gg =>
        gg.1.2 == gg.2.2 || gg.1.1 < gg.2.1

#guard workCounted (countdown 3).1 (countdown 3).2 30
#guard workCounted (fairOr 2 3).1 (fairOr 2 3).2 20
#guard workCounted (prog [("gen", gen)]) (.seq (.call "gen") (.seq (.call "gen") (.call "gen"))) 30
#guard workCounted (prog [("lr", lr)]) (.call "lr") 20
#guard workCounted (clash false).1 (clash false).2 12

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
