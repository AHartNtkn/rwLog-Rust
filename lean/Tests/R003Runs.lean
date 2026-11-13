import Tests.R002Runs
import RwLog.Rungs.R003.Spec

/-!
# Running rung R003

These checks run R003 and its parts, and fail the build if what they compute
changes.

* The race of two computations returns one of the two results within 7 times
  the cheaper cost.
* The shared evaluation gives R001's unfolding race without the repeated
  answers, on goals with boundaries, converses and conjunctions.
* R003 gives the same run as R001 and as R002 on the conformance cases, at no
  more than 7 times R002's cost.
* Costs on the separating family and on reachability in a graph whose paths
  meet again.

`Cost.within` decides whether a computation fits its budget from the
computation's cost, so running a race here runs both computations to the end.
The ticks are the cost of the machine; the time these checks take is not.
-/

namespace RwLog.Tests

/-! ## The race -/

#guard (List.range 40).all fun x => (List.range 40).all fun y =>
  let r := Cost.race (⟨0, x⟩ : Cost Nat) ⟨1, y⟩
  decide (r.ticks ≤ 7 * min x y) && (r.val == 0 || r.val == 1)

-- The cheaper one wins when the other needs more than twice as much.
#guard (Cost.race (⟨0, 100⟩ : Cost Nat) ⟨1, 10⟩).val == 1
#guard (Cost.race (⟨0, 10⟩ : Cost Nat) ⟨1, 100⟩).val == 0

/-! ## The shared evaluation computes R001's unfolding race without repeats -/

#guard raceGoals.all fun pg => (List.range 5).all fun d =>
  (R003.shared pg.1 d pg.2).val ==
    (R001.unfoldFinal pg.1 d pg.2, (R001.unfoldAnswers pg.1 d pg.2).eraseDups)

#guard raceGoals.all fun pg => (List.range 5).all fun d =>
  let u := (R003.unfolder pg.1 d pg.2).val
  u.1 == R001.unfoldFinal pg.1 d pg.2 &&
    (u.2 == R001.unfoldAnswers pg.1 d pg.2 || u.2 == (R001.unfoldAnswers pg.1 d pg.2).eraseDups)

-- The bound of `unfolder_ticks` on the same goals.
#guard raceGoals.all fun pg => (List.range 5).all fun d =>
  (R003.unfolder pg.1 d pg.2).ticks ≤
    7 * min (R002.onDemand pg.1 d pg.2).ticks (R003.shared pg.1 d pg.2).ticks

/-! ## The same run as R001 and R002, within 7 times R002's cost -/

def runR003 (P : Program) (q : Rel) (fuel : Nat) : List String × Bool :=
  let r := R003.runtime.run (R003.runtime.init P q) fuel
  (r.1.map fun a => showSpan (P.theory.present a), r.2)

def traceR003 (P : Program) (q : Rel) (fuel : Nat) : List (List String) :=
  (R003.runtime.trace (R003.runtime.init P q) fuel).map (·.map showSpan)

/-- R003 against R002, which is R001 (`R002.runtime_eq`) and can be run where
R001's own unfolding is out of reach. -/
def sameRun3 (P : Program) (q : Rel) (fuel : Nat) : Bool :=
  traceR003 P q fuel == traceR002 P q fuel &&
    (R003.runtime.run (R003.runtime.init P q) fuel).2 ==
      (R002.runtime.run (R002.runtime.init P q) fuel).2 &&
    (costOf R003.costed P q fuel).2.2 ≤ 7 * (costOf R002.costed P q fuel).2.2

#guard traceR003 addP (.seq (.call "add") (.at_ (num 2))) 30 ==
  traceR001 addP (.seq (.call "add") (.at_ (num 2))) 30

#guard sameRun3 addP (.seq (.at_ (ap "cons" [num 2, num 1])) (.call "add")) 30
#guard sameRun3 addP (.seq (.call "add") (.at_ (num 2))) 30
#guard sameRun3 addP (.seq (.at_ (num 2)) (.conv (.call "add"))) 30
#guard sameRun3 (prog [("lr", lr)]) (.call "lr") 8
#guard sameRun3 (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 30
#guard sameRun3 natP (.and (.rw (num 1) (num 1)) (.call "nat")) 30
#guard sameRun3 natP (.and (.call "nat") (.rw (c "b") (c "a"))) 30
#guard sameRun3 loopNat (.seq (.call "loop") (.call "nat")) 8
#guard sameRun3 (prog [("upr", upr)]) (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo")))) 8
#guard sameRun3 splitP (.seq (.call "x") (.call "y")) 20
#guard sameRun3 ⟨[], eqNeq⟩ (.seq eqSpan neqSpan) 10
#guard sameRun3 ⟨[("nat", nat)], pinT⟩ (.seq (.call "nat") (.rw (v 0) (v 0) [ap "pin" [v 0]])) 12
#guard sameRun3 ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", v 0]))) 10
#guard sameRun3 pathP (.call "path") 40
#guard sameRun3 halveP (.seq (.at_ (num 3)) (.call "halve")) 12

#guard runR003 addP (.seq (.call "add") (.at_ (num 2))) 60 ==
  (["(cons z (s (s z))) -> (s (s z))", "(cons (s z) (s z)) -> (s (s z))",
    "(cons (s (s z)) z) -> (s (s z))"], true)

-- Where the walk is already cheap the race costs more than the walk alone,
-- within the factor of 7.
#guard costOf R003.costed pathP (.call "path") 40 == (7, true, 10254)
#guard costOf R003.costed halveP (.seq (.at_ (num 3)) (.call "halve")) 12 == (6, true, 59578)

/-! ## Costs -/

-- The separating family: both machines halt after 2 rounds with the same
-- answer; R003 within the bound of `separates`, R002 having paid at least
-- `2 ^ k`.
#guard (List.range 11).all fun k => decide ((R003.sepFam k).1.WellFormed (R003.sepFam k).2)
#guard (List.range 11).all fun k =>
  let r := costOf R003.costed (R003.sepFam k).1 (R003.sepFam k).2 20
  let b := costOf R002.costed (R003.sepFam k).1 (R003.sepFam k).2 20
  r.1 == 2 && r.2.1 && b.1 == 2 && b.2.1 && r.2.2 ≤ 2000 * (k + 2) ^ 3 && 2 ^ k ≤ b.2.2
#guard runR003 (R003.sepFam 6).1 (R003.sepFam 6).2 20 == (["$0 -> z"], true)
#guard (costOf R003.costed (R003.sepFam 10).1 (R003.sepFam 10).2 20).2.2 == 50963
#guard (costOf R002.costed (R003.sepFam 10).1 (R003.sepFam 10).2 20).2.2 == 16296812

-- One race on the family, by `k`: the shared evaluation grows quadratically.
#guard [8, 16, 32, 64].map (fun k =>
    (R003.shared (R003.sepFam k).1 0 ⟨none, (R003.sepFam k).2, none⟩).ticks) ==
  [1871, 5815, 19847, 72487]

/-- A graph of `k` diamonds in a row: from `n(i)` one edge goes to `a(i)` and
one to `b(i)`, and both go on to `n(i+1)`. There are `2 ^ k` paths from `n0`
to `n(k)` through `2 k` edges. -/
def node (s : String) (i : Nat) : Pat := .sym (s ++ toString i)

def diamondEdges (k : Nat) : Rel :=
  (List.range k).foldr (fun i acc =>
    .or (.rw (node "n" i) (node "a" i)) (.or (.rw (node "n" i) (node "b" i))
      (.or (.rw (node "a" i) (node "n" (i + 1))) (.or (.rw (node "b" i) (node "n" (i + 1))) acc))))
    .zero

/-- `rel path { edge | edge ; path }` over the diamonds. -/
def diamondP (k : Nat) : Program :=
  prog [("edge", diamondEdges k), ("path", .or (.call "edge") (.seq (.call "edge") (.call "path")))]

def fromN0 : R001.Goal := ⟨at? (node "n" 0), .call "path", none⟩

-- Everything reachable from `n0`, at the first depth where the unfolding is
-- final: the walk's cost, then the shared evaluation's. The walk follows every
-- path and triples with each diamond; the shared evaluation visits every node
-- once per depth and its growth slows down.
#guard [1, 2, 3, 4, 5, 6].map (fun k =>
    ((R002.onDemand (diamondP k) (2 * k + 2) fromN0).ticks,
     (R003.shared (diamondP k) (2 * k + 2) fromN0).ticks)) ==
  [(421, 1808), (2669, 13987), (11053, 53254), (37661, 144173), (114669, 319180), (324477, 618583)]

#guard [1, 2, 3, 4, 5].all fun k =>
  (R003.shared (diamondP k) (2 * k + 2) fromN0).val ==
    ((R002.onDemand (diamondP k) (2 * k + 2) fromN0).val.1,
     (R002.onDemand (diamondP k) (2 * k + 2) fromN0).val.2.eraseDups)

end RwLog.Tests
