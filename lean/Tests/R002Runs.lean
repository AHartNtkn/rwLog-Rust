import Tests.R001Runs
import RwLog.Rungs.R002.Spec

/-!
# Running rung R002

These checks run R002 (the `Runtime` its theorems are about) and its costed
machines, and fail the build if what they compute changes.

* R002 gives the same run as R001 on the conformance cases.
* Both unfolders give R001's unfolding race on goals with boundaries,
  converses and conjunctions.
* Costs: on the separating family and on doubly recursive programs, what
  R001 and R002 pay to reach the same point of the same run.
-/

namespace RwLog.Tests

def runR002 (P : Program) (q : Rel) (fuel : Nat) : List String × Bool :=
  let r := R002.runtime.run (R002.runtime.init P q) fuel
  (r.1.map fun a => showSpan (P.theory.present a), r.2)

def traceR002 (P : Program) (q : Rel) (fuel : Nat) : List (List String) :=
  (R002.runtime.trace (R002.runtime.init P q) fuel).map (·.map showSpan)

/-- The number of steps taken within the fuel, whether the machine halted,
and the ticks spent. -/
def costOf (C : CostedRuntime) (P : Program) (q : Rel) (fuel : Nat) : Nat × Bool × Nat :=
  let rec go (s : C.State) : Nat → Nat → Nat → Nat × Bool × Nat
    | 0, i, acc => (i, false, acc)
    | f + 1, i, acc =>
      let r := C.step s
      match r.val with
      | .done => (i, true, acc + r.ticks)
      | .emit _ s' => go s' f (i + 1) (acc + r.ticks)
  go (C.init P q) fuel 0 0

/-! ## The same run as R001 -/

def sameRun (P : Program) (q : Rel) (fuel : Nat) : Bool :=
  traceR002 P q fuel == traceR001 P q fuel &&
    (R002.runtime.run (R002.runtime.init P q) fuel).2 ==
      (R001.runtime.run (R001.runtime.init P q) fuel).2 &&
    (R002.baseline.runtime.trace (R002.baseline.init P q) fuel).map (·.map showSpan) ==
      traceR001 P q fuel

#guard sameRun addP (.seq (.at_ (ap "cons" [num 2, num 1])) (.call "add")) 30
#guard sameRun addP (.seq (.call "add") (.at_ (num 2))) 30
#guard sameRun addP (.seq (.at_ (num 2)) (.conv (.call "add"))) 30
#guard sameRun (prog [("lr", lr)]) (.call "lr") 12
#guard sameRun (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 30
#guard sameRun natP (.and (.rw (num 1) (num 1)) (.call "nat")) 30
#guard sameRun natP (.and (.call "nat") (.rw (c "b") (c "a"))) 30
#guard sameRun loopNat (.seq (.call "loop") (.call "nat")) 20
#guard sameRun (prog [("upr", upr)]) (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo")))) 20
#guard sameRun natUpr
  (.seq (.seq (.call "nat") (.at_ (ap "s" [v 0]))) (.seq (.at_ (c "z")) (.call "upr"))) 20
#guard sameRun splitP (.seq (.call "x") (.call "y")) 20
#guard sameRun ⟨[], eqNeq⟩ (.seq eqSpan neqSpan) 10
#guard sameRun ⟨[("nat", nat)], pinT⟩ (.seq (.call "nat") (.rw (v 0) (v 0) [ap "pin" [v 0]])) 30
#guard sameRun ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", v 0]))) 10

#guard runR002 addP (.seq (.call "add") (.at_ (num 2))) 60 ==
  (["(cons z (s (s z))) -> (s (s z))", "(cons (s z) (s z)) -> (s (s z))",
    "(cons (s (s z)) z) -> (s (s z))"], true)

/-! ## Both unfolders compute R001's unfolding race -/

/-- `rel path { @z | path ; path }`: transitive closure written with two
recursive calls. -/
def path : Rel := .or (.at_ (c "z")) (.seq (.call "path") (.call "path"))
def pathP : Program := prog [("path", path)]

/-- `rel halve { z -> z | (s $x) -> $x ; halve ; halve }`: two recursive calls
behind a pattern. -/
def halve : Rel :=
  .or (.at_ (c "z")) (.seq (.rw (ap "s" [v 0]) (v 0)) (.seq (.call "halve") (.call "halve")))
def halveP : Program := prog [("halve", halve)]

def at? (t : Pat) : Option Span := some ⟨t, t, []⟩

def raceGoals : List (Program × R001.Goal) := [
  (pathP, ⟨none, .call "path", none⟩),
  (pathP, ⟨at? (c "z"), .call "path", none⟩),
  (pathP, ⟨at? (c "a"), .call "path", none⟩),
  (pathP, ⟨none, .call "path", at? (c "a")⟩),
  (halveP, ⟨at? (num 2), .call "halve", none⟩),
  (halveP, ⟨none, .call "halve", at? (num 2)⟩),
  (halveP, ⟨none, .conv (.call "halve"), at? (num 2)⟩),
  (halveP, ⟨at? (num 2), .conv (.call "halve"), none⟩),
  (halveP, ⟨at? (num 1), .and (.call "halve") (.rw (v 0) (c "z")), none⟩),
  (addP, ⟨at? (ap "cons" [num 2, num 1]), .call "add", none⟩),
  (addP, ⟨none, .call "add", at? (num 2)⟩),
  (addP, ⟨at? (num 2), .conv (.call "add"), none⟩),
  (natUpr, ⟨none, .seq (.seq (.call "nat") (.at_ (ap "s" [v 0]))) (.seq (.at_ (c "z")) (.call "upr")), none⟩),
  (splitP, ⟨none, .seq (.call "x") (.call "y"), none⟩),
  (natP, ⟨none, .and (.rw (num 1) (num 1)) (.call "nat"), none⟩),
  (natP, ⟨none, .conv (.and (.conv (.call "nat")) (.rw (num 1) (num 1))), none⟩)]

#guard raceGoals.all fun pg => (List.range 5).all fun d =>
  (R002.onDemand pg.1 d pg.2).val == (R001.unfoldFinal pg.1 d pg.2, R001.unfoldAnswers pg.1 d pg.2) &&
  (R002.eager pg.1 d pg.2).val == (R001.unfoldFinal pg.1 d pg.2, R001.unfoldAnswers pg.1 d pg.2)

-- The bound of `onDemand_dominated` on the same goals.
#guard raceGoals.all fun pg => (List.range 5).all fun d =>
  (R002.onDemand pg.1 d pg.2).ticks ≤
    4 * ((R002.eager pg.1 d pg.2).ticks + pg.1.size + R002.goalSize pg.2 + 1) ^ 3

/-! ## Costs -/

-- One unfolding race on `path`, by depth: R001's cost, then R002's.
#guard (List.range 5).map (fun d =>
    ((R002.eager pathP d ⟨none, .call "path", none⟩).ticks,
     (R002.onDemand pathP d ⟨none, .call "path", none⟩).ticks)) ==
  [(1, 1), (8, 6), (38, 23), (270, 58), (8366, 103)]

-- The whole run of `path`: R002 halts after 7 rounds having spent 4091 ticks.
-- R001 takes the same steps, and has spent over thirteen million ticks after
-- 5 of them.
#guard costOf R002.costed pathP (.call "path") 40 == (7, true, 4091)
#guard costOf R002.baseline pathP (.call "path") 5 == (5, false, 13393269)

-- Two recursive calls driven by an input: `@3 ; halve`.
#guard runR002 halveP (.seq (.at_ (num 3)) (.call "halve")) 12 == (["(s (s (s z))) -> z"], true)
#guard costOf R002.costed halveP (.seq (.at_ (num 3)) (.call "halve")) 12 == (6, true, 30483)
#guard costOf R002.baseline halveP (.seq (.at_ (num 3)) (.call "halve")) 5 == (5, false, 437910)

-- The separating family: both machines halt after `k + 4` rounds; R002 within
-- the bound of `separates`, R001 having paid at least `2 ^ k`.
#guard (List.range 9).all fun k => decide ((R002.sepFam k).1.WellFormed (R002.sepFam k).2)
#guard (List.range 9).all fun k =>
  let r := costOf R002.costed (R002.sepFam k).1 (R002.sepFam k).2 100
  let b := costOf R002.baseline (R002.sepFam k).1 (R002.sepFam k).2 100
  r.1 == k + 4 && r.2.1 && b.1 == k + 4 && b.2.1 && r.2.2 ≤ 500 * (k + 5) ^ 4 && 2 ^ k ≤ b.2.2
#guard (costOf R002.costed (R002.sepFam 8).1 (R002.sepFam 8).2 100).2.2 == 3421
#guard (costOf R002.baseline (R002.sepFam 8).1 (R002.sepFam 8).2 100).2.2 == 19822
-- The cost on the family is quartic in `k`, not cubic.
#guard (costOf R002.costed (R002.sepFam 100).1 (R002.sepFam 100).2 200).2.2 == 2036552

end RwLog.Tests
