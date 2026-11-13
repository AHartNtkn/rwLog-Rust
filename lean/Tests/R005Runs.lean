import Tests.R004Runs
import RwLog.Rungs.R005.Spec

/-!
# Running rung R005

These checks run R005 and fail the build if what they compute changes.

* R005 emits, step for step, R004's answers up to order and equivalence, and
  halts at the same step, on the conformance cases.
* R005 pays exactly the same for a query and for its mirror image in the
  mirrored program, and two ticks more for its converse.
* Costs on the family `chain k`, from both ends, beside R004's.

As in `R003Runs.lean`, running a race here runs both computations to the end.
The ticks are the cost of the machine; the time these checks take is not.
-/

namespace RwLog.Tests

def traceR005 (P : Program) (q : Rel) (fuel : Nat) : List (List Span) :=
  R005.runtime.trace (R005.runtime.init P q) fuel

/-- Every answer of one step is equivalent to an answer of the other, and
there are as many. -/
def stepSame (xs ys : List Span) : Bool :=
  xs.length == ys.length &&
    xs.all (fun a => ys.any fun b => a.covers? b && b.covers? a) &&
    ys.all (fun b => xs.any fun a => a.covers? b && b.covers? a)

def traceSame (t t' : List (List Span)) : Bool :=
  t.length == t'.length && (t.zip t').all fun p => stepSame p.1 p.2

/-- R005 against R004: the same answers at every step, and the same report
of exhaustion. -/
def sameRun5 (P : Program) (q : Rel) (fuel : Nat) : Bool :=
  traceSame (traceR005 P q fuel) (R004.runtime.trace (R004.runtime.init P q) fuel) &&
    (R005.runtime.run (R005.runtime.init P q) fuel).2 ==
      (R004.runtime.run (R004.runtime.init P q) fuel).2

/-! ## The same run as R004 -/

#guard sameRun5 addP (.seq (.at_ (ap "cons" [num 2, num 1])) (.call "add")) 30
#guard sameRun5 addP (.seq (.call "add") (.at_ (num 2))) 30
#guard sameRun5 addP (.seq (.at_ (num 2)) (.conv (.call "add"))) 30
#guard sameRun5 (prog [("lr", lr)]) (.call "lr") 8
#guard sameRun5 (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 30
#guard sameRun5 natP (.and (.rw (num 1) (num 1)) (.call "nat")) 30
#guard sameRun5 natP (.and (.call "nat") (.rw (c "b") (c "a"))) 30
#guard sameRun5 loopNat (.seq (.call "loop") (.call "nat")) 8
#guard sameRun5 (prog [("upr", upr)]) (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo")))) 8
#guard sameRun5 splitP (.seq (.call "x") (.call "y")) 20
#guard sameRun5 ⟨[], eqNeq⟩ (.seq eqSpan neqSpan) 10
#guard sameRun5 ⟨[("nat", nat)], pinT⟩ (.seq (.call "nat") (.rw (v 0) (v 0) [ap "pin" [v 0]])) 12
#guard sameRun5 ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", v 0]))) 10
#guard sameRun5 pathP (.call "path") 40
#guard sameRun5 halveP (.seq (.at_ (num 3)) (.call "halve")) 12

/-! ## The same cost from both ends -/

/-- The whole run costs the same on the mirror image, step count and report
of exhaustion included, and two ticks more on the converse. -/
def sameCost5 (P : Program) (q : Rel) (fuel : Nat) : Bool :=
  let r := costOf R005.costed P q fuel
  costOf R005.costed P.dual q.dual fuel == r &&
    costOf R005.costed P (.conv q) fuel == (r.1, r.2.1, r.2.2 + 2)

#guard sameCost5 (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 30
#guard sameCost5 loopNat (.seq (.call "loop") (.call "nat")) 8
#guard sameCost5 splitP (.seq (.call "x") (.call "y")) 20
#guard sameCost5 ⟨[], eqNeq⟩ (.seq eqSpan neqSpan) 10
#guard sameCost5 ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", v 0]))) 10
#guard sameCost5 pathP (.call "path") 40

-- What that costs on ordinary queries: R005 beside R004. Both runs are paid
-- for until one finishes a step, and level runs are raced in both orders.
#guard [costOf R005.costed pathP (.call "path") 40, costOf R004.costed pathP (.call "path") 40] ==
  [(7, true, 146494), (7, true, 19009)]
#guard [costOf R005.costed splitP (.seq (.call "x") (.call "y")) 20,
    costOf R004.costed splitP (.seq (.call "x") (.call "y")) 20] ==
  [(2, true, 7724), (2, true, 1091)]

/-! ## The family on which R004 depends on direction -/

#guard (List.range 5).all fun k => decide ((R005.sepFam k).1.WellFormed (R005.sepFam k).2)
#guard (List.range 5).all fun k => (R005.sepFam k).1.size + (R005.sepFam k).2.size == 12 * k + 15

-- The first round on `chain k`: R004 from the left, R004 on the mirror image,
-- and R005 from either end. R004 doubles from the left; R005 follows the run
-- on the mirror image.
#guard (List.range 5).map (fun k =>
    ((costOf R004.costed (R005.sepFam k).1 (R005.sepFam k).2 1).2.2,
     (costOf R004.costed (R005.sepFam k).1.dual (R005.sepFam k).2.dual 1).2.2,
     (costOf R005.costed (R005.sepFam k).1 (R005.sepFam k).2 1).2.2,
     (costOf R005.costed (R005.sepFam k).1.dual (R005.sepFam k).2.dual 1).2.2)) ==
  [(673, 676, 5402, 5402), (2216, 1891, 13974, 13974), (4595, 3884, 28196, 28196),
    (16238, 6740, 54384, 54384), (53611, 12774, 107408, 107408)]

-- The answers are the same from both ends, swapped.
#guard (traceR005 (R005.sepFam 2).1 (R005.sepFam 2).2 3).map (·.map showSpan) ==
  [["$1 -> c"], []]
#guard (traceR005 (R005.sepFam 2).1.dual (R005.sepFam 2).2.dual 3).map (·.map showSpan) ==
  [["c -> $1"], []]

end RwLog.Tests
