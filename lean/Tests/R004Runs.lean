import Tests.R003Runs
import RwLog.Rungs.R004.Spec

/-!
# Running rung R004

These checks run R004 and its parts, and fail the build if what they compute
changes.

* The evaluation pruned from the right gives R001's unfolding race without
  the repeated answers, on goals with boundaries, converses and conjunctions.
* R004 gives the same run as R001 and as R003 on the conformance cases, at no
  more than 7 times R003's cost.
* Costs on the separating family, and on generate-and-test queries that have
  an answer.

As in `R003Runs.lean`, running a race here runs both computations to the end.
The ticks are the cost of the machine; the time these checks take is not.
-/

namespace RwLog.Tests

/-! ## The order of derivations -/

open R004 in
#guard Key.lt (.inl .leaf) (.inr .leaf) && !Key.lt (.inr .leaf) (.inl .leaf) &&
  Key.lt (.pair (.inl .leaf) (.inr .leaf)) (.pair (.inr .leaf) (.inl .leaf)) &&
  Key.lt (.pair (.inl .leaf) (.inl .leaf)) (.pair (.inl .leaf) (.inr .leaf)) &&
  !Key.lt (.pair (.inl .leaf) (.inr .leaf)) (.pair (.inl .leaf) (.inr .leaf))

-- Sorting puts the products in the order of their keys, whatever order they
-- arrive in.
open R004 in
#guard
  let ks : List Key := [.pair (.inr .leaf) (.inl .leaf), .pair (.inl .leaf) (.inr .leaf),
    .pair (.inr .leaf) (.inr .leaf), .pair (.inl .leaf) (.inl .leaf)]
  ((sort (ks.map fun k => (k, []))).val.map Prod.fst) ==
    [.pair (.inl .leaf) (.inl .leaf), .pair (.inl .leaf) (.inr .leaf),
     .pair (.inr .leaf) (.inl .leaf), .pair (.inr .leaf) (.inr .leaf)]

/-! ## The pruned evaluation computes R001's unfolding race without repeats -/

#guard raceGoals.all fun pg => (List.range 5).all fun d =>
  (R004.pruned pg.1 d pg.2).val ==
    (R001.unfoldFinal pg.1 d pg.2, (R001.unfoldAnswers pg.1 d pg.2).eraseDups)

#guard raceGoals.all fun pg => (List.range 5).all fun d =>
  let u := (R004.unfolder pg.1 d pg.2).val
  u.1 == R001.unfoldFinal pg.1 d pg.2 &&
    (u.2 == R001.unfoldAnswers pg.1 d pg.2 || u.2 == (R001.unfoldAnswers pg.1 d pg.2).eraseDups)

-- The bound of `unfolder_ticks` on the same goals.
#guard raceGoals.all fun pg => (List.range 5).all fun d =>
  (R004.unfolder pg.1 d pg.2).ticks ≤
    7 * min (R003.unfolder pg.1 d pg.2).ticks (R004.pruned pg.1 d pg.2).ticks

/-! ## The same run as R001 and R003, within 7 times R003's cost -/

def runR004 (P : Program) (q : Rel) (fuel : Nat) : List String × Bool :=
  let r := R004.runtime.run (R004.runtime.init P q) fuel
  (r.1.map fun a => showSpan (P.theory.present a), r.2)

def traceR004 (P : Program) (q : Rel) (fuel : Nat) : List (List String) :=
  (R004.runtime.trace (R004.runtime.init P q) fuel).map (·.map showSpan)

def sameRun4 (P : Program) (q : Rel) (fuel : Nat) : Bool :=
  traceR004 P q fuel == traceR003 P q fuel &&
    (R004.runtime.run (R004.runtime.init P q) fuel).2 ==
      (R003.runtime.run (R003.runtime.init P q) fuel).2 &&
    (costOf R004.costed P q fuel).2.2 ≤ 7 * (costOf R003.costed P q fuel).2.2

#guard traceR004 addP (.seq (.call "add") (.at_ (num 2))) 30 ==
  traceR001 addP (.seq (.call "add") (.at_ (num 2))) 30

#guard sameRun4 addP (.seq (.at_ (ap "cons" [num 2, num 1])) (.call "add")) 30
#guard sameRun4 addP (.seq (.call "add") (.at_ (num 2))) 30
#guard sameRun4 addP (.seq (.at_ (num 2)) (.conv (.call "add"))) 30
#guard sameRun4 (prog [("lr", lr)]) (.call "lr") 8
#guard sameRun4 (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 30
#guard sameRun4 natP (.and (.rw (num 1) (num 1)) (.call "nat")) 30
#guard sameRun4 natP (.and (.call "nat") (.rw (c "b") (c "a"))) 30
#guard sameRun4 loopNat (.seq (.call "loop") (.call "nat")) 8
#guard sameRun4 (prog [("upr", upr)]) (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo")))) 8
#guard sameRun4 splitP (.seq (.call "x") (.call "y")) 20
#guard sameRun4 ⟨[], eqNeq⟩ (.seq eqSpan neqSpan) 10
#guard sameRun4 ⟨[("nat", nat)], pinT⟩ (.seq (.call "nat") (.rw (v 0) (v 0) [ap "pin" [v 0]])) 12
#guard sameRun4 ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", v 0]))) 10
#guard sameRun4 pathP (.call "path") 40
#guard sameRun4 halveP (.seq (.at_ (num 3)) (.call "halve")) 12

#guard runR004 addP (.seq (.call "add") (.at_ (num 2))) 60 ==
  (["(cons z (s (s z))) -> (s (s z))", "(cons (s z) (s z)) -> (s (s z))",
    "(cons (s (s z)) z) -> (s (s z))"], true)

/-! ## Costs -/

-- The separating family, `@a | (gen k ; @q)`: the first round of R004 emits
-- `a -> a` within the bound of `separates`; the first round of R003, before
-- which it has emitted nothing, costs at least `2 ^ k`. The input is within
-- the size bound.
#guard (List.range 9).all fun k => decide ((R004.sepFam k).1.WellFormed (R004.sepFam k).2)
#guard (List.range 9).all fun k =>
  (R004.sepFam k).1.size + (R004.sepFam k).2.size ≤ 12 * (k + 2)
#guard (List.range 9).all fun k =>
  (traceR004 (R004.sepFam k).1 (R004.sepFam k).2 1) == [["a -> a"]] &&
  (costOf R004.costed (R004.sepFam k).1 (R004.sepFam k).2 1).2.2 ≤ 1000 * (k + 2) &&
  2 ^ k ≤ (costOf R003.costed (R004.sepFam k).1 (R004.sepFam k).2 1).2.2
#guard (List.range 9).map (fun k =>
    (costOf R004.costed (R004.sepFam k).1 (R004.sepFam k).2 1).2.2) ==
  [408, 529, 650, 771, 892, 1013, 1134, 1255, 1376]
#guard (List.range 9).map (fun k =>
    (costOf R003.costed (R004.sepFam k).1 (R004.sepFam k).2 1).2.2) ==
  [267, 626, 1134, 3118, 6076, 12130, 24632, 83308, 169826]

-- Both machines halt after the second round; R004's whole run stays linear.
#guard (List.range 4).map (fun k =>
    (costOf R004.costed (R004.sepFam k).1 (R004.sepFam k).2 4,
      costOf R003.costed (R004.sepFam k).1 (R004.sepFam k).2 4)) ==
  [((2, true, 1637), 2, true, 1291), ((2, true, 2348), 2, true, 2716),
    ((2, true, 3059), 2, true, 4588), ((2, true, 3770), 2, true, 10888)]
#guard traceR004 (R004.sepFam 3).1 (R004.sepFam 3).2 4 == [["a -> a"], []]

-- One race on the family, by `k`: the walk from the right stops at the last
-- choice, `k + 37` ticks.
#guard [8, 16, 32, 64].map (fun k =>
    (R004.pruned (R004.sepFam k).1 0 ⟨none, (R004.sepFam k).2, none⟩).ticks) ==
  [45, 53, 69, 101]

-- The mirrored family, `@a | (@q ; (gen k)ᵒ)`, is cheap for R003 already:
-- R002's walk drops a product at the first span that cannot follow what is to
-- its left. R004 adds the same from the right. (No bound between a query and
-- its mirror image is claimed in general.)
#guard (List.range 6).map (fun k =>
    ((costOf R004.costed (R004.sepFam k).1.dual (R004.sepFam k).2.dual 1).2.2,
      (costOf R003.costed (R004.sepFam k).1.dual (R004.sepFam k).2.dual 1).2.2)) ==
  [(411, 268), (629, 389), (750, 510), (871, 631), (992, 752), (1113, 873)]

/-- The term `gen k` makes of `z` by taking the second wrapper at every choice
but the first. -/
def wrapped : Nat → Pat
  | 0 => .app (.sym "0") (.sym "z")
  | k + 1 => .app (.sym "1") (wrapped k)

/-- Generate and test, with one answer: `@z ; (gen k ; @t)`. -/
def oneOf (k : Nat) : Rel := .seq (.at_ (.sym "z")) (.seq (R004.gen k) (.at_ (wrapped k)))

#guard runR004 ⟨[], []⟩ (oneOf 3) 20 == (["z -> (1 (1 (1 (0 z))))"], true)

-- With one answer the query takes two rounds. R004's cost grows slowly with
-- `k` and R003's doubles.
#guard [2, 4, 6, 8].map (fun k =>
    ((costOf R004.costed ⟨[], []⟩ (oneOf k) 20).2.2, (costOf R003.costed ⟨[], []⟩ (oneOf k) 20).2.2)) ==
  [(9365, 11748), (17247, 41252), (30073, 260098), (34025, 1067382)]

-- The limit of this rung: with the test as the second factor of the query
-- itself, `gen k ; @t`, the machine opens a table for `gen k` alone in the
-- second round, and that table holds all `2 ^ (k + 1)` wrappings whatever the
-- unfolder does. Both machines pay for it.
#guard [2, 4, 6].map (fun k =>
    let q : Rel := .seq (R004.gen k) (.at_ (wrapped k))
    ((costOf R004.costed ⟨[], []⟩ q 20).2.2, (costOf R003.costed ⟨[], []⟩ q 20).2.2)) ==
  [(14563, 11935), (136721, 86883), (1166237, 1056577)]

end RwLog.Tests
