import Tests.NaiveRuns
import RwLog.Rungs.Tabled.Base.Engine
import RwLog.Rungs.Tabled.Base.Spec

/-!
# Running rung R001

These checks run the proper-baseline machine (the `Runtime` its theorems are
about) on the conformance cases and on the queries the execution properties
name, and fail the build if its output changes. `runR001` returns the answers
emitted within the step budget, as shown to the user (`Theory.present`
rewrites each store by the theory), and whether the machine reported that it
is done; an `exact` case must report done. `rawR001` returns the answers as the
tables keep them, with stores as written.
-/

namespace RwLog.Tests

def runR001 (P : Program) (q : Rel) (fuel : Nat) : List String × Bool :=
  let r := R001.runtime.run (R001.runtime.init P q) fuel
  (r.1.map fun a => showSpan (P.theory.present a), r.2)

def rawR001 (P : Program) (q : Rel) (fuel : Nat) : List String × Bool :=
  let r := R001.runtime.run (R001.runtime.init P q) fuel
  (r.1.map showSpan, r.2)

/-- The answers emitted step by step. -/
def traceR001 (P : Program) (q : Rel) (fuel : Nat) : List (List String) :=
  (R001.runtime.trace (R001.runtime.init P q) fuel).map (·.map showSpan)

def rule (heads : List Pat) (body : Body) : TRule := ⟨heads, body⟩

/-- Equality and disequality over Peano numerals, as refutation rules only. -/
def eqNeq : Theory :=
  [ rule [ap "eq" [v 0, v 0]] (.conj [] []),
    rule [ap "eq" [c "z", ap "s" [v 0]]] .fail,
    rule [ap "eq" [ap "s" [v 0], c "z"]] .fail,
    rule [ap "eq" [ap "s" [v 0], ap "s" [v 1]]] (.conj [] [ap "eq" [v 0, v 1]]),
    rule [ap "neq" [v 0, v 0]] .fail,
    rule [ap "neq" [c "z", ap "s" [v 0]]] (.conj [] []),
    rule [ap "neq" [ap "s" [v 0], c "z"]] (.conj [] []),
    rule [ap "neq" [ap "s" [v 0], ap "s" [v 1]]] (.conj [] [ap "neq" [v 0, v 1]]),
    rule [ap "eq" [v 0, v 1], ap "neq" [v 0, v 1]] .fail ]

/-- `no_c` from the SK notebook. -/
def noC : Theory :=
  [ rule [ap "no_c" [c "k"]] (.conj [] []),
    rule [ap "no_c" [c "s"]] (.conj [] []),
    rule [ap "no_c" [ap "a" [v 0, v 1]]] (.conj [] [ap "no_c" [v 0], ap "no_c" [v 1]]),
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
-- `(no_c (a k $1))` is replaced by its body; `(no_c k)` then fires away.
#guard runR001 ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", v 0]))) 20 ==
  (["(a k $1) { (no_c $1) } -> (a k $1)"], true)

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

/-! ## Equations in rule bodies instantiate the span they fire in

An equation is not a constraint: when its rule fires on a span, the span is
instantiated by the equation's most general unifier, and refuted when there
is none. In the answer shown, a firing replaces the matched atoms by the
rule's body, so `(pin z)` leaves the store; a rule keeps an atom by writing it
back. -/

/-- `theory pin { (pin $x) <=> $x = z. }` from conformance case 4. -/
def pinT : Theory := [rule [ap "pin" [v 0]] (.conj [(v 0, c "z")] [])]
/-- `(same $x $y) <=> $x = $y.` -/
def sameT : Theory := [rule [ap "same" [v 0, v 1]] (.conj [(v 0, v 1)] [])]
/-- `(cyc $x) <=> $x = (s $x).`: no finite term solves it. -/
def cycT : Theory := [rule [ap "cyc" [v 0]] (.conj [(v 0, ap "s" [v 0])] [])]
/-- `(wrap (f $x)) <=> (pin $x).` and the `pin` rule: the equation is
reached only after a firing that adds a constraint. -/
def wrapT : Theory := rule [ap "wrap" [ap "f" [v 0]]] (.conj [] [ap "pin" [v 0]]) :: pinT
def pinSpan : Rel := .rw (ap "pair" [v 0, v 1]) (v 1) [ap "pin" [v 0]]

theorem pinT_wellFormed : ∀ ρ ∈ pinT, ρ.WellFormed := by decide
theorem sameT_wellFormed : ∀ ρ ∈ sameT, ρ.WellFormed := by decide
theorem cycT_wellFormed : ∀ ρ ∈ cycT, ρ.WellFormed := by decide
theorem wrapT_wellFormed : ∀ ρ ∈ wrapT, ρ.WellFormed := by decide

-- Conformance case 4, `pin`: the equation instantiates `$x` to `z`.
#guard runR001 ⟨[], pinT⟩ pinSpan 20 == (["(pair z $1) -> $1"], true)
-- An input the equation rules out leaves nothing.
#guard runR001 ⟨[], pinT⟩ (.seq (.at_ (ap "pair" [num 1, c "a"])) pinSpan) 20 == ([], true)
#guard runR001 ⟨[], pinT⟩ (.seq (.at_ (ap "pair" [num 0, c "a"])) pinSpan) 20 ==
  (["(pair z a) -> a"], true)
-- Run backwards, the equation still reaches the input side.
#guard runR001 ⟨[], pinT⟩ (.conv pinSpan) 20 == (["$1 -> (pair z $1)"], true)
-- The equation fires inside a composition: the left span's output meets the
-- right span's store.
#guard runR001 ⟨[], pinT⟩ (.seq (.rw (v 0) (ap "pair" [v 0, c "b"])) pinSpan) 20 ==
  (["z -> b"], true)
-- An equation between two variables identifies them.
#guard runR001 ⟨[], sameT⟩ (.rw (ap "pair" [v 0, v 1]) (v 0) [ap "same" [v 0, v 1]]) 20 ==
  (["(pair $1 $1) -> $1"], true)
-- Two atoms each force an equation; both apply.
#guard runR001 ⟨[], pinT⟩ (.rw (ap "pair" [v 0, v 1]) (v 0) [ap "pin" [v 0], ap "pin" [v 1]]) 20 ==
  (["(pair z z) -> z"], true)
-- An equation with no finite solution refutes the span.
#guard runR001 ⟨[], cycT⟩ (.rw (v 0) (v 0) [ap "cyc" [v 0]]) 20 == ([], true)
-- An equation reached after an earlier firing still instantiates the span.
#guard runR001 ⟨[], wrapT⟩ (.rw (v 0) (v 0) [ap "wrap" [ap "f" [v 0]]]) 20 ==
  (["z -> z"], true)
-- An equation can prune a recursive relation to one answer, and the query halts.

#guard runR001 ⟨[("nat", nat)], pinT⟩ (.seq (.call "nat") (.rw (v 0) (v 0) [ap "pin" [v 0]])) 60 ==
  (["z -> z"], true)

/-- `pin` together with `(pin z), bad <=> fail.` -/
def pinBadT : Theory := pinT ++ [rule [ap "pin" [c "z"], c "bad"] .fail]
theorem pinBadT_wellFormed : ∀ ρ ∈ pinBadT, ρ.WellFormed := by decide

-- `(pin z)` is replaced by the empty body.
#guard runR001 ⟨[], pinBadT⟩ pinSpan 20 == (["(pair z $1) -> $1"], true)
-- A `bad` met before simplification refutes the composition.
#guard runR001 ⟨[], pinBadT⟩ (.seq pinSpan (.rw (v 0) (v 0) [c "bad"])) 20 == ([], true)
-- An atom is replaced by the constraints of its rule's body, which fire in turn.
#guard runR001 ⟨[], noC⟩ (.rw (v 0) (v 0) [ap "no_c" [ap "a" [c "k", c "s"]]]) 20 ==
  (["$0 -> $0"], true)
#guard runR001 ⟨[], noC⟩ (.rw (v 0) (v 0) [ap "no_c" [ap "a" [c "k", ap "c" [v 0]]]]) 20 == ([], true)
/-- A theory where replacing `(p (f z))` by `(q z)` merges it with a `(q z)`
already in the store. -/
def mergeT : Theory :=
  [ rule [ap "p" [ap "f" [v 0]]] (.conj [] [ap "q" [v 0]]),
    rule [ap "q" [v 0], ap "r" [ap "g" [v 0]]] (.conj [] [ap "t" [v 0]]),
    rule [ap "q" [v 0], ap "t" [v 0]] .fail ]
theorem mergeT_wellFormed : ∀ ρ ∈ mergeT, ρ.WellFormed := by decide
-- `{(p (f z)), (q z), (r (g z))}` is refuted, so the composition is empty.
#guard runR001 ⟨[], mergeT⟩
  (.seq (.rw (v 0) (v 0) [ap "p" [ap "f" [v 0]]])
    (.seq (.at_ (c "z")) (.rw (v 0) (v 0) [ap "q" [v 0], ap "r" [ap "g" [v 0]]]))) 20 == ([], true)

/-! ## Write-back, no-op firings and rules that never rewrite -/

/-- `(pin $x) <=> $x = z, (pin z).`: the equation applies and the atom is
written back. -/
def pinKeepT : Theory := [rule [ap "pin" [v 0]] (.conj [(v 0, c "z")] [ap "pin" [c "z"]])]
theorem pinKeepT_wellFormed : ∀ ρ ∈ pinKeepT, ρ.WellFormed := by decide
-- The span is instantiated, the atom stays, and firing it again changes
-- nothing, so it is not taken and the query halts.
#guard runR001 ⟨[], pinKeepT⟩ (.rw (v 0) (v 0) [ap "pin" [v 0]]) 20 == (["z { (pin z) } -> z"], true)
#guard runR001 ⟨[], pinKeepT⟩ (.seq (.at_ (num 1)) (.rw (v 0) (v 0) [ap "pin" [v 0]])) 20 == ([], true)
/-- `(p $x) <=> (p (s $x)).`: its body is larger than its head, so it is
neither bounded nor decreasing and is never used. The store keeps `(p $x)`,
which every model may contain or not. -/
def growT : Theory := [rule [ap "p" [v 0]] (.conj [] [ap "p" [ap "s" [v 0]]])]
theorem growT_wellFormed : ∀ ρ ∈ growT, ρ.WellFormed := by decide
#guard runR001 ⟨[], growT⟩ (.rw (v 0) (v 0) [ap "p" [v 0]]) 20 == (["$0 { (p $0) } -> $0"], true)
/-- `(q $x), (q $y) <=> fail.`: both heads may land on one atom, since the
rule's axiom holds for `$x = $y` as well. -/
def twiceT : Theory := [rule [ap "q" [v 0], ap "q" [v 1]] .fail]
theorem twiceT_wellFormed : ∀ ρ ∈ twiceT, ρ.WellFormed := by decide
#guard runR001 ⟨[], twiceT⟩ (.rw (v 0) (v 0) [ap "q" [v 0]]) 20 == ([], true)
/-- `(r (f $x)) <=> (t $x).` and `(t $x) <=> .`: a body atom already in the
store is kept once. -/
def mergeTwiceT : Theory :=
  [rule [ap "r" [ap "f" [v 0]]] (.conj [] [ap "t" [v 0]]), rule [ap "t" [v 0]] (.conj [] [])]
theorem mergeTwiceT_wellFormed : ∀ ρ ∈ mergeTwiceT, ρ.WellFormed := by decide
#guard runR001 ⟨[], mergeTwiceT⟩ (.rw (v 0) (v 0) [ap "r" [ap "f" [v 0]], ap "t" [v 0]]) 20 ==
  (["$0 -> $0"], true)
/-- `(r $x) <=> (t $x).` keeps the size, so it is not decreasing and never
replaces an atom, even where the result would merge with an atom already
there. -/
def sameSizeT : Theory := [rule [ap "r" [v 0]] (.conj [] [ap "t" [v 0]])]
theorem sameSizeT_wellFormed : ∀ ρ ∈ sameSizeT, ρ.WellFormed := by decide
#guard runR001 ⟨[], sameSizeT⟩ (.rw (v 0) (v 0) [ap "r" [v 0], ap "t" [v 0]]) 20 ==
  (["$0 { (r $0), (t $0) } -> $0"], true)
/-- `(h $x $y $z) <=> (b $x $x).` is smaller than its head, but not under every
substitution (`$x` occurs twice), so it is not decreasing. -/
def dupT : Theory := [rule [ap "h" [v 0, v 1, v 2]] (.conj [] [ap "b" [v 0, v 0]])]
theorem dupT_wellFormed : ∀ ρ ∈ dupT, ρ.WellFormed := by decide
#guard runR001 ⟨[], dupT⟩ (.rw (v 0) (v 0) [ap "h" [v 0, v 1, v 2]]) 20 ==
  (["$0 { (h $0 $1 $2) } -> $0"], true)

/-! ## Tables keep stores as written; refutation and equations come from a closure -/

-- The table's answer keeps `(pin z)`; only the shown answer drops it.
#guard rawR001 ⟨[], pinT⟩ pinSpan 20 == (["(pair z $1) { (pin z) } -> $1"], true)
#guard rawR001 ⟨[], noC⟩ (.seq (.rw (v 0) (v 0) [ap "no_c" [v 0]]) (.at_ (ap "a" [c "k", v 0]))) 20 ==
  (["(a k $1) { (no_c (a k $1)) } -> (a k $1)"], true)
-- The closure derives `(eq $0 $1)` beside `(eq (s $0) (s $1))`, which meets `(neq $0 $1)`.
#guard runR001 ⟨[], eqNeq⟩
  (.rw (ap "pair" [v 0, v 1]) (v 0) [ap "eq" [ap "s" [v 0], ap "s" [v 1]], ap "neq" [v 0, v 1]]) 20 ==
  ([], true)
/-- `(q (s $x)) <=> (q $x).` -/
def peelT : Theory := [rule [ap "q" [ap "s" [v 0]]] (.conj [] [ap "q" [v 0]])]
theorem peelT_wellFormed : ∀ ρ ∈ peelT, ρ.WellFormed := by decide
-- `(k $0) {(q $0)}` covers `(k (s z)) {(q (s z))}` because the latter's store is
-- kept as written, so one answer is kept. Shown, its store is rewritten.
#guard rawR001 ⟨[], peelT⟩
  (.or (.rw (ap "k" [v 0]) (ap "k" [v 0]) [ap "q" [v 0]])
    (.rw (ap "k" [num 1]) (ap "k" [num 1]) [ap "q" [num 1]])) 20 ==
  (["(k $0) { (q $0) } -> (k $0)"], true)
#guard runR001 ⟨[], peelT⟩ (.rw (ap "k" [num 1]) (ap "k" [num 1]) [ap "q" [num 1]]) 20 ==
  (["(k (s z)) { (q z) } -> (k (s z))"], true)
/-- `(p $x), (r $x) <=> fail.` beside `(p (f $x)) <=> (r $x).` -/
def crossT : Theory :=
  [ rule [ap "p" [v 0], ap "r" [v 0]] .fail,
    rule [ap "p" [ap "f" [v 0]]] (.conj [] [ap "r" [v 0]]) ]
theorem crossT_wellFormed : ∀ ρ ∈ crossT, ρ.WellFormed := by decide
-- The closure keeps `(p (f z))` beside the `(r z)` it derives, so `(p z)` still
-- meets `(r z)`.
#guard runR001 ⟨[], crossT⟩ (.rw (v 0) (v 0) [ap "p" [ap "f" [c "z"]], ap "p" [c "z"]]) 20 == ([], true)

/-! ## Which rules the closure uses -/

#guard eqNeq.all (·.bounded)
#guard noC.all (·.bounded)
#guard pinT.all (·.bounded)
-- A rule that writes its head back is bounded.
#guard pinKeepT.all (·.bounded)
#guard mergeT.all (·.bounded)
-- A body larger than, or as large as, the heads is not.
#guard !growT.all (·.bounded)
#guard !sameSizeT.all (·.bounded)
-- Nor is a body that can outgrow its head under a substitution.
#guard !dupT.all (·.bounded)

/-! ## R001 halts on everything rung zero halts on

Neither half of these sequences terminates on its own, but rung zero's
normalizer kills every product, and every goal races that unfolding. -/

def natUpr : Program := prog [("nat", nat), ("upr", upr)]
#guard runR001 natUpr
  (.seq (.seq (.call "nat") (.at_ (ap "s" [v 0]))) (.seq (.at_ (c "z")) (.call "upr"))) 25 == ([], true)
-- The halves behind definitions, and spread over `|`.
def splitP : Program := prog [("nat", nat), ("upr", upr),
  ("x", .or (.seq (.call "nat") (.at_ (ap "s" [v 0]))) (.seq (.call "nat") (.at_ (ap "c" [v 0])))),
  ("y", .or (.seq (.at_ (c "z")) (.call "upr")) (.seq (.at_ (c "d")) (.call "upr")))]
#guard runR001 splitP (.seq (.call "x") (.call "y")) 25 == ([], true)

/-! ## P1.1 and P1.4: order and direction do not change the trace -/

-- Swapping and regrouping `|` give the very same run, even when a branch is
-- a recursive call that would otherwise share the root's table.
#guard traceR001 (prog [("lr", lr)]) (.or (.at_ (c "z")) (.seq (.call "lr") (.rw (v 0) (ap "s" [v 0])))) 8 ==
  traceR001 (prog [("lr", lr)]) (.or (.seq (.call "lr") (.rw (v 0) (ap "s" [v 0]))) (.at_ (c "z"))) 8
#guard traceR001 empty (.or (.or (.at_ (c "z")) .zero) (.rw (v 0) (v 0))) 10 ==
  traceR001 empty (.or (.at_ (c "z")) (.or .zero (.rw (v 0) (v 0)))) 10

#guard traceR001 loopNat (.or (.call "nat") (.rw (c "a") (c "b"))) 12 ==
  traceR001 loopNat (.or (.rw (c "a") (c "b")) (.call "nat")) 12
#guard traceR001 addP.dual (RelOf.dual (.seq (.call "add") (.at_ (num 2)))) 30 ==
  (R001.runtime.trace (R001.runtime.init addP (.seq (.call "add") (.at_ (num 2)))) 30).map
    (·.map fun a => showSpan a.swap)

end RwLog.Tests
