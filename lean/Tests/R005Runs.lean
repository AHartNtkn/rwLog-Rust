import RwLog.Rungs.R005.Engine

/-!
# Running the yardstick

These checks run R005, the tabled machine with the raced unfolding
(`R004.engine`) and the tabled machine with the whole unfolding
(`R001.engine`) at the kernel of spans as they are written, and fail the build
if what they emit changes. They are the conformance cases of the review of
the Rust interpreter that need no constraint (cases 1, 5, 6 and 7); the cases
about constraints (2 and 4) are tests of the domain of sorts. Case 3 (answers
merged by a hash) has no program: every comparison an engine makes is an
operation of the kernel.
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

/-- Run an engine for at most `fuel` steps: the answers it emitted, and its
final report if it reported that it is done. -/
def runE (E : Engine) (P : Program) (q : Rel) (fuel : Nat) : List String × Option (List String) :=
  let r := E.costed.runtime.run (E.costed.start P q) fuel
  (r.1.map fun a => showSpan a.2, r.2.map (·.map fun a => showSpan a.2))

/-- What each step showed. -/
def traceE (E : Engine) (P : Program) (q : Rel) (fuel : Nat) : List (List String) :=
  (E.costed.runtime.trace (E.costed.start P q) fuel).map fun
    | .answers as => as.map fun a => showSpan a.2
    | .level n => [s!"level {n}"]
    | .final as => "final" :: as.map fun a => showSpan a.2

/-- The ticks paid by the end of the first `n` steps. -/
def paidE (E : Engine) (P : Program) (q : Rel) (n : Nat) : Nat := E.costed.paid P q n

def empty : Program := ⟨[], []⟩
def prog (defs : List (Name × Rel)) : Program := ⟨defs, []⟩

def add : Rel :=
  .or (.rw (ap "cons" [c "z", v 0]) (v 0))
    (.seq (.rw (ap "cons" [ap "s" [v 0], v 1]) (ap "cons" [v 0, v 1]))
      (.seq (.call "add") (.rw (v 0) (ap "s" [v 0]))))
def addP : Program := prog [("add", add)]

/-- `rel lr { z -> z | lr ; $x -> (s $x) }` -/
def lr : Rel := .or (.at_ (c "z")) (.seq (.call "lr") (.rw (v 0) (ap "s" [v 0])))
/-- `rel up { z -> z | up ; $x -> (s $x) }` -/
def up : Rel := .or (.at_ (c "z")) (.seq (.call "up") (.rw (v 0) (ap "s" [v 0])))
def callFirst : Rel :=
  .or (.seq (.call "call_first") (.rw (c "a") (c "b")))
    (.or (.at_ (c "a")) (.seq (.at_ (c "z")) (.call "up")))
def callLast : Rel :=
  .or (.at_ (c "a")) (.or (.seq (.at_ (c "z")) (.call "up"))
    (.seq (.call "call_last") (.rw (c "a") (c "b"))))
def nat : Rel :=
  .or (.at_ (c "z")) (.seq (.rw (ap "s" [v 0]) (v 0)) (.seq (.call "nat") (.rw (v 0) (ap "s" [v 0]))))
def natP : Program := prog [("nat", nat)]

/-- Every listed answer was emitted. -/
def contains (r : List String × Option (List String)) (xs : List String) : Bool := xs.all (· ∈ r.1)

/-- The run halted having emitted exactly the listed answers, in any order. -/
def exact (r : List String × Option (List String)) (xs : List String) : Bool :=
  r.2.isSome && xs.all (· ∈ r.1) && r.1.all (· ∈ xs)

def engines : List Engine := [R001.engine, R004.engine, R005.engine]

def zs : List String :=
  ["z -> z", "z -> (s z)", "z -> (s (s z))", "z -> (s (s (s z)))", "z -> (s (s (s (s z))))",
   "z -> (s (s (s (s (s z)))))"]

/-! ## Fixed-mode and recursion-free queries halt with the exact answer set -/

#guard engines.all fun E =>
  exact (runE E empty (.and (.rw (v 0) (ap "s" [v 0])) (.rw (ap "s" [v 0]) (v 0))) 20) []
#guard engines.all fun E =>
  exact (runE E addP (.seq (.at_ (ap "cons" [num 2, num 1])) (.call "add")) 40)
    ["(cons (s (s z)) (s z)) -> (s (s (s z)))"]
#guard engines.all fun E =>
  exact (runE E addP (.seq (.call "add") (.at_ (num 2))) 40)
    ["(cons z (s (s z))) -> (s (s z))", "(cons (s z) (s z)) -> (s (s z))",
      "(cons (s (s z)) z) -> (s (s z))"]
#guard engines.all fun E =>
  exact (runE E addP (.seq (.at_ (num 2)) (.conv (.call "add"))) 40)
    ["(s (s z)) -> (cons z (s (s z)))", "(s (s z)) -> (cons (s z) (s z))",
      "(s (s z)) -> (cons (s (s z)) z)"]

/-! ## Conformance case 1: left recursion keeps its answers, and halts in a fixed mode -/

#guard engines.all fun E => contains (runE E (prog [("lr", lr)]) (.call "lr") 26) zs
#guard engines.all fun E =>
  contains (runE E (prog [("lr", lr)]) (.seq (.at_ (c "z")) (.call "lr")) 26) zs
#guard engines.all fun E =>
  exact (runE E (prog [("lr", lr)]) (.seq (.call "lr") (.at_ (num 2))) 40) ["z -> (s (s z))"]
-- `lr` and `lr ; [$q -> $q]` have the same answers.
#guard engines.all fun E =>
  contains (runE E (prog [("lr", lr)]) (.seq (.call "lr") (.rw (v 0) (v 0))) 30) zs

/-! ## Conformance case 5: a finite conjunct restricts the other -/

#guard engines.all fun E => exact (runE E natP (.and (.rw (c "b") (c "a")) (.call "nat")) 40) []
#guard engines.all fun E => exact (runE E natP (.and (.call "nat") (.rw (c "b") (c "a"))) 40) []
#guard engines.all fun E =>
  exact (runE E natP (.and (.rw (num 1) (num 1)) (.call "nat")) 40) ["(s z) -> (s z)"]
#guard engines.all fun E => exact (runE E natP (.and (.rw (num 1) (num 0)) (.call "nat")) 40) []

/-! ## Conformance case 6: recursion beside an infinite branch still fires -/

def callP : Program := prog [("up", up), ("call_first", callFirst), ("call_last", callLast)]

#guard engines.all fun E =>
  contains (runE E callP (.call "call_first") 24) ["a -> a", "a -> b", "z -> (s (s (s z)))"]
#guard engines.all fun E =>
  contains (runE E callP (.call "call_last") 24) ["a -> a", "a -> b", "z -> (s (s (s z)))"]

/-! ## Conformance case 7: the order of `|` does not decide when an answer arrives

The members of a union are a set in the normal form, so two queries that
differ in the order or the grouping of `|` are the same node, and the run is
the same run. -/

#guard engines.all fun E =>
  traceE E (prog [("up", up)])
      (.or (.rw (c "a") (c "b")) (.or (.at_ (c "a")) (.seq (.at_ (c "z")) (.call "up")))) 12 ==
    traceE E (prog [("up", up)])
      (.or (.or (.seq (.at_ (c "z")) (.call "up")) (.at_ (c "a"))) (.rw (c "a") (c "b"))) 12

/-! ## An empty side makes `;` and `&` fail finitely, in either position -/

def loopNat : Program := prog [("nat", nat), ("loop", .call "loop")]

#guard engines.all fun E => exact (runE E loopNat (.seq (.call "nat") (.call "loop")) 30) []
#guard engines.all fun E => exact (runE E loopNat (.seq (.call "loop") (.call "nat")) 30) []
#guard engines.all fun E => exact (runE E loopNat (.and (.call "nat") (.call "loop")) 30) []
#guard engines.all fun E => exact (runE E loopNat (.and (.call "loop") (.call "nat")) 30) []

/-! ## Queries the Rust interpreter diverges on -/

/-- `rel upr { $x -> $x | [$x -> (s $x) ; upr] }` -/
def upr : Rel := .or (.rw (v 0) (v 0)) (.seq (.rw (v 0) (ap "s" [v 0])) (.call "upr"))

#guard engines.all fun E =>
  exact (runE E (prog [("upr", upr)]) (.seq (.call "upr") (.at_ (c "foo"))) 40) ["foo -> foo"]
#guard engines.all fun E =>
  exact (runE E (prog [("upr", upr)]) (.seq (.at_ (c "z")) (.seq (.call "upr") (.at_ (c "foo")))) 40)
    []
#guard engines.all fun E =>
  exact (runE E (prog [("lr", lr)]) (.seq (.at_ (num 1)) (.seq (.call "lr") (.at_ (c "z")))) 40) []

/-! ## The three evaluations of the unfolding agree

Whether the unfolding of a goal to a depth is final, and its answers when it
is, as the whole unfolding, each walk and the shared evaluation say. -/

open Tabled Tabled.Unfold in
/-- The answer of an unfolding race at the kernel of spans as written. -/
def askRace (U : Tabled.Unfolder) (P : Program) (q : Rel) (lb rb : Option Span) (d : Nat) :
    Bool × List String :=
  let r := (@U Span Rel (Ans Domain.written P) Cost (DerivationKernel.std P) d ⟨lb, q.norm, rb⟩).val
  (r.1, r.2.map fun a => showSpan a.span)

open Tabled.Unfold in
def races : List Tabled.Unfolder := [eagerRace, walkRace false, walkRace true, sharedRace, raced]

/-- All the races say the same of the goal at every depth below `n`. -/
def agree (P : Program) (q : Rel) (lb rb : Option Span) (n : Nat) : Bool :=
  (List.range n).all fun d =>
    let ref := askRace Tabled.Unfold.eagerRace P q lb rb d
    races.all fun U =>
      let r := askRace U P q lb rb d
      r.1 == ref.1 && r.2.all (· ∈ ref.2) && ref.2.all (· ∈ r.2)

def atom (t : Pat) : Option Span := some ⟨t, t, []⟩

#guard agree addP (.call "add") none none 9
#guard agree addP (.call "add") (atom (ap "cons" [num 2, num 1])) none 12
#guard agree addP (.call "add") none (atom (num 2)) 12
#guard agree addP (.conv (.call "add")) (atom (num 2)) none 12
#guard agree natP (.and (.rw (num 1) (num 1)) (.call "nat")) none none 9
#guard agree natP (.seq (.call "nat") (.and (.call "nat") (.rw (v 0) (v 0)))) (atom (num 1)) none 9
#guard agree natP (.seq (.and (.call "nat") (.rw (v 0) (v 0))) (.call "nat")) none (atom (num 1)) 9
#guard agree callP (.call "call_first") none none 8
#guard agree (prog [("upr", upr)]) (.seq (.call "upr") (.at_ (c "foo"))) (atom (c "z")) none 10
-- A meet of three: two members with no pair in common beside one that is
-- never read whole. Every evaluation says the same of it, wherever the open
-- member stands among the members.
#guard agree natP
  (.and (.rw (c "a") (c "a")) (.and (.rw (c "b") (c "b")) (.call "nat"))) none none 6
#guard agree natP
  (.and (.or (.rw (c "a") (c "a")) (.rw (c "a") (c "c")))
    (.and (.or (.rw (c "b") (c "b")) (.rw (c "b") (c "c"))) (.call "nat"))) none none 6
#guard agree natP
  (.and (.rw (c "a") (c "a"))
    (.and (.rw (c "b") (c "b")) (.or (.call "nat") (.rw (c "q") (c "q"))))) none none 6
#guard agree natP
  (.and (.or (.rw (c "a") (c "a")) (.rw (c "a") (c "c")))
    (.and (.or (.rw (c "b") (c "b")) (.rw (c "b") (c "c")))
      (.or (.call "nat") (.rw (c "q") (c "q"))))) none none 6
#guard agree natP
  (.seq (.rw (v 0) (v 0))
    (.and (.rw (c "a") (c "a")) (.and (.rw (c "b") (c "b")) (.call "nat")))) (atom (c "a")) none 6
-- The unfolding of a goal that is final at some depth is final from there on.
#guard (askRace Tabled.Unfold.eagerRace addP (.call "add") (atom (ap "cons" [num 2, num 1])) none 11)
  == (true, ["(cons (s (s z)) (s z)) -> (s (s (s z)))"])

end RwLog.Tests
