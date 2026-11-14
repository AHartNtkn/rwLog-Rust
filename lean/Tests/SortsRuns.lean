import RwLog.Sorts.Loop
import RwLog.Sorts.Dom

/-!
# The read-time check on sorts

`Sorts.WellFormed` is decided when a program is read. These runs evaluate the
decision on the sorts of the examples (`lean/SORTS.md` section 5) and on the
declarations the condition rejects (section 4), and then how many members
conjunctions of sorts have (`Sorts.count`) and whether a conjunction is
inside a sort but for some terms (`Sorts.inclBut`), and the one root of the
values of a variable (`Sorts.sole`), stores brought to tight ones
(`Sorts.tighten`), and exclusions brought to normal form (`Sorts.normEx`,
`Sorts.assembled`), problems brought to their normal stores
(`Sorts.Prob.norm`), and the operations of the domain (`Sorts.dom`).
-/

namespace RwLog.Tests.SortsRuns

open RwLog RwLog.Sorts

def nat : Name × SortDef := ("nat", ⟨[("z", []), ("s", [some "nat"])], none⟩)

/-- The sorts of the examples. -/
def examples : Sorts :=
  [ ("prog", ⟨[("l", []), ("b", [some "prog"]), ("f", [some "prog", some "prog"])], none⟩),
    ("sk", ⟨[("k", []), ("s", []), ("a", [some "sk", some "sk"])], none⟩),
    ("name", ⟨[], some ([("app", 2), ("lam", 2)], none)⟩),
    ("neut", ⟨[("app", [some "neut", some "norm"])], some ([("lam", 2)], none)⟩),
    ("norm", ⟨[("app", [some "neut", some "norm"]), ("lam", [none, some "norm"])],
      some ([], none)⟩),
    ("pos", ⟨[("s", [none])], none⟩) ]

-- one recursive sort
#guard decide (Sorts.WellFormed [nat])

-- no sorts at all
#guard decide (Sorts.WellFormed [])

-- the sorts of the examples
#guard decide examples.WellFormed

-- a sort with one member binds its variable, and is accepted
#guard decide (Sorts.WellFormed [("unit", ⟨[("u", [])], none⟩)])

-- a sort with no member is accepted
#guard decide (Sorts.WellFormed [("none", ⟨[("s", [some "none"])], none⟩)])

-- two members: rejected
#guard !decide (Sorts.WellFormed [("bit", ⟨[("zero", []), ("one", [])], none⟩)])

-- finitely many members through a finite sort of arguments: rejected
#guard !decide (Sorts.WellFormed
  [("bit", ⟨[("zero", [])], none⟩), ("two", ⟨[("p", [some "bit"]), ("q", [some "bit"])], none⟩)])

-- two infinite sorts that share two constants and nothing recursive: rejected
#guard !decide (Sorts.WellFormed
  [ ("sk", ⟨[("k", []), ("s", []), ("a", [some "sk", some "sk"])], none⟩),
    ("kn", ⟨[("k", []), ("s", []), ("succ", [some "kn"])], none⟩) ])

-- the same two sorts sharing one constant: accepted
#guard decide (Sorts.WellFormed
  [ ("sk", ⟨[("k", []), ("s", []), ("a", [some "sk", some "sk"])], none⟩),
    ("kn", ⟨[("k", []), ("succ", [some "kn"])], none⟩) ])

/-! ## How many members a conjunction has -/

/-- Sorts with a conjunction of each size. -/
def sized : Sorts :=
  [ nat,
    ("zero", ⟨[("z", [])], none⟩),
    ("pair", ⟨[("p", [some "zero", some "zero"])], none⟩),
    ("void", ⟨[("v", [some "void"])], none⟩),
    ("any", ⟨[], some ([], none)⟩),
    ("notz", ⟨[], some ([("z", 0)], none)⟩) ]

#guard decide sized.WellFormed

-- a recursive sort has more than one member
#guard count sized {"nat"} = .many

-- no sorts required: every term
#guard count sized ∅ = .many

-- a sort with only a rest
#guard count sized {"any"} = .many

-- two sorts that share one constant
#guard count sized {"nat", "zero"} = .one (.sym "z")

-- the one member is built from the one member of each argument
#guard count sized {"pair"} = .one (Term.mk "p" [.sym "z", .sym "z"])

-- a rest that agrees with the one case
#guard count sized {"zero", "any"} = .one (.sym "z")

-- a sort whose only case needs a member of itself
#guard count sized {"void"} = .none

-- two sorts with no root in common
#guard count sized {"nat", "pair"} = .none

-- a rest that excepts the only root of the other sort
#guard count sized {"zero", "notz"} = .none

-- the rest leaves the recursive case
#guard count sized {"nat", "notz"} = .many

-- a sort that is not declared has no member
#guard count sized {"nat", "missing"} = .none

-- the examples: names are neutral, and neutral terms are normal
#guard count examples {"name", "neut", "norm"} = .many
#guard count examples {"prog", "sk"} = .none
#guard count examples {"sk", "pos"} = .none

/-! ## Inside a sort but for some terms -/

/-! The decisions range over every set of declared names, so each run has few
sorts. -/

def z : GTerm := .sym "z"
def s (t : GTerm) : GTerm := Term.mk "s" [t]
def p (a b : GTerm) : GTerm := Term.mk "p" [a, b]

/-- Leaving a term out moves a variable to a smaller sort. -/
def zk : Sorts :=
  [ ("zk", ⟨[("z", []), ("k", [some "zk"])], none⟩),
    ("kk", ⟨[("k", [some "zk"])], none⟩) ]

#guard decide zk.WellFormed

-- nothing left out: inclusion
#guard inclBut zk {"kk"} "zk" []
#guard !inclBut zk {"zk"} "kk" []

-- the one term outside is left out
#guard inclBut zk {"zk"} "kk" [z]

/-- The numbers, those above zero, and those above one. -/
def nats : Sorts :=
  [ nat,
    ("pos", ⟨[("s", [some "nat"])], none⟩),
    ("two", ⟨[("s", [some "pos"])], none⟩),
    ("zero", ⟨[("z", [])], none⟩) ]

#guard decide nats.WellFormed

#guard inclBut nats {"nat"} "pos" [z]

-- a term that is not the one outside
#guard !inclBut nats {"nat"} "pos" [s z]

-- more left out than needed
#guard inclBut nats {"nat"} "pos" [s z, z]

-- two terms outside, one deep
#guard !inclBut nats {"nat"} "two" [z]
#guard inclBut nats {"nat"} "two" [z, s z]
#guard !inclBut nats {"nat"} "two" [s z]

-- a root the sort has no case for: its one term must be left out
#guard inclBut nats {"zero"} "pos" [z]
#guard !inclBut nats {"nat"} "zero" [z]

-- a conjunction with no member is inside every sort
#guard inclBut nats {"zero", "pos"} "two" [z]

/-- Pairs. -/
def pairs : Sorts :=
  [ nat,
    ("pos", ⟨[("s", [some "nat"])], none⟩),
    ("zero", ⟨[("z", [])], none⟩),
    ("pz", ⟨[("p", [some "zero", some "nat"])], none⟩),
    ("pp", ⟨[("p", [some "zero", some "pos"])], none⟩) ]

#guard decide pairs.WellFormed

-- the other argument has one value, so the term left out is one term
#guard inclBut pairs {"pz"} "pp" [p z z]
#guard !inclBut pairs {"pz"} "pp" [p z (s z)]

/-- Pairs whose arguments both have many values. -/
def wide : Sorts :=
  [ nat,
    ("pos", ⟨[("s", [some "nat"])], none⟩),
    ("pn", ⟨[("p", [some "nat", some "nat"])], none⟩),
    ("qq", ⟨[("p", [some "pos", some "pos"])], none⟩) ]

#guard decide wide.WellFormed

-- the other argument has many values: one term left out is not enough
#guard !inclBut wide {"pn"} "qq" [p z z]

/-- Sorts with a rest. -/
def rests : Sorts :=
  [ nat,
    ("any", ⟨[], some ([], none)⟩),
    ("notz", ⟨[], some ([("z", 0)], none)⟩) ]

#guard decide rests.WellFormed

-- any term but one symbol
#guard inclBut rests {"any"} "notz" [z]
#guard !inclBut rests {"any"} "notz" [s z]
#guard !inclBut rests {"any"} "nat" [z]

/-! ## The one root of the values of a variable -/

-- the numbers have two roots
#guard sole nats {"nat"} [] = none

-- without zero, one
#guard sole nats {"nat"} [z] = some ("s", 1)

-- leaving out a term that is not the only one with its root
#guard sole nats {"nat"} [s z] = none

-- a sort with one case
#guard sole nats {"pos"} [] = some ("s", 1)
#guard sole nats {"pos"} [s z] = some ("s", 1)

-- one member, left out: no root
#guard sole nats {"zero"} [z] = none
#guard sole nats {"zero"} [] = some ("z", 0)

-- no member: no root
#guard sole nats {"zero", "pos"} [] = none

-- a rest has every other symbol
#guard sole rests {"any"} [z] = none
#guard sole rests {"nat", "notz"} [] = some ("s", 1)

/-! ## Tight stores -/

/-- The pattern and the sorts of the tight store. -/
def tight (S : Sorts) (s : CStore) : Option (Pat × List Conj) :=
  if hS : S.WellFormed then (tighten S hS s).map fun r => (r.t, r.c) else none

def zp : Pat := .sym "z"
def sp (t : Pat) : Pat := Term.mk "s" [t]

-- a number: nothing to replace
#guard tight nats ⟨.var 0, [{"nat"}], []⟩ = some (.var 0, [{"nat"}])

-- a number that is not zero is a successor
#guard tight nats ⟨.var 0, [{"nat"}], [[(.var 0, zp)]]⟩ = some (sp (.var 1), [∅, {"nat"}])

-- a sort with one case, twice
#guard tight nats ⟨.var 0, [{"two"}], []⟩ = some (sp (sp (.var 2)), [∅, ∅, {"nat"}])

-- neither zero nor one
#guard tight nats ⟨.var 0, [{"nat"}], [[(.var 0, zp)], [(.var 0, sp zp)]]⟩ =
  some (sp (sp (.var 2)), [∅, ∅, {"nat"}])

-- an argument with one value is written out
#guard tight pairs ⟨.var 0, [{"pz"}], []⟩ =
  some (Term.mk "p" [zp, .var 2], [∅, ∅, {"nat"}])

-- an exclusion that always holds: nothing is left
#guard tight nats ⟨.var 0, [{"nat"}], [[(.var 0, .var 0)]]⟩ = none

-- an exclusion between two variables replaces neither
#guard tight nats ⟨Term.mk "p" [.var 0, .var 1], [{"nat"}, {"nat"}], [[(.var 0, .var 1)]]⟩ =
  some (Term.mk "p" [.var 0, .var 1], [{"nat"}, {"nat"}])

/-- Two numbers. -/
def two (c₀ c₁ : Conj) : Raw := ⟨Term.mk "p" [.var 0, .var 1], [c₀, c₁], []⟩

-- an alias binds the later variable, whichever way it is written
#guard normEx nats (two {"nat"} {"nat"}) [(.var 1, .var 0)] = some [(1, .var 0)]
#guard normEx nats (two {"nat"} {"nat"}) [(.var 0, .var 1)] = some [(1, .var 0)]

-- a variable bound to a pattern
#guard normEx nats (two {"nat"} {"nat"}) [(.var 0, sp (.var 1))] = some [(0, sp (.var 1))]

-- the sorts of the bound variable leave the free one a single value
#guard normEx nats (two {"nat"} {"zero"}) [(.var 0, .var 1)] = some [(0, zp), (1, zp)]

-- the sorts of the two variables share nothing: the exclusion removes nothing
#guard normEx nats (two {"pos"} {"zero"}) [(.var 0, .var 1)] = none

-- a sort rejects the value outright
#guard normEx nats (two {"zero"} {"nat"}) [(.var 0, sp (.var 1))] = none

-- equations with no solution
#guard normEx nats (two {"nat"} {"nat"}) [(.var 0, sp (.var 0))] = none

-- two equations
#guard normEx nats (two {"nat"} {"nat"}) [(.var 0, sp (.var 1)), (.var 1, zp)] =
  some [(0, sp zp), (1, zp)]

-- an exclusion covered by another is dropped, and a repeated one is kept once
#guard (assembled nats (Term.mk "p" [.var 0, .var 1]) [{"nat"}, {"nat"}]
    [[(.var 0, sp (.var 1)), (.var 1, zp)], [(.var 1, zp)], [(zp, .var 1)]]).x = [[(1, zp)]]

-- exclusions that do not cover each other are both kept, in order
#guard (assembled nats (Term.mk "p" [.var 0, .var 1]) [{"nat"}, {"nat"}]
    [[(.var 1, zp)], [(.var 0, zp)]]).x = [[(0, zp)], [(1, zp)]]

/-- The normal store of a problem. -/
def norm (S : Sorts) (P : Prob) : Option Raw :=
  if hS : S.WellFormed then P.norm S hS else none

-- a number
#guard norm nats ⟨.var 0, [], [("nat", .var 0)], []⟩ = some ⟨.var 0, [{"nat"}], []⟩

-- a variable with no sort
#guard norm nats ⟨.var 0, [], [], []⟩ = some ⟨.var 0, [∅], []⟩

-- a number that is not zero is a successor
#guard norm nats ⟨.var 0, [], [("nat", .var 0)], [[(.var 0, zp)]]⟩ =
  some ⟨sp (.var 0), [{"nat"}], []⟩

-- a sort with one case
#guard norm nats ⟨.var 0, [], [("pos", .var 0)], []⟩ = some ⟨sp (.var 0), [{"nat"}], []⟩

-- neither zero nor one
#guard norm nats ⟨.var 0, [], [("nat", .var 0)], [[(.var 0, zp)], [(.var 0, sp zp)]]⟩ =
  some ⟨sp (sp (.var 0)), [{"nat"}], []⟩

-- a sort with one member is written out
#guard norm nats ⟨.var 0, [], [("zero", .var 0)], []⟩ = some ⟨zp, [], []⟩

-- two sorts that share nothing
#guard norm nats ⟨.var 0, [], [("zero", .var 0), ("pos", .var 0)], []⟩ = none

-- an equation is solved, and the sort moves to the variable left
#guard norm nats ⟨.var 5, [(.var 5, sp (.var 3))], [("nat", .var 5)], []⟩ =
  some ⟨sp (.var 0), [{"nat"}], []⟩

-- equations with no solution
#guard norm nats ⟨.var 0, [(.var 0, sp (.var 0))], [], []⟩ = none

-- two numbers that differ: the exclusion binds the later variable
#guard norm nats ⟨Term.mk "p" [.var 0, .var 1], [], [("nat", .var 0), ("nat", .var 1)],
    [[(.var 0, .var 1)]]⟩ =
  some ⟨Term.mk "p" [.var 0, .var 1], [{"nat"}, {"nat"}], [[(1, .var 0)]]⟩

-- the variables are numbered as they occur in the pattern
#guard norm nats ⟨Term.mk "p" [.var 7, .var 2], [], [("nat", .var 7), ("pos", .var 2)], []⟩ =
  some ⟨Term.mk "p" [.var 0, sp (.var 1)], [{"nat"}, {"nat"}], []⟩

-- an exclusion against a variable that is not in the pattern says nothing
#guard norm nats ⟨.var 0, [], [("nat", .var 0), ("nat", .var 1)], [[(.var 0, .var 1)]]⟩ =
  some ⟨.var 0, [{"nat"}], []⟩

-- an exclusion that the sorts already give is dropped
#guard norm nats ⟨Term.mk "p" [.var 0, .var 1], [], [("pos", .var 0), ("nat", .var 1)],
    [[(.var 0, zp)]]⟩ =
  some ⟨Term.mk "p" [sp (.var 0), .var 1], [{"nat"}, {"nat"}], []⟩

-- an exclusion that always holds
#guard norm nats ⟨.var 0, [], [("nat", .var 0)], [[]]⟩ = none

/-! The operations of the domain, on the sorts `nats`. -/

def isNat (v : Nat) : Pat := .app (.sym "nat") (.var v)
def differ (a b : Pat) : Pat := .app (.app (.sym neSym) a) b

/-- The identity on numbers. -/
def idSpan : Span := ⟨.var 0, .var 0, [isNat 0]⟩

/-- The successor of a number. -/
def succSpan : Span := ⟨.var 0, sp (.var 0), [isNat 0]⟩

/-- The store of a representative. -/
def raw (o : Option (Rep nats)) : Option Raw := o.map (·.1)

-- a span as written
#guard raw ((dom nats).rep idSpan) = some ⟨tpair (.var 0) (.var 0), [{"nat"}], []⟩
#guard raw ((dom nats).rep succSpan) = some ⟨tpair (.var 0) (sp (.var 0)), [{"nat"}], []⟩

-- two numbers that differ
#guard raw ((dom nats).rep ⟨.var 0, .var 1, [isNat 0, isNat 1, differ (.var 0) (.var 1)]⟩) =
  some ⟨tpair (.var 0) (.var 1), [{"nat"}, {"nat"}], [[(1, .var 0)]]⟩

-- a span that relates nothing
#guard raw ((dom nats).rep ⟨.var 0, .var 0, [isNat 0, .app (.sym "zero") (.var 0),
  .app (.sym "pos") (.var 0)]⟩) = none

-- the successor twice
#guard raw (do let a ← (dom nats).rep succSpan; (dom nats).compose a a) =
  some ⟨tpair (.var 0) (sp (sp (.var 0))), [{"nat"}], []⟩

-- the successor and the identity share no pair
#guard raw (((dom nats).rep succSpan).bind fun a =>
  ((dom nats).rep idSpan).bind fun i => (dom nats).meet a i) = none

-- the successor and itself
#guard raw (do let a ← (dom nats).rep succSpan; (dom nats).meet a a) =
  some ⟨tpair (.var 0) (sp (.var 0)), [{"nat"}], []⟩

-- the right ends of the successor
#guard raw (do let a ← (dom nats).rep succSpan; (dom nats).rightBound a) =
  some ⟨tpair (sp (.var 0)) (sp (.var 0)), [{"nat"}], []⟩

-- the converse of the successor
#guard raw (((dom nats).rep succSpan).map Answer.swap) =
  some ⟨tpair (sp (.var 0)) (.var 0), [{"nat"}], []⟩

-- the identity covers its meet with the successor's right ends
#guard (((dom nats).rep succSpan).bind fun a => ((dom nats).rightBound a).bind fun b =>
  ((dom nats).rep idSpan).map fun i => (dom nats).covers i b) = some true

end RwLog.Tests.SortsRuns
