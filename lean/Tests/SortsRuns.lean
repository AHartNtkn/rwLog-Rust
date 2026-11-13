import RwLog.Sorts.Count

/-!
# The read-time check on sorts

`Sorts.WellFormed` is decided when a program is read. These runs evaluate the
decision on the sorts of the examples (`lean/SORTS.md` section 5) and on the
declarations the condition rejects (section 4), and then how many members
conjunctions of sorts have (`Sorts.count`).
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

end RwLog.Tests.SortsRuns
