import RwLog.Sorts.WF

/-!
# The read-time check on sorts

`Sorts.WellFormed` is decided when a program is read. These runs evaluate the
decision on the sorts of the examples (`lean/SORTS.md` section 5) and on the
declarations the condition rejects (section 4).
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

end RwLog.Tests.SortsRuns
