/-
# The charges of the search primitives

A coverage test of spans as written places the covering span's store in the
other's. That is a search, and it is charged for the search, not only for the
sizes of its arguments.
-/
import RwLog.Trusted.Cost

namespace RwLog.Tests.Charge

/-- `e($0, $1), …, e($(n-1), $n), e($n, end)`: a chain of `n + 1` atoms. -/
def chain (n : Nat) : Store :=
  ((List.range n).map fun i => Term.mk "e" [.var i, .var (i + 1)]) ++
    [Term.mk "e" [.var n, .sym "end"]]

/-- Every `e(i, j)` with `i, j < m`: no atom ends in `end`. -/
def grid (m : Nat) : Store :=
  (List.range m).flatMap fun i =>
    (List.range m).map fun j => Term.mk "e" [.sym (toString i), .sym (toString j)]

def covering (n : Nat) : Span := ⟨.sym "z", .sym "z", chain n⟩
def covered (m : Nat) : Span := ⟨.sym "z", .sym "z", grid m⟩

-- The chain is never placed (nothing ends in `end`), but only after every
-- way of placing its first `n` atoms was tried: `3 ^ n` of them in the grid of
-- three nodes. The charge follows the search.
#guard (List.range 6).all fun n => (Charged.covers (covering n) (covered 3)).val == false
#guard (List.range 6).all fun n =>
  3 ^ n ≤ (Charged.covers (covering n) (covered 3)).ticks
#guard (List.range 6).map (fun n => Charged.coversWork (covering n) (covered 3)) ==
  [90, 900, 3330, 10620, 32490, 98100]

-- A covering span without a store is charged the two sizes and nothing else.
#guard (List.range 4).all fun m =>
  (Charged.covers ⟨.sym "z", .sym "z", []⟩ (covered m)).ticks ==
    (⟨.sym "z", .sym "z", []⟩ : Span).size + (covered m).size

end RwLog.Tests.Charge
