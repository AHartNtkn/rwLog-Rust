import Tests.R005Runs

/-!
# A chain restricted in the middle

`mid k` is `bit ; … ; bit ; ($x -> t_k) ; unbit ; … ; unbit` with `k` factors on
each side, where `t_k` is `z` under `k` wrappers. It has one answer, `$0 -> z`.
An interval of the chain that contains the middle span has one answer; an
interval that does not has `2 ^ length`.

These checks record what R004 and R005 pay for it under four bracketings of
the same chain. All four grow by about three times per step of `k` on both
rungs: the cost is in the unfolding race, which does not read the bracketing,
and racing the mirror image does not help because neither end is the cheap
one. The symmetric engine of `lean/SYMMETRIC_ENGINE.md` is designed to be
polynomial here.
-/

namespace RwLog.Tests

def midUnwrap (f : Sym) : Span := ⟨.app (.sym f) (.var 0), .var 0, []⟩

def midUnbit : Rel := .or (.span (midUnwrap "0")) (.span (midUnwrap "1"))

/-- `z` under `k` wrappers. -/
def midTarget : Nat → Pat
  | 0 => .sym "z"
  | k + 1 => .app (.sym "0") (midTarget k)

/-- `$x -> t_k`. -/
def midPin (k : Nat) : Rel := .span ⟨.var 0, midTarget k, []⟩

def midFactors (k : Nat) : List Rel :=
  List.replicate k R004.bit ++ [midPin k] ++ List.replicate k midUnbit

def nestRight : List Rel → Rel
  | [] => .zero
  | [a] => a
  | a :: as => .seq a (nestRight as)

def nestLeft : List Rel → Rel
  | [] => .zero
  | a :: as => as.foldl .seq a

def nestBalanced : Nat → List Rel → Rel
  | 0, _ => .zero
  | _, [] => .zero
  | _, [a] => a
  | fuel + 1, xs =>
    .seq (nestBalanced fuel (xs.take (xs.length / 2))) (nestBalanced fuel (xs.drop (xs.length / 2)))

/-- From the middle outwards: `bit ; ((… ; ($x -> t_k) ; …) ; unbit)`. -/
def nestMiddle (k : Nat) : Rel :=
  (List.range k).foldl (fun core _ => .seq R004.bit (.seq core midUnbit)) (midPin k)

/-- The four bracketings of `mid k`. -/
def midWritings (k : Nat) : List Rel :=
  [nestRight (midFactors k), nestLeft (midFactors k),
    nestBalanced (2 * k + 1) (midFactors k), nestMiddle k]

def midCosts (C : CostedRuntime) (k : Nat) : List Nat :=
  (midWritings k).map fun q => (costOf C ⟨[], []⟩ q 12).2.2

-- One answer, in every bracketing.
#guard (midWritings 2).all fun q =>
  (traceR005 ⟨[], []⟩ q 12).map (·.map showSpan) == [["$0 -> z"], []]

-- R004: right-nested, left-nested, balanced, from the middle outwards.
#guard (List.range 6).map (midCosts R004.costed) ==
  [[129, 129, 129, 129], [4497, 4756, 4497, 4497], [13708, 15755, 14775, 13950],
    [43112, 50907, 46355, 43556], [138816, 156667, 156610, 139806],
    [323318, 392393, 353034, 325942]]

-- R005, the same four.
#guard (List.range 5).map (midCosts R005.costed) ==
  [[969, 969, 969, 969], [33540, 34064, 33540, 33540], [126308, 133287, 131045, 126619],
    [276012, 562939, 280358, 276661], [397884, 1123954, 1071841, 398622]]

end RwLog.Tests
