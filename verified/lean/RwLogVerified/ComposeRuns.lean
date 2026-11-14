/-
# The tick bound of composition on worked spans

`compose_spec` bounds the ticks the Rust composition of two spans spends by
`composeCost`. These checks compute that bound on the spans the Rust tests
measure (`verified/rust/tests/span.rs`), and fail the build if what they
compute changes.
-/
import RwLogVerified.Compose

namespace RwLogVerified.Tests

open RwLog

/-- `(b (a $x) $y) -> (b $x $y)` -/
def dec : Span :=
  ⟨.app (.app (.sym "b") (.app (.sym "a") (.var 0))) (.var 1),
   .app (.app (.sym "b") (.var 0)) (.var 1), []⟩

#guard composeCost "nil" dec dec == 5474

/-- `(x_i (x_{i+1} … x_{i+n}))`. -/
def wideT : Nat → Nat → Pat
  | 0, i => .var i
  | n + 1, i => .app (.var i) (wideT n (i + 1))

/-- The identity on a tuple of `n` variables. -/
def wide (n : Nat) : Span := ⟨wideT (n - 1) 0, wideT (n - 1) 0, []⟩

-- Composing `wide n` with itself solves `n` equations between variables.
-- Each removes a variable and rebuilds what is left, so the Rust spends ticks
-- that grow with the square of `n` (`verified/rust/tests/span.rs` measures
-- 104, 292, 863, 2785, 9749 and 36157), and so does the bound.
#guard [1, 2, 4, 8, 16, 32].map (fun n => composeCost "nil" (wide n) (wide n))
  == [896, 2734, 9386, 34594, 132626, 519154]

end RwLogVerified.Tests
