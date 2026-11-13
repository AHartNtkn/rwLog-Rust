/-
# The charges of the Rust kernel on a worked composition

These checks compute one composition at the specification kernel and at the
kernel rung of the Rust store (`rustKernel`), and fail the build if what
they compute changes.

The two kernels return the same span. The ticks differ: the specification
kernel charges the sizes of the spans, and the Rust kernel charges the tick
bound proved of the Rust function. That bound is linear in the distinct
subterms, except the part for solving, which is the number of variables times
the distinct subterms and equations (`RwLogVerified.SolveCost`), so on small
spans it is above the sizes.

No engine is run here: the engines written against the kernel as it stood
before the derivation kernel are out of the build until they are ported
(`lean/PARKED.md`).
-/
import RwLogVerified.Kernel

namespace RwLogVerified.Tests

open RwLog

/-- `(b (a $x) $y) -> (b $x $y)` -/
def dec : Span :=
  ⟨.app (.app (.sym "b") (.app (.sym "a") (.var 0))) (.var 1),
   .app (.app (.sym "b") (.var 0)) (.var 1), []⟩

#guard ((rustKernel "nil").compose dec dec).val == (Kernel.std.compose dec dec).val
#guard (Kernel.std.compose dec dec).ticks == 38
#guard ((rustKernel "nil").compose dec dec).ticks == 5474

/-- `(x_i (x_{i+1} … x_{i+n}))`. -/
def wideT : Nat → Nat → Pat
  | 0, i => .var i
  | n + 1, i => .app (.var i) (wideT n (i + 1))

/-- The identity on a tuple of `n` variables. -/
def wide (n : Nat) : Span := ⟨wideT (n - 1) 0, wideT (n - 1) 0, []⟩

-- Composing `wide n` with itself solves `n` equations between variables.
-- Each removes a variable and rebuilds what is left, so the Rust spends ticks
-- that grow with the square of `n` (`verified/rust/tests/span.rs` measures
-- 104, 292, 863, 2785, 9749 and 36157), and so does the charge.
#guard [1, 2, 4, 8, 16, 32].map (fun n => ((rustKernel "nil").compose (wide n) (wide n)).ticks)
  == [896, 2734, 9386, 34594, 132626, 519154]

-- Space: the specification kernel holds the span it built; the Rust kernel
-- is charged every node it may have added.
#guard (Kernel.std.compose dec dec).held == 14
#guard ((rustKernel "nil").compose dec dec).held == 5474

end RwLogVerified.Tests
