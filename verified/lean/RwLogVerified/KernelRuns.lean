/-
# The charges of the Rust kernel on a worked composition

These checks compute one composition at the specification kernel and at the
kernel rung of the Rust store (`rustKernel`), and fail the build if what
they compute changes.

The two kernels return the same span. The ticks differ: the specification
kernel charges the sizes of the spans, and the Rust kernel charges the tick
bound proved of the Rust function. That bound is a polynomial in the distinct
subterms with large constants (the bound for solving is cubic), so on small
spans it is far above the sizes (roadmap L42).

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
#guard ((rustKernel "nil").compose dec dec).ticks == 83460

-- Space: the specification kernel holds the span it built; the Rust kernel
-- is charged every node it may have added.
#guard (Kernel.std.compose dec dec).held == 14
#guard ((rustKernel "nil").compose dec dec).held == 83460

end RwLogVerified.Tests
