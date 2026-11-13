/-
# Running an engine at the Rust kernel

These checks run rung R002's engine at the specification kernel and at the
kernel rung of the Rust store (`rustKernel`), and fail the build if what
they compute changes. The engine's text is the same; only the kernel
differs.

On this query the two runs emit the same answers. The ticks differ: the
specification kernel charges the sizes of the spans, and the Rust kernel
charges the tick bounds proved of the Rust functions. Those bounds are
polynomials in the distinct subterms with large constants (the bound for
solving is cubic), so on small spans they are far above the sizes.
-/
import RwLogVerified.Kernel
import RwLog.Rungs.R005.Unfolder.R002.Gen

namespace RwLogVerified.Tests

open RwLog

/-- The answers emitted in the first `n` steps, whether the machine reported
that it is done, and the ticks paid. -/
def runAt (C : CostedRuntime) (P : Program) (q : Rel) (n : Nat) : List Span × Bool × Nat :=
  ((C.runtime.run (C.start P q) n).1, (C.runtime.run (C.start P q) n).2, C.paid P q n)

/-- `rel lr { z -> z | lr ; $x -> (s $x) }` -/
def lr : Rel :=
  .or (.span ⟨.sym "z", .sym "z", []⟩)
    (.seq (.call "lr") (.span ⟨.var 0, .app (.sym "s") (.var 0), []⟩))

def lrP : Program := ⟨[("lr", lr)], []⟩

def atStd : List Span × Bool × Nat := runAt R002.engine.costed lrP (.call "lr") 8

def atRust : List Span × Bool × Nat :=
  runAt (R002.engine.costedAt (rustKernel "nil")) lrP (.call "lr") 8

-- Two answers in eight steps, the same at both kernels.
#guard atStd.1.length == 2 && atStd.1 == atRust.1

-- What the eight steps cost at each kernel.
#guard atStd.2 == (false, 21862)
#guard atRust.2 == (false, 24699297)

-- One composition of `(b (a $x) $y) -> (b $x $y)` with itself.
def dec : Span :=
  ⟨.app (.app (.sym "b") (.app (.sym "a") (.var 0))) (.var 1),
   .app (.app (.sym "b") (.var 0)) (.var 1), []⟩

#guard ((rustKernel "nil").compose dec dec).val == (Kernel.std.compose dec dec).val
#guard (Kernel.std.compose dec dec).ticks == 38
#guard ((rustKernel "nil").compose dec dec).ticks == 83460

end RwLogVerified.Tests
