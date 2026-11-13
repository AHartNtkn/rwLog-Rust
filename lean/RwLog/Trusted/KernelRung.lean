/-
# Kernel rungs

`Kernel.std` (`Trusted/Kernel.lean`) is the specification kernel: it says
what every operation on spans returns. What it charges is postulated.

A *kernel rung* is another kernel on the same spans, in the same monad of
charged computations, that returns what the specification kernel returns
(`Kernel.Refines`, `Trusted/Kernel.lean`) and whose charges are theorems
about a machine: each charge is the number of ticks within which a program on
the machine returns the operation's result, and its space is a bound on the
cells that program allocates. The charges of a kernel rung are therefore its
own, and they may credit what the machine does well, such as sharing.

Refinement is stated operation by operation. It says nothing about the ticks,
so an engine may behave differently at two kernels where it reads the ticks
(`race`, `metered`): what an engine returns at a kernel rung is proved from
`Refines`, and what it costs is proved from that rung's charges. What does
not depend on the charges is that its answers are sound: the derivation
kernel over any kernel rung makes only valid answers
(`DerivationKernel.over`).

`Engine.costedAt` (`Trusted/Cost.lean`) is an engine at a kernel rung;
`Engine.costed` is the engine at the specification kernel.

The operations on nodes of the normal form, and the interning that the rules
`join` and `meetA` do, are charged the same at every kernel rung
(`Trusted/Charged.lean`): no machine holds nodes yet (roadmap L45).
-/
import RwLog.Trusted.Cost

namespace RwLog

/-- At the specification kernel `Engine.costedAt` is `Engine.costed`. -/
theorem Engine.costedAt_std (E : Engine) :
    E.costedAt Kernel.std Kernel.std_refines = E.costed := rfl

end RwLog
