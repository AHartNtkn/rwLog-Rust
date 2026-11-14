/-
# R005 at the domain of sorts

The kept properties of R005 (`Rungs/R005/Keeps.lean`) are proved at every
kernel that refines a lawful constraint domain. The domain of sorts
(`Sorts/Dom.lean`) is lawful at well-formed sorts (`Sorts.dom_lawful`), so at
any kernel that returns what it returns they hold with no hypothesis left.

`Sorts.uncharged` is the kernel rung of the domain of sorts with nothing
charged: each operation of the kernel is the operation of the domain
(`Kernel.uncharged`). `Engine.atSorts` is an engine at it. It is the machine
the tests run, and it says what a run shows and what the engine itself
spends, not what the run costs: the kernel of sorts with charges is derived
on a machine (`verified/`), and its charges are not computed here.
-/
import RwLog.Rungs.R005.Keeps
import RwLog.Sorts.Dom

namespace RwLog

/-- The kernel rung of the domain of sorts with nothing charged. -/
@[reducible] def Sorts.uncharged : KernelRung where
  Rep := Sorts.Rep
  dom := Sorts.dom
  kernel S := Kernel.uncharged (Sorts.dom S)
  refines S := Kernel.uncharged_refines (Sorts.dom S)
  lawful _ hS := Sorts.dom_lawful hS

/-- An engine at the domain of sorts, with nothing charged. -/
def Engine.atSorts (E : Engine) : CostedRuntime := E.costed Sorts.uncharged

section

variable {K : ∀ S, Kernel (Sorts.Rep S) Cost} {hK : ∀ S, (K S).Refines (Sorts.dom S)}

/-- **R005 at the domain of sorts keeps every property, and halts where R001
halts**, at any kernel that returns what the domain returns. -/
theorem R005.keeps_sorts :
    (R005.engine.costedAt Sorts.dom K hK).runtime.Keeps
      (R001.engine.costedAt Sorts.dom K hK).runtime :=
  R005.keeps fun _ hS => Sorts.dom_lawful hS

/-- The record of R005 at the domain of sorts. -/
theorem R005.record_sorts : (R005.engine.costedAt Sorts.dom K hK).runtime.Record :=
  R005.record fun _ hS => Sorts.dom_lawful hS

end

/-- **R005 keeps every property at every kernel rung, and halts where R001
halts.** -/
theorem R005.keeps_rung (κ : KernelRung) :
    (R005.engine.costed κ).runtime.Keeps (R001.engine.costed κ).runtime :=
  R005.keeps κ.lawful

/-- The machine the tests run keeps every property. -/
theorem R005.keeps_atSorts : R005.engine.atSorts.runtime.Keeps R001.engine.atSorts.runtime :=
  R005.keeps_rung Sorts.uncharged

end RwLog
