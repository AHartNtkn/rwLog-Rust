/-
# R005 at the domain of sorts

The kept properties of R005 (`Rungs/R005/Keeps.lean`) are proved at every
kernel that refines a lawful constraint domain. The domain of sorts
(`Sorts/Dom.lean`) is lawful at well-formed sorts (`Sorts.dom_lawful`), so at
any kernel that returns what it returns they hold with no hypothesis left.

`Engine.atSorts` is an engine at the domain of sorts with nothing charged:
each operation of the kernel is the operation of the domain
(`Kernel.uncharged`). It is the machine `Tests/SortsConformance.lean` runs,
and it says what a run shows, not what it costs. A kernel of sorts with
charges is roadmap L55.
-/
import RwLog.Rungs.R005.Keeps
import RwLog.Sorts.Dom

namespace RwLog

/-- An engine at the domain of sorts, with nothing charged. -/
def Engine.atSorts (E : Engine) : CostedRuntime :=
  E.costedAt (R := Sorts.Rep) Sorts.dom (fun S => Kernel.uncharged (Sorts.dom S))
    (fun S => Kernel.uncharged_refines (Sorts.dom S))

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

/-- The machine the tests run keeps every property. -/
theorem R005.keeps_atSorts : R005.engine.atSorts.runtime.Keeps R001.engine.atSorts.runtime :=
  R005.keeps_sorts

end RwLog
