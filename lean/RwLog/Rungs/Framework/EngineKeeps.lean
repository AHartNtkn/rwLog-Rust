/-
# The list an engine is held to, from what it must prove itself

`Runtime.Keeps` has thirteen parts. For an engine (`Trusted/Cost.lean`) at a
kernel that returns what a lawful domain returns, four are free: soundness
and generality (`Engine.sound`, `Engine.derivationGeneral`,
`Rungs/Framework/Derivation.lean`) and the two laws of `|`
(`Engine.orComm`, `Engine.orAssoc`, `Rungs/Framework/Writing.lean`).
Completeness pair by pair follows from completeness. The other eight are the
engine's own, and `Engine.Obligations` names them. `Obligations.keeps`
assembles the list.

Where each obligation usually comes from:

* `complete`: `Saturation.Fair.complete` (`Rungs/Framework/Saturation.lean`);
* `honest`: `Runtime.Tier0Cert.tier0` (`Rungs/Framework/Tier0.lean`);
* `honestProgress`: `Runtime.HonestProgress.of_never` for an engine that
  emits no certificate (`Rungs/Framework/SameTrace.lean`);
* `convTrace`, `dualTrace`: `oriented_convTrace`, `oriented_dualTrace`
  (`Rungs/Framework/Oriented.lean`);
* `terminates`, `emptySide`, `noSubsumed`: from the engine's invariant.

An engine that shows what a proved machine shows needs none of this:
`Runtime.SameTrace.keeps`.
-/
import RwLog.Rungs.Framework.Writing
import RwLog.Rungs.Framework.Tier0

namespace RwLog

namespace Engine

variable (E : Engine) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))

/-- What an engine must prove of its own runs to keep every property, with
the termination class of `Base`. -/
structure Obligations (Base : Runtime) : Prop where
  complete : (E.costedAt dom K hK).runtime.Complete
  honest : (E.costedAt dom K hK).runtime.HonestExhaustion
  honestProgress : (E.costedAt dom K hK).runtime.HonestProgress
  terminates : (E.costedAt dom K hK).runtime.TerminatesWhere Base
  emptySide : (E.costedAt dom K hK).runtime.EmptySide
  convTrace : (E.costedAt dom K hK).runtime.ConvTrace
  dualTrace : (E.costedAt dom K hK).runtime.DualTrace
  noSubsumed : (E.costedAt dom K hK).runtime.NoSubsumed

variable {E dom K hK}

/-- **An engine that meets its obligations keeps every property**, at every
kernel that returns what a domain returns that is lawful at well-formed
sorts. -/
theorem Obligations.keeps {Base : Runtime} (h : E.Obligations dom K hK Base)
    (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp) :
    (E.costedAt dom K hK).runtime.Keeps Base where
  sound := Engine.sound E dom K hK hD
  pointComplete := h.complete.pointwise
  honest := h.honest
  honestProgress := h.honestProgress
  derivationGeneral := Engine.derivationGeneral E dom K hK hD
  terminates := h.terminates
  orComm := Engine.orComm E dom K hK
  orAssoc := Engine.orAssoc E dom K hK
  emptySide := h.emptySide
  convTrace := h.convTrace
  dualTrace := h.dualTrace
  noSubsumed := h.noSubsumed
  complete := h.complete

end Engine

end RwLog
