/-
# What the symmetric engine keeps

The symmetric engine is run on one orientation of its input
(`CostedRuntime.oriented`): only so does it have the two mirror properties
(`oriented_convTrace`, `oriented_dualTrace`, `Rungs/Symmetric/Correct.lean`).
Run so, at every kernel that refines a constraint domain that is lawful at
well-formed sorts, and with any exact unfolding race that meets its
specification:

* `oriented_keeps`: it keeps every property of `Runtime.Keeps`, and halts
  wherever the tabled machine of any exact race halts.
* `oriented_keeps_R001`: so with the raced unfolding it halts wherever R001
  halts, which is the base R005 is held to (`R005.keeps`).

Everything is carried from the engine on the input as given by
`CostedRuntime.oriented_keeps`, with `sameHalt`
(`Rungs/Symmetric/SameHalt.lean`) and `voidSide`.
-/
import RwLog.Rungs.Symmetric.SameHalt
import RwLog.Rungs.Symmetric.FromTabled
import RwLog.Rungs.R005.Keeps

namespace RwLog

namespace Symmetric

variable {U U₀ : Unfolder} {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}
  (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)

include hD

/-- **The symmetric engine run on one orientation keeps every property**,
and halts wherever the tabled machine of any exact race halts. -/
theorem oriented_keeps (hG : RwLog.Good @U) (hE : Exact @U) (hG₀ : RwLog.Good @U₀)
    (hE₀ : Exact @U₀) :
    ((engine @U).costedAt dom K hK).oriented.runtime.Keeps (Tabled.Rt @U₀ dom K hK) :=
  CostedRuntime.oriented_keeps (Engine.sound _ dom K hK hD) (complete hD hG)
    (honestExhaustion hD hG) (honestProgress hD hG) (Engine.derivationGeneral _ dom K hK hD)
    (noSubsumed hD hG)
    (fun P q wf hb => terminatesWhere hD hG hE P q wf
      ((Tabled.mirror_keeps hD hG hE hG₀ hE₀).terminates P q wf hb))
    (sameHalt hD hG hE) (voidSide hD hG) (oriented_convTrace hD hG) (oriented_dualTrace hD hG)

/-- **The symmetric engine with the raced unfolding, run on one orientation,
keeps every property and halts where R001 halts.** -/
theorem oriented_keeps_R001 :
    ((engine Unfold.raced).costedAt dom K hK).oriented.runtime.Keeps
      (R001.engine.costedAt dom K hK).runtime :=
  oriented_keeps hD good_raced exact_raced good_eagerRace exact_eagerRace

end Symmetric

end RwLog
