/-
# What the tabled machines of R001 and R004 keep, at every lawful domain

`R001.engine` is the tabled machine with the unfolding race answered by
building the whole unfolding, and `R004.engine` the tabled machine with the
three evaluations raced. Each race meets the specification of the unfolding
race (`Tabled.good_eagerRace`, `Tabled.good_raced`), so at every kernel that
refines a domain that is lawful at well-formed sorts each machine

* is sound and no less general than a derivation (true of every engine);
* is complete, span by span and pair by pair;
* is honest when it reports that it is done, and certifies no progress;
* emits no answer covered by an earlier one;
* reports the maximal emitted answers when it is done;
* runs the same on two queries that differ by the order or grouping of `|`,
  the grouping of `;`, or the order or grouping of `&` (true of every
  engine).

Nothing here uses more of the domain than `Domain.Lawful`. What R005 is held
to beyond this list (halting where R001 halts, the run on a converse and on
the mirrored program, the empty side, and all of it for the mirrored
machine) needs the two runs of the mirror to gain the same answers in the
same round, which needs interfaces to be exact (roadmap L58).
-/
import RwLog.Rungs.R005.Engine
import RwLog.Rungs.Tabled.Unfolding.Races
import RwLog.Rungs.Framework.Writing

namespace RwLog

variable {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}
  (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)

/-- The properties of a tabled machine that hold at every lawful domain. -/
structure Runtime.TableKeeps (R : Runtime) : Prop where
  sound : R.Sound
  derivationGeneral : R.DerivationGeneral
  complete : R.Complete
  pointComplete : R.PointComplete
  honest : R.HonestExhaustion
  honestProgress : R.HonestProgress
  noSubsumed : R.NoSubsumed
  finalMaximal : R.FinalMaximal
  orComm : R.OrComm
  orAssoc : R.OrAssoc
  seqAssoc : R.SeqAssoc
  andComm : R.AndComm
  andAssoc : R.AndAssoc

include hD in
/-- The tabled machine with an unfolding race that meets its specification. -/
theorem Tabled.tableKeeps {U : Tabled.Unfolder} (hU : Tabled.Good @U) :
    ((Tabled.engine @U).costedAt dom K hK).runtime.TableKeeps where
  sound := Engine.sound _ dom K hK hD
  derivationGeneral := Engine.derivationGeneral _ dom K hK hD
  complete := Tabled.complete hD hU
  pointComplete := Tabled.pointComplete hD hU
  honest := Tabled.honestExhaustion hD hU
  honestProgress := Tabled.honestProgress hD hU
  noSubsumed := Tabled.noSubsumed hD hU
  finalMaximal := Tabled.finalMaximal hD hU
  orComm := Engine.orComm _ dom K hK
  orAssoc := Engine.orAssoc _ dom K hK
  seqAssoc := Engine.seqAssoc _ dom K hK
  andComm := Engine.andComm _ dom K hK
  andAssoc := Engine.andAssoc _ dom K hK

include hD in
theorem R001.tableKeeps : (R001.engine.costedAt dom K hK).runtime.TableKeeps :=
  Tabled.tableKeeps hD Tabled.good_eagerRace

include hD in
theorem R004.tableKeeps : (R004.engine.costedAt dom K hK).runtime.TableKeeps :=
  Tabled.tableKeeps hD Tabled.good_raced

end RwLog
