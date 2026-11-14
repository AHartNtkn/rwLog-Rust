/-
# What R005 keeps

R005 is the tabled machine with the three evaluations of the unfolding raced,
run on the root node and on its converse side by side
(`Rungs/R005/Engine.lean`). At every kernel that refines a constraint domain
that is lawful at well-formed sorts:

* `R005.keeps`: it keeps every property of `Runtime.Keeps`, with R001 (the
  tabled machine that builds the whole unfolding) as the base whose halting
  it keeps. `R004.keeps` and `R001.keeps` say the same of the two tabled
  machines.
* `R005.record`: the properties stated beside `Keeps` that it has. It runs
  the same on two queries that differ by the grouping of `;` or the order or
  grouping of `&` (`SeqAssoc`, `AndComm`, `AndAssoc`; true of every engine,
  since an engine sees a query through its normal form), and when it is done
  it reports the maximal answers it emitted (`FinalMaximal`).
* `R005.neverCertifies`: it emits no progress certificate. `HonestProgress`
  is a field of `Keeps` and holds because there is nothing to be honest
  about.

The fairness bound (`Fair` in `Trusted/Properties.lean`) is not in this
record. Both of its parts compare ticks, so they are statements about a
kernel's charges, and the only kernel with charges on master is the one of
spans as written, which is not lawful and is replaced by the domain of sorts
(roadmap L55). What is proved of R005 at every lawful kernel is that every
pair is covered at some step (`Keeps.pointComplete`); the roadmap row L36
carries the rest.

Nothing here uses a charge: every statement is about what a run shows.
-/
import RwLog.Rungs.R005.Tables
import RwLog.Rungs.Tabled.MirrorKeeps
import RwLog.Rungs.Tabled.Unfolding.RacesExact

namespace RwLog

variable {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}
  (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)

include hD

/-- R001 keeps every property, with itself as base. -/
theorem R001.keeps :
    (R001.engine.costedAt dom K hK).runtime.Keeps (R001.engine.costedAt dom K hK).runtime :=
  Tabled.tabled_keeps hD Tabled.good_eagerRace Tabled.exact_eagerRace
    Tabled.good_eagerRace Tabled.exact_eagerRace

/-- R004 keeps every property, and halts where R001 halts. -/
theorem R004.keeps :
    (R004.engine.costedAt dom K hK).runtime.Keeps (R001.engine.costedAt dom K hK).runtime :=
  Tabled.tabled_keeps hD Tabled.good_raced Tabled.exact_raced
    Tabled.good_eagerRace Tabled.exact_eagerRace

/-- **R005 keeps every property, and halts where R001 halts.** -/
theorem R005.keeps :
    (R005.engine.costedAt dom K hK).runtime.Keeps (R001.engine.costedAt dom K hK).runtime :=
  Tabled.mirror_keeps hD Tabled.good_raced Tabled.exact_raced
    Tabled.good_eagerRace Tabled.exact_eagerRace

/-- **R005 shows what R004 shows**, step for step, up to the order of the
answers of a step. -/
theorem R005.trace {P : Program} {q : Rel} (wf : P.WellFormed q) (n : Nat) :
    List.Forall₂ (Shown.Rel fun xs ys => xs.Perm ys)
      ((R005.engine.costedAt dom K hK).runtime.trace
        ((R005.engine.costedAt dom K hK).runtime.init P q) n)
      ((R004.engine.costedAt dom K hK).runtime.trace
        ((R004.engine.costedAt dom K hK).runtime.init P q) n) :=
  Tabled.mirror_trace hD Tabled.good_raced Tabled.exact_raced wf n

/-- The properties stated beside `Keeps` that a machine has. -/
structure Runtime.Record (R : Runtime) : Prop where
  seqAssoc : R.SeqAssoc
  andComm : R.AndComm
  andAssoc : R.AndAssoc
  finalMaximal : R.FinalMaximal

/-- **The record of R005.** -/
theorem R005.record : (R005.engine.costedAt dom K hK).runtime.Record where
  seqAssoc := Engine.seqAssoc _ dom K hK
  andComm := Engine.andComm _ dom K hK
  andAssoc := Engine.andAssoc _ dom K hK
  finalMaximal := Tabled.mirror_finalMaximal hD Tabled.good_raced Tabled.exact_raced

/-- **R005 emits no progress certificate.** -/
theorem R005.neverCertifies {P : Program} {q : Rel} (wf : P.WellFormed q) (k n : Nat) :
    ¬ (R005.engine.costedAt dom K hK).runtime.Certifies
      ((R005.engine.costedAt dom K hK).runtime.init P q) k n :=
  Tabled.mirror_neverCertifies hD Tabled.good_raced Tabled.exact_raced wf k n

end RwLog
