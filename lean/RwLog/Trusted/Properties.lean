/-
# The laws, and the ladder

There are two kinds of requirement, and they are never mixed.

## The laws

The laws say which answers a run gives. They say nothing of when or how: no
law mentions the order of answers, steps, runs that are equal or mirror
images of each other, halting, or cost. All of them hold of the first rung,
and no later rung adds one.

* `Sound` (`Trusted/Runtime.lean`): every answer relates only pairs the
  relation relates.
* `PointComplete`: every pair the relation relates is related by some answer
  after finitely many steps.
* `HonestExhaustion` (`Trusted/Runtime.lean`): if the run reports that it is
  done, its answers relate exactly the pairs of the relation.

`Runtime.Laws` is the three together. The meaning of a relation is its set
of ground pairs, and an answer is read by the pairs it relates.

A rung is its rewrites followed by a machine, and from the outside it is one
machine on the original input (`Rung.runtime`). A rewrite keeps the relation
and is held to nothing else: the answers of the run after it may be other
spans. `CostedRung.Lawful` asks the laws of the rung as that one machine.

Leaving out an answer that another answer covers is a filter on the final
set of answers. It is no law and does not constrain a run.

## The ladder

Performance is what an admission asks (`Admits`, `Trusted/Cost.lean`): a
strict win on a class, no trade for it on any other program beyond the bound
its kind of win allows, halting kept, and the cost of a relation forward and
backward comparable. It is stated on what a machine has paid when its
answers cover a level (`Trusted/Levels.lean`), and never by comparing two
runs step by step or answer by answer. `Ladder` is the rungs so admitted.
-/
import RwLog.Trusted.Cost

namespace RwLog

namespace Runtime

variable (R : Runtime)

/-- Completeness against the ground semantics, pair by pair: every pair the
query relates is related by some emitted answer. -/
def PointComplete : Prop :=
  ∀ P q, P.WellFormed q → ∀ p ∈ P.pairs q,
    ∃ n, ∃ a ∈ R.emitted (R.init P q) n, p ∈ Answer.den P.sorts.interp a

/-- **The laws.** Every answer relates only pairs the relation relates;
every pair the relation relates is related by some answer after finitely many
steps; and a run that reports it is done has answers that relate exactly the
pairs of the relation. -/
structure Laws : Prop where
  sound : R.Sound
  complete : R.PointComplete
  honest : R.HonestExhaustion

end Runtime

/-! ## Whole rungs -/

/-- The rung as one runtime on the original input, for an artifact store: its
first state is the machine's first state on the preprocessed input, the
preprocessors being run one after another at the kernel rung `κ`
(`Preprocessor.runAll`). -/
def Rung.runtime (G : Rung) (κ : KernelRung) (A : ArtifactStore) : Runtime where
  Ans := G.rt.Ans
  State := G.rt.State
  init P q := G.rt.init (Preprocessor.runAll κ G.pre A P q).val.1
    (Preprocessor.runAll κ G.pre A P q).val.2.1
  step := G.rt.step

/-! ## The ladder -/

/-- The rung `G` has the laws at the kernel rung `κ`: whatever the artifact
store, the rung as one machine on the original input has them. -/
def CostedRung.Lawful (G : CostedRung) (κ : KernelRung) : Prop :=
  ∀ A, ((G.rung κ).runtime κ A).Laws

/-- The ladder above the rung `base` at the kernel rung `κ`. The base has
the laws. A rung is put on top only by an admission above the rung below it,
and only if it has the laws. So every rung of a ladder has the laws. -/
inductive Ladder (κ : KernelRung) (base : CostedRung) : CostedRung → Prop where
  | base : base.Lawful κ → Ladder κ base base
  | admit {kind : Kind} {Old New : CostedRung} {b : Bounds} {d : PolyBound} {pre : Nat → Nat}
      {C : ProgClass} :
      Ladder κ base Old → Admits κ kind Old New b d pre C →
      New.Lawful κ → Ladder κ base New

end RwLog
