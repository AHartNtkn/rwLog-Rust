/-
# Rung 1

The first rung is the symmetric engine with no rewrite before it, run on one
orientation of its input (`rung`). With any unfolding race that meets its
specification, at every kernel rung:

* it has the laws (`rung_lawful`), so it is the base of a ladder
  (`rung_ladder`);
* its cost does not depend on the direction a query is written in: on an
  input, on its converse and on its mirror image it covers the same pairs
  having paid the same, and at most `8 * n + 12` ticks more for an input of
  size `n` (`rung_direction`, and within the bound of an admission
  `rung_directionFree`).

`rung1` is the one with the raced unfolding.
-/
import RwLog.Rungs.Symmetric.Correct
import RwLog.Rungs.Framework.OrientedLaws
import RwLog.Rungs.Framework.OrientedDirection
import RwLog.Rungs.Framework.Unfolding.Races

namespace RwLog

namespace Symmetric

/-- The symmetric engine as a rung: no rewrite, run on one orientation of
the input. -/
def rung (U : Unfolder) : CostedRung := ⟨[], engine @U, true⟩

variable {U : Unfolder}

/-- **The symmetric engine has the laws as a rung**, at every kernel rung. -/
theorem rung_lawful (hG : RwLog.Good @U) (κ : KernelRung) : (rung @U).Lawful κ :=
  fun _ => CostedRuntime.oriented_laws (Engine.sound (engine @U) κ.dom κ.kernel κ.refines κ.lawful)
    (complete (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG)
    (honestExhaustion (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG)

/-- **The symmetric engine is the base of a ladder.** -/
theorem rung_ladder (hG : RwLog.Good @U) (κ : KernelRung) : Ladder κ (rung @U) (rung @U) [] :=
  .base (rung_lawful hG κ)

/-- **The cost of the symmetric engine does not depend on the direction a
query is written in.** The rung, the rung run on the mirror image and the
rung run on the converse each cover what another has covered, having paid at
most what it has paid and `8 * n + 12` ticks, `n` the size of the input. -/
theorem rung_direction (hG : RwLog.Good @U) (κ : KernelRung) (A : ArtifactStore) :
    DirectionFree ((rung @U).machine κ A) fun c n => c + (8 * n + 12) :=
  CostedRuntime.oriented_directionFree
    (engine_selfConverse (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG)

/-- The same within the bound an admission asks (`Admits.direction`). -/
theorem rung_directionFree (hG : RwLog.Good @U) (κ : KernelRung) (A : ArtifactStore) :
    DirectionFree ((rung @U).machine κ A) (DirBound.fn ⟨12, 1⟩) :=
  CostedRuntime.oriented_directionFree_bound
    (engine_selfConverse (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG)

/-- Rung 1: the symmetric engine with the raced unfolding. -/
def rung1 : CostedRung := rung Unfold.raced

/-- **Rung 1 has the laws.** -/
theorem rung1_lawful (κ : KernelRung) : rung1.Lawful κ := rung_lawful good_raced κ

/-- **Rung 1 is the base of the ladder.** -/
theorem rung1_ladder (κ : KernelRung) : Ladder κ rung1 rung1 [] := rung_ladder good_raced κ

/-- **Rung 1 costs the same in both directions**, within `12 * (c + n + 1)`. -/
theorem rung1_directionFree (κ : KernelRung) (A : ArtifactStore) :
    DirectionFree (rung1.machine κ A) (DirBound.fn ⟨12, 1⟩) :=
  rung_directionFree good_raced κ A

end Symmetric

end RwLog
