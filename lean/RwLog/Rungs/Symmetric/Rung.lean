/-
# Rung 1

The first rung is the symmetric engine with no rewrite before it, run on one
orientation of its input (`rung`). With any unfolding race and any reading of
edges that meet their specifications, at every kernel rung:

* it has the laws (`rung_lawful`);
* its cost does not depend on the direction a query is written in: on an
  input, on its converse and on its mirror image it covers the same levels
  and halts alike, having paid the same and at most `8 * n + 12` ticks more
  for an input of size `n` (`rung_direction`, and within the bound of an
  admission `rung_directionFree`).

So it is the base of a ladder (`rung_ladder`).

`rung1` is the one with the raced unfolding and the reading that composes
every run of spans at an edge. `bothWays` is the one that reads an edge both
ways side by side within a budget (`Capped.lean`): it has the laws and the same bound on
direction.
-/
import RwLog.Rungs.Symmetric.Correct
import RwLog.Rungs.Symmetric.Capped
import RwLog.Rungs.Framework.OrientedLaws
import RwLog.Rungs.Framework.OrientedDirection
import RwLog.Rungs.Framework.Unfolding.Races

namespace RwLog

namespace Symmetric

/-- The symmetric engine as a rung: no rewrite, run on one orientation of
the input. -/
def rung (U : Unfolder) (rd : EdgeReader) : CostedRung := ⟨[], engine @U @rd, true⟩

variable {U : Unfolder} {rd : EdgeReader}

/-- **The symmetric engine has the laws as a rung**, at every kernel rung. -/
theorem rung_lawful (hG : RwLog.Good @U) (hRd : GoodReader @rd) (κ : KernelRung) : (rung @U @rd).Lawful κ :=
  fun _ => CostedRuntime.oriented_laws (Engine.sound (engine @U @rd) κ.dom κ.kernel κ.refines κ.lawful)
    (complete (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG hRd)
    (honestExhaustion (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG hRd)

/-- **The cost of the symmetric engine does not depend on the direction a
query is written in.** The rung, the rung run on the mirror image and the
rung run on the converse each cover every level another has covered, and
halt where it has halted, having paid at most what it has paid and `8 * n + 12` ticks, `n` the size of the input. -/
theorem rung_direction (hG : RwLog.Good @U) (hRd : GoodReader @rd) (κ : KernelRung) (A : ArtifactStore) :
    DirectionFree ((rung @U @rd).machine κ A) fun c n => c + (8 * n + 12) :=
  CostedRuntime.oriented_directionFree
    (C := (engine @U @rd).costedAt κ.dom κ.kernel κ.refines κ.cells)
    (engine_selfConverse (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG hRd)

/-- The same within the bound an admission asks (`Admits.direction`). -/
theorem rung_directionFree (hG : RwLog.Good @U) (hRd : GoodReader @rd) (κ : KernelRung) (A : ArtifactStore) :
    DirectionFree ((rung @U @rd).machine κ A) (PolyBound.fn ⟨12, 1⟩) :=
  CostedRuntime.oriented_directionFree_bound
    (C := (engine @U @rd).costedAt κ.dom κ.kernel κ.refines κ.cells)
    (engine_selfConverse (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG hRd)

/-- Rung 1: the symmetric engine with the raced unfolding, reading edges by
composing every run of spans (`runsReader`). -/
def rung1 : CostedRung := rung Unfold.raced @runsReader

/-- **Rung 1 has the laws.** -/
theorem rung1_lawful (κ : KernelRung) : rung1.Lawful κ := rung_lawful good_raced good_runsReader κ

/-- **The symmetric engine is the base of a ladder.** -/
theorem rung_ladder (hG : RwLog.Good @U) (hRd : GoodReader @rd) (κ : KernelRung) :
    Ladder κ (rung @U @rd) (rung @U @rd) :=
  .base (rung_lawful hG hRd κ)

/-- **Rung 1 is the base of the ladder.** -/
theorem rung1_ladder (κ : KernelRung) : Ladder κ rung1 rung1 :=
  rung_ladder good_raced good_runsReader κ

/-- **Rung 1 costs the same in both directions**, within `12 * (c + n + 1)`. -/
theorem rung1_directionFree (κ : KernelRung) (A : ArtifactStore) :
    DirectionFree (rung1.machine κ A) (PolyBound.fn ⟨12, 1⟩) :=
  rung_directionFree good_raced good_runsReader κ A

/-- The symmetric engine with the raced unfolding, reading edges both ways
side by side within a budget (`cappedReader`). -/
def bothWays : CostedRung := rung Unfold.raced @cappedReader

/-- **The engine that reads edges both ways has the laws.** -/
theorem bothWays_lawful (κ : KernelRung) : bothWays.Lawful κ :=
  rung_lawful good_raced good_cappedReader κ

/-- **The engine that reads edges both ways costs the same in both
directions**, within `12 * (c + n + 1)`. -/
theorem bothWays_directionFree (κ : KernelRung) (A : ArtifactStore) :
    DirectionFree (bothWays.machine κ A) (PolyBound.fn ⟨12, 1⟩) :=
  rung_directionFree good_raced good_cappedReader κ A

end Symmetric

end RwLog
