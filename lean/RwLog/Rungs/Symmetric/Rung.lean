/-
# Rung 1

The first rung is the symmetric engine with no rewrite before it, on the
input as it is given (`rung`). With any unfolding race that meets its
specification it has the laws at every kernel rung (`rung_lawful`), so it is
the base of a ladder (`rung_ladder`). `rung1` is the one with the raced
unfolding.
-/
import RwLog.Rungs.Symmetric.Correct
import RwLog.Rungs.Framework.Unfolding.Races

namespace RwLog

namespace Symmetric

/-- The symmetric engine as a rung: no rewrite, the input as it is given. -/
def rung (U : Unfolder) : CostedRung := ⟨[], engine @U, false⟩

/-- **The symmetric engine has the laws as a rung**, at every kernel rung. -/
theorem rung_lawful {U : Unfolder} (hG : RwLog.Good @U) (κ : KernelRung) :
    (rung @U).Lawful κ :=
  fun _ => laws (U := @U) (dom := κ.dom) (K := κ.kernel) (hK := κ.refines) κ.lawful hG

/-- **The symmetric engine is the base of a ladder.** -/
theorem rung_ladder {U : Unfolder} (hG : RwLog.Good @U) (κ : KernelRung) :
    Ladder κ (rung @U) (rung @U) [] :=
  .base (rung_lawful hG κ)

/-- Rung 1: the symmetric engine with the raced unfolding. -/
def rung1 : CostedRung := rung Unfold.raced

/-- **Rung 1 has the laws.** -/
theorem rung1_lawful (κ : KernelRung) : rung1.Lawful κ := rung_lawful good_raced κ

/-- **Rung 1 is the base of the ladder.** -/
theorem rung1_ladder (κ : KernelRung) : Ladder κ rung1 rung1 [] := rung_ladder good_raced κ

end Symmetric

end RwLog
