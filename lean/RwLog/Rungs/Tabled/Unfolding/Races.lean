/-
# The unfolding races meet their specification

Each way of answering the unfolding race meets `UOk` at the derivation kernel
of every lawful domain (`Tabled.Good`): building the whole unfolding
(`good_eagerRace`), a walk in either direction (`good_walkRace`), the shared
evaluation (`good_sharedRace`), and two of them side by side (`UOk.race`), so
the left-to-right walk raced with the shared evaluation (`good_walkShared`)
and those raced with the right-to-left walk (`good_raced`), which is the race
of R004 and R005.

A race returns what one of its two sides returns (`Cost.race_val`), which is
all that is used of it here.
-/
import RwLog.Rungs.Tabled.Unfolding.Shared
import RwLog.Rungs.Tabled.Correct
import RwLog.Rungs.Framework.Race

namespace RwLog

namespace Tabled

open Answer

section

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

omit [DecidableEq R] in
/-- Two races that meet the specification, side by side. -/
theorem UOk.race {U V : GOracle R Rel (Ans D P) Cost} (hU : UOk D P U) (hV : UOk D P V) :
    UOk D P (fun d g => Cost.race (U d g) (V d g)) := by
  refine ⟨fun n g hg a ha => ?_, fun n g hg hfin k G hG hne => ?_⟩
  · have ha' : a ∈ (Cost.race (U n g) (V n g)).val.2 := ha
    rcases Cost.race_val (U n g) (V n g) with e | e
    · rw [e] at ha'
      exact hU.goal n g hg a ha'
    · rw [e] at ha'
      exact hV.goal n g hg a ha'
  · have hfin' : (Cost.race (U n g) (V n g)).val.1 = true := hfin
    show Cov (Cost.race (U n g) (V n g)).val.2 _
    rcases Cost.race_val (U n g) (V n g) with e | e
    · rw [e] at hfin' ⊢
      exact hU.final n g hg hfin' k G hG hne
    · rw [e] at hfin' ⊢
      exact hV.final n g hg hfin' k G hG hne

end

theorem good_eagerRace : Good Unfold.eagerRace :=
  fun _ _ K hK hL hP => Unfold.eagerRace_ok hL K hK hP

theorem good_walkRace (rev : Bool) : Good (Unfold.walkRace rev) :=
  fun _ _ K hK hL hP => Unfold.walkRace_ok hL K hK hP rev

theorem good_sharedRace : Good Unfold.sharedRace :=
  fun _ _ K hK hL hP => Unfold.sharedRace_ok hL K hK hP

theorem good_walkShared : Good Unfold.walkShared := by
  intro R _ _ D P K hK hL hP
  have h := (Unfold.walkRace_ok hL K hK hP false).race (Unfold.sharedRace_ok hL K hK hP)
  have e : Unfold.walkShared (K := DerivationKernel.over D K hK P) =
      fun d g => Cost.race (Unfold.walkRace (K := DerivationKernel.over D K hK P) false d g)
        (Unfold.sharedRace (K := DerivationKernel.over D K hK P) d g) := by
    funext d g
    exact hK.race _ _ _
  show UOk D P (Unfold.walkShared (K := DerivationKernel.over D K hK P))
  rw [e]
  exact h

/-- The race of R004 and R005 meets the specification. -/
theorem good_raced : Good Unfold.raced := by
  intro R _ _ D P K hK hL hP
  have h := (good_walkShared D P K hK hL hP).race (Unfold.walkRace_ok hL K hK hP true)
  have e : Unfold.raced (K := DerivationKernel.over D K hK P) =
      fun d g => Cost.race (Unfold.walkShared (K := DerivationKernel.over D K hK P) d g)
        (Unfold.walkRace (K := DerivationKernel.over D K hK P) true d g) := by
    funext d g
    exact hK.race _ _ _
  show UOk D P (Unfold.raced (K := DerivationKernel.over D K hK P))
  rw [e]
  exact h

end Tabled

end RwLog
