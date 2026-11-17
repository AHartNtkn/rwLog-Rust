/-
# The unfolding races meet their specification

Each way of answering the unfolding race meets `UOk` at the derivation kernel
of every lawful domain (`Good`): building the whole unfolding
(`good_eagerRace`), a walk in either direction (`good_walkRace`), the shared
evaluation (`good_sharedRace`), and two of them side by side (`UOk.race`), so
the left-to-right walk raced with the shared evaluation (`good_walkShared`)
and those raced with the right-to-left walk (`good_raced`), which is the race
rung 1 uses.

A race returns what one of its two sides returns (`Cost.race_val`), which is
all that is used of it here.

`Whole`: a race that says the unfolding is final has read whole every
derivation that relates a pair, whatever the nodes are taken to derive. The
race rung 1 uses has it (`whole_raced`).
-/
import RwLog.Rungs.Framework.Unfolding.Shared
import RwLog.Rungs.Framework.Race

namespace RwLog

open Goals

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

/-- The race of all three ways meets the specification. -/
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

/-! ## A final unfolding has read every derivation whole -/

section

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- When the race says the unfolding of a goal is final, every derivation of
the goal that relates a pair between its boundaries was read whole: and that
whatever the nodes are taken to derive (`Unfold.OLaws`), so of the
derivations of a program with more of them too. -/
def Whole (D : Domain R) (P : Program) (U : GOracle R Rel (Ans D P) Cost) : Prop :=
  ∀ (Der : Rel → Set GRel), Unfold.OLaws P Der → ∀ (n : Nat) (g : GoalOf R Rel), GoalOk D g →
    (U n g).val.1 = true → ∀ G ∈ Der g.node, (pairsOf P g G).Nonempty → G ∈ Unfold.GR P n g.node

omit [DecidableEq R] in
theorem Whole.race {U V : GOracle R Rel (Ans D P) Cost} (hU : Whole D P U) (hV : Whole D P V) :
    Whole D P (fun d g => Cost.race (U d g) (V d g)) := by
  intro Der hDer n g hg hfin G hG hne
  have hfin' : (Cost.race (U n g) (V n g)).val.1 = true := hfin
  rcases Cost.race_val (U n g) (V n g) with e | e
  · rw [e] at hfin'
    exact hU Der hDer n g hg hfin' G hG hne
  · rw [e] at hfin'
    exact hV Der hDer n g hg hfin' G hG hne

/-- The race of all three ways reads whole what it says is final. -/
theorem whole_raced (K : Kernel R Cost) (hK : K.Refines D) (hL : D.Lawful P.sorts.interp)
    (hP : ProgFO P) : Whole D P (Unfold.raced (K := DerivationKernel.over D K hK P)) := by
  have hw : ∀ rev, Whole D P (Unfold.walkRace (K := DerivationKernel.over D K hK P) rev) :=
    fun rev Der hDer n g hg hfin G hG hne =>
      Unfold.walkRace_whole hL K hK hP rev hDer hg hfin hG hne
  have hs : Whole D P (Unfold.sharedRace (K := DerivationKernel.over D K hK P)) :=
    fun Der hDer n g hg hfin G hG hne => Unfold.sharedRace_whole hL K hK hP hDer hg hfin hG hne
  have e₁ : Unfold.walkShared (K := DerivationKernel.over D K hK P) =
      fun d g => Cost.race (Unfold.walkRace (K := DerivationKernel.over D K hK P) false d g)
        (Unfold.sharedRace (K := DerivationKernel.over D K hK P) d g) := by
    funext d g
    exact hK.race _ _ _
  have e₂ : Unfold.raced (K := DerivationKernel.over D K hK P) =
      fun d g => Cost.race (Unfold.walkShared (K := DerivationKernel.over D K hK P) d g)
        (Unfold.walkRace (K := DerivationKernel.over D K hK P) true d g) := by
    funext d g
    exact hK.race _ _ _
  rw [e₂, e₁]
  exact ((hw false).race hs).race (hw true)

end

end RwLog
