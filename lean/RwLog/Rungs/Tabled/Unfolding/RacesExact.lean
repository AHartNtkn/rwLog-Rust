/-
# The unfolding races are exact

An unfolding race is *exact* (`UEx`) when it says the unfolding of a goal to
a depth is final exactly when the unfolding has no open product
(`Unfolding/Model.lean`), and then answers with the closed products: its
answers relate exactly the relations of the closed products. When it does
not say so it has no answer.

Each way of answering the race is exact: building the whole unfolding
(`eagerRace_ex`), a walk in either direction (`walkRace_ex`), the shared
evaluation (`sharedRace_ex`), and two exact races side by side (`UEx.race`),
so the race of R004 and R005 (`raced_ex`).

Two exact races say the same of every goal, and their answers are the same
representatives (`UEx.agree`): representatives that relate the same pairs
are equal. So which side of a race finishes first changes nothing the tabled
machine can see but the order of the answers.
-/
import RwLog.Rungs.Tabled.Unfolding.SharedExact
import RwLog.Rungs.Tabled.Unfolding.Races

namespace RwLog

namespace Tabled

open Answer Unfold

section

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

local notation "𝕄" => P.sorts.interp

/-- An unfolding race that says what the unfolding is. -/
structure UEx (D : Domain R) (P : Program) (U : GOracle R Rel (Ans D P) Cost) : Prop where
  /-- It says the unfolding is final exactly when it has no open product. -/
  final : ∀ d g, GoalOk D g → ((U d g).val.1 = true ↔
    Final P P.sorts.interp d (bset P.sorts.interp g.lb) g.node
      (bset P.sorts.interp g.rb))
  /-- Its answers then relate exactly the relations of the closed
  products. -/
  closed : ∀ d g, GoalOk D g → (U d g).val.1 = true → ∀ X,
    (∃ a ∈ (U d g).val.2, den P.sorts.interp a.span = X) ↔
      X ∈ closedPart (SE P P.sorts.interp d (bset P.sorts.interp g.lb) g.node
        (bset P.sorts.interp g.rb))
  /-- Otherwise it has no answer. -/
  none : ∀ d g, (U d g).val.1 = false → (U d g).val.2 = []

omit [DecidableEq R] in
/-- Two exact races, side by side. -/
theorem UEx.race {U V : GOracle R Rel (Ans D P) Cost} (hU : UEx D P U) (hV : UEx D P V) :
    UEx D P (fun d g => Cost.race (U d g) (V d g)) := by
  refine ⟨fun d g hg => ?_, fun d g hg hfin X => ?_, fun d g hfin => ?_⟩
  · show (Cost.race (U d g) (V d g)).val.1 = true ↔ _
    rcases Cost.race_val (U d g) (V d g) with e | e <;> rw [e]
    · exact hU.final d g hg
    · exact hV.final d g hg
  · have hfin' : (Cost.race (U d g) (V d g)).val.1 = true := hfin
    show (∃ a ∈ (Cost.race (U d g) (V d g)).val.2, _) ↔ _
    rcases Cost.race_val (U d g) (V d g) with e | e <;> rw [e] at hfin' ⊢
    · exact hU.closed d g hg hfin' X
    · exact hV.closed d g hg hfin' X
  · have hfin' : (Cost.race (U d g) (V d g)).val.1 = false := hfin
    show (Cost.race (U d g) (V d g)).val.2 = []
    rcases Cost.race_val (U d g) (V d g) with e | e <;> rw [e] at hfin' ⊢
    · exact hU.none d g hfin'
    · exact hV.none d g hfin'

omit [DecidableEq R] in
/-- Two exact races say the same of a goal, and the representatives of their
answers are the same. -/
theorem UEx.agree (hL : D.Lawful 𝕄) {U V : GOracle R Rel (Ans D P) Cost} (hU : UEx D P U)
    (hV : UEx D P V) (d : Nat) (g : GoalOf R Rel) (hg : GoalOk D g) :
    (U d g).val.1 = (V d g).val.1 ∧
      ∀ r : R, (∃ a ∈ (U d g).val.2, a.span = r) ↔ ∃ a ∈ (V d g).val.2, a.span = r := by
  have hv : (U d g).val.1 = (V d g).val.1 := by
    have h₁ := hU.final d g hg
    have h₂ := hV.final d g hg
    cases hu : (U d g).val.1 <;> cases hv : (V d g).val.1 <;> simp_all
  refine ⟨hv, ?_⟩
  cases hu : (U d g).val.1 with
  | false =>
    rw [hU.none d g hu, hV.none d g (hv ▸ hu)]
    simp
  | true =>
    have hv' : (V d g).val.1 = true := hv ▸ hu
    have key : ∀ {U V : GOracle R Rel (Ans D P) Cost}, UEx D P U → UEx D P V →
        (U d g).val.1 = true → (V d g).val.1 = true → ∀ r : R,
        (∃ a ∈ (U d g).val.2, a.span = r) → ∃ a ∈ (V d g).val.2, a.span = r := by
      rintro U V hU hV hu hv r ⟨a, ha, rfl⟩
      obtain ⟨b, hb, e⟩ := (hV.closed d g hg hv _).2 ((hU.closed d g hg hu _).1 ⟨a, ha, rfl⟩)
      exact ⟨b, hb, hL.canon _ _ e⟩
    exact fun r => ⟨key hU hV hu hv' r, key hV hU hv' hu r⟩

end

namespace Unfold

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

local notation "𝕄" => P.sorts.interp

omit [DecidableEq R] in
/-- The representatives kept of a list of answers are those of the list. -/
theorem foldl_keepNew_den [DecidableEq R] (as : List (Ans D P)) (X : PRel) :
    (∃ a ∈ as.foldl keepNew [], den 𝕄 a.span = X) ↔ ∃ a ∈ as, den 𝕄 a.span = X := by
  constructor
  · rintro ⟨a, ha, e⟩
    exact ⟨a, ((keepNew_spec as []).1 a ha).resolve_left (by simp), e⟩
  · rintro ⟨a, ha, e⟩
    obtain ⟨b, hb, hs⟩ := (keepNew_spec as []).2 a (.inr ha)
    exact ⟨b, hb, by rw [hs]; exact e⟩

/-- The answers kept of the items of a walk are its closed items, and what
was kept before. -/
theorem foldl_keepItem (is : List (It D P)) : ∀ acc : List (Ans D P),
    is.foldl keepItem acc =
      (is.filterMap fun it => match it with
        | .closed a => some a
        | .opn _ => none).foldl keepNew acc := by
  induction is with
  | nil => intro acc; rfl
  | cons it is ih =>
    intro acc
    cases it with
    | closed a => simp only [List.foldl_cons, keepItem, List.filterMap_cons, ih]
    | opn t => simp only [List.foldl_cons, keepItem, List.filterMap_cons, ih]

include hL in
theorem eagerRace_ex (hP : ProgFO P) :
    UEx D P (eagerRace (K := DerivationKernel.over D K hK P)) := by
  refine ⟨fun d g hg => eagerRace_final hL K hK hP d g hg, fun d g hg hfin X => ?_,
    fun d g hfin => ?_⟩
  · have hex := eager_ex hL K hK hP d g.lb g.node g.rb hg.lb hg.rb hg.normal hg.fo
    rw [eagerRace_val] at hfin ⊢
    split at hfin
    · cases hfin
    · rename_i hop
      simp only [hop, Bool.false_eq_true, ite_false]
      rw [foldl_keepNew_den]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact hex.aex.sound a ha
      · exact fun hX => hex.aex.complete X hX
  · rw [eagerRace_val] at hfin ⊢
    split at hfin
    · rename_i hop
      simp only [hop, ite_true]
    · cases hfin

include hL in
theorem walkRace_ex (hP : ProgFO P) (rev : Bool) :
    UEx D P (walkRace (K := DerivationKernel.over D K hK P) rev) := by
  refine ⟨fun d g hg => walkRace_final hL K hK hP rev d g hg, fun d g hg hfin X => ?_,
    fun d g hfin => ?_⟩
  · have hn : IsBound D (if rev then g.rb else g.lb) := by
      cases rev <;> first | exact hg.lb | exact hg.rb
    have hf : IsBound D (if rev then g.lb else g.rb) := by
      cases rev <;> first | exact hg.lb | exact hg.rb
    have hex := walk_ex hL K hK hP rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
      (if rev then g.lb else g.rb) hn hf hg.normal hg.fo
    have hS : WS P 𝕄 rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
        (if rev then g.lb else g.rb) = SE P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb) := by
      cases rev <;> rfl
    rw [WT, hS] at hex
    rw [walkRace_val] at hfin ⊢
    generalize walkV (P := P) K hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
      (if rev then g.lb else g.rb) = is at hfin hex ⊢
    cases hop : is.any itOpn with
    | true => simp [hop] at hfin
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [foldl_keepItem, foldl_keepNew_den]
      show _ ↔ SP.closed X ∈ SE P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb)
      rw [← farD_closed_iff (rev := rev), ← hex, sem_closed_iff]
      constructor
      · rintro ⟨a, ha, e⟩
        obtain ⟨it, hit, hi⟩ := List.mem_filterMap.1 ha
        cases it with
        | closed b =>
          cases hi
          exact ⟨a, hit, e⟩
        | opn t => cases hi
      · rintro ⟨a, ha, e⟩
        exact ⟨a, List.mem_filterMap.2 ⟨_, ha, rfl⟩, e⟩
  · rw [walkRace_val] at hfin ⊢
    generalize walkV (P := P) K hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
      (if rev then g.lb else g.rb) = is at hfin ⊢
    cases hop : is.any itOpn with
    | true => simp
    | false => simp [hop] at hfin

include hL in
theorem sharedRace_ex (hP : ProgFO P) :
    UEx D P (sharedRace (K := DerivationKernel.over D K hK P)) := by
  refine ⟨fun d g hg => sharedRace_final hL K hK hP d g hg, fun d g hg hfin X => ?_,
    fun d g hfin => ?_⟩
  · obtain ⟨hex, -⟩ := evalS_ex hL K hK hP d ⟨g.lb, false⟩ g.node g.rb []
      (fun p hp => by cases hp) (fun p hp => by cases hp) hg.lb hg.rb hg.normal hg.fo
    have hS : WS P 𝕄 false d ⟨g.lb, false⟩ g.node g.rb =
        SE P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb) := rfl
    rw [WT, hS] at hex
    rw [sharedRace_val] at hfin ⊢
    split at hfin
    · rename_i hop
      simp only [hop, ite_true]
      show _ ↔ SP.closed X ∈ SE P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb)
      rw [← farD_closed_iff (rev := false), ← hex, sems_closed_iff]
    · cases hfin
  · rw [sharedRace_val] at hfin ⊢
    split at hfin
    · cases hfin
    · rename_i hop
      simp only [hop, Bool.false_eq_true, ite_false]

include hL in
/-- The race of R004 and R005 is exact. -/
theorem raced_ex (hP : ProgFO P) : UEx D P (raced (K := DerivationKernel.over D K hK P)) := by
  have h₁ := (walkRace_ex hL K hK hP false).race (sharedRace_ex hL K hK hP)
  have e₁ : walkShared (K := DerivationKernel.over D K hK P) =
      fun d g => Cost.race (walkRace (K := DerivationKernel.over D K hK P) false d g)
        (sharedRace (K := DerivationKernel.over D K hK P) d g) := by
    funext d g
    exact hK.race _ _ _
  have h₂ : UEx D P (walkShared (K := DerivationKernel.over D K hK P)) := by
    rw [e₁]; exact h₁
  have h₃ := h₂.race (walkRace_ex hL K hK hP true)
  have e₂ : raced (K := DerivationKernel.over D K hK P) =
      fun d g => Cost.race (walkShared (K := DerivationKernel.over D K hK P) d g)
        (walkRace (K := DerivationKernel.over D K hK P) true d g) := by
    funext d g
    exact hK.race _ _ _
  rw [e₂]; exact h₃

end Unfold

end Tabled

end RwLog
