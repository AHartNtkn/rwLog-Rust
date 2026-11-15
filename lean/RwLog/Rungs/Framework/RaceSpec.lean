/-
# The unfolding race, as a machine that tables sees it

An *unfolding race* is asked, for a goal and a depth, whether the unfolding
of the goal to that depth is final and, if it is, what its answers are
(`GOracle`, `Unfolder`). The races are built in `Rungs/Framework/Unfold.lean`
and proved in `Rungs/Framework/Unfolding/`.

This file is what a machine needs to host one: the goals it may be asked
about (`GoalOk`), what it is for a list of answers to cover a set of pairs
(`Cov`) and what the join and the meet of two answers cover (`join_cov`,
`meet_cov`), the programs it is specified on (`ProgFO`), and its specification
at one kernel (`UOk`) and at the derivation kernel of every lawful domain
(`Good`).

Nothing here is about a machine.
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.Framework.Void
import RwLog.Kernel.NormalFormSpans
import RwLog.Rungs.Framework.Rules

namespace RwLog

open Answer Goals

/-- The unfolding race: is the goal's unfolding to this depth final, and its
answers if it is (none otherwise). -/
abbrev GOracle (S N A : Type) (M : Type → Type) := Nat → GoalOf S N → M (Bool × List A)

/-- An unfolding race for every derivation kernel. -/
abbrev Unfolder :=
  {S N A : Type} → {M : Type → Type} → [DerivationKernel S N A M] → GOracle S N A M

variable {R : Type} [Answer R] {D : Domain R} {P : Program}

/-- A goal a machine that tables may hold: its boundaries are boundaries, and
its node is a node of the normal form with first-order spans. -/
structure GoalOk (D : Domain R) (g : GoalOf R Rel) : Prop where
  lb : IsBound D g.lb
  rb : IsBound D g.rb
  normal : Normal g.node
  fo : g.node.FO

/-- One of the answers relates every pair of `X`. -/
def Cov (as : List (Ans D P)) (X : PRel) : Prop :=
  ∃ a ∈ as, X ⊆ den P.sorts.interp a.span

theorem Cov.mono {as as' : List (Ans D P)} {X X' : PRel} (h : Cov as X) (hs : ∀ a ∈ as, a ∈ as')
    (hX : X' ⊆ X) : Cov as' X' := by
  obtain ⟨a, ha, h⟩ := h
  exact ⟨a, hs a ha, hX.trans h⟩

/-! ## What the rules cover -/

section cover

variable [DecidableEq R] (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)
include hL

/-- The join of two answers covers the composition of what they cover. -/
theorem join_cov {a b : Ans D P} {X₁ X₂ : PRel}
    (hok : JoinOk D a.span a.goal.rb b.goal.lb b.span)
    (h₁ : X₁ ⊆ den P.sorts.interp a.span) (h₂ : X₂ ⊆ den P.sorts.interp b.span)
    (hne : (X₁.comp X₂).Nonempty) :
    ∃ c, (Ans.join D P K hK a b).val = some c ∧ X₁.comp X₂ ⊆ den P.sorts.interp c.span ∧
      c.goal = ⟨a.goal.lb, mkSeq (seqParts a.goal.node ++ seqParts b.goal.node), b.goal.rb⟩ := by
  have hsub : X₁.comp X₂ ⊆ (den P.sorts.interp a.span).comp (den P.sorts.interp b.span) :=
    fun p ⟨m, ha, hb⟩ => ⟨m, h₁ ha, h₂ hb⟩
  cases hc : D.compose a.span b.span with
  | none =>
    obtain ⟨p, hp⟩ := hne
    have := hL.compose_none _ _ hc
    exact absurd (hsub hp) (Set.eq_empty_iff_forall_notMem.1 this p)
  | some z =>
    obtain ⟨c, hv, hs, hg⟩ := Ans.join_ok K hK hok hc
    exact ⟨c, hv, by rw [hs, hL.compose_some _ _ _ hc]; exact hsub, hg⟩

/-- The meet of two answers covers the meet of what they cover. -/
theorem meet_cov {a b : Ans D P} {X₁ X₂ : PRel}
    (hok : MeetOk D a.span a.goal.lb a.goal.rb b.goal.lb b.goal.rb)
    (h₁ : X₁ ⊆ den P.sorts.interp a.span) (h₂ : X₂ ⊆ den P.sorts.interp b.span)
    (hne : (X₁ ∩ X₂).Nonempty) :
    ∃ c, (Ans.meetA D P K hK a b).val = some c ∧ X₁ ∩ X₂ ⊆ den P.sorts.interp c.span ∧
      c.goal = ⟨a.goal.lb, mkAnd (sortedParts (andParts a.goal.node ++ andParts b.goal.node)),
        a.goal.rb⟩ := by
  have hsub : X₁ ∩ X₂ ⊆ den P.sorts.interp a.span ∩ den P.sorts.interp b.span :=
    Set.inter_subset_inter h₁ h₂
  cases hc : D.meet a.span b.span with
  | none =>
    obtain ⟨p, hp⟩ := hne
    have := hL.meet_none _ _ hc
    exact absurd (hsub hp) (Set.eq_empty_iff_forall_notMem.1 this p)
  | some z =>
    obtain ⟨c, hv, hs, hg⟩ := Ans.meetA_ok K hK hok hc
    exact ⟨c, hv, by rw [hs, hL.meet_some _ _ _ hc]; exact hsub, hg⟩

end cover

/-- The body of a call is a node of the normal form. -/
theorem bodyOf_normal {e b : Rel} (hb : Charged.bodyOf P e = some b) : Normal b := by
  unfold Charged.bodyOf at hb
  split at hb
  · cases hb; exact normal_norm _
  · cases hb; exact normal_normConv _
  · cases hb

/-- The spans of the bodies of the program are first-order. -/
def ProgFO (P : Program) : Prop := ∀ s ∈ P.defs.flatMap fun d => d.2.spans, s.firstOrder = true

/-- The specification of an unfolding race at one kernel. -/
structure UOk (D : Domain R) (P : Program) (U : GOracle R Rel (Ans D P) Cost) : Prop where
  /-- Its answers are answers of the goal. -/
  goal : ∀ n g, GoalOk D g → ∀ a ∈ (U n g).val.2, a.goal = toGoal g
  /-- When it says the unfolding is final, its answers cover every derivation
  of the goal. -/
  final : ∀ n g, GoalOk D g → (U n g).val.1 = true → ∀ k G, G ∈ GDn P k g.node →
    (pairsOf P g G).Nonempty → Cov (U n g).val.2 (pairsOf P g G)

/-- The unfolding race meets its specification at the derivation kernel of
every lawful domain. -/
def Good (U : Unfolder) : Prop :=
  ∀ {R : Type} [Answer R] [DecidableEq R] (D : Domain R) (P : Program) (K : Kernel R Cost)
    (hK : K.Refines D), D.Lawful P.sorts.interp → ProgFO P →
      UOk D P (@U R Rel (Ans D P) Cost (DerivationKernel.over D K hK P))

end RwLog
