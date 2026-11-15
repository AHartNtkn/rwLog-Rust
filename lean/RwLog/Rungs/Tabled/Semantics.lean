/-
# Which pairs the answers of a goal cover

A goal `⟨lb, node, rb⟩` of the tabled machine and a ground relation `G` its
node derives stand for the pairs of `lb ; G ; rb` (`pairsOf`). This file says
which of those pairs an answer made by a rule of the kernel covers, from the
laws of the constraint domain, and how the pairs of a chain or a meet are
made of the pairs of the two sides of a split.
-/
import RwLog.Rungs.Tabled.Candidates
import RwLog.Kernel.NormalFormSpans
import RwLog.Kernel.NormalFormSize
import RwLog.Kernel.DomainLaws
import RwLog.Kernel.Wrap
import RwLog.Rungs.Framework.Void

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- A goal the machine may hold: its boundaries are boundaries, and its node
is a node of the normal form with first-order spans. -/
structure GoalOk (D : Domain R) (g : GoalOf R Rel) : Prop where
  lb : IsBound D g.lb
  rb : IsBound D g.rb
  normal : Normal g.node
  fo : g.node.FO

/-- One of the answers relates every pair of `X`. -/
def Cov (as : List (Ans D P)) (X : PRel) : Prop :=
  ∃ a ∈ as, X ⊆ den P.sorts.interp a.span

omit [DecidableEq R] in
theorem Cov.mono {as as' : List (Ans D P)} {X X' : PRel} (h : Cov as X) (hs : ∀ a ∈ as, a ∈ as')
    (hX : X' ⊆ X) : Cov as' X' := by
  obtain ⟨a, ha, h⟩ := h
  exact ⟨a, hs a ha, hX.trans h⟩

/-! ## Coverage, decided -/

section cover

variable (hL : D.Lawful P.sorts.interp)
include hL

variable (K : Kernel R Cost) (hK : K.Refines D)

/-- Every candidate is covered by an answer of the table or by one that
enters it. -/
theorem cov_fresh {old cands : List (Ans D P)} {X : PRel} (h : Cov cands X) :
    Cov (old ++ (fresh (K := DerivationKernel.over D K hK P) old cands).val) X := by
  obtain ⟨c, hc, hX⟩ := h
  rw [fresh_val]
  by_cases ho : (old.any fun t => covB D P t c) = true
  · obtain ⟨t, ht, htc⟩ := List.any_eq_true.1 ho
    exact ⟨t, List.mem_append_left _ ht, hX.trans ((covB_iff hL t c).1 htc)⟩
  · have hmem : c ∈ cands.filter fun c => !old.any fun t => covB D P t c := by
      rw [List.mem_filter]; exact ⟨hc, by simpa using ho⟩
    obtain ⟨z, hz, hzc⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) hmem
    exact ⟨z, List.mem_append_right _ hz, hX.trans ((covB_iff hL z c).1 hzc)⟩

omit hL in
/-- An answer that enters a table is a candidate that no answer of the table
covers. -/
theorem mem_fresh {old cands : List (Ans D P)} {a : Ans D P}
    (h : a ∈ (fresh (K := DerivationKernel.over D K hK P) old cands).val) :
    a ∈ cands ∧ ∀ t ∈ old, covB D P t a = false := by
  rw [fresh_val] at h
  have := List.mem_filter.1 (List.mem_maximaBy h)
  refine ⟨this.1, fun t ht => ?_⟩
  have h2 := this.2
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at h2
  simpa using h2 t ht

omit hL in
/-- The answers that enter a table in one round do not cover each other. -/
theorem fresh_pairwise (old cands : List (Ans D P)) :
    ((fresh (K := DerivationKernel.over D K hK P) old cands).val).Pairwise
      fun y x => covB D P y x = false ∧ covB D P x y = false := by
  rw [fresh_val]; exact List.maximaBy_pairwise _

/-! ## The rules -/

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

end Tabled

end RwLog
