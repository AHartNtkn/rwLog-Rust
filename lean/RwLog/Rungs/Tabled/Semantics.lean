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

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The goal as the rules of the kernel name it. -/
def toGoal (g : GoalOf R Rel) : Goal R := ⟨g.lb, g.node, g.rb⟩

/-- A goal the machine may hold: its boundaries are boundaries, and its node
is a node of the normal form with first-order spans. -/
structure GoalOk (D : Domain R) (g : GoalOf R Rel) : Prop where
  lb : IsBound D g.lb
  rb : IsBound D g.rb
  normal : Normal g.node
  fo : g.node.FO

/-- The pairs of `lb ; G ; rb`, for a ground relation `G` the node of the
goal derives. -/
def pairsOf (P : Program) (g : GoalOf R Rel) (G : GRel) : PRel :=
  wrapAt P.sorts.interp g.lb (G.at P.sorts.interp) g.rb

/-- One of the answers relates every pair of `X`. -/
def Cov (as : List (Ans D P)) (X : PRel) : Prop :=
  ∃ a ∈ as, X ⊆ den P.sorts.interp a.span

omit [DecidableEq R] in
theorem Cov.mono {as as' : List (Ans D P)} {X X' : PRel} (h : Cov as X) (hs : ∀ a ∈ as, a ∈ as')
    (hX : X' ⊆ X) : Cov as' X' := by
  obtain ⟨a, ha, h⟩ := h
  exact ⟨a, hs a ha, hX.trans h⟩

/-! ## Pairs between boundaries -/

section wrap

variable {M : Interp}

omit [DecidableEq R] in
theorem mem_wrap (hL : D.Lawful M) {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb)
    {X : PRel} {x z : GTerm} :
    (x, z) ∈ wrapAt M lb X rb ↔ (x, x) ∈ bdenAt M lb ∧ (x, z) ∈ X ∧ (z, z) ∈ bdenAt M rb := by
  rw [mem_wrapAt]
  constructor
  · rintro ⟨u, v, h₁, h₂, h₃⟩
    obtain rfl := bden_eq hL hl h₁
    obtain rfl := bden_eq hL hr h₃
    exact ⟨h₁, h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨x, z, h₁, h₂, h₃⟩

omit [DecidableEq R] in
theorem wrap_comp (lb rb : Option R) (G₁ G₂ : GRel) :
    wrapAt M lb ((G₁.comp G₂).at M) rb =
      (wrapAt M lb (G₁.at M) (none : Option R)).comp (wrapAt M (none : Option R) (G₂.at M) rb) := by
  rw [at_comp]
  ext ⟨x, z⟩
  constructor
  · intro h
    obtain ⟨u, v, h₁, ⟨m, h₂, h₂'⟩, h₃⟩ := mem_wrapAt.1 h
    exact ⟨m, mem_wrapAt.2 ⟨u, m, h₁, h₂, rfl⟩, mem_wrapAt.2 ⟨m, v, rfl, h₂', h₃⟩⟩
  · rintro ⟨m, h₁, h₂⟩
    obtain ⟨u, v, p₁, p₂, p₃⟩ := mem_wrapAt.1 h₁
    obtain ⟨u', v', q₁, q₂, q₃⟩ := mem_wrapAt.1 h₂
    obtain rfl : m = v := p₃
    obtain rfl : u' = m := q₁
    exact mem_wrapAt.2 ⟨u, v', p₁, ⟨_, p₂, q₂⟩, q₃⟩

omit [DecidableEq R] in
theorem wrap_meet (hL : D.Lawful M) {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb)
    (G₁ G₂ : GRel) :
    wrapAt M lb ((G₁.meet G₂).at M) rb = wrapAt M lb (G₁.at M) rb ∩ wrapAt M lb (G₂.at M) rb := by
  rw [at_meet]
  ext ⟨x, z⟩
  simp only [Set.mem_inter_iff, mem_wrap hL hl hr]
  tauto

omit [DecidableEq R] in
theorem wrap_mono {lb rb : Option R} {X Y : PRel} (h : X ⊆ Y) :
    wrapAt M lb X rb ⊆ wrapAt M lb Y rb := by
  rintro ⟨x, z⟩ hx
  obtain ⟨u, v, h₁, h₂, h₃⟩ := mem_wrapAt.1 hx
  exact mem_wrapAt.2 ⟨u, v, h₁, h h₂, h₃⟩

omit [DecidableEq R] in
theorem wrap_empty (lb rb : Option R) : wrapAt M lb ∅ rb = ∅ :=
  Set.eq_empty_of_forall_notMem fun ⟨_, _⟩ h => by
    obtain ⟨_, _, _, h₂, _⟩ := mem_wrapAt.1 h
    exact h₂

omit [DecidableEq R] in
/-- The representative of a span between boundaries relates the pairs of the
span between the boundaries, and there is one unless there are no such
pairs. -/
theorem denO_spanBoth (hL : D.Lawful M) {s : Span} (hs : s.firstOrder = true)
    (lb rb : Option R) :
    Domain.denO M (spanBoth D lb s rb) = wrapAt M lb (s.den.at M) rb := by
  cases h : spanBoth D lb s rb with
  | some z => exact spanBoth_den hL h
  | none =>
    symm
    simp only [Domain.denO_none]
    unfold spanBoth at h
    cases hr : D.rep s with
    | none =>
      have : s.den.at M = ∅ := by rw [← Span.denAt_eq]; exact hL.rep_none s hs hr
      rw [this, wrap_empty]
    | some r =>
      have er : den M r = s.den.at M := by rw [hL.rep_some s r hr, Span.denAt_eq]
      rw [hr] at h
      simp only [Option.bind_some] at h
      refine Set.eq_empty_of_forall_notMem fun ⟨x, z⟩ hx => ?_
      obtain ⟨u, v, h₁, h₂, h₃⟩ := mem_wrapAt.1 hx
      rw [← er] at h₂
      cases lb with
      | none =>
        simp only [Option.bind_some] at h
        cases rb with
        | none => cases h
        | some t =>
          have := hL.compose_none r t h
          exact (Set.eq_empty_iff_forall_notMem.1 this (u, z)) ⟨v, h₂, h₃⟩
      | some l =>
        simp only at h
        cases hl : D.compose l r with
        | none =>
          have := hL.compose_none l r hl
          exact (Set.eq_empty_iff_forall_notMem.1 this (x, v)) ⟨u, h₁, h₂⟩
        | some y =>
          rw [hl] at h
          simp only [Option.bind_some] at h
          have ey := hL.compose_some l r y hl
          cases rb with
          | none => cases h
          | some t =>
            have := hL.compose_none y t h
            refine (Set.eq_empty_iff_forall_notMem.1 this (x, z)) ⟨v, ?_, h₃⟩
            rw [ey]; exact ⟨u, h₁, h₂⟩

end wrap

/-! ## Coverage, decided -/

section cover

variable (hL : D.Lawful P.sorts.interp)
include hL

omit [DecidableEq R] in
theorem covB_iff (y x : Ans D P) :
    covB D P y x = true ↔ den P.sorts.interp x.span ⊆ den P.sorts.interp y.span :=
  hL.covers_iff _ _

omit [DecidableEq R] in
theorem covB_refl (a : Ans D P) : covB D P a a = true := (covB_iff hL a a).2 subset_rfl

omit [DecidableEq R] in
theorem covB_trans (a b c : Ans D P) (h₁ : covB D P a b = true) (h₂ : covB D P b c = true) :
    covB D P a c = true :=
  (covB_iff hL a c).2 (((covB_iff hL b c).1 h₂).trans ((covB_iff hL a b).1 h₁))

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
