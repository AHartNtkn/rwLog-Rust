/-
# What the rules of the derivation kernel return

The rules of `DerivationKernel.over` (`Trusted/Kernel.lean`), one by one:
when a rule returns an answer, and which. An answer is determined by its goal
and its representative (`Ans.ext'`), so each is an equivalence.
-/
import RwLog.Rungs.Framework.KernelAt

namespace RwLog

namespace Ans

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

omit [DecidableEq R] in
theorem ext' {a b : Ans D P} (hg : a.goal = b.goal) (hs : a.span = b.span) : a = b := by
  cases a; cases b; cases hg; cases hs; rfl

omit [DecidableEq R] in
theorem ofCost_val {r : Cost (Option R)} {f : ∀ c, r.val = some c → Ans D P} {c : Ans D P} :
    (ofCost r f).val = some c ↔ ∃ z h, r.val = some z ∧ f z h = c := by
  unfold ofCost
  simp only
  split
  · next z h =>
    simp only [Option.some.injEq]
    constructor
    · intro e; exact ⟨z, h, h, e⟩
    · rintro ⟨z', h', e, rfl⟩
      have : z = z' := Option.some.inj (h.symm.trans e)
      subst this; rfl
  · next h =>
    constructor
    · intro e; cases e
    · rintro ⟨z, h', -, -⟩; rw [h] at h'; cases h'

variable (K : Kernel R Cost) (hK : K.Refines D)

theorem leaf_val {lb rb : Option R} {n : Rel} {c : Ans D P} :
    (leaf D P K hK lb n rb).val = some c ↔
      ∃ s, n = .span s ∧ IsBound D lb ∧ IsBound D rb ∧ spanBoth D lb s rb = some c.span ∧
        c.goal = ⟨lb, .span s, rb⟩ := by
  have hsb := fun s => spanBothK_val hK lb s rb
  at_cost K hK
  unfold leaf
  simp only [Cost.bind_val]
  cases n with
  | span s =>
    simp only
    by_cases h : IsBound D lb ∧ IsBound D rb
    · rw [dite_eq_left_of_eq_true (eq_true h), ofCost_val]
      constructor
      · rintro ⟨z, hz, e, rfl⟩
        exact ⟨s, rfl, h.1, h.2, (hsb s).symm.trans e, rfl⟩
      · rintro ⟨s', e, -, -, hs, hg⟩
        cases e
        exact ⟨c.span, (hsb s).trans hs, (hsb s).trans hs, ext' hg.symm rfl⟩
    · rw [dite_eq_right_of_eq_false (eq_false h)]
      constructor
      · intro e; cases e
      · rintro ⟨s', -, h₁, h₂, -, -⟩; exact absurd ⟨h₁, h₂⟩ h
  | _ =>
    constructor
    · intro e; cases e
    · rintro ⟨s, e, -⟩; cases e

theorem join_val {a b c : Ans D P} :
    (join D P K hK a b).val = some c ↔
      JoinOk D a.span a.goal.rb b.goal.lb b.span ∧ D.compose a.span b.span = some c.span ∧
        c.goal = ⟨a.goal.lb, mkSeq (seqParts a.goal.node ++ seqParts b.goal.node), b.goal.rb⟩ := by
  at_cost K hK
  unfold join
  simp only [Cost.bind_val]
  by_cases h : JoinOk D a.span a.goal.rb b.goal.lb b.span
  · rw [dite_eq_left_of_eq_true (eq_true h), ofCost_val]
    constructor
    · rintro ⟨z, hz, e, rfl⟩
      exact ⟨h, (hK.compose _ _).symm.trans e, rfl⟩
    · rintro ⟨-, hs, hg⟩
      exact ⟨c.span, (hK.compose _ _).trans hs, (hK.compose _ _).trans hs, ext' hg.symm rfl⟩
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    constructor
    · intro e; cases e
    · rintro ⟨h', -⟩; exact absurd h' h

theorem meetA_val {a b c : Ans D P} :
    (meetA D P K hK a b).val = some c ↔
      MeetOk D a.span a.goal.lb a.goal.rb b.goal.lb b.goal.rb ∧
        D.meet a.span b.span = some c.span ∧
        c.goal = ⟨a.goal.lb, mkAnd (sortedParts (andParts a.goal.node ++ andParts b.goal.node)),
          a.goal.rb⟩ := by
  at_cost K hK
  unfold meetA
  simp only [Cost.bind_val]
  by_cases h : MeetOk D a.span a.goal.lb a.goal.rb b.goal.lb b.goal.rb
  · rw [dite_eq_left_of_eq_true (eq_true h), ofCost_val]
    constructor
    · rintro ⟨z, hz, e, rfl⟩
      exact ⟨h, (hK.meet _ _).symm.trans e, rfl⟩
    · rintro ⟨-, hs, hg⟩
      exact ⟨c.span, (hK.meet _ _).trans hs, (hK.meet _ _).trans hs, ext' hg.symm rfl⟩
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    constructor
    · intro e; cases e
    · rintro ⟨h', -⟩; exact absurd h' h

omit [DecidableEq R] in
theorem inj_val {a c : Ans D P} {u : Rel} {i : Nat} :
    (inj D P a u i).val = some c ↔
      u.unionParts[i]? = some a.goal.node ∧ c.span = a.span ∧
        c.goal = ⟨a.goal.lb, u, a.goal.rb⟩ := by
  unfold inj
  simp only [Cost.bind_val, Cost.pure_val]
  by_cases h : u.unionParts[i]? = some a.goal.node
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    constructor
    · intro e; cases e; exact ⟨h, rfl, rfl⟩
    · rintro ⟨-, hs, hg⟩; exact congrArg some (ext' hg.symm hs.symm)
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    constructor
    · intro e; cases e
    · rintro ⟨h', -⟩; exact absurd h' h

omit [DecidableEq R] in
theorem unfold_val {a c : Ans D P} {n : Rel} :
    (unfold D P a n).val = some c ↔
      Charged.bodyOf P n = some a.goal.node ∧ c.span = a.span ∧
        c.goal = ⟨a.goal.lb, n, a.goal.rb⟩ := by
  unfold unfold
  simp only [Cost.bind_val, Cost.pure_val]
  split
  · next m =>
    by_cases h : a.goal.node = (P.body m).norm
    · rw [dite_eq_left_of_eq_true (eq_true h)]
      constructor
      · intro e; cases e; exact ⟨by simp [Charged.bodyOf, h], rfl, rfl⟩
      · rintro ⟨-, hs, hg⟩; exact congrArg some (ext' hg.symm hs.symm)
    · rw [dite_eq_right_of_eq_false (eq_false h)]
      constructor
      · intro e; cases e
      · rintro ⟨h', -⟩; simp only [Charged.bodyOf, Option.some.injEq] at h'; exact absurd h'.symm h
  · next m =>
    by_cases h : a.goal.node = (P.body m).normConv
    · rw [dite_eq_left_of_eq_true (eq_true h)]
      constructor
      · intro e; cases e; exact ⟨by simp [Charged.bodyOf, h], rfl, rfl⟩
      · rintro ⟨-, hs, hg⟩; exact congrArg some (ext' hg.symm hs.symm)
    · rw [dite_eq_right_of_eq_false (eq_false h)]
      constructor
      · intro e; cases e
      · rintro ⟨h', -⟩; simp only [Charged.bodyOf, Option.some.injEq] at h'; exact absurd h'.symm h
  · next h₁ h₂ =>
    constructor
    · intro e; cases e
    · rintro ⟨h', -⟩
      unfold Charged.bodyOf at h'
      split at h'
      · exact (h₁ _ rfl).elim
      · exact (h₂ _ rfl).elim
      · cases h'

/-! ## A rule whose side condition holds returns an answer -/

theorem leaf_ok {lb rb : Option R} {s : Span} {z : R} (hl : IsBound D lb) (hr : IsBound D rb)
    (hs : spanBoth D lb s rb = some z) :
    ∃ c, (leaf D P K hK lb (.span s) rb).val = some c ∧ c.span = z ∧
      c.goal = ⟨lb, .span s, rb⟩ :=
  ⟨⟨⟨lb, .span s, rb⟩, z, Valid.leaf hl hr hs⟩,
    (leaf_val K hK).2 ⟨s, rfl, hl, hr, hs, rfl⟩, rfl, rfl⟩

theorem join_ok {a b : Ans D P} {z : R} (h : JoinOk D a.span a.goal.rb b.goal.lb b.span)
    (hc : D.compose a.span b.span = some z) :
    ∃ c, (join D P K hK a b).val = some c ∧ c.span = z ∧
      c.goal = ⟨a.goal.lb, mkSeq (seqParts a.goal.node ++ seqParts b.goal.node), b.goal.rb⟩ :=
  ⟨⟨_, z, Valid.join a.valid b.valid h hc⟩, (join_val K hK).2 ⟨h, hc, rfl⟩, rfl, rfl⟩

theorem meetA_ok {a b : Ans D P} {z : R}
    (h : MeetOk D a.span a.goal.lb a.goal.rb b.goal.lb b.goal.rb)
    (hc : D.meet a.span b.span = some z) :
    ∃ c, (meetA D P K hK a b).val = some c ∧ c.span = z ∧
      c.goal = ⟨a.goal.lb, mkAnd (sortedParts (andParts a.goal.node ++ andParts b.goal.node)),
        a.goal.rb⟩ :=
  ⟨⟨_, z, Valid.meet (x := a.goal.node) (y := b.goal.node) a.valid b.valid h hc⟩,
    (meetA_val K hK).2 ⟨h, hc, rfl⟩, rfl, rfl⟩

omit [DecidableEq R] in
theorem inj_ok {a : Ans D P} {u : Rel} {i : Nat} (h : u.unionParts[i]? = some a.goal.node) :
    ∃ c, (inj D P a u i).val = some c ∧ c.span = a.span ∧ c.goal = ⟨a.goal.lb, u, a.goal.rb⟩ :=
  ⟨⟨_, a.span, a.valid.inj (List.mem_of_getElem? h)⟩, inj_val.2 ⟨h, rfl, rfl⟩, rfl, rfl⟩

omit [DecidableEq R] in
theorem unfold_ok {a : Ans D P} {n : Rel} (h : Charged.bodyOf P n = some a.goal.node) :
    ∃ c, (unfold D P a n).val = some c ∧ c.span = a.span ∧ c.goal = ⟨a.goal.lb, n, a.goal.rb⟩ := by
  cases hv : (unfold D P a n).val with
  | some c => exact ⟨c, rfl, (unfold_val.1 hv).2⟩
  | none =>
    exfalso
    unfold unfold at hv
    simp only [Cost.bind_val, Cost.pure_val] at hv
    unfold Charged.bodyOf at h
    split at h
    · have h' := (Option.some.inj h).symm
      simp only at hv; rw [dite_eq_left_of_eq_true (eq_true h')] at hv; cases hv
    · have h' := (Option.some.inj h).symm
      simp only at hv; rw [dite_eq_left_of_eq_true (eq_true h')] at hv; cases hv
    · cases h

end Ans

end RwLog
