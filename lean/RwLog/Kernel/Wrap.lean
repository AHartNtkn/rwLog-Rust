/-
# Pairs between boundaries

A goal `lb ; node ; rb` and a ground relation `G` its node derives stand for
the pairs of `lb ; G ; rb` (`wrapAt`, `Kernel/Derivation.lean`). This file
has what those pairs are when the boundaries are boundaries of a lawful
domain (`mem_wrap`), how the pairs of a chain and of a meet are made of the
pairs of their two sides (`wrap_comp`, `wrap_meet`), and that the
representative of a span between boundaries relates exactly the pairs of the
span between them, and exists unless there are none (`denO_spanBoth`).

Nothing here is about a machine.
-/
import RwLog.Kernel.Derivation
import RwLog.Kernel.DomainLaws

namespace RwLog

open Answer

variable {R : Type} [Answer R] {D : Domain R} {M : Interp}

/-! ## Pairs between boundaries -/


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

theorem wrap_meet (hL : D.Lawful M) {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb)
    (G₁ G₂ : GRel) :
    wrapAt M lb ((G₁.meet G₂).at M) rb = wrapAt M lb (G₁.at M) rb ∩ wrapAt M lb (G₂.at M) rb := by
  rw [at_meet]
  ext ⟨x, z⟩
  simp only [Set.mem_inter_iff, mem_wrap hL hl hr]
  tauto

theorem wrap_mono {lb rb : Option R} {X Y : PRel} (h : X ⊆ Y) :
    wrapAt M lb X rb ⊆ wrapAt M lb Y rb := by
  rintro ⟨x, z⟩ hx
  obtain ⟨u, v, h₁, h₂, h₃⟩ := mem_wrapAt.1 hx
  exact mem_wrapAt.2 ⟨u, v, h₁, h h₂, h₃⟩

theorem wrap_empty (lb rb : Option R) : wrapAt M lb ∅ rb = ∅ :=
  Set.eq_empty_of_forall_notMem fun ⟨_, _⟩ h => by
    obtain ⟨_, _, _, h₂, _⟩ := mem_wrapAt.1 h
    exact h₂

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

end RwLog
