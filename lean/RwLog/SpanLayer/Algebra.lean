/-
# Algebra of ground triple relations
-/
import RwLog.Kernel.Span

namespace RwLog

namespace GRel

/-- The identity: every term related to itself with the empty store. -/
def id : GRel := {x | x.2.1 = x.1 ∧ x.2.2 = ∅}

theorem comp_assoc (R S U : GRel) : (R.comp S).comp U = R.comp (S.comp U) := by
  ext ⟨a, b, X⟩
  simp only [comp, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, S₁₂, S₃, ⟨k, S₁, S₂, h₁, h₂, rfl⟩, h₃, rfl⟩
    exact ⟨k, S₁, S₂ ∪ S₃, h₁, ⟨m, S₂, S₃, h₂, h₃, rfl⟩, by simp [Finset.union_assoc]⟩
  · rintro ⟨k, S₁, S₂₃, h₁, ⟨m, S₂, S₃, h₂, h₃, rfl⟩, rfl⟩
    exact ⟨m, S₁ ∪ S₂, S₃, ⟨k, S₁, S₂, h₁, h₂, rfl⟩, h₃, by simp [Finset.union_assoc]⟩

theorem comp_id (R : GRel) : R.comp id = R := by
  ext ⟨a, b, X⟩
  simp only [comp, id, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, S₁, S₂, h₁, ⟨rfl, rfl⟩, rfl⟩; simpa using h₁
  · intro h; exact ⟨b, X, ∅, h, ⟨rfl, rfl⟩, by simp⟩

theorem id_comp (R : GRel) : id.comp R = R := by
  ext ⟨a, b, X⟩
  simp only [comp, id, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, S₁, S₂, ⟨rfl, rfl⟩, h₂, rfl⟩; simpa using h₂
  · intro h; exact ⟨a, ∅, X, ⟨rfl, rfl⟩, h, by simp⟩

theorem comp_mono {R R' S S' : GRel} (h₁ : R ⊆ R') (h₂ : S ⊆ S') : R.comp S ⊆ R'.comp S' :=
  fun _ ⟨m, A, B, ha, hb, hx⟩ => ⟨m, A, B, h₁ ha, h₂ hb, hx⟩

theorem meet_mono {R R' S S' : GRel} (h₁ : R ⊆ R') (h₂ : S ⊆ S') : R.meet S ⊆ R'.meet S' :=
  fun _ ⟨A, B, ha, hb, hx⟩ => ⟨A, B, h₁ ha, h₂ hb, hx⟩

theorem inv_mono {R R' : GRel} (h : R ⊆ R') : R.inv ⊆ R'.inv := fun _ hx => h hx

theorem inv_inv (R : GRel) : R.inv.inv = R := by
  ext ⟨a, b, X⟩; rfl

theorem inv_comp (R S : GRel) : (R.comp S).inv = S.inv.comp R.inv := by
  ext ⟨a, b, X⟩
  simp only [inv, comp, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, S₁, S₂, h₁, h₂, rfl⟩; exact ⟨m, S₂, S₁, h₂, h₁, Finset.union_comm _ _⟩
  · rintro ⟨m, S₁, S₂, h₁, h₂, rfl⟩; exact ⟨m, S₂, S₁, h₂, h₁, Finset.union_comm _ _⟩

theorem inv_meet (R S : GRel) : (R.meet S).inv = R.inv.meet S.inv := by
  ext ⟨a, b, X⟩; rfl

theorem inv_union (R S : GRel) : (R ∪ S).inv = R.inv ∪ S.inv := by
  ext ⟨a, b, X⟩; rfl

theorem comp_nonempty_left {R S : GRel} (h : (R.comp S).Nonempty) : R.Nonempty := by
  obtain ⟨_, m, A, B, ha, _, _⟩ := h; exact ⟨_, ha⟩

theorem comp_nonempty_right {R S : GRel} (h : (R.comp S).Nonempty) : S.Nonempty := by
  obtain ⟨_, m, A, B, _, hb, _⟩ := h; exact ⟨_, hb⟩

theorem nonempty_mono {R S : GRel} (h : R ⊆ S) (hR : R.Nonempty) : S.Nonempty :=
  hR.mono h

end GRel

theorem empty_comp (R : GRel) : (∅ : GRel).comp R = ∅ := by
  ext ⟨a, b, X⟩
  simp only [GRel.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, _, _, h, _⟩
  exact h

theorem comp_empty (R : GRel) : R.comp (∅ : GRel) = ∅ := by
  ext ⟨a, b, X⟩
  simp only [GRel.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, _, _, _, h, _⟩
  exact h

/-- The identity span `$0 -> $0`. -/
def Span.idSpan : Span := ⟨.var 0, .var 0, []⟩

theorem Span.den_idSpan : Span.idSpan.den = GRel.id := by
  ext ⟨a, b, X⟩
  simp only [Span.den, GRel.id, idSpan, Set.mem_ofPred_eq, Prod.mk.injEq, Term.bind_var]
  constructor
  · rintro ⟨σ, rfl, rfl, rfl⟩; exact ⟨rfl, by simp [Store.at]⟩
  · rintro ⟨h₁, h₂⟩; exact ⟨fun _ => a, rfl, h₁, by simp [Store.at, h₂]⟩

theorem compose_isSome {s₁ s₂ : Span} (h : ((s₁.den).comp s₂.den).Nonempty) :
    ∃ s, s₁.compose s₂ = some s ∧ s.den = (s₁.den).comp s₂.den := by
  cases hc : s₁.compose s₂ with
  | none => rw [compose_none hc] at h; exact absurd h Set.not_nonempty_empty
  | some s => exact ⟨s, rfl, compose_some hc⟩

theorem meet_isSome {s₁ s₂ : Span} (h : ((s₁.den).meet s₂.den).Nonempty) :
    ∃ s, s₁.meet s₂ = some s ∧ s.den = (s₁.den).meet s₂.den := by
  cases hc : s₁.meet s₂ with
  | none => rw [meet_none hc] at h; exact absurd h Set.not_nonempty_empty
  | some s => exact ⟨s, rfl, meet_some hc⟩

end RwLog
