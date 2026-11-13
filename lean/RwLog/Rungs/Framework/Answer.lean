/-
# Comparing answers by what they denote

`Answer.Covers M` and `Answer.Equiv M` (`Trusted/Runtime.lean`) are a preorder
and an equivalence on answers of any types, in any interpretation `M`, and
converse respects both. On spans, coverage in every interpretation is the
coverage of spans as written of the span layer (`Span.covers_iff`,
`Span.equiv_iff`), which is decided by matching.
-/
import RwLog.Trusted.Runtime
import RwLog.SpanLayer.Coverage

namespace RwLog

namespace Answer

variable {A B C : Type} [Answer A] [Answer B] [Answer C] {M : Interp}

theorem Covers.refl (a : A) : Covers M a a := le_rfl

theorem Covers.trans {a : A} {b : B} {c : C} (h₁ : Covers M a b) (h₂ : Covers M b c) :
    Covers M a c :=
  Set.Subset.trans h₂ h₁

/-- Converse respects coverage. -/
theorem Covers.swap {a : A} {b : B} (h : Covers M a b) : Covers M (swap a) (swap b) := by
  intro p hp
  rw [den_swap] at hp ⊢
  exact h hp

theorem Equiv.refl (a : A) : Equiv M a a := ⟨Covers.refl a, Covers.refl a⟩

theorem Equiv.symm {a : A} {b : B} (h : Equiv M a b) : Equiv M b a := ⟨h.2, h.1⟩

theorem Equiv.trans {a : A} {b : B} {c : C} (h₁ : Equiv M a b) (h₂ : Equiv M b c) : Equiv M a c :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem Equiv.swap {a : A} {b : B} (h : Equiv M a b) : Equiv M (swap a) (swap b) :=
  ⟨h.1.swap, h.2.swap⟩

/-- Equivalent answers relate the same pairs. -/
theorem Equiv.den_eq {a : A} {b : B} (h : Equiv M a b) : den M a = den M b :=
  Set.Subset.antisymm h.2 h.1

end Answer

/-! ## Spans -/

/-- Coverage of spans as written is coverage of what they denote whatever
constraints hold: a triple of `s` is matched by a triple of `a` with a
smaller store exactly when, in every interpretation, `a` relates what `s`
relates. -/
theorem Span.covers_iff {a s : Span} : a.Covers s ↔ ∀ M, Answer.Covers M a s := by
  constructor
  · exact fun h M => h.at_subset M
  · rintro h ⟨p, q, S⟩ hx
    have hp : (p, q) ∈ s.denAt (↑S : Set GTerm) := by
      rw [Span.denAt_eq]; exact ⟨S, hx, le_rfl⟩
    have := h _ hp
    change (p, q) ∈ a.denAt (↑S : Set GTerm) at this
    rw [Span.denAt_eq] at this
    obtain ⟨S', hS', hsub⟩ := this
    exact ⟨(p, q, S'), hS', rfl, rfl, Finset.coe_subset.1 hsub⟩

theorem Span.equiv_iff {a b : Span} : a.Equiv b ↔ ∀ M, Answer.Equiv M a b := by
  unfold Span.Equiv Answer.Equiv
  rw [Span.covers_iff, Span.covers_iff]
  exact ⟨fun h M => ⟨h.1 M, h.2 M⟩, fun h => ⟨fun M => (h M).1, fun M => (h M).2⟩⟩

end RwLog
