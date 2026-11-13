/-
# Comparing answers by what they denote

`Answer.Covers` and `Answer.Equiv` (`Trusted/Runtime.lean`) are a preorder and
an equivalence on answers of any types, and converse respects both. On spans
they are the syntactic coverage of the span layer (`Span.covers_iff`,
`Span.equiv_iff`), which the kernel decides by matching, and the coverage,
deadness and refinement modulo a theory of `SpanLayer/Coverage.lean` are the
generic ones by definition.
-/
import RwLog.Trusted.Runtime
import RwLog.SpanLayer.Coverage

namespace RwLog

namespace Answer

variable {A B C : Type} [Answer A] [Answer B] [Answer C]

theorem Covers.refl (a : A) : Covers a a := fun _ => le_rfl

theorem Covers.trans {a : A} {b : B} {c : C} (h₁ : Covers a b) (h₂ : Covers b c) : Covers a c :=
  fun M => (h₂ M).trans (h₁ M)

/-- Converse respects coverage. -/
theorem Covers.swap {a : A} {b : B} (h : Covers a b) : Covers (swap a) (swap b) := by
  intro M p hp
  rw [den_swap] at hp ⊢
  exact h M hp

theorem Covers.live {T : Theory} {a : A} {b : B} (h : Covers a b) : CoversLive T a b :=
  fun M _ => h M

theorem Equiv.refl (a : A) : Equiv a a := ⟨Covers.refl a, Covers.refl a⟩

theorem Equiv.symm {a : A} {b : B} (h : Equiv a b) : Equiv b a := ⟨h.2, h.1⟩

theorem Equiv.trans {a : A} {b : B} {c : C} (h₁ : Equiv a b) (h₂ : Equiv b c) : Equiv a c :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem Equiv.swap {a : A} {b : B} (h : Equiv a b) : Equiv (swap a) (swap b) :=
  ⟨h.1.swap, h.2.swap⟩

/-- Equivalent answers relate the same pairs in every interpretation. -/
theorem Equiv.den_eq {a : A} {b : B} (h : Equiv a b) (M : Interp) : den M a = den M b :=
  Set.Subset.antisymm (h.2 M) (h.1 M)

theorem CoversLive.refl (T : Theory) (a : A) : CoversLive T a a := fun _ _ => le_rfl

theorem CoversLive.trans {T : Theory} {a : A} {b : B} {c : C} (h₁ : CoversLive T a b)
    (h₂ : CoversLive T b c) : CoversLive T a c :=
  fun M hM => (h₂ M hM).trans (h₁ M hM)

end Answer

/-! ## Spans -/

/-- Syntactic coverage of spans is coverage of what they denote: a triple of
`s` is matched by a triple of `a` with a smaller store exactly when, in every
interpretation, `a` relates what `s` relates. -/
theorem Span.covers_iff {a s : Span} : a.Covers s ↔ Answer.Covers a s := by
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

theorem Span.equiv_iff {a b : Span} : a.Equiv b ↔ Answer.Equiv a b :=
  and_congr Span.covers_iff Span.covers_iff

theorem Span.coversLive_iff {T : Theory} {a s : Span} :
    a.CoversLive T s ↔ Answer.CoversLive T a s := Iff.rfl

theorem Span.dead_iff {T : Theory} {s : Span} : s.Dead T ↔ Answer.Dead T s := Iff.rfl

theorem Span.refines_iff {T : Theory} {a s : Span} : a.Refines T s ↔ Answer.Refines T a s :=
  Iff.rfl

end RwLog
