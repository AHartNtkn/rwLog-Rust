/-
# Coverage, dead spans and refinement

The notions the execution theorems of R001 are stated with.

* `Span.Covers a s` is syntactic coverage on ground triples: every triple of
  `s` is matched by a triple of `a` with the same pair and a store contained
  in its own. The engine decides it by matching (`Span.covers?`).
* `Span.Dead T s`: no model of `T` lets `s` relate anything.
* `Span.CoversLive T a s`: in every model of `T`, `a` relates every pair `s`
  relates. This is the coverage `Runtime.Complete` asks for.
* `Span.Refines T a s`: in every model of `T`, `a` and `s` relate the same
  pairs. Simplifying a span by its theory refines it.
-/
import RwLog.SpanLayer.Bridge

namespace RwLog

/-- `a` covers `s`: every ground triple of `s` is matched by a triple of `a`
with the same pair and a store contained in it. -/
def Span.Covers (a s : Span) : Prop :=
  ∀ x ∈ s.den, ∃ y ∈ a.den, y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 ⊆ x.2.2

/-- Two spans are equivalent answers when each covers the other. -/
def Span.Equiv (a b : Span) : Prop := a.Covers b ∧ b.Covers a

/-- No model of the theory lets the span relate a pair. -/
def Span.Dead (T : Theory) (s : Span) : Prop := ∀ M, T.Model M → s.denAt M = ∅

/-- In every model of the theory, `a` relates every pair `s` relates. -/
def Span.CoversLive (T : Theory) (a s : Span) : Prop :=
  ∀ M, T.Model M → s.denAt M ⊆ a.denAt M

/-- In every model of the theory, `a` and `s` relate the same pairs. -/
def Span.Refines (T : Theory) (a s : Span) : Prop :=
  ∀ M, T.Model M → a.denAt M = s.denAt M

theorem Span.Covers.at_subset {a s : Span} (h : a.Covers s) (M : Interp) :
    s.denAt M ⊆ a.denAt M := by
  rw [Span.denAt_eq, Span.denAt_eq]
  rintro ⟨p, q⟩ ⟨S, hS, hM⟩
  obtain ⟨y, hy, h1, h2, h3⟩ := h _ hS
  obtain ⟨y1, y2, Y⟩ := y
  simp only at h1 h2 h3
  subst h1 h2
  exact ⟨Y, hy, fun x hx => hM (h3 hx)⟩

theorem Span.Covers.live {T : Theory} {a s : Span} (h : a.Covers s) : a.CoversLive T s :=
  fun M _ => h.at_subset M

theorem Span.Covers.refl (a : Span) : a.Covers a :=
  fun x hx => ⟨x, hx, rfl, rfl, le_rfl⟩

theorem Span.Covers.trans {a b c : Span} (h₁ : a.Covers b) (h₂ : b.Covers c) : a.Covers c := by
  intro x hx
  obtain ⟨y, hy, h1, h2, h3⟩ := h₂ x hx
  obtain ⟨z, hz, k1, k2, k3⟩ := h₁ y hy
  exact ⟨z, hz, k1.trans h1, k2.trans h2, k3.trans h3⟩

theorem Span.Covers.of_den_subset {a s : Span} (h : s.den ⊆ a.den) : a.Covers s :=
  fun x hx => ⟨x, h hx, rfl, rfl, le_rfl⟩

theorem Span.CoversLive.refl (T : Theory) (a : Span) : a.CoversLive T a :=
  fun _ _ => le_rfl

theorem Span.CoversLive.trans {T : Theory} {a b c : Span} (h₁ : a.CoversLive T b)
    (h₂ : b.CoversLive T c) : a.CoversLive T c :=
  fun M hM => (h₂ M hM).trans (h₁ M hM)

end RwLog
