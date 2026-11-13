/-
# Rung R001, Symmetry: candidates of mirrored goals

The candidates a goal computes in a round, and the goals it reads, are those
of the corresponding goal of the mirrored run, swapped, up to the classes of
equivalent answers.

* Span algebra: the fusions of the mirrored run denote the converses of the
  run's fusions, up to mutual coverage of ground triples (`GEq`). Two
  optional spans whose meanings are mutually covering are both absent or
  equivalent (`optionRel_of_geq`), and simplification commutes with swapping
  (`simplify_swap`, which is syntactic).
-/
import RwLog.Rungs.R001.Proofs.SymmetryTables
import RwLog.SpanLayer.Algebra

namespace RwLog

namespace R001

namespace Symmetry

/-! ## Mutual coverage of ground relations -/

/-- `R` covers `S`: every triple of `S` is matched by a triple of `R` with the
same pair and a contained store. `Span.Covers a s` is `GCov a.den s.den`. -/
def GCov (R S : GRel) : Prop :=
  ∀ x ∈ S, ∃ y ∈ R, y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 ⊆ x.2.2

def GEq (R S : GRel) : Prop := GCov R S ∧ GCov S R

theorem GCov.refl (R : GRel) : GCov R R := fun x hx => ⟨x, hx, rfl, rfl, le_rfl⟩

theorem GCov.trans {R S U : GRel} (h₁ : GCov R S) (h₂ : GCov S U) : GCov R U := by
  intro x hx
  obtain ⟨y, hy, a1, a2, a3⟩ := h₂ x hx
  obtain ⟨z, hz, b1, b2, b3⟩ := h₁ y hy
  exact ⟨z, hz, b1.trans a1, b2.trans a2, b3.trans a3⟩

theorem GCov.of_eq {R S : GRel} (h : R = S) : GCov R S := h ▸ GCov.refl R

theorem GCov.comp {R R' S S' : GRel} (h₁ : GCov R R') (h₂ : GCov S S') :
    GCov (R.comp S) (R'.comp S') := by
  rintro ⟨a, b, U⟩ ⟨m, U₁, U₂, hR, hS, rfl⟩
  obtain ⟨⟨a', m', V₁⟩, hy, e1, e2, e3⟩ := h₁ _ hR
  obtain ⟨⟨m'', b', V₂⟩, hz, f1, f2, f3⟩ := h₂ _ hS
  simp only at e1 e2 e3 f1 f2 f3
  refine ⟨(a', b', V₁ ∪ V₂), ⟨m', V₁, V₂, hy, ?_, rfl⟩, e1, f2, Finset.union_subset_union e3 f3⟩
  rw [e2, ← f1]; exact hz

theorem GCov.meet {R R' S S' : GRel} (h₁ : GCov R R') (h₂ : GCov S S') :
    GCov (R.meet S) (R'.meet S') := by
  rintro ⟨a, b, U⟩ ⟨U₁, U₂, hR, hS, rfl⟩
  obtain ⟨⟨a', b', V₁⟩, hy, e1, e2, e3⟩ := h₁ _ hR
  obtain ⟨⟨a'', b'', V₂⟩, hz, f1, f2, f3⟩ := h₂ _ hS
  simp only at e1 e2 e3 f1 f2 f3
  refine ⟨(a', b', V₁ ∪ V₂), ⟨V₁, V₂, hy, ?_, rfl⟩, e1, e2, Finset.union_subset_union e3 f3⟩
  rw [e1, e2, ← f1, ← f2]; exact hz

theorem GCov.inv {R S : GRel} (h : GCov R S) : GCov R.inv S.inv := by
  rintro ⟨a, b, U⟩ hx
  obtain ⟨⟨b', a', V⟩, hy, e1, e2, e3⟩ := h (b, a, U) hx
  exact ⟨(a', b', V), hy, e2, e1, e3⟩

theorem GEq.refl (R : GRel) : GEq R R := ⟨GCov.refl R, GCov.refl R⟩
theorem GEq.symm {R S : GRel} (h : GEq R S) : GEq S R := ⟨h.2, h.1⟩
theorem GEq.trans {R S U : GRel} (h₁ : GEq R S) (h₂ : GEq S U) : GEq R U :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
theorem GEq.of_eq {R S : GRel} (h : R = S) : GEq R S := h ▸ GEq.refl R
theorem GEq.comp {R R' S S' : GRel} (h₁ : GEq R R') (h₂ : GEq S S') : GEq (R.comp S) (R'.comp S') :=
  ⟨h₁.1.comp h₂.1, h₁.2.comp h₂.2⟩
theorem GEq.meet {R R' S S' : GRel} (h₁ : GEq R R') (h₂ : GEq S S') : GEq (R.meet S) (R'.meet S') :=
  ⟨h₁.1.meet h₂.1, h₁.2.meet h₂.2⟩
theorem GEq.inv {R S : GRel} (h : GEq R S) : GEq R.inv S.inv := ⟨h.1.inv, h.2.inv⟩

theorem GCov.eq_empty {R S : GRel} (h : GCov R S) (hR : R = ∅) : S = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨y, hy, -⟩ := h x hx
  rw [hR] at hy; exact hy

theorem _root_.RwLog.Span.Equiv.geq {a b : Span} (h : a.Equiv b) : GEq a.den b.den := ⟨h.1, h.2⟩

theorem _root_.RwLog.Span.Equiv.of_geq {a b : Span} (h : GEq a.den b.den) : a.Equiv b := ⟨h.1, h.2⟩

theorem swap_geq (a : Span) : GEq a.swap.den a.den.inv := GEq.of_eq (swap_den a)

/-! ## Optional spans and their simplification -/

/-- The candidates of an optional fusion. -/
def liveO (T : Theory) : Option Span → List Span
  | some z => live T z
  | none => []

theorem composeLive_eq (T : Theory) (x y : Span) : composeLive T x y = liveO T (x.compose y) := by
  unfold composeLive; cases x.compose y <;> rfl

theorem meetLive_eq (T : Theory) (x y : Span) : meetLive T x y = liveO T (x.meet y) := by
  unfold meetLive; cases x.meet y <;> rfl

theorem denO_empty_iff : ∀ o : Option Span, Span.denO o = ∅ ↔ o = none
  | none => by simp [Span.denO]
  | some s => by
    simp only [Span.denO, reduceCtorEq, iff_false]
    exact (Span.den_nonempty s).ne_empty

/-- Optional spans with mutually covering meanings are both absent or
equivalent. -/
theorem optionRel_of_geq {o o' : Option Span} (h : GEq (Span.denO o) (Span.denO o')) :
    Option.Rel Span.Equiv o o' := by
  cases o with
  | none =>
    have := h.1.eq_empty ((denO_empty_iff none).2 rfl)
    rw [(denO_empty_iff _).1 this]; exact .none
  | some a =>
    cases o' with
    | none =>
      have := h.2.eq_empty ((denO_empty_iff none).2 rfl)
      rw [denO_empty_iff] at this; cases this
    | some b => exact .some (Span.Equiv.of_geq h)

theorem live_swap (T : Theory) (s : Span) : live T s.swap = (live T s).map Span.swap := by
  simp only [live, simplify_swap]; cases T.simplify s <;> rfl

theorem classEq_toList {o o' : Option Span} (h : Option.Rel Span.Equiv o o') :
    ClassEq o.toList o'.toList := by
  cases h with
  | none => exact ClassEq.refl _
  | some e =>
    rename_i a b
    refine ⟨fun x hx => ⟨b, by simp, ?_⟩, fun y hy => ⟨a, by simp, ?_⟩⟩
    · simp only [Option.toList_some, List.mem_singleton] at hx; subst hx; exact e
    · simp only [Option.toList_some, List.mem_singleton] at hy; subst hy; exact e

/-- The key step: optional spans whose meanings are mutually covering, one
the converse of the other, give the same classes of candidates up to
swapping, when simplification respects equivalent spans. -/
theorem liveO_mirror {T : Theory} (hK : Obligation.SimplifyRespectsEquiv T)
    {o' o : Option Span} (h : GEq (Span.denO o') (Span.denO o).inv) :
    ClassEq (liveO T o') ((liveO T o).map Span.swap) := by
  have h' : GEq (Span.denO o') (Span.denO (o.map Span.swap)) := by
    cases o with
    | none => simpa [Span.denO, GRel.inv] using h
    | some a => exact h.trans (swap_geq a).symm
  cases o with
  | none =>
    have hr := optionRel_of_geq h'
    cases o' with
    | none => exact ClassEq.refl _
    | some a' => cases hr
  | some a =>
    cases o' with
    | none =>
      have hr := optionRel_of_geq h'
      cases hr
    | some a' =>
      have e : a'.Equiv a.swap := by
        have hr := optionRel_of_geq h'
        cases hr with
        | some e => exact e
      simp only [liveO]
      rw [← live_swap]
      exact classEq_toList (hK a' a.swap e)

end Symmetry

end R001

end RwLog
