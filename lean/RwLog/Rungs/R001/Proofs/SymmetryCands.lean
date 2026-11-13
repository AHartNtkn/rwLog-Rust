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

/-! ## Optional spans and their simplification -/

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
