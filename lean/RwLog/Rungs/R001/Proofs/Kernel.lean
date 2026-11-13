/-
# Rung R001, Kernel obligations

The kernel facts R001 relies on are rung-independent and proved in
`RwLog/Kernel` and `RwLog/SpanLayer`; this file discharges R001's statements
of them and adds what is specific to R001's boundaries (`bound`, `boundEq`).

* `covers_iff`: `Span.covers?_iff` (`Kernel/Covers.lean`).
* `iface_exact`, `iface_equiv`: `Kernel/Iface.lean`, plus the facts about
  trivial boundaries below.
* `denote_dual`: `Program.sem_dual` (`SpanLayer/Dual.lean`).
* `refutes_sound`, `simplify_exact`, `simplify_stable`, `present_exact`:
  `Kernel/RefuteCorrect.lean`.
* `simplify_mono`: `simpLaws_of_wf` (`Kernel/SimplifyMono.lean`).
-/
import RwLog.Rungs.R001.Spec
import RwLog.Kernel.Iface
import RwLog.SpanLayer.Dual
import RwLog.Kernel.SimplifyMono

namespace RwLog

namespace R001

open Term

theorem covers_iff : Obligation.covers_iff := Span.covers?_iff

/-! ## Boundaries -/

theorem bound_none {s : Span} (h : bound s = none) : (∃ v, s.l = .var v) ∧ s.c = [] := by
  unfold bound at h
  split at h
  · rename_i v h₁ h₂; exact ⟨⟨v, h₁⟩, h₂⟩
  · cases h

theorem bound_some {s s' : Span} (h : bound s = some s') : s' = s := by
  unfold bound at h
  split at h
  · cases h
  · cases h; rfl

theorem iface_exact : Obligation.iface_exact := by
  intro s
  refine ⟨comp_rightIface s, leftIface_comp s, fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨v, hv⟩, hc⟩ := bound_none h
    exact den_trivial hv hv hc
  · obtain ⟨⟨v, hv⟩, hc⟩ := bound_none h
    exact den_trivial hv hv hc

/-- A span that covers a trivial span is trivial: it must reach every ground
term on the left with the empty store. -/
theorem bound_none_of_covers {a b : Span} (ha : bound a = none) (h : b.Covers a) : bound b = none := by
  obtain ⟨⟨v, hv⟩, hc⟩ := bound_none ha
  have inst : ∀ g : GTerm, ∃ τ : Nat → GTerm, b.l.bind τ = g ∧ b.c.at τ = ∅ := by
    intro g
    obtain ⟨y, ⟨τ, rfl⟩, h1, _, h3⟩ := h (g, a.r.bind fun _ => g, ∅) ⟨fun _ => g, by
      simp [hv, hc, Store.at]⟩
    exact ⟨τ, h1, Finset.subset_empty.1 h3⟩
  obtain ⟨τ₁, h₁, hc₁⟩ := inst (.sym "a")
  obtain ⟨τ₂, h₂, _⟩ := inst (.sym "b")
  have hbc : b.c = [] := by
    cases hb : b.c with
    | nil => rfl
    | cons c cs =>
      rw [hb] at hc₁; simp [Store.at] at hc₁
  unfold bound
  cases hl : b.l with
  | var w => simp [hbc]
  | sym f =>
    rw [hl] at h₁ h₂; simp at h₁ h₂; subst h₁; simp at h₂
  | app p q => rw [hl] at h₁; simp at h₁

/-- Covering in both directions makes boundaries equal as table keys. -/
theorem boundEq_of_equiv {a b : Span} (hab : a.Covers b) (hba : b.Covers a) :
    boundEq (bound a) (bound b) = true := by
  cases ha : bound a with
  | none =>
    rw [bound_none_of_covers ha hba]; rfl
  | some a' =>
    cases hb : bound b with
    | none => rw [bound_none_of_covers hb hab] at ha; cases ha
    | some b' =>
      rw [bound_some ha, bound_some hb]
      simp [boundEq, covers?_complete hab, covers?_complete hba]

theorem iface_equiv : Obligation.iface_equiv := by
  rintro x y ⟨hxy, hyx⟩
  refine ⟨boundEq_of_equiv (rightIface_covers hxy) (rightIface_covers hyx), ?_⟩
  rw [leftIface_eq, leftIface_eq]
  exact boundEq_of_equiv (rightIface_covers (covers_swap hxy)) (rightIface_covers (covers_swap hyx))

theorem denote_dual : Obligation.denote_dual := Program.sem_dual

/-! ## The constraint checker -/

theorem refutes_sound : Obligation.refutes_sound :=
  fun _ _ hwf h σ _ hM => Theory.refutes?_sound hwf h σ hM

theorem simplify_exact : Obligation.simplify_exact := fun _ s hwf => Theory.simplify_exact hwf s

theorem simplify_stable : Obligation.simplify_stable :=
  fun _ _ _ hwf h => Theory.simplify_stable hwf h

theorem present_exact : Obligation.present_exact := fun _ s hwf => Theory.present_exact hwf s

theorem simplify_mono : Obligation.simplify_mono := fun _ hwf =>
  have L := simpLaws_of_wf hwf
  ⟨L.mono, fun s t => ⟨L.compR s t, L.compL s t, L.meetR s t, L.meetL s t⟩⟩

end R001

end RwLog
