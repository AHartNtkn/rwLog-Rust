/-
# Interfaces of a span

The right interface of `l {c} -> r` is `r {c|r} -> r`: the identity restricted
to what the span can output, with the constraints that only mention its right
side. Composing a span with its interfaces changes nothing
(`comp_rightIface`, `leftIface_comp`), and coverage passes to interfaces
(`rightIface_covers`). Rungs use interfaces as the boundaries they push into
the other side of a `;` or `&`.
-/
import RwLog.Kernel.Covers
import RwLog.SpanLayer.Algebra

namespace RwLog

namespace Span

/-- The constraints of `s` that only mention variables of `p`. -/
def storeOn (s : Span) (p : Pat) : Store := s.c.filter fun a => a.vars.all (· ∈ p.vars)

/-- The right interface `r {c|r} -> r`: `s ; s.rightIface = s`. -/
def rightIface (s : Span) : Span := ⟨s.r, s.r, s.storeOn s.r⟩

/-- The left interface `l {c|l} -> l`: `s.leftIface ; s = s`. -/
def leftIface (s : Span) : Span := ⟨s.l, s.l, s.storeOn s.l⟩

end Span

open Term Fresh

theorem mem_storeOn {s : Span} {p c : Pat} : c ∈ s.storeOn p ↔ c ∈ s.c ∧ ∀ v ∈ c.vars, v ∈ p.vars := by
  simp [Span.storeOn, List.mem_filter, List.all_eq_true]

theorem storeOn_sub (s : Span) (p : Pat) (σ : Nat → GTerm) : (s.storeOn p).at σ ⊆ s.c.at σ := by
  intro g hg
  simp only [Store.at, List.mem_toFinset, List.mem_map] at hg ⊢
  obtain ⟨c, hc, rfl⟩ := hg
  exact ⟨c, (mem_storeOn.1 hc).1, rfl⟩

/-- The store on `p` only reads the variables of `p`. -/
theorem storeOn_at_congr (s : Span) (p : Pat) {σ τ : Nat → GTerm} (h : p.bind σ = p.bind τ) :
    (s.storeOn p).at σ = (s.storeOn p).at τ := by
  have hv := bind_agree h
  unfold Store.at
  congr 1
  refine List.map_congr_left fun c hc => bind_congr fun v hvc => hv v ((mem_storeOn.1 hc).2 v hvc)

/-- `s ; s.rightIface = s`. -/
theorem comp_rightIface (s : Span) : (s.den).comp s.rightIface.den = s.den := by
  ext ⟨a, b, S⟩
  simp only [GRel.comp, Span.den, Span.rightIface, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨m, S₁, S₂, ⟨σ, rfl, rfl, rfl⟩, ⟨τ, hm, rfl, rfl⟩, rfl⟩
    refine ⟨σ, rfl, hm.symm, ?_⟩
    rw [storeOn_at_congr s s.r hm.symm, Finset.union_eq_left.2 (storeOn_sub s s.r σ)]
  · rintro ⟨σ, rfl, rfl, rfl⟩
    exact ⟨_, _, _, ⟨σ, rfl, rfl, rfl⟩, ⟨σ, rfl, rfl, rfl⟩,
      (Finset.union_eq_left.2 (storeOn_sub s s.r σ)).symm⟩

/-- `s.leftIface ; s = s`. -/
theorem leftIface_comp (s : Span) : (s.leftIface.den).comp s.den = s.den := by
  ext ⟨a, b, S⟩
  simp only [GRel.comp, Span.den, Span.leftIface, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨m, S₁, S₂, ⟨τ, rfl, hm, rfl⟩, ⟨σ, hm', rfl, rfl⟩, rfl⟩
    refine ⟨σ, hm.symm.trans hm', rfl, ?_⟩
    rw [storeOn_at_congr s s.l (hm.symm.trans hm'), Finset.union_eq_right.2 (storeOn_sub s s.l σ)]
  · rintro ⟨σ, rfl, rfl, rfl⟩
    exact ⟨_, _, _, ⟨σ, rfl, rfl, rfl⟩, ⟨σ, rfl, rfl, rfl⟩,
      (Finset.union_eq_right.2 (storeOn_sub s s.l σ)).symm⟩

/-- The span `$v -> $v` with no constraints denotes the identity. -/
theorem den_trivial {s : Span} {v : Nat} (hl : s.l = .var v) (hr : s.r = .var v) (hc : s.c = []) :
    s.den = GRel.id := by
  ext ⟨a, b, S⟩
  simp only [Span.den, GRel.id, Set.mem_ofPred_eq, Prod.mk.injEq, hl, hr, hc]
  constructor
  · rintro ⟨σ, rfl, rfl, rfl⟩; exact ⟨rfl, by simp [Store.at]⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun _ => a, rfl, h1, by simp [Store.at, h2]⟩

theorem leftIface_eq (s : Span) : s.leftIface = s.swap.rightIface := rfl

/-- Coverage passes to right interfaces. The covered span's variables off its
right side are sent to a fresh constant, so no constraint mentioning them can
be hit by a constraint of the covering interface. -/
theorem rightIface_covers {x y : Span} (h : x.Covers y) : x.rightIface.Covers y.rightIface := by
  rintro z ⟨τ, rfl⟩
  let L : List Sym := x.c.flatMap Term.syms ++ y.r.syms ++ y.r.vars.flatMap fun w => (τ w).syms
  let F : Sym := code (lenBound L)
  have hF : F ∉ L := code_not_mem le_rfl
  let τ' : Nat → GTerm := fun w => if w ∈ y.r.vars then τ w else .sym F
  have hrτ : y.r.bind τ' = y.r.bind τ := bind_congr fun w hw => by simp [τ', hw]
  obtain ⟨u, ⟨σ', rfl⟩, _, hr, hst⟩ := h _ ⟨τ', rfl⟩
  simp only at hr hst
  refine ⟨_, ⟨σ', rfl⟩, ?_, ?_, ?_⟩
  · simp only [Span.rightIface]; exact hr.trans hrτ
  · simp only [Span.rightIface]; exact hr.trans hrτ
  · simp only [Span.rightIface]
    intro g hg
    simp only [Store.at, List.mem_toFinset, List.mem_map] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    obtain ⟨hcx, hcv⟩ := mem_storeOn.1 hc
    have hin : c.bind σ' ∈ y.c.at τ' := hst (by
      simp only [Store.at, List.mem_toFinset, List.mem_map]; exact ⟨c, hcx, rfl⟩)
    simp only [Store.at, List.mem_toFinset, List.mem_map] at hin
    obtain ⟨c', hc', he⟩ := hin
    by_cases hall : ∀ w ∈ c'.vars, w ∈ y.r.vars
    · simp only [Store.at, List.mem_toFinset, List.mem_map]
      refine ⟨c', mem_storeOn.2 ⟨hc', hall⟩, ?_⟩
      rw [← he]
      exact bind_congr fun w hw => by simp [τ', hall w hw]
    · exfalso
      push Not at hall
      obtain ⟨w, hw, hwr⟩ := hall
      have hFin : F ∈ (c'.bind τ').syms :=
        syms_var_sub hw (by simp [τ', hwr, Term.syms])
      rw [he] at hFin
      apply hF
      rcases syms_bind_sub hFin with hf | ⟨v, hv, hf⟩
      · simp only [L, List.mem_append, List.mem_flatMap]; exact .inl (.inl ⟨c, hcx, hf⟩)
      · have hf' : F ∈ (y.r.bind τ).syms := by
          rw [← hrτ, ← hr]; exact syms_var_sub (hcv v hv) hf
        rcases syms_bind_sub hf' with hf' | ⟨w', hw', hf'⟩
        · simp only [L, List.mem_append]; exact .inl (.inr hf')
        · simp only [L, List.mem_append, List.mem_flatMap]; exact .inr ⟨w', hw', hf'⟩


end RwLog
