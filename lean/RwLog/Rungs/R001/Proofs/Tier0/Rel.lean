/-
# Tier 0 proofs, part 1: relations up to the theory

The engine's answers are related to the relations they stand for in two ways:

* `LCov T Y X` (from `Lifting`): every triple of `X` the theory cannot refute
  is matched by a triple of `Y` with the same pair and a store no stronger
  (coverage up to the theory; `Span.CoversLive` is `LCov` on denotations);
* `GRel.Backed T Y X`: every triple of `Y` is backed by a triple of `X`
  (soundness up to the theory).

`Ref T a X` is both, for one answer `a`; `DC T A X` says that `X` is dead or
some answer of `A` covers it. Every operator the engine uses preserves these.
-/
import RwLog.Rungs.R001.Proofs.Derivations

namespace RwLog

namespace R001

namespace Tier0

variable {T : Theory}

open Lifting (LCov ns_refl ns_trans ns_union ns_live)

/-! ## Coverage and backing of relations -/

/-- Every triple of the relation carries a refuted store. -/
def DeadR (T : Theory) (X : GRel) : Prop := ∀ x ∈ X, Refutes T x.2.2

/-- The answer `a` stands for `X` exactly, up to the theory. -/
def Ref (T : Theory) (a : Span) (X : GRel) : Prop := (a.den).Backed T X ∧ LCov T a.den X

/-- `X` is dead, or one answer of `A` covers it. -/
def DC (T : Theory) (A : List Span) (X : GRel) : Prop := DeadR T X ∨ ∃ a ∈ A, LCov T a.den X

theorem lcov_of_subset {X Y : GRel} (h : X ⊆ Y) : LCov T Y X :=
  Lifting.LCov.of_sub fun _ _ S hx => ⟨S, h hx, subset_rfl⟩

theorem lcov_of_covers {a b : Span} (h : a.Covers b) : LCov T a.den b.den :=
  Lifting.coversLive_iff.1 h.live

theorem Backed.refl (X : GRel) : X.Backed T X := GRel.Backed.of_subset le_rfl

theorem Backed.trans {Z Y X : GRel} (h₁ : Z.Backed T Y) (h₂ : Y.Backed T X) : Z.Backed T X := by
  intro z hz
  obtain ⟨y, hy, e1, e2, hs⟩ := h₁ z hz
  obtain ⟨x, hx, f1, f2, hs'⟩ := h₂ y hy
  exact ⟨x, hx, f1.trans e1, f2.trans e2, ns_trans hs' hs⟩

theorem Backed.comp {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Y₁.Backed T X₁) (h₂ : Y₂.Backed T X₂) :
    (Y₁.comp Y₂).Backed T (X₁.comp X₂) := by
  rintro ⟨u, v, S⟩ ⟨m, S₁, S₂, hy₁, hy₂, hS⟩
  simp only at hS; subst hS
  obtain ⟨⟨u', m', S₁'⟩, hx₁, e1, e2, hs₁⟩ := h₁ _ hy₁
  obtain ⟨⟨m'', v', S₂'⟩, hx₂, f1, f2, hs₂⟩ := h₂ _ hy₂
  simp only at e1 e2 f1 f2 hs₁ hs₂; subst e1 e2 f1 f2
  exact ⟨(_, _, S₁' ∪ S₂'), ⟨_, S₁', S₂', hx₁, hx₂, rfl⟩, rfl, rfl, ns_union hs₁ hs₂⟩

theorem Backed.meet {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Y₁.Backed T X₁) (h₂ : Y₂.Backed T X₂) :
    (Y₁.meet Y₂).Backed T (X₁.meet X₂) := by
  rintro ⟨u, v, S⟩ ⟨S₁, S₂, hy₁, hy₂, hS⟩
  simp only at hS; subst hS
  obtain ⟨⟨u', v', S₁'⟩, hx₁, e1, e2, hs₁⟩ := h₁ _ hy₁
  obtain ⟨⟨u'', v'', S₂'⟩, hx₂, f1, f2, hs₂⟩ := h₂ _ hy₂
  simp only at e1 e2 f1 f2 hs₁ hs₂; subst e1 e2 f1 f2
  exact ⟨(_, _, S₁' ∪ S₂'), ⟨S₁', S₂', hx₁, hx₂, rfl⟩, rfl, rfl, ns_union hs₁ hs₂⟩

theorem Backed.inv {Y X : GRel} (h : Y.Backed T X) : Y.inv.Backed T X.inv := by
  rintro ⟨u, v, S⟩ hy
  obtain ⟨⟨v', u', S'⟩, hx, e1, e2, hs⟩ := h (v, u, S) hy
  simp only at e1 e2; subst e1 e2
  exact ⟨(u', v', S'), hx, rfl, rfl, hs⟩

theorem Ref.trans {a : Span} {Y X : GRel} (h : Ref T a Y) (hb : Y.Backed T X) (hd : LCov T Y X) :
    Ref T a X := ⟨Backed.trans h.1 hb, h.2.trans hd⟩

theorem Ref.of_eq {a : Span} {Y X : GRel} (h : Ref T a Y) (e : Y = X) : Ref T a X := e ▸ h

theorem Ref.self (a : Span) : Ref T a a.den := ⟨Backed.refl _, Lifting.LCov.refl _⟩

theorem Ref.swap {a : Span} {X : GRel} (h : Ref T a X) : Ref T a.swap X.inv := by
  unfold Ref; rw [swap_den]; exact ⟨Backed.inv h.1, h.2.inv⟩

theorem DeadR.of_dom {X Y : GRel} (hd : LCov T Y X) (h : DeadR T Y) : DeadR T X := by
  rintro ⟨a, b, S⟩ hx
  by_contra hn
  obtain ⟨S', hy, hs⟩ := hd a b S hx hn
  exact ns_live hs hn (h _ hy)

/-- A relation covered by nothing is dead. -/
theorem DeadR.of_empty {X : GRel} (hd : LCov T ∅ X) : DeadR T X := by
  rintro ⟨a, b, S⟩ hx
  by_contra hn
  obtain ⟨S', hy, -⟩ := hd a b S hx hn
  exact hy

theorem DC.dom {A : List Span} {X Y : GRel} (hd : LCov T Y X) (h : DC T A Y) : DC T A X := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl (h.of_dom hd)
  · exact Or.inr ⟨a, ha, h.trans hd⟩

theorem DC.of_eq {A : List Span} {X Y : GRel} (h : DC T A Y) (e : Y = X) : DC T A X := e ▸ h

theorem DC.mono {A A' : List Span} {X : GRel} (h : DC T A X) (hA : ∀ a ∈ A, a ∈ A') :
    DC T A' X := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, hA a ha, h⟩

theorem DC.covers {A A' : List Span} {X : GRel} (h : DC T A X)
    (hA : ∀ a ∈ A, ∃ b ∈ A', b.Covers a) : DC T A' X := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · obtain ⟨b, hb, hc⟩ := hA a ha
    exact Or.inr ⟨b, hb, (lcov_of_covers hc).trans h⟩

theorem DC.swap {A : List Span} {X : GRel} (h : DC T A X) : DC T (A.map Span.swap) X.inv := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl fun x hx => h (x.2.1, x.1, x.2.2) hx
  · refine Or.inr ⟨a.swap, List.mem_map_of_mem ha, ?_⟩
    rw [swap_den]; exact h.inv

theorem DeadR.comp_left {X Y : GRel} (h : DeadR T X) : DeadR T (X.comp Y) := by
  rintro ⟨u, v, S⟩ ⟨m, S₁, S₂, hx, -, hS⟩
  simp only at hS ⊢; rw [hS]; exact (h _ hx).mono Finset.subset_union_left

theorem DeadR.comp_right {X Y : GRel} (h : DeadR T Y) : DeadR T (X.comp Y) := by
  rintro ⟨u, v, S⟩ ⟨m, S₁, S₂, -, hy, hS⟩
  simp only at hS ⊢; rw [hS]; exact (h _ hy).mono Finset.subset_union_right

theorem DeadR.meet_left {X Y : GRel} (h : DeadR T X) : DeadR T (X.meet Y) := by
  rintro ⟨u, v, S⟩ ⟨S₁, S₂, hx, -, hS⟩
  simp only at hS ⊢; rw [hS]; exact (h _ hx).mono Finset.subset_union_left

theorem DeadR.meet_right {X Y : GRel} (h : DeadR T Y) : DeadR T (X.meet Y) := by
  rintro ⟨u, v, S⟩ ⟨S₁, S₂, -, hy, hS⟩
  simp only at hS ⊢; rw [hS]; exact (h _ hy).mono Finset.subset_union_right

theorem deadR_den {s : Span} : DeadR T s.den ↔ s.Dead T := by
  constructor
  · intro h σ; exact h _ ⟨σ, rfl⟩
  · rintro h _ ⟨σ, rfl⟩; exact h σ

/-! ## Simplified candidates -/

section Live

variable (hSE : Obligation.simplify_exact) (hwf : ∀ ρ ∈ T, ρ.WellFormed)
include hSE hwf

theorem live_ref {z c : Span} (h : c ∈ live T z) : Ref T c z.den := by
  simp only [live, Option.mem_toList] at h
  have hr := (hSE T z hwf).2 c h
  exact ⟨hr.1, Lifting.coversLive_iff.1 hr.2⟩

theorem live_dc {z : Span} {X : GRel} (h : LCov T z.den X) : DC T (live T z) X := by
  cases hs : T.simplify z with
  | none =>
    have hd := (hSE T z hwf).1 hs
    exact Or.inl (DeadR.of_dom h (deadR_den.2 hd))
  | some c =>
    have hr := (hSE T z hwf).2 c hs
    exact Or.inr ⟨c, by simp [live, hs], (Lifting.coversLive_iff.1 hr.2).trans h⟩

theorem composeLive_ref {x y c : Span} {X Y : GRel} (hx : Ref T x X) (hy : Ref T y Y)
    (hc : c ∈ composeLive T x y) : Ref T c (X.comp Y) := by
  unfold composeLive at hc
  split at hc
  · rename_i z hz
    refine (live_ref hSE hwf hc).trans ?_ ?_ <;> rw [compose_some hz]
    · exact Backed.comp hx.1 hy.1
    · exact hx.2.comp hy.2
  · simp at hc

theorem meetLive_ref {x y c : Span} {X Y : GRel} (hx : Ref T x X) (hy : Ref T y Y)
    (hc : c ∈ meetLive T x y) : Ref T c (X.meet Y) := by
  unfold meetLive at hc
  split at hc
  · rename_i z hz
    refine (live_ref hSE hwf hc).trans ?_ ?_ <;> rw [meet_some hz]
    · exact Backed.meet hx.1 hy.1
    · exact hx.2.meet hy.2
  · simp at hc

theorem composeLive_dc {x y : Span} {X Y : GRel} (hx : LCov T x.den X) (hy : LCov T y.den Y) :
    DC T (composeLive T x y) (X.comp Y) := by
  have hd := hx.comp hy
  unfold composeLive
  split
  · rename_i z hz
    rw [← compose_some hz] at hd
    exact live_dc hSE hwf hd
  · rename_i hz
    rw [compose_none hz] at hd
    exact Or.inl (DeadR.of_empty hd)

theorem meetLive_dc {x y : Span} {X Y : GRel} (hx : LCov T x.den X) (hy : LCov T y.den Y) :
    DC T (meetLive T x y) (X.meet Y) := by
  have hd := hx.meet hy
  unfold meetLive
  split
  · rename_i z hz
    rw [← meet_some hz] at hd
    exact live_dc hSE hwf hd
  · rename_i hz
    rw [meet_none hz] at hd
    exact Or.inl (DeadR.of_empty hd)

/-- Joining every answer of one side with every answer of the other covers
the composition of what they cover. -/
theorem join_comp_dc {xs ys : List Span} {X Y : GRel} (hx : DC T xs X) (hy : DC T ys Y) :
    DC T (xs.flatMap fun x => ys.flatMap fun y => composeLive T x y) (X.comp Y) := by
  rcases hx with hx | ⟨x, hxm, hx⟩
  · exact Or.inl hx.comp_left
  rcases hy with hy | ⟨y, hym, hy⟩
  · exact Or.inl hy.comp_right
  refine (composeLive_dc hSE hwf hx hy).mono fun c hc => ?_
  simp only [List.mem_flatMap]
  exact ⟨x, hxm, y, hym, hc⟩

theorem join_meet_dc {xs ys : List Span} {X Y : GRel} (hx : DC T xs X) (hy : DC T ys Y) :
    DC T (xs.flatMap fun x => ys.flatMap fun y => meetLive T x y) (X.meet Y) := by
  rcases hx with hx | ⟨x, hxm, hx⟩
  · exact Or.inl hx.meet_left
  rcases hy with hy | ⟨y, hym, hy⟩
  · exact Or.inl hy.meet_right
  refine (meetLive_dc hSE hwf hx hy).mono fun c hc => ?_
  simp only [List.mem_flatMap]
  exact ⟨x, hxm, y, hym, hc⟩

end Live

end Tier0

end R001

end RwLog
