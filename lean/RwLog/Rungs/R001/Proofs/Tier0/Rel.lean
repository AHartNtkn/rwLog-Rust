/-
# Tier 0 proofs, part 1: relations up to the theory

Relations are compared in every model of the theory, by `LCov` (from
`Lifting`): `LCov T Y X` says that in every model `Y` relates every pair `X`
relates. `Backed T Y X` is the converse inclusion, and also holds for the
pairs of the triples themselves, whatever their stores (`GRel.at Set.univ`):
that is what makes the derivation an answer stands for exist even when no
model lets the answer relate anything.

An answer `a` stands for a relation `X` (`Ref T a X`) when it is backed by `X`
and covers it; `DC T A X` says that `X` relates nothing in any model or some
answer of `A` covers it. Every operator the engine uses preserves these.
-/
import RwLog.Rungs.R001.Proofs.Derivations
import RwLog.Rungs.R001.Proofs.Tier0.Simp

namespace RwLog

namespace R001

namespace Tier0

variable {T : Theory}

open Lifting (LCov at_comp at_meet at_inv)

/-! ## Dead relations, answers and coverage -/

/-- No model of the theory lets the relation relate a pair. -/
def DeadR (T : Theory) (X : GRel) : Prop := ∀ M, T.Model M → X.at M = ∅

/-- `Y` relates only pairs `X` relates: in every model of the theory, and
among the pairs of their triples. -/
def Backed (T : Theory) (Y X : GRel) : Prop := LCov T X Y ∧ Y.at Set.univ ⊆ X.at Set.univ

/-- The answer `a` stands for `X`: it relates only pairs of `X`, and in every
model of the theory every pair of `X`. -/
def Ref (T : Theory) (a : Span) (X : GRel) : Prop := Backed T a.den X ∧ LCov T a.den X

/-- `X` is dead, or one answer of `A` covers it. -/
def DC (T : Theory) (A : List Span) (X : GRel) : Prop := DeadR T X ∨ ∃ a ∈ A, LCov T a.den X

theorem lcov_of_subset {X Y : GRel} (h : X ⊆ Y) : LCov T Y X := fun M _ => GRel.at_mono h M

theorem lcov_of_covers {a b : Span} (h : a.Covers b) : LCov T a.den b.den :=
  Lifting.coversLive_iff.1 h.live

theorem Backed.of_subset {Y X : GRel} (h : Y ⊆ X) : Backed T Y X :=
  ⟨lcov_of_subset h, GRel.at_mono h _⟩

theorem Backed.refl (X : GRel) : Backed T X X := ⟨LCov.refl X, le_rfl⟩

theorem Backed.trans {Z Y X : GRel} (h₁ : Backed T Z Y) (h₂ : Backed T Y X) : Backed T Z X :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem Backed.comp {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Backed T Y₁ X₁) (h₂ : Backed T Y₂ X₂) :
    Backed T (Y₁.comp Y₂) (X₁.comp X₂) := by
  refine ⟨h₁.1.comp h₂.1, ?_⟩
  rw [at_comp, at_comp]
  rintro p ⟨m, ha, hb⟩
  exact ⟨m, h₁.2 ha, h₂.2 hb⟩

theorem Backed.meet {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Backed T Y₁ X₁) (h₂ : Backed T Y₂ X₂) :
    Backed T (Y₁.meet Y₂) (X₁.meet X₂) := by
  refine ⟨h₁.1.meet h₂.1, ?_⟩
  rw [at_meet, at_meet]
  exact Set.inter_subset_inter h₁.2 h₂.2

theorem Backed.inv {Y X : GRel} (h : Backed T Y X) : Backed T Y.inv X.inv := by
  refine ⟨h.1.inv, ?_⟩
  rw [at_inv, at_inv]
  exact fun p hp => h.2 hp

theorem Ref.trans {a : Span} {Y X : GRel} (h : Ref T a Y) (hb : Backed T Y X) (hd : LCov T Y X) :
    Ref T a X := ⟨h.1.trans hb, h.2.trans hd⟩

theorem Ref.of_eq {a : Span} {Y X : GRel} (h : Ref T a Y) (e : Y = X) : Ref T a X := e ▸ h

theorem Ref.self (a : Span) : Ref T a a.den := ⟨Backed.refl _, LCov.refl _⟩

theorem Ref.swap {a : Span} {X : GRel} (h : Ref T a X) : Ref T a.swap X.inv := by
  unfold Ref; rw [swap_den]; exact ⟨h.1.inv, h.2.inv⟩

/-- An answer stands for a relation with a triple. -/
theorem Ref.nonempty {a : Span} {X : GRel} (h : Ref T a X) : X.Nonempty := by
  obtain ⟨y, hy⟩ := Span.den_nonempty a
  obtain ⟨S, hx, -⟩ := h.1.2 (show (y.1, y.2.1) ∈ a.den.at Set.univ from
    ⟨y.2.2, hy, Set.subset_univ _⟩)
  exact ⟨_, hx⟩

theorem at_empty (M : Interp) : (∅ : GRel).at M = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ => h

theorem DeadR.of_dom {X Y : GRel} (hd : LCov T Y X) (h : DeadR T Y) : DeadR T X :=
  fun M hM => Set.subset_eq_empty (hd M hM) (h M hM)

/-- A relation covered by nothing is dead. -/
theorem DeadR.of_empty {X : GRel} (hd : LCov T ∅ X) : DeadR T X :=
  fun M hM => Set.subset_eq_empty (hd M hM) (at_empty M)

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

theorem DeadR.inv {X : GRel} (h : DeadR T X) : DeadR T X.inv := by
  intro M hM
  rw [at_inv, h M hM]
  exact Set.eq_empty_of_forall_notMem fun _ h => h

theorem DC.swap {A : List Span} {X : GRel} (h : DC T A X) : DC T (A.map Span.swap) X.inv := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl h.inv
  · refine Or.inr ⟨a.swap, List.mem_map_of_mem ha, ?_⟩
    rw [swap_den]; exact h.inv

theorem DeadR.comp_left {X Y : GRel} (h : DeadR T X) : DeadR T (X.comp Y) := by
  intro M hM
  rw [at_comp, h M hM]
  exact Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ => h

theorem DeadR.comp_right {X Y : GRel} (h : DeadR T Y) : DeadR T (X.comp Y) := by
  intro M hM
  rw [at_comp, h M hM]
  exact Set.eq_empty_of_forall_notMem fun _ ⟨_, _, h⟩ => h

theorem DeadR.meet_left {X Y : GRel} (h : DeadR T X) : DeadR T (X.meet Y) := by
  intro M hM
  rw [at_meet, h M hM, Set.empty_inter]

theorem DeadR.meet_right {X Y : GRel} (h : DeadR T Y) : DeadR T (X.meet Y) := by
  intro M hM
  rw [at_meet, h M hM, Set.inter_empty]

theorem deadR_den {s : Span} : DeadR T s.den ↔ s.Dead T := by
  simp only [DeadR, Span.Dead, Span.denAt_eq]

/-! ## Simplified candidates -/

section Live

variable (hSE : Obligation.simplify_exact) (hwf : ∀ ρ ∈ T, ρ.WellFormed)
include hSE hwf

theorem live_ref {z c : Span} (h : c ∈ live T z) : Ref T c z.den := by
  have he := Lifting.live_leq hSE hwf h
  have hs : T.simplify z = some c := by simpa [live] using h
  exact ⟨⟨he.2, simplify_pairs hs⟩, he.1⟩

theorem live_dc {z : Span} {X : GRel} (h : LCov T z.den X) : DC T (live T z) X := by
  cases hs : T.simplify z with
  | none =>
    have hd := (hSE T z hwf).1 hs
    exact Or.inl (DeadR.of_dom h (deadR_den.2 hd))
  | some c =>
    have hc : c ∈ live T z := by simp [live, hs]
    exact Or.inr ⟨c, hc, (live_ref hSE hwf hc).2.trans h⟩

theorem composeLive_ref {x y c : Span} {X Y : GRel} (hx : Ref T x X) (hy : Ref T y Y)
    (hc : c ∈ composeLive T x y) : Ref T c (X.comp Y) := by
  unfold composeLive at hc
  split at hc
  · rename_i z hz
    refine (live_ref hSE hwf hc).trans ?_ ?_ <;> rw [compose_some hz]
    · exact hx.1.comp hy.1
    · exact hx.2.comp hy.2
  · simp at hc

theorem meetLive_ref {x y c : Span} {X Y : GRel} (hx : Ref T x X) (hy : Ref T y Y)
    (hc : c ∈ meetLive T x y) : Ref T c (X.meet Y) := by
  unfold meetLive at hc
  split at hc
  · rename_i z hz
    refine (live_ref hSE hwf hc).trans ?_ ?_ <;> rw [meet_some hz]
    · exact hx.1.meet hy.1
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
