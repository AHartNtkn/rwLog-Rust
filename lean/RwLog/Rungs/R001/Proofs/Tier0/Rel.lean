/-
# Tier 0 proofs, part 1: relations up to the theory

The engine's answers are related to the relations they stand for in two ways:

* `Dom T Y X`: every triple of `X` the theory cannot refute is matched by a
  triple of `Y` with the same pair and a store no stronger (coverage up to
  the theory; `Span.CoversLive` is `Dom` on denotations);
* `GRel.Backed T Y X`: every triple of `Y` is backed by a triple of `X`
  (soundness up to the theory).

`Ref T a X` is both, for one answer `a`; `DC T A X` says that `X` is dead or
some answer of `A` covers it. Every operator the engine uses preserves these.
-/
import RwLog.Rungs.R001.Proofs.Kernel

namespace RwLog

namespace R001

namespace Tier0

variable {T : Theory}

/-! ## Stores no stronger than others -/

theorem refutes_union_empty {S : GStore} : Refutes T (S ∪ ∅) ↔ Refutes T S := by
  rw [Finset.union_empty]

theorem NS.refl (S : GStore) : GStore.NoStronger T S S := fun _ h => h

theorem NS.trans {A B C : GStore} (h₁ : GStore.NoStronger T A B) (h₂ : GStore.NoStronger T B C) :
    GStore.NoStronger T A C := fun X h => h₂ X (h₁ X h)

theorem NS.union {A A' B B' : GStore} (h₁ : GStore.NoStronger T A A')
    (h₂ : GStore.NoStronger T B B') : GStore.NoStronger T (A ∪ B) (A' ∪ B') := by
  intro C h
  have e₁ : A ∪ B ∪ C = A ∪ (B ∪ C) := Finset.union_assoc _ _ _
  have h' := h₁ (B ∪ C) (e₁ ▸ h)
  have e₂ : A' ∪ (B ∪ C) = B ∪ (A' ∪ C) := by
    ext x; simp only [Finset.mem_union]; tauto
  have h'' := h₂ (A' ∪ C) (e₂ ▸ h')
  have e₃ : B' ∪ (A' ∪ C) = A' ∪ B' ∪ C := by
    ext x; simp only [Finset.mem_union]; tauto
  exact e₃ ▸ h''

/-- A store no stronger than an unrefuted one is unrefuted. -/
theorem NS.unref {A B : GStore} (h : GStore.NoStronger T A B) (hB : ¬ Refutes T B) :
    ¬ Refutes T A := fun hA =>
  hB (refutes_union_empty.1 (h ∅ (refutes_union_empty.2 hA)))

theorem NS.sub {A B : GStore} (h : A ⊆ B) : GStore.NoStronger T A B :=
  GStore.NoStronger.of_subset h

/-! ## Coverage and backing of relations -/

/-- `Y` covers the unrefuted triples of `X`, up to the theory. -/
def Dom (T : Theory) (Y X : GRel) : Prop :=
  ∀ x ∈ X, ¬ Refutes T x.2.2 →
    ∃ y ∈ Y, y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ GStore.NoStronger T y.2.2 x.2.2

/-- Every triple of the relation carries a refuted store. -/
def DeadR (T : Theory) (X : GRel) : Prop := ∀ x ∈ X, Refutes T x.2.2

/-- The answer `a` stands for `X` exactly, up to the theory. -/
def Ref (T : Theory) (a : Span) (X : GRel) : Prop := (a.den).Backed T X ∧ Dom T a.den X

/-- `X` is dead, or one answer of `A` covers it. -/
def DC (T : Theory) (A : List Span) (X : GRel) : Prop := DeadR T X ∨ ∃ a ∈ A, Dom T a.den X

theorem Dom.refl (X : GRel) : Dom T X X := fun x hx _ => ⟨x, hx, rfl, rfl, NS.refl _⟩

theorem Dom.of_subset {X Y : GRel} (h : X ⊆ Y) : Dom T Y X :=
  fun x hx _ => ⟨x, h hx, rfl, rfl, NS.refl _⟩

theorem Dom.trans {Z Y X : GRel} (h₁ : Dom T Z Y) (h₂ : Dom T Y X) : Dom T Z X := by
  intro x hx hn
  obtain ⟨y, hy, e1, e2, hs⟩ := h₂ x hx hn
  obtain ⟨z, hz, f1, f2, hs'⟩ := h₁ y hy (NS.unref hs hn)
  exact ⟨z, hz, f1.trans e1, f2.trans e2, NS.trans hs' hs⟩

theorem Dom.comp {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Dom T Y₁ X₁) (h₂ : Dom T Y₂ X₂) :
    Dom T (Y₁.comp Y₂) (X₁.comp X₂) := by
  rintro ⟨u, v, S⟩ ⟨m, S₁, S₂, hx₁, hx₂, hS⟩ hn
  simp only at hS hn; subst hS
  obtain ⟨⟨u', m', S₁'⟩, hy₁, e1, e2, hs₁⟩ :=
    h₁ _ hx₁ (fun h => hn (h.mono Finset.subset_union_left))
  obtain ⟨⟨m'', v', S₂'⟩, hy₂, f1, f2, hs₂⟩ :=
    h₂ _ hx₂ (fun h => hn (h.mono Finset.subset_union_right))
  simp only at e1 e2 f1 f2 hs₁ hs₂; subst e1 e2 f1 f2
  exact ⟨(_, _, S₁' ∪ S₂'), ⟨_, S₁', S₂', hy₁, hy₂, rfl⟩, rfl, rfl, NS.union hs₁ hs₂⟩

theorem Dom.meet {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Dom T Y₁ X₁) (h₂ : Dom T Y₂ X₂) :
    Dom T (Y₁.meet Y₂) (X₁.meet X₂) := by
  rintro ⟨u, v, S⟩ ⟨S₁, S₂, hx₁, hx₂, hS⟩ hn
  simp only at hS hn; subst hS
  obtain ⟨⟨u', v', S₁'⟩, hy₁, e1, e2, hs₁⟩ :=
    h₁ _ hx₁ (fun h => hn (h.mono Finset.subset_union_left))
  obtain ⟨⟨u'', v'', S₂'⟩, hy₂, f1, f2, hs₂⟩ :=
    h₂ _ hx₂ (fun h => hn (h.mono Finset.subset_union_right))
  simp only at e1 e2 f1 f2 hs₁ hs₂; subst e1 e2 f1 f2
  exact ⟨(_, _, S₁' ∪ S₂'), ⟨S₁', S₂', hy₁, hy₂, rfl⟩, rfl, rfl, NS.union hs₁ hs₂⟩

theorem Dom.inv {Y X : GRel} (h : Dom T Y X) : Dom T Y.inv X.inv := by
  rintro ⟨u, v, S⟩ hx hn
  obtain ⟨⟨v', u', S'⟩, hy, e1, e2, hs⟩ := h (v, u, S) hx hn
  simp only at e1 e2; subst e1 e2
  exact ⟨(u', v', S'), hy, rfl, rfl, hs⟩

theorem Backed.refl (X : GRel) : X.Backed T X := GRel.Backed.of_subset le_rfl

theorem Backed.trans {Z Y X : GRel} (h₁ : Z.Backed T Y) (h₂ : Y.Backed T X) : Z.Backed T X := by
  intro z hz
  obtain ⟨y, hy, e1, e2, hs⟩ := h₁ z hz
  obtain ⟨x, hx, f1, f2, hs'⟩ := h₂ y hy
  exact ⟨x, hx, f1.trans e1, f2.trans e2, NS.trans hs' hs⟩

theorem Backed.comp {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Y₁.Backed T X₁) (h₂ : Y₂.Backed T X₂) :
    (Y₁.comp Y₂).Backed T (X₁.comp X₂) := by
  rintro ⟨u, v, S⟩ ⟨m, S₁, S₂, hy₁, hy₂, hS⟩
  simp only at hS; subst hS
  obtain ⟨⟨u', m', S₁'⟩, hx₁, e1, e2, hs₁⟩ := h₁ _ hy₁
  obtain ⟨⟨m'', v', S₂'⟩, hx₂, f1, f2, hs₂⟩ := h₂ _ hy₂
  simp only at e1 e2 f1 f2 hs₁ hs₂; subst e1 e2 f1 f2
  exact ⟨(_, _, S₁' ∪ S₂'), ⟨_, S₁', S₂', hx₁, hx₂, rfl⟩, rfl, rfl, NS.union hs₁ hs₂⟩

theorem Backed.meet {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Y₁.Backed T X₁) (h₂ : Y₂.Backed T X₂) :
    (Y₁.meet Y₂).Backed T (X₁.meet X₂) := by
  rintro ⟨u, v, S⟩ ⟨S₁, S₂, hy₁, hy₂, hS⟩
  simp only at hS; subst hS
  obtain ⟨⟨u', v', S₁'⟩, hx₁, e1, e2, hs₁⟩ := h₁ _ hy₁
  obtain ⟨⟨u'', v'', S₂'⟩, hx₂, f1, f2, hs₂⟩ := h₂ _ hy₂
  simp only at e1 e2 f1 f2 hs₁ hs₂; subst e1 e2 f1 f2
  exact ⟨(_, _, S₁' ∪ S₂'), ⟨S₁', S₂', hx₁, hx₂, rfl⟩, rfl, rfl, NS.union hs₁ hs₂⟩

theorem Backed.inv {Y X : GRel} (h : Y.Backed T X) : Y.inv.Backed T X.inv := by
  rintro ⟨u, v, S⟩ hy
  obtain ⟨⟨v', u', S'⟩, hx, e1, e2, hs⟩ := h (v, u, S) hy
  simp only at e1 e2; subst e1 e2
  exact ⟨(u', v', S'), hx, rfl, rfl, hs⟩

theorem Ref.trans {a : Span} {Y X : GRel} (h : Ref T a Y) (hb : Y.Backed T X) (hd : Dom T Y X) :
    Ref T a X := ⟨Backed.trans h.1 hb, Dom.trans h.2 hd⟩

theorem Ref.of_eq {a : Span} {Y X : GRel} (h : Ref T a Y) (e : Y = X) : Ref T a X := e ▸ h

theorem Ref.self (a : Span) : Ref T a a.den := ⟨Backed.refl _, Dom.refl _⟩

theorem Ref.swap {a : Span} {X : GRel} (h : Ref T a X) : Ref T a.swap X.inv := by
  unfold Ref; rw [swap_den]; exact ⟨Backed.inv h.1, Dom.inv h.2⟩

theorem DeadR.of_dom {X Y : GRel} (hd : Dom T Y X) (h : DeadR T Y) : DeadR T X := by
  intro x hx
  by_contra hn
  obtain ⟨y, hy, -, -, hs⟩ := hd x hx hn
  exact NS.unref hs hn (h y hy)

theorem DC.dom {A : List Span} {X Y : GRel} (hd : Dom T Y X) (h : DC T A Y) : DC T A X := by
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
    refine Or.inr ⟨b, hb, Dom.trans ?_ h⟩
    intro x hx _
    obtain ⟨y, hy, e1, e2, e3⟩ := hc x hx
    exact ⟨y, hy, e1, e2, NS.sub e3⟩

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
  exact (hSE T z hwf).2 c h

theorem live_dc {z : Span} {X : GRel} (h : Dom T z.den X) : DC T (live T z) X := by
  cases hs : T.simplify z with
  | none =>
    have hd := (hSE T z hwf).1 hs
    exact Or.inl (DeadR.of_dom h (deadR_den.2 hd))
  | some c =>
    have hr := (hSE T z hwf).2 c hs
    refine Or.inr ⟨c, by simp [live, hs], Dom.trans hr.2 h⟩

theorem composeLive_ref {x y c : Span} {X Y : GRel} (hx : Ref T x X) (hy : Ref T y Y)
    (hc : c ∈ composeLive T x y) : Ref T c (X.comp Y) := by
  unfold composeLive at hc
  split at hc
  · rename_i z hz
    refine (live_ref hSE hwf hc).trans ?_ ?_ <;> rw [compose_some hz]
    · exact Backed.comp hx.1 hy.1
    · exact Dom.comp hx.2 hy.2
  · simp at hc

theorem meetLive_ref {x y c : Span} {X Y : GRel} (hx : Ref T x X) (hy : Ref T y Y)
    (hc : c ∈ meetLive T x y) : Ref T c (X.meet Y) := by
  unfold meetLive at hc
  split at hc
  · rename_i z hz
    refine (live_ref hSE hwf hc).trans ?_ ?_ <;> rw [meet_some hz]
    · exact Backed.meet hx.1 hy.1
    · exact Dom.meet hx.2 hy.2
  · simp at hc

theorem composeLive_dc {x y : Span} {X Y : GRel} (hx : Dom T x.den X) (hy : Dom T y.den Y) :
    DC T (composeLive T x y) (X.comp Y) := by
  have hd := Dom.comp hx hy
  unfold composeLive
  split
  · rename_i z hz
    rw [← compose_some hz] at hd
    exact live_dc hSE hwf hd
  · rename_i hz
    rw [compose_none hz] at hd
    exact Or.inl fun x hx => by
      by_contra hn
      obtain ⟨y, hy, -⟩ := hd x hx hn
      exact hy

theorem meetLive_dc {x y : Span} {X Y : GRel} (hx : Dom T x.den X) (hy : Dom T y.den Y) :
    DC T (meetLive T x y) (X.meet Y) := by
  have hd := Dom.meet hx hy
  unfold meetLive
  split
  · rename_i z hz
    rw [← meet_some hz] at hd
    exact live_dc hSE hwf hd
  · rename_i hz
    rw [meet_none hz] at hd
    exact Or.inl fun x hx => by
      by_contra hn
      obtain ⟨y, hy, -⟩ := hd x hx hn
      exact hy

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
