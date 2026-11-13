/-
# Distinct subterms

`Term.subs t` is the set of subterms of `t`, and `Eqns.subs E` the set of
subterms of both sides of every equation. Their sizes are what the base
machine pays for: its store keeps one node for each distinct subterm
(`Trusted/Base.lean`), so a term costs `(subs t).card` nodes however often a
subterm is repeated in it, never more than `t.size` (`Term.card_subs_le_size`).

For the cost of solving equations (`Kernel/Machine/Solve.lean`):

* eliminating a variable makes the set of subterms strictly smaller
  (`Eqns.card_subs_subst_lt`), because the variable and the term it is
  replaced by become one;
* `Eqns.lead E`, the height of the left side of the first equation whose
  sides differ, is below the number of subterms (`Eqns.lead_le`) and falls
  when that equation is between two applications and is split
  (`Eqns.lead_split`).
-/
import RwLog.Kernel.Solve
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Basic

namespace RwLog

namespace Term

variable {V : Type} [DecidableEq V]

/-- The subterms of a term. -/
def subs : Term V → Finset (Term V)
  | var v => {var v}
  | sym f => {sym f}
  | app a b => insert (app a b) (subs a ∪ subs b)

theorem self_mem_subs (t : Term V) : t ∈ subs t := by
  cases t <;> simp [subs]

theorem subs_trans {t u : Term V} (h : u ∈ subs t) : subs u ⊆ subs t := by
  induction t with
  | var v => simp only [subs, Finset.mem_singleton] at h; subst h; exact Finset.Subset.refl _
  | sym f => simp only [subs, Finset.mem_singleton] at h; subst h; exact Finset.Subset.refl _
  | app a b iha ihb =>
    simp only [subs, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Finset.Subset.refl _
    · exact (iha h).trans (by simp only [subs]; intro x hx; simp [hx])
    · exact (ihb h).trans (by simp only [subs]; intro x hx; simp [hx])

theorem subs_app_left {t a b : Term V} (h : app a b ∈ subs t) : a ∈ subs t :=
  subs_trans h (by simp [subs, self_mem_subs])

theorem subs_app_right {t a b : Term V} (h : app a b ∈ subs t) : b ∈ subs t :=
  subs_trans h (by simp [subs, self_mem_subs])

theorem size_le_of_mem_subs {t u : Term V} (h : u ∈ subs t) : u.size ≤ t.size := by
  induction t with
  | var v => simp only [subs, Finset.mem_singleton] at h; subst h; exact Nat.le_refl _
  | sym f => simp only [subs, Finset.mem_singleton] at h; subst h; exact Nat.le_refl _
  | app a b iha ihb =>
    simp only [subs, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Nat.le_refl _
    · have := iha h; simp only [size]; omega
    · have := ihb h; simp only [size]; omega

theorem card_subs_le_size (t : Term V) : (subs t).card ≤ t.size := by
  induction t with
  | var v => simp [subs, size]
  | sym f => simp [subs, size]
  | app a b iha ihb =>
    simp only [subs, size]
    calc (insert (app a b) (subs a ∪ subs b)).card ≤ (subs a ∪ subs b).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (subs a).card + (subs b).card + 1 := by
          have := Finset.card_union_le (subs a) (subs b); omega
      _ ≤ a.size + b.size + 1 := by omega

/-- The height of a term: the longest chain of applications in it. -/
def height : Term V → Nat
  | var _ => 0
  | sym _ => 0
  | app a b => max (height a) (height b) + 1

theorem height_lt_card (t : Term V) : height t < (subs t).card := by
  induction t with
  | var v => simp [subs, height]
  | sym f => simp [subs, height]
  | app a b iha ihb =>
    have hn : app a b ∉ subs a ∪ subs b := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · have := size_le_of_mem_subs h; simp only [size] at this; omega
      · have := size_le_of_mem_subs h; simp only [size] at this; omega
    simp only [subs, height, Finset.card_insert_of_notMem hn]
    have h₁ : (subs a).card ≤ (subs a ∪ subs b).card :=
      Finset.card_le_card Finset.subset_union_left
    have h₂ : (subs b).card ≤ (subs a ∪ subs b).card :=
      Finset.card_le_card Finset.subset_union_right
    omega

/-- A subterm of an instance by `single x u` is an instance of a subterm, or
a subterm of `u`. -/
theorem subs_bind_single (x : V) (u t : Term V) :
    subs (t.bind (single x u)) ⊆ (subs t).image (bind (single x u)) ∪ subs u := by
  induction t with
  | var v =>
    by_cases hv : v = x
    · subst hv
      simp only [bind_var, single, ↓reduceIte]
      exact Finset.subset_union_right
    · have e : (var v : Term V).bind (single x u) = var v := by simp [single, hv]
      rw [e]
      intro w hw
      simp only [subs, Finset.mem_singleton] at hw
      subst hw
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨var v, by simp [subs], e⟩)
  | sym f =>
    intro w hw
    simp only [bind_sym, subs, Finset.mem_singleton] at hw
    subst hw
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨sym f, by simp [subs], rfl⟩)
  | app a b iha ihb =>
    intro w hw
    simp only [bind_app, subs, Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hw | hw
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨app a b, self_mem_subs _, rfl⟩)
    · rcases Finset.mem_union.1 (iha hw) with h | h
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h
        exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨s, by simp [subs, hs], rfl⟩)
      · exact Finset.mem_union_right _ h
    · rcases Finset.mem_union.1 (ihb hw) with h | h
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h
        exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨s, by simp [subs, hs], rfl⟩)
      · exact Finset.mem_union_right _ h

theorem vars_subset_of_mem_subs {t s : Term V} (h : s ∈ subs t) : ∀ v ∈ s.vars, v ∈ t.vars := by
  induction t with
  | var v => simp only [subs, Finset.mem_singleton] at h; subst h; exact fun _ h => h
  | sym f => simp only [subs, Finset.mem_singleton] at h; subst h; exact fun _ h => h
  | app a b iha ihb =>
    simp only [subs, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact fun _ h => h
    · intro v hv; simp [vars, iha h v hv]
    · intro v hv; simp [vars, ihb h v hv]

end Term

open Term

namespace Eqns

variable {V : Type} [DecidableEq V]

/-- The subterms of both sides of every equation. -/
def subs : Eqns V → Finset (Term V)
  | [] => ∅
  | p :: E => Term.subs p.1 ∪ Term.subs p.2 ∪ subs E

@[simp] theorem subs_nil : subs ([] : Eqns V) = ∅ := rfl

@[simp] theorem subs_cons (t u : Term V) (E : Eqns V) :
    subs ((t, u) :: E) = Term.subs t ∪ Term.subs u ∪ subs E := rfl

theorem subs_tail_subset (t u : Term V) (E : Eqns V) : subs E ⊆ subs ((t, u) :: E) :=
  Finset.subset_union_right

theorem subs_split_subset (a b c d : Term V) (E : Eqns V) :
    subs ((a, c) :: (b, d) :: E) ⊆ subs ((app a b, app c d) :: E) := by
  intro w hw
  simp only [subs_cons, Finset.mem_union, Term.subs, Finset.mem_insert] at hw ⊢
  tauto

theorem subs_subst_subset (x : V) (u : Term V) (E : Eqns V) :
    subs (subst x u E) ⊆ (subs E).image (bind (single x u)) ∪ Term.subs u := by
  induction E with
  | nil => simp [subst]
  | cons p E ih =>
    obtain ⟨t, s⟩ := p
    have ih' : subs (subst x u E) ⊆ (subs E).image (bind (single x u)) ∪ Term.subs u := ih
    intro w hw
    simp only [subst, List.map_cons, subs_cons, Finset.mem_union] at hw
    simp only [subs_cons, Finset.image_union, Finset.mem_union]
    rcases hw with (hw | hw) | hw
    · rcases Finset.mem_union.1 (subs_bind_single x u t hw) with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases Finset.mem_union.1 (subs_bind_single x u s hw) with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases Finset.mem_union.1 (ih' hw) with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

/-- Eliminating a variable leaves fewer subterms: the variable and the term
it is replaced by become one. `S` is any set that has the equations' subterms,
the variable and the term. -/
theorem card_subs_subst_lt {x : V} {u : Term V} {E : Eqns V} {S : Finset (Term V)}
    (hx : x ∉ u.vars) (hE : subs E ⊆ S) (hv : var x ∈ S) (hu : Term.subs u ⊆ S) :
    (subs (subst x u E)).card < S.card := by
  have hfix : ∀ s ∈ Term.subs u, s.bind (single x u) = s := fun s hs =>
    bind_single_of_not_mem fun h => hx (vars_subset_of_mem_subs hs x h)
  have hne : var x ≠ u := by
    rintro rfl; exact hx (by simp [Term.vars])
  have hsub : subs (subst x u E) ⊆ (S.erase (var x)).image (bind (single x u)) := by
    intro w hw
    rcases Finset.mem_union.1 (subs_subst_subset x u E hw) with h | h
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h
      by_cases hsx : s = var x
      · subst hsx
        refine Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨hne.symm, hu (self_mem_subs u)⟩, ?_⟩
        rw [hfix u (self_mem_subs u)]
        simp [single]
      · exact Finset.mem_image.2 ⟨s, Finset.mem_erase.2 ⟨hsx, hE hs⟩, rfl⟩
    · refine Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨?_, hu h⟩, hfix w h⟩
      rintro rfl
      exact hx (vars_subset_of_mem_subs h x (by simp [Term.vars]))
  calc (subs (subst x u E)).card ≤ ((S.erase (var x)).image (bind (single x u))).card :=
        Finset.card_le_card hsub
    _ ≤ (S.erase (var x)).card := Finset.card_image_le
    _ < S.card := Finset.card_erase_lt_of_mem hv

/-- The height of the left side of the first equation whose sides differ. -/
def lead : Eqns V → Nat
  | [] => 0
  | p :: E => if p.1 = p.2 then lead E else height p.1

theorem lead_le (E : Eqns V) : lead E ≤ (subs E).card := by
  induction E with
  | nil => simp [lead]
  | cons p E ih =>
    obtain ⟨t, u⟩ := p
    simp only [lead, subs_cons]
    split
    · exact ih.trans (Finset.card_le_card Finset.subset_union_right)
    · have := height_lt_card t
      have h₁ : (Term.subs t).card ≤ (Term.subs t ∪ Term.subs u ∪ subs E).card :=
        Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)
      omega

theorem lead_skip (t : Term V) (E : Eqns V) : lead ((t, t) :: E) = lead E := by
  simp [lead]

/-- Splitting an equation between two different applications lowers `lead`. -/
theorem lead_split {a b c d : Term V} (E : Eqns V) (h : app a b ≠ app c d) :
    lead ((a, c) :: (b, d) :: E) < lead ((app a b, app c d) :: E) := by
  simp only [lead, h, ↓reduceIte, height]
  by_cases hac : a = c
  · have hbd : b ≠ d := fun e => h (by rw [hac, e])
    simp only [hac, ↓reduceIte, hbd]
    omega
  · simp only [hac, ↓reduceIte]
    omega

end Eqns

end RwLog
