/-
# Dropping hidden variables

A variable that occurs in the constraints of a store and not in its pattern
is *hidden*. When every variable has infinitely many values in its sorts, a
hidden variable says nothing about the others: an exclusion can be avoided
by a choice of a hidden variable alone exactly when that variable is in the
solved form of its equations, and then the exclusion is dropped with the
variable (`CStore.prune`, `prune_spec`). The exclusions that are left are
kept as their solved forms, which mention no hidden variable.

After this every variable of the store occurs in its pattern, so `tighten`
replaces variables of the pattern only.
-/
import RwLog.Sorts.Norm
import RwLog.Sorts.Orient

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-! ## The solved form of equations -/

/-- Changing a variable in the value of a variable the solution moves avoids
the equations. -/
theorem falsify_at {E : Eqns Nat} {θ : Nat → Pat} (hθ : solve E = some θ) {y w : Nat}
    (hy : θ y ≠ .var y) (hw : w ∈ (θ y).vars) (σ₀ : Nat → GTerm) :
    ¬ Eqns.Unifies (update σ₀ w (.app (σ₀ y) (σ₀ y))) E := by
  have hwy : w ≠ y := fun e => bound_not_mem hθ hy (e ▸ hw)
  intro hun
  have := (solve_some hθ).2 _ hun y
  have hsz := Term.size_le_bind (update σ₀ w (.app (σ₀ y) (σ₀ y))) hw
  rw [this] at hsz
  simp [update, Ne.symm hwy, Term.size] at hsz
  omega

/-- The equations `y = θ y` for the variables `y` of the list that `θ`
moves. -/
def solvedOn (θ : Nat → Pat) (V : List Nat) : Eqns Nat :=
  (V.filter fun y => decide (θ y ≠ .var y)).map fun y => (.var y, θ y)

theorem mem_solvedOn {θ : Nat → Pat} {V : List Nat} {p : Pat × Pat} :
    p ∈ solvedOn θ V ↔ ∃ y ∈ V, θ y ≠ .var y ∧ p = (.var y, θ y) := by
  simp only [solvedOn, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hy, hne⟩, rfl⟩
    exact ⟨y, hy, hne, rfl⟩
  · rintro ⟨y, hy, hne, rfl⟩
    exact ⟨y, ⟨hy, hne⟩, rfl⟩

section solved

variable {E : Eqns Nat} {θ : Nat → Pat} {V : List Nat}

/-- The solved form over all the variables of the equations holds exactly
when the equations do. -/
theorem solvedOn_unifies (hθ : solve E = some θ) (hV : ∀ y ∈ E.vars, y ∈ V) (σ : Nat → GTerm) :
    Eqns.Unifies σ (solvedOn θ V) ↔ Eqns.Unifies σ E := by
  constructor
  · intro hu
    have key : ∀ y ∈ E.vars, (θ y).bind σ = σ y := by
      intro y hy
      by_cases h : θ y = .var y
      · rw [h]; rfl
      · exact (hu (.var y, θ y) (mem_solvedOn.2 ⟨y, hV y hy, h, rfl⟩)).symm
    intro p hp
    have e₁ : p.1.bind σ = (p.1.bind θ).bind σ := by
      rw [Term.bind_bind]
      exact Term.bind_congr fun v hv =>
        (key v (List.mem_flatMap.2 ⟨p, hp, List.mem_append_left _ hv⟩)).symm
    have e₂ : p.2.bind σ = (p.2.bind θ).bind σ := by
      rw [Term.bind_bind]
      exact Term.bind_congr fun v hv =>
        (key v (List.mem_flatMap.2 ⟨p, hp, List.mem_append_right _ hv⟩)).symm
    rw [e₁, e₂, (solve_some hθ).1 p hp]
  · intro hu p hp
    obtain ⟨y, -, -, rfl⟩ := mem_solvedOn.1 hp
    exact ((solve_some hθ).2 σ hu y).symm

/-- The variables of the solved form are variables of the equations. -/
theorem solvedOn_vars (hθ : solve E = some θ) {v : Nat} (hv : v ∈ (solvedOn θ V).vars) :
    v ∈ E.vars := by
  obtain ⟨p, hp, hvp⟩ := List.mem_flatMap.1 hv
  obtain ⟨y, -, hne, rfl⟩ := mem_solvedOn.1 hp
  rcases List.mem_append.1 hvp with h | h
  · simp only [Term.vars, List.mem_singleton] at h
    subst h
    by_contra hno
    exact hne (solve_var_of_not_mem hθ hno)
  · exact solve_vars hθ h hne

theorem solvedOn_fo (hE : E.FO) (hθ : solve E = some θ) : (solvedOn θ V).FO := by
  intro p hp
  obtain ⟨y, -, -, rfl⟩ := mem_solvedOn.1 hp
  exact ⟨rfl, solve_fo E hE θ hθ y⟩

/-- Changing one variable of the solved form avoids the equations. -/
theorem solvedOn_avoid (hθ : solve E = some θ) {h : Nat} (hh : h ∈ (solvedOn θ V).vars)
    (σ₀ : Nat → GTerm) : ∃ u, ¬ Eqns.Unifies (update σ₀ h u) E := by
  obtain ⟨p, hp, hvp⟩ := List.mem_flatMap.1 hh
  obtain ⟨y, -, hne, rfl⟩ := mem_solvedOn.1 hp
  rcases List.mem_append.1 hvp with hy | hy
  · simp only [Term.vars, List.mem_singleton] at hy
    subst hy
    exact falsify_bound hθ hne σ₀
  · exact ⟨_, falsify_at hθ hne hy σ₀⟩

end solved

/-- The solved form of equations, over their variables in the order they
first occur; nothing when they have no solution. -/
def solvedEx (E : Eqns Nat) : Option (Eqns Nat) :=
  (solve E).map fun θ => solvedOn θ (firsts E.vars)

/-- The solved forms of the exclusions that have one and whose variables
are all in `K`. -/
def pruneX (K : List Nat) (X : List (Eqns Nat)) : List (Eqns Nat) :=
  (X.filterMap solvedEx).filter fun E' => decide (∀ v ∈ E'.vars, v ∈ K)

theorem mem_pruneX {K : List Nat} {X : List (Eqns Nat)} {E' : Eqns Nat} :
    E' ∈ pruneX K X ↔
      (∃ E ∈ X, ∃ θ, solve E = some θ ∧ E' = solvedOn θ (firsts E.vars)) ∧
        ∀ v ∈ E'.vars, v ∈ K := by
  simp only [pruneX, List.mem_filter, List.mem_filterMap, decide_eq_true_eq, solvedEx,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨E, hE, θ, hθ, rfl⟩, hK⟩
    exact ⟨⟨E, hE, θ, hθ, rfl⟩, hK⟩
  · rintro ⟨⟨E, hE, θ, hθ, rfl⟩, hK⟩
    exact ⟨⟨E, hE, θ, hθ, rfl⟩, hK⟩

theorem pruneX_congr {K K' : List Nat} (h : ∀ v, v ∈ K ↔ v ∈ K') (X : List (Eqns Nat)) :
    pruneX K X = pruneX K' X := by
  unfold pruneX
  refine List.filter_congr fun E' _ => ?_
  simp only [h]

/-! ## The store without its hidden variables -/

namespace CStore

/-- The store with the sorts of the variables of its pattern only, and the
solved forms of the exclusions over them. -/
def prune (s : CStore) : CStore :=
  ⟨s.t, (List.range s.c.length).map fun v => if v ∈ s.t.vars then s.conj v else ∅,
    pruneX s.t.vars s.x⟩

theorem prune_length (s : CStore) : s.prune.c.length = s.c.length := by simp [prune]

theorem prune_conj {s : CStore} (htv : ∀ v ∈ s.t.vars, v < s.c.length) (v : Nat) :
    s.prune.conj v = if v ∈ s.t.vars then s.conj v else ∅ := by
  have e : s.prune.conj v = ((List.range s.c.length).map fun v =>
      if v ∈ s.t.vars then s.conj v else ∅).getD v ∅ := rfl
  rw [e, List.getD_eq_getElem?_getD]
  by_cases hv : v < s.c.length
  · simp [hv]
  · have : v ∉ s.t.vars := fun h => hv (htv v h)
    simp [hv, this]

end CStore

open CStore

theorem count_empty_many (S : Sorts) : count S ∅ = .many :=
  count_many.2 ⟨.sym "a", .sym "b", by simp, fun n hn => by simp at hn, fun n hn => by simp at hn⟩

/-- A first-order store all of whose variables have infinitely many values
in their sorts denotes what it does without its hidden variables, and that
store is one `tighten` goes on from. -/
theorem prune_spec (hS : S.WellFormed) {s : CStore} (hfin : s.store.Fin s.c.length)
    (hmany : ∀ v, count S (s.conj v) = .many) :
    s.prune.store.Den S = s.store.Den S ∧ Kept S s.prune ∧
      ∀ v, count S (s.prune.conj v) = .many := by
  have hconj := prune_conj hfin.tv
  have hcm : ∀ v, count S (s.prune.conj v) = .many := by
    intro v
    rw [hconj]
    split
    · exact hmany v
    · exact count_empty_many S
  have hxK : ∀ E' ∈ s.prune.x, ∀ v ∈ E'.vars, v ∈ s.t.vars := fun E' hE' =>
    (mem_pruneX.1 hE').2
  refine ⟨?_, ⟨⟨hfin.fo, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, hcm⟩
  · -- what it denotes
    ext g
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      let H := (List.range s.c.length).filter fun v => decide (v ∉ s.t.vars)
      have hH : ∀ v, v ∈ H ↔ v < s.c.length ∧ v ∉ s.t.vars := by
        intro v; simp [H, List.mem_filter]
      obtain ⟨τ, hτ, hag, -⟩ := s.store.rich (S := S) H
        (fun h _ => count_many_infinite hS (hmany h)) σ
        (fun v hv => by
          show MemC S (s.conj v) (σ v)
          by_cases hvt : v ∈ s.t.vars
          · have := hσ.1 v
            change MemC S (s.prune.conj v) (σ v) at this
            rwa [hconj, ite_eq_left hvt] at this
          · have : s.c.length ≤ v := by
              by_contra h; exact hv ((hH v).2 ⟨by omega, hvt⟩)
            rw [s.conj_of_ge this]; exact memC_empty S _)
        []
        (by
          intro E hE
          cases hθ : solve E with
          | none => exact ⟨σ, fun _ _ => rfl, solve_none hθ σ⟩
          | some θ =>
            by_cases hK : ∀ v ∈ (solvedOn θ (firsts E.vars)).vars, v ∈ s.t.vars
            · refine ⟨σ, fun _ _ => rfl, fun hu => ?_⟩
              refine hσ.2 (solvedOn θ (firsts E.vars))
                (mem_pruneX.2 ⟨⟨E, hE, θ, hθ, rfl⟩, hK⟩) ?_
              exact (solvedOn_unifies hθ (fun y hy => ((firsts_spec E.vars).2.1 y).2 hy) σ).2 hu
            · simp only [not_forall] at hK
              obtain ⟨v, hv, hvt⟩ := hK
              obtain ⟨p, hp, hvp⟩ := List.mem_flatMap.1 (solvedOn_vars hθ hv)
              have hvN : v < s.c.length := hfin.xv E hE p hp v hvp
              obtain ⟨u, hu⟩ := solvedOn_avoid hθ hv σ
              refine ⟨update σ v u, fun w hw => ?_, hu⟩
              have : w ≠ v := by
                rintro rfl; exact hw ((hH _).2 ⟨hvN, hvt⟩)
              simp [update, this])
        (by simp)
      refine ⟨τ, hτ, ?_⟩
      show s.t.bind σ = s.t.bind τ
      exact Term.bind_congr fun v hv => (hag v fun hm => ((hH v).1 hm).2 hv).symm
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨σ, ⟨fun v => ?_, fun E' hE' hu => ?_⟩, rfl⟩
      · show MemC S (s.prune.conj v) (σ v)
        rw [hconj]
        split
        · exact hσ.1 v
        · exact memC_empty S _
      · obtain ⟨⟨E, hE, θ, hθ, rfl⟩, -⟩ := mem_pruneX.1 hE'
        exact hσ.2 E hE
          ((solvedOn_unifies hθ (fun y hy => ((firsts_spec E.vars).2.1 y).2 hy) σ).1 hu)
  · rw [prune_length]; exact hfin.tv
  · intro v hv
    rw [prune_length] at hv
    show s.prune.conj v = ∅
    rw [hconj, ite_eq_right (show v ∉ s.t.vars from fun h => absurd (hfin.tv v h) (by omega))]
  · intro E' hE'
    obtain ⟨⟨E, hE, θ, hθ, rfl⟩, -⟩ := mem_pruneX.1 hE'
    exact solvedOn_fo (hfin.xfo E hE) hθ
  · intro E' hE' p hp v hv
    rw [prune_length]
    exact hfin.tv v (hxK E' hE' v (List.mem_flatMap.2 ⟨p, hp, hv⟩))
  · intro v hv
    show s.prune.conj v = ∅
    rw [hconj, ite_eq_right (show v ∉ s.t.vars from hv)]
  · intro E' hE' p hp v hv
    exact hxK E' hE' v (List.mem_flatMap.2 ⟨p, hp, hv⟩)
  · intro v _ g e
    rw [hcm v] at e
    cases e

end Sorts
end RwLog
