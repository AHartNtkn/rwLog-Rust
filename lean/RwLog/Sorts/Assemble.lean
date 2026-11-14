/-
# A tight store has a normal form

A store whose pattern cannot be extended and whose variables are numbered in
the order they first occur is brought to normal form without changing its
solutions: each variable is given every declared sort that holds of all its
values, each exclusion is replaced by its normal form (`normExs`) or dropped
when nothing in the sorts satisfies its equations, the exclusions that
another implies are dropped (`antichain`, `covers`). `normal_assemble` is the
statement for any sorts and
exclusions with these properties, and `assembled` puts the computed
exclusions together (`assembled_normal`).
-/
import RwLog.Sorts.Renum
import RwLog.Lib.Antichain
import RwLog.Sorts.NormEx

namespace RwLog
namespace Sorts

open Function

/-! ## Dropping what another member covers -/

/-! ## The exclusions in normal form -/

/-- The normal forms of the exclusions that remove something. -/
def normExs (S : Sorts) (r : Raw) (X : List (Eqns Nat)) : List Binds := X.filterMap (normEx S r)

/-- Exclusions over the variables of a raw store, none of which removes
everything in the sorts, have normal forms that remove the same. -/
theorem normExs_spec {S : Sorts} (r : Raw) (X : List (Eqns Nat)) (hfo : ∀ E ∈ X, E.FO)
    (hv : ∀ E ∈ X, ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, v < r.c.length)
    (hprop : ∀ E ∈ X, ∃ σ ∈ r.store.Pos S, ¬ Eqns.Unifies σ E) :
    (∀ θ ∈ normExs S r X, NormalBinds S r θ) ∧
      ∀ σ ∈ r.store.Pos S,
        (∃ E ∈ X, Eqns.Unifies σ E) ↔ ∃ θ ∈ normExs S r X, Eqns.Unifies σ (eqnsOf θ) := by
  have hv' : ∀ E ∈ X, ∀ v ∈ E.vars, v < r.c.length := by
    intro E hE v hvE
    obtain ⟨p, hp, hvp⟩ := List.mem_flatMap.1 hvE
    exact hv E hE p hp v hvp
  constructor
  · intro θ hθ
    obtain ⟨E, hE, hn⟩ := List.mem_filterMap.1 hθ
    obtain ⟨hpre, hEx, hlive, hloose⟩ := normEx_some (hfo E hE) (hv' E hE) hn
    refine ⟨hpre, ?_, hlive, hloose⟩
    rintro rfl
    obtain ⟨σ, hσ, hnu⟩ := hprop E hE
    have : σ ∈ r.Ex S [] := ⟨hσ, fun p hp => by simp [eqnsOf] at hp⟩
    rw [hEx] at this
    exact hnu this.2
  · intro σ hσ
    constructor
    · rintro ⟨E, hE, hu⟩
      cases hn : normEx S r E with
      | none => exact absurd hu (normEx_none (hfo E hE) (hv' E hE) hn σ hσ)
      | some θ =>
        obtain ⟨-, hEx, -, -⟩ := normEx_some (hfo E hE) (hv' E hE) hn
        have : σ ∈ r.Ex S θ := by rw [hEx]; exact ⟨hσ, hu⟩
        exact ⟨θ, List.mem_filterMap.2 ⟨E, hE, hn⟩, this.2⟩
    · rintro ⟨θ, hθ, hu⟩
      obtain ⟨E, hE, hn⟩ := List.mem_filterMap.1 hθ
      obtain ⟨-, hEx, -, -⟩ := normEx_some (hfo E hE) (hv' E hE) hn
      have : σ ∈ r.Ex S θ := ⟨hσ, hu⟩
      rw [hEx] at this
      exact ⟨E, hE, this.2⟩

/-- Whether everything one exclusion removes is removed by the other, for
normal exclusions: the first is an instance of the second. -/
def covers (k : Nat) (θ θ' : Binds) : Bool :=
  (List.range k).all fun x => PSubst.apply θ x == (PSubst.apply θ' x).bind (PSubst.apply θ)

theorem covers_iff {S : Sorts} (hS : S.WellFormed) {r : Raw} {θ θ' : Binds}
    (hθ : NormalBinds S r θ) (hθ' : NormalBinds S r θ') :
    covers r.c.length θ θ' = true ↔ r.Ex S θ ⊆ r.Ex S θ' := by
  constructor
  · intro h σ hσ
    refine ⟨hσ.1, (unifies_eqnsOf hθ'.sorted σ).2 fun x => ?_⟩
    have h₁ := (unifies_eqnsOf hθ.sorted σ).1 hσ.2
    by_cases hx : x < r.c.length
    · have e : PSubst.apply θ x = (PSubst.apply θ' x).bind (PSubst.apply θ) := by
        simpa using List.all_eq_true.1 h x (List.mem_range.2 hx)
      rw [h₁ x, e, Term.bind_bind]
      exact Term.bind_congr fun v _ => (h₁ v).symm
    · rw [hθ'.apply_ge (by omega)]; rfl
  · intro h
    rw [covers, List.all_eq_true]
    intro x _
    simpa using hθ.apply_eq_of_subset hS hθ' h x

theorem getD_map_range {α : Type} (f : Nat → α) (k v : Nat) (d : α) :
    ((List.range k).map f).getD v d = if v < k then f v else d := by
  by_cases h : v < k
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-! ## Putting the store together -/

section assemble

variable {S : Sorts} {s : Store} {k : Nat} {cL : List Conj}

/-- A solution of the store is in the sorts that hold of all values. -/
theorem pos_of_sol
    (hcL : ∀ v n, n ∈ cL.getD v ∅ ↔ v < k ∧ n ∈ names S ∧ ∀ σ ∈ s.Sol S, mem S n (σ v) = true)
    (x : Finset Binds) {σ : Nat → GTerm} (hσ : σ ∈ s.Sol S) :
    σ ∈ (Raw.mk s.t cL x).store.Pos S :=
  fun v n hn => ((hcL v n).1 hn).2.2 σ hσ

/-- A store with its variables numbered by first occurrence, given the
sorts that hold of all values of each variable and normal exclusions that
remove the same, none covered by another, is a store determined by its
pattern and what it denotes, with the same solutions. -/
theorem shaped_assemble (hfin : s.Fin k) (hocc : FirstOcc s.t.vars)
    (hvars : ∀ v, v ∈ s.t.vars ↔ v < k) (hne : (s.Sol S).Nonempty) (hlen : cL.length = k)
    (hcL : ∀ v n, n ∈ cL.getD v ∅ ↔ v < k ∧ n ∈ names S ∧ ∀ σ ∈ s.Sol S, mem S n (σ v) = true)
    {Y : List Binds} {Z : Finset Binds} (hY : ∀ θ ∈ Y, NormalBinds S ⟨s.t, cL, ∅⟩ θ)
    (hYiff : ∀ σ ∈ (Raw.mk s.t cL ∅).store.Pos S,
      (∃ E ∈ s.x, Eqns.Unifies σ E) ↔ ∃ θ ∈ Y, Eqns.Unifies σ (eqnsOf θ))
    (hsub : ∀ θ ∈ Z, θ ∈ Y)
    (hcov : ∀ θ ∈ Y, ∃ θ' ∈ Z, Raw.Ex S ⟨s.t, cL, ∅⟩ θ ⊆ Raw.Ex S ⟨s.t, cL, ∅⟩ θ')
    (hanti : ∀ θ ∈ Z, ∀ θ' ∈ Z,
      Raw.Ex S ⟨s.t, cL, ∅⟩ θ ⊆ Raw.Ex S ⟨s.t, cL, ∅⟩ θ' → θ = θ') :
    (Raw.mk s.t cL Z).Shaped S ∧ (Raw.mk s.t cL Z).store.Sol S = s.Sol S := by
  obtain ⟨σ₀, hσ₀⟩ := hne
  have pos₂ : ∀ x, ∀ σ ∈ (Raw.mk s.t cL x).store.Pos S, σ ∈ s.Pos S := by
    intro x σ hσ v n hn
    have hv : v < k := by
      by_contra h
      rw [hfin.cv v (by omega)] at hn; simp at hn
    exact hσ v n ((hcL v n).2
      ⟨hv, subset_names_of_memC (hσ₀.1 v) hn, fun τ hτ => hτ.1 v n hn⟩)
  have hsol : (Raw.store ⟨s.t, cL, Z⟩).Sol S = s.Sol S := by
    ext σ
    constructor
    · rintro ⟨hp, hx⟩
      refine ⟨pos₂ Z σ hp, fun E hE hu => ?_⟩
      obtain ⟨θ, hθ, huθ⟩ := (hYiff σ hp).1 ⟨E, hE, hu⟩
      obtain ⟨θ', hθ', hle⟩ := hcov θ hθ
      exact hx (eqnsOf θ') (Raw.mem_store_x.2 ⟨θ', hθ', rfl⟩) (hle ⟨hp, huθ⟩).2
    · intro hσ
      refine ⟨pos_of_sol hcL Z hσ, fun E hE hu => ?_⟩
      obtain ⟨θ, hθ, rfl⟩ := Raw.mem_store_x.1 hE
      obtain ⟨E', hE', hu'⟩ := (hYiff σ (pos_of_sol hcL ∅ hσ)).2 ⟨θ, hsub θ hθ, hu⟩
      exact hσ.2 E' hE' hu'
  refine ⟨⟨hfin.fo, hocc, fun v => by rw [hvars, hlen], ?_, ?_, ?_⟩, hsol⟩
  · intro v hv n
    rw [hsol]
    show n ∈ cL.getD v ∅ ↔ _
    rw [hcL]
    exact ⟨fun h => h.2, fun h => ⟨hlen ▸ hv, h⟩⟩
  · intro θ hθ
    have h := hY θ (hsub θ hθ)
    exact ⟨h.toPre, h.ne, h.live, h.loose⟩
  · intro θ hθ θ' hθ' hle
    exact hanti θ hθ θ' hθ' hle

/-- A tight store with its variables numbered by first occurrence, given the
sorts that hold of all values of each variable and normal exclusions that
remove the same, none covered by another, is a normal store with
the same solutions. -/
theorem normal_assemble (hfin : s.Fin k) (ht : s.Tight S) (hocc : FirstOcc s.t.vars)
    (hvars : ∀ v, v ∈ s.t.vars ↔ v < k) (hne : (s.Sol S).Nonempty) (hlen : cL.length = k)
    (hcL : ∀ v n, n ∈ cL.getD v ∅ ↔ v < k ∧ n ∈ names S ∧ ∀ σ ∈ s.Sol S, mem S n (σ v) = true)
    {Y : List Binds} {Z : Finset Binds} (hY : ∀ θ ∈ Y, NormalBinds S ⟨s.t, cL, ∅⟩ θ)
    (hYiff : ∀ σ ∈ (Raw.mk s.t cL ∅).store.Pos S,
      (∃ E ∈ s.x, Eqns.Unifies σ E) ↔ ∃ θ ∈ Y, Eqns.Unifies σ (eqnsOf θ))
    (hsub : ∀ θ ∈ Z, θ ∈ Y)
    (hcov : ∀ θ ∈ Y, ∃ θ' ∈ Z, Raw.Ex S ⟨s.t, cL, ∅⟩ θ ⊆ Raw.Ex S ⟨s.t, cL, ∅⟩ θ')
    (hanti : ∀ θ ∈ Z, ∀ θ' ∈ Z,
      Raw.Ex S ⟨s.t, cL, ∅⟩ θ ⊆ Raw.Ex S ⟨s.t, cL, ∅⟩ θ' → θ = θ') :
    (Raw.mk s.t cL Z).Normal S ∧ (Raw.mk s.t cL Z).store.Sol S = s.Sol S := by
  obtain ⟨hsh, hsol⟩ := shaped_assemble hfin hocc hvars hne hlen hcL hY hYiff hsub hcov hanti
  refine ⟨⟨hsh, fun v hv => ?_⟩, hsol⟩
  rw [hsol]
  exact ht v ((hvars v).2 (hlen ▸ hv))

/-- The raw store with the given pattern and sorts and the normal forms of
the exclusions, without the ones another covers. -/
def assembled (S : Sorts) (t : Pat) (cL : List Conj) (X : List (Eqns Nat)) : Raw :=
  ⟨t, cL, (antichain (covers cL.length) (normExs S ⟨t, cL, ∅⟩ X)).toFinset⟩

/-- A store with its variables numbered by first occurrence, with the sorts
that hold of all values of each variable, assembles to a store determined by
its pattern and what it denotes, with the same solutions. -/
theorem assembled_shaped (hS : S.WellFormed) (hfin : s.Fin k)
    (hocc : FirstOcc s.t.vars) (hvars : ∀ v, v ∈ s.t.vars ↔ v < k) (hne : (s.Sol S).Nonempty)
    (hlen : cL.length = k)
    (hcL : ∀ v n, n ∈ cL.getD v ∅ ↔ v < k ∧ n ∈ names S ∧ ∀ σ ∈ s.Sol S, mem S n (σ v) = true) :
    (assembled S s.t cL s.x).Shaped S ∧ (assembled S s.t cL s.x).store.Sol S = s.Sol S := by
  obtain ⟨σ₀, hσ₀⟩ := hne
  obtain ⟨hY, hYiff⟩ := normExs_spec (S := S) ⟨s.t, cL, ∅⟩ s.x hfin.xfo
    (fun E hE p hp v hv => by rw [hlen]; exact hfin.xv E hE p hp v hv)
    (fun E hE => ⟨σ₀, pos_of_sol hcL ∅ hσ₀, hσ₀.2 E hE⟩)
  obtain ⟨hnd, hsub, hcov, hanti⟩ := antichain_spec (covers cL.length)
    (fun θ θ' : Binds => Raw.Ex S ⟨s.t, cL, ∅⟩ θ ⊆ Raw.Ex S ⟨s.t, cL, ∅⟩ θ')
    (fun _ => Set.Subset.rfl) (fun _ _ _ h₁ h₂ => Set.Subset.trans h₁ h₂)
    (normExs S ⟨s.t, cL, ∅⟩ s.x) (fun θ hθ θ' hθ' => covers_iff hS (hY θ hθ) (hY θ' hθ'))
  have hZ : ∀ θ, θ ∈ (antichain (covers cL.length) (normExs S ⟨s.t, cL, ∅⟩ s.x)).toFinset ↔
      θ ∈ antichain (covers cL.length) (normExs S ⟨s.t, cL, ∅⟩ s.x) := fun θ => List.mem_toFinset
  exact shaped_assemble hfin hocc hvars ⟨σ₀, hσ₀⟩ hlen hcL hY hYiff
    (fun θ hθ => hsub θ ((hZ θ).1 hθ))
    (fun θ hθ => by
      obtain ⟨θ', hθ', hle⟩ := hcov θ hθ
      exact ⟨θ', (hZ θ').2 hθ', hle⟩)
    (fun θ hθ θ' hθ' hle => hanti θ ((hZ θ).1 hθ) θ' ((hZ θ').1 hθ') hle)

/-- A tight store with its variables numbered by first occurrence, with the
sorts that hold of all values of each variable, assembles to a normal store
with the same solutions. -/
theorem assembled_normal (hS : S.WellFormed) (hfin : s.Fin k) (ht : s.Tight S)
    (hocc : FirstOcc s.t.vars) (hvars : ∀ v, v ∈ s.t.vars ↔ v < k) (hne : (s.Sol S).Nonempty)
    (hlen : cL.length = k)
    (hcL : ∀ v n, n ∈ cL.getD v ∅ ↔ v < k ∧ n ∈ names S ∧ ∀ σ ∈ s.Sol S, mem S n (σ v) = true) :
    (assembled S s.t cL s.x).Normal S ∧ (assembled S s.t cL s.x).store.Sol S = s.Sol S := by
  obtain ⟨hsh, hsol⟩ := assembled_shaped hS hfin hocc hvars hne hlen hcL
  refine ⟨⟨hsh, fun v hv => ?_⟩, hsol⟩
  rw [hsol]
  exact ht v ((hvars v).2 (show v < k from hlen ▸ hv))

/-- The exclusions an assembled store keeps are listed once each. -/
theorem assembled_nodup (hS : S.WellFormed) (hfin : s.Fin k) (hne : (s.Sol S).Nonempty)
    (hlen : cL.length = k)
    (hcL : ∀ v n, n ∈ cL.getD v ∅ ↔ v < k ∧ n ∈ names S ∧ ∀ σ ∈ s.Sol S, mem S n (σ v) = true) :
    (antichain (covers cL.length) (normExs S ⟨s.t, cL, ∅⟩ s.x)).Nodup := by
  obtain ⟨σ₀, hσ₀⟩ := hne
  obtain ⟨hY, -⟩ := normExs_spec (S := S) ⟨s.t, cL, ∅⟩ s.x hfin.xfo
    (fun E hE p hp v hv => by rw [hlen]; exact hfin.xv E hE p hp v hv)
    (fun E hE => ⟨σ₀, pos_of_sol hcL ∅ hσ₀, hσ₀.2 E hE⟩)
  exact (antichain_spec (covers cL.length)
    (fun θ θ' : Binds => Raw.Ex S ⟨s.t, cL, ∅⟩ θ ⊆ Raw.Ex S ⟨s.t, cL, ∅⟩ θ')
    (fun _ => Set.Subset.rfl) (fun _ _ _ h₁ h₂ => Set.Subset.trans h₁ h₂)
    (normExs S ⟨s.t, cL, ∅⟩ s.x) (fun θ hθ θ' hθ' => covers_iff hS (hY θ hθ) (hY θ' hθ'))).1

end assemble

end Sorts
end RwLog
