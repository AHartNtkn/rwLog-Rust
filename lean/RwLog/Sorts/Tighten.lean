/-
# Stores as data, and when one has a solution

`CStore` is a store with the sorts of its variables in a list. `Inv S s` is
decidable and says that the store is first-order, that every variable it
mentions occurs in its pattern, that every variable has more than one value in
its sorts, and that no exclusion always holds. Such a store has a solution
when the sorts are well formed (`Inv.nonempty`): every variable has
infinitely many values, and each exclusion can be avoided by changing one
variable.
-/
import RwLog.Sorts.Settle

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-! ## Avoiding an exclusion -/

theorem ground?_none : ∀ {p : Pat}, ground? p = none → ∃ w, w ∈ p.vars
  | .var v, _ => ⟨v, by simp [Term.vars]⟩
  | .sym f, h => by simp [ground?] at h
  | .app a b, h => by
    cases ha : ground? a with
    | none =>
      obtain ⟨w, hw⟩ := ground?_none ha
      exact ⟨w, by simp [Term.vars, hw]⟩
    | some a' =>
      cases hb : ground? b with
      | none =>
        obtain ⟨w, hw⟩ := ground?_none hb
        exact ⟨w, by simp [Term.vars, hw]⟩
      | some b' => simp [ground?, ha, hb] at h

/-- A variable the solution binds is not in what it is bound to. -/
theorem bound_not_mem {E : Eqns Nat} {θ : Nat → Pat} (hθ : solve E = some θ) {w : Nat}
    (hw : θ w ≠ .var w) : w ∉ (θ w).vars := by
  obtain ⟨hu, hm⟩ := solve_some hθ
  have hidem : (θ w).bind θ = θ w := hm θ hu w
  intro hin
  by_cases hvar : ∃ y, θ w = .var y
  · obtain ⟨y, hy⟩ := hvar
    rw [hy] at hin hw
    simp only [Term.vars, List.mem_singleton] at hin
    exact hw (by rw [hin])
  · exact Term.occurs_ne θ hin (fun y hy => hvar ⟨y, hy⟩) hidem.symm

/-- Changing a variable the solution binds avoids the exclusion. -/
theorem falsify_bound {E : Eqns Nat} {θ : Nat → Pat} (hθ : solve E = some θ) {w : Nat}
    (hw : θ w ≠ .var w) (σ₀ : Nat → GTerm) : ∃ u, ¬ Eqns.Unifies (update σ₀ w u) E := by
  obtain ⟨u, hu⟩ : ∃ u : GTerm, u ≠ (θ w).bind σ₀ :=
    ⟨.app ((θ w).bind σ₀) ((θ w).bind σ₀), fun h => by
      have := congrArg Term.size h; simp [Term.size] at this; omega⟩
  refine ⟨u, fun hun => hu ?_⟩
  have := (solve_some hθ).2 _ hun w
  rw [bind_update_of_not_mem (bound_not_mem hθ hw)] at this
  simpa using this.symm

/-- When the solution binds `v` to a term with a variable, changing that
variable avoids the exclusion. -/
theorem falsify_open {E : Eqns Nat} {θ : Nat → Pat} (hθ : solve E = some θ) {v : Nat}
    (hv : θ v ≠ .var v) (hng : ground? (θ v) = none) (σ₀ : Nat → GTerm) :
    ∃ w ∈ (θ v).vars, w ≠ v ∧ ¬ Eqns.Unifies (update σ₀ w (.app (σ₀ v) (σ₀ v))) E := by
  obtain ⟨w, hw⟩ := ground?_none hng
  have hwv : w ≠ v := fun e => bound_not_mem hθ hv (e ▸ hw)
  refine ⟨w, hw, hwv, fun hun => ?_⟩
  have := (solve_some hθ).2 _ hun v
  have hsz := Term.size_le_bind (update σ₀ w (.app (σ₀ v) (σ₀ v))) hw
  rw [this] at hsz
  simp [update, Ne.symm hwv, Term.size] at hsz
  omega

/-- The equations always hold. -/
def always (E : Eqns Nat) : Bool :=
  match solve E with
  | some θ => E.vars.all fun w => decide (θ w = .var w)
  | none => false

/-- An exclusion that does not always hold is avoided by a substitution that
differs from a given one on a variable of the exclusion. -/
theorem falsify_of_not_always {E : Eqns Nat} (h : always E = false) (σ₀ : Nat → GTerm)
    (H : List Nat) (hH : ∀ w ∈ E.vars, w ∈ H) :
    ∃ τ : Nat → GTerm, (∀ v, v ∉ H → τ v = σ₀ v) ∧ ¬ Eqns.Unifies τ E := by
  unfold always at h
  split at h
  · rename_i θ hθ
    rw [List.all_eq_false] at h
    obtain ⟨w, hw, hne⟩ := h
    rw [decide_eq_true_eq] at hne
    obtain ⟨u, hu⟩ := falsify_bound hθ hne σ₀
    refine ⟨update σ₀ w u, fun v hv => ?_, hu⟩
    have : v ≠ w := fun e => hv (e ▸ hH w hw)
    simp [update, this]
  · rename_i hθ
    exact ⟨σ₀, fun _ _ => rfl, solve_none hθ σ₀⟩

/-! ## Stores as data -/

/-- A store with the sorts of variable `i` at position `i`. -/
structure CStore where
  t : Pat
  c : List Conj
  x : List (Eqns Nat)

namespace CStore

/-- The sorts of a variable. -/
def conj (s : CStore) (v : Nat) : Conj := s.c.getD v ∅

/-- The store it is. -/
def store (s : CStore) : Store := ⟨s.t, s.conj, s.x⟩

theorem conj_of_ge (s : CStore) {v : Nat} (h : s.c.length ≤ v) : s.conj v = ∅ := by
  simp [conj, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

end CStore

/-- The store is first-order, every variable it mentions occurs in its
pattern, every variable has more than one value in its sorts, and no
exclusion always holds. -/
structure Inv (S : Sorts) (s : CStore) : Prop where
  fo : s.t.firstOrder = true
  tv : ∀ v ∈ s.t.vars, v < s.c.length
  xfo : ∀ E ∈ s.x, ∀ p ∈ E, p.1.firstOrder = true ∧ p.2.firstOrder = true
  xv : ∀ E ∈ s.x, ∀ v ∈ E.vars, v ∈ s.t.vars
  cs : ∀ v, v < s.c.length → v ∉ s.t.vars → s.conj v = ∅
  many : ∀ v ∈ s.t.vars, count S (s.conj v) = .many
  open_ : ∀ E ∈ s.x, always E = false

instance (S : Sorts) (s : CStore) : Decidable (Inv S s) :=
  decidable_of_iff
    (s.t.firstOrder = true ∧ (∀ v ∈ s.t.vars, v < s.c.length) ∧
      (∀ E ∈ s.x, ∀ p ∈ E, p.1.firstOrder = true ∧ p.2.firstOrder = true) ∧
      (∀ E ∈ s.x, ∀ v ∈ E.vars, v ∈ s.t.vars) ∧
      (∀ v, v < s.c.length → v ∉ s.t.vars → s.conj v = ∅) ∧
      (∀ v ∈ s.t.vars, count S (s.conj v) = .many) ∧ ∀ E ∈ s.x, always E = false)
    ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
      fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

namespace Inv

variable {s : CStore}

theorem fin (h : Inv S s) : s.store.Fin s.c.length where
  fo := h.fo
  tv := h.tv
  cv _ hv := s.conj_of_ge hv
  xfo := h.xfo
  xv E hE p hp v hv := h.tv v (h.xv E hE v (List.mem_flatMap.2 ⟨p, hp, hv⟩))

theorem full (h : Inv S s) : s.store.Full where
  cs v hv := by
    by_cases hl : v < s.c.length
    · exact h.cs v hl hv
    · exact s.conj_of_ge (Nat.le_of_not_lt hl)
  xs E hE p hp v hv := h.xv E hE v (List.mem_flatMap.2 ⟨p, hp, hv⟩)

/-- Every variable has infinitely many values in its sorts. -/
theorem infinite (hS : S.WellFormed) (h : Inv S s) (v : Nat) :
    {g | MemC S (s.conj v) g}.Infinite := by
  by_cases hv : v ∈ s.t.vars
  · exact count_many_infinite hS (h.many v hv)
  · have : s.conj v = ∅ := h.full.cs v hv
    rw [this]
    exact restOK_infinite fun n hn => by simp at hn

/-- The store has a solution. -/
theorem sol (hS : S.WellFormed) (h : Inv S s) : (s.store.Sol S).Nonempty := by
  obtain ⟨σ, hσ, -⟩ := s.store.rich (S := S) (List.range s.c.length)
    (fun v _ => h.infinite hS v) (fun _ => .sym "")
    (fun v hv => by
      have : s.c.length ≤ v := by simpa using hv
      show MemC S (s.conj v) _
      rw [s.conj_of_ge this]; intro n hn; simp at hn)
    []
    (fun E hE => falsify_of_not_always (h.open_ E hE) _ _ fun w hw =>
      List.mem_range.2 (h.tv w (h.xv E hE w hw)))
    (by simp)
  exact ⟨σ, hσ⟩

theorem nonempty (hS : S.WellFormed) (h : Inv S s) : (s.store.Den S).Nonempty := by
  obtain ⟨σ, hσ⟩ := h.sol hS
  exact ⟨_, σ, hσ, rfl⟩

end Inv

end Sorts
end RwLog
