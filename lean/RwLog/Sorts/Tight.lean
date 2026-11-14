/-
# The least pattern around a store

A store is *tight* when every variable of its pattern takes values with two
different head symbols among its solutions. If a variable takes values with
one head symbol only, `(f _ … _)`, the pattern can be extended there: the
variable is replaced by `(f $y₁ … $yₙ)` with new variables, which take the
sorts the sorts of the old one give to the arguments (`expStore`,
`expStore_fwd`, `expStore_bwd`). The pattern then has more symbols, and it
never has more than a term the store denotes, so this ends; `tighten`
(`Loop.lean`) is the loop.
-/
import RwLog.Sorts.Store
import RwLog.Sorts.FO

namespace RwLog
namespace Sorts

open Function

/-- The store is first-order and all its variables are below `N`. -/
structure Store.Fin (s : Store) (N : Nat) : Prop where
  fo : s.t.firstOrder = true
  tv : ∀ v ∈ s.t.vars, v < N
  cv : ∀ v, N ≤ v → s.c v = ∅
  xfo : ∀ E ∈ s.x, E.FO
  xv : ∀ E ∈ s.x, ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, v < N

/-- Every variable the store says anything about occurs in its pattern. -/
structure Store.Full (s : Store) : Prop where
  cs : ∀ v, v ∉ s.t.vars → s.c v = ∅
  xs : ∀ E ∈ s.x, ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, v ∈ s.t.vars

/-- Every variable of the pattern takes values with two different head
symbols. -/
def Store.Tight (S : Sorts) (s : Store) : Prop :=
  ∀ v ∈ s.t.vars, ∃ σ ∈ s.Sol S, ∃ σ' ∈ s.Sol S, (σ v).key ≠ (σ' v).key

theorem key_eq_mk {g : GTerm} {f : Sym} {n : Nat} (h : g.key = some (f, n)) :
    ∃ gs, g = Term.mk f gs ∧ gs.length = n := by
  obtain ⟨f', ts, rfl, -⟩ := exists_mk g
  simp only [Term.key, Term.spine_mk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨ts, rfl, rfl⟩

/-- `(f $N … $(N+n-1))`. -/
def expVar (N n : Nat) (f : Sym) : Pat := Term.mk f ((List.range n).map fun i => .var (N + i))

theorem mem_expVar_vars {N n : Nat} {f : Sym} {w : Nat} :
    w ∈ (expVar N n f).vars ↔ N ≤ w ∧ w < N + n := by
  simp only [expVar, Term.vars_mk, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, hw⟩
    simp only [Term.vars, List.mem_singleton] at hw
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, ⟨w - N, by omega, rfl⟩, by simp only [Term.vars, List.mem_singleton]; omega⟩

theorem expVar_fo (N n : Nat) (f : Sym) : (expVar N n f).firstOrder = true :=
  Term.fo_mk _ _ fun a ha => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha; rfl

theorem expVar_bind (N n : Nat) (f : Sym) (σ : Nat → GTerm) :
    (expVar N n f).bind σ = Term.mk f ((List.range n).map fun i => σ (N + i)) := by
  simp [expVar, Term.bind_mk, List.map_map, Function.comp_def]

/-- The store with the variable `v` replaced by `(f $N … $(N+n-1))`. -/
def expStore (S : Sorts) (s : Store) (N v : Nat) (f : Sym) (n : Nat) : Store :=
  ⟨s.t.bind (Term.single v (expVar N n f)),
    fun w => if w = v then ∅ else if N ≤ w ∧ w < N + n then kidC S (s.c v) f n (w - N) else s.c w,
    s.x.map (Eqns.subst v (expVar N n f))⟩

section expand

variable {S : Sorts} {s : Store} {N v : Nat} {f : Sym} {n : Nat}

theorem expStore_fwd (hfin : s.Fin N) (hv : v < N) {σ : Nat → GTerm} (hσ : σ ∈ s.Sol S)
    {gs : List GTerm} (hσv : σ v = Term.mk f gs) (hlen : gs.length = n) :
    ∃ σ' ∈ (expStore S s N v f n).Sol S, (expStore S s N v f n).t.bind σ' = s.t.bind σ := by
  subst hlen
  let σ' : Nat → GTerm := fun w =>
    if N ≤ w ∧ w < N + gs.length then gs.getD (w - N) (.sym "") else σ w
  have hlow : ∀ w, w < N → σ' w = σ w := fun w hw => ite_eq_right (by omega)
  have hu : (expVar N gs.length f).bind σ' = Term.mk f gs := by
    rw [expVar_bind]
    congr 1
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    have hi : i < gs.length := h₂
    show (if N ≤ N + i ∧ N + i < N + gs.length then gs.getD (N + i - N) (.sym "") else σ (N + i)) = _
    rw [ite_eq_left (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  have hv' : σ' v = (expVar N gs.length f).bind σ' := by rw [hlow v hv, hσv, hu]
  have hb : ∀ q : Pat, (∀ w ∈ q.vars, w < N) →
      (q.bind (Term.single v (expVar N gs.length f))).bind σ' = q.bind σ := by
    intro q hq
    rw [bind_single_bind hv']
    exact Term.bind_congr fun w hw => hlow w (hq w hw)
  refine ⟨σ', ⟨?_, ?_⟩, hb s.t hfin.tv⟩
  · intro w
    show MemC S (if w = v then ∅ else if N ≤ w ∧ w < N + gs.length
      then kidC S (s.c v) f gs.length (w - N) else s.c w) (σ' w)
    by_cases hwv : w = v
    · rw [ite_eq_left hwv]; intro m hm; simp at hm
    · rw [ite_eq_right hwv]
      by_cases hr : N ≤ w ∧ w < N + gs.length
      · rw [ite_eq_left hr]
        have hm : MemC S (s.c v) (Term.mk f gs) := hσv ▸ hσ.1 v
        have := (memC_mk.1 hm).2 (w - N) (by omega)
        show MemC S _ (if N ≤ w ∧ w < N + gs.length then gs.getD (w - N) (.sym "") else σ w)
        rw [ite_eq_left hr]
        simpa [List.getD_eq_getElem?_getD, show w - N < gs.length by omega] using this
      · rw [ite_eq_right hr]
        show MemC S _ (if N ≤ w ∧ w < N + gs.length then gs.getD (w - N) (.sym "") else σ w)
        rw [ite_eq_right hr]; exact hσ.1 w
  · intro E' hE' hu'
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    refine hσ.2 E hE (unifies_congr (fun p hp w hw => hlow w (hfin.xv E hE p hp w hw)) ?_)
    exact (unifies_subst_iff hv' E).1 hu'

theorem expStore_bwd (hfin : s.Fin N) (hv : v < N) (hacc : Accepts S (s.c v) f n)
    {σ' : Nat → GTerm} (hσ' : σ' ∈ (expStore S s N v f n).Sol S) :
    ∃ σ ∈ s.Sol S, s.t.bind σ = (expStore S s N v f n).t.bind σ' := by
  let σ : Nat → GTerm := fun w => (Term.single v (expVar N n f) w).bind σ'
  have hb : ∀ q : Pat, q.bind σ = (q.bind (Term.single v (expVar N n f))).bind σ' :=
    fun q => (Term.bind_bind _ _ q).symm
  have hσw : ∀ w, w ≠ v → σ w = σ' w := by
    intro w hw; simp [σ, Term.single, hw]
  have hσv : σ v = (expVar N n f).bind σ' := by simp [σ, Term.single]
  have hc : ∀ w, MemC S (if w = v then ∅ else if N ≤ w ∧ w < N + n
      then kidC S (s.c v) f n (w - N) else s.c w) (σ' w) := hσ'.1
  refine ⟨σ, ⟨?_, ?_⟩, hb s.t⟩
  · intro w
    by_cases hwv : w = v
    · subst hwv
      show MemC S (s.c w) (σ w)
      rw [hσv, expVar_bind]
      refine memC_mk.2 ⟨by simpa using hacc, ?_⟩
      intro i hi
      have hi' : i < n := by simpa using hi
      have := hc (N + i)
      rw [ite_eq_right (by omega), ite_eq_left (by omega)] at this
      simpa [hi'] using this
    · show MemC S (s.c w) (σ w)
      rw [hσw w hwv]
      have := hc w
      rw [ite_eq_right hwv] at this
      by_cases hr : N ≤ w ∧ w < N + n
      · rw [hfin.cv w hr.1]; intro m hm; simp at hm
      · rwa [ite_eq_right hr] at this
  · intro E hE hu
    refine hσ'.2 _ (List.mem_map.2 ⟨E, hE, rfl⟩) ?_
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    show (q.1.bind _).bind σ' = (q.2.bind _).bind σ'
    rw [← hb, ← hb]; exact hu q hq

/-- Replacing a variable of the pattern keeps the store first-order, with its
variables below the new bound. -/
theorem expStore_fin (hfin : s.Fin N) (hv : v ∈ s.t.vars) :
    (expStore S s N v f n).Fin (N + n) := by
  have hvN := hfin.tv v hv
  have hsfo : ∀ w, (Term.single v (expVar N n f) w).firstOrder = true := by
    intro w; unfold Term.single; split
    · exact expVar_fo N n f
    · rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Term.fo_bind hfin.fo fun w _ => hsfo w
  · intro w hw
    rcases Term.vars_bind_single w hw with ⟨hw', -⟩ | hw'
    · have := hfin.tv w hw'; omega
    · exact (mem_expVar_vars.1 hw').2
  · intro w hw
    show (if w = v then ∅ else if N ≤ w ∧ w < N + n then kidC S (s.c v) f n (w - N) else s.c w) = ∅
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hfin.cv w (by omega)
  · intro E' hE'
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    exact Eqns.fo_subst (hfin.xfo E hE) (expVar_fo N n f)
  · intro E' hE' p hp w hw
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have h₀ : ∀ u : Pat, (∀ z ∈ u.vars, z < N) →
        w ∈ (u.bind (Term.single v (expVar N n f))).vars → w < N + n := by
      intro u hu hwu
      rcases Term.vars_bind_single w hwu with ⟨hw', -⟩ | hw'
      · have := hu w hw'; omega
      · exact (mem_expVar_vars.1 hw').2
    rcases List.mem_append.1 hw with hw | hw
    · exact h₀ q.1 (fun z hz => hfin.xv E hE q hq z (List.mem_append_left _ hz)) hw
    · exact h₀ q.2 (fun z hz => hfin.xv E hE q hq z (List.mem_append_right _ hz)) hw

/-- Replacing a variable of the pattern keeps every variable in the pattern. -/
theorem expStore_full (hfull : s.Full) (hv : v ∈ s.t.vars) :
    (expStore S s N v f n).Full := by
  have hin : ∀ w, N ≤ w ∧ w < N + n → w ∈ (s.t.bind (Term.single v (expVar N n f))).vars := by
    intro w hw
    exact Term.vars_sub_bind hv w (by simp only [Term.single, ite_true]; exact mem_expVar_vars.2 hw)
  have hkeep : ∀ w, w ∈ s.t.vars → w ≠ v →
      w ∈ (s.t.bind (Term.single v (expVar N n f))).vars := by
    intro w hw hwv
    exact Term.vars_sub_bind hw w (by simp [Term.single, hwv, Term.vars])
  refine ⟨?_, ?_⟩
  · intro w hw
    show (if w = v then ∅ else if N ≤ w ∧ w < N + n then kidC S (s.c v) f n (w - N) else s.c w) = ∅
    by_cases hwv : w = v
    · rw [ite_eq_left hwv]
    · rw [ite_eq_right hwv]
      by_cases hr : N ≤ w ∧ w < N + n
      · exact absurd (hin w hr) hw
      · rw [ite_eq_right hr]
        exact hfull.cs w fun hwt => hw (hkeep w hwt hwv)
  · intro E' hE' p hp w hw
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have h₀ : ∀ u : Pat, (∀ z ∈ u.vars, z ∈ s.t.vars) →
        w ∈ (u.bind (Term.single v (expVar N n f))).vars →
        w ∈ (s.t.bind (Term.single v (expVar N n f))).vars := by
      intro u hu hwu
      rcases Term.vars_bind_single w hwu with ⟨hw', hwv⟩ | hw'
      · exact hkeep w (hu w hw') hwv
      · exact hin w (mem_expVar_vars.1 hw')
    rcases List.mem_append.1 hw with hw | hw
    · exact h₀ q.1 (fun z hz => hfull.xs E hE q hq z (List.mem_append_left _ hz)) hw
    · exact h₀ q.2 (fun z hz => hfull.xs E hE q hq z (List.mem_append_right _ hz)) hw

end expand

end Sorts
end RwLog
