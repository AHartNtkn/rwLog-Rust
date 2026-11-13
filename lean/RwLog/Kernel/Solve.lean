/-
# Solving term equations

`solve E` finds a most general substitution making both sides of every
equation in `E` equal, or reports that none exists. It is the engine behind
two-sided matching (`RwLog.Kernel.Match`): matching always calls it on two
terms whose variables live in disjoint namespaces (`V₁ ⊕ V₂`), so the two
sides never share a variable. It is not exposed as an operation on terms with
shared variables.
-/
import RwLog.Trusted.Syntax
import Mathlib.Data.Finset.Card
import Mathlib.Order.Prod.Lex.Basic

namespace RwLog

namespace Term

variable {V W : Type}

/-- Replace one variable. -/
def single [DecidableEq V] (x : V) (u : Term V) : V → Term V :=
  fun v => if v = x then u else var v

theorem size_pos (t : Term V) : 0 < t.size := by
  cases t <;> simp [size]

/-- A variable's image is no larger than the image of a term containing it. -/
theorem size_le_bind (σ : V → Term W) {x : V} {t : Term V} (h : x ∈ t.vars) :
    (σ x).size ≤ (t.bind σ).size := by
  induction t with
  | var v => simp [vars] at h; subst h; simp
  | sym f => simp [vars] at h
  | app a b iha ihb =>
    simp only [vars, List.mem_append] at h
    simp only [bind_app, size]
    rcases h with h | h
    · have := iha h; omega
    · have := ihb h; omega

/-- If `x` occurs strictly inside `t`, then no substitution can make `x` and
`t` equal (the occurs check). -/
theorem occurs_ne (σ : V → Term W) {x : V} {t : Term V} (h : x ∈ t.vars)
    (hne : ∀ y, t ≠ var y) : σ x ≠ t.bind σ := by
  intro heq
  cases t with
  | var y => exact hne y rfl
  | sym f => simp [vars] at h
  | app a b =>
    have h1 := congrArg size heq
    simp only [vars, List.mem_append] at h
    simp only [bind_app, size] at h1
    rcases h with h | h
    · have := size_le_bind σ h; have := size_pos (b.bind σ); omega
    · have := size_le_bind σ h; have := size_pos (a.bind σ); omega

variable [DecidableEq V]

theorem bind_single_of_not_mem {x : V} {u t : Term V} (h : x ∉ t.vars) :
    t.bind (single x u) = t := by
  conv_rhs => rw [← bind_var_id t]
  apply bind_congr
  intro v hv
  have : v ≠ x := fun e => h (e ▸ hv)
  simp [single, this]

theorem vars_bind_single {x : V} {u t : Term V} :
    ∀ v ∈ (t.bind (single x u)).vars, (v ∈ t.vars ∧ v ≠ x) ∨ v ∈ u.vars := by
  induction t with
  | var w =>
    intro v hv
    by_cases hw : w = x
    · subst hw; simp [single] at hv; exact Or.inr hv
    · simp [single, hw, vars] at hv; subst hv; exact Or.inl ⟨by simp [vars], hw⟩
  | sym f => intro v hv; simp [vars] at hv
  | app a b iha ihb =>
    intro v hv
    simp only [bind_app, vars, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · rcases iha v hv with h | h
      · exact Or.inl ⟨Or.inl h.1, h.2⟩
      · exact Or.inr h
    · rcases ihb v hv with h | h
      · exact Or.inl ⟨Or.inr h.1, h.2⟩
      · exact Or.inr h

end Term

open Term

variable {V W : Type} [DecidableEq V]

/-- Equations between terms. -/
abbrev Eqns (V : Type) := List (Term V × Term V)

namespace Eqns

def vars (E : Eqns V) : List V := E.flatMap fun p => p.1.vars ++ p.2.vars

def varset (E : Eqns V) : Finset V := (vars E).toFinset

def size (E : Eqns V) : Nat := (E.map fun p => p.1.size + p.2.size).sum

/-- `σ` makes both sides of every equation equal. -/
def Unifies (σ : V → Term W) (E : Eqns V) : Prop :=
  ∀ p ∈ E, p.1.bind σ = p.2.bind σ

def subst (x : V) (u : Term V) (E : Eqns V) : Eqns V :=
  E.map fun p => (p.1.bind (single x u), p.2.bind (single x u))

omit [DecidableEq V] in
@[simp] theorem vars_cons (t u : Term V) (E : Eqns V) :
    vars ((t, u) :: E) = t.vars ++ u.vars ++ vars E := by
  simp [vars]

omit [DecidableEq V] in
@[simp] theorem size_cons (t u : Term V) (E : Eqns V) :
    size ((t, u) :: E) = t.size + u.size + size E := by
  simp [size]

omit [DecidableEq V] in
theorem unifies_cons {σ : V → Term W} {t u : Term V} {E : Eqns V} :
    Unifies σ ((t, u) :: E) ↔ t.bind σ = u.bind σ ∧ Unifies σ E := by
  simp [Unifies]

/-- Eliminating `x` (which does not occur in `u`) removes `x` from the
variables. -/
theorem varset_subst_ssubset {x : V} {u : Term V} {E : Eqns V} {t : Term V}
    (hx : x ∉ u.vars)
    (hxt : x ∈ t.vars) :
    varset (subst x u E) ⊂ varset ((t, u) :: E) := by
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, by simp [varset, hxt], ?_⟩
    simp only [varset, List.mem_toFinset, vars, subst, List.flatMap_map,
      List.mem_flatMap, List.mem_append, not_exists, not_and]
    intro p _ hp
    rcases hp with hp | hp
    · rcases vars_bind_single x hp with h | h
      · exact h.2 rfl
      · exact hx h
    · rcases vars_bind_single x hp with h | h
      · exact h.2 rfl
      · exact hx h
  · intro v hv
    simp only [varset, List.mem_toFinset, vars, subst, List.flatMap_map,
      List.mem_flatMap, List.mem_append] at hv
    obtain ⟨p, hp, hv⟩ := hv
    simp only [varset, List.mem_toFinset, vars_cons, List.mem_append]
    have key : ∀ w ∈ (p.1.bind (single x u)).vars ++ (p.2.bind (single x u)).vars,
        w ∈ t.vars ∨ w ∈ u.vars ∨ w ∈ vars E := by
      intro w hw
      simp only [List.mem_append] at hw
      rcases hw with hw | hw <;> rcases vars_bind_single w hw with h | h
      · exact Or.inr (Or.inr (by simp only [vars, List.mem_flatMap, List.mem_append]; exact ⟨p, hp, Or.inl h.1⟩))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [vars, List.mem_flatMap, List.mem_append]; exact ⟨p, hp, Or.inr h.1⟩))
      · exact Or.inr (Or.inl h)
    rcases key v (by simpa using hv) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem varset_swap (t u : Term V) (E : Eqns V) :
    varset ((t, u) :: E) = varset ((u, t) :: E) := by
  ext v; simp only [varset, List.mem_toFinset, vars_cons, List.mem_append]; tauto

theorem varset_subst_ssubset' {x : V} {u : Term V} {E : Eqns V} {t : Term V}
    (hx : x ∉ u.vars) (hxt : x ∈ t.vars) :
    varset (subst x u E) ⊂ varset ((u, t) :: E) := by
  rw [← varset_swap]; exact varset_subst_ssubset hx hxt

end Eqns

open Eqns

theorem lex_left {a a' b b' : Nat} (h : a < a') : Prod.Lex (· < ·) (· < ·) (a, b) (a', b') :=
  Prod.Lex.left _ _ h

theorem lex_of_le {a a' b b' : Nat} (h : a ≤ a') (hb : b < b') :
    Prod.Lex (· < ·) (· < ·) (a, b) (a', b') := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ hb

theorem varset_tail_subset (t u : Term V) (E : Eqns V) :
    (varset E).card ≤ (varset ((t, u) :: E)).card := by
  apply Finset.card_le_card
  intro v hv
  simp only [varset, List.mem_toFinset, vars_cons, List.mem_append] at hv ⊢
  exact Or.inr hv

theorem varset_app_eq (a b c d : Term V) (E : Eqns V) :
    (varset ((a, c) :: (b, d) :: E)).card ≤ (varset ((Term.app a b, Term.app c d) :: E)).card := by
  apply Finset.card_le_card
  intro v hv
  simp only [varset, List.mem_toFinset, vars_cons, List.mem_append, Term.vars] at hv ⊢
  tauto

/-- Extend a solution of the eliminated system to one of the original. -/
def extend (x : V) (u : Term V) (θ : V → Term V) : V → Term V :=
  fun v => (single x u v).bind θ

/-- Most general solution of a system of equations, with occurs check. -/
def solve : Eqns V → Option (V → Term V)
  | [] => some Term.var
  | (.var x, .var y) :: E =>
    if x = y then solve E else (solve (subst x (.var y) E)).map (extend x (.var y))
  | (.var x, .sym f) :: E => (solve (subst x (.sym f) E)).map (extend x (.sym f))
  | (.var x, .app a b) :: E =>
    if x ∈ (Term.app a b).vars then none
    else (solve (subst x (.app a b) E)).map (extend x (.app a b))
  | (.sym f, .var y) :: E => (solve (subst y (.sym f) E)).map (extend y (.sym f))
  | (.app a b, .var y) :: E =>
    if y ∈ (Term.app a b).vars then none
    else (solve (subst y (.app a b) E)).map (extend y (.app a b))
  | (.sym f, .sym g) :: E => if f = g then solve E else none
  | (.app a b, .app c d) :: E => solve ((a, c) :: (b, d) :: E)
  | (.sym _, .app _ _) :: _ => none
  | (.app _ _, .sym _) :: _ => none
termination_by E => ((varset E).card, size E)
decreasing_by
  all_goals first
    | (apply lex_of_le (varset_tail_subset _ _ _); simp [Term.size])
    | (apply lex_of_le (varset_app_eq _ _ _ _ _); simp [Term.size]; omega)
    | (apply lex_left; apply Finset.card_lt_card
       first
        | (apply varset_subst_ssubset <;> simp_all [Term.vars])
        | (apply varset_subst_ssubset' <;> simp_all [Term.vars]))

end RwLog

namespace RwLog

open Term Eqns

variable {V W : Type} [DecidableEq V]

theorem single_bind_of_eq {x : V} {u : Term V} {σ : V → Term W} (h : σ x = u.bind σ) (v : V) :
    (single x u v).bind σ = σ v := by
  by_cases hv : v = x
  · subst hv; simp [single, h]
  · simp [single, hv]

theorem bind_single_bind {x : V} {u : Term V} {σ : V → Term W} (h : σ x = u.bind σ)
    (t : Term V) : (t.bind (single x u)).bind σ = t.bind σ := by
  rw [bind_bind]; exact bind_congr fun v _ => single_bind_of_eq h v

theorem unifies_subst_iff {x : V} {u : Term V} {σ : V → Term W} (h : σ x = u.bind σ)
    (E : Eqns V) : Unifies σ (subst x u E) ↔ Unifies σ E := by
  simp only [Unifies, subst, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, bind_single_bind h]

theorem bind_extend (x : V) (u : Term V) (θ : V → Term V) (t : Term V) :
    t.bind (extend x u θ) = (t.bind (single x u)).bind θ := by
  rw [bind_bind]; rfl

/-- What `solve` guarantees: a solution is a unifier through which every
unifier factors; failure means there is no unifier. -/
def SolveSpec (E : Eqns V) : Prop :=
  match solve E with
  | some θ => Unifies θ E ∧
      ∀ {W : Type} (σ : V → Term W), Unifies σ E → ∀ v, (θ v).bind σ = σ v
  | none => ∀ {W : Type} (σ : V → Term W), ¬ Unifies σ E

theorem spec_elim {L E : Eqns V} {x : V} {u : Term V} (hx : x ∉ u.vars)
    (ih : SolveSpec (subst x u E))
    (hd : ∀ {W : Type} (σ : V → Term W), Unifies σ L ↔ σ x = u.bind σ ∧ Unifies σ E)
    (hs : solve L = (solve (subst x u E)).map (extend x u)) : SolveSpec L := by
  unfold SolveSpec at ih ⊢
  rw [hs]
  cases h : solve (subst x u E) with
  | none =>
    rw [h] at ih
    intro W σ hσ
    obtain ⟨h1, h2⟩ := (hd σ).1 hσ
    exact ih σ ((unifies_subst_iff h1 E).2 h2)
  | some θ =>
    rw [h] at ih
    obtain ⟨hu, hm⟩ := ih
    refine ⟨(hd _).2 ⟨?_, ?_⟩, ?_⟩
    · simp [extend, single, bind_extend, bind_single_of_not_mem hx]
    · intro p hp
      rw [bind_extend, bind_extend]
      exact hu _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    · intro W σ hσ v
      obtain ⟨h1, h2⟩ := (hd σ).1 hσ
      have := hm σ ((unifies_subst_iff h1 E).2 h2)
      simp only [extend, bind_bind]
      rw [show (fun w => (θ w).bind σ) = σ from funext this]
      exact single_bind_of_eq h1 v

theorem solve_spec (E : Eqns V) : SolveSpec E := by
  induction E using solve.induct with
  | case1 =>
    unfold SolveSpec; simp only [solve]
    exact ⟨fun _ h => by simp at h, fun σ _ v => rfl⟩
  | case2 y E ih =>
    unfold SolveSpec at ih ⊢; simp only [solve, ite_true]
    cases h : solve E with
    | none => rw [h] at ih; intro W σ hσ; exact ih σ (unifies_cons.1 hσ).2
    | some θ =>
      rw [h] at ih
      exact ⟨unifies_cons.2 ⟨rfl, ih.1⟩, fun σ hσ => ih.2 σ (unifies_cons.1 hσ).2⟩
  | case3 x y E hxy ih =>
    refine spec_elim (by simp [Term.vars, hxy]) ih (fun σ => by simp [unifies_cons]) ?_
    simp [solve, hxy]
  | case4 x f E ih =>
    exact spec_elim (by simp [Term.vars]) ih (fun σ => by simp [unifies_cons]) (by simp [solve])
  | case5 x a b E hx =>
    unfold SolveSpec; simp only [solve, hx, ite_true]
    intro W σ hσ
    exact occurs_ne σ hx (fun _ h => by cases h) (unifies_cons.1 hσ).1
  | case6 x a b E hx ih =>
    exact spec_elim hx ih (fun σ => by simp [unifies_cons]) (by simp [solve, hx])
  | case7 f y E ih =>
    exact spec_elim (by simp [Term.vars]) ih (fun σ => by simp [unifies_cons, eq_comm])
      (by simp [solve])
  | case8 a b y E hy =>
    unfold SolveSpec; simp only [solve, hy, ite_true]
    intro W σ hσ
    exact occurs_ne σ hy (fun _ h => by cases h) (unifies_cons.1 hσ).1.symm
  | case9 a b y E hy ih =>
    exact spec_elim hy ih (fun σ => by simp [unifies_cons, eq_comm]) (by simp [solve, hy])
  | case10 g E ih =>
    unfold SolveSpec at ih ⊢; simp only [solve, ite_true]
    cases h : solve E with
    | none => rw [h] at ih; intro W σ hσ; exact ih σ (unifies_cons.1 hσ).2
    | some θ =>
      rw [h] at ih
      exact ⟨unifies_cons.2 ⟨rfl, ih.1⟩, fun σ hσ => ih.2 σ (unifies_cons.1 hσ).2⟩
  | case11 f g E hfg =>
    unfold SolveSpec; simp only [solve, hfg, ite_false]
    intro W σ hσ
    have := (unifies_cons.1 hσ).1
    simp at this; exact hfg this
  | case12 a b c d E ih =>
    unfold SolveSpec at ih ⊢; simp only [solve]
    have key : ∀ {W : Type} (σ : V → Term W),
        Unifies σ ((a, c) :: (b, d) :: E) ↔ Unifies σ ((a.app b, c.app d) :: E) := by
      intro W σ; simp [unifies_cons, and_assoc]
    cases h : solve ((a, c) :: (b, d) :: E) with
    | none => rw [h] at ih; intro W σ hσ; exact ih σ ((key σ).2 hσ)
    | some θ =>
      rw [h] at ih
      exact ⟨(key θ).1 ih.1, fun σ hσ => ih.2 σ ((key σ).2 hσ)⟩
  | case13 f a b E =>
    unfold SolveSpec; simp only [solve]
    intro W σ hσ; have := (unifies_cons.1 hσ).1; simp at this
  | case14 a b f E =>
    unfold SolveSpec; simp only [solve]
    intro W σ hσ; have := (unifies_cons.1 hσ).1; simp at this

theorem solve_some {E : Eqns V} {θ : V → Term V} (h : solve E = some θ) :
    Unifies θ E ∧ ∀ {W : Type} (σ : V → Term W), Unifies σ E → ∀ v, (θ v).bind σ = σ v := by
  have := solve_spec E; unfold SolveSpec at this; rw [h] at this; exact this

theorem solve_none {E : Eqns V} (h : solve E = none) {W : Type} (σ : V → Term W) :
    ¬ Unifies σ E := by
  have := solve_spec E; unfold SolveSpec at this; rw [h] at this; exact this σ

end RwLog
