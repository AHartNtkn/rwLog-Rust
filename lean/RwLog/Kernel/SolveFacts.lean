/-
# Facts about `solve` that a program for it needs

`solve` (`Kernel/Solve.lean`) is defined by cases on the first equation. A
program that solves equations on shared terms takes the same steps, except
that it drops an equation between two equal terms at once. This file states
each step as an equation about `solveOn E t`, the term `t` with the solution
of `E` applied, and shows that solving commutes with renaming the variables
by an injective function.
-/
import RwLog.Kernel.Solve

namespace RwLog

namespace Term

variable {V W : Type}

theorem vars_rename (f : V → W) (t : Term V) : (t.rename f).vars = t.vars.map f := by
  induction t with
  | var v => rfl
  | sym g => rfl
  | app a b iha ihb =>
    simp only [rename, bind_app, vars, List.map_append] at iha ihb ⊢
    rw [iha, ihb]

theorem mem_vars_rename {f : V → W} (hf : Function.Injective f) {x : V} {t : Term V} :
    f x ∈ (t.rename f).vars ↔ x ∈ t.vars := by
  rw [vars_rename, List.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    exact hf e ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

variable [DecidableEq V] [DecidableEq W]

theorem rename_bind_single {f : V → W} (hf : Function.Injective f) (x : V) (u t : Term V) :
    (t.bind (single x u)).rename f = (t.rename f).bind (single (f x) (u.rename f)) := by
  induction t with
  | var v =>
    by_cases h : v = x
    · subst h; simp [single, rename]
    · have h' : f v ≠ f x := fun e => h (hf e)
      simp [single, rename, h, h']
  | sym g => rfl
  | app a b iha ihb =>
    simp only [rename, bind_app] at iha ihb ⊢
    rw [iha, ihb]

end Term

open Term

variable {V W : Type} [DecidableEq V] [DecidableEq W]

namespace Eqns

/-- Rename the variables of every equation. -/
def ren (f : V → W) (E : Eqns V) : Eqns W := E.map fun p => (p.1.rename f, p.2.rename f)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem ren_nil (f : V → W) : ren f ([] : Eqns V) = [] := rfl

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem ren_cons (f : V → W) (t u : Term V) (E : Eqns V) :
    ren f ((t, u) :: E) = (t.rename f, u.rename f) :: ren f E := rfl

theorem ren_subst {f : V → W} (hf : Function.Injective f) (x : V) (u : Term V) (E : Eqns V) :
    ren f (subst x u E) = subst (f x) (u.rename f) (ren f E) := by
  simp [ren, subst, rename_bind_single hf]

/-- The term `t` with the solution of `E` applied; nothing if `E` has no
solution. -/
def solveOn (E : Eqns V) (t : Term V) : Option (Term V) := (solve E).map fun θ => t.bind θ

@[simp] theorem solveOn_nil (t : Term V) : solveOn [] t = some t := by
  simp [solveOn, solve]

/-- An equation between a term and itself can be dropped. -/
theorem solve_refl (t : Term V) (E : Eqns V) : solve ((t, t) :: E) = solve E := by
  induction t generalizing E with
  | var v => simp [solve]
  | sym g => simp [solve]
  | app a b iha ihb => rw [solve, iha, ihb]

theorem solveOn_refl (p : Term V) (E : Eqns V) (t : Term V) :
    solveOn ((p, p) :: E) t = solveOn E t := by
  simp [solveOn, solve_refl]

theorem solveOn_split (a b c d : Term V) (E : Eqns V) (t : Term V) :
    solveOn ((app a b, app c d) :: E) t = solveOn ((a, c) :: (b, d) :: E) t := by
  simp [solveOn, solve]

theorem solveOn_map_extend (x : V) (u : Term V) (E : Eqns V) (t : Term V) :
    ((solve E).map (extend x u)).map (fun θ => t.bind θ) = solveOn E (t.bind (single x u)) := by
  simp [solveOn, Option.map_map, Function.comp_def, bind_extend]

/-- Eliminating the variable on the left. -/
theorem solveOn_elim_left {x : V} {u : Term V} (hne : u ≠ var x) (hx : x ∉ u.vars)
    (E : Eqns V) (t : Term V) :
    solveOn ((var x, u) :: E) t = solveOn (subst x u E) (t.bind (single x u)) := by
  rw [← solveOn_map_extend]
  cases u with
  | var y =>
    have : x ≠ y := fun e => hne (by rw [e])
    simp [solveOn, solve, this]
  | sym g => simp [solveOn, solve]
  | app a b => simp [solveOn, solve, hx]

/-- Eliminating the variable on the right, when the left is not a variable. -/
theorem solveOn_elim_right {x : V} {u : Term V} (hu : ∀ y, u ≠ var y) (hx : x ∉ u.vars)
    (E : Eqns V) (t : Term V) :
    solveOn ((u, var x) :: E) t = solveOn (subst x u E) (t.bind (single x u)) := by
  rw [← solveOn_map_extend]
  cases u with
  | var y => exact absurd rfl (hu y)
  | sym g => simp [solveOn, solve]
  | app a b => simp [solveOn, solve, hx]

theorem solveOn_occurs_left {x : V} {a b : Term V} (hx : x ∈ (app a b).vars)
    (E : Eqns V) (t : Term V) : solveOn ((var x, app a b) :: E) t = none := by
  simp [solveOn, solve, hx]

theorem solveOn_occurs_right {x : V} {a b : Term V} (hx : x ∈ (app a b).vars)
    (E : Eqns V) (t : Term V) : solveOn ((app a b, var x) :: E) t = none := by
  simp [solveOn, solve, hx]

theorem solveOn_clash {f g : Sym} (h : f ≠ g) (E : Eqns V) (t : Term V) :
    solveOn ((sym f, sym g) :: E) t = none := by
  simp [solveOn, solve, h]

theorem solveOn_sym_app (f : Sym) (a b : Term V) (E : Eqns V) (t : Term V) :
    solveOn ((sym f, app a b) :: E) t = none := by
  simp [solveOn, solve]

theorem solveOn_app_sym (f : Sym) (a b : Term V) (E : Eqns V) (t : Term V) :
    solveOn ((app a b, sym f) :: E) t = none := by
  simp [solveOn, solve]

/-- Solving commutes with renaming the variables by an injective function. -/
theorem solveOn_ren {f : V → W} (hf : Function.Injective f) (E : Eqns V) (t : Term V) :
    solveOn (ren f E) (t.rename f) = (solveOn E t).map (rename f) := by
  fun_induction solve E generalizing t with
  | case1 => simp [rename]
  | case2 x E ih =>
    rw [ren_cons, solveOn_refl, solveOn_refl, ih]
  | case3 x y E hxy ih =>
    have hne : (var y : Term V) ≠ var x := fun e => hxy (by cases e; rfl)
    have hx : x ∉ (var y : Term V).vars := by simpa [Term.vars] using hxy
    have hne' : ((var y : Term V).rename f) ≠ var (f x) := by
      simp only [rename, bind_var, ne_eq, var.injEq]; exact fun e => hxy (hf e).symm
    rw [ren_cons, solveOn_elim_left hne hx]
    show solveOn ((var (f x), (var y : Term V).rename f) :: ren f E) _ = _
    rw [solveOn_elim_left hne' (by rwa [mem_vars_rename hf]), ← ren_subst hf,
      ← rename_bind_single hf, ih]
  | case4 x g E ih =>
    rw [ren_cons, solveOn_elim_left (by simp) (by simp [Term.vars])]
    show solveOn ((var (f x), (sym g : Term V).rename f) :: ren f E) _ = _
    rw [solveOn_elim_left (by simp [rename]) (by simp [rename, Term.vars]), ← ren_subst hf,
      ← rename_bind_single hf, ih]
  | case5 x a b E hx =>
    rw [ren_cons, solveOn_occurs_left hx]
    show solveOn ((var (f x), app (a.rename f) (b.rename f)) :: ren f E) _ = _
    rw [solveOn_occurs_left (a := a.rename f) (b := b.rename f)
      (by exact (mem_vars_rename hf (t := app a b)).2 hx)]
    rfl
  | case6 x a b E hx ih =>
    rw [ren_cons, solveOn_elim_left (by simp) hx]
    show solveOn ((var (f x), (app a b).rename f) :: ren f E) _ = _
    rw [solveOn_elim_left (by simp [rename]) (by rwa [mem_vars_rename hf]), ← ren_subst hf,
      ← rename_bind_single hf, ih]
  | case7 g y E ih =>
    rw [ren_cons, solveOn_elim_right (by simp) (by simp [Term.vars])]
    show solveOn (((sym g : Term V).rename f, var (f y)) :: ren f E) _ = _
    rw [solveOn_elim_right (by simp [rename]) (by simp [rename, Term.vars]), ← ren_subst hf,
      ← rename_bind_single hf, ih]
  | case8 a b y E hy =>
    rw [ren_cons, solveOn_occurs_right hy]
    show solveOn ((app (a.rename f) (b.rename f), var (f y)) :: ren f E) _ = _
    rw [solveOn_occurs_right (a := a.rename f) (b := b.rename f)
      (by exact (mem_vars_rename hf (t := app a b)).2 hy)]
    rfl
  | case9 a b y E hy ih =>
    rw [ren_cons, solveOn_elim_right (by simp) hy]
    show solveOn (((app a b).rename f, var (f y)) :: ren f E) _ = _
    rw [solveOn_elim_right (by simp [rename]) (by rwa [mem_vars_rename hf]), ← ren_subst hf,
      ← rename_bind_single hf, ih]
  | case10 g E ih =>
    rw [ren_cons, solveOn_refl, solveOn_refl, ih]
  | case11 g g' E h =>
    rw [ren_cons, solveOn_clash h]
    show solveOn ((sym g, sym g') :: ren f E) _ = _
    rw [solveOn_clash h]; rfl
  | case12 a b c d E ih =>
    rw [ren_cons, solveOn_split]
    show solveOn ((app (a.rename f) (b.rename f), app (c.rename f) (d.rename f)) :: ren f E) _ = _
    rw [solveOn_split]
    exact ih t
  | case13 g a b E =>
    rw [ren_cons, solveOn_sym_app]
    show solveOn ((sym g, app (a.rename f) (b.rename f)) :: ren f E) _ = _
    rw [solveOn_sym_app]; rfl
  | case14 a b g E =>
    rw [ren_cons, solveOn_app_sym]
    show solveOn ((app (a.rename f) (b.rename f), sym g) :: ren f E) _ = _
    rw [solveOn_app_sym]; rfl

end Eqns

end RwLog
