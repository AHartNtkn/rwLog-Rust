/-
# First-order terms under substitution and unification

A term is first-order when no variable is applied to an argument. Substituting
first-order terms into a first-order term gives one, a ground term is one, and
the most general unifier of first-order equations sends every variable to
one.
-/
import RwLog.Kernel.Solve
import RwLog.Kernel.TermFacts

namespace RwLog

namespace Term

variable {V W : Type}

theorem fo_app {t u : Term V} (h : (app t u).firstOrder = true) :
    t.firstOrder = true ∧ u.firstOrder = true ∧ ∀ x, t ≠ var x := by
  cases t with
  | var x => simp [firstOrder] at h
  | sym f => exact ⟨rfl, by simpa [firstOrder] using h, by simp⟩
  | app a b =>
    simp only [firstOrder, Bool.and_eq_true] at h
    exact ⟨h.1, h.2, by simp⟩

theorem fo_app_mk {t u : Term V} (ht : t.firstOrder = true) (hu : u.firstOrder = true)
    (hv : ∀ x, t ≠ var x) : (app t u).firstOrder = true := by
  cases t with
  | var x => exact absurd rfl (hv x)
  | sym f => simpa [firstOrder] using hu
  | app a b => simp only [firstOrder, Bool.and_eq_true]; exact ⟨ht, hu⟩

theorem fo_bind {σ : V → Term W} : ∀ {t : Term V}, t.firstOrder = true →
    (∀ v ∈ t.vars, (σ v).firstOrder = true) → (t.bind σ).firstOrder = true
  | var v, _, h => h v (by simp [vars])
  | sym _, _, _ => rfl
  | app t u, hfo, h => by
    obtain ⟨ht, hu, hnv⟩ := fo_app hfo
    refine fo_app_mk (fo_bind ht fun v hv => h v (by simp [vars, hv]))
      (fo_bind hu fun v hv => h v (by simp [vars, hv])) ?_
    cases t with
    | var x => exact absurd rfl (hnv x)
    | sym f => simp
    | app a b => simp

/-- A ground term is first-order. -/
theorem fo_ground : ∀ g : GTerm, g.firstOrder = true
  | var e => e.elim
  | sym _ => rfl
  | app (var e) _ => e.elim
  | app (sym _) u => by simpa [firstOrder] using fo_ground u
  | app (app a b) u => by
    simp only [firstOrder, Bool.and_eq_true]
    exact ⟨fo_ground (app a b), fo_ground u⟩

/-- A ground term as a pattern. -/
def lift (g : GTerm) : Pat := g.bind fun e => e.elim

@[simp] theorem lift_bind (g : GTerm) (σ : Nat → GTerm) : (lift g).bind σ = g := by
  unfold lift
  rw [bind_bind]
  conv_rhs => rw [← bind_var_id g]
  exact bind_congr fun v _ => v.elim

theorem lift_vars (g : GTerm) : (lift g).vars = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro v hv
  obtain ⟨e, -, -⟩ := Term.vars_bind_mem hv
  exact e.elim

theorem lift_fo (g : GTerm) : (lift g).firstOrder = true :=
  fo_bind (fo_ground g) fun v _ => v.elim

end Term

open Term Eqns

/-- The equations are between first-order terms. -/
def Eqns.FO {V : Type} (E : Eqns V) : Prop :=
  ∀ p ∈ E, p.1.firstOrder = true ∧ p.2.firstOrder = true

theorem Eqns.fo_subst {V : Type} [DecidableEq V] {E : Eqns V} {x : V} {u : Term V}
    (hE : E.FO) (hu : u.firstOrder = true) : (subst x u E).FO := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have hs : ∀ v, (single x u v).firstOrder = true := by
    intro v; unfold single; split
    · exact hu
    · rfl
  exact ⟨fo_bind (hE q hq).1 fun v _ => hs v, fo_bind (hE q hq).2 fun v _ => hs v⟩

theorem fo_extend {V : Type} [DecidableEq V] {x : V} {u : Term V} {θ : V → Term V}
    (hu : u.firstOrder = true) (hθ : ∀ v, (θ v).firstOrder = true) (v : V) :
    (extend x u θ v).firstOrder = true := by
  unfold extend
  refine fo_bind ?_ fun w _ => hθ w
  unfold single; split
  · exact hu
  · rfl

/-- The most general unifier of first-order equations is first-order. -/
theorem solve_fo {V : Type} [DecidableEq V] (E : Eqns V) :
    E.FO → ∀ θ, solve E = some θ → ∀ v, (θ v).firstOrder = true := by
  fun_induction solve E with
  | case1 => intro _ θ h v; cases h; rfl
  | case2 x E ih => exact fun hE => ih fun p hp => hE p (List.mem_cons_of_mem _ hp)
  | case3 x y E hxy ih =>
    intro hE θ h v
    obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fo_extend rfl
      (ih (Eqns.fo_subst (fun p hp => hE p (List.mem_cons_of_mem _ hp)) rfl) θ' hθ') v
  | case4 x g E ih =>
    intro hE θ h v
    obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fo_extend rfl
      (ih (Eqns.fo_subst (fun p hp => hE p (List.mem_cons_of_mem _ hp)) rfl) θ' hθ') v
  | case5 x a b E hx => intro _ θ h; cases h
  | case6 x a b E hx ih =>
    intro hE θ h v
    obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h
    have hab := (hE _ List.mem_cons_self).2
    exact fo_extend hab
      (ih (Eqns.fo_subst (fun p hp => hE p (List.mem_cons_of_mem _ hp)) hab) θ' hθ') v
  | case7 g y E ih =>
    intro hE θ h v
    obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fo_extend rfl
      (ih (Eqns.fo_subst (fun p hp => hE p (List.mem_cons_of_mem _ hp)) rfl) θ' hθ') v
  | case8 a b y E hy => intro _ θ h; cases h
  | case9 a b y E hy ih =>
    intro hE θ h v
    obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h
    have hab := (hE _ List.mem_cons_self).1
    exact fo_extend hab
      (ih (Eqns.fo_subst (fun p hp => hE p (List.mem_cons_of_mem _ hp)) hab) θ' hθ') v
  | case10 g E ih => exact fun hE => ih fun p hp => hE p (List.mem_cons_of_mem _ hp)
  | case11 g g' E h => intro _ θ h; cases h
  | case12 a b c d E ih =>
    intro hE
    apply ih
    have h₁ := fo_app (hE _ List.mem_cons_self).1
    have h₂ := fo_app (hE _ List.mem_cons_self).2
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨h₁.1, h₂.1⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨h₁.2.1, h₂.2.1⟩
      · exact hE p (List.mem_cons_of_mem _ hp)
  | case13 g a b E => intro _ θ h; cases h
  | case14 a b g E => intro _ θ h; cases h

end RwLog

namespace RwLog
namespace Term

variable {V W : Type}

theorem bind_foldl (σ : V → Term W) : ∀ (as : List (Term V)) (acc : Term V),
    (as.foldl app acc).bind σ = (as.map (bind σ)).foldl app (acc.bind σ)
  | [], _ => rfl
  | a :: as, acc => by simp [bind_foldl σ as]

/-- Substitution goes to the arguments of a surface term. -/
theorem bind_mk (σ : V → Term W) (f : Sym) (as : List (Term V)) :
    (mk f as).bind σ = mk f (as.map (bind σ)) := by
  simp [mk, bind_foldl]

theorem vars_foldl : ∀ (as : List (Term V)) (acc : Term V),
    (as.foldl app acc).vars = acc.vars ++ as.flatMap vars
  | [], _ => by simp
  | a :: as, acc => by simp [vars_foldl as, vars, List.append_assoc]

theorem vars_mk (f : Sym) (as : List (Term V)) : (mk f as).vars = as.flatMap vars := by
  simp [mk, vars_foldl, vars]

theorem syms_foldl_length : ∀ (as : List (Term V)) (acc : Term V),
    acc.syms.length ≤ (as.foldl app acc).syms.length
  | [], _ => Nat.le_refl _
  | a :: as, acc => by
    have := syms_foldl_length as (app acc a)
    simp only [syms, List.length_append] at this
    simp only [List.foldl_cons]
    omega

theorem syms_mk_pos (f : Sym) (as : List (Term V)) : 1 ≤ (mk f as).syms.length := by
  have := syms_foldl_length as (sym f)
  simpa [mk, syms] using this

theorem fo_foldl : ∀ (as : List (Term V)) (acc : Term V), acc.firstOrder = true →
    (∀ x, acc ≠ var x) → (∀ a ∈ as, a.firstOrder = true) → (as.foldl app acc).firstOrder = true
  | [], _, h, _, _ => h
  | a :: as, acc, h, hv, has => by
    simp only [List.foldl_cons]
    exact fo_foldl as (app acc a) (fo_app_mk h (has a List.mem_cons_self) hv) (by simp)
      fun b hb => has b (List.mem_cons_of_mem _ hb)

/-- A surface term with first-order arguments is first-order. -/
theorem fo_mk (f : Sym) (as : List (Term V)) (h : ∀ a ∈ as, a.firstOrder = true) :
    (mk f as).firstOrder = true :=
  fo_foldl as (sym f) rfl (by simp) h

theorem syms_length_bind_le (σ : V → Term W) : ∀ t : Term V,
    t.syms.length ≤ (t.bind σ).syms.length
  | var _ => by simp [syms]
  | sym _ => Nat.le_refl _
  | app t u => by
    have := syms_length_bind_le σ t
    have := syms_length_bind_le σ u
    simp only [bind_app, syms, List.length_append]
    omega

/-- Replacing a variable that occurs by a term with a symbol adds symbols. -/
theorem syms_length_bind_single_lt [DecidableEq V] {v : V} {u : Term V}
    (hu : 1 ≤ u.syms.length) : ∀ {t : Term V}, v ∈ t.vars →
    t.syms.length < (t.bind (single v u)).syms.length
  | var w, h => by
    simp only [vars, List.mem_singleton] at h
    subst h
    simp only [bind_var, single, ite_true, syms, List.length_nil]
    omega
  | sym _, h => by simp [vars] at h
  | app a b, h => by
    simp only [vars, List.mem_append] at h
    have ha := syms_length_bind_le (single v u) a
    have hb := syms_length_bind_le (single v u) b
    simp only [bind_app, syms, List.length_append]
    rcases h with h | h
    · have := syms_length_bind_single_lt hu h; omega
    · have := syms_length_bind_single_lt hu h; omega

end Term
end RwLog
