import RwLog.Rungs.R001.Spec

namespace RwLog

open Term

namespace Checker

open Matching

/-! ## Variables eliminated by a most general unifier -/

section SolveVars

variable {V W : Type} [DecidableEq V]

/-- What `solve` guarantees about variables: it leaves variables outside the
equations alone, sends the equations' variables to terms over them, and when
some equation is not trivial, some variable of the equations occurs in no
image. -/
def VarsSpec (E : Eqns V) (θ : V → Term V) : Prop :=
  (∀ w, w ∉ Eqns.vars E → θ w = .var w) ∧
  (∀ w ∈ Eqns.vars E, ∀ u ∈ (θ w).vars, u ∈ Eqns.vars E) ∧
  ((E.all fun e => decide (e.1 = e.2)) = false → ∃ x ∈ Eqns.vars E, ∀ w, x ∉ (θ w).vars)

theorem mem_vars_subst {x : V} {u : Term V} {E : Eqns V} {v : V} (hx : x ∉ u.vars)
    (h : v ∈ Eqns.vars (Eqns.subst x u E)) : v ≠ x ∧ (v ∈ Eqns.vars E ∨ v ∈ u.vars) := by
  simp only [Eqns.vars, Eqns.subst, List.flatMap_map, List.mem_flatMap, List.mem_append] at h
  obtain ⟨p, hp, h⟩ := h
  have key : ∀ t ∈ [p.1, p.2], v ∈ (t.bind (single x u)).vars →
      v ≠ x ∧ (v ∈ Eqns.vars E ∨ v ∈ u.vars) := by
    intro t ht hv
    rcases vars_bind_single v hv with ⟨h1, h2⟩ | h1
    · refine ⟨h2, Or.inl ?_⟩
      simp only [Eqns.vars, List.mem_flatMap, List.mem_append]
      simp at ht; rcases ht with rfl | rfl
      · exact ⟨p, hp, Or.inl h1⟩
      · exact ⟨p, hp, Or.inr h1⟩
    · exact ⟨fun e => hx (e ▸ h1), Or.inr h1⟩
  rcases h with h | h
  · exact key _ (by simp) h
  · exact key _ (by simp) h

theorem varsSpec_elim {L E : Eqns V} {x : V} {u : Term V} (hx : x ∉ u.vars)
    (hxL : x ∈ Eqns.vars L) (huL : ∀ v ∈ u.vars, v ∈ Eqns.vars L)
    (hEL : ∀ v ∈ Eqns.vars E, v ∈ Eqns.vars L) {θ₀ : V → Term V}
    (ih : VarsSpec (Eqns.subst x u E) θ₀) : VarsSpec L (extend x u θ₀) := by
  obtain ⟨i1, i2, -⟩ := ih
  have hsubL : ∀ v ∈ Eqns.vars (Eqns.subst x u E), v ∈ Eqns.vars L ∧ v ≠ x := by
    intro v hv
    obtain ⟨hne, h⟩ := mem_vars_subst hx hv
    rcases h with h | h
    · exact ⟨hEL v h, hne⟩
    · exact ⟨huL v h, hne⟩
  -- every variable of an image comes from a variable of `single x u w`
  have himg : ∀ w, ∀ u' ∈ (extend x u θ₀ w).vars, ∃ v ∈ (single x u w).vars,
      u' ∈ (θ₀ v).vars := fun w u' h => vars_bind_mem h
  have hθ₀ : ∀ v u', u' ∈ (θ₀ v).vars → (v ∈ Eqns.vars (Eqns.subst x u E) ∧
      u' ∈ Eqns.vars (Eqns.subst x u E)) ∨ (v ∉ Eqns.vars (Eqns.subst x u E) ∧ u' = v) := by
    intro v u' h
    by_cases hv : v ∈ Eqns.vars (Eqns.subst x u E)
    · exact Or.inl ⟨hv, i2 v hv u' h⟩
    · rw [i1 v hv] at h; simp [vars] at h; exact Or.inr ⟨hv, h⟩
  refine ⟨fun w hw => ?_, fun w hw u' hu' => ?_, fun _ => ⟨x, hxL, fun w hxw => ?_⟩⟩
  · have hwx : w ≠ x := fun e => hw (e ▸ hxL)
    have hws : w ∉ Eqns.vars (Eqns.subst x u E) := fun h => hw (hsubL w h).1
    simp [extend, single, hwx, i1 w hws]
  · obtain ⟨v, hv, hu'⟩ := himg w u' hu'
    have hvL : v ∈ Eqns.vars L := by
      by_cases hwx : w = x
      · simp [single, hwx] at hv; exact huL v hv
      · simp [single, hwx, vars] at hv; subst hv; exact hw
    rcases hθ₀ v u' hu' with ⟨-, h⟩ | ⟨-, rfl⟩
    · exact (hsubL u' h).1
    · exact hvL
  · obtain ⟨v, hv, hu'⟩ := himg w x hxw
    have hvx : v ≠ x := by
      by_cases hwx : w = x
      · simp [single, hwx] at hv; exact fun e => hx (e ▸ hv)
      · simp [single, hwx, vars] at hv; subst hv; exact hwx
    rcases hθ₀ v x hu' with ⟨-, h⟩ | ⟨-, h⟩
    · exact (hsubL x h).2 rfl
    · exact hvx h.symm

omit [DecidableEq V] in
theorem mem_vars_cons {t u : Term V} {E : Eqns V} {v : V} :
    v ∈ Eqns.vars ((t, u) :: E) ↔ v ∈ t.vars ∨ v ∈ u.vars ∨ v ∈ Eqns.vars E := by
  simp [Eqns.vars_cons]

theorem varsSpec_trivial {E : Eqns V} {t : Term V} {θ : V → Term V}
    (h : VarsSpec E θ) : VarsSpec ((t, t) :: E) θ := by
  obtain ⟨i1, i2, i3⟩ := h
  refine ⟨fun w hw => i1 w fun h => hw (mem_vars_cons.2 (Or.inr (Or.inr h))),
    fun w hw u hu => ?_, fun hall => ?_⟩
  · by_cases hE : w ∈ Eqns.vars E
    · exact mem_vars_cons.2 (Or.inr (Or.inr (i2 w hE u hu)))
    · rw [i1 w hE] at hu; simp [vars] at hu; subst hu; exact hw
  · simp only [List.all_cons, decide_true, Bool.true_and] at hall
    obtain ⟨x, hx, h⟩ := i3 hall
    exact ⟨x, mem_vars_cons.2 (Or.inr (Or.inr hx)), h⟩

theorem solve_vars : ∀ (E : Eqns V) (θ : V → Term V), solve E = some θ → VarsSpec E θ := by
  intro E
  induction E using solve.induct with
  | case1 =>
    intro θ h; simp only [solve, Option.some.injEq] at h; subst h
    exact ⟨fun _ _ => rfl, fun w _ u hu => by simp [vars] at hu; subst hu; assumption,
      fun h => by simp at h⟩
  | case2 y E ih =>
    intro θ h; simp only [solve, ite_true] at h
    exact varsSpec_trivial (ih θ h)
  | case3 x y E hxy ih =>
    intro θ h
    simp only [solve, hxy, ite_false, Option.map_eq_some_iff] at h
    obtain ⟨θ₀, h₀, rfl⟩ := h
    exact varsSpec_elim (by simp [vars, hxy]) (mem_vars_cons.2 (by simp [vars]))
      (fun v hv => mem_vars_cons.2 (Or.inr (Or.inl hv)))
      (fun v hv => mem_vars_cons.2 (Or.inr (Or.inr hv))) (ih θ₀ h₀)
  | case4 x f E ih =>
    intro θ h
    simp only [solve, Option.map_eq_some_iff] at h
    obtain ⟨θ₀, h₀, rfl⟩ := h
    exact varsSpec_elim (by simp [vars]) (mem_vars_cons.2 (by simp [vars]))
      (fun v hv => by simp [vars] at hv)
      (fun v hv => mem_vars_cons.2 (Or.inr (Or.inr hv))) (ih θ₀ h₀)
  | case5 x a b E hx =>
    intro θ h; simp [solve, hx] at h
  | case6 x a b E hx ih =>
    intro θ h
    simp only [solve, hx, ite_false, Option.map_eq_some_iff] at h
    obtain ⟨θ₀, h₀, rfl⟩ := h
    exact varsSpec_elim hx (mem_vars_cons.2 (by simp [vars]))
      (fun v hv => mem_vars_cons.2 (Or.inr (Or.inl hv)))
      (fun v hv => mem_vars_cons.2 (Or.inr (Or.inr hv))) (ih θ₀ h₀)
  | case7 f y E ih =>
    intro θ h
    simp only [solve, Option.map_eq_some_iff] at h
    obtain ⟨θ₀, h₀, rfl⟩ := h
    exact varsSpec_elim (by simp [vars]) (mem_vars_cons.2 (by simp [vars]))
      (fun v hv => by simp [vars] at hv)
      (fun v hv => mem_vars_cons.2 (Or.inr (Or.inr hv))) (ih θ₀ h₀)
  | case8 a b y E hy =>
    intro θ h; simp [solve, hy] at h
  | case9 a b y E hy ih =>
    intro θ h
    simp only [solve, hy, ite_false, Option.map_eq_some_iff] at h
    obtain ⟨θ₀, h₀, rfl⟩ := h
    exact varsSpec_elim hy (mem_vars_cons.2 (by simp [vars]))
      (fun v hv => mem_vars_cons.2 (Or.inl hv))
      (fun v hv => mem_vars_cons.2 (Or.inr (Or.inr hv))) (ih θ₀ h₀)
  | case10 g E ih =>
    intro θ h; simp only [solve, ite_true] at h
    exact varsSpec_trivial (ih θ h)
  | case11 f g E hfg =>
    intro θ h; simp [solve, hfg] at h
  | case12 a b c d E ih =>
    intro θ h
    simp only [solve] at h
    obtain ⟨i1, i2, i3⟩ := ih θ h
    have hiff : ∀ v, v ∈ Eqns.vars ((a, c) :: (b, d) :: E) ↔
        v ∈ Eqns.vars ((Term.app a b, Term.app c d) :: E) := by
      intro v; simp only [mem_vars_cons, vars, List.mem_append]; tauto
    refine ⟨fun w hw => i1 w fun h => hw ((hiff w).1 h),
      fun w hw u hu => (hiff u).1 (i2 w ((hiff w).2 hw) u hu), fun hall => ?_⟩
    obtain ⟨x, hx, hx'⟩ := i3 (by
      simp only [List.all_cons, Bool.and_eq_false_iff, decide_eq_false_iff_not,
        Term.app.injEq, not_and_or] at hall ⊢
      tauto)
    exact ⟨x, (hiff x).1 hx, hx'⟩
  | case13 f a b E =>
    intro θ h; simp [solve] at h
  | case14 a b f E =>
    intro θ h; simp [solve] at h

end SolveVars

/-! ## Counting a store's variables -/

theorem nodup_eraseDups {α : Type} [DecidableEq α] : ∀ l : List α, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    have : (as.filter fun b => !b == a).length < as.length + 1 :=
      Nat.lt_add_one_of_le (List.length_filter_le _ as)
    refine List.nodup_cons.2 ⟨?_, nodup_eraseDups _⟩
    simp
termination_by l => l.length

theorem length_eraseDups {α : Type} [DecidableEq α] (l : List α) :
    l.eraseDups.length = l.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (nodup_eraseDups l)]
  congr 1; ext; simp

/-- The variables of a store. -/
def storeVars (c : Store) : Finset Nat := (c.flatMap Term.vars).toFinset

theorem varCount_eq (c : Store) : c.varCount = (storeVars c).card := by
  rw [Store.varCount, length_eraseDups]; rfl

theorem mem_storeVars {c : Store} {v : Nat} : v ∈ storeVars c ↔ ∃ a ∈ c, v ∈ a.vars := by
  simp [storeVars]

/-! ## Symbolic firings and their ground instances -/

/-- The equations of a firing, instantiated by the match. -/
def instEqs (eqs : List (Pat × Pat)) (r : PSubst × List Pat) : List (Pat × Pat) :=
  eqs.map fun e => (e.1.bind r.1.apply, e.2.bind r.1.apply)

theorem mem_firings {ρ : TRule} {c : Store} {f : Firing} (h : f ∈ ρ.firings c) :
    ∃ r ∈ matchAll ρ.heads c [],
      (ρ.body = .fail ∧ f = .refuted) ∨
        ∃ eqs cs, ρ.body = .conj eqs cs ∧
          f = firingOfEqs (instEqs eqs r) (cs.map (Term.bind r.1.apply)) := by
  simp only [TRule.firings, List.mem_map] at h
  obtain ⟨r, hr, h⟩ := h
  refine ⟨r, hr, ?_⟩
  cases hb : ρ.body with
  | fail => rw [hb] at h; exact Or.inl ⟨rfl, h.symm⟩
  | conj eqs cs => rw [hb] at h; exact Or.inr ⟨eqs, cs, rfl, h.symm⟩

theorem mem_theory_firings {T : Theory} {c : Store} {f : Firing} (h : f ∈ T.firings c) :
    ∃ ρ ∈ T, f ∈ ρ.firings c := by
  simp only [Theory.firings, List.mem_flatMap] at h
  obtain ⟨ρ, hρ, h⟩ := h
  split_ifs at h
  · exact ⟨ρ, hρ, h⟩
  · simp at h

/-- The ground substitution of a symbolic firing at a ground instance. -/
def gsub (r : PSubst × List Pat) (σ : Nat → GTerm) : Nat → GTerm :=
  fun v => (r.1.apply v).bind σ

theorem bind_gsub (r : PSubst × List Pat) (σ : Nat → GTerm) (t : Pat) :
    t.bind (gsub r σ) = (t.bind r.1.apply).bind σ := by
  rw [bind_bind]; rfl

theorem heads_inst {ρ : TRule} {c : Store} {r : PSubst × List Pat}
    (hr : r ∈ matchAll ρ.heads c []) : ρ.heads.map (Term.bind r.1.apply) = r.2 :=
  (matchAll_sound _ _ _ _ hr).2.2.2 _ (Ext.refl _)

/-- Every atom of the store holds in `M` under `σ`. -/
def Holds (M : Interp) (σ : Nat → GTerm) (c : Store) : Prop := ∀ x ∈ c, x.bind σ ∈ M

/-- In a well-formed rule the heads fix the body, so a rule holding in `M`
says: its heads hold under `σ` exactly when its body does. -/
theorem rule_iff {M : Interp} {ρ : TRule} (hwf : ρ.WellFormed) (hρ : ρ.HoldsIn M)
    (σ : Nat → GTerm) : (∀ h ∈ ρ.heads, h.bind σ ∈ M) ↔ ρ.body.HoldsAt M σ := by
  rw [hρ σ]
  constructor
  · rintro ⟨τ, hτ, hb⟩
    have hc : ∀ t : Pat, (∀ v ∈ t.vars, ρ.HeadVar v) → t.bind τ = t.bind σ :=
      fun t ht => Term.bind_congr fun v hv => hτ v (ht v hv)
    cases hbd : ρ.body with
    | fail => rw [hbd] at hb; exact hb
    | conj eqs cs =>
      rw [hbd] at hb
      have he := hwf.2; have ha := hwf.1
      rw [hbd] at he ha
      refine ⟨fun e hee => ?_, fun x hx => ?_⟩
      · rw [← hc e.1 fun v hv => he e hee v (List.mem_append_left _ hv),
          ← hc e.2 fun v hv => he e hee v (List.mem_append_right _ hv)]
        exact hb.1 e hee
      · rw [← hc x (ha x hx)]; exact hb.2 x hx
  · intro hb; exact ⟨σ, fun _ _ => rfl, hb⟩

theorem heads_hold {M : Interp} {ρ : TRule} {c : Store} {r : PSubst × List Pat}
    (hr : r ∈ matchAll ρ.heads c []) {σ : Nat → GTerm} :
    (∀ h ∈ ρ.heads, h.bind (gsub r σ) ∈ M) ↔ ∀ x ∈ r.2, x.bind σ ∈ M := by
  rw [← heads_inst hr]
  simp [bind_gsub]

theorem unifies_instEqs {eqs : List (Pat × Pat)} {r : PSubst × List Pat} {σ : Nat → GTerm} :
    Eqns.Unifies σ (instEqs eqs r) ↔ ∀ e ∈ eqs, e.1.bind (gsub r σ) = e.2.bind (gsub r σ) := by
  simp only [Eqns.Unifies, instEqs, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, bind_gsub]

/-- What one symbolic firing says about a ground instance of its store in a
model. -/
def GroundFact (M : Interp) (σ : Nat → GTerm) (c : Store) : Firing → Prop
  | .refuted => ¬ Holds M σ c
  | .add bs => Holds M σ c → Holds M σ bs
  | .bind θ => Holds M σ c → ∀ v, (θ v).bind σ = σ v

theorem firing_ground {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {M : Interp} (hM : T.Model M)
    {ρ : TRule} (hρ : ρ ∈ T) {c : Store} {f : Firing} (hf : f ∈ ρ.firings c)
    (σ : Nat → GTerm) : GroundFact M σ c f := by
  obtain ⟨r, hr, h⟩ := mem_firings hf
  have hiff := rule_iff (hwf ρ hρ) (hM ρ hρ) (gsub r σ)
  have hrc : ∀ x ∈ r.2, x ∈ c := (matchAll_sound _ _ _ _ hr).2.2.1
  have hbody : Holds M σ c → ρ.body.HoldsAt M (gsub r σ) := fun hc =>
    hiff.1 ((heads_hold hr).2 fun x hx => hc x (hrc x hx))
  rcases h with ⟨hb, rfl⟩ | ⟨eqs, cs, hb, rfl⟩
  · intro hc; have := hbody hc; rw [hb] at this; exact this
  · have hbody' : Holds M σ c → Eqns.Unifies σ (instEqs eqs r) ∧
        ∀ x ∈ cs, x.bind (gsub r σ) ∈ M := by
      intro hc; have := hbody hc; rw [hb] at this
      exact ⟨unifies_instEqs.2 this.1, this.2⟩
    unfold firingOfEqs
    split_ifs with hall
    · intro hc x hx
      obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hx
      rw [← bind_gsub]; exact (hbody' hc).2 b hb'
    · cases hs : solve (instEqs eqs r) with
      | none => exact fun hc => solve_none hs σ (hbody' hc).1
      | some θ => exact fun hc v => (solve_some hs).2 σ (hbody' hc).1 v

/-! ## The closure -/

theorem firingOfEqs_add {eqs : List (Pat × Pat)} {bs bs' : Store}
    (h : firingOfEqs eqs bs = .add bs') : bs' = bs := by
  unfold firingOfEqs at h
  split_ifs at h
  · cases h; rfl
  · cases hs : solve eqs <;> rw [hs] at h <;> cases h

/-- An atom a round of the closure adds is added by a firing. -/
theorem mem_new {T : Theory} {c : Store} {x : Pat} (hx : x ∈ T.newAtoms c) :
    ∃ bs, Firing.add bs ∈ T.firings c ∧ x ∈ bs := by
  simp only [Theory.newAtoms, List.mem_filter, List.mem_eraseDups, List.mem_flatMap] at hx
  obtain ⟨⟨f, hf, hxf⟩, -⟩ := hx
  cases f with
  | add bs => exact ⟨bs, hf, hxf⟩
  | refuted => simp [Firing.added] at hxf
  | bind _ => simp [Firing.added] at hxf

/-- A property of the store's atoms that every firing passes on to the atoms
it adds holds of the closure. -/
theorem saturate_induct {T : Theory} (P : Pat → Prop)
    (hadd : ∀ d : Store, (∀ x ∈ d, P x) → ∀ bs, Firing.add bs ∈ T.firings d → ∀ x ∈ bs, P x) :
    ∀ c : Store, (∀ x ∈ c, P x) → ∀ x ∈ T.saturate c, P x := by
  intro c hc x hx
  rw [Theory.saturate] at hx
  split at hx
  · exact hc x hx
  · refine saturate_induct P hadd _ (fun y hy => ?_) x hx
    rcases List.mem_append.1 hy with hy | hy
    · exact hc y hy
    · obtain ⟨bs, hf, hyb⟩ := mem_new hy
      exact hadd c hc bs hf y hyb
termination_by c => T.room c
decreasing_by exact Theory.room_lt ‹_›

/-- The closure holds wherever the store does. -/
theorem saturate_holds {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {M : Interp} (hM : T.Model M)
    (σ : Nat → GTerm) {c : Store} (hc : Holds M σ c) : Holds M σ (T.saturate c) := by
  intro x hx
  refine saturate_induct (T := T) (fun x => x.bind σ ∈ M) ?_ c hc x hx
  intro d hd bs hf
  obtain ⟨ρ, hρ, hf⟩ := mem_theory_firings hf
  exact firing_ground hwf hM hρ hf σ hd

/-- A firing on a store is a firing on every larger store. -/
theorem firings_mono {T : Theory} {d e : Store} (h : ∀ x ∈ d, x ∈ e) {f : Firing}
    (hf : f ∈ T.firings d) : f ∈ T.firings e := by
  simp only [Theory.firings, List.mem_flatMap] at hf ⊢
  obtain ⟨ρ, hρ, hf⟩ := hf
  refine ⟨ρ, hρ, ?_⟩
  split_ifs at hf ⊢
  · simp only [TRule.firings, List.mem_map] at hf ⊢
    obtain ⟨r, hr, rfl⟩ := hf
    exact ⟨r, matchAll_mono h _ _ _ hr, rfl⟩
  · exact hf

/-- The closure of a store lies in the closure of every larger store. -/
theorem saturate_mono (T : Theory) {c' c : Store} (h : ∀ x ∈ c', x ∈ c) :
    ∀ x ∈ T.saturate c', x ∈ T.saturate c := by
  refine saturate_induct (T := T) (fun x => x ∈ T.saturate c) ?_ c'
    (fun x hx => T.sub_saturate c x (h x hx))
  intro d hd bs hf x hx
  by_contra hn
  have hnew : x ∈ T.newAtoms (T.saturate c) := by
    simp only [Theory.newAtoms, List.mem_filter, List.mem_eraseDups, List.mem_flatMap,
      Bool.not_eq_true']
    refine ⟨⟨_, firings_mono hd hf, hx⟩, ?_⟩
    cases hc : (T.saturate c).contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hn
  rw [T.saturate_closed c] at hnew
  cases hnew

/-- Refuting a store refutes every store that contains it. -/
theorem refutes_mono (T : Theory) {c' c : Store} (hsub : ∀ x ∈ c', x ∈ c)
    (h : T.refutes? c' = true) : T.refutes? c = true := by
  rw [Theory.refutes?] at h ⊢
  simp only [List.any_eq_true] at h ⊢
  obtain ⟨f, hf, hr⟩ := h
  exact ⟨f, firings_mono (saturate_mono T hsub) hf, hr⟩

/-- Two stores with the same members have closures with the same members. -/
theorem saturate_congr (T : Theory) {c c' : Store} (h : ∀ x, x ∈ c ↔ x ∈ c') :
    ∀ x, x ∈ T.saturate c ↔ x ∈ T.saturate c' :=
  fun x => ⟨saturate_mono T (fun y hy => (h y).1 hy) x, saturate_mono T (fun y hy => (h y).2 hy) x⟩

theorem refutes_congr (T : Theory) {c c' : Store} (h : ∀ x, x ∈ c ↔ x ∈ c') :
    T.refutes? c = T.refutes? c' := by
  apply Bool.eq_iff_iff.2
  exact ⟨refutes_mono T fun y hy => (h y).1 hy, refutes_mono T fun y hy => (h y).2 hy⟩

theorem bind_none_congr (T : Theory) {c c' : Store} (h : ∀ x, x ∈ c ↔ x ∈ c')
    (hb : T.bind? c = none) : T.bind? c' = none := by
  rw [Theory.bind?, List.findSome?_eq_none_iff] at hb ⊢
  intro f hf
  exact hb f (firings_mono (fun y hy => (saturate_congr T h y).2 hy) hf)

/-! ## `refutes_sound` -/

theorem refutes_ground {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {M : Interp}
    (hM : T.Model M) (σ : Nat → GTerm) (c : Store) (h : T.refutes? c = true) :
    ¬ Holds M σ c := by
  rw [Theory.refutes?] at h
  simp only [List.any_eq_true] at h
  obtain ⟨f, hf, h⟩ := h
  obtain ⟨ρ, hρ, hf⟩ := mem_theory_firings hf
  cases f with
  | refuted => exact fun hc => firing_ground hwf hM hρ hf σ (saturate_holds hwf hM σ hc)
  | add _ => simp at h
  | bind _ => simp at h

/-! ## Forced equations -/

theorem bind_ground {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {M : Interp}
    (hM : T.Model M) (σ : Nat → GTerm) (c : Store) {θ : Nat → Pat}
    (h : T.bind? c = some θ) : Holds M σ c → ∀ v, (θ v).bind σ = σ v := by
  rw [Theory.bind?] at h
  obtain ⟨f, hf, h⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨ρ, hρ, hf⟩ := mem_theory_firings hf
  cases f with
  | refuted => cases h
  | add _ => cases h
  | bind θ' => cases h; exact fun hc => firing_ground hwf hM hρ hf σ (saturate_holds hwf hM σ hc)

/-! ## Rewriting a store for showing -/

theorem mem_replace {c ms bs : Store} {x : Pat} :
    x ∈ c.replace ms bs ↔ (x ∈ c ∧ x ∉ ms) ∨ x ∈ bs := by
  simp [Store.replace, List.mem_eraseDups]

theorem rewrite_holds {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {M : Interp} (hM : T.Model M)
    {ρ : TRule} (hρ : ρ ∈ T) {c c' : Store} (h : c' ∈ ρ.rewrites c) (σ : Nat → GTerm) :
    Holds M σ c' ↔ Holds M σ c := by
  unfold TRule.rewrites at h
  cases hb : ρ.body with
  | fail => rw [hb] at h; cases h
  | conj eqs cs =>
    rw [hb] at h
    simp only [List.mem_filterMap] at h
    obtain ⟨r, hr, h⟩ := h
    split_ifs at h with hall
    cases h
    have hiff := rule_iff (hwf ρ hρ) (hM ρ hρ) (gsub r σ)
    rw [hb] at hiff
    have hrc : ∀ x ∈ r.2, x ∈ c := (matchAll_sound _ _ _ _ hr).2.2.1
    have heq : ∀ e ∈ eqs, e.1.bind (gsub r σ) = e.2.bind (gsub r σ) := by
      intro e he
      simp only [List.all_eq_true, decide_eq_true_eq] at hall
      rw [bind_gsub, bind_gsub, hall e he]
    constructor
    · intro hc' x hx
      by_cases hxr : x ∈ r.2
      · have hh := hiff.2 ⟨heq, fun b hb' => by
          rw [bind_gsub]; exact hc' _ (mem_replace.2 (Or.inr (List.mem_map_of_mem hb')))⟩
        exact (heads_hold hr).1 hh x hxr
      · exact hc' x (mem_replace.2 (Or.inl ⟨hx, hxr⟩))
    · intro hc x hx
      rcases mem_replace.1 hx with ⟨hx, -⟩ | hx
      · exact hc x hx
      · obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hx
        rw [← bind_gsub]
        exact (hiff.1 ((heads_hold hr).2 fun x hx => hc x (hrc x hx))).2 b hb'

theorem step_spec {T : Theory} {c : Store} {c' : {c' : Store // T.storeWeight c' < T.storeWeight c}}
    (h : T.step? c = some c') : ∃ ρ ∈ T, c'.1 ∈ ρ.rewrites c := by
  rw [Theory.step?] at h
  obtain ⟨ρ, hρ, h⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at h
  obtain ⟨d, hd, h⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at h
  cases h
  exact ⟨ρ, hρ, hd⟩

theorem normalize_holds {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {M : Interp}
    (hM : T.Model M) (σ : Nat → GTerm) (c : Store) :
    Holds M σ (T.normalize c) ↔ Holds M σ c := by
  rw [Theory.normalize]
  split
  · rfl
  · rename_i c' hs
    obtain ⟨ρ, hρ, hf⟩ := step_spec hs
    have := c'.2
    exact (normalize_holds hwf hM σ c'.1).trans (rewrite_holds hwf hM hρ hf σ)
termination_by T.storeWeight c

/-! ## Meanings of spans -/

theorem denAt_store {M : Interp} {s : Span} {c : Store} (h : ∀ σ, Holds M σ c ↔ Holds M σ s.c) :
    Span.denAt M ⟨s.l, s.r, c⟩ = s.denAt M := by
  ext p
  simp only [Span.denAt, Set.mem_ofPred_eq]
  exact exists_congr fun σ => and_congr_right fun _ => and_congr_right fun _ => h σ

theorem inst_denAt {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {M : Interp} (hM : T.Model M)
    {s : Span} {θ : Nat → Pat} (h : T.bind? s.c = some θ) : (s.inst θ).denAt M = s.denAt M := by
  ext p
  simp only [Span.denAt, Span.inst, Set.mem_ofPred_eq, List.mem_eraseDups, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨σ, h1, h2, h3⟩
    refine ⟨fun v => (θ v).bind σ, ?_, ?_, fun x hx => ?_⟩
    · rw [h1, bind_bind]
    · rw [h2, bind_bind]
    · have := h3 x hx; rwa [bind_bind] at this
  · rintro ⟨σ, h1, h2, h3⟩
    have hθ : (fun v => (θ v).bind σ) = σ := funext (bind_ground hwf hM σ s.c h h3)
    refine ⟨σ, ?_, ?_, fun x hx => ?_⟩
    · rw [h1, bind_bind, hθ]
    · rw [h2, bind_bind, hθ]
    · rw [bind_bind, hθ]; exact h3 x hx

/-! ## `simplify_exact` -/

theorem sw_refuted {T : Theory} {n : Nat} {s : Span} (hr : T.refutes? s.c = true) :
    T.simplifyWithin n s = none := by
  unfold Theory.simplifyWithin; simp [hr]

theorem sw_bind {T : Theory} {n : Nat} {s : Span} {θ : Nat → Pat} (hr : T.refutes? s.c = false)
    (hb : T.bind? s.c = some θ) : T.simplifyWithin (n + 1) s = T.simplifyWithin n (s.inst θ) := by
  conv_lhs => unfold Theory.simplifyWithin
  simp [hr, hb]

theorem sw_done {T : Theory} {n : Nat} {s : Span} (hr : T.refutes? s.c = false)
    (hb : n = 0 ∨ T.bind? s.c = none) :
    T.simplifyWithin n s = some ⟨s.l, s.r, s.c.eraseDups⟩ := by
  rcases hb with rfl | hb
  · unfold Theory.simplifyWithin; simp [hr]
  · unfold Theory.simplifyWithin; simp [hr, hb]

/-- What a simplification step owes. -/
def Exact (T : Theory) (s : Span) (o : Option Span) : Prop :=
  (o = none → s.Dead T) ∧ ∀ s', o = some s' → s'.Refines T s

theorem exact_refuted {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {s : Span}
    (hr : T.refutes? s.c = true) : Exact T s none := by
  refine ⟨fun _ M hM => ?_, fun _ h => by cases h⟩
  ext p; simp only [Span.denAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨σ, -, -, hc⟩
  exact refutes_ground hwf hM σ s.c hr hc

theorem exact_done (T : Theory) (s : Span) :
    Exact T s (some ⟨s.l, s.r, s.c.eraseDups⟩) := by
  refine ⟨fun h => (by cases h), fun s' h => ?_⟩
  cases h
  exact fun M _ => denAt_store fun σ => by simp [Holds, List.mem_eraseDups]

theorem simplifyWithin_exact {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) :
    ∀ (n : Nat) (s : Span), Exact T s (T.simplifyWithin n s) := by
  intro n
  induction n with
  | zero =>
    intro s
    cases hr : T.refutes? s.c
    · rw [sw_done hr (Or.inl rfl)]; exact exact_done T s
    · rw [sw_refuted hr]; exact exact_refuted hwf hr
  | succ n ih =>
    intro s
    cases hr : T.refutes? s.c
    · cases hb : T.bind? s.c with
      | some θ =>
        rw [sw_bind hr hb]
        obtain ⟨i1, i2⟩ := ih (s.inst θ)
        refine ⟨fun h M hM => ?_, fun s' h M hM => ?_⟩
        · rw [← inst_denAt hwf hM hb]; exact i1 h M hM
        · rw [i2 s' h M hM, inst_denAt hwf hM hb]
      | none => rw [sw_done hr (Or.inr hb)]; exact exact_done T s
    · rw [sw_refuted hr]; exact exact_refuted hwf hr

/-! ## Forced equations stay inside the store -/

theorem vars_body_sub {ρ : TRule} {c : Store} {r : PSubst × List Pat}
    (hr : r ∈ matchAll ρ.heads c []) {t : Pat} (ht : ∀ v ∈ t.vars, ∃ h ∈ ρ.heads, v ∈ h.vars)
    {u : Nat} (hu : u ∈ (t.bind r.1.apply).vars) : u ∈ storeVars c := by
  obtain ⟨v, hv, hu⟩ := vars_bind_mem hu
  obtain ⟨h, hh, hvh⟩ := ht v hv
  have hmem : h.bind r.1.apply ∈ c := by
    have : h.bind r.1.apply ∈ r.2 := by rw [← heads_inst hr]; exact List.mem_map_of_mem hh
    exact (matchAll_sound _ _ _ _ hr).2.2.1 _ this
  exact mem_storeVars.2 ⟨_, hmem, vars_sub_bind hvh u hu⟩

theorem firingOfEqs_bind {eqs : List (Pat × Pat)} {c : Store} {θ : Nat → Pat}
    (h : firingOfEqs eqs c = .bind θ) :
    solve eqs = some θ ∧ (eqs.all fun e => decide (e.1 = e.2)) = false := by
  unfold firingOfEqs at h
  by_cases hall : (eqs.all fun e => decide (e.1 = e.2)) = true
  · simp only [hall, ↓reduceIte] at h; cases h
  · simp only [hall, ↓reduceIte, Bool.false_eq_true] at h
    cases hs : solve eqs with
    | none => rw [hs] at h; cases h
    | some θ' => rw [hs] at h; cases h; exact ⟨rfl, by simpa using hall⟩

/-- The closure adds no variable: every variable of a rule's body occurs in its
heads, which the firing matched to members. -/
theorem storeVars_saturate {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) (c : Store) :
    storeVars (T.saturate c) ⊆ storeVars c := by
  intro u hu
  obtain ⟨a, ha, hu⟩ := mem_storeVars.1 hu
  refine saturate_induct (T := T) (fun a => ∀ u ∈ a.vars, u ∈ storeVars c) ?_ c
    (fun x hx u hu => mem_storeVars.2 ⟨x, hx, hu⟩) a ha u hu
  intro d hd bs hf x hx u hu
  obtain ⟨ρ, hρ, hf⟩ := mem_theory_firings hf
  obtain ⟨r, hr, h⟩ := mem_firings hf
  rcases h with ⟨-, h⟩ | ⟨eqs, cs, hb, h⟩
  · cases h
  · rw [firingOfEqs_add h.symm] at hx
    obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hx
    have := (hwf ρ hρ).1; rw [hb] at this
    obtain ⟨y, hy, hu'⟩ := mem_storeVars.1 (vars_body_sub hr (this b hb') hu)
    exact hd y hy u hu'

/-- A forced instantiation solves non-trivial equations over the store's
variables. -/
theorem bind_solve {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) (c : Store) {θ : Nat → Pat}
    (h : T.bind? c = some θ) :
    ∃ E : Eqns Nat, solve E = some θ ∧ (E.all fun e => decide (e.1 = e.2)) = false ∧
      ∀ v ∈ Eqns.vars E, v ∈ storeVars c := by
  rw [Theory.bind?] at h
  obtain ⟨f, hf, h⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨ρ, hρ, hf⟩ := mem_theory_firings hf
  cases f with
  | refuted => cases h
  | add _ => cases h
  | bind θ' =>
    cases h
    obtain ⟨r, hr, hfr⟩ := mem_firings hf
    rcases hfr with ⟨-, h⟩ | ⟨eqs, cs, hb, h⟩
    · cases h
    · obtain ⟨hs, hall⟩ := firingOfEqs_bind h.symm
      refine ⟨_, hs, hall, fun v hv => storeVars_saturate hwf c ?_⟩
      have heqv := (hwf ρ hρ).2; rw [hb] at heqv
      simp only [Eqns.vars, instEqs, List.flatMap_map, List.mem_flatMap,
        List.mem_append] at hv
      obtain ⟨e, he, hv⟩ := hv
      rcases hv with hv | hv
      · exact vars_body_sub hr (fun w hw => heqv e he w (List.mem_append_left _ hw)) hv
      · exact vars_body_sub hr (fun w hw => heqv e he w (List.mem_append_right _ hw)) hv

/-- A forced instantiation removes a variable from the store. -/
theorem varCount_inst_lt {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {s : Span}
    {θ : Nat → Pat} (h : T.bind? s.c = some θ) :
    (s.inst θ).c.varCount < s.c.varCount := by
  obtain ⟨E, hs, hall, hv⟩ := bind_solve hwf s.c h
  obtain ⟨i1, i2, i3⟩ := solve_vars E θ hs
  obtain ⟨x, hxE, hx⟩ := i3 hall
  rw [varCount_eq, varCount_eq]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨x, hv x hxE, ?_⟩
  · intro u hu
    obtain ⟨a, ha, hu⟩ := mem_storeVars.1 hu
    simp only [Span.inst, List.mem_eraseDups, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨w, hw, hu⟩ := vars_bind_mem hu
    by_cases hwE : w ∈ Eqns.vars E
    · exact hv u (i2 w hwE u hu)
    · rw [i1 w hwE] at hu; simp [vars] at hu; subst hu
      exact mem_storeVars.2 ⟨b, hb, hw⟩
  · intro hxs
    obtain ⟨a, ha, hxa⟩ := mem_storeVars.1 hxs
    simp only [Span.inst, List.mem_eraseDups, List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    obtain ⟨w, -, hxw⟩ := vars_bind_mem hxa
    exact hx w hxw

/-- A store without variables has no forced equation. -/
theorem bind_none_of_ground {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {c : Store}
    (h0 : c.varCount = 0) : T.bind? c = none := by
  cases hb : T.bind? c with
  | none => rfl
  | some θ =>
    obtain ⟨E, hs, hall, hv⟩ := bind_solve hwf c hb
    obtain ⟨x, hxE, -⟩ := (solve_vars E θ hs).2.2 hall
    rw [varCount_eq, Finset.card_eq_zero] at h0
    have := hv x hxE; rw [h0] at this; simp at this

/-! ## `simplify_stable` -/

theorem simplifyWithin_stable {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) :
    ∀ (n : Nat) (s s' : Span), s.c.varCount ≤ n → T.simplifyWithin n s = some s' →
      T.refutes? s'.c = false ∧ T.bind? s'.c = none := by
  intro n
  induction n with
  | zero =>
    intro s s' hn h
    cases hr : T.refutes? s.c
    · rw [sw_done hr (Or.inl rfl)] at h; cases h
      exact ⟨by rw [← hr]; exact refutes_congr T (by simp [List.mem_eraseDups]),
        bind_none_congr T (c := s.c) (by simp [List.mem_eraseDups])
          (bind_none_of_ground hwf (by omega))⟩
    · rw [sw_refuted hr] at h; cases h
  | succ n ih =>
    intro s s' hn h
    cases hr : T.refutes? s.c
    · cases hb : T.bind? s.c with
      | some θ =>
        rw [sw_bind hr hb] at h
        exact ih _ s' (by have := varCount_inst_lt hwf hb; omega) h
      | none =>
        rw [sw_done hr (Or.inr hb)] at h; cases h
        exact ⟨by rw [← hr]; exact refutes_congr T (by simp [List.mem_eraseDups]),
          bind_none_congr T (by simp [List.mem_eraseDups]) hb⟩
    · rw [sw_refuted hr] at h; cases h

end Checker

theorem R001.refutes_sound : R001.Obligation.refutes_sound := by
  intro T c hwf h σ M hM hc
  exact Checker.refutes_ground hwf hM σ c h hc

theorem R001.simplify_exact : R001.Obligation.simplify_exact :=
  fun _ s hwf => Checker.simplifyWithin_exact hwf _ s

theorem R001.present_exact : R001.Obligation.present_exact :=
  fun _ s hwf _ hM => Checker.denAt_store fun σ => Checker.normalize_holds hwf hM σ s.c

theorem R001.simplify_stable : R001.Obligation.simplify_stable := by
  intro T s s' hwf h
  exact Checker.simplifyWithin_stable hwf _ s s' le_rfl h

end RwLog
