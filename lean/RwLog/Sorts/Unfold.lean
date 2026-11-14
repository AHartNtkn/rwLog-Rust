/-
# The folded pattern is read off before unfolding

Replacing a variable whose values have one root by that root applied to new
variables is an unfolding of the store, and when no exclusion mentions the
variable the term it is replaced by is free in the store after
(`unfolding_stepAt`). So a store whose exclusions mention only variables
with two roots has the folded pattern of the store `tighten` makes of it
(`tighten_fold`), and the store assembled from it has the folded pattern of
the normal store of what it denotes (`foldPat_ofTight_norm`).
-/
import RwLog.Sorts.Fold
import RwLog.Sorts.Norm

namespace RwLog
namespace Sorts

open Function CStore

variable {S : Sorts}

/-! ## The links of one replacement -/

theorem expVar_vars (N n : Nat) (f : Sym) : (expVar N n f).vars = (List.range n).map (N + ·) := by
  simp only [expVar, Term.vars_mk, List.flatMap_map, Term.vars]
  induction List.range n with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem expVar_not_var (N n : Nat) (f : Sym) (x : Nat) : expVar N n f ≠ .var x := by
  intro e
  have := congrArg Term.spine e
  rw [expVar, Term.spine_mk] at this
  simp [Term.spine] at this

theorem linked_exp {s : Store} {N v : Nat} {f : Sym} {n : Nat} (hfin : s.Fin N)
    (hv : v ∈ s.t.vars) (hacc : Accepts S (s.c v) f n)
    (hroot : ∀ σ ∈ s.Sol S, ∃ gs, σ v = Term.mk f gs ∧ gs.length = n) :
    Linked S s (expStore S s N v f n) (Term.single v (expVar N n f)) where
  t := rfl
  down := fun _ hσ' => expStore_down hfin (hfin.tv v hv) hacc hσ'
  up := fun σ hσ => by
    obtain ⟨gs, e, hl⟩ := hroot σ hσ
    obtain ⟨σ', hσ', hlow, hu⟩ := expStore_up hfin (hfin.tv v hv) hσ e hl
    refine ⟨σ', hσ', fun w hw => ?_⟩
    by_cases hwv : w = v
    · subst hwv
      simpa [Term.single] using hu
    · simpa [Term.single, hwv] using hlow w (hfin.tv w hw)

theorem linked_set {s : Store} {v : Nat} {g : GTerm} (h₁ : MemC S (s.c v) g)
    (h₂ : ∀ u, MemC S (s.c v) u → u = g) :
    Linked S s (setStore s v g) (Term.single v (GTerm.toPat g)) where
  t := rfl
  down := fun _ hσ' => setStore_down h₁ hσ'
  up := fun σ hσ => ⟨σ, (setStore_up h₂ hσ).1, fun w _ => congrFun (setStore_up h₂ hσ).2 w⟩

/-- Replacing the listed variables that have one value is a substitution
that leaves the other variables alone and sends each variable to itself or to
a term without variables. -/
theorem linked_settle (S : Sorts) : ∀ (ws : List Nat) (s : CStore),
    ∃ γ : Nat → Pat, Linked S s.store (settle S s ws).store γ ∧
      (∀ x, x ∉ ws → γ x = .var x) ∧ ∀ x, γ x = .var x ∨ (γ x).vars = []
  | [], s => ⟨.var, Linked.refl S _, fun _ _ => rfl, fun _ => Or.inl rfl⟩
  | w :: ws, s => by
    have hrest : ∀ γ : Nat → Pat, (∀ x, x ∉ ws → γ x = .var x) →
        ∀ x, x ∉ w :: ws → γ x = .var x :=
      fun γ h x hx => h x fun hm => hx (List.mem_cons_of_mem _ hm)
    cases hc : count S (s.conj w) with
    | one g =>
      have e : settle S s (w :: ws) = settle S (s.set w g) ws := by simp only [settle, hc]
      rw [e]
      obtain ⟨γ, hγ, hid, hgr⟩ := linked_settle S ws (s.set w g)
      have h0 : Linked S s.store (s.set w g).store (Term.single w (GTerm.toPat g)) := by
        rw [set_store]
        exact linked_set (count_one.1 hc).1 (count_one.1 hc).2
      refine ⟨_, h0.trans hγ, fun x hx => ?_, fun x => ?_⟩
      · have hxw : x ≠ w := fun h => hx (h ▸ List.mem_cons_self)
        simp only [Term.single, hxw, ite_false, Term.bind]
        exact hrest γ hid x hx
      · by_cases hxw : x = w
        · right
          simp only [Term.single, hxw, ite_true]
          rw [Term.vars_bind_eq, toPat_vars]
          rfl
        · simp only [Term.single, hxw, ite_false, Term.bind]
          exact hgr x
    | none =>
      have e : settle S s (w :: ws) = settle S s ws := by simp only [settle, hc]
      rw [e]
      obtain ⟨γ, hγ, hid, hgr⟩ := linked_settle S ws s
      exact ⟨γ, hγ, hrest γ hid, hgr⟩
    | many =>
      have e : settle S s (w :: ws) = settle S s ws := by simp only [settle, hc]
      rw [e]
      obtain ⟨γ, hγ, hid, hgr⟩ := linked_settle S ws s
      exact ⟨γ, hγ, hrest γ hid, hgr⟩

theorem flatMap_vars_sublist {γ : Nat → Pat} (hgr : ∀ x, γ x = .var x ∨ (γ x).vars = []) :
    ∀ L : List Nat, (L.flatMap fun x => (γ x).vars).Sublist L
  | [] => List.Sublist.slnil
  | x :: L => by
    rw [List.flatMap_cons]
    rcases hgr x with e | e
    · rw [e]
      exact (flatMap_vars_sublist hgr L).cons_cons x
    · rw [e]
      exact (flatMap_vars_sublist hgr L).cons x

/-- One replacement is a substitution that leaves the other variables of the
pattern alone and sends the variable replaced to a term that is not a
variable, has no variable twice, and has only new variables. -/
theorem linked_stepAt {s : CStore} (hI : Inv S s) {v : Nat} {f : Sym} {n : Nat}
    (hv : v ∈ s.t.vars) (hsole : sole S (s.conj v) (gone s.x v) = some (f, n)) :
    ∃ τ : Nat → Pat, Linked S s.store (stepAt S s v (f, n)).store τ ∧
      (∀ w ∈ s.t.vars, w ≠ v → τ w = .var w) ∧ (∀ x, τ v ≠ .var x) ∧ (τ v).vars.Nodup ∧
      ∀ y ∈ (τ v).vars, y ∉ s.t.vars := by
  have hvN := hI.tv v hv
  obtain ⟨γ, hγ, hid, hgr⟩ :=
    linked_settle S ((List.range n).map (s.c.length + ·)) (s.exp S v f n)
  have h0 : Linked S s.store (s.exp S v f n).store (Term.single v (expVar s.c.length n f)) := by
    rw [s.exp_store hvN]
    exact linked_exp hI.fin hv (sole_accepts hsole) fun σ hσ =>
      key_eq_mk (sole_sound hsole (hσ.1 v) (not_mem_gone hσ.2 v))
  have hτv : (Term.single v (expVar s.c.length n f) v).bind γ =
      (expVar s.c.length n f).bind γ := by simp [Term.single]
  refine ⟨_, h0.trans hγ, fun w hw hwv => ?_, ?_, ?_, ?_⟩
  · simp only [Term.single, hwv, ite_false, Term.bind]
    refine hid w fun hm => ?_
    obtain ⟨i, -, e⟩ := List.mem_map.1 hm
    have := hI.tv w hw
    omega
  · rw [hτv]
    exact bind_not_var (expVar_not_var _ _ _) γ
  · rw [hτv, Term.vars_bind_eq, expVar_vars]
    exact (flatMap_vars_sublist hgr _).nodup
      (List.nodup_range.map fun a b (h : s.c.length + a = s.c.length + b) => by omega)
  · rw [hτv]
    intro y hy hys
    obtain ⟨w, hw, hyw⟩ := Term.mem_vars_bind.1 hy
    rcases hgr w with e | e
    · rw [e] at hyw
      simp only [Term.vars, List.mem_singleton] at hyw
      subst hyw
      have := hI.tv _ hys
      have := (mem_expVar_vars.1 hw).1
      omega
    · rw [e] at hyw
      cases hyw

/-! ## Exclusions on variables with two roots -/

theorem subst_of_not_mem {v : Nat} {u : Pat} {E : Eqns Nat} (h : v ∉ E.vars) :
    Eqns.subst v u E = E := by
  unfold Eqns.subst
  conv_rhs => rw [← List.map_id E]
  refine List.map_congr_left fun p hp => ?_
  have h1 : v ∉ p.1.vars := fun hm => h (List.mem_flatMap.2 ⟨p, hp, List.mem_append_left _ hm⟩)
  have h2 : v ∉ p.2.vars := fun hm => h (List.mem_flatMap.2 ⟨p, hp, List.mem_append_right _ hm⟩)
  rw [Term.bind_single_of_not_mem h1, Term.bind_single_of_not_mem h2]
  rfl

theorem map_subst_of_not_mem {v : Nat} {u : Pat} {X : List (Eqns Nat)}
    (h : ∀ E ∈ X, v ∉ E.vars) : X.map (Eqns.subst v u) = X := by
  conv_rhs => rw [← List.map_id X]
  exact List.map_congr_left fun E hE => subst_of_not_mem (h E hE)

/-- Replacing variables no exclusion mentions leaves the exclusions. -/
theorem settle_x (S : Sorts) : ∀ (ws : List Nat) (s : CStore),
    (∀ w ∈ ws, ∀ E ∈ s.x, w ∉ E.vars) → (settle S s ws).x = s.x
  | [], _, _ => rfl
  | w :: ws, s, h => by
    have hx : ∀ g, (s.set w g).x = s.x := fun g =>
      map_subst_of_not_mem (h w List.mem_cons_self)
    have hws : ∀ u ∈ ws, ∀ E ∈ s.x, u ∉ E.vars := fun u hu => h u (List.mem_cons_of_mem _ hu)
    cases hc : count S (s.conj w) with
    | one g =>
      have e : settle S s (w :: ws) = settle S (s.set w g) ws := by simp only [settle, hc]
      rw [e, settle_x S ws (s.set w g) (by rw [hx]; exact hws), hx]
    | none =>
      have e : settle S s (w :: ws) = settle S s ws := by simp only [settle, hc]
      rw [e]
      exact settle_x S ws s hws
    | many =>
      have e : settle S s (w :: ws) = settle S s ws := by simp only [settle, hc]
      rw [e]
      exact settle_x S ws s hws

/-- A replacement at a variable no exclusion mentions leaves the
exclusions. -/
theorem stepAt_x {s : CStore} (hI : Inv S s) {v : Nat} {key : Sym × Nat}
    (hvx : ∀ E ∈ s.x, v ∉ E.vars) : (stepAt S s v key).x = s.x := by
  have he : (s.exp S v key.1 key.2).x = s.x := map_subst_of_not_mem hvx
  unfold stepAt
  rw [settle_x, he]
  intro w hw E hE hm
  rw [he] at hE
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
  have := hI.tv _ (hI.xv E hE _ hm)
  omega

/-- A replacement leaves the sorts of the other variables of the pattern. -/
theorem stepAt_conj {s : CStore} (hI : Inv S s) {v : Nat} {f : Sym} {n : Nat} (hv : v ∈ s.t.vars)
    {u : Nat} (hu : u ∈ (stepAt S s v (f, n)).t.vars) (hut : u ∈ s.t.vars) (huv : u ≠ v) :
    (stepAt S s v (f, n)).conj u = s.conj u := by
  obtain ⟨-, -, -, -, -, h6, -⟩ :=
    settle_spec S ((List.range n).map (s.c.length + ·)) (s.exp S v f n)
  show (settle S (s.exp S v f n) _).conj u = _
  rw [(h6 u hu).2]
  have := congrArg (fun st : Store => st.c u) (s.exp_store (S := S) (hI.tv v hv) f n)
  have hlt := hI.tv u hut
  simpa [expStore, huv, CStore.store, Nat.not_le.2 hlt] using this

/-- A replacement in a store whose exclusions mention only variables with
two roots is at a variable no exclusion mentions, and leaves such a store. -/
theorem xtight_stepAt {s : CStore} (hI : Inv S s) (hX : XTight S s) {v : Nat} {f : Sym} {n : Nat}
    (hv : v ∈ s.t.vars) (hsole : sole S (s.conj v) (gone s.x v) = some (f, n)) :
    (∀ E ∈ s.x, v ∉ E.vars) ∧ XTight S (stepAt S s v (f, n)) := by
  have hvx : ∀ E ∈ s.x, v ∉ E.vars := fun E hE hm => by
    have := hX v hv ⟨E, hE, hm⟩
    rw [hsole] at this
    cases this
  have hxeq := stepAt_x (key := (f, n)) hI hvx
  refine ⟨hvx, fun u hu ⟨E, hE, hm⟩ => ?_⟩
  rw [hxeq] at hE
  have hut := hI.xv E hE u hm
  have huv : u ≠ v := fun e => hvx E hE (e ▸ hm)
  rw [hxeq, stepAt_conj hI hv hu hut huv]
  exact hX u hut ⟨E, hE, hm⟩

/-! ## The folded pattern along the replacements -/

/-- A replacement at a variable no exclusion mentions is an unfolding to a
free term, so it leaves the folded pattern. -/
theorem foldPat_stepAt (hS : S.WellFormed) {s : CStore} (hI : Inv S s) {v : Nat} {f : Sym}
    {n : Nat} (hv : v ∈ s.t.vars) (hsole : sole S (s.conj v) (gone s.x v) = some (f, n))
    (hvx : ∀ E ∈ s.x, v ∉ E.vars) :
    foldPat S (stepAt S s v (f, n)).store = foldPat S s.store := by
  obtain ⟨τ, hL, hid, happ, hlin, hfresh⟩ := linked_stepAt hI hv hsole
  have hinf : ({g | MemC S (s.conj v) g} \ {g | g ∈ gone s.x v}).Infinite :=
    (hI.infinite hS v).sdiff (List.finite_toSet _)
  obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ := hinf.nontrivial
  obtain ⟨σ₁, hσ₁, e₁⟩ := hI.exists_sol hS v hg₁.1 hg₁.2
  obtain ⟨σ₂, hσ₂, e₂⟩ := hI.exists_sol hS v hg₂.1 hg₂.2
  have hne' : (τ v).vars ≠ [] := hL.vars_ne hv hσ₁ hσ₂ (by rw [e₁, e₂]; exact hne)
  have hun : Unfolds s.t.vars τ := by
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw w' hw' y hy hy' => ?_⟩
    · by_cases e : w = v
      · rw [e]; exact hne'
      · rw [hid w hw e]; simp [Term.vars]
    · by_cases e : w = v
      · rw [e]; exact hlin
      · rw [hid w hw e]; simp [Term.vars]
    · by_cases e : w = v
      · by_cases e' : w' = v
        · rw [e, e']
        · rw [e] at hy
          rw [hid w' hw' e'] at hy'
          simp only [Term.vars, List.mem_singleton] at hy'
          exact absurd hw' (hy' ▸ hfresh y hy)
      · rw [hid w hw e] at hy
        simp only [Term.vars, List.mem_singleton] at hy
        by_cases e' : w' = v
        · rw [e'] at hy'
          exact absurd hw (hy ▸ hfresh y hy')
        · rw [hid w' hw' e'] at hy'
          simp only [Term.vars, List.mem_singleton] at hy'
          exact hy.symm.trans hy'
  refine foldPat_bind ⟨hL, hun⟩ (fun w hw hnv => ?_) hI.fo
  by_cases e : w = v
  · rw [e]
    exact hL.free hv hid (fun E hE p hp hm => hvx E hE (List.mem_flatMap.2 ⟨p, hp, hm⟩)) hI.fo
      happ hne' hlin hfresh
  · exact absurd (hid w hw e) (hnv w)

/-- A store whose exclusions mention only variables with two roots has the
folded pattern of the store `tighten` makes of it. -/
theorem tighten_fold (hS : S.WellFormed) : ∀ (k : Nat) (s : CStore), room S s = k → Inv S s →
    XTight S s → ∃ s', tighten S hS s = some s' ∧ foldPat S s'.store = foldPat S s.store := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hk hI hX
    rw [tighten]
    split
    · split
      · rename_i s₁ hs
        obtain ⟨v, ⟨f, n⟩, hv, hsole, rfl⟩ := step?_eq hs
        obtain ⟨hvx, hX₁⟩ := xtight_stepAt hI hX hv hsole
        obtain ⟨hden, -, hK⟩ := stepAt_spec hI hv hsole
        have hI₁ : Inv S (stepAt S s v (f, n)) := by
          by_contra hn
          have := den_empty_of_not_inv hK hn
          rw [hden] at this
          exact (hI.nonempty hS).ne_empty this
        obtain ⟨s', h1, h2⟩ := ih _ (hk ▸ room_lt hS hI hs) _ rfl hI₁ hX₁
        exact ⟨s', h1, h2.trans (foldPat_stepAt hS hI hv hsole hvx)⟩
      · exact ⟨s, rfl, rfl⟩
    · rename_i hn
      exact absurd hI hn

/-- The store assembled from a store has the folded pattern of the store. -/
theorem foldPat_ofTight (hS : S.WellFormed) {s : CStore} (hI : Inv S s) :
    foldPat S (ofTight S s).store = foldPat S s.store := by
  obtain ⟨-, hsol, -, -⟩ := ofTight_shaped hS hI
  have ht : (ofTight S s).store.t = (s.store.ren (fun v => (firsts s.t.vars).idxOf v)
      fun w => (firsts s.t.vars).getD w 0).t := rfl
  refine (foldPat_congr ht hsol).trans ?_
  exact foldPat_ren hI.full (fun v hv => ((renum_spec s.t.vars).2.1 v hv).2) hI.fo

/-- The store assembled from a store whose exclusions mention only variables
with two roots is determined by its pattern and what it denotes, denotes
what the normal store of the problem does, and has its folded pattern. -/
theorem foldPat_ofTight_norm (hS : S.WellFormed) {s : CStore} (hI : Inv S s) (hX : XTight S s)
    {P : Prob} (hP : P.FO) (hden : s.store.Den S = P.Den S) :
    ∃ n, P.norm S hS = some n ∧ (ofTight S s).Shaped S ∧
      (ofTight S s).store.Den S = n.store.Den S ∧
      foldPat S (ofTight S s).store = foldPat S n.store := by
  obtain ⟨s', ht, hf⟩ := tighten_fold hS _ s rfl hI hX
  obtain ⟨hd', hI', hsole'⟩ := tighten_some hS _ s s' rfl ht
  obtain ⟨hN, hD⟩ := ofTight_normal hS hI' hsole'
  obtain ⟨hsh, -, hD₀, -⟩ := ofTight_shaped hS hI
  refine ⟨ofTight S s', Prob.norm_unique hS hP hN (hD.trans (hd'.trans hden)), hsh, ?_, ?_⟩
  · rw [hD₀, hD, hd']
  · rw [foldPat_ofTight hS hI, foldPat_ofTight hS hI', hf]

end Sorts
end RwLog
