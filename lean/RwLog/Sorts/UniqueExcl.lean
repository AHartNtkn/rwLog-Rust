/-
# Two normal stores with the same denotation are equal

What is left after `Sorts/Unique.lean` is the exclusions. What a normal
exclusion removes is laid out by its free variables: each ranges over
infinitely many values, independently of the others (`rect`), and the bound
variables follow. Independence then gives two facts.

* What one normal exclusion removes is never covered by finitely many others
  unless one of them covers it alone (`irreducible`).
* Two normal exclusions that remove the same substitutions are the same list
  of bindings (`eq_of_ex_eq`).

So the exclusions of two normal stores with the same solutions remove the same
sets one for one, and are the same lists.
-/
import RwLog.Sorts.Unique

namespace RwLog
namespace Sorts

open Function

/-- Two different patterns have different instances under some substitution. -/
theorem exists_sep {u w : Pat} (h : u ≠ w) : ∃ τ : Nat → GTerm, u.bind τ ≠ w.bind τ := by
  have hu : ∀ f ∈ u.syms, f.length < Fresh.lenBound (u.syms ++ w.syms) :=
    fun f hf => Fresh.lt_lenBound (by simp [hf])
  have hw : ∀ f ∈ w.syms, f.length < Fresh.lenBound (u.syms ++ w.syms) :=
    fun f hf => Fresh.lt_lenBound (by simp [hf])
  exact ⟨frz _, fun e => h (by rw [← thaw_frz u hu, e, thaw_frz w hw])⟩

namespace Pre

variable {k : Nat} {θ : Binds}

/-- The variables of the value of a variable under a normal exclusion are
free. -/
theorem apply_free (hθ : Pre k θ) (v : Nat) :
    ∀ y ∈ (PSubst.apply θ v).vars, ∀ b ∈ θ, b.1 ≠ y := by
  intro y hy
  rcases apply_cases θ v with e | hm
  · rw [e] at hy
    simp only [Term.vars, List.mem_singleton] at hy
    subst hy
    intro b hb hby
    have hb2 : b.2 = .var b.1 := by rw [← apply_of_mem hθ.sorted hb, hby, e]
    exact (hθ.ran b hb b.1 (by simp [hb2, Term.vars])).2 b hb rfl
  · exact (hθ.ran _ hm y hy).2

theorem apply_lt (hθ : Pre k θ) {v : Nat} (hv : v < k) :
    ∀ y ∈ (PSubst.apply θ v).vars, y < k := by
  intro y hy
  rcases apply_cases θ v with e | hm
  · rw [e] at hy
    simp only [Term.vars, List.mem_singleton] at hy
    subst hy; exact hv
  · exact (hθ.ran _ hm y hy).1

theorem apply_fo (hθ : Pre k θ) (v : Nat) : (PSubst.apply θ v).firstOrder = true := by
  rcases apply_cases θ v with e | hm
  · rw [e]; rfl
  · exact hθ.fo _ hm

theorem apply_ge (hθ : Pre k θ) {v : Nat} (hv : k ≤ v) :
    PSubst.apply θ v = .var v :=
  apply_of_not_mem fun b hb e => by have := hθ.dom b hb; omega

/-- A pattern over free variables is not changed by the exclusion. -/
theorem bind_apply_of_free {q : Pat} (h : ∀ y ∈ q.vars, ∀ b ∈ θ, b.1 ≠ y) (τ : Nat → GTerm) :
    q.bind (fun v => (PSubst.apply θ v).bind τ) = q.bind τ :=
  Term.bind_congr fun y hy => by rw [apply_of_not_mem (h y hy)]; rfl

end Pre

namespace NormalBinds

variable {S : Sorts} {r : Raw} {θ θ' : Binds}

open Classical in
/-- The declared sorts that hold of every value a variable takes among the
substitutions the exclusion removes. -/
noncomputable def up (S : Sorts) (r : Raw) (θ : Binds) (y : Nat) : Conj :=
  (names S).filter fun n => ∀ σ ∈ r.Ex S θ, mem S n (σ y) = true

theorem mem_up_of_ex {σ : Nat → GTerm} (hσ : σ ∈ r.Ex S θ) (y : Nat) :
    MemC S (up S r θ y) (σ y) := by
  intro n hn
  simp only [up, Finset.mem_filter] at hn
  exact hn.2 σ hσ

/-- The substitutions an exclusion removes are laid out by the values of its
free variables, each taken freely among the values it takes at all. -/
theorem rect (hθ : NormalBinds S r θ) {τ : Nat → GTerm}
    (hτ : ∀ y, MemC S (up S r θ y) (τ y)) :
    (fun v => (PSubst.apply θ v).bind τ) ∈ r.Ex S θ := by
  obtain ⟨σb, hσb⟩ := hθ.live
  have hF := unifies_eqnsOf hθ.sorted
  refine ⟨fun v n hn => ?_, (hF _).2 fun v => ?_⟩
  · have hall : ∀ σ ∈ r.Ex S θ, mem S n ((PSubst.apply θ v).bind σ) = true := by
      intro σ hσ
      rw [← (hF σ).1 hσ.2 v]; exact hσ.1 v n hn
    cases hp : push S n (PSubst.apply θ v) with
    | none =>
      have := push_none (hθ.apply_fo v) hp σb
      rw [hall σb hσb] at this; cases this
    | some as =>
      refine (push_some (hθ.apply_fo v) hp τ).2 fun a ha => ?_
      have hmem : ∀ σ ∈ r.Ex S θ, mem S a.2 (σ a.1) = true :=
        fun σ hσ => (push_some (hθ.apply_fo v) hp σ).1 (hall σ hσ) a ha
      refine hτ a.1 a.2 ?_
      simp only [up, Finset.mem_filter]
      refine ⟨?_, hmem⟩
      by_contra hn'
      have := mem_false_of_not_names hn' (σb a.1)
      rw [hmem σb hσb] at this; cases this
  · exact (Pre.bind_apply_of_free (hθ.apply_free v) τ).symm

/-- A free variable of a normal exclusion takes infinitely many values. -/
theorem up_infinite (hS : S.WellFormed) (hθ : NormalBinds S r θ) {y : Nat} (hy : y < r.c.length)
    (hfree : ∀ b ∈ θ, b.1 ≠ y) : {g | MemC S (up S r θ y) g}.Infinite := by
  obtain ⟨σ, hσ, σ', hσ', hne⟩ := hθ.loose y hy hfree
  exact conj_infinite hS _ (mem_up_of_ex hσ y) (mem_up_of_ex hσ' y) hne

/-- Independence among what a normal exclusion removes: finitely many lists
of equations over the variables of the store, each failing somewhere in the
layout of the exclusion, all fail at one substitution it removes. -/
theorem rich (hS : S.WellFormed) (hθ : NormalBinds S r θ) (X : List (Eqns Nat))
    (hX : ∀ E ∈ X, (∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, v < r.c.length) ∧
      ∃ τ : Nat → GTerm, ¬ Eqns.Unifies (fun v => (PSubst.apply θ v).bind τ) E) :
    ∃ σ ∈ r.Ex S θ, ∀ E ∈ X, ¬ Eqns.Unifies σ E := by
  obtain ⟨σb, hσb⟩ := hθ.live
  let tr : Eqns Nat → Eqns Nat := fun E =>
    E.map fun p => (p.1.bind (PSubst.apply θ), p.2.bind (PSubst.apply θ))
  have htr : ∀ (E : Eqns Nat) (τ : Nat → GTerm),
      Eqns.Unifies τ (tr E) ↔ Eqns.Unifies (fun v => (PSubst.apply θ v).bind τ) E := by
    intro E τ
    simp only [Eqns.Unifies, tr, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro h p hp
      have := h _ p hp rfl
      simpa [Term.bind_bind] using this
    · rintro h _ p hp rfl
      have := h p hp
      simpa [Term.bind_bind] using this
  let H : List Nat := (List.range r.c.length).filter fun y => ∀ b ∈ θ, b.1 ≠ y
  have hH : ∀ y, y ∈ H ↔ y < r.c.length ∧ ∀ b ∈ θ, b.1 ≠ y := by
    intro y; simp [H]
  obtain ⟨τ, hτ, -, -⟩ := Store.rich (S := S) ⟨.sym "", up S r θ, X.map tr⟩ H
    (fun h hh => hθ.up_infinite hS ((hH h).1 hh).1 ((hH h).1 hh).2) σb
    (fun v _ => mem_up_of_ex hσb v) []
    (by
      intro E' hE'
      obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
      obtain ⟨hvars, τ₁, hτ₁⟩ := hX E hE
      refine ⟨fun v => if v ∈ H then τ₁ v else σb v, fun v hv => by simp [hv], ?_⟩
      rw [htr]
      intro hu
      apply hτ₁
      refine unifies_congr (fun p hp v hv => ?_) hu
      refine Term.bind_congr fun y hy => ?_
      have hyH : y ∈ H := (hH y).2 ⟨hθ.apply_lt (hvars p hp v hv) y hy, hθ.apply_free v y hy⟩
      simp [hyH])
    (by simp)
  refine ⟨_, hθ.rect hτ.1, ?_⟩
  intro E hE hu
  exact hτ.2 (tr E) (List.mem_map.2 ⟨E, hE, rfl⟩) ((htr E τ).2 hu)

/-- What a normal exclusion removes is covered by finitely many exclusions
only if one of them covers it. -/
theorem irreducible (hS : S.WellFormed) (hθ : NormalBinds S r θ) (X : List Binds)
    (hX : ∀ θ₂ ∈ X, NormalBinds S r θ₂)
    (hcov : ∀ σ ∈ r.Ex S θ, ∃ θ₂ ∈ X, Eqns.Unifies σ (eqnsOf θ₂)) :
    ∃ θ₂ ∈ X, r.Ex S θ ⊆ r.Ex S θ₂ := by
  by_contra hno
  have hno' : ∀ θ₂ ∈ X, ∃ σ ∈ r.Ex S θ, ¬ Eqns.Unifies σ (eqnsOf θ₂) := by
    intro θ₂ hθ₂
    by_contra h
    exact hno ⟨θ₂, hθ₂, fun σ hσ => ⟨hσ.1, by_contra fun hu => h ⟨σ, hσ, hu⟩⟩⟩
  obtain ⟨σ, hσ, hσX⟩ := hθ.rich hS (X.map eqnsOf) (by
    intro E hE
    obtain ⟨θ₂, hθ₂, rfl⟩ := List.mem_map.1 hE
    refine ⟨?_, ?_⟩
    · intro p hp v hv
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
      simp only [Term.vars, List.cons_append, List.nil_append, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact (hX θ₂ hθ₂).dom b hb
      · exact ((hX θ₂ hθ₂).ran b hb v hv).1
    · obtain ⟨σ₂, hσ₂, hne⟩ := hno' θ₂ hθ₂
      refine ⟨σ₂, fun hu => hne ?_⟩
      have e : (fun v => (PSubst.apply θ v).bind σ₂) = σ₂ :=
        funext fun v => ((unifies_eqnsOf hθ.sorted σ₂).1 hσ₂.2 v).symm
      rwa [e] at hu)
  obtain ⟨θ₂, hθ₂, hu⟩ := hcov σ hσ
  exact hσX _ (List.mem_map.2 ⟨θ₂, hθ₂, rfl⟩) hu

/-- If everything one normal exclusion removes is removed by another, the
first is an instance of the second. -/
theorem apply_eq_of_subset (hS : S.WellFormed) (hθ : NormalBinds S r θ)
    (hθ' : NormalBinds S r θ') (hsub : r.Ex S θ ⊆ r.Ex S θ') (x : Nat) :
    PSubst.apply θ x = (PSubst.apply θ' x).bind (PSubst.apply θ) := by
  by_cases hx : x < r.c.length
  · by_contra hne
    have hfree₁ := hθ.apply_free x
    have hfree₂ : ∀ y ∈ ((PSubst.apply θ' x).bind (PSubst.apply θ)).vars, ∀ b ∈ θ, b.1 ≠ y := by
      intro y hy
      obtain ⟨z, -, hz⟩ := Term.vars_bind_mem hy
      exact hθ.apply_free z y hz
    obtain ⟨τ₁, hτ₁⟩ := exists_sep hne
    obtain ⟨σ, hσ, hσX⟩ := hθ.rich hS
      [[(PSubst.apply θ x, (PSubst.apply θ' x).bind (PSubst.apply θ))]] (by
        intro E hE
        rw [List.mem_singleton] at hE; subst hE
        refine ⟨?_, τ₁, ?_⟩
        · intro p hp v hv
          rw [List.mem_singleton] at hp; subst hp
          rcases List.mem_append.1 hv with hv | hv
          · exact hθ.apply_lt hx v hv
          · obtain ⟨z, hz, hvz⟩ := Term.vars_bind_mem hv
            exact hθ.apply_lt (hθ'.apply_lt hx z hz) v hvz
        · intro hu
          have := hu _ (List.mem_singleton.2 rfl)
          rw [Pre.bind_apply_of_free hfree₁, Pre.bind_apply_of_free hfree₂] at this
          exact hτ₁ this)
    apply hσX _ (List.mem_singleton.2 rfl)
    intro p hp
    rw [List.mem_singleton] at hp; subst hp
    have h₁ := (unifies_eqnsOf hθ.sorted σ).1 hσ.2
    have h₂ := (unifies_eqnsOf hθ'.sorted σ).1 (hsub hσ).2 x
    show (PSubst.apply θ x).bind σ = ((PSubst.apply θ' x).bind (PSubst.apply θ)).bind σ
    rw [← h₁ x, Term.bind_bind, h₂]
    exact Term.bind_congr fun v _ => h₁ v
  · have hx' : r.c.length ≤ x := Nat.le_of_not_lt hx
    rw [hθ.apply_ge hx', hθ'.apply_ge hx']
    simp [hθ.apply_ge hx']

/-- If two normal exclusions each remove what the other removes, every
variable bound by one is bound by the other. -/
theorem dom_of_subset (hS : S.WellFormed) (hθ : NormalBinds S r θ) (hθ' : NormalBinds S r θ')
    (h₁ : r.Ex S θ ⊆ r.Ex S θ') {b' : Nat × Pat} (hb' : b' ∈ θ') :
    ∃ b ∈ θ, b.1 = b'.1 := by
  by_contra hno
  have hfree : ∀ b ∈ θ, b.1 ≠ b'.1 := fun b hb e => hno ⟨b, hb, e⟩
  have e := hθ.apply_eq_of_subset hS hθ' h₁ b'.1
  rw [apply_of_not_mem hfree, apply_of_mem hθ'.sorted hb'] at e
  -- the value of `b'` is a variable `y` that `θ` sends to the variable of `b'`
  cases hb2 : b'.2 with
  | sym f => rw [hb2] at e; simp at e
  | app a c => rw [hb2] at e; simp at e
  | var y =>
    rw [hb2] at e
    simp only [Term.bind_var] at e
    have hy : y < b'.1 := hθ'.later b' hb' y hb2
    rcases apply_cases θ y with e' | hm
    · rw [e'] at e
      simp only [Term.var.injEq] at e
      omega
    · rw [← e] at hm
      have := hθ.later _ hm b'.1 rfl
      simp only at this
      omega

/-- Two normal exclusions that remove the same substitutions are equal. -/
theorem eq_of_ex_eq (hS : S.WellFormed) (hθ : NormalBinds S r θ) (hθ' : NormalBinds S r θ')
    (h : r.Ex S θ = r.Ex S θ') : θ = θ' := by
  have key : ∀ {α β : Binds}, NormalBinds S r α → NormalBinds S r β → r.Ex S α = r.Ex S β →
      ∀ b ∈ β, b ∈ α := by
    intro α β hα hβ hE b hb
    obtain ⟨a, ha, hab⟩ := hα.dom_of_subset hS hβ (hE ▸ Set.Subset.refl _) hb
    have e := hα.apply_eq_of_subset hS hβ (hE ▸ Set.Subset.refl _) b.1
    rw [← hab, apply_of_mem hα.sorted ha, hab, apply_of_mem hβ.sorted hb] at e
    -- the variables of `b.2` are free in `β`, so in `α`
    have hfix : b.2.bind (PSubst.apply α) = b.2 := by
      conv_rhs => rw [← Term.bind_var_id b.2]
      refine Term.bind_congr fun v hv => apply_of_not_mem fun a' ha' ea => ?_
      obtain ⟨b₂, hb₂, hb₂e⟩ := hβ.dom_of_subset hS hα (hE ▸ Set.Subset.refl _) ha'
      exact (hβ.ran b hb v hv).2 b₂ hb₂ (hb₂e.trans ea)
    rw [hfix] at e
    have : a = b := Prod.ext hab e
    rw [← this]; exact ha
  have : Std.Irrefl (fun a b : Nat × Pat => a.1 < b.1) := ⟨fun a => Nat.lt_irrefl _⟩
  have : Std.Antisymm (fun a b : Nat × Pat => a.1 < b.1) :=
    ⟨fun a b h₁ h₂ => absurd h₁ (Nat.lt_asymm h₂)⟩
  exact List.Pairwise.eq_of_mem_iff hθ.sorted hθ'.sorted
    fun b => ⟨key hθ' hθ h.symm b, key hθ hθ' h b⟩

end NormalBinds

namespace Raw.Normal

variable {S : Sorts}

/-- The exclusions of one normal store are among those of another with the
same sorts and the same solutions. -/
theorem x_subset (hS : S.WellFormed) {t t' : Pat} {c : List Conj} {x x' : Finset Binds}
    (hr : Raw.Normal S ⟨t, c, x⟩) (hr' : Raw.Normal S ⟨t', c, x'⟩)
    (hsol : (Raw.store ⟨t, c, x⟩).Sol S = (Raw.store ⟨t', c, x'⟩).Sol S) :
    ∀ θ' ∈ x', θ' ∈ x := by
  have tr : ∀ {θ : Binds}, NormalBinds S ⟨t', c, x'⟩ θ → NormalBinds S ⟨t, c, x⟩ θ :=
    fun h => ⟨h.toPre, h.ne, h.live, h.loose⟩
  have tr' : ∀ {θ : Binds}, NormalBinds S ⟨t, c, x⟩ θ → NormalBinds S ⟨t', c, x'⟩ θ :=
    fun h => ⟨h.toPre, h.ne, h.live, h.loose⟩
  -- what an exclusion of one store removes is covered by the exclusions of the other
  have cover : ∀ {u u' : Pat} {y y' : Finset Binds},
      (Raw.store ⟨u, c, y⟩).Sol S = (Raw.store ⟨u', c, y'⟩).Sol S → ∀ θ' ∈ y',
      ∀ σ ∈ Raw.Ex S ⟨u, c, y⟩ θ', ∃ θ ∈ y, Eqns.Unifies σ (eqnsOf θ) := by
    intro u u' y y' hs θ' hθ' σ hσ
    have hnot : σ ∉ (Raw.store ⟨u', c, y'⟩).Sol S :=
      fun h => h.2 _ (Raw.mem_store_x.2 ⟨θ', hθ', rfl⟩) hσ.2
    rw [← hs] at hnot
    by_contra hno
    apply hnot
    refine ⟨hσ.1, ?_⟩
    intro E hE hu
    obtain ⟨θ, hθ, rfl⟩ := Raw.mem_store_x.1 hE
    exact hno ⟨θ, hθ, hu⟩
  intro θ' hθ'
  have hn' := hr'.ex θ' hθ'
  obtain ⟨θ, hθ, h₁⟩ := (tr hn').irreducible hS x.toList
    (fun θ₂ h₂ => hr.ex θ₂ (Finset.mem_toList.1 h₂))
    (fun σ hσ => by simpa using cover hsol θ' hθ' σ hσ)
  rw [Finset.mem_toList] at hθ
  have hn := hr.ex θ hθ
  obtain ⟨θ'', hθ'', h₂⟩ := (tr' hn).irreducible hS x'.toList
    (fun θ₂ h₂ => hr'.ex θ₂ (Finset.mem_toList.1 h₂))
    (fun σ hσ => by simpa using cover hsol.symm θ hθ σ hσ)
  rw [Finset.mem_toList] at hθ''
  have e : θ' = θ'' := hr'.anti θ' hθ' θ'' hθ'' (fun σ hσ => h₂ (h₁ hσ))
  subst e
  have : θ = θ' := hn.eq_of_ex_eq hS (tr hn') (Set.Subset.antisymm h₂ h₁)
  rw [← this]; exact hθ

/-- Two normal stores with the same denotation are equal. -/
theorem eq (hS : S.WellFormed) {r r' : Raw} (hr : r.Normal S) (hr' : r'.Normal S)
    (hden : r.store.Den S = r'.store.Den S) : r = r' := by
  have ht := t_eq hS hr hr' hden
  have hc := c_eq hS hr hr' hden
  have hsol := sol_eq hS hr hr' hden
  obtain ⟨t, c, x⟩ := r
  obtain ⟨t', c', x'⟩ := r'
  simp only at ht hc
  subst ht hc
  have hx : x = x' := Finset.ext fun θ =>
    ⟨x_subset hS hr' hr hsol.symm θ, x_subset hS hr hr' hsol θ⟩
  rw [hx]

end Raw.Normal

end Sorts
end RwLog
