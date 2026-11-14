/-
# The folded pattern of a store

The normal store (`Raw.Normal`) replaces every variable whose values have one
root by that root applied to new variables. That makes two stores with the
same denotation equal, and it makes a store as large as the values are deep:
a variable of a sort with one rule is written out as the rule, and so on down.

This file says which subterms of a pattern need not be written out. A
subterm is *free* (`Free`) when it is not a variable, has a variable, has no
variable twice, its variables occur nowhere else in the pattern, and its
values are exactly the members of some sorts whatever the other variables
are. The *folded pattern* (`foldPat`) has one variable in place of each
outermost free subterm, numbered in the order they first occur.

The folded pattern does not change when a store is unfolded
(`foldPat_bind`): if one store is another with its variables replaced by
terms that share no variable, each a variable or free, and the solutions
correspond, the two have the same folded pattern. Renaming the variables and
replacing a variable by its root applied to new variables are both of this
kind, so the folded pattern is a function of the normal store, and of what a
store denotes.

A store determined by its pattern and denotation (`Raw.Shaped`) whose
pattern is the folded pattern of the normal store is therefore unique
(`FoldOf.eq`), and two normal stores with the same folded store are equal
(`FoldOf.inj`).
-/
import RwLog.Sorts.UniqueExcl
import RwLog.Sorts.Renum
import RwLog.Lib.Firsts
import RwLog.Sorts.FO

namespace RwLog
namespace Sorts

open Function

/-! ## Terms under a substitution -/

theorem Term.vars_bind_eq {V W : Type} (σ : V → Term W) :
    ∀ t : Term V, (t.bind σ).vars = t.vars.flatMap fun v => (σ v).vars
  | .var v => by simp [Term.bind, Term.vars]
  | .sym _ => by simp [Term.bind, Term.vars]
  | .app a b => by
    simp [Term.bind, Term.vars, Term.vars_bind_eq σ a, Term.vars_bind_eq σ b]

theorem Term.mem_vars_bind {V W : Type} {σ : V → Term W} {t : Term V} {y : W} :
    y ∈ (t.bind σ).vars ↔ ∃ v ∈ t.vars, y ∈ (σ v).vars := by
  rw [Term.vars_bind_eq, List.mem_flatMap]

theorem Term.size_bind_le {V W : Type} (σ : V → Term W) :
    ∀ {t : Term V} {v : V}, v ∈ t.vars → (σ v).size ≤ (t.bind σ).size
  | .var w, v, h => by
    simp only [Term.vars, List.mem_singleton] at h
    subst h
    exact Nat.le_refl _
  | .sym _, v, h => by simp [Term.vars] at h
  | .app a b, v, h => by
    simp only [Term.vars, List.mem_append] at h
    simp only [Term.bind, Term.size]
    rcases h with h | h
    · have := Term.size_bind_le σ h; omega
    · have := Term.size_bind_le σ h; omega

theorem Term.size_bind_lt {V W : Type} (σ : V → Term W) {t : Term V} {v : V} (hv : v ∈ t.vars)
    (hnv : ∀ x, t ≠ .var x) : (σ v).size < (t.bind σ).size := by
  cases t with
  | var w => exact absurd rfl (hnv w)
  | sym _ => simp [Term.vars] at hv
  | app a b =>
    simp only [Term.vars, List.mem_append] at hv
    simp only [Term.bind, Term.size]
    rcases hv with h | h
    · have := Term.size_bind_le σ h; omega
    · have := Term.size_bind_le σ h; omega

/-! ## Substitutions that unfold -/

/-- The substitution sends the variables of `D` to terms that each have a
variable, have none twice, and share none with each other. -/
structure Unfolds (D : List Nat) (τ : Nat → Pat) : Prop where
  ne : ∀ v ∈ D, (τ v).vars ≠ []
  lin : ∀ v ∈ D, (τ v).vars.Nodup
  disj : ∀ v ∈ D, ∀ w ∈ D, ∀ y, y ∈ (τ v).vars → y ∈ (τ w).vars → v = w

namespace Unfolds

variable {D : List Nat} {τ : Nat → Pat}

/-- The value of a variable is not the image of a term that is not a
variable. -/
theorem var_ne (h : Unfolds D τ) {x : Nat} (hx : x ∈ D) {q : Pat} (hq : ∀ v ∈ q.vars, v ∈ D)
    (hnv : ∀ y, q ≠ .var y) : τ x ≠ q.bind τ := by
  intro e
  by_cases hxq : x ∈ q.vars
  · have := Term.size_bind_lt τ hxq hnv
    rw [← e] at this
    exact Nat.lt_irrefl _ this
  · cases hl : (τ x).vars with
    | nil => exact h.ne x hx hl
    | cons y _ =>
      have hy : y ∈ (τ x).vars := by rw [hl]; exact List.mem_cons_self
      have hy' := hy
      rw [e, Term.mem_vars_bind] at hy'
      obtain ⟨w, hw, hyw⟩ := hy'
      have := h.disj x hx w (hq w hw) y hy hyw
      subst this
      exact hxq hw

/-- The substitution is one to one on terms over `D`. -/
theorem inj (h : Unfolds D τ) : ∀ {p q : Pat}, (∀ v ∈ p.vars, v ∈ D) → (∀ v ∈ q.vars, v ∈ D) →
    p.bind τ = q.bind τ → p = q
  | .var x, q, hp, hq, e => by
    have hx : x ∈ D := hp x (by simp [Term.vars])
    by_cases hnv : ∀ y, q ≠ .var y
    · exact absurd e (h.var_ne hx hq hnv)
    · rw [not_forall] at hnv
      obtain ⟨y, hy⟩ := hnv
      obtain rfl : q = .var y := not_not.1 hy
      have hyD : y ∈ D := hq y (by simp [Term.vars])
      simp only [Term.bind] at e
      cases hl : (τ x).vars with
      | nil => exact absurd hl (h.ne x hx)
      | cons z _ =>
        have hz : z ∈ (τ x).vars := by rw [hl]; exact List.mem_cons_self
        rw [h.disj x hx y hyD z hz (e ▸ hz)]
  | .sym f, q, _, hq, e => by
    cases q with
    | var y =>
      have hyD : y ∈ D := hq y (by simp [Term.vars])
      simp only [Term.bind] at e
      exact absurd (by rw [← e]; rfl) (h.ne y hyD)
    | sym g => simpa [Term.bind] using e
    | app a b => simp [Term.bind] at e
  | .app a b, q, hp, hq, e => by
    cases q with
    | var y =>
      have hyD : y ∈ D := hq y (by simp [Term.vars])
      exact absurd e.symm (h.var_ne hyD hp (by simp))
    | sym g => simp [Term.bind] at e
    | app a' b' =>
      simp only [Term.bind, Term.app.injEq] at e
      rw [h.inj (fun v hv => hp v (by simp [Term.vars, hv]))
          (fun v hv => hq v (by simp [Term.vars, hv])) e.1,
        h.inj (fun v hv => hp v (by simp [Term.vars, hv]))
          (fun v hv => hq v (by simp [Term.vars, hv])) e.2]

end Unfolds

/-! ## The places outside a subterm -/

/-- The variables at the places of a term that are not inside an argument
equal to `u`. -/
def outF (u : Pat) : Pat → List Nat
  | .var x => [x]
  | .sym _ => []
  | .app g b => outF u g ++ (if b = u then [] else outF u b)

/-- The variables at the places of a term that are not inside an occurrence
of `u`, as an argument or as the whole term. -/
def outV (u t : Pat) : List Nat := if t = u then [] else outF u t

theorem outF_sub (u : Pat) : ∀ (t : Pat) (y : Nat), y ∈ outF u t → y ∈ t.vars
  | .var x, y, h => by simpa [outF, Term.vars] using h
  | .sym _, y, h => by simp [outF] at h
  | .app g b, y, h => by
    simp only [outF, List.mem_append] at h
    simp only [Term.vars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (outF_sub u g y h)
    · by_cases hb : b = u
      · simp [hb] at h
      · rw [ite_eq_right hb] at h
        exact Or.inr (outF_sub u b y h)

theorem outV_sub (u t : Pat) (y : Nat) (h : y ∈ outV u t) : y ∈ t.vars := by
  unfold outV at h
  by_cases ht : t = u
  · simp [ht] at h
  · rw [ite_eq_right ht] at h
    exact outF_sub u t y h

/-- A term that lacks a variable of `u`, or is smaller than `u`, has no
argument equal to `u`. -/
theorem outF_eq_vars (u : Pat) : ∀ p : Pat, ((∃ y ∈ u.vars, y ∉ p.vars) ∨ p.size < u.size) →
    outF u p = p.vars
  | .var _, _ => rfl
  | .sym _, _ => rfl
  | .app g b, h => by
    have hg : (∃ y ∈ u.vars, y ∉ g.vars) ∨ g.size < u.size := by
      rcases h with ⟨y, hy, hn⟩ | h
      · exact Or.inl ⟨y, hy, fun hc => hn (by simp [Term.vars, hc])⟩
      · exact Or.inr (by simp only [Term.size] at h; omega)
    have hb : (∃ y ∈ u.vars, y ∉ b.vars) ∨ b.size < u.size := by
      rcases h with ⟨y, hy, hn⟩ | h
      · exact Or.inl ⟨y, hy, fun hc => hn (by simp [Term.vars, hc])⟩
      · exact Or.inr (by simp only [Term.size] at h; omega)
    have hne : b ≠ u := by
      rintro rfl
      rcases hb with ⟨y, hy, hn⟩ | hb
      · exact hn hy
      · exact Nat.lt_irrefl _ hb
    simp only [outF, ite_eq_right hne, Term.vars, outF_eq_vars u g hg, outF_eq_vars u b hb]

section outside

variable {D : List Nat} {τ : Nat → Pat}

theorem outF_bind (h : Unfolds D τ) {u : Pat} (hu : ∀ v ∈ u.vars, v ∈ D) (hnv : ∀ x, u ≠ .var x)
    (hne : u.vars ≠ []) : ∀ t : Pat, (∀ v ∈ t.vars, v ∈ D) →
    outF (u.bind τ) (t.bind τ) = (outF u t).flatMap fun v => (τ v).vars
  | .var x, ht => by
    have hx : x ∈ D := ht x (by simp [Term.vars])
    simp only [Term.bind, outF, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply outF_eq_vars
    by_cases hxu : x ∈ u.vars
    · exact Or.inr (Term.size_bind_lt τ hxu hnv)
    · left
      cases hl : u.vars with
      | nil => exact absurd hl hne
      | cons w _ =>
        have hw : w ∈ u.vars := by rw [hl]; exact List.mem_cons_self
        cases hl' : (τ w).vars with
        | nil => exact absurd hl' (h.ne w (hu w hw))
        | cons y _ =>
          have hy : y ∈ (τ w).vars := by rw [hl']; exact List.mem_cons_self
          refine ⟨y, Term.mem_vars_bind.2 ⟨w, hw, hy⟩, fun hc => ?_⟩
          have := h.disj w (hu w hw) x hx y hy hc
          subst this
          exact hxu hw
  | .sym _, _ => rfl
  | .app g b, ht => by
    have hg : ∀ v ∈ g.vars, v ∈ D := fun v hv => ht v (by simp [Term.vars, hv])
    have hb : ∀ v ∈ b.vars, v ∈ D := fun v hv => ht v (by simp [Term.vars, hv])
    simp only [Term.bind, outF, List.flatMap_append, outF_bind h hu hnv hne g hg]
    by_cases e : b = u
    · simp [e]
    · have e' : b.bind τ ≠ u.bind τ := fun hc => e (h.inj hb hu hc)
      rw [ite_eq_right e, ite_eq_right e', outF_bind h hu hnv hne b hb]

theorem outV_bind (h : Unfolds D τ) {u : Pat} (hu : ∀ v ∈ u.vars, v ∈ D) (hnv : ∀ x, u ≠ .var x)
    (hne : u.vars ≠ []) {t : Pat} (ht : ∀ v ∈ t.vars, v ∈ D) :
    outV (u.bind τ) (t.bind τ) = (outV u t).flatMap fun v => (τ v).vars := by
  unfold outV
  by_cases e : t = u
  · simp [e]
  · have e' : t.bind τ ≠ u.bind τ := fun hc => e (h.inj ht hu hc)
    rw [ite_eq_right e, ite_eq_right e', outF_bind h hu hnv hne t ht]

end outside

/-! ## Free subterms -/

/-- The subterm need not be written out: it is not a variable, it has a
variable and none twice, its variables occur nowhere else in the pattern,
and its values are exactly the members of some sorts, whatever the values of
the other variables. -/
structure Free (S : Sorts) (s : Store) (u : Pat) : Prop where
  app : ∀ x, u ≠ .var x
  ne : u.vars ≠ []
  lin : u.vars.Nodup
  inside : ∀ y ∈ u.vars, y ∉ outV u s.t
  sem : ∃ C : Conj, (∀ σ ∈ s.Sol S, MemC S C (u.bind σ)) ∧
    ∀ σ ∈ s.Sol S, ∀ g, MemC S C g → ∃ σ' ∈ s.Sol S, u.bind σ' = g ∧
      ∀ y ∈ s.t.vars, y ∉ u.vars → σ' y = σ y

/-- One store is another under a substitution: its pattern is the other's
under the substitution, and their solutions correspond. -/
structure Linked (S : Sorts) (s s' : Store) (τ : Nat → Pat) : Prop where
  t : s'.t = s.t.bind τ
  down : ∀ σ' ∈ s'.Sol S, (fun v => (τ v).bind σ') ∈ s.Sol S
  up : ∀ σ ∈ s.Sol S, ∃ σ' ∈ s'.Sol S, ∀ v ∈ s.t.vars, (τ v).bind σ' = σ v

/-- One store is another unfolded: it is the other under a substitution that
unfolds. -/
structure Unfolding (S : Sorts) (s s' : Store) (τ : Nat → Pat) : Prop
    extends Linked S s s' τ where
  un : Unfolds s.t.vars τ

section unfolding

variable {S : Sorts} {s s' : Store} {τ : Nat → Pat}

theorem bind_not_var {u : Pat} (hnv : ∀ x, u ≠ .var x) (τ : Nat → Pat) (x : Nat) :
    u.bind τ ≠ .var x := by
  cases u with
  | var y => exact absurd rfl (hnv y)
  | sym _ => simp [Term.bind]
  | app _ _ => simp [Term.bind]

/-- A subterm is free in a store exactly when its image is free in the
store unfolded. -/
theorem free_bind (h : Unfolding S s s' τ) {u : Pat} (hu : ∀ v ∈ u.vars, v ∈ s.t.vars)
    (hnv : ∀ x, u ≠ .var x) : Free S s u ↔ Free S s' (u.bind τ) := by
  have hbind : ∀ σ' : Nat → GTerm, u.bind (fun v => (τ v).bind σ') = (u.bind τ).bind σ' :=
    fun σ' => (Term.bind_bind τ σ' u).symm
  have hne : u.vars ≠ [] ↔ (u.bind τ).vars ≠ [] := by
    constructor
    · intro hn hc
      cases hl : u.vars with
      | nil => exact hn hl
      | cons w _ =>
        have hw : w ∈ u.vars := by rw [hl]; exact List.mem_cons_self
        cases hl' : (τ w).vars with
        | nil => exact h.un.ne w (hu w hw) hl'
        | cons y _ =>
          have : y ∈ (u.bind τ).vars :=
            Term.mem_vars_bind.2 ⟨w, hw, by rw [hl']; exact List.mem_cons_self⟩
          rw [hc] at this
          cases this
    · intro hn hc
      apply hn
      rw [Term.vars_bind_eq, hc]
      rfl
  have hlin : u.vars.Nodup ↔ (u.bind τ).vars.Nodup := by
    rw [Term.vars_bind_eq, List.nodup_flatMap]
    constructor
    · intro hn
      refine ⟨fun v hv => h.un.lin v (hu v hv), ?_⟩
      refine List.Pairwise.imp_of_mem ?_ hn
      intro a b ha hb hab y hya hyb
      exact hab (h.un.disj a (hu a ha) b (hu b hb) y hya hyb)
    · rintro ⟨-, hp⟩
      refine List.Pairwise.imp_of_mem ?_ hp
      intro a b ha _ hd hab
      subst hab
      cases hl : (τ a).vars with
      | nil => exact h.un.ne a (hu a ha) hl
      | cons y _ =>
        have hy : y ∈ (τ a).vars := by rw [hl]; exact List.mem_cons_self
        exact hd hy hy
  have hins : ∀ (_ : u.vars ≠ []), (∀ y ∈ u.vars, y ∉ outV u s.t) ↔
      ∀ y ∈ (u.bind τ).vars, y ∉ outV (u.bind τ) s'.t := by
    intro hn
    rw [h.t, outV_bind h.un hu hnv hn (fun v hv => hv)]
    constructor
    · intro hi y hy hc
      obtain ⟨w, hw, hyw⟩ := Term.mem_vars_bind.1 hy
      obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.1 hc
      have := h.un.disj w (hu w hw) z (outV_sub u s.t z hz) y hyw hyz
      subst this
      exact hi w hw hz
    · intro hi w hw hc
      cases hl : (τ w).vars with
      | nil => exact h.un.ne w (hu w hw) hl
      | cons y _ =>
        have hy : y ∈ (τ w).vars := by rw [hl]; exact List.mem_cons_self
        exact hi y (Term.mem_vars_bind.2 ⟨w, hw, hy⟩) (List.mem_flatMap.2 ⟨w, hc, hy⟩)
  constructor
  · intro hf
    refine ⟨bind_not_var hnv τ, hne.1 hf.ne, hlin.1 hf.lin, (hins hf.ne).1 hf.inside, ?_⟩
    obtain ⟨C, hC, hind⟩ := hf.sem
    refine ⟨C, fun σ' hσ' => ?_, fun σ' hσ' g hg => ?_⟩
    · rw [← hbind]
      exact hC _ (h.down σ' hσ')
    · obtain ⟨σ₁, hσ₁, e₁, hag⟩ := hind _ (h.down σ' hσ') g hg
      obtain ⟨σ₁', hσ₁', hup⟩ := h.up σ₁ hσ₁
      refine ⟨σ₁', hσ₁', ?_, fun y hy hyu => ?_⟩
      · rw [← hbind, ← e₁]
        exact Term.bind_congr fun v hv => hup v (hu v hv)
      · rw [h.t] at hy
        obtain ⟨z, hz, hyz⟩ := Term.mem_vars_bind.1 hy
        have hzu : z ∉ u.vars := fun hc => hyu (Term.mem_vars_bind.2 ⟨z, hc, hyz⟩)
        have e : (τ z).bind σ₁' = (τ z).bind σ' := by rw [hup z hz, hag z hz hzu]
        exact bind_agree e y hyz
  · intro hf
    have hn : u.vars ≠ [] := hne.2 hf.ne
    refine ⟨hnv, hn, hlin.2 hf.lin, (hins hn).2 hf.inside, ?_⟩
    obtain ⟨C, hC, hind⟩ := hf.sem
    refine ⟨C, fun σ hσ => ?_, fun σ hσ g hg => ?_⟩
    · obtain ⟨σ', hσ', hup⟩ := h.up σ hσ
      have := hC σ' hσ'
      rw [← hbind] at this
      rwa [Term.bind_congr (σ := fun v => (τ v).bind σ') (τ := σ) fun v hv => hup v (hu v hv)]
        at this
    · obtain ⟨σ', hσ', hup⟩ := h.up σ hσ
      obtain ⟨σ₁', hσ₁', e₁, hag⟩ := hind σ' hσ' g hg
      refine ⟨_, h.down σ₁' hσ₁', by rw [hbind]; exact e₁, fun z hz hzu => ?_⟩
      show (τ z).bind σ₁' = σ z
      rw [← hup z hz]
      refine Term.bind_congr fun y hy => ?_
      refine hag y (by rw [h.t]; exact Term.mem_vars_bind.2 ⟨z, hz, hy⟩) fun hc => ?_
      obtain ⟨w, hw, hyw⟩ := Term.mem_vars_bind.1 hc
      have := h.un.disj z hz w (hu w hw) y hy hyw
      subst this
      exact hzu hw

end unfolding

/-! ## The folded pattern -/

open Classical in
/-- A term with each outermost free argument replaced by a variable named by
the argument, and each variable named by itself. -/
noncomputable def foldF (S : Sorts) (s : Store) : Pat → Term Pat
  | .var x => .var (.var x)
  | .sym f => .sym f
  | .app g b => .app (foldF S s g) (if Free S s b then .var b else foldF S s b)

open Classical in
/-- A term with each outermost free subterm replaced by a variable named by
the subterm. -/
noncomputable def foldV (S : Sorts) (s : Store) (t : Pat) : Term Pat :=
  if Free S s t then .var t else foldF S s t

/-- The folded pattern of a store: each outermost free subterm of its
pattern replaced by a variable, the variables numbered in the order they
first occur. -/
noncomputable def foldPat (S : Sorts) (s : Store) : Pat :=
  (foldV S s s.t).rename fun p => (firsts (foldV S s s.t).vars).idxOf p

section fold

variable {S : Sorts} {s s' : Store} {τ : Nat → Pat}

theorem foldF_vars (S : Sorts) (s : Store) : ∀ (t : Pat), ∀ p ∈ (foldF S s t).vars,
    ∀ v ∈ p.vars, v ∈ t.vars
  | .var x, p, hp, v, hv => by
    simp only [foldF, Term.vars, List.mem_singleton] at hp
    subst hp
    exact hv
  | .sym _, p, hp, _, _ => by simp [foldF, Term.vars] at hp
  | .app g b, p, hp, v, hv => by
    simp only [foldF, Term.vars, List.mem_append] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl (foldF_vars S s g p hp v hv)
    · by_cases hb : Free S s b
      · simp only [ite_eq_left hb, Term.vars, List.mem_singleton] at hp
        subst hp
        exact Or.inr hv
      · rw [ite_eq_right hb] at hp
        exact Or.inr (foldF_vars S s b p hp v hv)

theorem foldV_vars (S : Sorts) (s : Store) (t : Pat) : ∀ p ∈ (foldV S s t).vars,
    ∀ v ∈ p.vars, v ∈ t.vars := by
  intro p hp v hv
  unfold foldV at hp
  by_cases ht : Free S s t
  · simp only [ite_eq_left ht, Term.vars, List.mem_singleton] at hp
    subst hp
    exact hv
  · rw [ite_eq_right ht] at hp
    exact foldF_vars S s t p hp v hv

open Classical in
/-- The image of a variable folds to a variable named by the image. -/
theorem foldArg_leaf (hfree : ∀ v ∈ s.t.vars, (∀ x, τ v ≠ .var x) → Free S s' (τ v)) {x : Nat}
    (hxs : x ∈ s.t.vars) :
    (if Free S s' (τ x) then Term.var (τ x) else foldF S s' (τ x)) = Term.var (τ x) := by
  by_cases hτ : ∀ y, τ x ≠ .var y
  · rw [ite_eq_left (hfree x hxs hτ)]
  · rw [not_forall] at hτ
    obtain ⟨y, hy⟩ := hτ
    have e : τ x = .var y := not_not.1 hy
    have hnf' : ¬ Free S s' (τ x) := fun hc => hc.app y e
    rw [ite_eq_right hnf', e]
    rfl

/-- Folding the image of a term under an unfolding gives the fold of the
term with each name replaced by its image. -/
theorem foldF_bind (h : Unfolding S s s' τ)
    (hfree : ∀ v ∈ s.t.vars, (∀ x, τ v ≠ .var x) → Free S s' (τ v)) :
    ∀ g : Pat, g.firstOrder = true → (∀ x, g ≠ .var x) → (∀ v ∈ g.vars, v ∈ s.t.vars) →
      foldF S s' (g.bind τ) = (foldF S s g).rename fun p => p.bind τ
  | .var x, _, hnv, _ => absurd rfl (hnv x)
  | .sym _, _, _, _ => rfl
  | .app g b, hfo, _, hv => by
    obtain ⟨hgfo, hbfo, hgnv⟩ := Term.fo_app hfo
    have hg : ∀ v ∈ g.vars, v ∈ s.t.vars := fun v hv' => hv v (by simp [Term.vars, hv'])
    have hb : ∀ v ∈ b.vars, v ∈ s.t.vars := fun v hv' => hv v (by simp [Term.vars, hv'])
    simp only [Term.bind, foldF, Term.rename]
    rw [foldF_bind h hfree g hgfo hgnv hg]
    congr 1
    by_cases hbv : ∀ x, b ≠ .var x
    · by_cases hf : Free S s b
      · rw [ite_eq_left hf, ite_eq_left ((free_bind h hb hbv).1 hf)]
        rfl
      · rw [ite_eq_right hf, ite_eq_right fun hc => hf ((free_bind h hb hbv).2 hc)]
        exact foldF_bind h hfree b hbfo hbv hb
    · rw [not_forall] at hbv
      obtain ⟨x, hx⟩ := hbv
      obtain rfl : b = .var x := not_not.1 hx
      have hxs : x ∈ s.t.vars := hb x (by simp [Term.vars])
      have hnf : ¬ Free S s (.var x) := fun hc => hc.app x rfl
      rw [ite_eq_right hnf]
      exact foldArg_leaf hfree hxs

theorem foldV_bind (h : Unfolding S s s' τ)
    (hfree : ∀ v ∈ s.t.vars, (∀ x, τ v ≠ .var x) → Free S s' (τ v)) {t : Pat}
    (hfo : t.firstOrder = true) (hv : ∀ v ∈ t.vars, v ∈ s.t.vars) :
    foldV S s' (t.bind τ) = (foldV S s t).rename fun p => p.bind τ := by
  unfold foldV
  by_cases hnv : ∀ x, t ≠ .var x
  · by_cases hf : Free S s t
    · rw [ite_eq_left hf, ite_eq_left ((free_bind h hv hnv).1 hf)]
      rfl
    · rw [ite_eq_right hf, ite_eq_right fun hc => hf ((free_bind h hv hnv).2 hc)]
      exact foldF_bind h hfree t hfo hnv hv
  · rw [not_forall] at hnv
    obtain ⟨x, hx⟩ := hnv
    obtain rfl : t = .var x := not_not.1 hx
    have hxs : x ∈ s.t.vars := hv x (by simp [Term.vars])
    have hnf : ¬ Free S s (.var x) := fun hc => hc.app x rfl
    rw [ite_eq_right hnf]
    exact foldArg_leaf hfree hxs

theorem firsts_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ L : List α, (∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) → firsts (L.map f) = (firsts L).map f := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton L x ih =>
    intro hf
    have ih' := ih fun a ha b hb => hf a (by simp [ha]) b (by simp [hb])
    rw [List.map_append, List.map_singleton, firsts_concat, firsts_concat, ih']
    unfold addNew
    by_cases hx : x ∈ firsts L
    · rw [ite_eq_left hx, ite_eq_left (List.mem_map_of_mem hx)]
    · have hx' : f x ∉ (firsts L).map f := by
        intro hc
        obtain ⟨a, ha, e⟩ := List.mem_map.1 hc
        have := hf a (by simp [mem_firsts.1 ha]) x (by simp) e
        subst this
        exact hx ha
      rw [ite_eq_right hx, ite_eq_right hx', List.map_append, List.map_singleton]

theorem idxOf_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (p : α) :
    ∀ F : List α, (∀ a ∈ F, f a = f p → a = p) → (F.map f).idxOf (f p) = F.idxOf p
  | [], _ => rfl
  | a :: F, hf => by
    by_cases e : a = p
    · subst e
      simp
    · have e' : f a ≠ f p := fun hc => e (hf a List.mem_cons_self hc)
      simp only [List.map_cons, List.idxOf_cons_ne _ e', List.idxOf_cons_ne _ e]
      rw [idxOf_map_inj f p F fun b hb => hf b (List.mem_cons_of_mem _ hb)]

/-- A store and the store unfolded have the same folded pattern, when each
term a variable is unfolded to is free. -/
theorem foldPat_bind (h : Unfolding S s s' τ)
    (hfree : ∀ v ∈ s.t.vars, (∀ x, τ v ≠ .var x) → Free S s' (τ v))
    (hfo : s.t.firstOrder = true) : foldPat S s' = foldPat S s := by
  unfold foldPat
  rw [h.t, foldV_bind h hfree hfo fun v hv => hv]
  generalize hT : foldV S s s.t = T
  have hleaf : ∀ p ∈ T.vars, ∀ v ∈ p.vars, v ∈ s.t.vars := by
    rw [← hT]
    exact foldV_vars S s s.t
  have hinj : ∀ a ∈ T.vars, ∀ b ∈ T.vars, a.bind τ = b.bind τ → a = b :=
    fun a ha b hb e => h.un.inj (hleaf a ha) (hleaf b hb) e
  simp only [Term.rename, Term.bind_bind, Term.bind]
  refine Term.bind_congr fun p hp => ?_
  have e : (Term.bind (fun v => Term.var (Term.bind τ v)) T).vars = T.vars.map (Term.bind τ) :=
    Term.vars_rename (Term.bind τ) T
  rw [e, firsts_map _ _ hinj]
  simp only [Term.var.injEq]
  exact idxOf_map_inj _ p _ fun a ha e => hinj a (mem_firsts.1 ha) p hp e

/-- Stores with the same pattern and solutions have the same free
subterms. -/
theorem free_congr (ht : s.t = s'.t) (hsol : s.Sol S = s'.Sol S) : Free S s = Free S s' := by
  funext u
  apply propext
  constructor
  · rintro ⟨a, b, c, d, e⟩
    exact ⟨a, b, c, by rw [← ht]; exact d, by rw [← ht, ← hsol]; exact e⟩
  · rintro ⟨a, b, c, d, e⟩
    exact ⟨a, b, c, by rw [ht]; exact d, by rw [ht, hsol]; exact e⟩

/-- Stores with the same pattern and solutions have the same folded
pattern. -/
theorem foldPat_congr (ht : s.t = s'.t) (hsol : s.Sol S = s'.Sol S) :
    foldPat S s = foldPat S s' := by
  have hF : ∀ u, Free S s u ↔ Free S s' u := fun u => by rw [free_congr ht hsol]
  have h1 : ∀ t : Pat, foldF S s t = foldF S s' t := by
    intro t
    induction t with
    | var x => rfl
    | sym f => rfl
    | app g b ihg ihb =>
      simp only [foldF, ihg, ihb]
      by_cases hb : Free S s b
      · rw [ite_eq_left hb, ite_eq_left ((hF b).1 hb)]
      · rw [ite_eq_right hb, ite_eq_right fun hc => hb ((hF b).2 hc)]
  have h2 : ∀ t : Pat, foldV S s t = foldV S s' t := by
    intro t
    simp only [foldV, h1]
    by_cases hb : Free S s t
    · rw [ite_eq_left hb, ite_eq_left ((hF t).1 hb)]
    · rw [ite_eq_right hb, ite_eq_right fun hc => hb ((hF t).2 hc)]
  unfold foldPat
  rw [h2, ht]

end fold

/-! ## Stores under a substitution -/

section linked

variable {S : Sorts} {s s' : Store} {τ : Nat → Pat}

namespace Linked

theorem refl (S : Sorts) (s : Store) : Linked S s s .var where
  t := (Term.bind_var_id s.t).symm
  down := fun _ hσ' => hσ'
  up := fun σ hσ => ⟨σ, hσ, fun _ _ => rfl⟩

theorem trans {s'' : Store} {τ' : Nat → Pat} (h : Linked S s s' τ) (h' : Linked S s' s'' τ') :
    Linked S s s'' fun v => (τ v).bind τ' where
  t := by rw [h'.t, h.t, Term.bind_bind]
  down := fun σ'' hσ'' => by
    have := h.down _ (h'.down σ'' hσ'')
    simpa only [Term.bind_bind] using this
  up := fun σ hσ => by
    obtain ⟨σ', hσ', e'⟩ := h.up σ hσ
    obtain ⟨σ'', hσ'', e''⟩ := h'.up σ' hσ'
    refine ⟨σ'', hσ'', fun v hv => ?_⟩
    rw [Term.bind_bind, ← e' v hv]
    refine Term.bind_congr fun w hw => e'' w ?_
    rw [h.t]
    exact Term.mem_vars_bind.2 ⟨v, hv, hw⟩

/-- A variable with two values is not sent to a term without variables. -/
theorem vars_ne (h : Linked S s s' τ) {v : Nat} (hv : v ∈ s.t.vars) {σ₁ σ₂ : Nat → GTerm}
    (h₁ : σ₁ ∈ s.Sol S) (h₂ : σ₂ ∈ s.Sol S) (hne : σ₁ v ≠ σ₂ v) : (τ v).vars ≠ [] := by
  intro e
  obtain ⟨σ₁', -, e₁⟩ := h.up σ₁ h₁
  obtain ⟨σ₂', -, e₂⟩ := h.up σ₂ h₂
  apply hne
  rw [← e₁ v hv, ← e₂ v hv]
  exact Term.bind_congr fun w hw => by rw [e] at hw; cases hw

end Linked

/-- The places of a term with one variable replaced by `u` that are outside
`u` hold variables of the term. -/
theorem outF_single {v : Nat} {u : Pat} : ∀ t : Pat, t.firstOrder = true → (∀ x, t ≠ .var x) →
    ∀ y ∈ outF u (t.bind (Term.single v u)), y ∈ t.vars
  | .var x, _, hnv => absurd rfl (hnv x)
  | .sym _, _, _ => by intro y hy; simp [Term.bind, outF] at hy
  | .app g b, hfo, _ => by
    obtain ⟨hgfo, hbfo, hgnv⟩ := Term.fo_app hfo
    intro y hy
    simp only [Term.bind, outF, List.mem_append] at hy
    simp only [Term.vars, List.mem_append]
    rcases hy with hy | hy
    · exact Or.inl (outF_single g hgfo hgnv y hy)
    · right
      by_cases e : Term.bind (Term.single v u) b = u
      · rw [ite_eq_left e] at hy; cases hy
      · rw [ite_eq_right e] at hy
        by_cases hbv : ∀ x, b ≠ .var x
        · exact outF_single b hbfo hbv y hy
        · rw [not_forall] at hbv
          obtain ⟨x, hx⟩ := hbv
          obtain rfl : b = .var x := not_not.1 hx
          have hxv : x ≠ v := fun h => e (by simp [Term.bind, Term.single, h])
          simp only [Term.bind, Term.single, hxv, ite_false, outF, List.mem_singleton] at hy
          simp [Term.vars, hy]

theorem outV_single {v : Nat} {u t : Pat} (hfo : t.firstOrder = true) {y : Nat}
    (hy : y ∈ outV u (t.bind (Term.single v u))) : y ∈ t.vars := by
  unfold outV at hy
  by_cases e : t.bind (Term.single v u) = u
  · rw [ite_eq_left e] at hy; cases hy
  · rw [ite_eq_right e] at hy
    by_cases hnv : ∀ x, t ≠ .var x
    · exact outF_single t hfo hnv y hy
    · rw [not_forall] at hnv
      obtain ⟨x, hx⟩ := hnv
      obtain rfl : t = .var x := not_not.1 hx
      have hxv : x ≠ v := fun h => e (by simp [Term.bind, Term.single, h])
      simp only [Term.bind, Term.single, hxv, ite_false, outF, List.mem_singleton] at hy
      simp [Term.vars, hy]

/-- The term a variable is replaced by is free in the store after, when the
store before says nothing of the variable but its sorts, no other variable is
replaced, and the term is not a variable, has a variable and none twice, and
has no variable of the pattern before. -/
theorem Linked.free (h : Linked S s s' τ) {v : Nat} (hv : v ∈ s.t.vars)
    (hid : ∀ w ∈ s.t.vars, w ≠ v → τ w = .var w)
    (hx : ∀ E ∈ s.x, ∀ p ∈ E, v ∉ p.1.vars ++ p.2.vars) (hfo : s.t.firstOrder = true)
    (app : ∀ x, τ v ≠ .var x) (ne : (τ v).vars ≠ []) (lin : (τ v).vars.Nodup)
    (fresh : ∀ y ∈ (τ v).vars, y ∉ s.t.vars) : Free S s' (τ v) := by
  have ht : s'.t = s.t.bind (Term.single v (τ v)) := by
    rw [h.t]
    refine Term.bind_congr fun w hw => ?_
    by_cases e : w = v
    · simp [Term.single, e]
    · simp [Term.single, e, hid w hw e]
  refine ⟨app, ne, lin, fun y hy hc => ?_, s.c v, fun σ' hσ' => ?_, fun σ' hσ' g hg => ?_⟩
  · rw [ht] at hc
    exact fresh y hy (outV_single hfo hc)
  · exact (h.down σ' hσ').1 v
  · have hσ : (fun w => (τ w).bind σ') ∈ s.Sol S := h.down σ' hσ'
    have hσ₂ : update (fun w => (τ w).bind σ') v g ∈ s.Sol S := by
      refine ⟨fun w => ?_, fun E hE hu => hσ.2 E hE (unifies_congr (fun p hp w hw => ?_) hu)⟩
      · by_cases e : w = v
        · subst e
          simpa using hg
        · rw [update_of_ne e]
          exact hσ.1 w
      · exact update_of_ne (fun e : w = v => hx E hE p hp (e ▸ hw)) _ _
    obtain ⟨σ'', hσ'', e⟩ := h.up _ hσ₂
    refine ⟨σ'', hσ'', by rw [e v hv]; simp, fun y hy hyu => ?_⟩
    rw [h.t] at hy
    obtain ⟨w, hw, hyw⟩ := Term.mem_vars_bind.1 hy
    have hwv : w ≠ v := fun e => hyu (e ▸ hyw)
    rw [hid w hw hwv] at hyw
    simp only [Term.vars, List.mem_singleton] at hyw
    subst hyw
    have := e y hw
    rw [hid y hw hwv, update_of_ne hwv, hid y hw hwv] at this
    exact this

/-- A store renamed is the store unfolded by the renaming. -/
theorem unfolding_ren {ρ ρ' : Nat → Nat} (hfull : s.Full) (hinv : ∀ v ∈ s.t.vars, ρ' (ρ v) = v) :
    Unfolding S s (s.ren ρ ρ') fun v => .var (ρ v) where
  t := rfl
  down := fun _ hσ' => (ren_bwd hfull hinv hσ').1
  up := fun σ hσ => ⟨σ ∘ ρ', (ren_fwd hfull hinv hσ).1, fun v hv => by
    show σ (ρ' (ρ v)) = σ v
    rw [hinv v hv]⟩
  un := ⟨fun v _ => by simp [Term.vars], fun v _ => by simp [Term.vars], fun v hv w hw y h₁ h₂ => by
    simp only [Term.vars, List.mem_singleton] at h₁ h₂
    exact (hinv v hv).symm.trans ((congrArg ρ' (h₁.symm.trans h₂)).trans (hinv w hw))⟩

/-- A store renamed has the folded pattern of the store. -/
theorem foldPat_ren {ρ ρ' : Nat → Nat} (hfull : s.Full) (hinv : ∀ v ∈ s.t.vars, ρ' (ρ v) = v)
    (hfo : s.t.firstOrder = true) : foldPat S (s.ren ρ ρ') = foldPat S s :=
  foldPat_bind (unfolding_ren hfull hinv) (fun v _ hnv => absurd rfl (hnv (ρ v))) hfo

end linked

end Sorts
end RwLog
