/-
# Two normal stores with the same denotation have the same pattern and sorts

The pattern of a normal store is the least pattern around what it denotes:
where one of two normal stores with the same denotation has a variable, the
other cannot have a symbol, because the variable takes values with two
different head symbols; and two places that hold one variable in one store
hold one variable in the other, because two different variables take
different values in some solution. So the patterns agree up to the names of
variables, and the numbering by first occurrence makes them equal. The
solutions are then the same, and the sorts are read off the solutions.

The exclusions are compared in `Sorts/UniqueExcl.lean`.
-/
import RwLog.Sorts.Normal
import RwLog.Kernel.SolveFacts

namespace RwLog
namespace Sorts

open Function

/-- Lists numbered by first occurrence that repeat at the same places are
equal. -/
theorem firstOcc_eq {L L' : List Nat} (hlen : L.length = L'.length) (h : FirstOcc L)
    (h' : FirstOcc L')
    (hc : ∀ (i j : Nat) (hi : i < L.length) (hj : j < L.length),
      L[i] = L[j] ↔ L'[i]'(hlen ▸ hi) = L'[j]'(hlen ▸ hj)) : L = L' := by
  apply List.ext_getElem hlen
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hi'
    rcases Nat.lt_trichotomy L[i] L'[i] with hlt | heq | hgt
    · obtain ⟨j, hj, hjm⟩ := h' i hi' L[i] hlt
      have hjl : j < L.length := by omega
      have e := ih j hj hjl (by omega)
      have : L[j] = L[i] := by rw [e]; exact hjm
      have := (hc j i hjl hi).1 this
      omega
    · exact heq
    · obtain ⟨j, hj, hjm⟩ := h i hi L'[i] hgt
      have hjl : j < L.length := by omega
      have e := ih j hj hjl (by omega)
      have : L'[j] = L'[i] := by rw [← e]; exact hjm
      have := (hc j i hjl hi).2 this
      omega

theorem Term.rename_eq_self {t : Pat} {ρ : Nat → Nat} (h : ∀ v ∈ t.vars, ρ v = v) :
    t.rename ρ = t := by
  conv_rhs => rw [← Term.bind_var_id t]
  exact Term.bind_congr fun v hv => by rw [h v hv]

namespace Raw.Normal

variable {S : Sorts} {r r' : Raw}

/-- Whether a substitution is a solution depends only on the values of the
variables of the store. -/
theorem sol_congr (hr : r.Normal S) {σ σ' : Nat → GTerm} (h : ∀ v, v < r.c.length → σ v = σ' v)
    (hσ' : σ' ∈ r.store.Sol S) : σ ∈ r.store.Sol S := by
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v < r.c.length
    · rw [h v hv]; exact hσ'.1 v
    · show MemC S (r.conj v) (σ v)
      rw [conj_of_ge r (Nat.le_of_not_lt hv)]; intro n hn; simp at hn
  · intro E hE hu
    obtain ⟨θ, hθ, rfl⟩ := Raw.mem_store_x.1 hE
    refine hσ'.2 _ hE ?_
    intro p hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
    have hn := hr.ex θ hθ
    have e : b.2.bind σ = b.2.bind σ' :=
      Term.bind_congr fun v hv => h v (hn.ran b hb v hv).1
    have := hu _ (List.mem_map.2 ⟨b, hb, rfl⟩)
    simp only [Term.bind_var] at this ⊢
    rw [← h b.1 (hn.dom b hb), ← e]; exact this

section shape

open Classical in
/-- The variable of the second store that always has the value of `v` in the
first. -/
noncomputable def pair (S : Sorts) (r r' : Raw) (v : Nat) : Nat :=
  if h : ∃ j, j < r'.c.length ∧ ∀ σ ∈ r.store.Sol S, ∀ σ' ∈ r'.store.Sol S,
      r.t.bind σ = r'.t.bind σ' → σ v = σ' j then choose h else 0

variable (hS : S.WellFormed) (hr : r.Normal S) (hr' : r'.Normal S)
  (hden : r.store.Den S = r'.store.Den S)

include hden in
theorem total_left : ∀ σ ∈ r.store.Sol S, ∃ σ' ∈ r'.store.Sol S, r.t.bind σ = r'.t.bind σ' := by
  intro σ hσ
  have : r.t.bind σ ∈ r'.store.Den S := hden ▸ ⟨σ, hσ, rfl⟩
  obtain ⟨σ', hσ', e⟩ := this
  exact ⟨σ', hσ', e⟩

include hden in
theorem total_right : ∀ σ' ∈ r'.store.Sol S, ∃ σ ∈ r.store.Sol S, r.t.bind σ = r'.t.bind σ' := by
  intro σ' hσ'
  have : r'.t.bind σ' ∈ r.store.Den S := hden ▸ ⟨σ', hσ', rfl⟩
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

include hS hr hr' hden

omit hS hr' in
/-- A variable of one store is never aligned with a symbol of the other. -/
theorem var_not_aligned {v : Nat} (hv : v < r.c.length) {p' : Pat} (hfo : p'.firstOrder = true)
    (hnv : ∀ x, p' ≠ .var x)
    (hal : ∀ σ ∈ r.store.Sol S, ∀ σ' ∈ r'.store.Sol S, r.t.bind σ = r'.t.bind σ' →
      σ v = p'.bind σ') : False := by
  obtain ⟨κ, hκ⟩ := Option.isSome_iff_exists.1 (Term.key_isSome hfo hnv)
  obtain ⟨σ₁, h₁, σ₂, h₂, hne⟩ := hr.two v hv
  obtain ⟨σ₁', h₁', e₁⟩ := total_left hden σ₁ h₁
  obtain ⟨σ₂', h₂', e₂⟩ := total_left hden σ₂ h₂
  apply hne
  rw [hal σ₁ h₁ σ₁' h₁' e₁, hal σ₂ h₂ σ₂' h₂' e₂, Term.key_bind _ hκ, Term.key_bind _ hκ]

/-- Patterns of the two stores that always have the same value are the same
up to the pairing of variables. -/
theorem shape : ∀ (p p' : Pat), p.firstOrder = true → p'.firstOrder = true →
    (∀ v ∈ p.vars, v < r.c.length) → (∀ v ∈ p'.vars, v < r'.c.length) →
    (∀ σ ∈ r.store.Sol S, ∀ σ' ∈ r'.store.Sol S, r.t.bind σ = r'.t.bind σ' →
      p.bind σ = p'.bind σ') → p' = p.rename (pair S r r')
  | .var v, p', _, hfo', hv, hv', hal => by
    have hvk : v < r.c.length := hv v (by simp [Term.vars])
    by_cases hnv : ∀ x, p' ≠ .var x
    · exact (var_not_aligned hr hden hvk hfo' hnv hal).elim
    · rw [not_forall] at hnv
      obtain ⟨j, hj'⟩ := hnv
      obtain rfl : p' = .var j := not_not.1 hj'
      have hj : j < r'.c.length := hv' j (by simp [Term.vars])
      have hex : ∃ j, j < r'.c.length ∧ ∀ σ ∈ r.store.Sol S, ∀ σ' ∈ r'.store.Sol S,
          r.t.bind σ = r'.t.bind σ' → σ v = σ' j := ⟨j, hj, hal⟩
      have hspec := Classical.choose_spec hex
      have hp : pair S r r' v = Classical.choose hex := by simp [pair, hex]
      simp only [Term.rename, Term.bind_var, Term.var.injEq]
      rw [hp]
      by_contra hne
      obtain ⟨σ', hσ', hd⟩ := hr'.sep_vars hS hj hspec.1 hne
      obtain ⟨σ, hσ, e⟩ := total_right hden σ' hσ'
      exact hd ((hal σ hσ σ' hσ' e).symm.trans (hspec.2 σ hσ σ' hσ' e))
  | .sym f, p', _, hfo', _, hv', hal => by
    obtain ⟨σ, hσ⟩ := hr.sol_nonempty hS
    obtain ⟨σ', hσ', e⟩ := total_left hden σ hσ
    have h := hal σ hσ σ' hσ' e
    cases p' with
    | var j =>
      exfalso
      have hden' : r'.store.Den S = r.store.Den S := hden.symm
      refine var_not_aligned hr' hden' (hv' j (by simp [Term.vars])) (p' := .sym f) rfl
        (by simp) ?_
      intro τ' hτ' τ hτ e'
      exact (hal τ hτ τ' hτ' e'.symm).symm
    | sym g => simpa [Term.rename] using h.symm
    | app a b => simp at h
  | .app a b, p', hfo, hfo', hv, hv', hal => by
    obtain ⟨σ, hσ⟩ := hr.sol_nonempty hS
    obtain ⟨σ', hσ', e⟩ := total_left hden σ hσ
    have h := hal σ hσ σ' hσ' e
    cases p' with
    | var j =>
      exfalso
      have hden' : r'.store.Den S = r.store.Den S := hden.symm
      refine var_not_aligned hr' hden' (hv' j (by simp [Term.vars])) (p' := .app a b) hfo
        (by simp) ?_
      intro τ' hτ' τ hτ e'
      exact (hal τ hτ τ' hτ' e'.symm).symm
    | sym g => simp at h
    | app a' b' =>
      have fo_parts : ∀ {x y : Pat}, (Term.app x y).firstOrder = true →
          x.firstOrder = true ∧ y.firstOrder = true := by
        intro x y hxy
        cases x with
        | var _ => simp [Term.firstOrder] at hxy
        | sym _ => exact ⟨rfl, by simpa [Term.firstOrder] using hxy⟩
        | app _ _ => simpa [Term.firstOrder] using hxy
      obtain ⟨ha, hb⟩ := fo_parts hfo
      obtain ⟨ha', hb'⟩ := fo_parts hfo'
      have iha := shape a a' ha ha' (fun v hv₁ => hv v (by simp [Term.vars, hv₁]))
        (fun v hv₁ => hv' v (by simp [Term.vars, hv₁]))
        (fun τ hτ τ' hτ' e' => by
          have := hal τ hτ τ' hτ' e'
          simp only [Term.bind_app, Term.app.injEq] at this; exact this.1)
      have ihb := shape b b' hb hb' (fun v hv₁ => hv v (by simp [Term.vars, hv₁]))
        (fun v hv₁ => hv' v (by simp [Term.vars, hv₁]))
        (fun τ hτ τ' hτ' e' => by
          have := hal τ hτ τ' hτ' e'
          simp only [Term.bind_app, Term.app.injEq] at this; exact this.2)
      rw [iha, ihb]; rfl

end shape

/-- Two normal stores with the same denotation have the same pattern. -/
theorem t_eq (hS : S.WellFormed) (hr : r.Normal S) (hr' : r'.Normal S)
    (hden : r.store.Den S = r'.store.Den S) : r.t = r'.t := by
  have h₁ : r'.t = r.t.rename (pair S r r') :=
    shape hS hr hr' hden r.t r'.t hr.fo hr'.fo (fun v hv => (hr.len v).1 hv)
      (fun v hv => (hr'.len v).1 hv) (fun _ _ _ _ e => e)
  have h₂ : r.t = r'.t.rename (pair S r' r) :=
    shape hS hr' hr hden.symm r'.t r.t hr'.fo hr.fo (fun v hv => (hr'.len v).1 hv)
      (fun v hv => (hr.len v).1 hv) (fun _ _ _ _ e => e)
  have hinv : ∀ v ∈ r.t.vars, pair S r' r (pair S r r' v) = v := by
    have e : r.t.bind (fun v => Term.var (pair S r' r (pair S r r' v))) = r.t.bind Term.var := by
      conv_rhs => rw [Term.bind_var_id, h₂, h₁]
      simp [Term.rename]
    intro v hv
    simpa using bind_agree e v hv
  have hvars : r'.t.vars = r.t.vars.map (pair S r r') := by rw [h₁, Term.vars_rename]
  have hL : r.t.vars = r'.t.vars := by
    refine firstOcc_eq (by rw [hvars, List.length_map]) hr.occ hr'.occ ?_
    intro i j hi hj
    simp only [hvars, List.getElem_map]
    constructor
    · intro e; rw [e]
    · intro e
      have := congrArg (pair S r' r) e
      rwa [hinv _ (List.getElem_mem hi), hinv _ (List.getElem_mem hj)] at this
  have hfix : ∀ v ∈ r.t.vars, pair S r r' v = v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have h₃ : r.t.vars.map (pair S r r') = r.t.vars := by rw [← hvars, hL]
    have := List.getElem_map (pair S r r') (l := r.t.vars) (i := i) (h := by simpa using hi)
    simp only [h₃] at this
    exact this.symm
  rw [h₁, Term.rename_eq_self hfix]

/-- Two normal stores with the same denotation have the same solutions. -/
theorem sol_eq (hS : S.WellFormed) (hr : r.Normal S) (hr' : r'.Normal S)
    (hden : r.store.Den S = r'.store.Den S) : r.store.Sol S = r'.store.Sol S := by
  have ht := t_eq hS hr hr' hden
  have key : ∀ {a b : Raw}, a.Normal S → b.Normal S → a.t = b.t →
      a.store.Den S = b.store.Den S → a.store.Sol S ⊆ b.store.Sol S := by
    intro a b ha hb hab hd σ hσ
    have : a.t.bind σ ∈ b.store.Den S := hd ▸ ⟨σ, hσ, rfl⟩
    obtain ⟨σ', hσ', e⟩ := this
    refine hb.sol_congr (fun v hv => ?_) hσ'
    have e' : b.t.bind σ = b.t.bind σ' := by
      have e₀ : a.t.bind σ = b.t.bind σ' := e
      rw [← hab]; rw [← hab] at e₀; exact e₀
    exact bind_agree e' v ((hb.len v).2 hv)
  exact Set.Subset.antisymm (key hr hr' ht hden) (key hr' hr ht.symm hden.symm)

/-- Two normal stores with the same denotation have the same sorts. -/
theorem c_eq (hS : S.WellFormed) (hr : r.Normal S) (hr' : r'.Normal S)
    (hden : r.store.Den S = r'.store.Den S) : r.c = r'.c := by
  have ht := t_eq hS hr hr' hden
  have hsol := sol_eq hS hr hr' hden
  have hlen : r.c.length = r'.c.length := by
    apply Nat.le_antisymm
    · by_contra h
      have := (hr.len r'.c.length).2 (by omega)
      rw [ht] at this
      exact absurd ((hr'.len _).1 this) (Nat.lt_irrefl _)
    · by_contra h
      have := (hr'.len r.c.length).2 (by omega)
      rw [← ht] at this
      exact absurd ((hr.len _).1 this) (Nat.lt_irrefl _)
  apply List.ext_getElem hlen
  intro v hv hv'
  have e₁ : r.c[v] = r.conj v := by simp [Raw.conj, List.getD_eq_getElem?_getD, hv]
  have e₂ : r'.c[v] = r'.conj v := by simp [Raw.conj, List.getD_eq_getElem?_getD, hv']
  rw [e₁, e₂]
  ext n
  rw [hr.up v hv, hr'.up v hv', hsol]

end Raw.Normal

end Sorts
end RwLog
