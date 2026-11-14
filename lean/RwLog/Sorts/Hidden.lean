/-
# Hidden variables, and the normal form of any store

A variable that occurs in the constraints of a store and not in its pattern
is *hidden*. In a normal store every variable has infinitely many values, so
an exclusion that mentions a hidden variable can always be satisfied by a
choice of that variable, and says nothing about the others: hidden variables
and the exclusions that mention them are dropped (`Raw.Normal.proj`).

To bring a store with hidden variables to normal form, its pattern is paired
with a tuple of all its variables, so that none is hidden, the result is
brought to normal form, and the tuple is projected away (`normal_exists`).
-/
import RwLog.Sorts.Assemble

namespace RwLog
namespace Sorts

open Function

/-- Two terms as one. -/
def tpair {V : Type} (a b : Term V) : Term V := .app (.app (.sym "") a) b

theorem tpair_inj {V : Type} {a b c d : Term V} (h : tpair a b = tpair c d) : a = c ∧ b = d := by
  simp only [tpair, Term.app.injEq] at h; exact ⟨h.1.2, h.2⟩

theorem tpair_bind {V W : Type} (σ : V → Term W) (a b : Term V) :
    (tpair a b).bind σ = tpair (a.bind σ) (b.bind σ) := rfl

theorem tpair_vars {V : Type} (a b : Term V) : (tpair a b).vars = a.vars ++ b.vars := by
  simp [tpair, Term.vars]

theorem tpair_fo {V : Type} (a b : Term V) :
    (tpair a b).firstOrder = (a.firstOrder && b.firstOrder) := by
  simp [tpair, Term.firstOrder]

theorem tpair_key (a b : GTerm) : (tpair a b).key = some ("", 2) := by
  simp [tpair, Term.key, Term.spine]

/-- A first part of a list numbered by first occurrence is numbered so, and
its members are the numbers below some bound. -/
theorem firstOcc_prefix {L M : List Nat} (h : FirstOcc (L ++ M)) :
    FirstOcc L ∧ ∃ k, ∀ v, v ∈ L ↔ v < k := by
  rw [firstOcc_iff] at h
  have hL : ∀ (i m v : Nat), L[i]? = some v → m < v → ∃ j, j < i ∧ L[j]? = some m := by
    intro i m v hv hm
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hv
    obtain ⟨j, hj, e⟩ := h i m v (by rw [List.getElem?_append_left hi]; exact hv) hm
    exact ⟨j, hj, by rwa [List.getElem?_append_left (by omega)] at e⟩
  refine ⟨firstOcc_iff.2 hL, ?_⟩
  classical
  have hex : ∃ k, k ∉ L := by
    obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset L.toFinset
    exact ⟨k, by simpa using hk⟩
  refine ⟨Nat.find hex, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · by_contra hge
    have hne : Nat.find hex ≠ v := fun e => Nat.find_spec hex (e ▸ hv)
    have hlt : Nat.find hex < v := by omega
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hv
    obtain ⟨j, -, e⟩ := hL i _ v hi hlt
    exact Nat.find_spec hex (List.mem_of_getElem? e)
  · by_contra hn
    exact absurd (Nat.find_min' hex hn) (by omega)

/-- All variables of the exclusion are below `k`. -/
def Low (k : Nat) (θ : Binds) : Prop := ∀ b ∈ θ, b.1 < k ∧ ∀ v ∈ b.2.vars, v < k

instance (k : Nat) (θ : Binds) : Decidable (Low k θ) := by unfold Low; infer_instance

/-- The first part of the pattern of a normal store, with the variables and
exclusions it needs, is a normal store. -/
theorem Raw.Normal.proj {S : Sorts} (hS : S.WellFormed) {r : Raw} (hr : r.Normal S) {a b : Pat}
    (ht : r.t = tpair a b) :
    ∃ r' : Raw, r'.Normal S ∧ r'.t = a ∧
      ∀ g, g ∈ r'.store.Den S ↔ ∃ σ ∈ r.store.Sol S, g = a.bind σ := by
  have hocc := hr.occ
  rw [ht, tpair_vars] at hocc
  obtain ⟨hoccA, k, hk⟩ := firstOcc_prefix hocc
  have hkl : k ≤ r.c.length := by
    by_contra h
    have h₁ : r.c.length ∈ a.vars := (hk _).2 (by omega)
    have := (hr.len r.c.length).1 (by rw [ht, tpair_vars]; exact List.mem_append_left _ h₁)
    omega
  let r' : Raw := ⟨a, r.c.take k, r.x.filter fun θ => decide (Low k θ)⟩
  have hlen : r'.c.length = k := by simp [r', hkl]
  have hconj : ∀ v, r'.conj v = if v < k then r.conj v else ∅ := by
    intro v
    simp only [Raw.conj, r', List.getD_eq_getElem?_getD, List.getElem?_take]
    split <;> rfl
  have hx' : ∀ θ, θ ∈ r'.x ↔ θ ∈ r.x ∧ Low k θ := by intro θ; simp [r', List.mem_filter]
  have posr : ∀ σ ∈ r.store.Pos S, σ ∈ r'.store.Pos S := by
    intro σ hσ v
    show MemC S (r'.conj v) (σ v)
    rw [hconj]; split
    · exact hσ v
    · exact memC_empty S _
  have res : ∀ σ ∈ r.store.Sol S, σ ∈ r'.store.Sol S := by
    intro σ hσ
    refine ⟨posr σ hσ.1, fun E hE => ?_⟩
    obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
    exact hσ.2 _ (List.mem_map.2 ⟨θ, ((hx' θ).1 hθ).1, rfl⟩)
  have ext : ∀ σ ∈ r'.store.Sol S, ∃ τ ∈ r.store.Sol S, ∀ v, v < k → τ v = σ v := by
    intro σ hσ
    let H := (List.range r.c.length).filter fun v => decide (k ≤ v)
    have hH : ∀ v, v ∈ H ↔ k ≤ v ∧ v < r.c.length := by
      intro v; simp [H, List.mem_filter, and_comm]
    obtain ⟨τ, hτ, hag, -⟩ := r.store.rich (S := S) H
      (fun h hh => hr.infinite hS ((hH h).1 hh).2) σ
      (fun v hv => by
        show MemC S (r.conj v) (σ v)
        by_cases hvk : v < k
        · have := hσ.1 v
          change MemC S (r'.conj v) (σ v) at this
          simpa only [hconj, hvk, ite_true] using this
        · have : r.c.length ≤ v := by
            by_contra h; exact hv ((hH v).2 ⟨by omega, by omega⟩)
          rw [Raw.Normal.conj_of_ge r this]; exact memC_empty S _)
      []
      (by
        intro E hE
        obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
        have hn := hr.ex θ hθ
        by_cases hlow : Low k θ
        · exact ⟨σ, fun _ _ => rfl, hσ.2 _ (List.mem_map.2 ⟨θ, (hx' θ).2 ⟨hθ, hlow⟩, rfl⟩)⟩
        · simp only [Low, not_forall] at hlow
          obtain ⟨b, hb, hnot⟩ := hlow
          by_cases hb1 : b.1 < k
          · have hex : ∃ v ∈ b.2.vars, k ≤ v := by
              by_contra hno
              exact hnot ⟨hb1, fun v hv => by
                by_contra h; exact hno ⟨v, hv, by omega⟩⟩
            obtain ⟨v, hv, hkv⟩ := hex
            by_cases hu : Eqns.Unifies σ (eqnsOf θ)
            · obtain ⟨g, hg⟩ := exists_ne (σ v)
              refine ⟨update σ v g, fun w hw => ?_, fun hu' => ?_⟩
              · have : w ≠ v := by
                  rintro rfl; exact hw ((hH _).2 ⟨hkv, (hn.ran b hb _ hv).1⟩)
                simp [update, this]
              · have e₁ := hu (Term.var b.1, b.2) (List.mem_map.2 ⟨b, hb, rfl⟩)
                have e₂ := hu' (Term.var b.1, b.2) (List.mem_map.2 ⟨b, hb, rfl⟩)
                have hne : b.1 ≠ v := by omega
                simp only [Term.bind_var] at e₁ e₂
                rw [show update σ v g b.1 = σ b.1 from by simp [update, hne]] at e₂
                have h3 := bind_agree (e₁.symm.trans e₂) v hv
                rw [update_self] at h3
                exact hg h3.symm
            · exact ⟨σ, fun _ _ => rfl, hu⟩
          · have hbv : b.1 ∉ b.2.vars := fun hm => (hn.ran b hb b.1 hm).2 b hb rfl
            obtain ⟨τ, hτ, hne⟩ := exists_not_unifies hb hbv σ
            refine ⟨τ, fun w hw => hτ w ?_, hne⟩
            rintro rfl
            exact hw ((hH _).2 ⟨by omega, hn.dom b hb⟩))
      (by simp)
    exact ⟨τ, hτ, fun v hv => hag v (fun hm => by have := (hH v).1 hm; omega)⟩
  have habind : ∀ {σ τ : Nat → GTerm}, (∀ v, v < k → τ v = σ v) → a.bind τ = a.bind σ :=
    fun h => Term.bind_congr fun v hv => h v ((hk v).1 hv)
  have hfo : a.firstOrder = true := by
    have := hr.fo; rw [ht, tpair_fo, Bool.and_eq_true] at this; exact this.1
  have exsub : ∀ θ, r.Ex S θ ⊆ r'.Ex S θ := fun θ σ hσ => ⟨posr σ hσ.1, hσ.2⟩
  refine ⟨r', ⟨hfo, hoccA, fun v => by rw [hlen]; exact hk v, ?_, ?_, ?_, ?_,
    hr.sorted.filter _⟩, rfl, ?_⟩
  · intro v hv
    rw [hlen] at hv
    obtain ⟨σ, hσ, σ', hσ', hne⟩ := hr.two v (by omega)
    exact ⟨σ, res σ hσ, σ', res σ' hσ', hne⟩
  · intro v hv n
    rw [hlen] at hv
    rw [hconj]; simp only [hv, ite_true]; rw [hr.up v (by omega) n]
    constructor
    · rintro ⟨hn, h⟩
      refine ⟨hn, fun σ hσ => ?_⟩
      obtain ⟨τ, hτ, hag⟩ := ext σ hσ
      rw [← hag v hv]; exact h τ hτ
    · rintro ⟨hn, h⟩
      exact ⟨hn, fun σ hσ => h σ (res σ hσ)⟩
  · intro θ hθ
    obtain ⟨hθr, hlow⟩ := (hx' θ).1 hθ
    have hn := hr.ex θ hθr
    refine ⟨⟨hn.sorted, fun b hb => by rw [hlen]; exact (hlow b hb).1, hn.fo,
      fun b hb v hv => ⟨by rw [hlen]; exact (hlow b hb).2 v hv, (hn.ran b hb v hv).2⟩,
      hn.later⟩, hn.ne, hn.live.mono (exsub θ), ?_⟩
    intro y hy hfree
    rw [hlen] at hy
    obtain ⟨σ, hσ, σ', hσ', hne⟩ := hn.loose y (by omega) hfree
    exact ⟨σ, exsub θ hσ, σ', exsub θ hσ', hne⟩
  · intro θ hθ θ' hθ' hle
    exact hr.anti θ ((hx' θ).1 hθ).1 θ' ((hx' θ').1 hθ').1
      fun σ hσ => ⟨hσ.1, (hle (exsub θ hσ)).2⟩
  · intro g
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨τ, hτ, hag⟩ := ext σ hσ
      exact ⟨τ, hτ, (habind hag).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, res σ hσ, rfl⟩

/-- A tuple of the variables below `n`. -/
def tup : Nat → Pat
  | 0 => .sym ""
  | n + 1 => tpair (.var n) (tup n)

theorem mem_tup_vars {n v : Nat} : v ∈ (tup n).vars ↔ v < n := by
  induction n with
  | zero => simp [tup, Term.vars]
  | succ n ih =>
    rw [tup, tpair_vars, List.mem_append, ih]
    simp only [Term.vars, List.mem_singleton]
    omega

theorem tup_fo (n : Nat) : (tup n).firstOrder = true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tup, tpair_fo, ih]; rfl

/-- A normal store that denotes pairs only has a tpair as its pattern. -/
theorem shape_pair {S : Sorts} {r : Raw} (hr : r.Normal S) (hne : (r.store.Sol S).Nonempty)
    (h : ∀ g ∈ r.store.Den S, ∃ x y, g = tpair x y) : ∃ a b, r.t = tpair a b := by
  obtain ⟨σ, hσ⟩ := hne
  have hfo := hr.fo
  have hden : ∀ τ ∈ r.store.Sol S, ∃ x y, r.t.bind τ = tpair x y := fun τ hτ => h _ ⟨τ, hτ, rfl⟩
  obtain ⟨x, y, hxy⟩ := hden σ hσ
  cases ht : r.t with
  | var v =>
    have hv : v < r.c.length := (hr.len v).1 (by rw [ht]; simp [Term.vars])
    obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hk⟩ := hr.two v hv
    obtain ⟨x₁, y₁, e₁⟩ := hden σ₁ hσ₁
    obtain ⟨x₂, y₂, e₂⟩ := hden σ₂ hσ₂
    rw [ht] at e₁ e₂
    simp only [Term.bind_var] at e₁ e₂
    rw [e₁, e₂, tpair_key, tpair_key] at hk
    exact absurd rfl hk
  | sym f => rw [ht] at hxy; cases hxy
  | app c d =>
    rw [ht] at hxy hfo
    cases c with
    | var w => simp [Term.firstOrder] at hfo
    | sym f => simp [tpair, Term.bind_app] at hxy
    | app e a' =>
      cases e with
      | var w => simp [Term.firstOrder] at hfo
      | sym f =>
        simp only [tpair, Term.bind_app, Term.app.injEq] at hxy
        have : f = "" := by have := hxy.1.1; cases this; rfl
        subst this
        exact ⟨a', d, rfl⟩
      | app e₁ e₂ => simp [tpair, Term.bind_app] at hxy

/-- A store with a first-order pattern, first-order exclusions and finitely
many variables that denotes some term has a normal form. -/
theorem normal_exists {S : Sorts} (hS : S.WellFormed) {s : Store} {N : Nat} (hfin : s.Fin N)
    (hne : (s.Den S).Nonempty) : ∃ r : Raw, r.Normal S ∧ r.store.Den S = s.Den S := by
  let s₁ : Store := ⟨tpair s.t (tup N), s.c, s.x⟩
  have hv₁ : ∀ v, v < N → v ∈ s₁.t.vars := fun v hv => by
    show v ∈ (tpair s.t (tup N)).vars
    rw [tpair_vars]; exact List.mem_append_right _ (mem_tup_vars.2 hv)
  have hfin₁ : s₁.Fin N := by
    refine ⟨?_, ?_, hfin.cv, hfin.xfo, hfin.xv⟩
    · show (tpair s.t (tup N)).firstOrder = true
      rw [tpair_fo, hfin.fo, tup_fo]; rfl
    · intro v hv
      change v ∈ (tpair s.t (tup N)).vars at hv
      rw [tpair_vars, List.mem_append, mem_tup_vars] at hv
      rcases hv with h | h
      · exact hfin.tv v h
      · exact h
  have hfull₁ : s₁.Full :=
    ⟨fun v hv => hfin.cv v (by by_contra h; exact hv (hv₁ v (by omega))),
      fun E hE p hp v hv => hv₁ v (hfin.xv E hE p hp v hv)⟩
  obtain ⟨g₀, σ₀, hσ₀, -⟩ := hne
  have hne₁ : (s₁.Den S).Nonempty := ⟨_, σ₀, hσ₀, rfl⟩
  obtain ⟨s₂, N₂, hfin₂, hfull₂, ht₂, hden₂⟩ := tight_exists hfin₁ hfull₁ hne₁
  obtain ⟨s₃, k, hfin₃, hfull₃, ht₃, hden₃, hocc₃, hv₃⟩ := renum_exists hfin₂ hfull₂ ht₂
  have hne₃ : (s₃.Sol S).Nonempty := by
    have : (s₃.Den S).Nonempty := by rw [hden₃, hden₂]; exact hne₁
    obtain ⟨g, σ, hσ, -⟩ := this; exact ⟨σ, hσ⟩
  obtain ⟨r, hr, hrt, hrsol⟩ := normal_of_tight hS hfin₃ ht₃ hocc₃ hv₃ hne₃
  have hden : r.store.Den S = s₁.Den S := by
    rw [← hden₂, ← hden₃]
    show {g | ∃ σ ∈ r.store.Sol S, g = r.t.bind σ} = {g | ∃ σ ∈ s₃.Sol S, g = s₃.t.bind σ}
    rw [hrsol, hrt]
  obtain ⟨a, b, hab⟩ := shape_pair hr (hr.sol_nonempty hS) (by
    rw [hden]; rintro g ⟨σ, -, rfl⟩; exact ⟨_, _, tpair_bind σ _ _⟩)
  obtain ⟨r', hr', -, hden'⟩ := hr.proj hS hab
  refine ⟨r', hr', ?_⟩
  ext g
  rw [hden']
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have : tpair (a.bind σ) (b.bind σ) ∈ s₁.Den S := by
      rw [← hden]; exact ⟨σ, hσ, by show _ = r.t.bind σ; rw [hab, tpair_bind]⟩
    obtain ⟨τ, hτ, e⟩ := this
    exact ⟨τ, hτ, (tpair_inj (e.trans (tpair_bind τ _ _))).1⟩
  · rintro ⟨τ, hτ, rfl⟩
    have : tpair (s.t.bind τ) ((tup N).bind τ) ∈ r.store.Den S := by
      rw [hden]; exact ⟨τ, hτ, (tpair_bind τ _ _).symm⟩
    obtain ⟨σ, hσ, e⟩ := this
    have e' : tpair (s.t.bind τ) ((tup N).bind τ) = tpair (a.bind σ) (b.bind σ) := by
      rw [e]; show r.t.bind σ = _; rw [hab, tpair_bind]
    exact ⟨σ, hσ, (tpair_inj e').1⟩

end Sorts
end RwLog
