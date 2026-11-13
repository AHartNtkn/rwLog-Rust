/-
# A tight store has a normal form

A store whose pattern cannot be extended and whose variables are numbered in
the order they first occur is brought to normal form without changing its
solutions (`normal_of_tight`): each variable is given every declared sort
that holds of all its values, each exclusion is replaced by its normal form
or dropped when nothing in the sorts satisfies its equations, the exclusions
that another implies are dropped, and the rest are put in order.
-/
import RwLog.Sorts.Renum
import RwLog.Sorts.Solved
import RwLog.Sorts.UniqueExcl

namespace RwLog
namespace Sorts

open Function

/-- A list has an antichain that covers it. -/
theorem exists_antichain {α : Type} (le : α → α → Prop) (refl : ∀ a, le a a)
    (trans : ∀ a b c, le a b → le b c → le a c) : ∀ L : List α,
    ∃ L' : List α, L'.Nodup ∧ (∀ a ∈ L', a ∈ L) ∧ (∀ a ∈ L, ∃ b ∈ L', le a b) ∧
      ∀ a ∈ L', ∀ b ∈ L', le a b → a = b
  | [] => ⟨[], List.nodup_nil, by simp, by simp, by simp⟩
  | a :: L => by
    classical
    obtain ⟨L', hnd, hsub, hcov, hanti⟩ := exists_antichain le refl trans L
    by_cases h : ∃ b ∈ L', le a b
    · refine ⟨L', hnd, fun b hb => List.mem_cons_of_mem _ (hsub b hb), ?_, hanti⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h
      · exact hcov c hc
    · have hf : ∀ b, b ∈ L'.filter (fun b => decide (¬ le b a)) ↔ b ∈ L' ∧ ¬ le b a := by
        intro b; simp [List.mem_filter]
      refine ⟨a :: L'.filter (fun b => decide (¬ le b a)), ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        exact ⟨fun hm => h ⟨a, ((hf a).1 hm).1, refl a⟩, hnd.filter _⟩
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub b ((hf b).1 hb).1)
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨c, List.mem_cons_self, refl c⟩
        · obtain ⟨b, hb, hcb⟩ := hcov c hc
          by_cases hba : le b a
          · exact ⟨a, List.mem_cons_self, trans _ _ _ hcb hba⟩
          · exact ⟨b, List.mem_cons_of_mem _ ((hf b).2 ⟨hb, hba⟩), hcb⟩
      · intro b hb c hc hbc
        rcases List.mem_cons.1 hb with rfl | hb <;> rcases List.mem_cons.1 hc with rfl | hc
        · rfl
        · exact absurd ⟨c, ((hf c).1 hc).1, hbc⟩ h
        · exact absurd hbc ((hf b).1 hb).2
        · exact hanti b ((hf b).1 hb).1 c ((hf c).1 hc).1 hbc

theorem bindsLE_iff (a b : Binds) : (bindsCmp a b != .gt) = (bindsCmp a b).isLE := by
  cases bindsCmp a b <;> rfl

/-- Exclusions without repeats can be listed in order. -/
theorem exists_sorted (Y : List Binds) (hnd : Y.Nodup) :
    ∃ Z : List Binds, (∀ θ, θ ∈ Z ↔ θ ∈ Y) ∧ Z.Pairwise fun a b => bindsCmp a b = .lt := by
  refine ⟨Y.mergeSort fun a b => bindsCmp a b != .gt, fun θ => List.mem_mergeSort, ?_⟩
  have hp : (Y.mergeSort fun a b => bindsCmp a b != .gt).Pairwise
      fun a b => (bindsCmp a b != .gt) = true := by
    refine List.pairwise_mergeSort ?_ ?_ _
    · intro a b c h₁ h₂
      rw [bindsLE_iff] at h₁ h₂ ⊢
      exact Std.TransCmp.isLE_trans (cmp := listCmp patCmp) h₁ h₂
    · intro a b
      rw [bindsLE_iff, bindsLE_iff]
      have := Std.OrientedCmp.eq_swap (cmp := listCmp patCmp)
        (a := a.map fun p => Term.app (.var p.1) p.2) (b := b.map fun p => Term.app (.var p.1) p.2)
      unfold bindsCmp
      rw [this]
      cases listCmp patCmp (b.map fun p => Term.app (.var p.1) p.2)
        (a.map fun p => Term.app (.var p.1) p.2) <;> rfl
  have hnd' : (Y.mergeSort fun a b => bindsCmp a b != .gt).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.2 hnd
  refine (hp.and hnd').imp ?_
  rintro a b ⟨hle, hne⟩
  cases h : bindsCmp a b with
  | lt => rfl
  | eq => exact absurd (bindsCmp_eq h) hne
  | gt => rw [h] at hle; cases hle

/-- Exclusions over the variables of a raw store, each of which some
substitution in the sorts satisfies, have normal forms that remove the same
substitutions in the sorts. -/
theorem exists_exclusions {S : Sorts} (r : Raw) : ∀ X : List (Eqns Nat),
    (∀ E ∈ X, E.FO) → (∀ E ∈ X, ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, v < r.c.length) →
    (∀ E ∈ X, ∃ σ ∈ r.store.Pos S, ¬ Eqns.Unifies σ E) →
    ∃ Y : List Binds, (∀ θ ∈ Y, NormalBinds S r θ) ∧
      ∀ σ ∈ r.store.Pos S, (∃ E ∈ X, Eqns.Unifies σ E) ↔ ∃ θ ∈ Y, Eqns.Unifies σ (eqnsOf θ)
  | [], _, _, _ => ⟨[], by simp, by simp⟩
  | E :: X, hfo, hv, hprop => by
    obtain ⟨Y, hY, hiff⟩ := exists_exclusions r X
      (fun E' h => hfo E' (List.mem_cons_of_mem _ h)) (fun E' h => hv E' (List.mem_cons_of_mem _ h))
      (fun E' h => hprop E' (List.mem_cons_of_mem _ h))
    by_cases hsat : ∃ σ ∈ r.store.Pos S, Eqns.Unifies σ E
    · obtain ⟨θ, hθ, hEx⟩ := exists_normalBinds r E (hfo E List.mem_cons_self)
        (hv E List.mem_cons_self) hsat (hprop E List.mem_cons_self)
      have key : ∀ σ ∈ r.store.Pos S, Eqns.Unifies σ (eqnsOf θ) ↔ Eqns.Unifies σ E := by
        intro σ hσ
        constructor
        · intro hu
          have : σ ∈ r.Ex S θ := ⟨hσ, hu⟩
          rw [hEx] at this; exact this.2
        · intro hu
          have : σ ∈ r.Ex S θ := by rw [hEx]; exact ⟨hσ, hu⟩
          exact this.2
      refine ⟨θ :: Y, ?_, ?_⟩
      · intro θ' hθ'
        rcases List.mem_cons.1 hθ' with rfl | hθ'
        · exact hθ
        · exact hY θ' hθ'
      · intro σ hσ
        constructor
        · rintro ⟨E', hE', hu⟩
          rcases List.mem_cons.1 hE' with rfl | hE'
          · exact ⟨θ, List.mem_cons_self, (key σ hσ).2 hu⟩
          · obtain ⟨θ', hθ', hu'⟩ := (hiff σ hσ).1 ⟨E', hE', hu⟩
            exact ⟨θ', List.mem_cons_of_mem _ hθ', hu'⟩
        · rintro ⟨θ', hθ', hu⟩
          rcases List.mem_cons.1 hθ' with rfl | hθ'
          · exact ⟨E, List.mem_cons_self, (key σ hσ).1 hu⟩
          · obtain ⟨E', hE', hu'⟩ := (hiff σ hσ).2 ⟨θ', hθ', hu⟩
            exact ⟨E', List.mem_cons_of_mem _ hE', hu'⟩
    · refine ⟨Y, hY, fun σ hσ => ?_⟩
      constructor
      · rintro ⟨E', hE', hu⟩
        rcases List.mem_cons.1 hE' with rfl | hE'
        · exact absurd ⟨σ, hσ, hu⟩ hsat
        · exact (hiff σ hσ).1 ⟨E', hE', hu⟩
      · intro h
        obtain ⟨E', hE', hu'⟩ := (hiff σ hσ).2 h
        exact ⟨E', List.mem_cons_of_mem _ hE', hu'⟩

theorem getD_map_range {α : Type} (f : Nat → α) (k v : Nat) (d : α) :
    ((List.range k).map f).getD v d = if v < k then f v else d := by
  by_cases h : v < k
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-- A tight store with its variables numbered by first occurrence has a normal
form with the same pattern and the same solutions. -/
theorem normal_of_tight {S : Sorts} {s : Store} {k : Nat} (hfin : s.Fin k)
    (ht : s.Tight S) (hocc : FirstOcc s.t.vars) (hvars : ∀ v, v ∈ s.t.vars ↔ v < k)
    (hne : (s.Sol S).Nonempty) :
    ∃ r : Raw, r.Normal S ∧ r.t = s.t ∧ r.store.Sol S = s.Sol S := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hne
  let f : Nat → Conj := fun v => (names S).filter fun n => ∀ σ ∈ s.Sol S, mem S n (σ v) = true
  let cL : List Conj := (List.range k).map f
  have hlen : cL.length = k := by simp [cL]
  have hconj : ∀ (x : List Binds) (v : Nat) (n : Name), n ∈ (Raw.mk s.t cL x).conj v ↔
      v < k ∧ n ∈ names S ∧ ∀ σ ∈ s.Sol S, mem S n (σ v) = true := by
    intro x v n
    show n ∈ cL.getD v ∅ ↔ _
    rw [getD_map_range]
    by_cases h : v < k
    · simp [h, f]
    · simp [h]
  have pos₁ : ∀ x, ∀ σ ∈ s.Sol S, σ ∈ (Raw.mk s.t cL x).store.Pos S := by
    intro x σ hσ v n hn
    exact ((hconj x v n).1 hn).2.2 σ hσ
  have pos₂ : ∀ x, ∀ σ ∈ (Raw.mk s.t cL x).store.Pos S, σ ∈ s.Pos S := by
    intro x σ hσ v n hn
    have hv : v < k := by
      by_contra h
      rw [hfin.cv v (by omega)] at hn; simp at hn
    exact hσ v n ((hconj x v n).2
      ⟨hv, subset_names_of_memC (hσ₀.1 v) hn, fun τ hτ => hτ.1 v n hn⟩)
  obtain ⟨Y, hY, hYiff⟩ := exists_exclusions (S := S) ⟨s.t, cL, []⟩ s.x hfin.xfo
    (fun E hE p hp v hv => by rw [hlen]; exact hfin.xv E hE p hp v hv)
    (fun E hE => ⟨σ₀, pos₁ [] σ₀ hσ₀, hσ₀.2 E hE⟩)
  obtain ⟨Y', hnd, hsub, hcov, hanti⟩ := exists_antichain
    (fun θ θ' : Binds => Raw.Ex S ⟨s.t, cL, []⟩ θ ⊆ Raw.Ex S ⟨s.t, cL, []⟩ θ')
    (fun _ => Set.Subset.rfl) (fun _ _ _ h₁ h₂ => Set.Subset.trans h₁ h₂) Y
  obtain ⟨Z, hZ, hsorted⟩ := exists_sorted Y' hnd
  have hsol : (Raw.store ⟨s.t, cL, Z⟩).Sol S = s.Sol S := by
    ext σ
    constructor
    · rintro ⟨hp, hx⟩
      refine ⟨pos₂ Z σ hp, fun E hE hu => ?_⟩
      obtain ⟨θ, hθ, huθ⟩ := (hYiff σ hp).1 ⟨E, hE, hu⟩
      obtain ⟨θ', hθ', hle⟩ := hcov θ hθ
      exact hx (eqnsOf θ') (List.mem_map.2 ⟨θ', (hZ θ').2 hθ', rfl⟩) (hle ⟨hp, huθ⟩).2
    · intro hσ
      refine ⟨pos₁ Z σ hσ, fun E hE hu => ?_⟩
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
      obtain ⟨E', hE', hu'⟩ := (hYiff σ (pos₁ [] σ hσ)).2 ⟨θ, hsub θ ((hZ θ).1 hθ), hu⟩
      exact hσ.2 E' hE' hu'
  refine ⟨⟨s.t, cL, Z⟩, ⟨hfin.fo, hocc, fun v => by rw [hvars, hlen], ?_, ?_, ?_, ?_, hsorted⟩,
    rfl, hsol⟩
  · intro v hv
    rw [hsol]
    exact ht v ((hvars v).2 (hlen ▸ hv))
  · intro v hv n
    rw [hsol, hconj]
    exact ⟨fun h => h.2, fun h => ⟨hlen ▸ hv, h⟩⟩
  · intro θ hθ
    have h := hY θ (hsub θ ((hZ θ).1 hθ))
    exact ⟨h.toPre, h.ne, h.live, h.loose⟩
  · intro θ hθ θ' hθ' hle
    exact hanti θ ((hZ θ).1 hθ) θ' ((hZ θ').1 hθ') hle

end Sorts
end RwLog
