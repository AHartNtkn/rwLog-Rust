/-
# Membership of a list

`sorts::among` walks a list of terms and answers whether a term is one of
its members. Terms are shared, so two members are the same term exactly when
they are the same node.
-/
import RwLogVerified.Sorts

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-- `among` decides whether a term is a member of a list. -/
theorem among_loop_spec (hnm : Function.Injective nm) :
    ∀ (L : List Pat) (s : store.Store) (n l : store.TermId) {tn : Pat},
    Inv s → Repr nm s.nodes.val n.val tn → Repr nm s.nodes.val l.val (encList (nm none) L) →
    Room s (2 * L.length + 1) →
    sorts.among_loop s n false l true ⦃ res s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 2 * L.length + 1 ∧ s.ticks.val ≤ s'.ticks.val ∧
        res = decide (tn ∈ L) ⦄ := by
  intro L
  induction L with
  | nil =>
    intro s n l tn hI hn hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.among_loop
    rw [loop]
    simp only [sorts.among_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf (p := Term.sym (nm none)) hl (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok]
    rw [loop]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, K1.nodes, K1.tbl, by simp only [List.length_nil]; omega, by omega, by simp⟩
  | cons p L ih =>
    intro s n l tn hI hn hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.among_loop
    rw [loop]
    simp only [sorts.among_loop.body, ↓reduceIte]
    step with uncons_repr s l hI.toWf (p := Term.app p (encList (nm none) L)) hl
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨m, rest, rfl, rp, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with same_spec s1 m n K1.inv (by unfold Room; omega) as ⟨r1, hres, K2⟩
    obtain ⟨b, s2⟩ := r1
    simp only at hres K2
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    have htb2 : tbl s2 = tbl s := by rw [K2.tbl, K1.tbl]
    by_cases e : m.val = n.val
    · have : b = true := by simp [hres, e]
      subst this
      have hpt : tn = p := by rw [e] at rp; exact hn.unique rp
      simp only [↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      exact ⟨K2.inv, hn2, htb2, by simp only [List.length_cons]; omega, by omega, by simp [hpt]⟩
    · have : b = false := by simp [hres, e]
      subst this
      have hpt : tn ≠ p := fun h => e (Repr.inj hnm hI.nodesOK rp (h ▸ hn))
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 n rest (tn := tn) K2.inv (by rw [hn2]; exact hn) (by rw [hn2]; exact rrest)
        (by unfold Room; omega)
      unfold sorts.among_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hn', htb', ht', hm', hres'⟩
      refine ⟨hI', by rw [hn', hn2], by rw [htb', htb2], by simp only [List.length_cons]; omega,
        by omega, ?_⟩
      rw [hres']
      simp [hpt]

/-- `among` decides whether a term is a member of a list. -/
theorem among_spec (hnm : Function.Injective nm) (L : List Pat) (s : store.Store)
    (n l : store.TermId) {tn : Pat} (hI : Inv s) (hn : Repr nm s.nodes.val n.val tn)
    (hl : Repr nm s.nodes.val l.val (encList (nm none) L)) (hroom : Room s (2 * L.length + 1)) :
    sorts.among s n l ⦃ res s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 2 * L.length + 1 ∧ s.ticks.val ≤ s'.ticks.val ∧
        res = decide (tn ∈ L) ⦄ :=
  among_loop_spec hnm L s n l hI hn hl hroom

end RwLogVerified
