/-
# Constraint problems

Composing or conjoining two spans, or reading a span as written, gives a
*problem*: a pattern, equations that must hold, sorts that patterns must
belong to, and exclusions. A first-order problem with a solution has a normal
store that denotes the same terms (`Prob.normal`): the equations are solved
and their most general solution applied, each sort is pushed down to the
variables of its pattern, and the store that results is brought to normal
form.
-/
import RwLog.Sorts.Hidden

namespace RwLog
namespace Sorts

open Function

/-- A constraint problem. -/
structure Prob where
  /-- The pattern. -/
  t : Pat
  /-- Equations that hold. -/
  e : Eqns Nat
  /-- Patterns with the sort each belongs to. -/
  a : List (Name × Pat)
  /-- Exclusions: of each list, the equations do not all hold. -/
  x : List (Eqns Nat)

namespace Prob

/-- The solutions of a problem. -/
def Sol (S : Sorts) (P : Prob) : Set (Nat → GTerm) :=
  {σ | Eqns.Unifies σ P.e ∧ (∀ a ∈ P.a, mem S a.1 (a.2.bind σ) = true) ∧
    ∀ E ∈ P.x, ¬ Eqns.Unifies σ E}

/-- The ground terms a problem denotes. -/
def Den (S : Sorts) (P : Prob) : Set GTerm := {g | ∃ σ ∈ P.Sol S, g = P.t.bind σ}

/-- The problem is first-order. -/
structure FO (P : Prob) : Prop where
  t : P.t.firstOrder = true
  e : P.e.FO
  a : ∀ a ∈ P.a, a.2.firstOrder = true
  x : ∀ E ∈ P.x, E.FO

end Prob

/-- Sorts of first-order patterns that some substitution satisfies come down
to sorts of variables. -/
theorem exists_atoms {S : Sorts} : ∀ L : List (Name × Pat), (∀ a ∈ L, a.2.firstOrder = true) →
    (∃ τ : Nat → GTerm, ∀ a ∈ L, mem S a.1 (a.2.bind τ) = true) →
    ∃ As : Atoms, ∀ τ : Nat → GTerm,
      (∀ a ∈ L, mem S a.1 (a.2.bind τ) = true) ↔ Atoms.Holds S As τ
  | [], _, _ => ⟨[], fun τ => by simp [Atoms.Holds]⟩
  | (n, p) :: L, hfo, ⟨τ₀, hτ₀⟩ => by
    obtain ⟨As, hAs⟩ := exists_atoms L (fun a ha => hfo a (List.mem_cons_of_mem _ ha))
      ⟨τ₀, fun a ha => hτ₀ a (List.mem_cons_of_mem _ ha)⟩
    have hp : p.firstOrder = true := hfo (n, p) List.mem_cons_self
    cases hpush : push S n p with
    | none =>
      have := push_none hp hpush τ₀
      rw [hτ₀ (n, p) List.mem_cons_self] at this; cases this
    | some as =>
      refine ⟨as ++ As, fun τ => ?_⟩
      rw [Atoms.holds_append, ← hAs τ, ← push_some hp hpush τ]
      simp only [List.mem_cons, forall_eq_or_imp]

/-- A number above every member of a list. -/
def bound (L : List Nat) : Nat := L.foldr max 0 + 1

theorem lt_bound : ∀ {L : List Nat} {v : Nat}, v ∈ L → v < bound L
  | a :: L, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [bound, List.foldr_cons]; omega
    · have := lt_bound h
      simp only [bound, List.foldr_cons] at this ⊢; omega

/-- A first-order problem with a solution has a normal store that denotes the
same terms. -/
theorem Prob.normal {S : Sorts} (hS : S.WellFormed) {P : Prob} (hP : P.FO)
    (hne : (P.Den S).Nonempty) : ∃ r : Raw, r.Normal S ∧ r.store.Den S = P.Den S := by
  classical
  obtain ⟨g₀, σ₀, hσ₀, -⟩ := hne
  cases hsolve : solve P.e with
  | none => exact absurd hσ₀.1 (solve_none hsolve σ₀)
  | some θ =>
    obtain ⟨hθu, hθm⟩ := solve_some hsolve
    have hθfo := solve_fo P.e hP.e θ hsolve
    have fix : ∀ σ : Nat → GTerm, Eqns.Unifies σ P.e → (fun v => (θ v).bind σ) = σ :=
      fun σ hσ => funext (hθm σ hσ)
    have bb : ∀ (q : Pat) (τ : Nat → GTerm), (q.bind θ).bind τ = q.bind fun v => (θ v).bind τ :=
      fun q τ => Term.bind_bind _ _ _
    have uni : ∀ τ : Nat → GTerm, Eqns.Unifies (fun v => (θ v).bind τ) P.e := by
      intro τ p hp
      rw [← bb, ← bb, hθu p hp]
    let L : List (Name × Pat) := P.a.map fun a => (a.1, a.2.bind θ)
    have hL : ∀ τ : Nat → GTerm, (∀ a ∈ L, mem S a.1 (a.2.bind τ) = true) ↔
        ∀ a ∈ P.a, mem S a.1 (a.2.bind fun v => (θ v).bind τ) = true := by
      intro τ
      simp only [L, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, bb]
    obtain ⟨As, hAs⟩ := exists_atoms (S := S) L
      (by
        intro a ha
        obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
        exact Term.fo_bind (hP.a a' ha') fun v _ => hθfo v)
      ⟨σ₀, (hL σ₀).2 (by rw [fix σ₀ hσ₀.1]; exact hσ₀.2.1)⟩
    let c : Nat → Conj := fun v => ((As.filter fun a => a.1 = v).map Prod.snd).toFinset
    have hc : ∀ τ : Nat → GTerm, (∀ v, MemC S (c v) (τ v)) ↔ Atoms.Holds S As τ := by
      intro τ
      constructor
      · intro h a ha
        exact h a.1 a.2 (by simp only [c, List.mem_toFinset, List.mem_map, List.mem_filter]
                            exact ⟨a, ⟨ha, by simp⟩, rfl⟩)
      · intro h v n hn
        simp only [c, List.mem_toFinset, List.mem_map, List.mem_filter] at hn
        obtain ⟨a, ⟨ha, hav⟩, rfl⟩ := hn
        have := h a ha
        simp only [decide_eq_true_eq] at hav
        rwa [hav] at this
    let x' : List (Eqns Nat) := P.x.map fun E => E.map fun p => (p.1.bind θ, p.2.bind θ)
    have hx : ∀ (τ : Nat → GTerm) (E : Eqns Nat),
        Eqns.Unifies τ (E.map fun p => (p.1.bind θ, p.2.bind θ)) ↔
          Eqns.Unifies (fun v => (θ v).bind τ) E := by
      intro τ E
      simp only [Eqns.Unifies, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, bb]
    let s : Store := ⟨P.t.bind θ, c, x'⟩
    let N := bound ((P.t.bind θ).vars ++ As.map Prod.fst ++ x'.flatMap Eqns.vars)
    have hfin : s.Fin N := by
      refine ⟨Term.fo_bind hP.t fun v _ => hθfo v, ?_, ?_, ?_, ?_⟩
      · intro v hv
        exact lt_bound (List.mem_append_left _ (List.mem_append_left _ hv))
      · intro v hv
        show c v = ∅
        rw [Finset.eq_empty_iff_forall_notMem]
        intro n hn
        simp only [c, List.mem_toFinset, List.mem_map, List.mem_filter] at hn
        obtain ⟨a, ⟨ha, hav⟩, rfl⟩ := hn
        simp only [decide_eq_true_eq] at hav
        have : a.1 < N := lt_bound (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map_of_mem ha)))
        omega
      · intro E' hE' q hq
        obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        exact ⟨Term.fo_bind (hP.x E hE p hp).1 fun v _ => hθfo v,
          Term.fo_bind (hP.x E hE p hp).2 fun v _ => hθfo v⟩
      · intro E' hE' q hq v hv
        exact lt_bound (List.mem_append_right _
          (List.mem_flatMap.2 ⟨E', hE', List.mem_flatMap.2 ⟨q, hq, hv⟩⟩))
    have hden : s.Den S = P.Den S := by
      ext g
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        refine ⟨fun v => (θ v).bind τ, ⟨uni τ, (hL τ).1 ((hAs τ).2 ((hc τ).1 hτ.1)), ?_⟩, bb _ _⟩
        intro E hE hu
        exact hτ.2 _ (List.mem_map_of_mem hE) ((hx τ E).2 hu)
      · rintro ⟨σ, hσ, rfl⟩
        have e := fix σ hσ.1
        refine ⟨σ, ⟨(hc σ).2 ((hAs σ).1 ((hL σ).2 (by rw [e]; exact hσ.2.1))), ?_⟩, ?_⟩
        · intro E' hE' hu
          obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
          rw [hx, e] at hu
          exact hσ.2.2 E hE hu
        · show P.t.bind σ = (P.t.bind θ).bind σ
          rw [bb, e]
    obtain ⟨r, hr, hrd⟩ := normal_exists hS hfin (by
      rw [hden]; exact ⟨_, σ₀, hσ₀, rfl⟩)
    exact ⟨r, hr, hrd.trans hden⟩

end Sorts
end RwLog
