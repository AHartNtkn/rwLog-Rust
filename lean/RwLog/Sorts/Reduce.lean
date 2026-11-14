/-
# Constraint problems

A problem is a pattern with equations, sorts of patterns, and exclusions
(`Prob`). The sorts of patterns come down to sorts of variables (`pushAll`).
`Norm.lean` brings a problem to its normal store.
-/
import RwLog.Sorts.Push
import RwLog.Sorts.FO

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

/-- The sorts of patterns brought down to sorts of variables; nothing when a
sort rejects a pattern whatever its variables are. -/
def pushAll (S : Sorts) : List (Name × Pat) → Option Atoms
  | [] => some []
  | a :: L =>
    match push S a.1 a.2, pushAll S L with
    | some as, some As => some (as ++ As)
    | _, _ => none

theorem pushAll_some {S : Sorts} : ∀ {L : List (Name × Pat)} {As : Atoms},
    (∀ a ∈ L, a.2.firstOrder = true) → pushAll S L = some As → ∀ τ : Nat → GTerm,
      (∀ a ∈ L, mem S a.1 (a.2.bind τ) = true) ↔ Atoms.Holds S As τ
  | [], As, _, h, τ => by
    simp only [pushAll, Option.some.injEq] at h
    subst h
    simp [Atoms.Holds]
  | a :: L, As, hfo, h, τ => by
    rw [pushAll] at h
    cases hp : push S a.1 a.2 with
    | none => rw [hp] at h; cases h
    | some as =>
      cases hL : pushAll S L with
      | none => rw [hp, hL] at h; cases h
      | some As' =>
        rw [hp, hL] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [Atoms.holds_append,
          ← pushAll_some (fun b hb => hfo b (List.mem_cons_of_mem _ hb)) hL τ,
          ← push_some (hfo a List.mem_cons_self) hp τ]
        simp only [List.mem_cons, forall_eq_or_imp]

theorem pushAll_none {S : Sorts} : ∀ {L : List (Name × Pat)},
    (∀ a ∈ L, a.2.firstOrder = true) → pushAll S L = none → ∀ τ : Nat → GTerm,
      ¬ ∀ a ∈ L, mem S a.1 (a.2.bind τ) = true
  | [], _, h, _ => by simp [pushAll] at h
  | a :: L, hfo, h, τ => by
    intro hall
    rw [pushAll] at h
    cases hp : push S a.1 a.2 with
    | none =>
      have := push_none (hfo a List.mem_cons_self) hp τ
      rw [hall a List.mem_cons_self] at this; cases this
    | some as =>
      cases hL : pushAll S L with
      | none =>
        exact pushAll_none (fun b hb => hfo b (List.mem_cons_of_mem _ hb)) hL τ
          fun b hb => hall b (List.mem_cons_of_mem _ hb)
      | some As' => rw [hp, hL] at h; cases h

/-- A number above every member of a list. -/
def bound (L : List Nat) : Nat := L.foldr max 0 + 1

theorem lt_bound : ∀ {L : List Nat} {v : Nat}, v ∈ L → v < bound L
  | a :: L, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [bound, List.foldr_cons]; omega
    · have := lt_bound h
      simp only [bound, List.foldr_cons] at this ⊢; omega

end Sorts
end RwLog
