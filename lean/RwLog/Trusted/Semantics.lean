/-
# Ground semantics (the specification)

## Constraints

An *interpretation* `M` is a set of ground constraint atoms: the atoms taken
to hold. A theory says which interpretations are allowed. A rule
`h₁, …, hₙ <=> B` is the axiom that, for every ground instance of the
variables of the heads, all heads hold exactly when some ground values of
the variables occurring only in the body make the body hold. `fail` is
false, `.` is true, an atom holds when it is in `M`, and an equation holds
when its two sides are the same term. `T.Model M` says every rule of `T`
holds in `M`. This is defined for every theory: it assumes neither range
restriction, nor termination, nor confluence.
This is the declarative reading of constraint handling rules. Firing rules,
stores and refutation are how an engine computes with it, and they live
outside this file.

So `(pin $x) <=> $x = z.` makes `(pin a)` hold exactly when `a` is `z`, and
`(pin $x) <=> $x = z, (pin z).` says the same thing while also stating that
`(pin z)` holds.

## Relations

In one interpretation, an expression denotes a set of pairs of ground terms.
A span `l {c} -> r` relates `lσ` to `rσ` when every atom of `cσ` holds in
`M`. Union, intersection, composition and converse are the usual ones, and
recursion is the least fixpoint, all in the same `M`. A pair is observable
when some model of the program's theory relates it. Two meanings are
equivalent under a theory when they agree in every model; since every
operator works in one `M` at a time, this is a congruence.
-/
import RwLog.Trusted.Syntax
import Mathlib.Order.FixedPoints

namespace RwLog

/-! ## Interpretations and models -/

/-- An interpretation: the ground constraint atoms that hold. -/
abbrev Interp := Set GTerm

/-- A rule body holds under `σ` in `M`. -/
def Body.HoldsAt (M : Interp) (σ : Nat → GTerm) : Body → Prop
  | .fail => False
  | .conj eqs cs => (∀ e ∈ eqs, e.1.bind σ = e.2.bind σ) ∧ ∀ c ∈ cs, c.bind σ ∈ M

/-- `v` occurs in a head of the rule. -/
def TRule.HeadVar (ρ : TRule) (v : Nat) : Prop := ∃ h ∈ ρ.heads, v ∈ h.vars

/-- A rule holds in `M`: for every ground `σ`, its heads all hold under `σ`
exactly when the body holds under some `τ` that agrees with `σ` on the
variables of the heads (the body-only variables are existential). -/
def TRule.HoldsIn (M : Interp) (ρ : TRule) : Prop :=
  ∀ σ : Nat → GTerm, (∀ h ∈ ρ.heads, h.bind σ ∈ M) ↔
    ∃ τ : Nat → GTerm, (∀ v, ρ.HeadVar v → τ v = σ v) ∧ ρ.body.HoldsAt M τ

/-- `M` is a model of the theory: every rule holds in it. -/
def Theory.Model (T : Theory) (M : Interp) : Prop := ∀ ρ ∈ T, ρ.HoldsIn M

/-! ## Relations in one interpretation -/

/-- A relation between ground terms. -/
abbrev PRel := Set (GTerm × GTerm)

namespace PRel

def comp (R S : PRel) : PRel := {p | ∃ m, (p.1, m) ∈ R ∧ (m, p.2) ∈ S}

def inv (R : PRel) : PRel := {p | (p.2, p.1) ∈ R}

end PRel

/-- The pairs a span relates in `M`. -/
def Span.denAt (M : Interp) (s : Span) : PRel :=
  {p | ∃ σ : Nat → GTerm, p.1 = s.l.bind σ ∧ p.2 = s.r.bind σ ∧ ∀ c ∈ s.c, c.bind σ ∈ M}

/-- Denotation of an expression in `M`, given the meaning `ρ` of each name. -/
def denoteAt (M : Interp) (ρ : Name → PRel) : Rel → PRel
  | .zero => ∅
  | .span s => s.denAt M
  | .or a b => denoteAt M ρ a ∪ denoteAt M ρ b
  | .and a b => denoteAt M ρ a ∩ denoteAt M ρ b
  | .seq a b => (denoteAt M ρ a).comp (denoteAt M ρ b)
  | .conv a => (denoteAt M ρ a).inv
  | .call n => ρ n

theorem denoteAt_mono (M : Interp) {ρ ρ' : Name → PRel} (h : ρ ≤ ρ') :
    ∀ e, denoteAt M ρ e ⊆ denoteAt M ρ' e
  | .zero => le_rfl
  | .span _ => le_rfl
  | .or a b => Set.union_subset_union (denoteAt_mono M h a) (denoteAt_mono M h b)
  | .and a b => Set.inter_subset_inter (denoteAt_mono M h a) (denoteAt_mono M h b)
  | .seq a b => fun _ ⟨m, h1, h2⟩ => ⟨m, denoteAt_mono M h a h1, denoteAt_mono M h b h2⟩
  | .conv a => fun _ hp => denoteAt_mono M h a hp
  | .call n => h n

/-- One unfolding of every definition of the program, in `M`. -/
def ProgramOf.stepAt (P : Program) (M : Interp) : (Name → PRel) →o (Name → PRel) where
  toFun ρ n := denoteAt M ρ (P.body n)
  monotone' _ _ h n := denoteAt_mono M h (P.body n)

/-- The meaning of every name in `M`: the least fixpoint. -/
def ProgramOf.meaningAt (P : Program) (M : Interp) : Name → PRel := OrderHom.lfp (P.stepAt M)

/-- The meaning of an expression in a program, in `M`. -/
def ProgramOf.semAt (P : Program) (M : Interp) (e : Rel) : PRel := denoteAt M (P.meaningAt M) e

theorem ProgramOf.meaningAt_eq (P : Program) (M : Interp) (n : Name) :
    P.meaningAt M n = denoteAt M (P.meaningAt M) (P.body n) := by
  have := OrderHom.map_lfp (P.stepAt M)
  exact (congrFun this n).symm

/-- The observable relation: the pairs some model of the theory relates. -/
def ProgramOf.obs (P : Program) (e : Rel) : PRel :=
  {p | ∃ M, P.theory.Model M ∧ p ∈ P.semAt M e}

/-! ## Equivalence -/

/-- Two interpretation-indexed meanings are equivalent under a theory when
they agree in every model. -/
def MEquiv (T : Theory) (R S : Interp → PRel) : Prop :=
  ∀ M, T.Model M → R M = S M

/-- Equivalent queries have the same observable pairs. -/
theorem MEquiv.obs_eq {P P' : Program} {e e' : Rel} (ht : P'.theory = P.theory)
    (h : MEquiv P.theory (fun M => P'.semAt M e') (fun M => P.semAt M e)) :
    P'.obs e' = P.obs e := by
  ext p
  simp only [ProgramOf.obs, Set.mem_ofPred_eq, ht]
  constructor
  · rintro ⟨M, hM, hp⟩
    have := h M hM; simp only at this; exact ⟨M, hM, this ▸ hp⟩
  · rintro ⟨M, hM, hp⟩
    have := h M hM; simp only at this; exact ⟨M, hM, this.symm ▸ hp⟩

end RwLog
