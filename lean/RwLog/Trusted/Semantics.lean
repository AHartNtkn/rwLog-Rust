/-
# Ground semantics (the specification)

An expression denotes a set of *ground triples* `(a, b, S)`: input term,
output term, and the finite set `S` of ground constraints the pair carries.
A span `l {c} -> r` denotes its instances `(lσ, rσ, cσ)`. Composition and
conjunction combine the stores of the two sides, so a constraint from one
span can interact with a constraint from another. Recursion is the least
fixpoint.

The observable relation keeps the pairs that carry a store the program's
theory cannot refute (`GRel.observe`). Refutability is monotone in the store
(`Refutes.mono`), so discarding refuted triples early never changes what is
observed. Because constraints of different spans interact, the observable
pairs of `R ; S` are not determined by the observable pairs of `R` and `S`
alone; equality of meaning is therefore equality of triples.
-/
import RwLog.Trusted.Syntax
import Mathlib.Order.FixedPoints
import Mathlib.Data.Finset.Basic

namespace RwLog

/-- A finite set of ground constraints. -/
abbrev GStore := Finset GTerm

/-- Ground triples: input, output, store. -/
abbrev GRel := Set (GTerm × GTerm × GStore)

namespace GRel

/-- Composition: the middle terms agree and the stores are combined. -/
def comp (R S : GRel) : GRel :=
  {x | ∃ m S₁ S₂, (x.1, m, S₁) ∈ R ∧ (m, x.2.1, S₂) ∈ S ∧ x.2.2 = S₁ ∪ S₂}

/-- Conjunction: both relate the same pair, and the stores are combined. -/
def meet (R S : GRel) : GRel :=
  {x | ∃ S₁ S₂, (x.1, x.2.1, S₁) ∈ R ∧ (x.1, x.2.1, S₂) ∈ S ∧ x.2.2 = S₁ ∪ S₂}

/-- Converse. -/
def inv (R : GRel) : GRel := {x | (x.2.1, x.1, x.2.2) ∈ R}

end GRel

/-! ## Constraint theories

`Refutes T S` holds when the rules of `T` derive `fail` from the ground store
`S`. A rule fires when its heads, under one substitution, are distinct members
of the store; it then either refutes the store (body `fail`) or replaces the
matched constraints by its body. A store holds exactly when it is not
refuted. `Refutes` asks whether *some* sequence of firings reaches `fail`, so
refutability never depends on the order in which rules are tried. -/

/-- The heads of a rule, instantiated. -/
def TRule.headsAt (ρ : TRule) (σ : Nat → GTerm) : List GTerm := ρ.heads.map (Term.bind σ)

/-- The heads of the rule, instantiated by `σ`, are distinct members of `S`. -/
def TRule.Fires (ρ : TRule) (σ : Nat → GTerm) (S : GStore) : Prop :=
  (ρ.headsAt σ).Nodup ∧ ∀ h ∈ ρ.headsAt σ, h ∈ S

inductive Refutes (T : Theory) : GStore → Prop
  | fail {S : GStore} {ρ : TRule} (hρ : ρ ∈ T) (σ : Nat → GTerm)
      (hb : ρ.body = .fail) (hf : ρ.Fires σ S) : Refutes T S
  | conj {S : GStore} {ρ : TRule} {cs : List Pat} (hρ : ρ ∈ T) (σ : Nat → GTerm)
      (hb : ρ.body = .conj cs) (hf : ρ.Fires σ S)
      (h : Refutes T (S \ (ρ.headsAt σ).toFinset ∪ (cs.map (Term.bind σ)).toFinset)) :
      Refutes T S

/-- A rule is well formed when it has a head and every variable of its body
occurs in its heads. (A body variable not bound by the heads would have to
hold for every value, which firing by matching cannot express.) -/
def TRule.WellFormed (ρ : TRule) : Prop :=
  ρ.heads ≠ [] ∧
  match ρ.body with
  | .fail => True
  | .conj cs => ∀ c ∈ cs, ∀ v ∈ c.vars, ∃ h ∈ ρ.heads, v ∈ h.vars

namespace GRel

/-- The observable pairs: those carrying a store the theory cannot refute. -/
def observe (T : Theory) (R : GRel) : Set (GTerm × GTerm) :=
  {p | ∃ S, (p.1, p.2, S) ∈ R ∧ ¬ Refutes T S}

end GRel

/-! ## Spans -/

/-- Instantiate a store. -/
def Store.at (c : Store) (σ : Nat → GTerm) : GStore := (c.map (Term.bind σ)).toFinset

/-- The ground triples a span denotes. -/
def Span.den (s : Span) : GRel :=
  {x | ∃ σ : Nat → GTerm, x = (s.l.bind σ, s.r.bind σ, s.c.at σ)}

/-! ## Relations -/

/-- Denotation of an expression, given the meaning `ρ` of each name. -/
def denote (ρ : Name → GRel) : Rel → GRel
  | .zero => ∅
  | .span s => s.den
  | .or a b => denote ρ a ∪ denote ρ b
  | .and a b => (denote ρ a).meet (denote ρ b)
  | .seq a b => (denote ρ a).comp (denote ρ b)
  | .conv a => (denote ρ a).inv
  | .call n => ρ n

theorem denote_mono {ρ ρ' : Name → GRel} (h : ρ ≤ ρ') :
    ∀ e, denote ρ e ⊆ denote ρ' e
  | .zero => le_rfl
  | .span _ => le_rfl
  | .or a b => Set.union_subset_union (denote_mono h a) (denote_mono h b)
  | .and a b => fun _ ⟨S₁, S₂, h1, h2, hu⟩ =>
      ⟨S₁, S₂, denote_mono h a h1, denote_mono h b h2, hu⟩
  | .seq a b => fun _ ⟨m, S₁, S₂, h1, h2, hu⟩ =>
      ⟨m, S₁, S₂, denote_mono h a h1, denote_mono h b h2, hu⟩
  | .conv a => fun _ hp => denote_mono h a hp
  | .call n => h n

/-- One unfolding of every definition of the program. -/
def Program.step (P : Program) : (Name → GRel) →o (Name → GRel) where
  toFun ρ n := denote ρ (P.body n)
  monotone' _ _ h n := denote_mono h (P.body n)

/-- The meaning of every name: the least fixpoint. -/
def Program.meaning (P : Program) : Name → GRel := OrderHom.lfp P.step

/-- The meaning (as triples) of an expression in a program. -/
def Program.sem (P : Program) (e : Rel) : GRel := denote P.meaning e

/-- The observable relation of an expression in a program. -/
def Program.obs (P : Program) (e : Rel) : Set (GTerm × GTerm) :=
  (P.sem e).observe P.theory

theorem Program.meaning_eq (P : Program) (n : Name) :
    P.meaning n = denote P.meaning (P.body n) := by
  have := OrderHom.map_lfp P.step
  exact (congrFun this n).symm

end RwLog

namespace RwLog

/-- Refutability is monotone: more constraints can only make refutation
easier. -/
theorem Refutes.mono {T : Theory} {S : GStore} (h : Refutes T S) :
    ∀ {S'}, S ⊆ S' → Refutes T S' := by
  induction h with
  | fail hρ σ hb hf =>
    intro S' hS
    exact .fail hρ σ hb ⟨hf.1, fun x hx => hS (hf.2 x hx)⟩
  | conj hρ σ hb hf _ ih =>
    intro S' hS
    refine .conj hρ σ hb ⟨hf.1, fun x hx => hS (hf.2 x hx)⟩ (ih ?_)
    exact Finset.union_subset_union (Finset.sdiff_subset_sdiff hS le_rfl) le_rfl

namespace GRel

/-- The pairs a relation carries using only constraints from the store `M`. -/
def within (R : GRel) (M : GStore) : Set (GTerm × GTerm) :=
  {p | ∃ S ⊆ M, (p.1, p.2, S) ∈ R}

/-- Equivalence of meanings under a theory: for every non-refutable store `M`,
the same pairs are carried within `M`. This ignores triples whose store is
refutable and triples whose store is a superset of another's for the same
pair, and every operator acts pointwise in `M`. -/
def Equiv (T : Theory) (R S : GRel) : Prop :=
  ∀ M : GStore, ¬ Refutes T M → R.within M = S.within M

/-- The observable pairs are the union, over non-refutable stores `M`, of the
pairs carried within `M`. -/
theorem observe_eq_iUnion_within (T : Theory) (R : GRel) :
    R.observe T = ⋃ (M : GStore) (_ : ¬ Refutes T M), R.within M := by
  ext ⟨a, b⟩
  simp only [observe, within, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨S, hS, hn⟩
    exact ⟨S, hn, S, le_rfl, hS⟩
  · rintro ⟨M, hM, S, hSM, hS⟩
    exact ⟨S, hS, fun h => hM (h.mono hSM)⟩

/-- Equivalent meanings have the same observable pairs. -/
theorem Equiv.observe_eq {T : Theory} {R S : GRel} (h : Equiv T R S) :
    R.observe T = S.observe T := by
  rw [observe_eq_iUnion_within, observe_eq_iUnion_within]
  refine Set.iUnion_congr fun M => ?_
  by_cases hM : Refutes T M
  · simp [hM]
  · simp [hM, h M hM]

end GRel

end RwLog
