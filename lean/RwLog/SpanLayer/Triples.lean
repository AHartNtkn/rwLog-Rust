/-
# Ground triples (the span layer's denotation)

The execution layer works with *ground triples* `(a, b, S)`: input term,
output term, and the finite set `S` of ground constraint atoms the pair
carries. A span `l {c} -> r` denotes its instances `(lσ, rσ, cσ)`;
composition and conjunction take the union of the two stores. This is not
the specification: `RwLog.Trusted.Semantics` is. The bridge
(`RwLog.SpanLayer.Bridge`) proves that the meaning in an interpretation `M`
is exactly the pairs of the triples whose store lies inside `M`, so every
statement about triples is a statement about the specification in every
interpretation at once.
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

/-! ## Spans -/

/-- Instantiate a store. -/
def Store.at (c : Store) (σ : Nat → GTerm) : GStore := (c.map (Term.bind σ)).toFinset

/-- The ground triples a span denotes. -/
def Span.den (s : Span) : GRel :=
  {x | ∃ σ : Nat → GTerm, x = (s.l.bind σ, s.r.bind σ, s.c.at σ)}

/-- Every span has a ground instance: the signature has a constant. -/
theorem Span.den_nonempty (s : Span) : (s.den).Nonempty :=
  ⟨_, fun _ => .sym "", rfl⟩

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


theorem Program.meaning_eq (P : Program) (n : Name) :
    P.meaning n = denote P.meaning (P.body n) := by
  have := OrderHom.map_lfp P.step
  exact (congrFun this n).symm

end RwLog
