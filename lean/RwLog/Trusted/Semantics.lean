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
matched constraints by its body. The body's equations are tests on the
ground instance: when one fails, the firing refutes the store, and when all
hold, the firing goes on. A store holds exactly when it is not
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
  | eq {S : GStore} {ρ : TRule} {eqs : List (Pat × Pat)} {cs : List Pat} {e : Pat × Pat}
      (hρ : ρ ∈ T) (σ : Nat → GTerm) (hb : ρ.body = .conj eqs cs) (hf : ρ.Fires σ S)
      (he : e ∈ eqs) (hne : e.1.bind σ ≠ e.2.bind σ) : Refutes T S
  | conj {S : GStore} {ρ : TRule} {eqs : List (Pat × Pat)} {cs : List Pat} (hρ : ρ ∈ T)
      (σ : Nat → GTerm) (hb : ρ.body = .conj eqs cs) (hf : ρ.Fires σ S)
      (heq : ∀ e ∈ eqs, e.1.bind σ = e.2.bind σ)
      (h : Refutes T (S \ (ρ.headsAt σ).toFinset ∪ (cs.map (Term.bind σ)).toFinset)) :
      Refutes T S

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
  | eq hρ σ hb hf he hne =>
    intro S' hS
    exact .eq hρ σ hb ⟨hf.1, fun x hx => hS (hf.2 x hx)⟩ he hne
  | conj hρ σ hb hf heq _ ih =>
    intro S' hS
    refine .conj hρ σ hb ⟨hf.1, fun x hx => hS (hf.2 x hx)⟩ heq (ih ?_)
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

/-! ## Coverage and dead spans

These are the two notions the execution theorems are stated with, once an
engine may prune refuted answers and drop answers that a more general one
already covers. -/

/-- `a` covers `s`: every ground triple of `s` is matched by a triple of `a`
with the same pair and a store contained in it. A covering answer carries
every pair the covered one carries, within every store. -/
def Span.Covers (a s : Span) : Prop :=
  ∀ x ∈ s.den, ∃ y ∈ a.den, y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 ⊆ x.2.2

/-- Two spans are equivalent answers when each covers the other. -/
def Span.Equiv (a b : Span) : Prop := a.Covers b ∧ b.Covers a

/-- A span is dead under a theory when every ground instance carries a store
the theory refutes. A dead span has no observable pair. -/
def Span.Dead (T : Theory) (s : Span) : Prop := ∀ σ : Nat → GTerm, Refutes T (s.c.at σ)

/-- `a` covers the unrefuted instances of `s`: every ground triple of `s`
whose store the theory cannot refute is matched by a triple of `a` with the
same pair and a store contained in it. This is coverage up to refutation, the
coverage an engine owes when it prunes and simplifies. -/
def Span.CoversLive (T : Theory) (a s : Span) : Prop :=
  ∀ x ∈ s.den, ¬ Refutes T x.2.2 → ∃ y ∈ a.den, y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 ⊆ x.2.2

/-- `a` refines `s` under a theory: `a` denotes some of the triples of `s`,
including every one whose store the theory cannot refute. Instantiating a span
by an equation its theory forces is a refinement. -/
def Span.Refines (T : Theory) (a s : Span) : Prop :=
  a.den ⊆ s.den ∧ ∀ x ∈ s.den, ¬ Refutes T x.2.2 → x ∈ a.den

theorem Span.Covers.live {T : Theory} {a s : Span} (h : a.Covers s) : a.CoversLive T s :=
  fun x hx _ => h x hx

theorem Span.Covers.refl (a : Span) : a.Covers a :=
  fun x hx => ⟨x, hx, rfl, rfl, le_rfl⟩

theorem Span.Covers.trans {a b c : Span} (h₁ : a.Covers b) (h₂ : b.Covers c) : a.Covers c := by
  intro x hx
  obtain ⟨y, hy, h1, h2, h3⟩ := h₂ x hx
  obtain ⟨z, hz, k1, k2, k3⟩ := h₁ y hy
  exact ⟨z, hz, k1.trans h1, k2.trans h2, k3.trans h3⟩

theorem Span.Covers.of_den_subset {a s : Span} (h : s.den ⊆ a.den) : a.Covers s :=
  fun x hx => ⟨x, h hx, rfl, rfl, le_rfl⟩

end RwLog
