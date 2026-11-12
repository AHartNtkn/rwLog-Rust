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
`S`. A rule fires when its heads, under one substitution `σ`, are distinct
members of the store. A `fail` body refutes the store. A conjunction body
refutes the store if one of its equations fails under `σ`; otherwise it
removes the matched heads and adds its constraints. This is the ground
reading of an equation unifying the span the rule fires in: the ground
instances that unification removes are exactly those where the equation
fails. Equations never enter a store.

A store holds exactly when it is not refuted. `Refutes` asks whether *some*
sequence of firings reaches `fail`, so refutability never depends on the order
in which rules are tried. In a well-formed theory (`TRule.WellFormed`) every
body variable occurs in the heads, so `σ` determines the whole body. -/

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

/-- The pairs `R` carries in the context of an extra ground store `C`: some
triple for the pair has a store that, together with `C`, the theory cannot
refute. Composition and conjunction with other relations add exactly such
extra stores. -/
def liveIn (T : Theory) (R : GRel) (C : GStore) : Set (GTerm × GTerm) :=
  {p | ∃ S, (p.1, p.2, S) ∈ R ∧ ¬ Refutes T (S ∪ C)}

/-- Equivalence of meanings under a theory: in every context store `C`, the
same pairs are carried. It ignores triples whose store is refutable and
triples whose store is a superset of another's for the same pair, it is a
congruence for the operators (`Equiv.union`, `Equiv.comp`, `Equiv.meet`,
`Equiv.inv`), and it lets a store be replaced by one the theory rewrites it
to, since what matters about a store is only which contexts refute it. -/
def Equiv (T : Theory) (R S : GRel) : Prop :=
  ∀ C : GStore, R.liveIn T C = S.liveIn T C

theorem observe_eq_liveIn (T : Theory) (R : GRel) : R.observe T = R.liveIn T ∅ := by
  ext ⟨a, b⟩
  have h : ∀ S : GStore, S ∪ ∅ = S := fun S => by ext; simp
  simp only [observe, liveIn, Set.mem_ofPred_eq, h]

/-- Equivalent meanings have the same observable pairs. -/
theorem Equiv.observe_eq {T : Theory} {R S : GRel} (h : Equiv T R S) :
    R.observe T = S.observe T := by
  rw [observe_eq_liveIn, observe_eq_liveIn, h ∅]

theorem Equiv.refl (T : Theory) (R : GRel) : Equiv T R R := fun _ => rfl

theorem Equiv.symm {T : Theory} {R S : GRel} (h : Equiv T R S) : Equiv T S R :=
  fun C => (h C).symm

theorem Equiv.trans {T : Theory} {R S U : GRel} (h₁ : Equiv T R S) (h₂ : Equiv T S U) :
    Equiv T R U := fun C => (h₁ C).trans (h₂ C)

theorem Equiv.union {T : Theory} {R R' S S' : GRel} (h₁ : Equiv T R R') (h₂ : Equiv T S S') :
    Equiv T (R ∪ S) (R' ∪ S') := by
  intro C
  have e₁ := h₁ C; have e₂ := h₂ C
  ext p
  simp only [liveIn, Set.mem_union, Set.mem_ofPred_eq] at e₁ e₂ ⊢
  constructor
  · rintro ⟨S₀, h | h, hn⟩
    · obtain ⟨S₁, h', hn'⟩ := (Set.ext_iff.1 e₁ p).1 ⟨S₀, h, hn⟩; exact ⟨S₁, Or.inl h', hn'⟩
    · obtain ⟨S₁, h', hn'⟩ := (Set.ext_iff.1 e₂ p).1 ⟨S₀, h, hn⟩; exact ⟨S₁, Or.inr h', hn'⟩
  · rintro ⟨S₀, h | h, hn⟩
    · obtain ⟨S₁, h', hn'⟩ := (Set.ext_iff.1 e₁ p).2 ⟨S₀, h, hn⟩; exact ⟨S₁, Or.inl h', hn'⟩
    · obtain ⟨S₁, h', hn'⟩ := (Set.ext_iff.1 e₂ p).2 ⟨S₀, h, hn⟩; exact ⟨S₁, Or.inr h', hn'⟩

theorem Equiv.inv {T : Theory} {R R' : GRel} (h : Equiv T R R') : Equiv T R.inv R'.inv := by
  intro C
  ext ⟨a, b⟩
  have := Set.ext_iff.1 (h C) (b, a)
  simpa [liveIn, GRel.inv] using this

theorem liveIn_comp_subset {T : Theory} {R R' S S' : GRel} (h₁ : Equiv T R R') (h₂ : Equiv T S S')
    (C : GStore) : (R.comp S).liveIn T C ⊆ (R'.comp S').liveIn T C := by
  rintro ⟨a, b⟩ ⟨_, ⟨m, S₁, S₂, hR, hS, rfl⟩, hn⟩
  obtain ⟨S₁', hR', hn₁⟩ := (Set.ext_iff.1 (h₁ (S₂ ∪ C)) (a, m)).1
    ⟨S₁, hR, by rwa [← Finset.union_assoc]⟩
  obtain ⟨S₂', hS', hn₂⟩ := (Set.ext_iff.1 (h₂ (S₁' ∪ C)) (m, b)).1
    ⟨S₂, hS, by rwa [← Finset.union_assoc, Finset.union_comm S₂ S₁', Finset.union_assoc]⟩
  refine ⟨S₁' ∪ S₂', ⟨m, S₁', S₂', hR', hS', rfl⟩, ?_⟩
  have hc : S₁' ∪ S₂' ∪ C = S₂' ∪ (S₁' ∪ C) := by
    rw [Finset.union_comm S₁' S₂', Finset.union_assoc]
  rwa [hc]

theorem Equiv.comp {T : Theory} {R R' S S' : GRel} (h₁ : Equiv T R R') (h₂ : Equiv T S S') :
    Equiv T (R.comp S) (R'.comp S') := fun C =>
  (liveIn_comp_subset h₁ h₂ C).antisymm (liveIn_comp_subset h₁.symm h₂.symm C)

theorem liveIn_meet_subset {T : Theory} {R R' S S' : GRel} (h₁ : Equiv T R R') (h₂ : Equiv T S S')
    (C : GStore) : (R.meet S).liveIn T C ⊆ (R'.meet S').liveIn T C := by
  rintro ⟨a, b⟩ ⟨_, ⟨S₁, S₂, hR, hS, rfl⟩, hn⟩
  obtain ⟨S₁', hR', hn₁⟩ := (Set.ext_iff.1 (h₁ (S₂ ∪ C)) (a, b)).1
    ⟨S₁, hR, by rwa [← Finset.union_assoc]⟩
  obtain ⟨S₂', hS', hn₂⟩ := (Set.ext_iff.1 (h₂ (S₁' ∪ C)) (a, b)).1
    ⟨S₂, hS, by rwa [← Finset.union_assoc, Finset.union_comm S₂ S₁', Finset.union_assoc]⟩
  refine ⟨S₁' ∪ S₂', ⟨S₁', S₂', hR', hS', rfl⟩, ?_⟩
  have hc : S₁' ∪ S₂' ∪ C = S₂' ∪ (S₁' ∪ C) := by
    rw [Finset.union_comm S₁' S₂', Finset.union_assoc]
  rwa [hc]

theorem Equiv.meet {T : Theory} {R R' S S' : GRel} (h₁ : Equiv T R R') (h₂ : Equiv T S S') :
    Equiv T (R.meet S) (R'.meet S') := fun C =>
  (liveIn_meet_subset h₁ h₂ C).antisymm (liveIn_meet_subset h₁.symm h₂.symm C)

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
