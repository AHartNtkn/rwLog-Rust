/-
# From ground triples to the specification

The specification (`RwLog.Trusted.Semantics`) gives an expression a meaning
in each interpretation `M`. The execution layer computes ground triples
`(a, b, S)` instead. They agree: in `M`, an expression relates exactly the
pairs of its triples whose store lies inside `M` (`Program.semAt_eq`), and
likewise for a span (`Span.denAt_eq`). So an inclusion or equality of triple
sets gives the same inclusion or equality in every interpretation.
-/
import RwLog.SpanLayer.Triples
import RwLog.Trusted.Semantics

namespace RwLog

/-- The pairs of the triples of `R` whose store lies in `M`. -/
def GRel.at (R : GRel) (M : Interp) : PRel :=
  {p | ∃ S : GStore, (p.1, p.2, S) ∈ R ∧ (↑S : Set GTerm) ⊆ M}

theorem GRel.at_mono {R R' : GRel} (h : R ⊆ R') (M : Interp) : R.at M ⊆ R'.at M :=
  fun _ ⟨S, hS, hM⟩ => ⟨S, h hS, hM⟩

theorem Store.at_subset {c : Store} {σ : Nat → GTerm} {M : Interp} :
    (↑(c.at σ) : Set GTerm) ⊆ M ↔ ∀ x ∈ c, x.bind σ ∈ M := by
  simp [Store.at, Set.subset_def]

theorem Span.denAt_eq (M : Interp) (s : Span) : s.denAt M = s.den.at M := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨σ, rfl, rfl, hc⟩
    exact ⟨s.c.at σ, ⟨σ, rfl⟩, Store.at_subset.2 hc⟩
  · rintro ⟨S, ⟨σ, hx⟩, hM⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨σ, rfl, rfl, Store.at_subset.1 hM⟩

theorem union_subset_iff_coe {S₁ S₂ : GStore} {M : Interp} :
    (↑(S₁ ∪ S₂) : Set GTerm) ⊆ M ↔ (↑S₁ : Set GTerm) ⊆ M ∧ (↑S₂ : Set GTerm) ⊆ M := by
  rw [Finset.coe_union, Set.union_subset_iff]

/-- Triples of `denote ρ e` with a store inside `M` give pairs of the
specification, if they do for the names. -/
theorem denote_at_sub (M : Interp) {ρ : Name → GRel} {ρM : Name → PRel}
    (hρ : ∀ n, (ρ n).at M ⊆ ρM n) : ∀ e, (denote ρ e).at M ⊆ denoteAt M ρM e
  | .zero => fun _ ⟨_, h, _⟩ => h.elim
  | .span s => by show (s.den).at M ⊆ s.denAt M; rw [Span.denAt_eq]
  | .or a b => by
    rintro p ⟨S, h | h, hM⟩
    · exact Or.inl (denote_at_sub M hρ a ⟨S, h, hM⟩)
    · exact Or.inr (denote_at_sub M hρ b ⟨S, h, hM⟩)
  | .and a b => by
    rintro p ⟨_, ⟨S₁, S₂, h₁, h₂, rfl⟩, hM⟩
    obtain ⟨hM₁, hM₂⟩ := union_subset_iff_coe.1 hM
    exact ⟨denote_at_sub M hρ a ⟨S₁, h₁, hM₁⟩, denote_at_sub M hρ b ⟨S₂, h₂, hM₂⟩⟩
  | .seq a b => by
    rintro ⟨x, y⟩ ⟨_, ⟨m, S₁, S₂, h₁, h₂, rfl⟩, hM⟩
    obtain ⟨hM₁, hM₂⟩ := union_subset_iff_coe.1 hM
    exact ⟨m, denote_at_sub M hρ a (show (x, m) ∈ (denote ρ a).at M from ⟨S₁, h₁, hM₁⟩),
      denote_at_sub M hρ b (show (m, y) ∈ (denote ρ b).at M from ⟨S₂, h₂, hM₂⟩)⟩
  | .conv a => by
    rintro ⟨x, y⟩ ⟨S, h, hM⟩
    exact denote_at_sub M hρ a (show (y, x) ∈ (denote ρ a).at M from ⟨S, h, hM⟩)
  | .call n => hρ n

/-- Pairs of the specification come from triples with a store inside `M`, if
they do for the names. -/
theorem denote_at_sup (M : Interp) {ρ : Name → GRel} {ρM : Name → PRel}
    (hρ : ∀ n, ρM n ⊆ (ρ n).at M) : ∀ e, denoteAt M ρM e ⊆ (denote ρ e).at M
  | .zero => fun _ h => h.elim
  | .span s => by show s.denAt M ⊆ (s.den).at M; rw [Span.denAt_eq]
  | .or a b => by
    rintro p (h | h)
    · exact GRel.at_mono Set.subset_union_left M (denote_at_sup M hρ a h)
    · exact GRel.at_mono Set.subset_union_right M (denote_at_sup M hρ b h)
  | .and a b => by
    rintro p ⟨h₁, h₂⟩
    obtain ⟨S₁, h₁, hM₁⟩ := denote_at_sup M hρ a h₁
    obtain ⟨S₂, h₂, hM₂⟩ := denote_at_sup M hρ b h₂
    exact ⟨S₁ ∪ S₂, ⟨S₁, S₂, h₁, h₂, rfl⟩, union_subset_iff_coe.2 ⟨hM₁, hM₂⟩⟩
  | .seq a b => by
    rintro ⟨x, y⟩ ⟨m, h₁, h₂⟩
    obtain ⟨S₁, h₁, hM₁⟩ := denote_at_sup M hρ a h₁
    obtain ⟨S₂, h₂, hM₂⟩ := denote_at_sup M hρ b h₂
    exact ⟨S₁ ∪ S₂, ⟨m, S₁, S₂, h₁, h₂, rfl⟩, union_subset_iff_coe.2 ⟨hM₁, hM₂⟩⟩
  | .conv a => by
    rintro ⟨x, y⟩ h
    obtain ⟨S, h, hM⟩ := denote_at_sup M hρ a h
    exact ⟨S, h, hM⟩
  | .call n => hρ n

/-- **Bridge.** In every interpretation, the meaning of a name is the pairs of
its triples whose store lies inside the interpretation. -/
theorem Program.meaningAt_eq_at (P : Program) (M : Interp) (n : Name) :
    P.meaningAt M n = (P.meaning n).at M := by
  apply le_antisymm
  · -- the pairs of the triples form a pre-fixed point of the step in `M`
    have hpre : P.stepAt M (fun n => (P.meaning n).at M) ≤ fun n => (P.meaning n).at M := by
      intro n p hp
      have := denote_at_sup M (ρ := P.meaning) (fun _ => le_rfl) (P.body n) hp
      rwa [← P.meaning_eq] at this
    exact OrderHom.lfp_le _ hpre n
  · -- the triples whose store lies in `M` and whose pair is in the meaning in
    -- `M` form a pre-fixed point of the triple step
    let ρ' : Name → GRel := fun n => {x | (↑x.2.2 : Set GTerm) ⊆ M → (x.1, x.2.1) ∈ P.meaningAt M n}
    have key : ∀ e, ∀ x ∈ denote ρ' e, (↑x.2.2 : Set GTerm) ⊆ M →
        (x.1, x.2.1) ∈ denoteAt M (P.meaningAt M) e := by
      intro e x hx hM
      exact denote_at_sub M (ρ := ρ') (fun n _ ⟨S, hS, hSM⟩ => hS hSM) e ⟨x.2.2, hx, hM⟩
    have hpre : P.step ρ' ≤ ρ' := by
      intro n x hx hM
      rw [P.meaningAt_eq]
      exact key _ x hx hM
    have hle : P.meaning ≤ ρ' := OrderHom.lfp_le _ hpre
    rintro p ⟨S, hS, hM⟩
    exact hle n hS hM

/-- **Bridge.** In every interpretation, an expression relates exactly the
pairs of its triples whose store lies inside the interpretation. -/
theorem Program.semAt_eq (P : Program) (M : Interp) (e : Rel) : P.semAt M e = (P.sem e).at M := by
  apply le_antisymm
  · exact denote_at_sup M (fun n => (P.meaningAt_eq_at M n).le) e
  · exact denote_at_sub M (fun n => (P.meaningAt_eq_at M n).ge) e

end RwLog
