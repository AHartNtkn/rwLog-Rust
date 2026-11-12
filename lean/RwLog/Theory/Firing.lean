/-
# Rule firing is sound for the declarative reading

The specification (`RwLog.Trusted.Semantics`) reads a theory as axioms about
interpretations and says nothing about firing. This file defines firing on
ground stores and proves it sound for every theory: if firing derives `fail`
from a ground store `S`, then no model of the theory contains `S`
(`Refutes.sound`). So an engine that drops an answer because its store fires
to `fail` never drops a real answer.

The side conditions are the ones the proof uses, and no others:

* stores are ground (lists of ground atoms);
* a rule fires only when it is range-restricted (`TRule.WellFormed`), so its
  body has no variable that the match of its heads leaves unbound. A rule
  with body-only variables still has a meaning, it just never fires;
* heads match atoms of the store by membership, so two heads may match the
  same atom. This is sound because the axiom holds for every instance of the
  head variables, including those that make two heads equal.

Neither termination nor confluence is assumed: they matter only for the
converse (a store that no model contains fires to `fail`).
-/
import RwLog.Trusted.Semantics

namespace RwLog

/-- The ground instance of a pattern list under `σ`. -/
def instAll (ps : List Pat) (σ : Nat → GTerm) : List GTerm := ps.map (Term.bind σ)

/-- Variables of a body: those of its constraints and of its equations. -/
def Body.Var (b : Body) (v : Nat) : Prop :=
  (∃ c ∈ b.atoms, v ∈ c.vars) ∨ ∃ e ∈ b.eqs, v ∈ e.1.vars ++ e.2.vars

theorem Body.holdsAt_congr {M : Interp} {σ τ : Nat → GTerm} :
    ∀ {b : Body}, (∀ v, b.Var v → σ v = τ v) → (b.HoldsAt M σ ↔ b.HoldsAt M τ)
  | .fail, _ => Iff.rfl
  | .conj eqs cs, h => by
    have hc : ∀ c ∈ cs, c.bind σ = c.bind τ := fun c hc =>
      Term.bind_congr fun v hv => h v (Or.inl ⟨c, hc, hv⟩)
    have he : ∀ e ∈ eqs, e.1.bind σ = e.1.bind τ ∧ e.2.bind σ = e.2.bind τ := fun e he =>
      ⟨Term.bind_congr fun v hv => h v (Or.inr ⟨e, he, List.mem_append_left _ hv⟩),
        Term.bind_congr fun v hv => h v (Or.inr ⟨e, he, List.mem_append_right _ hv⟩)⟩
    simp only [Body.HoldsAt]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun e hm => (he e hm).1 ▸ (he e hm).2 ▸ h₁ e hm, fun c hm => hc c hm ▸ h₂ c hm⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun e hm => (he e hm).1.symm ▸ (he e hm).2.symm ▸ h₁ e hm,
        fun c hm => (hc c hm).symm ▸ h₂ c hm⟩

theorem TRule.WellFormed.headVar {ρ : TRule} (hw : ρ.WellFormed) {v : Nat}
    (hv : ρ.body.Var v) : ρ.HeadVar v := by
  rcases hv with ⟨c, hc, hv⟩ | ⟨e, he, hv⟩
  · exact hw.1 c hc v hv
  · exact hw.2 e he v hv

/-- For a range-restricted rule, the existential in `TRule.HoldsIn` is
trivial: the heads hold under `σ` exactly when the body does. -/
theorem TRule.holdsIn_iff {M : Interp} {ρ : TRule} (hw : ρ.WellFormed) :
    ρ.HoldsIn M ↔ ∀ σ : Nat → GTerm, (∀ h ∈ ρ.heads, h.bind σ ∈ M) ↔ ρ.body.HoldsAt M σ := by
  have key : ∀ σ : Nat → GTerm, (∃ τ : Nat → GTerm, (∀ v, ρ.HeadVar v → τ v = σ v) ∧
      ρ.body.HoldsAt M τ) ↔ ρ.body.HoldsAt M σ := fun σ =>
    ⟨fun ⟨τ, hτ, hb⟩ => (Body.holdsAt_congr fun v hv => hτ v (hw.headVar hv)).1 hb,
      fun hb => ⟨σ, fun _ _ => rfl, hb⟩⟩
  simp only [TRule.HoldsIn, key]

/-- One firing on a ground store: `some S'` is the next store, `none` is
`fail`. The matched heads are removed and the body's constraints are added;
an equation of the body that does not hold, or a `fail` body, refutes. -/
inductive Fire (T : Theory) : List GTerm → Option (List GTerm) → Prop
  | step {S : List GTerm} {ρ : TRule} {σ : Nat → GTerm} {eqs : List (Pat × Pat)} {cs : List Pat} :
      ρ ∈ T → ρ.WellFormed → (∀ h ∈ ρ.heads, h.bind σ ∈ S) → ρ.body = .conj eqs cs →
      (∀ e ∈ eqs, e.1.bind σ = e.2.bind σ) →
      Fire T S (some (S.filter (· ∉ instAll ρ.heads σ) ++ instAll cs σ))
  | eqFail {S : List GTerm} {ρ : TRule} {σ : Nat → GTerm} {eqs : List (Pat × Pat)} {cs : List Pat} :
      ρ ∈ T → ρ.WellFormed → (∀ h ∈ ρ.heads, h.bind σ ∈ S) → ρ.body = .conj eqs cs →
      (∃ e ∈ eqs, e.1.bind σ ≠ e.2.bind σ) → Fire T S none
  | fail {S : List GTerm} {ρ : TRule} {σ : Nat → GTerm} :
      ρ ∈ T → ρ.WellFormed → (∀ h ∈ ρ.heads, h.bind σ ∈ S) → ρ.body = .fail → Fire T S none

/-- Firing derives `fail` from the store in finitely many steps. -/
inductive Refutes (T : Theory) : List GTerm → Prop
  | now {S : List GTerm} : Fire T S none → Refutes T S
  | next {S S' : List GTerm} : Fire T S (some S') → Refutes T S' → Refutes T S

/-- A firing step keeps a store inside every model that contains it, and
never refutes a store some model contains. -/
theorem Fire.sound {T : Theory} {S : List GTerm} {o : Option (List GTerm)} (hf : Fire T S o)
    {M : Interp} (hM : T.Model M) (hS : ∀ x ∈ S, x ∈ M) : ∃ S', o = some S' ∧ ∀ x ∈ S', x ∈ M := by
  cases hf with
  | step hρ hw hh hb heq =>
    have hbody := ((TRule.holdsIn_iff hw).1 (hM _ hρ) _).1 fun h hm => hS _ (hh h hm)
    rw [hb] at hbody
    refine ⟨_, rfl, fun x hx => ?_⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hS x (List.mem_of_mem_filter hx)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      exact hbody.2 c hc
  | eqFail hρ hw hh hb hne =>
    have hbody := ((TRule.holdsIn_iff hw).1 (hM _ hρ) _).1 fun h hm => hS _ (hh h hm)
    rw [hb] at hbody
    obtain ⟨e, he, hne⟩ := hne
    exact (hne (hbody.1 e he)).elim
  | fail hρ hw hh hb =>
    have hbody := ((TRule.holdsIn_iff hw).1 (hM _ hρ) _).1 fun h hm => hS _ (hh h hm)
    rw [hb] at hbody
    exact hbody.elim

/-- **Soundness of firing.** For every theory, if firing derives `fail` from a
ground store, no model of the theory contains the store. -/
theorem Refutes.sound {T : Theory} {S : List GTerm} (h : Refutes T S) {M : Interp}
    (hM : T.Model M) : ¬ ∀ x ∈ S, x ∈ M := by
  induction h with
  | now hf =>
    intro hS
    obtain ⟨_, h, _⟩ := hf.sound hM hS
    cases h
  | next hf _ ih =>
    intro hS
    obtain ⟨_, h, hS'⟩ := hf.sound hM hS
    cases h
    exact ih hS'

end RwLog
