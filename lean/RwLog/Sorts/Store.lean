/-
# Stores

A store is what a span carries beside its two sides: the sorts of each
variable, and exclusions. An exclusion is a list of equations between patterns, and says
that the equations do not all hold. `$x != $y` is the exclusion `[($x, $y)]`.

The *solutions* of a store are the ground substitutions that put every
variable in its sorts and satisfy no exclusion. A store is kept with one
pattern (for a span, its two sides paired), and *denotes* the instances of
the pattern under its solutions.

`Store.rich` is the form of the independence lemma used from here on: if the
variables of a list each range over infinitely many values, and each
exclusion and each of finitely many further disequations can be satisfied by
some choice of those variables, then one solution satisfies them all.
-/
import RwLog.Sorts.Push
import RwLog.Sorts.Indep
import RwLog.Kernel.Solve

namespace RwLog

/-- The head symbol of a term and the number of its arguments. -/
def Term.key {V : Type} (t : Term V) : Option (Sym × Nat) :=
  t.spine.map fun p => (p.1, p.2.length)

theorem Term.spine_bind {V W : Type} (σ : V → Term W) : ∀ {t : Term V} {f : Sym} {as : List (Term V)},
    t.spine = some (f, as) → (t.bind σ).spine = some (f, as.map (Term.bind σ))
  | .var _, _, _, h => by simp [Term.spine] at h
  | .sym g, f, as, h => by
    simp only [Term.spine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | .app t u, f, as, h => by
    simp only [Term.spine, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨g, bs⟩, hs, rfl, rfl⟩ := h
    simp [Term.spine, Term.spine_bind σ hs]

theorem Term.key_bind {V W : Type} (σ : V → Term W) {t : Term V} {k : Sym × Nat}
    (h : t.key = some k) : (t.bind σ).key = some k := by
  unfold Term.key at h ⊢
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨f, as⟩, hs, rfl⟩ := h
  simp [Term.spine_bind σ hs]

/-- A first-order term that is not a variable has a head symbol. -/
theorem Term.key_isSome {V : Type} : ∀ {t : Term V}, t.firstOrder = true → (∀ x, t ≠ .var x) →
    t.key.isSome = true
  | .var x, _, h => absurd rfl (h x)
  | .sym f, _, _ => rfl
  | .app (.var x) u, h, _ => by simp [Term.firstOrder] at h
  | .app (.sym f) u, _, _ => rfl
  | .app (.app a b) u, h, _ => by
    have h' : (Term.app a b).firstOrder = true := by
      simp only [Term.firstOrder, Bool.and_eq_true] at h; exact h.1
    have := Term.key_isSome h' (by simp)
    simp only [Term.key, Option.isSome_map] at this ⊢
    rw [Option.isSome_iff_exists] at this ⊢
    obtain ⟨p, hp⟩ := this
    exact ⟨(p.1, p.2 ++ [u]), by rw [Term.spine, hp]; rfl⟩

namespace Sorts

open Function

/-- A ground term has a head symbol. -/
theorem key_ground (g : GTerm) : ∃ k, g.key = some k := by
  obtain ⟨f, ts, rfl, -⟩ := exists_mk g
  exact ⟨(f, ts.length), by simp [Term.key, Term.spine_mk]⟩

/-- A store with the pattern it is kept with. -/
structure Store where
  /-- The pattern. -/
  t : Pat
  /-- The sorts of each variable; no sorts allow every term. -/
  c : Nat → Conj
  /-- The exclusions: of each list, the equations do not all hold. -/
  x : List (Eqns Nat)

/-- The substitutions that put every variable in its sorts. -/
def Store.Pos (S : Sorts) (s : Store) : Set (Nat → GTerm) := {σ | ∀ v, MemC S (s.c v) (σ v)}

/-- The solutions of a store. -/
def Store.Sol (S : Sorts) (s : Store) : Set (Nat → GTerm) :=
  {σ | σ ∈ s.Pos S ∧ ∀ E ∈ s.x, ¬ Eqns.Unifies σ E}

/-- The ground terms a store denotes. -/
def Store.Den (S : Sorts) (s : Store) : Set GTerm := {g | ∃ σ ∈ s.Sol S, g = s.t.bind σ}

/-- Under well-formed sorts, sorts with two terms in common have infinitely
many. -/
theorem conj_infinite {S : Sorts} (hS : S.WellFormed) (c : Conj) {g₁ g₂ : GTerm}
    (h₁ : MemC S c g₁) (h₂ : MemC S c g₂) (hne : g₁ ≠ g₂) : {g | MemC S c g}.Infinite := by
  have e : {g | MemC S c g} = {t : GTerm | ∀ n ∈ c.toList, S.Mem n t} := by
    ext g
    simp only [Set.mem_ofPred_eq, memC_iff_Mem, Finset.mem_toList]
  have h₁' : g₁ ∈ {g | MemC S c g} := h₁
  have h₂' : g₂ ∈ {g | MemC S c g} := h₂
  rw [e] at h₁' h₂' ⊢
  rcases hS c.toList with he | ⟨t, ht⟩ | hi
  · rw [he] at h₁'; exact absurd h₁' (Set.notMem_empty _)
  · rw [ht] at h₁' h₂'
    exact absurd (h₁'.trans h₂'.symm) hne
  · exact hi

/-- Whether a substitution satisfies equations depends only on the values of
their variables. -/
theorem unifies_congr {E : Eqns Nat} {σ σ' : Nat → GTerm}
    (h : ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, σ v = σ' v) (hu : Eqns.Unifies σ E) :
    Eqns.Unifies σ' E := by
  intro p hp
  have e₁ : p.1.bind σ = p.1.bind σ' :=
    Term.bind_congr fun v hv => h p hp v (List.mem_append_left _ hv)
  have e₂ : p.2.bind σ = p.2.bind σ' :=
    Term.bind_congr fun v hv => h p hp v (List.mem_append_right _ hv)
  rw [← e₁, ← e₂]; exact hu p hp

/-- Finitely many exclusions, each satisfiable by a substitution of a given
kind, come down to finitely many disequations each satisfiable in that
way. -/
theorem exists_pairs (C : (Nat → GTerm) → Prop) : ∀ X : List (Eqns Nat),
    (∀ E ∈ X, ∃ τ, C τ ∧ ¬ Eqns.Unifies τ E) →
    ∃ L : List (Pat × Pat), (∀ p ∈ L, ∃ τ, C τ ∧ p.1.bind τ ≠ p.2.bind τ) ∧
      ∀ σ : Nat → GTerm, (∀ p ∈ L, p.1.bind σ ≠ p.2.bind σ) → ∀ E ∈ X, ¬ Eqns.Unifies σ E
  | [], _ => ⟨[], by simp, by simp⟩
  | E :: X, h => by
    obtain ⟨L, hL₁, hL₂⟩ := exists_pairs C X fun E' hE' => h E' (List.mem_cons_of_mem _ hE')
    obtain ⟨τ, hτ, hne⟩ := h E List.mem_cons_self
    simp only [Eqns.Unifies, not_forall] at hne
    obtain ⟨p, hp, hpne⟩ := hne
    refine ⟨p :: L, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨τ, hτ, hpne⟩
      · exact hL₁ q hq
    · intro σ hσ E' hE'
      rcases List.mem_cons.1 hE' with rfl | hE'
      · intro hu; exact hσ p List.mem_cons_self (hu p hp)
      · exact hL₂ σ (fun q hq => hσ q (List.mem_cons_of_mem _ hq)) E' hE'

/-- Independence, for a store. The variables of `H` each have infinitely many
values in their sorts. Outside `H` the substitution `σ₀` is in the sorts. Each
exclusion, and each disequation of `D`, is satisfied by some substitution that
agrees with `σ₀` outside `H`. Then one solution of the store agrees with `σ₀`
outside `H` and satisfies every disequation of `D`. -/
theorem Store.rich {S : Sorts} (s : Store) (H : List Nat)
    (hinf : ∀ h ∈ H, {g | MemC S (s.c h) g}.Infinite) (σ₀ : Nat → GTerm)
    (hσ₀ : ∀ v, v ∉ H → MemC S (s.c v) (σ₀ v)) (D : List (Pat × Pat))
    (hx : ∀ E ∈ s.x, ∃ τ : Nat → GTerm, (∀ v, v ∉ H → τ v = σ₀ v) ∧ ¬ Eqns.Unifies τ E)
    (hD : ∀ p ∈ D, ∃ τ : Nat → GTerm, (∀ v, v ∉ H → τ v = σ₀ v) ∧ p.1.bind τ ≠ p.2.bind τ) :
    ∃ σ ∈ s.Sol S, (∀ v, v ∉ H → σ v = σ₀ v) ∧ ∀ p ∈ D, p.1.bind σ ≠ p.2.bind σ := by
  obtain ⟨L, hL₁, hL₂⟩ := exists_pairs (fun τ => ∀ v, v ∉ H → τ v = σ₀ v) s.x hx
  obtain ⟨τ, hτ₀, hτH, hτD⟩ := avoid (fun h => {g | MemC S (s.c h) g}) H hinf (D ++ L) σ₀ (by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hD p hp
    · exact hL₁ p hp)
  refine ⟨τ, ⟨?_, ?_⟩, hτ₀, fun p hp => hτD p (List.mem_append_left _ hp)⟩
  · intro v
    by_cases hH : v ∈ H
    · exact hτH v hH
    · rw [hτ₀ v hH]; exact hσ₀ v hH
  · exact hL₂ τ fun p hp => hτD p (List.mem_append_right _ hp)

end Sorts
end RwLog
