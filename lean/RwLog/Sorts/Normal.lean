/-
# Normal stores

A *raw* store is plain data: a pattern, the sorts of its variables as a list
(variable `i` has the sorts at position `i`), and exclusions in solved form,
each a list of bindings `$x := p` read as "not all of `$x = p`".

`Raw.Normal S r` says the raw store is the canonical one for the set it
denotes under the sorts `S`. The conditions that carry the weight are stated
on solutions and not on syntax, so they are kept by anything that keeps the
solutions:

* every variable occurs in the pattern, and variables are numbered in the
  order they first occur;
* every variable takes values with two different head symbols (otherwise the
  pattern could be extended at that variable);
* the sorts listed for a variable are all the declared sorts that hold of
  every value it takes (so `$x : zk, $x != z` is written with `kk` when `kk`
  is declared);
* an exclusion is solved and idempotent, an alias `$x := $y` binds the later
  variable, some substitution in the sorts satisfies its equations, and no
  variable it leaves free is forced to one value by them (it would be bound);
* no exclusion is implied by another, and they are listed in a fixed order.

`Sorts/Unique.lean` proves that two normal stores with the same denotation are
equal.
-/
import RwLog.Sorts.Store
import RwLog.Sorts.Incl
import RwLog.Kernel.Covers
import RwLog.Kernel.Order

namespace RwLog
namespace Sorts

open Function

/-- An exclusion in solved form. -/
abbrev Binds := PSubst

/-- The equations of an exclusion. -/
def eqnsOf (θ : Binds) : Eqns Nat := θ.map fun b => (Term.var b.1, b.2)

/-- A raw store: a pattern, the sorts of variable `i` at position `i`, and
exclusions. -/
structure Raw where
  t : Pat
  c : List Conj
  x : List Binds
  deriving DecidableEq

namespace Raw

/-- The sorts of a variable. -/
def conj (r : Raw) (v : Nat) : Conj := r.c.getD v ∅

/-- The raw store as a store. -/
def store (r : Raw) : Store := ⟨r.t, r.conj, r.x.map eqnsOf⟩

/-- The substitutions in the sorts that satisfy the equations of an
exclusion: what the exclusion removes. -/
def Ex (S : Sorts) (r : Raw) (θ : Binds) : Set (Nat → GTerm) :=
  {σ | σ ∈ r.store.Pos S ∧ Eqns.Unifies σ (eqnsOf θ)}

end Raw

/-- The variables are numbered in the order they first occur: a variable is
preceded by every smaller one. -/
def FirstOcc (L : List Nat) : Prop :=
  ∀ (i : Nat) (h : i < L.length) (m : Nat), m < L[i] → ∃ (j : Nat) (hj : j < i), L[j] = m

/-- A linear order on exclusions, to list them in. -/
def bindsCmp (a b : Binds) : Ordering :=
  listCmp patCmp (a.map fun p => Term.app (.var p.1) p.2) (b.map fun p => Term.app (.var p.1) p.2)

/-- An exclusion of a raw store is in normal form. -/
structure NormalBinds (S : Sorts) (r : Raw) (θ : Binds) : Prop where
  ne : θ ≠ []
  sorted : θ.Pairwise fun a b => a.1 < b.1
  dom : ∀ b ∈ θ, b.1 < r.c.length
  fo : ∀ b ∈ θ, b.2.firstOrder = true
  ran : ∀ b ∈ θ, ∀ v ∈ b.2.vars, v < r.c.length ∧ ∀ b' ∈ θ, b'.1 ≠ v
  later : ∀ b ∈ θ, ∀ y, b.2 = .var y → y < b.1
  live : (r.Ex S θ).Nonempty
  loose : ∀ y, y < r.c.length → (∀ b ∈ θ, b.1 ≠ y) → ∃ σ ∈ r.Ex S θ, ∃ σ' ∈ r.Ex S θ, σ y ≠ σ' y

/-- The raw store is the canonical one for what it denotes. -/
structure Raw.Normal (S : Sorts) (r : Raw) : Prop where
  fo : r.t.firstOrder = true
  occ : FirstOcc r.t.vars
  len : ∀ v, v ∈ r.t.vars ↔ v < r.c.length
  two : ∀ v, v < r.c.length →
    ∃ σ ∈ r.store.Sol S, ∃ σ' ∈ r.store.Sol S, (σ v).key ≠ (σ' v).key
  up : ∀ v, v < r.c.length → ∀ n, n ∈ r.conj v ↔
    n ∈ names S ∧ ∀ σ ∈ r.store.Sol S, mem S n (σ v) = true
  ex : ∀ θ ∈ r.x, NormalBinds S r θ
  anti : ∀ θ ∈ r.x, ∀ θ' ∈ r.x, r.Ex S θ ⊆ r.Ex S θ' → θ = θ'
  sorted : r.x.Pairwise fun a b => bindsCmp a b = .lt

/-! ## Solved exclusions as substitutions -/

theorem lookup_of_sorted : ∀ {θ : Binds}, (θ.Pairwise fun a b => a.1 < b.1) →
    ∀ b ∈ θ, θ.lookup b.1 = some b.2
  | [], _, b, hb => by simp at hb
  | a :: θ, h, b, hb => by
    rw [List.pairwise_cons] at h
    obtain ⟨k, p⟩ := a
    rcases List.mem_cons.1 hb with rfl | hb
    · exact List.lookup_cons_self
    · have hne : (b.1 == k) = false := by simpa using Nat.ne_of_gt (h.1 b hb)
      rw [List.lookup_cons, hne]
      exact lookup_of_sorted h.2 b hb

theorem apply_of_mem {θ : Binds} (h : θ.Pairwise fun a b => a.1 < b.1) {b : Nat × Pat}
    (hb : b ∈ θ) : PSubst.apply θ b.1 = b.2 := by
  simp [PSubst.apply, lookup_of_sorted h b hb]

theorem apply_of_not_mem {θ : Binds} {v : Nat} (h : ∀ b ∈ θ, b.1 ≠ v) :
    PSubst.apply θ v = .var v := by
  unfold PSubst.apply
  cases hl : θ.lookup v with
  | none => rfl
  | some p => exact absurd rfl (h _ (mem_of_lookup hl))

theorem apply_cases (θ : Binds) (v : Nat) :
    PSubst.apply θ v = .var v ∨ (v, PSubst.apply θ v) ∈ θ := by
  unfold PSubst.apply
  cases hl : θ.lookup v with
  | none => left; rfl
  | some p => right; exact mem_of_lookup hl

/-- A substitution satisfies the equations of a solved exclusion exactly when
it is unchanged by the exclusion read as a substitution. -/
theorem unifies_eqnsOf {θ : Binds} (h : θ.Pairwise fun a b => a.1 < b.1) (σ : Nat → GTerm) :
    Eqns.Unifies σ (eqnsOf θ) ↔ ∀ v, σ v = (PSubst.apply θ v).bind σ := by
  constructor
  · intro hu v
    rcases apply_cases θ v with e | hm
    · rw [e]; rfl
    · exact hu (Term.var v, PSubst.apply θ v) (List.mem_map.2 ⟨_, hm, rfl⟩)
  · intro hv p hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
    have := hv b.1
    rw [apply_of_mem h hb] at this
    exact this

/-! ## What normal stores have -/

/-- A term that differs from a given one. -/
theorem exists_ne (g : GTerm) : ∃ g' : GTerm, g' ≠ g :=
  ⟨.app g g, fun h => by have := congrArg Term.size h; simp [Term.size] at this; omega⟩

/-- An exclusion with a binding whose variable is not in its own value can be
satisfied by changing that one variable. -/
theorem exists_not_unifies {θ : Binds} {b : Nat × Pat} (hb : b ∈ θ) (hv : b.1 ∉ b.2.vars)
    (σ₀ : Nat → GTerm) :
    ∃ τ : Nat → GTerm, (∀ v, v ≠ b.1 → τ v = σ₀ v) ∧ ¬ Eqns.Unifies τ (eqnsOf θ) := by
  obtain ⟨g, hg⟩ := exists_ne (b.2.bind σ₀)
  refine ⟨update σ₀ b.1 g, fun v hv' => by simp [update, hv'], ?_⟩
  intro hu
  have := hu (Term.var b.1, b.2) (List.mem_map.2 ⟨b, hb, rfl⟩)
  simp only [Term.bind_var, update_self] at this
  rw [bind_update_of_not_mem hv] at this
  exact hg this

namespace Raw.Normal

variable {S : Sorts} {r : Raw}

theorem conj_of_ge (r : Raw) {v : Nat} (h : r.c.length ≤ v) : r.conj v = ∅ := by
  simp [Raw.conj, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Every variable of a normal store has infinitely many values in its
sorts. -/
theorem infinite (hS : S.WellFormed) (hr : r.Normal S) {v : Nat} (hv : v < r.c.length) :
    {g | MemC S (r.conj v) g}.Infinite := by
  obtain ⟨σ, hσ, σ', hσ', hne⟩ := hr.two v hv
  exact conj_infinite hS _ (hσ.1 v) (hσ'.1 v) fun e => hne (by rw [e])

/-- Independence in a normal store: finitely many disequations between
patterns over its variables, each satisfiable somewhere, are all satisfied by
one solution. -/
theorem rich (hS : S.WellFormed) (hr : r.Normal S) (D : List (Pat × Pat))
    (hD : ∀ p ∈ D, (∀ v ∈ p.1.vars ++ p.2.vars, v < r.c.length) ∧
      ∃ τ : Nat → GTerm, p.1.bind τ ≠ p.2.bind τ) :
    ∃ σ ∈ r.store.Sol S, ∀ p ∈ D, p.1.bind σ ≠ p.2.bind σ := by
  have σ₀ : Nat → GTerm := fun _ => .sym ""
  obtain ⟨σ, hσ, -, hσD⟩ := r.store.rich (S := S) (List.range r.c.length)
    (fun h hh => hr.infinite hS (List.mem_range.1 hh)) σ₀
    (fun v hv => by
      have : r.c.length ≤ v := by simpa using hv
      show MemC S (r.conj v) (σ₀ v)
      rw [conj_of_ge r this]; intro n hn; simp at hn)
    D
    (by
      intro E hE
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
      have hn := hr.ex θ hθ
      obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil θ hn.ne
      have hbv : b.1 ∉ b.2.vars := fun hm => (hn.ran b hb b.1 hm).2 b hb rfl
      obtain ⟨τ, hτ, hne⟩ := exists_not_unifies hb hbv σ₀
      refine ⟨τ, fun v hv => hτ v ?_, hne⟩
      rintro rfl
      exact hv (List.mem_range.2 (hn.dom b hb)))
    (by
      intro p hp
      obtain ⟨hvars, τ₁, hτ₁⟩ := hD p hp
      refine ⟨fun v => if v < r.c.length then τ₁ v else σ₀ v, fun v hv => ?_, ?_⟩
      · have : ¬ v < r.c.length := by simpa using hv
        simp [this]
      · have e : ∀ q : Pat, (∀ v ∈ q.vars, v < r.c.length) →
            q.bind (fun v => if v < r.c.length then τ₁ v else σ₀ v) = q.bind τ₁ :=
          fun q hq => Term.bind_congr fun v hv => by simp [hq v hv]
        rw [e p.1 fun v hv => hvars v (List.mem_append_left _ hv),
          e p.2 fun v hv => hvars v (List.mem_append_right _ hv)]
        exact hτ₁)
  exact ⟨σ, hσ, hσD⟩

/-- A normal store has a solution. -/
theorem sol_nonempty (hS : S.WellFormed) (hr : r.Normal S) : (r.store.Sol S).Nonempty := by
  obtain ⟨σ, hσ, -⟩ := hr.rich hS [] (by simp)
  exact ⟨σ, hσ⟩

/-- Two different variables of a normal store take different values in some
solution. -/
theorem sep_vars (hS : S.WellFormed) (hr : r.Normal S) {i j : Nat} (hi : i < r.c.length)
    (hj : j < r.c.length) (hne : i ≠ j) : ∃ σ ∈ r.store.Sol S, σ i ≠ σ j := by
  obtain ⟨σ, hσ, h⟩ := hr.rich hS [(.var i, .var j)] (by
    intro p hp
    rw [List.mem_singleton] at hp; subst hp
    refine ⟨by simp [Term.vars, hi, hj], ?_⟩
    obtain ⟨g, hg⟩ := exists_ne (.sym "")
    exact ⟨update (fun _ => .sym "") j g, by simp [update, hne, Ne.symm hg]⟩)
  exact ⟨σ, hσ, by simpa using h (.var i, .var j) (by simp)⟩

end Raw.Normal

end Sorts
end RwLog
