/-
# Span kernel: two-sided matching, composition, conjunction

Composing or conjoining two spans matches terms of one span against terms of
the other. The two spans keep separate variable namespaces: the first span's
variables are tagged `inl`, the second's `inr`, so a variable index shared by
both spans has no shared meaning. The equations are then solved over
`Nat ⊕ Nat` (a most general matching), and the result is renumbered back into
`Nat`. Stores are combined.

Each operation is proved to compute exactly the corresponding operation on
ground triples (`compose_den`, `meet_den`, `swap_den`); `none` means the
ground result is empty.
-/
import RwLog.Kernel.Solve
import RwLog.Trusted.Semantics
import Mathlib.Logic.Equiv.Nat

namespace RwLog

open Term Eqns

/-- Renumber `Nat ⊕ Nat` variables back into `Nat`. -/
def enc : Nat ⊕ Nat → Nat := Equiv.natSumNatEquivNat

def dec : Nat → Nat ⊕ Nat := Equiv.natSumNatEquivNat.symm

@[simp] theorem dec_enc (v : Nat ⊕ Nat) : dec (enc v) = v :=
  Equiv.natSumNatEquivNat.symm_apply_apply v

/-- The two namespaces of a matching problem. -/
def Pat.left (t : Pat) : Term (Nat ⊕ Nat) := t.rename Sum.inl
def Pat.right (t : Pat) : Term (Nat ⊕ Nat) := t.rename Sum.inr

/-- Finish a matched span: apply the matching and renumber. -/
def finish (θ : Nat ⊕ Nat → Term (Nat ⊕ Nat)) (l r : Term (Nat ⊕ Nat))
    (c : List (Term (Nat ⊕ Nat))) : Span :=
  ⟨(l.bind θ).rename enc, (r.bind θ).rename enc, c.map fun t => (t.bind θ).rename enc⟩

namespace Span

/-- Sequential composition of spans: match `s₁.r` against `s₂.l`. -/
def compose (s₁ s₂ : Span) : Option Span :=
  (solve [(Pat.left s₁.r, Pat.right s₂.l)]).map fun θ =>
    finish θ (Pat.left s₁.l) (Pat.right s₂.r) (s₁.c.map Pat.left ++ s₂.c.map Pat.right)

/-- Conjunction of spans: match both sides. -/
def meet (s₁ s₂ : Span) : Option Span :=
  (solve [(Pat.left s₁.l, Pat.right s₂.l), (Pat.left s₁.r, Pat.right s₂.r)]).map fun θ =>
    finish θ (Pat.left s₁.l) (Pat.left s₁.r) (s₁.c.map Pat.left ++ s₂.c.map Pat.right)

end Span

/-- Ground triples of an optional span. -/
def Span.denO : Option Span → GRel
  | none => ∅
  | some s => s.den

/-! ## Correctness -/

section
variable {V W : Type}

theorem rename_bind (f : V → W) (σ : W → GTerm) (t : Term V) :
    (t.rename f).bind σ = t.bind (σ ∘ f) := by
  simp [rename, bind_bind]; rfl

end

theorem Store.at_eq (c : Store) (σ : Nat → GTerm) :
    c.at σ = (c.map (Term.bind σ)).toFinset := rfl

/-- Instantiating a finished span. -/
theorem finish_bind (θ : Nat ⊕ Nat → Term (Nat ⊕ Nat)) (σ : Nat → GTerm)
    (t : Term (Nat ⊕ Nat)) :
    ((t.bind θ).rename enc).bind σ = t.bind (fun w => (θ w).bind (σ ∘ enc)) := by
  rw [rename_bind, bind_bind]

/-- The ground substitution that a `Nat ⊕ Nat` substitution induces on a
renumbered span. -/
def unenc (τ : Nat ⊕ Nat → GTerm) : Nat → GTerm := τ ∘ dec

theorem unenc_enc (τ : Nat ⊕ Nat → GTerm) : unenc τ ∘ enc = τ := by
  funext v; simp [unenc]

theorem left_bind (t : Pat) (τ : Nat ⊕ Nat → GTerm) : (Pat.left t).bind τ = t.bind (τ ∘ Sum.inl) :=
  rename_bind _ _ _

theorem right_bind (t : Pat) (τ : Nat ⊕ Nat → GTerm) : (Pat.right t).bind τ = t.bind (τ ∘ Sum.inr) :=
  rename_bind _ _ _

theorem left_bind_elim (t : Pat) (σ₁ σ₂ : Nat → GTerm) :
    (Pat.left t).bind (Sum.elim σ₁ σ₂) = t.bind σ₁ := by rw [left_bind]; rfl

theorem right_bind_elim (t : Pat) (σ₁ σ₂ : Nat → GTerm) :
    (Pat.right t).bind (Sum.elim σ₁ σ₂) = t.bind σ₂ := by rw [right_bind]; rfl

/-- Stores of a finished span. -/
theorem finish_store (θ : Nat ⊕ Nat → Term (Nat ⊕ Nat)) (σ : Nat → GTerm) (c₁ c₂ : Store) :
    Store.at ((c₁.map Pat.left ++ c₂.map Pat.right).map fun t => (t.bind θ).rename enc) σ =
      c₁.at (fun v => (θ (.inl v)).bind (σ ∘ enc)) ∪
      c₂.at (fun v => (θ (.inr v)).bind (σ ∘ enc)) := by
  ext g
  simp only [Store.at, List.map_append, List.map_map, List.toFinset_append, Finset.mem_union,
    List.mem_toFinset, List.mem_map, Function.comp_apply, finish_bind, left_bind, right_bind]
  rfl

theorem store_at_congr {c : Store} {σ τ : Nat → GTerm} (h : σ = τ) : c.at σ = c.at τ := by
  rw [h]

theorem compose_den (s₁ s₂ : Span) :
    Span.denO (s₁.compose s₂) = (s₁.den).comp s₂.den := by
  unfold Span.compose
  cases hs : solve [(Pat.left s₁.r, Pat.right s₂.l)] with
  | none =>
    simp only [Option.map_none, Span.denO]
    symm; apply Set.eq_empty_of_forall_notMem
    rintro ⟨a, b, S⟩ ⟨m, S₁, S₂, ⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩, _⟩
    simp only [Prod.mk.injEq] at h₁ h₂
    apply solve_none hs (Sum.elim σ₁ σ₂)
    simp only [Unifies, List.mem_singleton, forall_eq, left_bind_elim, right_bind_elim]
    rw [← h₁.2.1, ← h₂.1]
  | some θ =>
    obtain ⟨hu, hm⟩ := solve_some hs
    simp only [Option.map_some, Span.denO]
    ext ⟨a, b, S⟩
    simp only [Span.den, GRel.comp, Set.mem_ofPred_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨σ, ha, hb, hS⟩
      let τ : Nat ⊕ Nat → GTerm := fun w => (θ w).bind (σ ∘ enc)
      have hτ : (Pat.left s₁.r).bind τ = (Pat.right s₂.l).bind τ := by
        have := hu _ (List.mem_singleton_self _)
        simp only [τ]; rw [← bind_bind, ← bind_bind, this]
      refine ⟨s₁.r.bind (τ ∘ Sum.inl), s₁.c.at (τ ∘ Sum.inl), s₂.c.at (τ ∘ Sum.inr),
        ⟨τ ∘ Sum.inl, ?_⟩, ⟨τ ∘ Sum.inr, ?_⟩, ?_⟩
      · simp only [finish, finish_bind] at ha
        rw [ha, left_bind]; exact ⟨rfl, rfl, rfl⟩
      · simp only [finish, finish_bind] at hb
        rw [hb, right_bind, ← left_bind, hτ, right_bind]; exact ⟨rfl, rfl, rfl⟩
      · rw [hS]; simp only [finish]; rw [finish_store]; rfl
    · rintro ⟨m, S₁, S₂, ⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩, hS⟩
      let σ : Nat ⊕ Nat → GTerm := Sum.elim σ₁ σ₂
      have huσ : Unifies σ [(Pat.left s₁.r, Pat.right s₂.l)] := by
        simp only [Unifies, List.mem_singleton, forall_eq, σ, left_bind_elim, right_bind_elim]
        rw [← h₁.2.1, ← h₂.1]
      have hθ := hm σ huσ
      have hτ : (fun w => (θ w).bind (unenc σ ∘ enc)) = σ := by
        funext w; rw [unenc_enc]; exact hθ w
      refine ⟨unenc σ, ?_, ?_, ?_⟩
      · rw [h₁.1]
        show _ = Term.bind (unenc σ) ((Term.bind θ (Pat.left s₁.l)).rename enc)
        rw [finish_bind, hτ, left_bind_elim]
      · rw [h₂.2.1]
        show _ = Term.bind (unenc σ) ((Term.bind θ (Pat.right s₂.r)).rename enc)
        rw [finish_bind, hτ, right_bind_elim]
      · rw [hS]; simp only [finish]; rw [finish_store, h₁.2.2, h₂.2.2]
        congr 1
        · exact store_at_congr (funext fun v => by
            have := congrFun hτ (.inl v); exact this.symm)
        · exact store_at_congr (funext fun v => by
            have := congrFun hτ (.inr v); exact this.symm)

theorem unifies_two {σ : Nat ⊕ Nat → GTerm} {a b c d : Term (Nat ⊕ Nat)} :
    Unifies σ [(a, b), (c, d)] ↔ a.bind σ = b.bind σ ∧ c.bind σ = d.bind σ := by
  simp [Unifies]

theorem meet_den (s₁ s₂ : Span) :
    Span.denO (s₁.meet s₂) = (s₁.den).meet s₂.den := by
  unfold Span.meet
  cases hs : solve [(Pat.left s₁.l, Pat.right s₂.l), (Pat.left s₁.r, Pat.right s₂.r)] with
  | none =>
    simp only [Option.map_none, Span.denO]
    symm; apply Set.eq_empty_of_forall_notMem
    rintro ⟨a, b, S⟩ ⟨S₁, S₂, ⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩, _⟩
    simp only [Prod.mk.injEq] at h₁ h₂
    apply solve_none hs (Sum.elim σ₁ σ₂)
    rw [unifies_two, left_bind_elim, right_bind_elim, left_bind_elim, right_bind_elim,
      ← h₁.1, ← h₂.1, ← h₁.2.1, ← h₂.2.1]
    exact ⟨rfl, rfl⟩
  | some θ =>
    obtain ⟨hu, hm⟩ := solve_some hs
    simp only [Option.map_some, Span.denO]
    ext ⟨a, b, S⟩
    simp only [Span.den, GRel.meet, Set.mem_ofPred_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨σ, ha, hb, hS⟩
      let τ : Nat ⊕ Nat → GTerm := fun w => (θ w).bind (σ ∘ enc)
      have hτ := (unifies_two (σ := τ)).1 (by
        intro p hp
        simp only [τ]; rw [← bind_bind, ← bind_bind, hu p hp])
      simp only [finish, finish_bind] at ha hb
      refine ⟨s₁.c.at (τ ∘ Sum.inl), s₂.c.at (τ ∘ Sum.inr),
        ⟨τ ∘ Sum.inl, ?_, ?_, rfl⟩, ⟨τ ∘ Sum.inr, ?_, ?_, rfl⟩, ?_⟩
      · rw [ha, left_bind]
      · rw [hb, left_bind]
      · rw [ha, ← right_bind, ← hτ.1]
      · rw [hb, ← right_bind, ← hτ.2]
      · rw [hS]; simp only [finish]; rw [finish_store]; rfl
    · rintro ⟨S₁, S₂, ⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩, hS⟩
      let σ : Nat ⊕ Nat → GTerm := Sum.elim σ₁ σ₂
      have huσ : Unifies σ [(Pat.left s₁.l, Pat.right s₂.l), (Pat.left s₁.r, Pat.right s₂.r)] := by
        rw [unifies_two]
        simp only [σ, left_bind_elim, right_bind_elim]
        exact ⟨h₁.1.symm.trans h₂.1, h₁.2.1.symm.trans h₂.2.1⟩
      have hθ := hm σ huσ
      have hτ : (fun w => (θ w).bind (unenc σ ∘ enc)) = σ := by
        funext w; rw [unenc_enc]; exact hθ w
      refine ⟨unenc σ, ?_, ?_, ?_⟩
      · rw [h₁.1]
        show _ = Term.bind (unenc σ) ((Term.bind θ (Pat.left s₁.l)).rename enc)
        rw [finish_bind, hτ, left_bind_elim]
      · rw [h₁.2.1]
        show _ = Term.bind (unenc σ) ((Term.bind θ (Pat.left s₁.r)).rename enc)
        rw [finish_bind, hτ, left_bind_elim]
      · rw [hS]; simp only [finish]; rw [finish_store, h₁.2.2, h₂.2.2]
        congr 1
        · exact store_at_congr (funext fun v => by
            have := congrFun hτ (.inl v); exact this.symm)
        · exact store_at_congr (funext fun v => by
            have := congrFun hτ (.inr v); exact this.symm)

theorem swap_den (s : Span) : s.swap.den = (s.den).inv := by
  ext ⟨a, b, S⟩
  simp only [Span.den, Span.swap, GRel.inv, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨σ, h1, h2, h3⟩; exact ⟨σ, h2, h1, h3⟩
  · rintro ⟨σ, h1, h2, h3⟩; exact ⟨σ, h2, h1, h3⟩

/-- Unification failure means the ground composition is empty. -/
theorem compose_none {s₁ s₂ : Span} (h : s₁.compose s₂ = none) : (s₁.den).comp s₂.den = ∅ := by
  rw [← compose_den, h]; rfl

theorem meet_none {s₁ s₂ : Span} (h : s₁.meet s₂ = none) : (s₁.den).meet s₂.den = ∅ := by
  rw [← meet_den, h]; rfl

theorem compose_some {s₁ s₂ s : Span} (h : s₁.compose s₂ = some s) :
    s.den = (s₁.den).comp s₂.den := by
  rw [← compose_den, h]; rfl

theorem meet_some {s₁ s₂ s : Span} (h : s₁.meet s₂ = some s) :
    s.den = (s₁.den).meet s₂.den := by
  rw [← meet_den, h]; rfl

end RwLog
