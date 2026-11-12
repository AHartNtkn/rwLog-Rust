/-
# Derivable spans, and their agreement with the ground semantics

`Derives P e s` says that the span `s` is a derivable answer of `e`: a span
derives itself, `or` derives what either side derives, `seq` and `and`
combine one derivable span from each side by most general matching,
converse swaps, and a call derives what its body derives.

The lifting theorem `sem_eq_derivable` says that the ground meaning of `e`
is exactly the union of the ground triples of its derivable spans.
`DerivesN` additionally bounds the depth of call unfolding.
-/
import RwLog.Kernel.Span

namespace RwLog

variable (P : Program)

inductive Derives : Rel → Span → Prop
  | span (s : Span) : Derives (.span s) s
  | orl {a b s} : Derives a s → Derives (.or a b) s
  | orr {a b s} : Derives b s → Derives (.or a b) s
  | seq {a b s₁ s₂ s} : Derives a s₁ → Derives b s₂ → s₁.compose s₂ = some s →
      Derives (.seq a b) s
  | and {a b s₁ s₂ s} : Derives a s₁ → Derives b s₂ → s₁.meet s₂ = some s →
      Derives (.and a b) s
  | conv {a s} : Derives a s → Derives (.conv a) s.swap
  | call {n s} : Derives (P.body n) s → Derives (.call n) s

/-- Derivations in which calls are nested at most `n` deep. -/
inductive DerivesN : Nat → Rel → Span → Prop
  | span (n : Nat) (s : Span) : DerivesN n (.span s) s
  | orl {n a b s} : DerivesN n a s → DerivesN n (.or a b) s
  | orr {n a b s} : DerivesN n b s → DerivesN n (.or a b) s
  | seq {n a b s₁ s₂ s} : DerivesN n a s₁ → DerivesN n b s₂ → s₁.compose s₂ = some s →
      DerivesN n (.seq a b) s
  | and {n a b s₁ s₂ s} : DerivesN n a s₁ → DerivesN n b s₂ → s₁.meet s₂ = some s →
      DerivesN n (.and a b) s
  | conv {n a s} : DerivesN n a s → DerivesN n (.conv a) s.swap
  | call {n m s} : DerivesN n (P.body m) s → DerivesN (n + 1) (.call m) s

variable {P}

theorem DerivesN.mono {n e s} (h : DerivesN P n e s) : ∀ {k}, n ≤ k → DerivesN P k e s := by
  induction h with
  | span n s => intro k _; exact .span k s
  | orl _ ih => intro k hk; exact .orl (ih hk)
  | orr _ ih => intro k hk; exact .orr (ih hk)
  | seq _ _ hc ih₁ ih₂ => intro k hk; exact .seq (ih₁ hk) (ih₂ hk) hc
  | and _ _ hc ih₁ ih₂ => intro k hk; exact .and (ih₁ hk) (ih₂ hk) hc
  | conv _ ih => intro k hk; exact .conv (ih hk)
  | @call n m s _ ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact .call (ih (by omega))

theorem DerivesN.derives {n e s} (h : DerivesN P n e s) : Derives P e s := by
  induction h with
  | span n s => exact .span s
  | orl _ ih => exact .orl ih
  | orr _ ih => exact .orr ih
  | seq _ _ hc ih₁ ih₂ => exact .seq ih₁ ih₂ hc
  | and _ _ hc ih₁ ih₂ => exact .and ih₁ ih₂ hc
  | conv _ ih => exact .conv ih
  | call _ ih => exact .call ih

theorem Derives.derivesN {e s} (h : Derives P e s) : ∃ n, DerivesN P n e s := by
  induction h with
  | span s => exact ⟨0, .span 0 s⟩
  | orl _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n, .orl h⟩
  | orr _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n, .orr h⟩
  | seq _ _ hc ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂
    exact ⟨max n₁ n₂, .seq (h₁.mono (le_max_left _ _)) (h₂.mono (le_max_right _ _)) hc⟩
  | and _ _ hc ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂
    exact ⟨max n₁ n₂, .and (h₁.mono (le_max_left _ _)) (h₂.mono (le_max_right _ _)) hc⟩
  | conv _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n, .conv h⟩
  | call _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .call h⟩

theorem derives_iff_derivesN {e s} : Derives P e s ↔ ∃ n, DerivesN P n e s :=
  ⟨Derives.derivesN, fun ⟨_, h⟩ => h.derives⟩

/-- The ground triples covered by the derivable spans of `e`. -/
def derivable (P : Program) (e : Rel) : GRel := ⋃ (s : Span) (_ : Derives P e s), s.den

theorem mem_derivable {e x} : x ∈ derivable P e ↔ ∃ s, Derives P e s ∧ x ∈ s.den := by
  simp [derivable]

/-- Soundness of derivations: a derivable span denotes only triples of the
expression. -/
theorem Derives.den_subset {e s} (h : Derives P e s) : s.den ⊆ P.sem e := by
  induction h with
  | span s => exact le_rfl
  | orl _ ih => exact ih.trans Set.subset_union_left
  | orr _ ih => exact ih.trans Set.subset_union_right
  | seq _ _ hc ih₁ ih₂ =>
    rw [compose_some hc]
    rintro x ⟨m, S₁, S₂, h₁, h₂, hx⟩
    exact ⟨m, S₁, S₂, ih₁ h₁, ih₂ h₂, hx⟩
  | and _ _ hc ih₁ ih₂ =>
    rw [meet_some hc]
    rintro x ⟨S₁, S₂, h₁, h₂, hx⟩
    exact ⟨S₁, S₂, ih₁ h₁, ih₂ h₂, hx⟩
  | conv _ ih =>
    rw [swap_den]; intro x hx; exact ih hx
  | @call n s _ ih =>
    intro x hx
    show x ∈ P.meaning n
    rw [P.meaning_eq]; exact ih hx

/-- Completeness of derivations against any interpretation of names that is
covered by derivations. -/
theorem denote_subset_derivable {ρ : Name → GRel}
    (hρ : ∀ n, ρ n ⊆ derivable P (.call n)) : ∀ e, denote ρ e ⊆ derivable P e
  | .zero => fun _ h => h.elim
  | .span s => fun x hx => mem_derivable.2 ⟨s, .span s, hx⟩
  | .or a b => by
    rintro x (hx | hx)
    · obtain ⟨s, hs, hx⟩ := mem_derivable.1 (denote_subset_derivable hρ a hx)
      exact mem_derivable.2 ⟨s, .orl hs, hx⟩
    · obtain ⟨s, hs, hx⟩ := mem_derivable.1 (denote_subset_derivable hρ b hx)
      exact mem_derivable.2 ⟨s, .orr hs, hx⟩
  | .seq a b => by
    rintro x ⟨m, S₁, S₂, h₁, h₂, hx⟩
    obtain ⟨s₁, hs₁, h₁⟩ := mem_derivable.1 (denote_subset_derivable hρ a h₁)
    obtain ⟨s₂, hs₂, h₂⟩ := mem_derivable.1 (denote_subset_derivable hρ b h₂)
    have hmem : x ∈ (s₁.den).comp s₂.den := ⟨m, S₁, S₂, h₁, h₂, hx⟩
    cases hc : s₁.compose s₂ with
    | none => rw [compose_none hc] at hmem; exact hmem.elim
    | some s => exact mem_derivable.2 ⟨s, .seq hs₁ hs₂ hc, by rw [compose_some hc]; exact hmem⟩
  | .and a b => by
    rintro x ⟨S₁, S₂, h₁, h₂, hx⟩
    obtain ⟨s₁, hs₁, h₁⟩ := mem_derivable.1 (denote_subset_derivable hρ a h₁)
    obtain ⟨s₂, hs₂, h₂⟩ := mem_derivable.1 (denote_subset_derivable hρ b h₂)
    have hmem : x ∈ (s₁.den).meet s₂.den := ⟨S₁, S₂, h₁, h₂, hx⟩
    cases hc : s₁.meet s₂ with
    | none => rw [meet_none hc] at hmem; exact hmem.elim
    | some s => exact mem_derivable.2 ⟨s, .and hs₁ hs₂ hc, by rw [meet_some hc]; exact hmem⟩
  | .conv a => by
    intro x hx
    obtain ⟨s, hs, hx⟩ := mem_derivable.1 (denote_subset_derivable hρ a hx)
    refine mem_derivable.2 ⟨s.swap, .conv hs, ?_⟩
    rw [swap_den]; exact hx
  | .call n => hρ n

/-- **Lifting theorem.** The ground meaning of an expression is the union of
the ground triples of its derivable spans. -/
theorem sem_eq_derivable (e : Rel) : P.sem e = derivable P e := by
  apply le_antisymm
  · -- the derivable meanings of names form a pre-fixed point
    let ρ' : Name → GRel := fun n => derivable P (.call n)
    have hpre : P.step ρ' ≤ ρ' := by
      intro n x hx
      obtain ⟨s, hs, hx⟩ := mem_derivable.1 (denote_subset_derivable (fun _ => le_rfl) _ hx)
      exact mem_derivable.2 ⟨s, .call hs, hx⟩
    have hle : P.meaning ≤ ρ' := OrderHom.lfp_le _ hpre
    exact (denote_mono hle e).trans (denote_subset_derivable (fun _ => le_rfl) e)
  · intro x hx
    obtain ⟨s, hs, hx⟩ := mem_derivable.1 hx
    exact hs.den_subset hx

end RwLog
