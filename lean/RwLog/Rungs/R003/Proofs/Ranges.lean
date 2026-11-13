/-
# What an interface lets through

The shared evaluation prunes with an interface: the right interface of what
stands to the left of a sub-expression. Whether a span can be fused with what
stands to its left depends only on the set of terms the left side can end in,
its *range*. This file states the pruning tests of `Shared.lean` through
ranges:

* `alive ctx s` holds exactly when some term of the range of `ctx` is accepted
  by `s` (`alive_iff`);
* the interface left by a span after an interface has the image of the range
  as its range (`rng_extend`);
* interfaces that are equal as memo keys have the same range (`sameCtx_rng`).
-/
import RwLog.Rungs.R003.Shared
import RwLog.Rungs.R002.Proofs.Chains

namespace RwLog

namespace R003

open R001 Cost

/-- The terms a span sends the terms of `ρ` to. -/
def img (ρ : Set GTerm) (s : Span) : Set GTerm := {b | ∃ m ∈ ρ, ∃ S, (m, b, S) ∈ s.den}

/-- The span accepts some term of `ρ`. -/
def AliveP (ρ : Set GTerm) (s : Span) : Prop := ∃ m ∈ ρ, ∃ b S, (m, b, S) ∈ s.den

/-- The terms an interface lets through: every term when there is none. -/
def rng : Option Span → Set GTerm
  | none => Set.univ
  | some c => img Set.univ c

theorem aliveP_univ (s : Span) : AliveP Set.univ s := by
  obtain ⟨⟨a, b, S⟩, h⟩ := s.den_nonempty
  exact ⟨a, trivial, b, S, h⟩

theorem AliveP.of_img {ρ : Set GTerm} {a b : Span} (h : AliveP (img ρ a) b) : AliveP ρ a := by
  obtain ⟨m, ⟨m', hm', S, hS⟩, -⟩ := h
  exact ⟨m', hm', m, S, hS⟩

theorem AliveP.mono {ρ ρ' : Set GTerm} {s : Span} (h : AliveP ρ s) (hsub : ρ ⊆ ρ') : AliveP ρ' s := by
  obtain ⟨m, hm, r⟩ := h
  exact ⟨m, hsub hm, r⟩

theorem img_mono {ρ ρ' : Set GTerm} (s : Span) (hsub : ρ ⊆ ρ') : img ρ s ⊆ img ρ' s := by
  rintro b ⟨m, hm, r⟩
  exact ⟨m, hsub hm, r⟩

theorem comp_nonempty_iff (a b : Span) :
    ((a.den).comp b.den).Nonempty ↔ AliveP (img Set.univ a) b := by
  constructor
  · rintro ⟨x, m, S₁, S₂, h₁, h₂, -⟩
    exact ⟨m, ⟨x.1, trivial, S₁, h₁⟩, x.2.1, S₂, h₂⟩
  · rintro ⟨m, ⟨a₀, -, S₁, h₁⟩, b₀, S₂, h₂⟩
    exact ⟨(a₀, b₀, S₁ ∪ S₂), m, S₁, S₂, h₁, h₂, rfl⟩

theorem compose_isSome_iff (a b : Span) : (a.compose b).isSome ↔ AliveP (img Set.univ a) b := by
  rw [← comp_nonempty_iff]
  cases h : a.compose b with
  | none => simp [compose_none h]
  | some c => simp [← compose_some h, c.den_nonempty]

theorem img_compose {a b c : Span} (h : a.compose b = some c) (ρ : Set GTerm) :
    img ρ c = img (img ρ a) b := by
  ext t
  simp only [img, compose_some h, GRel.comp, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, S, m', S₁, S₂, h₁, h₂, -⟩
    exact ⟨m', ⟨m, hm, S₁, h₁⟩, S₂, h₂⟩
  · rintro ⟨m', ⟨m, hm, S₁, h₁⟩, S₂, h₂⟩
    exact ⟨m, hm, S₁ ∪ S₂, m', S₁, S₂, h₁, h₂, rfl⟩

theorem aliveP_compose {a b c : Span} (h : a.compose b = some c) (ρ : Set GTerm) :
    AliveP ρ c ↔ AliveP (img ρ a) b := by
  simp only [AliveP, img, compose_some h, GRel.comp, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, t, S, m', S₁, S₂, h₁, h₂, -⟩
    exact ⟨m', ⟨m, hm, S₁, h₁⟩, t, S₂, h₂⟩
  · rintro ⟨m', ⟨m, hm, S₁, h₁⟩, t, S₂, h₂⟩
    exact ⟨m, hm, t, S₁ ∪ S₂, m', S₁, S₂, h₁, h₂, rfl⟩

theorem not_aliveP_of_compose_none {a b : Span} (h : a.compose b = none) (ρ : Set GTerm) :
    ¬ AliveP (img ρ a) b := by
  intro hal
  have := (compose_isSome_iff a b).mpr (hal.mono (img_mono a (Set.subset_univ ρ)))
  rw [h] at this
  cases this

/-- The pruning test, through ranges. -/
theorem alive_iff (ctx : Option Span) (s : Span) :
    (alive ctx s).val = true ↔ AliveP (rng ctx) s := by
  cases ctx with
  | none => exact ⟨fun _ => aliveP_univ s, fun _ => rfl⟩
  | some c =>
    change (Span.chain [c, s]).isSome = true ↔ _
    rw [Span.chain_isSome_iff]
    simp only [List.map_cons, List.map_nil, GRel.chain_cons, GRel.chain_nil, GRel.comp_id]
    exact comp_nonempty_iff c s

/-- `AliveP` as a test. -/
noncomputable def aliveB (ρ : Set GTerm) (s : Span) : Bool := by
  classical exact decide (AliveP ρ s)

@[simp] theorem aliveB_iff {ρ : Set GTerm} {s : Span} : aliveB ρ s = true ↔ AliveP ρ s := by
  simp [aliveB]

theorem alive_eq (ctx : Option Span) : (fun s => (alive ctx s).val) = aliveB (rng ctx) := by
  funext s
  rw [Bool.eq_iff_iff, alive_iff, aliveB_iff]

/-- The range of the right interface of a span is the range of the span, also
when the interface is trivial and so not represented. -/
theorem rng_bound_rightIface (x : Span) : rng (bound x.rightIface) = img Set.univ x := by
  have key : img Set.univ x.rightIface = img Set.univ x := by
    ext t
    simp only [img, Span.den, Span.rightIface, Set.mem_ofPred_eq, Set.mem_univ, true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨m, S, σ, -, rfl, -⟩
      exact ⟨_, _, σ, rfl, rfl, rfl⟩
    · rintro ⟨m, S, σ, -, rfl, -⟩
      exact ⟨_, _, σ, rfl, rfl, rfl⟩
  unfold bound
  split
  · rename_i v hl _
    rw [← key]
    ext t
    simp only [rng, Set.mem_univ, img, Span.den, Set.mem_ofPred_eq, true_and, Prod.mk.injEq,
      true_iff]
    exact ⟨_, _, fun _ => t, rfl, by rw [show x.rightIface.r = x.rightIface.l from rfl, hl]; rfl,
      rfl⟩
  · exact key

/-- The interface left by a span that is alive after an interface lets
through the image of what the interface lets through. -/
theorem rng_extend {ctx : Option Span} {x : Span} (h : AliveP (rng ctx) x) :
    rng (extend ctx x).val = img (rng ctx) x := by
  cases ctx with
  | none => exact rng_bound_rightIface x
  | some c =>
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp ((compose_isSome_iff c x).mpr h)
    have hv : (extend (some c) x).val = bound z.rightIface := by
      simp only [extend, bind_val]
      rw [show (Charged.compose c x).val = some z from hz]
      rfl
    rw [hv, rng_bound_rightIface, img_compose hz]
    rfl

theorem img_subset_of_covers {a s : Span} (h : a.Covers s) (ρ : Set GTerm) : img ρ s ⊆ img ρ a := by
  rintro t ⟨m, hm, S, hS⟩
  obtain ⟨y, hy, h₁, h₂, -⟩ := h _ hS
  obtain ⟨y₁, y₂, y₃⟩ := y
  simp only at h₁ h₂
  subst h₁ h₂
  exact ⟨_, hm, y₃, hy⟩

/-- Interfaces that are equal as memo keys let the same terms through. -/
theorem sameCtx_rng {a b : Option Span} (h : (sameCtx a b).val = true) : rng a = rng b := by
  match a, b, h with
  | none, none, _ => rfl
  | some a, some b, h =>
    simp only [sameCtx, bind_val] at h
    have h₁ : a.covers? b = true := by
      by_contra hc
      rw [show (Charged.covers a b).val = a.covers? b from rfl] at h
      simp [hc] at h
    rw [show (Charged.covers a b).val = a.covers? b from rfl, h₁] at h
    have h₂ : b.covers? a = true := h
    exact Set.Subset.antisymm (img_subset_of_covers ((covers?_iff b a).mp h₂) _)
      (img_subset_of_covers ((covers?_iff a b).mp h₁) _)
  | none, some _, h => cases h
  | some _, none, h => cases h

end R003

end RwLog
