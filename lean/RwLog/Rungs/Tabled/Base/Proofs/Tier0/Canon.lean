/-
# Tier 0 proofs, part 3: table keys

A goal's table is keyed by `GoalOf.norm`: its expression is put in canonical
form (`|` nests flattened, sorted, deduplicated, `0` dropped) and its
converses are stripped. Derivations survive both exactly. To measure them,
`DW w e s` is a derivation of weight `w` in which `|` steps are free: the
canonical form keeps the weight, and stripping a converse lowers it. This is
the measure the completion and fairness inductions run on.
-/
import RwLog.Rungs.Tabled.Base.Proofs.Tier0.Goal

namespace RwLog

namespace R001

namespace Tier0

variable (P : Program)

/-- Derivations with a weight that ignores `|` steps. -/
inductive DW : Nat → Rel → Span → Prop
  | span (s : Span) : DW 1 (.span s) s
  | orl {w : Nat} {a b : Rel} {s : Span} : DW w a s → DW w (.or a b) s
  | orr {w : Nat} {a b : Rel} {s : Span} : DW w b s → DW w (.or a b) s
  | seq {w₁ w₂ : Nat} {a b : Rel} {s₁ s₂ s : Span} : DW w₁ a s₁ → DW w₂ b s₂ →
      s₁.compose s₂ = some s → DW (w₁ + w₂ + 1) (.seq a b) s
  | and {w₁ w₂ : Nat} {a b : Rel} {s₁ s₂ s : Span} : DW w₁ a s₁ → DW w₂ b s₂ →
      s₁.meet s₂ = some s → DW (w₁ + w₂ + 1) (.and a b) s
  | conv {w : Nat} {a : Rel} {s : Span} : DW w a s → DW (w + 1) (.conv a) s.swap
  | call {w : Nat} {n : Name} {s : Span} : DW w (P.body n) s → DW (w + 1) (.call n) s

variable {P}

theorem DW.derives {w : Nat} {e : Rel} {s : Span} (h : DW P w e s) : Derives P e s := by
  induction h with
  | span s => exact .span s
  | orl _ ih => exact .orl ih
  | orr _ ih => exact .orr ih
  | seq _ _ hc ih₁ ih₂ => exact .seq ih₁ ih₂ hc
  | and _ _ hc ih₁ ih₂ => exact .and ih₁ ih₂ hc
  | conv _ ih => exact .conv ih
  | call _ ih => exact .call ih

theorem dw_of_derives {e : Rel} {s : Span} (h : Derives P e s) : ∃ w, DW P w e s := by
  induction h with
  | span s => exact ⟨1, .span s⟩
  | orl _ ih => obtain ⟨w, h⟩ := ih; exact ⟨w, .orl h⟩
  | orr _ ih => obtain ⟨w, h⟩ := ih; exact ⟨w, .orr h⟩
  | seq _ _ hc ih₁ ih₂ =>
    obtain ⟨w₁, h₁⟩ := ih₁; obtain ⟨w₂, h₂⟩ := ih₂; exact ⟨_, .seq h₁ h₂ hc⟩
  | and _ _ hc ih₁ ih₂ =>
    obtain ⟨w₁, h₁⟩ := ih₁; obtain ⟨w₂, h₂⟩ := ih₂; exact ⟨_, .and h₁ h₂ hc⟩
  | conv _ ih => obtain ⟨w, h⟩ := ih; exact ⟨_, .conv h⟩
  | call _ ih => obtain ⟨w, h⟩ := ih; exact ⟨_, .call h⟩

theorem dw_zero {w : Nat} {s : Span} : ¬ DW P w .zero s := fun h => by cases h

theorem dw_or {w : Nat} {a b : Rel} {s : Span} : DW P w (.or a b) s ↔ DW P w a s ∨ DW P w b s := by
  constructor
  · intro h; cases h with
    | orl h => exact .inl h
    | orr h => exact .inr h
  · rintro (h | h)
    · exact .orl h
    · exact .orr h

theorem orBranches_of_not_or {e : Rel} (h : ∀ a b, e ≠ .or a b) : orBranches e = [e] := by
  cases e <;> first | (exfalso; exact h _ _ rfl) | rfl

theorem dw_orBranches {w : Nat} {s : Span} : ∀ e : Rel,
    DW P w e s ↔ ∃ b ∈ orBranches e, DW P w b s
  | .or a b => by
    rw [dw_or, dw_orBranches a, dw_orBranches b]
    simp only [orBranches, List.mem_append]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | .zero => by simp [orBranches]
  | .span _ => by simp [orBranches]
  | .and _ _ => by simp [orBranches]
  | .seq _ _ => by simp [orBranches]
  | .conv _ => by simp [orBranches]
  | .call _ => by simp [orBranches]

theorem dw_mkOr {w : Nat} {s : Span} : ∀ es : List Rel, DW P w (mkOr es) s ↔ ∃ e ∈ es, DW P w e s
  | [] => by simp only [mkOr, List.not_mem_nil, false_and, exists_false, iff_false]; exact dw_zero
  | [e] => by simp [mkOr]
  | e :: e' :: es => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, dw_or, dw_mkOr (e' :: es)]
    simp only [List.mem_cons]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨e, .inl rfl, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, rfl | hx, h⟩
      · exact .inl h
      · exact .inr ⟨x, hx, h⟩

/-- The canonical form derives exactly what the expression derives, with the
same weights. -/
theorem dw_canon : ∀ (e : Rel) {w : Nat} {s : Span}, DW P w (canon e) s ↔ DW P w e s
  | .zero, _, _ => by rw [canon]
  | .span _, _, _ => by rw [canon]
  | .call _, _, _ => by rw [canon]
  | .or a b, w, s => by
    rw [canon, dw_mkOr, dw_or, ← dw_canon a, ← dw_canon b, dw_orBranches (canon a),
      dw_orBranches (canon b)]
    simp only [mem_sortedBranches, List.mem_append]
    constructor
    · rintro ⟨x, ⟨hx | hx, -⟩, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, ⟨.inl hx, fun e => dw_zero (e ▸ h)⟩, h⟩
      · exact ⟨x, ⟨.inr hx, fun e => dw_zero (e ▸ h)⟩, h⟩
  | .and a b, w, s => by
    rw [canon]
    constructor
    · intro h; cases h with
      | and h₁ h₂ hc => exact .and ((dw_canon a).1 h₁) ((dw_canon b).1 h₂) hc
    · intro h; cases h with
      | and h₁ h₂ hc => exact .and ((dw_canon a).2 h₁) ((dw_canon b).2 h₂) hc
  | .seq a b, w, s => by
    rw [canon]
    constructor
    · intro h; cases h with
      | seq h₁ h₂ hc => exact .seq ((dw_canon a).1 h₁) ((dw_canon b).1 h₂) hc
    · intro h; cases h with
      | seq h₁ h₂ hc => exact .seq ((dw_canon a).2 h₁) ((dw_canon b).2 h₂) hc
  | .conv a, w, s => by
    rw [canon]
    constructor
    · intro h; cases h with
      | conv h => exact .conv ((dw_canon a).1 h)
    · intro h; cases h with
      | conv h => exact .conv ((dw_canon a).2 h)

theorem derives_canon {e : Rel} {s : Span} : Derives P (canon e) s ↔ Derives P e s := by
  constructor
  · intro h; obtain ⟨w, h⟩ := dw_of_derives h; exact ((dw_canon e).1 h).derives
  · intro h; obtain ⟨w, h⟩ := dw_of_derives h; exact ((dw_canon e).2 h).derives

/-! ## Stripping converses -/

theorem strip_conv (lb rb : Option Span) (a : Rel) :
    GoalOf.stripConv ⟨lb, .conv a, rb⟩ =
      (!(GoalOf.stripConv ⟨rb.map Span.swap, a, lb.map Span.swap⟩).1,
        (GoalOf.stripConv ⟨rb.map Span.swap, a, lb.map Span.swap⟩).2) := by
  rw [GoalOf.stripConv]

theorem strip_nc (g : Goal) (h : ∀ a, g.e ≠ .conv a) : g.stripConv = (false, g) := by
  obtain ⟨lb, e, rb⟩ := g
  cases e <;> first | (exfalso; exact h _ rfl) | (rw [GoalOf.stripConv]; intro _ _ _ h; simp at h)

variable {T : Theory}

theorem goodG_strip : ∀ (e : Rel) (lb rb : Option Span), GoodG ⟨lb, e, rb⟩ →
    GoodG (GoalOf.stripConv ⟨lb, e, rb⟩).2
  | .conv a, lb, rb, h => by
    rw [strip_conv]
    exact goodG_strip a _ _ ⟨goodBO_map_swap h.2, goodBO_map_swap h.1⟩
  | .zero, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .span _, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .or _ _, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .and _ _, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .seq _ _, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .call _, _, _, h => by rw [strip_nc _ (by simp)]; exact h

theorem goodG_norm {g : Goal} (h : GoodG g) : GoodG g.norm.2 :=
  goodG_strip (canon g.e) g.lb g.rb h

theorem gden_e (g : Goal) (e : Rel) (R : GRel) : GDen ⟨g.lb, e, g.rb⟩ R = GDen g R := rfl

/-- Reading a derivation of a stripped goal back through its converses. -/
theorem strip_back : ∀ (e : Rel) (lb rb : Option Span) (s : Span),
    Derives P (GoalOf.stripConv ⟨lb, e, rb⟩).2.e s →
    Derives P e (oS (GoalOf.stripConv ⟨lb, e, rb⟩).1 s) ∧
    GDen ⟨lb, e, rb⟩ (oS (GoalOf.stripConv ⟨lb, e, rb⟩).1 s).den =
      oR (GoalOf.stripConv ⟨lb, e, rb⟩).1 (GDen (GoalOf.stripConv ⟨lb, e, rb⟩).2 s.den)
  | .conv a, lb, rb, s, h => by
    rw [strip_conv] at h ⊢
    obtain ⟨h1, h2⟩ := strip_back a _ _ s h
    refine ⟨?_, ?_⟩
    · rw [oS_not]; exact .conv h1
    · rw [oS_not, oR_not, ← h2, swap_den]
      exact gden_conv ⟨lb, .conv a, rb⟩ a _
  | .zero, lb, rb, s, h => by rw [strip_nc _ (by simp)] at h ⊢; exact ⟨h, rfl⟩
  | .span _, lb, rb, s, h => by rw [strip_nc _ (by simp)] at h ⊢; exact ⟨h, rfl⟩
  | .or _ _, lb, rb, s, h => by rw [strip_nc _ (by simp)] at h ⊢; exact ⟨h, rfl⟩
  | .and _ _, lb, rb, s, h => by rw [strip_nc _ (by simp)] at h ⊢; exact ⟨h, rfl⟩
  | .seq _ _, lb, rb, s, h => by rw [strip_nc _ (by simp)] at h ⊢; exact ⟨h, rfl⟩
  | .call _, lb, rb, s, h => by rw [strip_nc _ (by simp)] at h ⊢; exact ⟨h, rfl⟩

/-- A derivation of a goal's table key gives one of the goal, with the
relation read through the key's orientation. -/
theorem norm_back (g : Goal) {s : Span} (h : Derives P g.norm.2.e s) :
    Derives P g.e (oS g.norm.1 s) ∧ GDen g (oS g.norm.1 s).den = oR g.norm.1 (GDen g.norm.2 s.den) := by
  obtain ⟨h1, h2⟩ := strip_back (canon g.e) g.lb g.rb s h
  exact ⟨derives_canon.1 h1, h2⟩

/-- Moving a weighted derivation onto a stripped goal: the weight does not
grow, and it drops when a converse is stripped. -/
theorem strip_fwd : ∀ (e : Rel) (lb rb : Option Span) {w : Nat} {s : Span}, DW P w e s →
    ∃ w' s', DW P w' (GoalOf.stripConv ⟨lb, e, rb⟩).2.e s' ∧ w' ≤ w ∧
      ((∃ a, e = .conv a) → w' < w) ∧
      GDen ⟨lb, e, rb⟩ s.den = oR (GoalOf.stripConv ⟨lb, e, rb⟩).1 (GDen (GoalOf.stripConv ⟨lb, e, rb⟩).2 s'.den)
  | .conv a, lb, rb, w, s, h => by
    rw [strip_conv]
    cases h with
    | @conv w₀ _ s₀ h₀ =>
      obtain ⟨w', s', h1, h2, -, h4⟩ := strip_fwd a (rb.map Span.swap) (lb.map Span.swap) h₀
      refine ⟨w', s', h1, by omega, fun _ => by omega, ?_⟩
      rw [oR_not, ← h4, swap_den]
      exact gden_conv ⟨lb, .conv a, rb⟩ a _
  | .zero, lb, rb, w, s, h => ⟨w, s, by rw [strip_nc _ (by simp)]; exact h, le_rfl,
      (fun ⟨_, h⟩ => by cases h), by rw [strip_nc _ (by simp)]; rfl⟩
  | .span _, lb, rb, w, s, h => ⟨w, s, by rw [strip_nc _ (by simp)]; exact h, le_rfl,
      (fun ⟨_, h⟩ => by cases h), by rw [strip_nc _ (by simp)]; rfl⟩
  | .or _ _, lb, rb, w, s, h => ⟨w, s, by rw [strip_nc _ (by simp)]; exact h, le_rfl,
      (fun ⟨_, h⟩ => by cases h), by rw [strip_nc _ (by simp)]; rfl⟩
  | .and _ _, lb, rb, w, s, h => ⟨w, s, by rw [strip_nc _ (by simp)]; exact h, le_rfl,
      (fun ⟨_, h⟩ => by cases h), by rw [strip_nc _ (by simp)]; rfl⟩
  | .seq _ _, lb, rb, w, s, h => ⟨w, s, by rw [strip_nc _ (by simp)]; exact h, le_rfl,
      (fun ⟨_, h⟩ => by cases h), by rw [strip_nc _ (by simp)]; rfl⟩
  | .call _, lb, rb, w, s, h => ⟨w, s, by rw [strip_nc _ (by simp)]; exact h, le_rfl,
      (fun ⟨_, h⟩ => by cases h), by rw [strip_nc _ (by simp)]; rfl⟩

/-- Moving a weighted derivation onto a goal's table key. The weight does not
grow; if the goal's expression is not a `|`, then the key's expression is not
a `|` either unless the weight dropped. -/
theorem norm_fwd (g : Goal) {w : Nat} {s : Span} (h : DW P w g.e s) :
    ∃ w' s', DW P w' g.norm.2.e s' ∧ w' ≤ w ∧
      ((∀ a b, g.e ≠ .or a b) → w' < w ∨ ∀ a b, g.norm.2.e ≠ .or a b) ∧
      GDen g s.den = oR g.norm.1 (GDen g.norm.2 s'.den) := by
  obtain ⟨w', s', h1, h2, h3, h4⟩ := strip_fwd (canon g.e) g.lb g.rb ((dw_canon g.e).2 h)
  refine ⟨w', s', h1, h2, fun hn => ?_, h4⟩
  obtain ⟨lb, e, rb⟩ := g
  simp only at hn h3 ⊢
  cases e with
  | conv a => exact .inl (h3 ⟨canon a, by rw [canon]⟩)
  | or a b => exact absurd rfl (hn a b)
  | zero => right; intro a b; simp [GoalOf.norm, canon, strip_nc]
  | span _ => right; intro a b; simp [GoalOf.norm, canon, strip_nc]
  | and _ _ => right; intro a b; simp [GoalOf.norm, canon, strip_nc]
  | seq _ _ => right; intro a b; simp [GoalOf.norm, canon, strip_nc]
  | call _ => right; intro a b; simp [GoalOf.norm, canon, strip_nc]

theorem goodG_root (q : Rel) : GoodG ⟨none, q, none⟩ := ⟨trivial, trivial⟩

end Tier0

end R001

end RwLog
