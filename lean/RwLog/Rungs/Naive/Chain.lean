/-
# Sequential chains

A chain is a list of factors read as their sequential composition, with the
empty chain the identity. These lemmas let a chain be split and joined both
in the ground semantics and in derivations.
-/
import RwLog.SpanLayer.Derives
import RwLog.SpanLayer.Algebra

namespace RwLog

def idRel : Rel := .span Span.idSpan

/-- A chain of factors as an expression. -/
def toRel : List Rel → Rel
  | [] => idRel
  | [f] => f
  | f :: g :: fs => .seq f (toRel (g :: fs))

variable {P : Program}

theorem denote_idRel (ρ : Name → GRel) : denote ρ idRel = GRel.id := Span.den_idSpan

theorem denote_toRel_cons (ρ : Name → GRel) (f : Rel) (p : List Rel) :
    denote ρ (toRel (f :: p)) = (denote ρ f).comp (denote ρ (toRel p)) := by
  cases p with
  | nil => simp [toRel, denote_idRel, GRel.comp_id]
  | cons g p => rfl

theorem denote_toRel_append (ρ : Name → GRel) (p q : List Rel) :
    denote ρ (toRel (p ++ q)) = (denote ρ (toRel p)).comp (denote ρ (toRel q)) := by
  induction p with
  | nil => simp [toRel, denote_idRel, GRel.id_comp]
  | cons f p ih =>
    rw [List.cons_append, denote_toRel_cons, ih, denote_toRel_cons, GRel.comp_assoc]

theorem derivesN_idRel {n s} (h : DerivesN P n idRel s) : s = Span.idSpan := by
  cases h; rfl

theorem chain_cons_split {n f p s} (h : DerivesN P n (toRel (f :: p)) s) :
    ∃ s₁ s₂, DerivesN P n f s₁ ∧ DerivesN P n (toRel p) s₂ ∧
      s.den = (s₁.den).comp s₂.den := by
  cases p with
  | nil =>
    refine ⟨s, Span.idSpan, h, .span n _, ?_⟩
    rw [Span.den_idSpan, GRel.comp_id]
  | cons g p =>
    cases h with
    | seq h₁ h₂ hc => exact ⟨_, _, h₁, h₂, compose_some hc⟩

theorem chain_cons_join {n f p s₁ s₂} (h₁ : DerivesN P n f s₁) (h₂ : DerivesN P n (toRel p) s₂)
    (hne : ((s₁.den).comp s₂.den).Nonempty) :
    ∃ s, DerivesN P n (toRel (f :: p)) s ∧ (s₁.den).comp s₂.den = s.den := by
  cases p with
  | nil =>
    rw [derivesN_idRel h₂, Span.den_idSpan, GRel.comp_id]
    exact ⟨s₁, h₁, rfl⟩
  | cons g p =>
    obtain ⟨s, hc, hs⟩ := compose_isSome hne
    exact ⟨s, .seq h₁ h₂ hc, hs.symm⟩

theorem chain_split {n} : ∀ (p q : List Rel) {s}, DerivesN P n (toRel (p ++ q)) s →
    (s.den).Nonempty →
    ∃ s₁ s₂, DerivesN P n (toRel p) s₁ ∧ DerivesN P n (toRel q) s₂ ∧
      s.den = (s₁.den).comp s₂.den
  | [], q, s, h, _ => by
    refine ⟨Span.idSpan, s, .span n _, h, ?_⟩
    rw [Span.den_idSpan, GRel.id_comp]
  | f :: p, q, s, h, hne => by
    rw [List.cons_append] at h
    obtain ⟨sf, s', hf, h', hs⟩ := chain_cons_split h
    have hne' : (s'.den).Nonempty := GRel.comp_nonempty_right (hs ▸ hne)
    obtain ⟨sp, sq, hp, hq, hs'⟩ := chain_split p q h' hne'
    have hsub : s.den = ((sf.den).comp sp.den).comp sq.den := by
      rw [GRel.comp_assoc, hs, hs']
    obtain ⟨t, ht, ht'⟩ := chain_cons_join hf hp (GRel.comp_nonempty_left (hsub ▸ hne))
    exact ⟨t, sq, ht, hq, by rw [hsub, ht']⟩

theorem chain_join {n} : ∀ (p q : List Rel) {s₁ s₂}, DerivesN P n (toRel p) s₁ →
    DerivesN P n (toRel q) s₂ → ((s₁.den).comp s₂.den).Nonempty →
    ∃ s, DerivesN P n (toRel (p ++ q)) s ∧ (s₁.den).comp s₂.den = s.den
  | [], q, s₁, s₂, h₁, h₂, _ => by
    rw [derivesN_idRel h₁, Span.den_idSpan, GRel.id_comp]
    exact ⟨s₂, h₂, rfl⟩
  | f :: p, q, s₁, s₂, h₁, h₂, hne => by
    obtain ⟨sf, sp, hf, hp, hs⟩ := chain_cons_split h₁
    have hsub : (s₁.den).comp s₂.den = (sf.den).comp ((sp.den).comp s₂.den) := by
      rw [hs, GRel.comp_assoc]
    have hne' := hsub ▸ hne
    obtain ⟨t, ht, ht'⟩ := chain_join p q hp h₂ (GRel.comp_nonempty_right hne')
    have hne'' : ((sf.den).comp t.den).Nonempty := ht' ▸ hne'
    obtain ⟨u, hu, hu'⟩ := chain_cons_join hf ht hne''
    rw [List.cons_append]
    exact ⟨u, hu, by rw [hsub, ht', hu']⟩

end RwLog
