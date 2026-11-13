/-
# Derivations of a bounded depth

`GDn P k e` is the set of ground relations `e` derives with at most `k`
calls unfolded along any branch of the derivation. Every derivation has a
depth (`mem_gd_iff`), and a node of the normal form derives at depth `k` what
its parts derive at depth `k`, however a chain is split in two and whichever
member is taken out of a meet (`GLaws.chain_split`, `GLaws.meet_split`); a
call derives at depth `k + 1` what the node of its body derives at depth `k`
(`gdn_bodyOf`).

Proofs about a machine that splits the chains and meets of the normal form
its own way go by induction on the depth and then on the node, where a
derivation of the expression as written would have fixed the split.
-/
import RwLog.Kernel.NormalFormStable
import RwLog.Trusted.Charged

namespace RwLog

open GRel

variable (P : Program)

/-- The ground relations `e` derives with at most `k` nested calls
unfolded. -/
def GDn : Nat → Rel → Set GRel
  | _, .zero => ∅
  | _, .span s => {s.den}
  | k, .or a b => GDn k a ∪ GDn k b
  | k, .seq a b => Set.image2 GRel.comp (GDn k a) (GDn k b)
  | k, .and a b => Set.image2 GRel.meet (GDn k a) (GDn k b)
  | k, .conv a => GRel.inv '' GDn k a
  | 0, .call _ => ∅
  | k + 1, .call n => GDn k (P.body n)
termination_by k e => (k, e)

theorem gdn_laws (k : Nat) : GLaws (GDn P k) where
  zero := by cases k <;> simp [GDn]
  span s := by cases k <;> simp [GDn]
  or a b := by cases k <;> simp [GDn]
  seq a b := by cases k <;> simp [GDn]
  and a b := by cases k <;> simp [GDn]
  conv a := by cases k <;> simp [GDn]

@[simp] theorem gdn_call_zero (n : Name) : GDn P 0 (.call n) = ∅ := by simp [GDn]

@[simp] theorem gdn_call_succ (k : Nat) (n : Name) : GDn P (k + 1) (.call n) = GDn P k (P.body n) := by
  simp [GDn]

variable {P}

theorem gdn_succ : ∀ (k : Nat) (e : Rel), GDn P k e ⊆ GDn P (k + 1) e
  | k, .zero => by rw [(gdn_laws P k).zero]; exact Set.empty_subset _
  | k, .span s => by rw [(gdn_laws P k).span, (gdn_laws P (k + 1)).span]
  | k, .or a b => by
    rw [(gdn_laws P k).or, (gdn_laws P (k + 1)).or]
    exact Set.union_subset_union (gdn_succ k a) (gdn_succ k b)
  | k, .seq a b => by
    rw [(gdn_laws P k).seq, (gdn_laws P (k + 1)).seq]
    exact Set.image2_subset (gdn_succ k a) (gdn_succ k b)
  | k, .and a b => by
    rw [(gdn_laws P k).and, (gdn_laws P (k + 1)).and]
    exact Set.image2_subset (gdn_succ k a) (gdn_succ k b)
  | k, .conv a => by
    rw [(gdn_laws P k).conv, (gdn_laws P (k + 1)).conv]
    exact Set.image_mono (gdn_succ k a)
  | 0, .call n => by rw [gdn_call_zero]; exact Set.empty_subset _
  | k + 1, .call n => by
    rw [gdn_call_succ, gdn_call_succ]; exact gdn_succ k (P.body n)
termination_by k e => (k, e)

theorem gdn_mono {k k' : Nat} (h : k ≤ k') (e : Rel) : GDn P k e ⊆ GDn P k' e := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (gdn_succ _ e)

theorem gdn_sub_gd : ∀ (k : Nat) (e : Rel), GDn P k e ⊆ GD P e
  | k, .zero => by rw [(gdn_laws P k).zero]; exact Set.empty_subset _
  | k, .span s => by rw [(gdn_laws P k).span, gd_span]
  | k, .or a b => by
    rw [(gdn_laws P k).or, gd_or]
    exact Set.union_subset_union (gdn_sub_gd k a) (gdn_sub_gd k b)
  | k, .seq a b => by
    rw [(gdn_laws P k).seq, gd_seq]
    exact Set.image2_subset (gdn_sub_gd k a) (gdn_sub_gd k b)
  | k, .and a b => by
    rw [(gdn_laws P k).and, gd_and]
    exact Set.image2_subset (gdn_sub_gd k a) (gdn_sub_gd k b)
  | k, .conv a => by
    rw [(gdn_laws P k).conv, gd_conv]
    exact Set.image_mono (gdn_sub_gd k a)
  | 0, .call n => by rw [gdn_call_zero]; exact Set.empty_subset _
  | k + 1, .call n => by
    rw [gdn_call_succ, gd_call]; exact gdn_sub_gd k (P.body n)
termination_by k e => (k, e)

theorem DerivesG.depth {e : Rel} {G : GRel} (h : DerivesG P e G) : ∃ k, G ∈ GDn P k e := by
  induction h with
  | span s => exact ⟨0, by rw [(gdn_laws P 0).span]; rfl⟩
  | @orl a b G _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k, by rw [(gdn_laws P k).or]; exact .inl hk⟩
  | @orr a b G _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k, by rw [(gdn_laws P k).or]; exact .inr hk⟩
  | @seq a b A B _ _ ih₁ ih₂ =>
    obtain ⟨k₁, h₁⟩ := ih₁
    obtain ⟨k₂, h₂⟩ := ih₂
    refine ⟨max k₁ k₂, ?_⟩
    rw [(gdn_laws P _).seq]
    exact ⟨_, gdn_mono (le_max_left _ _) a h₁, _, gdn_mono (le_max_right _ _) b h₂, rfl⟩
  | @and a b A B _ _ ih₁ ih₂ =>
    obtain ⟨k₁, h₁⟩ := ih₁
    obtain ⟨k₂, h₂⟩ := ih₂
    refine ⟨max k₁ k₂, ?_⟩
    rw [(gdn_laws P _).and]
    exact ⟨_, gdn_mono (le_max_left _ _) a h₁, _, gdn_mono (le_max_right _ _) b h₂, rfl⟩
  | @conv a A _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k, by rw [(gdn_laws P k).conv]; exact ⟨_, hk, rfl⟩⟩
  | @call n G _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by rw [gdn_call_succ]; exact hk⟩

/-- Every derivation has a depth. -/
theorem mem_gd_iff {e : Rel} {G : GRel} : G ∈ GD P e ↔ ∃ k, G ∈ GDn P k e :=
  ⟨fun h => DerivesG.depth h, fun ⟨k, h⟩ => gdn_sub_gd k e h⟩

/-! ## Nodes -/

/-- The body node of a call node derives, one level down, what the call
derives. -/
theorem gdn_bodyOf {e b : Rel} (h : Charged.bodyOf P e = some b) (k : Nat) :
    GDn P (k + 1) e = GDn P k b ∧ GDn P 0 e = ∅ := by
  unfold Charged.bodyOf at h
  split at h
  · cases h
    exact ⟨by rw [gdn_call_succ, (gdn_laws P k).gd_norm], gdn_call_zero P _⟩
  · cases h
    exact ⟨by rw [(gdn_laws P _).conv, gdn_call_succ, (gdn_laws P k).gd_normConv],
      by rw [(gdn_laws P _).conv, gdn_call_zero, Set.image_empty]⟩
  · cases h

section

variable {G : Rel → Set GRel} (hG : GLaws G)
include hG

/-- A chain derives the compositions of what its two stretches derive,
wherever it is split. -/
theorem GLaws.chain_split {e l r : Rel} {i : Nat} (hl : e.interval 0 i = some l)
    (hr : e.interval i (seqParts e).length = some r) :
    G e = Set.image2 GRel.comp (G l) (G r) := by
  unfold RelOf.interval at hl hr
  split at hl
  · next h₁ =>
    split at hr
    · next h₂ =>
      cases hl; cases hr
      have hne₁ : ((seqParts e).take i).drop 0 ≠ [] := by
        simp only [List.drop_zero, ne_eq, List.take_eq_nil_iff, not_or]
        exact ⟨by omega, seqParts_ne_nil e⟩
      have hne₂ : ((seqParts e).take (seqParts e).length).drop i ≠ [] := by
        simp only [List.take_length, ne_eq, List.drop_eq_nil_iff, not_le]; omega
      rw [hG.gd_mkSeq hne₁, hG.gd_mkSeq hne₂, ← seqAll_append, ← List.map_append,
        List.drop_zero, List.take_length, List.take_append_drop, hG.gd_seqParts]
    · cases hr
  · cases hl

/-- A meet derives the meets of what a member and the meet of the others
derive, whichever member is taken out. -/
theorem GLaws.meet_split {e l r : Rel} {i : Nat} (hl : (andParts e)[i]? = some l)
    (hr : e.without i = some r) : G e = Set.image2 GRel.meet (G l) (G r) := by
  unfold RelOf.without at hr
  split at hr
  · next h =>
    cases hr
    have hne : (andParts e).eraseIdx i ≠ [] := by
      intro h'
      have := List.length_eraseIdx_of_lt h.1
      rw [h'] at this; simp at this; omega
    have hp : (andParts e).Perm (l :: (andParts e).eraseIdx i) := by
      have hi := h.1
      have : l = (andParts e)[i] := by
        rw [List.getElem?_eq_getElem hi] at hl; exact (Option.some.inj hl).symm
      rw [this]
      exact (List.getElem_cons_eraseIdx_perm hi).symm
    rw [hG.gd_mkAnd hne, ← hG.gd_andParts e, andAll_perm (hp.map G)]
    rfl
  · cases hr

end

end RwLog
