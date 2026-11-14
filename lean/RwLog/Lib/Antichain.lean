/-
# An antichain that covers a list

`antichain le L` keeps the members of `L` that no other member covers, one
of each class of members that cover each other. When `le` decides a
reflexive and transitive relation on the members, the result has no repeats,
covers every member, and no member of it covers another
(`antichain_spec`).
-/
import RwLog.Lib.List

namespace RwLog

/-- The members that no other member covers, one of each. -/
def antichain {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: L =>
    if (antichain le L).any (le a) then antichain le L
    else a :: (antichain le L).filter fun b => !le b a

/-- `antichain` gives an antichain that covers the list, when the test
decides a reflexive and transitive relation on its members. -/
theorem antichain_spec {α : Type} (le : α → α → Bool) (P : α → α → Prop) (refl : ∀ a, P a a)
    (trans : ∀ a b c, P a b → P b c → P a c) : ∀ L : List α,
    (∀ a ∈ L, ∀ b ∈ L, le a b = true ↔ P a b) →
    (antichain le L).Nodup ∧ (∀ a ∈ antichain le L, a ∈ L) ∧
      (∀ a ∈ L, ∃ b ∈ antichain le L, P a b) ∧
      ∀ a ∈ antichain le L, ∀ b ∈ antichain le L, P a b → a = b
  | [], _ => ⟨List.nodup_nil, by simp [antichain], by simp, by simp [antichain]⟩
  | a :: L, hle => by
    obtain ⟨hnd, hsub, hcov, hanti⟩ := antichain_spec le P refl trans L
      fun b hb c hc => hle b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc)
    have hla : ∀ b ∈ antichain le L, (le a b = true ↔ P a b) ∧ (le b a = true ↔ P b a) :=
      fun b hb => ⟨hle a List.mem_cons_self b (List.mem_cons_of_mem _ (hsub b hb)),
        hle b (List.mem_cons_of_mem _ (hsub b hb)) a List.mem_cons_self⟩
    rw [antichain]
    by_cases h : (antichain le L).any (le a) = true
    · simp only [h, ↓reduceIte]
      refine ⟨hnd, fun b hb => List.mem_cons_of_mem _ (hsub b hb), ?_, hanti⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · obtain ⟨b, hb, hcb⟩ := List.any_eq_true.1 h
        exact ⟨b, hb, ((hla b hb).1).1 hcb⟩
      · exact hcov c hc
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      have hno : ∀ b ∈ antichain le L, ¬ P a b := by
        intro b hb hp
        exact h (List.any_eq_true.2 ⟨b, hb, ((hla b hb).1).2 hp⟩)
      have hf : ∀ b, b ∈ (antichain le L).filter (fun b => !le b a) ↔
          b ∈ antichain le L ∧ ¬ P b a := by
        intro b
        rw [List.mem_filter]
        constructor
        · rintro ⟨hb, hn⟩
          refine ⟨hb, fun hp => ?_⟩
          rw [((hla b hb).2).2 hp] at hn
          cases hn
        · rintro ⟨hb, hn⟩
          refine ⟨hb, ?_⟩
          cases hl : le b a with
          | false => rfl
          | true => exact absurd (((hla b hb).2).1 hl) hn
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        exact ⟨fun hm => hno a ((hf a).1 hm).1 (refl a), hnd.filter _⟩
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub b ((hf b).1 hb).1)
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨c, List.mem_cons_self, refl c⟩
        · obtain ⟨b, hb, hcb⟩ := hcov c hc
          by_cases hba : P b a
          · exact ⟨a, List.mem_cons_self, trans _ _ _ hcb hba⟩
          · exact ⟨b, List.mem_cons_of_mem _ ((hf b).2 ⟨hb, hba⟩), hcb⟩
      · intro b hb c hc hbc
        rcases List.mem_cons.1 hb with rfl | hb <;> rcases List.mem_cons.1 hc with rfl | hc
        · rfl
        · exact absurd hbc (hno c ((hf c).1 hc).1)
        · exact absurd hbc ((hf b).1 hb).2
        · exact hanti b ((hf b).1 hb).1 c ((hf c).1 hc).1 hbc

end RwLog
