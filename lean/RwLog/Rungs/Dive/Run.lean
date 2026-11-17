/-
# The run of the diving engine

A step of the diving engine at a kernel that returns what a domain returns
(`st_eq`): it costs at most its budget and a tick, it never reports that it
is done, and it emits the answer of its reading if the reading fits the
budget. With that, the run from the first state: the budget `2 ^ L` is
reached within `L * L` steps, and if the reading by the number 0 makes an
answer within that budget, the answer is emitted at the next step, the
engine having spent at most `(L * L + 1) * (2 ^ L + 3)` ticks
(`first_reading`).
-/
import RwLog.Rungs.Dive.Read
import RwLog.Rungs.Framework.BesideRun
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace RwLog

namespace Dive

open Beside

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D)

/-- The step at the derivation kernel of `P`. -/
abbrev st (s : State Rel) : Cost (StepOf (Ans D P) (State Rel)) :=
  @step R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) s

/-- What a step shows, at the derivation kernel of `P`. -/
abbrev fin (s : State Rel) (r : Option (Option (Ans D P) × Nat)) :
    Cost (StepOf (Ans D P) (State Rel)) :=
  @finish R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) s r

theorem st_eq (s : State Rel) :
    st (P := P) K hK s =
      Cost.within (2 ^ s.level) (rd K hK (2 ^ s.level) s.number s.root) >>= fin K hK s := by
  at_cost K hK
  rfl

theorem fin_some (s : State Rel) (a : Ans D P) (k : Nat) :
    fin K hK s (some (some a, k)) =
      (Ans.swapA D P a >>= fun a' => pure (.emit [a, a'] s.next)) := by
  at_cost K hK
  rfl

theorem fin_next (s : State Rel) (r : Option (Option (Ans D P) × Nat)) :
    next (fin K hK s r).val = some s.next := by
  at_cost K hK
  rcases r with _ | ⟨_ | a, k⟩ <;> rfl

theorem fin_price (s : State Rel) (r : Option (Option (Ans D P) × Nat)) :
    (fin K hK s r).ticks + shown (fin K hK s r).val ≤ 3 := by
  at_cost K hK
  rcases r with _ | ⟨_ | a, k⟩
  · exact Nat.zero_le 3
  · exact Nat.zero_le 3
  · exact Nat.le_refl 3

theorem within_ticks_le {α : Type} (b : Nat) (m : Cost α) : (Cost.within b m).ticks ≤ b := by
  unfold Cost.within
  split
  · assumption
  · exact Nat.le_refl b

/-- A step never reports that the engine is done. -/
theorem st_next (s : State Rel) : next (st (P := P) K hK s).val = some s.next := by
  rw [st_eq, Cost.bind_val]
  exact fin_next K hK s _

/-- A step costs at most its budget and three ticks, with the tick for each
answer it shows. -/
theorem st_price (s : State Rel) :
    (st (P := P) K hK s).ticks + shown (st (P := P) K hK s).val ≤ 2 ^ s.level + 3 := by
  rw [st_eq, Cost.bind_ticks, Cost.bind_val]
  have h1 := within_ticks_le (2 ^ s.level) (rd (P := P) K hK (2 ^ s.level) s.number s.root)
  have h2 := fin_price K hK s
    (Cost.within (2 ^ s.level) (rd (P := P) K hK (2 ^ s.level) s.number s.root)).val
  omega

/-- A step emits the answer of its reading, if the reading fits the
budget. -/
theorem st_emit {s : State Rel} {a : Ans D P} {k' : Nat}
    (hv : (rd K hK (2 ^ s.level) s.number s.root).val = (some a, k'))
    (ht : (rd (P := P) K hK (2 ^ s.level) s.number s.root).ticks ≤ 2 ^ s.level) :
    a ∈ outs (st K hK s).val := by
  have hw : (Cost.within (2 ^ s.level) (rd (P := P) K hK (2 ^ s.level) s.number s.root)).val =
      some (some a, k') := by
    unfold Cost.within
    simp only [ht, ↓reduceIte, hv]
  rw [st_eq, Cost.bind_val, hw, fin_some]
  exact List.mem_cons_self

/-! ## The run -/

/-- From a reading under the budget `2 ^ L`, the run reaches the first
reading under twice the budget, having spent at most the budget and three
ticks at each step. -/
theorem level_up (root : Rel) (L : Nat) : ∀ (e k : Nat), k + e = L →
    after (st (P := P) K hK) ⟨root, L, k⟩ (e + 1) = some ⟨root, L + 1, 0⟩ ∧
      cost (st (P := P) K hK) ⟨root, L, k⟩ (e + 1) ≤ (e + 1) * (2 ^ L + 3)
  | 0, k, h => by
    have hn : next (st (P := P) K hK ⟨root, L, k⟩).val = some ⟨root, L + 1, 0⟩ := by
      rw [st_next]
      simp [State.next, show ¬ k < L by omega]
    have hp : (st (P := P) K hK ⟨root, L, k⟩).ticks +
        shown (st (P := P) K hK ⟨root, L, k⟩).val ≤ 2 ^ L + 3 := st_price (P := P) K hK ⟨root, L, k⟩
    refine ⟨by rw [after_succ_some _ hn]; rfl, ?_⟩
    rw [cost_succ_some _ hn]
    simp only [cost]
    omega
  | e + 1, k, h => by
    have hn : next (st (P := P) K hK ⟨root, L, k⟩).val = some ⟨root, L, k + 1⟩ := by
      rw [st_next]
      simp [State.next, show k < L by omega]
    have hp : (st (P := P) K hK ⟨root, L, k⟩).ticks +
        shown (st (P := P) K hK ⟨root, L, k⟩).val ≤ 2 ^ L + 3 := st_price (P := P) K hK ⟨root, L, k⟩
    obtain ⟨h1, h2⟩ := level_up root L e (k + 1) (by omega)
    refine ⟨by rw [after_succ_some _ hn]; exact h1, ?_⟩
    rw [cost_succ_some _ hn]
    have e3 : (e + 1 + 1) * (2 ^ L + 3) = (e + 1) * (2 ^ L + 3) + (2 ^ L + 3) := by ring
    omega

/-- The first reading under the budget `2 ^ L` is reached within `L * L`
steps, at `2 ^ L` and three ticks or less a step. -/
theorem reach (root : Rel) : ∀ L : Nat, ∃ n, n ≤ L * L ∧
    after (st (P := P) K hK) ⟨root, 0, 0⟩ n = some ⟨root, L, 0⟩ ∧
      cost (st (P := P) K hK) ⟨root, 0, 0⟩ n ≤ L * L * (2 ^ L + 3)
  | 0 => ⟨0, Nat.le_refl _, rfl, by simp [cost]⟩
  | L + 1 => by
    obtain ⟨n, hn, ha, hc⟩ := reach root L
    obtain ⟨h1, h2⟩ := level_up (P := P) K hK root L L 0 (by omega)
    refine ⟨n + (L + 1), by nlinarith, by rw [after_add _ n _ _ ha]; exact h1, ?_⟩
    rw [cost_add _ n _ _ ha]
    have hp : 2 ^ L + 3 ≤ 2 ^ (L + 1) + 3 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) (Nat.le_succ L)
      omega
    calc cost (st (P := P) K hK) ⟨root, 0, 0⟩ n + cost (st (P := P) K hK) ⟨root, L, 0⟩ (L + 1)
        ≤ L * L * (2 ^ L + 3) + (L + 1) * (2 ^ L + 3) := Nat.add_le_add hc h2
      _ = (L * L + (L + 1)) * (2 ^ L + 3) := by ring
      _ ≤ ((L + 1) * (L + 1)) * (2 ^ (L + 1) + 3) :=
        Nat.mul_le_mul (by nlinarith) hp

/-- **The first reading is emitted.** If the reading of the root by the
number 0 to the depth `2 ^ L` makes an answer and costs at most `2 ^ L`
ticks, the run from the first state has emitted that answer within
`L * L + 1` steps and `(L * L + 1) * (2 ^ L + 3)` ticks. -/
theorem first_reading {root : Rel} {L : Nat} {g : Goal R} {r : R} {k' c : Nat}
    (h : Reads P K hK (2 ^ L) 0 root g r k' c) (hc : c ≤ 2 ^ L) :
    ∃ n, ∃ a : Ans D P, n ≤ L * L + 1 ∧ a ∈ emits (st (P := P) K hK) ⟨root, 0, 0⟩ n ∧
      a.goal = g ∧ a.span = r ∧
      cost (st (P := P) K hK) ⟨root, 0, 0⟩ n ≤ (L * L + 1) * (2 ^ L + 3) := by
  obtain ⟨a, hv, hg, hr, ht⟩ := h
  obtain ⟨n, hn, ha, hcn⟩ := reach (P := P) K hK root L
  have hn1 := st_next (P := P) K hK ⟨root, L, 0⟩
  have hp : (st (P := P) K hK ⟨root, L, 0⟩).ticks +
      shown (st (P := P) K hK ⟨root, L, 0⟩).val ≤ 2 ^ L + 3 := st_price (P := P) K hK ⟨root, L, 0⟩
  have he : a ∈ outs (st (P := P) K hK ⟨root, L, 0⟩).val :=
    st_emit K hK (s := ⟨root, L, 0⟩) hv (by rw [ht]; exact hc)
  refine ⟨n + 1, a, by omega, ?_, hg, hr, ?_⟩
  · rw [emits_add _ n _ _ ha, emits_succ_some _ hn1]
    exact List.mem_append_right _ (List.mem_append_left _ he)
  · rw [cost_add _ n _ _ ha, cost_succ_some _ hn1]
    have e3 : (L * L + 1) * (2 ^ L + 3) = L * L * (2 ^ L + 3) + (2 ^ L + 3) := by ring
    simp only [cost] at hp ⊢
    omega

end Dive

end RwLog
