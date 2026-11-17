/-
# The machine of the diving engine on the fan

The machine of the diving engine (`dive`) starts from the root node with the
budget of one tick and the number 0, at the charge of bringing the input to
its normal form (`dive_start`, `dive_init_ticks`). On a member of the fan it
has emitted an answer that relates the target within a number of steps and
of ticks that do not depend on the rank (`dive_fan`).
-/
import RwLog.Rungs.Dive.Fan
import RwLog.Rungs.Dive.Run
import RwLog.Rungs.Framework.BesideLaws

open RwLog.Symmetric RwLog.Symmetric.Fan

namespace RwLog

namespace Dive

open Answer Beside

variable {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
  (cells : ∀ S, R S → Nat)

/-- The machine starts from the root node, with the budget of one tick and
the number 0. -/
theorem dive_start (P : Program) (q : Rel) :
    (dive.costedAt dom K hK cells).start P q = ⟨P, q.norm, ⟨q.norm, 0, 0⟩⟩ := by
  show (Charged.load P q >>= fun root =>
    (@Engine.init dive (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
      (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P) root) >>= fun st =>
      pure (⟨P, root, st⟩ : dive.StateAt dom)).val = _
  simp only [Cost.bind_val, Cost.pure_val]
  show (⟨P, q.norm, (@pure Cost (K P.sorts).toMonad.toApplicative.toPure _
    (⟨q.norm, 0, 0⟩ : Dive.State Rel)).val⟩ : dive.StateAt dom) = _
  rw [(hK P.sorts).pure_eq]
  rfl

/-- Building the first state costs what bringing the input to its normal
form costs. -/
theorem dive_init_ticks (P : Program) (q : Rel) :
    ((dive.costedAt dom K hK cells).init P q).ticks = (P.size + q.size) ^ 2 := by
  show (Charged.load P q >>= fun root =>
    (@Engine.init dive (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
      (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P) root) >>= fun st =>
      pure (⟨P, root, st⟩ : dive.StateAt dom)).ticks = _
  simp only [Cost.bind_ticks, Cost.pure_ticks]
  show (Charged.load P q).ticks + ((@pure Cost (K P.sorts).toMonad.toApplicative.toPure _
    (⟨(Charged.load P q).val, 0, 0⟩ : Dive.State Rel)).ticks + 0) = _
  rw [(hK P.sorts).pure_eq]
  rfl

/-- The budget the first reading of a member fits: the least power of two
above `w + 5`, as its exponent. -/
def fanLevel (w : Nat) : Nat := (w + 5).log2 + 1

theorem fanLevel_lt (w : Nat) : w + 5 < 2 ^ fanLevel w :=
  Nat.lt_log2_self

variable {m : Nat} {Po : Program} {t : Bool}

/-- **The machine of the diving engine on a member of the fan** has emitted
an answer that relates the target, the other way round when the chain is
read backwards, within `L * L + 1` steps and `(L * L + 1) * (2 ^ L + 3)`
ticks, where `2 ^ L` is the budget the first reading fits, whatever the
rank. -/
theorem dive_fan (hP : IsFan m Po t) (hL : (dom Po.sorts).Lawful Po.sorts.interp) (c : Bool) :
    ∃ n g, way (c ^^ t) ∈ den Po.sorts.interp g ∧
      (⟨Po.sorts, g⟩ : (S : Sorts) × R S) ∈ (dive.costedAt dom K hK cells).runtime.emitted
        ((dive.costedAt dom K hK cells).start Po (hl c)) n ∧
      n ≤ fanLevel (fanTicks (dom Po.sorts) (K Po.sorts)) *
        fanLevel (fanTicks (dom Po.sorts) (K Po.sorts)) + 1 ∧
      (dive.costedAt dom K hK cells).spent ((dive.costedAt dom K hK cells).start Po (hl c)) n ≤
        (fanLevel (fanTicks (dom Po.sorts) (K Po.sorts)) *
          fanLevel (fanTicks (dom Po.sorts) (K Po.sorts)) + 1) *
          (2 ^ fanLevel (fanTicks (dom Po.sorts) (K Po.sorts)) + 3) := by
  generalize hw : fanTicks (dom Po.sorts) (K Po.sorts) = w
  have hlt := fanLevel_lt w
  generalize fanLevel w = L at hlt ⊢
  obtain ⟨g, cost, hway, hr, hcost⟩ :=
    reads_root (K Po.sorts) (hK Po.sorts) hP hL c (2 ^ L - 5)
  rw [show 2 ^ L - 5 + 5 = 2 ^ L by omega] at hr
  obtain ⟨n, a, hn, ha, hg, hsp, hc⟩ :=
    first_reading (K Po.sorts) (hK Po.sorts) hr (by omega)
  have hnorm : (hl c).norm = hl c := by cases c <;> rfl
  refine ⟨n, g, hway, ?_, hn, ?_⟩
  · rw [dive_start, Engine.machine_emitted, hnorm]
    refine List.mem_map.2 ⟨g, List.mem_filterMap.2 ⟨a, ha, ?_⟩, rfl⟩
    simp [Ans.rootSpan, hg, hsp]
  · rw [dive_start, Engine.machine_spent, hnorm]
    exact hc

end Dive

end RwLog
