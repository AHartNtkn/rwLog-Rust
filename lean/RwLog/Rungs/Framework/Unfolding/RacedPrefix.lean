/-
# The race of R004 on a chain that doubles from both ends

The race of R004 and R005 runs a walk from the left, the shared evaluation
and a walk from the right side by side, and costs at least what the cheapest
of the three costs (`raced_ticks_ge`). On a goal whose unfolding is final and
whose chain starts with `k` members that split and ends with `k` members
that double from the right, each of the three costs `2 ^ k`
(`walkRace_prefix_ticks`, `sharedRace_prefix_ticks`), so the race does
(`raced_prefix_ticks`).

For the members of such a chain: a member that splits doubles from the left
(`Splits.doubles`); a union has the relation of each of its spans as a closed
product (`sed_union_span`); and a chain of spans and of unions of spans has
no open product from the third depth on (`final_flat`).
-/
import RwLog.Rungs.Framework.Unfolding.WalkPrefix
import RwLog.Rungs.Framework.Unfolding.SharedPrefix
import RwLog.Rungs.Framework.Unfolding.RacesExact
import RwLog.Rungs.Framework.RaceWinner

namespace RwLog

open Goals

namespace Unfold

open Answer

/-! ## The members -/

section members

variable {P : Program} {M : Interp}

/-- A member that splits doubles what a walk from the left holds. -/
theorem Splits.doubles {d : Nat} {x : Rel} {Y : Bool → PRel} (h : Splits P M d x Y) :
    Doubles P M false d x := by
  refine ⟨Y false, Y true, h.mem false, h.mem true, fun X hX => ?_⟩
  obtain ⟨⟨s, t⟩, hst⟩ := hX
  have live : ∀ f, (compP false X (Y f)).Nonempty := fun f => by
    obtain ⟨z, m, hm, hmz⟩ := h.live f {t} ⟨t, rfl⟩
    obtain rfl : m = t := hm
    exact ⟨(s, z), m, hst, hmz⟩
  refine ⟨live false, live true, fun e => ?_⟩
  have e' : (X.comp (Y false)).rends = (X.comp (Y true)).rends := congrArg PRel.rends e
  rw [rends_comp, rends_comp] at e'
  exact Bool.noConfusion (h.inj false true X.rends X.rends ⟨t, s, hst⟩ ⟨t, s, hst⟩ e').1

/-- The relation of a span of a union is a closed product of the union. -/
theorem sed_union_span {rev : Bool} {d : Nat} {b : Rel} {L : List Rel}
    (hv : b.view.forget = .union L) {s : Span} (hs : .span s ∈ L)
    (hne : (s.den.at M).Nonempty) :
    SP.closed (s.den.at M) ∈ SED P M rev (d + 2) Set.univ b Set.univ := by
  rw [sed_union hv]
  refine ⟨_, hs, ?_⟩
  rw [sed_span]
  have : restrO rev Set.univ (s.den.at M) Set.univ = s.den.at M := by
    cases rev <;>
    · ext ⟨u, v⟩
      exact ⟨fun h => h.1, fun h => ⟨h, trivial, trivial⟩⟩
  rw [this]
  exact ⟨rfl, hne⟩

theorem seqSets_closed {S T : Set SP} (hS : ¬ HasOpn S) (hT : ¬ HasOpn T) :
    ¬ HasOpn (seqSets S T) := by
  rintro ⟨A, B, p, hp, q, hq, h⟩
  cases h with
  | co _ => exact hT ⟨_, _, hq⟩
  | oc _ => exact hS ⟨_, _, hp⟩
  | oo _ => exact hS ⟨_, _, hp⟩

theorem chainS_closed : ∀ Ss : List (Set SP), (∀ S ∈ Ss, ¬ HasOpn S) → ¬ HasOpn (chainS Ss)
  | [], _ => by rintro ⟨A, B, h⟩; cases h
  | S :: rest, H => by
    have gen : ∀ (rest : List (Set SP)) (S : Set SP), ¬ HasOpn S → (∀ T ∈ rest, ¬ HasOpn T) →
        ¬ HasOpn (rest.foldl seqSets S) := by
      intro rest
      induction rest with
      | nil => exact fun S hS _ => hS
      | cons T rest ih =>
        exact fun S hS hT => ih _ (seqSets_closed hS (hT T List.mem_cons_self))
          (fun U hU => hT U (List.mem_cons_of_mem _ hU))
    exact gen rest S (H S List.mem_cons_self) (fun T hT => H T (List.mem_cons_of_mem _ hT))

/-- A span, or a union of spans. -/
def Flat (x : Rel) : Prop :=
  (∃ s, x = .span s) ∨ ∃ L, x.view.forget = .union L ∧ ∀ z ∈ L, ∃ s, z = .span s

/-- A chain of spans and of unions of spans has no open product from the
third depth on. -/
theorem final_flat {d : Nat} {A B : Set GTerm} {e : Rel} {xs : List Rel}
    (hv : e.view.forget = .chain xs) (H : ∀ x ∈ xs, Flat x) : Final P M (d + 3) A e B := by
  unfold Final
  rw [se_chain hv]
  refine chainS_closed _ fun S hS => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS
  have hx : p.1 ∈ xs := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp)
  rcases H p.1 hx with ⟨s, hs⟩ | ⟨L, hL, hall⟩
  · rw [hs, se_span]
    rintro ⟨A', B', h, -⟩
    cases h
  · rw [se_union hL]
    rintro ⟨A', B', z, hz, h⟩
    obtain ⟨s, rfl⟩ := hall z hz
    rw [se_span] at h
    cases h.1

end members

/-! ## The race -/

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

local notation "𝕄" => P.sorts.interp

/-- The race costs at least what the cheapest of its three sides costs. -/
theorem raced_ticks_ge (d : Nat) (g : GoalOf R Rel) :
    min (min (walkRace (K := DerivationKernel.over D K hK P) false d g).ticks
          (sharedRace (K := DerivationKernel.over D K hK P) d g).ticks)
        (walkRace (K := DerivationKernel.over D K hK P) true d g).ticks ≤
      (raced (K := DerivationKernel.over D K hK P) d g).ticks := by
  have e₁ : walkShared (K := DerivationKernel.over D K hK P) d g =
      Cost.race (walkRace (K := DerivationKernel.over D K hK P) false d g)
        (sharedRace (K := DerivationKernel.over D K hK P) d g) := hK.race _ _ _
  have e₂ : raced (K := DerivationKernel.over D K hK P) d g =
      Cost.race (walkShared (K := DerivationKernel.over D K hK P) d g)
        (walkRace (K := DerivationKernel.over D K hK P) true d g) := hK.race _ _ _
  rw [e₂, Cost.race_ticks_eq, e₁, Cost.race_ticks_eq]
  have h₁ := Cost.winner_le_raceCost
    (walkRace (K := DerivationKernel.over D K hK P) false d g).ticks
    (sharedRace (K := DerivationKernel.over D K hK P) d g).ticks
  have h₂ := Cost.winner_le_raceCost
    (Cost.raceCost (walkRace (K := DerivationKernel.over D K hK P) false d g).ticks
      (sharedRace (K := DerivationKernel.over D K hK P) d g).ticks)
    (walkRace (K := DerivationKernel.over D K hK P) true d g).ticks
  split at h₁ <;> split at h₂ <;> omega

include hL in
/-- **The race of R004 costs at least `2 ^ k`** on a goal with no boundary
whose unfolding is final and whose chain starts with `k` members that split
and ends with `k` members that double from the right. -/
theorem raced_prefix_ticks (hP : ProgFO P) (e : Nat) (g : GoalOf R Rel) (hg : GoalOk D g)
    {Bs Us : List Rel} {y : Rel} (hBs : Bs ≠ []) (hUs : Us ≠ [])
    (hv : g.node.view.forget = .chain (Bs ++ y :: Us)) (W : Rel → Bool → PRel)
    (HB : ∀ b ∈ Bs, Splits P 𝕄 (e + 2) b (W b)) (HU : ∀ u ∈ Us, Doubles P 𝕄 true (e + 2) u)
    (hl : g.lb = none) (hr : g.rb = none)
    (hfin : Final P 𝕄 (e + 3) (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb)) :
    min (2 ^ Bs.length) (2 ^ Us.length) ≤
      (raced (K := DerivationKernel.over D K hK P) (e + 3) g).ticks := by
  have hvc := forget_chain hv
  obtain ⟨-, hmem, -⟩ := hg.normal.view_chain hvc
  have hfo : ∀ x ∈ Bs ++ y :: Us, x.FO := fun x hx =>
    hg.fo.view_members (by rw [hvc]; exact hx)
  have w₁ : 2 ^ Bs.length ≤
      (walkRace (K := DerivationKernel.over D K hK P) false (e + 3) g).ticks :=
    walkRace_prefix_ticks hL K hK hP false (e + 1) g hg (Bs := Bs) (y := y) (ys := Us) hv
      (by simp) hBs
      (fun b hb => ⟨(hmem b (List.mem_append_left _ hb)).1, hfo b (List.mem_append_left _ hb),
        (HB b hb).doubles⟩) (by simpa using hl) hfin
  have w₂ : 2 ^ Us.reverse.length ≤
      (walkRace (K := DerivationKernel.over D K hK P) true (e + 3) g).ticks :=
    walkRace_prefix_ticks hL K hK hP true (e + 1) g hg (Bs := Us.reverse) (y := y)
      (ys := Bs.reverse) hv
      (show (if true = true then (Bs ++ y :: Us).reverse else Bs ++ y :: Us) =
        Us.reverse ++ y :: Bs.reverse by simp)
      (by simpa using hUs)
      (fun u hu => by
        have hu' : u ∈ Us := List.mem_reverse.1 hu
        have hx : u ∈ Bs ++ y :: Us := List.mem_append_right _ (List.mem_cons_of_mem _ hu')
        exact ⟨(hmem u hx).1, hfo u hx, HU u hu'⟩) (by simpa using hr) hfin
  have s : 2 ^ Bs.length ≤
      (sharedRace (K := DerivationKernel.over D K hK P) (e + 3) g).ticks :=
    sharedRace_prefix_ticks hL K hK hP (e + 1) g hg hUs hBs hv W HB hl
  have := raced_ticks_ge (P := P) K hK (e + 3) g
  rw [List.length_reverse] at w₂
  omega

end Unfold

end RwLog
