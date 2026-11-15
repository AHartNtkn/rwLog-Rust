/-
# A walk of a chain whose first members double

A member of a chain *doubles* (`Doubles`) when two of its closed products
follow any relation that relates a pair, with different results. A prefix of
`k` such members has at least `2 ^ k` products after any answer
(`seqV_doubling`, `seqV_doubling_top`): the count is read off the exact
description of what a walk holds (`step_ex`, `Unfolding/WalkExact.lean`).

A walk goes through the rest of the chain once for each of them
(`seqW_prefix_ticks`). So the unfolding race answered by a walk costs at
least `2 ^ k` on a goal whose unfolding is final and whose chain starts, in
the direction of the walk, with `k` members that double
(`walkRace_prefix_ticks`).
-/
import RwLog.Rungs.Framework.Unfolding.WalkExact
import RwLog.Rungs.Framework.Unfolding.WalkTicks

namespace RwLog

open Goals

namespace Unfold

open Answer

section lists

variable {β γ : Type}

theorem length_le_flatMap (g : β → List γ) {a : β} : ∀ l : List β, a ∈ l →
    (g a).length ≤ (l.flatMap g).length
  | x :: l, h => by
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 h with e | h'
    · rw [e]; omega
    · have := length_le_flatMap g l h'
      omega

/-- Two different members of a list each contribute to what the list maps
to. -/
theorem length_flatMap_two (g : β → List γ) {a b : β} (hab : a ≠ b) : ∀ l : List β, a ∈ l →
    b ∈ l → (g a).length + (g b).length ≤ (l.flatMap g).length
  | x :: l, ha, hb => by
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 ha with ea | ha'
    · have hb' : b ∈ l := (List.mem_cons.1 hb).resolve_left (fun e => hab (ea.trans e.symm))
      have := length_le_flatMap g l hb'
      rw [ea]; omega
    · rcases List.mem_cons.1 hb with eb | hb'
      · have := length_le_flatMap g l ha'
        rw [eb]; omega
      · have := length_flatMap_two g hab l ha' hb'
        omega

theorem sum_map_const (L : Nat) (l : List β) : (l.map fun _ => L).sum = L * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_succ]
    omega

end lists

/-- A member whose closed products double what was walked: two of them follow
any relation that relates a pair, with different results. -/
def Doubles (P : Program) (M : Interp) (rev : Bool) (d : Nat) (x : Rel) : Prop :=
  ∃ Y₀ Y₁ : PRel, SP.closed Y₀ ∈ SED P M rev d Set.univ x Set.univ ∧
    SP.closed Y₁ ∈ SED P M rev d Set.univ x Set.univ ∧
    ∀ X : PRel, X.Nonempty → (compP rev X Y₀).Nonempty ∧ (compP rev X Y₁).Nonempty ∧
      compP rev X Y₀ ≠ compP rev X Y₁

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

local notation "𝕄" => P.sorts.interp

omit [DecidableEq R] in
theorem semI_closed {rev : Bool} {it : It D P} {X : PRel} (h : semI 𝕄 rev it = .closed X) :
    ∃ a, it = .closed a ∧ den 𝕄 a.span = X := by
  cases it with
  | closed a => exact ⟨a, rfl, by simpa [semI] using h⟩
  | opn t => cases t <;> cases h

include hL in
/-- After an answer, a prefix of `k` members that double has `2 ^ k`
products. -/
theorem seqV_doubling (hP : ProgFO P) (rev : Bool) (d : Nat) : ∀ (ys : List Rel),
    (∀ y ∈ ys, Normal y ∧ y.FO ∧ Doubles P 𝕄 rev d y) → ∀ a : Ans D P,
    ItNone rev (.closed a : It D P) →
    2 ^ ys.length ≤ (seqV (P := P) K hK rev (walkV K hK rev d) none (some (.closed a))
      (nearAfterV D rev (.closed a)) ys).length
  | [], _, a, _ => by simp [seqV]
  | y :: ys, H, a, hit => by
    obtain ⟨hn, hfo, Y₀, Y₁, h₀, h₁, hX⟩ := H y (List.mem_cons_self ..)
    have ih := seqV_doubling hP rev d ys (fun z hz => H z (List.mem_cons_of_mem _ hz))
    have HWy : MemEx (P := P) rev d (walkV K hK rev d) [y] := fun x hx c fr hc hf => by
      obtain rfl := List.mem_singleton.1 hx
      exact ⟨walk_ex hL K hK hP rev d c x fr hc hf hn hfo,
        (walk_ok hL K hK hP rev d c x fr hc hf hn hfo).goal⟩
    have hgoal := (HWy y (List.mem_singleton.2 rfl) (nearAfterV D rev (.closed a)) none
      (nearAfterV_isBound hL rev _) (isBound_none D)).2
    have hstep := step_ex hL K hK rev d HWy hit (isBound_none D)
    obtain ⟨hne₀, hne₁, hdiff⟩ := hX (den 𝕄 a.span) (hL.live _)
    obtain ⟨i₀, hi₀, j₀, he₀, hs₀⟩ := (hstep (.closed (compP rev (den 𝕄 a.span) Y₀))).2
      ⟨.closed Y₀, h₀, SeqI.cc hne₀⟩
    obtain ⟨i₁, hi₁, j₁, he₁, hs₁⟩ := (hstep (.closed (compP rev (den 𝕄 a.span) Y₁))).2
      ⟨.closed Y₁, h₁, SeqI.cc hne₁⟩
    have hne : i₀ ≠ i₁ := by
      rintro rfl
      rw [he₀] at he₁
      cases he₁
      rw [hs₀] at hs₁
      exact hdiff (by simpa using hs₁)
    obtain ⟨a₀, rfl, -⟩ := semI_closed hs₀
    obtain ⟨a₁, rfl, -⟩ := semI_closed hs₁
    have hn₀ := extend_none K hK rev hit (fun b hb => hgoal b (hb ▸ hi₀)) he₀
    have hn₁ := extend_none K hK rev hit (fun b hb => hgoal b (hb ▸ hi₁)) he₁
    have l₀ := ih a₀ hn₀
    have l₁ := ih a₁ hn₁
    simp only [seqV, ite_self, List.length_cons, Nat.pow_succ]
    refine Nat.le_trans ?_ (length_flatMap_two _ hne _ hi₀ hi₁)
    simp only [he₀, he₁]
    omega

include hL in
/-- From a context that restricts nothing, a prefix of `k + 1` members that
double has `2 ^ (k + 1)` products. -/
theorem seqV_doubling_top (hP : ProgFO P) (rev : Bool) (d : Nat) (c : Near R)
    (hc : c.bound = none) (y : Rel) (ys : List Rel)
    (H : ∀ z ∈ y :: ys, Normal z ∧ z.FO ∧ Doubles P 𝕄 rev d z) :
    2 ^ (ys.length + 1) ≤
      (seqV (P := P) K hK rev (walkV K hK rev d) none none c (y :: ys)).length := by
  obtain ⟨hn, hfo, Y₀, Y₁, h₀, h₁, hX⟩ := H y (List.mem_cons_self ..)
  have tail := seqV_doubling hL K hK hP rev d ys (fun z hz => H z (List.mem_cons_of_mem _ hz))
  have hcb : IsBound D c.bound := by rw [hc]; exact isBound_none D
  have hsem := walk_ex hL K hK hP rev d c y none hcb (isBound_none D) hn hfo
  have hgoal := (walk_ok hL K hK hP rev d c y none hcb (isBound_none D) hn hfo).goal
  rw [WT, ws_none hL hc (isBound_none D)] at hsem
  have hY : Y₀ ≠ Y₁ := by
    rintro rfl
    exact (hX Set.univ ⟨(.sym "", .sym ""), trivial⟩).2.2 rfl
  have m₀ : farD rev (.closed Y₀) ∈ Sem 𝕄 rev (walkV (P := P) K hK rev d c y none) := by
    rw [hsem]; exact ⟨_, h₀, rfl⟩
  have m₁ : farD rev (.closed Y₁) ∈ Sem 𝕄 rev (walkV (P := P) K hK rev d c y none) := by
    rw [hsem]; exact ⟨_, h₁, rfl⟩
  obtain ⟨i₀, hi₀, hs₀⟩ := m₀
  obtain ⟨i₁, hi₁, hs₁⟩ := m₁
  obtain ⟨a₀, rfl, e₀⟩ := semI_closed hs₀
  obtain ⟨a₁, rfl, e₁⟩ := semI_closed hs₁
  have hne : (Item.closed a₀ : It D P) ≠ .closed a₁ := by
    intro h
    cases h
    exact hY (e₀.symm.trans e₁)
  have l₀ := tail a₀ ⟨_, _, hgoal a₀ hi₀⟩
  have l₁ := tail a₁ ⟨_, _, hgoal a₁ hi₁⟩
  simp only [seqV, ite_self, extendV, Nat.pow_succ]
  refine Nat.le_trans ?_ (length_flatMap_two _ hne _ hi₀ hi₁)
  omega

/-- Reading a node costs a tick. -/
theorem walk_succ_ticks {α : Type} (rev : Bool) (d : Nat) (c : Near R) (n : Rel) (far : Option R)
    (k : It D P → α → Cost (Bool × α)) (acc : α) :
    1 ≤ (walk (K := DerivationKernel.over D K hK P) rev (d + 1) c n far k acc).ticks := by
  at_cost K hK
  simp only [walk, Cost.bind_ticks]
  exact Nat.le_add_right _ _

/-- A walk of a chain costs at least the walk of its members. -/
theorem walk_chain_ticks {α : Type} (rev : Bool) (d : Nat) (c : Near R) (n : Rel) (far : Option R)
    (k : It D P → α → Cost (Bool × α)) (acc : α) {xs : List Rel}
    (hv : n.view.forget = .chain xs) :
    (seqW (K := DerivationKernel.over D K hK P) rev
        (walk (K := DerivationKernel.over D K hK P) rev d) far none c
        (if rev then xs.reverse else xs) k acc).ticks ≤
      (walk (K := DerivationKernel.over D K hK P) rev (d + 1) c n far k acc).ticks := by
  at_cost K hK
  simp only [walk, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op_val, hv]
  exact le_add_two _ _ _

include hL in
/-- A walk of a chain that starts, in its direction, with `k` members that
double costs at least `2 ^ k`, when its continuation does not say stop, there
is no boundary on the near side and the chain goes on after them. -/
theorem walk_prefix_ticks {α : Type} (hP : ProgFO P) (rev : Bool) (d : Nat) (c : Near R)
    (hc : c.bound = none) (n : Rel) (far : Option R) {xs Bs : List Rel} {y : Rel}
    {ys : List Rel} (hv : n.view.forget = .chain xs)
    (hxs : (if rev then xs.reverse else xs) = Bs ++ y :: ys) (hB : Bs ≠ [])
    (H : ∀ b ∈ Bs, Normal b ∧ b.FO ∧ Doubles P 𝕄 rev (d + 1) b)
    (k : It D P → α → Cost (Bool × α)) (acc : α)
    (hk : Quiet k (walkV K hK rev (d + 2) c n far)) :
    2 ^ Bs.length ≤ (walk (K := DerivationKernel.over D K hK P) rev (d + 2) c n far k acc).ticks := by
  obtain ⟨b, Bs', rfl⟩ := List.exists_cons_of_ne_nil hB
  have e : walkV (P := P) K hK rev (d + 2) c n far =
      seqV K hK rev (walkV K hK rev (d + 1)) far none c ((b :: Bs') ++ y :: ys) := by
    simp only [walkV, hv, hxs]
  rw [e] at hk
  have count := seqV_doubling_top hL K hK hP rev (d + 1) c hc b Bs' H
  have key := seqW_prefix_ticks K hK rev
    (walk (K := DerivationKernel.over D K hK P) rev (d + 1)) (walkV K hK rev (d + 1))
    (walk_val K hK rev (d + 1)) (walk_ticks K hK rev (d + 1)) far
    (y :: ys) (List.cons_ne_nil _ _) k 1
    (fun pre c acc => walk_succ_ticks K hK rev d _ _ _ _ _)
    (b :: Bs') none c acc hk
  rw [sum_map_const, Nat.one_mul] at key
  exact Nat.le_trans (Nat.le_trans count key)
    (hxs ▸ walk_chain_ticks K hK rev (d + 1) c n far k acc hv)

include hL in
/-- **The unfolding race answered by a walk costs at least `2 ^ k`** on a
goal whose unfolding is final and whose chain starts, in the direction of the
walk, with `k` members that double, when the goal has no boundary on that
side and the chain goes on after them. -/
theorem walkRace_prefix_ticks (hP : ProgFO P) (rev : Bool) (d : Nat) (g : GoalOf R Rel)
    (hg : GoalOk D g) {xs Bs : List Rel} {y : Rel} {ys : List Rel}
    (hv : g.node.view.forget = .chain xs)
    (hxs : (if rev then xs.reverse else xs) = Bs ++ y :: ys) (hB : Bs ≠ [])
    (H : ∀ b ∈ Bs, Normal b ∧ b.FO ∧ Doubles P 𝕄 rev (d + 1) b)
    (hnear : (if rev then g.rb else g.lb) = none)
    (hfin : Final P 𝕄 (d + 2) (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb)) :
    2 ^ Bs.length ≤ (walkRace (K := DerivationKernel.over D K hK P) rev (d + 2) g).ticks := by
  have hval := (walkRace_final hL K hK hP rev (d + 2) g hg).2 hfin
  rw [walkRace_val] at hval
  have hno : (walkV (P := P) K hK rev (d + 2) ⟨if rev then g.rb else g.lb, false⟩ g.node
      (if rev then g.lb else g.rb)).any itOpn = false := by
    cases h : (walkV (P := P) K hK rev (d + 2) ⟨if rev then g.rb else g.lb, false⟩ g.node
      (if rev then g.lb else g.rb)).any itOpn with
    | false => rfl
    | true => rw [h] at hval; simp at hval
  have key := fun k hk => walk_prefix_ticks (α := List (Ans D P)) hL K hK hP rev d
    ⟨if rev then g.rb else g.lb, false⟩ hnear g.node (if rev then g.lb else g.rb) hv hxs hB H k
    [] hk
  at_cost K hK
  simp only [walkRace, Cost.bind_ticks]
  refine Nat.le_trans (key _ (fun it hit acc => ?_)) (Nat.le_add_right _ _)
  cases it with
  | closed a => rfl
  | opn t =>
    have := List.any_eq_false.1 hno _ hit
    simp [itOpn] at this

end Unfold

end RwLog
