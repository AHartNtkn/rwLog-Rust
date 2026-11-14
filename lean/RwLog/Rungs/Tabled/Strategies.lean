/-
# The strategies of a goal

What a goal of the tabled machine computes in a round, strategy by strategy:

* every candidate is an answer of the goal (`cand_goal`);
* every goal a strategy depends on is a goal the machine may hold
  (`strat_ok`);
* if the tables of the goals of one strategy cover every derivation of their
  nodes that is smaller (at a smaller depth of unfolding, or at the same
  depth on a smaller node), the candidates cover every derivation of the
  node of the goal (`strat_cov`).

The third is what makes a table complete when its strategy's dependencies are
complete, and it is the step of the induction in
`Rungs/Tabled/Complete.lean`.
-/
import RwLog.Rungs.Tabled.Covers

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## The two sides of a split -/

/-- What a split of a chain is. -/
structure SeqSplit (D : Domain R) (P : Program) (g : GoalOf R Rel)
    (w : Kind × GoalOf R Rel × GoalOf R Rel) : Prop where
  kind : w.1 = .seq
  llb : w.2.1.lb = g.lb
  lrb : w.2.1.rb = none
  rlb : w.2.2.lb = none
  rrb : w.2.2.rb = g.rb
  lok : GoalOk D w.2.1
  rok : GoalOk D w.2.2
  lsize : w.2.1.node.size < g.node.size
  rsize : w.2.2.node.size < g.node.size
  node : mkSeq (seqParts w.2.1.node ++ seqParts w.2.2.node) = g.node
  gdn : ∀ k, GDn P k g.node = Set.image2 GRel.comp (GDn P k w.2.1.node) (GDn P k w.2.2.node)

/-- What a split of a meet is. -/
structure AndSplit (D : Domain R) (P : Program) (g : GoalOf R Rel)
    (w : Kind × GoalOf R Rel × GoalOf R Rel) : Prop where
  kind : w.1 = .and
  llb : w.2.1.lb = g.lb
  lrb : w.2.1.rb = g.rb
  rlb : w.2.2.lb = g.lb
  rrb : w.2.2.rb = g.rb
  lok : GoalOk D w.2.1
  rok : GoalOk D w.2.2
  lsize : w.2.1.node.size < g.node.size
  rsize : w.2.2.node.size < g.node.size
  node : mkAnd (sortedParts (andParts w.2.1.node ++ andParts w.2.2.node)) = g.node
  node' : mkAnd (sortedParts (andParts w.2.2.node ++ andParts w.2.1.node)) = g.node
  gdn : ∀ k, GDn P k g.node = Set.image2 GRel.meet (GDn P k w.2.1.node) (GDn P k w.2.2.node)

variable (K : Kernel R Cost) (hK : K.Refines D)

omit [Answer R] [DecidableEq R] in
theorem mem_seqSplits {n i : Nat} (hn : 2 ≤ n) (hi : i ∈ seqSplits n) : 0 < i ∧ i < n := by
  unfold seqSplits at hi
  split at hi
  · simp only [List.mem_singleton] at hi; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega

omit [Answer R] [DecidableEq R] in
theorem mem_andSplits {n i : Nat} (hn : 2 ≤ n) (hi : i ∈ andSplits n) : i < n := by
  unfold andSplits at hi
  split at hi
  · simp only [List.mem_singleton] at hi; omega
  · exact List.mem_range.1 hi

theorem seqSplit_of_mem {g : GoalOf R Rel} (hg : GoalOk D g) {xs : List Rel}
    (hv : g.node.view.forget = .chain xs) {w : Kind × GoalOf R Rel × GoalOf R Rel}
    (hw : w ∈ (splitsOf (K := DerivationKernel.over D K hK P) g (.chain xs)).val) :
    SeqSplit D P g w := by
  obtain ⟨i, hi, l, r, hl, hr, rfl⟩ := (mem_splitsOf_chain K hK g xs w).1 hw
  have hv' := forget_chain hv
  obtain ⟨h2, -, -⟩ := hg.normal.view_chain hv'
  obtain ⟨h0, hlt⟩ := mem_seqSplits h2 hi
  obtain ⟨hlen, l', r', hl', hr', hnode, hls, hrs⟩ := hg.normal.chain_split hv' h0 hlt
  obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hl)
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
  exact
    { kind := rfl, llb := rfl, lrb := rfl, rlb := rfl, rrb := rfl
      lok := ⟨hg.lb, isBound_none D, hg.normal.interval hl, hg.fo.interval hl⟩
      rok := ⟨isBound_none D, hg.rb, hg.normal.interval hr, hg.fo.interval hr⟩
      lsize := hls, rsize := hrs, node := hnode
      gdn := fun k => (gdn_laws P k).chain_split hl (by rw [hlen]; exact hr) }

theorem andSplit_of_mem {g : GoalOf R Rel} (hg : GoalOk D g) {xs : List Rel}
    (hv : g.node.view.forget = .meet xs) {w : Kind × GoalOf R Rel × GoalOf R Rel}
    (hw : w ∈ (splitsOf (K := DerivationKernel.over D K hK P) g (.meet xs)).val) :
    AndSplit D P g w := by
  obtain ⟨i, hi, l, r, hl, hr, rfl⟩ := (mem_splitsOf_meet K hK g xs w).1 hw
  have hv' := forget_meet hv
  obtain ⟨h2, -, -, -⟩ := hg.normal.view_meet hv'
  have hlt := mem_andSplits h2 hi
  obtain ⟨hparts, l', r', hl', hr', hnode, hnode', hls, hrs⟩ := hg.normal.meet_split hv' hlt
  obtain rfl : l = l' := Option.some.inj (hl.symm.trans hl')
  obtain rfl : r = r' := Option.some.inj (hr.symm.trans hr')
  have hmem : l ∈ g.node.view.members := by
    rw [hv']; exact List.mem_of_getElem? hl
  exact
    { kind := rfl, llb := rfl, lrb := rfl, rlb := rfl, rrb := rfl
      lok := ⟨hg.lb, hg.rb, hg.normal.view_members hmem, hg.fo.view_members hmem⟩
      rok := ⟨hg.lb, hg.rb, hg.normal.without hr, hg.fo.without hr⟩
      lsize := hls, rsize := hrs, node := hnode, node' := hnode'
      gdn := fun k => (gdn_laws P k).meet_split (by rw [hparts]; exact hl) hr }

/-- A chain has a split. -/
theorem exists_seqSplit {g : GoalOf R Rel} (hg : GoalOk D g) {xs : List Rel}
    (hv : g.node.view.forget = .chain xs) :
    ∃ w, w ∈ (splitsOf (K := DerivationKernel.over D K hK P) g (.chain xs)).val := by
  have hv' := forget_chain hv
  obtain ⟨h2, -, -⟩ := hg.normal.view_chain hv'
  obtain ⟨-, l, r, hl, hr, -⟩ := hg.normal.chain_split hv' (i := 1) (by omega) (by omega)
  exact ⟨_, (mem_splitsOf_chain K hK g xs _).2
    ⟨1, by unfold seqSplits; split <;> simp, l, r, hl, hr, rfl⟩⟩

/-- A meet has a split. -/
theorem exists_andSplit {g : GoalOf R Rel} (hg : GoalOk D g) {xs : List Rel}
    (hv : g.node.view.forget = .meet xs) :
    ∃ w, w ∈ (splitsOf (K := DerivationKernel.over D K hK P) g (.meet xs)).val := by
  have hv' := forget_meet hv
  obtain ⟨h2, -, -, -⟩ := hg.normal.view_meet hv'
  obtain ⟨-, l, r, hl, hr, -⟩ := hg.normal.meet_split hv' (i := 0) (by omega)
  exact ⟨_, (mem_splitsOf_meet K hK g xs _).2
    ⟨0, by unfold andSplits; split <;> simp; omega, l, r, hl, hr, rfl⟩⟩

/-! ## The candidates of a split are answers of the goal -/

variable (ts : List (TableOf R Rel (Ans D P)))

theorem way_goal_seq (hT : TablesOk D ts) {g : GoalOf R Rel}
    {w : Kind × GoalOf R Rel × GoalOf R Rel} (hw : SeqSplit D P g w) {c : Ans D P}
    (hc : c ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.1) : c.goal = toGoal g := by
  obtain ⟨kd, L, Rr⟩ := w
  obtain ⟨rfl, llb, lrb, rlb, rrb, -, -, -, -, node, -⟩ := hw
  simp only at llb lrb rlb rrb node
  rcases (mem_way K hK ts g _ c).1 hc with ⟨x, hx, y, hy, h⟩ | ⟨-, x, hx, y, hy, h⟩ |
    ⟨-, y, hy, x, hx, h⟩
  · obtain ⟨-, -, hcg⟩ := (Ans.join_val K hK).1 h
    rw [hcg, ansOf_goal hT hx, ansOf_goal hT hy]
    simp only [toGoal, llb, rrb, node]
  · obtain ⟨-, -, hcg⟩ := (Ans.join_val K hK).1 h
    rw [hcg, ansOf_goal hT (List.mem_maximaBy hx), ansOf_goal hT hy]
    simp only [toGoal, pushLG, llb, node]
  · obtain ⟨-, -, hcg⟩ := (Ans.join_val K hK).1 h
    rw [hcg, ansOf_goal hT (List.mem_maximaBy hy), ansOf_goal hT hx]
    simp only [toGoal, pushRG, rrb, node]

theorem way_goal_and (hT : TablesOk D ts) {g : GoalOf R Rel}
    {w : Kind × GoalOf R Rel × GoalOf R Rel} (hw : AndSplit D P g w) {c : Ans D P}
    (hc : c ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.1) : c.goal = toGoal g := by
  obtain ⟨kd, L, Rr⟩ := w
  obtain ⟨rfl, llb, lrb, rlb, rrb, -, -, -, -, node, node', -⟩ := hw
  simp only at llb lrb rlb rrb node node'
  rcases (mem_way K hK ts g _ c).1 hc with ⟨x, hx, y, hy, h⟩ | ⟨-, x, hx, y, hy, h⟩ |
    ⟨-, y, hy, x, hx, h⟩
  · obtain ⟨-, -, hcg⟩ := (Ans.meetA_val K hK).1 h
    rw [hcg, ansOf_goal hT hx, ansOf_goal hT hy]
    simp only [toGoal, llb, lrb, node]
  · obtain ⟨-, -, hcg⟩ := (Ans.meetA_val K hK).1 h
    rw [hcg, ansOf_goal hT (List.mem_maximaBy hx), ansOf_goal hT hy]
    simp only [toGoal, pushLG, llb, lrb, node]
  · obtain ⟨-, -, hcg⟩ := (Ans.meetA_val K hK).1 h
    rw [hcg, ansOf_goal hT (List.mem_maximaBy hy), ansOf_goal hT hx]
    simp only [toGoal, pushRG, rlb, rrb, node']

/-- Every candidate of a goal is an answer of that goal. -/
theorem cand_goal (hT : TablesOk D ts) {g : GoalOf R Rel} (hg : GoalOk D g) {c : Ans D P}
    (hc : c ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1) :
    c.goal = toGoal g := by
  cases hv : g.node.view.forget with
  | span u =>
    rw [produceTables_span K hK ts g hv] at hc
    obtain ⟨s, hs, -, -, -, hcg⟩ := (Ans.leaf_val K hK).1 (Option.mem_toList.1 hc)
    rw [hcg, ← hs]; rfl
  | call n f =>
    obtain ⟨b, hb⟩ := forget_call (P := P) hv
    rw [produceTables_call K hK ts g hv hb] at hc
    obtain ⟨a, ha, hac⟩ := List.mem_filterMap.1 hc
    obtain ⟨-, -, hcg⟩ := Ans.unfold_val.1 hac
    rw [hcg, ansOf_goal hT ha]; rfl
  | union xs =>
    rw [produceTables_union K hK ts g hv] at hc
    obtain ⟨p, hp, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨a, ha, hac⟩ := List.mem_filterMap.1 hc
    obtain ⟨-, -, hcg⟩ := Ans.inj_val.1 hac
    obtain ⟨x, -, hx⟩ := List.mem_map.1 (List.mem_zipIdx hp |>.2.2 ▸ List.getElem_mem _)
    rw [hcg, ansOf_goal hT ha, ← hx]; rfl
  | chain xs =>
    rw [produceTables_chain K hK ts g hv] at hc
    obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact way_goal_seq K hK ts hT (seqSplit_of_mem K hK hg hv hw) hc
  | meet xs =>
    rw [produceTables_meet K hK ts g hv] at hc
    obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact way_goal_and K hK ts hT (andSplit_of_mem K hK hg hv hw) hc

/-! ## The goals of a strategy -/

/-- The spans of the bodies of the program are first-order. -/
def ProgFO (P : Program) : Prop := ∀ s ∈ P.defs.flatMap fun d => d.2.spans, s.firstOrder = true

omit [Answer R] [DecidableEq R] in
theorem bodyOf_normal {e b : Rel} (hb : Charged.bodyOf P e = some b) : Normal b := by
  unfold Charged.bodyOf at hb
  split at hb
  · cases hb; exact normal_norm _
  · cases hb; exact normal_normConv _
  · cases hb

section

variable {M : Interp} (hL : D.Lawful M)
include hL

omit [DecidableEq R] in
theorem isBound_right (a : R) : IsBound D (D.rightBound a) :=
  fun r h => hL.rightBound_isBound a r h

omit [DecidableEq R] in
theorem isBound_left (a : R) : IsBound D (D.leftBound a) := isBound_right hL _

omit [DecidableEq R] in
theorem pushLG_ok {g r : GoalOf R Rel} (hg : GoalOk D g) (hr : GoalOk D r) (k : Kind)
    (x : Ans D P) : GoalOk D (pushLG D g r k x) := by
  cases k
  · exact ⟨isBound_right hL _, hg.rb, hr.normal, hr.fo⟩
  · exact ⟨isBound_left hL _, isBound_right hL _, hr.normal, hr.fo⟩

omit [DecidableEq R] in
theorem pushRG_ok {g l : GoalOf R Rel} (hg : GoalOk D g) (hl : GoalOk D l) (k : Kind)
    (y : Ans D P) : GoalOk D (pushRG D g l k y) := by
  cases k
  · exact ⟨hg.lb, isBound_left hL _, hl.normal, hl.fo⟩
  · exact ⟨isBound_left hL _, isBound_right hL _, hl.normal, hl.fo⟩

end

/-- The strategies of a split. -/
theorem mem_way_strats (g : GoalOf R Rel) (w : Kind × GoalOf R Rel × GoalOf R Rel)
    (strat : List (GoalOf R Rel)) :
    strat ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.2 ↔
      strat = [w.2.1, w.2.2] ∨
      (isDone ts w.2.1 = true ∧
        strat = w.2.1 :: ((ansOf ts w.2.1).maximaBy (covB D P)).map (pushLG D g w.2.2 w.1)) ∨
      (isDone ts w.2.2 = true ∧
        strat = w.2.2 :: ((ansOf ts w.2.2).maximaBy (covB D P)).map (pushRG D g w.2.1 w.1)) := by
  rw [way_strats]
  cases isDone ts w.2.1 <;> cases isDone ts w.2.2 <;> simp

theorem way_ok (hL : D.Lawful P.sorts.interp) {g : GoalOf R Rel}
    {w : Kind × GoalOf R Rel × GoalOf R Rel} (hg : GoalOk D g) (hl : GoalOk D w.2.1)
    (hr : GoalOk D w.2.2) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.2) {d : GoalOf R Rel}
    (hd : d ∈ strat) : GoalOk D d := by
  rcases (mem_way_strats K hK ts g w strat).1 hs with rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> assumption
  · rcases List.mem_cons.1 hd with rfl | hd
    · exact hl
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd
      exact pushLG_ok hL hg hr _ x
  · rcases List.mem_cons.1 hd with rfl | hd
    · exact hr
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hd
      exact pushRG_ok hL hg hl _ y

/-- Every goal a strategy depends on is a goal the machine may hold. -/
theorem strat_ok (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) {g : GoalOf R Rel}
    (hg : GoalOk D g) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.2)
    {d : GoalOf R Rel} (hd : d ∈ strat) : GoalOk D d := by
  cases hv : g.node.view.forget with
  | span u =>
    rw [produceTables_span K hK ts g hv] at hs
    obtain rfl : strat = [] := by simpa using hs
    cases hd
  | call n f =>
    obtain ⟨b, hb⟩ := forget_call (P := P) hv
    rw [produceTables_call K hK ts g hv hb] at hs
    obtain rfl : strat = [⟨g.lb, b, g.rb⟩] := by simpa using hs
    obtain rfl : d = ⟨g.lb, b, g.rb⟩ := by simpa using hd
    exact ⟨hg.lb, hg.rb, bodyOf_normal hb, bodyOf_fo hP hb⟩
  | union xs =>
    rw [produceTables_union K hK ts g hv] at hs
    obtain rfl : strat = xs.map fun x => ⟨g.lb, x, g.rb⟩ := by simpa using hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    have hm : x ∈ g.node.view.members := by rw [forget_union hv]; exact hx
    exact ⟨hg.lb, hg.rb, hg.normal.view_members hm, hg.fo.view_members hm⟩
  | chain xs =>
    rw [produceTables_chain K hK ts g hv] at hs
    obtain ⟨r, hr, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have := seqSplit_of_mem K hK hg hv hw
    exact way_ok K hK ts hL hg this.lok this.rok hs hd
  | meet xs =>
    rw [produceTables_meet K hK ts g hv] at hs
    obtain ⟨r, hr, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have := andSplit_of_mem K hK hg hv hw
    exact way_ok K hK ts hL hg this.lok this.rok hs hd

/-! ## What the candidates of one strategy cover -/

/-- The tables cover every derivation of the goals of a strategy that is
smaller than the derivations at depth `k` of the node of `g`: at a smaller
depth of unfolding, or at depth `k` on a smaller node. -/
def Below (P : Program) (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel) (k : Nat)
    (strat : List (GoalOf R Rel)) : Prop :=
  ∀ d ∈ strat, ∀ (k' : Nat) (G' : GRel), (k' < k ∨ (k' = k ∧ d.node.size < g.node.size)) →
    G' ∈ GDn P k' d.node → (pairsOf P d G').Nonempty → Cov (ansOf ts d) (pairsOf P d G')

theorem way_cov_seq (hL : D.Lawful P.sorts.interp) (hT : TablesOk D ts) {g : GoalOf R Rel}
    {w : Kind × GoalOf R Rel × GoalOf R Rel} (hw : SeqSplit D P g w)
    {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.2) {k : Nat} {G : GRel}
    (hG : G ∈ GDn P k g.node) (hne : (pairsOf P g G).Nonempty) (H : Below P ts g k strat) :
    Cov (way (K := DerivationKernel.over D K hK P) ts g w).val.1 (pairsOf P g G) := by
  obtain ⟨kd, L, Rr⟩ := w
  obtain ⟨rfl, llb, lrb, rlb, rrb, lok, rok, lsize, rsize, node, gdn⟩ := hw
  simp only at llb lrb rlb rrb lsize rsize gdn lok rok
  rw [gdn k] at hG
  obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
  have e : pairsOf P g (G₁.comp G₂) = (pairsOf P L G₁).comp (pairsOf P Rr G₂) := by
    unfold pairsOf; rw [wrap_comp, llb, lrb, rlb, rrb]
  rw [e] at hne ⊢
  have ne₁ : (pairsOf P L G₁).Nonempty := by
    obtain ⟨⟨p, q⟩, m, h₁, -⟩ := hne; exact ⟨_, h₁⟩
  have ne₂ : (pairsOf P Rr G₂).Nonempty := by
    obtain ⟨⟨p, q⟩, m, -, h₂⟩ := hne; exact ⟨_, h₂⟩
  rcases (mem_way_strats K hK ts g _ strat).1 hs with rfl | ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · exact cov_join_seq hL K hK ts g _ hT rfl lrb rlb
      (H L (by simp) k G₁ (.inr ⟨rfl, lsize⟩) hG₁ ne₁)
      (H Rr (by simp) k G₂ (.inr ⟨rfl, rsize⟩) hG₂ ne₂) hne
  · exact cov_pushL_seq hL K hK ts g _ hT rfl lrb rlb rrb hd
      (H L (by simp) k G₁ (.inr ⟨rfl, lsize⟩) hG₁ ne₁)
      (fun x hx hne' => H _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx)) k G₂
        (.inr ⟨rfl, rsize⟩) hG₂ hne') hne
  · exact cov_pushR_seq hL K hK ts g _ hT rfl lrb rlb llb hd
      (H Rr (by simp) k G₂ (.inr ⟨rfl, rsize⟩) hG₂ ne₂)
      (fun y hy hne' => H _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) k G₁
        (.inr ⟨rfl, lsize⟩) hG₁ hne') hne

theorem way_cov_and (hL : D.Lawful P.sorts.interp) (hT : TablesOk D ts) {g : GoalOf R Rel}
    (hg : GoalOk D g) {w : Kind × GoalOf R Rel × GoalOf R Rel} (hw : AndSplit D P g w)
    {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.2) {k : Nat} {G : GRel}
    (hG : G ∈ GDn P k g.node) (hne : (pairsOf P g G).Nonempty) (H : Below P ts g k strat) :
    Cov (way (K := DerivationKernel.over D K hK P) ts g w).val.1 (pairsOf P g G) := by
  obtain ⟨kd, L, Rr⟩ := w
  obtain ⟨rfl, llb, lrb, rlb, rrb, lok, rok, lsize, rsize, node, node', gdn⟩ := hw
  simp only at llb lrb rlb rrb lsize rsize gdn lok rok
  rw [gdn k] at hG
  obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
  have e : pairsOf P g (G₁.meet G₂) = pairsOf P L G₁ ∩ pairsOf P Rr G₂ := by
    unfold pairsOf; rw [wrap_meet hL hg.lb hg.rb, llb, lrb, rlb, rrb]
  rw [e] at hne ⊢
  have ne₁ : (pairsOf P L G₁).Nonempty := hne.mono Set.inter_subset_left
  have ne₂ : (pairsOf P Rr G₂).Nonempty := hne.mono Set.inter_subset_right
  rcases (mem_way_strats K hK ts g _ strat).1 hs with rfl | ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · exact cov_join_and hL K hK ts g _ hT rfl (rlb.trans llb.symm) (rrb.trans lrb.symm)
      (H L (by simp) k G₁ (.inr ⟨rfl, lsize⟩) hG₁ ne₁)
      (H Rr (by simp) k G₂ (.inr ⟨rfl, rsize⟩) hG₂ ne₂) hne
  · exact cov_pushL_and hL K hK ts g _ hT rfl rok.lb rok.rb hd
      (H L (by simp) k G₁ (.inr ⟨rfl, lsize⟩) hG₁ ne₁)
      (fun x hx hne' => H _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx)) k G₂
        (.inr ⟨rfl, rsize⟩) hG₂ hne') hne
  · exact cov_pushR_and hL K hK ts g _ hT rfl lok.lb lok.rb hd
      (H Rr (by simp) k G₂ (.inr ⟨rfl, rsize⟩) hG₂ ne₂)
      (fun y hy hne' => H _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) k G₁
        (.inr ⟨rfl, lsize⟩) hG₁ hne') hne

/-- If the tables cover every smaller derivation of the goals of one strategy
of a goal, the candidates of the goal cover every derivation of its node at
depth `k`. -/
theorem strat_cov (hL : D.Lawful P.sorts.interp) (hT : TablesOk D ts) {g : GoalOf R Rel}
    (hg : GoalOk D g) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.2) {k : Nat}
    {G : GRel} (hG : G ∈ GDn P k g.node) (hne : (pairsOf P g G).Nonempty)
    (H : Below P ts g k strat) :
    Cov (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1 (pairsOf P g G) := by
  cases hv : g.node.view.forget with
  | span u => exact cov_span hL K hK ts g hg hv hG hne
  | call n f =>
    obtain ⟨b, hb⟩ := forget_call (P := P) hv
    have hs' := hs
    rw [produceTables_call K hK ts g hv hb] at hs'
    obtain rfl : strat = [⟨g.lb, b, g.rb⟩] := by simpa using hs'
    cases k with
    | zero => rw [(gdn_bodyOf hb 0).2] at hG; cases hG
    | succ k =>
      rw [(gdn_bodyOf hb k).1] at hG
      exact cov_call K hK ts g hT hv hb (H _ (by simp) k G (.inl (Nat.lt_succ_self k)) hG hne)
  | union xs =>
    have hs' := hs
    rw [produceTables_union K hK ts g hv] at hs'
    obtain rfl : strat = xs.map fun x => ⟨g.lb, x, g.rb⟩ := by simpa using hs'
    have hv' := forget_union hv
    rw [← (gdn_laws P k).gd_unionParts, ← hg.normal.view_union_eq hv'] at hG
    obtain ⟨x, hx, hGx⟩ : ∃ x ∈ xs, G ∈ GDn P k x := by simpa using hG
    exact cov_union K hK ts g hT hg.normal hv hx
      (H ⟨g.lb, x, g.rb⟩ (List.mem_map_of_mem hx) k G
        (.inr ⟨rfl, hg.normal.union_member_lt hv' hx⟩) hGx hne)
  | chain xs =>
    have hs' := hs
    rw [produceTables_chain K hK ts g hv] at hs' ⊢
    obtain ⟨r, hr, hs'⟩ := List.mem_flatMap.1 hs'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    refine (way_cov_seq K hK ts hL hT (seqSplit_of_mem K hK hg hv hw) hs' hG hne H).mono
      (fun a ha => List.mem_flatMap.2 ⟨_, hr, ha⟩) subset_rfl
  | meet xs =>
    have hs' := hs
    rw [produceTables_meet K hK ts g hv] at hs' ⊢
    obtain ⟨r, hr, hs'⟩ := List.mem_flatMap.1 hs'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    refine (way_cov_and K hK ts hL hT hg (andSplit_of_mem K hK hg hv hw) hs' hG hne H).mono
      (fun a ha => List.mem_flatMap.2 ⟨_, hr, ha⟩) subset_rfl

/-! ## The strategy that is always there -/

/-- A derivation of a goal's node needs finitely many smaller derivations of
the goals of one strategy the goal has whatever the tables hold (for a split,
joining the two sides): once the tables cover those, the candidates cover
it. -/
theorem static_cov (hL : D.Lawful P.sorts.interp) {g : GoalOf R Rel} (hg : GoalOk D g) {k : Nat}
    {G : GRel} (hG : G ∈ GDn P k g.node) (hne : (pairsOf P g G).Nonempty) :
    ∃ needs : List (GoalOf R Rel × Nat × GRel),
      (∀ x ∈ needs, (x.2.1 < k ∨ (x.2.1 = k ∧ x.1.node.size < g.node.size)) ∧
        x.2.2 ∈ GDn P x.2.1 x.1.node ∧ (pairsOf P x.1 x.2.2).Nonempty) ∧
      ∀ ts : List (TableOf R Rel (Ans D P)), TablesOk D ts →
        (∃ strat ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.2,
          ∀ x ∈ needs, x.1 ∈ strat) ∧
        ((∀ x ∈ needs, Cov (ansOf ts x.1) (pairsOf P x.1 x.2.2)) →
          Cov (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1 (pairsOf P g G)) := by
  cases hv : g.node.view.forget with
  | span u =>
    refine ⟨[], by simp, fun ts _ => ⟨⟨[], ?_, by simp⟩, fun _ => cov_span hL K hK ts g hg hv hG hne⟩⟩
    rw [produceTables_span K hK ts g hv]; simp
  | call n f =>
    obtain ⟨b, hb⟩ := forget_call (P := P) hv
    cases k with
    | zero => rw [(gdn_bodyOf hb 0).2] at hG; cases hG
    | succ k =>
      rw [(gdn_bodyOf hb k).1] at hG
      refine ⟨[(⟨g.lb, b, g.rb⟩, k, G)], ?_, fun ts hT => ⟨⟨[⟨g.lb, b, g.rb⟩], ?_, by simp⟩,
        fun H => cov_call K hK ts g hT hv hb (H (⟨g.lb, b, g.rb⟩, k, G) (by simp))⟩⟩
      · intro x hx
        obtain rfl : x = (⟨g.lb, b, g.rb⟩, k, G) := by simpa using hx
        exact ⟨.inl (Nat.lt_succ_self k), hG, hne⟩
      · rw [produceTables_call K hK ts g hv hb]; simp
  | union xs =>
    have hv' := forget_union hv
    rw [← (gdn_laws P k).gd_unionParts, ← hg.normal.view_union_eq hv'] at hG
    obtain ⟨x, hx, hGx⟩ : ∃ x ∈ xs, G ∈ GDn P k x := by simpa using hG
    refine ⟨[(⟨g.lb, x, g.rb⟩, k, G)], ?_, fun ts hT =>
      ⟨⟨xs.map fun x => ⟨g.lb, x, g.rb⟩, ?_, ?_⟩,
        fun H => cov_union K hK ts g hT hg.normal hv hx (H (⟨g.lb, x, g.rb⟩, k, G) (by simp))⟩⟩
    · intro y hy
      obtain rfl : y = (⟨g.lb, x, g.rb⟩, k, G) := by simpa using hy
      exact ⟨.inr ⟨rfl, hg.normal.union_member_lt hv' hx⟩, hGx, hne⟩
    · rw [produceTables_union K hK ts g hv]; simp
    · intro y hy
      obtain rfl : y = (⟨g.lb, x, g.rb⟩, k, G) := by simpa using hy
      exact List.mem_map_of_mem hx
  | chain xs =>
    obtain ⟨w, hw⟩ := exists_seqSplit (P := P) K hK hg hv
    have hsp := seqSplit_of_mem K hK hg hv hw
    obtain ⟨kd, L, Rr⟩ := w
    obtain ⟨hkd, llb, lrb, rlb, rrb, lok, rok, lsize, rsize, node, gdn⟩ := hsp
    simp only at hkd llb lrb rlb rrb lsize rsize gdn lok rok
    subst hkd
    rw [gdn k] at hG
    obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
    have e : pairsOf P g (G₁.comp G₂) = (pairsOf P L G₁).comp (pairsOf P Rr G₂) := by
      unfold pairsOf; rw [wrap_comp, llb, lrb, rlb, rrb]
    rw [e] at hne ⊢
    have ne₁ : (pairsOf P L G₁).Nonempty := by
      obtain ⟨⟨p, q⟩, m, h₁, -⟩ := hne; exact ⟨_, h₁⟩
    have ne₂ : (pairsOf P Rr G₂).Nonempty := by
      obtain ⟨⟨p, q⟩, m, -, h₂⟩ := hne; exact ⟨_, h₂⟩
    refine ⟨[(L, k, G₁), (Rr, k, G₂)], ?_, fun ts hT => ⟨⟨[L, Rr], ?_, ?_⟩, fun H => ?_⟩⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨.inr ⟨rfl, lsize⟩, hG₁, ne₁⟩
      · exact ⟨.inr ⟨rfl, rsize⟩, hG₂, ne₂⟩
    · rw [produceTables_chain K hK ts g hv]
      exact List.mem_flatMap.2 ⟨_, List.mem_map_of_mem hw,
        (mem_way_strats K hK ts g _ _).2 (.inl rfl)⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
    · rw [produceTables_chain K hK ts g hv]
      exact (cov_join_seq hL K hK ts g _ hT rfl lrb rlb (H (L, k, G₁) (by simp))
        (H (Rr, k, G₂) (by simp)) hne).mono
        (fun a ha => List.mem_flatMap.2 ⟨_, List.mem_map_of_mem hw, ha⟩) subset_rfl
  | meet xs =>
    obtain ⟨w, hw⟩ := exists_andSplit (P := P) K hK hg hv
    have hsp := andSplit_of_mem K hK hg hv hw
    obtain ⟨kd, L, Rr⟩ := w
    obtain ⟨hkd, llb, lrb, rlb, rrb, lok, rok, lsize, rsize, node, node', gdn⟩ := hsp
    simp only at hkd llb lrb rlb rrb lsize rsize gdn lok rok
    subst hkd
    rw [gdn k] at hG
    obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
    have e : pairsOf P g (G₁.meet G₂) = pairsOf P L G₁ ∩ pairsOf P Rr G₂ := by
      unfold pairsOf; rw [wrap_meet hL hg.lb hg.rb, llb, lrb, rlb, rrb]
    rw [e] at hne ⊢
    have ne₁ : (pairsOf P L G₁).Nonempty := hne.mono Set.inter_subset_left
    have ne₂ : (pairsOf P Rr G₂).Nonempty := hne.mono Set.inter_subset_right
    refine ⟨[(L, k, G₁), (Rr, k, G₂)], ?_, fun ts hT => ⟨⟨[L, Rr], ?_, ?_⟩, fun H => ?_⟩⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨.inr ⟨rfl, lsize⟩, hG₁, ne₁⟩
      · exact ⟨.inr ⟨rfl, rsize⟩, hG₂, ne₂⟩
    · rw [produceTables_meet K hK ts g hv]
      exact List.mem_flatMap.2 ⟨_, List.mem_map_of_mem hw,
        (mem_way_strats K hK ts g _ _).2 (.inl rfl)⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
    · rw [produceTables_meet K hK ts g hv]
      exact (cov_join_and hL K hK ts g _ hT rfl (rlb.trans llb.symm) (rrb.trans lrb.symm)
        (H (L, k, G₁) (by simp)) (H (Rr, k, G₂) (by simp)) hne).mono
        (fun a ha => List.mem_flatMap.2 ⟨_, List.mem_map_of_mem hw, ha⟩) subset_rfl

end Tabled

end RwLog
