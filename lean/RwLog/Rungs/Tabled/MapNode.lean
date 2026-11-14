/-
# What a goal and its image compute

In two runs of the tabled machine that correspond
(`Rungs/Tabled/MapGoal.lean`), the candidates of the image of a goal are the
images of the candidates of the goal (`cand_fwd`), and its strategies are the
images of the strategies (`strat_fwd`), by the kind of the node.

A split of a chain has for image a split of the image chain, with the sides
exchanged under the converse (`chain_split_fwd`); a split of a meet has for
image a split of the image meet, or one with its sides exchanged
(`meet_split_fwd`).
-/
import RwLog.Rungs.Tabled.MapSplit

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P P' : Program}

theorem ite_of_neg {α : Type} {c : Prop} [Decidable c] {x y : α} (h : ¬ c) :
    (if c then x else y) = y := by simp [h]

theorem seqSplits_mirror {n i : Nat} (h2 : 2 ≤ n) (hi : i ∈ seqSplits n) : n - i ∈ seqSplits n := by
  unfold seqSplits at hi ⊢
  by_cases h : n ≤ 2
  · rw [ite_of_pos h] at hi ⊢
    simp only [List.mem_singleton] at hi ⊢; omega
  · rw [ite_of_neg h] at hi ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega

theorem forget_call_view {e : Rel} {n : Name} {f : Bool} (h : e.view.forget = .call n f) :
    e.view = .call n f := by
  cases hv : e.view <;> rw [hv] at h <;> simp only [NodeView.forget] at h <;> cases h
  rfl

theorem without_eq {e : Rel} {xs : List Rel} (hp : andParts e = xs) {i : Nat} (hi : i < xs.length)
    (h2 : 2 ≤ xs.length) : e.without i = some (mkAnd (xs.eraseIdx i)) := by
  unfold RelOf.without
  simp only [RelOf.meetParts, hp]
  exact ite_of_pos ⟨hi, h2⟩

variable (K : Kernel R Cost) (hK : K.Refines D)

/-! ## The image of a split -/

theorem chain_split_fwd {g : GoalOf R Rel} (hg : GoalOk D g) {xs : List Rel}
    (hv : g.node.view.forget = .chain xs) {w : Kind × GoalOf R Rel × GoalOf R Rel}
    (hw : w ∈ (splitsOf (K := DerivationKernel.over D K hK P) g (.chain xs)).val) (b t : Bool) :
    (if b then (Kind.seq, gmap b t w.2.2, gmap b t w.2.1)
      else (Kind.seq, gmap b t w.2.1, gmap b t w.2.2)) ∈
      (splitsOf (K := DerivationKernel.over D K hK P') (gmap b t g)
        (.chain ((if b then xs.reverse else xs).map (nmap b t)))).val := by
  obtain ⟨i, hi, l, r, hl, hr, rfl⟩ := (mem_splitsOf_chain K hK g xs w).1 hw
  have hview := forget_chain hv
  obtain ⟨h2, -, -⟩ := hg.normal.view_chain hview
  obtain ⟨h0, hin⟩ := mem_seqSplits h2 hi
  have hlen := (hg.normal.chain_split hview h0 hin).1
  rw [mem_splitsOf_chain]
  have hlen' : ((if b then xs.reverse else xs).map (nmap b t)).length = xs.length := by
    cases b <;> simp
  rw [hlen']
  cases b
  · refine ⟨i, hi, nmap false t l, nmap false t r, ?_, ?_, rfl⟩
    · show (nmap false t g.node).interval 0 i = _
      rw [hg.normal.nmap_interval false t h0 (by omega)]
      simp [hl]
    · show (nmap false t g.node).interval i xs.length = _
      rw [hg.normal.nmap_interval false t hin (by omega)]
      simp [hr]
  · refine ⟨xs.length - i, seqSplits_mirror h2 hi, nmap true t r, nmap true t l, ?_, ?_, rfl⟩
    · show (nmap true t g.node).interval 0 (xs.length - i) = _
      rw [hg.normal.nmap_interval true t (by omega) (by omega), hlen]
      simp only [ite_true, Nat.sub_zero, Nat.sub_sub_self (Nat.le_of_lt hin), hr, Option.map_some]
    · show (nmap true t g.node).interval (xs.length - i) xs.length = _
      rw [hg.normal.nmap_interval true t (by omega) (by omega), hlen]
      simp only [ite_true, Nat.sub_self, Nat.sub_sub_self (Nat.le_of_lt hin), hl, Option.map_some]

theorem meet_split_fwd {g : GoalOf R Rel} (hg : GoalOk D g) {xs : List Rel}
    (hv : g.node.view.forget = .meet xs) {w : Kind × GoalOf R Rel × GoalOf R Rel}
    (hw : w ∈ (splitsOf (K := DerivationKernel.over D K hK P) g (.meet xs)).val) (b t : Bool) :
    (Kind.and, gmap b t w.2.1, gmap b t w.2.2) ∈
        (splitsOf (K := DerivationKernel.over D K hK P') (gmap b t g)
          (.meet (sortedParts (xs.map (nmap b t))))).val ∨
      (Kind.and, gmap b t w.2.2, gmap b t w.2.1) ∈
        (splitsOf (K := DerivationKernel.over D K hK P') (gmap b t g)
          (.meet (sortedParts (xs.map (nmap b t))))).val := by
  obtain ⟨i, hi, l, r, hl, hr, rfl⟩ := (mem_splitsOf_meet K hK g xs w).1 hw
  have hview := forget_meet hv
  obtain ⟨h2, -, -, -⟩ := hg.normal.view_meet hview
  have hilt := mem_andSplits h2 hi
  have hparts := (hg.normal.meet_split hview hilt).1
  have hparts' : andParts (nmap b t g.node) = sortedParts (xs.map (nmap b t)) := by
    rw [hg.normal.andParts_nmap, hparts]
  have hperm : (sortedParts (xs.map (nmap b t))).Perm (xs.map (nmap b t)) := sortedParts_perm _
  have hlen : (sortedParts (xs.map (nmap b t))).length = xs.length := by
    rw [hperm.length_eq, List.length_map]
  have key : ∀ (i j : Nat) (x y : Rel), xs[i]? = some x → g.node.without i = some y →
      (sortedParts (xs.map (nmap b t)))[j]? = some (nmap b t x) →
      (nmap b t g.node).without j = some (nmap b t y) := by
    intro i j x y hx hy hj
    rw [hg.normal.nmap_without b t (by rw [hparts]; exact h2) (by rw [hparts]; exact hx)
      (by rw [hparts']; exact hj), hy]
    rfl
  obtain ⟨j, hjlt, hj⟩ := List.getElem_of_mem
    (hperm.mem_iff.2 (List.mem_map_of_mem (List.mem_of_getElem? hl)))
  have hj' : (sortedParts (xs.map (nmap b t)))[j]? = some (nmap b t l) := by
    rw [List.getElem?_eq_getElem hjlt, hj]
  rw [mem_splitsOf_meet, mem_splitsOf_meet]
  by_cases hjs : j ∈ andSplits (sortedParts (xs.map (nmap b t))).length
  · exact .inl ⟨j, hjs, _, _, hj', key _ _ _ _ hl hr hj', rfl⟩
  · right
    rw [hlen] at hjs hjlt ⊢
    have hn : xs.length = 2 := by
      by_contra hne
      exact hjs (by unfold andSplits; rw [ite_of_neg (by omega)]; exact List.mem_range.2 hjlt)
    have hi0 : i = 0 := by
      unfold andSplits at hi; rw [ite_of_pos (by omega)] at hi; simpa using hi
    have hj1 : j = 1 := by
      have : j ≠ 0 := fun h => hjs (by unfold andSplits; rw [ite_of_pos (by omega)]; simp [h])
      omega
    subst hi0 hj1
    match xs, hn, hl, hr, hparts, hperm, hlen, hj', key with
    | [a, m], _, hl, hr, hparts, hperm, hlen, hj', key =>
      obtain rfl : a = l := by simpa using hl
      have hr0 := without_eq hparts (i := 0) (by simp) (by simp)
      have hr1 := without_eq hparts (i := 1) (by simp) (by simp)
      obtain rfl : m = r := by
        rw [hr0] at hr; simpa [mkAnd] using hr
      have hr1' : g.node.without 1 = some a := by rw [hr1]; rfl
      match hs : sortedParts ([a, m].map (nmap b t)), hlen with
      | [u, v], _ =>
        rw [hs] at hperm hj' key
        obtain rfl : v = nmap b t a := by simpa using hj'
        have hu : u = nmap b t m := by
          have hu' : u ∈ [nmap b t a, nmap b t m] := by
            simpa using hperm.mem_iff.1 (List.mem_cons_self ..)
          rcases List.mem_cons.1 hu' with rfl | hu'
          · have : nmap b t m ∈ [nmap b t a, nmap b t a] :=
              hperm.mem_iff.2 (by simp)
            exact (by simpa using this : nmap b t m = nmap b t a).symm
          · simpa using hu'
        subst hu
        exact ⟨0, by simp [andSplits], nmap b t m, nmap b t a, by simp,
          key 1 0 m a (by simp) hr1' (by simp), rfl⟩

/-! ## Candidates and strategies -/

section tied

variable {b t : Bool} {U : GOracle R Rel (Ans D P) Cost} {U' : GOracle R Rel (Ans D P') Cost}
  {ts : List (TableOf R Rel (Ans D P))} {ts' : List (TableOf R Rel (Ans D P'))}
  (hW : Twin D P P' b t U U') (hT : Tied b t ts ts')
include hW hT

omit [Answer R] [DecidableEq R] hW hT in
theorem gmap_lb_eq {L Rg : GoalOf R Rel} (h₁ : Rg.lb = L.lb) (h₂ : Rg.rb = L.rb) :
    (gmap b t Rg).lb = (gmap b t L).lb ∧ (gmap b t Rg).rb = (gmap b t L).rb := by
  cases b <;> simp [gmap, h₁, h₂]

/-- The candidates of the image of a goal are the images of its
candidates. -/
theorem cand_fwd {g : GoalOf R Rel} (hg : GoalOk D g) {c : Ans D P}
    (hc : c ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1) :
    ∃ c' ∈ (produceTables (K := DerivationKernel.over D K hK P') ts' (gmap b t g)).val.1,
      c'.span = smap b c.span := by
  cases hv : g.node.view.forget with
  | span u =>
    obtain ⟨s, hs⟩ := forget_span hv
    rw [produceTables_span K hK ts g hv] at hc
    have hc' : (Ans.leaf D P K hK g.lb g.node g.rb).val = some c := by simpa using hc
    obtain ⟨s', hs', -, -, hsb, -⟩ := (Ans.leaf_val K hK).1 hc'
    obtain rfl : s' = s := by rw [hs] at hs'; cases hs'; rfl
    have hfo : s'.firstOrder = true := hg.fo s' (by rw [hs]; simp [RelOf.spans])
    have hnode : (gmap b t g).node = .span (if b then s'.swap else s') := by
      show nmap b t g.node = _
      rw [hs, nmap_span]
    have hv' : (gmap b t g).node.view.forget = .span () := by rw [hnode]; rfl
    have hsb' := spanBoth_smap hW.law hfo hg.lb hg.rb b
    rw [hsb] at hsb'
    obtain ⟨c', hc1, hc2, -⟩ :=
      Ans.leaf_ok (P := P') K hK (hg.gmap b t).lb (hg.gmap b t).rb hsb'
    refine ⟨c', ?_, hc2⟩
    rw [produceTables_span K hK ts' _ hv', hnode, hc1]
    simp
  | call n f =>
    obtain ⟨b0, hb0⟩ := forget_call (P := P) hv
    rw [produceTables_call K hK ts g hv hb0] at hc
    obtain ⟨x, hx, hxc⟩ := List.mem_filterMap.1 hc
    have hcs := (Ans.unfold_val.1 hxc).2.1
    have hview := forget_call_view hv
    have hv' : (gmap b t g).node.view.forget = .call n (f ^^ (b ^^ t)) := by
      show (nmap b t g.node).view.forget = _
      rw [Normal.view_call hview b t]; rfl
    have hb' : Charged.bodyOf P' (gmap b t g).node = some (nmap b t b0) := by
      show Charged.bodyOf P' (nmap b t g.node) = _
      rw [hW.link.body _ hg.normal, hb0]; rfl
    obtain ⟨x', hx', ex⟩ := hT.fwd.ans _ x hx
    have gx := ansOf_goal hT.inv'.ok hx'
    obtain ⟨c', hc1, hc2, -⟩ :=
      Ans.unfold_ok (a := x') (n := (gmap b t g).node) (by rw [hb', gx]; rfl)
    refine ⟨c', ?_, by rw [hc2, ex, hcs]⟩
    rw [produceTables_call K hK ts' _ hv' hb']
    exact List.mem_filterMap.2 ⟨x', hx', hc1⟩
  | union xs =>
    have hview := forget_union hv
    have hmem := (hg.normal.view_union hview).1
    have hview' := hg.normal.view_union_nmap hview b t
    have hv' : (gmap b t g).node.view.forget = .union (sortedBranches (xs.map (nmap b t))) := by
      show (nmap b t g.node).view.forget = _
      rw [hview']; rfl
    rw [produceTables_union K hK ts g hv] at hc
    obtain ⟨p, hp, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨a, ha, hac⟩ := List.mem_filterMap.1 hc
    have hcs := (Ans.inj_val.1 hac).2.1
    obtain ⟨d, i⟩ := p
    have hd : d ∈ xs.map fun x => (⟨g.lb, x, g.rb⟩ : GoalOf R Rel) :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    obtain ⟨a', ha', ea⟩ := hT.fwd.ans _ a ha
    have ga := ansOf_goal hT.inv'.ok ha'
    have hx' : nmap b t x ∈ sortedBranches (xs.map (nmap b t)) :=
      mem_sortedBranches.2 ⟨List.mem_map_of_mem hx,
        (hmem x hx).1.nmap_ne_zero (hmem x hx).2.2 b t⟩
    obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hx'
    have hparts := (normal_nmap b t g.node).view_union_eq hview'
    obtain ⟨c', hc1, hc2, -⟩ := Ans.inj_ok (a := a') (u := (gmap b t g).node) (i := j) (by
      show (nmap b t g.node).unionParts[j]? = _
      rw [← hparts, ga, List.getElem?_eq_getElem hj, hxj]; rfl)
    refine ⟨c', ?_, by rw [hc2, ea, hcs]⟩
    rw [produceTables_union K hK ts' _ hv']
    refine List.mem_flatMap.2 ⟨(⟨(gmap b t g).lb, nmap b t x, (gmap b t g).rb⟩, j), ?_,
      List.mem_filterMap.2 ⟨a', ha', hc1⟩⟩
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hj, hxj]
  | chain xs =>
    rw [produceTables_chain K hK ts g hv] at hc
    obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have hS := seqSplit_of_mem K hK hg hv hw
    have hview := forget_chain hv
    have hv' : (gmap b t g).node.view.forget =
        .chain ((if b then xs.reverse else xs).map (nmap b t)) := by
      show (nmap b t g.node).view.forget = _
      rw [hg.normal.view_chain_nmap hview b t]; rfl
    have hw' := chain_split_fwd (P' := P') K hK hg hv hw b t
    obtain ⟨k, L, Rg⟩ := w
    obtain rfl : k = .seq := hS.kind
    rw [produceTables_chain K hK ts' _ hv']
    cases b
    · obtain ⟨c', hc', e⟩ := way_seq_cand K hK hW hT hS.lok.normal hS.rok.normal hS.lrb hS.rlb hc
      have hw'' : (Kind.seq, gmap false t L, gmap false t Rg) ∈ _ := hw'
      exact ⟨c', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw'', rfl⟩, hc'⟩, e⟩
    · obtain ⟨c', hc', e⟩ := way_conv_cand K hK hW hT hS.lok.normal hS.rok.normal hS.lrb hS.rlb hc
      have hw'' : (Kind.seq, gmap true t Rg, gmap true t L) ∈ _ := hw'
      exact ⟨c', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw'', rfl⟩, hc'⟩, e⟩
  | meet xs =>
    rw [produceTables_meet K hK ts g hv] at hc
    obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have hS := andSplit_of_mem K hK hg hv hw
    have hview := forget_meet hv
    have hv' : (gmap b t g).node.view.forget = .meet (sortedParts (xs.map (nmap b t))) := by
      show (nmap b t g.node).view.forget = _
      rw [hg.normal.view_meet_nmap hview b t]; rfl
    have hw' := meet_split_fwd (P' := P') K hK hg hv hw b t
    obtain ⟨k, L, Rg⟩ := w
    obtain rfl : k = .and := hS.kind
    have h₁ : Rg.lb = L.lb := hS.rlb.trans hS.llb.symm
    have h₂ : Rg.rb = L.rb := hS.rrb.trans hS.lrb.symm
    obtain ⟨c', hc', e⟩ := way_and_cand K hK hW hT hS.lok.normal hS.rok.normal h₁ h₂ hc
    rw [produceTables_meet K hK ts' _ hv']
    rcases hw' with hw' | hw'
    · exact ⟨c', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw', rfl⟩, hc'⟩, e⟩
    · obtain ⟨c'', hc'', e'⟩ := way_swap_cand K hK hW.law' hT.inv'.ok
        (gmap_lb_eq h₁ h₂).1 (gmap_lb_eq h₁ h₂).2 hc'
      exact ⟨c'', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw', rfl⟩, hc''⟩, e'.trans e⟩

/-- The strategies of the image of a goal are the images of its
strategies. -/
theorem strat_fwd {g : GoalOf R Rel} (hg : GoalOk D g) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.2) :
    ∃ strat' ∈ (produceTables (K := DerivationKernel.over D K hK P') ts' (gmap b t g)).val.2,
      Img (gmap b t) strat strat' := by
  cases hv : g.node.view.forget with
  | span u =>
    obtain ⟨s, hs'⟩ := forget_span hv
    rw [produceTables_span K hK ts g hv] at hs
    obtain rfl : strat = [] := by simpa using hs
    have hv' : (gmap b t g).node.view.forget = .span () := by
      show (nmap b t g.node).view.forget = _
      rw [hs', nmap_span]; rfl
    refine ⟨[], ?_, by simp [Img]⟩
    rw [produceTables_span K hK ts' _ hv']
    simp
  | call n f =>
    obtain ⟨b0, hb0⟩ := forget_call (P := P) hv
    rw [produceTables_call K hK ts g hv hb0] at hs
    obtain rfl : strat = [⟨g.lb, b0, g.rb⟩] := by simpa using hs
    have hview := forget_call_view hv
    have hv' : (gmap b t g).node.view.forget = .call n (f ^^ (b ^^ t)) := by
      show (nmap b t g.node).view.forget = _
      rw [Normal.view_call hview b t]; rfl
    have hb' : Charged.bodyOf P' (gmap b t g).node = some (nmap b t b0) := by
      show Charged.bodyOf P' (nmap b t g.node) = _
      rw [hW.link.body _ hg.normal, hb0]; rfl
    refine ⟨[gmap b t ⟨g.lb, b0, g.rb⟩], ?_, by simp [Img]⟩
    rw [produceTables_call K hK ts' _ hv' hb']
    exact List.mem_singleton.2 rfl
  | union xs =>
    have hview := forget_union hv
    have hmem := (hg.normal.view_union hview).1
    have hview' := hg.normal.view_union_nmap hview b t
    have hv' : (gmap b t g).node.view.forget = .union (sortedBranches (xs.map (nmap b t))) := by
      show (nmap b t g.node).view.forget = _
      rw [hview']; rfl
    rw [produceTables_union K hK ts g hv] at hs
    obtain rfl : strat = xs.map fun x => (⟨g.lb, x, g.rb⟩ : GoalOf R Rel) := by simpa using hs
    refine ⟨_, by rw [produceTables_union K hK ts' _ hv']; exact List.mem_singleton.2 rfl, ?_, ?_⟩
    · intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      exact List.mem_map.2 ⟨nmap b t x, mem_sortedBranches.2 ⟨List.mem_map_of_mem hx,
        (hmem x hx).1.nmap_ne_zero (hmem x hx).2.2 b t⟩, rfl⟩
    · intro d' hd'
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hd'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (mem_sortedBranches.1 hz).1
      exact ⟨_, List.mem_map_of_mem hx, rfl⟩
  | chain xs =>
    rw [produceTables_chain K hK ts g hv] at hs
    obtain ⟨r, hr, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have hS := seqSplit_of_mem K hK hg hv hw
    have hview := forget_chain hv
    have hv' : (gmap b t g).node.view.forget =
        .chain ((if b then xs.reverse else xs).map (nmap b t)) := by
      show (nmap b t g.node).view.forget = _
      rw [hg.normal.view_chain_nmap hview b t]; rfl
    have hw' := chain_split_fwd (P' := P') K hK hg hv hw b t
    obtain ⟨k, L, Rg⟩ := w
    obtain rfl : k = .seq := hS.kind
    rw [produceTables_chain K hK ts' _ hv']
    cases b
    · obtain ⟨s', hs', e⟩ := way_seq_strat K hK hW hT hS.lok.normal hS.rok.normal hs
      have hw'' : (Kind.seq, gmap false t L, gmap false t Rg) ∈ _ := hw'
      exact ⟨s', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw'', rfl⟩, hs'⟩, e⟩
    · obtain ⟨s', hs', e⟩ := way_conv_strat K hK hW hT hS.lok.normal hS.rok.normal hs
      have hw'' : (Kind.seq, gmap true t Rg, gmap true t L) ∈ _ := hw'
      exact ⟨s', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw'', rfl⟩, hs'⟩, e⟩
  | meet xs =>
    rw [produceTables_meet K hK ts g hv] at hs
    obtain ⟨r, hr, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have hS := andSplit_of_mem K hK hg hv hw
    have hview := forget_meet hv
    have hv' : (gmap b t g).node.view.forget = .meet (sortedParts (xs.map (nmap b t))) := by
      show (nmap b t g.node).view.forget = _
      rw [hg.normal.view_meet_nmap hview b t]; rfl
    have hw' := meet_split_fwd (P' := P') K hK hg hv hw b t
    obtain ⟨k, L, Rg⟩ := w
    obtain rfl : k = .and := hS.kind
    obtain ⟨s', hs', e⟩ := way_and_strat K hK hW hT hS.lok.normal hS.rok.normal hs
    rw [produceTables_meet K hK ts' _ hv']
    rcases hw' with hw' | hw'
    · exact ⟨s', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw', rfl⟩, hs'⟩, e⟩
    · obtain ⟨s'', hs'', e'⟩ := way_swap_strat K hK hs'
      refine ⟨s'', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw', rfl⟩, hs''⟩, ?_, ?_⟩
      · exact fun d hd => (e' _).2 (e.1 d hd)
      · exact fun d' hd' => e.2 d' ((e' _).1 hd')

end tied

end Tabled

end RwLog
