/-
# What the candidates of a goal cover

For each kind of node, and for each strategy of a split, the pairs a
candidate of the goal covers, given what the answers of the goals the
strategy depends on cover. These are the steps of the completeness proof of
the tabled machine (`Rungs/Tabled/Complete.lean`).
-/
import RwLog.Rungs.Tabled.Semantics
import RwLog.Kernel.NormalFormSplit

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- Every table has a goal the machine may hold, and its answers are answers
of that goal. -/
def TablesOk (D : Domain R) (ts : List (TableOf R Rel (Ans D P))) : Prop :=
  ∀ t ∈ ts, GoalOk D t.goal ∧ ∀ a ∈ t.answers, a.goal = toGoal t.goal

theorem lookup_some {ts : List (TableOf R Rel (Ans D P))} {g : GoalOf R Rel}
    {t : TableOf R Rel (Ans D P)} (h : lookup ts g = some t) : t ∈ ts ∧ t.goal = g := by
  unfold lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The answers a goal has in the tables are answers of that goal. -/
theorem ansOf_goal {ts : List (TableOf R Rel (Ans D P))} (hT : TablesOk D ts) {g : GoalOf R Rel}
    {a : Ans D P} (ha : a ∈ ansOf ts g) : a.goal = toGoal g := by
  unfold ansOf at ha
  cases h : lookup ts g with
  | none => rw [h] at ha; cases ha
  | some t =>
    rw [h] at ha
    obtain ⟨ht, rfl⟩ := lookup_some h
    exact (hT t ht).2 a ha

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)
  (ts : List (TableOf R Rel (Ans D P))) (g : GoalOf R Rel)

/-! ## Nodes that are not split -/

include hL in
/-- A span node: the answer of the rule `leaf` covers the pairs of the goal. -/
theorem cov_span (hg : GoalOk D g) (hv : g.node.view.forget = .span ()) {k : Nat} {G : GRel}
    (hG : G ∈ GDn P k g.node) (hne : (pairsOf P g G).Nonempty) :
    Cov (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1 (pairsOf P g G) := by
  obtain ⟨s, hs⟩ := forget_span hv
  rw [produceTables_span K hK ts g hv]
  rw [hs, (gdn_laws P k).span] at hG
  obtain rfl : G = s.den := hG
  have hfo : s.firstOrder = true := hg.fo s (by rw [hs]; simp [RelOf.spans])
  have hden := denO_spanBoth hL hfo g.lb g.rb
  cases hsb : spanBoth D g.lb s g.rb with
  | none =>
    rw [hsb, Domain.denO_none] at hden
    exact absurd hden.symm hne.ne_empty
  | some z =>
    rw [hsb, Domain.denO_some] at hden
    obtain ⟨c, hc, hcs, -⟩ := Ans.leaf_ok (P := P) K hK hg.lb hg.rb hsb
    rw [hs, hc]
    exact ⟨c, by simp, by rw [hcs, hden]; rfl⟩

/-- A call node: an answer of the body, by the rule `unfold`. -/
theorem cov_call (hT : TablesOk D ts) {n : Name} {f : Bool} {b : Rel}
    (hv : g.node.view.forget = .call n f) (hb : Charged.bodyOf P g.node = some b) {X : PRel}
    (hc : Cov (ansOf ts ⟨g.lb, b, g.rb⟩) X) :
    Cov (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1 X := by
  obtain ⟨a, ha, hX⟩ := hc
  rw [produceTables_call K hK ts g hv hb]
  have hag := ansOf_goal hT ha
  obtain ⟨c, hcv, hcs, -⟩ := Ans.unfold_ok (a := a) (n := g.node) (by rw [hb, hag]; rfl)
  exact ⟨c, List.mem_filterMap.2 ⟨a, ha, hcv⟩, by rw [hcs]; exact hX⟩

/-- A union node: an answer of a member, by the rule `inj`. -/
theorem cov_union (hT : TablesOk D ts) (hn : Normal g.node) {xs : List Rel}
    (hv : g.node.view.forget = .union xs) {x : Rel} (hx : x ∈ xs) {X : PRel}
    (hc : Cov (ansOf ts ⟨g.lb, x, g.rb⟩) X) :
    Cov (produceTables (K := DerivationKernel.over D K hK P) ts g).val.1 X := by
  obtain ⟨a, ha, hX⟩ := hc
  rw [produceTables_union K hK ts g hv]
  have hag := ansOf_goal hT ha
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  have hparts := hn.view_union_eq (forget_union hv)
  obtain ⟨c, hcv, hcs, -⟩ := Ans.inj_ok (a := a) (u := g.node) (i := i) (by
    rw [← hparts, hag, List.getElem?_eq_getElem hi, hxi]; rfl)
  refine ⟨c, List.mem_flatMap.2 ⟨(⟨g.lb, x, g.rb⟩, i), ?_, List.mem_filterMap.2 ⟨a, ha, hcv⟩⟩,
    by rw [hcs]; exact hX⟩
  rw [List.mem_zipIdx_iff_getElem?]
  simp [List.getElem?_eq_getElem hi, hxi]

/-! ## The strategies of a split -/

variable (w : Kind × GoalOf R Rel × GoalOf R Rel)

include hL in
/-- Joining answers of the two sides of a split of a chain. -/
theorem cov_join_seq (hT : TablesOk D ts) (hk : w.1 = .seq) (h₁ : w.2.1.rb = none)
    (h₂ : w.2.2.lb = none) {X₁ X₂ : PRel} (hc₁ : Cov (ansOf ts w.2.1) X₁)
    (hc₂ : Cov (ansOf ts w.2.2) X₂) (hne : (X₁.comp X₂).Nonempty) :
    Cov (way (K := DerivationKernel.over D K hK P) ts g w).val.1 (X₁.comp X₂) := by
  obtain ⟨a, ha, hX₁⟩ := hc₁
  obtain ⟨b, hb, hX₂⟩ := hc₂
  have hag := ansOf_goal hT ha
  have hbg := ansOf_goal hT hb
  obtain ⟨c, hcv, hcs, -⟩ := join_cov hL K hK (a := a) (b := b)
    (.inl ⟨by rw [hag]; exact h₁, .inl (by rw [hbg]; exact h₂)⟩) hX₁ hX₂ hne
  exact ⟨c, (mem_way K hK ts g w c).2 (.inl ⟨a, ha, b, hb, by rw [hk]; exact hcv⟩), hcs⟩

include hL in
/-- Conjoining answers of the two sides of a split of a meet. -/
theorem cov_join_and (hT : TablesOk D ts) (hk : w.1 = .and) (h₁ : w.2.2.lb = w.2.1.lb)
    (h₂ : w.2.2.rb = w.2.1.rb) {X₁ X₂ : PRel} (hc₁ : Cov (ansOf ts w.2.1) X₁)
    (hc₂ : Cov (ansOf ts w.2.2) X₂) (hne : (X₁ ∩ X₂).Nonempty) :
    Cov (way (K := DerivationKernel.over D K hK P) ts g w).val.1 (X₁ ∩ X₂) := by
  obtain ⟨a, ha, hX₁⟩ := hc₁
  obtain ⟨b, hb, hX₂⟩ := hc₂
  have hag := ansOf_goal hT ha
  have hbg := ansOf_goal hT hb
  obtain ⟨c, hcv, hcs, -⟩ := meet_cov hL K hK (a := a) (b := b)
    (.inl ⟨by rw [hag, hbg]; exact h₁, by rw [hag, hbg]; exact h₂⟩) hX₁ hX₂ hne
  exact ⟨c, (mem_way K hK ts g w c).2 (.inl ⟨a, ha, b, hb, by rw [hk]; exact hcv⟩), hcs⟩

include hL in
/-- Pushing the answers of the left side of a split of a chain into the
right side. -/
theorem cov_pushL_seq (hT : TablesOk D ts) (hk : w.1 = .seq) (h₁ : w.2.1.rb = none)
    (h₂ : w.2.2.lb = none) (h₃ : w.2.2.rb = g.rb) (hd : isDone ts w.2.1 = true) {X₁ : PRel}
    {G₂ : GRel} (hc₁ : Cov (ansOf ts w.2.1) X₁)
    (hc₂ : ∀ x ∈ (ansOf ts w.2.1).maximaBy (covB D P),
      (pairsOf P (pushLG D g w.2.2 .seq x) G₂).Nonempty →
        Cov (ansOf ts (pushLG D g w.2.2 .seq x)) (pairsOf P (pushLG D g w.2.2 .seq x) G₂))
    (hne : (X₁.comp (pairsOf P w.2.2 G₂)).Nonempty) :
    Cov (way (K := DerivationKernel.over D K hK P) ts g w).val.1
      (X₁.comp (pairsOf P w.2.2 G₂)) := by
  obtain ⟨a, ha, hX₁⟩ := hc₁
  obtain ⟨x, hx, hxa⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) ha
  have hX₁' : X₁ ⊆ den P.sorts.interp x.span := hX₁.trans ((covB_iff hL x a).1 hxa)
  have hxm : x ∈ ansOf ts w.2.1 := List.mem_maximaBy hx
  have hxg := ansOf_goal hT hxm
  have hsub : X₁.comp (pairsOf P w.2.2 G₂) ⊆
      X₁.comp (pairsOf P (pushLG D g w.2.2 .seq x) G₂) := by
    rintro ⟨p, q⟩ ⟨m, hpm, hmq⟩
    refine ⟨m, hpm, ?_⟩
    obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 hmq
    rw [h₂] at q₁
    obtain rfl : u = m := q₁
    rw [h₃] at q₃
    exact mem_wrapAt.2 ⟨u, v, rightBound_at hL (hX₁' hpm), q₂, q₃⟩
  have hne' : (pairsOf P (pushLG D g w.2.2 .seq x) G₂).Nonempty := by
    obtain ⟨⟨p, q⟩, hp⟩ := hne
    obtain ⟨m, -, hmq⟩ := hsub hp
    exact ⟨_, hmq⟩
  obtain ⟨y, hy, hY⟩ := hc₂ x hx hne'
  have hyg := ansOf_goal hT hy
  obtain ⟨c, hcv, hcs, -⟩ := join_cov hL K hK (a := x) (b := y)
    (.inl ⟨by rw [hxg]; exact h₁, .inr (by rw [hyg]; rfl)⟩) hX₁' hY
    (by
      obtain ⟨p, hp⟩ := hne
      exact ⟨p, hsub hp⟩)
  exact ⟨c, (mem_way K hK ts g w c).2 (.inr (.inl ⟨hd, x, hx, y,
    by rw [hk]; exact hy, by rw [hk]; exact hcv⟩)), hsub.trans hcs⟩

include hL in
/-- Pushing the answers of the right side of a split of a chain into the
left side. -/
theorem cov_pushR_seq (hT : TablesOk D ts) (hk : w.1 = .seq) (h₁ : w.2.1.rb = none)
    (h₂ : w.2.2.lb = none) (h₃ : w.2.1.lb = g.lb) (hd : isDone ts w.2.2 = true) {X₂ : PRel}
    {G₁ : GRel} (hc₂ : Cov (ansOf ts w.2.2) X₂)
    (hc₁ : ∀ y ∈ (ansOf ts w.2.2).maximaBy (covB D P),
      (pairsOf P (pushRG D g w.2.1 .seq y) G₁).Nonempty →
        Cov (ansOf ts (pushRG D g w.2.1 .seq y)) (pairsOf P (pushRG D g w.2.1 .seq y) G₁))
    (hne : ((pairsOf P w.2.1 G₁).comp X₂).Nonempty) :
    Cov (way (K := DerivationKernel.over D K hK P) ts g w).val.1
      ((pairsOf P w.2.1 G₁).comp X₂) := by
  obtain ⟨b, hb, hX₂⟩ := hc₂
  obtain ⟨y, hy, hyb⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) hb
  have hX₂' : X₂ ⊆ den P.sorts.interp y.span := hX₂.trans ((covB_iff hL y b).1 hyb)
  have hym : y ∈ ansOf ts w.2.2 := List.mem_maximaBy hy
  have hyg := ansOf_goal hT hym
  have hsub : (pairsOf P w.2.1 G₁).comp X₂ ⊆
      (pairsOf P (pushRG D g w.2.1 .seq y) G₁).comp X₂ := by
    rintro ⟨p, q⟩ ⟨m, hpm, hmq⟩
    refine ⟨m, ?_, hmq⟩
    obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 hpm
    rw [h₁] at q₃
    obtain rfl : m = v := q₃
    rw [h₃] at q₁
    exact mem_wrapAt.2 ⟨u, m, q₁, q₂, leftBound_at hL (hX₂' hmq)⟩
  have hne' : (pairsOf P (pushRG D g w.2.1 .seq y) G₁).Nonempty := by
    obtain ⟨⟨p, q⟩, hp⟩ := hne
    obtain ⟨m, hpm, -⟩ := hsub hp
    exact ⟨_, hpm⟩
  obtain ⟨x, hx, hY⟩ := hc₁ y hy hne'
  have hxg := ansOf_goal hT hx
  obtain ⟨c, hcv, hcs, -⟩ := join_cov hL K hK (a := x) (b := y)
    (.inr ⟨by rw [hyg]; exact h₂, by rw [hxg]; rfl⟩) hY hX₂'
    (by
      obtain ⟨p, hp⟩ := hne
      exact ⟨p, hsub hp⟩)
  exact ⟨c, (mem_way K hK ts g w c).2 (.inr (.inr ⟨hd, y, hy, x,
    by rw [hk]; exact hx, by rw [hk]; exact hcv⟩)), hsub.trans hcs⟩

include hL in
/-- Pushing the answers of one side of a split of a meet into the other
side, from the left. -/
theorem cov_pushL_and (hT : TablesOk D ts) (hk : w.1 = .and) (hl : IsBound D w.2.2.lb)
    (hr : IsBound D w.2.2.rb) (hd : isDone ts w.2.1 = true) {X₁ : PRel} {G₂ : GRel}
    (hc₁ : Cov (ansOf ts w.2.1) X₁)
    (hc₂ : ∀ x ∈ (ansOf ts w.2.1).maximaBy (covB D P),
      (pairsOf P (pushLG D g w.2.2 .and x) G₂).Nonempty →
        Cov (ansOf ts (pushLG D g w.2.2 .and x)) (pairsOf P (pushLG D g w.2.2 .and x) G₂))
    (hne : (X₁ ∩ pairsOf P w.2.2 G₂).Nonempty) :
    Cov (way (K := DerivationKernel.over D K hK P) ts g w).val.1
      (X₁ ∩ pairsOf P w.2.2 G₂) := by
  obtain ⟨a, ha, hX₁⟩ := hc₁
  obtain ⟨x, hx, hxa⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) ha
  have hX₁' : X₁ ⊆ den P.sorts.interp x.span := hX₁.trans ((covB_iff hL x a).1 hxa)
  have hsub : X₁ ∩ pairsOf P w.2.2 G₂ ⊆ X₁ ∩ pairsOf P (pushLG D g w.2.2 .and x) G₂ := by
    rintro ⟨p, q⟩ ⟨hp₁, hp₂⟩
    refine ⟨hp₁, ?_⟩
    have := ((mem_wrap hL hl hr).1 hp₂).2.1
    exact mem_wrapAt.2 ⟨p, q, leftBound_at hL (hX₁' hp₁), this, rightBound_at hL (hX₁' hp₁)⟩
  have hne' : (pairsOf P (pushLG D g w.2.2 .and x) G₂).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, (hsub hp).2⟩
  obtain ⟨y, hy, hY⟩ := hc₂ x hx hne'
  have hyg := ansOf_goal hT hy
  obtain ⟨c, hcv, hcs, -⟩ := meet_cov hL K hK (a := x) (b := y)
    (.inr ⟨by rw [hyg]; rfl, by rw [hyg]; rfl⟩) hX₁' hY
    (by
      obtain ⟨p, hp⟩ := hne
      exact ⟨p, (hsub hp).1, (hsub hp).2⟩)
  refine ⟨c, (mem_way K hK ts g w c).2 (.inr (.inl ⟨hd, x, hx, y,
    by rw [hk]; exact hy, by rw [hk]; exact hcv⟩)), fun p hp => hcs ?_⟩
  exact ⟨(hsub hp).1, (hsub hp).2⟩

include hL in
/-- Pushing the answers of one side of a split of a meet into the other
side, from the right. -/
theorem cov_pushR_and (hT : TablesOk D ts) (hk : w.1 = .and) (hl : IsBound D w.2.1.lb)
    (hr : IsBound D w.2.1.rb) (hd : isDone ts w.2.2 = true) {X₂ : PRel} {G₁ : GRel}
    (hc₂ : Cov (ansOf ts w.2.2) X₂)
    (hc₁ : ∀ y ∈ (ansOf ts w.2.2).maximaBy (covB D P),
      (pairsOf P (pushRG D g w.2.1 .and y) G₁).Nonempty →
        Cov (ansOf ts (pushRG D g w.2.1 .and y)) (pairsOf P (pushRG D g w.2.1 .and y) G₁))
    (hne : (pairsOf P w.2.1 G₁ ∩ X₂).Nonempty) :
    Cov (way (K := DerivationKernel.over D K hK P) ts g w).val.1
      (pairsOf P w.2.1 G₁ ∩ X₂) := by
  obtain ⟨b, hb, hX₂⟩ := hc₂
  obtain ⟨y, hy, hyb⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) hb
  have hX₂' : X₂ ⊆ den P.sorts.interp y.span := hX₂.trans ((covB_iff hL y b).1 hyb)
  have hsub : pairsOf P w.2.1 G₁ ∩ X₂ ⊆ pairsOf P (pushRG D g w.2.1 .and y) G₁ ∩ X₂ := by
    rintro ⟨p, q⟩ ⟨hp₁, hp₂⟩
    refine ⟨?_, hp₂⟩
    have := ((mem_wrap hL hl hr).1 hp₁).2.1
    exact mem_wrapAt.2 ⟨p, q, leftBound_at hL (hX₂' hp₂), this, rightBound_at hL (hX₂' hp₂)⟩
  have hne' : (pairsOf P (pushRG D g w.2.1 .and y) G₁).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, (hsub hp).1⟩
  obtain ⟨x, hx, hY⟩ := hc₁ y hy hne'
  have hxg := ansOf_goal hT hx
  obtain ⟨c, hcv, hcs, -⟩ := meet_cov hL K hK (a := y) (b := x)
    (.inr ⟨by rw [hxg]; rfl, by rw [hxg]; rfl⟩) hX₂' hY
    (by
      obtain ⟨p, hp⟩ := hne
      exact ⟨p, (hsub hp).2, (hsub hp).1⟩)
  refine ⟨c, (mem_way K hK ts g w c).2 (.inr (.inr ⟨hd, y, hy, x,
    by rw [hk]; exact hx, by rw [hk]; exact hcv⟩)), fun p hp => hcs ?_⟩
  exact ⟨(hsub hp).2, (hsub hp).1⟩

end Tabled

end RwLog
