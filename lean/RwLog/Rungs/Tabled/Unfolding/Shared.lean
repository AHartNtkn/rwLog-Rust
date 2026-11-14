/-
# The shared evaluation meets the specification of the unfolding race

`SmOk near n far C O s`: the summary `s` is the unfolding of the goal between
the boundaries, where `O` is what the node derives and `C` the derivations
read whole.

* Every answer of the summary is an answer of the goal.
* Every derivation read whole that relates a pair between the boundaries is
  covered by an answer of the summary.
* Every other derivation that relates a pair between the boundaries has an
  open interface of the summary that holds the right end of each of its pairs.
* The open interfaces are boundaries.

The memo holds summaries computed earlier. `MemoOk`: each is the unfolding of
what its key says (`Means`): a node at a depth between two boundaries, or the
members of a chain from the `idx`-th on. A summary that is looked up is then
as good as one that is computed (`memo_node`, `memo_spec`).

`evalS_ok`: the summary of a node is its unfolding and the memo stays right.
`sharedRace_ok`: the race answered with shared work meets `UOk`.
-/
import RwLog.Rungs.Tabled.Unfolding.SharedVal

namespace RwLog

namespace Tabled

namespace Unfold

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The summary is the unfolding of the goal between the boundaries. -/
structure SmOk (near : Option R) (n : Rel) (far : Option R) (C O : Set GRel) (s : Sm D P) :
    Prop where
  goal : ∀ a ∈ s.closed, a.goal = ⟨near, n, far⟩
  closed : ∀ G ∈ C, (wrapAt P.sorts.interp near (G.at P.sorts.interp) far).Nonempty →
    Cov s.closed (wrapAt P.sorts.interp near (G.at P.sorts.interp) far)
  opn : ∀ G ∈ O, G ∉ C → (wrapAt P.sorts.interp near (G.at P.sorts.interp) far).Nonempty →
    ∃ o ∈ s.opens, ∀ p ∈ wrapAt P.sorts.interp near (G.at P.sorts.interp) far,
      (p.2, p.2) ∈ bdenAt P.sorts.interp o
  bound : ∀ o ∈ s.opens, IsBound D o

omit [DecidableEq R] in
theorem SmOk.of_eq {near far : Option R} {n : Rel} {C O C' O' : Set GRel} {s : Sm D P}
    (h : SmOk near n far C O s) (hC : C' = C) (hO : O' = O) : SmOk near n far C' O' s :=
  hC ▸ hO ▸ h

omit [DecidableEq R] in
theorem SmOk.mok {near far : Option R} {n : Rel} {C O : Set GRel} {s : Sm D P}
    (h : SmOk near n far C O s) : MOk near n far C s.closed := ⟨h.goal, h.closed⟩

/-! ## Adding to a summary -/

omit [Answer R] in
theorem mem_addOpenV {xs : List (Option R)} {x o : Option R} :
    o ∈ addOpenV xs x ↔ o ∈ xs ∨ o = x := by
  unfold addOpenV
  split
  · next h =>
    obtain ⟨y, hy, e⟩ := List.any_eq_true.1 h
    obtain rfl : y = x := of_decide_eq_true e
    constructor
    · exact .inl
    · rintro (h | rfl)
      · exact h
      · exact hy
  · simp

omit [Answer R] in
theorem mem_foldl_addOpenV : ∀ (os acc : List (Option R)) (o : Option R),
    o ∈ os.foldl addOpenV acc ↔ o ∈ acc ∨ o ∈ os
  | [], acc, o => by simp
  | x :: os, acc, o => by
    rw [List.foldl_cons, mem_foldl_addOpenV os, mem_addOpenV, List.mem_cons, or_assoc]

theorem add_closed_from {s : Sm D P} {cs : List (Ans D P)} {os : List (Option R)} {b : Ans D P}
    (h : b ∈ (addSummaryV s cs os).closed) : b ∈ s.closed ∨ b ∈ cs :=
  (keepNew_spec cs s.closed).1 b h

theorem add_closed_to {s : Sm D P} {cs : List (Ans D P)} (os : List (Option R)) {a : Ans D P}
    (h : a ∈ s.closed ∨ a ∈ cs) : ∃ b ∈ (addSummaryV s cs os).closed, b.span = a.span :=
  (keepNew_spec cs s.closed).2 a h

theorem add_opens {s : Sm D P} {cs : List (Ans D P)} {os : List (Option R)} {o : Option R} :
    o ∈ (addSummaryV s cs os).opens ↔ o ∈ s.opens ∨ o ∈ os :=
  mem_foldl_addOpenV _ _ _

/-- What a summary holds after the products of each member of a list were
added to it: nothing but what it held and those products, and each of them,
an answer up to its representative. -/
structure FoldOk {ι : Type} (Q : ι → List (Ans D P) → List (Option R) → Prop) (L : List ι)
    (init r : Sm D P) : Prop where
  from_c : ∀ b ∈ r.closed, b ∈ init.closed ∨ ∃ x ∈ L, ∃ cs os, Q x cs os ∧ b ∈ cs
  from_o : ∀ o ∈ r.opens, o ∈ init.opens ∨ ∃ x ∈ L, ∃ cs os, Q x cs os ∧ o ∈ os
  keep_c : ∀ a ∈ init.closed, ∃ b ∈ r.closed, b.span = a.span
  keep_o : ∀ o ∈ init.opens, o ∈ r.opens
  into : ∀ x ∈ L, ∃ cs os, Q x cs os ∧ (∀ a ∈ cs, ∃ b ∈ r.closed, b.span = a.span) ∧
    ∀ o ∈ os, o ∈ r.opens

/-- A fold that adds the products of each member of a list to a summary and
threads the memo. -/
theorem fold_spec {ι : Type} (F : ι → Mm D P → List (Ans D P) × List (Option R) × Mm D P)
    (Q : ι → List (Ans D P) → List (Option R) → Prop) (Inv : Mm D P → Prop) :
    ∀ (L : List ι) (init : Sm D P × Mm D P), Inv init.2 →
      (∀ x ∈ L, ∀ m, Inv m → Q x (F x m).1 (F x m).2.1 ∧ Inv (F x m).2.2) →
      Inv (L.foldl (fun acc x =>
          (addSummaryV acc.1 (F x acc.2).1 (F x acc.2).2.1, (F x acc.2).2.2)) init).2 ∧
        FoldOk Q L init.1 (L.foldl (fun acc x =>
          (addSummaryV acc.1 (F x acc.2).1 (F x acc.2).2.1, (F x acc.2).2.2)) init).1
  | [], init, hinv, _ =>
    ⟨hinv, fun _ hb => .inl hb, fun _ ho => .inl ho, fun a ha => ⟨a, ha, rfl⟩, fun _ ho => ho,
      fun _ hx => by cases hx⟩
  | x :: L, init, hinv, H => by
    obtain ⟨hQ, hI⟩ := H x (by simp) init.2 hinv
    obtain ⟨ihI, ih⟩ := fold_spec F Q Inv L
      (addSummaryV init.1 (F x init.2).1 (F x init.2).2.1, (F x init.2).2.2) hI
      (fun y hy => H y (List.mem_cons_of_mem _ hy))
    refine ⟨ihI, fun b hb => ?_, fun o ho => ?_, fun a ha => ?_, fun o ho => ?_, fun y hy => ?_⟩
    · rcases ih.from_c b hb with h | ⟨y, hy, cs, os, q, hb'⟩
      · rcases add_closed_from h with h | h
        · exact .inl h
        · exact .inr ⟨x, by simp, _, _, hQ, h⟩
      · exact .inr ⟨y, List.mem_cons_of_mem _ hy, cs, os, q, hb'⟩
    · rcases ih.from_o o ho with h | ⟨y, hy, cs, os, q, ho'⟩
      · rcases add_opens.1 h with h | h
        · exact .inl h
        · exact .inr ⟨x, by simp, _, _, hQ, h⟩
      · exact .inr ⟨y, List.mem_cons_of_mem _ hy, cs, os, q, ho'⟩
    · obtain ⟨b, hb, e⟩ := add_closed_to (F x init.2).2.1 (cs := (F x init.2).1) (.inl ha)
      obtain ⟨b', hb', e'⟩ := ih.keep_c b hb
      exact ⟨b', hb', e'.trans e⟩
    · exact ih.keep_o o (add_opens.2 (.inl ho))
    · rcases List.mem_cons.1 hy with rfl | hy
      · refine ⟨_, _, hQ, fun a ha => ?_, fun o ho => ih.keep_o o (add_opens.2 (.inr ho))⟩
        obtain ⟨b, hb, e⟩ := add_closed_to (F y init.2).2.1 (s := init.1) (.inr ha)
        obtain ⟨b', hb', e'⟩ := ih.keep_c b hb
        exact ⟨b', hb', e'.trans e⟩
      · exact ih.into y hy

/-! ## A rule applied to the answers, and a union -/

omit [DecidableEq R] in
theorem lift_sm {near far : Option R} {b n : Rel} {C O : Set GRel} {s : Sm D P}
    {f : Ans D P → Option (Ans D P)} (h : SmOk near b far C O s)
    (hf₁ : ∀ a c, f a = some c → c.goal = ⟨a.goal.lb, n, a.goal.rb⟩)
    (hf₂ : ∀ a, a.goal = ⟨near, b, far⟩ → ∃ c, f a = some c ∧ c.span = a.span) :
    SmOk near n far C O ⟨s.closed.filterMap f, s.opens⟩ := by
  refine ⟨fun c hc => ?_, fun G hG hne => ?_, h.opn, h.bound⟩
  · obtain ⟨a, ha, e⟩ := List.mem_filterMap.1 hc
    rw [hf₁ a c e, h.goal a ha]
  · obtain ⟨a, ha, hX⟩ := h.closed G hG hne
    obtain ⟨c, hc, hs⟩ := hf₂ a (h.goal a ha)
    exact ⟨c, List.mem_filterMap.2 ⟨a, ha, hc⟩, by rw [hs]; exact hX⟩

omit [DecidableEq R] in
theorem union_sm {ι : Type} {near far : Option R} {n : Rel} (L : List ι) (C O : ι → Set GRel)
    {r : Sm D P}
    (h : FoldOk (fun i cs os => SmOk near n far (C i) (O i) (⟨cs, os⟩ : Sm D P)) L ⟨[], []⟩ r) :
    SmOk near n far {G | ∃ i ∈ L, G ∈ C i} {G | ∃ i ∈ L, G ∈ O i} r := by
  refine ⟨fun b hb => ?_, ?_, ?_, fun o ho => ?_⟩
  · rcases h.from_c b hb with h' | ⟨i, hi, cs, os, q, hb'⟩
    · simp at h'
    · exact q.goal b hb'
  · rintro G ⟨i, hi, hG⟩ hne
    obtain ⟨cs, os, q, hc, -⟩ := h.into i hi
    obtain ⟨a, ha, hX⟩ := q.closed G hG hne
    obtain ⟨b, hb, e⟩ := hc a ha
    exact ⟨b, hb, by rw [e]; exact hX⟩
  · rintro G ⟨i, hi, hG⟩ hnC hne
    obtain ⟨cs, os, q, -, ho⟩ := h.into i hi
    obtain ⟨o, ho', hp⟩ := q.opn G hG (fun hc => hnC ⟨i, hi, hc⟩) hne
    exact ⟨o, ho o ho', hp⟩
  · rcases h.from_o o ho with h' | ⟨i, hi, cs, os, q, ho'⟩
    · simp at h'
    · exact q.bound o ho'

/-! ## The memo -/

/-- What the summary recorded for a key has to be: the unfolding of a node,
or of the members of a chain from the `idx`-th on. -/
def Means (k : Key R Rel) (s : Sm D P) : Prop :=
  IsBound D k.near.bound → IsBound D k.far → Normal k.node → k.node.FO →
    (k.idx = 0 → SmOk k.near.bound k.node k.far (GR P k.d k.node) (GD P k.node) s) ∧
      (k.idx ≠ 0 → ∀ xs, k.node.view.forget = .chain xs → 2 ≤ (xs.drop k.idx).length →
        SmOk k.near.bound (mkSeq (xs.drop k.idx)) k.far
          (chainSet false (GR P k.d) (xs.drop k.idx)) (chainSet false (GD P) (xs.drop k.idx)) s)

/-- Every summary of the memo is what its key says. -/
def MemoOk (m : Mm D P) : Prop := ∀ p ∈ m, Means p.1 p.2

/-- A summary that is the unfolding of a goal, and a memo that is right. -/
abbrev Good2 (near : Option R) (n : Rel) (far : Option R) (C O : Set GRel)
    (r : Sm D P × Mm D P) : Prop :=
  SmOk near n far C O r.1 ∧ MemoOk r.2

theorem memo_spec {k : Key R Rel} {m : Mm D P} {body : Mm D P → Sm D P × Mm D P} (hm : MemoOk m)
    (hb : Means k (body m).1 ∧ MemoOk (body m).2) :
    Means k (memoV k m body).1 ∧ MemoOk (memoV k m body).2 := by
  unfold memoV
  cases h : lookupV m k with
  | some s =>
    unfold lookupV at h
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
    have hk : p.1 = k := sameKeyV_eq (by simpa using List.find?_some hp)
    have := hm p (List.mem_of_find?_eq_some hp)
    rw [hk] at this
    exact ⟨this, hm⟩
  | none =>
    refine ⟨hb.1, fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hb.1
    · exact hb.2 p hp

/-- The summary of a node, looked up or computed. -/
theorem memo_node {c : Near R} {n : Rel} {far : Option R} {d : Nat} {m : Mm D P}
    {body : Mm D P → Sm D P × Mm D P} (hm : MemoOk m) (hc : IsBound D c.bound)
    (hf : IsBound D far) (hn : Normal n) (hfo : n.FO)
    (hb : ∀ m', MemoOk m' → Good2 c.bound n far (GR P d n) (GD P n) (body m')) :
    Good2 c.bound n far (GR P d n) (GD P n) (memoV ⟨n, 0, d, c, far⟩ m body) := by
  obtain ⟨h₁, h₂⟩ := memo_spec (k := ⟨n, 0, d, c, far⟩) (body := body) hm
    ⟨fun _ _ _ _ => ⟨fun _ => (hb m hm).1, fun h => absurd rfl h⟩, (hb m hm).2⟩
  exact ⟨(h₁ hc hf hn hfo).1 rfl, h₂⟩

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

/-! ## A chain -/

section chain

include hL in
/-- The first member's summary, each of its products followed by the summary
of the rest. -/
theorem suf_body {c : Near R} {x : Rel} {tl : List Rel} (htl : tl ≠ []) (hx : NotSeq x)
    (hnt : ∀ y ∈ tl, NotSeq y) {C₁ O₁ C₂ O₂ : Set GRel} {far : Option R}
    (s₁ : Sm D P × Mm D P) (h₁ : SmOk c.bound x none C₁ O₁ s₁.1) (hm₁ : MemoOk s₁.2)
    (sv : Near R → Mm D P → Sm D P × Mm D P)
    (hsv : ∀ c' m, MemoOk m → IsBound D c'.bound →
      Good2 c'.bound (mkSeq tl) far C₂ O₂ (sv c' m)) :
    Good2 c.bound (mkSeq (x :: tl)) far {G | ∃ G₁ ∈ C₁, ∃ G' ∈ C₂, G = G₁.comp G'}
      {G | ∃ G₁ ∈ O₁, ∃ G' ∈ O₂, G = G₁.comp G'} (sufBodyV K hK sv s₁) := by
  obtain ⟨hmF₁, F₁⟩ := fold_spec (ι := Ans D P)
    (fun a m => ((sv ⟨D.rightBound a.span, true⟩ m).1.closed.filterMap
        fun b => (Ans.join D P K hK a b).val,
      (sv ⟨D.rightBound a.span, true⟩ m).1.opens, (sv ⟨D.rightBound a.span, true⟩ m).2))
    (fun a cs os => ∃ t : Sm D P, SmOk (D.rightBound a.span) (mkSeq tl) far C₂ O₂ t ∧
      cs = t.closed.filterMap (fun b => (Ans.join D P K hK a b).val) ∧ os = t.opens)
    MemoOk s₁.1.closed (⟨[], []⟩, s₁.2) hm₁
    (fun a _ m hm => ⟨⟨_, (hsv ⟨_, true⟩ m hm (isBound_right hL _)).1, rfl, rfl⟩,
      (hsv ⟨_, true⟩ m hm (isBound_right hL _)).2⟩)
  obtain ⟨hmF₂, F₂⟩ := fold_spec (ι := Option R)
    (fun o m => ([], (sv ⟨o, o.isSome⟩ m).1.closed.map (fun b => D.rightBound b.span) ++
        (sv ⟨o, o.isSome⟩ m).1.opens, (sv ⟨o, o.isSome⟩ m).2))
    (fun o cs os => ∃ t : Sm D P, SmOk o (mkSeq tl) far C₂ O₂ t ∧ cs = [] ∧
      os = t.closed.map (fun b => D.rightBound b.span) ++ t.opens)
    MemoOk s₁.1.opens _ hmF₁
    (fun o ho m hm => ⟨⟨_, (hsv ⟨o, o.isSome⟩ m hm (h₁.bound o ho)).1, rfl, rfl⟩,
      (hsv ⟨o, o.isSome⟩ m hm (h₁.bound o ho)).2⟩)
  -- what follows a closed product of the first member
  have push : ∀ {a : Ans D P} {G₁ : GRel} (G' : GRel),
      wrapAt P.sorts.interp c.bound (G₁.at P.sorts.interp) none ⊆ den P.sorts.interp a.span →
      (wrapAt P.sorts.interp c.bound (G₁.at P.sorts.interp) none).comp
          (wrapAt P.sorts.interp none (G'.at P.sorts.interp) far) ⊆
        (wrapAt P.sorts.interp c.bound (G₁.at P.sorts.interp) none).comp
          (wrapAt P.sorts.interp (D.rightBound a.span) (G'.at P.sorts.interp) far) :=
    fun {a} {G₁} G' hW =>
      push_sub hL false (t := some a.span) (fun p hp => adm_mem false (hW hp)) _ _
  -- what follows an open product of the first member
  have pushO : ∀ {o : Option R} {G₁ : GRel} (G' : GRel),
      (∀ p ∈ wrapAt P.sorts.interp c.bound (G₁.at P.sorts.interp) none,
        (p.2, p.2) ∈ bdenAt P.sorts.interp o) →
      (wrapAt P.sorts.interp c.bound (G₁.at P.sorts.interp) none).comp
          (wrapAt P.sorts.interp none (G'.at P.sorts.interp) far) ⊆
        (wrapAt P.sorts.interp c.bound (G₁.at P.sorts.interp) none).comp
          (wrapAt P.sorts.interp o (G'.at P.sorts.interp) far) := by
    rintro o G₁ G' hadm ⟨x', z⟩ ⟨mid, q₁, q₂⟩
    refine ⟨mid, q₁, ?_⟩
    obtain ⟨u, v, e₁, e₂, e₃⟩ := mem_wrapAt.1 q₂
    obtain rfl : u = mid := e₁
    exact mem_wrapAt.2 ⟨u, v, hadm (x', u) q₁, e₂, e₃⟩
  unfold sufBodyV
  refine ⟨⟨fun b hb => ?_, ?_, ?_, fun o ho => ?_⟩, hmF₂⟩
  · rcases F₂.from_c b hb with h | ⟨o, -, cs, os, ⟨t, -, rfl, -⟩, hb'⟩
    · rcases F₁.from_c b h with h' | ⟨a, ha, cs, os, ⟨t, ht, rfl, -⟩, hb'⟩
      · simp at h'
      · obtain ⟨b', hb'', e⟩ := List.mem_filterMap.1 hb'
        have hg := ((Ans.join_val K hK).1 e).2.2
        rw [h₁.goal a ha, ht.goal b' hb''] at hg
        rw [hg]
        show (⟨c.bound, mkSeq (seqParts x ++ seqParts (mkSeq tl)), far⟩ : Goal R) = _
        rw [seqParts_notSeq hx, seqParts_mkSeq htl hnt]
        rfl
    · simp at hb'
  · rintro G ⟨G₁, hG₁, G', hG', rfl⟩ hne
    rw [wrap_comp] at hne ⊢
    obtain ⟨a, ha, hW⟩ := h₁.closed G₁ hG₁ (by
      obtain ⟨⟨u, w⟩, mid, p₁, -⟩ := hne
      exact ⟨_, p₁⟩)
    have hsub := push G' hW
    have hne' := hne.mono hsub
    obtain ⟨cs, os, ⟨t, ht, rfl, rfl⟩, hcs, -⟩ := F₁.into a ha
    obtain ⟨b, hb, hWb⟩ := ht.closed G' hG' (by
      obtain ⟨⟨u, w⟩, mid, -, p₂⟩ := hne'
      exact ⟨_, p₂⟩)
    obtain ⟨c', hj, hcov, -⟩ := join_cov hL K hK (a := a) (b := b)
      (.inl ⟨by rw [h₁.goal a ha], .inr (by rw [ht.goal b hb])⟩) hW hWb hne'
    obtain ⟨c₁, hc₁, e₁⟩ := hcs c' (List.mem_filterMap.2 ⟨b, hb, hj⟩)
    obtain ⟨c₂, hc₂, e₂⟩ := F₂.keep_c c₁ hc₁
    exact ⟨c₂, hc₂, by rw [e₂, e₁]; exact hsub.trans hcov⟩
  · rintro G ⟨G₁, hG₁, G', hG', rfl⟩ hnC hne
    rw [wrap_comp] at hne ⊢
    have hne₁ : (wrapAt P.sorts.interp c.bound (G₁.at P.sorts.interp) none).Nonempty := by
      obtain ⟨⟨u, w⟩, mid, p₁, -⟩ := hne
      exact ⟨_, p₁⟩
    by_cases hc₁ : G₁ ∈ C₁
    · have hnC' : G' ∉ C₂ := fun h => hnC ⟨G₁, hc₁, G', h, rfl⟩
      obtain ⟨a, ha, hW⟩ := h₁.closed G₁ hc₁ hne₁
      have hsub := push G' hW
      obtain ⟨cs, os, ⟨t, ht, rfl, rfl⟩, -, hos⟩ := F₁.into a ha
      obtain ⟨o', ho', hadm⟩ := ht.opn G' hG' hnC' (by
        obtain ⟨⟨u, w⟩, mid, -, p₂⟩ := hne.mono hsub
        exact ⟨_, p₂⟩)
      refine ⟨o', F₂.keep_o o' (hos o' ho'), ?_⟩
      rintro ⟨x', z⟩ hp
      obtain ⟨mid, -, q₂⟩ := hsub hp
      exact hadm (mid, z) q₂
    · obtain ⟨o, ho, hadm⟩ := h₁.opn G₁ hG₁ hc₁ hne₁
      have hsub := pushO G' hadm
      obtain ⟨cs, os, ⟨t, ht, -, rfl⟩, -, hos⟩ := F₂.into o ho
      have hne₂ : (wrapAt P.sorts.interp o (G'.at P.sorts.interp) far).Nonempty := by
        obtain ⟨⟨u, w⟩, mid, -, p₂⟩ := hne.mono hsub
        exact ⟨_, p₂⟩
      by_cases hc₂ : G' ∈ C₂
      · obtain ⟨b, hb, hWb⟩ := ht.closed G' hc₂ hne₂
        refine ⟨D.rightBound b.span, hos _ (List.mem_append_left _
          (List.mem_map_of_mem (f := fun b : Ans D P => D.rightBound b.span) hb)), ?_⟩
        rintro ⟨x', z⟩ hp
        obtain ⟨mid, -, q₂⟩ := hsub hp
        exact rightBound_at hL (hWb q₂)
      · obtain ⟨o', ho', hadm'⟩ := ht.opn G' hG' hc₂ hne₂
        refine ⟨o', hos _ (List.mem_append_right _ ho'), ?_⟩
        rintro ⟨x', z⟩ hp
        obtain ⟨mid, -, q₂⟩ := hsub hp
        exact hadm' (mid, z) q₂
  · rcases F₂.from_o o ho with h | ⟨o₁, -, cs, os, ⟨t, ht, -, rfl⟩, ho'⟩
    · rcases F₁.from_o o h with h' | ⟨a, -, cs, os, ⟨t, ht, -, rfl⟩, ho'⟩
      · simp at h'
      · exact ht.bound o ho'
    · rcases List.mem_append.1 ho' with h' | h'
      · obtain ⟨b, -, rfl⟩ := List.mem_map.1 h'
        exact isBound_right hL _
      · exact ht.bound o h'

variable (wv : Near R → Rel → Option R → Mm D P → Sm D P × Mm D P)

/-- The members know their summaries in every context, at every memo. -/
def MembersS (d : Nat) (ys : List Rel) : Prop :=
  ∀ x ∈ ys, ∀ (c : Near R) (fr : Option R) (m : Mm D P), MemoOk m → IsBound D c.bound →
    IsBound D fr → Good2 c.bound x fr (GR P d x) (GD P x) (wv c x fr m)

include hL in
/-- The summary of the members of a chain from the `i`-th on. -/
theorem suf_ok {n : Rel} {d : Nat} {far : Option R} (hfar : IsBound D far) (hn : Normal n)
    (hfo : n.FO) {xsAll : List Rel} (hv : n.view.forget = .chain xsAll) :
    ∀ (ys : List Rel) (i : Nat) (c : Near R) (m : Mm D P), ys ≠ [] → xsAll.drop i = ys →
      MembersS wv d ys → (∀ x ∈ ys, NotSeq x) → MemoOk m → IsBound D c.bound →
      Good2 c.bound (mkSeq ys) far (chainSet false (GR P d) ys) (chainSet false (GD P) ys)
        (sufSV K hK wv n d far i ys c m)
  | [], _, _, _, h, _, _, _, _, _ => absurd rfl h
  | [x], i, c, m, _, _, HW, _, hm, hc => by
    simp only [sufSV]
    exact HW x (by simp) c far m hm hc hfar
  | x :: y :: zs, i, c, m, _, hi, HW, hns, hm, hc => by
    have hi' : xsAll.drop (i + 1) = y :: zs := by
      rw [← List.tail_drop, hi]
      rfl
    have body : ∀ m', MemoOk m' →
        Good2 c.bound (mkSeq (x :: y :: zs)) far (chainSet false (GR P d) (x :: y :: zs))
          (chainSet false (GD P) (x :: y :: zs))
          (sufBodyV K hK (sufSV K hK wv n d far (i + 1) (y :: zs)) (wv c x none m')) := by
      intro m' hm'
      obtain ⟨h₁, hm₁⟩ := HW x (by simp) c none m' hm' hc (isBound_none D)
      exact suf_body hL K hK (by simp) (hns x (by simp))
        (fun z hz => hns z (List.mem_cons_of_mem _ hz)) _ h₁ hm₁ _
        (fun c' m₂ hm₂ hc' => suf_ok hfar hn hfo hv (y :: zs) (i + 1) c' m₂ (by simp) hi'
          (fun z hz => HW z (List.mem_cons_of_mem _ hz))
          (fun z hz => hns z (List.mem_cons_of_mem _ hz)) hm₂ hc')
    by_cases hi0 : i = 0
    · simp only [sufSV, hi0, ite_true]
      rw [hi0] at body
      exact body m hm
    · simp only [sufSV, hi0, ite_false]
      obtain ⟨h₁, h₂⟩ := memo_spec (k := ⟨n, i, d, c, far⟩)
        (body := fun m => sufBodyV K hK (sufSV K hK wv n d far (i + 1) (y :: zs))
          (wv c x none m)) hm
        ⟨fun _ _ _ _ => ⟨fun h => absurd h hi0, fun _ xs' hxs' _ => by
          obtain rfl : xs' = xsAll := by
            rw [hv] at hxs'
            exact (NodeView.chain.inj hxs').symm
          show SmOk c.bound (mkSeq (xs'.drop i)) far _ _ _
          rw [hi]
          exact (body m hm).1⟩, (body m hm).2⟩
      have := (h₁ hc hfar hn hfo).2 hi0 xsAll hv (by rw [hi]; simp)
      refine ⟨?_, h₂⟩
      have e : xsAll.drop i = x :: y :: zs := hi
      simp only [e] at this
      exact this

end chain

/-! ## A meet -/

theorem f2_left {α β : Type} {Rr : α → β → Prop} {xs : List α} {ss : List β}
    (h : List.Forall₂ Rr xs ss) : ∀ x ∈ xs, ∃ s ∈ ss, Rr x s := by
  induction h with
  | nil => intro x hx; cases hx
  | cons hr _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨s, hs, r⟩ := ih x hx
      exact ⟨s, List.mem_cons_of_mem _ hs, r⟩

theorem f2_right {α β : Type} {Rr : α → β → Prop} {xs : List α} {ss : List β}
    (h : List.Forall₂ Rr xs ss) : ∀ s ∈ ss, ∃ x ∈ xs, Rr x s := by
  induction h with
  | nil => intro s hs; cases hs
  | cons hr _ ih =>
    intro s hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, r⟩ := ih s hs
      exact ⟨x, List.mem_cons_of_mem _ hx, r⟩

omit [DecidableEq R] in
/-- The summaries of the members of a meet, one for each. -/
theorem members_ok (wv : Rel → Mm D P → Sm D P × Mm D P) (Q : Rel → Sm D P → Prop) :
    ∀ (xs : List Rel) (m : Mm D P), MemoOk m →
      (∀ x ∈ xs, ∀ m, MemoOk m → Q x (wv x m).1 ∧ MemoOk (wv x m).2) →
      List.Forall₂ Q xs (membersSV wv xs m).1 ∧ MemoOk (membersSV wv xs m).2
  | [], _, hm, _ => ⟨.nil, hm⟩
  | x :: xs, m, hm, H => by
    obtain ⟨h₁, h₂⟩ := H x (by simp) m hm
    obtain ⟨h₃, h₄⟩ := members_ok wv Q xs _ h₂ (fun y hy => H y (List.mem_cons_of_mem _ hy))
    exact ⟨.cons h₁ h₃, h₄⟩

theorem isEmpty_of_mem {α : Type} {l : List α} {a : α} (h : a ∈ l) : l.isEmpty = false := by
  cases l with
  | nil => cases h
  | cons _ _ => rfl

omit [DecidableEq R] in
/-- A meet with a derivation that is not read whole is opaque. -/
theorem opaque_of {near far : Option R} {xs : List Rel} (C O : Rel → Set GRel)
    {ss : List (Sm D P)}
    (h : List.Forall₂ (fun x s => SmOk near x far (C x) (O x) s) xs ss) {G : GRel}
    (hG : G ∈ RwLog.andAll (xs.map O)) (hnC : G ∉ RwLog.andAll (xs.map C))
    (hne : (wrapAt P.sorts.interp near (G.at P.sorts.interp) far).Nonempty) :
    opaqueS ss = true := by
  have hsub := andAll_sub P.sorts.interp O _ G hG
  unfold opaqueS
  rw [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  refine ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨x, hx, hs'⟩ := f2_right h s hs
    obtain ⟨g, hg, hsb⟩ := hsub x hx
    have ne := hne.mono (wrap_mono hsb)
    by_cases hc : g ∈ C x
    · obtain ⟨a, ha, -⟩ := hs'.closed g hc ne
      simp [isEmpty_of_mem ha]
    · obtain ⟨o, ho, -⟩ := hs'.opn g hg hc ne
      simp [isEmpty_of_mem ho]
  · rcases andAll_cases P.sorts.interp C O _ G hG with hc | ⟨x, hx, g, hg, hn, hs'⟩
    · exact absurd hc hnC
    · obtain ⟨s, hs, hsm⟩ := f2_left h x hx
      obtain ⟨o, ho, -⟩ := hsm.opn g hg hn (hne.mono (wrap_mono hs'))
      exact ⟨s, hs, by simp [isEmpty_of_mem ho]⟩

include hL in
/-- The summary of a meet: its answers under the boundary it has, and whether
it is opaque under a boundary that takes no pair away. -/
theorem meet_sm {near near' far : Option R}
    (hn' : ∀ X : PRel, wrapAt P.sorts.interp near X far ⊆ wrapAt P.sorts.interp near' X far)
    (hf : IsBound D far) {xs : List Rel} (C O : Rel → Set GRel) {cl : List (Ans D P)}
    {ss : List (Sm D P)} (hm : MOk near (mkAnd xs) far (RwLog.andAll (xs.map C)) cl)
    (hB : List.Forall₂ (fun x s => SmOk near' x far (C x) (O x) s) xs ss) :
    SmOk near (mkAnd xs) far (RwLog.andAll (xs.map C)) (RwLog.andAll (xs.map O))
      ⟨cl.foldl keepNew [], if opaqueS ss then [far] else []⟩ := by
  refine ⟨fun a ha => ?_, fun G hG hne => ?_, fun G hG hnC hne => ?_, fun o ho => ?_⟩
  · exact hm.goal a (((keepNew_spec cl []).1 a ha).resolve_left (by simp))
  · obtain ⟨a, ha, hX⟩ := hm.closed G hG hne
    obtain ⟨b, hb, e⟩ := (keepNew_spec cl []).2 a (.inr ha)
    exact ⟨b, hb, by rw [e]; exact hX⟩
  · have hop := opaque_of C O hB hG hnC (hne.mono (hn' _))
    refine ⟨far, by simp [hop], ?_⟩
    rintro ⟨x, z⟩ hp
    obtain ⟨u, v, -, -, h₃⟩ := mem_wrapAt.1 hp
    have e : z = v := bden_eq hL hf h₃
    subst e
    exact h₃
  · have ho' : o ∈ (if opaqueS ss then [far] else []) := ho
    split at ho'
    · obtain rfl : o = far := by simpa using ho'
      exact hf
    · simp at ho'

/-! ## The whole unfolding -/

include hL in
/-- The summary of a node is its unfolding, and the memo stays right. -/
theorem evalS_ok (hP : ProgFO P) : ∀ (d : Nat) (c : Near R) (n : Rel) (far : Option R)
    (m : Mm D P), MemoOk m → IsBound D c.bound → IsBound D far → Normal n → n.FO →
    Good2 c.bound n far (GR P d n) (GD P n) (evalSV K hK d c n far m)
  | 0, c, n, far, m, hm, _, hf, _, _ => by
    simp only [evalSV]
    refine ⟨⟨fun a ha => by simp at ha, fun G hG => by simp at hG,
      fun G _ _ _ => ⟨far, by simp, ?_⟩, fun o ho => ?_⟩, hm⟩
    · rintro ⟨x, z⟩ hp
      obtain ⟨u, v, -, -, h₃⟩ := mem_wrapAt.1 hp
      have e : z = v := bden_eq hL hf h₃
      subst e
      exact h₃
    · obtain rfl : o = far := by simpa using ho
      exact hf
  | d + 1, c, n, far, m, hm, hc, hf, hn, hfo => by
    have ih := evalS_ok hP d
    simp only [evalSV]
    refine memo_node hm hc hf hn hfo fun m' hm' => ?_
    cases hv : n.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      dsimp only
      rw [gr_span P hv, (gd_laws P).span]
      have lc := leaf_cov hL K hK hc hf (hfo s (by simp [RelOf.spans]))
      refine ⟨⟨fun a ha => lc.1 a (Option.mem_toList.1 ha), fun G hG hne => ?_,
        fun G hG hnC _ => absurd hG hnC, fun o ho => by simp at ho⟩, hm'⟩
      obtain rfl : G = s.den := hG
      obtain ⟨a, ha, hX⟩ := lc.2 hne
      exact ⟨a, Option.mem_toList.2 ha, hX⟩
    | call f b₀ =>
      obtain ⟨b, hb⟩ := forget_call (P := P) hv
      simp only [hb]
      rw [gr_call P hv hb, gd_of_body P hb]
      obtain ⟨h₁, h₂⟩ := ih c b far m' hm' hc hf (bodyOf_normal hb) (bodyOf_fo hP hb)
      refine ⟨lift_sm h₁ (fun a c e => (Ans.unfold_val.1 e).2.2) (fun a ha => ?_), h₂⟩
      obtain ⟨c', hc', hs, -⟩ := Ans.unfold_ok (a := a) (n := n) (by rw [hb, ha])
      exact ⟨c', hc', hs⟩
    | union xs =>
      have hvu := forget_union hv
      have hparts := hn.view_union_eq hvu
      dsimp only
      have hzip : ∀ (S : Rel → Set GRel) (G : GRel),
          (∃ p ∈ xs.zipIdx, G ∈ S p.1) ↔ ∃ x ∈ xs, G ∈ S x := by
        intro S G
        constructor
        · rintro ⟨⟨x, i⟩, hp, hG⟩
          exact ⟨x, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp), hG⟩
        · rintro ⟨x, hx, hG⟩
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
          exact ⟨(x, i), List.mem_zipIdx_iff_getElem?.2 hi, hG⟩
      obtain ⟨hmF, F⟩ := fold_spec (ι := Rel × Nat)
        (fun p m => ((evalSV K hK d c p.1 far m).1.closed.filterMap
            fun a => (Ans.inj D P a n p.2).val,
          (evalSV K hK d c p.1 far m).1.opens, (evalSV K hK d c p.1 far m).2))
        (fun p cs os => SmOk c.bound n far (GR P d p.1) (GD P p.1) (⟨cs, os⟩ : Sm D P))
        MemoOk xs.zipIdx (⟨[], []⟩, m') hm'
        (fun p hp m₂ hm₂ => by
          have hx : xs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hp
          have hmem : p.1 ∈ n.view.members := by rw [hvu]; exact List.mem_of_getElem? hx
          obtain ⟨h₁, h₂⟩ := ih c p.1 far m₂ hm₂ hc hf (hn.view_members hmem)
            (hfo.view_members hmem)
          refine ⟨lift_sm h₁ (fun a c e => (Ans.inj_val.1 e).2.2) (fun a ha => ?_), h₂⟩
          obtain ⟨c', hc', hs, -⟩ := Ans.inj_ok (a := a) (u := n) (i := p.2) (by
            rw [← hparts, ha]; exact hx)
          exact ⟨c', hc', hs⟩)
      refine ⟨(union_sm xs.zipIdx (fun p => GR P d p.1) (fun p => GD P p.1) F).of_eq ?_ ?_, hmF⟩
      · rw [gr_union P hv]; ext G; exact (hzip _ G).symm
      · ext G; rw [gd_of_union P hn hvu]; exact (hzip _ G).symm
    | chain xs =>
      have hvc := forget_chain hv
      obtain ⟨h2, hmem, hmk⟩ := hn.view_chain hvc
      dsimp only
      have hxs : xs ≠ [] := by rintro rfl; simp at h2
      have key := suf_ok hL K hK (evalSV K hK d) hf hn hfo hv xs 0 c m' hxs rfl
        (fun x hx c' fr m₂ hm₂ hc' hfr => ih c' x fr m₂ hm₂ hc' hfr (hmem x hx).1
          (hfo.view_members (by rw [hvc]; exact hx)))
        (fun x hx => (hmem x hx).2) hm' hc
      rw [chainSet_fwd _ xs hxs, chainSet_fwd _ xs hxs, hmk] at key
      rw [gr_chain P hv, gd_of_chain P hvc]
      exact key
    | meet xs =>
      have hvm := forget_meet hv
      obtain ⟨h2, hmem, hs, hmk⟩ := hn.view_meet hvm
      dsimp only
      have mem : ∀ c' : Near R, IsBound D c'.bound → ∀ x ∈ xs, ∀ m₂, MemoOk m₂ →
          SmOk c'.bound x far (GR P d x) (GD P x) (evalSV K hK d c' x far m₂).1 ∧
            MemoOk (evalSV K hK d c' x far m₂).2 :=
        fun c' hc' x hx m₂ hm₂ => ih c' x far m₂ hm₂ hc' hf (hmem x hx).1
          (hfo.view_members (by rw [hvm]; exact hx))
      obtain ⟨hA, hmA⟩ := members_ok (fun x m => evalSV K hK d c x far m)
        (fun x s => SmOk c.bound x far (GR P d x) (GD P x) s) xs m' hm' (mem c hc)
      have hmok : MOk c.bound (mkAnd xs) far (RwLog.andAll (xs.map (GR P d)))
          (meetAllV K hK ((membersSV (fun x m => evalSV K hK d c x far m) xs m').1.map
            (·.closed))) :=
        meetAll_mok hL K hK hc hf h2 (fun x hx => (hmem x hx).2) hs (GR P d) (by
          rw [List.forall₂_map_right_iff]
          exact List.Forall₂.imp (fun _ _ h => h.mok) hA)
      rw [gr_meet P hv, gd_of_meet P hvm]
      cases hp : c.isPushed with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have := meet_sm hL (fun _ => subset_rfl) hf (GR P d) (GD P) hmok hA
        rw [hmk] at this
        exact ⟨this, hmA⟩
      | true =>
        simp only [ite_true]
        have ho : c.own.bound = none := by
          have h := hp
          simp only [Near.isPushed, Bool.and_eq_true] at h
          simp [Near.own, h.1]
        obtain ⟨hB, hmB⟩ := members_ok (fun x m => evalSV K hK d c.own x far m)
          (fun x s => SmOk none x far (GR P d x) (GD P x) s) xs _ hmA
          (fun x hx m₂ hm₂ => by
            have h := mem c.own (by rw [ho]; exact isBound_none D) x hx m₂ hm₂
            rwa [ho] at h)
        have := meet_sm hL (fun X => wrapD_none_sub hL false hc X far) hf (GR P d) (GD P)
          hmok hB
        rw [hmk] at this
        exact ⟨this, hmB⟩

/-! ## The race -/

include hL in
/-- The shared evaluation answers the unfolding race. -/
theorem sharedRace_ok (hP : ProgFO P) :
    UOk D P (sharedRace (K := DerivationKernel.over D K hK P)) := by
  have ok : ∀ (d : Nat) (g : GoalOf R Rel), GoalOk D g →
      SmOk g.lb g.node g.rb (GR P d g.node) (GD P g.node)
        (evalSV (P := P) K hK d ⟨g.lb, false⟩ g.node g.rb []).1 := fun d g hg =>
    (evalS_ok hL K hK hP d ⟨g.lb, false⟩ g.node g.rb [] (fun p hp => by cases hp) hg.lb hg.rb
      hg.normal hg.fo).1
  refine ⟨fun d g hg a ha => ?_, fun d g hg hfin k G hG hne => ?_⟩
  · rw [sharedRace_val] at ha
    by_cases hop : (evalSV (P := P) K hK d ⟨g.lb, false⟩ g.node g.rb []).1.opens.isEmpty = true
    · simp only [hop, ite_true] at ha
      exact (ok d g hg).goal a ha
    · simp [hop] at ha
  · by_cases hop : (evalSV (P := P) K hK d ⟨g.lb, false⟩ g.node g.rb []).1.opens.isEmpty = true
    · rw [sharedRace_val]
      simp only [hop, ite_true]
      by_cases hc : G ∈ GR P d g.node
      · exact (ok d g hg).closed G hc hne
      · obtain ⟨o, ho, -⟩ := (ok d g hg).opn G (gdn_sub_gd k _ hG) hc hne
        rw [isEmpty_of_mem ho] at hop
        cases hop
    · rw [sharedRace_val] at hfin
      simp [hop] at hfin

end Unfold

end Tabled

end RwLog
