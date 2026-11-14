/-
# What the items of a walk are: a rule applied, a union, a span, a chain

`WOk rev near n far C O is`: the items `is` are the unfolding of the goal
between the near and the far boundary, where `O` is what the node derives and
`C` the derivations read whole.

* Every item that is an answer is an answer of the goal.
* Every derivation read whole that relates a pair between the boundaries is
  covered by an item that is an answer.
* Every other derivation that relates a pair between the boundaries has an
  open item whose far stretch admits its pairs.

The near boundary may be one the walk pushed there. Whether a derivation is
read whole does not depend on it, which is why the statement is by
derivation.

This file proves it of the items of a chain from the items of its members
(`chain_wok`), each walked under what the items before it push, in either
direction.
-/
import RwLog.Rungs.Tabled.Unfolding.Dir

namespace RwLog

namespace Tabled

namespace Unfold

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The items are the unfolding of the goal between the near and the far
boundary. -/
structure WOk (rev : Bool) (near : Option R) (n : Rel) (far : Option R) (C O : Set GRel)
    (is : List (It D P)) : Prop where
  goal : ∀ a, Item.closed a ∈ is → a.goal = goalD rev near n far
  closed : ∀ G ∈ C, (wrapD P.sorts.interp rev near (G.at P.sorts.interp) far).Nonempty →
    ∃ a, Item.closed a ∈ is ∧
      wrapD P.sorts.interp rev near (G.at P.sorts.interp) far ⊆ den P.sorts.interp a.span
  opn : ∀ G ∈ O, G ∉ C → (wrapD P.sorts.interp rev near (G.at P.sorts.interp) far).Nonempty →
    ∃ t, Item.opn t ∈ is ∧
      ∀ p ∈ wrapD P.sorts.interp rev near (G.at P.sorts.interp) far, admD P.sorts.interp rev t p

omit [DecidableEq R] in
theorem WOk.of_eq {rev : Bool} {near far : Option R} {n : Rel} {C O C' O' : Set GRel}
    {is : List (It D P)} (h : WOk rev near n far C O is) (hC : C' = C) (hO : O' = O) :
    WOk rev near n far C' O' is :=
  hC ▸ hO ▸ h

/-! ## A rule applied to the answers, and a union -/

omit [DecidableEq R] in
theorem mem_lift {f : Ans D P → Option (Ans D P)} {is : List (It D P)} {it' : It D P} :
    it' ∈ is.flatMap (fun it => (liftItemV f it).toList) ↔
      ∃ it ∈ is, liftItemV f it = some it' := by
  simp only [List.mem_flatMap, Option.mem_toList]

omit [DecidableEq R] in
theorem lift_wok {rev : Bool} {near far : Option R} {b n : Rel} {C O : Set GRel}
    {is : List (It D P)} {f : Ans D P → Option (Ans D P)} (h : WOk rev near b far C O is)
    (hf₁ : ∀ a c, f a = some c → c.goal = ⟨a.goal.lb, n, a.goal.rb⟩)
    (hf₂ : ∀ a, a.goal = goalD rev near b far → ∃ c, f a = some c ∧ c.span = a.span) :
    WOk rev near n far C O (is.flatMap fun it => (liftItemV f it).toList) := by
  refine ⟨fun c hc => ?_, fun G hG hne => ?_, fun G hG hnC hne => ?_⟩
  · obtain ⟨it, hit, e⟩ := mem_lift.1 hc
    cases it with
    | closed a =>
      simp only [liftItemV, Option.map_eq_some_iff, Item.closed.injEq] at e
      obtain ⟨c', hc', rfl⟩ := e
      rw [hf₁ a c' hc', h.goal a hit]
      cases rev <;> rfl
    | opn t => simp [liftItemV] at e
  · obtain ⟨a, ha, hX⟩ := h.closed G hG hne
    obtain ⟨c, hc, hs⟩ := hf₂ a (h.goal a ha)
    exact ⟨c, mem_lift.2 ⟨_, ha, by simp [liftItemV, hc]⟩, by rw [hs]; exact hX⟩
  · obtain ⟨t, ht, hadm⟩ := h.opn G hG hnC hne
    exact ⟨t, mem_lift.2 ⟨_, ht, rfl⟩, hadm⟩

omit [DecidableEq R] in
theorem union_wok {ι : Type} {rev : Bool} {near far : Option R} {n : Rel} (L : List ι)
    (C O : ι → Set GRel) (is : ι → List (It D P))
    (h : ∀ i ∈ L, WOk rev near n far (C i) (O i) (is i)) :
    WOk rev near n far {G | ∃ i ∈ L, G ∈ C i} {G | ∃ i ∈ L, G ∈ O i} (L.flatMap is) := by
  refine ⟨fun c hc => ?_, ?_, ?_⟩
  · obtain ⟨i, hi, hc⟩ := List.mem_flatMap.1 hc
    exact (h i hi).goal c hc
  · rintro G ⟨i, hi, hG⟩ hne
    obtain ⟨a, ha, hX⟩ := (h i hi).closed G hG hne
    exact ⟨a, List.mem_flatMap.2 ⟨i, hi, ha⟩, hX⟩
  · rintro G ⟨i, hi, hG⟩ hnC hne
    obtain ⟨t, ht, hadm⟩ := (h i hi).opn G hG (fun hc => hnC ⟨i, hi, hc⟩) hne
    exact ⟨t, List.mem_flatMap.2 ⟨i, hi, ht⟩, hadm⟩

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

/-! ## A span -/

include hL in
theorem leaf_cov {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb) {s : Span}
    (hfo : s.firstOrder = true) :
    (∀ c, (Ans.leaf D P K hK lb (.span s) rb).val = some c → c.goal = ⟨lb, .span s, rb⟩) ∧
      ((wrapAt P.sorts.interp lb (s.den.at P.sorts.interp) rb).Nonempty →
        ∃ c, (Ans.leaf D P K hK lb (.span s) rb).val = some c ∧
          wrapAt P.sorts.interp lb (s.den.at P.sorts.interp) rb ⊆ den P.sorts.interp c.span) := by
  refine ⟨fun c hc => ?_, fun hne => ?_⟩
  · obtain ⟨s', hs, -, -, -, hcg⟩ := (Ans.leaf_val K hK).1 hc
    rw [hcg, ← hs]
  · have hden := denO_spanBoth hL hfo lb rb
    cases hsb : spanBoth D lb s rb with
    | none =>
      rw [hsb, Domain.denO_none] at hden
      exact absurd hden.symm hne.ne_empty
    | some z =>
      rw [hsb, Domain.denO_some] at hden
      obtain ⟨c, hc, hcs, -⟩ := Ans.leaf_ok (P := P) K hK hl hr hsb
      exact ⟨c, hc, by rw [hcs, hden]⟩

include hL in
theorem leaf_wok (rev : Bool) {near far : Option R} (hn : IsBound D near) (hf : IsBound D far)
    {s : Span} (hfo : s.firstOrder = true) :
    WOk rev near (.span s) far {s.den} {s.den}
      ((leafAtV (P := P) K hK rev near (.span s) far).toList.map .closed) := by
  have key : ∀ {c : Ans D P}, (Item.closed c : It D P) ∈
      (leafAtV (P := P) K hK rev near (.span s) far).toList.map
        (Item.closed : Ans D P → It D P) ↔
        leafAtV K hK rev near (.span s) far = some c := by
    intro c
    simp only [List.mem_map, Option.mem_toList, Item.closed.injEq, exists_eq_right]
  refine ⟨fun c hc => ?_, fun G hG hne => ?_, fun G hG hnC _ => absurd hG hnC⟩
  · have := key.1 hc
    cases rev
    · exact (leaf_cov hL K hK hn hf hfo).1 c this
    · exact (leaf_cov hL K hK hf hn hfo).1 c this
  · obtain rfl : G = s.den := hG
    cases rev
    · obtain ⟨c, hc, hX⟩ := (leaf_cov hL K hK hn hf hfo).2 hne
      exact ⟨c, key.2 hc, hX⟩
    · obtain ⟨c, hc, hX⟩ := (leaf_cov hL K hK hf hn hfo).2 hne
      exact ⟨c, key.2 hc, hX⟩

/-! ## A chain -/

section chain

variable (rev : Bool) (wv : Near R → Rel → Option R → List (It D P)) (far : Option R)

theorem mem_seqV_one {pre : Option (It D P)} {c : Near R} {x : Rel} {it'' : It D P} :
    it'' ∈ seqV K hK rev wv far pre c [x] ↔
      ∃ it ∈ wv c x far, extendV K hK rev pre it = some it'' := by
  simp only [seqV, List.isEmpty_nil, ite_true, List.mem_flatMap]
  constructor
  · rintro ⟨it, hit, h⟩
    cases he : extendV K hK rev pre it with
    | none => rw [he] at h; cases h
    | some it' =>
      rw [he] at h
      obtain rfl : it'' = it' := by simpa using h
      exact ⟨it, hit, he⟩
  · rintro ⟨it, hit, he⟩
    exact ⟨it, hit, by rw [he]; simp⟩

theorem mem_seqV_two {pre : Option (It D P)} {c : Near R} {x y : Rel} {zs : List Rel}
    {it'' : It D P} :
    it'' ∈ seqV K hK rev wv far pre c (x :: y :: zs) ↔
      ∃ it ∈ wv c x none, ∃ it', extendV K hK rev pre it = some it' ∧
        it'' ∈ seqV K hK rev wv far (some it') (nearAfterV D rev it') (y :: zs) := by
  rw [seqV]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.mem_flatMap]
  constructor
  · rintro ⟨it, hit, h⟩
    cases he : extendV K hK rev pre it with
    | none => rw [he] at h; cases h
    | some it' => rw [he] at h; exact ⟨it, hit, it', he, h⟩
  · rintro ⟨it, hit, it', he, h⟩
    exact ⟨it, hit, by rw [he]; exact h⟩

/-- After an open product nothing is an answer. -/
theorem seq_noclosed : ∀ (ys : List Rel) (t : Option R) (c : Near R) (a : Ans D P),
    Item.closed a ∉ seqV K hK rev wv far (some (.opn t)) c ys
  | [], t, c, a => by simp [seqV]
  | [x], t, c, a => by
    intro h
    obtain ⟨it, -, he⟩ := (mem_seqV_one K hK rev wv far).1 h
    cases it <;> simp [extendV] at he
  | x :: y :: zs, t, c, a => by
    intro h
    obtain ⟨it, -, it', he, h'⟩ := (mem_seqV_two K hK rev wv far).1 h
    cases it with
    | closed b =>
      obtain rfl : it' = .opn (some b.span) := by simpa [extendV] using he.symm
      exact seq_noclosed (y :: zs) _ _ a h'
    | opn t' =>
      obtain rfl : it' = .opn t' := by simpa [extendV] using he.symm
      exact seq_noclosed (y :: zs) _ _ a h'

variable (C O : Rel → Set GRel)

/-- The next member after an open product: the product stays open, and its
far stretch admits the pairs so far. -/
theorem step_open {β fr : Option R} {x : Rel} {is : List (It D P)}
    (hw : WOk rev β x fr (C x) (O x) is) (t : Option R) {X₀ : PRel} {G₁ : GRel}
    (hG₁ : G₁ ∈ O x)
    (hne : (compP rev X₀
      (wrapD P.sorts.interp rev β (G₁.at P.sorts.interp) fr)).Nonempty) :
    ∃ it ∈ is, ∃ t'', extendV K hK rev (some (.opn t)) it = some (.opn t'') ∧
      ∀ p ∈ compP rev X₀ (wrapD P.sorts.interp rev β (G₁.at P.sorts.interp) fr),
        admD P.sorts.interp rev t'' p := by
  by_cases hc : G₁ ∈ C x
  · obtain ⟨b, hb, hsub⟩ := hw.closed G₁ hc (compP_ne_right rev hne)
    exact ⟨.closed b, hb, some b.span, rfl, adm_comp rev fun q hq => adm_mem rev (hsub hq)⟩
  · obtain ⟨t', ht', hadm⟩ := hw.opn G₁ hG₁ hc (compP_ne_right rev hne)
    exact ⟨.opn t', ht', t', rfl, adm_comp rev hadm⟩

include hL in
omit [DecidableEq R] in
/-- The pairs of what was walked followed by two more stretches, with what
was walked pushed into the first of them. -/
theorem total_sub {t : Option R} {X₀ : PRel}
    (h : ∀ p ∈ X₀, admD P.sorts.interp rev t p) (G₁ G₂ : GRel) :
    compP rev X₀ (wrapD P.sorts.interp rev none ((compG rev G₁ G₂).at P.sorts.interp) far) ⊆
      compP rev (compP rev X₀
          (wrapD P.sorts.interp rev (nearB D rev t) (G₁.at P.sorts.interp) none))
        (wrapD P.sorts.interp rev none (G₂.at P.sorts.interp) far) := by
  rw [wrapD_comp, ← compP_assoc]
  exact compP_mono rev (push_sub hL rev h _ _) subset_rfl

variable (hfar : IsBound D far)

/-- The members know their items in every context. -/
def Members (ys : List Rel) : Prop :=
  ∀ x ∈ ys, ∀ (c : Near R) (fr : Option R), IsBound D c.bound → IsBound D fr →
    WOk rev c.bound x fr (C x) (O x) (wv c x fr)

include hL hfar in
/-- After an open product, every derivation of the rest that goes on from the
pairs so far has an open product. -/
theorem seq_open : ∀ (ys : List Rel), ys ≠ [] → Members rev wv C O ys →
    ∀ (t : Option R) (X₀ : PRel), (∀ p ∈ X₀, admD P.sorts.interp rev t p) →
    ∀ G ∈ chainSet rev O ys,
      (compP rev X₀ (wrapD P.sorts.interp rev none (G.at P.sorts.interp) far)).Nonempty →
      ∃ t', Item.opn t' ∈
          seqV K hK rev wv far (some (.opn t)) (nearAfterV (P := P) D rev (.opn t)) ys ∧
        ∀ p ∈ compP rev X₀ (wrapD P.sorts.interp rev none (G.at P.sorts.interp) far),
          admD P.sorts.interp rev t' p
  | [], h, _, _, _, _, _, _, _ => absurd rfl h
  | [x], _, HW, t, X₀, hX, G, hG, hne => by
    have hw := HW x (by simp) (nearAfterV D rev (.opn t)) far
      (by rw [nearAfterV_bound (P := P)]; exact nearB_isBound hL rev t) hfar
    rw [nearAfterV_bound (P := P)] at hw
    have hsub := push_sub hL rev hX (G.at P.sorts.interp) far
    obtain ⟨it, hit, t'', he, hadm⟩ := step_open K hK rev C O hw t hG (hne.mono hsub)
    exact ⟨t'', (mem_seqV_one K hK rev wv far).2 ⟨it, hit, he⟩, fun p hp => hadm p (hsub hp)⟩
  | x :: y :: zs, _, HW, t, X₀, hX, G, hG, hne => by
    obtain ⟨G₁, hG₁, G'', hG'', rfl⟩ := hG
    have hw := HW x (by simp) (nearAfterV D rev (.opn t)) none
      (by rw [nearAfterV_bound (P := P)]; exact nearB_isBound hL rev t) (isBound_none D)
    rw [nearAfterV_bound (P := P)] at hw
    have hsub := total_sub hL rev far hX G₁ G''
    have hne' := hne.mono hsub
    obtain ⟨it, hit, t'', he, hadm⟩ := step_open K hK rev C O hw t hG₁ (compP_ne_left rev hne')
    obtain ⟨t', ht', hadm'⟩ := seq_open (y :: zs) (by simp)
      (fun z hz => HW z (List.mem_cons_of_mem _ hz)) t'' _ hadm G'' hG'' hne'
    exact ⟨t', (mem_seqV_two K hK rev wv far).2 ⟨it, hit, _, he, ht'⟩,
      fun p hp => hadm' p (hsub hp)⟩

/-- The items of the rest of a chain after an answer `a` of what was walked
so far. -/
structure SOk (l : Option R) (a : Ans D P) (node : Rel) (Cs Os : Set GRel)
    (L : List (It D P)) : Prop where
  goal : ∀ c, Item.closed c ∈ L → c.goal = goalD rev l node far
  closed : ∀ X₀ : PRel, X₀ ⊆ den P.sorts.interp a.span → ∀ G ∈ Cs,
    (compP rev X₀ (wrapD P.sorts.interp rev none (G.at P.sorts.interp) far)).Nonempty →
    ∃ c, Item.closed c ∈ L ∧
      compP rev X₀ (wrapD P.sorts.interp rev none (G.at P.sorts.interp) far) ⊆
        den P.sorts.interp c.span
  opn : ∀ X₀ : PRel, X₀ ⊆ den P.sorts.interp a.span → ∀ G ∈ Os, G ∉ Cs →
    (compP rev X₀ (wrapD P.sorts.interp rev none (G.at P.sorts.interp) far)).Nonempty →
    ∃ t', Item.opn t' ∈ L ∧
      ∀ p ∈ compP rev X₀ (wrapD P.sorts.interp rev none (G.at P.sorts.interp) far),
        admD P.sorts.interp rev t' p

include hL hfar in
theorem seq_closed : ∀ (ys : List Rel), ys ≠ [] → Members rev wv C O ys →
    (∀ x ∈ ys, NotSeq x) → ∀ (pm : List Rel) (a : Ans D P) (l : Option R), pm ≠ [] →
    (∀ y ∈ pm, NotSeq y) → a.goal = goalD rev l (nodeD rev pm) none →
    SOk rev far l a (nodeD rev (pm ++ ys)) (chainSet rev C ys) (chainSet rev O ys)
      (seqV K hK rev wv far (some (.closed a)) (nearAfterV D rev (.closed a)) ys)
  | [], h, _, _, _, _, _, _, _, _ => absurd rfl h
  | [x], _, HW, hnsy, pm, a, l, hpm, hns, ha => by
    have hw : WOk rev (nearB D rev (some a.span)) x far (C x) (O x)
        (wv (nearAfterV D rev (.closed a)) x far) :=
      HW x (by simp) (nearAfterV D rev (.closed a)) far (nearB_isBound hL rev (some a.span)) hfar
    have hadm : ∀ X₀ : PRel, X₀ ⊆ den P.sorts.interp a.span →
        ∀ p ∈ X₀, admD P.sorts.interp rev (some a.span) p :=
      fun X₀ hX p hp => adm_mem rev (hX hp)
    refine ⟨fun c hc => ?_, fun X₀ hX G hG hne => ?_, fun X₀ hX G hG hnC hne => ?_⟩
    · obtain ⟨it, hit, he⟩ := (mem_seqV_one K hK rev wv far).1 hc
      cases it with
      | closed b =>
        simp only [extendV, Option.map_eq_some_iff, Item.closed.injEq] at he
        obtain ⟨c', hc', rfl⟩ := he
        rw [joinD_goal K hK rev hc' ha (hw.goal b hit),
          catD_node rev hpm hns (hnsy x (by simp))]
      | opn t => simp [extendV] at he
    · have hsub := push_sub hL rev (hadm X₀ hX) (G.at P.sorts.interp) far
      have hne' := hne.mono hsub
      obtain ⟨b, hb, hW⟩ := hw.closed G hG (compP_ne_right rev hne')
      obtain ⟨c, hc, hcs, -⟩ := joinD hL K hK rev ha (hw.goal b hb) hX hW hne'
      exact ⟨c, (mem_seqV_one K hK rev wv far).2 ⟨.closed b, hb, by simp [extendV, hc]⟩,
        hsub.trans hcs⟩
    · have hsub := push_sub hL rev (hadm X₀ hX) (G.at P.sorts.interp) far
      have hne' := hne.mono hsub
      obtain ⟨t', ht', ha'⟩ := hw.opn G hG hnC (compP_ne_right rev hne')
      exact ⟨t', (mem_seqV_one K hK rev wv far).2 ⟨.opn t', ht', rfl⟩,
        fun p hp => adm_comp rev ha' p (hsub hp)⟩
  | x :: y :: zs, _, HW, hnsy, pm, a, l, hpm, hns, ha => by
    have hw : WOk rev (nearB D rev (some a.span)) x none (C x) (O x)
        (wv (nearAfterV D rev (.closed a)) x none) :=
      HW x (by simp) (nearAfterV D rev (.closed a)) none (nearB_isBound hL rev (some a.span))
        (isBound_none D)
    have hadm : ∀ X₀ : PRel, X₀ ⊆ den P.sorts.interp a.span →
        ∀ p ∈ X₀, admD P.sorts.interp rev (some a.span) p :=
      fun X₀ hX p hp => adm_mem rev (hX hp)
    have HW' : Members rev wv C O (y :: zs) := fun z hz => HW z (List.mem_cons_of_mem _ hz)
    have hx := hnsy x (by simp)
    have hpm' : pm ++ [x] ≠ [] := by simp
    have hns' : ∀ z ∈ pm ++ [x], NotSeq z := fun z hz => by
      rcases List.mem_append.1 hz with h | h
      · exact hns z h
      · obtain rfl : z = x := by simpa using h
        exact hx
    have next : ∀ {b c' : Ans D P}, Item.closed b ∈ wv (nearAfterV D rev (.closed a)) x none →
        joinAtV K hK rev a b = some c' →
        SOk rev far l c' (nodeD rev (pm ++ x :: y :: zs)) (chainSet rev C (y :: zs))
          (chainSet rev O (y :: zs))
          (seqV K hK rev wv far (some (.closed c')) (nearAfterV D rev (.closed c')) (y :: zs)) := by
      intro b c' hb hc'
      have hg := joinD_goal K hK rev hc' ha (hw.goal b hb)
      rw [catD_node rev hpm hns hx] at hg
      have := seq_closed (y :: zs) (by simp) HW'
        (fun z hz => hnsy z (List.mem_cons_of_mem _ hz)) (pm ++ [x]) c' l hpm' hns' hg
      rwa [List.append_assoc, List.singleton_append] at this
    refine ⟨fun c hc => ?_, fun X₀ hX G hG hne => ?_, fun X₀ hX G hG hnC hne => ?_⟩
    · obtain ⟨it, hit, it', he, hc'⟩ := (mem_seqV_two K hK rev wv far).1 hc
      cases it with
      | closed b =>
        simp only [extendV, Option.map_eq_some_iff] at he
        obtain ⟨c', hj, rfl⟩ := he
        exact (next hit hj).goal c hc'
      | opn t =>
        obtain rfl : it' = .opn t := by simpa [extendV] using he.symm
        exact absurd hc' (seq_noclosed K hK rev wv far _ _ _ _)
    · obtain ⟨G₁, hG₁, G'', hG'', rfl⟩ := hG
      have hsub := total_sub hL rev far (hadm X₀ hX) G₁ G''
      have hne' := hne.mono hsub
      obtain ⟨b, hb, hW⟩ := hw.closed G₁ hG₁ (compP_ne_right rev (compP_ne_left rev hne'))
      obtain ⟨c', hj, hcs, -⟩ := joinD hL K hK rev ha (hw.goal b hb) hX hW
        (compP_ne_left rev hne')
      obtain ⟨c, hc, hcov⟩ := (next hb hj).closed _ hcs G'' hG'' hne'
      exact ⟨c, (mem_seqV_two K hK rev wv far).2 ⟨.closed b, hb, .closed c',
        by simp [extendV, hj], hc⟩, hsub.trans hcov⟩
    · obtain ⟨G₁, hG₁, G'', hG'', rfl⟩ := hG
      have hsub := total_sub hL rev far (hadm X₀ hX) G₁ G''
      have hne' := hne.mono hsub
      by_cases hc₁ : G₁ ∈ C x
      · have hnC' : G'' ∉ chainSet rev C (y :: zs) := fun h => hnC ⟨G₁, hc₁, G'', h, rfl⟩
        obtain ⟨b, hb, hW⟩ := hw.closed G₁ hc₁ (compP_ne_right rev (compP_ne_left rev hne'))
        obtain ⟨c', hj, hcs, -⟩ := joinD hL K hK rev ha (hw.goal b hb) hX hW
          (compP_ne_left rev hne')
        obtain ⟨t', ht', ha'⟩ := (next hb hj).opn _ hcs G'' hG'' hnC' hne'
        exact ⟨t', (mem_seqV_two K hK rev wv far).2 ⟨.closed b, hb, .closed c',
          by simp [extendV, hj], ht'⟩, fun p hp => ha' p (hsub hp)⟩
      · obtain ⟨t', ht', ha'⟩ := hw.opn G₁ hG₁ hc₁
          (compP_ne_right rev (compP_ne_left rev hne'))
        obtain ⟨t'', ht'', ha''⟩ := seq_open hL K hK rev wv far C O hfar (y :: zs) (by simp) HW'
          t' _ (adm_comp rev ha') G'' hG'' hne'
        exact ⟨t'', (mem_seqV_two K hK rev wv far).2 ⟨.opn t', ht', .opn t', rfl, ht''⟩,
          fun p hp => ha'' p (hsub hp)⟩

include hL hfar in
/-- The items of a chain, from the items of its members in the order they are
walked. -/
theorem chain_wok {ys : List Rel} (h2 : 2 ≤ ys.length) (HW : Members rev wv C O ys)
    (hns : ∀ x ∈ ys, NotSeq x) (c : Near R) (hc : IsBound D c.bound) :
    WOk rev c.bound (nodeD rev ys) far (chainSet rev C ys) (chainSet rev O ys)
      (seqV K hK rev wv far none c ys) := by
  obtain ⟨x, y, zs, rfl⟩ : ∃ x y zs, ys = x :: y :: zs := by
    match ys, h2 with
    | x :: y :: zs, _ => exact ⟨x, y, zs, rfl⟩
  have hw := HW x (by simp) c none hc (isBound_none D)
  have HW' : Members rev wv C O (y :: zs) := fun z hz => HW z (List.mem_cons_of_mem _ hz)
  have next : ∀ {b : Ans D P}, Item.closed b ∈ wv c x none →
      SOk rev far c.bound b (nodeD rev (x :: y :: zs)) (chainSet rev C (y :: zs))
        (chainSet rev O (y :: zs))
        (seqV K hK rev wv far (some (.closed b)) (nearAfterV D rev (.closed b)) (y :: zs)) := by
    intro b hb
    have hg : b.goal = goalD rev c.bound (nodeD rev [x]) none := by
      rw [hw.goal b hb]; cases rev <;> rfl
    exact seq_closed hL K hK rev wv far C O hfar (y :: zs) (by simp) HW'
      (fun z hz => hns z (List.mem_cons_of_mem _ hz)) [x] b c.bound (by simp)
      (fun z hz => by
        obtain rfl : z = x := by simpa using hz
        exact hns _ (by simp)) hg
  refine ⟨fun a ha => ?_, fun G hG hne => ?_, fun G hG hnC hne => ?_⟩
  · obtain ⟨it, hit, it', he, ha'⟩ := (mem_seqV_two K hK rev wv far).1 ha
    obtain rfl : it = it' := by simpa [extendV] using he
    cases it with
    | closed b => exact (next hit).goal a ha'
    | opn t => exact absurd ha' (seq_noclosed K hK rev wv far _ _ _ _)
  · obtain ⟨G₁, hG₁, G'', hG'', rfl⟩ := hG
    rw [wrapD_comp] at hne ⊢
    obtain ⟨b, hb, hW⟩ := hw.closed G₁ hG₁ (compP_ne_left rev hne)
    obtain ⟨a, ha, hcov⟩ := (next hb).closed _ hW G'' hG'' hne
    exact ⟨a, (mem_seqV_two K hK rev wv far).2 ⟨.closed b, hb, .closed b, rfl, ha⟩, hcov⟩
  · obtain ⟨G₁, hG₁, G'', hG'', rfl⟩ := hG
    rw [wrapD_comp] at hne ⊢
    by_cases hc₁ : G₁ ∈ C x
    · have hnC' : G'' ∉ chainSet rev C (y :: zs) := fun h => hnC ⟨G₁, hc₁, G'', h, rfl⟩
      obtain ⟨b, hb, hW⟩ := hw.closed G₁ hc₁ (compP_ne_left rev hne)
      obtain ⟨t', ht', ha'⟩ := (next hb).opn _ hW G'' hG'' hnC' hne
      exact ⟨t', (mem_seqV_two K hK rev wv far).2 ⟨.closed b, hb, .closed b, rfl, ht'⟩, ha'⟩
    · obtain ⟨t', ht', ha'⟩ := hw.opn G₁ hG₁ hc₁ (compP_ne_left rev hne)
      obtain ⟨t'', ht'', ha''⟩ := seq_open hL K hK rev wv far C O hfar (y :: zs) (by simp) HW'
        t' _ ha' G'' hG'' hne
      exact ⟨t'', (mem_seqV_two K hK rev wv far).2 ⟨.opn t', ht', .opn t', rfl, ht''⟩, ha''⟩

end chain

end Unfold

end Tabled

end RwLog
