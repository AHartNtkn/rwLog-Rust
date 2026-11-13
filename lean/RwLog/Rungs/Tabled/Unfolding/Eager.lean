/-
# The whole unfolding meets the specification of the unfolding race

`POk lb n rb C O ps`: the products `ps` are the unfolding of the goal
`lb ; n ; rb`, where `O` is what the node derives and `C` the derivations
read whole.

* Every closed product is an answer of the goal.
* Every derivation read whole that relates a pair between the boundaries is
  covered by a closed product.
* Every other derivation that relates a pair between the boundaries has an
  open product whose first and last stretch admit its pairs.

`eager_ok`: the products `Unfold.eager` builds are that. So when none is
open, the closed ones cover every derivation of the goal, which is what the
tabled machine asks of the unfolding race (`eagerRace_ok`).
-/
import RwLog.Rungs.Tabled.Unfolding.EagerVal

namespace RwLog

namespace Tabled

namespace Unfold

open Answer Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The products are the unfolding of the goal `lb ; n ; rb`. -/
structure POk (lb : Option R) (n : Rel) (rb : Option R) (C O : Set GRel) (ps : List (Pr D P)) :
    Prop where
  goal : ∀ a ∈ closedOf ps, a.goal = ⟨lb, n, rb⟩
  closed : ∀ G ∈ C, (wrapAt P.sorts.interp lb (G.at P.sorts.interp) rb).Nonempty →
    Cov (closedOf ps) (wrapAt P.sorts.interp lb (G.at P.sorts.interp) rb)
  opn : ∀ G ∈ O, G ∉ C → (wrapAt P.sorts.interp lb (G.at P.sorts.interp) rb).Nonempty →
    ∃ l r, Prod.opn l r ∈ ps ∧ ∀ p ∈ wrapAt P.sorts.interp lb (G.at P.sorts.interp) rb,
      admL P.sorts.interp l p.1 ∧ admR P.sorts.interp r p.2

/-! ## Stretches that meet -/

section glue

variable {M : Interp} (hL : D.Lawful M)
include hL

omit [DecidableEq R] in
theorem glue_left {a : R} {l : Option R} {x m : GTerm} (h₁ : (x, m) ∈ den M a)
    (h₂ : admL M l m) :
    ∃ c, glueV D (some a) l = some (some c) ∧
      ∀ x m, (x, m) ∈ den M a → admL M l m → ∃ u, (x, u) ∈ den M c := by
  cases l with
  | none => exact ⟨a, rfl, fun x m h _ => ⟨m, h⟩⟩
  | some l =>
    obtain ⟨u, hu⟩ := h₂ l rfl
    cases hc : D.compose a l with
    | none =>
      have := hL.compose_none a l hc
      exact absurd (show (x, u) ∈ (den M a).comp (den M l) from ⟨m, h₁, hu⟩)
        (Set.eq_empty_iff_forall_notMem.1 this _)
    | some c =>
      refine ⟨c, by simp [glueV, hc], fun x m h h' => ?_⟩
      obtain ⟨u, hu⟩ := h' l rfl
      exact ⟨u, by rw [hL.compose_some a l c hc]; exact ⟨m, h, hu⟩⟩

omit [DecidableEq R] in
theorem glue_right {r : Option R} {b : R} {m z : GTerm} (h₁ : admR M r m)
    (h₂ : (m, z) ∈ den M b) :
    ∃ c, glueV D r (some b) = some (some c) ∧
      ∀ m z, admR M r m → (m, z) ∈ den M b → ∃ v, (v, z) ∈ den M c := by
  cases r with
  | none => exact ⟨b, rfl, fun m z _ h => ⟨m, h⟩⟩
  | some r =>
    obtain ⟨v, hv⟩ := h₁ r rfl
    cases hc : D.compose r b with
    | none =>
      have := hL.compose_none r b hc
      exact absurd (show (v, z) ∈ (den M r).comp (den M b) from ⟨m, hv, h₂⟩)
        (Set.eq_empty_iff_forall_notMem.1 this _)
    | some c =>
      refine ⟨c, by simp [glueV, hc], fun m z h' h => ?_⟩
      obtain ⟨v, hv⟩ := h' r rfl
      exact ⟨v, by rw [hL.compose_some r b c hc]; exact ⟨m, hv, h⟩⟩

omit [DecidableEq R] in
theorem glue_mid {r l : Option R} {m : GTerm} (h₁ : admR M r m) (h₂ : admL M l m) :
    ∃ g, glueV D r l = some g := by
  cases r with
  | none => exact ⟨_, rfl⟩
  | some r =>
    cases l with
    | none => exact ⟨_, rfl⟩
    | some l =>
      obtain ⟨v, hv⟩ := h₁ r rfl
      obtain ⟨u, hu⟩ := h₂ l rfl
      cases hc : D.compose r l with
      | none =>
        have := hL.compose_none r l hc
        exact absurd (show (v, u) ∈ (den M r).comp (den M l) from ⟨m, hv, hu⟩)
          (Set.eq_empty_iff_forall_notMem.1 this _)
      | some c => exact ⟨some c, by simp [glueV, hc]⟩

end glue

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

/-! ## A chain -/

include hL in
/-- The products of a stretch of a chain followed by the products of the next
member. -/
theorem seq_step {lb rb : Option R} {n₁ n₂ : Rel} {C₁ O₁ C₂ O₂ : Set GRel} {ps qs : List (Pr D P)}
    (h₁ : POk lb n₁ none C₁ O₁ ps) (h₂ : POk none n₂ rb C₂ O₂ qs) :
    POk lb (mkSeq (seqParts n₁ ++ seqParts n₂)) rb (Set.image2 GRel.comp C₁ C₂)
      (Set.image2 GRel.comp O₁ O₂) (ps.flatMap fun p => qs.filterMap (seqProdV K hK p)) := by
  have hmem : ∀ {p q r}, p ∈ ps → q ∈ qs → seqProdV K hK p q = some r →
      r ∈ ps.flatMap fun p => qs.filterMap (seqProdV K hK p) := fun hp hq h =>
    List.mem_flatMap.2 ⟨_, hp, List.mem_filterMap.2 ⟨_, hq, h⟩⟩
  have hsplit : ∀ G₁ G₂ : GRel, wrapAt P.sorts.interp lb ((G₁.comp G₂).at P.sorts.interp) rb =
      (wrapAt P.sorts.interp lb (G₁.at P.sorts.interp) (none : Option R)).comp
        (wrapAt P.sorts.interp (none : Option R) (G₂.at P.sorts.interp) rb) :=
    fun G₁ G₂ => wrap_comp lb rb G₁ G₂
  refine ⟨fun c hc => ?_, ?_, ?_⟩
  · obtain ⟨p, hp, hc⟩ := List.mem_flatMap.1 (mem_closedOf.1 hc)
    obtain ⟨q, hq, hc⟩ := List.mem_filterMap.1 hc
    cases p with
    | closed a =>
      cases q with
      | closed b =>
        simp only [seqProdV, Option.map_eq_some_iff, Prod.closed.injEq] at hc
        obtain ⟨c', hc', rfl⟩ := hc
        obtain ⟨-, -, hg⟩ := (Ans.join_val K hK).1 hc'
        rw [hg, h₁.goal a (mem_closedOf.2 hp), h₂.goal b (mem_closedOf.2 hq)]
      | opn l r => simp [seqProdV] at hc
    | opn l r => cases q <;> simp [seqProdV] at hc
  · rintro G ⟨G₁, hG₁, G₂, hG₂, rfl⟩ hne
    rw [hsplit] at hne ⊢
    have ne₁ : (wrapAt P.sorts.interp lb (G₁.at P.sorts.interp) (none : Option R)).Nonempty := by
      obtain ⟨⟨p, q⟩, m, h, -⟩ := hne; exact ⟨_, h⟩
    have ne₂ : (wrapAt P.sorts.interp (none : Option R) (G₂.at P.sorts.interp) rb).Nonempty := by
      obtain ⟨⟨p, q⟩, m, -, h⟩ := hne; exact ⟨_, h⟩
    obtain ⟨a, ha, hX₁⟩ := h₁.closed G₁ hG₁ ne₁
    obtain ⟨b, hb, hX₂⟩ := h₂.closed G₂ hG₂ ne₂
    obtain ⟨c, hcv, hcs, -⟩ := join_cov hL K hK (a := a) (b := b)
      (.inl ⟨by rw [h₁.goal a ha], .inl (by rw [h₂.goal b hb])⟩) hX₁ hX₂ hne
    exact ⟨c, mem_closedOf.2 (hmem (mem_closedOf.1 ha) (mem_closedOf.1 hb)
      (by simp [seqProdV, hcv])), hcs⟩
  · rintro G ⟨G₁, hG₁, G₂, hG₂, rfl⟩ hnC hne
    rw [hsplit] at hne ⊢
    have ne₁ : (wrapAt P.sorts.interp lb (G₁.at P.sorts.interp) (none : Option R)).Nonempty := by
      obtain ⟨⟨p, q⟩, m, h, -⟩ := hne; exact ⟨_, h⟩
    have ne₂ : (wrapAt P.sorts.interp (none : Option R) (G₂.at P.sorts.interp) rb).Nonempty := by
      obtain ⟨⟨p, q⟩, m, -, h⟩ := hne; exact ⟨_, h⟩
    obtain ⟨⟨x₀, z₀⟩, m₀, hx₀, hz₀⟩ := hne
    by_cases hc₁ : G₁ ∈ C₁
    · have hc₂ : G₂ ∉ C₂ := fun h => hnC ⟨G₁, hc₁, G₂, h, rfl⟩
      obtain ⟨a, ha, hX₁⟩ := h₁.closed G₁ hc₁ ne₁
      obtain ⟨l, r, hlr, hadm⟩ := h₂.opn G₂ hG₂ hc₂ ne₂
      obtain ⟨c, hg, hc⟩ := glue_left hL (hX₁ hx₀) (hadm _ hz₀).1
      refine ⟨some c, r, hmem (mem_closedOf.1 ha) hlr (by simp [seqProdV, hg]), ?_⟩
      rintro ⟨x, z⟩ ⟨m, hx, hz⟩
      exact ⟨fun s hs => by cases hs; exact hc x m (hX₁ hx) (hadm _ hz).1, (hadm _ hz).2⟩
    · obtain ⟨l, r, hlr, hadm⟩ := h₁.opn G₁ hG₁ hc₁ ne₁
      by_cases hc₂ : G₂ ∈ C₂
      · obtain ⟨b, hb, hX₂⟩ := h₂.closed G₂ hc₂ ne₂
        obtain ⟨c, hg, hc⟩ := glue_right hL (hadm _ hx₀).2 (hX₂ hz₀)
        refine ⟨l, some c, hmem hlr (mem_closedOf.1 hb) (by simp [seqProdV, hg]), ?_⟩
        rintro ⟨x, z⟩ ⟨m, hx, hz⟩
        exact ⟨(hadm _ hx).1, fun s hs => by cases hs; exact hc m z (hadm _ hx).2 (hX₂ hz)⟩
      · obtain ⟨l', r', hlr', hadm'⟩ := h₂.opn G₂ hG₂ hc₂ ne₂
        obtain ⟨g, hg⟩ := glue_mid hL (hadm _ hx₀).2 (hadm' _ hz₀).1
        refine ⟨l, r', hmem hlr hlr' (by simp [seqProdV, hg]), ?_⟩
        rintro ⟨x, z⟩ ⟨m, hx, hz⟩
        exact ⟨(hadm _ hx).1, (hadm' _ hz).2⟩

/-- The members of a chain after its first, with their products: each between
no boundaries, but for the right boundary of the last. -/
inductive Tail (rb : Option R) :
    List Rel → List (List (Pr D P)) → List (Set GRel) → List (Set GRel) → Prop
  | last {x : Rel} {q : List (Pr D P)} {C O : Set GRel} : NotSeq x → POk none x rb C O q →
      Tail rb [x] [q] [C] [O]
  | cons {x : Rel} {q : List (Pr D P)} {C O : Set GRel} {xs : List Rel}
      {qs : List (List (Pr D P))} {Cs Os : List (Set GRel)} : NotSeq x →
      POk none x (none : Option R) C O q → Tail rb xs qs Cs Os →
      Tail rb (x :: xs) (q :: qs) (C :: Cs) (O :: Os)

include hL in
theorem seq_fold {lb rb : Option R} {xs : List Rel} {qs : List (List (Pr D P))}
    {Cs Os : List (Set GRel)} (ht : Tail rb xs qs Cs Os) :
    ∀ {pre : List Rel}, pre ≠ [] → (∀ x ∈ pre, NotSeq x) → ∀ {C₀ O₀ : Set GRel}
      {acc : List (Pr D P)}, POk lb (mkSeq pre) none C₀ O₀ acc →
      POk lb (mkSeq (pre ++ xs)) rb (Set.image2 GRel.comp C₀ (RwLog.seqAll Cs))
        (Set.image2 GRel.comp O₀ (RwLog.seqAll Os))
        (qs.foldl (fun acc qs => acc.flatMap fun p => qs.filterMap (seqProdV K hK p)) acc) := by
  induction ht with
  | @last x q C O hx hq =>
    intro pre hpre hns C₀ O₀ acc h₀
    have := seq_step hL K hK h₀ hq
    rw [seqParts_mkSeq hpre hns, seqParts_notSeq hx] at this
    simpa [RwLog.seqAll, GRel.comp_id] using this
  | @cons x q C O xs qs Cs Os hx hq _ ih =>
    intro pre hpre hns C₀ O₀ acc h₀
    have h' := seq_step hL K hK h₀ hq
    rw [seqParts_mkSeq hpre hns, seqParts_notSeq hx] at h'
    have := ih (pre := pre ++ [x]) (by simp)
      (fun y hy => by
        rcases List.mem_append.1 hy with h | h
        · exact hns y h
        · obtain rfl : y = x := by simpa using h
          exact hx) h'
    rw [List.append_assoc, image2_comp_assoc, image2_comp_assoc] at this
    exact this

omit [DecidableEq R] in
/-- The products of the members of a chain after its first are a tail. -/
theorem tail_of {rb : Option R} {N : Nat} (F : Rel × Nat → List (Pr D P)) (C O : Rel → Set GRel) :
    ∀ (tl : List Rel) (k : Nat), tl ≠ [] → k + tl.length = N → (∀ x ∈ tl, NotSeq x) →
      (∀ x ∈ tl, ∀ i, i + 1 < N → k ≤ i →
        POk none x (none : Option R) (C x) (O x) (F (x, i))) →
      (∀ x ∈ tl, POk none x rb (C x) (O x) (F (x, N - 1))) →
      Tail rb tl ((tl.zipIdx k).map F) (tl.map C) (tl.map O)
  | [], _, h, _, _, _, _ => absurd rfl h
  | [x], k, _, hk, hns, _, hl => by
    have hk' : k = N - 1 := by simp at hk; omega
    subst hk'
    exact .last (hns x (by simp)) (hl x (by simp))
  | x :: y :: tl, k, _, hk, hns, hm, hl => by
    refine .cons (hns x (by simp)) (hm x (by simp) k (by simp at hk; omega) le_rfl) ?_
    exact tail_of F C O (y :: tl) (k + 1) (by simp) (by simp at hk ⊢; omega)
      (fun z hz => hns z (List.mem_cons_of_mem _ hz))
      (fun z hz i hi hki => hm z (List.mem_cons_of_mem _ hz) i hi (by omega))
      (fun z hz => hl z (List.mem_cons_of_mem _ hz))

/-! ## A rule applied to the answers, and a union -/

omit [DecidableEq R] in
theorem POk.of_eq {lb rb : Option R} {n : Rel} {C O C' O' : Set GRel} {ps : List (Pr D P)}
    (h : POk lb n rb C O ps) (hC : C' = C) (hO : O' = O) : POk lb n rb C' O' ps :=
  hC ▸ hO ▸ h

omit [DecidableEq R] in
theorem lift_ok {lb rb : Option R} {b n : Rel} {C O : Set GRel} {ps : List (Pr D P)}
    {f : Ans D P → Option (Ans D P)} (h : POk lb b rb C O ps)
    (hf₁ : ∀ a c, f a = some c → c.goal = ⟨a.goal.lb, n, a.goal.rb⟩)
    (hf₂ : ∀ a, a.goal = ⟨lb, b, rb⟩ → ∃ c, f a = some c ∧ c.span = a.span) :
    POk lb n rb C O (liftV f ps) := by
  have hcl : ∀ c, .closed c ∈ liftV f ps ↔ ∃ a, .closed a ∈ ps ∧ f a = some c := by
    intro c
    unfold liftV
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨p, hp, e⟩
      cases p with
      | closed a =>
        simp only [Option.map_eq_some_iff, Prod.closed.injEq] at e
        obtain ⟨c', hc', rfl⟩ := e
        exact ⟨a, hp, hc'⟩
      | opn l r => simp at e
    · rintro ⟨a, ha, e⟩
      exact ⟨_, ha, by simp [e]⟩
  refine ⟨fun c hc => ?_, fun G hG hne => ?_, fun G hG hnC hne => ?_⟩
  · obtain ⟨a, ha, e⟩ := (hcl c).1 (mem_closedOf.1 hc)
    rw [hf₁ a c e, h.goal a (mem_closedOf.2 ha)]
  · obtain ⟨a, ha, hX⟩ := h.closed G hG hne
    obtain ⟨c, hc, hs⟩ := hf₂ a (h.goal a ha)
    exact ⟨c, mem_closedOf.2 ((hcl c).2 ⟨a, mem_closedOf.1 ha, hc⟩), by rw [hs]; exact hX⟩
  · obtain ⟨l, r, hlr, hadm⟩ := h.opn G hG hnC hne
    exact ⟨l, r, List.mem_filterMap.2 ⟨_, hlr, rfl⟩, hadm⟩

omit [DecidableEq R] in
theorem union_ok {ι : Type} {lb rb : Option R} {n : Rel} (L : List ι) (C O : ι → Set GRel)
    (ps : ι → List (Pr D P)) (h : ∀ i ∈ L, POk lb n rb (C i) (O i) (ps i)) :
    POk lb n rb {G | ∃ i ∈ L, G ∈ C i} {G | ∃ i ∈ L, G ∈ O i} (L.flatMap ps) := by
  refine ⟨fun c hc => ?_, ?_, ?_⟩
  · obtain ⟨i, hi, hc⟩ := List.mem_flatMap.1 (mem_closedOf.1 hc)
    exact (h i hi).goal c (mem_closedOf.2 hc)
  · rintro G ⟨i, hi, hG⟩ hne
    exact ((h i hi).closed G hG hne).mono
      (fun a ha => mem_closedOf.2 (List.mem_flatMap.2 ⟨i, hi, mem_closedOf.1 ha⟩)) subset_rfl
  · rintro G ⟨i, hi, hG⟩ hnC hne
    obtain ⟨l, r, hlr, hadm⟩ := (h i hi).opn G hG (fun hc => hnC ⟨i, hi, hc⟩) hne
    exact ⟨l, r, List.mem_flatMap.2 ⟨i, hi, hlr⟩, hadm⟩

/-! ## A meet -/

/-- The answers are the closed products of the goal `lb ; n ; rb`. -/
structure MOk (lb : Option R) (n : Rel) (rb : Option R) (C : Set GRel) (as : List (Ans D P)) :
    Prop where
  goal : ∀ a ∈ as, a.goal = ⟨lb, n, rb⟩
  closed : ∀ G ∈ C, (wrapAt P.sorts.interp lb (G.at P.sorts.interp) rb).Nonempty →
    Cov as (wrapAt P.sorts.interp lb (G.at P.sorts.interp) rb)

omit [DecidableEq R] in
theorem POk.mok {lb rb : Option R} {n : Rel} {C O : Set GRel} {ps : List (Pr D P)}
    (h : POk lb n rb C O ps) : MOk lb n rb C (closedOf ps) := ⟨h.goal, h.closed⟩

include hL in
theorem meet_step {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb) {n₁ n₂ : Rel}
    {C₁ C₂ : Set GRel} {as bs : List (Ans D P)} (h₁ : MOk lb n₁ rb C₁ as)
    (h₂ : MOk lb n₂ rb C₂ bs) :
    MOk lb (mkAnd (sortedParts (andParts n₁ ++ andParts n₂))) rb (Set.image2 GRel.meet C₁ C₂)
      (as.flatMap fun a => bs.filterMap fun b => (Ans.meetA D P K hK a b).val) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · obtain ⟨a, ha, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨b, hb, hc⟩ := List.mem_filterMap.1 hc
    obtain ⟨-, -, hg⟩ := (Ans.meetA_val K hK).1 hc
    rw [hg, h₁.goal a ha, h₂.goal b hb]
  · rintro G ⟨G₁, hG₁, G₂, hG₂, rfl⟩ hne
    rw [wrap_meet hL hl hr] at hne ⊢
    obtain ⟨a, ha, hX₁⟩ := h₁.closed G₁ hG₁ (hne.mono Set.inter_subset_left)
    obtain ⟨b, hb, hX₂⟩ := h₂.closed G₂ hG₂ (hne.mono Set.inter_subset_right)
    obtain ⟨c, hcv, hcs, -⟩ := meet_cov hL K hK (a := a) (b := b)
      (.inl ⟨by rw [h₁.goal a ha, h₂.goal b hb], by rw [h₁.goal a ha, h₂.goal b hb]⟩) hX₁ hX₂ hne
    exact ⟨c, List.mem_flatMap.2 ⟨a, ha, List.mem_filterMap.2 ⟨b, hb, hcv⟩⟩, hcs⟩

include hL in
theorem meet_fold {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb)
    (A : Rel → List (Ans D P)) (C : Rel → Set GRel) (tl : List Rel) :
    (∀ x ∈ tl, NotAnd x ∧ MOk lb x rb (C x) (A x)) → ∀ {pre : List Rel}, pre ≠ [] →
      (∀ x ∈ pre, NotAnd x) → ∀ {C₀ : Set GRel} {acc : List (Ans D P)},
      MOk lb (mkAnd (sortedParts pre)) rb C₀ acc →
      MOk lb (mkAnd (sortedParts (pre ++ tl))) rb
        (Set.image2 GRel.meet C₀ (RwLog.andAll (tl.map C)))
        ((tl.map A).foldl (fun acc bs => acc.flatMap fun a => bs.filterMap fun b =>
          (Ans.meetA D P K hK a b).val) acc) := by
  induction tl with
  | nil =>
    intro _ pre _ _ C₀ acc h₀
    simpa [RwLog.andAll, GRel.meet_top] using h₀
  | cons x tl ih =>
    intro h pre hpre hns C₀ acc h₀
    have hx := h x (by simp)
    have h' := meet_step hL K hK hl hr h₀ hx.2
    rw [andParts_mkAnd (sortedParts_ne_nil hpre)
        (fun z hz => hns z ((sortedParts_perm _).mem_iff.1 hz)),
      andParts_notAnd hx.1, sortedParts_eq ((sortedParts_perm pre).append_right [x])] at h'
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) (pre := pre ++ [x]) (by simp)
      (fun y hy => by
        rcases List.mem_append.1 hy with h'' | h''
        · exact hns y h''
        · obtain rfl : y = x := by simpa using h''
          exact hx.1) h'
    rw [List.append_assoc, image2_meet_assoc] at this
    exact this

theorem andAll_sub (M : Interp) (O : Rel → Set GRel) : ∀ (xs : List Rel) (G : GRel),
    G ∈ RwLog.andAll (xs.map O) → ∀ x ∈ xs, ∃ g ∈ O x, G.at M ⊆ g.at M
  | [], _, _, x, hx => by cases hx
  | y :: xs, G, hG, x, hx => by
    obtain ⟨g, hg, G', hG', rfl⟩ := hG
    rw [at_meet]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨g, hg, Set.inter_subset_left⟩
    · obtain ⟨g', hg', hs⟩ := andAll_sub M O xs G' hG' x hx
      exact ⟨g', hg', Set.inter_subset_right.trans hs⟩

theorem andAll_cases (M : Interp) (C O : Rel → Set GRel) : ∀ (xs : List Rel) (G : GRel),
    G ∈ RwLog.andAll (xs.map O) →
      G ∈ RwLog.andAll (xs.map C) ∨ ∃ x ∈ xs, ∃ g ∈ O x, g ∉ C x ∧ G.at M ⊆ g.at M
  | [], _, hG => .inl hG
  | y :: xs, G, hG => by
    obtain ⟨g, hg, G', hG', rfl⟩ := hG
    by_cases hc : g ∈ C y
    · rcases andAll_cases M C O xs G' hG' with h | ⟨x, hx, g', hg', hn, hs⟩
      · exact .inl ⟨g, hc, G', h, rfl⟩
      · exact .inr ⟨x, List.mem_cons_of_mem _ hx, g', hg', hn, by
          rw [at_meet]; exact Set.inter_subset_right.trans hs⟩
    · exact .inr ⟨y, by simp, g, hg, hc, by rw [at_meet]; exact Set.inter_subset_left⟩

omit [DecidableEq R] in
theorem any_isOpn {ps : List (Pr D P)} :
    ps.any Prod.isOpn = true ↔ ∃ l r, Prod.opn l r ∈ ps := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, h⟩
    cases p with
    | closed a => cases h
    | opn l r => exact ⟨l, r, hp⟩
  · rintro ⟨l, r, h⟩
    exact ⟨_, h, rfl⟩

include hL in
/-- The products of a meet from the products of its members. -/
theorem meet_ok {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb) {xs : List Rel}
    (h2 : 2 ≤ xs.length) (hna : ∀ x ∈ xs, NotAnd x) (hs : xs.Pairwise RelLE)
    (C O : Rel → Set GRel) (F : Rel → List (Pr D P))
    (h : ∀ x ∈ xs, POk lb x rb (C x) (O x) (F x)) :
    POk lb (mkAnd xs) rb (RwLog.andAll (xs.map C)) (RwLog.andAll (xs.map O))
      ((meetAllV K hK ((xs.map F).map closedOf)).map .closed ++
        if ((xs.map F).all fun ps => !ps.isEmpty) && ((xs.map F).any fun ps => ps.any Prod.isOpn)
        then [.opn lb rb] else []) := by
  obtain ⟨x₀, tl, rfl⟩ : ∃ x₀ tl, xs = x₀ :: tl := by
    cases xs with
    | nil => simp at h2
    | cons a b => exact ⟨a, b, rfl⟩
  have hm : MOk lb (mkAnd (x₀ :: tl)) rb (RwLog.andAll ((x₀ :: tl).map C))
      (meetAllV K hK (((x₀ :: tl).map F).map closedOf)) := by
    have h₀ : MOk lb (mkAnd (sortedParts [x₀])) rb (C x₀) (closedOf (F x₀)) := by
      rw [sortedParts_of_sorted (List.pairwise_singleton _ _)]
      exact (h x₀ (by simp)).mok
    have := meet_fold hL K hK hl hr (fun x => closedOf (F x)) C tl
      (fun x hx => ⟨hna x (List.mem_cons_of_mem _ hx), (h x (List.mem_cons_of_mem _ hx)).mok⟩)
      (pre := [x₀]) (by simp)
      (fun y hy => by
        obtain rfl : y = x₀ := by simpa using hy
        exact hna _ (by simp)) h₀
    rw [List.singleton_append, sortedParts_of_sorted hs] at this
    have e : ((x₀ :: tl).map F).map closedOf =
        closedOf (F x₀) :: tl.map fun x => closedOf (F x) := by simp
    rw [e]
    exact this
  refine ⟨fun c hc => ?_, fun G hG hne => ?_, fun G hG hnC hne => ?_⟩
  · refine hm.goal c ?_
    rcases List.mem_append.1 (mem_closedOf.1 hc) with h' | h'
    · obtain ⟨a, ha, e⟩ := List.mem_map.1 h'
      cases e
      exact ha
    · split at h' <;> simp at h'
  · obtain ⟨a, ha, hX⟩ := hm.closed G hG hne
    exact ⟨a, mem_closedOf.2 (List.mem_append_left _ (List.mem_map_of_mem ha)), hX⟩
  · refine ⟨lb, rb, List.mem_append_right _ ?_, fun ⟨x, z⟩ hp => ⟨admL_bound hp, admR_bound hp⟩⟩
    have hsub := andAll_sub P.sorts.interp O _ G hG
    have hall : ((x₀ :: tl).map F).all (fun ps => !ps.isEmpty) = true := by
      rw [List.all_eq_true]
      intro ps hps
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hps
      obtain ⟨g, hg, hs'⟩ := hsub x hx
      have ne := hne.mono (wrap_mono hs')
      by_cases hc : g ∈ C x
      · obtain ⟨a, ha, -⟩ := (h x hx).closed g hc ne
        have := mem_closedOf.1 ha
        cases hF : F x with
        | nil => rw [hF] at this; cases this
        | cons _ _ => rfl
      · obtain ⟨l, r, hlr, -⟩ := (h x hx).opn g hg hc ne
        cases hF : F x with
        | nil => rw [hF] at hlr; cases hlr
        | cons _ _ => rfl
    have hany : ((x₀ :: tl).map F).any (fun ps => ps.any Prod.isOpn) = true := by
      rcases andAll_cases P.sorts.interp C O _ G hG with hc | ⟨x, hx, g, hg, hn, hs'⟩
      · exact absurd hc hnC
      · obtain ⟨l, r, hlr, -⟩ := (h x hx).opn g hg hn (hne.mono (wrap_mono hs'))
        exact List.any_eq_true.2 ⟨F x, List.mem_map_of_mem hx, any_isOpn.2 ⟨l, r, hlr⟩⟩
    rw [hall, hany]
    simp

/-! ## The whole unfolding -/

include hL in
/-- The products `Unfold.eager` builds are the unfolding of the goal. -/
theorem eager_ok (hP : ProgFO P) : ∀ (d : Nat) (lb : Option R) (n : Rel) (rb : Option R),
    IsBound D lb → IsBound D rb → Normal n → n.FO →
    POk lb n rb (GR P d n) (GD P n) (eager (K := DerivationKernel.over D K hK P) d lb n rb).val
  | 0, lb, n, rb, _, _, _, _ => by
    rw [eager_zero]
    exact ⟨fun a ha => by simp [closedOf] at ha, fun G hG => by simp at hG,
      fun G _ _ _ => ⟨lb, rb, by simp, fun ⟨x, z⟩ hp => ⟨admL_bound hp, admR_bound hp⟩⟩⟩
  | d + 1, lb, n, rb, hl, hr, hn, hfo => by
    cases hv : n.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      rw [eager_span K hK d lb _ rb hv, gr_span P hv, (gd_laws P).span]
      have hfo' : s.firstOrder = true := hfo s (by simp [RelOf.spans])
      have hden := denO_spanBoth hL hfo' lb rb
      refine ⟨fun c hc => ?_, fun G hG hne => ?_, fun G hG hnC _ => absurd hG hnC⟩
      · obtain ⟨a, ha, e⟩ := List.mem_map.1 (mem_closedOf.1 hc)
        cases e
        obtain ⟨s', hs, -, -, -, hcg⟩ := (Ans.leaf_val K hK).1 (Option.mem_toList.1 ha)
        rw [hcg, ← hs]
      · obtain rfl : G = s.den := hG
        cases hsb : spanBoth D lb s rb with
        | none =>
          rw [hsb, Domain.denO_none] at hden
          exact absurd hden.symm hne.ne_empty
        | some z =>
          rw [hsb, Domain.denO_some] at hden
          obtain ⟨c, hc, hcs, -⟩ := Ans.leaf_ok (P := P) K hK hl hr hsb
          exact ⟨c, mem_closedOf.2 (List.mem_map_of_mem (by rw [hc]; simp)), by
            rw [hcs, hden]⟩
    | call m f =>
      obtain ⟨b, hb⟩ := forget_call (P := P) hv
      rw [eager_call K hK d lb n rb hv hb, gr_call P hv hb, gd_of_body P hb]
      refine lift_ok (eager_ok hP d lb b rb hl hr (bodyOf_normal hb) (bodyOf_fo hP hb))
        (fun a c e => (Ans.unfold_val.1 e).2.2) (fun a ha => ?_)
      obtain ⟨c, hc, hs, -⟩ := Ans.unfold_ok (a := a) (n := n) (by rw [hb, ha])
      exact ⟨c, hc, hs⟩
    | union xs =>
      have hvu := forget_union hv
      have hparts := hn.view_union_eq hvu
      rw [eager_union K hK d lb n rb hv, gr_union P hv]
      have hzip : ∀ (S : Rel → Set GRel) (G : GRel),
          (∃ p ∈ xs.zipIdx, G ∈ S p.1) ↔ ∃ x ∈ xs, G ∈ S x := by
        intro S G
        constructor
        · rintro ⟨⟨x, i⟩, hp, hG⟩
          exact ⟨x, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp), hG⟩
        · rintro ⟨x, hx, hG⟩
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
          exact ⟨(x, i), List.mem_zipIdx_iff_getElem?.2 hi, hG⟩
      refine (union_ok (lb := lb) (rb := rb) (n := n) xs.zipIdx (fun p => GR P d p.1)
        (fun p => GD P p.1)
        (fun p => liftV (fun a => (Ans.inj D P a n p.2).val)
          (eager (K := DerivationKernel.over D K hK P) d lb p.1 rb).val) (fun p hp => ?_)).of_eq
        (by ext G; exact (hzip _ G).symm)
        (by ext G; rw [gd_of_union P hn hvu]; exact (hzip _ G).symm)
      have hx : xs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hp
      have hm : p.1 ∈ n.view.members := by rw [hvu]; exact List.mem_of_getElem? hx
      refine lift_ok (eager_ok hP d lb p.1 rb hl hr (hn.view_members hm) (hfo.view_members hm))
        (fun a c e => (Ans.inj_val.1 e).2.2) (fun a ha => ?_)
      obtain ⟨c, hc, hs, -⟩ := Ans.inj_ok (a := a) (u := n) (i := p.2) (by
        rw [← hparts, ha]; exact hx)
      exact ⟨c, hc, hs⟩
    | chain xs =>
      have hvc := forget_chain hv
      obtain ⟨h2, hmem, hmk⟩ := hn.view_chain hvc
      rw [eager_chain K hK d lb n rb hv, gr_chain P hv, gd_of_chain P hvc]
      obtain ⟨x₀, tl, rfl⟩ : ∃ x₀ tl, xs = x₀ :: tl := by
        cases xs with
        | nil => simp at h2
        | cons a b => exact ⟨a, b, rfl⟩
      have htl : 0 < tl.length := by simp at h2; omega
      have hin : ∀ x ∈ x₀ :: tl, Normal x ∧ x.FO := fun x hx =>
        ⟨(hmem x hx).1, hfo.view_members (by rw [hvc]; exact hx)⟩
      have ht := tail_of (rb := rb) (N := tl.length + 1)
        (fun p => (eager (K := DerivationKernel.over D K hK P) d (if p.2 = 0 then lb else none) p.1
          (if p.2 + 1 = tl.length + 1 then rb else none)).val) (GR P d) (GD P) tl 1
        (List.ne_nil_of_length_pos htl) (by omega)
        (fun x hx => (hmem x (List.mem_cons_of_mem _ hx)).2)
        (fun x hx i hi hki => by
          have e₁ : (if i = 0 then lb else none) = none := by
            simp only [ite_eq_right_iff]; intro h; omega
          have e₂ : (if i + 1 = tl.length + 1 then rb else none) = none := by
            simp only [ite_eq_right_iff]; intro h; omega
          show POk none x none _ _ (eager (K := DerivationKernel.over D K hK P) d
            (if i = 0 then lb else none) x (if i + 1 = tl.length + 1 then rb else none)).val
          rw [e₁, e₂]
          exact eager_ok hP d none x none (isBound_none D) (isBound_none D)
            (hin x (List.mem_cons_of_mem _ hx)).1 (hin x (List.mem_cons_of_mem _ hx)).2)
        (fun x hx => by
          have e₁ : (if tl.length + 1 - 1 = 0 then lb else none) = none := by
            simp only [ite_eq_right_iff]; intro h; omega
          have e₂ : (if tl.length + 1 - 1 + 1 = tl.length + 1 then rb else none) = rb := by
            simp only [ite_eq_left_iff]; intro h; omega
          show POk none x rb _ _ (eager (K := DerivationKernel.over D K hK P) d
            (if tl.length + 1 - 1 = 0 then lb else none) x
            (if tl.length + 1 - 1 + 1 = tl.length + 1 then rb else none)).val
          rw [e₁, e₂]
          exact eager_ok hP d none x rb (isBound_none D) hr
            (hin x (List.mem_cons_of_mem _ hx)).1 (hin x (List.mem_cons_of_mem _ hx)).2)
      have h₀ : POk lb (mkSeq [x₀]) none (GR P d x₀) (GD P x₀)
          (eager (K := DerivationKernel.over D K hK P) d lb x₀ none).val :=
        eager_ok hP d lb x₀ none hl (isBound_none D) (hin x₀ (by simp)).1 (hin x₀ (by simp)).2
      have := seq_fold hL K hK ht (pre := [x₀]) (by simp)
        (fun y hy => by
          obtain rfl : y = x₀ := by simpa using hy
          exact (hmem _ (by simp)).2) h₀
      rw [List.singleton_append, hmk] at this
      have e₂ : (if 0 + 1 = tl.length + 1 then rb else none) = none := by
        simp only [ite_eq_right_iff]; intro h; omega
      simp only [List.zipIdx_cons, List.map_cons, seqAllV, ite_true, List.length_cons]
      rw [e₂]
      exact this
    | meet xs =>
      have hvm := forget_meet hv
      obtain ⟨h2, hmem, hs, hmk⟩ := hn.view_meet hvm
      rw [eager_meet K hK d lb n rb hv, gr_meet P hv, gd_of_meet P hvm]
      have := meet_ok hL K hK hl hr h2 (fun x hx => (hmem x hx).2) hs (GR P d) (GD P)
        (fun x => (eager (K := DerivationKernel.over D K hK P) d lb x rb).val)
        (fun x hx => eager_ok hP d lb x rb hl hr (hmem x hx).1
          (hfo.view_members (by rw [hvm]; exact hx)))
      rw [hmk] at this
      exact this

/-! ## The race -/

/-- Add an answer unless one with the same representative is there. -/
def keepNew (xs : List (Ans D P)) (x : Ans D P) : List (Ans D P) :=
  if xs.any (fun y => decide (y.span = x.span)) then xs else xs ++ [x]

theorem keepNew_spec : ∀ (as acc : List (Ans D P)),
    (∀ b ∈ as.foldl keepNew acc, b ∈ acc ∨ b ∈ as) ∧
      ∀ a, a ∈ acc ∨ a ∈ as → ∃ b ∈ as.foldl keepNew acc, b.span = a.span
  | [], acc => ⟨fun b hb => .inl hb, fun a ha => ⟨a, by simpa using ha, rfl⟩⟩
  | x :: as, acc => by
    simp only [List.foldl_cons]
    obtain ⟨h₁, h₂⟩ := keepNew_spec as (keepNew acc x)
    have hsub : ∀ a ∈ acc, a ∈ keepNew acc x := by
      intro a ha
      unfold keepNew
      split <;> simp [ha]
    refine ⟨fun b hb => ?_, fun a ha => ?_⟩
    · rcases h₁ b hb with h | h
      · unfold keepNew at h
        split at h
        · exact .inl h
        · rcases List.mem_append.1 h with h | h
          · exact .inl h
          · exact .inr (by simp at h; simp [h])
      · exact .inr (List.mem_cons_of_mem _ h)
    · rcases ha with ha | ha
      · exact h₂ a (.inl (hsub a ha))
      · rcases List.mem_cons.1 ha with rfl | ha
        · by_cases hany : acc.any (fun y => decide (y.span = a.span)) = true
          · obtain ⟨y, hy, e⟩ := List.any_eq_true.1 hany
            obtain ⟨b, hb, hbs⟩ := h₂ y (.inl (hsub y hy))
            exact ⟨b, hb, hbs.trans (of_decide_eq_true e)⟩
          · exact h₂ a (.inl (by simp [keepNew, hany]))
        · exact h₂ a (.inr ha)

theorem eagerRace_val (d : Nat) (g : GoalOf R Rel) :
    (eagerRace (K := DerivationKernel.over D K hK P) d g).val =
      if (eager (K := DerivationKernel.over D K hK P) d g.lb g.node g.rb).val.any Prod.isOpn
      then (false, [])
      else (true, (closedOf
        (eager (K := DerivationKernel.over D K hK P) d g.lb g.node g.rb).val).foldl keepNew []) := by
  have ek : ∀ xs x, (addAns (K := DerivationKernel.over D K hK P) xs x).val = keepNew xs x := by
    intro xs x
    at_cost K hK
    simp only [addAns, keepNew, Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val, hK.eq,
      over_span]
  at_cost K hK
  simp only [eagerRace, Cost.bind_val]
  split <;> simp only [Cost.bind_val, Cost.pure_val, foldL_std, Cost.foldL_val, ek]

include hL in
/-- Building the whole unfolding answers the unfolding race. -/
theorem eagerRace_ok (hP : ProgFO P) :
    UOk D P (eagerRace (K := DerivationKernel.over D K hK P)) := by
  refine ⟨fun d g hg a ha => ?_, fun d g hg hfin k G hG hne => ?_⟩
  · rw [eagerRace_val] at ha
    split at ha
    · cases ha
    · exact (eager_ok hL K hK hP d g.lb g.node g.rb hg.lb hg.rb hg.normal hg.fo).goal a
        (((keepNew_spec _ []).1 a ha).resolve_left (by simp))
  · have ok := eager_ok hL K hK hP d g.lb g.node g.rb hg.lb hg.rb hg.normal hg.fo
    by_cases hop :
        (eager (K := DerivationKernel.over D K hK P) d g.lb g.node g.rb).val.any Prod.isOpn = true
    · rw [eagerRace_val] at hfin
      simp only [hop, reduceIte] at hfin
      cases hfin
    · rw [eagerRace_val]
      simp only [hop]
      by_cases hc : G ∈ GR P d g.node
      · obtain ⟨a, ha, hX⟩ := ok.closed G hc hne
        obtain ⟨b, hb, hbs⟩ := (keepNew_spec _ []).2 a (.inr ha)
        exact ⟨b, hb, by rw [hbs]; exact hX⟩
      · obtain ⟨l, r, hlr, -⟩ := ok.opn G (gdn_sub_gd k _ hG) hc hne
        exact absurd (any_isOpn.2 ⟨l, r, hlr⟩) hop

end Unfold

end Tabled

end RwLog
