/-
# The two directions of a walk

A walk goes through a chain from its first member to its last, or with `rev`
from its last to its first. The boundary on the side it comes from is the
*near* one and the other the *far* one. This file states, for both
directions at once, what the walk is about: the pairs between a near and a
far boundary (`wrapD`), the goal between them (`goalD`), what was walked
first followed by what was walked after it (`compP`, `compG`, `catD`), and
what the far stretch of an open product says of a pair (`admD`).

The lemmas are the two directions of facts about `wrapAt`, the rule `join`
and the rule `meetA`.
-/
import RwLog.Rungs.Tabled.Unfolding.WalkVal

namespace RwLog

namespace Tabled

namespace Unfold

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## Pairs, goals and derivations in the direction of a walk -/

/-- The pairs of `X` between the near and the far boundary. -/
def wrapD (M : Interp) (rev : Bool) (near : Option R) (X : PRel) (far : Option R) : PRel :=
  if rev then wrapAt M far X near else wrapAt M near X far

/-- The goal between the near and the far boundary. -/
def goalD (rev : Bool) (near : Option R) (n : Rel) (far : Option R) : Goal R :=
  if rev then ⟨far, n, near⟩ else ⟨near, n, far⟩

/-- The far stretch of an open product relates the far end of the pair to
something. -/
def admD (M : Interp) (rev : Bool) (t : Option R) (p : GTerm × GTerm) : Prop :=
  if rev then admL M t p.1 else admR M t p.2

/-- What was walked first, followed by what was walked after it. -/
def compP (rev : Bool) (X Y : PRel) : PRel := if rev then Y.comp X else X.comp Y

/-- What was walked first, followed by what was walked after it. -/
def compG (rev : Bool) (G₁ G₂ : GRel) : GRel := if rev then G₂.comp G₁ else G₁.comp G₂

/-- The chain of what was walked first and what was walked after it. -/
def catD (rev : Bool) (n₁ n₂ : Rel) : Rel :=
  mkSeq (if rev then seqParts n₂ ++ seqParts n₁ else seqParts n₁ ++ seqParts n₂)

/-- The chain of the members in the order they are walked. -/
def nodeD (rev : Bool) (ys : List Rel) : Rel := mkSeq (if rev then ys.reverse else ys)

/-- What a far stretch pushes into the next member. -/
def nearB (D : Domain R) (rev : Bool) : Option R → Option R
  | none => none
  | some t => farBoundV D rev t

omit [DecidableEq R] in
theorem nearB_isBound {M : Interp} (hL : D.Lawful M) (rev : Bool) (t : Option R) :
    IsBound D (nearB D rev t) := by
  cases t with
  | none => exact isBound_none D
  | some s => cases rev <;> exact isBound_right hL _

omit [DecidableEq R] in
theorem nearAfterV_bound (rev : Bool) (t : Option R) :
    (nearAfterV (P := P) D rev (.opn t)).bound = nearB D rev t := by
  cases t <;> rfl

section

variable {M : Interp}

omit [DecidableEq R] in
theorem wrapD_comp (rev : Bool) (near far : Option R) (G₁ G₂ : GRel) :
    wrapD M rev near ((compG rev G₁ G₂).at M) far =
      compP rev (wrapD M rev near (G₁.at M) none) (wrapD M rev none (G₂.at M) far) := by
  cases rev
  · exact wrap_comp near far G₁ G₂
  · exact wrap_comp far near G₂ G₁

omit [DecidableEq R] in
theorem wrapD_mono (rev : Bool) (near far : Option R) {X Y : PRel} (h : X ⊆ Y) :
    wrapD M rev near X far ⊆ wrapD M rev near Y far := by
  cases rev <;> exact wrap_mono h

omit [DecidableEq R] in
theorem wrapD_meet (hL : D.Lawful M) (rev : Bool) {near far : Option R} (hn : IsBound D near)
    (hf : IsBound D far) (G₁ G₂ : GRel) :
    wrapD M rev near ((G₁.meet G₂).at M) far =
      wrapD M rev near (G₁.at M) far ∩ wrapD M rev near (G₂.at M) far := by
  cases rev
  · exact wrap_meet hL hn hf G₁ G₂
  · exact wrap_meet hL hf hn G₁ G₂

omit [DecidableEq R] in
/-- A boundary only takes pairs away. -/
theorem wrapD_none_sub (hL : D.Lawful M) (rev : Bool) {near : Option R} (hn : IsBound D near)
    (X : PRel) (far : Option R) : wrapD M rev near X far ⊆ wrapD M rev none X far := by
  cases rev
  · rintro ⟨x, z⟩ h
    obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 h
    obtain rfl := bden_eq hL hn q₁
    exact mem_wrapAt.2 ⟨_, v, rfl, q₂, q₃⟩
  · rintro ⟨x, z⟩ h
    obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 h
    obtain rfl := bden_eq hL hn q₃
    exact mem_wrapAt.2 ⟨u, _, q₁, q₂, rfl⟩

theorem compP_mono (rev : Bool) {X X' Y Y' : PRel} (h₁ : X ⊆ X') (h₂ : Y ⊆ Y') :
    compP rev X Y ⊆ compP rev X' Y' := by
  cases rev
  · rintro ⟨x, z⟩ ⟨m, p, q⟩; exact ⟨m, h₁ p, h₂ q⟩
  · rintro ⟨x, z⟩ ⟨m, p, q⟩; exact ⟨m, h₂ p, h₁ q⟩

theorem compP_ne_right (rev : Bool) {X Y : PRel} (h : (compP rev X Y).Nonempty) : Y.Nonempty := by
  cases rev
  · obtain ⟨⟨x, z⟩, m, -, q⟩ := h; exact ⟨_, q⟩
  · obtain ⟨⟨x, z⟩, m, p, -⟩ := h; exact ⟨_, p⟩

theorem compP_ne_left (rev : Bool) {X Y : PRel} (h : (compP rev X Y).Nonempty) : X.Nonempty := by
  cases rev
  · obtain ⟨⟨x, z⟩, m, p, -⟩ := h; exact ⟨_, p⟩
  · obtain ⟨⟨x, z⟩, m, -, q⟩ := h; exact ⟨_, q⟩

theorem compP_assoc (rev : Bool) (X Y Z : PRel) :
    compP rev (compP rev X Y) Z = compP rev X (compP rev Y Z) := by
  cases rev
  · exact PRel.comp_assoc X Y Z
  · exact (PRel.comp_assoc Z Y X).symm

omit [DecidableEq R] in
/-- What a far stretch pushes into the next member takes no pair away from
what follows it. -/
theorem push_sub (hL : D.Lawful M) (rev : Bool) {t : Option R} {X₀ : PRel}
    (h : ∀ p ∈ X₀, admD M rev t p) (Y : PRel) (fr : Option R) :
    compP rev X₀ (wrapD M rev none Y fr) ⊆ compP rev X₀ (wrapD M rev (nearB D rev t) Y fr) := by
  cases rev
  · rintro ⟨x, z⟩ ⟨m, h₁, h₂⟩
    refine ⟨m, h₁, ?_⟩
    obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 h₂
    obtain rfl : u = m := q₁
    refine mem_wrapAt.2 ⟨u, v, ?_, q₂, q₃⟩
    have ha : admR M t u := h _ h₁
    cases t with
    | none => rfl
    | some s =>
      obtain ⟨w, hw⟩ := ha s rfl
      exact rightBound_at hL hw
  · rintro ⟨x, z⟩ ⟨m, h₂, h₁⟩
    refine ⟨m, ?_, h₁⟩
    obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 h₂
    obtain rfl : m = v := q₃
    refine mem_wrapAt.2 ⟨u, m, q₁, q₂, ?_⟩
    have ha : admL M t m := h _ h₁
    cases t with
    | none => rfl
    | some s =>
      obtain ⟨w, hw⟩ := ha s rfl
      exact leftBound_at hL hw

omit [DecidableEq R] in
theorem adm_comp (rev : Bool) {t : Option R} {X₀ W : PRel} (h : ∀ q ∈ W, admD M rev t q) :
    ∀ p ∈ compP rev X₀ W, admD M rev t p := by
  cases rev
  · rintro ⟨x, z⟩ ⟨m, -, q⟩; exact h (m, z) q
  · rintro ⟨x, z⟩ ⟨m, q, -⟩; exact h (x, m) q

omit [DecidableEq R] in
theorem adm_mem (rev : Bool) {b : R} {q : GTerm × GTerm} (h : q ∈ den M b) :
    admD M rev (some b) q := by
  cases rev
  · intro s hs; cases hs; exact ⟨q.1, h⟩
  · intro s hs; cases hs; exact ⟨q.2, h⟩

omit [DecidableEq R] in
theorem adm_far (rev : Bool) {near far : Option R} {X : PRel} {p : GTerm × GTerm}
    (h : p ∈ wrapD M rev near X far) : admD M rev far p := by
  cases rev
  · exact admR_bound (x := p.1) (z := p.2) h
  · exact admL_bound (x := p.1) (z := p.2) h

end

/-! ## The rules in the direction of a walk -/

section rules

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

include hL in
theorem joinD (rev : Bool) {a b : Ans D P} {l fr : Option R} {n₁ n₂ : Rel} {X₁ X₂ : PRel}
    (ha : a.goal = goalD rev l n₁ none)
    (hb : b.goal = goalD rev (nearB D rev (some a.span)) n₂ fr)
    (h₁ : X₁ ⊆ den P.sorts.interp a.span) (h₂ : X₂ ⊆ den P.sorts.interp b.span)
    (hne : (compP rev X₁ X₂).Nonempty) :
    ∃ c, joinAtV K hK rev a b = some c ∧ compP rev X₁ X₂ ⊆ den P.sorts.interp c.span ∧
      c.goal = goalD rev l (catD rev n₁ n₂) fr := by
  cases rev
  · obtain ⟨c, hcv, hcs, hg⟩ := join_cov hL K hK (a := a) (b := b)
      (.inl ⟨by rw [ha]; rfl, .inr (by rw [hb]; rfl)⟩) h₁ h₂ hne
    exact ⟨c, hcv, hcs, by rw [hg, ha, hb]; rfl⟩
  · obtain ⟨c, hcv, hcs, hg⟩ := join_cov hL K hK (a := b) (b := a)
      (.inr ⟨by rw [ha]; rfl, by rw [hb]; rfl⟩) h₂ h₁ hne
    exact ⟨c, hcv, hcs, by rw [hg, ha, hb]; rfl⟩

theorem joinD_goal (rev : Bool) {a b c : Ans D P} {l β fr : Option R} {n₁ n₂ : Rel}
    (h : joinAtV K hK rev a b = some c) (ha : a.goal = goalD rev l n₁ none)
    (hb : b.goal = goalD rev β n₂ fr) : c.goal = goalD rev l (catD rev n₁ n₂) fr := by
  cases rev
  · rw [((Ans.join_val K hK).1 h).2.2, ha, hb]; rfl
  · rw [((Ans.join_val K hK).1 h).2.2, ha, hb]; rfl

include hL in
theorem meetD (rev : Bool) {a b : Ans D P} {near far : Option R} {n₁ n₂ : Rel} {W : PRel}
    (ha : a.goal = goalD rev near n₁ far) (hb : b.goal = goalD rev near n₂ far)
    (h₁ : W ⊆ den P.sorts.interp a.span) (h₂ : W ⊆ den P.sorts.interp b.span)
    (hne : W.Nonempty) :
    ∃ c, (Ans.meetA D P K hK a b).val = some c ∧ W ⊆ den P.sorts.interp c.span ∧
      c.goal = goalD rev near (mkAnd (sortedParts (andParts n₁ ++ andParts n₂))) far := by
  obtain ⟨c, hcv, hcs, hg⟩ := meet_cov hL K hK (a := a) (b := b)
    (.inl ⟨by rw [ha, hb]; cases rev <;> rfl, by rw [ha, hb]; cases rev <;> rfl⟩) h₁ h₂
    (by rwa [Set.inter_self])
  refine ⟨c, hcv, by rwa [Set.inter_self] at hcs, ?_⟩
  rw [hg, ha, hb]
  cases rev <;> rfl

theorem meetD_goal (rev : Bool) {a b c : Ans D P} {near far : Option R} {n₁ n₂ : Rel}
    (h : (Ans.meetA D P K hK a b).val = some c) (ha : a.goal = goalD rev near n₁ far)
    (hb : b.goal = goalD rev near n₂ far) :
    c.goal = goalD rev near (mkAnd (sortedParts (andParts n₁ ++ andParts n₂))) far := by
  rw [((Ans.meetA_val K hK).1 h).2.2, ha, hb]
  cases rev <;> rfl

end rules

/-! ## Chains in the order they are walked -/

theorem catD_node (rev : Bool) {pm : List Rel} {x : Rel} (hpm : pm ≠ [])
    (hns : ∀ y ∈ pm, NotSeq y) (hx : NotSeq x) :
    catD rev (nodeD rev pm) x = nodeD rev (pm ++ [x]) := by
  cases rev
  · show mkSeq (seqParts (mkSeq pm) ++ seqParts x) = mkSeq (pm ++ [x])
    rw [seqParts_mkSeq hpm hns, seqParts_notSeq hx]
  · show mkSeq (seqParts x ++ seqParts (mkSeq pm.reverse)) = mkSeq (pm ++ [x]).reverse
    rw [seqParts_mkSeq (by simpa using hpm) (fun y hy => hns y (List.mem_reverse.1 hy)),
      seqParts_notSeq hx, List.reverse_append]
    rfl

/-- What a chain derives, by its members in the order they are walked. The
list is not empty. -/
def chainSet (rev : Bool) (S : Rel → Set GRel) : List Rel → Set GRel
  | [] => ∅
  | [x] => S x
  | x :: y :: ys => {G | ∃ G₁ ∈ S x, ∃ G' ∈ chainSet rev S (y :: ys), G = compG rev G₁ G'}

theorem chainSet_fwd (S : Rel → Set GRel) : ∀ ys : List Rel, ys ≠ [] →
    chainSet false S ys = RwLog.seqAll (ys.map S)
  | [], h => absurd rfl h
  | [x], _ => (image2_comp_id (S x)).symm
  | x :: y :: ys, _ => by
    ext G
    rw [chainSet, chainSet_fwd S (y :: ys) (by simp)]
    constructor
    · rintro ⟨G₁, h₁, G', h', rfl⟩; exact ⟨G₁, h₁, G', h', rfl⟩
    · rintro ⟨G₁, h₁, G', h', rfl⟩; exact ⟨G₁, h₁, G', h', rfl⟩

theorem chainSet_bwd (S : Rel → Set GRel) : ∀ ys : List Rel, ys ≠ [] →
    chainSet true S ys = RwLog.seqAll (ys.reverse.map S)
  | [], h => absurd rfl h
  | [x], _ => (image2_comp_id (S x)).symm
  | x :: y :: ys, _ => by
    have ih := chainSet_bwd S (y :: ys) (by simp)
    have e : RwLog.seqAll ((x :: y :: ys).reverse.map S) =
        Set.image2 GRel.comp (RwLog.seqAll ((y :: ys).reverse.map S)) (S x) := by
      rw [List.reverse_cons, List.map_append, seqAll_append]
      congr 1
      exact image2_comp_id (S x)
    ext G
    rw [chainSet, ih, e]
    constructor
    · rintro ⟨G₁, h₁, G', h', rfl⟩; exact ⟨G', h', G₁, h₁, rfl⟩
    · rintro ⟨G', h', G₁, h₁, rfl⟩; exact ⟨G₁, h₁, G', h', rfl⟩

/-- The members of a chain in the order they are walked derive what the
chain derives. -/
theorem chainSet_seqAll (rev : Bool) (S : Rel → Set GRel) {xs : List Rel} (h : xs ≠ []) :
    chainSet rev S (if rev then xs.reverse else xs) = RwLog.seqAll (xs.map S) := by
  cases rev
  · exact chainSet_fwd S xs h
  · show chainSet true S xs.reverse = _
    rw [chainSet_bwd S xs.reverse (by simpa using h), List.reverse_reverse]

end Unfold

end Tabled

end RwLog
