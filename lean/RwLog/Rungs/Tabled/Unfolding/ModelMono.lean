/-
# A deeper unfolding refines a shallower one

`SP.Ref p' p`: the product `p'` is the product `p`, or `p` is open and `p'`
lies between its ends. Every product of the unfolding of a node to depth
`d + 1` refines a product of its unfolding to depth `d` (`se_succ`), so an
unfolding that is final at a depth is final at every greater depth
(`final_mono`): an open product can only come from an open one.
-/
import RwLog.Rungs.Tabled.Unfolding.Model

namespace RwLog

namespace Tabled

namespace Unfold

/-- The product `p'` is `p`, or `p` is open and `p'` lies between its ends. -/
def SP.Ref : SP → SP → Prop
  | .closed X, .closed Y => X = Y
  | .closed X, .opn A B => X.lends ⊆ A ∧ X.rends ⊆ B
  | .opn A' B', .opn A B => A' ⊆ A ∧ B' ⊆ B
  | .opn _ _, .closed _ => False

theorem SP.Ref.refl : ∀ p : SP, p.Ref p
  | .closed _ => rfl
  | .opn _ _ => ⟨subset_rfl, subset_rfl⟩

/-- Every product of the first set refines one of the second. -/
def SRef (S' S : Set SP) : Prop := ∀ r' ∈ S', ∃ r ∈ S, r'.Ref r

theorem SRef.refl (S : Set SP) : SRef S S := fun r hr => ⟨r, hr, SP.Ref.refl r⟩

/-- The left ends of a product lie in `A`. -/
def SP.LeftIn (A : Set GTerm) : SP → Prop
  | .closed X => X.lends ⊆ A
  | .opn A' _ => A' ⊆ A

/-- The right ends of a product lie in `B`. -/
def SP.RightIn (B : Set GTerm) : SP → Prop
  | .closed X => X.rends ⊆ B
  | .opn _ B' => B' ⊆ B

theorem SP.ref_opn {p : SP} {A B : Set GTerm} : p.Ref (.opn A B) ↔ p.LeftIn A ∧ p.RightIn B := by
  cases p <;> exact Iff.rfl

theorem comp_lends (X Y : PRel) : (X.comp Y).lends ⊆ X.lends := by
  rintro x ⟨z, m, h, -⟩; exact ⟨m, h⟩

theorem comp_rends (X Y : PRel) : (X.comp Y).rends ⊆ Y.rends := by
  rintro z ⟨x, m, -, h⟩; exact ⟨m, h⟩

theorem preS_lends (X : PRel) (A : Set GTerm) : preS X A ⊆ X.lends := by
  rintro x ⟨m, -, h⟩; exact ⟨m, h⟩

theorem postS_rends (B : Set GTerm) (Y : PRel) : postS B Y ⊆ Y.rends := by
  rintro z ⟨m, -, h⟩; exact ⟨m, h⟩

theorem SeqS.leftIn {p q r : SP} (h : SeqS p q r) {A : Set GTerm} (hp : p.LeftIn A) :
    r.LeftIn A := by
  cases h with
  | cc _ => exact (comp_lends _ _).trans hp
  | co _ => exact (preS_lends _ _).trans hp
  | oc _ => exact hp
  | oo _ => exact hp

theorem SeqS.rightIn {p q r : SP} (h : SeqS p q r) {B : Set GTerm} (hq : q.RightIn B) :
    r.RightIn B := by
  cases h with
  | cc _ => exact (comp_rends _ _).trans hq
  | co _ => exact hq
  | oc _ => exact (postS_rends _ _).trans hq
  | oo _ => exact hq

/-- Sequencing keeps refinement. -/
theorem SeqS.ref {p' q' r' p q : SP} (h : SeqS p' q' r') (hp : p'.Ref p) (hq : q'.Ref q) :
    ∃ r, SeqS p q r ∧ r'.Ref r := by
  cases h with
  | @cc X Y hne =>
    obtain ⟨⟨x, z⟩, m, h₁, h₂⟩ := hne
    cases p with
    | closed X' =>
      obtain rfl : X = X' := hp
      cases q with
      | closed Y' =>
        obtain rfl : Y = Y' := hq
        exact ⟨_, .cc ⟨(x, z), m, h₁, h₂⟩, rfl⟩
      | opn A B =>
        exact ⟨_, .co ⟨x, m, hq.1 ⟨z, h₂⟩, h₁⟩,
          fun x' ⟨z', m', a, b⟩ => ⟨m', hq.1 ⟨z', b⟩, a⟩, (comp_rends _ _).trans hq.2⟩
    | opn A B =>
      cases q with
      | closed Y' =>
        obtain rfl : Y = Y' := hq
        exact ⟨_, .oc ⟨z, m, hp.2 ⟨x, h₁⟩, h₂⟩, (comp_lends _ _).trans hp.1,
          fun z' ⟨x', m', a, b⟩ => ⟨m', hp.2 ⟨x', a⟩, b⟩⟩
      | opn A₂ B₂ =>
        exact ⟨_, .oo ⟨m, hp.2 ⟨x, h₁⟩, hq.1 ⟨z, h₂⟩⟩, (comp_lends _ _).trans hp.1,
          (comp_rends _ _).trans hq.2⟩
  | @co X A' B' hne =>
    obtain ⟨x, m, hm, hx⟩ := hne
    cases q with
    | closed _ => exact hq.elim
    | opn A₂ B₂ =>
      cases p with
      | closed X' =>
        obtain rfl : X = X' := hp
        exact ⟨_, .co ⟨x, m, hq.1 hm, hx⟩, fun x' ⟨m', a, b⟩ => ⟨m', hq.1 a, b⟩, hq.2⟩
      | opn A B =>
        exact ⟨_, .oo ⟨m, hp.2 ⟨x, hx⟩, hq.1 hm⟩, (preS_lends _ _).trans hp.1, hq.2⟩
  | @oc A' B' Y hne =>
    obtain ⟨z, m, hm, hz⟩ := hne
    cases p with
    | closed _ => exact hp.elim
    | opn A B =>
      cases q with
      | closed Y' =>
        obtain rfl : Y = Y' := hq
        exact ⟨_, .oc ⟨z, m, hp.2 hm, hz⟩, hp.1, fun z' ⟨m', a, b⟩ => ⟨m', hp.2 a, b⟩⟩
      | opn A₂ B₂ =>
        exact ⟨_, .oo ⟨m, hp.2 hm, hq.1 ⟨z, hz⟩⟩, hp.1, (postS_rends _ _).trans hq.2⟩
  | @oo A' B' A'' B'' hne =>
    obtain ⟨m, h₁, h₂⟩ := hne
    cases p with
    | closed _ => exact hp.elim
    | opn A B =>
      cases q with
      | closed _ => exact hq.elim
      | opn A₂ B₂ => exact ⟨_, .oo ⟨m, hp.2 h₁, hq.1 h₂⟩, hp.1, hq.2⟩

theorem seqSets_ref {S' T' S T : Set SP} (hS : SRef S' S) (hT : SRef T' T) :
    SRef (seqSets S' T') (seqSets S T) := by
  rintro r' ⟨p', hp', q', hq', h⟩
  obtain ⟨p, hp, e₁⟩ := hS p' hp'
  obtain ⟨q, hq, e₂⟩ := hT q' hq'
  obtain ⟨r, hr, e⟩ := h.ref e₁ e₂
  exact ⟨r, ⟨p, hp, q, hq, hr⟩, e⟩

theorem foldl_seqSets_ref : ∀ {l' l : List (Set SP)}, List.Forall₂ SRef l' l →
    ∀ {S' S : Set SP}, SRef S' S → SRef (l'.foldl seqSets S') (l.foldl seqSets S)
  | _, _, .nil, _, _, h => h
  | _, _, .cons h t, _, _, hS => foldl_seqSets_ref t (seqSets_ref hS h)

theorem chainS_ref : ∀ {l' l : List (Set SP)}, List.Forall₂ SRef l' l → SRef (chainS l') (chainS l)
  | _, _, .nil => SRef.refl _
  | _, _, .cons h t => foldl_seqSets_ref t h

/-! ## Where the products of a chain lie -/

theorem foldl_seqSets_leftIn {A : Set GTerm} : ∀ (rest : List (Set SP)) (S : Set SP),
    (∀ p ∈ S, p.LeftIn A) → ∀ p ∈ rest.foldl seqSets S, p.LeftIn A
  | [], _, h => h
  | T :: rest, S, h => by
    refine foldl_seqSets_leftIn rest (seqSets S T) ?_
    rintro r ⟨p, hp, q, -, hs⟩
    exact hs.leftIn (h p hp)

theorem chainR_rightIn {B : Set GTerm} : ∀ (l : List (Set SP)) (hl : l ≠ []),
    (∀ p ∈ l.getLast hl, p.RightIn B) → ∀ p ∈ chainR l, p.RightIn B
  | [S], _, h => h
  | S :: T :: rest, _, h => by
    rw [chainR_cons S (List.cons_ne_nil T rest)]
    rintro r ⟨p, -, q, hq, hs⟩
    exact hs.rightIn (chainR_rightIn (T :: rest) (List.cons_ne_nil T rest)
      (by rwa [List.getLast_cons (List.cons_ne_nil T rest)] at h) q hq)

/-! ## Meets -/

theorem foldl_meetSets_sub : ∀ (rest : List (Set PRel)) (S : Set PRel) (Z : PRel),
    Z ∈ rest.foldl meetSets S → ∃ X ∈ S, Z ⊆ X
  | [], _, Z, h => ⟨Z, h, subset_rfl⟩
  | T :: rest, S, Z, h => by
    obtain ⟨W, ⟨X, hX, Y, -, rfl, -⟩, hZ⟩ := foldl_meetSets_sub rest (meetSets S T) Z h
    exact ⟨X, hX, hZ.trans Set.inter_subset_left⟩

theorem foldl_meetSets_nonempty : ∀ (rest : List (Set PRel)) (S : Set PRel) (Z : PRel),
    Z ∈ rest.foldl meetSets S → S.Nonempty ∧ ∀ T ∈ rest, T.Nonempty
  | [], _, Z, h => ⟨⟨Z, h⟩, by simp⟩
  | T :: rest, S, Z, h => by
    obtain ⟨⟨W, X, hX, Y, hY, -, -⟩, hr⟩ := foldl_meetSets_nonempty rest (meetSets S T) Z h
    refine ⟨⟨X, hX⟩, fun U hU => ?_⟩
    rcases List.mem_cons.1 hU with rfl | hU
    · exact ⟨Y, hY⟩
    · exact hr U hU

theorem closedPart_ref {S' S : Set SP} (h : SRef S' S) (hn : ¬ HasOpn S) :
    closedPart S' ⊆ closedPart S := by
  intro X hX
  obtain ⟨r, hr, e⟩ := h _ hX
  cases r with
  | closed Y => obtain rfl : X = Y := e; exact hr
  | opn A B => exact (hn ⟨A, B, hr⟩).elim

theorem meetSets_mono {S S' T T' : Set PRel} (hS : S' ⊆ S) (hT : T' ⊆ T) :
    meetSets S' T' ⊆ meetSets S T := by
  rintro Z ⟨X, hX, Y, hY, h⟩
  exact ⟨X, hS hX, Y, hT hY, h⟩

/-- A member of the fold of the closed products of sets that refine others is
in the fold of the closed products of those, or one of those has an open
product. -/
theorem foldl_meetSets_ref : ∀ {l' l : List (Set SP)}, List.Forall₂ SRef l' l →
    ∀ (S' S : Set PRel) (Z : PRel), S' ⊆ S → Z ∈ (l'.map closedPart).foldl meetSets S' →
      Z ∈ (l.map closedPart).foldl meetSets S ∨ ∃ T ∈ l, HasOpn T
  | _, _, .nil, _, _, _, h, hZ => .inl (h hZ)
  | _, _, @List.Forall₂.cons _ _ _ T' T l' l hT t, S', S, Z, h, hZ => by
    simp only [List.map_cons, List.foldl_cons] at hZ ⊢
    by_cases ho : HasOpn T
    · exact .inr ⟨T, by simp, ho⟩
    · rcases foldl_meetSets_ref t _ _ Z (meetSets_mono h (closedPart_ref hT ho)) hZ with h | ⟨U, hU, h⟩
      · exact .inl h
      · exact .inr ⟨U, List.mem_cons_of_mem _ hU, h⟩

/-- The products of a meet of sets that refine others, each within the ends,
refine the products of the meet of those. -/
theorem meetS_ref {A B : Set GTerm} {l' l : List (Set SP)} (h : List.Forall₂ SRef l' l)
    (hin : ∀ S ∈ l', ∀ p ∈ S, p.Ref (.opn A B)) : SRef (meetS A B l') (meetS A B l) := by
  have hne : (∀ S ∈ l', S.Nonempty) → ∀ S ∈ l, S.Nonempty := by
    intro h' S hS
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hS
    have hi' : i < l'.length := by rw [List.forall₂_iff_get.1 h |>.1]; exact hi
    have hr : SRef l'[i] l[i] := (List.forall₂_iff_get.1 h).2 i hi' hi
    obtain ⟨r', hr'⟩ := h' _ (List.getElem_mem hi')
    obtain ⟨r, hr, -⟩ := hr r' hr'
    exact ⟨r, hr⟩
  have hopn : (∃ S ∈ l', HasOpn S) → ∃ S ∈ l, HasOpn S := by
    rintro ⟨S', hS', A', B', ho⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hS'
    have hi' : i < l.length := by rw [← List.forall₂_iff_get.1 h |>.1]; exact hi
    obtain ⟨r, hr, e⟩ := (List.forall₂_iff_get.1 h).2 i hi hi' _ ho
    cases r with
    | closed _ => exact e.elim
    | opn A₂ B₂ => exact ⟨_, List.getElem_mem hi', A₂, B₂, hr⟩
  rintro r' (⟨Z, hZ, rfl⟩ | ⟨rfl, h₁, h₂⟩)
  · cases h with
    | nil => cases hZ
    | @cons S' S l' l hS t =>
      have hZ' : Z ∈ (l'.map closedPart).foldl meetSets (closedPart S') := hZ
      obtain ⟨⟨X₀, hX₀⟩, hrest⟩ := foldl_meetSets_nonempty _ _ _ hZ'
      have hall : ∀ T ∈ S' :: l', T.Nonempty := by
        intro T hT
        rcases List.mem_cons.1 hT with rfl | hT
        · exact ⟨_, hX₀⟩
        · obtain ⟨X, hX⟩ := hrest _ (List.mem_map_of_mem hT)
          exact ⟨_, hX⟩
      have hopen : (∃ T ∈ S :: l, HasOpn T) → ∃ r ∈ meetS A B (S :: l), (SP.closed Z).Ref r := by
        intro ho
        refine ⟨.opn A B, .inr ⟨rfl, hne hall, ho⟩, ?_⟩
        obtain ⟨X, hX, hsub⟩ := foldl_meetSets_sub _ _ _ hZ'
        obtain ⟨hl, hr⟩ := hin S' (by simp) _ hX
        exact ⟨fun x ⟨z, hz⟩ => hl ⟨z, hsub hz⟩, fun z ⟨x, hz⟩ => hr ⟨x, hsub hz⟩⟩
      by_cases ho : HasOpn S
      · exact hopen ⟨S, by simp, ho⟩
      · rcases foldl_meetSets_ref t _ _ Z (closedPart_ref hS ho) hZ' with h | ⟨U, hU, h⟩
        · exact ⟨.closed Z, .inl ⟨Z, h, rfl⟩, rfl⟩
        · exact hopen ⟨U, List.mem_cons_of_mem _ hU, h⟩
  · exact ⟨.opn A B, .inr ⟨rfl, hne h₁, hopn h₂⟩, SP.Ref.refl _⟩

/-! ## The products of a node -/

variable {P : Program} {M : Interp}

/-- Every product of a node lies between the ends it was unfolded between. -/
theorem se_within : ∀ (d : Nat) (A : Set GTerm) (e : Rel) (B : Set GTerm),
    ∀ p ∈ SE P M d A e B, p.Ref (.opn A B)
  | 0, A, e, B => by
    intro p hp
    obtain rfl : p = .opn A B := hp
    exact SP.Ref.refl _
  | d + 1, A, e, B => by
    cases hv : e.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      rw [se_span]
      rintro p ⟨rfl, -⟩
      exact ⟨fun x ⟨z, _, hx, _⟩ => hx, fun z ⟨x, _, _, hz⟩ => hz⟩
    | call n f =>
      cases hb : Charged.bodyOf P e with
      | none =>
        obtain ⟨b, hb'⟩ := forget_call (P := P) hv
        rw [hb] at hb'; cases hb'
      | some b =>
        rw [se_call hv hb]
        exact se_within d A b B
    | union xs =>
      rw [se_union hv]
      rintro p ⟨x, -, hp⟩
      exact se_within d A x B p hp
    | chain xs =>
      rw [se_chain hv]
      intro p hp
      rw [SP.ref_opn]
      cases xs with
      | nil => cases hp
      | cons x rest =>
        constructor
        · rw [List.zipIdx_cons, List.map_cons] at hp
          refine foldl_seqSets_leftIn _ _ (fun q hq => ?_) p hp
          exact (SP.ref_opn.1 (se_within d _ x _ q hq)).1
        · rw [chainS_eq_chainR] at hp
          refine chainR_rightIn _ (by simp) (fun q hq => ?_) p hp
          rw [List.getLast_eq_getElem] at hq
          simp only [List.getElem_map, List.getElem_zipIdx, List.length_map, List.length_zipIdx,
            List.length_cons, Nat.zero_add, Nat.add_sub_cancel, ↓reduceIte] at hq
          exact (SP.ref_opn.1 (se_within d _ _ _ q hq)).2
    | meet xs =>
      rw [se_meet hv]
      rintro p (⟨X, hX, rfl⟩ | ⟨rfl, -, -⟩)
      · cases xs with
        | nil => cases hX
        | cons x rest =>
          obtain ⟨X₀, hX₀, hsub⟩ := foldl_meetSets_sub _ _ _ hX
          obtain ⟨hl, hr⟩ := se_within d A x B _ hX₀
          exact ⟨fun a ⟨z, hz⟩ => hl ⟨z, hsub hz⟩, fun z ⟨a, hz⟩ => hr ⟨a, hsub hz⟩⟩
      · exact SP.Ref.refl _

theorem forall₂_map_of {α : Type} {l : List α} {f' f : α → Set SP}
    (h : ∀ a ∈ l, SRef (f' a) (f a)) : List.Forall₂ SRef (l.map f') (l.map f) := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    exact .cons (h a (by simp)) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- Every product of the unfolding one deeper refines a product of the
unfolding. -/
theorem se_succ : ∀ (d : Nat) (A : Set GTerm) (e : Rel) (B : Set GTerm),
    SRef (SE P M (d + 1) A e B) (SE P M d A e B)
  | 0, A, e, B => fun p hp => ⟨.opn A B, rfl, se_within 1 A e B p hp⟩
  | d + 1, A, e, B => by
    cases hv : e.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      rw [se_span, se_span]
      exact SRef.refl _
    | call n f =>
      cases hb : Charged.bodyOf P e with
      | none =>
        obtain ⟨b, hb'⟩ := forget_call (P := P) hv
        rw [hb] at hb'; cases hb'
      | some b =>
        rw [se_call hv hb, se_call hv hb]
        exact se_succ d A b B
    | union xs =>
      rw [se_union hv, se_union hv]
      rintro p ⟨x, hx, hp⟩
      obtain ⟨r, hr, e⟩ := se_succ d A x B p hp
      exact ⟨r, ⟨x, hx, hr⟩, e⟩
    | chain xs =>
      rw [se_chain hv, se_chain hv]
      exact chainS_ref (forall₂_map_of fun q _ => se_succ d _ q.1 _)
    | meet xs =>
      rw [se_meet hv, se_meet hv]
      refine meetS_ref (forall₂_map_of fun x _ => se_succ d A x B) fun S hS p hp => ?_
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hS
      exact se_within (d + 1) A x B p hp

/-- An unfolding with no open product has none at any greater depth. -/
theorem final_mono {d d' : Nat} (h : d ≤ d') {A B : Set GTerm} {e : Rel}
    (hf : Final P M d A e B) : Final P M d' A e B := by
  induction h with
  | refl => exact hf
  | @step m _ ih =>
    rintro ⟨A', B', ho⟩
    obtain ⟨r, hr, e⟩ := se_succ m A e B _ ho
    cases r with
    | closed _ => exact e.elim
    | opn A₂ B₂ => exact ih ⟨A₂, B₂, hr⟩

end Unfold

end Tabled

end RwLog
