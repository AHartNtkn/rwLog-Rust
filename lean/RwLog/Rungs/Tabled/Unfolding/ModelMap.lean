/-
# The unfolding of a mapped node

`Kernel/NormalFormMap.lean` reads a node as the node of its converse, of its
mirror image in the mirrored program, or as itself (`nmap b t`). The products
of the unfolding of the mapped node, in the program mirrored when the calls
are flipped, are the products of the unfolding of the node, each turned
round when the converse is taken (`se_nmap`): a closed product relates the
converse pairs, and an open product has its two ends exchanged.

So an unfolding is final exactly when the unfolding of the mapped node is
(`final_nmap`), and their closed products relate the same pairs, turned
round (`closedPart_nmap`).
-/
import RwLog.Rungs.Tabled.Unfolding.Model
import RwLog.Kernel.NormalFormMap
import RwLog.SpanLayer.Modulo

namespace RwLog

namespace Tabled

namespace Unfold

/-- A product read from the other end. -/
def SP.inv : SP → SP
  | .closed X => .closed X.inv
  | .opn A B => .opn B A

/-- A product, read from the other end when `b`. -/
def SP.invD (b : Bool) (p : SP) : SP := if b then p.inv else p

theorem SP.invD_false : SP.invD false = id := funext fun _ => rfl

theorem SP.invD_true : SP.invD true = SP.inv := funext fun _ => rfl

theorem SP.inv_inv (p : SP) : p.inv.inv = p := by cases p <;> rfl

theorem SP.invD_invD (b : Bool) (p : SP) : SP.invD b (SP.invD b p) = p := by
  cases b
  · rfl
  · exact p.inv_inv

theorem mem_image_invD {b : Bool} {S : Set SP} {p : SP} :
    p ∈ SP.invD b '' S ↔ SP.invD b p ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩; rwa [SP.invD_invD]
  · intro h; exact ⟨_, h, SP.invD_invD b p⟩

theorem preS_inv (X : PRel) (A : Set GTerm) : preS X.inv A = postS A X := rfl

theorem postS_inv (B : Set GTerm) (X : PRel) : postS B X.inv = preS X B := rfl

theorem SeqS.inv {p q r : SP} (h : SeqS p q r) : SeqS q.inv p.inv r.inv := by
  cases h with
  | @cc X Y hne =>
    have e : (X.comp Y).inv = Y.inv.comp X.inv := PRel.inv_comp X Y
    show SeqS (.closed Y.inv) (.closed X.inv) (.closed (X.comp Y).inv)
    rw [e]
    refine .cc ?_
    rw [← e]
    obtain ⟨⟨x, y⟩, hp⟩ := hne
    exact ⟨(y, x), hp⟩
  | @co X A B hne => exact .oc (by rw [postS_inv]; exact hne)
  | @oc A B Y hne => exact .co (by rw [preS_inv]; exact hne)
  | @oo A B A' B' hne => exact .oo (by rw [Set.inter_comm]; exact hne)

theorem seqSets_inv (S T : Set SP) :
    SP.inv '' seqSets S T = seqSets (SP.inv '' T) (SP.inv '' S) := by
  ext r
  constructor
  · rintro ⟨r', ⟨p, hp, q, hq, h⟩, rfl⟩
    exact ⟨q.inv, ⟨q, hq, rfl⟩, p.inv, ⟨p, hp, rfl⟩, h.inv⟩
  · rintro ⟨q', ⟨q, hq, rfl⟩, p', ⟨p, hp, rfl⟩, h⟩
    refine ⟨r.inv, ⟨p, hp, q, hq, ?_⟩, r.inv_inv⟩
    have := h.inv
    rwa [SP.inv_inv, SP.inv_inv] at this

theorem chainS_snoc {l : List (Set SP)} (h : l ≠ []) (T : Set SP) :
    chainS (l ++ [T]) = seqSets (chainS l) T := by
  cases l with
  | nil => exact absurd rfl h
  | cons S rest => simp [chainS, List.foldl_append]

/-- The products of a chain read from the other end are the products of the
chain of the members read from the other end, in the reverse order. -/
theorem chainS_inv : ∀ l : List (Set SP),
    SP.inv '' chainS l = chainS (l.reverse.map fun S => SP.inv '' S)
  | [] => by simp [chainS]
  | [S] => by simp [chainS]
  | S :: T :: rest => by
    have ih := chainS_inv (T :: rest)
    rw [chainS_eq_chainR, chainR_cons S (by simp), ← chainS_eq_chainR, seqSets_inv, ih,
      List.reverse_cons (a := S), List.map_append, List.map_singleton, chainS_snoc (by simp)]

theorem chainS_invD (b : Bool) (l : List (Set SP)) :
    SP.invD b '' chainS l =
      chainS ((if b then l.reverse else l).map fun S => SP.invD b '' S) := by
  cases b
  · simp [SP.invD_false]
  · simpa [SP.invD_true] using chainS_inv l

/-! ## Meets -/

theorem meetSets_comm (S T : Set PRel) : meetSets S T = meetSets T S := by
  ext Z
  constructor <;>
  · rintro ⟨X, hX, Y, hY, rfl, hne⟩
    exact ⟨Y, hY, X, hX, Set.inter_comm _ _, hne⟩

theorem meetSets_assoc (S T U : Set PRel) :
    meetSets (meetSets S T) U = meetSets S (meetSets T U) := by
  ext Z
  constructor
  · rintro ⟨_, ⟨X, hX, Y, hY, rfl, -⟩, W, hW, rfl, hne⟩
    refine ⟨X, hX, Y ∩ W, ⟨Y, hY, W, hW, rfl, ?_⟩, Set.inter_assoc _ _ _, ?_⟩
    · exact hne.mono fun p hp => ⟨hp.1.2, hp.2⟩
    · exact hne
  · rintro ⟨X, hX, _, ⟨Y, hY, W, hW, rfl, -⟩, rfl, hne⟩
    refine ⟨X ∩ Y, ⟨X, hX, Y, hY, rfl, ?_⟩, W, hW, (Set.inter_assoc _ _ _).symm, ?_⟩
    · exact hne.mono fun p hp => ⟨hp.1, hp.2.1⟩
    · exact hne

theorem meetSets_right_comm (S T U : Set PRel) :
    meetSets (meetSets S T) U = meetSets (meetSets S U) T := by
  rw [meetSets_assoc, meetSets_comm T U, ← meetSets_assoc]

/-- The relations of a set that relate a pair. -/
def liveOf (S : Set PRel) : Set PRel := {X | X ∈ S ∧ X.Nonempty}

theorem meetSets_univ (S : Set PRel) : meetSets {Set.univ} S = liveOf S := by
  ext Z
  constructor
  · rintro ⟨X, hX, Y, hY, rfl, hne⟩
    obtain rfl : X = Set.univ := hX
    rw [Set.univ_inter] at hne ⊢
    exact ⟨hY, hne⟩
  · rintro ⟨hZ, hne⟩
    exact ⟨Set.univ, rfl, Z, hZ, (Set.univ_inter Z).symm, hne⟩

theorem meetSets_liveOf (S T : Set PRel) : meetSets (liveOf S) T = meetSets S T := by
  ext Z
  constructor
  · rintro ⟨X, hX, Y, hY, rfl, hne⟩
    exact ⟨X, hX.1, Y, hY, rfl, hne⟩
  · rintro ⟨X, hX, Y, hY, rfl, hne⟩
    exact ⟨X, ⟨hX, hne.mono Set.inter_subset_left⟩, Y, hY, rfl, hne⟩

/-- The closed products of a meet of at least two members, folded from the
relation that relates everything. -/
theorem meetAllS_eq_foldl {L : List (Set PRel)} (h2 : 2 ≤ L.length) :
    meetAllS L = L.foldl meetSets {Set.univ} := by
  match L, h2 with
  | S :: T :: rest, _ =>
    simp only [meetAllS, List.foldl_cons, meetSets_univ, meetSets_liveOf]

/-- The closed products of a meet do not depend on the order of its
members. -/
theorem meetAllS_perm {L L' : List (Set PRel)} (h : L.Perm L') (h2 : 2 ≤ L.length) :
    meetAllS L = meetAllS L' := by
  rw [meetAllS_eq_foldl h2, meetAllS_eq_foldl (h.length_eq ▸ h2)]
  exact h.foldl_eq' (fun x _ y _ z => meetSets_right_comm z x y) _

/-- The products of a meet do not depend on the order of its members. -/
theorem meetS_perm (A B : Set GTerm) {L L' : List (Set SP)} (h : L.Perm L')
    (h2 : 2 ≤ L.length) : meetS A B L = meetS A B L' := by
  unfold meetS
  rw [meetAllS_perm (h.map closedPart) (by simpa using h2)]
  ext r
  simp only [Set.mem_ofPred_eq, h.mem_iff]

theorem closedPart_inv (S : Set SP) :
    closedPart (SP.inv '' S) = PRel.inv '' closedPart S := by
  ext X
  constructor
  · rintro ⟨p, hp, e⟩
    cases p with
    | closed Y =>
      obtain rfl : Y.inv = X := by simpa [SP.inv] using e
      exact ⟨Y, hp, rfl⟩
    | opn A B => cases e
  · rintro ⟨Y, hY, rfl⟩
    exact ⟨_, hY, rfl⟩

theorem inv_inv' (X : PRel) : X.inv.inv = X := rfl

theorem meetSets_inv (S T : Set PRel) :
    PRel.inv '' meetSets S T = meetSets (PRel.inv '' S) (PRel.inv '' T) := by
  ext Z
  constructor
  · rintro ⟨_, ⟨X, hX, Y, hY, rfl, hne⟩, rfl⟩
    refine ⟨X.inv, ⟨X, hX, rfl⟩, Y.inv, ⟨Y, hY, rfl⟩, rfl, ?_⟩
    obtain ⟨⟨x, y⟩, hp⟩ := hne
    exact ⟨(y, x), hp⟩
  · rintro ⟨_, ⟨X, hX, rfl⟩, _, ⟨Y, hY, rfl⟩, rfl, hne⟩
    refine ⟨X ∩ Y, ⟨X, hX, Y, hY, rfl, ?_⟩, rfl⟩
    obtain ⟨⟨x, y⟩, hp⟩ := hne
    exact ⟨(y, x), hp⟩

theorem foldl_meetSets_inv : ∀ (rest : List (Set PRel)) (S : Set PRel),
    PRel.inv '' rest.foldl meetSets S =
      (rest.map fun T => PRel.inv '' T).foldl meetSets (PRel.inv '' S)
  | [], S => rfl
  | T :: rest, S => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_meetSets_inv rest, meetSets_inv]

theorem meetAllS_inv : ∀ L : List (Set PRel),
    PRel.inv '' meetAllS L = meetAllS (L.map fun T => PRel.inv '' T)
  | [] => by simp [meetAllS]
  | S :: rest => foldl_meetSets_inv rest S

theorem hasOpn_inv (S : Set SP) : HasOpn (SP.inv '' S) ↔ HasOpn S := by
  constructor
  · rintro ⟨A, B, p, hp, e⟩
    cases p with
    | closed Y => cases e
    | opn A' B' => exact ⟨A', B', hp⟩
  · rintro ⟨A, B, h⟩
    exact ⟨B, A, _, h, rfl⟩

/-- The products of a meet read from the other end. -/
theorem meetS_inv (A B : Set GTerm) (L : List (Set SP)) :
    SP.inv '' meetS A B L = meetS B A (L.map fun S => SP.inv '' S) := by
  have hc : (L.map fun S => SP.inv '' S).map closedPart =
      (L.map closedPart).map fun T => PRel.inv '' T := by
    simp only [List.map_map]
    exact List.map_congr_left fun S _ => closedPart_inv S
  ext r
  constructor
  · rintro ⟨r', h, rfl⟩
    rcases h with ⟨X, hX, rfl⟩ | ⟨rfl, hall, S, hS, hop⟩
    · refine .inl ⟨X.inv, ?_, rfl⟩
      rw [hc, ← meetAllS_inv]
      exact ⟨X, hX, rfl⟩
    · refine .inr ⟨rfl, ?_, SP.inv '' S, List.mem_map_of_mem hS, (hasOpn_inv S).2 hop⟩
      intro T hT
      obtain ⟨S', hS', rfl⟩ := List.mem_map.1 hT
      exact (hall S' hS').image _
  · rintro (⟨X, hX, rfl⟩ | ⟨rfl, hall, T, hT, hop⟩)
    · rw [hc, ← meetAllS_inv] at hX
      obtain ⟨Y, hY, rfl⟩ := hX
      exact ⟨.closed Y, .inl ⟨Y, hY, rfl⟩, rfl⟩
    · obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hT
      refine ⟨.opn A B, .inr ⟨rfl, fun S' hS' => ?_, S, hS, (hasOpn_inv S).1 hop⟩, rfl⟩
      exact Set.image_nonempty.1 (hall _ (List.mem_map_of_mem hS'))

theorem meetS_invD (b : Bool) (A B : Set GTerm) (L : List (Set SP)) :
    SP.invD b '' meetS A B L =
      meetS (if b then B else A) (if b then A else B) (L.map fun S => SP.invD b '' S) := by
  cases b
  · simp [SP.invD_false]
  · simpa [SP.invD_true] using meetS_inv A B L

/-! ## The unfolding of a mapped node -/

variable {P : Program} {M : Interp}

theorem restr_inv (A : Set GTerm) (X : PRel) (B : Set GTerm) :
    (restr A X B).inv = restr B X.inv A := by
  ext ⟨x, y⟩
  exact ⟨fun ⟨h, ha, hb⟩ => ⟨h, hb, ha⟩, fun ⟨h, hb, ha⟩ => ⟨h, ha, hb⟩⟩

/-- The products of the unfolding of a mapped node are the products of the
unfolding of the node, read from the other end when the converse is
taken. -/
theorem se_nmap (b t : Bool) : ∀ (d : Nat) (e : Rel), Normal e → ∀ A B : Set GTerm,
    SE (if t then P.dual else P) M d (if b then B else A) (nmap b t e) (if b then A else B) =
      SP.invD b '' SE P M d A e B
  | 0, e, _, A, B => by
    rw [se_zero, se_zero, Set.image_singleton]
    cases b <;> rfl
  | d + 1, e, he, A, B => by
    have ih := se_nmap b t d
    cases hv : e.view with
    | span s =>
      obtain ⟨s', rfl⟩ := forget_span (e := e) (by rw [hv]; rfl)
      obtain rfl : s' = s := by simpa [RelOf.view] using hv
      rw [nmap_span, se_span, se_span]
      ext r
      rw [mem_image_invD]
      cases b
      · simp only [Bool.false_eq_true, ite_false, SP.invD]
      · simp only [ite_true, SP.invD, Set.mem_ofPred_eq]
        have e : restr B (s'.swap.den.at M) A = (restr A (s'.den.at M) B).inv := by
          rw [restr_inv, swap_den, at_inv]
        rw [e]
        constructor
        · rintro ⟨rfl, hne⟩
          refine ⟨rfl, ?_⟩
          obtain ⟨⟨x, y⟩, hp⟩ := hne
          exact ⟨(y, x), hp⟩
        · rintro ⟨hr, hne⟩
          refine ⟨?_, ?_⟩
          · rw [← r.inv_inv, hr]; rfl
          · obtain ⟨⟨x, y⟩, hp⟩ := hne
            exact ⟨(y, x), hp⟩
    | call n f =>
      have hv' := Normal.view_call hv b t
      have hb := he.bodyOf_nmap P b t
      cases hbody : Charged.bodyOf P e with
      | none =>
        rw [hbody] at hb
        simp only [SE, hv, hv', NodeView.forget, hbody, hb, Option.map_none, Set.image_empty]
      | some m =>
        rw [hbody] at hb
        rw [se_call (by rw [hv']; rfl) hb, se_call (by rw [hv]; rfl) hbody]
        exact ih m (bodyOf_normal' hbody) A B
    | union xs =>
      have hv' := he.view_union_nmap hv b t
      obtain ⟨hmem, -, -⟩ := he.view_union hv
      rw [se_union (by rw [hv']; rfl), se_union (by rw [hv]; rfl)]
      ext r
      rw [mem_image_invD]
      simp only [Set.mem_ofPred_eq, mem_sortedBranches, List.mem_map]
      constructor
      · rintro ⟨_, ⟨⟨x, hx, rfl⟩, -⟩, hr⟩
        rw [ih x (hmem x hx).1, mem_image_invD] at hr
        exact ⟨x, hx, hr⟩
      · rintro ⟨x, hx, hr⟩
        refine ⟨nmap b t x, ⟨⟨x, hx, rfl⟩, (hmem x hx).1.nmap_ne_zero (hmem x hx).2.2 b t⟩, ?_⟩
        rw [ih x (hmem x hx).1, mem_image_invD]
        exact hr
    | chain xs =>
      have hv' := he.view_chain_nmap hv b t
      obtain ⟨h2, hmem, -⟩ := he.view_chain hv
      rw [se_chain (by rw [hv']; rfl), se_chain (by rw [hv]; rfl), chainS_invD]
      congr 1
      cases b
      · simp only [Bool.false_eq_true, ite_false, List.length_map]
        rw [List.zipIdx_map, List.map_map, List.map_map]
        refine List.map_congr_left fun p hp => ?_
        have hx : p.1 ∈ xs := (List.mem_zipIdx hp).2.2 ▸ List.getElem_mem _
        have := ih p.1 (hmem p.1 hx).1 (if p.2 = 0 then A else Set.univ)
          (if p.2 + 1 = xs.length then B else Set.univ)
        simpa using this
      · simp only [ite_true, List.length_map, List.length_reverse]
        refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
        have hk : k < xs.length := by simpa using h₁
        simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_reverse, Nat.zero_add,
          List.length_map, List.length_zipIdx]
        have := ih xs[xs.length - 1 - k] (hmem _ (List.getElem_mem _)).1
          (if xs.length - 1 - k = 0 then A else Set.univ)
          (if xs.length - 1 - k + 1 = xs.length then B else Set.univ)
        simp only [ite_true] at this
        rw [← this]
        congr 1
        · by_cases h0 : k = 0
          · simp [h0]; omega
          · have : ¬ (xs.length - 1 - k + 1 = xs.length) := by omega
            simp [h0, this]
        · by_cases h1 : k + 1 = xs.length
          · have : xs.length - 1 - k = 0 := by omega
            simp [h1, this]
          · have : ¬ (xs.length - 1 - k = 0) := by omega
            simp [h1, this]
    | meet xs =>
      have hv' := he.view_meet_nmap hv b t
      obtain ⟨h2, hmem, -, -⟩ := he.view_meet hv
      rw [se_meet (by rw [hv']; rfl), se_meet (by rw [hv]; rfl), meetS_invD]
      have hperm := sortedParts_perm (xs.map (nmap b t))
      rw [meetS_perm _ _ (hperm.map _)
        (by rw [List.length_map, hperm.length_eq, List.length_map]; exact h2)]
      congr 1
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun x hx => ih x (hmem x hx).1 A B
where
  bodyOf_normal' {P : Program} {e m : Rel} (hb : Charged.bodyOf P e = some m) : Normal m := by
    unfold Charged.bodyOf at hb
    split at hb
    · cases hb; exact normal_norm _
    · cases hb; exact normal_normConv _
    · cases hb

/-- An unfolding has an open product exactly when the unfolding of the mapped
node has. -/
theorem final_nmap (b t : Bool) (d : Nat) {e : Rel} (he : Normal e) (A B : Set GTerm) :
    Final (if t then P.dual else P) M d (if b then B else A) (nmap b t e) (if b then A else B) ↔
      Final P M d A e B := by
  unfold Final
  rw [se_nmap b t d e he A B]
  cases b
  · simp [SP.invD_false]
  · rw [SP.invD_true, hasOpn_inv]

/-- The closed products of the unfolding of the mapped node relate the pairs
of those of the node, turned round when the converse is taken. -/
theorem closedPart_nmap (b t : Bool) (d : Nat) {e : Rel} (he : Normal e) (A B : Set GTerm)
    (X : PRel) :
    X ∈ closedPart (SE (if t then P.dual else P) M d (if b then B else A) (nmap b t e)
        (if b then A else B)) ↔
      (if b then X.inv else X) ∈ closedPart (SE P M d A e B) := by
  rw [se_nmap b t d e he A B]
  cases b
  · simp [SP.invD_false]
  · rw [SP.invD_true, closedPart_inv]
    constructor
    · rintro ⟨Y, hY, rfl⟩; exact hY
    · intro h; exact ⟨X.inv, h, rfl⟩

end Unfold

end Tabled

end RwLog
