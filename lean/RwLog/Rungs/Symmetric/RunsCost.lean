/-
# What reading an edge inwards costs on a chain of unions of two spans

`runs` follows an edge of a chain inwards and carries whole products of
spans. On a chain that has, at the edge read, `m + 2` members that are each
the same union of two spans, it carries every product of a choice of one
span from each, when the products of different choices relate different
pairs. With a kernel that charges a tick or more for a composition, reading
the last of these members costs `2 ^ (m + 1)` ticks (`runs_dear`).
-/
import RwLog.Rungs.Symmetric.Edge
import RwLog.Rungs.Framework.PaidOr
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

namespace RwLog

namespace Cost

variable {α β : Type}

/-- A fold spends a tick for each member whose step spends one. -/
theorem filter_length_le_foldL_ticks (f : β → α → Cost β) (p : α → Bool)
    (h : ∀ b x, p x = true → 1 ≤ (f b x).ticks) :
    ∀ (xs : List α) (b : β), (xs.filter p).length ≤ (foldL f b xs).ticks
  | [], _ => Nat.zero_le _
  | x :: xs, b => by
    have h2 := filter_length_le_foldL_ticks f p h xs (f b x).val
    simp only [foldL, bind_ticks, List.filter_cons]
    cases hp : p x with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
    | true =>
      have h1 := h b x hp
      simp only [↓reduceIte, List.length_cons]; omega

/-- A fold over a list spends what the fold over its first part spends. -/
theorem foldL_append_ticks (f : β → α → Cost β) :
    ∀ (xs ys : List α) (b : β), (foldL f b xs).ticks ≤ (foldL f b (xs ++ ys)).ticks
  | [], _, _ => Nat.zero_le _
  | x :: xs, ys, b => by
    have := foldL_append_ticks f xs ys (f b x).val
    simp only [List.cons_append, foldL, bind_ticks]
    omega

end Cost

namespace Symmetric

open Traverse Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The run is a whole product. -/
def Run.whole (r : Run R) : Bool := r.2 && r.1.isSome

/-- The runs hold, for every choice `w` of `j` spans, a whole product that
relates the pairs `Wd w`. -/
def Fans (M : Interp) (Wd : List Bool → PRel) (j : Nat) (rs : List (Run R)) : Prop :=
  ∀ w : List Bool, w.length = j → ∃ s, (some s, true) ∈ rs ∧ den M s = Wd w

omit [DecidableEq R] in
theorem Fans.any {M : Interp} {Wd : List Bool → PRel} {j : Nat} {rs : List (Run R)}
    (h : Fans M Wd j rs) : rs.any (·.2) = true := by
  obtain ⟨s, hs, -⟩ := h (List.replicate j true) (List.length_replicate ..)
  exact List.any_eq_true.2 ⟨_, hs, rfl⟩

/-- Runs that hold a whole product for every choice of `j` spans, where
different choices relate different pairs, hold `2 ^ j` whole products. -/
theorem Fans.pow_le {M : Interp} {Wd : List Bool → PRel} {j : Nat} {rs : List (Run R)}
    (h : Fans M Wd j rs)
    (hinj : ∀ w w' : List Bool, w.length = j → w'.length = j → Wd w = Wd w' → w = w') :
    2 ^ j ≤ (rs.filter Run.whole).length := by
  choose g hg using fun f : Fin j → Bool => h (List.ofFn f) (List.length_ofFn ..)
  have hcard : (Finset.univ : Finset (Fin j → Bool)).card = 2 ^ j := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← hcard]
  refine Nat.le_trans (Finset.card_le_card_of_injOn (t := (rs.filter Run.whole).toFinset)
    (fun f => ((some (g f), true) : Run R)) (fun f _ => ?_) (fun f _ f' _ e => ?_))
    (List.toFinset_card_le _)
  · exact List.mem_toFinset.2 (List.mem_filter.2 ⟨(hg f).1, rfl⟩)
  · have e' : g f = g f' := by
      have := congrArg Prod.fst e
      exact Option.some.inj this
    have hw : Wd (List.ofFn f) = Wd (List.ofFn f') := by rw [← (hg f).2, ← (hg f').2, e']
    exact List.ofFn_injective (hinj _ _ (List.length_ofFn ..) (List.length_ofFn ..) hw)

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- Continuing runs through a member that has a run of spans composes every
whole product: a tick or more for each, at a kernel that charges a tick or
more for a composition. -/
theorem extendRuns_ticks (hc : ∀ a b : R, 1 ≤ (K.compose a b).ticks) (last : Bool)
    (rs ys : List (Run R)) (hy : ∃ q ∈ ys, q.1.isSome = true) :
    (rs.filter Run.whole).length ≤
      (extendRuns (K := DerivationKernel.over D K hK P) last rs ys).ticks := by
  revert hc
  at_cost K hK
  intro hc
  simp only [extendRuns, foldL_std]
  refine Cost.filter_length_le_foldL_ticks _ _ (fun acc r hr => ?_) _ _
  obtain ⟨o, w⟩ := r
  cases o with
  | none => simp [Run.whole] at hr
  | some x =>
    cases w with
    | false => simp [Run.whole] at hr
    | true =>
      simp only
      obtain ⟨q, hq, hqs⟩ := hy
      refine Nat.le_trans ?_ (Cost.filter_length_le_foldL_ticks _ (fun q : Run R => q.1.isSome)
        (fun acc q hq => ?_) ys acc)
      · exact List.length_pos_of_mem (List.mem_filter.2 ⟨hq, hqs⟩)
      · obtain ⟨qo, qw⟩ := q
        cases qo with
        | none => cases hq
        | some y =>
          dsimp only
          cases last
          · exact Nat.le_trans (hc x y) (Nat.le_add_right _ _)
          · exact Nat.le_trans (hc y x) (Nat.le_add_right _ _)

/-- Continued through a member that has both spans, the runs hold a whole
product for every choice of one span more. -/
theorem Fans.extend {M : Interp} (hL : D.Lawful M) {Wd : List Bool → PRel} {rsp : Bool → R}
    (last : Bool)
    (hW : ∀ w b, w ≠ [] → Wd (w ++ [b]) =
      if last then (den M (rsp b)).comp (Wd w) else (Wd w).comp (den M (rsp b)))
    (hne : ∀ w, (Wd w).Nonempty) {j : Nat} {rs ys : List (Run R)} (hj : 1 ≤ j)
    (h : Fans M Wd j rs) (hys : ∀ b, (some (rsp b), true) ∈ ys) :
    Fans M Wd (j + 1) (extendRuns (K := DerivationKernel.over D K hK P) last rs ys).val := by
  intro w hw
  obtain ⟨w0, b, rfl⟩ : ∃ w0 b, w = w0 ++ [b] := by
    have hn : w ≠ [] := by intro e; rw [e] at hw; cases hw
    exact ⟨w.dropLast, w.getLast hn, (List.dropLast_append_getLast hn).symm⟩
  have hl : w0.length = j := by simpa using hw
  have hw0 : w0 ≠ [] := by intro e; rw [e] at hl; simp at hl; omega
  obtain ⟨s, hs, hds⟩ := h w0 hl
  have hsp := (extendRuns_spec (K := K) (hK := hK) (P := P) last rs ys).2 s hs _ (hys b)
  have hWb := hW w0 b hw0
  cases last with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hsp hWb
    cases hcp : D.compose s (rsp b) with
    | none =>
      have := hL.compose_none _ _ hcp
      rw [hds, ← hWb] at this
      exact absurd this (hne _).ne_empty
    | some c => exact ⟨c, hsp c hcp, by rw [hL.compose_some _ _ _ hcp, hds, hWb]⟩
  | true =>
    simp only [ite_true] at hsp hWb
    cases hcp : D.compose (rsp b) s with
    | none =>
      have := hL.compose_none _ _ hcp
      rw [hds, ← hWb] at this
      exact absurd this (hne _).ne_empty
    | some c => exact ⟨c, hsp c hcp, by rw [hL.compose_some _ _ _ hcp, hds, hWb]⟩

/-- A fold of steps that each continue the runs through one member more: the
runs hold a whole product for every choice, and the last step has spent a
tick for every whole product it was given. -/
theorem fans_fold {M : Interp} {Wd : List Bool → PRel}
    (hinj : ∀ j, ∀ w w' : List Bool, w.length = j → w'.length = j → Wd w = Wd w' → w = w')
    (G : Option (List (Run R)) → Rel → Cost (Option (List (Run R))))
    (E : List (Run R) → Cost (List (Run R)))
    (hEf : ∀ j rs, 1 ≤ j → Fans M Wd j rs → Fans M Wd (j + 1) (E rs).val)
    (hEt : ∀ rs, (rs.filter Run.whole).length ≤ (E rs).ticks) :
    ∀ (us : List Rel), (∀ x ∈ us, ∀ rs, rs.any (·.2) = true →
        (G (some rs) x).val = some (E rs).val ∧ (E rs).ticks ≤ (G (some rs) x).ticks) →
      ∀ j rs, 1 ≤ j → Fans M Wd j rs →
      ∃ rs', (Cost.foldL G (some rs) us).val = some rs' ∧ Fans M Wd (j + us.length) rs' ∧
        (us ≠ [] → 2 ^ (j + us.length - 1) ≤ (Cost.foldL G (some rs) us).ticks)
  | [], _, j, rs, _, h => ⟨rs, rfl, h, fun h => absurd rfl h⟩
  | x :: us, hG, j, rs, hj, h => by
    obtain ⟨hv, ht⟩ := hG x List.mem_cons_self rs h.any
    obtain ⟨rs', hv', hf', ht'⟩ := fans_fold hinj G E hEf hEt us
      (fun y hy => hG y (List.mem_cons_of_mem _ hy)) (j + 1) (E rs).val (by omega) (hEf j rs hj h)
    refine ⟨rs', ?_, ?_, fun _ => ?_⟩
    · simp only [Cost.foldL, Cost.bind_val, hv]; exact hv'
    · rw [List.length_cons, show j + (us.length + 1) = j + 1 + us.length by omega]; exact hf'
    · simp only [Cost.foldL, Cost.bind_ticks, hv]
      have h1 := Nat.le_trans (h.pow_le (hinj j)) (Nat.le_trans (hEt rs) ht)
      cases us with
      | nil =>
        rw [List.length_cons, List.length_nil, show j + (0 + 1) - 1 = j by omega]
        exact Nat.le_trans h1 (Nat.le_add_right _ _)
      | cons y us =>
        have h2 := ht' (by simp)
        rw [show j + (x :: y :: us).length - 1 = j + 1 + (y :: us).length - 1 by
          simp only [List.length_cons]; omega]
        exact Nat.le_trans h2 (Nat.le_add_left _ _)

/-- The same fold has spent a tick for every whole product its last step was
given. -/
theorem fans_fold_ticks {M : Interp} {Wd : List Bool → PRel}
    (hinj : ∀ j, ∀ w w' : List Bool, w.length = j → w'.length = j → Wd w = Wd w' → w = w')
    (G : Option (List (Run R)) → Rel → Cost (Option (List (Run R))))
    (E : List (Run R) → Cost (List (Run R)))
    (hEf : ∀ j rs, 1 ≤ j → Fans M Wd j rs → Fans M Wd (j + 1) (E rs).val)
    (hEt : ∀ rs, (rs.filter Run.whole).length ≤ (E rs).ticks) (us : List Rel)
    (hG : ∀ x ∈ us, ∀ rs, rs.any (·.2) = true →
      (G (some rs) x).val = some (E rs).val ∧ (E rs).ticks ≤ (G (some rs) x).ticks)
    (j : Nat) (rs : List (Run R)) (hj : 1 ≤ j) (h : Fans M Wd j rs) (hus : us ≠ []) :
    2 ^ (j + us.length - 1) ≤ (Cost.foldL G (some rs) us).ticks :=
  (fans_fold hinj G E hEf hEt us hG j rs hj h).choose_spec.2.2 hus

/-- The runs of a span are the span. -/
theorem runs_span_val (last : Bool) (d : Nat) (seen : List Rel) {s : Span} {r : R}
    (hr : D.rep s = some r) :
    (runs (K := DerivationKernel.over D K hK P) last (d + 1) seen (.span s)).val =
      some [(some r, true)] := by
  obtain ⟨c, hc, hcs, -⟩ := Ans.leaf_ok (P := P) K hK (s := s) (z := r) (isBound_none D)
    (isBound_none D) (by simp [spanBoth, hr])
  at_cost K hK
  unfold runs
  simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, RelOf.view,
    NodeView.forget, over_leaf, hc, Cost.pure_val, over_span, hcs]

/-- The runs of a union of two spans hold both. -/
theorem runs_two (last : Bool) (d : Nat) (seen : List Rel) {U : Rel} {sa sb : Span} {ra rb : R}
    (hU : U.view = .union [.span sa, .span sb]) (ha : D.rep sa = some ra)
    (hb : D.rep sb = some rb) :
    ∃ ys, (runs (K := DerivationKernel.over D K hK P) last (d + 2) seen U).val = some ys ∧
      (some ra, true) ∈ ys ∧ (some rb, true) ∈ ys := by
  have h1 := runs_span_val (K := K) (hK := hK) (P := P) last d seen ha
  have h2 := runs_span_val (K := K) (hK := hK) (P := P) last d seen hb
  have hadd := fun acc r => addRun_spec (K := K) (hK := hK) (P := P) acc r
  at_cost K hK
  unfold runs
  simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hU, NodeView.forget,
    foldL_std, Cost.foldL_val, List.foldl, h1, h2, Cost.pure_val]
  exact ⟨_, rfl, (hadd _ _).1 (hadd _ _).2, (hadd _ _).2⟩

/-- **Reading an edge inwards through `m + 2` unions of two spans costs
`2 ^ (m + 1)`.** The chain has, at the end read, `m + 2` members that are the
union `U` of two spans. The products of different choices of spans relate
different pairs, and the kernel charges a tick or more for a composition.
To a depth of three or more the reading spends `2 ^ (m + 1)` ticks, whatever
it returns. -/
theorem runs_dear {M : Interp} (hL : D.Lawful M) (hc : ∀ a b : R, 1 ≤ (K.compose a b).ticks)
    (last : Bool) {n U : Rel} {xs tl : List Rel} {m : Nat} {sa sb : Span} {rsp : Bool → R}
    (hv : n.view = .chain xs)
    (hx : (if last then xs.reverse else xs) = List.replicate (m + 2) U ++ tl)
    (hU : U.view = .union [.span sa, .span sb]) (ha : D.rep sa = some (rsp true))
    (hb : D.rep sb = some (rsp false)) {Wd : List Bool → PRel}
    (hW1 : ∀ b, Wd [b] = den M (rsp b))
    (hW : ∀ w b, w ≠ [] → Wd (w ++ [b]) =
      if last then (den M (rsp b)).comp (Wd w) else (Wd w).comp (den M (rsp b)))
    (hne : ∀ w, (Wd w).Nonempty)
    (hinj : ∀ j, ∀ w w' : List Bool, w.length = j → w'.length = j → Wd w = Wd w' → w = w')
    (d : Nat) (seen : List Rel) :
    2 ^ (m + 1) ≤ (runs (K := DerivationKernel.over D K hK P) last (d + 3) seen n).ticks := by
  obtain ⟨ys, hys, hya, hyb⟩ := runs_two (K := K) (hK := hK) (P := P) last d seen hU ha hb
  have hyall : ∀ b, (some (rsp b), true) ∈ ys := fun b => by cases b <;> assumption
  have hEf := fun j rs (hj : 1 ≤ j) (h : Fans M Wd j rs) =>
    Fans.extend (K := K) (hK := hK) (P := P) hL last hW hne hj h hyall
  have hEt := fun rs => extendRuns_ticks (hK := hK) (P := P) hc last rs ys ⟨_, hya, rfl⟩
  have hF1 : Fans M Wd 1 ys := by
    intro w hw
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 hw
    exact ⟨rsp b, hyall b, (hW1 b).symm⟩
  clear hc
  at_cost K hK
  unfold runs
  have hx' : (if last then xs.reverse else xs) = U :: (List.replicate (m + 1) U ++ tl) := by
    rw [hx]; rfl
  simp only [Cost.bind_ticks, over_view, Charged.viewNode, Charged.op_val, hv,
    NodeView.forget, hx', foldL_std, hys]
  refine Nat.le_trans ?_ (Nat.le_add_left _ _)
  refine Nat.le_trans ?_ (Nat.le_add_left _ _)
  refine Nat.le_trans ?_ (Cost.foldL_append_ticks _ _ _ _)
  refine Nat.le_trans (Nat.le_of_eq ?_) (fans_fold_ticks hinj _ _ hEf hEt
    (List.replicate (m + 1) U) (fun x hx rs hany => ?_) 1 ys (Nat.le_refl 1) hF1 (by simp))
  · rw [List.length_replicate, show 1 + (m + 1) - 1 = m + 1 by omega]
  · obtain rfl := List.eq_of_mem_replicate hx
    simp only [hany, ↓reduceIte, Cost.bind_val, hys, Cost.pure_val, Cost.bind_ticks]
    exact ⟨trivial, by omega⟩

/-- To a depth of two or less the reading returns nothing. -/
theorem runs_shallow (last : Bool) {n U : Rel} {xs tl : List Rel} {sa sb : Span}
    (hv : n.view = .chain xs) (hx : (if last then xs.reverse else xs) = U :: tl)
    (hU : U.view = .union [.span sa, .span sb]) (d : Nat) (hd : d ≤ 2) (seen : List Rel) :
    (runs (K := DerivationKernel.over D K hK P) last d seen n).val = none := by
  have hU1 : (runs (K := DerivationKernel.over D K hK P) last 1 seen U).val = none := by
    at_cost K hK
    unfold runs
    simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hU, NodeView.forget,
      foldL_std, Cost.foldL_val, List.foldl]
    rfl
  at_cost K hK
  have hfix : ∀ (G : Option (List (Run R)) → Rel → Cost (Option (List (Run R))))
      (_ : ∀ x, (G none x).val = none) (ys : List Rel), (Cost.foldL G none ys).val = none :=
    fun G hG ys => by rw [Cost.foldL_val]; exact List.foldl_fixed' hG ys
  match d, hd with
  | 0, _ => rfl
  | 1, _ =>
    unfold runs
    simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget,
      hx, foldL_std]
    have h0 : (runs (K := DerivationKernel.over D _ hK P) last 0 seen U).val = none := rfl
    rw [h0]
    exact hfix _ (fun _ => rfl) _
  | 2, _ =>
    unfold runs
    simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget,
      hx, foldL_std]
    rw [hU1]
    exact hfix _ (fun _ => rfl) _

/-- A chain with a member that is never found free of calls is never found
free of calls. -/
theorem hasCall_chain_ne_false {n : Rel} {xs : List Rel} (hv : n.view = .chain xs)
    (hcall : ∃ x ∈ xs, ∀ d, (hasCall (K := DerivationKernel.over D K hK P) d x).val ≠ some false)
    (d : Nat) : (hasCall (K := DerivationKernel.over D K hK P) d n).val ≠ some false := by
  at_cost K hK
  cases d with
  | zero => intro h; cases h
  | succ d =>
    unfold hasCall
    simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget,
      foldL_std, Cost.foldL_val]
    obtain ⟨x, hx, hxc⟩ := hcall
    have key : ∀ (ys : List Rel) (acc : Option Bool), (acc ≠ some false ∨ x ∈ ys) →
        ys.foldl (fun (acc : Option Bool) y => (match acc with
          | some false => hasCall (K := DerivationKernel.over D _ hK P) d y
          | r => pure r : Cost (Option Bool)).val) acc ≠ some false := by
      intro ys
      induction ys with
      | nil =>
        intro acc h
        rcases h with h | h
        · exact h
        · cases h
      | cons y ys ih =>
        intro acc h
        rw [List.foldl_cons]
        refine ih _ ?_
        by_cases hacc : acc = some false
        · subst hacc
          rcases h with h | h
          · exact absurd rfl h
          · rcases List.mem_cons.1 h with rfl | h
            · exact .inl (hxc d)
            · exact .inr h
        · left
          cases acc with
          | none => intro h'; cases h'
          | some b =>
            cases b
            · exact absurd rfl hacc
            · intro h'; cases h'
    exact key xs (some false) (.inr hx)

/-- A chain whose members are each decided at a depth is decided one
deeper. -/
theorem hasCall_chain_ne_none {n : Rel} {xs : List Rel} (hv : n.view = .chain xs) (d : Nat)
    (hdeep : ∀ x ∈ xs, (hasCall (K := DerivationKernel.over D K hK P) d x).val ≠ none) :
    (hasCall (K := DerivationKernel.over D K hK P) (d + 1) n).val ≠ none := by
  at_cost K hK
  unfold hasCall
  simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget,
    foldL_std, Cost.foldL_val]
  have key : ∀ (ys : List Rel) (acc : Option Bool), (∀ y ∈ ys, y ∈ xs) → acc ≠ none →
      ys.foldl (fun (acc : Option Bool) y => (match acc with
        | some false => hasCall (K := DerivationKernel.over D _ hK P) d y
        | r => pure r : Cost (Option Bool)).val) acc ≠ none := by
    intro ys
    induction ys with
    | nil => exact fun acc _ h => h
    | cons y ys ih =>
      intro acc hys h
      rw [List.foldl_cons]
      refine ih _ (fun z hz => hys z (List.mem_cons_of_mem _ hz)) ?_
      cases acc with
      | none => exact absurd rfl h
      | some b =>
        cases b
        · exact hdeep y (hys y List.mem_cons_self)
        · intro h'; cases h'
  exact key xs (some false) (fun _ h => h) (by intro h; cases h)

/-- **What `readEdge` spends on an edge of `m + 2` unions of two spans.** If
it returns something, or reads to a depth of three or more, it has spent
`2 ^ (m + 1)` ticks. -/
theorem readEdge_dear {M : Interp} (hL : D.Lawful M) (hc : ∀ a b : R, 1 ≤ (K.compose a b).ticks)
    (last : Bool) {n U : Rel} {xs tl : List Rel} {m : Nat} {sa sb : Span} {rsp : Bool → R}
    (hv : n.view = .chain xs)
    (hx : (if last then xs.reverse else xs) = List.replicate (m + 2) U ++ tl)
    (hU : U.view = .union [.span sa, .span sb]) (ha : D.rep sa = some (rsp true))
    (hb : D.rep sb = some (rsp false)) {Wd : List Bool → PRel}
    (hW1 : ∀ b, Wd [b] = den M (rsp b))
    (hW : ∀ w b, w ≠ [] → Wd (w ++ [b]) =
      if last then (den M (rsp b)).comp (Wd w) else (Wd w).comp (den M (rsp b)))
    (hne : ∀ w, (Wd w).Nonempty)
    (hinj : ∀ j, ∀ w w' : List Bool, w.length = j → w'.length = j → Wd w = Wd w' → w = w')
    (hcall : ∃ x ∈ xs, ∀ d, (hasCall (K := DerivationKernel.over D K hK P) d x).val ≠ some false)
    (hdeep : ∀ x ∈ xs, ∀ d, (hasCall (K := DerivationKernel.over D K hK P) (d + 2) x).val ≠ none)
    (depth : Nat) :
    (3 ≤ depth ∨ ∃ e, (readEdge (K := DerivationKernel.over D K hK P) last depth n).val = some e) →
      2 ^ (m + 1) ≤ (readEdge (K := DerivationKernel.over D K hK P) last depth n).ticks := by
  have hruns := fun d => runs_dear (K := K) (hK := hK) (P := P) hL hc last hv hx hU ha hb hW1 hW
    hne hinj d []
  have hsh := fun d hd => runs_shallow (K := K) (hK := hK) (P := P) last hv
    (show (if last then xs.reverse else xs) = U :: (List.replicate (m + 1) U ++ tl) by rw [hx]; rfl)
    hU d hd []
  have hnf := hasCall_chain_ne_false (K := K) (hK := hK) (P := P) hv hcall
  have hnn := fun d => hasCall_chain_ne_none (K := K) (hK := hK) (P := P) hv (d + 2)
    fun x hx => hdeep x hx d
  clear hc hcall hdeep
  at_cost K hK
  intro h
  have hcv : ∀ d, 3 ≤ d → (hasCall (K := DerivationKernel.over D _ hK P) d n).val = some true := by
    intro d hd
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 3 := ⟨d - 3, by omega⟩
    cases hv' : (hasCall (K := DerivationKernel.over D _ hK P) (d + 3) n).val with
    | none => exact absurd hv' (hnn d)
    | some b =>
      cases b
      · exact absurd hv' (hnf _)
      · rfl
  have deep : ∀ d, 3 ≤ d →
      2 ^ (m + 1) ≤ (readEdge (K := DerivationKernel.over D _ hK P) last d n).ticks := by
    intro d hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 3 := ⟨d - 3, by omega⟩
    have h1 := hcv (d' + 3) hd
    have h2 := hruns d'
    simp only [readEdge, offered, readRuns, Cost.bind_ticks, h1]
    omega
  rcases h with h | ⟨e, he⟩
  · exact deep depth h
  · by_cases hd : 3 ≤ depth
    · exact deep depth hd
    · exfalso
      have h2 := hsh depth (by omega)
      simp only [readEdge, offered, readRuns, Cost.bind_val] at he
      cases hcv' : (hasCall (K := DerivationKernel.over D _ hK P) depth n).val with
      | none => rw [hcv'] at he; cases he
      | some b =>
        cases b
        · exact hnf depth hcv'
        · rw [hcv'] at he
          simp only [Cost.bind_val, h2, Cost.pure_val] at he
          cases he

end kernel

end Symmetric

end RwLog
