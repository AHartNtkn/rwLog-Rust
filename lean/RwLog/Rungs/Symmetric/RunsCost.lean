/-
# What reading an edge inwards costs on a chain of unions of two spans

`runs` follows an edge of a chain inwards and carries whole products of
spans. On a chain that has, at the edge read, `m + 2` members that are each
the same union of two spans, it carries every product of a choice of one
span from each, when the products of different choices relate different
pairs. With a kernel that charges a tick or more for a composition, reading
the last of these members costs `2 ^ (m + 1)` ticks (`runs_dear`).

A reading that is led into such a chain pays for it: through copies of a
span at the end read, and then a union that has the chain for a member
(`runs_chain_reach`, `runs_union_reach`). So `readEdge` on such a side has
spent `2 ^ (m + 1)` ticks if it returns something or reads to a depth of
five (`readEdge_side_dear`).
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

/-- A fold spends what its first step spends. -/
theorem foldL_cons_ticks (f : β → α → Cost β) (x : α) (xs : List α) (b : β) :
    (f b x).ticks ≤ (foldL f b (x :: xs)).ticks := by
  simp only [foldL, bind_ticks]
  omega

/-- A fold over a list spends what the fold over its last part spends, from
where the first part left it. -/
theorem foldL_append_ticks_ge (f : β → α → Cost β) :
    ∀ (xs ys : List α) (b : β),
      (foldL f (foldL f b xs).val ys).ticks ≤ (foldL f b (xs ++ ys)).ticks
  | [], _, _ => Nat.le_refl _
  | x :: xs, ys, b => by
    have := foldL_append_ticks_ge f xs ys (f b x).val
    simp only [List.cons_append, foldL, bind_ticks, bind_val]
    omega

/-- A fold of steps that may stop: while each step of the first part goes
on, and keeps `I`, the step at the member `y` is made, and the fold spends
what that step spends. -/
theorem foldL_reach_ticks {γ : Type} (G : Option γ → α → Cost (Option γ)) (I : γ → Prop)
    (pre post : List α) (y : α) (X : Nat)
    (hpre : ∀ c, I c → ∀ x ∈ pre, ∃ c', (G (some c) x).val = some c' ∧ I c')
    (hy : ∀ c, I c → X ≤ (G (some c) y).ticks) (c0 : γ) (h0 : I c0) :
    X ≤ (foldL G (some c0) (pre ++ y :: post)).ticks := by
  have hI : ∃ c, (foldL G (some c0) pre).val = some c ∧ I c :=
    foldL_inv (fun b => ∃ c, b = some c ∧ I c) G pre
      (fun b x hx hb => by obtain ⟨c, rfl, hc⟩ := hb; exact hpre c hc x hx) _ ⟨c0, rfl, h0⟩
  obtain ⟨c, hc, hIc⟩ := hI
  refine Nat.le_trans ?_ (foldL_append_ticks_ge G pre (y :: post) (some c0))
  rw [hc]
  exact Nat.le_trans (hy c hIc) (foldL_cons_ticks G y post (some c))

/-- The same fold returns nothing if the step at `y` stops. -/
theorem foldL_reach_none {γ : Type} (G : Option γ → α → Cost (Option γ)) (I : γ → Prop)
    (pre post : List α) (y : α)
    (hpre : ∀ c, I c → ∀ x ∈ pre, ∃ c', (G (some c) x).val = some c' ∧ I c')
    (hy : ∀ c, I c → (G (some c) y).val = none) (hnone : ∀ x, (G none x).val = none)
    (c0 : γ) (h0 : I c0) : (foldL G (some c0) (pre ++ y :: post)).val = none := by
  have hI : ∃ c, (foldL G (some c0) pre).val = some c ∧ I c :=
    foldL_inv (fun b => ∃ c, b = some c ∧ I c) G pre
      (fun b x hx hb => by obtain ⟨c, rfl, hc⟩ := hb; exact hpre c hc x hx) _ ⟨c0, rfl, h0⟩
  obtain ⟨c, hc, hIc⟩ := hI
  have e : (foldL G (some c0) (pre ++ y :: post)).val =
      (foldL G (foldL G (some c0) pre).val (y :: post)).val := by
    simp only [foldL_val, List.foldl_append]
  rw [e, hc]
  show (foldL G (G (some c) y).val post).val = none
  rw [hy c hIc, foldL_val]
  exact List.foldl_fixed' hnone post

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

/-- A chain or a union whose members are each decided at a depth is decided
one deeper. -/
theorem hasCall_ne_none {n : Rel} {xs : List Rel}
    (hv : n.view = .chain xs ∨ n.view = .union xs) (d : Nat)
    (hdeep : ∀ x ∈ xs, (hasCall (K := DerivationKernel.over D K hK P) d x).val ≠ none) :
    (hasCall (K := DerivationKernel.over D K hK P) (d + 1) n).val ≠ none := by
  at_cost K hK
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
  unfold hasCall
  rcases hv with hv | hv <;>
  · simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget,
      foldL_std, Cost.foldL_val]
    exact key xs (some false) (fun _ h => h) (by intro h; cases h)

/-- A span is found free of calls, to any depth but none. -/
theorem hasCall_span_val (d : Nat) (s : Span) :
    (hasCall (K := DerivationKernel.over D K hK P) (d + 1) (.span s)).val = some false := by
  at_cost K hK
  unfold hasCall
  simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, RelOf.view,
    NodeView.forget, Cost.pure_val]

/-- A call is found to be one, to any depth but none. -/
theorem hasCall_call_val {n : Rel} {c : Name} {f : Bool} (hv : n.view = .call c f) (d : Nat) :
    (hasCall (K := DerivationKernel.over D K hK P) (d + 1) n).val = some true := by
  at_cost K hK
  unfold hasCall
  simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget,
    Cost.pure_val]

theorem hasCall_call_ne_false {n : Rel} {c : Name} {f : Bool} (hv : n.view = .call c f)
    (d : Nat) : (hasCall (K := DerivationKernel.over D K hK P) d n).val ≠ some false := by
  cases d with
  | zero =>
    at_cost K hK
    intro h; cases h
  | succ d => rw [hasCall_call_val hv]; intro h; cases h

/-- To a depth of one, a chain or a union with a member is not read. -/
theorem runs_one (last : Bool) {n : Rel} {xs : List Rel}
    (hv : n.view = .chain xs ∨ n.view = .union xs) (hne : xs ≠ []) (seen : List Rel) :
    (runs (K := DerivationKernel.over D K hK P) last 1 seen n).val = none := by
  at_cost K hK
  have hfix : ∀ (G : Option (List (Run R)) → Rel → Cost (Option (List (Run R))))
      (_ : ∀ x, (G none x).val = none) (ys : List Rel), (Cost.foldL G none ys).val = none :=
    fun G hG ys => by rw [Cost.foldL_val]; exact List.foldl_fixed' hG ys
  have h0 : ∀ x, (runs (K := DerivationKernel.over D _ hK P) last 0 seen x).val = none :=
    fun _ => rfl
  unfold runs
  rcases hv with hv | hv
  · simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget]
    have hne' : (if last then xs.reverse else xs) ≠ [] := by
      cases last <;> simpa using hne
    split
    · next e => exact absurd e hne'
    · simp only [Cost.bind_val, foldL_std, h0]
      exact hfix _ (fun _ => rfl) _
  · obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget,
      foldL_std, Cost.foldL, h0]
    exact hfix _ (fun _ => rfl) _

/-- The runs of a span are something, to any depth but none. -/
theorem runs_span_some (last : Bool) (d : Nat) (seen : List Rel) (s : Span) :
    ∃ r, (runs (K := DerivationKernel.over D K hK P) last (d + 1) seen (.span s)).val = some r := by
  at_cost K hK
  unfold runs
  simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, RelOf.view,
    NodeView.forget, Cost.pure_val]
  exact ⟨_, rfl⟩

/-- Reading a union whose members before `B` are spans reads `B`: it spends
what reading `B` spends, and returns nothing if reading `B` does. -/
theorem runs_union_reach (last : Bool) {Ud B : Rel} {pre post : List Rel}
    (hU : Ud.view = .union (pre ++ B :: post)) (hpre : ∀ x ∈ pre, ∃ s, x = .span s)
    (d : Nat) (seen : List Rel) :
    (runs (K := DerivationKernel.over D K hK P) last (d + 1) seen B).ticks ≤
        (runs (K := DerivationKernel.over D K hK P) last (d + 2) seen Ud).ticks ∧
      ((runs (K := DerivationKernel.over D K hK P) last (d + 1) seen B).val = none →
        (runs (K := DerivationKernel.over D K hK P) last (d + 2) seen Ud).val = none) := by
  have hspan := fun s => runs_span_some (K := K) (hK := hK) (P := P) last d seen s
  at_cost K hK
  constructor
  · conv_rhs => unfold runs
    simp only [Cost.bind_ticks, over_view, Charged.viewNode, Charged.op_val, hU,
      NodeView.forget, foldL_std]
    refine Nat.le_trans ?_ (Nat.le_add_left _ _)
    refine Cost.foldL_reach_ticks _ (fun _ => True) pre post B _ (fun c _ x hx => ?_)
      (fun c _ => ?_) [] trivial
    · obtain ⟨s, rfl⟩ := hpre x hx
      obtain ⟨r, hr⟩ := hspan s
      simp only [Cost.bind_val, hr, Cost.pure_val]
      exact ⟨_, rfl, trivial⟩
    · simp only [Cost.bind_ticks]
      omega
  · intro hB
    unfold runs
    simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hU,
      NodeView.forget, foldL_std]
    refine Cost.foldL_reach_none _ (fun _ => True) pre post B (fun c _ x hx => ?_)
      (fun c _ => ?_) (fun _ => rfl) [] trivial
    · obtain ⟨s, rfl⟩ := hpre x hx
      obtain ⟨r, hr⟩ := hspan s
      simp only [Cost.bind_val, hr, Cost.pure_val]
      exact ⟨_, rfl, trivial⟩
    · simp only [Cost.bind_val, hB]
      rfl

/-- Reading a chain that has, at the end read, copies of one span that
composes with itself to itself and then the member `Ud`, reads `Ud`: it
spends what reading `Ud` spends, and returns nothing if reading `Ud`
does. -/
theorem runs_chain_reach {M : Interp} (hL : D.Lawful M) (last : Bool) {n Ud : Rel}
    {xs ids tl : List Rel} {sid : Span} {rid : R} (hv : n.view = .chain xs)
    (hx : (if last then xs.reverse else xs) = ids ++ Ud :: tl)
    (hids : ∀ x ∈ ids, x = .span sid) (hrid : D.rep sid = some rid)
    (hid : (den M rid).comp (den M rid) = den M rid) (d : Nat) (seen : List Rel) :
    (runs (K := DerivationKernel.over D K hK P) last (d + 1) seen Ud).ticks ≤
        (runs (K := DerivationKernel.over D K hK P) last (d + 2) seen n).ticks ∧
      ((runs (K := DerivationKernel.over D K hK P) last (d + 1) seen Ud).val = none →
        (runs (K := DerivationKernel.over D K hK P) last (d + 2) seen n).val = none) := by
  have h1 := runs_span_val (K := K) (hK := hK) (P := P) last d seen hrid
  have hext := fun rs ys => extendRuns_spec (K := K) (hK := hK) (P := P) last rs ys
  have hstep : ∀ rs : List (Run R), (∃ s, (some s, true) ∈ rs ∧ den M s = den M rid) →
      ∃ s, (some s, true) ∈ (extendRuns (K := DerivationKernel.over D K hK P) last rs
        [(some rid, true)]).val ∧ den M s = den M rid := by
    rintro rs ⟨s, hs, hds⟩
    have hsp := (hext rs [(some rid, true)]).2 s hs _ (List.mem_singleton_self _)
    have hne : ((den M rid).comp (den M rid)).Nonempty := by rw [hid]; exact hL.live rid
    cases last with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hsp
      cases hcp : D.compose s rid with
      | none =>
        have := hL.compose_none _ _ hcp
        rw [hds] at this
        exact absurd this hne.ne_empty
      | some c => exact ⟨c, hsp c hcp, by rw [hL.compose_some _ _ _ hcp, hds, hid]⟩
    | true =>
      simp only [ite_true] at hsp
      cases hcp : D.compose rid s with
      | none =>
        have := hL.compose_none _ _ hcp
        rw [hds] at this
        exact absurd this hne.ne_empty
      | some c => exact ⟨c, hsp c hcp, by rw [hL.compose_some _ _ _ hcp, hds, hid]⟩
  have hany : ∀ rs : List (Run R), (∃ s, (some s, true) ∈ rs ∧ den M s = den M rid) →
      rs.any (·.2) = true := fun rs ⟨s, hs, _⟩ => List.any_eq_true.2 ⟨_, hs, rfl⟩
  at_cost K hK
  have hfix : ∀ (G : Option (List (Run R)) → Rel → Cost (Option (List (Run R))))
      (_ : ∀ x, (G none x).val = none) (ys : List Rel), (Cost.foldL G none ys).val = none :=
    fun G hG ys => by rw [Cost.foldL_val]; exact List.foldl_fixed' hG ys
  cases ids with
  | nil =>
    rw [List.nil_append] at hx
    constructor
    · conv_rhs => unfold runs
      simp only [Cost.bind_ticks, over_view, Charged.viewNode, Charged.op_val, hv,
        NodeView.forget, hx]
      omega
    · intro hB
      unfold runs
      simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv,
        NodeView.forget, hx, foldL_std]
      rw [hB]
      exact hfix _ (fun _ => rfl) _
  | cons i0 ids =>
    obtain rfl := hids i0 List.mem_cons_self
    have hids' : ∀ x ∈ ids, x = RelOf.span sid := fun x hx => hids x (List.mem_cons_of_mem _ hx)
    rw [List.cons_append] at hx
    constructor
    · conv_rhs => unfold runs
      simp only [Cost.bind_ticks, over_view, Charged.viewNode, Charged.op_val, hv,
        NodeView.forget, hx, foldL_std, h1]
      refine Nat.le_trans ?_ (Nat.le_add_left _ _)
      refine Nat.le_trans ?_ (Nat.le_add_left _ _)
      refine Cost.foldL_reach_ticks _
        (fun c => ∃ s, (some s, true) ∈ c ∧ den M s = den M rid) ids tl Ud _
        (fun c hc x hx => ?_) (fun c hc => ?_) _ ⟨rid, List.mem_singleton_self _, rfl⟩
      · obtain rfl := hids' x hx
        refine ⟨_, ?_, hstep c hc⟩
        simp only [hany c hc, ↓reduceIte, Cost.bind_val, h1, Cost.pure_val]
      · simp only [hany c hc, ↓reduceIte, Cost.bind_ticks]
        omega
    · intro hB
      unfold runs
      simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op_val, hv,
        NodeView.forget, hx, foldL_std, h1]
      refine Cost.foldL_reach_none _
        (fun c => ∃ s, (some s, true) ∈ c ∧ den M s = den M rid) ids tl Ud
        (fun c hc x hx => ?_) (fun c hc => ?_) (fun _ => rfl) _
        ⟨rid, List.mem_singleton_self _, rfl⟩
      · obtain rfl := hids' x hx
        refine ⟨_, ?_, hstep c hc⟩
        simp only [hany c hc, ↓reduceIte, Cost.bind_val, h1, Cost.pure_val]
      · simp only [hany c hc, ↓reduceIte, Cost.bind_val, hB]
        rfl

/-- **What `readEdge` spends on a node whose runs are dear.** Reading the
runs of the node to the depth `T` or more spends `X`, and to a lesser depth
returns nothing; the node is never found free of calls, and to the depth `T`
it is found to have one. If `readEdge` returns something, or reads to the
depth `T` or more, it has spent `X` ticks. -/
theorem readEdge_of_runs (last : Bool) {n : Rel} {X T : Nat}
    (hruns : ∀ d, X ≤ (runs (K := DerivationKernel.over D K hK P) last (d + T) [] n).ticks)
    (hsh : ∀ d, d < T → (runs (K := DerivationKernel.over D K hK P) last d [] n).val = none)
    (hnf : ∀ d, (hasCall (K := DerivationKernel.over D K hK P) d n).val ≠ some false)
    (hnn : ∀ d, (hasCall (K := DerivationKernel.over D K hK P) (d + T) n).val ≠ none)
    (depth : Nat) :
    (T ≤ depth ∨ ∃ e, (readEdge (K := DerivationKernel.over D K hK P) last depth n).val = some e) →
      X ≤ (readEdge (K := DerivationKernel.over D K hK P) last depth n).ticks := by
  at_cost K hK
  intro h
  have hcv : ∀ d, T ≤ d → (hasCall (K := DerivationKernel.over D _ hK P) d n).val = some true := by
    intro d hd
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + T := ⟨d - T, by omega⟩
    cases hv' : (hasCall (K := DerivationKernel.over D _ hK P) (d + T) n).val with
    | none => exact absurd hv' (hnn d)
    | some b =>
      cases b
      · exact absurd hv' (hnf _)
      · rfl
  have deep : ∀ d, T ≤ d →
      X ≤ (readEdge (K := DerivationKernel.over D _ hK P) last d n).ticks := by
    intro d hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + T := ⟨d - T, by omega⟩
    have h1 := hcv (d' + T) hd
    have h2 := hruns d'
    simp only [readEdge, offered, readRuns, Cost.bind_ticks, h1]
    omega
  rcases h with h | ⟨e, he⟩
  · exact deep depth h
  · by_cases hd : T ≤ depth
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

/-- **What `readEdge` spends on a side that leads into a chain of unions.**
The node is a chain. From the end read it has copies of one span that
composes with itself to itself, then a union with a member `B`, then calls.
`B` is a chain of `m + 2` copies of a union of two spans, whose products
relate different pairs. At a kernel that charges a tick or more for a
composition, `readEdge` has spent `2 ^ (m + 1)` ticks if it returns
something or reads to a depth of five or more. -/
theorem readEdge_side_dear {M : Interp} (hL : D.Lawful M)
    (hc : ∀ a b : R, 1 ≤ (K.compose a b).ticks) (last : Bool) {n Ud B U : Rel}
    {xs ids tl pre post bs : List Rel} {m : Nat} {sid sa sb : Span} {rid : R} {rsp : Bool → R}
    (hv : n.view = .chain xs) (hx : (if last then xs.reverse else xs) = ids ++ Ud :: tl)
    (hids : ∀ x ∈ ids, x = .span sid) (hrid : D.rep sid = some rid)
    (hid : (den M rid).comp (den M rid) = den M rid)
    (htl : ∀ x ∈ tl, ∃ c f, x.view = .call c f) (htl0 : tl ≠ [])
    (hUd : Ud.view = .union (pre ++ B :: post)) (hpre : ∀ x ∈ pre, ∃ s, x = .span s)
    (hpost : ∀ x ∈ post, ∃ s, x = .span s)
    (hB : B.view = .chain bs) (hbx : (if last then bs.reverse else bs) = List.replicate (m + 2) U)
    (hU : U.view = .union [.span sa, .span sb]) (ha : D.rep sa = some (rsp true))
    (hb : D.rep sb = some (rsp false)) {Wd : List Bool → PRel}
    (hW1 : ∀ b, Wd [b] = den M (rsp b))
    (hW : ∀ w b, w ≠ [] → Wd (w ++ [b]) =
      if last then (den M (rsp b)).comp (Wd w) else (Wd w).comp (den M (rsp b)))
    (hne : ∀ w, (Wd w).Nonempty)
    (hinj : ∀ j, ∀ w w' : List Bool, w.length = j → w'.length = j → Wd w = Wd w' → w = w')
    (depth : Nat) :
    (5 ≤ depth ∨ ∃ e, (readEdge (K := DerivationKernel.over D K hK P) last depth n).val = some e) →
      2 ^ (m + 1) ≤ (readEdge (K := DerivationKernel.over D K hK P) last depth n).ticks := by
  have hbx' : (if last then bs.reverse else bs) = List.replicate (m + 2) U ++ [] := by
    rw [List.append_nil]; exact hbx
  have hmem : ∀ x, x ∈ xs ↔ x ∈ ids ++ Ud :: tl := fun x => by
    rw [← hx]; cases last <;> simp
  have hbs : ∀ x ∈ bs, x = U := fun x hxb => by
    have : x ∈ (if last then bs.reverse else bs) := by cases last <;> simpa using hxb
    rw [hbx] at this
    exact List.eq_of_mem_replicate this
  have hne1 : ids ++ Ud :: tl ≠ [] := by simp
  have hxs : xs ≠ [] := by
    intro e; rw [e] at hx; cases last <;> simp at hx
  have chain := fun d => runs_chain_reach (K := K) (hK := hK) (P := P) hL last hv hx hids hrid hid
    d []
  have union := fun d => runs_union_reach (K := K) (hK := hK) (P := P) last hUd hpre d []
  have dear := fun d => runs_dear (K := K) (hK := hK) (P := P) hL hc last hB hbx' hU ha hb hW1 hW
    hne hinj d []
  have shallow := fun d hd => runs_shallow (K := K) (hK := hK) (P := P) last hB
    (show (if last then bs.reverse else bs) = U :: List.replicate (m + 1) U by rw [hbx]; rfl)
    hU d hd []
  -- the members of the node, of the union and of `B` are decided
  have dU : ∀ d, (hasCall (K := DerivationKernel.over D K hK P) (d + 2) U).val ≠ none :=
    fun d => hasCall_ne_none (.inr hU) (d + 1) fun x hxm => by
      rcases List.mem_cons.1 hxm with rfl | hxm
      · rw [hasCall_span_val]; intro h; cases h
      · obtain rfl := List.mem_singleton.1 hxm
        rw [hasCall_span_val]; intro h; cases h
  have dB : ∀ d, (hasCall (K := DerivationKernel.over D K hK P) (d + 3) B).val ≠ none :=
    fun d => hasCall_ne_none (.inl hB) (d + 2) fun x hxm => by
      obtain rfl := hbs x hxm
      exact dU d
  have dUd : ∀ d, (hasCall (K := DerivationKernel.over D K hK P) (d + 4) Ud).val ≠ none :=
    fun d => hasCall_ne_none (.inr hUd) (d + 3) fun x hxm => by
      rcases List.mem_append.1 hxm with hxm | hxm
      · obtain ⟨s, rfl⟩ := hpre x hxm
        rw [hasCall_span_val]; intro h; cases h
      · rcases List.mem_cons.1 hxm with rfl | hxm
        · exact dB d
        · obtain ⟨s, rfl⟩ := hpost x hxm
          rw [hasCall_span_val]; intro h; cases h
  refine readEdge_of_runs (T := 5) last (fun d => ?_) (fun d hd => ?_) (fun d => ?_) (fun d => ?_)
    depth
  · exact Nat.le_trans (dear d) (Nat.le_trans (union (d + 2)).1 (chain (d + 3)).1)
  · match d, hd with
    | 0, _ =>
      at_cost K hK
      rfl
    | 1, _ => exact runs_one last (.inl hv) hxs []
    | 2, _ =>
      exact (chain 0).2 (runs_one last (.inr hUd) (by simp) [])
    | 3, _ => exact (chain 1).2 ((union 0).2 (shallow 1 (by decide)))
    | 4, _ => exact (chain 2).2 ((union 1).2 (shallow 2 (by decide)))
  · obtain ⟨x, hxt⟩ := List.exists_mem_of_ne_nil tl htl0
    obtain ⟨c, f, hcf⟩ := htl x hxt
    exact hasCall_chain_ne_false hv ⟨x, (hmem x).2 (by simp [hxt]), hasCall_call_ne_false hcf⟩ d
  · refine hasCall_ne_none (.inl hv) (d + 4) fun x hxm => ?_
    rcases List.mem_append.1 ((hmem x).1 hxm) with hxi | hxi
    · obtain rfl := hids x hxi
      rw [hasCall_span_val]; intro h; cases h
    · rcases List.mem_cons.1 hxi with rfl | hxi
      · exact dUd d
      · obtain ⟨c, f, hcf⟩ := htl x hxi
        rw [hasCall_call_val hcf]; intro h; cases h

end kernel

end Symmetric

end RwLog
