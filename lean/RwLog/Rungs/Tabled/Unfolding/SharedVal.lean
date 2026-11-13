/-
# The shared evaluation, read off its text

`Unfold.evalS` computes the summary of a node after a context and threads a
memo of the summaries it has computed. What it returns is what the same text
returns without the kernel's monad: `evalSV`, with `sufSV` for the members of
a chain, `membersSV` for the members of a meet and `memoV` for the lookup.

`sharedRace_val`: the race answered with shared work says the unfolding is
final when the summary of the goal has no open product, and then returns its
answers.
-/
import RwLog.Rungs.Tabled.Unfolding.Walk

namespace RwLog

namespace Tabled

namespace Unfold

open Answer Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The summaries at the derivation kernel of a domain. -/
abbrev Sm (D : Domain R) (P : Program) := Summary R (Ans D P)

/-- The memos at the derivation kernel of a domain. -/
abbrev Mm (D : Domain R) (P : Program) := Memo R Rel (Ans D P)

variable (K : Kernel R Cost) (hK : K.Refines D)

/-! ## The memo -/

/-- Are the two keys the same? -/
def sameKeyV (k k' : Key R Rel) : Bool :=
  if k.idx = k'.idx ∧ k.d = k'.d ∧ k.near.pushed = k'.near.pushed then
    if decide (k.node = k'.node) then
      if decide (k.near.bound = k'.near.bound) then decide (k.far = k'.far) else false
    else false
  else false

omit [Answer R] in
theorem sameKeyV_eq {k k' : Key R Rel} (h : sameKeyV k k' = true) : k = k' := by
  obtain ⟨n, i, d, ⟨b, p⟩, f⟩ := k
  obtain ⟨n', i', d', ⟨b', p'⟩, f'⟩ := k'
  unfold sameKeyV at h
  simp only at h
  split at h
  · next h₁ =>
    split at h
    · next h₂ =>
      split at h
      · next h₃ =>
        obtain ⟨rfl, rfl, rfl⟩ := h₁
        obtain rfl := of_decide_eq_true h₂
        obtain rfl := of_decide_eq_true h₃
        obtain rfl := of_decide_eq_true h
        rfl
      · cases h
    · cases h
  · cases h

theorem sameKey_val (k k' : Key R Rel) :
    (sameKey (A := Ans D P) (K := DerivationKernel.over D K hK P) k k').val = sameKeyV k k' := by
  have sb := sameBound_val (P := P) K hK
  at_cost K hK
  simp only [sameKey, sameKeyV, Cost.bind_val, ite_val, over_eqNode, Charged.eqNode, Charged.op,
    sb, Cost.pure_val]

/-- The summary recorded for a key. -/
def lookupV (m : Mm D P) (k : Key R Rel) : Option (Sm D P) :=
  (m.find? fun p => sameKeyV p.1 k).map Prod.snd

theorem lookup_val (m : Mm D P) (k : Key R Rel) :
    (lookup (K := DerivationKernel.over D K hK P) m k).val = lookupV m k := by
  have sk := sameKey_val (P := P) K hK
  at_cost K hK
  simp only [lookup, lookupV, Cost.bind_val, Cost.pure_val, findL_std, Cost.findL_val, sk]

/-- Look the key up; compute and record the summary if it is not there. -/
def memoV (k : Key R Rel) (m : Mm D P) (body : Mm D P → Sm D P × Mm D P) : Sm D P × Mm D P :=
  match lookupV m k with
  | some s => (s, m)
  | none => ((body m).1, (k, (body m).1) :: (body m).2)

theorem memo_val (k : Key R Rel) (m : Mm D P) (body : Mm D P → Cost (Sm D P × Mm D P)) :
    (memo (K := DerivationKernel.over D K hK P) k m body).val =
      memoV k m (fun m => (body m).val) := by
  have lk := lookup_val (P := P) K hK
  at_cost K hK
  simp only [memo, memoV, Cost.bind_val, lk]
  cases lookupV m k <;> simp only [Cost.pure_val, Cost.bind_val]

/-! ## Summaries -/

/-- Add an interface unless it is already there. -/
def addOpenV (xs : List (Option R)) (x : Option R) : List (Option R) :=
  if xs.any (fun y => decide (y = x)) then xs else xs ++ [x]

theorem addOpen_val (xs : List (Option R)) (x : Option R) :
    (addOpen (A := Ans D P) (K := DerivationKernel.over D K hK P) xs x).val = addOpenV xs x := by
  have sb := sameBound_val (P := P) K hK
  at_cost K hK
  simp only [addOpen, addOpenV, Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val, sb]

/-- Add the products of one summary to another. -/
def addSummaryV (s : Sm D P) (closed : List (Ans D P)) (opens : List (Option R)) : Sm D P :=
  ⟨closed.foldl keepNew s.closed, opens.foldl addOpenV s.opens⟩

theorem addSummary_val (s : Sm D P) (closed : List (Ans D P)) (opens : List (Option R)) :
    (addSummary (K := DerivationKernel.over D K hK P) s closed opens).val =
      addSummaryV s closed opens := by
  have ea := addAns_val (P := P) K hK
  have eo := addOpen_val (P := P) K hK
  at_cost K hK
  simp only [addSummary, addSummaryV, Cost.bind_val, Cost.pure_val, foldL_std, Cost.foldL_val,
    ea, eo]

/-! ## A chain -/

/-- The summary of the members `xs` of the chain `n`, which start at its
`i`-th member, after the context `c`. -/
def sufSV (wv : Near R → Rel → Option R → Mm D P → Sm D P × Mm D P) (n : Rel) (d : Nat)
    (far : Option R) : Nat → List Rel → Near R → Mm D P → Sm D P × Mm D P
  | _, [], _, m => (⟨[], []⟩, m)
  | _, [x], c, m => wv c x far m
  | i, x :: y :: xs, c, m =>
    (if i = 0 then fun body => body m else memoV ⟨n, i, d, c, far⟩ m) fun m =>
      (wv c x none m).1.opens.foldl
        (fun (acc : Sm D P × Mm D P) o =>
          (addSummaryV acc.1 []
            ((sufSV wv n d far (i + 1) (y :: xs) ⟨o, o.isSome⟩ acc.2).1.closed.map
                (fun b => D.rightBound b.span) ++
              (sufSV wv n d far (i + 1) (y :: xs) ⟨o, o.isSome⟩ acc.2).1.opens),
            (sufSV wv n d far (i + 1) (y :: xs) ⟨o, o.isSome⟩ acc.2).2))
        ((wv c x none m).1.closed.foldl
          (fun (acc : Sm D P × Mm D P) a =>
            (addSummaryV acc.1
              ((sufSV wv n d far (i + 1) (y :: xs) ⟨D.rightBound a.span, true⟩ acc.2).1.closed.filterMap
                fun b => (Ans.join D P K hK a b).val)
              (sufSV wv n d far (i + 1) (y :: xs) ⟨D.rightBound a.span, true⟩ acc.2).1.opens,
              (sufSV wv n d far (i + 1) (y :: xs) ⟨D.rightBound a.span, true⟩ acc.2).2))
          (⟨[], []⟩, (wv c x none m).2))

theorem sufS_val (w : Evaluator R Rel (Ans D P) Cost)
    (wv : Near R → Rel → Option R → Mm D P → Sm D P × Mm D P)
    (hw : ∀ c x fr m, (w c x fr m).val = wv c x fr m) (n : Rel) (d : Nat) (far : Option R) :
    ∀ (xs : List Rel) (i : Nat) (c : Near R) (m : Mm D P),
      (sufS (K := DerivationKernel.over D K hK P) w n d far i xs c m).val =
        sufSV K hK wv n d far i xs c m
  | [], i, c, m => by
    at_cost K hK
    simp only [sufS, sufSV, Cost.pure_val]
  | [x], i, c, m => by simp only [sufS, sufSV, hw]
  | x :: y :: xs, i, c, m => by
    have ih := sufS_val w wv hw n d far (y :: xs)
    have mv := memo_val (P := P) K hK
    have as := addSummary_val (P := P) K hK
    by_cases hi : i = 0
    · subst hi
      at_cost K hK
      simp only [sufS, sufSV, ite_true, Cost.bind_val, Cost.pure_val, foldL_std, Cost.foldL_val,
        filterMapL_std, Cost.filterMapL_val, mapL_std, Cost.mapL_val, hw, ih, as, hK.rightBound,
        over_span, over_join]
    · at_cost K hK
      simp only [sufS, sufSV, hi, ite_false, mv, Cost.bind_val, Cost.pure_val, foldL_std,
        Cost.foldL_val, filterMapL_std, Cost.filterMapL_val, mapL_std, Cost.mapL_val, hw, ih, as,
        hK.rightBound, over_span, over_join]

/-! ## A meet -/

/-- The summaries of the members of a meet, all in the same context. -/
def membersSV (wv : Rel → Mm D P → Sm D P × Mm D P) : List Rel → Mm D P → List (Sm D P) × Mm D P
  | [], m => ([], m)
  | x :: xs, m => ((wv x m).1 :: (membersSV wv xs (wv x m).2).1, (membersSV wv xs (wv x m).2).2)

theorem membersS_val (w : Rel → Mm D P → Cost (Sm D P × Mm D P))
    (wv : Rel → Mm D P → Sm D P × Mm D P) (hw : ∀ x m, (w x m).val = wv x m) :
    ∀ (xs : List Rel) (m : Mm D P),
      (membersS (K := DerivationKernel.over D K hK P) w xs m).val = membersSV wv xs m
  | [], m => by
    at_cost K hK
    simp only [membersS, membersSV, Cost.pure_val]
  | x :: xs, m => by
    have ih := membersS_val w wv hw xs
    at_cost K hK
    simp only [membersS, membersSV, Cost.bind_val, Cost.pure_val, hw, ih]

/-! ## The evaluation -/

/-- The summary of a node unfolded to depth `d` after the context `c`. -/
def evalSV : Nat → Near R → Rel → Option R → Mm D P → Sm D P × Mm D P
  | 0, _, _, far, m => (⟨[], [far]⟩, m)
  | d + 1, c, n, far, m => memoV ⟨n, 0, d + 1, c, far⟩ m fun m =>
    match n.view.forget with
    | .span _ => (⟨(Ans.leaf D P K hK c.bound n far).val.toList, []⟩, m)
    | .call _ _ =>
      match Charged.bodyOf P n with
      | none => (⟨[], []⟩, m)
      | some b =>
        (⟨(evalSV d c b far m).1.closed.filterMap fun a => (Ans.unfold D P a n).val,
          (evalSV d c b far m).1.opens⟩, (evalSV d c b far m).2)
    | .union xs => xs.zipIdx.foldl
        (fun (acc : Sm D P × Mm D P) p =>
          (addSummaryV acc.1
            ((evalSV d c p.1 far acc.2).1.closed.filterMap fun a => (Ans.inj D P a n p.2).val)
            (evalSV d c p.1 far acc.2).1.opens, (evalSV d c p.1 far acc.2).2))
        (⟨[], []⟩, m)
    | .chain xs => sufSV K hK (evalSV d) n d far 0 xs c m
    | .meet xs =>
      (⟨(meetAllV K hK ((membersSV (fun x m => evalSV d c x far m) xs m).1.map (·.closed))).foldl
          keepNew [],
        if opaqueS (if c.isPushed then
            membersSV (fun x m => evalSV d c.own x far m) xs
              (membersSV (fun x m => evalSV d c x far m) xs m).2
          else membersSV (fun x m => evalSV d c x far m) xs m).1 then [far] else []⟩,
        (if c.isPushed then
            membersSV (fun x m => evalSV d c.own x far m) xs
              (membersSV (fun x m => evalSV d c x far m) xs m).2
          else membersSV (fun x m => evalSV d c x far m) xs m).2)

theorem evalS_val : ∀ (d : Nat) (c : Near R) (n : Rel) (far : Option R) (m : Mm D P),
    (evalS (K := DerivationKernel.over D K hK P) d c n far m).val = evalSV K hK d c n far m
  | 0, c, n, far, m => by
    at_cost K hK
    simp only [evalS, evalSV, Cost.pure_val]
  | d + 1, c, n, far, m => by
    have ih := evalS_val d
    have mv := memo_val (P := P) K hK
    have as := addSummary_val (P := P) K hK
    have ea := addAns_val (P := P) K hK
    have ma := meetAll_val (P := P) K hK
    have sv := sufS_val K hK (evalS (K := DerivationKernel.over D K hK P) d) (evalSV K hK d) ih n d
      far
    have ms := fun c' : Near R =>
      membersS_val K hK (fun x m => evalS (K := DerivationKernel.over D K hK P) d c' x far m)
        (fun x m => evalSV K hK d c' x far m) (fun x m => ih c' x far m)
    simp only [evalS, evalSV]
    rw [mv]
    congr 1
    funext m'
    at_cost K hK
    cases hv : n.view.forget with
    | span u =>
      simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, Cost.pure_val,
        over_leaf]
    | call f b =>
      cases hb : Charged.bodyOf P n <;>
        simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, Cost.pure_val,
          over_body, Charged.body, hb, ih, filterMapL_std, Cost.filterMapL_val, over_unfold]
    | union xs =>
      simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, Cost.pure_val,
        foldL_std, Cost.foldL_val, ih, filterMapL_std, Cost.filterMapL_val, over_inj, as]
    | chain xs =>
      simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, sv]
    | meet xs =>
      cases hp : c.isPushed <;>
        simp only [Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, Cost.pure_val, ms,
          ma, foldL_std, Cost.foldL_val, ea, Bool.false_eq_true, ite_false, ite_true]

/-! ## The race -/

theorem sharedRace_val (d : Nat) (g : GoalOf R Rel) :
    (sharedRace (K := DerivationKernel.over D K hK P) d g).val =
      if (evalSV (P := P) K hK d ⟨g.lb, false⟩ g.node g.rb []).1.opens.isEmpty then
        (true, (evalSV (P := P) K hK d ⟨g.lb, false⟩ g.node g.rb []).1.closed)
      else (false, []) := by
  have ev := evalS_val (P := P) K hK d
  at_cost K hK
  simp only [sharedRace, Cost.bind_val, Cost.pure_val, ev]

end Unfold

end Tabled

end RwLog
