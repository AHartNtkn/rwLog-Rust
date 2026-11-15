/-
# What a walk costs, from below

A walk hands the items of `walkV` to its continuation one at a time
(`Unfolding/WalkVal.lean`). When the continuation never says stop, the walk
hands every item on, so it costs at least what the continuation costs on all
of them: `walk_ticks`, for a bound `T` on what the continuation costs on an
item. The same for the members of a chain (`seqW_ticks`) and of a meet
(`andW_ticks`).

`seqW_prefix_ticks`: a chain walked in two parts. The rest is walked once for
every product of the prefix, so a walk of a chain costs at least one walk of
the rest for every product of a prefix.

Nothing here says what the kernel charges: the only facts used are that
`bind` adds ticks.
-/
import RwLog.Rungs.Framework.Unfolding.WalkVal

namespace RwLog

open Goals

namespace Unfold

open Answer Traverse

section lists

variable {α β γ : Type}

/-- A continuation that never says stop is never stopped. -/
theorem untilV_quiet (f : β → α → Bool × α) (h : ∀ x acc, (f x acc).1 = false) :
    ∀ (xs : List β) (acc : α), (untilV f xs acc).1 = false
  | [], _ => rfl
  | x :: xs, acc => by
    simp only [untilV, h, Bool.false_eq_true, ite_false]
    exact untilV_quiet f h xs _

/-- Going through a list with a body that never says stop costs at least what
the body costs on every member. -/
theorem untilL_ticks (f : β → α → Cost (Bool × α)) (L : β → Nat)
    (hq : ∀ x acc, (f x acc).val.1 = false) (hL : ∀ x acc, L x ≤ (f x acc).ticks) :
    ∀ (xs : List β) (acc : α), (xs.map L).sum ≤ (untilL f xs acc).ticks
  | [], _ => Nat.zero_le _
  | x :: xs, acc => by
    have ih := untilL_ticks f L hq hL xs (f x acc).val.2
    have h := hL x acc
    simp only [untilL, Cost.bind_ticks, List.map_cons, List.sum_cons, hq, Bool.false_eq_true,
      ite_false]
    omega

theorem le_add_two (a x y : Nat) : a ≤ x + (y + a) := by omega

theorem le_add_three (a x y z : Nat) : a ≤ x + (y + (z + a)) := by omega

theorem sum_map_flatMap (T : β → Nat) (g : γ → List β) : ∀ xs : List γ,
    ((xs.flatMap g).map T).sum = (xs.map fun x => ((g x).map T).sum).sum
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_flatMap T g xs]

end lists

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

variable (K : Kernel R Cost) (hK : K.Refines D)

variable {α : Type}

/-- A continuation that never says stop. -/
def Quiet (k : It D P → α → Cost (Bool × α)) : Prop := ∀ it acc, (k it acc).val.1 = false

/-! ## A chain -/

/-- What the members of a chain hand on, when each member hands on what
`T` bounds from below. -/
theorem seqW_ticks (rev : Bool) (w : Walker R Rel (Ans D P) Cost α)
    (wv : Near R → Rel → Option R → List (It D P))
    (hw : ∀ c x far k acc, (w c x far k acc).val =
      untilV (fun it acc => (k it acc).val) (wv c x far) acc)
    (hwt : ∀ c x far (k : It D P → α → Cost (Bool × α)) acc (T : It D P → Nat), Quiet k →
      (∀ it acc, T it ≤ (k it acc).ticks) → ((wv c x far).map T).sum ≤ (w c x far k acc).ticks)
    (far : Option R) :
    ∀ (xs : List Rel) (pre : Option (It D P)) (c : Near R)
      (k : It D P → α → Cost (Bool × α)) (acc : α) (T : It D P → Nat), Quiet k →
      (∀ it acc, T it ≤ (k it acc).ticks) →
      ((seqV K hK rev wv far pre c xs).map T).sum ≤
        (seqW (K := DerivationKernel.over D K hK P) rev w far pre c xs k acc).ticks
  | [], pre, c, k, acc, T, _, hT => by
    cases pre with
    | none => exact Nat.zero_le _
    | some it =>
      have := hT it acc
      simpa [seqW, seqV] using this
  | x :: xs, pre, c, k, acc, T, hk, hT => by
    have ih := seqW_ticks rev w wv hw hwt far xs
    have iv := seqW_val K hK rev w wv hw far xs
    have ee := extend_val (P := P) K hK rev
    have en := nearAfter_val (P := P) K hK rev
    simp only [seqW, seqV]
    rw [sum_map_flatMap]
    refine hwt c x _ _ acc (fun it => ((match extendV K hK rev pre it with
      | none => []
      | some it' => seqV K hK rev wv far (some it') (nearAfterV D rev it') xs).map T).sum)
      (fun it acc' => ?_) (fun it acc' => ?_)
    · at_cost K hK
      simp only [Cost.bind_val, ee]
      cases extendV _ _ rev pre it with
      | none => rfl
      | some it' =>
        simp only [Cost.bind_val, en, iv]
        exact untilV_quiet _ hk _ _
    · at_cost K hK
      simp only [Cost.bind_ticks, ee]
      cases extendV _ _ rev pre it with
      | none => exact Nat.zero_le _
      | some it' =>
        simp only [Cost.bind_ticks, en]
        have := ih (some it') (nearAfterV D rev it') k acc' T hk hT
        omega

/-- A chain walked in two parts: the rest is walked once for every product
of the prefix, so the chain costs at least `L` for each of them, when a walk
of the rest costs at least `L`. -/
theorem seqW_prefix_ticks (rev : Bool) (w : Walker R Rel (Ans D P) Cost α)
    (wv : Near R → Rel → Option R → List (It D P))
    (hw : ∀ c x far k acc, (w c x far k acc).val =
      untilV (fun it acc => (k it acc).val) (wv c x far) acc)
    (hwt : ∀ c x far (k : It D P → α → Cost (Bool × α)) acc (T : It D P → Nat), Quiet k →
      (∀ it acc, T it ≤ (k it acc).ticks) → ((wv c x far).map T).sum ≤ (w c x far k acc).ticks)
    (far : Option R) (ys : List Rel) (hys : ys ≠ []) (k : It D P → α → Cost (Bool × α))
    (hk : Quiet k) (L : Nat)
    (hL : ∀ pre c acc,
      L ≤ (seqW (K := DerivationKernel.over D K hK P) rev w far pre c ys k acc).ticks) :
    ∀ (xs : List Rel) (pre : Option (It D P)) (c : Near R) (acc : α),
      ((seqV K hK rev wv none pre c xs).map fun _ => L).sum ≤
        (seqW (K := DerivationKernel.over D K hK P) rev w far pre c (xs ++ ys) k acc).ticks
  | [], pre, c, acc => by
    have := hL pre c acc
    cases pre with
    | none => exact Nat.zero_le _
    | some it => simpa [seqV] using this
  | x :: xs, pre, c, acc => by
    have ih := seqW_prefix_ticks rev w wv hw hwt far ys hys k hk L hL xs
    have iv := seqW_val K hK rev w wv hw far (xs ++ ys)
    have ee := extend_val (P := P) K hK rev
    have en := nearAfter_val (P := P) K hK rev
    have hne : (xs ++ ys).isEmpty = false := by
      cases xs with
      | nil => obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_ne_nil hys; rfl
      | cons _ _ => rfl
    simp only [List.cons_append, seqW, seqV, hne, Bool.false_eq_true, ite_false, ite_self]
    rw [sum_map_flatMap]
    refine hwt c x _ _ acc (fun it => ((match extendV K hK rev pre it with
      | none => []
      | some it' => seqV K hK rev wv none (some it') (nearAfterV D rev it') xs).map
        fun _ => L).sum) (fun it acc' => ?_) (fun it acc' => ?_)
    · at_cost K hK
      simp only [Cost.bind_val, ee]
      cases extendV _ _ rev pre it with
      | none => rfl
      | some it' =>
        simp only [Cost.bind_val, en, iv]
        exact untilV_quiet _ hk _ _
    · at_cost K hK
      simp only [Cost.bind_ticks, ee]
      cases extendV _ _ rev pre it with
      | none => exact Nat.zero_le _
      | some it' =>
        simp only [Cost.bind_ticks, en]
        have := ih (some it') (nearAfterV D rev it') acc'
        omega

/-! ## A meet -/

/-- What the members of a meet hand on. -/
theorem andW_ticks (closed opq : Bool)
    (w : Rel → (It D P → α → Cost (Bool × α)) → α → Cost (Bool × α)) (wv : Rel → List (It D P))
    (hw : ∀ x k acc, (w x k acc).val = untilV (fun it acc => (k it acc).val) (wv x) acc)
    (hwt : ∀ x (k : It D P → α → Cost (Bool × α)) acc (T : It D P → Nat), Quiet k →
      (∀ it acc, T it ≤ (k it acc).ticks) → ((wv x).map T).sum ≤ (w x k acc).ticks)
    (far : Option R) :
    ∀ (xs : List Rel) (pre : Met (Ans D P)) (k : It D P → α → Cost (Bool × α)) (acc : α)
      (T : It D P → Nat), Quiet k → (∀ it acc, T it ≤ (k it acc).ticks) →
      ((andV K hK closed opq wv far pre xs).map T).sum ≤
        (andW (K := DerivationKernel.over D K hK P) closed opq w far pre xs k acc).ticks
  | [], pre, k, acc, T, _, hT => by
    cases pre with
    | start => exact Nat.zero_le _
    | dead => exact Nat.zero_le _
    | closed a =>
      cases closed
      · exact Nat.zero_le _
      · have := hT (.closed a) acc
        simpa [andW, andV] using this
    | opn =>
      cases opq
      · exact Nat.zero_le _
      · have := hT (.opn far) acc
        simpa [andW, andV] using this
  | x :: xs, pre, k, acc, T, hk, hT => by
    have ih := andW_ticks closed opq w wv hw hwt far xs
    have iv := andW_val K hK closed opq w wv hw far xs
    have step : ((wv x).map fun it =>
        ((andV K hK closed opq wv far (metNext K hK closed pre it) xs).map T).sum).sum ≤
        (w x (fun it acc =>
          andW (K := DerivationKernel.over D K hK P) closed opq w far
            (metNext K hK closed pre it) xs k acc) acc).ticks :=
      hwt x _ acc _ (fun it acc' => by rw [iv]; exact untilV_quiet _ hk _ _)
        (fun it acc' => ih _ k acc' T hk hT)
    cases pre with
    | start =>
      simp only [andW, andV]
      rw [sum_map_flatMap]
      refine Nat.le_trans step (Nat.le_of_eq ?_)
      congr 2
      funext it acc'
      cases it <;> rfl
    | closed a =>
      simp only [andW, andV]
      rw [sum_map_flatMap]
      refine hwt x _ acc _ (fun it acc' => ?_) (fun it acc' => ?_)
      · cases it with
        | closed b =>
          at_cost K hK
          simp only [Cost.bind_val, over_meetA]
          cases (Ans.meetA D P _ hK a b).val <;> (simp only [iv]; exact untilV_quiet _ hk _ _)
        | opn t => rw [iv]; exact untilV_quiet _ hk _ _
      · cases it with
        | closed b =>
          at_cost K hK
          simp only [Cost.bind_ticks, over_meetA, metNext]
          cases h : (Ans.meetA D P _ hK a b).val with
          | none =>
            have := ih .dead k acc' T hk hT
            simp only at this ⊢
            omega
          | some c =>
            have := ih (.closed c) k acc' T hk hT
            simp only at this ⊢
            omega
        | opn t => exact ih _ k acc' T hk hT
    | dead =>
      cases opq with
      | false => exact Nat.zero_le _
      | true =>
        simp only [andW, andV]
        rw [sum_map_flatMap]
        refine Nat.le_trans step (Nat.le_of_eq ?_)
        congr 2
        funext it acc'
        cases it <;> rfl
    | opn =>
      cases opq with
      | false => exact Nat.zero_le _
      | true =>
        simp only [andW, andV]
        rw [sum_map_flatMap]
        refine Nat.le_trans step (Nat.le_of_eq ?_)
        congr 2
        funext it acc'
        cases it <;> rfl

/-! ## The walk -/

/-- **A walk whose continuation never says stop costs at least what the
continuation costs on every item.** -/
theorem walk_ticks (rev : Bool) : ∀ (d : Nat) (c : Near R) (n : Rel) (far : Option R)
    (k : It D P → α → Cost (Bool × α)) (acc : α) (T : It D P → Nat), Quiet k →
    (∀ it acc, T it ≤ (k it acc).ticks) →
    ((walkV K hK rev d c n far).map T).sum ≤
      (walk (K := DerivationKernel.over D K hK P) rev d c n far k acc).ticks
  | 0, c, n, far, k, acc, T, _, hT => by
    have := hT (.opn far) acc
    simpa [walk, walkV] using this
  | d + 1, c, n, far, k, acc, T, hk, hT => by
    have ih := walk_ticks rev d
    have iv := walk_val (P := P) (α := α) K hK rev d
    have el := leafAt_val (P := P) K hK rev
    have eli := liftItem_val (P := P) K hK
    have es := seqW_ticks K hK rev (walk (K := DerivationKernel.over D K hK P) rev d)
      (walkV K hK rev d) iv ih
    have ea := fun (cl opq : Bool) (c' : Near R) =>
      andW_ticks K hK cl opq (fun x => walk (K := DerivationKernel.over D K hK P) rev d c' x far)
        (fun x => walkV K hK rev d c' x far) (fun x k acc => iv c' x far k acc)
        (fun x k acc T hk hT => ih c' x far k acc T hk hT) far
    have eav := fun (cl opq : Bool) (c' : Near R) =>
      andW_val K hK cl opq (fun x => walk (K := DerivationKernel.over D K hK P) rev d c' x far)
        (fun x => walkV K hK rev d c' x far) (fun x k acc => iv c' x far k acc) far
    -- a rule applied to the items of a member
    have lift : ∀ (f : Ans D P → Option (Ans D P)) (k' : It D P → α → Cost (Bool × α)),
        (∀ it acc, (k' it acc).val = match liftItemV f it with
          | some it' => (k it' acc).val
          | none => (false, acc)) →
        (∀ it acc, (match liftItemV f it with
          | some it' => (k it' acc).ticks
          | none => 0) ≤ (k' it acc).ticks) →
        ∀ (c' : Near R) (x : Rel) (acc' : α),
        (((walkV K hK rev d c' x far).flatMap fun it => (liftItemV f it).toList).map T).sum ≤
          (walk (K := DerivationKernel.over D K hK P) rev d c' x far k' acc').ticks ∧
        (walk (K := DerivationKernel.over D K hK P) rev d c' x far k' acc').val.1 = false := by
      intro f k' hv' ht' c' x acc'
      have hq : Quiet k' := by
        intro it acc''
        rw [hv']
        cases liftItemV f it with
        | none => rfl
        | some it' => exact hk it' acc''
      refine ⟨?_, by rw [iv]; exact untilV_quiet _ hq _ _⟩
      rw [sum_map_flatMap]
      refine ih c' x far _ acc' _ hq (fun it acc'' => Nat.le_trans ?_ (ht' it acc''))
      cases liftItemV f it with
      | none => exact Nat.zero_le _
      | some it' =>
        have := hT it' acc''
        simpa using this
    cases hv : n.view.forget with
    | span u =>
      at_cost K hK
      simp only [walk, walkV, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op, hv, el]
      cases leafAtV _ hK rev c.bound n far with
      | none => exact Nat.zero_le _
      | some a =>
        have := hT (.closed a) acc
        simp only [Option.toList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | call m f =>
      cases hb : Charged.bodyOf P n with
      | none =>
        at_cost K hK
        simp only [walk, walkV, over_view, Charged.viewNode, Charged.op, hv, over_body,
          Charged.body, hb]
        exact Nat.zero_le _
      | some b =>
        at_cost K hK
        simp only [walk, walkV, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op, hv,
          over_body, Charged.body, hb]
        refine Nat.le_trans (lift (fun a => (Ans.unfold D P a n).val) _ (fun it acc' => ?_)
          (fun it acc' => ?_) c b acc).1 (le_add_three _ _ _ _)
        · simp only [Cost.bind_val, eli, over_unfold]
          cases liftItemV (fun a => (Ans.unfold D P a n).val) it <;> rfl
        · simp only [Cost.bind_ticks, eli, over_unfold]
          cases liftItemV (fun a => (Ans.unfold D P a n).val) it with
          | none => exact Nat.zero_le _
          | some it' => exact Nat.le_add_left _ _
    | union xs =>
      at_cost K hK
      simp only [walk, walkV, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op, hv]
      rw [sum_map_flatMap]
      refine Nat.le_trans ?_ (le_add_two _ _ _)
      refine untilL_ticks _ _ (fun p acc' => ?_) (fun p acc' => ?_) _ _
      · refine (lift (fun a => (Ans.inj D P a n p.2).val) _ (fun it acc'' => ?_)
          (fun it acc'' => ?_) c p.1 acc').2
        · simp only [Cost.bind_val, eli, over_inj]
          cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it <;> rfl
        · simp only [Cost.bind_ticks, eli, over_inj]
          cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it with
          | none => exact Nat.zero_le _
          | some it' => exact Nat.le_add_left _ _
      · refine (lift (fun a => (Ans.inj D P a n p.2).val) _ (fun it acc'' => ?_)
          (fun it acc'' => ?_) c p.1 acc').1
        · simp only [Cost.bind_val, eli, over_inj]
          cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it <;> rfl
        · simp only [Cost.bind_ticks, eli, over_inj]
          cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it with
          | none => exact Nat.zero_le _
          | some it' => exact Nat.le_add_left _ _
    | chain xs =>
      have := es far (if rev then xs.reverse else xs) none c k acc T hk hT
      at_cost K hK
      simp only [walk, walkV, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op, hv]
      omega
    | meet xs =>
      cases hp : c.isPushed with
      | false =>
        have := ea true true c xs .start k acc T hk hT
        at_cost K hK
        simp only [walk, walkV, Cost.bind_ticks, over_view, Charged.viewNode,
          Charged.op, hv, hp, Bool.false_eq_true, ite_false]
        omega
      | true =>
        have h₁ := ea true false c xs .start k acc T hk hT
        have hq : (andW (K := DerivationKernel.over D K hK P) true false
            (fun x => walk (K := DerivationKernel.over D K hK P) rev d c x far) far .start xs k
            acc).val.1 = false := by
          rw [eav]; exact untilV_quiet _ hk _ _
        have h₂ := ea false true c.own xs .start k
          (andW (K := DerivationKernel.over D K hK P) true false
            (fun x => walk (K := DerivationKernel.over D K hK P) rev d c x far) far .start xs k
            acc).val.2 T hk hT
        at_cost K hK
        simp only [walk, walkV, Cost.bind_ticks, over_view, Charged.viewNode,
          Charged.op, hv, hp, ite_true, hq, Bool.false_eq_true, ite_false, List.map_append,
          List.sum_append]
        omega

end Unfold

end RwLog
