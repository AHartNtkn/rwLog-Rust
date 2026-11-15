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
theorem untilV_quiet (f : β → α → Bool × α) :
    ∀ (xs : List β), (∀ x ∈ xs, ∀ acc, (f x acc).1 = false) → ∀ acc : α,
      (untilV f xs acc).1 = false
  | [], _, _ => rfl
  | x :: xs, h, acc => by
    simp only [untilV, h x (List.mem_cons_self ..), Bool.false_eq_true, ite_false]
    exact untilV_quiet f xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) _

/-- Going through a list with a body that never says stop costs at least what
the body costs on every member. -/
theorem untilL_ticks (f : β → α → Cost (Bool × α)) (L : β → Nat) :
    ∀ (xs : List β), (∀ x ∈ xs, ∀ acc, (f x acc).val.1 = false) →
      (∀ x ∈ xs, ∀ acc, L x ≤ (f x acc).ticks) → ∀ acc : α,
      (xs.map L).sum ≤ (untilL f xs acc).ticks
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, hq, hL, acc => by
    have ih := untilL_ticks f L xs (fun y hy => hq y (List.mem_cons_of_mem _ hy))
      (fun y hy => hL y (List.mem_cons_of_mem _ hy)) (f x acc).val.2
    have h := hL x (List.mem_cons_self ..) acc
    simp only [untilL, Cost.bind_ticks, List.map_cons, List.sum_cons,
      hq x (List.mem_cons_self ..), Bool.false_eq_true, ite_false]
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

/-- A continuation that does not say stop on the items of a list. -/
def Quiet (k : It D P → α → Cost (Bool × α)) (is : List (It D P)) : Prop :=
  ∀ it ∈ is, ∀ acc, (k it acc).val.1 = false

omit [DecidableEq R] in
theorem Quiet.until {k : It D P → α → Cost (Bool × α)} {is : List (It D P)} (h : Quiet k is)
    (acc : α) : (untilV (fun it acc => (k it acc).val) is acc).1 = false :=
  untilV_quiet _ is h acc

/-- `T` bounds from below what the continuation costs on the items of a
list. -/
def Costs (k : It D P → α → Cost (Bool × α)) (T : It D P → Nat) (is : List (It D P)) : Prop :=
  ∀ it ∈ is, ∀ acc, T it ≤ (k it acc).ticks

/-- What a walker of one node must satisfy: it costs at least what its
continuation costs on its items, when the continuation does not stop on
them. -/
def WalkerCosts (w : Near R → Rel → Option R → (It D P → α → Cost (Bool × α)) → α → Cost (Bool × α))
    (wv : Near R → Rel → Option R → List (It D P)) : Prop :=
  ∀ c x far (k : It D P → α → Cost (Bool × α)) acc (T : It D P → Nat),
    Quiet k (wv c x far) → Costs k T (wv c x far) →
    ((wv c x far).map T).sum ≤ (w c x far k acc).ticks

/-! ## A chain -/

/-- What the members of a chain hand on, when each member hands on what
`T` bounds from below. -/
theorem seqW_ticks (rev : Bool) (w : Walker R Rel (Ans D P) Cost α)
    (wv : Near R → Rel → Option R → List (It D P))
    (hw : ∀ c x far k acc, (w c x far k acc).val =
      untilV (fun it acc => (k it acc).val) (wv c x far) acc)
    (hwt : WalkerCosts w wv) (far : Option R) :
    ∀ (xs : List Rel) (pre : Option (It D P)) (c : Near R)
      (k : It D P → α → Cost (Bool × α)) (acc : α) (T : It D P → Nat),
      Quiet k (seqV K hK rev wv far pre c xs) → Costs k T (seqV K hK rev wv far pre c xs) →
      ((seqV K hK rev wv far pre c xs).map T).sum ≤
        (seqW (K := DerivationKernel.over D K hK P) rev w far pre c xs k acc).ticks
  | [], pre, c, k, acc, T, _, hT => by
    cases pre with
    | none => exact Nat.zero_le _
    | some it =>
      have := hT it (by simp [seqV]) acc
      simpa [seqW, seqV] using this
  | x :: xs, pre, c, k, acc, T, hk, hT => by
    have ih := seqW_ticks rev w wv hw hwt far xs
    have iv := seqW_val K hK rev w wv hw far xs
    have ee := extend_val (P := P) K hK rev
    have en := nearAfter_val (P := P) K hK rev
    have sub : ∀ it ∈ wv c x (if xs.isEmpty then far else none), ∀ it',
        extendV K hK rev pre it = some it' →
        ∀ j ∈ seqV K hK rev wv far (some it') (nearAfterV D rev it') xs,
          j ∈ seqV K hK rev wv far pre c (x :: xs) := fun it hit it' he j hj => by
      simp only [seqV]
      exact List.mem_flatMap.2 ⟨it, hit, by rw [he]; exact hj⟩
    simp only [seqW, seqV]
    rw [sum_map_flatMap]
    refine hwt c x _ _ acc (fun it => ((match extendV K hK rev pre it with
      | none => []
      | some it' => seqV K hK rev wv far (some it') (nearAfterV D rev it') xs).map T).sum)
      (fun it hit acc' => ?_) (fun it hit acc' => ?_)
    · have sub' := sub it hit
      at_cost K hK
      simp only [Cost.bind_val, ee]
      cases he : extendV _ _ rev pre it with
      | none => rfl
      | some it' =>
        simp only [Cost.bind_val, en, iv]
        exact Quiet.until (fun j hj => hk j (sub' it' he j hj)) _
    · have sub' := sub it hit
      at_cost K hK
      simp only [Cost.bind_ticks, ee]
      cases he : extendV _ _ rev pre it with
      | none => exact Nat.zero_le _
      | some it' =>
        simp only [Cost.bind_ticks, en]
        have := ih (some it') (nearAfterV D rev it') k acc' T
          (fun j hj => hk j (sub' it' he j hj)) (fun j hj => hT j (sub' it' he j hj))
        omega

/-- A chain walked in two parts: the rest is walked once for every product
of the prefix, so the chain costs at least `L` for each of them, when a walk
of the rest costs at least `L`. -/
theorem seqW_prefix_ticks (rev : Bool) (w : Walker R Rel (Ans D P) Cost α)
    (wv : Near R → Rel → Option R → List (It D P))
    (hw : ∀ c x far k acc, (w c x far k acc).val =
      untilV (fun it acc => (k it acc).val) (wv c x far) acc)
    (hwt : WalkerCosts w wv)
    (far : Option R) (ys : List Rel) (hys : ys ≠ []) (k : It D P → α → Cost (Bool × α)) (L : Nat)
    (hL : ∀ pre c acc,
      L ≤ (seqW (K := DerivationKernel.over D K hK P) rev w far pre c ys k acc).ticks) :
    ∀ (xs : List Rel) (pre : Option (It D P)) (c : Near R) (acc : α),
      Quiet k (seqV K hK rev wv far pre c (xs ++ ys)) →
      ((seqV K hK rev wv none pre c xs).map fun _ => L).sum ≤
        (seqW (K := DerivationKernel.over D K hK P) rev w far pre c (xs ++ ys) k acc).ticks
  | [], pre, c, acc, _ => by
    have := hL pre c acc
    cases pre with
    | none => exact Nat.zero_le _
    | some it => simpa [seqV] using this
  | x :: xs, pre, c, acc, hk => by
    have ih := seqW_prefix_ticks rev w wv hw hwt far ys hys k L hL xs
    have iv := seqW_val K hK rev w wv hw far (xs ++ ys)
    have ee := extend_val (P := P) K hK rev
    have en := nearAfter_val (P := P) K hK rev
    have hne : (xs ++ ys).isEmpty = false := by
      cases xs with
      | nil => obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_ne_nil hys; rfl
      | cons _ _ => rfl
    have sub : ∀ it ∈ wv c x none, ∀ it', extendV K hK rev pre it = some it' →
        ∀ j ∈ seqV K hK rev wv far (some it') (nearAfterV D rev it') (xs ++ ys),
          j ∈ seqV K hK rev wv far pre c (x :: xs ++ ys) := fun it hit it' he j hj => by
      simp only [List.cons_append, seqV, hne, Bool.false_eq_true, ite_false]
      exact List.mem_flatMap.2 ⟨it, hit, by rw [he]; exact hj⟩
    simp only [List.cons_append, seqW, seqV, hne, Bool.false_eq_true, ite_false, ite_self]
    rw [sum_map_flatMap]
    refine hwt c x _ _ acc (fun it => ((match extendV K hK rev pre it with
      | none => []
      | some it' => seqV K hK rev wv none (some it') (nearAfterV D rev it') xs).map
        fun _ => L).sum) (fun it hit acc' => ?_) (fun it hit acc' => ?_)
    · have sub' := sub it hit
      at_cost K hK
      simp only [Cost.bind_val, ee]
      cases he : extendV _ _ rev pre it with
      | none => rfl
      | some it' =>
        simp only [Cost.bind_val, en, iv]
        exact Quiet.until (fun j hj => hk j (sub' it' he j hj)) _
    · have sub' := sub it hit
      at_cost K hK
      simp only [Cost.bind_ticks, ee]
      cases he : extendV _ _ rev pre it with
      | none => exact Nat.zero_le _
      | some it' =>
        simp only [Cost.bind_ticks, en]
        have := ih (some it') (nearAfterV D rev it') acc' (fun j hj => hk j (sub' it' he j hj))
        omega

/-! ## A meet -/

/-- What the members of a meet hand on. -/
theorem andW_ticks (closed opq : Bool)
    (w : Rel → (It D P → α → Cost (Bool × α)) → α → Cost (Bool × α)) (wv : Rel → List (It D P))
    (hw : ∀ x k acc, (w x k acc).val = untilV (fun it acc => (k it acc).val) (wv x) acc)
    (hwt : ∀ x (k : It D P → α → Cost (Bool × α)) acc (T : It D P → Nat), Quiet k (wv x) →
      Costs k T (wv x) → ((wv x).map T).sum ≤ (w x k acc).ticks)
    (far : Option R) :
    ∀ (xs : List Rel) (pre : Met (Ans D P)) (k : It D P → α → Cost (Bool × α)) (acc : α)
      (T : It D P → Nat), Quiet k (andV K hK closed opq wv far pre xs) →
      Costs k T (andV K hK closed opq wv far pre xs) →
      ((andV K hK closed opq wv far pre xs).map T).sum ≤
        (andW (K := DerivationKernel.over D K hK P) closed opq w far pre xs k acc).ticks
  | [], pre, k, acc, T, _, hT => by
    cases pre with
    | start => exact Nat.zero_le _
    | dead => exact Nat.zero_le _
    | closed a =>
      cases closed
      · exact Nat.zero_le _
      · have := hT (.closed a) (by simp [andV]) acc
        simpa [andW, andV] using this
    | opn =>
      cases opq
      · exact Nat.zero_le _
      · have := hT (.opn far) (by simp [andV]) acc
        simpa [andW, andV] using this
  | x :: xs, pre, k, acc, T, hk, hT => by
    have ih := andW_ticks closed opq w wv hw hwt far xs
    have iv := andW_val K hK closed opq w wv hw far xs
    -- the items of the meet are those of the rest after each item of `x`
    have step : andV K hK closed opq wv far pre (x :: xs) =
          ((wv x).flatMap fun it => andV K hK closed opq wv far (metNext K hK closed pre it) xs) →
        ((andV K hK closed opq wv far pre (x :: xs)).map T).sum ≤
        (w x (fun it acc =>
          andW (K := DerivationKernel.over D K hK P) closed opq w far
            (metNext K hK closed pre it) xs k acc) acc).ticks := by
      intro e
      rw [e] at hk hT ⊢
      rw [sum_map_flatMap]
      exact hwt x _ acc _
        (fun it hit acc' => by
          rw [iv]
          exact Quiet.until (fun j hj => hk j (List.mem_flatMap.2 ⟨it, hit, hj⟩)) _)
        (fun it hit acc' => ih _ k acc' T
          (fun j hj => hk j (List.mem_flatMap.2 ⟨it, hit, hj⟩))
          (fun j hj => hT j (List.mem_flatMap.2 ⟨it, hit, hj⟩)))
    cases pre with
    | start =>
      refine Nat.le_trans (step (by simp only [andV])) (Nat.le_of_eq ?_)
      simp only [andW]
      congr 2
      funext it acc'
      cases it <;> rfl
    | closed a =>
      have e : andV K hK closed opq wv far (.closed a) (x :: xs) =
          ((wv x).flatMap fun it =>
            andV K hK closed opq wv far (metNext K hK closed (.closed a) it) xs) := by
        simp only [andV]
      rw [e] at hk hT ⊢
      simp only [andW]
      rw [sum_map_flatMap]
      refine hwt x _ acc _ (fun it hit acc' => ?_) (fun it hit acc' => ?_)
      · have hk' : Quiet k (andV K hK closed opq wv far (metNext K hK closed (.closed a) it) xs) :=
          fun j hj => hk j (List.mem_flatMap.2 ⟨it, hit, hj⟩)
        cases it with
        | closed b =>
          at_cost K hK
          simp only [metNext] at hk'
          simp only [Cost.bind_val, over_meetA]
          cases h : (Ans.meetA D P _ hK a b).val with
          | none => rw [h] at hk'; simp only [iv]; exact Quiet.until hk' _
          | some c => rw [h] at hk'; simp only [iv]; exact Quiet.until hk' _
        | opn t => rw [iv]; exact Quiet.until hk' _
      · have hk' : Quiet k (andV K hK closed opq wv far (metNext K hK closed (.closed a) it) xs) :=
          fun j hj => hk j (List.mem_flatMap.2 ⟨it, hit, hj⟩)
        have hT' : Costs k T
            (andV K hK closed opq wv far (metNext K hK closed (.closed a) it) xs) :=
          fun j hj => hT j (List.mem_flatMap.2 ⟨it, hit, hj⟩)
        cases it with
        | closed b =>
          at_cost K hK
          simp only [metNext] at hk' hT' ⊢
          simp only [Cost.bind_ticks, over_meetA]
          cases h : (Ans.meetA D P _ hK a b).val with
          | none =>
            rw [h] at hk' hT'
            have := ih .dead k acc' T hk' hT'
            simp only at this ⊢
            omega
          | some c =>
            rw [h] at hk' hT'
            have := ih (.closed c) k acc' T hk' hT'
            simp only at this ⊢
            omega
        | opn t => exact ih _ k acc' T hk' hT'
    | dead =>
      cases opq with
      | false => exact Nat.zero_le _
      | true =>
        refine Nat.le_trans (step (by simp only [andV])) (Nat.le_of_eq ?_)
        simp only [andW]
        congr 2
        funext it acc'
        cases it <;> rfl
    | opn =>
      cases opq with
      | false => exact Nat.zero_le _
      | true =>
        refine Nat.le_trans (step (by simp only [andV])) (Nat.le_of_eq ?_)
        simp only [andW]
        congr 2
        funext it acc'
        cases it <;> rfl

/-! ## The walk -/

/-- **A walk costs at least what its continuation costs on every item**,
when the continuation does not say stop on any of them. -/
theorem walk_ticks (rev : Bool) : ∀ (d : Nat),
    WalkerCosts (D := D) (P := P) (α := α) (walk (K := DerivationKernel.over D K hK P) rev d)
      (walkV K hK rev d)
  | 0, c, n, far, k, acc, T, _, hT => by
    have := hT (.opn far) (by simp [walkV]) acc
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
        Quiet k ((walkV K hK rev d c' x far).flatMap fun it => (liftItemV f it).toList) →
        Costs k T ((walkV K hK rev d c' x far).flatMap fun it => (liftItemV f it).toList) →
        (((walkV K hK rev d c' x far).flatMap fun it => (liftItemV f it).toList).map T).sum ≤
          (walk (K := DerivationKernel.over D K hK P) rev d c' x far k' acc').ticks ∧
        (walk (K := DerivationKernel.over D K hK P) rev d c' x far k' acc').val.1 = false := by
      intro f k' hv' ht' c' x acc' hk' hT'
      have hq : Quiet k' (walkV K hK rev d c' x far) := by
        intro it hit acc''
        rw [hv']
        cases he : liftItemV f it with
        | none => rfl
        | some it' => exact hk' it' (List.mem_flatMap.2 ⟨it, hit, by simp [he]⟩) acc''
      refine ⟨?_, by rw [iv]; exact Quiet.until hq _⟩
      rw [sum_map_flatMap]
      refine ih c' x far _ acc' _ hq (fun it hit acc'' => Nat.le_trans ?_ (ht' it acc''))
      cases he : liftItemV f it with
      | none => exact Nat.zero_le _
      | some it' =>
        have := hT' it' (List.mem_flatMap.2 ⟨it, hit, by simp [he]⟩) acc''
        simpa using this
    cases hv : n.view.forget with
    | span u =>
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          (leafAtV (P := P) K hK rev c.bound n far).toList.map .closed := by
        simp only [walkV, hv]
      rw [e] at hT ⊢
      at_cost K hK
      simp only [walk, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op, hv, el]
      cases h : leafAtV _ hK rev c.bound n far with
      | none => exact Nat.zero_le _
      | some a =>
        have := hT (.closed a) (by simp [h]) acc
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
        have e : walkV (P := P) K hK rev (d + 1) c n far =
            (walkV K hK rev d c b far).flatMap fun it =>
              (liftItemV (fun a => (Ans.unfold D P a n).val) it).toList := by
          simp only [walkV, hv, hb]
        rw [e] at hk hT ⊢
        at_cost K hK
        simp only [walk, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op, hv,
          over_body, Charged.body, hb]
        refine Nat.le_trans (lift (fun a => (Ans.unfold D P a n).val) _ (fun it acc' => ?_)
          (fun it acc' => ?_) c b acc hk hT).1 (le_add_three _ _ _ _)
        · simp only [Cost.bind_val, eli, over_unfold]
          cases liftItemV (fun a => (Ans.unfold D P a n).val) it <;> rfl
        · simp only [Cost.bind_ticks, eli, over_unfold]
          cases liftItemV (fun a => (Ans.unfold D P a n).val) it with
          | none => exact Nat.zero_le _
          | some it' => exact Nat.le_add_left _ _
    | union xs =>
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          xs.zipIdx.flatMap fun p => (walkV K hK rev d c p.1 far).flatMap fun it =>
            (liftItemV (fun a => (Ans.inj D P a n p.2).val) it).toList := by
        simp only [walkV, hv]
      rw [e] at hk hT ⊢
      at_cost K hK
      simp only [walk, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op, hv]
      rw [sum_map_flatMap]
      refine Nat.le_trans ?_ (le_add_two _ _ _)
      refine untilL_ticks _ _ _ (fun p hp acc' => ?_) (fun p hp acc' => ?_) _
      · refine (lift (fun a => (Ans.inj D P a n p.2).val) _ (fun it acc'' => ?_)
          (fun it acc'' => ?_) c p.1 acc'
          (fun j hj => hk j (List.mem_flatMap.2 ⟨p, hp, hj⟩))
          (fun j hj => hT j (List.mem_flatMap.2 ⟨p, hp, hj⟩))).2
        · simp only [Cost.bind_val, eli, over_inj]
          cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it <;> rfl
        · simp only [Cost.bind_ticks, eli, over_inj]
          cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it with
          | none => exact Nat.zero_le _
          | some it' => exact Nat.le_add_left _ _
      · refine (lift (fun a => (Ans.inj D P a n p.2).val) _ (fun it acc'' => ?_)
          (fun it acc'' => ?_) c p.1 acc'
          (fun j hj => hk j (List.mem_flatMap.2 ⟨p, hp, hj⟩))
          (fun j hj => hT j (List.mem_flatMap.2 ⟨p, hp, hj⟩))).1
        · simp only [Cost.bind_val, eli, over_inj]
          cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it <;> rfl
        · simp only [Cost.bind_ticks, eli, over_inj]
          cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it with
          | none => exact Nat.zero_le _
          | some it' => exact Nat.le_add_left _ _
    | chain xs =>
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          seqV K hK rev (walkV K hK rev d) far none c (if rev then xs.reverse else xs) := by
        simp only [walkV, hv]
      rw [e] at hk hT ⊢
      have := es far (if rev then xs.reverse else xs) none c k acc T hk hT
      at_cost K hK
      simp only [walk, Cost.bind_ticks, over_view, Charged.viewNode, Charged.op, hv]
      omega
    | meet xs =>
      cases hp : c.isPushed with
      | false =>
        have e : walkV (P := P) K hK rev (d + 1) c n far =
            andV K hK true true (fun x => walkV K hK rev d c x far) far .start xs := by
          simp only [walkV, hv, hp, Bool.false_eq_true, ite_false]
        rw [e] at hk hT ⊢
        have := ea true true c xs .start k acc T hk hT
        at_cost K hK
        simp only [walk, Cost.bind_ticks, over_view, Charged.viewNode,
          Charged.op, hv, hp, Bool.false_eq_true, ite_false]
        omega
      | true =>
        have e : walkV (P := P) K hK rev (d + 1) c n far =
            andV K hK true false (fun x => walkV K hK rev d c x far) far .start xs ++
              andV K hK false true (fun x => walkV K hK rev d c.own x far) far .start xs := by
          simp only [walkV, hv, hp, ite_true]
        rw [e] at hk hT ⊢
        have hk₁ : Quiet k (andV K hK true false (fun x => walkV K hK rev d c x far) far
            .start xs) := fun j hj => hk j (List.mem_append_left _ hj)
        have h₁ := ea true false c xs .start k acc T hk₁
          (fun j hj => hT j (List.mem_append_left _ hj))
        have hq : (andW (K := DerivationKernel.over D K hK P) true false
            (fun x => walk (K := DerivationKernel.over D K hK P) rev d c x far) far .start xs k
            acc).val.1 = false := by
          rw [eav]; exact Quiet.until hk₁ _
        have h₂ := ea false true c.own xs .start k
          (andW (K := DerivationKernel.over D K hK P) true false
            (fun x => walk (K := DerivationKernel.over D K hK P) rev d c x far) far .start xs k
            acc).val.2 T (fun j hj => hk j (List.mem_append_right _ hj))
          (fun j hj => hT j (List.mem_append_right _ hj))
        at_cost K hK
        simp only [walk, Cost.bind_ticks, over_view, Charged.viewNode,
          Charged.op, hv, hp, ite_true, hq, Bool.false_eq_true, ite_false, List.map_append,
          List.sum_append]
        omega

end Unfold

end RwLog
