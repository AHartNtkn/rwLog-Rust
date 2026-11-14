/-
# The walk, read off its text

`Unfold.walk` hands the products of an unfolding to a continuation one at a
time, until the continuation says stop. What it returns is going through a
list of items with the continuation (`untilV`): the list `walkV` builds, by
the kind of node, from the lists of its members (`seqV` for a chain, `andV`
for a meet). The list does not depend on the continuation.

`walkRace_val`: the race answered by a walk says the unfolding is not final
when the list has an open item, and otherwise returns the answers of the
list, the first with each representative.
-/
import RwLog.Rungs.Tabled.Unfolding.Eager

namespace RwLog

namespace Tabled

namespace Unfold

open Answer Traverse

/-! ## Going through a list until told to stop -/

section untilV

variable {α β γ : Type}

/-- Go through a list, threading what is carried, until told to stop. -/
def untilV (f : β → α → Bool × α) : List β → α → Bool × α
  | [], acc => (false, acc)
  | x :: xs, acc => if (f x acc).1 then f x acc else untilV f xs (f x acc).2

theorem untilL_val (f : β → α → Cost (Bool × α)) : ∀ (xs : List β) (acc : α),
    (untilL f xs acc).val = untilV (fun x acc => (f x acc).val) xs acc
  | [], _ => rfl
  | x :: xs, acc => by
    simp only [untilL, untilV, Cost.bind_val]
    cases h : (f x acc).val.1
    · simp only [Bool.false_eq_true, ite_false]; exact untilL_val f xs _
    · simp only [ite_true, Cost.pure_val]

theorem untilV_singleton (f : β → α → Bool × α) (x : β) (acc : α) :
    untilV f [x] acc = f x acc := by
  simp only [untilV]
  cases h : (f x acc).1
  · simp only [Bool.false_eq_true, ite_false]; exact Prod.ext h.symm rfl
  · simp only [ite_true]

theorem untilV_append (f : β → α → Bool × α) : ∀ (xs ys : List β) (acc : α),
    untilV f (xs ++ ys) acc =
      if (untilV f xs acc).1 then untilV f xs acc else untilV f ys (untilV f xs acc).2
  | [], _, _ => by simp [untilV]
  | x :: xs, ys, acc => by
    have ih := untilV_append f xs ys (f x acc).2
    simp only [List.cons_append, untilV]
    by_cases h : (f x acc).1 = true
    · simp only [h, ite_true]
    · simp only [h]; exact ih

theorem untilV_flatMap (f : β → α → Bool × α) (g : γ → List β) : ∀ (xs : List γ) (acc : α),
    untilV f (xs.flatMap g) acc = untilV (fun x acc => untilV f (g x) acc) xs acc
  | [], _ => rfl
  | x :: xs, acc => by
    simp only [List.flatMap_cons, untilV_append, untilV]
    cases h : (untilV f (g x) acc).1
    · simp only [Bool.false_eq_true, ite_false]; exact untilV_flatMap f g xs _
    · simp only [ite_true]

theorem untilV_toList (f : β → α → Bool × α) (o : Option β) (acc : α) :
    untilV f o.toList acc = match o with
      | some x => f x acc
      | none => (false, acc) := by
  cases o with
  | none => rfl
  | some x => exact untilV_singleton f x acc

/-- A continuation that stops at the first of some items and otherwise folds:
the walk stops exactly when there is such an item, and otherwise has folded
the whole list. -/
theorem untilV_stop (stop : β → Bool) (g : α → β → α) : ∀ (xs : List β) (acc : α),
    untilV (fun x acc => if stop x then (true, acc) else (false, g acc x)) xs acc =
      if xs.any stop then (true, (untilV (fun x acc =>
          if stop x then (true, acc) else (false, g acc x)) xs acc).2)
      else (false, xs.foldl g acc)
  | [], _ => rfl
  | x :: xs, acc => by
    simp only [untilV, List.any_cons, List.foldl_cons]
    cases h : stop x
    · simp only [Bool.false_eq_true, ite_false, Bool.false_or]
      exact untilV_stop stop g xs _
    · simp only [ite_true, Bool.true_or]

end untilV

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The items of a walk at the derivation kernel of a domain. -/
abbrev It (D : Domain R) (P : Program) := Item R (Ans D P)

variable (K : Kernel R Cost) (hK : K.Refines D)

/-! ## The operations of a walk -/

/-- The rule `leaf` between the near and the far boundary. -/
def leafAtV (rev : Bool) (near : Option R) (n : Rel) (far : Option R) : Option (Ans D P) :=
  if rev then (Ans.leaf D P K hK far n near).val else (Ans.leaf D P K hK near n far).val

theorem leafAt_val (rev : Bool) (near : Option R) (n : Rel) (far : Option R) :
    (leafAt (K := DerivationKernel.over D K hK P) rev near n far).val =
      leafAtV K hK rev near n far := by
  cases rev <;> simp [leafAt, leafAtV]

/-- The interface of a representative on the far side. -/
def farBoundV (D : Domain R) (rev : Bool) (s : R) : Option R :=
  if rev then D.leftBound s else D.rightBound s

theorem farBound_val (rev : Bool) (s : R) :
    (farBound (K := DerivationKernel.over D K hK P) rev s).val = farBoundV D rev s := by
  cases rev <;> simp [farBound, farBoundV, hK.leftBound, hK.rightBound]

/-- The rule `join` of what was walked first and what was walked after it. -/
def joinAtV (rev : Bool) (a b : Ans D P) : Option (Ans D P) :=
  if rev then (Ans.join D P K hK b a).val else (Ans.join D P K hK a b).val

theorem joinAt_val (rev : Bool) (a b : Ans D P) :
    (joinAt (K := DerivationKernel.over D K hK P) rev a b).val = joinAtV K hK rev a b := by
  cases rev <;> simp [joinAt, joinAtV]

/-- What is pushed into the next member of a chain after an item. -/
def nearAfterV (D : Domain R) (rev : Bool) : It D P → Near R
  | .closed a => ⟨farBoundV D rev a.span, true⟩
  | .opn none => ⟨none, false⟩
  | .opn (some t) => ⟨farBoundV D rev t, true⟩

theorem nearAfter_val (rev : Bool) (it : It D P) :
    (nearAfter (K := DerivationKernel.over D K hK P) rev it).val = nearAfterV D rev it := by
  have ef := farBound_val (P := P) K hK rev
  at_cost K hK
  cases it with
  | closed a => simp only [nearAfter, nearAfterV, Cost.bind_val, Cost.pure_val, ef, over_span]
  | opn t =>
    cases t with
    | none => simp only [nearAfter, nearAfterV, Cost.pure_val]
    | some t => simp only [nearAfter, nearAfterV, Cost.bind_val, Cost.pure_val, ef]

/-- An item of what was walked so far, followed by an item of the next
member. -/
def extendV (rev : Bool) : Option (It D P) → It D P → Option (It D P)
  | none, it => some it
  | some (.closed a), .closed b => (joinAtV K hK rev a b).map .closed
  | some (.closed _), .opn t => some (.opn t)
  | some (.opn _), .closed b => some (.opn (some b.span))
  | some (.opn _), .opn t => some (.opn t)

theorem extend_val (rev : Bool) (pre : Option (It D P)) (it : It D P) :
    (extend (K := DerivationKernel.over D K hK P) rev pre it).val = extendV K hK rev pre it := by
  have ej := joinAt_val (P := P) K hK rev
  at_cost K hK
  cases pre with
  | none => simp only [extend, extendV, Cost.pure_val]
  | some p =>
    cases p <;> cases it <;>
      simp only [extend, extendV, Cost.bind_val, Cost.pure_val, ej, over_span]

/-- Apply a rule to an item that is an answer. -/
def liftItemV (f : Ans D P → Option (Ans D P)) : It D P → Option (It D P)
  | .closed a => (f a).map .closed
  | .opn t => some (.opn t)

theorem liftItem_val (f : Ans D P → Cost (Option (Ans D P))) (it : It D P) :
    (liftItem (K := DerivationKernel.over D K hK P) f it).val =
      liftItemV (fun a => (f a).val) it := by
  at_cost K hK
  cases it <;> simp only [liftItem, liftItemV, Cost.bind_val, Cost.pure_val]

/-! ## A chain -/

/-- The items of the members of a chain in the order given, each under what
the items before it push. -/
def seqV (rev : Bool) (w : Near R → Rel → Option R → List (It D P)) (far : Option R) :
    Option (It D P) → Near R → List Rel → List (It D P)
  | pre, _, [] => pre.toList
  | pre, c, x :: xs => (w c x (if xs.isEmpty then far else none)).flatMap fun it =>
      match extendV K hK rev pre it with
      | none => []
      | some it' => seqV rev w far (some it') (nearAfterV D rev it') xs

variable {α : Type}

theorem seqW_val (rev : Bool) (w : Walker R Rel (Ans D P) Cost α)
    (wv : Near R → Rel → Option R → List (It D P))
    (hw : ∀ c x far k acc, (w c x far k acc).val =
      untilV (fun it acc => (k it acc).val) (wv c x far) acc) (far : Option R) :
    ∀ (xs : List Rel) (pre : Option (It D P)) (c : Near R)
      (k : It D P → α → Cost (Bool × α)) (acc : α),
      (seqW (K := DerivationKernel.over D K hK P) rev w far pre c xs k acc).val =
        untilV (fun it acc => (k it acc).val) (seqV K hK rev wv far pre c xs) acc
  | [], pre, c, k, acc => by
    at_cost K hK
    cases pre with
    | none => simp only [seqW, seqV, Cost.pure_val, Option.toList, untilV]
    | some it => simp only [seqW, seqV, Option.toList, untilV_singleton]
  | x :: xs, pre, c, k, acc => by
    have ih := seqW_val rev w wv hw far xs
    have ee := extend_val (P := P) K hK rev
    have en := nearAfter_val (P := P) K hK rev
    simp only [seqW, seqV]
    rw [hw, untilV_flatMap]
    congr 1
    funext it acc'
    at_cost K hK
    simp only [Cost.bind_val, ee]
    cases extendV _ _ rev pre it with
    | none => simp only [Cost.pure_val, untilV]
    | some it' => simp only [Cost.bind_val, en, ih]

/-! ## A meet -/

/-- What a walk holds of the members of a meet after an item of the next
one. -/
def metNext (closed : Bool) : Met (Ans D P) → It D P → Met (Ans D P)
  | _, .opn _ => .opn
  | .start, .closed b => if closed then .closed b else .dead
  | .closed a, .closed b =>
    match (Ans.meetA D P K hK a b).val with
    | some c => .closed c
    | none => .dead
  | .dead, .closed _ => .dead
  | .opn, .closed _ => .opn

/-- The items of a meet from the items of its members. -/
def andV (closed opq : Bool) (w : Rel → List (It D P)) (far : Option R) :
    Met (Ans D P) → List Rel → List (It D P)
  | pre, [] =>
    match pre with
    | .closed a => if closed then [.closed a] else []
    | .opn => if opq then [.opn far] else []
    | .start => []
    | .dead => []
  | pre, x :: xs =>
    match pre, opq with
    | .opn, false => []
    | .dead, false => []
    | _, _ => (w x).flatMap fun it => andV closed opq w far (metNext K hK closed pre it) xs

theorem andW_val (closed opq : Bool)
    (w : Rel → (It D P → α → Cost (Bool × α)) → α → Cost (Bool × α)) (wv : Rel → List (It D P))
    (hw : ∀ x k acc, (w x k acc).val = untilV (fun it acc => (k it acc).val) (wv x) acc)
    (far : Option R) :
    ∀ (xs : List Rel) (pre : Met (Ans D P)) (k : It D P → α → Cost (Bool × α)) (acc : α),
      (andW (K := DerivationKernel.over D K hK P) closed opq w far pre xs k acc).val =
        untilV (fun it acc => (k it acc).val) (andV K hK closed opq wv far pre xs) acc
  | [], pre, k, acc => by
    at_cost K hK
    cases pre with
    | start => simp only [andW, andV, Cost.pure_val, untilV]
    | dead => simp only [andW, andV, Cost.pure_val, untilV]
    | closed a =>
      cases closed <;>
        simp only [andW, andV, Cost.pure_val, untilV, untilV_singleton, Bool.false_eq_true,
          ite_false, ite_true]
    | opn =>
      cases opq <;>
        simp only [andW, andV, Cost.pure_val, untilV, untilV_singleton, Bool.false_eq_true,
          ite_false, ite_true]
  | x :: xs, pre, k, acc => by
    have ih := andW_val closed opq w wv hw far xs
    cases pre with
    | start =>
      simp only [andW, andV]
      rw [hw, untilV_flatMap]
      congr 1
      funext it acc'
      cases it <;> exact ih _ _ _
    | closed a =>
      simp only [andW, andV]
      rw [hw, untilV_flatMap]
      congr 1
      funext it acc'
      cases it with
      | closed b =>
        at_cost K hK
        simp only [Cost.bind_val, over_meetA, metNext]
        cases (Ans.meetA D P _ hK a b).val <;> simp only [ih]
      | opn t => exact ih _ _ _
    | dead =>
      cases opq with
      | false =>
        at_cost K hK
        simp only [andW, andV, Cost.pure_val, untilV]
      | true =>
        simp only [andW, andV]
        rw [hw, untilV_flatMap]
        congr 1
        funext it acc'
        cases it <;> exact ih _ _ _
    | opn =>
      cases opq with
      | false =>
        at_cost K hK
        simp only [andW, andV, Cost.pure_val, untilV]
      | true =>
        simp only [andW, andV]
        rw [hw, untilV_flatMap]
        congr 1
        funext it acc'
        cases it <;> exact ih _ _ _

/-! ## The walk -/

/-- The items of the unfolding of a node to depth `d`, in the order the walk
hands them on. -/
def walkV (rev : Bool) : Nat → Near R → Rel → Option R → List (It D P)
  | 0, _, _, far => [.opn far]
  | d + 1, c, n, far =>
    match n.view.forget with
    | .span _ => (leafAtV K hK rev c.bound n far).toList.map .closed
    | .call _ _ =>
      match Charged.bodyOf P n with
      | none => []
      | some b => (walkV rev d c b far).flatMap fun it =>
          (liftItemV (fun a => (Ans.unfold D P a n).val) it).toList
    | .union xs => xs.zipIdx.flatMap fun p => (walkV rev d c p.1 far).flatMap fun it =>
        (liftItemV (fun a => (Ans.inj D P a n p.2).val) it).toList
    | .chain xs => seqV K hK rev (walkV rev d) far none c (if rev then xs.reverse else xs)
    | .meet xs =>
      if c.isPushed then
        andV K hK true false (fun x => walkV rev d c x far) far .start xs ++
          andV K hK false true (fun x => walkV rev d c.own x far) far .start xs
      else andV K hK true true (fun x => walkV rev d c x far) far .start xs

theorem walk_val (rev : Bool) : ∀ (d : Nat) (c : Near R) (n : Rel) (far : Option R)
    (k : It D P → α → Cost (Bool × α)) (acc : α),
    (walk (K := DerivationKernel.over D K hK P) rev d c n far k acc).val =
      untilV (fun it acc => (k it acc).val) (walkV K hK rev d c n far) acc
  | 0, c, n, far, k, acc => by simp only [walk, walkV, untilV_singleton]
  | d + 1, c, n, far, k, acc => by
    have ih := walk_val rev d
    have el := leafAt_val (P := P) K hK rev
    have eli := liftItem_val (P := P) K hK
    have es := seqW_val K hK rev (walk (K := DerivationKernel.over D K hK P) rev d)
      (walkV K hK rev d) ih
    have ea := fun (cl opq : Bool) (c' : Near R) =>
      andW_val K hK cl opq (fun x => walk (K := DerivationKernel.over D K hK P) rev d c' x far)
        (fun x => walkV K hK rev d c' x far) (fun x k acc => ih c' x far k acc) far
    at_cost K hK
    cases hv : n.view.forget with
    | span u =>
      simp only [walk, walkV, Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, el]
      cases leafAtV _ hK rev c.bound n far <;>
        simp only [Cost.pure_val, Option.toList, List.map_nil, List.map_cons, untilV,
          untilV_singleton]
    | call m f =>
      cases hb : Charged.bodyOf P n with
      | none =>
        simp only [walk, walkV, Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv,
          over_body, Charged.body, hb, Cost.pure_val, untilV]
      | some b =>
        simp only [walk, walkV, Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv,
          over_body, Charged.body, hb, ih, untilV_flatMap]
        congr 1
        funext it acc'
        simp only [eli, untilV_toList, over_unfold]
        cases liftItemV (fun a => (Ans.unfold D P a n).val) it <;> simp only [Cost.pure_val]
    | union xs =>
      simp only [walk, walkV, Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv,
        untilL_val, ih, untilV_flatMap]
      congr 1
      funext p acc'
      congr 1
      funext it acc''
      simp only [eli, untilV_toList, over_inj]
      cases liftItemV (fun a => (Ans.inj D P a n p.2).val) it <;> simp only [Cost.pure_val]
    | chain xs =>
      simp only [walk, walkV, Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, es]
    | meet xs =>
      cases hp : c.isPushed with
      | false =>
        simp only [walk, walkV, Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, hp,
          Bool.false_eq_true, ite_false, ea]
      | true =>
        simp only [walk, walkV, Cost.bind_val, over_view, Charged.viewNode, Charged.op, hv, hp,
          ite_true, ite_val, Cost.pure_val, ea, untilV_append]

/-! ## The race -/

theorem addAns_val (xs : List (Ans D P)) (x : Ans D P) :
    (addAns (K := DerivationKernel.over D K hK P) xs x).val = keepNew xs x := by
  at_cost K hK
  simp only [addAns, keepNew, Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val, hK.eq,
    over_span]

/-- Is the item an open product? -/
def itOpn : It D P → Bool
  | .closed _ => false
  | .opn _ => true

/-- Add the item, if it is an answer, unless one with the same representative
is there. -/
def keepItem (acc : List (Ans D P)) : It D P → List (Ans D P)
  | .closed a => keepNew acc a
  | .opn _ => acc

theorem untilV_congr {α β : Type} {f f' : β → α → Bool × α} (h : ∀ x acc, f x acc = f' x acc)
    (xs : List β) (acc : α) : untilV f xs acc = untilV f' xs acc := by
  rw [show f = f' from funext fun x => funext fun acc => h x acc]

theorem walkRace_val (rev : Bool) (d : Nat) (g : GoalOf R Rel) :
    (walkRace (K := DerivationKernel.over D K hK P) rev d g).val =
      if (walkV (P := P) K hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
          (if rev then g.lb else g.rb)).any itOpn then (false, [])
      else (true, (walkV (P := P) K hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
          (if rev then g.lb else g.rb)).foldl keepItem []) := by
  have ew := walk_val (P := P) (α := List (Ans D P)) K hK rev d
  have ek := addAns_val (P := P) K hK
  at_cost K hK
  simp only [walkRace, Cost.bind_val, Cost.pure_val, ew]
  rw [untilV_congr (f' := fun it acc => if itOpn it then (true, acc) else (false, keepItem acc it))
    (fun it acc => by
      cases it <;> simp only [Cost.bind_val, Cost.pure_val, ek, itOpn, keepItem,
        Bool.false_eq_true, ite_false, ite_true]), untilV_stop]
  cases List.any (walkV _ hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
    (if rev then g.lb else g.rb)) itOpn <;> rfl

end Unfold

end Tabled

end RwLog
