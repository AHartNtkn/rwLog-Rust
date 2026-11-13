/-
# Forgetting the ticks

The value of a charged computation is the uncharged computation: each free
list traversal of `Trusted/Cost.lean` has, as its value, the list function of
the same name applied to the values. These are the lemmas every "the costed
machine computes the plain machine" proof rewrites with. They mention no rung.
-/
import RwLog.Trusted.Cost
import RwLog.Lib.Gfp

namespace RwLog

namespace Cost

@[simp] theorem ite_val {α : Type} (c : Prop) [Decidable c] (a b : Cost α) :
    (if c then a else b).val = if c then a.val else b.val := by
  split <;> rfl

@[simp] theorem mapL_val {α β : Type} (f : α → Cost β) :
    ∀ xs : List α, (mapL f xs).val = xs.map fun x => (f x).val
  | [] => rfl
  | x :: xs => by simp [mapL, mapL_val f xs]

@[simp] theorem flatMapL_val {α β : Type} (f : α → Cost (List β)) :
    ∀ xs : List α, (flatMapL f xs).val = xs.flatMap fun x => (f x).val
  | [] => rfl
  | x :: xs => by simp [flatMapL, flatMapL_val f xs]

@[simp] theorem filterL_val {α : Type} (f : α → Cost Bool) :
    ∀ xs : List α, (filterL f xs).val = xs.filter fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [filterL, bind_val, pure_val, filterL_val f xs, List.filter_cons]

@[simp] theorem filterMapL_val {α β : Type} (f : α → Cost (Option β)) :
    ∀ xs : List α, (filterMapL f xs).val = xs.filterMap fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [filterMapL, bind_val, pure_val, filterMapL_val f xs, List.filterMap_cons]
    cases (f x).val <;> simp

@[simp] theorem anyL_val {α : Type} (f : α → Cost Bool) :
    ∀ xs : List α, (anyL f xs).val = xs.any fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [anyL, bind_val, List.any_cons]
    cases (f x).val <;> simp [anyL_val f xs]

@[simp] theorem allL_val {α : Type} (f : α → Cost Bool) :
    ∀ xs : List α, (allL f xs).val = xs.all fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [allL, bind_val, List.all_cons]
    cases (f x).val <;> simp [allL_val f xs]

@[simp] theorem foldL_val {α β : Type} (f : β → α → Cost β) :
    ∀ (xs : List α) (b : β), (foldL f b xs).val = xs.foldl (fun b x => (f b x).val) b
  | [], _ => rfl
  | x :: xs, b => by simp [foldL, foldL_val f xs]

@[simp] theorem findL_val {α : Type} (f : α → Cost Bool) :
    ∀ xs : List α, (findL f xs).val = xs.find? fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [findL, bind_val, List.find?_cons]
    cases (f x).val <;> simp [findL_val f xs]

end Cost

/-- `gfpFrom` only asks `ok` about members of the set it started from. -/
theorem gfpFrom_congr {ok ok' : List Nat → Nat → Bool} {p : Nat → Prop}
    (h : ∀ S i, p i → ok S i = ok' S i) :
    ∀ (n : Nat) (S : List Nat), (∀ i ∈ S, p i) → gfpFrom ok n S = gfpFrom ok' n S
  | 0, _, _ => rfl
  | n + 1, S, hS => by
    have hf : S.filter (ok S) = S.filter (ok' S) :=
      List.filter_congr fun i hi => h S i (hS i hi)
    unfold gfpFrom
    simp only [hf]
    split
    · rfl
    · exact gfpFrom_congr h n _ fun i hi => hS i (List.mem_filter.1 hi).1

end RwLog
