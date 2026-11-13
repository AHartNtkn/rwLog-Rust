/-
# The cost monad: forgetting and counting ticks

`Cost` and its free traversals are defined in `Trusted/Cost.lean`. Here are
the facts every costed rung needs to relate its machine to an uncosted one:
`Cost` is a lawful monad, the value of each traversal is the list function of
the same name, the ticks of the total traversals are sums, and the spending of
a costed runtime grows with the number of steps.
-/
import RwLog.Trusted.Cost
import RwLog.Rungs.Framework.Runtime

namespace RwLog

namespace Cost

variable {α β : Type}

@[ext] theorem ext {x y : Cost α} (hv : x.val = y.val) (ht : x.ticks = y.ticks) : x = y := by
  cases x; cases y; cases hv; cases ht; rfl

instance : LawfulMonad Cost := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => Cost.ext rfl (Nat.zero_add _))
  (bind_assoc := fun _ _ _ => Cost.ext rfl (Nat.add_assoc _ _ _))

@[simp] theorem map_val (f : α → β) (m : Cost α) : (f <$> m).val = f m.val := rfl
@[simp] theorem map_ticks (f : α → β) (m : Cost α) : (f <$> m).ticks = m.ticks := rfl

/-! ## Values of the traversals -/

@[simp] theorem mapL_val (f : α → Cost β) :
    ∀ xs : List α, (mapL f xs).val = xs.map fun x => (f x).val
  | [] => rfl
  | x :: xs => by simp only [mapL, bind_val, pure_val, List.map_cons, mapL_val f xs]

@[simp] theorem flatMapL_val (f : α → Cost (List β)) :
    ∀ xs : List α, (flatMapL f xs).val = xs.flatMap fun x => (f x).val
  | [] => rfl
  | x :: xs => by simp only [flatMapL, bind_val, pure_val, List.flatMap_cons, flatMapL_val f xs]

@[simp] theorem filterL_val (f : α → Cost Bool) :
    ∀ xs : List α, (filterL f xs).val = xs.filter fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    cases h : (f x).val <;> simp [filterL, h, filterL_val f xs]

@[simp] theorem filterMapL_val (f : α → Cost (Option β)) :
    ∀ xs : List α, (filterMapL f xs).val = xs.filterMap fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [filterMapL, bind_val, pure_val, List.filterMap_cons, filterMapL_val f xs]
    cases (f x).val <;> rfl

@[simp] theorem anyL_val (f : α → Cost Bool) :
    ∀ xs : List α, (anyL f xs).val = xs.any fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [anyL, bind_val, List.any_cons]
    cases h : (f x).val <;> simp [anyL_val f xs]

@[simp] theorem allL_val (f : α → Cost Bool) :
    ∀ xs : List α, (allL f xs).val = xs.all fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [allL, bind_val, List.all_cons]
    cases h : (f x).val <;> simp [allL_val f xs]

@[simp] theorem foldL_val (f : β → α → Cost β) :
    ∀ (xs : List α) (b : β), (foldL f b xs).val = xs.foldl (fun b x => (f b x).val) b
  | [], _ => rfl
  | x :: xs, b => by simp only [foldL, bind_val, List.foldl_cons, foldL_val f xs]

@[simp] theorem findL_val (f : α → Cost Bool) :
    ∀ xs : List α, (findL f xs).val = xs.find? fun x => (f x).val
  | [] => rfl
  | x :: xs => by
    simp only [findL, bind_val, List.find?_cons]
    cases h : (f x).val <;> simp [findL_val f xs]

/-! ## Ticks of the traversals

The traversals that visit every member spend the sum of what the function
spends; the ones that stop early spend at most that. -/

theorem mapL_ticks (f : α → Cost β) :
    ∀ xs : List α, (mapL f xs).ticks = (xs.map fun x => (f x).ticks).sum
  | [] => rfl
  | x :: xs => by
    simp only [mapL, bind_ticks, pure_ticks, List.map_cons, List.sum_cons, mapL_ticks f xs,
      Nat.add_zero]

theorem flatMapL_ticks (f : α → Cost (List β)) :
    ∀ xs : List α, (flatMapL f xs).ticks = (xs.map fun x => (f x).ticks).sum
  | [] => rfl
  | x :: xs => by
    simp only [flatMapL, bind_ticks, pure_ticks, List.map_cons, List.sum_cons,
      flatMapL_ticks f xs, Nat.add_zero]

theorem filterL_ticks (f : α → Cost Bool) :
    ∀ xs : List α, (filterL f xs).ticks = (xs.map fun x => (f x).ticks).sum
  | [] => rfl
  | x :: xs => by
    simp only [filterL, bind_ticks, pure_ticks, List.map_cons, List.sum_cons,
      filterL_ticks f xs, Nat.add_zero]

theorem filterMapL_ticks (f : α → Cost (Option β)) :
    ∀ xs : List α, (filterMapL f xs).ticks = (xs.map fun x => (f x).ticks).sum
  | [] => rfl
  | x :: xs => by
    simp only [filterMapL, bind_ticks, pure_ticks, List.map_cons, List.sum_cons,
      filterMapL_ticks f xs, Nat.add_zero]

theorem anyL_ticks_le (f : α → Cost Bool) :
    ∀ xs : List α, (anyL f xs).ticks ≤ (xs.map fun x => (f x).ticks).sum
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := anyL_ticks_le f xs
    simp only [anyL, bind_ticks, List.map_cons, List.sum_cons]
    cases (f x).val <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_ticks] <;> omega

theorem allL_ticks_le (f : α → Cost Bool) :
    ∀ xs : List α, (allL f xs).ticks ≤ (xs.map fun x => (f x).ticks).sum
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := allL_ticks_le f xs
    simp only [allL, bind_ticks, List.map_cons, List.sum_cons]
    cases (f x).val <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_ticks] <;> omega

theorem findL_ticks_le (f : α → Cost Bool) :
    ∀ xs : List α, (findL f xs).ticks ≤ (xs.map fun x => (f x).ticks).sum
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := findL_ticks_le f xs
    simp only [findL, bind_ticks, List.map_cons, List.sum_cons]
    cases (f x).val <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_ticks] <;> omega

end Cost

/-! ## Costed runtimes -/

namespace CostedRuntime

variable (C : CostedRuntime)

@[simp] theorem runtime_step (s : C.State) : C.runtime.step s = (C.step s).val := rfl

@[simp] theorem runtime_init (P : Program) (q : Rel) : C.runtime.init P q = C.init P q := rfl

@[simp] theorem spent_zero (s : C.State) : C.spent s 0 = 0 := rfl

theorem spent_succ_emit {s s' : C.State} {as : List Span} (h : (C.step s).val = .emit as s')
    (n : Nat) : C.spent s (n + 1) = (C.step s).ticks + C.spent s' n := by
  simp only [spent, h]

theorem spent_succ_done {s : C.State} (h : (C.step s).val = .done) (n : Nat) :
    C.spent s (n + 1) = (C.step s).ticks := by
  simp only [spent, h, Nat.add_zero]

/-- Spending grows with the number of steps. -/
theorem spent_mono : ∀ (s : C.State) {m n : Nat}, m ≤ n → C.spent s m ≤ C.spent s n
  | _, 0, _, _ => Nat.zero_le _
  | s, m + 1, 0, h => absurd h (Nat.not_succ_le_zero m)
  | s, m + 1, n + 1, h => by
    cases hs : (C.step s).val with
    | done => rw [C.spent_succ_done hs, C.spent_succ_done hs]
    | emit as s' =>
      rw [C.spent_succ_emit hs, C.spent_succ_emit hs]
      exact Nat.add_le_add_left (spent_mono s' (Nat.le_of_succ_le_succ h)) _

/-- A halted machine spends nothing more. -/
theorem spent_of_halts : ∀ (s : C.State) {m n : Nat}, C.runtime.Halts s m → m ≤ n →
    C.spent s n = C.spent s m
  | _, 0, _, hm, _ => by simp [Runtime.Halts, Runtime.run] at hm
  | s, m + 1, 0, _, h => absurd h (Nat.not_succ_le_zero m)
  | s, m + 1, n + 1, hm, h => by
    cases hs : (C.step s).val with
    | done => rw [C.spent_succ_done hs, C.spent_succ_done hs]
    | emit as s' =>
      have hs' : C.runtime.step s = .emit as s' := hs
      rw [C.spent_succ_emit hs, C.spent_succ_emit hs]
      unfold Runtime.Halts at hm
      rw [C.runtime.run_succ_emit hs'] at hm
      rw [spent_of_halts s' hm (Nat.le_of_succ_le_succ h)]

end CostedRuntime

end RwLog
