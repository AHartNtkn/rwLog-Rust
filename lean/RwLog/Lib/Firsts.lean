/-
# Lists without repeats, built by adding at the end

`addNew xs x` puts `x` at the end of `xs` unless it is already there, and
`addAll acc xs` does that for every member of `xs` in order. `firsts xs`, the
members of `xs` in the order of their first occurrence, is `addAll [] xs`,
and it is `List.eraseDups` (`firsts_eq_eraseDups`).

What is added matters only through its first occurrences (`addAll_firsts`),
also under a `flatMap` (`addAll_flatMap_firsts`). So removing repeats at any
stage of a nested `flatMap` gives the same first occurrences as removing them
once at the end.
-/
import RwLog.Lib.List

namespace RwLog

variable {α β : Type} [DecidableEq α]

/-- Put `x` at the end unless it is already there. -/
def addNew (xs : List α) (x : α) : List α := if x ∈ xs then xs else xs ++ [x]

/-- Add every member of `xs`, in order, unless it is already there. -/
def addAll (acc xs : List α) : List α := xs.foldl addNew acc

/-- The members of a list in the order of their first occurrence. -/
def firsts (xs : List α) : List α := addAll [] xs

theorem mem_addNew {xs : List α} {x y : α} : y ∈ addNew xs x ↔ y ∈ xs ∨ y = x := by
  unfold addNew
  split
  · rename_i h
    constructor
    · exact Or.inl
    · rintro (h' | rfl)
      · exact h'
      · exact h
  · simp

@[simp] theorem addAll_nil (acc : List α) : addAll acc [] = acc := rfl

theorem addAll_cons (acc : List α) (x : α) (xs : List α) :
    addAll acc (x :: xs) = addAll (addNew acc x) xs := rfl

theorem addAll_append (acc xs ys : List α) :
    addAll acc (xs ++ ys) = addAll (addAll acc xs) ys := List.foldl_append

theorem mem_addAll {xs acc : List α} {y : α} : y ∈ addAll acc xs ↔ y ∈ acc ∨ y ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [addAll_cons, ih, mem_addNew, List.mem_cons]
    tauto

@[simp] theorem firsts_nil : firsts ([] : List α) = [] := rfl

theorem mem_firsts {xs : List α} {y : α} : y ∈ firsts xs ↔ y ∈ xs := by
  simp [firsts, mem_addAll]

theorem firsts_append (xs ys : List α) : firsts (xs ++ ys) = addAll (firsts xs) ys :=
  addAll_append [] xs ys

theorem firsts_concat (xs : List α) (x : α) : firsts (xs ++ [x]) = addNew (firsts xs) x :=
  firsts_append xs [x]

/-- Adding what is already there changes nothing. -/
theorem addAll_of_subset {acc zs : List α} (h : ∀ z ∈ zs, z ∈ acc) : addAll acc zs = acc := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    rw [addAll_cons, addNew, ite_eq_left (h z List.mem_cons_self)]
    exact ih fun z hz => h z (List.mem_cons_of_mem _ hz)

/-- Under a `flatMap`, repeats of the list mapped over do not matter. -/
theorem addAll_flatMap_firsts [DecidableEq β] (acc : List α) (g : β → List α) (ys : List β) :
    addAll acc ((firsts ys).flatMap g) = addAll acc (ys.flatMap g) := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    rw [firsts_concat, List.flatMap_append, addAll_append, ← ih]
    unfold addNew
    split
    · rename_i hy
      refine (addAll_of_subset fun z hz => ?_).symm
      rw [ih, mem_addAll]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hz
      exact .inr (List.mem_flatMap.mpr ⟨y, mem_firsts.mp hy, hz⟩)
    · rw [List.flatMap_append, addAll_append]

/-- What is added matters only through its first occurrences. -/
theorem addAll_firsts (acc ys : List α) : addAll acc (firsts ys) = addAll acc ys := by
  have := addAll_flatMap_firsts acc (fun y : α => [y]) ys
  simpa using this

theorem addAll_congr (acc : List α) {ys ys' : List α} (h : firsts ys = firsts ys') :
    addAll acc ys = addAll acc ys' := by
  rw [← addAll_firsts acc ys, h, addAll_firsts]

theorem firsts_firsts (ys : List α) : firsts (firsts ys) = firsts ys := addAll_firsts [] ys

theorem addAll_filterMap_firsts [DecidableEq β] (acc : List α) (f : β → Option α) (ys : List β) :
    addAll acc ((firsts ys).filterMap f) = addAll acc (ys.filterMap f) := by
  simp only [List.filterMap_eq_flatMap_toList, addAll_flatMap_firsts]

/-- Under a `flatMap`, repeats within what each member is mapped to do not
matter. -/
theorem addAll_flatMap_congr (g g' : β → List α) : ∀ (ys : List β) (acc : List α),
    (∀ y ∈ ys, firsts (g y) = firsts (g' y)) → addAll acc (ys.flatMap g) = addAll acc (ys.flatMap g')
  | [], _, _ => rfl
  | y :: ys, acc, h => by
    rw [List.flatMap_cons, List.flatMap_cons, addAll_append, addAll_append,
      addAll_congr acc (h y List.mem_cons_self)]
    exact addAll_flatMap_congr g g' ys _ fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- `addAll` puts the new members after the old ones, without their repeats. -/
theorem addAll_eq_append_eraseDups (xs acc : List α) :
    addAll acc xs = acc ++ (xs.filter fun x => decide (x ∉ acc)).eraseDups := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [addAll_cons, ih, addNew]
    by_cases hx : x ∈ acc
    · rw [ite_eq_left hx, List.filter_cons]
      simp [hx]
    · rw [ite_eq_right hx, List.filter_cons]
      simp only [hx, not_false_eq_true, decide_true, ↓reduceIte, List.eraseDups_cons,
        List.append_assoc, List.cons_append, List.nil_append, List.filter_filter]
      congr 3
      refine List.filter_congr fun y _ => ?_
      by_cases hy : y = x <;> simp [hy, hx]

/-- The first occurrences are what `List.eraseDups` keeps. -/
theorem firsts_eq_eraseDups (xs : List α) : firsts xs = xs.eraseDups := by
  simp [firsts, addAll_eq_append_eraseDups]

end RwLog
