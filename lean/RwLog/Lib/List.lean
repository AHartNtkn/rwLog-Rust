/-
# Facts about lists and conditionals with no rwLog content
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card

namespace RwLog

theorem ite_of_pos {α : Type} {c : Prop} [Decidable c] {x y : α} (h : c) :
    (if c then x else y) = x := by simp [h]

theorem ite_of_neg {α : Type} {c : Prop} [Decidable c] {x y : α} (h : ¬ c) :
    (if c then x else y) = y := by simp [h]

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  cases l with
  | nil => simp
  | cons a as =>
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨by simp, ih _ ?_ _ rfl⟩
    have := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons] at h
    omega

theorem length_eraseDups {α : Type} [DecidableEq α] (l : List α) :
    l.eraseDups.length = l.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (nodup_eraseDups l)]
  congr 1; ext; simp

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun x => (x, f x)
  | [] => rfl
  | x :: l => by simp [zip_map_self f l]

theorem map_zip_map_self {α β γ : Type} (f : α → β) (h : α × β → γ) (l : List α) :
    (l.zip (l.map f)).map h = l.map fun a => h (a, f a) := by
  rw [zip_map_self, List.map_map]; rfl

/-! ## Sums of natural numbers over lists -/

theorem sum_flatMap_map {α β : Type} (f : α → List β) (g : β → Nat) (xs : List α) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]

/-- A sum over a `filterMap` is a sum over the list, with dropped members
counting zero. -/
theorem sum_filterMap_map {α β : Type} (f : α → Option β) (g : β → Nat) (xs : List α) :
    ((xs.filterMap f).map g).sum = (xs.map fun x => (f x).elim 0 g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons]
    cases h : f x with
    | none => simp only [ih, List.map_cons, List.sum_cons, h, Option.elim_none, Nat.zero_add]
    | some y => simp only [ih, List.map_cons, List.sum_cons, h, Option.elim_some]

theorem le_sum_map_of_mem {α : Type} (f : α → Nat) {xs : List α} {x : α} (h : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => cases h
  | cons y xs ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

theorem sum_map_le {α : Type} {f g : α → Nat} {xs : List α} (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons y xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem sum_map_le_mul {α : Type} {f : α → Nat} {c : Nat} : ∀ {xs : List α}, (∀ x ∈ xs, f x ≤ c) →
    (xs.map f).sum ≤ xs.length * c
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := sum_map_le_mul (xs := xs) fun y hy => h y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem sum_range_getD : ∀ l : List Nat,
    ((List.range l.length).map fun i => l[i]?.getD 0).sum = l.sum
  | [] => by simp
  | a :: l => by
    have ih := sum_range_getD l
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.sum_cons, List.getElem?_cons_zero, Option.getD_some]
    have e : ((fun i => (a :: l)[i]?.getD 0) ∘ Nat.succ) = fun i => l[i]?.getD 0 := by
      funext i; simp
    rw [e, ih]

theorem sum_map_add' {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons y xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul_left' {α : Type} (a : Nat) (f : α → Nat) (xs : List α) :
    (xs.map fun x => a * f x).sum = a * (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons y xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_mul_right' {α : Type} (a : Nat) (f : α → Nat) (xs : List α) :
    (xs.map fun x => f x * a).sum = (xs.map f).sum * a := by
  induction xs with
  | nil => simp
  | cons y xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

/-! ## Lengths and stretches -/

theorem two_le_length_of_mem {α : Type} {L : List α} {a c : α} (ha : a ∈ L) (hc : c ∈ L)
    (h : a ≠ c) : 2 ≤ L.length := by
  match L, ha, hc with
  | [x], ha, hc =>
    simp only [List.mem_singleton] at ha hc
    exact absurd (ha.trans hc.symm) h
  | _ :: _ :: _, _, _ => simp

theorem drop_take_reverse {α : Type} (l : List α) {i j : Nat} (hij : i < j) (hj : j ≤ l.length) :
    (l.reverse.take j).drop i = ((l.take (l.length - i)).drop (l.length - j)).reverse := by
  rw [List.take_reverse, List.drop_reverse, List.drop_take, List.length_drop]
  congr 2
  omega

/-! ## Changing one member -/

/-- A change that a function does not see is not seen in the image. -/
theorem map_modify_eq {α β : Type} (g : α → β) (f : α → α) (h : ∀ x, g (f x) = g x)
    (l : List α) (k : Nat) : (l.modify k f).map g = l.map g := by
  apply List.ext_getElem?
  intro n
  simp only [List.getElem?_map, List.getElem?_modify]
  cases l[n]? with
  | none => rfl
  | some x =>
    show some (g (if k = n then f x else x)) = some (g x)
    split
    · rw [h]
    · rfl

/-- A member of a list with one member changed is a member or a changed
member. -/
theorem mem_modify {α : Type} {l : List α} {k : Nat} {f : α → α} {x : α}
    (h : x ∈ l.modify k f) : x ∈ l ∨ ∃ y ∈ l, x = f y := by
  obtain ⟨n, hn⟩ := List.getElem?_of_mem h
  rw [List.getElem?_modify] at hn
  cases hl : l[n]? with
  | none => rw [hl] at hn; cases hn
  | some y =>
    rw [hl] at hn
    have e : (if k = n then f y else y) = x := Option.some.inj hn
    split at e
    · exact .inr ⟨y, List.mem_of_getElem? hl, e.symm⟩
    · exact .inl (e ▸ List.mem_of_getElem? hl)

/-! ## Lists related member by member -/

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β},
    List.Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons (b := b) h hs, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self .., h⟩
    · obtain ⟨y, hy, r⟩ := forall₂_mem_left hs hx
      exact ⟨y, List.mem_cons_of_mem _ hy, r⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β},
    List.Forall₂ R xs ys → ∀ {y}, y ∈ ys → ∃ x ∈ xs, R x y
  | _, _, .nil, _, hy => by cases hy
  | _, _, .cons (a := a) h hs, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨x, hx, r⟩ := forall₂_mem_right hs hy
      exact ⟨x, List.mem_cons_of_mem _ hx, r⟩

theorem forall₂_getElem? {α β : Type} {E : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ E l l' → ∀ {k : Nat} {x : α}, l[k]? = some x → ∃ y, l'[k]? = some y ∧ E x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab t, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, hab⟩
  | _, _, .cons _ t, k + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? t h

theorem forall₂_getLast? {α β : Type} {E : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ E l l') {x : α} (hx : l.getLast? = some x) :
    ∃ y, l'.getLast? = some y ∧ E x y := by
  rw [List.getLast?_eq_getElem?] at hx ⊢
  rw [← h.length_eq]
  exact forall₂_getElem? h hx

end RwLog
