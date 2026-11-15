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

/-- A list of numbers in order, with its duplicates erased, is strictly in
order. -/
theorem pairwise_lt_eraseDups (l : List Nat) (hl : l.Pairwise (· ≤ ·)) :
    l.eraseDups.Pairwise (· < ·) := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  cases l with
  | nil => simp
  | cons a as =>
    rw [List.eraseDups_cons]
    have hp := List.pairwise_cons.1 hl
    refine List.pairwise_cons.2 ⟨fun b hb => ?_,
      ih _ ?_ _ (hp.2.sublist List.filter_sublist) rfl⟩
    · have hb' := List.mem_filter.1 (List.mem_eraseDups.1 hb)
      have h1 := hp.1 b hb'.1
      have h2 : b ≠ a := by simpa using hb'.2
      omega
    · have := List.length_filter_le (fun b => !b == a) as
      simp only [List.length_cons] at h
      omega

/-- Two lists of numbers of one length, the second no less at any place:
its sum is no less. -/
theorem sum_le_sum_of_getElem : ∀ {l l' : List Nat}, l.length = l'.length →
    (∀ (i a b : Nat), l[i]? = some a → l'[i]? = some b → a ≤ b) → l.sum ≤ l'.sum
  | [], [], _, _ => Nat.le_refl _
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l, b :: l', hlen, h => by
    have h0 := h 0 a b rfl rfl
    have ih := sum_le_sum_of_getElem (l := l) (l' := l') (by simpa using hlen)
      fun i x y hx hy => h (i + 1) x y hx hy
    simp only [List.sum_cons]
    omega

/-- And if it is more at some place, its sum is more. -/
theorem sum_lt_sum_of_getElem : ∀ {l l' : List Nat}, l.length = l'.length →
    (∀ (i a b : Nat), l[i]? = some a → l'[i]? = some b → a ≤ b) →
    (∃ (i a b : Nat), l[i]? = some a ∧ l'[i]? = some b ∧ a < b) → l.sum < l'.sum
  | [], _, _, _, ⟨_, _, _, h, _⟩ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | a :: l, b :: l', hlen, h, ⟨i, x, y, hx, hy, hxy⟩ => by
    have h0 := h 0 a b rfl rfl
    have hlen' : l.length = l'.length := by simpa using hlen
    have hle := sum_le_sum_of_getElem hlen' fun i x y hx hy => h (i + 1) x y hx hy
    simp only [List.sum_cons]
    cases i with
    | zero =>
      cases hx
      cases hy
      omega
    | succ i =>
      have := sum_lt_sum_of_getElem hlen' (fun i x y hx hy => h (i + 1) x y hx hy)
        ⟨i, x, y, hx, hy, hxy⟩
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

/-- Setting a member to one with the same image leaves the images. -/
theorem map_set_same {α β : Type} (f : α → β) {l : List α} {j : Nat} {a a' : α}
    (h : l[j]? = some a) (e : f a' = f a) : (l.set j a').map f = l.map f := by
  apply List.ext_getElem?
  intro m
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_set]
  split
  · next hjm =>
    subst hjm
    have hlt := (List.getElem?_eq_some_iff.1 h).1
    rw [h]
    simp [hlt, e]
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

/-- A function that sends each member of the second list to the member of the
first it is related to maps the second list to the first. -/
theorem forall₂_map {α β : Type} {E : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ E l l') {f : β → α} (hf : ∀ x y, E x y → f y = x) : l'.map f = l := by
  induction h with
  | nil => rfl
  | cons hq _ ih => simp only [List.map_cons, hf _ _ hq, ih]

theorem forall₂_getLast? {α β : Type} {E : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ E l l') {x : α} (hx : l.getLast? = some x) :
    ∃ y, l'.getLast? = some y ∧ E x y := by
  rw [List.getLast?_eq_getElem?] at hx ⊢
  rw [← h.length_eq]
  exact forall₂_getElem? h hx

/-! ## Lookup in a list sorted by key -/

theorem lookup_sorted {β : Type} : ∀ {L : List (Nat × β)}, (L.Pairwise fun a b => a.1 < b.1) →
    ∀ b ∈ L, L.lookup b.1 = some b.2
  | [], _, b, hb => by simp at hb
  | a :: L, h, b, hb => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · simp [List.lookup]
    · have hne : (b.1 == a.1) = false := by
        have := h.1 b hb
        simpa using Nat.ne_of_gt this
      simp only [List.lookup, hne]
      exact lookup_sorted h.2 b hb

/-! ## The values of a list of options -/

/-- The values of a list of options, when each has one. -/
def gather {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | a :: l => a.bind fun x => (gather l).map (x :: ·)

theorem gather_eq_some {α : Type} : ∀ {l : List (Option α)} {ys : List α},
    gather l = some ys ↔ l = ys.map some
  | [], ys => by cases ys <;> simp [gather]
  | a :: l, ys => by
    cases a with
    | none => cases ys <;> simp [gather]
    | some x =>
      cases ys with
      | nil => simp [gather]
      | cons y ys =>
        simp only [gather, Option.bind_some, Option.map_eq_some_iff, List.map_cons,
          List.cons.injEq, Option.some.injEq]
        constructor
        · rintro ⟨zs, hz, rfl, rfl⟩
          exact ⟨rfl, gather_eq_some.1 hz⟩
        · rintro ⟨rfl, h⟩
          exact ⟨ys, gather_eq_some.2 h, rfl, rfl⟩

theorem gather_range {α : Type} {k : Nat} {g : Nat → Option α} {ys : List α} :
    gather ((List.range k).map g) = some ys ↔
      ys.length = k ∧ ∀ i (h : i < ys.length), g i = some ys[i] := by
  rw [gather_eq_some]
  constructor
  · intro h
    have hl : ys.length = k := by simpa using (congrArg List.length h).symm
    refine ⟨hl, fun i hi => ?_⟩
    have := congrArg (fun l => l[i]?) h
    simpa [hl ▸ hi, List.getElem?_eq_getElem hi] using this
  · rintro ⟨rfl, h⟩
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp only [List.length_map, List.length_range] at h₁
    simp [h i h₁]

theorem gather_isSome {α : Type} : ∀ {l : List (Option α)},
    (gather l).isSome = true ↔ ∀ o ∈ l, o.isSome = true
  | [] => by simp [gather]
  | a :: l => by
    cases a with
    | none => simp [gather]
    | some x => simp [gather, gather_isSome (l := l)]

/-! ## Lists related place by place -/

/-- A member of a list of numbers is no more than their sum. -/
theorem le_sum_of_mem : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | x :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem h
      simp only [List.sum_cons]
      omega

/-- Two lists of the same length whose members at each place are related. -/
def Pointwise {α β : Type} (r : α → β → Prop) (l : List α) (l' : List β) : Prop :=
  l.length = l'.length ∧ ∀ (m : Nat) (x : α) (y : β), l[m]? = some x → l'[m]? = some y → r x y

theorem Pointwise.refl {α : Type} {r : α → α → Prop} (h : ∀ x, r x x) (l : List α) :
    Pointwise r l l :=
  ⟨rfl, fun m x y hx hy => by rw [hx] at hy; cases hy; exact h x⟩

theorem Pointwise.get {α β : Type} {r : α → β → Prop} {l : List α} {l' : List β}
    (h : Pointwise r l l') {m : Nat} {x : α} (hx : l[m]? = some x) :
    ∃ y, l'[m]? = some y ∧ r x y := by
  have hm : m < l'.length := by rw [← h.1]; exact (List.getElem?_eq_some_iff.1 hx).1
  exact ⟨l'[m], List.getElem?_eq_getElem hm, h.2 m x _ hx (List.getElem?_eq_getElem hm)⟩

theorem Pointwise.get' {α β : Type} {r : α → β → Prop} {l : List α} {l' : List β}
    (h : Pointwise r l l') {m : Nat} {y : β} (hy : l'[m]? = some y) :
    ∃ x, l[m]? = some x ∧ r x y := by
  have hm : m < l.length := by rw [h.1]; exact (List.getElem?_eq_some_iff.1 hy).1
  exact ⟨l[m], List.getElem?_eq_getElem hm, h.2 m _ y (List.getElem?_eq_getElem hm) hy⟩

theorem Pointwise.comp {α β γ : Type} {r₁ : α → β → Prop} {r₂ : β → γ → Prop}
    {r₃ : α → γ → Prop} (h : ∀ a b c, r₁ a b → r₂ b c → r₃ a c) {l₁ : List α} {l₂ : List β}
    {l₃ : List γ} (h₁ : Pointwise r₁ l₁ l₂) (h₂ : Pointwise r₂ l₂ l₃) : Pointwise r₃ l₁ l₃ :=
  ⟨h₁.1.trans h₂.1, fun m x z hx hz => by
    obtain ⟨y, hy, hr⟩ := h₁.get hx
    exact h _ _ _ hr (h₂.2 m y z hy hz)⟩

theorem Pointwise.imp {α β : Type} {r r' : α → β → Prop} (h : ∀ a b, r a b → r' a b)
    {l : List α} {l' : List β} (hp : Pointwise r l l') : Pointwise r' l l' :=
  ⟨hp.1, fun m x y hx hy => h _ _ (hp.2 m x y hx hy)⟩

theorem pointwise_cons {α β : Type} {r : α → β → Prop} {x : α} {y : β} {l : List α}
    {l' : List β} : Pointwise r (x :: l) (y :: l') ↔ r x y ∧ Pointwise r l l' := by
  constructor
  · intro h
    exact ⟨h.2 0 x y rfl rfl, by simpa using h.1, fun m a b ha hb =>
      h.2 (m + 1) a b (by simpa using ha) (by simpa using hb)⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨by simp [h1], fun m a b ha hb => ?_⟩
    cases m with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
      subst ha; subst hb; exact h0
    | succ m => exact h2 m a b (by simpa using ha) (by simpa using hb)

/-- Changing one member to a related one. -/
theorem Pointwise.set {α : Type} {r : α → α → Prop} {l l' : List α} (h : Pointwise r l l')
    {j : Nat} {y : α} (hy : ∀ x, l[j]? = some x → r x y) : Pointwise r l (l'.set j y) := by
  refine ⟨by rw [List.length_set]; exact h.1, fun m a b ha hb => ?_⟩
  rw [List.getElem?_set] at hb
  split at hb
  · next e =>
    subst e
    split at hb
    · cases hb; exact hy a ha
    · cases hb
  · exact h.2 m a b ha hb

/-- Changing one member by a function to a related one. -/
theorem pointwise_modify {α : Type} {r : α → α → Prop} (hr : ∀ x, r x x) (l : List α) (j : Nat)
    (f : α → α) (hf : ∀ x, l[j]? = some x → r x (f x)) : Pointwise r l (l.modify j f) := by
  refine ⟨by rw [List.length_modify], fun m a b ha hb => ?_⟩
  rw [List.getElem?_modify, ha] at hb
  split at hb
  · next e =>
    subst e
    cases hb
    exact hf a ha
  · simp only [id_map', Option.some.injEq] at hb
    subst hb
    exact hr a

end RwLog
