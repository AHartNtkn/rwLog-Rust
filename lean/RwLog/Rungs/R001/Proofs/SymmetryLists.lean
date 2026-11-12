/-
# Rung R001, Symmetry: answer lists up to equivalence

The mirrored run picks other representatives of the same classes of
equivalent answers, and sees its candidates in another order. These are the
list facts the comparison of the two runs needs:

* `StepEquiv` is an equivalence relation and a congruence for `++`,
  `flatMap` and `map Span.swap`.
* `ClassEq xs ys`: the same classes of equivalent answers occur in both
  lists. Candidates only need to agree up to `ClassEq`, because a table keeps
  one representative of each maximal new class (`fresh`), and two lists with
  one member per class and the same classes are `StepEquiv`.
* `maxima` and `fresh` commute with `map Span.swap` exactly, since they read
  spans only through `covers?`.
-/
import RwLog.Rungs.R001.Proofs.Kernel

namespace RwLog

namespace R001

/-! ## Equivalent spans -/

theorem covers?_iff (a s : Span) : a.covers? s = true ↔ a.Covers s := covers_iff a s

theorem Span.Equiv.refl (a : Span) : a.Equiv a := ⟨Span.Covers.refl a, Span.Covers.refl a⟩

theorem Span.Equiv.symm {a b : Span} (h : a.Equiv b) : b.Equiv a := ⟨h.2, h.1⟩

theorem Span.Equiv.trans {a b c : Span} (h₁ : a.Equiv b) (h₂ : b.Equiv c) : a.Equiv c :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem Span.Equiv.swap {a b : Span} (h : a.Equiv b) : a.swap.Equiv b.swap :=
  ⟨covers_swap h.1, covers_swap h.2⟩

theorem Span.Covers.of_swap {a b : Span} (h : a.swap.Covers b.swap) : a.Covers b := by
  simpa using covers_swap h

theorem covers?_swap (a b : Span) : a.swap.covers? b.swap = a.covers? b := by
  apply Bool.eq_iff_iff.2
  rw [covers?_iff, covers?_iff]
  exact ⟨Span.Covers.of_swap, covers_swap⟩

/-- Equivalence is read the same through `covers?`. -/
theorem covers?_congr {a a' b b' : Span} (ha : a.Equiv a') (hb : b.Equiv b') :
    a.covers? b = a'.covers? b' := by
  apply Bool.eq_iff_iff.2
  rw [covers?_iff, covers?_iff]
  exact ⟨fun h => ha.2.trans (h.trans hb.1), fun h => ha.1.trans (h.trans hb.2)⟩

theorem equiv_of_den_eq {a b : Span} (h : a.den = b.den) : a.Equiv b :=
  ⟨Span.Covers.of_den_subset h.ge, Span.Covers.of_den_subset h.le⟩

/-! ## `StepEquiv` -/

theorem StepEquiv.refl (xs : List Span) : StepEquiv xs xs :=
  ⟨xs, List.Perm.refl _, List.forall₂_same.2 fun x _ => Span.Equiv.refl x⟩

theorem StepEquiv.of_perm {xs ys : List Span} (h : xs.Perm ys) : StepEquiv xs ys :=
  ⟨xs, h, List.forall₂_same.2 fun x _ => Span.Equiv.refl x⟩

theorem StepEquiv.of_forall₂ {xs ys : List Span} (h : List.Forall₂ Span.Equiv xs ys) :
    StepEquiv xs ys :=
  ⟨ys, List.Perm.refl _, h⟩

theorem StepEquiv.symm {xs ys : List Span} (h : StepEquiv xs ys) : StepEquiv ys xs := by
  obtain ⟨ys', hp, hf⟩ := h
  obtain ⟨m, hm, hmp⟩ := List.perm_comp_forall₂ hp.symm (hf.flip)
  exact ⟨m, hmp, hm.imp fun _ _ h => Span.Equiv.symm h⟩

theorem forall₂_equiv_trans : ∀ {xs ys zs : List Span}, List.Forall₂ Span.Equiv xs ys →
    List.Forall₂ Span.Equiv ys zs → List.Forall₂ Span.Equiv xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' => .cons (Span.Equiv.trans h h') (forall₂_equiv_trans hs hs')

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β},
    List.Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons (b := b) h hs, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self .., h⟩
    · obtain ⟨y, hy, r⟩ := forall₂_mem_left hs hx
      exact ⟨y, List.mem_cons_of_mem _ hy, r⟩

theorem StepEquiv.trans {xs ys zs : List Span} (h₁ : StepEquiv xs ys) (h₂ : StepEquiv ys zs) :
    StepEquiv xs zs := by
  obtain ⟨ys', hp, hf⟩ := h₁
  obtain ⟨zs', hq, hg⟩ := h₂
  obtain ⟨m, hm, hmp⟩ := List.perm_comp_forall₂ hp hg
  refine ⟨m, hmp.trans hq, ?_⟩
  exact forall₂_equiv_trans hf hm

theorem StepEquiv.append {xs ys xs' ys' : List Span} (h : StepEquiv xs ys) (h' : StepEquiv xs' ys') :
    StepEquiv (xs ++ xs') (ys ++ ys') := by
  obtain ⟨u, hp, hf⟩ := h
  obtain ⟨u', hp', hf'⟩ := h'
  exact ⟨u ++ u', hp.append hp', List.rel_append hf hf'⟩

theorem StepEquiv.map_swap {xs ys : List Span} (h : StepEquiv xs ys) :
    StepEquiv (xs.map Span.swap) (ys.map Span.swap) := by
  obtain ⟨u, hp, hf⟩ := h
  refine ⟨u.map Span.swap, hp.map _, ?_⟩
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hf.imp fun _ _ h => Span.Equiv.swap h

theorem StepEquiv.length {xs ys : List Span} (h : StepEquiv xs ys) : xs.length = ys.length := by
  obtain ⟨u, hp, hf⟩ := h
  rw [hf.length_eq, hp.length_eq]

theorem StepEquiv.mem {xs ys : List Span} (h : StepEquiv xs ys) {x : Span} (hx : x ∈ xs) :
    ∃ y ∈ ys, x.Equiv y := by
  obtain ⟨u, hp, hf⟩ := h
  obtain ⟨y, hy, hxy⟩ := forall₂_mem_left hf hx
  exact ⟨y, hp.subset hy, hxy⟩

/-- `flatMap` over related lists with related images. -/
theorem StepEquiv.flatMap {α : Type} {xs ys : List α} (R : α → α → Prop)
    (hxy : ∃ ys', ys'.Perm ys ∧ List.Forall₂ R xs ys')
    {f g : α → List Span} (hfg : ∀ x y, R x y → StepEquiv (f x) (g y)) :
    StepEquiv (xs.flatMap f) (ys.flatMap g) := by
  obtain ⟨ys', hp, hf⟩ := hxy
  refine StepEquiv.trans ?_ (StepEquiv.of_perm (hp.flatMap_right g))
  clear hp
  induction hf with
  | nil => exact StepEquiv.refl _
  | cons h _ ih => simp only [List.flatMap_cons]; exact (hfg _ _ h).append ih

/-! ## The same classes of equivalent answers -/

/-- The same classes of equivalent answers occur in both lists. -/
def ClassEq (xs ys : List Span) : Prop :=
  (∀ x ∈ xs, ∃ y ∈ ys, x.Equiv y) ∧ (∀ y ∈ ys, ∃ x ∈ xs, x.Equiv y)

theorem ClassEq.refl (xs : List Span) : ClassEq xs xs :=
  ⟨fun x hx => ⟨x, hx, Span.Equiv.refl x⟩, fun x hx => ⟨x, hx, Span.Equiv.refl x⟩⟩

theorem ClassEq.symm {xs ys : List Span} (h : ClassEq xs ys) : ClassEq ys xs :=
  ⟨fun y hy => let ⟨x, hx, e⟩ := h.2 y hy; ⟨x, hx, e.symm⟩,
   fun x hx => let ⟨y, hy, e⟩ := h.1 x hx; ⟨y, hy, e.symm⟩⟩

theorem ClassEq.trans {xs ys zs : List Span} (h₁ : ClassEq xs ys) (h₂ : ClassEq ys zs) :
    ClassEq xs zs :=
  ⟨fun x hx => let ⟨y, hy, e⟩ := h₁.1 x hx; let ⟨z, hz, e'⟩ := h₂.1 y hy; ⟨z, hz, Span.Equiv.trans e e'⟩,
   fun z hz => let ⟨y, hy, e⟩ := h₂.2 z hz; let ⟨x, hx, e'⟩ := h₁.2 y hy; ⟨x, hx, Span.Equiv.trans e' e⟩⟩

theorem ClassEq.of_stepEquiv {xs ys : List Span} (h : StepEquiv xs ys) : ClassEq xs ys :=
  ⟨fun _ hx => h.mem hx, fun _ hy => let ⟨x, hx, e⟩ := h.symm.mem hy; ⟨x, hx, e.symm⟩⟩

theorem ClassEq.append {xs ys xs' ys' : List Span} (h : ClassEq xs ys) (h' : ClassEq xs' ys') :
    ClassEq (xs ++ xs') (ys ++ ys') := by
  constructor
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨y, hy, e⟩ := h.1 x hx; exact ⟨y, List.mem_append_left _ hy, e⟩
    · obtain ⟨y, hy, e⟩ := h'.1 x hx; exact ⟨y, List.mem_append_right _ hy, e⟩
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨x, hx, e⟩ := h.2 y hy; exact ⟨x, List.mem_append_left _ hx, e⟩
    · obtain ⟨x, hx, e⟩ := h'.2 y hy; exact ⟨x, List.mem_append_right _ hx, e⟩

theorem ClassEq.map_swap {xs ys : List Span} (h : ClassEq xs ys) :
    ClassEq (xs.map Span.swap) (ys.map Span.swap) := by
  constructor
  · simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := h.1 x hx
    exact ⟨_, ⟨y, hy, rfl⟩, Span.Equiv.swap e⟩
  · simp only [List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, e⟩ := h.2 y hy
    exact ⟨_, ⟨x, hx, rfl⟩, Span.Equiv.swap e⟩

/-- `flatMap` over lists with the same classes, with images that depend only
on the class. -/
theorem ClassEq.flatMap {α : Type} {xs ys : List α} (R : α → α → Prop)
    (h₁ : ∀ x ∈ xs, ∃ y ∈ ys, R x y) (h₂ : ∀ y ∈ ys, ∃ x ∈ xs, R x y)
    {f g : α → List Span} (hfg : ∀ x y, R x y → ClassEq (f x) (g y)) :
    ClassEq (xs.flatMap f) (ys.flatMap g) := by
  constructor
  · intro z hz
    obtain ⟨x, hx, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨y, hy, r⟩ := h₁ x hx
    obtain ⟨w, hw, e⟩ := (hfg x y r).1 z hz
    exact ⟨w, List.mem_flatMap.2 ⟨y, hy, hw⟩, e⟩
  · intro w hw
    obtain ⟨y, hy, hw⟩ := List.mem_flatMap.1 hw
    obtain ⟨x, hx, r⟩ := h₂ y hy
    obtain ⟨z, hz, e⟩ := (hfg x y r).2 w hw
    exact ⟨z, List.mem_flatMap.2 ⟨x, hx, hz⟩, e⟩

theorem ClassEq.of_mem_iff {xs ys : List Span} (h : ∀ z, z ∈ xs ↔ z ∈ ys) : ClassEq xs ys :=
  ⟨fun x hx => ⟨x, (h x).1 hx, Span.Equiv.refl x⟩, fun y hy => ⟨y, (h y).2 hy, Span.Equiv.refl y⟩⟩

/-! ## Maximal answers, one per class -/

/-- The members of `xs` no member strictly covers. -/
def top (xs : List Span) : List Span :=
  xs.filter fun x => !xs.any fun y => y.covers? x && !x.covers? y

theorem maxima_eq (xs : List Span) :
    maxima xs = (top xs).foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x]) [] :=
  rfl

/-- The fold of `maxima`: what it keeps comes from its input, no member covers
another, and every input member is covered by a kept one. -/
theorem fold_spec : ∀ (l acc : List Span),
    (∀ a ∈ acc, ∀ b ∈ acc, a ≠ b ∨ True) →
    let r := l.foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x]) acc
    (∀ z ∈ r, z ∈ acc ∨ z ∈ l) ∧ (∀ z ∈ acc, z ∈ r) ∧ (∀ x ∈ l, ∃ y ∈ r, y.covers? x = true)
  | [], acc, _ => by simp
  | x :: l, acc, h => by
    simp only [List.foldl_cons]
    by_cases hx : (acc.any fun y => y.covers? x) = true
    · simp only [hx, ite_true]
      obtain ⟨h₁, h₂, h₃⟩ := fold_spec l acc h
      refine ⟨fun z hz => (h₁ z hz).elim .inl fun hz => .inr (List.mem_cons_of_mem _ hz), h₂, ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · obtain ⟨w, hw, hc⟩ := List.any_eq_true.1 hx
        exact ⟨w, h₂ w hw, hc⟩
      · exact h₃ y hy
    · simp only [hx, Bool.false_eq_true, ite_false]
      obtain ⟨h₁, h₂, h₃⟩ := fold_spec l (acc ++ [x]) (fun _ _ _ _ => .inr trivial)
      refine ⟨fun z hz => ?_, fun z hz => h₂ z (List.mem_append_left _ hz), ?_⟩
      · rcases h₁ z hz with hz | hz
        · rcases List.mem_append.1 hz with hz | hz
          · exact .inl hz
          · simp only [List.mem_singleton] at hz; subst hz; exact .inr (List.mem_cons_self ..)
        · exact .inr (List.mem_cons_of_mem _ hz)
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨y, h₂ y (by simp), (covers?_iff _ _).2 (Span.Covers.refl y)⟩
        · exact h₃ y hy

/-- No member of the fold's result covers a later one. -/
theorem fold_pairwise : ∀ (l acc : List Span),
    acc.Pairwise (fun a b => a.covers? b = false ∧ b.covers? a = false) →
    (l.foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x]) acc).Pairwise
      (fun a b => a.covers? b = false ∨ b.covers? a = false)
  | [], acc, h => h.imp fun h => .inl h.1
  | x :: l, acc, h => by
    simp only [List.foldl_cons]
    by_cases hx : (acc.any fun y => y.covers? x) = true
    · simp only [hx, ite_true]; exact fold_pairwise l acc h
    · simp only [hx, Bool.false_eq_true, ite_false]
      refine (fold_pairwise_weak l (acc ++ [x]) ?_)
      rw [List.pairwise_append]
      refine ⟨h.imp fun h => .inl h.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb; subst hb
      exact .inl (by simpa using (List.any_eq_false.1 (Bool.eq_false_iff.2 hx)) a ha)
where
  fold_pairwise_weak : ∀ (l acc : List Span),
      acc.Pairwise (fun a b => a.covers? b = false ∨ b.covers? a = false) →
      (l.foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x]) acc).Pairwise
        (fun a b => a.covers? b = false ∨ b.covers? a = false)
    | [], acc, h => h
    | x :: l, acc, h => by
      simp only [List.foldl_cons]
      by_cases hx : (acc.any fun y => y.covers? x) = true
      · simp only [hx, ite_true]; exact fold_pairwise_weak l acc h
      · simp only [hx, Bool.false_eq_true, ite_false]
        refine fold_pairwise_weak l (acc ++ [x]) ?_
        rw [List.pairwise_append]
        refine ⟨h, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
        simp only [List.mem_singleton] at hb; subst hb
        exact .inl (by simpa using (List.any_eq_false.1 (Bool.eq_false_iff.2 hx)) a ha)

theorem mem_maxima {xs : List Span} {x : Span} (h : x ∈ maxima xs) : x ∈ top xs := by
  rw [maxima_eq] at h
  rcases (fold_spec (top xs) [] (by simp)).1 x h with h | h
  · simp at h
  · exact h

theorem maxima_covers {xs : List Span} {x : Span} (h : x ∈ top xs) :
    ∃ y ∈ maxima xs, y.covers? x = true := by
  rw [maxima_eq]; exact (fold_spec (top xs) [] (by simp)).2.2 x h

/-- No two kept answers are equivalent. -/
theorem maxima_distinct (xs : List Span) :
    (maxima xs).Pairwise fun a b => ¬ a.Equiv b := by
  rw [maxima_eq]
  refine (fold_pairwise.fold_pairwise_weak _ [] List.Pairwise.nil).imp fun h e => ?_
  rcases h with h | h
  · rw [(covers?_iff _ _).2 e.1] at h; cases h
  · rw [(covers?_iff _ _).2 e.2] at h; cases h

theorem mem_top {xs : List Span} {x : Span} :
    x ∈ top xs ↔ x ∈ xs ∧ ∀ y ∈ xs, y.Covers x → x.Covers y := by
  simp only [top, List.mem_filter, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true,
    not_and, Bool.not_eq_false, covers?_iff]

/-- The tops of two lists with the same classes have the same classes. -/
theorem top_classEq {xs ys : List Span} (h : ClassEq xs ys) : ClassEq (top xs) (top ys) := by
  have key : ∀ {xs ys : List Span}, ClassEq xs ys → ∀ x ∈ top xs, ∃ y ∈ top ys, x.Equiv y := by
    intro xs ys h x hx
    rw [mem_top] at hx
    obtain ⟨y, hy, e⟩ := h.1 x hx.1
    refine ⟨y, mem_top.2 ⟨hy, fun z hz hzy => ?_⟩, e⟩
    obtain ⟨w, hw, e'⟩ := h.2 z hz
    exact e.2.trans ((hx.2 w hw (e'.1.trans (hzy.trans e.2))).trans e'.1)
  exact ⟨key h, fun y hy => let ⟨x, hx, e⟩ := key h.symm y hy; ⟨x, hx, e.symm⟩⟩

theorem maxima_classEq_top (xs : List Span) : ClassEq (maxima xs) (top xs) := by
  constructor
  · intro x hx; exact ⟨x, mem_maxima hx, Span.Equiv.refl x⟩
  · intro x hx
    obtain ⟨y, hy, hc⟩ := maxima_covers hx
    rw [covers?_iff] at hc
    have hyt := mem_top.1 (mem_maxima hy)
    exact ⟨y, hy, hc, (mem_top.1 hx).2 y hyt.1 hc⟩

/-- Two lists with one member per class and the same classes agree up to
order and equivalence. -/
theorem stepEquiv_of_classEq : ∀ {xs ys : List Span},
    xs.Pairwise (fun a b => ¬ a.Equiv b) → ys.Pairwise (fun a b => ¬ a.Equiv b) →
    ClassEq xs ys → StepEquiv xs ys
  | [], ys, _, _, h => by
    cases ys with
    | nil => exact StepEquiv.refl _
    | cons y _ => obtain ⟨x, hx, _⟩ := h.2 y (List.mem_cons_self ..); cases hx
  | x :: xs, ys, hx, hy, h => by
    obtain ⟨y, hyin, e⟩ := h.1 x (List.mem_cons_self ..)
    have hperm := List.perm_cons_erase hyin
    have hy' : (ys.erase y).Pairwise (fun a b => ¬ a.Equiv b) := hy.sublist (List.erase_sublist ..)
    have hx' := (List.pairwise_cons.1 hx)
    have hrest : ClassEq xs (ys.erase y) := by
      constructor
      · intro x' hx'in
        obtain ⟨y', hy'in, e'⟩ := h.1 x' (List.mem_cons_of_mem _ hx'in)
        refine ⟨y', ?_, e'⟩
        have hne : y' ≠ y := by
          rintro rfl; exact hx'.1 x' hx'in (Span.Equiv.trans e (Span.Equiv.symm e'))
        exact (List.mem_erase_of_ne hne).2 hy'in
      · intro y' hy'in
        obtain ⟨x', hx'in, e'⟩ := h.2 y' (List.mem_of_mem_erase hy'in)
        rcases List.mem_cons.1 hx'in with rfl | hx'in
        · exfalso
          have hp := (List.perm_cons_erase hyin)
          have : (y :: ys.erase y).Pairwise (fun a b => ¬ a.Equiv b) := hp.pairwise hy
            (fun h e => h e.symm)
          exact (List.pairwise_cons.1 this).1 y' hy'in (Span.Equiv.trans (Span.Equiv.symm e) e')
        · exact ⟨x', hx'in, e'⟩
    obtain ⟨u, hu, hf⟩ := stepEquiv_of_classEq hx'.2 hy' hrest
    exact ⟨y :: u, (hu.cons y).trans hperm.symm, .cons e hf⟩

theorem maxima_stepEquiv {xs ys : List Span} (h : ClassEq xs ys) :
    StepEquiv (maxima xs) (maxima ys) :=
  stepEquiv_of_classEq (maxima_distinct xs) (maxima_distinct ys)
    (((maxima_classEq_top xs).trans (top_classEq h)).trans (maxima_classEq_top ys).symm)

theorem filter_classEq {xs ys old old' : List Span} (h : ClassEq xs ys) (ho : ClassEq old old') :
    ClassEq (xs.filter fun c => !old.any fun t => t.covers? c)
      (ys.filter fun c => !old'.any fun t => t.covers? c) := by
  have key : ∀ {xs ys old old' : List Span}, ClassEq xs ys → ClassEq old old' →
      ∀ x ∈ xs.filter (fun c => !old.any fun t => t.covers? c),
        ∃ y ∈ ys.filter (fun c => !old'.any fun t => t.covers? c), x.Equiv y := by
    intro xs ys old old' h ho x hx
    simp only [List.mem_filter, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true] at hx ⊢
    obtain ⟨y, hy, e⟩ := h.1 x hx.1
    refine ⟨y, ⟨hy, fun t ht => ?_⟩, e⟩
    obtain ⟨t', ht', e'⟩ := ho.2 t ht
    rw [← covers?_congr e' e]
    exact hx.2 t' ht'
  exact ⟨key h ho, fun y hy => let ⟨x, hx, e⟩ := key h.symm ho.symm y hy; ⟨x, hx, e.symm⟩⟩

theorem fresh_stepEquiv {old old' cands cands' : List Span} (ho : ClassEq old old')
    (hc : ClassEq cands cands') : StepEquiv (fresh old cands) (fresh old' cands') :=
  maxima_stepEquiv (filter_classEq hc ho)

/-! ## `maxima` and `fresh` commute with swapping -/

theorem top_map_swap (xs : List Span) : top (xs.map Span.swap) = (top xs).map Span.swap := by
  simp only [top, List.filter_map, List.any_map, Function.comp_def, covers?_swap]

theorem maxima_map_swap (xs : List Span) :
    maxima (xs.map Span.swap) = (maxima xs).map Span.swap := by
  rw [maxima_eq, maxima_eq, top_map_swap]
  generalize top xs = l
  suffices ∀ acc : List Span,
      (l.map Span.swap).foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x])
        (acc.map Span.swap) =
      (l.foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x]) acc).map
        Span.swap from this []
  induction l with
  | nil => intro; rfl
  | cons x l ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons, List.any_map, Function.comp_def, covers?_swap]
    split
    · exact ih acc
    · rw [← ih (acc ++ [x])]; simp

theorem fresh_map_swap (old cands : List Span) :
    fresh (old.map Span.swap) (cands.map Span.swap) = (fresh old cands).map Span.swap := by
  simp only [fresh, List.filter_map, List.any_map, Function.comp_def, covers?_swap, maxima_map_swap]

end R001

end RwLog
