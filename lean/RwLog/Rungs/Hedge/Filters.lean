/-
# The filters of the hedge

What `Hedge.plain` and `Hedge.dropCovered` return and what they spend.

* `plain_sound`: a span that `plain` accepts carries no constraints.
* `dropCovered_ticks`: dropping the spans covered by spans without constraints
  costs the sizes compared, and nothing for any search.
* `fresh_sizes_le`: the spans that enter a list through `Tabled.fresh` have
  been paid for by their sizes.
-/
import RwLog.Rungs.Hedge.Machine
import RwLog.Rungs.Tabled.Exact
import RwLog.Rungs.Framework.Cost
import RwLog.Lib.List
import RwLog.Kernel.Size

namespace RwLog

open Cost

theorem Term.size_le_bind' {V W : Type} (σ : V → Term W) : ∀ t : Term V, t.size ≤ (t.bind σ).size
  | .var v => Term.size_pos _
  | .sym _ => Nat.le_refl _
  | .app t u => by
    have h1 := Term.size_le_bind' σ t
    have h2 := Term.size_le_bind' σ u
    simp only [Term.bind_app, Term.size]
    omega

theorem Term.size_le_rename {V W : Type} (f : V → W) (t : Term V) : t.size ≤ (t.rename f).size :=
  Term.size_le_bind' _ t

namespace Hedge

/-- The sizes of a list of spans, added up. -/
def sizes (xs : List Span) : Nat := (xs.map Span.size).sum

@[simp] theorem sizes_nil : sizes [] = 0 := rfl

@[simp] theorem sizes_cons (x : Span) (xs : List Span) : sizes (x :: xs) = x.size + sizes xs := by
  simp [sizes]

@[simp] theorem sizes_append (xs ys : List Span) : sizes (xs ++ ys) = sizes xs + sizes ys := by
  simp [sizes]

theorem length_le_sizes : ∀ xs : List Span, xs.length ≤ sizes xs
  | [] => Nat.le_refl _
  | x :: xs => by
    have := length_le_sizes xs
    have := Span.size_pos x
    simp only [List.length_cons, sizes_cons]
    omega

theorem sizes_sublist {xs ys : List Span} (h : xs.Sublist ys) : sizes xs ≤ sizes ys := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a _ ih => simp only [sizes_cons]; omega
  | cons_cons a _ ih => simp only [sizes_cons]; omega

/-! ## `plain` -/

theorem store_size_finish (θ : Nat ⊕ Nat → Term (Nat ⊕ Nat)) (f : Nat → Nat ⊕ Nat) :
    ∀ c : Store, Store.size c ≤
      Store.size ((c.map (Term.rename f)).map fun t => (t.bind θ).rename enc)
  | [] => Nat.le_refl _
  | t :: c => by
    have ih := store_size_finish θ f c
    have h1 := Term.size_le_rename f t
    have h2 := Term.size_le_bind' θ (t.rename f)
    have h3 := Term.size_le_rename enc ((t.rename f).bind θ)
    simp only [Store.size, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem store_size_map_append (g : Term (Nat ⊕ Nat) → Pat) (xs ys : List (Term (Nat ⊕ Nat))) :
    Store.size ((xs ++ ys).map g) = Store.size (xs.map g) + Store.size (ys.map g) := by
  simp [Store.size]

/-- A span conjoined with itself has its store twice. -/
theorem size_meet_self {x z : Span} (h : x.meet x = some z) : x.size + Store.size x.c ≤ z.size := by
  unfold Span.meet at h
  cases hs : solve [(Pat.left x.l, Pat.right x.l), (Pat.left x.r, Pat.right x.r)] with
  | none => rw [hs] at h; cases h
  | some θ =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have h1 := Term.size_le_rename enc ((Pat.left x.l).bind θ)
    have h2 := Term.size_le_bind' θ (Pat.left x.l)
    have h3 : x.l.size ≤ (Pat.left x.l).size := Term.size_le_rename _ x.l
    have h4 := Term.size_le_rename enc ((Pat.left x.r).bind θ)
    have h5 := Term.size_le_bind' θ (Pat.left x.r)
    have h6 : x.r.size ≤ (Pat.left x.r).size := Term.size_le_rename _ x.r
    have h7 : Store.size x.c ≤ Store.size ((x.c.map Pat.left).map fun t => (t.bind θ).rename enc) :=
      store_size_finish θ Sum.inl x.c
    have h8 : Store.size x.c ≤ Store.size ((x.c.map Pat.right).map fun t => (t.bind θ).rename enc) :=
      store_size_finish θ Sum.inr x.c
    have h9 := store_size_map_append (fun t => (t.bind θ).rename enc) (x.c.map Pat.left)
      (x.c.map Pat.right)
    show x.l.size + x.r.size + Store.size x.c + Store.size x.c ≤
      ((Pat.left x.l).bind θ |>.rename enc).size + ((Pat.left x.r).bind θ |>.rename enc).size +
        Store.size ((x.c.map Pat.left ++ x.c.map Pat.right).map fun t => (t.bind θ).rename enc)
    omega

theorem store_nil_of_size {c : Store} (h : Store.size c = 0) : c = [] := by
  cases c with
  | nil => rfl
  | cons t c =>
    have := Term.size_pos t
    simp only [Store.size, List.map_cons, List.sum_cons] at h
    omega

/-- A span that `plain` accepts carries no constraints. -/
theorem plain_sound {x : Span} (h : (plain x).val = true) : x.c = [] := by
  simp only [plain, bind_val, Charged.meet, pure_val] at h
  cases hm : x.meet x with
  | none => rw [hm] at h; cases h
  | some z =>
    rw [hm] at h
    have hz : z.size ≤ x.size := of_decide_eq_true h
    have := size_meet_self hm
    exact store_nil_of_size (by omega)

/-! ## `dropCovered` -/

@[simp] theorem dropCovered_val (old xs : List Span) :
    (dropCovered old xs).val = xs.filter fun x => !old.any fun t => t.covers? x := by
  simp [dropCovered, Charged.covers]

theorem any_covers_ticks {old : List Span} (h : ∀ t ∈ old, t.c = []) (x : Span) :
    (anyL (fun t => Charged.covers t x) old).ticks ≤ sizes old + old.length * x.size := by
  refine le_trans (anyL_ticks_le _ _) ?_
  induction old with
  | nil => simp
  | cons t old ih =>
    have ih' := ih fun u hu => h u (List.mem_cons_of_mem _ hu)
    have ht : Charged.coversWork t x = 0 := Charged.coversWork_nil (h t List.mem_cons_self) x
    simp only [List.map_cons, List.sum_cons, Charged.covers, sizes_cons, List.length_cons, ht,
      Nat.succ_mul] at ih' ⊢
    omega

/-- Dropping the spans covered by spans without constraints costs the sizes
compared. -/
theorem dropCovered_ticks {old : List Span} (h : ∀ t ∈ old, t.c = []) :
    ∀ xs : List Span, (dropCovered old xs).ticks ≤ xs.length * sizes old + old.length * sizes xs
  | [] => by simp [dropCovered, filterL]
  | x :: xs => by
    have ih := dropCovered_ticks h xs
    have hx := any_covers_ticks h x
    simp only [dropCovered, filterL, bind_ticks, pure_ticks, Nat.add_zero, List.length_cons,
      sizes_cons, Nat.succ_mul, Nat.mul_add] at ih ⊢
    omega

end Hedge

end RwLog

namespace RwLog

open Cost

namespace Hedge

/-! ## What enters through `fresh` has been paid for -/

theorem anyL_ticks_of_false {α : Type} (f : α → Cost Bool) :
    ∀ xs : List α, (anyL f xs).val = false → (anyL f xs).ticks = (xs.map fun x => (f x).ticks).sum
  | [], _ => rfl
  | x :: xs, h => by
    simp only [anyL, bind_val] at h
    simp only [anyL, bind_ticks, List.map_cons, List.sum_cons]
    cases hx : (f x).val with
    | true => rw [hx] at h; simp at h
    | false =>
      rw [hx] at h
      simp only [Bool.false_eq_true, ite_false] at h ⊢
      rw [anyL_ticks_of_false f xs h]

theorem sizes_filter_le {f : Span → Cost Bool} :
    ∀ ys : List Span, (∀ x ∈ ys, (f x).val = true → x.size ≤ (f x).ticks) →
      sizes (ys.filter fun x => (f x).val) ≤ (ys.map fun x => (f x).ticks).sum
  | [], _ => Nat.le_refl _
  | y :: ys, h => by
    have ih := sizes_filter_le ys fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hy := h y List.mem_cons_self
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases hv : (f y).val with
    | true => simp only [ite_true, sizes_cons]; have := hy hv; omega
    | false => simp only [Bool.false_eq_true, ite_false]; omega

theorem foldl_keep_sublist (p : List Span → Span → Bool) :
    ∀ (l acc : List Span), ∃ r, r.Sublist l ∧
      l.foldl (fun acc x => if p acc x then acc else acc ++ [x]) acc = acc ++ r
  | [], acc => ⟨[], List.Sublist.refl _, by simp⟩
  | x :: l, acc => by
    simp only [List.foldl_cons]
    by_cases hp : p acc x = true
    · obtain ⟨r, hr, e⟩ := foldl_keep_sublist p l acc
      exact ⟨r, hr.cons x, by simp only [hp, ite_true]; exact e⟩
    · obtain ⟨r, hr, e⟩ := foldl_keep_sublist p l (acc ++ [x])
      exact ⟨x :: r, hr.cons_cons x, by simp only [hp, Bool.false_eq_true, ite_false]; rw [e]; simp⟩

/-- The maximal spans of a list have been paid for by their sizes. -/
theorem maxima_sizes_le (xs : List Span) : sizes (Tabled.maxima xs).val ≤ (Tabled.maxima xs).ticks := by
  rw [Tabled.maxima_val]
  let f : Span → Cost Bool := fun x => do
    let b ← anyL (fun y => do
      let c ← Charged.covers y x
      if c then do
        let c' ← Charged.covers x y
        pure !c'
      else pure false) xs
    pure !b
  have ht : (filterL f xs).ticks ≤ (Tabled.maxima xs).ticks := by
    simp only [Tabled.maxima, bind_ticks, f]
    omega
  have hv : (xs.filter fun x => (f x).val) =
      xs.filter fun x => !xs.any fun y => y.covers? x && !x.covers? y := by
    simp [f, Charged.covers]
  obtain ⟨r, hr, e⟩ := foldl_keep_sublist (fun acc x => acc.any fun y => y.covers? x)
    (xs.filter fun x => !xs.any fun y => y.covers? x && !x.covers? y) []
  have hm : RwLog.maxima xs = r := by
    unfold RwLog.maxima
    simpa using e
  rw [hm]
  refine le_trans (sizes_sublist hr) (le_trans ?_ ht)
  rw [← hv, filterL_ticks]
  refine sizes_filter_le xs fun x hx hk => ?_
  simp only [f, bind_val, pure_val, Bool.not_eq_true'] at hk
  simp only [f, bind_ticks, pure_ticks, Nat.add_zero]
  rw [anyL_ticks_of_false _ _ hk]
  refine le_trans ?_ (le_sum_map_of_mem _ hx)
  simp only [bind_ticks, Charged.covers]
  omega

/-- The spans that enter through `fresh` have been paid for by their sizes. -/
theorem fresh_sizes_le (old cands : List Span) :
    sizes (Tabled.fresh old cands).val ≤ (Tabled.fresh old cands).ticks := by
  have h := maxima_sizes_le (filterL (fun c => do
    let b ← anyL (fun t => Charged.covers t c) old
    pure !b) cands).val
  simp only [Tabled.fresh, bind_val, bind_ticks]
  omega

end Hedge

end RwLog
