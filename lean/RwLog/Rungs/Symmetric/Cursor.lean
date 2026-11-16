/-
# The cursor of a join combines every pair of answers

`Cursor.Before c p q` says the pair at the positions `p` and `q` is combined
when the cursor is `c`. `Cursor.Ok` is what a cursor keeps in tables of given
lengths: it has filed no more answers than there are, and the pairs combined
are of answers that are there.

`Cursor.next` returns a pair of answers filed that was not combined, and
after it is marked the pairs combined are those combined before and that pair
(`next_spec`).

Every pair of answers filed is reached. `Cursor.rank` measures how far a
cursor is from a pair: the pairs of earlier answers not combined, and then,
for each class of the pair from the narrowest to the widest, how far its
siblings are from having been fed more than the class. The order of the
measures is well founded (`rankLt_wf`), and a unit of a join that combines
another pair makes the measure fall (`Cursor.rank_fall`): the pair combined is
of the same class to the end, and then it is an earlier pair; or it leaves the
classes of the pair at some depth for a sibling that was fed no more than the
class of the pair there, and is now fed more than it was, while nothing
narrower is touched.

`leastBy` returns an entry that passes its test (`leastBy_ok`), with the
least key of those that pass (`leastBy_le`), and returns nothing only when
none passes (`leastBy_none`). Moving one entry of a list to a smaller
measure makes the sum of the measures smaller (`sum_map_modify_lt`).

Nothing here is about a kernel.
-/
import RwLog.Rungs.Symmetric.Machine
import Mathlib.Data.List.Shortlex
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace RwLog

namespace Symmetric

/-- The pair at the positions `p` and `q` is combined. -/
def Cursor.Before (c : Cursor) (p q : Nat) : Prop := (p, q) ∈ c.done

/-- Every pair of answers of tables of `la` and `lb` answers is combined. -/
def Cursor.Full (la lb : Nat) (c : Cursor) : Prop := ∀ p q, p < la → q < lb → c.Before p q

/-- The pairs of positions below `la` and `lb`. -/
def pairsBelow (la lb : Nat) : List (Nat × Nat) :=
  (List.range la).flatMap fun i => (List.range lb).map fun j => (i, j)

/-- The pairs still to combine in tables of `la` and `lb` answers. -/
def Cursor.left (la lb : Nat) (c : Cursor) : List (Nat × Nat) :=
  (pairsBelow la lb).filter fun p => !c.done.contains p

/-- What a cursor keeps in tables of `la` and `lb` answers: it has filed no
more answers than there are, the pairs combined are of answers filed, and the
pairs to combine are those of answers filed that are not combined. -/
def Cursor.Ok (la lb : Nat) (c : Cursor) : Prop :=
  c.pa.length ≤ la ∧ c.pb.length ≤ lb ∧
    (∀ x ∈ c.done, x.1 < c.pa.length ∧ x.2 < c.pb.length) ∧
    ∀ x, x ∈ c.todo ↔ (x.1 < c.pa.length ∧ x.2 < c.pb.length) ∧ x ∉ c.done

theorem Cursor.ok_start (la lb : Nat) : Cursor.start.Ok la lb := by
  simp [Cursor.Ok, Cursor.start]

theorem Cursor.before_start (p q : Nat) : ¬ Cursor.start.Before p q := by
  simp [Cursor.Before, Cursor.start]

/-- A cursor that fits tables fits them when they have grown. -/
theorem Cursor.Ok.mono {la lb la' lb' : Nat} {c : Cursor} (h : c.Ok la lb) (ha : la ≤ la')
    (hb : lb ≤ lb') : c.Ok la' lb' :=
  ⟨Nat.le_trans h.1 ha, Nat.le_trans h.2.1 hb, h.2.2⟩

/-- A pair that is combined is inside the tables. -/
theorem Cursor.Ok.before_lt {la lb : Nat} {c : Cursor} (h : c.Ok la lb) {p q : Nat}
    (hb : c.Before p q) : p < la ∧ q < lb := by
  have := h.2.2.1 (p, q) hb
  have h1 := h.1
  have h2 := h.2.1
  exact ⟨by omega, by omega⟩

theorem mem_pairsBelow {la lb : Nat} {x : Nat × Nat} :
    x ∈ pairsBelow la lb ↔ x.1 < la ∧ x.2 < lb := by
  obtain ⟨p, q⟩ := x
  simp only [pairsBelow, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, j, hj, rfl, rfl⟩
    exact ⟨hi, hj⟩
  · exact fun h => ⟨p, h.1, q, h.2, rfl, rfl⟩

theorem mem_pairsNew {a0 b0 a1 b1 : Nat} (ha : a0 ≤ a1) (hb : b0 ≤ b1) {x : Nat × Nat} :
    x ∈ pairsNew a0 b0 a1 b1 ↔ (x.1 < a1 ∧ x.2 < b1) ∧ ¬ (x.1 < a0 ∧ x.2 < b0) := by
  obtain ⟨p, q⟩ := x
  simp only [pairsNew, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_range',
    List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨i, ⟨d, hd, rfl⟩, j, hj, rfl, rfl⟩ | ⟨i, hi, j, ⟨d, hd, rfl⟩, rfl, rfl⟩)
    · exact ⟨⟨by omega, hj⟩, by omega⟩
    · exact ⟨⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    by_cases hp : p < a0
    · exact .inr ⟨p, hp, q, ⟨q - b0, by omega, by omega⟩, rfl, rfl⟩
    · exact .inl ⟨p, ⟨p - a0, by omega, by omega⟩, q, h2, rfl, rfl⟩

theorem Cursor.mem_left {la lb : Nat} {c : Cursor} {x : Nat × Nat} :
    x ∈ c.left la lb ↔ (x.1 < la ∧ x.2 < lb) ∧ ¬ c.Before x.1 x.2 := by
  simp [Cursor.left, mem_pairsBelow, Cursor.Before]

/-- The pairs to combine are the pairs of answers filed that are left. -/
theorem Cursor.Ok.mem_todo {la lb : Nat} {c : Cursor} (h : c.Ok la lb) {x : Nat × Nat} :
    x ∈ c.todo ↔ x ∈ c.left c.pa.length c.pb.length := by
  rw [h.2.2.2 x, Cursor.mem_left]
  rfl

/-- **Is a pair left?** No pair is left exactly when every pair of answers of
the tables is combined. -/
theorem Cursor.Ok.pending_false {la lb : Nat} {c : Cursor} (h : c.Ok la lb) :
    c.pending la lb = false ↔ c.Full la lb := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Cursor.pending, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
    List.isEmpty_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨ht, ha⟩, hb⟩ p q hp hq
    have hpa : p < c.pa.length := by omega
    have hqb : q < c.pb.length := by omega
    by_contra hn
    have : (p, q) ∈ c.todo := (h4 (p, q)).2 ⟨⟨hpa, hqb⟩, hn⟩
    rw [ht] at this
    cases this
  · intro hf
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · cases ht : c.todo with
      | nil => rfl
      | cons x l =>
        have hx : x ∈ c.todo := by rw [ht]; exact List.mem_cons_self
        have hm := (h4 x).1 hx
        exact absurd (hf x.1 x.2 (by omega) (by omega)) hm.2
    · by_contra hc
      have hc' : c.pa.length < la ∧ 0 < lb := by omega
      have := h3 _ (hf c.pa.length 0 hc'.1 hc'.2)
      simp at this
    · by_contra hc
      have hc' : c.pb.length < lb ∧ 0 < la := by omega
      have := h3 _ (hf 0 c.pb.length hc'.2 hc'.1)
      simp at this

/-! ## Filing the answers -/

@[simp] theorem Cursor.see_done (pa pb : List Path) (c : Cursor) : (c.see pa pb).done = c.done :=
  rfl

@[simp] theorem Cursor.see_fed (pa pb : List Path) (c : Cursor) : (c.see pa pb).fed = c.fed := rfl

theorem Cursor.see_pa_length (pa pb : List Path) (c : Cursor) :
    (c.see pa pb).pa.length = max c.pa.length pa.length := by
  simp only [Cursor.see, List.length_append, List.length_drop]
  omega

theorem Cursor.see_pb_length (pa pb : List Path) (c : Cursor) :
    (c.see pa pb).pb.length = max c.pb.length pb.length := by
  simp only [Cursor.see, List.length_append, List.length_drop]
  omega

theorem Cursor.before_see {pa pb : List Path} {c : Cursor} {p q : Nat} :
    (c.see pa pb).Before p q ↔ c.Before p q := Iff.rfl

/-- The steps down to a pair of answers that were filed stay. -/
theorem Cursor.stepsAt_see (pa pb : List Path) (c : Cursor) {x : Nat × Nat}
    (h1 : x.1 < c.pa.length) (h2 : x.2 < c.pb.length) : (c.see pa pb).stepsAt x = c.stepsAt x := by
  simp only [Cursor.stepsAt, Cursor.see, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h1, List.getElem?_append_left h2]

/-- A cursor that fits the tables fits them with their answers filed, and
has then filed them all. -/
theorem Cursor.Ok.see {la lb : Nat} {c : Cursor} (h : c.Ok la lb) {pa pb : List Path}
    (ha : pa.length = la) (hb : pb.length = lb) :
    (c.see pa pb).Ok la lb ∧ (c.see pa pb).pa.length = la ∧ (c.see pa pb).pb.length = lb := by
  have h1 := Cursor.see_pa_length pa pb c
  have h2 := Cursor.see_pb_length pa pb c
  obtain ⟨h3, h4, h5, h6⟩ := h
  have e1 : (c.see pa pb).pa.length = la := by omega
  have e2 : (c.see pa pb).pb.length = lb := by omega
  refine ⟨⟨by omega, by omega, fun x hx => ?_, fun x => ?_⟩, e1, e2⟩
  · have := h5 x hx
    rw [e1, e2]
    omega
  · have ht : (c.see pa pb).todo = c.todo ++
        pairsNew c.pa.length c.pb.length (c.see pa pb).pa.length (c.see pa pb).pb.length := rfl
    rw [ht, List.mem_append, mem_pairsNew (by omega) (by omega), h6 x]
    show _ ↔ _ ∧ x ∉ c.done
    constructor
    · rintro (⟨hf, hd⟩ | ⟨hf, hn⟩)
      · exact ⟨⟨by omega, by omega⟩, hd⟩
      · exact ⟨hf, fun hd => hn (h5 x hd)⟩
    · rintro ⟨hf, hd⟩
      by_cases hold : x.1 < c.pa.length ∧ x.2 < c.pb.length
      · exact .inl ⟨hold, hd⟩
      · exact .inr ⟨hf, hold⟩

/-! ## The next pair -/

/-- Choosing by a comparison returns an entry of the list, and nothing only
of the empty list. -/
theorem foldl_choose_mem {α : Type} (lt : α → α → Bool) :
    ∀ (l : List α) (b : Option α) (x : α),
      l.foldl (fun best p => match best with
        | none => some p
        | some b => if lt p b then some p else some b) b = some x → x ∈ l ∨ b = some x
  | [], b, x, h => .inr h
  | a :: l, b, x, h => by
    rw [List.foldl_cons] at h
    rcases foldl_choose_mem lt l _ x h with h1 | h1
    · exact .inl (List.mem_cons_of_mem _ h1)
    · cases b with
      | none => simp only [Option.some.injEq] at h1; exact .inl (h1 ▸ List.mem_cons_self)
      | some b =>
        by_cases hl : lt a b = true
        · simp only [hl, ite_true, Option.some.injEq] at h1; exact .inl (h1 ▸ List.mem_cons_self)
        · simp only [hl, Bool.false_eq_true, ite_false] at h1; exact .inr h1

theorem foldl_choose_none {α : Type} (lt : α → α → Bool) :
    ∀ (l : List α) (b : Option α),
      l.foldl (fun best p => match best with
        | none => some p
        | some b => if lt p b then some p else some b) b = none → l = [] ∧ b = none
  | [], b, h => ⟨rfl, h⟩
  | a :: l, b, h => by
    rw [List.foldl_cons] at h
    have := (foldl_choose_none lt l _ h).2
    cases b with
    | none => simp at this
    | some b => by_cases hl : lt a b = true <;> simp [hl] at this

/-- Choosing by a key returns an entry of the least key. -/
theorem foldl_choose_least {α β : Type} [LinearOrder β] (key : α → β) (lt : α → α → Bool)
    (hlt : ∀ p b, lt p b = true ↔ key p < key b) :
    ∀ (l : List α) (b : Option α) (x : α),
      l.foldl (fun best p => match best with
        | none => some p
        | some b => if lt p b then some p else some b) b = some x →
      (∀ y ∈ l, key x ≤ key y) ∧ ∀ y, b = some y → key x ≤ key y
  | [], b, x, h => ⟨fun _ hy => (by cases hy), fun y hy => by
      rw [List.foldl_nil] at h
      rw [h] at hy
      cases hy
      exact le_refl _⟩
  | a :: l, b, x, h => by
    rw [List.foldl_cons] at h
    obtain ⟨i1, i2⟩ := foldl_choose_least key lt hlt l _ x h
    cases b with
    | none =>
      have ha := i2 a rfl
      exact ⟨fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ha
        · exact i1 y hy, fun _ hy => by cases hy⟩
    | some b =>
      by_cases hl : key a < key b
      · have ha := i2 a (by simp only [(hlt a b).2 hl, ite_true])
        refine ⟨fun y hy => ?_, fun y hy => ?_⟩
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact ha
          · exact i1 y hy
        · cases hy
          exact le_of_lt (lt_of_le_of_lt ha hl)
      · have hb := i2 b (by
          have : lt a b = false := by
            cases e : lt a b with
            | false => rfl
            | true => exact absurd ((hlt a b).1 e) hl
          simp only [this, Bool.false_eq_true, ite_false])
        refine ⟨fun y hy => ?_, fun y hy => by cases hy; exact hb⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact le_trans hb (not_lt.1 hl)
        · exact i1 y hy

/-- A pair returned is one of the pairs to combine. -/
theorem Cursor.next_todo {c : Cursor} {x : Nat × Nat} (h : c.next = some x) : x ∈ c.todo := by
  rcases foldl_choose_mem _ _ _ _ (show List.foldl _ none _ = some x from h) with h1 | h1
  · exact h1
  · cases h1

/-- No pair is returned only when there is none to combine. -/
theorem Cursor.next_none_todo {c : Cursor} (h : c.next = none) : c.todo = [] :=
  (foldl_choose_none _ _ _ (show List.foldl _ none _ = none from h)).1

/-- The pair returned has the least key of the pairs to combine. -/
theorem Cursor.next_least {c : Cursor} {x : Nat × Nat} (h : c.next = some x) :
    ∀ y ∈ c.todo, c.keyOf x ≤ c.keyOf y :=
  fun y hy => (foldl_choose_least c.keyOf _ (fun _ _ => by simp) _ _ _
    (show List.foldl _ none _ = some x from h)).1 y hy

/-- A pair returned is of answers filed and was not combined. -/
theorem Cursor.next_mem {la lb : Nat} {c : Cursor} (hok : c.Ok la lb) {x : Nat × Nat}
    (h : c.next = some x) : x ∈ c.left c.pa.length c.pb.length := by
  rcases foldl_choose_mem _ _ _ _ (show List.foldl _ none _ = some x from h) with h1 | h1
  · exact hok.mem_todo.1 h1
  · cases h1

/-- No pair is returned only when every pair of answers filed is combined. -/
theorem Cursor.next_none {la lb : Nat} {c : Cursor} (hok : c.Ok la lb) (h : c.next = none) :
    c.Full c.pa.length c.pb.length := by
  intro p q hp hq
  by_contra hn
  have hm : (p, q) ∈ c.todo := hok.mem_todo.2 (Cursor.mem_left.2 ⟨⟨hp, hq⟩, hn⟩)
  rw [(foldl_choose_none _ _ _ (show List.foldl _ none _ = none from h)).1] at hm
  cases hm

/-- The pair returned has the least key of the pairs left. -/
theorem Cursor.next_le {la lb : Nat} {c : Cursor} (hok : c.Ok la lb) {x : Nat × Nat}
    (h : c.next = some x) : ∀ y ∈ c.left c.pa.length c.pb.length, c.keyOf x ≤ c.keyOf y :=
  fun y hy => (foldl_choose_least c.keyOf _ (fun _ _ => by simp) _ _ _
    (show List.foldl _ none _ = some x from h)).1 y (hok.mem_todo.2 hy)

/-- The pairs combined after a pair is marked are those combined before and
that pair. -/
theorem Cursor.before_mark {c : Cursor} {x : Nat × Nat} {t p q : Nat} :
    (c.mark x t).Before p q ↔ c.Before p q ∨ x = (p, q) := by
  simp only [Cursor.Before, Cursor.mark, List.mem_cons]
  constructor
  · rintro (h | h)
    · exact .inr h.symm
    · exact .inl h
  · rintro (h | h)
    · exact .inr h
    · exact .inl h.symm

/-- **A unit of a join**: a pair returned is of answers filed and was not
combined; once it is marked the cursor still fits and the pair is
combined. -/
theorem Cursor.next_spec {la lb : Nat} {c : Cursor} {x : Nat × Nat} (t : Nat)
    (hok : c.Ok la lb) (h : c.next = some x) :
    (x.1 < c.pa.length ∧ x.2 < c.pb.length) ∧ ¬ c.Before x.1 x.2 ∧
      (c.mark x t).Ok la lb ∧ (c.mark x t).Before x.1 x.2 := by
  have hm := Cursor.mem_left.1 (Cursor.next_mem hok h)
  refine ⟨hm.1, hm.2, ⟨hok.1, hok.2.1, fun y hy => ?_, fun y => ?_⟩,
    Cursor.before_mark.2 (.inr rfl)⟩
  · simp only [Cursor.mark, List.mem_cons] at hy
    rcases hy with hy | hy
    · exact hy ▸ hm.1
    · exact hok.2.2.1 y hy
  · simp only [Cursor.mark, List.mem_filter, List.mem_cons, bne_iff_ne, ne_eq, not_or]
    rw [hok.2.2.2 y]
    constructor
    · rintro ⟨⟨hf, hd⟩, hne⟩
      exact ⟨hf, hne, hd⟩
    · rintro ⟨hf, hne, hd⟩
      exact ⟨⟨hf, hd⟩, hne⟩

theorem leastBy_ok {α : Type} {key : α → Nat} {ok : α → Bool} {l : List α} {x : α}
    (h : leastBy key ok l = some x) : ok x = true := by
  have main : ∀ (ys : List α) (best : Option α), (∀ y ∈ ys, ok y = true) →
      (∀ b, best = some b → ok b = true) →
      ys.foldl (fun best x =>
        match best with
        | none => some x
        | some b => if key x < key b then some x else some b) best = some x → ok x = true := by
    intro ys
    induction ys with
    | nil => intro best _ hb h; exact hb x h
    | cons y ys ih =>
      intro best hy hb h
      refine ih _ (fun z hz => hy z (List.mem_cons_of_mem _ hz)) (fun b hbb => ?_) h
      cases best with
      | none => cases hbb; exact hy _ List.mem_cons_self
      | some b' =>
        simp only at hbb
        split at hbb
        · cases hbb; exact hy _ List.mem_cons_self
        · cases hbb; exact hb _ rfl
  exact main _ none (fun y hy => (List.mem_filter.1 hy).2) (fun _ h => by cases h) h

theorem leastBy_le {α : Type} {key : α → Nat} {ok : α → Bool} {l : List α} {x : α}
    (h : leastBy key ok l = some x) : ∀ y ∈ l, ok y = true → key x ≤ key y := by
  have main : ∀ (ys : List α) (best : Option α),
      ys.foldl (fun best x =>
        match best with
        | none => some x
        | some b => if key x < key b then some x else some b) best = some x →
      (∀ b, best = some b → key x ≤ key b) ∧ ∀ y ∈ ys, key x ≤ key y := by
    intro ys
    induction ys with
    | nil =>
      intro best h
      exact ⟨fun b hb => by rw [List.foldl_nil] at h; rw [h] at hb; cases hb; exact Nat.le_refl _,
        fun _ hy => by cases hy⟩
    | cons y ys ih =>
      intro best h
      obtain ⟨i1, i2⟩ := ih _ h
      cases best with
      | none =>
        have := i1 y rfl
        exact ⟨(fun _ hb => by cases hb), fun z hz => by
          rcases List.mem_cons.1 hz with rfl | hz
          · exact this
          · exact i2 z hz⟩
      | some b =>
        by_cases hk : key y < key b
        · have := i1 y (by simp only [hk, ite_true])
          exact ⟨fun b' hb => by cases hb; omega, fun z hz => by
            rcases List.mem_cons.1 hz with rfl | hz
            · exact this
            · exact i2 z hz⟩
        · have := i1 b (by simp only [hk, ite_false])
          exact ⟨fun b' hb => by cases hb; exact this, fun z hz => by
            rcases List.mem_cons.1 hz with rfl | hz
            · omega
            · exact i2 z hz⟩
  intro y hy hok
  exact (main _ none h).2 y (List.mem_filter.2 ⟨hy, hok⟩)

/-- `leastBy` returns nothing only when no entry passes. -/
theorem leastBy_none {α : Type} {key : α → Nat} {ok : α → Bool} {l : List α}
    (h : leastBy key ok l = none) : ∀ y ∈ l, ok y = false := by
  have main : ∀ (ys : List α) (best : Option α),
      ys.foldl (fun best x =>
        match best with
        | none => some x
        | some b => if key x < key b then some x else some b) best = none →
      best = none ∧ ys = [] := by
    intro ys
    induction ys with
    | nil => intro best h; exact ⟨h, rfl⟩
    | cons y ys ih =>
      intro best h
      have := (ih _ h).1
      cases best with
      | none => cases this
      | some b =>
        simp only at this
        split at this <;> cases this
  intro y hy
  have := (main _ none h).2
  cases hok : ok y with
  | false => rfl
  | true =>
    have hm : y ∈ l.filter ok := List.mem_filter.2 ⟨hy, hok⟩
    rw [this] at hm
    cases hm

/-- Moving one entry of a list to a smaller measure makes the sum of the
measures smaller. -/
theorem sum_map_modify_lt {α : Type} (g : α → Nat) (f : α → α) :
    ∀ (l : List α) (j : Nat) (x : α), l[j]? = some x → g (f x) < g x →
      ((l.modify j f).map g).sum < (l.map g).sum
  | [], _, _, h, _ => by cases h
  | y :: l, 0, x, h, hlt => by
    cases h
    simp only [List.modify_zero_cons, List.map_cons, List.sum_cons]
    omega
  | y :: l, j + 1, x, h, hlt => by
    have := sum_map_modify_lt g f l j x (by simpa using h) hlt
    simp only [List.modify_succ_cons, List.map_cons, List.sum_cons]
    omega

/-! ## Every pair is reached -/

/-- The steps of a pair choose a side or end. -/
theorem stepsOf_side {u v : Path} {s : Step} (h : s ∈ stepsOf u v) : s.1 < 3 := by
  simp only [stepsOf, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl <;> simp

/-- Only the last step of a pair is the end. -/
theorem stepsOf_end {u v : Path} {i : Nat} {s : Step} (h : (stepsOf u v)[i]? = some s) :
    s.1 = 2 ↔ i + 1 = (stepsOf u v).length := by
  generalize hA : (u.map fun e => ((0, e) : Step)) ++ (v.map fun e => ((1, e) : Step)) = A
  have hA' : ∀ s ∈ A, s.1 ≠ 2 := fun s hs => by
    rw [← hA] at hs
    simp only [List.mem_append, List.mem_map] at hs
    rcases hs with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp
  have hs : stepsOf u v = A ++ [(2, 0, 0)] := by rw [← hA]; rfl
  rw [hs] at h ⊢
  rw [List.length_append, List.length_singleton]
  by_cases hi : i < A.length
  · rw [List.getElem?_append_left hi] at h
    have := hA' s (List.mem_of_getElem? h)
    constructor
    · exact fun h' => absurd h' this
    · intro h'; omega
  · rw [List.getElem?_append_right (by omega)] at h
    have hlt := (List.getElem?_eq_some_iff.1 h).1
    simp only [List.length_singleton] at hlt
    have h0 : i - A.length = 0 := by omega
    rw [h0] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [true_iff]
    omega

/-- Two lists that differ differ at a first place. -/
theorem first_diff {α : Type} : ∀ (l₁ l₂ : List α), l₁ ≠ l₂ →
    ∃ e, l₁.take e = l₂.take e ∧ l₁[e]? ≠ l₂[e]?
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => ⟨0, rfl, by simp⟩
  | _ :: _, [], _ => ⟨0, rfl, by simp⟩
  | a :: l₁, b :: l₂, h => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨e, h1, h2⟩ := first_diff l₁ l₂ fun h' => h (by rw [h'])
      exact ⟨e + 1, by simp [h1], by simpa using h2⟩
    · exact ⟨0, rfl, by simpa using hab⟩

/-- Lists that agree on their first `e` entries agree on fewer and at each
place before `e`. -/
theorem take_of_take {α : Type} {l₁ l₂ : List α} {e i : Nat} (h : l₁.take e = l₂.take e)
    (hi : i ≤ e) : l₁.take i = l₂.take i := by
  have := congrArg (List.take i) h
  rwa [List.take_take, List.take_take, Nat.min_eq_left hi] at this

theorem getElem?_of_take {α : Type} {l₁ l₂ : List α} {e i : Nat} (h : l₁.take e = l₂.take e)
    (hi : i < e) : l₁[i]? = l₂[i]? := by
  have := congrArg (fun l => l[i]?) h
  simpa [List.getElem?_take, hi] using this

/-- The steps of two pairs that are not the same differ at a place both
have. -/
theorem stepsOf_diff {u v u' v' : Path} (h : stepsOf u v ≠ stepsOf u' v') :
    ∃ e s s', (stepsOf u v).take e = (stepsOf u' v').take e ∧ (stepsOf u v)[e]? = some s ∧
      (stepsOf u' v')[e]? = some s' ∧ s ≠ s' := by
  obtain ⟨e, h1, h2⟩ := first_diff _ _ h
  have key : ∀ {u v u' v' : Path} {e : Nat}, (stepsOf u v).take e = (stepsOf u' v').take e →
      (stepsOf u v)[e]? ≠ (stepsOf u' v')[e]? → (stepsOf u v)[e]? ≠ none := by
    intro u v u' v' e h1 h2 hn
    have hle : (stepsOf u v).length ≤ e := List.getElem?_eq_none_iff.1 hn
    have hpos : 0 < (stepsOf u v).length := by simp [stepsOf]
    have hlast : (stepsOf u v)[(stepsOf u v).length - 1]? =
        some (stepsOf u v)[(stepsOf u v).length - 1] := List.getElem?_eq_getElem (by omega)
    have hsame := getElem?_of_take h1 (show (stepsOf u v).length - 1 < e by omega)
    rw [hlast] at hsame
    have e1 := (stepsOf_end hlast).2 (by omega)
    have e2 := (stepsOf_end hsame.symm).1 e1
    have hlen : (stepsOf u' v').length ≤ e := by omega
    exact h2 (by rw [hn, List.getElem?_eq_none_iff.2 hlen])
  have k1 := key h1 h2
  have k2 := key h1.symm (Ne.symm h2)
  cases e1 : (stepsOf u v)[e]? with
  | none => exact absurd e1 k1
  | some s =>
    cases e2 : (stepsOf u' v')[e]? with
    | none => exact absurd e2 k2
    | some s' =>
      refine ⟨e, s, s', h1, e1, e2, fun hs => h2 ?_⟩
      rw [e1, e2, hs]

theorem bump_sum (k ss : List Step) (t : Nat) : ∀ l : List (List Step × Nat),
    (((bump ss t l).filter fun e => k.isPrefixOf e.1).map (·.2)).sum =
      ((l.filter fun e => k.isPrefixOf e.1).map (·.2)).sum + if k.isPrefixOf ss then t else 0
  | [] => by by_cases h : k.isPrefixOf ss = true <;> simp [bump, h]
  | e :: l => by
    by_cases he : e.1 = ss
    · subst he
      by_cases h : k.isPrefixOf e.1 = true <;> simp [bump, h]
      omega
    · have ih := bump_sum k ss t l
      by_cases h : k.isPrefixOf e.1 = true <;> simp [bump, he, h, ih]
      omega

/-- What a class was fed once a pair is marked: the ticks of the pair more if
the pair is of the class. -/
theorem Cursor.fedOf_mark (c : Cursor) (x : Nat × Nat) (t : Nat) (k : List Step) :
    (c.mark x t).fedOf k = c.fedOf k + if k.isPrefixOf (c.stepsAt x) then t else 0 :=
  bump_sum k (c.stepsAt x) t c.fed

@[simp] theorem Cursor.stepsAt_mark (c : Cursor) (x : Nat × Nat) (t : Nat) (y : Nat × Nat) :
    (c.mark x t).stepsAt y = c.stepsAt y := rfl

/-- The steps every class of at most the place `V` has. -/
def sibs (V : Nat) : List Step :=
  (List.range 3).flatMap fun a => (List.range (V + 1)).flatMap fun i =>
    (List.range (V + 1)).map fun m => (a, i, m)

theorem mem_sibs {V : Nat} {s : Step} : s ∈ sibs V ↔ s.1 < 3 ∧ s.2.1 ≤ V ∧ s.2.2 ≤ V := by
  obtain ⟨a, i, m⟩ := s
  simp only [sibs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha, i', hi, m', hm, rfl, rfl, rfl⟩
    exact ⟨ha, by omega, by omega⟩
  · rintro ⟨ha, hi, hm⟩
    exact ⟨a, ha, i, by omega, m, by omega, rfl, rfl, rfl⟩

/-- How far the siblings of the class of the steps `ss` at the depth `e` are
from places after its place: over the siblings that could come before it, by
how much each is short of the place after. -/
def Cursor.level (c : Cursor) (ss : List Step) (e : Nat) : Nat :=
  let V := c.place (ss.take (e + 1)) (ss.getD e (2, 0, 0))
  ((sibs V).map fun s => V + 1 - c.place (ss.take e ++ [s]) s).sum

/-- How far a cursor is from the pair at the positions `p` and `q`: the pairs
of answers no later than its own that are not combined, and then the level
of each of its classes, the narrowest first. -/
def Cursor.rank (c : Cursor) (p q : Nat) : List Nat :=
  (c.left (max p q + 1) (max p q + 1)).length ::
    (List.range (c.stepsAt (p, q)).length).reverse.map (c.level (c.stepsAt (p, q)))

/-- The order of the measures: of two of one length, by the first entry in
which they differ. -/
def RankLt : List Nat → List Nat → Prop := List.Shortlex (· < ·)

theorem rankLt_wf : WellFounded RankLt := List.Shortlex.wf Nat.lt_wfRel.wf

theorem RankLt.trans {a b c : List Nat} (h₁ : RankLt a b) (h₂ : RankLt b c) : RankLt a c := by
  rcases List.shortlex_def.1 h₁ with h₁ | ⟨e₁, l₁⟩
  · rcases List.shortlex_def.1 h₂ with h₂ | ⟨e₂, -⟩
    · exact List.Shortlex.of_length_lt (by omega)
    · exact List.Shortlex.of_length_lt (by omega)
  · rcases List.shortlex_def.1 h₂ with h₂ | ⟨e₂, l₂⟩
    · exact List.Shortlex.of_length_lt (by omega)
    · exact List.Shortlex.of_lex (e₁.trans e₂)
        (List.lex_trans (fun h h' => Nat.lt_trans h h') l₁ l₂)

/-- The measure of a pair of answers that were filed stays when more are
filed. -/
theorem Cursor.rank_see (pa pb : List Path) (c : Cursor) {p q : Nat} (h1 : p < c.pa.length)
    (h2 : q < c.pb.length) : (c.see pa pb).rank p q = c.rank p q := by
  unfold Cursor.rank
  rw [Cursor.stepsAt_see pa pb c (x := (p, q)) h1 h2]
  rfl

/-- Two lists of measures over the depths below `n`, the deepest first: one
that agrees with the other beyond the depth `e` and is less at `e` comes
before it. -/
theorem lex_range (f g : Nat → Nat) (e : Nat) : ∀ n, e < n →
    (∀ j, e < j → j < n → f j = g j) → f e < g e →
    List.Lex (· < ·) ((List.range n).reverse.map f) ((List.range n).reverse.map g)
  | 0, he, _, _ => absurd he (by omega)
  | n + 1, he, hgt, hlt => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, List.map_cons]
    by_cases hn : e = n
    · subst hn
      exact .rel hlt
    · rw [hgt n (by omega) (by omega)]
      exact .cons (lex_range f g e n (by omega) (fun j h1 h2 => hgt j h1 (by omega)) hlt)

/-- In two lists ordered one before the other that agree up to a place, the
entries at the place are in that order. -/
theorem le_at_diff {β : Type} [LinearOrder β] : ∀ (e : Nat) (l₁ l₂ : List β) (a b : β),
    l₁ ≤ l₂ → l₁.take e = l₂.take e → l₁[e]? = some a → l₂[e]? = some b → a ≤ b
  | 0, a' :: l₁, b' :: l₂, a, b, hle, _, ha, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
    subst ha; subst hb
    by_contra hc
    exact absurd hle (not_le.2 (List.cons_lt_cons_iff.2 (.inl (not_le.1 hc))))
  | 0, [], _, _, _, _, _, ha, _ => by simp at ha
  | 0, _ :: _, [], _, _, _, _, _, hb => by simp at hb
  | e + 1, [], _, _, _, _, _, ha, _ => by simp at ha
  | e + 1, _ :: _, [], _, _, _, _, _, hb => by simp at hb
  | e + 1, a' :: l₁, b' :: l₂, a, b, hle, ht, ha, hb => by
    simp only [List.take_succ_cons, List.cons.injEq] at ht
    obtain ⟨rfl, ht⟩ := ht
    refine le_at_diff e l₁ l₂ a b ?_ ht (by simpa using ha) (by simpa using hb)
    by_contra hc
    exact absurd hle (not_le.2 (List.cons_lt_cons_iff.2 (.inr ⟨rfl, not_le.1 hc⟩)))

theorem head_le_of_cons_le {a b : Nat} {l l' : List Nat} (h : a :: l ≤ b :: l') : a ≤ b := by
  by_contra hc
  exact absurd h (not_le.2 (List.cons_lt_cons_iff.2 (.inl (not_le.1 hc))))

/-- Marking a pair leaves no more pairs to combine below a bound, and fewer
when the pair marked was one of them. -/
theorem Cursor.left_mark (c : Cursor) (x : Nat × Nat) (t K : Nat) :
    ((c.mark x t).left K K).length ≤ (c.left K K).length ∧
      (x ∈ c.left K K → ((c.mark x t).left K K).length < (c.left K K).length) := by
  have hsub : List.Sublist ((c.mark x t).left K K) (c.left K K) := by
    unfold Cursor.left Cursor.mark
    refine List.monotone_filter_right _ fun y hy => ?_
    simp only [List.contains_cons, Bool.not_or, Bool.and_eq_true] at hy
    exact hy.2
  refine ⟨hsub.length_le, fun hx => ?_⟩
  rcases Nat.lt_or_eq_of_le hsub.length_le with h | h
  · exact h
  · have := hsub.eq_of_length h
    rw [← this] at hx
    have hb := (Cursor.mem_left.1 hx).2
    exact absurd (Cursor.before_mark.2 (.inr rfl)) hb

/-- The place of a class once a pair is marked. -/
theorem Cursor.place_mark (c : Cursor) (x : Nat × Nat) (t : Nat) (k : List Step) (s : Step) :
    (c.mark x t).place k s =
      c.place k s + (if k.isPrefixOf (c.stepsAt x) then t else 0) * (s.2.2 + 1) := by
  unfold Cursor.place
  rw [Cursor.fedOf_mark]
  generalize (if k.isPrefixOf (c.stepsAt x) then t else 0) = d
  rw [show c.fedOf k + d + 1 = (c.fedOf k + 1) + d by omega, Nat.add_mul]
  omega

/-- **A unit that combines a pair brings its cursor nearer to each pair still
to combine.** -/
theorem Cursor.rank_fall_todo {c : Cursor} {x : Nat × Nat} (hx : ¬ c.Before x.1 x.2)
    {t : Nat} (ht : 0 < t) (h : c.next = some x) {p q : Nat} (hpq : (p, q) ∈ c.todo) :
    RankLt ((c.mark x t).rank p q) (c.rank p q) := by
  have hkey := Cursor.next_least h (p, q) hpq
  have hxm : True ∧ ¬ c.Before x.1 x.2 := ⟨trivial, hx⟩
  obtain ⟨hL, hL'⟩ := c.left_mark x t (max p q + 1)
  unfold Cursor.rank
  simp only [Cursor.stepsAt_mark]
  refine List.Shortlex.of_lex (by simp) ?_
  generalize hss : c.stepsAt (p, q) = ss at hkey ⊢
  generalize hsx : c.stepsAt x = sx at hkey
  have kx : c.keyOf x = (List.range sx.length).map (c.group sx) ++ [[max x.1 x.2, x.1, x.2]] := by
    rw [← hsx]; rfl
  have ko : c.keyOf (p, q) = (List.range ss.length).map (c.group ss) ++ [[max p q, p, q]] := by
    rw [← hss]; rfl
  rw [kx, ko] at hkey
  by_cases hs : sx = ss
  · -- the same class to the end: an earlier pair
    subst hs
    have hle := le_at_diff sx.length _ _ [max x.1 x.2, x.1, x.2] [max p q, p, q] hkey
      (by simp) (by simp) (by simp)
    have hm := head_le_of_cons_le hle
    refine .rel (hL' (Cursor.mem_left.2 ⟨?_, hxm.2⟩))
    constructor <;> omega
  · -- another class from the depth `e` on
    have hs' : stepsOf (c.pa.getD x.1 []) (c.pb.getD x.2 []) ≠
        stepsOf (c.pa.getD p []) (c.pb.getD q []) := by
      intro h'
      apply hs
      rw [← hsx, ← hss]
      exact h'
    obtain ⟨e, s, s', htake, hs1, hs2, hsne⟩ := stepsOf_diff hs'
    have hsx' : stepsOf (c.pa.getD x.1 []) (c.pb.getD x.2 []) = sx := hsx
    have hss' : stepsOf (c.pa.getD p []) (c.pb.getD q []) = ss := hss
    rw [hsx'] at htake hs1
    rw [hss'] at htake hs2
    have hside : s.1 < 3 := stepsOf_side (u := c.pa.getD x.1 []) (v := c.pb.getD x.2 [])
      (by rw [hsx']; exact List.mem_of_getElem? hs1)
    have he1 : e < sx.length := (List.getElem?_eq_some_iff.1 hs1).1
    have he2 : e < ss.length := (List.getElem?_eq_some_iff.1 hs2).1
    -- the keys agree up to `e`, and are in order there
    have hgrp : ∀ i, i < e → c.group sx i = c.group ss i := fun i hi => by
      unfold Cursor.group
      rw [take_of_take htake (show i + 1 ≤ e by omega), List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, getElem?_of_take htake hi]
    have hle := le_at_diff e _ _ (c.group sx e) (c.group ss e) hkey (by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < e
        · simp only [List.getElem?_take, hi, ↓reduceIte]
          rw [List.getElem?_append_left (by simp; omega),
            List.getElem?_append_left (by simp; omega)]
          simp only [List.getElem?_map, List.getElem?_range (show i < sx.length by omega),
            List.getElem?_range (show i < ss.length by omega), Option.map_some, hgrp i hi]
        · simp [hi])
      (by rw [List.getElem?_append_left (by simp; omega)]; simp [he1])
      (by rw [List.getElem?_append_left (by simp; omega)]; simp [he2])
    have hV : c.place (sx.take (e + 1)) s ≤ c.place (ss.take (e + 1)) s' := by
      have := head_le_of_cons_le hle
      simpa [List.getD_eq_getElem?_getD, hs1, hs2] using this
    -- a class that has the step `s'` at `e` is not one of `x`
    have np : ∀ k : List Step, k[e]? = some s' → k.isPrefixOf sx = false := fun k hk => by
      cases hp : k.isPrefixOf sx with
      | false => rfl
      | true =>
        have hpre := List.isPrefixOf_iff_prefix.1 hp
        have hek : e < k.length := (List.getElem?_eq_some_iff.1 hk).1
        rw [List.prefix_iff_eq_take.1 hpre, List.getElem?_take_of_lt hek, hs1] at hk
        exact absurd (Option.some.inj hk) hsne
    have hp : ∀ (k : List Step) (s0 : Step), k[e]? = some s' →
        (c.mark x t).place k s0 = c.place k s0 := fun k s0 hk => by
      rw [Cursor.place_mark, hsx, np k hk]
      simp
    have hmono : ∀ (k : List Step) (s0 : Step), c.place k s0 ≤ (c.mark x t).place k s0 :=
      fun k s0 => by rw [Cursor.place_mark]; omega
    have hown : (ss.take (e + 1))[e]? = some s' := by
      rw [List.getElem?_take_of_lt (by omega), hs2]
    have hgt : ∀ j, e < j → j < ss.length → (c.mark x t).level ss j = c.level ss j :=
      fun j hj hjn => by
        unfold Cursor.level
        have h1 : (ss.take (j + 1))[e]? = some s' := by
          rw [List.getElem?_take_of_lt (by omega), hs2]
        simp only [hp _ _ h1]
        congr 1
        refine List.map_congr_left fun s0 _ => ?_
        rw [hp (ss.take j ++ [s0]) s0 (by
          rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj, hs2])]
    have hlt : (c.mark x t).level ss e < c.level ss e := by
      unfold Cursor.level
      simp only [hp _ _ hown]
      have hd : ss.getD e (2, 0, 0) = s' := by rw [List.getD_eq_getElem?_getD, hs2]; rfl
      rw [hd]
      refine List.sum_lt_sum _ _ (fun s0 _ => ?_) ⟨s, ?_, ?_⟩
      · have := hmono (ss.take e ++ [s0]) s0
        omega
      · have h1 : s.2.1 ≤ c.place (sx.take (e + 1)) s := by unfold Cursor.place; omega
        have h2 : s.2.2 + 1 ≤ c.place (sx.take (e + 1)) s := by
          unfold Cursor.place
          have := Nat.le_mul_of_pos_left (s.2.2 + 1) (show 0 < c.fedOf (sx.take (e + 1)) + 1 by omega)
          omega
        exact mem_sibs.2 ⟨hside, by omega, by omega⟩
      · have hcls : ss.take e ++ [s] = sx.take (e + 1) := by
          rw [List.take_add_one, hs1, htake]
          rfl
        rw [hcls, Cursor.place_mark, hsx,
          List.isPrefixOf_iff_prefix.2 (List.take_prefix (e + 1) sx)]
        have : 0 < t * (s.2.2 + 1) := Nat.mul_pos ht (Nat.succ_pos _)
        simp only [↓reduceIte]
        omega
    rcases Nat.lt_or_eq_of_le hL with hlt' | heq
    · exact .rel hlt'
    · rw [heq]
      exact .cons (lex_range _ _ e ss.length he2 hgt hlt)

/-- **A unit of a join that combines a pair brings the join nearer to each
pair left.** -/
theorem Cursor.rank_fall {la lb : Nat} {c : Cursor} (hok : c.Ok la lb) {x : Nat × Nat}
    {t : Nat} (ht : 0 < t) (h : c.next = some x) {p q : Nat}
    (hpq : (p, q) ∈ c.left c.pa.length c.pb.length) :
    RankLt ((c.mark x t).rank p q) (c.rank p q) :=
  Cursor.rank_fall_todo (Cursor.mem_left.1 (Cursor.next_mem hok h)).2 ht h (hok.mem_todo.2 hpq)

/-! ## The cursor of a push -/

/-- The steps down to a pair of answers that were filed stay when an answer
is pushed. -/
theorem Cursor.stepsAt_opened (pth : Path) (c : Cursor) {x : Nat × Nat}
    (h1 : x.1 < c.pa.length) : (c.opened pth).stepsAt x = c.stepsAt x := by
  simp only [Cursor.stepsAt, Cursor.opened, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h1]

/-- The steps down to a pair of answers that were filed stay when an answer
is filed. -/
theorem Cursor.stepsAt_read (s : Nat) (pth : Path) (c : Cursor) {x : Nat × Nat}
    (h2 : x.2 < c.pb.length) : (c.read s pth).stepsAt x = c.stepsAt x := by
  simp only [Cursor.stepsAt, Cursor.read, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h2]

/-- The measure of a pair stays when an answer is pushed. -/
theorem Cursor.rank_opened (pth : Path) (c : Cursor) {p q : Nat} (h1 : p < c.pa.length) :
    (c.opened pth).rank p q = c.rank p q := by
  unfold Cursor.rank
  rw [Cursor.stepsAt_opened pth c (x := (p, q)) h1]
  rfl

/-- The measure of a pair of answers that were filed stays when an answer is
filed. -/
theorem Cursor.rank_read (s : Nat) (pth : Path) (c : Cursor) {p q : Nat}
    (h2 : q < c.pb.length) : (c.read s pth).rank p q = c.rank p q := by
  unfold Cursor.rank
  rw [Cursor.stepsAt_read s pth c (x := (p, q)) h2]
  rfl

/-- Taking units off a cursor leaves the measure of every unit: the measure
is of what was combined and what it cost. -/
@[simp] theorem Cursor.rank_kill (dead : List Nat) (c : Cursor) (p q : Nat) :
    (c.kill dead).rank p q = c.rank p q := rfl

@[simp] theorem Cursor.before_kill (dead : List Nat) (c : Cursor) (p q : Nat) :
    (c.kill dead).Before p q ↔ c.Before p q := Iff.rfl

theorem Cursor.mem_kill {dead : List Nat} {c : Cursor} {x : Nat × Nat} :
    x ∈ (c.kill dead).todo ↔ x ∈ c.todo ∧ x.1 ∉ dead := by
  simp [Cursor.kill]

/-! ## The feed cursor of a push -/

/-- What the feed cursor of a push keeps: a unit still to take is of an
answer seen and was filed, and is not taken; a unit taken was filed. -/
def Cursor.Fits (c : Cursor) : Prop :=
  (∀ x ∈ c.todo, x.1 < c.pa.length ∧ x.2 < c.pb.length ∧ ¬ c.Before x.1 x.2) ∧
    ∀ x ∈ c.done, x.2 < c.pb.length

theorem Cursor.fits_start : Cursor.start.Fits :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem Cursor.Fits.opened {c : Cursor} (h : c.Fits) (pth : Path) : (c.opened pth).Fits := by
  refine ⟨fun x hx => ?_, h.2⟩
  obtain ⟨h1, h2, h3⟩ := h.1 x hx
  refine ⟨?_, h2, h3⟩
  simp only [Cursor.opened, List.length_append, List.length_cons, List.length_nil]
  omega

theorem Cursor.Fits.pad {c : Cursor} (h : c.Fits) (pths : List Path) : (c.pad pths).Fits := by
  refine ⟨fun x hx => ?_, h.2⟩
  obtain ⟨h1, h2, h3⟩ := h.1 x hx
  refine ⟨?_, h2, h3⟩
  simp only [Cursor.pad, List.length_append]
  omega

/-- The measure of a unit of an answer seen stays when more answers are
seen. -/
theorem Cursor.rank_pad (pths : List Path) (c : Cursor) {p q : Nat} (h1 : p < c.pa.length) :
    (c.pad pths).rank p q = c.rank p q := by
  have e : (c.pad pths).stepsAt (p, q) = c.stepsAt (p, q) := by
    simp only [Cursor.stepsAt, Cursor.pad, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1]
  unfold Cursor.rank
  rw [e]
  rfl

theorem Cursor.Fits.kill {c : Cursor} (h : c.Fits) (dead : List Nat) : (c.kill dead).Fits :=
  ⟨fun x hx => h.1 x (Cursor.mem_kill.1 hx).1, h.2⟩

theorem Cursor.Fits.read {c : Cursor} (h : c.Fits) {s : Nat} (hs : s < c.pa.length) (pth : Path) :
    (c.read s pth).Fits := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Cursor.read, List.mem_append, List.mem_singleton] at hx
    simp only [Cursor.read, List.length_append, List.length_cons, List.length_nil]
    rcases hx with hx | rfl
    · obtain ⟨h1, h2, h3⟩ := h.1 x hx
      exact ⟨h1, by omega, h3⟩
    · refine ⟨hs, by simp, fun hb => ?_⟩
      exact absurd (h.2 _ hb) (Nat.lt_irrefl _)
  · have := h.2 x hx
    simp only [Cursor.read, List.length_append, List.length_cons, List.length_nil]
    omega

theorem Cursor.Fits.mark {c : Cursor} (h : c.Fits) {x : Nat × Nat} (hx : x ∈ c.todo) (t : Nat) :
    (c.mark x t).Fits := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · simp only [Cursor.mark, List.mem_filter, bne_iff_ne, ne_eq] at hy
    obtain ⟨h1, h2, h3⟩ := h.1 y hy.1
    refine ⟨h1, h2, fun hb => ?_⟩
    rcases Cursor.before_mark.1 hb with hb | hb
    · exact h3 hb
    · exact hy.2 hb.symm
  · simp only [Cursor.mark, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact (h.1 _ hx).2.1
    · exact h.2 y hy

/-- Taking a unit that cost nothing leaves every other unit no further from
its turn. -/
theorem Cursor.rank_mark_zero (c : Cursor) (x : Nat × Nat) (p q : Nat) :
    (c.mark x 0).rank p q = c.rank p q ∨ RankLt ((c.mark x 0).rank p q) (c.rank p q) := by
  obtain ⟨hL, -⟩ := c.left_mark x 0 (max p q + 1)
  have hlev : ∀ ss e, (c.mark x 0).level ss e = c.level ss e := fun ss e => by
    unfold Cursor.level
    simp only [Cursor.place_mark, ite_self, Nat.zero_mul, Nat.add_zero]
  unfold Cursor.rank
  simp only [Cursor.stepsAt_mark]
  rw [show (c.mark x 0).level (c.stepsAt (p, q)) = c.level (c.stepsAt (p, q)) from
    funext (hlev _)]
  rcases Nat.lt_or_eq_of_le hL with h | h
  · exact .inr (List.Shortlex.of_lex (by simp) (List.Lex.rel h))
  · exact .inl (by rw [h])

end Symmetric

end RwLog
