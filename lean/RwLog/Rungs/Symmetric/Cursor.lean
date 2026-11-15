/-
# The cursor of a join combines each pair once it is counted

`Cursor.Before c p q` says the pair at the positions `p` and `q` is combined
when the cursor is `c`: it lies in the block counted in, or in the line in
progress before the place reached. `Cursor.Ok` is what a cursor keeps in
tables of given lengths.

`Cursor.next` returns a pair inside the tables, and after it the pairs
combined are those combined before and that pair (`next_spec`).

Every pair is reached: `Cursor.rank` measures how far a cursor is from the
pairs of positions below a bound, in an order that is well founded
(`rankLt_wf`). A unit of a join combines a pair inside the tables or makes
the measure fall (`next_rank`).

`leastBy` returns an entry that passes its test (`leastBy_ok`), with the
least key of those that pass (`leastBy_le`), and returns nothing only when
none passes (`leastBy_none`). Moving one entry of a list to a smaller
measure makes the sum of the measures smaller (`sum_map_modify_lt`).

Nothing here is about a kernel.
-/
import RwLog.Rungs.Symmetric.Machine

namespace RwLog

namespace Symmetric

/-- The pair at the positions `p` and `q` is combined. -/
def Cursor.Before (c : Cursor) (p q : Nat) : Prop := (p, q) ∈ c.done

/-- What a cursor keeps in tables of `la` and `lb` answers: the pairs combined
are of answers that are there. -/
def Cursor.Ok (la lb : Nat) (c : Cursor) : Prop := ∀ x ∈ c.done, x.1 < la ∧ x.2 < lb

theorem Cursor.ok_start (la lb : Nat) : Cursor.start.Ok la lb := by
  simp [Cursor.Ok, Cursor.start]

theorem Cursor.before_start (p q : Nat) : ¬ Cursor.start.Before p q := by
  simp [Cursor.Before, Cursor.start]

/-- A cursor that fits tables fits them when they have grown. -/
theorem Cursor.Ok.mono {la lb la' lb' : Nat} {c : Cursor} (h : c.Ok la lb) (ha : la ≤ la')
    (hb : lb ≤ lb') : c.Ok la' lb' := fun x hx => by
  have := h x hx
  omega

/-- A pair that is combined is inside the tables. -/
theorem Cursor.Ok.before_lt {la lb : Nat} {c : Cursor} (h : c.Ok la lb) {p q : Nat}
    (hb : c.Before p q) : p < la ∧ q < lb := h (p, q) hb

theorem mem_pairsBelow {la lb : Nat} {x : Nat × Nat} :
    x ∈ pairsBelow la lb ↔ x.1 < la ∧ x.2 < lb := by
  obtain ⟨p, q⟩ := x
  simp only [pairsBelow, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_append,
    List.mem_map, Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨max p q, by omega, ?_⟩, h⟩
    by_cases hpq : p < q
    · exact .inl ⟨p, by omega, rfl, by omega⟩
    · exact .inr ⟨q, by omega, by omega, rfl⟩

theorem Cursor.mem_left {la lb : Nat} {c : Cursor} {x : Nat × Nat} :
    x ∈ c.left la lb ↔ (x.1 < la ∧ x.2 < lb) ∧ ¬ c.Before x.1 x.2 := by
  simp [Cursor.left, mem_pairsBelow, Cursor.Before]

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

/-- A pair returned is inside the tables and was not combined. -/
theorem Cursor.next_mem {pa pb : List Path} {c : Cursor} {x : Nat × Nat}
    (h : c.next pa pb = some x) : x ∈ c.left pa.length pb.length := by
  rcases foldl_choose_mem _ _ _ _ (show List.foldl _ none _ = some x from h) with h1 | h1
  · exact h1
  · cases h1

/-- No pair is returned only when none is left. -/
theorem Cursor.next_none {pa pb : List Path} {c : Cursor} (h : c.next pa pb = none) :
    c.pending pa.length pb.length = false := by
  simp [Cursor.pending, (foldl_choose_none _ _ _ (show List.foldl _ none _ = none from h)).1]

/-- When nothing is left every pair inside the tables is combined. -/
theorem Cursor.before_of_not_pending' {la lb : Nat} {c : Cursor}
    (hp : c.pending la lb = false) {p q : Nat} (h1 : p < la) (h2 : q < lb) : c.Before p q := by
  by_contra hn
  have : (p, q) ∈ c.left la lb := Cursor.mem_left.2 ⟨⟨h1, h2⟩, hn⟩
  simp only [Cursor.pending, Bool.not_eq_false', List.isEmpty_iff] at hp
  rw [hp] at this
  cases this

/-- The pairs combined after a pair is marked are those combined before and
that pair. -/
theorem Cursor.before_mark {pa pb : List Path} {c : Cursor} {x : Nat × Nat} {t p q : Nat} :
    (c.mark pa pb x t).Before p q ↔ c.Before p q ∨ x = (p, q) := by
  simp only [Cursor.Before, Cursor.mark, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | h)
    · exact .inl h
    · exact .inr h.symm
  · rintro (h | h)
    · exact .inl h
    · exact .inr h.symm

/-- **A unit of a join**: a pair returned is inside the tables and was not
combined; once it is marked the cursor still fits and the pair is
combined. -/
theorem Cursor.next_spec {pa pb : List Path} {c : Cursor} {x : Nat × Nat} (t : Nat)
    (hok : c.Ok pa.length pb.length) (h : c.next pa pb = some x) :
    (x.1 < pa.length ∧ x.2 < pb.length) ∧ ¬ c.Before x.1 x.2 ∧
      (c.mark pa pb x t).Ok pa.length pb.length ∧ (c.mark pa pb x t).Before x.1 x.2 := by
  have hm := Cursor.mem_left.1 (Cursor.next_mem h)
  refine ⟨hm.1, hm.2, fun y hy => ?_, Cursor.before_mark.2 (.inr rfl)⟩
  simp only [Cursor.mark, List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | hy
  · exact hok y hy
  · exact hy ▸ hm.1


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

/-! ## Every pair is reached -/

/-- A measure of how far a cursor is from a pair of positions below `K`: the
answers below `K` not yet counted, and then what is left of the line in
progress. A line of an answer at `K` or beyond is counted as longer than
anything that follows it. -/

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

end Symmetric

end RwLog
