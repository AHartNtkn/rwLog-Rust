/-
# The cursor of a join combines each pair once it is counted

`Cursor.Before c p q` says the pair at the positions `p` and `q` is combined
when the cursor is `c`: it lies in the block counted in, or in the line in
progress before the place reached. `Cursor.Ok` is what a cursor keeps in
tables of given lengths.

`Cursor.next` returns a pair inside the tables, and after it the pairs
combined are those combined before and that pair (`next_spec`).
`Cursor.all` returns pairs inside the tables, and after it the pairs
combined are those combined before and those returned (`all_spec`).

Every pair is reached: `Cursor.rank` measures how far a cursor is from the
pairs of positions below a bound, in an order that is well founded
(`rankLt_wf`). A unit of a join combines a pair inside the tables or makes
the measure fall (`next_rank`), and so does its whole work (`all_rank`).

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
def Cursor.Before (c : Cursor) (p q : Nat) : Prop :=
  (p < c.na ∧ q < c.nb) ∨
    (c.col = true ∧ q = c.nb ∧ p < c.inner) ∨ (c.col = false ∧ p = c.na ∧ q < c.inner)

/-- What a cursor keeps in tables of `la` and `lb` answers: the answers
counted are there, and the line in progress is of an answer that is there
and goes no further than the answers counted on the other side. -/
def Cursor.Ok (la lb : Nat) (c : Cursor) : Prop :=
  c.na ≤ la ∧ c.nb ≤ lb ∧
    (c.col = true → c.inner ≤ c.na ∧ (0 < c.inner → c.nb < lb)) ∧
    (c.col = false → c.inner ≤ c.nb ∧ (0 < c.inner → c.na < la))

theorem Cursor.ok_start (la lb : Nat) : Cursor.start.Ok la lb := by
  simp [Cursor.Ok, Cursor.start]

theorem Cursor.before_start (p q : Nat) : ¬ Cursor.start.Before p q := by
  simp [Cursor.Before, Cursor.start]

/-- A cursor that fits tables fits them when they have grown. -/
theorem Cursor.Ok.mono {la lb la' lb' : Nat} {c : Cursor} (h : c.Ok la lb) (ha : la ≤ la')
    (hb : lb ≤ lb') : c.Ok la' lb' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨h5, h6⟩ := h3 hc
    exact ⟨h5, fun hi => by have := h6 hi; omega⟩
  · obtain ⟨h5, h6⟩ := h4 hc
    exact ⟨h5, fun hi => by have := h6 hi; omega⟩

/-- A pair that is combined is inside the tables. -/
theorem Cursor.Ok.before_lt {la lb : Nat} {c : Cursor} (h : c.Ok la lb) {p q : Nat}
    (hb : c.Before p q) : p < la ∧ q < lb := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases hb with ⟨hp, hq⟩ | ⟨hc, hq, hp⟩ | ⟨hc, hp, hq⟩
  · omega
  · have := h3 hc
    have := this.2 (by omega)
    omega
  · have := h4 hc
    have := this.2 (by omega)
    omega

/-- What `Cursor.next` returns: the cursor still fits; a pair returned is
inside the tables; and the pairs combined after it are those combined before
it and the pair returned. -/
theorem Cursor.next_spec (la lb : Nat) : ∀ (f : Nat) (c : Cursor), c.Ok la lb →
    (Cursor.next la lb f c).2.Ok la lb ∧
    (∀ p q, c.Before p q → (Cursor.next la lb f c).2.Before p q) ∧
    (∀ pr, (Cursor.next la lb f c).1 = some pr → pr.1 < la ∧ pr.2 < lb) ∧
    ∀ p q, (Cursor.next la lb f c).2.Before p q →
      c.Before p q ∨ (Cursor.next la lb f c).1 = some (p, q)
  | 0, c, h => ⟨h, fun _ _ h => h, (fun _ h => by cases h), fun _ _ h => .inl h⟩
  | f + 1, c, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have e : ∃ col : Bool, (c.inner ≠ 0 → c.col = col) ∧ Cursor.next la lb (f + 1) c =
        if col then
          if c.nb < lb then
            if c.inner < c.na then
              (some (c.inner, c.nb), { c with inner := c.inner + 1, col := true })
            else Cursor.next la lb f ⟨c.na, c.nb + 1, 0, false⟩
          else (none, c)
        else
          if c.na < la then
            if c.inner < c.nb then
              (some (c.na, c.inner), { c with inner := c.inner + 1, col := false })
            else Cursor.next la lb f ⟨c.na + 1, c.nb, 0, false⟩
          else (none, c) :=
      ⟨_, fun hi => by simp [hi], rfl⟩
    obtain ⟨col, hcol', e⟩ := e
    rw [e]
    cases col with
    | true =>
      simp only [ite_true]
      split
      · next hnb =>
        split
        · next hin =>
          refine ⟨⟨h1, h2, fun _ => ⟨by simp only; omega, fun _ => hnb⟩, fun hc => by cases hc⟩,
            fun p q hb => ?_, fun pr hpr => ?_, fun p q hb => ?_⟩
          · rcases hb with hb | ⟨hc, hq, hp⟩ | ⟨hc, hp, hq⟩
            · exact .inl hb
            · exact .inr (.inl ⟨rfl, hq, by simp only; omega⟩)
            · have : c.inner ≠ 0 := by omega
              rw [hcol' this] at hc
              cases hc
          · cases hpr
            exact ⟨by simp only; omega, hnb⟩
          · rcases hb with hb | ⟨-, hq, hp⟩ | ⟨hc, -, -⟩
            · exact .inl (.inl hb)
            · simp only at hq hp
              by_cases e : p = c.inner
              · subst e; subst hq; exact .inr rfl
              · have hi : c.inner ≠ 0 := by omega
                exact .inl (.inr (.inl ⟨hcol' hi, hq, by omega⟩))
            · cases hc
        · next hin =>
          have hle : c.inner ≠ 0 → c.inner = c.na := fun hi => by
            have := (h3 (hcol' hi)).1
            omega
          have hok : (⟨c.na, c.nb + 1, 0, false⟩ : Cursor).Ok la lb :=
            ⟨h1, hnb, (fun hc => by cases hc), fun _ => ⟨Nat.zero_le _, fun h => by cases h⟩⟩
          obtain ⟨i1, i2, i3, i4⟩ := Cursor.next_spec la lb f _ hok
          refine ⟨i1, fun p q hb => i2 p q ?_, i3, fun p q hb => ?_⟩
          · rcases hb with hb | ⟨hc, hq, hp⟩ | ⟨hc, hp, hq⟩
            · exact .inl ⟨hb.1, by simp only; omega⟩
            · have hi : c.inner ≠ 0 := by omega
              exact .inl ⟨by simp only; have := hle hi; omega, by simp only; omega⟩
            · have hi : c.inner ≠ 0 := by omega
              rw [hcol' hi] at hc
              cases hc
          · rcases i4 p q hb with hb | hb
            · rcases hb with ⟨hp, hq⟩ | ⟨hc, -, -⟩ | ⟨-, -, hq⟩
              · simp only at hp hq
                by_cases e : q < c.nb
                · exact .inl (.inl ⟨hp, e⟩)
                · have hi : c.inner ≠ 0 := by omega
                  exact .inl (.inr (.inl ⟨hcol' hi, by omega, by have := hle hi; omega⟩))
              · cases hc
              · simp only at hq
                omega
            · exact .inr hb
      · exact ⟨⟨h1, h2, h3, h4⟩, fun _ _ h => h, (fun _ h => by cases h), fun _ _ h => .inl h⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      split
      · next hna =>
        split
        · next hin =>
          refine ⟨⟨h1, h2, (fun hc => by cases hc), fun _ => ⟨by simp only; omega, fun _ => hna⟩⟩,
            fun p q hb => ?_, fun pr hpr => ?_, fun p q hb => ?_⟩
          · rcases hb with hb | ⟨hc, hq, hp⟩ | ⟨hc, hp, hq⟩
            · exact .inl hb
            · have : c.inner ≠ 0 := by omega
              rw [hcol' this] at hc
              cases hc
            · exact .inr (.inr ⟨rfl, hp, by simp only; omega⟩)
          · cases hpr
            exact ⟨hna, by simp only; omega⟩
          · rcases hb with hb | ⟨hc, -, -⟩ | ⟨-, hp, hq⟩
            · exact .inl (.inl hb)
            · cases hc
            · simp only at hq hp
              by_cases e : q = c.inner
              · subst e; subst hp; exact .inr rfl
              · have hi : c.inner ≠ 0 := by omega
                exact .inl (.inr (.inr ⟨hcol' hi, hp, by omega⟩))
        · next hin =>
          have hle : c.inner ≠ 0 → c.inner = c.nb := fun hi => by
            have := (h4 (hcol' hi)).1
            omega
          have hok : (⟨c.na + 1, c.nb, 0, false⟩ : Cursor).Ok la lb :=
            ⟨hna, h2, (fun hc => by cases hc), fun _ => ⟨Nat.zero_le _, fun h => by cases h⟩⟩
          obtain ⟨i1, i2, i3, i4⟩ := Cursor.next_spec la lb f _ hok
          refine ⟨i1, fun p q hb => i2 p q ?_, i3, fun p q hb => ?_⟩
          · rcases hb with hb | ⟨hc, hq, hp⟩ | ⟨hc, hp, hq⟩
            · exact .inl ⟨by simp only; omega, hb.2⟩
            · have hi : c.inner ≠ 0 := by omega
              rw [hcol' hi] at hc
              cases hc
            · have hi : c.inner ≠ 0 := by omega
              exact .inl ⟨by simp only; omega, by simp only; have := hle hi; omega⟩
          · rcases i4 p q hb with hb | hb
            · rcases hb with ⟨hp, hq⟩ | ⟨hc, -, -⟩ | ⟨-, -, hq⟩
              · simp only at hp hq
                by_cases e : p < c.na
                · exact .inl (.inl ⟨e, hq⟩)
                · have hi : c.inner ≠ 0 := by omega
                  exact .inl (.inr (.inr ⟨hcol' hi, by omega, by have := hle hi; omega⟩))
              · cases hc
              · simp only at hq
                omega
            · exact .inr hb
      · exact ⟨⟨h1, h2, h3, h4⟩, fun _ _ h => h, (fun _ h => by cases h), fun _ _ h => .inl h⟩

/-- What `Cursor.all` returns: the cursor still fits; the pairs returned are
inside the tables; and the pairs combined after it are those combined before
it and the pairs returned. -/
theorem Cursor.all_spec (la lb : Nat) : ∀ (f : Nat) (c : Cursor), c.Ok la lb →
    (Cursor.all la lb f c).2.Ok la lb ∧
    (∀ p q, c.Before p q → (Cursor.all la lb f c).2.Before p q) ∧
    (∀ pr ∈ (Cursor.all la lb f c).1, pr.1 < la ∧ pr.2 < lb) ∧
    ∀ p q, (Cursor.all la lb f c).2.Before p q →
      c.Before p q ∨ (p, q) ∈ (Cursor.all la lb f c).1
  | 0, c, h => ⟨h, fun _ _ h => h, (fun _ h => by cases h), fun _ _ h => .inl h⟩
  | f + 1, c, h => by
    obtain ⟨n1, n2, n3, n4⟩ := Cursor.next_spec la lb (c.room la lb) c h
    unfold Cursor.all
    cases hn : Cursor.next la lb (c.room la lb) c with
    | mk o c' =>
      rw [hn] at n1 n2 n3 n4
      cases o with
      | none =>
        exact ⟨n1, n2, (fun _ h => by cases h), fun p q hb => by
          rcases n4 p q hb with h | h
          · exact .inl h
          · cases h⟩
      | some pr =>
        obtain ⟨a1, a2, a3, a4⟩ := Cursor.all_spec la lb f c' n1
        refine ⟨a1, fun p q hb => a2 p q (n2 p q hb), fun x hx => ?_, fun p q hb => ?_⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact n3 _ rfl
          · exact a3 x hx
        · rcases a4 p q hb with h | h
          · rcases n4 p q h with h | h
            · exact .inl h
            · cases h
              exact .inr List.mem_cons_self
          · exact .inr (List.mem_cons_of_mem _ h)

/-- What `leastBy` returns passes its test. -/
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
def Cursor.rank (K : Nat) (c : Cursor) : Nat × Nat :=
  ((K - c.na) + (K - c.nb),
    if c.inner = 0 then c.na + c.nb + 1
    else if c.col then
      (if K ≤ c.nb then c.na + c.nb + 3 + (c.na - c.inner) else c.na - c.inner)
    else (if K ≤ c.na then c.na + c.nb + 3 + (c.nb - c.inner) else c.nb - c.inner))

/-- The order of the measure: the first part falls, or it stays and the
second falls. -/
def RankLt (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

theorem RankLt.trans {a b c : Nat × Nat} (h₁ : RankLt a b) (h₂ : RankLt b c) : RankLt a c := by
  unfold RankLt at *
  omega

/-- **A unit of a join brings it nearer to every pair not yet combined**: a
pair inside the tables is combined after it, or the measure has fallen. -/
theorem Cursor.next_rank (la lb p q K : Nat) (hp : p < la) (hq : q < lb) (hpK : p < K)
    (hqK : q < K) :
    ∀ (f : Nat) (c : Cursor), c.Ok la lb → c.room la lb ≤ f → ¬ c.Before p q →
      (Cursor.next la lb f c).2.Before p q ∨
        RankLt (Cursor.rank K (Cursor.next la lb f c).2)
          (Cursor.rank K c)
  | 0, c, _, hr, _ => by simp [Cursor.room] at hr
  | f + 1, c, h, hr, hnb => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h0 : c.inner = 0 → ¬ (p < c.na ∧ q < c.nb) := fun _ hh => hnb (.inl hh)
    have e : ∃ col : Bool, (c.inner ≠ 0 → c.col = col) ∧
        (c.inner = 0 → col = (if c.na < la ∧ c.nb < lb then decide (c.nb < c.na)
          else decide (¬ c.na < la))) ∧
        Cursor.next la lb (f + 1) c =
        if col then
          if c.nb < lb then
            if c.inner < c.na then
              (some (c.inner, c.nb), { c with inner := c.inner + 1, col := true })
            else Cursor.next la lb f ⟨c.na, c.nb + 1, 0, false⟩
          else (none, c)
        else
          if c.na < la then
            if c.inner < c.nb then
              (some (c.na, c.inner), { c with inner := c.inner + 1, col := false })
            else Cursor.next la lb f ⟨c.na + 1, c.nb, 0, false⟩
          else (none, c) :=
      ⟨_, fun hi => by simp [hi], fun hi => by simp [hi], rfl⟩
    obtain ⟨col, hcol', hrule, e⟩ := e
    rw [e]
    simp only [Cursor.room] at hr
    cases col with
    | true =>
      have hr1 : c.inner = 0 → (c.na < la ∧ c.nb < lb ∧ c.nb < c.na) ∨
          (¬ (c.na < la ∧ c.nb < lb) ∧ ¬ c.na < la) := fun hi => by
        have := hrule hi
        split at this
        · next hb => exact .inl ⟨hb.1, hb.2, by simpa using this.symm⟩
        · next hb => exact .inr ⟨hb, by simpa using this.symm⟩
      simp only [ite_true]
      split
      · next hnb' =>
        split
        · next hin =>
          right
          by_cases hi : c.inner = 0
          · have h0i : c.na ≤ p ∨ c.nb ≤ q := by have := h0 hi; omega
            have hr1i := hr1 hi
            refine Or.inr ⟨rfl, ?_⟩
            simp only [Cursor.rank, hi]
            simp only [Nat.zero_add, Nat.add_one_ne_zero, ite_false, ite_true]
            split <;> omega
          · have hc := hcol' hi
            refine Or.inr ⟨rfl, ?_⟩
            simp only [Cursor.rank, hi, hc, Nat.add_one_ne_zero, ite_false, ite_true]
            split <;> omega
        · next hin =>
          have hok : (⟨c.na, c.nb + 1, 0, false⟩ : Cursor).Ok la lb :=
            ⟨h1, hnb', (fun hc => by cases hc), fun _ => ⟨Nat.zero_le _, fun h => by cases h⟩⟩
          have hlt : RankLt (Cursor.rank K ⟨c.na, c.nb + 1, 0, false⟩)
              (Cursor.rank K c) := by
            by_cases hi : c.inner = 0
            · have h0i : c.na ≤ p ∨ c.nb ≤ q := by have := h0 hi; omega
              have hr1i := hr1 hi
              simp only [Cursor.rank, RankLt, hi, ite_true]
              omega
            · have hc := hcol' hi
              have := (h3 hc).1
              simp only [Cursor.rank, RankLt, hi, hc, ite_false, ite_true]
              split <;> omega
          by_cases hb2 : (⟨c.na, c.nb + 1, 0, false⟩ : Cursor).Before p q
          · exact .inl ((Cursor.next_spec la lb f _ hok).2.1 p q hb2)
          · rcases Cursor.next_rank la lb p q K hp hq hpK hqK f _ hok (by simp only [Cursor.room]; omega)
              hb2 with h' | h'
            · exact .inl h'
            · exact .inr (h'.trans hlt)
      · next hnb' =>
        exfalso
        by_cases hi : c.inner = 0
        · have h0i : c.na ≤ p ∨ c.nb ≤ q := by have := h0 hi; omega
          have hr1i := hr1 hi
          omega
        · have := (h3 (hcol' hi)).2 (by omega)
          omega
    | false =>
      have hr1 : c.inner = 0 → (c.na < la ∧ c.nb < lb ∧ ¬ c.nb < c.na) ∨
          (¬ (c.na < la ∧ c.nb < lb) ∧ c.na < la) := fun hi => by
        have := hrule hi
        split at this
        · next hb => exact .inl ⟨hb.1, hb.2, by simpa using this.symm⟩
        · next hb => exact .inr ⟨hb, by simpa using this.symm⟩
      simp only [Bool.false_eq_true, ite_false]
      split
      · next hna' =>
        split
        · next hin =>
          right
          by_cases hi : c.inner = 0
          · have h0i : c.na ≤ p ∨ c.nb ≤ q := by have := h0 hi; omega
            have hr1i := hr1 hi
            refine Or.inr ⟨rfl, ?_⟩
            simp only [Cursor.rank, hi]
            simp only [Nat.zero_add, Nat.add_one_ne_zero, ite_false, ite_true,
              Bool.false_eq_true]
            split <;> omega
          · have hc := hcol' hi
            refine Or.inr ⟨rfl, ?_⟩
            simp only [Cursor.rank, hi, hc, Nat.add_one_ne_zero, ite_false,
              Bool.false_eq_true]
            split <;> omega
        · next hin =>
          have hok : (⟨c.na + 1, c.nb, 0, false⟩ : Cursor).Ok la lb :=
            ⟨hna', h2, (fun hc => by cases hc), fun _ => ⟨Nat.zero_le _, fun h => by cases h⟩⟩
          have hlt : RankLt (Cursor.rank K ⟨c.na + 1, c.nb, 0, false⟩)
              (Cursor.rank K c) := by
            by_cases hi : c.inner = 0
            · have h0i : c.na ≤ p ∨ c.nb ≤ q := by have := h0 hi; omega
              have hr1i := hr1 hi
              simp only [Cursor.rank, RankLt, hi, ite_true]
              omega
            · have hc := hcol' hi
              have := (h4 hc).1
              simp only [Cursor.rank, RankLt, hi, hc, ite_false, ite_true, Bool.false_eq_true]
              split <;> omega
          by_cases hb2 : (⟨c.na + 1, c.nb, 0, false⟩ : Cursor).Before p q
          · exact .inl ((Cursor.next_spec la lb f _ hok).2.1 p q hb2)
          · rcases Cursor.next_rank la lb p q K hp hq hpK hqK f _ hok (by simp only [Cursor.room]; omega)
              hb2 with h' | h'
            · exact .inl h'
            · exact .inr (h'.trans hlt)
      · next hna' =>
        exfalso
        by_cases hi : c.inner = 0
        · have h0i : c.na ≤ p ∨ c.nb ≤ q := by have := h0 hi; omega
          have hr1i := hr1 hi
          omega
        · have := (h4 (hcol' hi)).2 (by omega)
          omega

/-- The order of the measure is well founded. -/
theorem rankLt_wf : WellFounded RankLt := by
  refine Subrelation.wf (r := Prod.Lex (· < ·) (· < ·)) ?_ (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  intro a b h
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  rcases h with h | ⟨h, h'⟩
  · exact Prod.Lex.left _ _ h
  · simp only at h h'
    subst h
    exact Prod.Lex.right _ h'

/-- **The whole work of a join brings it no further from a pair not yet
combined**: the pair is combined after it, or the cursor has not moved, or
the measure has fallen. -/
theorem Cursor.all_rank_le (la lb p q K : Nat) (hp : p < la) (hq : q < lb) (hpK : p < K)
    (hqK : q < K) :
    ∀ (f : Nat) (c : Cursor), c.Ok la lb →
      (Cursor.all la lb f c).2.Before p q ∨ (Cursor.all la lb f c).2 = c ∨
        RankLt (Cursor.rank K (Cursor.all la lb f c).2) (Cursor.rank K c)
  | 0, c, _ => .inr (.inl rfl)
  | f + 1, c, h => by
    obtain ⟨n1, n2, -, -⟩ := Cursor.next_spec la lb (c.room la lb) c h
    by_cases hb : c.Before p q
    · exact .inl ((Cursor.all_spec la lb (f + 1) c h).2.1 p q hb)
    have hn := Cursor.next_rank la lb p q K hp hq hpK hqK (c.room la lb) c h (Nat.le_refl _) hb
    unfold Cursor.all
    cases hx : Cursor.next la lb (c.room la lb) c with
    | mk o c' =>
      rw [hx] at n1 n2 hn
      cases o with
      | none =>
        rcases hn with hn | hn
        · exact .inl hn
        · exact .inr (.inr hn)
      | some pr =>
        simp only
        rcases hn with hn | hn
        · exact .inl ((Cursor.all_spec la lb f c' n1).2.1 p q hn)
        · rcases Cursor.all_rank_le la lb p q K hp hq hpK hqK f c' n1 with h' | h' | h'
          · exact .inl h'
          · rw [h']
            exact .inr (.inr hn)
          · exact .inr (.inr (h'.trans hn))

/-- **The whole work of a join brings it nearer to every pair not yet
combined.** -/
theorem Cursor.all_rank (la lb p q K : Nat) (hp : p < la) (hq : q < lb) (hpK : p < K)
    (hqK : q < K) (f : Nat) (c : Cursor) (h : c.Ok la lb) (hb : ¬ c.Before p q) :
    (Cursor.all la lb (f + 1) c).2.Before p q ∨
      RankLt (Cursor.rank K (Cursor.all la lb (f + 1) c).2) (Cursor.rank K c) := by
  obtain ⟨n1, n2, -, -⟩ := Cursor.next_spec la lb (c.room la lb) c h
  have hn := Cursor.next_rank la lb p q K hp hq hpK hqK (c.room la lb) c h (Nat.le_refl _) hb
  unfold Cursor.all
  cases hx : Cursor.next la lb (c.room la lb) c with
  | mk o c' =>
    rw [hx] at n1 n2 hn
    cases o with
    | none => exact hn
    | some pr =>
      simp only
      rcases hn with hn | hn
      · exact .inl ((Cursor.all_spec la lb f c' n1).2.1 p q hn)
      · rcases Cursor.all_rank_le la lb p q K hp hq hpK hqK f c' n1 with h' | h' | h'
        · exact .inl h'
        · rw [h']
          exact .inr hn
        · exact .inr (h'.trans hn)

/-! ## The entry furthest behind is served first -/

/-- What `leastBy` returns has the least key of the entries that pass. -/
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
