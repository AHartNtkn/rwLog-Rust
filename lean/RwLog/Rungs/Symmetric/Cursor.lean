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

`leastBy` returns an entry that passes its test (`leastBy_ok`).

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

end Symmetric

end RwLog
