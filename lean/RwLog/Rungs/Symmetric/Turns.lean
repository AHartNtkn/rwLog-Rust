/-
# What a request does for each table

The record of a stretch of a run, from one state to a later one (`Turns`).
It says what the completeness proof needs of the order in which the machine
works, and nothing of the levels that choose the order.

* `SAdv` relates a strategy to itself later: its kind and the tables it
  reads stay, and its cursors only move on. `SStep` is the same after the
  strategy has worked at least once: a span is tried; a call or a union is
  nearer to every answer of the tables it reads that was there at the start
  (`behind` falls); a join is nearer to every pair that was there at the
  start (`Cursor.rank` falls, or the pair is combined); a check that was
  still to be read is read, or the depth edges are read to has doubled.
* `Settled st j`: the table at `j` needs no round in this request any more.
  `SFed st s`: the tables the strategy `s` reads are settled.
* `Turn st st' go go'` relates the groups of a table before its round to its
  groups after: the groups are the same ones, each strategy moved on, less
  the groups all of whose strategies are dead; and one of the groups worked,
  and the tables it reads are settled.
* `Turns st st'` is the record: what a round keeps (`Keep`); the groups of a
  table change in its own round only; every table that had its round has
  `Turn`; and every table that became complete has a strategy with nothing
  left to do that reads complete tables only (`QuietAt`).

`Turns` is transitive (`TurnsBut.trans`), and it is proved of the round of a
table with every round nested in it (`turns_advance`). The record of a whole
request is `Req` (`req_request`): the same, across the change of the number
of the request and the marking of the tables that complete together.

`Shaped` is the shape of the groups a goal begins with (`shaped_expand`):
every group but the last has a span, a call, a union or a join, so the only
group a round can remove is the last.
-/
import RwLog.Rungs.Symmetric.Kept
import RwLog.Rungs.Symmetric.Cursor

namespace RwLog

namespace Symmetric

open Traverse Answer

section pure

variable {S N A : Type}

/-- How many answers the table at `j` has. -/
def StateOf.len (st : StateOf S N A) (j : Nat) : Nat := (st.answers j).length

theorem Stable.len_le {st st' : StateOf S N A} (h : Stable st st') (j : Nat) :
    st.len j ≤ st'.len j := h.length_le j

/-! ## A call or a union reads on -/

/-- An entry of a call or a union later: the same table, read at least as
far. -/
def SubAdv (p p' : Nat × Nat) : Prop := p'.1 = p.1 ∧ p.2 ≤ p'.2

/-- How far a call or a union is from having read the first `n` answers of
each table it reads. -/
def behind (n : Nat) (subs : List (Nat × Nat)) : Nat := (subs.map fun p => n - p.2).sum

theorem behind_le (n : Nat) : ∀ {subs subs' : List (Nat × Nat)},
    Pointwise SubAdv subs subs' → behind n subs' ≤ behind n subs
  | [], [], _ => Nat.le_refl _
  | [], _ :: _, h => absurd h.1 (by simp)
  | _ :: _, [], h => absurd h.1 (by simp)
  | x :: l, y :: l', h => by
    obtain ⟨h0, h1⟩ := pointwise_cons.1 h
    have h2 := behind_le n h1
    have h3 := h0.2
    simp only [behind, List.map_cons, List.sum_cons] at h2 ⊢
    omega

theorem behind_lt (n : Nat) : ∀ {subs subs' : List (Nat × Nat)},
    Pointwise SubAdv subs subs' → ∀ (m : Nat) (p p' : Nat × Nat), subs[m]? = some p →
      subs'[m]? = some p' → p.2 < n → n ≤ p'.2 → behind n subs' < behind n subs
  | [], _, _, m, p, p', hp, _, _, _ => by simp at hp
  | _ :: _, [], h, _, _, _, _, _, _, _ => absurd h.1 (by simp)
  | x :: l, y :: l', h, m, p, p', hp, hp', h1, h2 => by
    obtain ⟨h0, hl⟩ := pointwise_cons.1 h
    cases m with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hp'
      subst hp; subst hp'
      have h3 := behind_le n hl
      simp only [behind, List.map_cons, List.sum_cons] at h3 ⊢
      omega
    | succ m =>
      have h3 := behind_lt n hl m p p' (by simpa using hp) (by simpa using hp') h1 h2
      have h4 := h0.2
      simp only [behind, List.map_cons, List.sum_cons] at h3 ⊢
      omega

/-! ## A strategy later -/

/-- A strategy and itself later: its kind and the tables it reads are the
same, and its cursors have only moved on. `len` is how many answers each
table had at the start. -/
inductive SAdv (len : Nat → Nat) : Strat N A → Strat N A → Prop
  | span {ran ran' : Bool} : (ran = true → ran' = true) → SAdv len (.span ran) (.span ran')
  | copy {c : Bool} {subs subs' : List (Nat × Nat)} : Pointwise SubAdv subs subs' →
      SAdv len (.copy c subs) (.copy c subs')
  | join {k : Kind} {a b : Nat} {c c' : Cursor} :
      (∀ p q, c.Before p q → c'.Before p q) →
      (∀ p q n, p < len a → q < len b → p < n → q < n →
        c'.Before p q ∨ c' = c ∨ RankLt (Cursor.rank n c') (Cursor.rank n c)) →
      SAdv len (.join k a b c) (.join k a b c')
  | push {k k' : Kind} {l l' : Bool} {side side' : Nat} {o o' : N} {t t' : Option (List A)}
      {subs subs' : List (A × Nat × Nat)} :
      SAdv len (.push k l side o t subs) (.push k' l' side' o' t' subs')
  | check {l : Bool} {side o : N} {c c' : Check} : (c = .reading ∨ c' = c) →
      SAdv len (.check l side o c) (.check l side o c')

theorem SAdv.refl (len : Nat → Nat) : ∀ s : Strat N A, SAdv len s s
  | .span _ => .span id
  | .copy _ _ => .copy (Pointwise.refl (fun _ => ⟨rfl, Nat.le_refl _⟩) _)
  | .join _ _ _ _ => .join (fun _ _ h => h) (fun _ _ _ _ _ _ _ => .inr (.inl rfl))
  | .push _ _ _ _ _ _ => .push
  | .check _ _ _ _ => .check (.inr rfl)

theorem SAdv.mono {len len' : Nat → Nat} (hl : ∀ j, len' j ≤ len j) {s s' : Strat N A}
    (h : SAdv len s s') : SAdv len' s s' := by
  cases h with
  | span h => exact .span h
  | copy h => exact .copy h
  | join h1 h2 =>
    exact .join h1 fun p q n hp hq =>
      h2 p q n (Nat.lt_of_lt_of_le hp (hl _)) (Nat.lt_of_lt_of_le hq (hl _))
  | push => exact .push
  | check h => exact .check h

theorem SubAdv.trans {a b c : Nat × Nat} (h₁ : SubAdv a b) (h₂ : SubAdv b c) : SubAdv a c :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem SAdv.trans {len : Nat → Nat} {s s1 s2 : Strat N A} (h₁ : SAdv len s s1)
    (h₂ : SAdv len s1 s2) : SAdv len s s2 := by
  cases h₁ with
  | span a =>
    cases h₂ with
    | span b => exact .span fun h => b (a h)
  | copy a =>
    cases h₂ with
    | copy b => exact .copy (Pointwise.comp (r₃ := SubAdv) (fun _ _ _ h h' => h.trans h') a b)
  | join a1 a2 =>
    cases h₂ with
    | join b1 b2 =>
      refine .join (fun p q h => b1 p q (a1 p q h)) fun p q n hp hq hpn hqn => ?_
      rcases b2 p q n hp hq hpn hqn with h | h | h
      · exact .inl h
      · rw [h]
        exact a2 p q n hp hq hpn hqn
      · rcases a2 p q n hp hq hpn hqn with h' | h' | h'
        · exact .inl (b1 p q h')
        · rw [h'] at h
          exact .inr (.inr h)
        · exact .inr (.inr (h.trans h'))
  | push =>
    cases h₂ with
    | push => exact .push
  | check a =>
    cases h₂ with
    | check b =>
      rcases a with a | a
      · exact .check (.inl a)
      · rw [a] at b
        exact .check b

/-- A strategy and itself after it has worked at least once. `d` is the
depth edges were read to at the start, `d'` the depth at the end. -/
inductive SStep (len : Nat → Nat) (d d' : Nat) : Strat N A → Strat N A → Prop
  | span {ran : Bool} : SStep len d d' (.span ran) (.span true)
  | copy {c : Bool} {subs subs' : List (Nat × Nat)} : Pointwise SubAdv subs subs' →
      (∀ (n m j pos : Nat), subs[m]? = some (j, pos) → pos < n → n ≤ len j →
        behind n subs' < behind n subs) →
      SStep len d d' (.copy c subs) (.copy c subs')
  | join {k : Kind} {a b : Nat} {c c' : Cursor} :
      (∀ p q, c.Before p q → c'.Before p q) →
      (∀ p q n, p < len a → q < len b → p < n → q < n →
        c'.Before p q ∨ RankLt (Cursor.rank n c') (Cursor.rank n c)) →
      SStep len d d' (.join k a b c) (.join k a b c')
  | push {k k' : Kind} {l l' : Bool} {side side' : Nat} {o o' : N} {t t' : Option (List A)}
      {subs subs' : List (A × Nat × Nat)} :
      SStep len d d' (.push k l side o t subs) (.push k' l' side' o' t' subs')
  | check {l : Bool} {side o : N} {c c' : Check} : (c = .reading ∨ c' = c) →
      (c = .reading → c' ≠ .reading ∨ 2 * d ≤ d') →
      SStep len d d' (.check l side o c) (.check l side o c')

theorem SStep.adv {len : Nat → Nat} {d d' : Nat} {s s' : Strat N A} (h : SStep len d d' s s') :
    SAdv len s s' := by
  cases h with
  | span => exact .span fun _ => rfl
  | copy h _ => exact .copy h
  | join h1 h2 =>
    exact .join h1 fun p q n hp hq hpn hqn =>
      (h2 p q n hp hq hpn hqn).elim .inl fun h => .inr (.inr h)
  | push => exact .push
  | check h _ => exact .check h

theorem SStep.mono {len len' : Nat → Nat} {d d' d0 d1 : Nat} (hl : ∀ j, len' j ≤ len j)
    (hd : d0 ≤ d) (hd' : d' ≤ d1) {s s' : Strat N A} (h : SStep len d d' s s') :
    SStep len' d0 d1 s s' := by
  cases h with
  | span => exact .span
  | copy h1 h2 =>
    exact .copy h1 fun n m j pos hm hp hn => h2 n m j pos hm hp (hn.trans (hl j))
  | join h1 h2 =>
    exact .join h1 fun p q n hp hq =>
      h2 p q n (Nat.lt_of_lt_of_le hp (hl _)) (Nat.lt_of_lt_of_le hq (hl _))
  | push => exact .push
  | check h1 h2 => exact .check h1 fun hc => (h2 hc).imp id fun h => by omega

/-- A strategy that has moved on and then worked has worked. -/
theorem SStep.after {len : Nat → Nat} {d d1 d2 : Nat} {s s1 s2 : Strat N A}
    (h₁ : SAdv len s s1) (h₂ : SStep len d1 d2 s1 s2) (hd : d ≤ d1) : SStep len d d2 s s2 := by
  cases h₁ with
  | span a =>
    cases h₂ with
    | span => exact .span
  | copy a =>
    cases h₂ with
    | copy b1 b2 =>
      refine .copy (Pointwise.comp (r₃ := SubAdv) (fun _ _ _ h h' => h.trans h') a b1) fun n m j pos hm hp hn => ?_
      obtain ⟨p1, hp1, hr⟩ := a.get hm
      by_cases h : p1.2 < n
      · have h3 := b2 n m p1.1 p1.2 hp1 h (by rw [hr.1]; exact hn)
        have h4 := behind_le n a
        omega
      · have h3 := behind_lt n a m (j, pos) p1 hm hp1 hp (by omega)
        have h4 := behind_le n b1
        omega
  | join a1 a2 =>
    cases h₂ with
    | join b1 b2 =>
      refine .join (fun p q h => b1 p q (a1 p q h)) fun p q n hp hq hpn hqn => ?_
      rcases b2 p q n hp hq hpn hqn with h | h
      · exact .inl h
      · rcases a2 p q n hp hq hpn hqn with h' | h' | h'
        · exact .inl (b1 p q h')
        · rw [h'] at h
          exact .inr h
        · exact .inr (h.trans h')
  | push =>
    cases h₂ with
    | push => exact .push
  | check a =>
    cases h₂ with
    | check b1 b2 =>
      refine .check ?_ fun hc => ?_
      · rcases a with a | a
        · exact .inl a
        · rw [a] at b1
          exact b1
      · rename_i c1 c2
        by_cases h1 : c1 = .reading
        · exact (b2 h1).imp id fun h => by omega
        · rcases b1 with h | h
          · exact absurd h h1
          · rw [h]
            exact .inl h1

/-- A dead strategy stays dead. -/
theorem dead_adv {len : Nat → Nat} {s s' : Strat N A} (h : SAdv len s s')
    {st st' : StateOf S N A} (hS : ∀ j, st.answers j <+: st'.answers j)
    (hd : s.dead st = true) : s'.dead st' = true := by
  cases h with
  | span _ => simp [Strat.dead] at hd
  | copy _ => simp [Strat.dead] at hd
  | join _ _ => simp [Strat.dead] at hd
  | push => simp [Strat.dead] at hd
  | check hc =>
    rename_i l side o c c'
    rcases hc with rfl | rfl
    · simp [Strat.dead] at hd
    · cases c' with
      | reading => simp [Strat.dead] at hd
      | off => rfl
      | opened subs =>
        simp only [Strat.dead] at hd ⊢
        obtain ⟨j, hj, hne⟩ := List.any_eq_true.1 hd
        refine List.any_eq_true.2 ⟨j, hj, ?_⟩
        obtain ⟨l', hl'⟩ := hS j
        rw [← hl']
        cases hx : st.answers j with
        | nil => rw [hx] at hne; simp at hne
        | cons _ _ => rfl

theorem Stable.dead {st st' : StateOf S N A} (h : Stable st st') {s : Strat N A}
    (hd : s.dead st = true) : s.dead st' = true :=
  dead_adv (SAdv.refl (fun _ => 0) s) h.answers hd

/-- A strategy with nothing left to do that reads only tables that pass, in
a state where the tables that pass are complete with the same answers, has
nothing left to do and reads complete tables only. -/
theorem quiet_mono {st st' : StateOf S N A} {ok : Nat → Bool}
    (hd : ∀ j, st.isDone j = true → st'.isDone j = true ∧ st'.answers j = st.answers j)
    (hok : ∀ j, ok j = true → st'.isDone j = true ∧ st'.answers j = st.answers j)
    {s : Strat N A} (h : s.quiet st ok = true) : s.quiet st' st'.isDone = true := by
  cases s with
  | span ran => exact h
  | copy c subs =>
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
      List.any_eq_false, List.all_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨fun p hp => by rw [(hok _ (h.2 p hp)).2]; exact h.1 p hp,
      fun p hp => (hok _ (h.2 p hp)).1⟩
  | join k a b c =>
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    rw [(hok a h.2.1).2, (hok b h.2.2).2]
    exact ⟨h.1, (hok a h.2.1).1, (hok b h.2.2).1⟩
  | push k l side o todo subs =>
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true] at h ⊢
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := h
    refine ⟨?_, ⟨(hd side h2).1, h3⟩, fun e he => (hok _ (h4 e he)).1⟩
    rw [h2] at h1
    rw [(hd side h2).1]
    cases todo with
    | none => simp at h1
    | some l0 =>
      simp only [Bool.true_and, Bool.or_eq_false_iff, List.any_eq_false,
        decide_eq_true_eq] at h1 ⊢
      exact ⟨h1.1, fun e he => by rw [(hok _ (h4 e he)).2]; exact h1.2 e he⟩
  | check l side o c =>
    cases c with
    | reading => simp [Strat.quiet, Strat.pending] at h
    | off => simp [Strat.quiet] at h
    | opened subs =>
      simp only [Strat.quiet, Strat.pending, Bool.not_false, Bool.true_and, List.all_eq_true,
        Bool.and_eq_true] at h ⊢
      exact fun j hj => ⟨(hok j (h j hj).1).1, by rw [(hok j (h j hj).1).2]; exact (h j hj).2⟩

/-! ## Tables that need no round -/

/-- The table at `j` needs no round in this request any more: it is
complete, it has had its round, or it was opened in this request. -/
def Settled (st : StateOf S N A) (j : Nat) : Prop :=
  ∀ t, st.tables[j]? = some t → t.done = true ∨ t.stamp = st.round ∨ t.born = st.round

theorem Keep.settled {st st' : StateOf S N A} (h : Keep st st') {j : Nat}
    (hs : Settled st j) : Settled st' j := by
  intro t' ht'
  cases ht : st.tables[j]? with
  | none => exact .inr (.inr ((h.2.2 j t' ht' ht).trans h.1.symm))
  | some t =>
    obtain ⟨u, hu, -, e2, -, e4, e5⟩ := h.2.1 j t ht
    rw [ht'] at hu
    cases hu
    rcases hs t ht with h1 | h1 | h1
    · exact .inl (e4 h1).1
    · exact .inr (.inl ((e5 h1).1.trans h.1.symm))
    · exact .inr (.inr (e2.trans (h1.trans h.1.symm)))

/-- The tables that still need a round in this request. -/
def waiting (st : StateOf S N A) : List Nat :=
  (List.range st.tables.length).filter fun j =>
    match st.tables[j]? with
    | some t => !t.done && !decide (t.stamp = st.round) && !decide (t.born = st.round)
    | none => false

theorem mem_waiting {st : StateOf S N A} {j : Nat} :
    j ∈ waiting st ↔ ∃ t, st.tables[j]? = some t ∧ t.done = false ∧ t.stamp ≠ st.round ∧
      t.born ≠ st.round := by
  unfold waiting
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨-, h⟩
    cases ht : st.tables[j]? with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact ⟨t, rfl, h.1.1, h.1.2, h.2⟩
  · rintro ⟨t, ht, h1, h2, h3⟩
    refine ⟨(List.getElem?_eq_some_iff.1 ht).1, ?_⟩
    rw [ht]
    simp [h1, h2, h3]

theorem settled_of_not_waiting {st : StateOf S N A} {j : Nat} (h : j ∉ waiting st) :
    Settled st j := by
  intro t ht
  by_contra hc
  simp only [not_or] at hc
  exact h (mem_waiting.2 ⟨t, ht, by simpa using hc.1, hc.2.1, hc.2.2⟩)

theorem waiting_sub {st st' : StateOf S N A} (h : Keep st st') : waiting st' ⊆ waiting st := by
  intro j hj
  obtain ⟨t', ht', h1, h2, h3⟩ := mem_waiting.1 hj
  by_contra hc
  have hs : Settled st j := settled_of_not_waiting hc
  rcases h.settled hs t' ht' with h' | h' | h'
  · rw [h1] at h'; cases h'
  · exact h2 h'
  · exact h3 h'

theorem waiting_nodup (st : StateOf S N A) : (waiting st).Nodup :=
  List.nodup_range.filter _

theorem waiting_le {st st' : StateOf S N A} (h : Keep st st') :
    (waiting st').length ≤ (waiting st).length :=
  (List.subperm_of_subset (waiting_nodup st') (waiting_sub h)).length_le

theorem waiting_lt {st st' : StateOf S N A} (h : waiting st' ⊆ waiting st) {i : Nat}
    (hi : i ∈ waiting st) (hn : i ∉ waiting st') :
    (waiting st').length < (waiting st).length := by
  have hsub : waiting st' ⊆ (waiting st).erase i := fun x hx =>
    ((waiting_nodup st).mem_erase_iff).2 ⟨fun e => hn (e ▸ hx), h hx⟩
  have h1 := (List.subperm_of_subset (waiting_nodup st') hsub).length_le
  have h2 := List.length_erase_of_mem hi
  have h3 := List.length_pos_of_mem hi
  omega

/-- The tables the strategy reads need no round in this request any more. A
check is asked only while none of the goals it opened has an answer. -/
def SFed (st : StateOf S N A) : Strat N A → Prop
  | .copy _ subs => ∀ p ∈ subs, Settled st p.1
  | .join _ a b _ => Settled st a ∧ Settled st b
  | .check _ _ _ c =>
    match c with
    | .opened subs => (∀ j ∈ subs, st.answers j = []) → ∀ j ∈ subs, Settled st j
    | _ => True
  | _ => True

theorem SFed.mono {st st' : StateOf S N A} (h : Stable st st')
    (hset : ∀ j, Settled st j → Settled st' j) {s : Strat N A} (hs : SFed st s) :
    SFed st' s := by
  cases s with
  | span _ => trivial
  | copy _ subs => exact fun p hp => hset _ (hs p hp)
  | join _ a b _ => exact ⟨hset _ hs.1, hset _ hs.2⟩
  | push _ _ _ _ _ _ => trivial
  | check _ _ _ c =>
    cases c with
    | reading => trivial
    | off => trivial
    | opened subs =>
      intro he j hj
      refine hset _ (hs (fun j' hj' => ?_) j hj)
      have := h.answers j'
      rw [he j' hj'] at this
      exact List.prefix_nil.1 this

theorem SFed.keep {st st' : StateOf S N A} (h : Keep st st') {s : Strat N A}
    (hs : SFed st s) : SFed st' s := hs.mono h.stable fun _ => h.settled

/-- The tables a strategy reads, once each has had what a round gives it,
need no round. -/
theorem sfed_of_feeds {st st' : StateOf S N A} (hS : Stable st st') {s : Strat N A}
    (h : ∀ j ∈ s.feeds st, Settled st' j) : SFed st' s := by
  cases s with
  | span _ => trivial
  | copy _ subs => exact fun p hp => h p.1 (List.mem_map.2 ⟨p, hp, rfl⟩)
  | join _ a b _ => exact ⟨h a (by simp [Strat.feeds]), h b (by simp [Strat.feeds])⟩
  | push _ _ _ _ _ _ => trivial
  | check _ _ _ c =>
    cases c with
    | reading => trivial
    | off => trivial
    | opened subs =>
      intro he j hj
      apply h
      have hno : (subs.any fun j => !(st.answers j).isEmpty) = false := by
        rw [List.any_eq_false]
        intro j' hj'
        have := hS.answers j'
        rw [he j' hj'] at this
        rw [List.prefix_nil.1 this]
        simp
      simp only [Strat.feeds, hno]
      exact hj

/-! ## The groups of a table over its round -/

/-- A group later: each of its strategies later. -/
def GrAdv (len : Nat → Nat) (gr gr' : Group N A) : Prop :=
  Pointwise (SAdv len) gr.strats gr'.strats

/-- A group after it has worked: each of its strategies has. -/
def GrStep (len : Nat → Nat) (d d' : Nat) (gr gr' : Group N A) : Prop :=
  Pointwise (SStep len d d') gr.strats gr'.strats

/-- A span, a call, a union or a join: the strategies that head a group. -/
def Strat.lead : Strat N A → Bool
  | .span _ => true
  | .copy _ _ => true
  | .join _ _ _ _ => true
  | _ => false

/-- The shape of the groups of a table: one of them has a span, a call, a
union or a join, and only the last can be without one. -/
def Shaped (gs : List (Group N A)) : Prop :=
  (∃ gr ∈ gs, ∃ s ∈ gr.strats, s.lead = true) ∧
    ∀ gr ∈ gs.dropLast, ∃ s ∈ gr.strats, s.lead = true

/-- The groups of a table before its round (`go`, nothing if this is its
first) and after it (`go'`). -/
def Turn (st st' : StateOf S N A) (go go' : Option (List (Group N A))) : Prop :=
  ∃ (gs0 gs1 : List (Group N A)) (p : Group N A → Bool),
    (∀ gs, go = some gs → gs = gs0) ∧ (go = none → Shaped gs0) ∧ go'.getD [] = gs1.filter p ∧
    Pointwise (fun gr0 gr1 => GrAdv st.len gr0 gr1 ∧
      (p gr1 = true → ∃ s ∈ gr0.strats, s.dead st = false) ∧
      (p gr1 = false → ∀ s ∈ gr1.strats, s.dead st' = true)) gs0 gs1 ∧
    (gs0 = [] ∨ ∃ (k : Nat) (gr0 gr1 : Group N A), gs0[k]? = some gr0 ∧ gs1[k]? = some gr1 ∧
      GrStep st.len st.depth st'.depth gr0 gr1 ∧ ∀ s ∈ gr1.strats, SFed st' s)

/-- The record of a round stays true from an earlier state. -/
theorem Turn.start {a b c : StateOf S N A} (hS : Stable a b) (hd : a.depth ≤ b.depth)
    {go go' : Option (List (Group N A))} (h : Turn b c go go') : Turn a c go go' := by
  obtain ⟨gs0, gs1, p, h1, h2, h3, h4, h5⟩ := h
  have h4' := h4.imp (r' := fun gr0 gr1 => GrAdv a.len gr0 gr1 ∧
      (p gr1 = true → ∃ s ∈ gr0.strats, s.dead a = false) ∧
      (p gr1 = false → ∀ s ∈ gr1.strats, s.dead c = true)) fun gr0 gr1 hg => by
    refine ⟨hg.1.imp fun _ _ hs => hs.mono hS.len_le, fun hp => ?_, hg.2.2⟩
    obtain ⟨s, hs, hdead⟩ := hg.2.1 hp
    refine ⟨s, hs, ?_⟩
    cases hx : s.dead a with
    | false => rfl
    | true => rw [hS.dead hx] at hdead; cases hdead
  refine ⟨gs0, gs1, p, h1, h2, h3, h4', ?_⟩
  · rcases h5 with h5 | ⟨k, gr0, gr1, e0, e1, hst, hf⟩
    · exact .inl h5
    · exact .inr ⟨k, gr0, gr1, e0, e1,
        hst.imp fun _ _ hs => hs.mono hS.len_le hd (Nat.le_refl _), hf⟩

/-- The record of a round stays true to a later state. -/
theorem Turn.finish {a b c : StateOf S N A} (hS : Stable b c)
    (hset : ∀ j, Settled b j → Settled c j) (hd : b.depth ≤ c.depth)
    {go go' : Option (List (Group N A))} (h : Turn a b go go') : Turn a c go go' := by
  obtain ⟨gs0, gs1, p, h1, h2, h3, h4, h5⟩ := h
  have h4' := h4.imp (r' := fun gr0 gr1 => GrAdv a.len gr0 gr1 ∧
      (p gr1 = true → ∃ s ∈ gr0.strats, s.dead a = false) ∧
      (p gr1 = false → ∀ s ∈ gr1.strats, s.dead c = true)) fun gr0 gr1 hg =>
    ⟨hg.1, hg.2.1, fun hp s hs => hS.dead (hg.2.2 hp s hs)⟩
  refine ⟨gs0, gs1, p, h1, h2, h3, h4', ?_⟩
  rcases h5 with h5 | ⟨k, gr0, gr1, e0, e1, hst, hf⟩
  · exact .inl h5
  · exact .inr ⟨k, gr0, gr1, e0, e1,
      hst.imp fun _ _ hs => hs.mono (fun _ => Nat.le_refl _) (Nat.le_refl _) hd,
      fun s hs => (hf s hs).mono hS hset⟩

theorem shaped_all {gs : List (Group N A)} (hne : gs ≠ [])
    (h : ∀ gr ∈ gs, ∃ s ∈ gr.strats, s.lead = true) : Shaped gs := by
  cases gs with
  | nil => exact absurd rfl hne
  | cons gr gs =>
    exact ⟨⟨gr, List.mem_cons_self, h gr List.mem_cons_self⟩,
      fun gr' hk => h gr' (List.mem_of_mem_dropLast hk)⟩

theorem shaped_of {gs : List (Group N A)} {c : Prop}
    (h : (∀ gr ∈ gs, ∃ s ∈ gr.strats, s.lead = true) ∧ (c → gs ≠ [])) (hc : c) : Shaped gs :=
  shaped_all (h.2 hc) h.1

theorem shaped_snoc {gs : List (Group N A)} (hne : gs ≠ [])
    (h : ∀ gr ∈ gs, ∃ s ∈ gr.strats, s.lead = true) (last : Group N A) :
    Shaped (gs ++ [last]) := by
  obtain ⟨⟨gr, hgr, hl⟩, -⟩ := shaped_all hne h
  refine ⟨⟨gr, List.mem_append_left _ hgr, hl⟩, fun gr' hk => ?_⟩
  rw [List.dropLast_concat] at hk
  exact h gr' hk

theorem mem_levelsOf {gs : List (Group N A)} {lv : Nat} (h : lv ∈ levelsOf gs) :
    ∃ gr ∈ gs, gr.level = lv := by
  unfold levelsOf at h
  obtain ⟨gr, hgr, rfl⟩ := List.mem_map.1 (List.mem_mergeSort.1 (List.mem_eraseDups.1 h))
  exact ⟨gr, hgr, rfl⟩

theorem levelsOf_ne_nil {gs : List (Group N A)} (h : gs ≠ []) : levelsOf gs ≠ [] := by
  cases gs with
  | nil => exact absurd rfl h
  | cons gr gs =>
    have : gr.level ∈ levelsOf (gr :: gs) := by
      unfold levelsOf
      exact List.mem_eraseDups.2 (List.mem_mergeSort.2 (List.mem_map.2 ⟨gr, List.mem_cons_self, rfl⟩))
    exact List.ne_nil_of_mem this

/-! ## The record -/

/-- The table has a strategy with nothing left to do that reads complete
tables only. -/
def QuietAt (st : StateOf S N A) (t : Table S N A) : Prop :=
  ∃ gs, t.groups = some gs ∧ ∃ gr ∈ gs, ∃ s ∈ gr.strats, s.quiet st st.isDone = true

theorem QuietAt.mono {st st' : StateOf S N A} (hS : Stable st st') {t t' : Table S N A}
    (hg : t'.groups = t.groups) (h : QuietAt st t) : QuietAt st' t' := by
  obtain ⟨gs, h1, gr, hgr, s, hs, hq⟩ := h
  exact ⟨gs, hg.trans h1, gr, hgr, s, hs,
    quiet_mono (fun _ => hS.isDone) (fun _ => hS.isDone) hq⟩

/-- The record of a stretch of a run. With `x` the position of a table in
its round, the record says nothing of the groups of that table while it is
not complete. -/
structure TurnsBut (x : Option Nat) (st st' : StateOf S N A) : Prop where
  keep : Keep st st'
  depth : st.depth ≤ st'.depth
  stamp : (∀ (k : Nat) (t : Table S N A), st.tables[k]? = some t → t.stamp ≤ st.round) →
    ∀ (k : Nat) (t : Table S N A), st'.tables[k]? = some t → t.stamp ≤ st'.round
  groups : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    (t.done = true ∨ (some k ≠ x ∧ (t.stamp = st.round ∨ t'.stamp ≠ st.round))) →
    t'.groups = t.groups
  done : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → t'.done = true →
    (∃ t, st.tables[k]? = some t ∧ t.done = true) ∨ QuietAt st' t'
  turn : ∀ (k : Nat) (t t' : Table S N A), some k ≠ x → st.tables[k]? = some t →
    st'.tables[k]? = some t' → t.stamp ≠ st.round → t'.stamp = st.round →
    Turn st st' t.groups t'.groups
  young : ∀ (k : Nat) (t' : Table S N A), some k ≠ x → st'.tables[k]? = some t' →
    t'.born = st'.round → (∀ t, st.tables[k]? = some t → t.groups = none) → t'.groups = none

/-- The record of a stretch of a run. -/
abbrev Turns (st st' : StateOf S N A) : Prop := TurnsBut none st st'

theorem TurnsBut.trans {x : Option Nat} {a b c : StateOf S N A} (h₁ : TurnsBut x a b)
    (h₂ : TurnsBut x b c) : TurnsBut x a c := by
  have hr : b.round = a.round := h₁.keep.1
  refine ⟨h₁.keep.trans h₂.keep, h₁.depth.trans h₂.depth, fun h => h₂.stamp (h₁.stamp h),
    fun k ta tc ha hc hyp => ?_, fun k tc hc hdc => ?_, fun k ta tc hx ha hc hs hs' => ?_,
    fun k tc hx hc hbc hyp => ?_⟩
  · obtain ⟨tb, hb, -, -, -, e4, e5⟩ := h₁.keep.2.1 k ta ha
    obtain ⟨tc', hc', -, -, -, -, f5⟩ := h₂.keep.2.1 k tb hb
    rw [hc] at hc'
    cases hc'
    rcases hyp with hd | ⟨hx, hs | hs⟩
    · exact (h₂.groups k tb tc hb hc (.inl (e4 hd).1)).trans (h₁.groups k ta tb ha hb (.inl hd))
    · have hsb : tb.stamp = b.round := by rw [(e5 hs).1, hr]
      exact (h₂.groups k tb tc hb hc (.inr ⟨hx, .inl hsb⟩)).trans
        (h₁.groups k ta tb ha hb (.inr ⟨hx, .inl hs⟩))
    · have hsb : tb.stamp ≠ a.round := fun e => hs (by rw [(f5 (by rw [e, hr])).1, hr])
      exact (h₂.groups k tb tc hb hc (.inr ⟨hx, .inr (by rw [hr]; exact hs)⟩)).trans
        (h₁.groups k ta tb ha hb (.inr ⟨hx, .inr hsb⟩))
  · rcases h₂.done k tc hc hdc with ⟨tb, hb, hdb⟩ | hq
    · rcases h₁.done k tb hb hdb with h | hq
      · exact .inl h
      · exact .inr (hq.mono h₂.keep.stable (h₂.groups k tb tc hb hc (.inl hdb)))
    · exact .inr hq
  · obtain ⟨tb, hb, -, -, -, -, e5⟩ := h₁.keep.2.1 k ta ha
    by_cases hsb : tb.stamp = a.round
    · have hg := h₂.groups k tb tc hb hc (.inr ⟨hx, .inl (by rw [hsb, hr])⟩)
      rw [hg]
      exact (h₁.turn k ta tb hx ha hb hs hsb).finish h₂.keep.stable (fun _ => h₂.keep.settled)
        h₂.depth
    · have hg := h₁.groups k ta tb ha hb (.inr ⟨hx, .inr hsb⟩)
      rw [← hg]
      exact (h₂.turn k tb tc hx hb hc (by rw [hr]; exact hsb) (by rw [hr]; exact hs')).start
        h₁.keep.stable h₁.depth
  · cases hb : b.tables[k]? with
    | none => exact h₂.young k tc hx hc hbc fun t h => by rw [hb] at h; cases h
    | some tb =>
      obtain ⟨tc', hc', -, e2, -⟩ := h₂.keep.2.1 k tb hb
      rw [hc] at hc'
      cases hc'
      have hg := h₁.young k tb hx hb (by rw [← e2, hbc, h₂.keep.1]) hyp
      exact h₂.young k tc hx hc hbc fun t h => by rw [hb] at h; cases h; exact hg

theorem TurnsBut.refl (x : Option Nat) (st : StateOf S N A) : TurnsBut x st st :=
  ⟨Keep.refl st, Nat.le_refl _, fun h => h, (fun k t t' h h' _ => by rw [h] at h'; cases h'; rfl),
    fun k t' h hd => .inl ⟨t', h, hd⟩, (fun k t t' _ h h' hs hs' => by
      rw [h] at h'; cases h'; exact absurd hs' hs), fun k t' _ h _ hyp => hyp t' h⟩

/-- A record that says everything says what a record about a round says. -/
theorem TurnsBut.weaken {st st' : StateOf S N A} (h : Turns st st') (x : Option Nat) :
    TurnsBut x st st' :=
  ⟨h.keep, h.depth, h.stamp, fun k t t' ht ht' hyp => h.groups k t t' ht ht'
      (hyp.imp id fun hh => ⟨(fun e => by cases e), hh.2⟩),
    h.done, (fun k t t' _ => h.turn k t t' (fun e => by cases e)),
    fun k t' _ => h.young k t' (fun e => by cases e)⟩

/-! ## The record of a request -/

/-- No table is stamped or opened later than now. -/
def Dated (st : StateOf S N A) : Prop :=
  ∀ (k : Nat) (t : Table S N A), st.tables[k]? = some t → t.stamp ≤ st.round ∧ t.born ≤ st.round

/-- The record of a request. -/
structure Req (st st' : StateOf S N A) : Prop where
  round : st'.round = st.round + 1
  stable : Stable st st'
  depth : st.depth ≤ st'.depth
  dated : Dated st'
  born : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → st.tables[k]? = none →
    t'.born = st'.round ∧ t'.groups = none
  groups : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    (t.done = true ∨ t'.stamp ≠ st'.round) → t'.groups = t.groups
  done : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → t'.done = true →
    (∃ t, st.tables[k]? = some t ∧ t.done = true) ∨ QuietAt st' t'
  turn : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    t'.stamp = st'.round → Turn st st' t.groups t'.groups
  root : Settled st' 0

/-- **The record of a request**, from the record of the round of the root:
the tables that complete together are marked. -/
theorem req_of_turns {st st2 : StateOf S N A} (hD : Dated st)
    (T : Turns { st with round := st.round + 1 } st2) (h0 : Settled st2 0) (shown : Nat) :
    Req st { st2 with
      tables := st2.tables.mapIdx fun i t =>
        if (completing st2).contains i then { t with done := true } else t,
      shown := shown } := by
  generalize hst' : ({ st2 with
      tables := st2.tables.mapIdx fun i t =>
        if (completing st2).contains i then { t with done := true } else t,
      shown := shown } : StateOf S N A) = st'
  have hr' : st'.round = st2.round := by rw [← hst']
  have hd' : st'.depth = st2.depth := by rw [← hst']
  have hr2 : st2.round = st.round + 1 := T.keep.1
  have hsame : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' →
      ∃ t2, st2.tables[k]? = some t2 ∧ t'.born = t2.born ∧ t'.stamp = t2.stamp ∧
        t'.groups = t2.groups ∧ (t2.done = true → t'.done = true) ∧
        (t'.done = true → t2.done = true ∨ k ∈ completing st2) := by
    intro k t' hk
    rw [← hst'] at hk
    simp only [List.getElem?_mapIdx] at hk
    cases h2 : st2.tables[k]? with
    | none => rw [h2] at hk; cases hk
    | some t2 =>
      rw [h2] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      subst hk
      refine ⟨t2, rfl, ?_⟩
      split
      · next hc => exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => .inr (by simpa using hc)⟩
      · exact ⟨rfl, rfl, rfl, id, .inl⟩
  have hS23 : Stable st2 st' := by
    intro k t2 hk
    rw [← hst']
    refine ⟨_, by simp only [List.getElem?_mapIdx, hk]; rfl, ?_⟩
    split
    · exact ⟨rfl, rfl, List.prefix_refl _, fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩⟩
  have hS01 : Stable st ({ st with round := st.round + 1 } : StateOf S N A) :=
    fun k t h => ⟨t, h, rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩⟩
  have hset : ∀ j, Settled st2 j → Settled st' j := by
    intro j hj t' ht'
    obtain ⟨t2, h2, e1, e2, -, e4, -⟩ := hsame j t' ht'
    rcases hj t2 h2 with h | h | h
    · exact .inl (e4 h)
    · exact .inr (.inl (by rw [e2, h, hr']))
    · exact .inr (.inr (by rw [e1, h, hr']))
  have hst2 : ∀ (k : Nat) (t2 : Table S N A), st2.tables[k]? = some t2 → t2.stamp ≤ st2.round :=
    T.stamp fun k t (h : st.tables[k]? = some t) => Nat.le_succ_of_le (hD k t h).1
  refine ⟨hr'.trans hr2, hS01.trans (T.keep.stable.trans hS23), by rw [hd']; exact T.depth,
    fun k t' hk => ?_, fun k t' hk hn => ?_, fun k t t' ht hk hyp => ?_, fun k t' hk hdn => ?_,
    fun k t t' ht hk hs => ?_, hset 0 h0⟩
  · obtain ⟨t2, h2, e1, e2, -⟩ := hsame k t' hk
    refine ⟨by rw [e2, hr']; exact hst2 k t2 h2, ?_⟩
    rw [e1, hr']
    cases ht : st.tables[k]? with
    | none => exact Nat.le_of_eq ((T.keep.2.2 k t2 h2 ht).trans hr2.symm)
    | some t =>
      obtain ⟨u, hu, -, f2, -⟩ := T.keep.2.1 k t ht
      rw [h2] at hu
      cases hu
      rw [f2, hr2]
      exact Nat.le_succ_of_le (hD k t ht).2
  · obtain ⟨t2, h2, e1, -, e3, -⟩ := hsame k t' hk
    have hb : t2.born = st2.round := (T.keep.2.2 k t2 h2 hn).trans hr2.symm
    exact ⟨by rw [e1, hb, hr'], by
      rw [e3]
      exact T.young k t2 (fun e => by cases e) h2 hb fun t (h : st.tables[k]? = some t) => by
        rw [hn] at h; cases h⟩
  · obtain ⟨t2, h2, -, e2, e3, -⟩ := hsame k t' hk
    rw [e3]
    refine T.groups k t t2 ht h2 (hyp.imp id fun h => ⟨(fun e => by cases e), .inr fun e => h ?_⟩)
    rw [e2, hr', hr2]
    exact e
  · obtain ⟨t2, h2, -, -, e3, -, e5⟩ := hsame k t' hk
    rcases e5 hdn with h | h
    · rcases T.done k t2 h2 h with h | h
      · exact .inl h
      · exact .inr (h.mono hS23 e3)
    · refine .inr ?_
      unfold completing at h
      obtain ⟨-, hok⟩ := gfpFrom_closed _ _ _ (Nat.le_refl _) k h
      rw [h2] at hok
      obtain ⟨gr, hgr, hq⟩ := List.any_eq_true.1 hok
      obtain ⟨s, hs, hq⟩ := List.any_eq_true.1 hq
      cases hg : t2.groups with
      | none => rw [hg] at hgr; simp at hgr
      | some gs =>
        rw [hg] at hgr
        refine ⟨gs, e3.trans hg, gr, hgr, s, hs,
          quiet_mono (fun _ => hS23.isDone) (fun j hj => ?_) hq⟩
        rcases Bool.or_eq_true_iff.1 hj with hj | hj
        · exact hS23.isDone hj
        · have hj' := List.contains_iff_mem.1 hj
          have hjS := (gfpFrom_closed _ _ _ (Nat.le_refl _) j hj').1
          have hlt : j < st2.tables.length := List.mem_range.1 (List.mem_filter.1 hjS).1
          have hj'' : j ∈ completing st2 := hj'
          rw [← hst']
          simp [StateOf.isDone, StateOf.answers, List.getElem?_mapIdx,
            List.getElem?_eq_getElem hlt, hj'']
  · obtain ⟨t2, h2, -, e2, e3, -⟩ := hsame k t' hk
    rw [e3]
    have hs2 : t2.stamp = st.round + 1 := by rw [← e2, hs, hr', hr2]
    have hne : t.stamp ≠ st.round + 1 := fun e => by
      have := (hD k t ht).1
      omega
    exact ((T.turn k t t2 (fun e => by cases e) ht h2 hne hs2).finish hS23 hset
      (Nat.le_of_eq hd'.symm)).start hS01 (Nat.le_refl _)

end pure

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-! ## The work of a strategy -/

theorem length_addAnswer (i : Nat) (st : StateOf R Rel (Ans D P)) (a : Ans D P) :
    (addAnswer (K := DerivationKernel.over D K hK P) i st a).val.tables.length =
      st.tables.length ∧
    (addAnswer (K := DerivationKernel.over D K hK P) i st a).val.depth = st.depth := by
  rw [addAnswer_val]
  split
  · exact ⟨rfl, rfl⟩
  · split
    · split
      · exact ⟨by simp [StateOf.modify], rfl⟩
      · exact ⟨by simp [StateOf.modify], rfl⟩
    · exact ⟨by simp [StateOf.modify], rfl⟩

/-- The work of a strategy does not lower the depth edges are read to. -/
theorem Inner.depth_le {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK j st st') :
    st.depth ≤ st'.depth := by
  induction h with
  | refl st => exact Nat.le_refl _
  | trans _ _ a b => exact a.trans b
  | same _ _ _ hd => exact hd
  | opened _ _ _ _ _ hd => exact hd
  | add st a => rw [(length_addAnswer j st a).2]

/-- A table the work of a strategy opens has had no round. -/
theorem Inner.fresh_stamp {j : Nat} {st st' : StateOf R Rel (Ans D P)}
    (h : Inner K hK j st st') : ∀ (k : Nat) (t' : Table R Rel (Ans D P)),
      st'.tables[k]? = some t' → st.tables[k]? = none → t'.stamp = 0 := by
  induction h with
  | refl st => intro k t' h h'; rw [h] at h'; cases h'
  | @trans a b c hab hbc ih1 ih2 =>
    intro k t' hc ha
    cases hb : b.tables[k]? with
    | none => exact ih2 k t' hc hb
    | some tb =>
      obtain ⟨u, hu, -, -, e3, -⟩ := hbc.frame.2.1 k tb hb
      rw [hc] at hu
      cases hu
      rw [e3]
      exact ih1 k tb hb ha
  | @same st st' e _ _ _ =>
    intro k t' h h'
    have hl : st'.tables.length = st.tables.length := by
      simpa [StateOf.frames] using congrArg List.length e
    have h1 := (List.getElem?_eq_some_iff.1 h).1
    have h2 := List.getElem?_eq_none_iff.1 h'
    omega
  | @opened st st' g self e _ _ _ =>
    intro k t' h h'
    have h2 := List.getElem?_eq_none_iff.1 h'
    have hf : st'.frames[k]? = some t'.frame := by
      simp [StateOf.frames, h]
    rw [e] at hf
    have hl : st.frames.length = st.tables.length := by simp [StateOf.frames]
    rw [List.getElem?_append_right (by omega)] at hf
    cases hk : k - st.frames.length with
    | zero =>
      rw [hk] at hf
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      have := congrArg (fun f => f.2.2.2.2.2.1) hf
      simpa [Table.frame] using this.symm
    | succ n => rw [hk] at hf; simp at hf
  | add st a =>
    intro k t' h h'
    have hl := (length_addAnswer (K := K) (hK := hK) j st a).1
    have h1 := (List.getElem?_eq_some_iff.1 h).1
    have h2 := List.getElem?_eq_none_iff.1 h'
    omega

/-- The record of the work of a strategy of an open table. -/
theorem Inner.turns {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK j st st')
    (ho : Open st j) : Turns st st' := by
  have hf := h.frame
  have hopen : ∀ t, st.tables[j]? = some t → t.done = false := fun t ht => by
    obtain ⟨u, hu, hd⟩ := ho
    rw [ht] at hu
    cases hu
    exact hd
  refine ⟨hf.keep hopen, h.depth_le, fun hs k t' hk => ?_, fun k t t' ht ht' _ => ?_,
    fun k t' hk hd => ?_, fun k t t' _ ht ht' hs hs' => ?_, fun k t' _ hk _ hyp => ?_⟩
  · rw [hf.1]
    cases ht : st.tables[k]? with
    | none => rw [h.fresh_stamp k t' hk ht]; exact Nat.zero_le _
    | some t =>
      obtain ⟨u, hu, -, -, e3, -⟩ := hf.2.1 k t ht
      rw [hk] at hu
      cases hu
      rw [e3]
      exact hs k t ht
  · obtain ⟨u, hu, -, -, -, -, e5, -⟩ := hf.2.1 k t ht
    rw [ht'] at hu
    cases hu
    exact e5
  · cases ht : st.tables[k]? with
    | none => rw [(hf.2.2 k t' hk ht).2.2] at hd; cases hd
    | some t =>
      obtain ⟨u, hu, -, e2, -⟩ := hf.2.1 k t ht
      rw [hk] at hu
      cases hu
      exact .inl ⟨t, rfl, by rw [← e2]; exact hd⟩
  · obtain ⟨u, hu, -, -, e3, -⟩ := hf.2.1 k t ht
    rw [ht'] at hu
    cases hu
    rw [e3] at hs'
    exact absurd hs' hs
  · cases ht : st.tables[k]? with
    | none => exact (hf.2.2 k t' hk ht).1
    | some t =>
      obtain ⟨u, hu, -, -, -, -, e5, -⟩ := hf.2.1 k t ht
      rw [hk] at hu
      cases hu
      rw [e5]
      exact hyp t ht

omit [DecidableEq R] in
/-- The record of a change to an open table that leaves its goal, its
answers and its marks. -/
theorem turnsBut_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hf : ∀ t, (f t).goal = t.goal ∧ (f t).born = t.born ∧ (f t).answers = t.answers ∧
      (f t).done = t.done ∧ ((f t).stamp = t.stamp ∨ (f t).stamp = st.round))
    (ho : ∀ t, st.tables[i]? = some t → t.done = false) :
    TurnsBut (some i) st (st.modify i f) := by
  refine ⟨keep_modify st i f fun t _ => ⟨(hf t).1, (hf t).2.1, (hf t).2.2.1,
      fun h => by rw [(hf t).2.2.2.1]; exact h,
      fun h => ⟨by rcases (hf t).2.2.2.2 with e | e
                   · rw [e]; exact h
                   · exact e,
        fun h => by rw [(hf t).2.2.2.1]; exact h⟩⟩,
    Nat.le_refl _, fun hs k t' hk => ?_, fun k t t' ht ht' hyp => ?_, fun k t' hk hd => ?_,
    fun k t t' hx ht ht' hs hs' => ?_, fun k t' hx hk _ hyp => ?_⟩
  · rcases getElem?_modify_cases st i f hk with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
    · exact hs k t' h
    · rcases (hf t).2.2.2.2 with e | e
      · rw [e]
        exact hs k t ht
      · exact Nat.le_of_eq e
  · rcases getElem?_modify_cases st i f ht' with ⟨-, h⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h
      cases h
      rfl
    · rw [ht] at hu
      cases hu
      rcases hyp with hd | ⟨hx, -⟩
      · rw [ho t ht] at hd
        cases hd
      · exact absurd rfl hx
  · rcases getElem?_modify_cases st i f hk with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
    · exact .inl ⟨t', h, hd⟩
    · exact .inl ⟨t, ht, by rw [← (hf t).2.2.2.1]; exact hd⟩
  · rcases getElem?_modify_cases st i f ht' with ⟨-, h⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h
      cases h
      exact absurd hs' hs
    · exact absurd rfl hx
  · rcases getElem?_modify_cases st i f hk with ⟨-, h⟩ | ⟨rfl, u, hu, rfl⟩
    · exact hyp t' h
    · exact absurd rfl hx

/-- A reading of an edge that was not deep enough doubles the depth. -/
theorem edgeOf_none (st : StateOf R Rel (Ans D P)) (last : Bool) (n : Rel) :
    (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.2 = none →
      (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1.depth = 2 * st.depth := by
  at_cost K hK
  simp only [edgeOf, Cost.bind_val]
  split
  · intro h
    cases h
  · simp only [Cost.bind_val, Cost.pure_val]
    cases (readEdge (K := DerivationKernel.over D _ hK P) last st.depth n).val with
    | none => intro _; rfl
    | some e => intro h; cases h

/-- **The work of a strategy moves it on**: a span is tried; a call or a
union is nearer to every answer that was there; a join is nearer to every
pair that was there; a check still to be read is read, or the depth has
doubled. -/
theorem step_work (whole : Bool) (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P))
    (hok : ∀ k a b c, s = .join k a b c → c.Ok (st.len a) (st.len b)) :
    SStep st.len st.depth
      (work (K := DerivationKernel.over D K hK P) whole i g st s).val.1.depth s
      (work (K := DerivationKernel.over D K hK P) whole i g st s).val.2.1 := by
  have hedge := edgeOf_none (K := K) (hK := hK) (P := P) st
  at_cost K hK
  cases s with
  | span ran =>
    cases ran
    · simp only [work, Cost.bind_val, Cost.pure_val]
      exact .span
    · exact .span
  | copy c subs =>
    simp only [work]
    split
    · simp only [Cost.bind_val, Cost.pure_val]
      have hpw : Pointwise SubAdv subs
          (subs.map fun p => (p.1, max p.2 (st.answers p.1).length)) := by
        refine ⟨by simp, fun m x y hx hy => ?_⟩
        rw [List.getElem?_map, hx] at hy
        cases hy
        exact ⟨rfl, Nat.le_max_left _ _⟩
      refine .copy hpw fun n m j pos hm hp hn => ?_
      exact behind_lt n hpw m (j, pos) _ hm (by rw [List.getElem?_map, hm]; rfl) hp
        (hn.trans (Nat.le_max_right _ _))
    · split
      · next hnone =>
        refine .copy (Pointwise.refl (fun _ => ⟨rfl, Nat.le_refl _⟩) _)
          fun n m j pos hm hp hn => ?_
        have h := leastBy_none hnone ((j, pos), m) (List.mem_zipIdx_iff_getElem?.2 hm)
        have h' : ¬ pos < (st.answers j).length := by simpa using h
        exact absurd (Nat.lt_of_lt_of_le hp hn) h'
      · next p hp =>
        simp only [Cost.bind_val, Cost.pure_val]
        have hq0 : subs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 (mem_of_leastBy hp)
        refine .copy (pointwise_modify (fun _ => ⟨rfl, Nat.le_refl _⟩) _ _ _
          fun x _ => ⟨rfl, Nat.le_succ _⟩) fun n m j pos hm hpos hn => ?_
        have hle : p.1.2 ≤ pos := leastBy_le hp ((j, pos), m)
          (List.mem_zipIdx_iff_getElem?.2 hm) (by
            simp only [decide_eq_true_eq]
            exact Nat.lt_of_lt_of_le hpos hn)
        exact sum_map_modify_lt (fun q : Nat × Nat => n - q.2) _ subs p.2 p.1 hq0
          (by simp only; omega)
  | join k a b c =>
    have hc := hok k a b c rfl
    simp only [work]
    split
    · simp only [Cost.bind_val, Cost.pure_val]
      have hs := (Cursor.all_spec (st.answers a).length (st.answers b).length
        ((st.answers a).length * (st.answers b).length + 1) c hc).2.1
      refine .join hs fun p q n hp hq hpn hqn => ?_
      by_cases hb : c.Before p q
      · exact .inl (hs p q hb)
      · exact Cursor.all_rank _ _ p q n hp hq hpn hqn _ c hc hb
    · have hn := (Cursor.next_spec (st.answers a).length (st.answers b).length
        (c.room (st.answers a).length (st.answers b).length) c hc).2.1
      have hr := fun p q n hp hq hpn hqn hb =>
        Cursor.next_rank (st.answers a).length (st.answers b).length p q n hp hq hpn hqn
          (c.room (st.answers a).length (st.answers b).length) c hc (Nat.le_refl _) hb
      split
      · next c' hx =>
        rw [hx] at hn hr
        refine .join hn fun p q n hp hq hpn hqn => ?_
        by_cases hb : c.Before p q
        · exact .inl (hn p q hb)
        · exact hr p q n hp hq hpn hqn hb
      · next pr c' hx =>
        rw [hx] at hn hr
        simp only [Cost.bind_val, Cost.pure_val]
        refine .join hn fun p q n hp hq hpn hqn => ?_
        by_cases hb : c.Before p q
        · exact .inl (hn p q hb)
        · exact hr p q n hp hq hpn hqn hb
  | push k left side other todo subs =>
    simp only [work]
    split
    · exact .push
    · split
      · cases todo <;>
        · erw [Cost.bind_val]
          simp only [Cost.bind_val, Cost.pure_val]
          exact .push
      · split
        · simp only [Cost.bind_val, Cost.pure_val]
          exact .push
        · simp only [Cost.bind_val, Cost.pure_val]
          exact .push
        · split
          · exact .push
          · simp only [Cost.bind_val, Cost.pure_val]
            exact .push
  | check left side other c =>
    cases c with
    | reading =>
      simp only [work, Cost.bind_val]
      split
      · next heq => exact .check (.inl rfl) fun _ => .inr (Nat.le_of_eq (hedge left side heq).symm)
      · exact .check (.inl rfl) fun _ => .inl (fun h => by cases h)
      · simp only [Cost.bind_val, Cost.pure_val]
        exact .check (.inl rfl) fun _ => .inl (fun h => by cases h)
    | off => exact .check (.inr rfl) (fun h => by cases h)
    | opened subs => exact .check (.inr rfl) (fun h => by cases h)

/-! ## The shape of the groups a goal begins with -/

theorem lead_splitGroup (k : Kind) (L Rg : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    ∃ s ∈ (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.2.strats,
      s.lead = true := by
  at_cost K hK
  simp only [splitGroup, Cost.bind_val, Cost.pure_val]
  exact ⟨_, List.mem_cons_self, rfl⟩

/-- A chain goal has a group for each of its splits, and it has a split. -/
theorem lead_chainGroups (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (hn : Normal g.node) {xs : List Rel} (hvc : g.node.view = .chain xs) :
    (∀ gr ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1,
      ∃ s ∈ gr.strats, s.lead = true) ∧
    (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1 ≠ [] := by
  have h2 := (hn.view_chain hvc).1
  have hsp := hn.chain_split hvc (i := 1) (by omega) (by omega)
  have hlead := fun k L Rg st => lead_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  have key : (∀ gr ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1,
      ∃ s ∈ gr.strats, s.lead = true) ∧
      (1 ∈ (List.range xs.length).drop 1 →
        (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1 ≠ []) := by
    at_cost K hK
    refine foldL_done (fun done (acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) ×
        List (Strat Rel (Ans D P))) =>
      (∀ gr ∈ acc.2.1, ∃ s ∈ gr.strats, s.lead = true) ∧ (1 ∈ done → acc.2.1 ≠ []))
      _ _ (fun done b i _ hb => ?_) (st, [], []) ⟨(fun gr hgr => by cases hgr), fun h => by cases h⟩
    simp only [Cost.bind_val]
    split
    · next l r hl hr =>
      simp only [Cost.bind_val, Cost.pure_val]
      refine ⟨fun gr hgr => ?_, fun _ => by simp⟩
      rcases List.mem_append.1 hgr with hgr | hgr
      · exact hb.1 gr hgr
      · obtain rfl := List.mem_singleton.1 hgr
        exact hlead _ _ _ _
    · next hno =>
      refine ⟨hb.1, fun h1 => ?_⟩
      rcases List.mem_append.1 h1 with h1 | h1
      · exact hb.2 h1
      · obtain rfl := List.mem_singleton.1 h1
        obtain ⟨-, l, r, hl, hr, -⟩ := hsp
        exact absurd hr (hno l r hl)
  refine ⟨key.1, key.2 ?_⟩
  rw [List.mem_drop_iff_getElem]
  exact ⟨0, by simp; omega, by simp⟩

/-- **The groups a goal begins with are shaped**: one of them has a span, a
call, a union or a join, and only the last can be without one. -/
theorem shaped_expand (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) (hn : Normal g.node) :
    Shaped (expand (K := DerivationKernel.over D K hK P) g st).val.2 := by
  have hch := fun xs hvc => lead_chainGroups (K := K) (hK := hK) (P := P) g st hn (xs := xs) hvc
  have hlead := fun k L Rg st => lead_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  at_cost K hK
  simp only [expand, Cost.bind_val]
  have one : ∀ s : Strat Rel (Ans D P), s.lead = true → Shaped [(⟨0, [s]⟩ : Group Rel (Ans D P))] :=
    fun s hs => shaped_all (by simp) fun gr hgr => by
      obtain rfl := List.mem_singleton.1 hgr
      exact ⟨s, List.mem_singleton.2 rfl, hs⟩
  split
  · exact one _ rfl
  · simp only [Cost.bind_val]
    split
    · exact one _ rfl
    · simp only [Cost.bind_val, Cost.pure_val]
      exact one _ rfl
  · simp only [Cost.bind_val, Cost.pure_val]
    exact one _ rfl
  · next xs hv =>
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨h1, h2⟩ := hch xs (forget_chain hv)
    split
    · exact shaped_all h2 h1
    · exact shaped_snoc h2 h1 _
  · next xs hv =>
    have hvm := forget_meet hv
    have h2 := (hn.view_meet hvm).1
    have hsp := hn.meet_split hvm (i := 0) (by omega)
    refine shaped_of (c := 0 ∈ andSplits xs.length) ?_ ?_
    · refine foldL_done (fun done (acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P))) =>
        (∀ gr ∈ acc.2, ∃ s ∈ gr.strats, s.lead = true) ∧ (0 ∈ done → acc.2 ≠ []))
        _ _ (fun done b i _ hb => ?_) (st, []) ⟨(fun gr hgr => by cases hgr), fun h => by cases h⟩
      simp only [Cost.bind_val]
      split
      · next l r hl hr =>
        simp only [Cost.bind_val, Cost.pure_val]
        refine ⟨fun gr hgr => ?_, fun _ => by simp⟩
        rcases List.mem_append.1 hgr with hgr | hgr
        · exact hb.1 gr hgr
        · obtain rfl := List.mem_singleton.1 hgr
          exact hlead _ _ _ _
      · next hno =>
        refine ⟨hb.1, fun h1 => ?_⟩
        rcases List.mem_append.1 h1 with h1 | h1
        · exact hb.2 h1
        · obtain rfl := List.mem_singleton.1 h1
          obtain ⟨-, l, r, hl, hr, -⟩ := hsp
          exact absurd hr (hno l r hl)
    · unfold andSplits
      split
      · exact List.mem_singleton.2 rfl
      · exact List.mem_range.2 (by omega)

/-! ## The strategies of a group work -/

omit [DecidableEq R] in
theorem groupsAt_setGroup (st : StateOf R Rel (Ans D P)) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P)) :
    groupsAt (setGroup st i k f) i = (groupsAt st i).modify k f := by
  unfold groupsAt setGroup StateOf.modify
  cases ht : st.tables[i]? with
  | none => simp [ht]
  | some t => cases hg : t.groups <;> simp [ht, hg]

omit [DecidableEq R] in
/-- The work of a strategy leaves the groups of every table. -/
theorem Frame.groupsAt {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Frame j st st')
    {i : Nat} {t : Table R Rel (Ans D P)} (ht : st.tables[i]? = some t) :
    groupsAt st' i = groupsAt st i := by
  obtain ⟨t', ht', -, -, -, -, e5, -⟩ := h.2.1 i t ht
  simp only [Symmetric.groupsAt, ht, ht', e5]

omit [DecidableEq R] in
/-- A stretch of a run leaves the groups of a table in its round, if the
table is not the one the record leaves out. -/
theorem TurnsBut.groupsAt {st st' : StateOf R Rel (Ans D P)} (h : Turns st st') {i : Nat}
    (hb : Busy st i) : groupsAt st' i = groupsAt st i := by
  obtain ⟨t, ht, hs, -⟩ := hb
  obtain ⟨t', ht', -⟩ := h.keep.2.1 i t ht
  simp only [Symmetric.groupsAt, ht, ht',
    h.groups i t t' ht ht' (.inr ⟨(fun e => by cases e), .inl hs⟩)]

/-- What holds while the strategies of the group `k` of the table at `i`
work, from the state `st`, when those at the places `done` have worked. -/
structure StratsInv (st : StateOf R Rel (Ans D P)) (i : Nat) (g : GoalOf R Rel) (k : Nat)
    (done : List Nat) (X : StateOf R Rel (Ans D P)) : Prop where
  good : Good X
  goal : goalAt X i = some g
  busy : Busy X i
  turns : TurnsBut (some i) st X
  length : (groupsAt X i).length = (groupsAt st i).length
  others : ∀ k', k' ≠ k → (groupsAt X i)[k']? = (groupsAt st i)[k']?
  group : ∀ gr, (groupsAt st i)[k]? = some gr → ∃ gr', (groupsAt X i)[k]? = some gr' ∧
    GrAdv st.len gr gr' ∧ ∀ m ∈ done, ∀ s0 s, gr.strats[m]? = some s0 → gr'.strats[m]? = some s →
      SStep st.len st.depth X.depth s0 s

/-- **The strategies of a group work**: each has worked once, and nothing
else of the groups of the table has changed. -/
theorem turn_workStrats (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (whole : Bool) (i : Nat) (g : GoalOf R Rel)
    (k : Nat) (hg : goalAt st i = some g) (hb : Busy st i) :
    StratsInv st i g k (List.range (((groupsAt st i)[k]?.map (·.strats.length)).getD 0))
      (workStrats (K := DerivationKernel.over D K hK P) whole i g k st).val.1 := by
  have hstep := fun (st : StateOf R Rel (Ans D P)) hG j s hg hb hs =>
    good_workStep (K := K) (hK := hK) hL hR (st := st) hG whole i g k j s hg hb hs
  have hin := fun (st : StateOf R Rel (Ans D P)) s =>
    inner_work (K := K) (hK := hK) (P := P) whole i g st s
  have hsw := fun (st : StateOf R Rel (Ans D P)) s hok =>
    step_work (K := K) (hK := hK) (P := P) whole i g st s hok
  clear hR
  at_cost K hK
  simp only [workStrats]
  refine foldL_done (fun done (acc : StateOf R Rel (Ans D P) × Nat × Bool) =>
    StratsInv st i g k done acc.1) _ _ (fun done b j _ hI => ?_) (st, 0, false)
    ⟨hG, hg, hb, TurnsBut.refl _ _, rfl, fun _ _ => rfl, fun gr h =>
      ⟨gr, h, Pointwise.refl (SAdv.refl _) _, fun m hm => by cases hm⟩⟩
  split
  · next hnone =>
    refine ⟨hI.good, hI.goal, hI.busy, hI.turns, hI.length, hI.others, fun gr hgr => ?_⟩
    obtain ⟨gr', h1, h2, h3⟩ := hI.group gr hgr
    refine ⟨gr', h1, h2, fun m hm s0 s hs0 hs => ?_⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact h3 m hm s0 s hs0 hs
    · obtain rfl := List.mem_singleton.1 hm
      rw [h1] at hnone
      simp only [Option.bind_some] at hnone
      rw [hnone] at hs
      cases hs
  · next s hs =>
    simp only [Cost.bind_val, Cost.pure_val]
    change StratsInv st i g k (done ++ [j])
      (setGroup (work (K := DerivationKernel.over D _ hK P) whole i g b.1 s).val.1 i k
        (fun gr => { gr with
          strats := gr.strats.set j
            (work (K := DerivationKernel.over D _ hK P) whole i g b.1 s).val.2.1 }))
    have hkw : Keep b.1 (work (K := DerivationKernel.over D _ hK P) whole i g b.1 s).val.1 :=
      (hin b.1 s).frame.keep hI.busy.open
    have hks := keep_setGroup (work (K := DerivationKernel.over D _ hK P) whole i g b.1 s).val.1
      i k (fun gr => { gr with
        strats := gr.strats.set j
          (work (K := DerivationKernel.over D _ hK P) whole i g b.1 s).val.2.1 })
    obtain ⟨tb, htb, -, -⟩ := hI.busy
    have hga := (hin b.1 s).frame.groupsAt htb
    have hp := prog_of_groupsAt hI.good.prog hI.goal hs
    have hstepS := hsw b.1 s (fun k' a' b' c' e => by
      subst e
      dsimp only [Prog] at hp
      obtain ⟨L, Rg, -, -, -, hok, -⟩ := hp
      exact hok)
    have hS : Stable st b.1 := hI.turns.keep.stable
    have hstepS' := hstepS.mono hS.len_le (Nat.le_refl _) (Nat.le_refl _)
    refine ⟨hstep b.1 hI.good j s hI.goal hI.busy hs, (hkw.trans hks).stable.ext _ _ hI.goal,
      (hkw.trans hks).busy hI.busy, ?_, ?_, fun k' hk' => ?_, fun gr hgr => ?_⟩
    · exact hI.turns.trans ((((hin b.1 s).turns hI.busy.isOpen).weaken (some i)).trans
        (turnsBut_modify _ i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩) (hkw.busy hI.busy).open))
    · rw [groupsAt_setGroup, List.length_modify, hga]
      exact hI.length
    · simp only [groupsAt_setGroup, List.getElem?_modify, Ne.symm hk', ite_false, hga, id_map']
      exact hI.others k' hk'
    · obtain ⟨gr_a, h1, h2, h3⟩ := hI.group gr hgr
      have hsj : gr_a.strats[j]? = some s := by
        rw [h1] at hs
        exact hs
      refine ⟨{ gr_a with
          strats := gr_a.strats.set j
            (work (K := DerivationKernel.over D _ hK P) whole i g b.1 s).val.2.1 }, ?_,
        Pointwise.set h2 (fun x hx => (h2.2 j x s hx hsj).trans hstepS'.adv),
        fun m hm s0 s'' hs0 hs'' => ?_⟩
      · simp [groupsAt_setGroup, hga, h1]
      · simp only [List.getElem?_set] at hs''
        by_cases e : j = m
        · subst e
          simp only [ite_true] at hs''
          split at hs''
          · cases hs''
            exact SStep.after (h2.2 j s0 s hs0 hsj) hstepS' hI.turns.depth
          · cases hs''
        · simp only [e, ite_false] at hs''
          have hm' : m ∈ done := by
            rcases List.mem_append.1 hm with hm | hm
            · exact hm
            · exact absurd (List.mem_singleton.1 hm).symm e
          exact (h3 m hm' s0 s'' hs0 hs'').mono (fun _ => Nat.le_refl _) (Nat.le_refl _)
            (hin b.1 s).depth_le

/-! ## A group works -/

/-- What holds while the tables a group reads have their rounds, from the
state `st`, when those at `done` have had theirs. -/
structure FeedInv (st : StateOf R Rel (Ans D P)) (i : Nat) (g : GoalOf R Rel)
    (done : List Nat) (X : StateOf R Rel (Ans D P)) : Prop where
  good : Good X
  goal : goalAt X i = some g
  busy : Busy X i
  turns : Turns st X
  settled : ∀ h ∈ done, Settled X h

/-- The tables a group reads have their rounds, given what a round is known
to do while no more tables wait for one than `fuel`. -/
theorem turn_feedAll (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat) (g : GoalOf R Rel)
    (hg : goalAt st i = some g) (hb : Busy st i) (hw : (waiting st).length ≤ fuel) (d : Nat)
    (feeds : List Nat) :
    FeedInv st i g feeds
      (feedAll (K := DerivationKernel.over D K hK P) adv st d feeds).val.1 := by
  at_cost K hK
  simp only [feedAll]
  refine foldL_done (fun done (acc : StateOf R Rel (Ans D P) × Nat) =>
    FeedInv st i g done acc.1) _ _ (fun done b h _ hI => ?_) (st, d)
    ⟨hG, hg, hb, TurnsBut.refl _ _, fun _ h => by cases h⟩
  simp only [Cost.bind_val, Cost.pure_val]
  obtain ⟨ht, hs⟩ := hadv h b.1 hI.good ((waiting_le hI.turns.keep).trans hw)
  refine ⟨hadvG _ _ hI.good, ht.keep.stable.ext _ _ hI.goal, ht.keep.busy hI.busy,
    hI.turns.trans ht, fun h' hh' => ?_⟩
  rcases List.mem_append.1 hh' with hm | hm
  · exact ht.keep.settled (hI.settled h' hm)
  · obtain rfl := List.mem_singleton.1 hm
    exact hs

/-- **A group works**: each of its strategies has worked, the tables they
read need no round any more, and nothing else of the groups of the table has
changed. -/
theorem turn_workGroup (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (whole : Bool) (i : Nat) (g : GoalOf R Rel)
    (k : Nat) (hg : goalAt st i = some g) (hb : Busy st i) (hw : (waiting st).length ≤ fuel) :
    Good (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1 ∧
    goalAt (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1 i =
      some g ∧
    Busy (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1 i ∧
    TurnsBut (some i) st
      (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1 ∧
    (groupsAt (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1
      i).length = (groupsAt st i).length ∧
    (∀ k', k' ≠ k →
      (groupsAt (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1
        i)[k']? = (groupsAt st i)[k']?) ∧
    ∀ gr, (groupsAt st i)[k]? = some gr → ∃ gr',
      (groupsAt (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1
        i)[k]? = some gr' ∧
      GrStep st.len st.depth
        (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1.depth
        gr gr' ∧
      ∀ s ∈ gr'.strats,
        SFed (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k st).val.1 s := by
  have h1 := turn_workStrats (K := K) (hK := hK) hL hR hG whole i g k hg hb
  have h2 := fun X hGX hgX hbX hwX d feeds =>
    turn_feedAll (K := K) (hK := hK) (P := P) adv fuel hadvG hadv (st := X) hGX i g hgX hbX
      hwX d feeds
  clear hR
  at_cost K hK
  simp only [workGroup, Cost.bind_val, Cost.pure_val]
  generalize (workStrats (K := DerivationKernel.over D _ hK P) whole i g k st).val = r1 at h1 ⊢
  have h2' := h2 r1.1 h1.good h1.goal h1.busy ((waiting_le h1.turns.keep).trans hw) r1.2.1
    ((((groupsAt r1.1 i)[k]?.map (·.strats)).getD []).flatMap (Strat.feeds r1.1)).eraseDups
  generalize (feedAll (K := DerivationKernel.over D _ hK P) adv r1.1 r1.2.1
    ((((groupsAt r1.1 i)[k]?.map (·.strats)).getD []).flatMap
      (Strat.feeds r1.1)).eraseDups).val = r2 at h2' ⊢
  have hks := keep_setGroup r2.1 i k (fun gr => { gr with level := gr.level + r2.2 })
  have hg2 : groupsAt r2.1 i = groupsAt r1.1 i := h2'.turns.groupsAt h1.busy
  refine ⟨Good.setGroup h2'.good i k _ (fun _ _ _ s hs => .inl hs),
    hks.stable.ext _ _ h2'.goal, hks.busy h2'.busy, ?_, ?_, fun k' hk' => ?_, fun gr hgr => ?_⟩
  · exact h1.turns.trans ((h2'.turns.weaken (some i)).trans
      (turnsBut_modify _ i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩) h2'.busy.open))
  · rw [groupsAt_setGroup, List.length_modify, hg2]
    exact h1.length
  · simp only [groupsAt_setGroup, List.getElem?_modify, Ne.symm hk', ite_false, hg2, id_map']
    exact h1.others k' hk'
  · obtain ⟨gr1, e1, hadv1, hst⟩ := h1.group gr hgr
    have hn : ((groupsAt st i)[k]?.map (·.strats.length)).getD 0 = gr.strats.length := by
      rw [hgr]
      rfl
    refine ⟨{ gr1 with level := gr1.level + r2.2 }, by simp [groupsAt_setGroup, hg2, e1],
      ⟨hadv1.1, fun m s0 s hs0 hs => ?_⟩, fun s hs => ?_⟩
    · have hm : m ∈ List.range (((groupsAt st i)[k]?.map (·.strats.length)).getD 0) := by
        rw [hn]
        exact List.mem_range.2 (List.getElem?_eq_some_iff.1 hs0).1
      exact (hst m hm s0 s hs0 hs).mono (fun _ => Nat.le_refl _) (Nat.le_refl _)
        h2'.turns.depth
    · refine (sfed_of_feeds h2'.turns.keep.stable fun j hj => ?_).keep hks
      refine h2'.settled j (List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨s, ?_, hj⟩))
      rw [e1]
      exact hs

/-! ## The groups of one level work -/

/-- What holds during the round of the table at `i`, which began in the
state `st0` with the groups `gs0`. -/
structure LevelInv (st0 : StateOf R Rel (Ans D P)) (gs0 : List (Group Rel (Ans D P))) (i : Nat)
    (g : GoalOf R Rel) (X : StateOf R Rel (Ans D P)) : Prop where
  good : Good X
  goal : goalAt X i = some g
  busy : Busy X i
  turns : TurnsBut (some i) st0 X
  groups : Pointwise (GrAdv st0.len) gs0 (groupsAt X i)

/-- One of the groups has worked since the round began, and the tables it
reads need no round any more. -/
def Worked (st0 : StateOf R Rel (Ans D P)) (gs0 : List (Group Rel (Ans D P))) (i : Nat) (X : StateOf R Rel (Ans D P)) : Prop :=
  ∃ (k : Nat) (gr0 gr1 : Group Rel (Ans D P)), gs0[k]? = some gr0 ∧
    (groupsAt X i)[k]? = some gr1 ∧ GrStep st0.len st0.depth X.depth gr0 gr1 ∧
    ∀ s ∈ gr1.strats, SFed X s

theorem level_workGroup (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {st0 X : StateOf R Rel (Ans D P)} {gs0 : List (Group Rel (Ans D P))} (whole : Bool) (i : Nat)
    (g : GoalOf R Rel) (hI : LevelInv st0 gs0 i g X) (hw : (waiting st0).length ≤ fuel)
    (k : Nat) :
    LevelInv st0 gs0 i g (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k X).val.1 ∧
    (Worked st0 gs0 i X → Worked st0 gs0 i (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k X).val.1) ∧
    ((groupsAt X i)[k]? ≠ none → Worked st0 gs0 i (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k X).val.1) := by
  obtain ⟨hG', hg', hb', ht, hlen, hoth, hgrp⟩ := turn_workGroup (K := K) (hK := hK) hL hR adv
    fuel hadvG hadv hI.good whole i g k hI.goal hI.busy ((waiting_le hI.turns.keep).trans hw)
  generalize (workGroup (K := DerivationKernel.over D K hK P) adv whole i g k X).val.1 = X' at *
  have hS : Stable st0 X := hI.turns.keep.stable
  have stepK : ∀ gr0 grX, gs0[k]? = some gr0 → (groupsAt X i)[k]? = some grX →
      ∃ gr', (groupsAt X' i)[k]? = some gr' ∧ GrStep st0.len st0.depth X'.depth gr0 gr' ∧
        ∀ s ∈ gr'.strats, SFed X' s := by
    intro gr0 grX h0 hX
    obtain ⟨gr', e, hstp, hf⟩ := hgrp grX hX
    have h1 : Pointwise (SAdv st0.len) gr0.strats grX.strats := hI.groups.2 k gr0 grX h0 hX
    have h2 : Pointwise (SStep X.len X.depth X'.depth) grX.strats gr'.strats := hstp
    have h3 : Pointwise (SStep st0.len st0.depth X'.depth) gr0.strats gr'.strats :=
      Pointwise.comp (r₁ := SAdv st0.len) (r₂ := SStep X.len X.depth X'.depth)
        (r₃ := SStep st0.len st0.depth X'.depth) (fun a b c h1 h2 =>
        SStep.after h1 (h2.mono hS.len_le (Nat.le_refl _) (Nat.le_refl _)) hI.turns.depth) h1 h2
    exact ⟨gr', e, h3, hf⟩
  refine ⟨⟨hG', hg', hb', hI.turns.trans ht, hI.groups.1.trans hlen.symm,
    fun m gr0 gr' h0 h' => ?_⟩, ?_, ?_⟩
  · by_cases e : m = k
    · subst e
      obtain ⟨grX, hX, -⟩ := hI.groups.get h0
      obtain ⟨gr'', e', hstp, -⟩ := stepK gr0 grX h0 hX
      rw [h'] at e'
      cases e'
      exact hstp.imp fun _ _ h => h.adv
    · rw [hoth m e] at h'
      exact hI.groups.2 m gr0 gr' h0 h'
  · rintro ⟨k0, gr0, gr1, e0, e1, hst, hf⟩
    by_cases e : k0 = k
    · subst e
      obtain ⟨gr', e', hstp, hf'⟩ := stepK gr0 gr1 e0 e1
      exact ⟨k0, gr0, gr', e0, e', hstp, hf'⟩
    · exact ⟨k0, gr0, gr1, e0, by rw [hoth k0 e]; exact e1,
        hst.imp fun _ _ h => h.mono (fun _ => Nat.le_refl _) (Nat.le_refl _) ht.depth,
        fun s hs => (hf s hs).keep ht.keep⟩
  · intro hne
    cases hX : (groupsAt X i)[k]? with
    | none => exact absurd hX hne
    | some grX =>
      obtain ⟨gr0, h0, -⟩ := hI.groups.get' hX
      obtain ⟨gr', e', hstp, hf'⟩ := stepK gr0 grX h0 hX
      exact ⟨k, gr0, gr', h0, e', hstp, hf'⟩

/-- **The groups of one level work**: what holds during the round still
does, a group that had worked still has, and if a group stands at the level
one has worked. -/
theorem level_workLevel (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {st0 X : StateOf R Rel (Ans D P)} {gs0 : List (Group Rel (Ans D P))} (whole : Bool) (i : Nat)
    (g : GoalOf R Rel) (hI : LevelInv st0 gs0 i g X) (hw : (waiting st0).length ≤ fuel)
    (lv : Nat) :
    LevelInv st0 gs0 i g (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv X).val.1 ∧
    (Worked st0 gs0 i X → Worked st0 gs0 i (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv X).val.1) ∧
    ((∃ (k : Nat) (gr : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr ∧ gr.level = lv) →
      Worked st0 gs0 i (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv X).val.1) := by
  have hgl := fun (Y : StateOf R Rel (Ans D P)) hY k =>
    level_workGroup (K := K) (hK := hK) hL hR adv fuel hadvG hadv (st0 := st0) (gs0 := gs0)
      (X := Y) whole i g hY hw k
  have key : LevelInv st0 gs0 i g (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv X).val.1 ∧
      (Worked st0 gs0 i X → Worked st0 gs0 i (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv X).val.1) ∧
      ∀ p ∈ (groupsAt X i).zipIdx, p.1.level = lv → Worked st0 gs0 i (workLevel (K := DerivationKernel.over D K hK P) adv whole i g lv X).val.1 := by
    clear hR
    at_cost K hK
    refine foldL_done (fun done (acc : StateOf R Rel (Ans D P) × Bool) =>
      LevelInv st0 gs0 i g acc.1 ∧ (Worked st0 gs0 i X → Worked st0 gs0 i acc.1) ∧
        ∀ p ∈ done, (p : Group Rel (Ans D P) × Nat).1.level = lv → Worked st0 gs0 i acc.1)
      _ _ (fun done b p hp hI' => ?_) (X, false) ⟨hI, id, fun _ h => by cases h⟩
    split
    · next hlv =>
      simp only [Cost.bind_val, Cost.pure_val]
      obtain ⟨a, b', c⟩ := hgl b.1 hI'.1 p.2
      refine ⟨a, fun h => b' (hI'.2.1 h), fun q hq hq' => ?_⟩
      rcases List.mem_append.1 hq with hq | hq
      · exact b' (hI'.2.2 q hq hq')
      · refine c fun hn => ?_
        have h1 : (groupsAt X i)[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hp
        have h2 := (List.getElem?_eq_some_iff.1 h1).1
        have h3 := hI.groups.1
        have h4 := hI'.1.groups.1
        have h5 := List.getElem?_eq_none_iff.1 hn
        omega
    · next hlv =>
      refine ⟨hI'.1, hI'.2.1, fun q hq hq' => ?_⟩
      rcases List.mem_append.1 hq with hq | hq
      · exact hI'.2.2 q hq hq'
      · obtain rfl := List.mem_singleton.1 hq
        exact absurd hq' hlv
  refine ⟨key.1, key.2.1, ?_⟩
  rintro ⟨k, gr, hk, hlv⟩
  exact key.2.2 (gr, k) (List.mem_zipIdx_iff_getElem?.2 hk) hlv

/-! ## A round -/

omit [DecidableEq R] in
theorem groupsAt_mapGroups (st : StateOf R Rel (Ans D P)) (i : Nat)
    (F : List (Group Rel (Ans D P)) → List (Group Rel (Ans D P))) (hF : F [] = []) :
    groupsAt (st.modify i fun t => { t with groups := t.groups.map F }) i = F (groupsAt st i) := by
  unfold groupsAt StateOf.modify
  cases ht : st.tables[i]? with
  | none => simp [ht, hF]
  | some t => cases hg : t.groups <;> simp [ht, hg, hF]

/-- **Before a round**: the table is stamped, and its groups are those it
had, or shaped if it had none. -/
theorem turn_prepare (hR : ReadOk D P K hK) (hP : ProgFO P) {st : StateOf R Rel (Ans D P)}
    (hG : Good st) (i : Nat) (t : Table R Rel (Ans D P)) (ht : st.tables[i]? = some t)
    (hd : t.done = false) :
    Good (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
    goalAt (prepare (K := DerivationKernel.over D K hK P) i t st).val i = some t.goal ∧
    Busy (prepare (K := DerivationKernel.over D K hK P) i t st).val i ∧
    TurnsBut (some i) st (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
    (∀ gs, t.groups = some gs →
      groupsAt (prepare (K := DerivationKernel.over D K hK P) i t st).val i = gs) ∧
    (t.groups = none →
      Shaped (groupsAt (prepare (K := DerivationKernel.over D K hK P) i t st).val i)) := by
  have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
  obtain ⟨hk, hb⟩ := keep_prepare (K := K) (hK := hK) (P := P) i t st ht hd
  refine ⟨good_prepare hR hP hG i t ht hd, hk.stable.ext _ _ hg, hb, ?_⟩
  have hopen : ∀ t', st.tables[i]? = some t' → t'.done = false := fun t' h => by
    rw [ht] at h; cases h; exact hd
  have hexp := inner_expand (K := K) (hK := hK) (P := P) (w := i) t.goal st
  have hT := (hexp.turns ⟨t, ht, hd⟩).weaken (some i)
  have hfr := hexp.frame
  have hsh := shaped_expand (K := K) (hK := hK) (P := P) t.goal st (hG.inv.core i t ht).1
  clear hR hk hb
  at_cost K hK
  unfold prepare
  cases hgs : t.groups with
  | some gs =>
    simp only [Cost.pure_val, Cost.bind_val]
    refine ⟨turnsBut_modify st i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inr rfl⟩) hopen,
      fun gs' e => ?_, fun e => by cases e⟩
    cases e
    unfold groupsAt StateOf.modify
    simp [ht, hgs]
  | none =>
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨t1, ht1, -, d1, -⟩ := hfr.2.1 i t ht
    generalize (expand (K := DerivationKernel.over D _ hK P) t.goal st).val = e at *
    have h2 : (e.1.modify i fun t' => { t' with groups := some e.2 }).tables[i]? =
        some { t1 with groups := some e.2 } := by
      unfold StateOf.modify
      simp [ht1]
    refine ⟨hT.trans ((turnsBut_modify e.1 i (fun t' => { t' with groups := some e.2 }) (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩)
        (fun t' h => by rw [ht1] at h; cases h; exact d1.trans hd)).trans
      (turnsBut_modify (e.1.modify i fun t' => { t' with groups := some e.2 }) i
        (fun t => { t with stamp := (e.1.modify i fun t' => { t' with groups := some e.2 }).round,
                           delta := 0 }) (fun _ => ⟨rfl, rfl, rfl, rfl, .inr rfl⟩)
        (fun t' h => by rw [h2] at h; cases h; exact d1.trans hd))),
      (fun gs' e' => by cases e'), fun _ => ?_⟩
    have : groupsAt ((e.1.modify i fun t' => { t' with groups := some e.2 }).modify i
        fun t => { t with stamp := (e.1.modify i fun t' => { t' with groups := some e.2 }).round,
                          delta := 0 }) i = e.2 := by
      unfold groupsAt StateOf.modify
      simp [ht1]
    rw [this]
    exact hsh

omit [DecidableEq R] in
/-- **The end of a round**: the groups with nothing left are removed, and
the table may be marked complete. The record of the whole round. -/
theorem turns_finish {st stp X Y : StateOf R Rel (Ans D P)} {i : Nat} {g : GoalOf R Rel}
    {t : Table R Rel (Ans D P)} {gs0 : List (Group Rel (Ans D P))}
    (ht : st.tables[i]? = some t) (hs : t.stamp ≠ st.round) (hd : t.done = false)
    (hbn : t.born ≠ st.round) (T1 : TurnsBut (some i) st stp) (hp1 : ∀ gs, t.groups = some gs → gs0 = gs)
    (hp2 : t.groups = none → Shaped gs0) (LI : LevelInv stp gs0 i g X)
    (hW : gs0 ≠ [] → Worked stp gs0 i X)
    (hY : Y = X.modify i (fun t =>
      { t with groups := t.groups.map (fun gs => gs.filter (fun gr => !gr.strats.all (Strat.dead X))) }))
    (fin : Bool) (d : Nat)
    (hfin : fin = true → ∃ gr ∈ groupsAt Y i, ∃ s ∈ gr.strats, s.quiet Y Y.isDone = true) :
    Turns st (Y.modify i (fun t => { t with done := t.done || fin, delta := d })) ∧
    Settled (Y.modify i (fun t => { t with done := t.done || fin, delta := d })) i := by
  have hgY : groupsAt Y i =
      (groupsAt X i).filter (fun gr => !gr.strats.all (Strat.dead X)) := by
    rw [hY]
    exact groupsAt_mapGroups X i _ rfl
  have T3 : TurnsBut (some i) X Y := by
    rw [hY]
    exact turnsBut_modify X i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩) LI.busy.open
  clear hY
  have T : TurnsBut (some i) st Y := T1.trans (LI.turns.trans T3)
  obtain ⟨u, hu, hsu, hdu⟩ := T3.keep.busy LI.busy
  have hSYZ : Stable Y (Y.modify i fun t => { t with done := t.done || fin, delta := d }) :=
    stable_modify Y i _ fun _ _ => ⟨rfl, rfl, rfl, fun h => by simp [h]⟩
  have hsetYZ : ∀ j, Settled Y j →
      Settled (Y.modify i fun t => { t with done := t.done || fin, delta := d }) j := by
    intro j hj t' ht'
    rcases getElem?_modify_cases Y i _ ht' with ⟨-, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact hj t' h'
    · rcases hj v hv with h | h | h
      · exact .inl (by simp [h])
      · exact .inr (.inl h)
      · exact .inr (.inr h)
  have hrY : Y.round = st.round := T.keep.1
  refine ⟨⟨keep_mark T.keep ht hs hd _ (fun t'' => ⟨rfl, rfl, rfl, rfl, fun h => by simp [h]⟩),
    T.depth, fun h k t' hk => ?_, fun k ta tz ha hz hyp => ?_, fun k tz hz hdz => ?_,
    fun k ta tz _ ha hz hs' hs'' => ?_, fun k tz _ hz hbz hyp => ?_⟩, fun t' ht' => ?_⟩
  · rcases getElem?_modify_cases Y i _ hk with ⟨-, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact T.stamp h k t' h'
    · exact T.stamp h k v hv
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact T.groups k ta tz ha h' (hyp.imp id fun hh => ⟨fun e => hne (Option.some.inj e), hh.2⟩)
    · rw [ht] at ha
      cases ha
      rw [hu] at hv
      cases hv
      rcases hyp with h | ⟨-, h | h⟩
      · rw [hd] at h; cases h
      · exact absurd h hs
      · exact absurd (hsu.trans hrY) h
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · rcases T.done k tz h' hdz with h | hq
      · exact .inl h
      · exact .inr (hq.mono hSYZ rfl)
    · rw [hu] at hv
      cases hv
      simp only [hdu, Bool.false_or] at hdz
      obtain ⟨gr, hgr, s, hs1, hq⟩ := hfin hdz
      refine .inr ?_
      simp only [groupsAt, hu] at hgr
      cases hgu : u.groups with
      | none => rw [hgu] at hgr; simp at hgr
      | some gs =>
        rw [hgu] at hgr
        exact ⟨gs, rfl, gr, hgr, s, hs1,
          quiet_mono (fun _ => hSYZ.isDone) (fun _ => hSYZ.isDone) hq⟩
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact (T.turn k ta tz (fun e => hne (Option.some.inj e)) ha h' hs' hs'').finish hSYZ hsetYZ
        (Nat.le_refl _)
    · rw [ht] at ha
      cases ha
      rw [hu] at hv
      cases hv
      have hSXZ : Stable X (Y.modify k fun t => { t with done := t.done || fin, delta := d }) :=
        T3.keep.stable.trans hSYZ
      refine Turn.start T1.keep.stable T1.depth ⟨gs0, groupsAt X k,
        (fun gr => !gr.strats.all (Strat.dead X)), fun gs h => (hp1 gs h).symm, hp2, ?_, ?_, ?_⟩
      · rw [← hgY]
        simp only [groupsAt, hu]
      · refine LI.groups.imp fun gr0 gr1 hadv => ⟨hadv, fun hp => ?_, fun hp s1 hs1 => ?_⟩
        · simp only [Bool.not_eq_true', List.all_eq_false] at hp
          obtain ⟨s1, hs1, hdead⟩ := hp
          obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hs1
          obtain ⟨s0, hs0, hsa⟩ := Pointwise.get' hadv (List.getElem?_eq_getElem hm)
          refine ⟨s0, List.mem_of_getElem? hs0, ?_⟩
          cases hx : s0.dead stp with
          | false => rfl
          | true => exact absurd (dead_adv hsa LI.turns.keep.stable.answers hx) hdead
        · simp only [Bool.not_eq_false', List.all_eq_true] at hp
          exact hSXZ.dead (hp s1 hs1)
      · by_cases he : gs0 = []
        · exact .inl he
        · obtain ⟨k, gr0, gr1, e0, e1, hst, hf⟩ := hW he
          exact .inr ⟨k, gr0, gr1, e0, e1,
            hst.imp fun _ _ h => h.mono (fun _ => Nat.le_refl _) (Nat.le_refl _) T3.depth,
            fun s hs1 => (hf s hs1).mono hSXZ fun j hj => hsetYZ j (T3.keep.settled hj)⟩
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact T.young k tz (fun e => hne (Option.some.inj e)) h' hbz hyp
    · obtain ⟨v', hv', -, e2, -⟩ := T.keep.2.1 k t ht
      rw [hv] at hv'
      cases hv'
      exact absurd (e2.symm.trans (hbz.trans hrY)) hbn
  · rcases getElem?_modify_cases Y i _ ht' with ⟨hne, -⟩ | ⟨-, v, hv, rfl⟩
    · exact absurd rfl hne
    · rw [hu] at hv
      cases hv
      exact .inr (.inl hsu)

/-- **The record of a round**: over the round of a table, with every round
nested in it, the record holds, and the table needs no round any more. -/
theorem turns_advance (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) (hP : ProgFO P) :
    ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)), Good st → (waiting st).length ≤ fuel →
      Turns st (advance (K := DerivationKernel.over D K hK P) fuel i st).val.1 ∧
      Settled (advance (K := DerivationKernel.over D K hK P) fuel i st).val.1 i
  | 0, i, st, _, hw => by
    clear hR
    at_cost K hK
    show Turns st st ∧ Settled st i
    refine ⟨TurnsBut.refl _ _, settled_of_not_waiting ?_⟩
    have : waiting st = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hw)
    rw [this]
    exact List.not_mem_nil
  | fuel + 1, i, st, hG, hw => by
    have ih := fun h st hG hw => turns_advance hL hR hP fuel h st hG hw
    have ihG := fun h st => good_advance (K := K) (hK := hK) hL hR hP fuel h st
    have hprep := fun t ht hd => turn_prepare (K := K) (hK := hK) hR hP hG i t ht hd
    have hlev := fun whole g lv (st0 : StateOf R Rel (Ans D P)) gs0 X hI hw =>
      level_workLevel (K := K) (hK := hK) hL hR _ fuel ihG ih (st0 := st0) (X := X) (gs0 := gs0)
        whole i g hI hw lv
    clear hR
    at_cost K hK
    simp only [advance]
    split
    · next hnone =>
      exact ⟨TurnsBut.refl _ _, fun t (ht : st.tables[i]? = some t) => by
        rw [hnone] at ht; cases ht⟩
    · next t ht =>
      split
      · next hd =>
        exact ⟨TurnsBut.refl _ _, fun t' (ht' : st.tables[i]? = some t') => by
          rw [ht] at ht'; cases ht'; exact .inl hd⟩
      · next hd =>
        split
        · next hs =>
          exact ⟨TurnsBut.refl _ _, fun t' (ht' : st.tables[i]? = some t') => by
            rw [ht] at ht'; cases ht'; exact .inr (.inl hs)⟩
        · next hs =>
          split
          · next hb =>
            exact ⟨TurnsBut.refl _ _, fun t' (ht' : st.tables[i]? = some t') => by
              rw [ht] at ht'; cases ht'; exact .inr (.inr hb)⟩
          · next hb =>
            simp only [Cost.bind_val, Cost.pure_val]
            have hd' : t.done = false := by simpa using hd
            obtain ⟨hGp, hgp, hbp, T1, hp1, hp2⟩ := hprep t ht hd'
            have hi : i ∈ waiting st := mem_waiting.2 ⟨t, ht, hd', hs, hb⟩
            have hwp : (waiting (prepare (K := DerivationKernel.over D _ hK P) i t st).val).length
                ≤ fuel := by
              have := waiting_lt (waiting_sub T1.keep) hi fun h => by
                obtain ⟨u, hu, -, hsu, -⟩ := mem_waiting.1 h
                obtain ⟨v, hv, hsv, -⟩ := hbp
                rw [hu] at hv
                cases hv
                exact hsu hsv
              omega
            generalize (prepare (K := DerivationKernel.over D _ hK P) i t st).val = stp at *
            have hmid := foldL_done (fun done (acc : StateOf R Rel (Ans D P) × Bool) =>
                LevelInv stp (groupsAt stp i) i t.goal acc.1 ∧ (done = [] → acc = (stp, false)) ∧
                  (done ≠ [] → Worked stp (groupsAt stp i) i acc.1))
              (fun (acc : StateOf R Rel (Ans D P) × Bool) lv =>
                if acc.2 then pure acc
                else workLevel (K := DerivationKernel.over D _ hK P)
                  (advance (K := DerivationKernel.over D _ hK P) fuel)
                  (decide ((groupsAt stp i).length ≤ 1)) i t.goal lv acc.1)
              (levelsOf (groupsAt stp i))
              (fun done b lv hlv hI => by
                split
                · next hb2 =>
                  refine ⟨hI.1, fun h => absurd h (by simp), fun _ => hI.2.2 fun hdn => ?_⟩
                  rw [hI.2.1 hdn] at hb2
                  cases hb2
                · obtain ⟨a, b', c⟩ := hlev (decide ((groupsAt stp i).length ≤ 1)) t.goal lv stp
                    (groupsAt stp i) b.1 hI.1 hwp
                  refine ⟨a, fun h => absurd h (by simp), fun _ => ?_⟩
                  by_cases hdn : done = []
                  · have hb1 : b.1 = stp := by rw [hI.2.1 hdn]
                    apply c
                    obtain ⟨gr, hgr, hl⟩ := mem_levelsOf hlv
                    obtain ⟨k, hk⟩ := List.getElem?_of_mem hgr
                    exact ⟨k, gr, by rw [hb1]; exact hk, hl⟩
                  · exact b' (hI.2.2 hdn))
              (stp, false)
              ⟨⟨hGp, hgp, hbp, TurnsBut.refl _ _, Pointwise.refl (fun gr =>
                  Pointwise.refl (SAdv.refl _) gr.strats) _⟩, fun _ => rfl, fun h => absurd rfl h⟩
            exact turns_finish ht hs hd' hb T1 hp1 hp2 hmid.1
              (fun hne => hmid.2.2 (levelsOf_ne_nil hne)) rfl _ _ (fun hfin => by
                obtain ⟨gr, hgr, h⟩ := List.any_eq_true.1 hfin
                obtain ⟨s, hs1, hq⟩ := List.any_eq_true.1 h
                exact ⟨gr, hgr, s, hs1, hq⟩)

/-- **The record of a request**: the root has its round, with every round
nested in it, and the tables that complete together are marked. -/
theorem req_request (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) (hP : ProgFO P)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (hD : Dated st) :
    Req st (request (K := DerivationKernel.over D K hK P) st).val.1 := by
  have h := fun (fuel : Nat) (st : StateOf R Rel (Ans D P)) hG hw =>
    turns_advance (K := K) (hK := hK) hL hR hP fuel 0 st hG hw
  clear hR
  at_cost K hK
  simp only [request, Cost.bind_val, Cost.pure_val]
  have h0 : Good ({ st with round := st.round + 1 } : StateOf R Rel (Ans D P)) :=
    hG.of_map (fun _ t => t) (fun j => by simp) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ h => h) rfl
  have hw : (waiting ({ st with round := st.round + 1 } : StateOf R Rel (Ans D P))).length ≤
      st.tables.length := by
    unfold waiting
    exact (List.length_filter_le _ _).trans (by simp)
  obtain ⟨T, hs⟩ := h st.tables.length _ h0 hw
  exact req_of_turns hD T hs _

end kernel

end Symmetric

end RwLog
