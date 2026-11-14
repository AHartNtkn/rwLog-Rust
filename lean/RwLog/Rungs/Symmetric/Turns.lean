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

`Turns` is transitive (`TurnsBut.trans`).
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

theorem SFed.keep {st st' : StateOf S N A} (h : Keep st st') {s : Strat N A}
    (hs : SFed st s) : SFed st' s := by
  cases s with
  | span _ => trivial
  | copy _ subs => exact fun p hp => h.settled (hs p hp)
  | join _ a b _ => exact ⟨h.settled hs.1, h.settled hs.2⟩
  | push _ _ _ _ _ _ => trivial
  | check _ _ _ c =>
    cases c with
    | reading => trivial
    | off => trivial
    | opened subs =>
      intro he j hj
      refine h.settled (hs (fun j' hj' => ?_) j hj)
      have := h.stable.answers j'
      rw [he j' hj'] at this
      exact List.prefix_nil.1 this

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
    ∀ (k : Nat) (gr : Group N A), gs[k]? = some gr →
      (∃ s ∈ gr.strats, s.lead = true) ∨ k + 1 = gs.length

/-- The groups of a table before its round (`go`, nothing if this is its
first) and after it (`go'`). -/
def Turn (st st' : StateOf S N A) (go go' : Option (List (Group N A))) : Prop :=
  ∃ (gs0 gs1 : List (Group N A)) (p : Group N A → Bool),
    (∀ gs, go = some gs → gs = gs0) ∧ (go = none → Shaped gs0) ∧ go' = some (gs1.filter p) ∧
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
theorem Turn.finish {a b c : StateOf S N A} (hK : Keep b c) (hd : b.depth ≤ c.depth)
    {go go' : Option (List (Group N A))} (h : Turn a b go go') : Turn a c go go' := by
  obtain ⟨gs0, gs1, p, h1, h2, h3, h4, h5⟩ := h
  have h4' := h4.imp (r' := fun gr0 gr1 => GrAdv a.len gr0 gr1 ∧
      (p gr1 = true → ∃ s ∈ gr0.strats, s.dead a = false) ∧
      (p gr1 = false → ∀ s ∈ gr1.strats, s.dead c = true)) fun gr0 gr1 hg =>
    ⟨hg.1, hg.2.1, fun hp s hs => hK.stable.dead (hg.2.2 hp s hs)⟩
  refine ⟨gs0, gs1, p, h1, h2, h3, h4', ?_⟩
  rcases h5 with h5 | ⟨k, gr0, gr1, e0, e1, hst, hf⟩
  · exact .inl h5
  · exact .inr ⟨k, gr0, gr1, e0, e1,
      hst.imp fun _ _ hs => hs.mono (fun _ => Nat.le_refl _) (Nat.le_refl _) hd,
      fun s hs => (hf s hs).keep hK⟩

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

/-- The record of a stretch of a run. -/
abbrev Turns (st st' : StateOf S N A) : Prop := TurnsBut none st st'

theorem TurnsBut.trans {x : Option Nat} {a b c : StateOf S N A} (h₁ : TurnsBut x a b)
    (h₂ : TurnsBut x b c) : TurnsBut x a c := by
  have hr : b.round = a.round := h₁.keep.1
  refine ⟨h₁.keep.trans h₂.keep, h₁.depth.trans h₂.depth, fun h => h₂.stamp (h₁.stamp h),
    fun k ta tc ha hc hyp => ?_, fun k tc hc hdc => ?_, fun k ta tc hx ha hc hs hs' => ?_⟩
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
      exact (h₁.turn k ta tb hx ha hb hs hsb).finish h₂.keep h₂.depth
    · have hg := h₁.groups k ta tb ha hb (.inr ⟨hx, .inr hsb⟩)
      rw [← hg]
      exact (h₂.turn k tb tc hx hb hc (by rw [hr]; exact hsb) (by rw [hr]; exact hs')).start
        h₁.keep.stable h₁.depth

theorem TurnsBut.refl (x : Option Nat) (st : StateOf S N A) : TurnsBut x st st :=
  ⟨Keep.refl st, Nat.le_refl _, fun h => h, (fun k t t' h h' _ => by rw [h] at h'; cases h'; rfl),
    fun k t' h hd => .inl ⟨t', h, hd⟩, fun k t t' _ h h' hs hs' => by
      rw [h] at h'; cases h'; exact absurd hs' hs⟩

/-- A record that says everything says what a record about a round says. -/
theorem TurnsBut.weaken {st st' : StateOf S N A} (h : Turns st st') (x : Option Nat) :
    TurnsBut x st st' :=
  ⟨h.keep, h.depth, h.stamp, fun k t t' ht ht' hyp => h.groups k t t' ht ht'
      (hyp.imp id fun hh => ⟨(fun e => by cases e), hh.2⟩),
    h.done, fun k t t' _ => h.turn k t t' (fun e => by cases e)⟩

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
    fun k t' hk hd => ?_, fun k t t' _ ht ht' hs hs' => ?_⟩
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

omit [DecidableEq R] in
/-- The record of a change to an open table that leaves its goal, its
answers and its marks. -/
theorem turnsBut_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hf : ∀ t, (f t).goal = t.goal ∧ (f t).born = t.born ∧ (f t).answers = t.answers ∧
      (f t).done = t.done ∧ (f t).stamp = t.stamp)
    (ho : ∀ t, st.tables[i]? = some t → t.done = false) :
    TurnsBut (some i) st (st.modify i f) := by
  refine ⟨keep_modify st i f fun t _ => ⟨(hf t).1, (hf t).2.1, (hf t).2.2.1,
      fun h => by rw [(hf t).2.2.2.1]; exact h,
      fun h => ⟨by rw [(hf t).2.2.2.2]; exact h, fun h => by rw [(hf t).2.2.2.1]; exact h⟩⟩,
    Nat.le_refl _, fun hs k t' hk => ?_, fun k t t' ht ht' hyp => ?_, fun k t' hk hd => ?_,
    fun k t t' hx ht ht' hs hs' => ?_⟩
  · rcases getElem?_modify_cases st i f hk with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
    · exact hs k t' h
    · rw [(hf t).2.2.2.2]
      exact hs k t ht
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

end kernel

end Symmetric

end RwLog
