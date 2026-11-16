/-
# What a request does for each table

The record of a stretch of a run, from one state to a later one (`Turns`).
It says what the completeness proof needs of the order in which the machine
works, and of the levels that choose the order only the balance of a round.

* `SAdv` relates a strategy to itself later: its kind and the tables it
  reads stay, and its cursors only move on. `SStep` is the same after the
  strategy has worked at least once: a span is tried; a call or a union is
  nearer to every answer of the tables it reads that was there at the start
  (`behind` falls); a join is nearer to every pair that was there at the
  start (`Cursor.rank` falls, or the pair is combined); a check that was
  still to be read is read, or the depth edges are read to has doubled from a
  depth below what the node needs (`need`, which every relation here takes
  first; for the machine it is `readNeed`, `ReadLive.lean`).
* `Settled st j`: the table at `j` needs no round in this request any more.
  `SFed st s`: the tables the strategy `s` reads are settled. `Fed st st' s`
  is what a group that worked from `st` to `st'` did for the tables `s`
  reads: they are settled, but of the members of a union one that was not
  settled had a round that cost something, and it had been fed no more than
  any member that is still not settled.
* `Turn st st' go go'` relates the groups of a table before its round to its
  groups after: the groups are the same ones, each strategy moved on, less
  the groups all of whose strategies are dead; one of the groups worked,
  and the tables it reads are fed (`Tried`); and the round is balanced
  (`Balanced`): no level fell, and each group worked, or stands as it stood
  while a group that stood lower rose. The levels are worked lowest first
  (`pairwise_levelsOf`), a level only if nothing was done at the lower ones,
  and a group did something exactly when its level rose (`workGroup_did`).
* `Turns st st'` is the record: what a round keeps (`Keep`); the groups of a
  table change in its own round only; every table that had its round has
  `Turn`; and every table that became complete has a strategy with nothing
  left to do that reads complete tables only (`QuietAt`).

`Turns` is transitive (`TurnsBut.trans`), and it is proved of the round of a
table with every round nested in it (`turns_advance`). The record of a whole
request is `Req` (`req_request`): the same, across the change of the number
of the request and the marking of the tables that complete together.

`Shaped` is the shape of the groups a goal begins with (`shaped_expand`):
one group has a span, a call, a union or a join, and a group that has none
is all interface checks. A round keeps the shape (`Turn.shaped`).
-/
import RwLog.Rungs.Symmetric.Kept
import RwLog.Rungs.Symmetric.ReadLive
import RwLog.Rungs.Symmetric.Cursor

namespace RwLog

namespace Symmetric

open Traverse Answer

/-- What the race of a goal means to the record of a run: what a final
verdict gives of answers of the table of the goal (`cov`), at which depths
the verdict for a goal is final (`final`), which goals have a race (`has`), and
what the ask for a goal at a depth costs (`cost`). -/
structure RaceSem (S N A : Type) where
  cov : GoalOf S N → List A → Prop
  final : GoalOf S N → Nat → Prop
  has : GoalOf S N → Bool
  cost : GoalOf S N → Nat → Nat

section pure

variable {S N A : Type} {need : N → Nat} {Rc : RaceSem S N A}

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

/-! ## A push goes on -/

/-- The answers a push has seen, later: those it had, each with the table
opened for it if it had one, filed at least as far; and maybe more. -/
def PushAdv (subs subs' : List (A × Option (Nat × Nat))) : Prop :=
  subs.length ≤ subs'.length ∧ ∀ (n : Nat) (e e' : A × Option (Nat × Nat)), subs[n]? = some e →
    subs'[n]? = some e' → e'.1 = e.1 ∧
      ∀ t, e.2 = some t → ∃ t', e'.2 = some t' ∧ t'.1 = t.1 ∧ t.2 ≤ t'.2

theorem PushAdv.refl (subs : List (A × Option (Nat × Nat))) : PushAdv subs subs :=
  ⟨Nat.le_refl _, fun _ _ _ h h' => by
    rw [h] at h'
    cases h'
    exact ⟨rfl, fun t ht => ⟨t, ht, rfl, Nat.le_refl _⟩⟩⟩

theorem PushAdv.trans {a b c : List (A × Option (Nat × Nat))} (h₁ : PushAdv a b)
    (h₂ : PushAdv b c) : PushAdv a c := by
  refine ⟨h₁.1.trans h₂.1, fun n e e'' he he'' => ?_⟩
  have hn := (List.getElem?_eq_some_iff.1 he).1
  have hb : n < b.length := Nat.lt_of_lt_of_le hn h₁.1
  obtain ⟨x1, x2⟩ := h₁.2 n e b[n] he (List.getElem?_eq_getElem hb)
  obtain ⟨y1, y2⟩ := h₂.2 n b[n] e'' (List.getElem?_eq_getElem hb) he''
  refine ⟨y1.trans x1, fun t ht => ?_⟩
  obtain ⟨t1, ht1, e1, l1⟩ := x2 t ht
  obtain ⟨t2, ht2, e2, l2⟩ := y2 t1 ht1
  exact ⟨t2, ht2, e2.trans e1, l1.trans l2⟩

/-- Opening the goal of an answer seen. -/
theorem PushAdv.set_open {subs : List (A × Option (Nat × Nat))} {n : Nat} {x : A}
    (hx : subs[n]? = some (x, none)) (o : Option (Nat × Nat)) :
    PushAdv subs (subs.set n (x, o)) := by
  refine ⟨by rw [List.length_set], fun m e e' he he' => ?_⟩
  by_cases en : n = m
  · subst en
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hx).1] at he'
    rw [hx] at he
    cases he
    cases he'
    exact ⟨rfl, fun t ht => by cases ht⟩
  · rw [List.getElem?_set_ne en, he] at he'
    cases he'
    exact ⟨rfl, fun t ht => ⟨t, ht, rfl, Nat.le_refl _⟩⟩

/-- An answer seen with its table is seen with that table later. -/
theorem PushAdv.get {subs subs' : List (A × Option (Nat × Nat))} (h : PushAdv subs subs')
    {n : Nat} {x : A} {t : Nat × Nat} (he : subs[n]? = some (x, some t)) :
    ∃ t', subs'[n]? = some (x, some t') ∧ t'.1 = t.1 ∧ t.2 ≤ t'.2 := by
  have hn : n < subs'.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 he).1 h.1
  obtain ⟨x1, x2⟩ := h.2 n _ subs'[n] he (List.getElem?_eq_getElem hn)
  obtain ⟨t', ht', e1, l1⟩ := x2 t rfl
  refine ⟨t', ?_, e1, l1⟩
  rw [List.getElem?_eq_getElem hn]
  exact congrArg some (Prod.ext x1 ht')

/-- A push, later: the answers it has seen, the answers superseded, which are
the same once they are known, the units filed, the units taken, and each
unit still to take, which is taken, or is of an answer superseded, or is
still to take, no further from its turn. -/
structure PAdv (subs : List (A × Option (Nat × Nat))) (dead : Option (List Nat))
    (reads : List (Nat × Option Nat)) (c : Cursor) (subs' : List (A × Option (Nat × Nat)))
    (dead' : Option (List Nat)) (reads' : List (Nat × Option Nat)) (c' : Cursor) : Prop where
  adv : PushAdv subs subs'
  fixed : ∀ d, dead = some d → dead' = some d
  pre : reads <+: reads'
  before : ∀ p q, c.Before p q → c'.Before p q
  rank : ∀ p q, (p, q) ∈ c.todo → c'.Before p q ∨ p ∈ dead'.getD [] ∨
    ((p, q) ∈ c'.todo ∧ (c'.rank p q = c.rank p q ∨ RankLt (c'.rank p q) (c.rank p q)))

theorem PAdv.refl (subs : List (A × Option (Nat × Nat))) (dead : Option (List Nat))
    (reads : List (Nat × Option Nat)) (c : Cursor) : PAdv subs dead reads c subs dead reads c :=
  ⟨PushAdv.refl _, fun _ h => h, List.prefix_rfl, fun _ _ h => h,
    fun _ _ h => .inr (.inr ⟨h, .inl rfl⟩)⟩

/-- An answer superseded stays so. -/
theorem PAdv.kills {subs subs' : List (A × Option (Nat × Nat))} {dead dead' : Option (List Nat)}
    {reads reads' : List (Nat × Option Nat)} {c c' : Cursor}
    (h : PAdv subs dead reads c subs' dead' reads' c') :
    ∀ s ∈ dead.getD [], s ∈ dead'.getD [] := by
  cases dead with
  | none => exact fun s hs => by cases hs
  | some d =>
    rw [h.fixed d rfl]
    exact fun s hs => hs

theorem PAdv.trans {subs subs1 subs2 : List (A × Option (Nat × Nat))}
    {dead dead1 dead2 : Option (List Nat)} {reads reads1 reads2 : List (Nat × Option Nat)}
    {c c1 c2 : Cursor} (h₁ : PAdv subs dead reads c subs1 dead1 reads1 c1)
    (h₂ : PAdv subs1 dead1 reads1 c1 subs2 dead2 reads2 c2) :
    PAdv subs dead reads c subs2 dead2 reads2 c2 := by
  refine ⟨h₁.adv.trans h₂.adv, fun d hd => h₂.fixed d (h₁.fixed d hd),
    h₁.pre.trans h₂.pre, fun p q h => h₂.before p q (h₁.before p q h), fun p q h => ?_⟩
  rcases h₁.rank p q h with h' | h' | ⟨h', hr⟩
  · exact .inl (h₂.before p q h')
  · exact .inr (.inl (h₂.kills p h'))
  · rcases h₂.rank p q h' with h'' | h'' | ⟨h'', hr'⟩
    · exact .inl h''
    · exact .inr (.inl h'')
    · refine .inr (.inr ⟨h'', ?_⟩)
      rcases hr with hr | hr
      · rw [← hr]
        exact hr'
      · rcases hr' with hr' | hr'
        · rw [hr']
          exact .inr hr
        · exact .inr (hr'.trans hr)

/-- A push that has worked: each unit that was still to take is taken, or is
of an answer superseded, or is nearer to its turn; every answer of the side
is seen; every answer of the table of an answer that is not superseded is
filed; and if the side was complete, the answers superseded are known. -/
structure PStep (len : Nat → Nat) (dn : Nat → Bool) (side : Nat)
    (subs : List (A × Option (Nat × Nat))) (c : Cursor)
    (subs' : List (A × Option (Nat × Nat))) (dead' : Option (List Nat)) (c' : Cursor) :
    Prop where
  rank : ∀ p q, (p, q) ∈ c.todo → c'.Before p q ∨ p ∈ dead'.getD [] ∨
    ((p, q) ∈ c'.todo ∧ RankLt (c'.rank p q) (c.rank p q))
  seen : len side ≤ subs'.length
  filed : ∀ (n : Nat) (x : A) (t : Nat × Nat), subs[n]? = some (x, some t) →
    n ∉ dead'.getD [] → ∃ t', subs'[n]? = some (x, some t') ∧ len t.1 ≤ t'.2
  sup : dn side = true → dead'.isSome = true

/-! ## A strategy later -/

/-- A strategy and itself later: its kind and the tables it reads are the
same, and its cursors have only moved on. -/
inductive SAdv : Strat N A → Strat N A → Prop
  | span {ran ran' : Bool} : (ran = true → ran' = true) → SAdv (.span ran) (.span ran')
  | copy {c : Bool} {subs subs' : List (Nat × Nat)} : Pointwise SubAdv subs subs' →
      SAdv (.copy c subs) (.copy c subs')
  | join {k : Kind} {a b : Nat} {c c' : Cursor} :
      (∀ p q, c.Before p q → c'.Before p q) →
      (∀ p q, p < c.pa.length → q < c.pb.length →
        c'.Before p q ∨ c'.rank p q = c.rank p q ∨ RankLt (c'.rank p q) (c.rank p q)) →
      (c.pa.length ≤ c'.pa.length ∧ c.pb.length ≤ c'.pb.length) →
      SAdv (.join k a b c) (.join k a b c')
  | push {k : Kind} {l : Bool} {side : Nat} {o : N} {subs subs' : List (A × Option (Nat × Nat))}
      {dead dead' : Option (List Nat)} {reads reads' : List (Nat × Option Nat)} {c c' : Cursor} :
      PAdv subs dead reads c subs' dead' reads' c' →
      SAdv (.push k l side o subs dead reads c fc) (.push k l side o subs' dead' reads' c' fc')
  | check {l : Bool} {side o : N} {c c' : Check} : (c = .reading ∨ c' = c) →
      SAdv (.check l side o c) (.check l side o c')

theorem SAdv.refl : ∀ s : Strat N A, SAdv s s
  | .span _ => .span id
  | .copy _ _ => .copy (Pointwise.refl (fun _ => ⟨rfl, Nat.le_refl _⟩) _)
  | .join _ _ _ _ => .join (fun _ _ h => h) (fun _ _ _ _ => .inr (.inl rfl))
      ⟨Nat.le_refl _, Nat.le_refl _⟩
  | .push _ _ _ _ _ _ _ _ _ => .push (PAdv.refl _ _ _ _)
  | .check _ _ _ _ => .check (.inr rfl)

theorem SubAdv.trans {a b c : Nat × Nat} (h₁ : SubAdv a b) (h₂ : SubAdv b c) : SubAdv a c :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem SAdv.trans {s s1 s2 : Strat N A} (h₁ : SAdv s s1)
    (h₂ : SAdv s1 s2) : SAdv s s2 := by
  cases h₁ with
  | span a =>
    cases h₂ with
    | span b => exact .span fun h => b (a h)
  | copy a =>
    cases h₂ with
    | copy b => exact .copy (Pointwise.comp (r₃ := SubAdv) (fun _ _ _ h h' => h.trans h') a b)
  | join a1 a2 a3 =>
    cases h₂ with
    | join b1 b2 b3 =>
      refine .join (fun p q h => b1 p q (a1 p q h)) (fun p q hp hq => ?_)
        ⟨a3.1.trans b3.1, a3.2.trans b3.2⟩
      rcases b2 p q (Nat.lt_of_lt_of_le hp a3.1) (Nat.lt_of_lt_of_le hq a3.2) with h | h | h
      · exact .inl h
      · rcases a2 p q hp hq with h' | h' | h'
        · exact .inl (b1 p q h')
        · exact .inr (.inl (h.trans h'))
        · rw [h]
          exact .inr (.inr h')
      · rcases a2 p q hp hq with h' | h' | h'
        · exact .inl (b1 p q h')
        · rw [h'] at h
          exact .inr (.inr h)
        · exact .inr (.inr (h.trans h'))
  | push a =>
    cases h₂ with
    | push b => exact .push (a.trans b)
  | check a =>
    cases h₂ with
    | check b =>
      rcases a with a | a
      · exact .check (.inl a)
      · rw [a] at b
        exact .check b

/-- A strategy and itself after it has worked at least once. `d` is the
depth edges were read to at the start, `d'` the depth at the end. -/
inductive SStep (need : N → Nat) (len : Nat → Nat) (dn : Nat → Bool) (d d' : Nat) :
    Strat N A → Strat N A → Prop
  | span {ran : Bool} : SStep need len dn d d' (.span ran) (.span true)
  | copy {c : Bool} {subs subs' : List (Nat × Nat)} : Pointwise SubAdv subs subs' →
      (∀ (n m j pos : Nat), subs[m]? = some (j, pos) → pos < n → n ≤ len j →
        behind n subs' < behind n subs) →
      SStep need len dn d d' (.copy c subs) (.copy c subs')
  | join {k : Kind} {a b : Nat} {c c' : Cursor} :
      (∀ p q, c.Before p q → c'.Before p q) →
      (∀ p q, p < c.pa.length → q < c.pb.length →
        c'.Before p q ∨ RankLt (c'.rank p q) (c.rank p q)) →
      (c.pa.length ≤ c'.pa.length ∧ c.pb.length ≤ c'.pb.length) →
      (len a ≤ c'.pa.length ∧ len b ≤ c'.pb.length) →
      (c'.Full (len a) (len b) ∨ ∃ p q, ¬ c.Before p q ∧ c'.Before p q) →
      SStep need len dn d d' (.join k a b c) (.join k a b c')
  | push {k : Kind} {l : Bool} {side : Nat} {o : N} {subs subs' : List (A × Option (Nat × Nat))}
      {dead dead' : Option (List Nat)} {reads reads' : List (Nat × Option Nat)} {c c' : Cursor} :
      PAdv subs dead reads c subs' dead' reads' c' → PStep len dn side subs c subs' dead' c' →
      SStep need len dn d d' (.push k l side o subs dead reads c fc)
        (.push k l side o subs' dead' reads' c' fc')
  | check {l : Bool} {side o : N} {c c' : Check} : (c = .reading ∨ c' = c) →
      (c = .reading → c' ≠ .reading ∨ (2 * d ≤ d' ∧ d < need side)) →
      SStep need len dn d d' (.check l side o c) (.check l side o c')

theorem SStep.adv {len : Nat → Nat} {dn : Nat → Bool} {d d' : Nat} {s s' : Strat N A}
    (h : SStep need len dn d d' s s') : SAdv s s' := by
  cases h with
  | span => exact .span fun _ => rfl
  | copy h _ => exact .copy h
  | join h1 h2 h3 _ _ =>
    exact .join h1 (fun p q hp hq => (h2 p q hp hq).elim .inl fun h => .inr (.inr h)) h3
  | push h _ => exact .push h
  | check h _ => exact .check h

theorem SStep.mono {len len' : Nat → Nat} {dn dn' : Nat → Bool} {d d' d0 d1 : Nat}
    (hl : ∀ j, len' j ≤ len j) (hdn : ∀ j, dn' j = true → dn j = true)
    (hd : d0 ≤ d) (hd' : d' ≤ d1) {s s' : Strat N A} (h : SStep need len dn d d' s s') :
    SStep need len' dn' d0 d1 s s' := by
  cases h with
  | span => exact .span
  | copy h1 h2 =>
    exact .copy h1 fun n m j pos hm hp hn => h2 n m j pos hm hp (hn.trans (hl j))
  | @join _ a b _ _ h1 h2 h3 h5 h4 =>
    exact .join h1 h2 h3 ⟨(hl a).trans h5.1, (hl b).trans h5.2⟩
      (h4.imp (fun h p q hp hq => h p q (Nat.lt_of_lt_of_le hp (hl a))
        (Nat.lt_of_lt_of_le hq (hl b))) id)
  | push h1 h2 =>
    exact .push h1 ⟨h2.rank, (hl _).trans h2.seen, fun n x t he hd => by
      obtain ⟨t', ht', hle⟩ := h2.filed n x t he hd
      exact ⟨t', ht', (hl _).trans hle⟩, fun h => h2.sup (hdn _ h)⟩
  | check h1 h2 => exact .check h1 fun hc => (h2 hc).imp id fun h => ⟨by omega, by omega⟩

/-- A strategy that has moved on and then worked has worked. -/
theorem SStep.after {len : Nat → Nat} {dn : Nat → Bool} {d d1 d2 : Nat} {s s1 s2 : Strat N A}
    (h₁ : SAdv s s1) (h₂ : SStep need len dn d1 d2 s1 s2) (hd : d ≤ d1) :
    SStep need len dn d d2 s s2 := by
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
  | join a1 a2 a3 =>
    cases h₂ with
    | join b1 b2 b3 b5 b4 =>
      refine .join (fun p q h => b1 p q (a1 p q h)) (fun p q hp hq => ?_)
        ⟨a3.1.trans b3.1, a3.2.trans b3.2⟩ b5
        (b4.imp id fun ⟨p, q, h1, h2⟩ => ⟨p, q, fun h => h1 (a1 p q h), h2⟩)
      rcases b2 p q (Nat.lt_of_lt_of_le hp a3.1) (Nat.lt_of_lt_of_le hq a3.2) with h | h
      · exact .inl h
      · rcases a2 p q hp hq with h' | h' | h'
        · exact .inl (b1 p q h')
        · rw [h'] at h
          exact .inr h
        · exact .inr (h.trans h')
  | push a =>
    cases h₂ with
    | push b1 b2 =>
      refine .push (a.trans b1) ⟨fun p q h => ?_, b2.seen, fun n x t he hd => ?_, b2.sup⟩
      · rcases a.rank p q h with h' | h' | ⟨h', hr⟩
        · exact .inl (b1.before p q h')
        · exact .inr (.inl (b1.kills p h'))
        · rcases b2.rank p q h' with h'' | h'' | ⟨h'', hr'⟩
          · exact .inl h''
          · exact .inr (.inl h'')
          · refine .inr (.inr ⟨h'', ?_⟩)
            rcases hr with hr | hr
            · rw [← hr]
              exact hr'
            · exact hr'.trans hr
      · obtain ⟨t1, ht1, e1, -⟩ := a.adv.get he
        obtain ⟨t2, ht2, hle⟩ := b2.filed n x t1 ht1 hd
        rw [e1] at hle
        exact ⟨t2, ht2, hle⟩
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
        · exact (b2 h1).imp id fun h => ⟨by omega, by omega⟩
        · rcases b1 with h | h
          · exact absurd h h1
          · rw [h]
            exact .inl h1

/-- A strategy that has worked and then moved on has worked. -/
theorem SStep.before {len : Nat → Nat} {dn : Nat → Bool} {d d' : Nat} {s s1 s2 : Strat N A}
    (h₁ : SStep need len dn d d' s s1) (h₂ : SAdv s1 s2) :
    SStep need len dn d d' s s2 := by
  cases h₁ with
  | span =>
    cases h₂ with
    | span b => rw [b rfl]; exact .span
  | copy a1 a2 =>
    cases h₂ with
    | copy b =>
      refine .copy (Pointwise.comp (r₃ := SubAdv) (fun _ _ _ h h' => h.trans h') a1 b)
        fun n m j pos hm hp hn => ?_
      have h3 := a2 n m j pos hm hp hn
      have h4 := behind_le n b
      omega
  | join a1 a2 a3 a5 a4 =>
    cases h₂ with
    | join b1 b2 b3 =>
      refine .join (fun p q h => b1 p q (a1 p q h)) (fun p q hp hq => ?_)
        ⟨a3.1.trans b3.1, a3.2.trans b3.2⟩ ⟨a5.1.trans b3.1, a5.2.trans b3.2⟩
        (a4.imp (fun h p q hp hq => b1 p q (h p q hp hq)) fun ⟨p, q, h1, h2⟩ =>
          ⟨p, q, h1, b1 p q h2⟩)
      rcases a2 p q hp hq with h | h
      · exact .inl (b1 p q h)
      · rcases b2 p q (Nat.lt_of_lt_of_le hp a3.1) (Nat.lt_of_lt_of_le hq a3.2) with h' | h' | h'
        · exact .inl h'
        · rw [h']
          exact .inr h
        · exact .inr (h'.trans h)
  | push a1 a2 =>
    cases h₂ with
    | push b =>
      refine .push (a1.trans b) ⟨fun p q h => ?_, a2.seen.trans b.adv.1, fun n x t he hd => ?_,
        fun h => ?_⟩
      rotate_right
      · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (a2.sup h)
        rw [b.fixed d hd]
        rfl
      · rcases a2.rank p q h with h' | h' | ⟨h', hr⟩
        · exact .inl (b.before p q h')
        · exact .inr (.inl (b.kills p h'))
        · rcases b.rank p q h' with h'' | h'' | ⟨h'', hr'⟩
          · exact .inl h''
          · exact .inr (.inl h'')
          · refine .inr (.inr ⟨h'', ?_⟩)
            rcases hr' with hr' | hr'
            · rw [hr']
              exact hr
            · exact hr'.trans hr
      · obtain ⟨t1, ht1, hle⟩ := a2.filed n x t he fun h => hd (b.kills n h)
        obtain ⟨t2, ht2, -, l2⟩ := b.adv.get ht1
        exact ⟨t2, ht2, hle.trans l2⟩
  | check a1 a2 =>
    cases h₂ with
    | check b =>
      rename_i c c1 c2
      refine .check ?_ fun hc => ?_
      · rcases a1 with a | a
        · exact .inl a
        · rcases b with b | b
          · by_cases hc : c = .reading
            · exact .inl hc
            · rw [a] at b
              exact .inl b
          · rw [b, a]
            exact .inr rfl
      · rcases a2 hc with h | h
        · rcases b with b | b
          · exact absurd b h
          · rw [b]
            exact .inl h
        · exact .inr h

/-- A dead strategy stays dead. -/
theorem dead_adv {s s' : Strat N A} (h : SAdv s s')
    {st st' : StateOf S N A} (hS : ∀ j, st.answers j <+: st'.answers j)
    (hd : s.dead st = true) : s'.dead st' = true := by
  cases h with
  | span _ => simp [Strat.dead] at hd
  | copy _ => simp [Strat.dead] at hd
  | join _ _ => simp [Strat.dead] at hd
  | push _ => simp [Strat.dead] at hd
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
  dead_adv (SAdv.refl s) h.answers hd

/-- A strategy with nothing left to do that reads only tables that pass, in
a state where the tables that pass are complete with the same answers, has
nothing left to do and reads complete tables only. -/
theorem quiet_mono' {st st' : StateOf S N A} {ok ok' : Nat → Bool} {s : Strat N A}
    (hd : ∀ k l side o subs dead reads c fc, s = .push k l side o subs dead reads c fc →
      st.isDone side = true → st'.isDone side = true ∧ st'.answers side = st.answers side)
    (hok : ∀ j, ok j = true → ok' j = true ∧ st'.answers j = st.answers j)
    (h : s.quiet st ok = true) : s.quiet st' ok' = true := by
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
  | push k l side o subs dead reads c fc =>
    simp only [Strat.quiet, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    obtain ⟨h1, ⟨h2, h2s⟩, h3⟩ := h
    obtain ⟨hd1, hd2⟩ := hd k l side o subs dead reads c rfl h2
    have hall := List.all_eq_true.1 h3
    simp only [Strat.pending, Bool.or_eq_false_iff, List.any_eq_false] at h1 ⊢
    refine ⟨⟨⟨by rw [hd2]; exact h1.1.1, h1.1.2⟩, fun e he => ?_⟩, ⟨hd1, h2s⟩,
      List.all_eq_true.2 fun e he => ?_⟩
    · have h4 := h1.2 e he
      have h5 := hall e he
      rcases e with ⟨⟨x, o⟩, n⟩
      cases hdn : (dead.getD []).contains n with
      | true => simp
      | false =>
        cases o with
        | none => simp
        | some t =>
          simp only [hdn, Bool.false_or] at h5
          simp only [hdn, Bool.not_false, Bool.true_and] at h4 ⊢
          rw [(hok _ h5).2]
          exact h4
    · have h5 := hall e he
      rcases e with ⟨⟨x, o⟩, n⟩
      cases hdn : (dead.getD []).contains n with
      | true => simp
      | false =>
        cases o with
        | none =>
          simp only [hdn, Bool.false_or] at h5
          exact Bool.noConfusion h5
        | some t =>
          simp only [hdn, Bool.false_or] at h5 ⊢
          exact (hok _ h5).1
  | check l side o c =>
    cases c with
    | reading => simp [Strat.quiet, Strat.pending] at h
    | off => simp [Strat.quiet] at h
    | opened subs =>
      simp only [Strat.quiet, Strat.pending, Bool.not_false, Bool.true_and, List.all_eq_true,
        Bool.and_eq_true] at h ⊢
      exact fun j hj => ⟨(hok j (h j hj).1).1, by rw [(hok j (h j hj).1).2]; exact (h j hj).2⟩

theorem quiet_mono {st st' : StateOf S N A} {ok : Nat → Bool}
    (hd : ∀ j, st.isDone j = true → st'.isDone j = true ∧ st'.answers j = st.answers j)
    (hok : ∀ j, ok j = true → st'.isDone j = true ∧ st'.answers j = st.answers j)
    {s : Strat N A} (h : s.quiet st ok = true) : s.quiet st' st'.isDone = true :=
  quiet_mono' (fun _ _ side _ _ _ _ _ _ h => hd side h) hok h

/-- A push with nothing left to do pushes the answers of a complete table. -/
theorem quiet_push_side {st : StateOf S N A} {ok : Nat → Bool} {k : Kind} {l : Bool} {side : Nat}
    {o : N} {subs : List (A × Option (Nat × Nat))} {dead : Option (List Nat)}
    {reads : List (Nat × Option Nat)} {c : Cursor}
    (h : (Strat.push k l side o subs dead reads c fc).quiet st ok = true) :
    st.isDone side = true := by
  simp only [Strat.quiet, Bool.and_eq_true] at h
  exact h.2.1.1

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

/-! ## What a table has been fed -/

theorem fedAt_modify (st : StateOf S N A) (i : Nat) (f : Table S N A → Table S N A) (k : Nat) :
    (st.modify i f).fedAt k =
      match st.tables[k]? with
      | some t => if i = k then (f t).fed else t.fed
      | none => 0 := by
  unfold StateOf.fedAt StateOf.modify
  simp only [List.getElem?_modify]
  cases st.tables[k]? with
  | none => simp
  | some t => by_cases e : i = k <;> simp [e]

/-- A change to a table that leaves what it has been fed. -/
theorem fedAt_modify_same (st : StateOf S N A) (i : Nat) (f : Table S N A → Table S N A)
    (hf : ∀ t, (f t).fed = t.fed) (k : Nat) : (st.modify i f).fedAt k = st.fedAt k := by
  rw [fedAt_modify]
  unfold StateOf.fedAt
  cases st.tables[k]? with
  | none => rfl
  | some t => simp only [hf]; split <;> rfl

theorem fedAt_feed_le (st : StateOf S N A) (h c k : Nat) :
    st.fedAt k ≤ (st.modify h fun t => { t with fed := t.fed + c }).fedAt k := by
  rw [fedAt_modify]
  unfold StateOf.fedAt
  cases st.tables[k]? with
  | none => exact Nat.le_refl _
  | some t => simp only; split <;> omega

theorem fedAt_feed_ne (st : StateOf S N A) (h c : Nat) {k : Nat} (hk : k ≠ h) :
    (st.modify h fun t => { t with fed := t.fed + c }).fedAt k = st.fedAt k := by
  rw [fedAt_modify]
  unfold StateOf.fedAt
  cases st.tables[k]? with
  | none => rfl
  | some t => simp only [Ne.symm hk, ite_false]

theorem fedAt_feed_self (st : StateOf S N A) (h c : Nat) {t : Table S N A}
    (ht : st.tables[h]? = some t) :
    (st.modify h fun t => { t with fed := t.fed + c }).fedAt h = st.fedAt h + c := by
  rw [fedAt_modify]
  unfold StateOf.fedAt
  simp only [ht, ite_true]

/-- The tables the strategy reads need no round in this request any more. A
check is asked only while none of the goals it opened has an answer. -/
def SFed (st : StateOf S N A) : Strat N A → Prop
  | .copy _ subs => ∀ p ∈ subs, Settled st p.1
  | .join _ a b _ => Settled st a ∧ Settled st b
  | .check _ _ _ c =>
    match c with
    | .opened subs => (∀ j ∈ subs, st.answers j = []) → ∀ j ∈ subs, Settled st j
    | _ => True
  | .push k l side o subs dead reads c fc =>
    ∀ j ∈ (Strat.push k l side o subs dead reads c fc : Strat N A).feeds st, Settled st j
  | .span _ => True

theorem SFed.mono {st st' : StateOf S N A} (h : Stable st st')
    (hset : ∀ j, Settled st j → Settled st' j) {s : Strat N A} (hs : SFed st s) :
    SFed st' s := by
  cases s with
  | span _ => trivial
  | copy _ subs => exact fun p hp => hset _ (hs p hp)
  | join _ a b _ => exact ⟨hset _ hs.1, hset _ hs.2⟩
  | push _ _ _ _ _ _ _ _ _ => exact fun j hj => hset _ (hs j hj)
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

theorem settled_of_isDone {st : StateOf S N A} {j : Nat} (h : st.isDone j = true) :
    Settled st j := fun t ht => by
  simp only [StateOf.isDone, ht] at h
  exact .inl h

/-- A push reads its side. -/
theorem feeds_push_side (st : StateOf S N A) (k : Kind) (l : Bool) (side : Nat) (o : N)
    (subs : List (A × Option (Nat × Nat))) (dead : Option (List Nat))
    (reads : List (Nat × Option Nat))
    (c : Cursor) : side ∈ (Strat.push k l side o subs dead reads c fc : Strat N A).feeds st :=
  List.mem_cons_self

/-- A push reads the table opened for an answer that is not superseded. -/
theorem feeds_push_sub (st : StateOf S N A) (k : Kind) (l : Bool) (side : Nat) (o : N)
    {subs : List (A × Option (Nat × Nat))} {dead : Option (List Nat)}
    (reads : List (Nat × Option Nat))
    (c : Cursor) {n : Nat} {x : A} {t : Nat × Nat} (he : subs[n]? = some (x, some t))
    (hn : n ∉ dead.getD []) : t.1 ∈ (Strat.push k l side o subs dead reads c fc : Strat N A).feeds st := by
  refine List.mem_cons_of_mem _ (List.mem_filterMap.2 ⟨((x, some t), n),
    List.mk_mem_zipIdx_iff_getElem?.2 he, ?_⟩)
  simp [hn]

/-- The tables a strategy reads, once each has had what a round gives it,
need no round. -/
theorem sfed_of_feeds {st st' : StateOf S N A} (hS : Stable st st') {s : Strat N A}
    (h : ∀ j ∈ s.feeds st, Settled st' j) : SFed st' s := by
  cases s with
  | span _ => trivial
  | copy _ subs => exact fun p hp => h p.1 (List.mem_map.2 ⟨p, hp, rfl⟩)
  | join _ a b _ => exact ⟨h a (by simp [Strat.feeds]), h b (by simp [Strat.feeds])⟩
  | push k l side o subs dead reads c fc => exact h
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

/-- What a group that worked from `st` to `st'` did for the tables a strategy
of it reads: they need no round in this request any more. The members of a
union share the ticks instead: each needs no round any more, or a member had
a round that cost something, and that member had been fed no more than this
one has been. -/
def Fed (st st' : StateOf S N A) : Strat N A → Prop
  | .copy false subs => ∀ p ∈ subs, Settled st' p.1 ∨
      ∃ q ∈ subs, st.fedAt q.1 < st'.fedAt q.1 ∧ st.fedAt q.1 ≤ st'.fedAt p.1
  | s => SFed st' s

theorem Fed.of_sfed {st st' : StateOf S N A} {s : Strat N A} (h : SFed st' s) : Fed st st' s := by
  cases s with
  | copy c subs =>
    cases c with
    | true => exact h
    | false => exact fun p hp => .inl (h p hp)
  | span _ => exact h
  | join _ _ _ _ => exact h
  | push _ _ _ _ _ _ _ _ _ => exact h
  | check _ _ _ _ => exact h

/-- What is fed is fed from an earlier state. -/
theorem Fed.start {a b c : StateOf S N A} (hf : ∀ j, a.fedAt j ≤ b.fedAt j) {s : Strat N A}
    (h : Fed b c s) : Fed a c s := by
  cases s with
  | copy cl subs =>
    cases cl with
    | true => exact h
    | false =>
      intro p hp
      rcases h p hp with hs | ⟨q, hq, h1, h2⟩
      · exact .inl hs
      · exact .inr ⟨q, hq, Nat.lt_of_le_of_lt (hf _) h1, Nat.le_trans (hf _) h2⟩
  | span _ => exact h
  | join _ _ _ _ => exact h
  | push _ _ _ _ _ _ _ _ _ => exact h
  | check _ _ _ _ => exact h

/-- What is fed is fed to a later state. -/
theorem Fed.finish {a b c : StateOf S N A} (hS : Stable b c)
    (hset : ∀ j, Settled b j → Settled c j) (hf : ∀ j, b.fedAt j ≤ c.fedAt j) {s : Strat N A}
    (h : Fed a b s) : Fed a c s := by
  cases s with
  | copy cl subs =>
    cases cl with
    | true => exact SFed.mono hS hset (s := .copy true subs) h
    | false =>
      intro p hp
      rcases h p hp with hs | ⟨q, hq, h1, h2⟩
      · exact .inl (hset _ hs)
      · exact .inr ⟨q, hq, Nat.lt_of_lt_of_le h1 (hf _), Nat.le_trans h2 (hf _)⟩
  | span _ => exact h
  | join k x y cu => exact SFed.mono hS hset (s := .join k x y cu) h
  | push k l sd o sb dd rd cu fcu => exact SFed.mono hS hset (s := .push k l sd o sb dd rd cu fcu) h
  | check l sd o ck => exact SFed.mono hS hset (s := .check l sd o ck) h

/-! ## The groups of a table over its round -/

/-- A group later: each of its strategies later. -/
def GrAdv (gr gr' : Group N A) : Prop :=
  Pointwise (SAdv) gr.strats gr'.strats

/-- A strategy and itself after its turn, with what it owed before the turn
(`o`) and what it owes after it (`o'`): it has worked, or it owes less. -/
def OStep (need : N → Nat) (len : Nat → Nat) (dn : Nat → Bool) (d d' o o' : Nat)
    (s s' : Strat N A) : Prop :=
  SStep need len dn d d' s s' ∨ o' < o

theorem OStep.mono {len len' : Nat → Nat} {dn dn' : Nat → Bool} {d d' d0 d1 o o' : Nat}
    (hl : ∀ j, len' j ≤ len j) (hdn : ∀ j, dn' j = true → dn j = true)
    (hd : d0 ≤ d) (hd' : d' ≤ d1) {s s' : Strat N A} (h : OStep need len dn d d' o o' s s') :
    OStep need len' dn' d0 d1 o o' s s' :=
  h.imp (fun h => h.mono hl hdn hd hd') id

/-- A group after it has worked: each of its strategies has had its turn. -/
def GrStep (need : N → Nat) (len : Nat → Nat) (dn : Nat → Bool) (d d' : Nat)
    (gr gr' : Group N A) : Prop :=
  gr.strats.length = gr'.strats.length ∧
    ∀ (m : Nat) (s s' : Strat N A), gr.strats[m]? = some s → gr'.strats[m]? = some s' →
      OStep need len dn d d' (gr.owed.getD m 0) (gr'.owed.getD m 0) s s'

theorem GrStep.mono {len len' : Nat → Nat} {dn dn' : Nat → Bool} {d d' d0 d1 : Nat}
    (hl : ∀ j, len' j ≤ len j) (hdn : ∀ j, dn' j = true → dn j = true)
    (hd : d0 ≤ d) (hd' : d' ≤ d1) {gr gr' : Group N A} (h : GrStep need len dn d d' gr gr') :
    GrStep need len' dn' d0 d1 gr gr' :=
  ⟨h.1, fun m s s' hs hs' => (h.2 m s s' hs hs').mono hl hdn hd hd'⟩

/-- A span, a call, a union or a join: the strategies that head a group. -/
def Strat.lead : Strat N A → Bool
  | .span _ => true
  | .copy _ _ => true
  | .join _ _ _ _ => true
  | _ => false

/-- An interface check. -/
def Strat.isCheck : Strat N A → Bool
  | .check _ _ _ _ => true
  | _ => false

/-- The shape of the groups of a table: one of them has a span, a call, a
union or a join, and one that has none is all interface checks. -/
def Shaped (gs : List (Group N A)) : Prop :=
  (∃ gr ∈ gs, ∃ s ∈ gr.strats, s.lead = true) ∧
    ∀ gr ∈ gs, (∃ s ∈ gr.strats, s.lead = true) ∨ ∀ s ∈ gr.strats, s.isCheck = true

/-- A group worked in a round from `st` to `st'`: each of its strategies
has, and the tables they read are fed. -/
abbrev Tried (need : N → Nat) (st st' : StateOf S N A) (gr0 gr1 : Group N A) : Prop :=
  GrStep need st.len st.isDone st.depth st'.depth gr0 gr1 ∧ ∀ s ∈ gr1.strats, Fed st st' s

theorem Tried.start {a b c : StateOf S N A} (hS : Stable a b) (hd : a.depth ≤ b.depth)
    (hf : ∀ j, a.fedAt j ≤ b.fedAt j)
    {gr0 gr1 : Group N A} (h : Tried need b c gr0 gr1) : Tried need a c gr0 gr1 :=
  ⟨h.1.mono hS.len_le (fun _ h => (hS.isDone h).1) hd (Nat.le_refl _),
    fun s hs => (h.2 s hs).start hf⟩

theorem Tried.finish {a b c : StateOf S N A} (hS : Stable b c)
    (hset : ∀ j, Settled b j → Settled c j) (hd : b.depth ≤ c.depth)
    (hf : ∀ j, b.fedAt j ≤ c.fedAt j)
    {gr0 gr1 : Group N A} (h : Tried need a b gr0 gr1) : Tried need a c gr0 gr1 :=
  ⟨h.1.mono (fun _ => Nat.le_refl _) (fun _ h => h) (Nat.le_refl _) hd,
    fun s hs => (h.2 s hs).finish hS hset hf⟩

/-- The balance of a round, for the group at a place before (`gr0`) and
after (`gr1`): its level has not fallen, and it worked, or it stands as it
stood, its strategies owing what they owed, and a group that stood lower has
risen. `gs0` and `gs1` are the groups
before the round and after it, before any is removed. -/
def Balanced (need : N → Nat) (st st' : StateOf S N A) (gs0 gs1 : List (Group N A))
    (gr0 gr1 : Group N A) : Prop :=
  gr0.level ≤ gr1.level ∧ (Tried need st st' gr0 gr1 ∨
    (gr1.level = gr0.level ∧ gr1.owed = gr0.owed ∧ ∃ (k' : Nat) (gr0' gr1' : Group N A),
      gs0[k']? = some gr0' ∧ gs1[k']? = some gr1' ∧ gr0'.level < gr0.level ∧
      gr0'.level < gr1'.level))

/-- The groups of a table before its round (`go`, nothing if this is its
first) and after it (`go'`). -/
def Turn (need : N → Nat) (st st' : StateOf S N A) (go go' : Option (List (Group N A))) : Prop :=
  ∃ (gs0 gs1 : List (Group N A)) (p : Group N A → Bool),
    (∀ gs, go = some gs → gs = gs0) ∧ (go = none → Shaped gs0) ∧ go'.getD [] = gs1.filter p ∧
    Pointwise (fun gr0 gr1 => GrAdv gr0 gr1 ∧
      (p gr1 = true → ∃ s ∈ gr0.strats, s.dead st = false) ∧
      (p gr1 = false → ∀ s ∈ gr1.strats, s.dead st' = true)) gs0 gs1 ∧
    (gs0 = [] ∨ ∃ (k : Nat) (gr0 gr1 : Group N A), gs0[k]? = some gr0 ∧ gs1[k]? = some gr1 ∧
      Tried need st st' gr0 gr1) ∧
    ∀ (k : Nat) (gr0 gr1 : Group N A), gs0[k]? = some gr0 → gs1[k]? = some gr1 →
      Balanced need st st' gs0 gs1 gr0 gr1

/-- The record of a round stays true from an earlier state. -/
theorem Turn.start {a b c : StateOf S N A} (hS : Stable a b) (hd : a.depth ≤ b.depth)
    (hf : ∀ j, a.fedAt j ≤ b.fedAt j)
    {go go' : Option (List (Group N A))} (h : Turn need b c go go') : Turn need a c go go' := by
  obtain ⟨gs0, gs1, p, h1, h2, h3, h4, h5, h6⟩ := h
  have h4' := h4.imp (r' := fun gr0 gr1 => GrAdv gr0 gr1 ∧
      (p gr1 = true → ∃ s ∈ gr0.strats, s.dead a = false) ∧
      (p gr1 = false → ∀ s ∈ gr1.strats, s.dead c = true)) fun gr0 gr1 hg => by
    refine ⟨hg.1, fun hp => ?_, hg.2.2⟩
    obtain ⟨s, hs, hdead⟩ := hg.2.1 hp
    refine ⟨s, hs, ?_⟩
    cases hx : s.dead a with
    | false => rfl
    | true => rw [hS.dead hx] at hdead; cases hdead
  refine ⟨gs0, gs1, p, h1, h2, h3, h4', ?_, fun k gr0 gr1 e0 e1 => ?_⟩
  · rcases h5 with h5 | ⟨k, gr0, gr1, e0, e1, ht⟩
    · exact .inl h5
    · exact .inr ⟨k, gr0, gr1, e0, e1, ht.start hS hd hf⟩
  · obtain ⟨hle, hb⟩ := h6 k gr0 gr1 e0 e1
    exact ⟨hle, hb.imp (fun ht => ht.start hS hd hf) id⟩

/-- The record of a round stays true to a later state. -/
theorem Turn.finish {a b c : StateOf S N A} (hS : Stable b c)
    (hset : ∀ j, Settled b j → Settled c j) (hd : b.depth ≤ c.depth)
    (hf : ∀ j, b.fedAt j ≤ c.fedAt j)
    {go go' : Option (List (Group N A))} (h : Turn need a b go go') : Turn need a c go go' := by
  obtain ⟨gs0, gs1, p, h1, h2, h3, h4, h5, h6⟩ := h
  have h4' := h4.imp (r' := fun gr0 gr1 => GrAdv gr0 gr1 ∧
      (p gr1 = true → ∃ s ∈ gr0.strats, s.dead a = false) ∧
      (p gr1 = false → ∀ s ∈ gr1.strats, s.dead c = true)) fun gr0 gr1 hg =>
    ⟨hg.1, hg.2.1, fun hp s hs => hS.dead (hg.2.2 hp s hs)⟩
  refine ⟨gs0, gs1, p, h1, h2, h3, h4', ?_, fun k gr0 gr1 e0 e1 => ?_⟩
  · rcases h5 with h5 | ⟨k, gr0, gr1, e0, e1, ht⟩
    · exact .inl h5
    · exact .inr ⟨k, gr0, gr1, e0, e1, ht.finish hS hset hd hf⟩
  · obtain ⟨hle, hb⟩ := h6 k gr0 gr1 e0 e1
    exact ⟨hle, hb.imp (fun ht => ht.finish hS hset hd hf) id⟩

theorem shaped_all {gs : List (Group N A)} (hne : gs ≠ [])
    (h : ∀ gr ∈ gs, ∃ s ∈ gr.strats, s.lead = true) : Shaped gs := by
  cases gs with
  | nil => exact absurd rfl hne
  | cons gr gs =>
    exact ⟨⟨gr, List.mem_cons_self, h gr List.mem_cons_self⟩, fun gr' hk => .inl (h gr' hk)⟩

theorem shaped_of {gs : List (Group N A)} {c : Prop}
    (h : (∀ gr ∈ gs, ∃ s ∈ gr.strats, s.lead = true) ∧ (c → gs ≠ [])) (hc : c) : Shaped gs :=
  shaped_all (h.2 hc) h.1

theorem shaped_snoc {gs : List (Group N A)} (hne : gs ≠ [])
    (h : ∀ gr ∈ gs, ∃ s ∈ gr.strats, s.lead = true) (last : Group N A)
    (hl : ∀ s ∈ last.strats, s.isCheck = true) : Shaped (gs ++ [last]) := by
  obtain ⟨⟨gr, hgr, hlead⟩, -⟩ := shaped_all hne h
  refine ⟨⟨gr, List.mem_append_left _ hgr, hlead⟩, fun gr' hk => ?_⟩
  rcases List.mem_append.1 hk with hk | hk
  · exact .inl (h gr' hk)
  · obtain rfl := List.mem_singleton.1 hk
    exact .inr hl

theorem SAdv.lead {s s' : Strat N A} (h : SAdv s s') :
    s'.lead = s.lead := by
  cases h <;> rfl

theorem SAdv.isCheck {s s' : Strat N A} (h : SAdv s s') :
    s'.isCheck = s.isCheck := by
  cases h <;> rfl

theorem lead_not_dead (st : StateOf S N A) {s : Strat N A} (h : s.lead = true) :
    s.dead st = false := by
  cases s <;> first | rfl | cases h

/-- **A round keeps the shape of the groups**, and leaves the table with
groups. -/
theorem Turn.shaped {st st' : StateOf S N A} {go go' : Option (List (Group N A))}
    (h : Turn need st st' go go') (hs : ∀ gs, go = some gs → Shaped gs) :
    ∃ gs', go' = some gs' ∧ Shaped gs' := by
  obtain ⟨gs0, gs1, p, h1, h2, h3, h4, -, -⟩ := h
  have h0 : Shaped gs0 := by
    cases hg : go with
    | none => exact h2 hg
    | some gs => rw [← h1 gs hg]; exact hs gs hg
  have hl : ∀ gr0 gr1 : Group N A, GrAdv gr0 gr1 → (∃ s ∈ gr0.strats, s.lead = true) →
      ∃ s ∈ gr1.strats, s.lead = true := by
    rintro gr0 gr1 ha ⟨s, hs0, hlead⟩
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hs0
    obtain ⟨s1, hs1, hadv⟩ := Pointwise.get ha (List.getElem?_eq_getElem hm)
    exact ⟨s1, List.mem_of_getElem? hs1, by rw [hadv.lead]; exact hlead⟩
  have hc : ∀ gr0 gr1 : Group N A, GrAdv gr0 gr1 → (∀ s ∈ gr0.strats, s.isCheck = true) →
      ∀ s ∈ gr1.strats, s.isCheck = true := by
    intro gr0 gr1 ha hall s1 hs1
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hs1
    obtain ⟨s0, hs0, hadv⟩ := Pointwise.get' ha (List.getElem?_eq_getElem hm)
    rw [hadv.isCheck]
    exact hall s0 (List.mem_of_getElem? hs0)
  have hsh : Shaped (gs1.filter p) := by
    obtain ⟨⟨gr0, hgr0, hlead⟩, hall⟩ := h0
    constructor
    · obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hgr0
      obtain ⟨gr1, hgr1, hr⟩ := Pointwise.get h4 (List.getElem?_eq_getElem hm)
      obtain ⟨s1, hs1, hl1⟩ := hl _ _ hr.1 hlead
      refine ⟨gr1, List.mem_filter.2 ⟨List.mem_of_getElem? hgr1, ?_⟩, s1, hs1, hl1⟩
      cases hp : p gr1 with
      | true => rfl
      | false =>
        have := hr.2.2 hp s1 hs1
        rw [lead_not_dead st' hl1] at this
        cases this
    · intro gr1 hgr1
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem (List.mem_filter.1 hgr1).1
      obtain ⟨gr0, hgr0, hr⟩ := Pointwise.get' h4 (List.getElem?_eq_getElem hm)
      rcases hall gr0 (List.mem_of_getElem? hgr0) with h | h
      · exact .inl (hl _ _ hr.1 h)
      · exact .inr (hc _ _ hr.1 h)
  cases hg' : go' with
  | none =>
    rw [hg'] at h3
    obtain ⟨⟨gr, hgr, -⟩, -⟩ := hsh
    rw [← h3] at hgr
    simp at hgr
  | some gs' =>
    rw [hg'] at h3
    exact ⟨gs', rfl, by rw [show gs' = gs1.filter p from h3]; exact hsh⟩

theorem mem_levelsOf {gs : List (Group N A)} {lv : Nat} (h : lv ∈ levelsOf gs) :
    ∃ gr ∈ gs, gr.level = lv := by
  unfold levelsOf at h
  obtain ⟨gr, hgr, rfl⟩ := List.mem_map.1 (List.mem_mergeSort.1 (List.mem_eraseDups.1 h))
  exact ⟨gr, hgr, rfl⟩

theorem level_mem_levelsOf {gs : List (Group N A)} {gr : Group N A} (h : gr ∈ gs) :
    gr.level ∈ levelsOf gs := by
  unfold levelsOf
  exact List.mem_eraseDups.2 (List.mem_mergeSort.2 (List.mem_map.2 ⟨gr, h, rfl⟩))

/-- The levels are worked lowest first. -/
theorem pairwise_levelsOf (gs : List (Group N A)) : (levelsOf gs).Pairwise (· < ·) := by
  unfold levelsOf
  refine pairwise_lt_eraseDups _ ?_
  have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (gs.map (·.level))
  exact this.imp fun h => by simpa using h

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

/-- The race of the table at `k` gave a final verdict: answers of the table,
from the first on, are what a final verdict gives. -/
def Raced (Rc : RaceSem S N A) (st : StateOf S N A) (k : Nat) : Prop :=
  ∃ t, st.tables[k]? = some t ∧ ∃ l, l <+: t.answers ∧ Rc.cov t.goal l

theorem Raced.mono {st st' : StateOf S N A} (hS : Stable st st') {k : Nat}
    (h : Raced Rc st k) : Raced Rc st' k := by
  obtain ⟨t, ht, l, hl, hc⟩ := h
  obtain ⟨t', ht', e1, -, e3, -⟩ := hS k t ht
  exact ⟨t', ht', l, hl.trans e3, by rw [e1]; exact hc⟩

/-- What its round does to the race of a table, `t` before the round and
`t'` after: the table has had one more round; and if it had a race, or
begins with one in its first round, then the race was not asked, the table
having had fewer rounds than the race has spent and needs for its next ask;
or the table is complete; or the race stands one depth further, having given
up nothing there, and its verdict at the depth it stood at is not final; or
the race gave up an ask that costs more than it was allowed, and was allowed
at least one tick and twice what it gave up before. -/
def Asked (Rc : RaceSem S N A) (t t' : Table S N A) : Prop :=
  t'.rounds = t.rounds + 1 ∧
  ∀ r, (if t.groups.isNone then (if Rc.has t.goal then some ⟨0, 0, 0⟩ else none) else t.race) =
      some r →
    (t'.race = some r ∧ t.rounds < r.spent + max 1 (2 * r.gaveUp)) ∨ t'.done = true ∨
    (∃ c, t'.race = some ⟨r.depth + 1, r.spent + c, 0⟩ ∧ ¬ Rc.final t.goal r.depth) ∨
    ∃ left, t'.race = some ⟨r.depth, r.spent + left, left⟩ ∧ max 1 (2 * r.gaveUp) ≤ left ∧
      left < Rc.cost t.goal r.depth

theorem Asked.finish {t t' t'' : Table S N A} (h : Asked Rc t t')
    (hr : t''.race = t'.race ∧ t''.rounds = t'.rounds) (hd : t'.done = true → t''.done = true) :
    Asked Rc t t'' :=
  ⟨hr.2.trans h.1, fun r e => (h.2 r e).imp (fun p => ⟨hr.1.trans p.1, p.2⟩)
    (Or.imp hd (Or.imp (fun ⟨c, p, q⟩ => ⟨c, hr.1.trans p, q⟩)
      fun ⟨l, p, q⟩ => ⟨l, hr.1.trans p, q⟩))⟩

theorem Asked.start {t t' t'' : Table S N A} (h : Asked Rc t' t'') (hg : t'.goal = t.goal)
    (hgr : t'.groups = t.groups) (hr : t'.race = t.race ∧ t'.rounds = t.rounds) :
    Asked Rc t t'' := by
  refine ⟨by rw [← hr.2]; exact h.1, fun r e => ?_⟩
  have := h.2 r (by rw [hgr, hg, hr.1]; exact e)
  rw [hg, hr.2] at this
  exact this

/-! ## The order in which tables complete -/

/-- The complete tables stand in the order `ρ`: each has a strategy with
nothing left to do that reads only complete tables that stand no higher, and
if it pushes the answers of a table, that table stands lower; or its race
gave a final verdict. Tables that complete together stand together; a table
whose answers are pushed was complete before the push began. -/
def Ranked (Rc : RaceSem S N A) (st : StateOf S N A) (ρ : Nat → Nat) : Prop :=
  ∀ (i : Nat) (t : Table S N A), st.tables[i]? = some t → t.done = true →
    (∃ gs, t.groups = some gs ∧ ∃ gr ∈ gs, ∃ s ∈ gr.strats,
      s.quiet st (fun j => st.isDone j && decide (ρ j ≤ ρ i)) = true ∧
      ∀ k l side o subs dead reads c fc, s = .push k l side o subs dead reads c fc → ρ side < ρ i) ∨
    Raced Rc st i

/-- The complete tables stand in some order (`Ranked`): none is complete
only because of itself. -/
def Founded (Rc : RaceSem S N A) (st : StateOf S N A) : Prop := ∃ ρ, Ranked Rc st ρ

/-- The order is kept by a stretch in which the tables that become complete
have a strategy with nothing left to do that reads complete tables only and
pushes only the answers of a table that was complete before, or a final
verdict of their race. The new tables stand above all the old ones. -/
theorem Founded.step {st st' : StateOf S N A} (hS : Stable st st')
    (hg : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
      t.done = true → t'.groups = t.groups)
    (hnew : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → t'.done = true →
      (∃ t, st.tables[k]? = some t ∧ t.done = true) ∨
      (∃ gs, t'.groups = some gs ∧ ∃ gr ∈ gs, ∃ s ∈ gr.strats, s.quiet st' st'.isDone = true ∧
        ∀ k l side o subs dead reads c fc, s = .push k l side o subs dead reads c fc → st.isDone side = true) ∨
      Raced Rc st' k)
    (h : Founded Rc st) : Founded Rc st' := by
  obtain ⟨ρ, hρ⟩ := h
  have hM : ∀ j, st.isDone j = true → ρ j ≤ ((List.range st.tables.length).map ρ).sum :=
    fun j hj => by
      have hlt : j < st.tables.length := by
        by_contra hn
        simp [StateOf.isDone, List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hj
      exact le_sum_of_mem (List.mem_map.2 ⟨j, List.mem_range.2 hlt, rfl⟩)
  generalize ((List.range st.tables.length).map ρ).sum = M at hM
  refine ⟨fun j => if st.isDone j = true then ρ j else M + 1, fun i t' ht' hd' => ?_⟩
  have hle : ∀ j, (if st.isDone j = true then ρ j else M + 1) ≤ M + 1 := fun j => by
    split
    · next hj => exact Nat.le_succ_of_le (hM j hj)
    · exact Nat.le_refl _
  cases hi : st.isDone i with
  | true =>
    cases ht : st.tables[i]? with
    | none => simp [StateOf.isDone, ht] at hi
    | some t =>
      have hdt : t.done = true := by simpa [StateOf.isDone, ht] using hi
      rcases hρ i t ht hdt with ⟨gs, hgs, gr, hgr, s, hs, hq, hp⟩ | hrc
      swap
      · exact .inr (hrc.mono hS)
      refine .inl ⟨gs, (hg i t t' ht ht' hdt).trans hgs, gr, hgr, s, hs, ?_, ?_⟩
      · refine quiet_mono' (fun _ _ _ _ _ _ _ _ _ h => hS.isDone h) (fun j hj => ?_) hq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        refine ⟨?_, (hS.isDone hj.1).2⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, (hS.isDone hj.1).1, hj.1, hi, ite_true,
          true_and]
        exact hj.2
      · intro k l side o subs dead reads c e
        subst e
        have := hp k l side o subs dead reads c rfl
        simp only [quiet_push_side hq, hi, ite_true]
        exact this
  | false =>
    rcases hnew i t' ht' hd' with ⟨t, ht, hdt⟩ | ⟨gs, hgs, gr, hgr, s, hs, hq, hp⟩ | hrc
    · simp [StateOf.isDone, ht, hdt] at hi
    swap
    · exact .inr hrc
    · refine .inl ⟨gs, hgs, gr, hgr, s, hs, ?_, ?_⟩
      · refine quiet_mono' (fun _ _ _ _ _ _ _ _ _ h => ⟨h, rfl⟩) (fun j hj => ⟨?_, rfl⟩) hq
        simp only [Bool.and_eq_true, decide_eq_true_eq, hj, hi, true_and]
        exact hle j
      · intro k l side o subs dead reads c e
        have hsd := hp k l side o subs dead reads c e
        simp only [hsd, hi, ite_true]
        exact Nat.lt_succ_of_le (hM side hsd)

/-- The record of a stretch of a run. With `x` the position of a table in
its round, the record says nothing of the groups of that table while it is
not complete. -/
structure TurnsBut (need : N → Nat) (Rc : RaceSem S N A) (x : Option Nat)
    (st st' : StateOf S N A) : Prop where
  keep : Keep st st'
  depth : st.depth ≤ st'.depth
  stamp : (∀ (k : Nat) (t : Table S N A), st.tables[k]? = some t → t.stamp ≤ st.round) →
    ∀ (k : Nat) (t : Table S N A), st'.tables[k]? = some t → t.stamp ≤ st'.round
  groups : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    (t.done = true ∨ (some k ≠ x ∧ (t.stamp = st.round ∨ t'.stamp ≠ st.round))) →
    t'.groups = t.groups
  done : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → t'.done = true →
    (∃ t, st.tables[k]? = some t ∧ t.done = true) ∨ QuietAt st' t' ∨ Raced Rc st' k
  turn : ∀ (k : Nat) (t t' : Table S N A), some k ≠ x → st.tables[k]? = some t →
    st'.tables[k]? = some t' → t.stamp ≠ st.round → t'.stamp = st.round →
    Turn need st st' t.groups t'.groups
  young : ∀ (k : Nat) (t' : Table S N A), some k ≠ x → st'.tables[k]? = some t' →
    t'.born = st'.round → (∀ t, st.tables[k]? = some t → t.groups = none) → t'.groups = none
  founded : Founded Rc st → Founded Rc st'
  race : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    (t.done = true ∨ t.stamp = st.round ∨ (some k ≠ x ∧ t'.stamp ≠ st.round)) →
    t'.race = t.race ∧ t'.rounds = t.rounds
  asked : ∀ (k : Nat) (t t' : Table S N A), some k ≠ x → st.tables[k]? = some t →
    st'.tables[k]? = some t' → t.stamp ≠ st.round → t'.stamp = st.round → Asked Rc t t'
  fed : ∀ k : Nat, st.fedAt k ≤ st'.fedAt k ∧ (st.fedAt k < st'.fedAt k → Settled st' k)

/-- The record of a stretch of a run. -/
abbrev Turns (need : N → Nat) (Rc : RaceSem S N A) (st st' : StateOf S N A) : Prop :=
  TurnsBut need Rc none st st'

theorem TurnsBut.trans {x : Option Nat} {a b c : StateOf S N A} (h₁ : TurnsBut need Rc x a b)
    (h₂ : TurnsBut need Rc x b c) : TurnsBut need Rc x a c := by
  have hr : b.round = a.round := h₁.keep.1
  refine ⟨h₁.keep.trans h₂.keep, h₁.depth.trans h₂.depth, fun h => h₂.stamp (h₁.stamp h),
    fun k ta tc ha hc hyp => ?_, fun k tc hc hdc => ?_, fun k ta tc hx ha hc hs hs' => ?_,
    fun k tc hx hc hbc hyp => ?_, fun h => h₂.founded (h₁.founded h),
    fun k ta tc ha hc hyp => ?_, fun k ta tc hx ha hc hs hs' => ?_, fun k => ?_⟩
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
  · rcases h₂.done k tc hc hdc with ⟨tb, hb, hdb⟩ | hq | hrc
    · rcases h₁.done k tb hb hdb with h | hq | hrc
      · exact .inl h
      · exact .inr (.inl (hq.mono h₂.keep.stable (h₂.groups k tb tc hb hc (.inl hdb))))
      · exact .inr (.inr (hrc.mono h₂.keep.stable))
    · exact .inr (.inl hq)
    · exact .inr (.inr hrc)
  · obtain ⟨tb, hb, -, -, -, -, e5⟩ := h₁.keep.2.1 k ta ha
    by_cases hsb : tb.stamp = a.round
    · have hg := h₂.groups k tb tc hb hc (.inr ⟨hx, .inl (by rw [hsb, hr])⟩)
      rw [hg]
      exact (h₁.turn k ta tb hx ha hb hs hsb).finish h₂.keep.stable (fun _ => h₂.keep.settled)
        h₂.depth fun j => (h₂.fed j).1
    · have hg := h₁.groups k ta tb ha hb (.inr ⟨hx, .inr hsb⟩)
      rw [← hg]
      exact (h₂.turn k tb tc hx hb hc (by rw [hr]; exact hsb) (by rw [hr]; exact hs')).start
        h₁.keep.stable h₁.depth fun j => (h₁.fed j).1
  · cases hb : b.tables[k]? with
    | none => exact h₂.young k tc hx hc hbc fun t h => by rw [hb] at h; cases h
    | some tb =>
      obtain ⟨tc', hc', -, e2, -⟩ := h₂.keep.2.1 k tb hb
      rw [hc] at hc'
      cases hc'
      have hg := h₁.young k tb hx hb (by rw [← e2, hbc, h₂.keep.1]) hyp
      exact h₂.young k tc hx hc hbc fun t h => by rw [hb] at h; cases h; exact hg
  · obtain ⟨tb, hb, -, -, -, e4, e5⟩ := h₁.keep.2.1 k ta ha
    obtain ⟨tc', hc', -, -, -, -, f5⟩ := h₂.keep.2.1 k tb hb
    rw [hc] at hc'
    cases hc'
    have comb : (tb.race = ta.race ∧ tb.rounds = ta.rounds) →
        (tc.race = tb.race ∧ tc.rounds = tb.rounds) → tc.race = ta.race ∧ tc.rounds = ta.rounds :=
      fun p q => ⟨q.1.trans p.1, q.2.trans p.2⟩
    rcases hyp with hd | hs | ⟨hx, hs⟩
    · exact comb (h₁.race k ta tb ha hb (.inl hd)) (h₂.race k tb tc hb hc (.inl (e4 hd).1))
    · have hsb : tb.stamp = b.round := by rw [(e5 hs).1, hr]
      exact comb (h₁.race k ta tb ha hb (.inr (.inl hs)))
        (h₂.race k tb tc hb hc (.inr (.inl hsb)))
    · have hsb : tb.stamp ≠ a.round := fun e => hs (by rw [(f5 (by rw [e, hr])).1, hr])
      exact comb (h₁.race k ta tb ha hb (.inr (.inr ⟨hx, hsb⟩)))
        (h₂.race k tb tc hb hc (.inr (.inr ⟨hx, by rw [hr]; exact hs⟩)))
  · obtain ⟨tb, hb, e1, -, -, -, -⟩ := h₁.keep.2.1 k ta ha
    by_cases hsb : tb.stamp = a.round
    · obtain ⟨tc', hc', -, -, -, f4, -⟩ := h₂.keep.2.1 k tb hb
      rw [hc] at hc'
      cases hc'
      exact (h₁.asked k ta tb hx ha hb hs hsb).finish
        (h₂.race k tb tc hb hc (.inr (.inl (by rw [hsb, hr])))) fun hd => (f4 hd).1
    · exact (h₂.asked k tb tc hx hb hc (by rw [hr]; exact hsb) (by rw [hr]; exact hs')).start e1
        (h₁.groups k ta tb ha hb (.inr ⟨hx, .inr hsb⟩))
        (h₁.race k ta tb ha hb (.inr (.inr ⟨hx, hsb⟩)))
  · refine ⟨Nat.le_trans (h₁.fed k).1 (h₂.fed k).1, fun hlt => ?_⟩
    by_cases h1 : a.fedAt k < b.fedAt k
    · exact h₂.keep.settled ((h₁.fed k).2 h1)
    · exact (h₂.fed k).2 (by have := (h₁.fed k).1; omega)

theorem TurnsBut.refl (x : Option Nat) (st : StateOf S N A) : TurnsBut need Rc x st st :=
  ⟨Keep.refl st, Nat.le_refl _, fun h => h, (fun k t t' h h' _ => by rw [h] at h'; cases h'; rfl),
    fun k t' h hd => .inl ⟨t', h, hd⟩, (fun k t t' _ h h' hs hs' => by
      rw [h] at h'; cases h'; exact absurd hs' hs), fun k t' _ h _ hyp => hyp t' h, fun h => h,
    (fun k t t' h h' _ => by rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩),
    (fun k t t' _ h h' hs hs' => by rw [h] at h'; cases h'; exact absurd hs' hs),
    fun k => ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩⟩

/-- The record of a stretch in which no table becomes complete. -/
theorem TurnsBut.of_open {x : Option Nat} {st st' : StateOf S N A} (keep : Keep st st')
    (depth : st.depth ≤ st'.depth)
    (stamp : (∀ (k : Nat) (t : Table S N A), st.tables[k]? = some t → t.stamp ≤ st.round) →
      ∀ (k : Nat) (t : Table S N A), st'.tables[k]? = some t → t.stamp ≤ st'.round)
    (groups : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t →
      st'.tables[k]? = some t' →
      (t.done = true ∨ (some k ≠ x ∧ (t.stamp = st.round ∨ t'.stamp ≠ st.round))) →
      t'.groups = t.groups)
    (done : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → t'.done = true →
      ∃ t, st.tables[k]? = some t ∧ t.done = true)
    (turn : ∀ (k : Nat) (t t' : Table S N A), some k ≠ x → st.tables[k]? = some t →
      st'.tables[k]? = some t' → t.stamp ≠ st.round → t'.stamp = st.round →
      Turn need st st' t.groups t'.groups)
    (young : ∀ (k : Nat) (t' : Table S N A), some k ≠ x → st'.tables[k]? = some t' →
      t'.born = st'.round → (∀ t, st.tables[k]? = some t → t.groups = none) →
      t'.groups = none)
    (race : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
      (t.done = true ∨ t.stamp = st.round ∨ (some k ≠ x ∧ t'.stamp ≠ st.round)) →
      t'.race = t.race ∧ t'.rounds = t.rounds)
    (asked : ∀ (k : Nat) (t t' : Table S N A), some k ≠ x → st.tables[k]? = some t →
      st'.tables[k]? = some t' → t.stamp ≠ st.round → t'.stamp = st.round → Asked Rc t t')
    (fed : ∀ k : Nat, st.fedAt k ≤ st'.fedAt k ∧ (st.fedAt k < st'.fedAt k → Settled st' k)) :
    TurnsBut need Rc x st st' :=
  ⟨keep, depth, stamp, groups, fun k t' h hd => .inl (done k t' h hd), turn, young,
    Founded.step keep.stable (fun k t t' ht ht' hd => groups k t t' ht ht' (.inl hd))
      (fun k t' h hd => .inl (done k t' h hd)), race, asked, fed⟩

/-- A record that says everything says what a record about a round says. -/
theorem TurnsBut.weaken {st st' : StateOf S N A} (h : Turns need Rc st st') (x : Option Nat) :
    TurnsBut need Rc x st st' :=
  ⟨h.keep, h.depth, h.stamp, fun k t t' ht ht' hyp => h.groups k t t' ht ht'
      (hyp.imp id fun hh => ⟨(fun e => by cases e), hh.2⟩),
    h.done, (fun k t t' _ => h.turn k t t' (fun e => by cases e)),
    (fun k t' _ => h.young k t' (fun e => by cases e)), h.founded,
    (fun k t t' ht ht' hyp => h.race k t t' ht ht'
      (hyp.imp id (Or.imp id fun hh => ⟨(fun e => by cases e), hh.2⟩))),
    (fun k t t' _ => h.asked k t t' (fun e => by cases e)), h.fed⟩

/-! ## The record of a request -/

/-- No table is stamped or opened later than now. -/
def Dated (st : StateOf S N A) : Prop :=
  ∀ (k : Nat) (t : Table S N A), st.tables[k]? = some t → t.stamp ≤ st.round ∧ t.born ≤ st.round

/-- The record of a request. -/
structure Req (need : N → Nat) (Rc : RaceSem S N A) (st st' : StateOf S N A) : Prop where
  round : st'.round = st.round + 1
  stable : Stable st st'
  depth : st.depth ≤ st'.depth
  dated : Dated st'
  born : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → st.tables[k]? = none →
    t'.born = st'.round ∧ t'.groups = none
  groups : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    (t.done = true ∨ t'.stamp ≠ st'.round) → t'.groups = t.groups
  done : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' → t'.done = true →
    (∃ t, st.tables[k]? = some t ∧ t.done = true) ∨ QuietAt st' t' ∨ Raced Rc st' k
  turn : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    t'.stamp = st'.round → Turn need st st' t.groups t'.groups
  root : Settled st' 0
  founded : Founded Rc st → Founded Rc st'
  closed : ∀ X : List Nat, (∀ k ∈ X, ∃ t', st'.tables[k]? = some t' ∧ ∃ gs, t'.groups = some gs ∧
      ∃ gr ∈ gs, ∃ s ∈ gr.strats, s.quiet st' (fun j => st'.isDone j || X.contains j) = true ∧
        ∀ k l side o subs dead reads c fc, s = .push k l side o subs dead reads c fc → st.isDone side = true) →
    ∀ k ∈ X, st'.isDone k = true
  race : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    (t.done = true ∨ t'.stamp ≠ st'.round) → t'.race = t.race ∧ t'.rounds = t.rounds
  asked : ∀ (k : Nat) (t t' : Table S N A), st.tables[k]? = some t → st'.tables[k]? = some t' →
    t'.stamp = st'.round → Asked Rc t t'
  fed : ∀ k : Nat, st.fedAt k ≤ st'.fedAt k ∧ (st.fedAt k < st'.fedAt k → Settled st' k)

/-- **The record of a request**, from the record of the round of the root:
the tables that complete together are marked. -/
theorem req_of_turns {st st2 : StateOf S N A} (hD : Dated st)
    (T : Turns need Rc { st with round := st.round + 1 } st2) (h0 : Settled st2 0) (shown : Nat) :
    Req need Rc st { st2 with
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
  have hsameR : ∀ (k : Nat) (t' : Table S N A), st'.tables[k]? = some t' →
      ∃ t2, st2.tables[k]? = some t2 ∧ t'.race = t2.race ∧ t'.rounds = t2.rounds := by
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
      split <;> exact ⟨rfl, rfl⟩
  have hS23 : Stable st2 st' := by
    intro k t2 hk
    rw [← hst']
    refine ⟨_, by simp only [List.getElem?_mapIdx, hk]; rfl, ?_⟩
    split
    · exact ⟨rfl, rfl, List.prefix_refl _, fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩⟩
  have hS01 : Stable st ({ st with round := st.round + 1 } : StateOf S N A) :=
    fun k t h => ⟨t, h, rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩⟩
  have hf23 : ∀ j, st'.fedAt j = st2.fedAt j := by
    intro j
    rw [← hst']
    simp only [StateOf.fedAt, List.getElem?_mapIdx]
    cases st2.tables[j]? with
    | none => rfl
    | some t2 =>
      simp only [Option.map_some]
      split <;> rfl
  have hset : ∀ j, Settled st2 j → Settled st' j := by
    intro j hj t' ht'
    obtain ⟨t2, h2, e1, e2, -, e4, -⟩ := hsame j t' ht'
    rcases hj t2 h2 with h | h | h
    · exact .inl (e4 h)
    · exact .inr (.inl (by rw [e2, h, hr']))
    · exact .inr (.inr (by rw [e1, h, hr']))
  have hst2 : ∀ (k : Nat) (t2 : Table S N A), st2.tables[k]? = some t2 → t2.stamp ≤ st2.round :=
    T.stamp fun k t (h : st.tables[k]? = some t) => Nat.le_succ_of_le (hD k t h).1
  have hcomp : ∀ (k : Nat) (t2 t' : Table S N A), st2.tables[k]? = some t2 →
      t'.groups = t2.groups → k ∈ completing st2 →
      ∃ gs, t'.groups = some gs ∧ ∃ gr ∈ gs, ∃ s ∈ gr.strats, s.quiet st' st'.isDone = true ∧
        ∀ k l side o subs dead reads c fc, s = .push k l side o subs dead reads c fc → st2.isDone side = true := by
    intro k t2 t' h2 e3 h
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
        quiet_mono (fun _ => hS23.isDone) (fun j hj => ?_) hq,
        fun k l side o subs dead reads c e => by subst e; exact quiet_push_side hq⟩
      rcases Bool.or_eq_true_iff.1 hj with hj | hj
      · exact hS23.isDone hj
      · have hj' := List.contains_iff_mem.1 hj
        have hjS := (gfpFrom_closed _ _ _ (Nat.le_refl _) j hj').1
        have hlt : j < st2.tables.length := List.mem_range.1 (List.mem_filter.1 hjS).1
        have hj'' : j ∈ completing st2 := hj'
        rw [← hst']
        simp [StateOf.isDone, StateOf.answers, List.getElem?_mapIdx,
          List.getElem?_eq_getElem hlt, hj'']
  refine ⟨hr'.trans hr2, hS01.trans (T.keep.stable.trans hS23), by rw [hd']; exact T.depth,
    fun k t' hk => ?_, fun k t' hk hn => ?_, fun k t t' ht hk hyp => ?_, fun k t' hk hdn => ?_,
    fun k t t' ht hk hs => ?_, hset 0 h0, fun hF => ?_, fun X hX k hk => ?_,
    fun k t t' ht hk hyp => ?_, fun k t t' ht hk hs => ?_,
    fun k => by
      rw [hf23 k]
      exact ⟨(T.fed k).1, fun h => hset k ((T.fed k).2 h)⟩⟩
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
    · rcases T.done k t2 h2 h with h | h | h
      · exact .inl h
      · exact .inr (.inl (h.mono hS23 e3))
      · exact .inr (.inr (h.mono hS23))
    · obtain ⟨gs, hgs, gr, hgr, s, hs, hq, -⟩ := hcomp k t2 t' h2 e3 h
      exact .inr (.inl ⟨gs, hgs, gr, hgr, s, hs, hq⟩)
  · obtain ⟨t2, h2, -, e2, e3, -⟩ := hsame k t' hk
    rw [e3]
    have hs2 : t2.stamp = st.round + 1 := by rw [← e2, hs, hr', hr2]
    have hne : t.stamp ≠ st.round + 1 := fun e => by
      have := (hD k t ht).1
      omega
    exact ((T.turn k t t2 (fun e => by cases e) ht h2 hne hs2).finish hS23 hset
      (Nat.le_of_eq hd'.symm) fun j => Nat.le_of_eq (hf23 j).symm).start hS01 (Nat.le_refl _)
      fun _ => Nat.le_refl _
  · refine Founded.step hS23 (fun k t2 t' h2 hk _ => ?_) (fun k t' hk hdn => ?_) (T.founded hF)
    · obtain ⟨u, hu, -, -, e3, -⟩ := hsame k t' hk
      rw [h2] at hu
      cases hu
      exact e3
    · obtain ⟨t2, h2, -, -, e3, -, e5⟩ := hsame k t' hk
      rcases e5 hdn with h | h
      · exact .inl ⟨t2, h2, h⟩
      · exact .inr (.inl (hcomp k t2 t' h2 e3 h))
  · have hans : ∀ j, st'.answers j = st2.answers j := by
      intro j
      rw [← hst']
      simp only [StateOf.answers, List.getElem?_mapIdx]
      cases st2.tables[j]? with
      | none => rfl
      | some t =>
        simp only [Option.map_some]
        split <;> rfl
    have hdone : ∀ j, st'.isDone j = true → st2.isDone j = true ∨ j ∈ completing st2 := by
      intro j hj
      cases ht' : st'.tables[j]? with
      | none => simp [StateOf.isDone, ht'] at hj
      | some t' =>
        obtain ⟨t2, h2, -, -, -, -, e5⟩ := hsame j t' ht'
        have hd : t'.done = true := by simpa [StateOf.isDone, ht'] using hj
        exact (e5 hd).imp (fun h => by simp [StateOf.isDone, h2, h]) id
    have hmark : ∀ j, j ∈ completing st2 → st'.isDone j = true := by
      intro j hj
      have hjS : j ∈ _ := gfpFrom_sub _ _ _ j hj
      have hlt : j < st2.tables.length := List.mem_range.1 (List.mem_filter.1 hjS).1
      rw [← hst']
      simp [StateOf.isDone, List.getElem?_mapIdx, List.getElem?_eq_getElem hlt, hj]
    have hopenC : ∀ j, j ∈ completing st2 → st2.isDone j = false := by
      intro j hj
      have hjS : j ∈ _ := gfpFrom_sub _ _ _ j hj
      have h2 := (List.mem_filter.1 hjS).2
      cases ht : st2.tables[j]? with
      | none => simp [StateOf.isDone, ht]
      | some t =>
        simp only [ht, Bool.and_eq_true, Bool.not_eq_true'] at h2
        simp [StateOf.isDone, ht, h2.1]
    have hmem : ∀ j, j ∈ (X ++ completing st2).filter (fun j => !st2.isDone j) ↔
        (j ∈ X ∨ j ∈ completing st2) ∧ st2.isDone j = false := fun j => by simp [or_and_right]
    generalize (X ++ completing st2).filter (fun j => !st2.isDone j) = X2 at hmem
    have hsub : ∀ j ∈ X2, j ∈ completing st2 := by
      unfold completing
      refine subset_gfpFrom (fun A B hAB i hi => ?_) X2 (fun i hi => ?_) _ _ (fun i hi => ?_)
      · cases ht : st2.tables[i]? with
        | none => simp [ht] at hi
        | some t =>
          simp only [ht, List.any_eq_true] at hi ⊢
          obtain ⟨gr, hgr, s, hs, hq⟩ := hi
          refine ⟨gr, hgr, s, hs, quiet_mono' (fun _ _ _ _ _ _ _ _ _ h => ⟨h, rfl⟩) (fun j hj => ⟨?_, rfl⟩) hq⟩
          rcases Bool.or_eq_true_iff.1 hj with hj | hj
          · simp [hj]
          · simp [hAB j (List.contains_iff_mem.1 hj)]
      · obtain ⟨hi1, hi2⟩ := (hmem i).1 hi
        rcases hi1 with hi1 | hi1
        · obtain ⟨t', ht', gs, hgs, gr, hgr, s, hs, hq, hp⟩ := hX i hi1
          obtain ⟨t2, h2, -, -, e3, -⟩ := hsame i t' ht'
          simp only [h2, List.any_eq_true]
          refine ⟨gr, by rw [← e3, hgs]; exact hgr, s, hs,
            quiet_mono' (fun k l side o subs dead reads c e _ =>
              ⟨((hS01.trans T.keep.stable).isDone (hp k l side o subs dead reads c e)).1,
                (hans _).symm⟩)
              (fun j hj => ⟨?_, (hans j).symm⟩) hq⟩
          cases hj2 : st2.isDone j with
          | true => rfl
          | false =>
            simp only [Bool.false_or]
            refine List.contains_iff_mem.2 ((hmem j).2 ⟨?_, hj2⟩)
            rcases Bool.or_eq_true_iff.1 hj with hj | hj
            · exact .inr ((hdone j hj).resolve_left (by rw [hj2]; exact Bool.false_ne_true))
            · exact .inl (List.contains_iff_mem.1 hj)
        · have hc := (gfpFrom_closed _ _ _ (Nat.le_refl _) i hi1).2
          cases ht : st2.tables[i]? with
          | none => simp [ht] at hc
          | some t =>
            simp only [ht, List.any_eq_true] at hc ⊢
            obtain ⟨gr, hgr, s, hs, hq⟩ := hc
            refine ⟨gr, hgr, s, hs,
              quiet_mono' (fun _ _ _ _ _ _ _ _ _ h => ⟨h, rfl⟩) (fun j hj => ⟨?_, rfl⟩) hq⟩
            rcases Bool.or_eq_true_iff.1 hj with hj | hj
            · simp [hj]
            · have hj' : j ∈ completing st2 := List.contains_iff_mem.1 hj
              simp [(hmem j).2 ⟨.inr hj', hopenC j hj'⟩]
      · obtain ⟨hi1, hi2⟩ := (hmem i).1 hi
        rcases hi1 with hi1 | hi1
        · obtain ⟨t', ht', gs, hgs, -⟩ := hX i hi1
          obtain ⟨t2, h2, -, -, e3, -⟩ := hsame i t' ht'
          have hd2 : t2.done = false := by simpa [StateOf.isDone, h2] using hi2
          refine List.mem_filter.2 ⟨List.mem_range.2 (List.getElem?_eq_some_iff.1 h2).1, ?_⟩
          simp [h2, hd2, ← e3, hgs]
        · exact gfpFrom_sub _ _ _ i hi1
    cases hk2 : st2.isDone k with
    | true => exact (hS23.isDone hk2).1
    | false => exact hmark k (hsub k ((hmem k).2 ⟨.inl hk, hk2⟩))
  · obtain ⟨t2, h2, -, e2, -⟩ := hsame k t' hk
    obtain ⟨u, hu, er⟩ := hsameR k t' hk
    rw [h2] at hu
    cases hu
    rw [er.1, er.2]
    refine T.race k t t2 ht h2 (hyp.imp id fun h => .inr ⟨(fun e => by cases e), fun e => h ?_⟩)
    rw [e2, hr', hr2]
    exact e
  · obtain ⟨t2, h2, -, e2, -, e4, -⟩ := hsame k t' hk
    obtain ⟨u, hu, er⟩ := hsameR k t' hk
    rw [h2] at hu
    cases hu
    have hs2 : t2.stamp = st.round + 1 := by rw [← e2, hs, hr', hr2]
    have hne : t.stamp ≠ st.round + 1 := fun e => by
      have := (hD k t ht).1
      omega
    exact (T.asked k t t2 (fun e => by cases e) ht h2 hne hs2).finish er e4

end pure

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D} {Rc : RaceSem R Rel (Ans D P)}

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

/-- The work of a strategy leaves the race of every table and the number of
its rounds. -/
theorem Inner.race {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK j st st') :
    ∀ (k : Nat) (t t' : Table R Rel (Ans D P)), st.tables[k]? = some t →
      st'.tables[k]? = some t' → t'.race = t.race ∧ t'.rounds = t.rounds := by
  induction h with
  | refl st => intro k t t' h h'; rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
  | @trans a b c hab hbc ih1 ih2 =>
    intro k t t' ha hc
    obtain ⟨tb, hb, -⟩ := hab.frame.2.1 k t ha
    exact ⟨(ih2 k tb t' hb hc).1.trans (ih1 k t tb ha hb).1,
      (ih2 k tb t' hb hc).2.trans (ih1 k t tb ha hb).2⟩
  | @same st st' e _ _ _ =>
    intro k t t' h h'
    have hf : st'.frames[k]? = st.frames[k]? := by rw [e]
    simp only [StateOf.frames, List.getElem?_map, h, h', Option.map_some, Option.some.injEq,
      Table.frame, Prod.mk.injEq] at hf
    exact ⟨hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1⟩
  | @opened st st' g self e _ _ _ =>
    intro k t t' h h'
    have hf : st'.frames[k]? =
        (st.frames ++ [(g, self, [], false, st.round, 0, none, none, 0, 0)])[k]? := by rw [e]
    have hlt : k < st.frames.length := by
      simp only [StateOf.frames, List.length_map]
      exact (List.getElem?_eq_some_iff.1 h).1
    rw [List.getElem?_append_left hlt] at hf
    simp only [StateOf.frames, List.getElem?_map, h, h', Option.map_some, Option.some.injEq,
      Table.frame, Prod.mk.injEq] at hf
    exact ⟨hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1⟩
  | add st a =>
    intro k t t' h h'
    have one : ∀ (s : StateOf R Rel (Ans D P)) (blk : List (Ans D P))
        (u u' : Table R Rel (Ans D P)), s.tables[k]? = some u →
        (s.modify j (app blk)).tables[k]? = some u' →
        u'.race = u.race ∧ u'.rounds = u.rounds := by
      intro s blk u u' hu hu'
      rcases getElem?_modify_cases s j _ hu' with ⟨-, h2⟩ | ⟨rfl, v, hv, rfl⟩
      · rw [hu] at h2; cases h2; exact ⟨rfl, rfl⟩
      · rw [hu] at hv; cases hv; exact ⟨rfl, rfl⟩
    rw [addAnswer_val] at h'
    split at h'
    · rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
    · split at h'
      · split at h'
        · exact one st _ t t' h h'
        · obtain ⟨tb, hb, -⟩ := (Frame.of_app j st [a]).2.1 k t h
          exact ⟨(one _ _ tb t' hb h').1.trans (one st _ t tb h hb).1,
            (one _ _ tb t' hb h').2.trans (one st _ t tb h hb).2⟩
      · exact one st _ t t' h h'

/-- The work of a strategy leaves what every table has been fed. -/
theorem Inner.fed {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK j st st') :
    ∀ (k : Nat) (t t' : Table R Rel (Ans D P)), st.tables[k]? = some t →
      st'.tables[k]? = some t' → t'.fed = t.fed := by
  induction h with
  | refl st => intro k t t' h h'; rw [h] at h'; cases h'; rfl
  | @trans a b c hab hbc ih1 ih2 =>
    intro k t t' ha hc
    obtain ⟨tb, hb, -⟩ := hab.frame.2.1 k t ha
    exact (ih2 k tb t' hb hc).trans (ih1 k t tb ha hb)
  | @same st st' e _ _ _ =>
    intro k t t' h h'
    have hf : st'.frames[k]? = st.frames[k]? := by rw [e]
    simp only [StateOf.frames, List.getElem?_map, h, h', Option.map_some, Option.some.injEq,
      Table.frame, Prod.mk.injEq] at hf
    exact hf.2.2.2.2.2.2.2.2.2
  | @opened st st' g self e _ _ _ =>
    intro k t t' h h'
    have hf : st'.frames[k]? =
        (st.frames ++ [(g, self, [], false, st.round, 0, none, none, 0, 0)])[k]? := by rw [e]
    have hlt : k < st.frames.length := by
      simp only [StateOf.frames, List.length_map]
      exact (List.getElem?_eq_some_iff.1 h).1
    rw [List.getElem?_append_left hlt] at hf
    simp only [StateOf.frames, List.getElem?_map, h, h', Option.map_some, Option.some.injEq,
      Table.frame, Prod.mk.injEq] at hf
    exact hf.2.2.2.2.2.2.2.2.2
  | add st a =>
    intro k t t' h h'
    have one : ∀ (s : StateOf R Rel (Ans D P)) (blk : List (Ans D P))
        (u u' : Table R Rel (Ans D P)), s.tables[k]? = some u →
        (s.modify j (app blk)).tables[k]? = some u' → u'.fed = u.fed := by
      intro s blk u u' hu hu'
      rcases getElem?_modify_cases s j _ hu' with ⟨-, h2⟩ | ⟨rfl, v, hv, rfl⟩
      · rw [hu] at h2; cases h2; rfl
      · rw [hu] at hv; cases hv; rfl
    rw [addAnswer_val] at h'
    split at h'
    · rw [h] at h'; cases h'; rfl
    · split at h'
      · split at h'
        · exact one st _ t t' h h'
        · obtain ⟨tb, hb, -⟩ := (Frame.of_app j st [a]).2.1 k t h
          exact (one _ _ tb t' hb h').trans (one st _ t tb h hb)
      · exact one st _ t t' h h'

/-- The work of a strategy feeds no table. -/
theorem Inner.fedAt {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK j st st')
    (k : Nat) : st.fedAt k ≤ st'.fedAt k ∧ (st.fedAt k < st'.fedAt k → Settled st' k) := by
  cases ht : st.tables[k]? with
  | none =>
    refine ⟨by simp [StateOf.fedAt, ht], fun _ t' ht' => .inr (.inr ?_)⟩
    rw [(h.frame.2.2 k t' ht' ht).2.1, h.frame.1]
  | some t =>
    obtain ⟨t', ht', -⟩ := h.frame.2.1 k t ht
    have := h.fed k t t' ht ht'
    simp only [StateOf.fedAt, ht, ht', this]
    exact ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

/-- The record of the work of a strategy of an open table. -/
theorem Inner.turns {j : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Inner K hK j st st')
    (ho : Open st j) : Turns (readNeed P) Rc st st' := by
  have hf := h.frame
  have hopen : ∀ t, st.tables[j]? = some t → t.done = false := fun t ht => by
    obtain ⟨u, hu, hd⟩ := ho
    rw [ht] at hu
    cases hu
    exact hd
  refine TurnsBut.of_open (hf.keep hopen) h.depth_le (fun hs k t' hk => ?_)
    (fun k t t' ht ht' _ => ?_) (fun k t' hk hd => ?_) (fun k t t' _ ht ht' hs hs' => ?_)
    (fun k t' _ hk _ hyp => ?_) (fun k t t' ht ht' _ => h.race k t t' ht ht')
    (fun k t t' _ ht ht' hs hs' => ?_) h.fedAt
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
      exact ⟨t, rfl, by rw [← e2]; exact hd⟩
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
      (f t).done = t.done ∧ ((f t).stamp = t.stamp ∨ (f t).stamp = st.round))
    (hr : ∀ t, st.tables[i]? = some t → t.stamp = st.round →
      (f t).race = t.race ∧ (f t).rounds = t.rounds)
    (ho : ∀ t, st.tables[i]? = some t → t.done = false)
    (hfed : ∀ t, (f t).fed = t.fed := by intro _; rfl) :
    TurnsBut (readNeed P) Rc (some i) st (st.modify i f) := by
  refine TurnsBut.of_open (keep_modify st i f fun t _ => ⟨(hf t).1, (hf t).2.1, (hf t).2.2.1,
      fun h => by rw [(hf t).2.2.2.1]; exact h,
      fun h => ⟨by rcases (hf t).2.2.2.2 with e | e
                   · rw [e]; exact h
                   · exact e,
        fun h => by rw [(hf t).2.2.2.1]; exact h⟩⟩)
    (Nat.le_refl _) (fun hs k t' hk => ?_) (fun k t t' ht ht' hyp => ?_) (fun k t' hk hd => ?_)
    (fun k t t' hx ht ht' hs hs' => ?_) (fun k t' hx hk _ hyp => ?_)
    (fun k t t' ht ht' hyp => ?_) (fun k t t' hx ht ht' hs hs' => ?_) (fun k => ?_)
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
    · exact ⟨t', h, hd⟩
    · exact ⟨t, ht, by rw [← (hf t).2.2.2.1]; exact hd⟩
  · rcases getElem?_modify_cases st i f ht' with ⟨-, h⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h
      cases h
      exact absurd hs' hs
    · exact absurd rfl hx
  · rcases getElem?_modify_cases st i f hk with ⟨-, h⟩ | ⟨rfl, u, hu, rfl⟩
    · exact hyp t' h
    · exact absurd rfl hx
  · rcases getElem?_modify_cases st i f ht' with ⟨-, h⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h
      cases h
      exact ⟨rfl, rfl⟩
    · rw [ht] at hu
      cases hu
      rcases hyp with hd | hst | ⟨hx, -⟩
      · rw [ho t ht] at hd
        cases hd
      · exact hr t ht hst
      · exact absurd rfl hx
  · rcases getElem?_modify_cases st i f ht' with ⟨-, h⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h
      cases h
      exact absurd hs' hs
    · exact absurd rfl hx
  · rw [fedAt_modify_same st i f hfed k]
    exact ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

omit [DecidableEq R] in
/-- The record of adding to what a table that needs no round has been
fed. -/
theorem turnsBut_fed (x : Option Nat) (st : StateOf R Rel (Ans D P)) (h c : Nat)
    (hs : Settled st h) :
    TurnsBut (readNeed P) Rc x st (st.modify h fun t => { t with fed := t.fed + c }) := by
  have hkp : Keep st (st.modify h fun t => { t with fed := t.fed + c }) :=
    keep_modify st h _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h, fun h => ⟨h, fun h => h⟩⟩
  refine TurnsBut.of_open hkp (Nat.le_refl _) (fun hst k t' hk => ?_)
    (fun k t t' ht ht' _ => ?_) (fun k t' hk hd => ?_) (fun k t t' _ ht ht' hs0 hs' => ?_)
    (fun k t' _ hk _ hyp => ?_) (fun k t t' ht ht' _ => ?_)
    (fun k t t' _ ht ht' hs0 hs' => ?_) (fun k => ⟨fedAt_feed_le st h c k, fun hlt => ?_⟩)
  · rcases getElem?_modify_cases st h _ hk with ⟨-, h1⟩ | ⟨rfl, t, ht, rfl⟩
    · exact hst k t' h1
    · exact hst k t ht
  · rcases getElem?_modify_cases st h _ ht' with ⟨-, h1⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h1; cases h1; rfl
    · rw [ht] at hu; cases hu; rfl
  · rcases getElem?_modify_cases st h _ hk with ⟨-, h1⟩ | ⟨rfl, t, ht, rfl⟩
    · exact ⟨t', h1, hd⟩
    · exact ⟨t, ht, hd⟩
  · rcases getElem?_modify_cases st h _ ht' with ⟨-, h1⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h1; cases h1; exact absurd hs' hs0
    · rw [ht] at hu; cases hu; exact absurd hs' hs0
  · rcases getElem?_modify_cases st h _ hk with ⟨-, h1⟩ | ⟨rfl, t, ht, rfl⟩
    · exact hyp t' h1
    · exact hyp t ht
  · rcases getElem?_modify_cases st h _ ht' with ⟨-, h1⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h1; cases h1; exact ⟨rfl, rfl⟩
    · rw [ht] at hu; cases hu; exact ⟨rfl, rfl⟩
  · rcases getElem?_modify_cases st h _ ht' with ⟨-, h1⟩ | ⟨rfl, u, hu, rfl⟩
    · rw [ht] at h1; cases h1; exact absurd hs' hs0
    · rw [ht] at hu; cases hu; exact absurd hs' hs0
  · by_cases e : k = h
    · subst e
      exact hkp.settled hs
    · rw [fedAt_feed_ne st h c e] at hlt
      exact absurd hlt (Nat.lt_irrefl _)

/-- A reading of an edge that was not deep enough doubles the depth. -/
theorem edgeOf_none (st : StateOf R Rel (Ans D P)) (last : Bool) (n : Rel) :
    (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.2 = none →
      (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1.depth = 2 * st.depth ∧
        st.depth < readNeed P n := by
  have hlive := readEdge_some (K := K) (hK := hK) (P := P) last st.depth n
  at_cost K hK
  simp only [edgeOf, Cost.bind_val]
  split
  · intro h
    cases h
  · simp only [Cost.bind_val, Cost.pure_val]
    cases hr : (readEdge (K := DerivationKernel.over D _ hK P) last st.depth n).val with
    | none => exact fun _ => ⟨rfl, Nat.lt_of_not_le fun h => hlive h hr⟩
    | some e => intro h; cases h

/-- **The work of a push moves it on**: every answer of its side is seen and
every answer of the tables it reads is filed, and each unit that was to take
is taken, or is of an answer superseded, or is nearer to its turn. -/
theorem step_work_push (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) (k : Kind)
    (left : Bool) (side : Nat) (other : Rel) (subs : List (Ans D P × Option (Nat × Nat)))
    (dead : Option (List Nat)) (reads : List (Nat × Option Nat)) (c : Cursor)
    (hp : Prog st i g (.push k left side other subs dead reads c fc)) :
    SStep (readNeed P) st.len st.isDone st.depth
      (work (K := DerivationKernel.over D K hK P) i g st
        (.push k left side other subs dead reads c fc)).val.1.depth
      (.push k left side other subs dead reads c fc)
      (work (K := DerivationKernel.over D K hK P) i g st
        (.push k left side other subs dead reads c fc)).val.2.1 := by
  have hp0 := hp
  dsimp only [Prog] at hp0
  obtain ⟨L, Rg, -, -, -, h4, hD, h5, hfit, -⟩ := hp0
  have hlen : subs.length ≤ (st.answers side).length := by
    have := congrArg List.length h4
    simp only [List.length_map, List.length_take] at this
    omega
  have hsup := superseded_spec (K := K) (hK := hK) (P := P) st side dead
  have hP := fun dz (h1 : ∀ d, dz = some d → st.isDone side = true ∧
      DeadOk D P (st.answers side) (st.answers side).length d)
      (h2 : ∀ d, dead = some d → dz = some d) =>
    prog_push_file i g k left side other subs dead reads c dz h1 h2 hp
  have hgs := seeSide_grows (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c
  have hss := seeSide_subs (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c
  have hsd := seeSide_done (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c
  have hsp := seeSide_prefix (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c
  at_cost K hK
  simp only [work, Cost.bind_val]
  generalize (superseded (K := DerivationKernel.over D _ hK P) st side dead).val = dead0
    at hsup ⊢
  replace hP := hP dead0 (fun d hd => by
    rcases hsup.2.1 d hd with h | ⟨-, h1, h2⟩
    · subst h
      exact ⟨hD.1, hD.2.2⟩
    · exact ⟨h1, h2⟩) hsup.1
  generalize seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c = f0 at hP hgs hss hsd hsp ⊢
  have hfe := pushFile_getElem? st (dead0.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead0.getD []))
  have hfl := pushFile_length st (dead0.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead0.getD []))
  have hfd : (pushFile st (dead0.getD []) 0 f0.2.1 (f0.2.2.kill (dead0.getD [])) f0.1).2.2.done = f0.2.2.done :=
    pushFile_done st (dead0.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead0.getD []))
  have hfp := pushFile_prefix st (dead0.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead0.getD []))
  have hgf := pushFile_grows st (dead0.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead0.getD []))
  generalize hfdef : pushFile st (dead0.getD []) 0 f0.2.1 (f0.2.2.kill (dead0.getD [])) f0.1 = f
  rw [hfdef] at hP hfe hfl hfd hfp hgf
  obtain ⟨subs', reads', c'⟩ := f
  dsimp only at hP hfe hfl hfd hfp hgf ⊢
  have hP0 := hP
  dsimp only [Prog] at hP0
  obtain ⟨-, -, -, -, -, -, -, -, hfit', -⟩ := hP0
  have hseen : subs'.length = (st.answers side).length := by
    rw [hfl, hss, List.length_append, List.length_map, List.length_drop, List.length_zip,
      pathsAt_length, Nat.min_self]
    omega
  have hA : PAdv subs dead reads c subs' dead0 reads' c' := by
    refine ⟨⟨by rw [hseen]; exact hlen, fun n e e' he he' => ?_⟩, hsup.1,
      hsp.trans hfp, fun p q h => ?_, fun p q h => ?_⟩
    · have h0 : f0.1[n]? = some e := by
        rw [hss, List.getElem?_append_left (List.getElem?_eq_some_iff.1 he).1]
        exact he
      rw [hfe, h0] at he'
      cases he'
      refine ⟨rfl, fun t ht => ?_⟩
      dsimp only
      rw [ht]
      refine ⟨_, rfl, rfl, ?_⟩
      dsimp only
      split
      · exact Nat.le_refl _
      · rw [pathsAt_length]
        exact (h5 e (List.mem_of_getElem? he) t ht).2
    · show (p, q) ∈ c'.done
      rw [hfd, hsd]
      exact h
    · by_cases hd : p ∈ (dead0.getD [])
      · exact .inr (.inl hd)
      · obtain ⟨b1, b2⟩ := hfit.todo_lt h
        have h1 : (p, q) ∈ (f0.2.2.kill (dead0.getD [])).todo := Cursor.mem_kill.2 ⟨hgs.1 _ h, hd⟩
        refine .inr (.inr ⟨hgf.1 _ h1, .inl ?_⟩)
        rw [hgf.2.2.2 p q (Nat.lt_of_lt_of_le b1 hgs.2.1) (Nat.lt_of_lt_of_le b2 hgs.2.2.1),
          Cursor.rank_kill]
        exact hgs.2.2.2 p q b1 b2
  have hC : ∀ (n : Nat) (x : Ans D P) (t : Nat × Nat), subs'[n]? = some (x, some t) →
      n ∉ (dead0.getD []) → st.len t.1 ≤ t.2 := by
    intro n x t he hn
    rw [hfe] at he
    cases h0 : f0.1[n]? with
    | none => rw [h0] at he; cases he
    | some e0 =>
      rw [h0] at he
      rcases e0 with ⟨x0, _ | t0⟩
      · cases he
      · cases he
        have hc : (dead0.getD []).contains (0 + n) = false := by simpa using hn
        simp only [hc, Bool.false_eq_true, ite_false, pathsAt_length]
        exact Nat.le_refl _
  split
  · next hnext =>
    refine .push hA ⟨fun p q h => ?_, Nat.le_of_eq hseen.symm, fun n x t he hn => ?_,
      hsup.2.2⟩
    · rcases hA.rank p q h with h | h | ⟨h, -⟩
      · exact .inl h
      · exact .inr (.inl h)
      · rw [Cursor.next_none_todo hnext] at h
        cases h
    · obtain ⟨t', ht', e1, -⟩ := hA.adv.get he
      exact ⟨t', ht', by rw [← e1]; exact hC n x t' ht' hn⟩
  · next p hnext =>
    obtain ⟨hnb, -, -⟩ := hfit'.next hnext
    have fin : ∀ (subs'' : List (Ans D P × Option (Nat × Nat))) (tt : Nat), 0 < tt →
        PushAdv subs' subs'' → subs''.length = subs'.length →
        (∀ (n : Nat) (x : Ans D P) (t : Nat × Nat), subs'[n]? = some (x, some t) → subs''[n]? = some (x, some t)) → ∀ d',
        SStep (readNeed P) st.len st.isDone st.depth d'
          (.push k left side other subs dead reads c fc)
          (.push k left side other subs'' dead0 reads' (c'.mark p tt) fc) := by
      intro subs'' tt htt hadv hl hkeep d'
      refine SStep.after (.push hA) (.push ⟨hadv, fun _ h => h, List.prefix_rfl,
        fun a b h => Cursor.before_mark.2 (.inl h), fun a b h => ?_⟩
        ⟨fun a b h => ?_, by rw [hl]; exact Nat.le_of_eq hseen.symm,
          fun n x t he hn => ⟨t, hkeep n x t he, hC n x t he hn⟩, hsup.2.2⟩) (Nat.le_refl _)
      · by_cases e : p = (a, b)
        · exact .inl (Cursor.before_mark.2 (.inr e))
        · exact .inr (.inr ⟨List.mem_filter.2 ⟨h, by
            simpa [bne_iff_ne] using fun h' : (a, b) = p => e h'.symm⟩,
            .inr (Cursor.rank_fall_todo hnb htt hnext h)⟩)
      · by_cases e : p = (a, b)
        · exact .inl (Cursor.before_mark.2 (.inr e))
        · exact .inr (.inr ⟨List.mem_filter.2 ⟨h, by
            simpa [bne_iff_ne] using fun h' : (a, b) = p => e h'.symm⟩,
            Cursor.rank_fall_todo hnb htt hnext h⟩)
    split
    · next x a hx hr =>
      simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      refine fin _ _ (Nat.succ_pos _) (PushAdv.set_open hx _) (List.length_set ..)
        (fun n x' t he => ?_) _
      by_cases en : p.1 = n
      · subst en
        rw [hx] at he
        cases he
      · rw [List.getElem?_set_ne en]
        exact he
    · simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      exact fin _ _ (Nat.succ_pos _) (PushAdv.refl _) rfl (fun _ _ _ h => h) _
    · exact fin _ _ Nat.one_pos (PushAdv.refl _) rfl (fun _ _ _ h => h) _

/-- **The work of a strategy moves it on**: a span is tried; a call or a
union is nearer to every answer that was there; a join is nearer to every
pair that was there; a check still to be read is read, or the depth has
doubled. -/
theorem step_work (i : Nat) (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (s : Strat Rel (Ans D P)) (hp : Prog st i g s) :
    SStep (readNeed P) st.len st.isDone st.depth
      (work (K := DerivationKernel.over D K hK P) i g st s).val.1.depth s
      (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1 := by
  have hedge := edgeOf_none (K := K) (hK := hK) (P := P) st
  have hok : ∀ k a b c, s = .join k a b c → c.Ok (st.len a) (st.len b) := fun k a b c e => by
    subst e
    dsimp only [Prog] at hp
    obtain ⟨L, Rg, -, -, -, hok, -⟩ := hp
    exact hok
  have hpush := fun k left side other subs dead reads c
      (e : s = .push k left side other subs dead reads c fc) =>
    step_work_push (K := K) (hK := hK) i g st k left side other subs dead reads c (e ▸ hp)
  clear hp
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
    obtain ⟨hsok, hsa, hsb⟩ := hc.see (pathsAt_length st a) (pathsAt_length st b)
    have hlen : c.pa.length ≤ (c.see (st.pathsAt a) (st.pathsAt b)).pa.length ∧
        c.pb.length ≤ (c.see (st.pathsAt a) (st.pathsAt b)).pb.length := by
      rw [hsa, hsb]
      exact ⟨hc.1, hc.2.1⟩
    split
    · next hx =>
      have hnone := Cursor.next_none hsok hx
      rw [hsa, hsb] at hnone
      exact .join (fun _ _ h => h) (fun p q hp hq => .inl (hnone p q
          (Nat.lt_of_lt_of_le hp hc.1) (Nat.lt_of_lt_of_le hq hc.2.1))) hlen
        ⟨Nat.le_of_eq hsa.symm, Nat.le_of_eq hsb.symm⟩ (.inl hnone)
    · next pr hx =>
      simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      obtain ⟨-, n2, -, n4⟩ := Cursor.next_spec
        ((joinPairs (K := DerivationKernel.over D _ hK P) i k (st.answers a) (st.answers b) st
          [pr]).ticks + 1) hsok hx
      refine .join (fun p q h => Cursor.before_mark.2 (.inl h)) (fun p q hp hq => ?_) hlen
        ⟨Nat.le_of_eq hsa.symm, Nat.le_of_eq hsb.symm⟩ (.inr ⟨pr.1, pr.2, n2, n4⟩)
      by_cases hb : c.Before p q
      · exact .inl (Cursor.before_mark.2 (.inl hb))
      · right
        rw [← Cursor.rank_see (st.pathsAt a) (st.pathsAt b) c hp hq]
        exact Cursor.rank_fall hsok (Nat.succ_pos _) hx (Cursor.mem_left.2
          ⟨⟨Nat.lt_of_lt_of_le hp hlen.1, Nat.lt_of_lt_of_le hq hlen.2⟩, hb⟩)
  | push k left side other subs dead reads c fc =>
    exact hpush k left side other subs dead reads c rfl
  | check left side other c =>
    cases c with
    | reading =>
      simp only [work, Cost.bind_val]
      split
      · next heq => exact .check (.inl rfl) fun _ => .inr ⟨Nat.le_of_eq (hedge left side heq).1.symm, (hedge left side heq).2⟩
      · exact .check (.inl rfl) fun _ => .inl (fun h => by cases h)
      · simp only [Cost.bind_val, Cost.pure_val]
        exact .check (.inl rfl) fun _ => .inl (fun h => by cases h)
    | off => exact .check (.inr rfl) (fun h => by cases h)
    | opened subs => exact .check (.inr rfl) (fun h => by cases h)

/-- **A turn with ticks to spend moves its strategy on**: it begins with a
unit of work, and the units after it move the strategy further. -/
theorem step_turn (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) {i : Nat}
    {g : GoalOf R Rel} (hg : GoodG D g) {st0 : StateOf R Rel (Ans D P)}
    {s0 : Strat Rel (Ans D P)} (f : Nat) :
    ∀ (left : Nat) (st : StateOf R Rel (Ans D P)) (s : Strat Rel (Ans D P)) (c : Nat),
      UnitOk K hK i g st0 s0 st s → left ≠ 0 →
      SStep (readNeed P) st.len st.isDone st.depth
        (turn (K := DerivationKernel.over D K hK P) i g (f + 1) left st s c).val.1.depth s
        (turn (K := DerivationKernel.over D K hK P) i g (f + 1) left st s c).val.2.1 := by
  induction f with
  | zero =>
    intro left st s c h hl
    have hw := step_work (K := K) (hK := hK) (P := P) i g st s h.prog
    rw [turn_succ i g 0 left st s c hl]
    split
    · rw [turn_fuel_zero]
      exact hw
    · exact hw
  | succ f ih =>
    intro left st s c h hl
    have hw := step_work (K := K) (hK := hK) (P := P) i g st s h.prog
    have h1 := h.work hL hR hg
    have hin := inner_work (K := K) (hK := hK) (P := P) i g st s
    have hS := hin.frame.stable h.isOpen
    rw [turn_succ i g (f + 1) left st s c hl]
    split
    · generalize left - ((work (K := DerivationKernel.over D K hK P) i g st s).ticks + 1) = left'
      generalize c + (work (K := DerivationKernel.over D K hK P) i g st s).ticks + 1 = c'
      by_cases hl' : left' = 0
      · rw [hl', turn_zero]
        exact hw
      · exact SStep.after hw.adv ((ih left' _ _ c' h1 hl').mono hS.len_le (fun _ h => (hS.isDone h).1)
          (Nat.le_refl _) (Nat.le_refl _)) hin.depth_le
    · exact hw

/-- **The turn of a strategy**: it works on the table at `i` alone, the
strategy is itself later, and it has worked or owes less. -/
theorem turn_record (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat) (g : GoalOf R Rel) (k j o : Nat)
    (s : Strat Rel (Ans D P)) (hg : goalAt st i = some g) (hb : Busy st i)
    (hs : ((groupsAt st i)[k]?).bind (·.strats[j]?) = some s) :
    Inner K hK i st (turn (K := DerivationKernel.over D K hK P) i g
        (turnTicks * weight st s - o) (turnTicks * weight st s - o) st s 0).val.1 ∧
      SAdv s (turn (K := DerivationKernel.over D K hK P) i g
        (turnTicks * weight st s - o) (turnTicks * weight st s - o) st s 0).val.2.1 ∧
      OStep (readNeed P) st.len st.isDone st.depth (turn (K := DerivationKernel.over D K hK P) i g
        (turnTicks * weight st s - o) (turnTicks * weight st s - o) st s 0).val.1.depth o
        (o + (turn (K := DerivationKernel.over D K hK P) i g
          (turnTicks * weight st s - o) (turnTicks * weight st s - o) st s 0).val.2.2 -
            turnTicks * weight st s) s
        (turn (K := DerivationKernel.over D K hK P) i g
          (turnTicks * weight st s - o) (turnTicks * weight st s - o) st s 0).val.2.1 := by
  refine ⟨inner_turn i g _ _ st s 0, ?_⟩
  have hpos : 0 < turnTicks * weight st s := by
    simp only [turnTicks, weight]
    omega
  generalize hfl : turnTicks * weight st s - o = fl
  cases fl with
  | zero =>
    rw [turn_zero]
    exact ⟨SAdv.refl s, .inr (by dsimp only; omega)⟩
  | succ fl =>
    have hU : UnitOk K hK i g st s st s :=
      ⟨hG.inv, hG.base, hg, hb.isOpen, strat_of_groupsAt hG.inv hg hs,
        prog_of_groupsAt hG.prog hg hs, rfl, Inner.refl st⟩
    have h := step_turn hL hR (hG.base.good i g hg) fl (fl + 1) st s 0 hU (by omega)
    exact ⟨h.adv, .inl h⟩

/-! ## The shape of the groups a goal begins with -/

theorem lead_splitGroup (k : Kind) (L Rg : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) :
    ∃ s ∈ (splitGroup (K := DerivationKernel.over D K hK P) k L Rg st).val.2.strats,
      s.lead = true := by
  at_cost K hK
  simp only [splitGroup, Cost.bind_val, Cost.pure_val]
  exact ⟨_, List.mem_cons_self, rfl⟩

theorem check_checkOf (st : StateOf R Rel (Ans D P)) (left : Bool) (side other : Rel) :
    ∀ s ∈ (checkOf (K := DerivationKernel.over D K hK P) st left side other).val.2,
      s.isCheck = true := by
  at_cost K hK
  simp only [checkOf, Cost.bind_val, Cost.pure_val]
  intro s hs
  split at hs
  · cases hs
  · obtain rfl := List.mem_singleton.1 hs
    rfl

/-- A chain goal has a group for each of its splits, it has a split, and its
interface checks are checks. -/
theorem lead_chainGroups (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P))
    (hn : Normal g.node) {xs : List Rel} (hvc : g.node.view = .chain xs) :
    (∀ gr ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1,
      ∃ s ∈ gr.strats, s.lead = true) ∧
    (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1 ≠ [] ∧
    ∀ s ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.2,
      s.isCheck = true := by
  have h2 := (hn.view_chain hvc).1
  have hsp := hn.chain_split hvc (i := 1) (by omega) (by omega)
  have hlead := fun k L Rg st => lead_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  have hchk := fun st left side other =>
    check_checkOf (K := K) (hK := hK) (P := P) st left side other
  have key : (∀ gr ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1,
      ∃ s ∈ gr.strats, s.lead = true) ∧
      (1 ∈ (List.range xs.length).drop 1 →
        (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.1 ≠ []) ∧
      ∀ s ∈ (chainGroups (K := DerivationKernel.over D K hK P) g xs.length st).val.2.2,
        s.isCheck = true := by
    at_cost K hK
    refine foldL_done (fun done (acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) ×
        List (Strat Rel (Ans D P))) =>
      (∀ gr ∈ acc.2.1, ∃ s ∈ gr.strats, s.lead = true) ∧ (1 ∈ done → acc.2.1 ≠ []) ∧
        ∀ s ∈ acc.2.2, s.isCheck = true)
      _ _ (fun done b i _ hb => ?_) (st, [], [])
      ⟨(fun gr hgr => by cases hgr), (fun h => by cases h), fun s hs => by cases hs⟩
    simp only [Cost.bind_val]
    split
    · next l r hl hr =>
      simp only [Cost.bind_val, Cost.pure_val]
      refine ⟨fun gr hgr => ?_, (fun _ => by simp), fun s hs => ?_⟩
      · rcases List.mem_append.1 hgr with hgr | hgr
        · exact hb.1 gr hgr
        · obtain rfl := List.mem_singleton.1 hgr
          exact hlead _ _ _ _
      · rcases List.mem_append.1 hs with hs | hs
        · rcases List.mem_append.1 hs with hs | hs
          · exact hb.2.2 s hs
          · exact hchk _ _ _ _ s hs
        · exact hchk _ _ _ _ s hs
    · next hno =>
      refine ⟨hb.1, fun h1 => ?_, hb.2.2⟩
      rcases List.mem_append.1 h1 with h1 | h1
      · exact hb.2.1 h1
      · obtain rfl := List.mem_singleton.1 h1
        obtain ⟨-, l, r, hl, hr, -⟩ := hsp
        exact absurd hr (hno l r hl)
  refine ⟨key.1, key.2.1 ?_, key.2.2⟩
  rw [List.mem_drop_iff_getElem]
  exact ⟨0, by simp; omega, by simp⟩

/-- **The groups a goal begins with are shaped**: one of them has a span, a
call, a union or a join, and one that has none is all interface checks. -/
theorem shaped_expand (g : GoalOf R Rel) (st : StateOf R Rel (Ans D P)) (hn : Normal g.node) :
    Shaped (expand (K := DerivationKernel.over D K hK P) g st).val.2 := by
  have hch := fun xs hvc => lead_chainGroups (K := K) (hK := hK) (P := P) g st hn (xs := xs) hvc
  have hlead := fun k L Rg st => lead_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  at_cost K hK
  simp only [expand, Cost.bind_val]
  have one : ∀ s : Strat Rel (Ans D P), s.lead = true → Shaped [(⟨0, [s], []⟩ : Group Rel (Ans D P))] :=
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
    obtain ⟨h1, h2, h3⟩ := hch xs (forget_chain hv)
    split
    · exact shaped_all h2 h1
    · exact shaped_snoc h2 h1 _ h3
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
theorem groupsAt_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (hf : ∀ t, (f t).groups = t.groups)
    (j : Nat) : groupsAt (st.modify i f) j = groupsAt st j := by
  unfold groupsAt StateOf.modify
  simp only [List.getElem?_modify]
  by_cases e : i = j
  · subst e
    cases ht : st.tables[i]? <;> simp [hf]
  · cases ht : st.tables[j]? <;> simp [e]

omit [DecidableEq R] in
theorem groupsAt_setGroup (st : StateOf R Rel (Ans D P)) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P)) :
    groupsAt (setGroup st i k f) i = (groupsAt st i).modify k f := by
  unfold groupsAt setGroup StateOf.modify
  cases ht : st.tables[i]? with
  | none => simp [ht]
  | some t => cases hg : t.groups <;> simp [ht, hg]

omit [DecidableEq R] in
theorem fedAt_setGroup (st : StateOf R Rel (Ans D P)) (i k : Nat)
    (f : Group Rel (Ans D P) → Group Rel (Ans D P)) (j : Nat) :
    (setGroup st i k f).fedAt j = st.fedAt j := by
  unfold setGroup
  exact fedAt_modify_same st i (fun t => { t with groups := t.groups.map fun gs => gs.modify k f })
    (fun _ => rfl) j

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
theorem TurnsBut.groupsAt {st st' : StateOf R Rel (Ans D P)} (h : Turns (readNeed P) Rc st st') {i : Nat}
    (hb : Busy st i) : groupsAt st' i = groupsAt st i := by
  obtain ⟨t, ht, hs, -⟩ := hb
  obtain ⟨t', ht', -⟩ := h.keep.2.1 i t ht
  simp only [Symmetric.groupsAt, ht, ht',
    h.groups i t t' ht ht' (.inr ⟨(fun e => by cases e), .inl hs⟩)]

/-- What holds while the strategies of the group `k` of the table at `i`
work, from the state `st`, when those at the places `done` have worked. -/
structure StratsInv (Rc : RaceSem R Rel (Ans D P)) (st : StateOf R Rel (Ans D P)) (i : Nat) (g : GoalOf R Rel) (k : Nat)
    (done : List Nat) (X : StateOf R Rel (Ans D P)) : Prop where
  good : Good X
  goal : goalAt X i = some g
  busy : Busy X i
  turns : TurnsBut (readNeed P) Rc (some i) st X
  length : (groupsAt X i).length = (groupsAt st i).length
  others : ∀ k', k' ≠ k → (groupsAt X i)[k']? = (groupsAt st i)[k']?
  group : ∀ gr, (groupsAt st i)[k]? = some gr → ∃ gr', (groupsAt X i)[k]? = some gr' ∧
    gr'.level = gr.level ∧ GrAdv gr gr' ∧
    (∀ m ∈ done, ∀ s0 s, gr.strats[m]? = some s0 → gr'.strats[m]? = some s →
      OStep (readNeed P) st.len st.isDone st.depth X.depth (gr.owed.getD m 0)
        (gr'.owed.getD m 0) s0 s) ∧
    ∀ m, m ∉ done → gr'.owed.getD m 0 = gr.owed.getD m 0

/-- **The strategies of a group work**: each has had its turn, and nothing
else of the groups of the table has changed. -/
theorem turn_workStrats (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat) (g : GoalOf R Rel)
    (k : Nat) (hg : goalAt st i = some g) (hb : Busy st i) :
    StratsInv Rc st i g k (List.range (((groupsAt st i)[k]?.map (·.strats.length)).getD 0))
      (workStrats (K := DerivationKernel.over D K hK P) i g k st).val.1 := by
  have hstep := fun (st : StateOf R Rel (Ans D P)) hG j s f left c ow hg hb hs =>
    good_workStep (K := K) (hK := hK) hL hR (st := st) hG i g k j s f left c ow hg hb hs
  have hrec := fun (st : StateOf R Rel (Ans D P)) hG j o s hg hb hs =>
    turn_record (K := K) (hK := hK) hL hR (st := st) hG i g k j o s hg hb hs
  clear hR
  at_cost K hK
  simp only [workStrats]
  refine foldL_split (fun done (acc : StateOf R Rel (Ans D P) × Nat × Bool) =>
    StratsInv Rc st i g k done acc.1) _ _ (fun done rest b j hsplit hI => ?_) (st, 0, false)
    ⟨hG, hg, hb, TurnsBut.refl _ _, rfl, fun _ _ => rfl, fun gr h =>
      ⟨gr, h, rfl, Pointwise.refl SAdv.refl _, fun m hm => (by cases hm), fun _ _ => rfl⟩⟩
  have hjd : j ∉ done := by
    have hnd : (done ++ j :: rest).Nodup := hsplit ▸ List.nodup_range
    exact fun hj => (List.nodup_append.1 hnd).2.2 j hj j List.mem_cons_self rfl
  split
  · next hnone =>
    refine ⟨hI.good, hI.goal, hI.busy, hI.turns, hI.length, hI.others, fun gr hgr => ?_⟩
    obtain ⟨gr', h1, hlv, h2, h3, h4⟩ := hI.group gr hgr
    refine ⟨gr', h1, hlv, h2, fun m hm s0 s hs0 hs => ?_, fun m hm => h4 m fun h => hm
      (List.mem_append_left _ h)⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact h3 m hm s0 s hs0 hs
    · obtain rfl := List.mem_singleton.1 hm
      rw [h1] at hnone
      simp only [Option.bind_some, hs, Option.map_some] at hnone
      cases hnone
  · next s o hs =>
    obtain ⟨hs', grb, hgrb, rfl⟩ := pick_strat hs
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨hin, hadv, hos⟩ := hrec b.1 hI.good j (grb.owed.getD j 0) s hI.goal hI.busy hs'
    have hgd := hstep b.1 hI.good j s (turnTicks * weight b.1 s - grb.owed.getD j 0)
      (turnTicks * weight b.1 s - grb.owed.getD j 0) 0
      (fun l => setOwed l j (grb.owed.getD j 0 + (turn (K := DerivationKernel.over D _ hK P) i g
        (turnTicks * weight b.1 s - grb.owed.getD j 0)
        (turnTicks * weight b.1 s - grb.owed.getD j 0) b.1 s 0).val.2.2 -
          turnTicks * weight b.1 s)) hI.goal hI.busy hs'
    generalize (turn (K := DerivationKernel.over D _ hK P) i g
      (turnTicks * weight b.1 s - grb.owed.getD j 0)
      (turnTicks * weight b.1 s - grb.owed.getD j 0) b.1 s 0).val = T at hin hadv hos hgd ⊢
    have hkw : Keep b.1 T.1 := hin.frame.keep hI.busy.open
    have hks := keep_setGroup T.1 i k (fun gr => { gr with
      strats := gr.strats.set j T.2.1,
      owed := setOwed gr.owed j (grb.owed.getD j 0 + T.2.2 - turnTicks * weight b.1 s) })
    obtain ⟨tb, htb, -, -⟩ := hI.busy
    have hga := hin.frame.groupsAt htb
    have hS : Stable st b.1 := hI.turns.keep.stable
    refine ⟨hgd, (hkw.trans hks).stable.ext _ _ hI.goal,
      (hkw.trans hks).busy hI.busy, ?_, ?_, fun k' hk' => ?_, fun gr hgr => ?_⟩
    · exact hI.turns.trans (((hin.turns hI.busy.isOpen).weaken (some i)).trans
        (turnsBut_modify _ i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩) (hkw.busy hI.busy).open))
    · rw [groupsAt_setGroup, List.length_modify, hga]
      exact hI.length
    · simp only [groupsAt_setGroup, List.getElem?_modify, Ne.symm hk', ite_false, hga, id_map']
      exact hI.others k' hk'
    · obtain ⟨gr_a, h1, hlv, h2, h3, h4⟩ := hI.group gr hgr
      obtain rfl : grb = gr_a := Option.some.inj (hgrb.symm.trans h1)
      have hsj : grb.strats[j]? = some s := by
        rw [h1] at hs'
        exact hs'
      have hadv' := hadv
      refine ⟨{ grb with
          strats := grb.strats.set j T.2.1,
          owed := setOwed grb.owed j (grb.owed.getD j 0 + T.2.2 - turnTicks * weight b.1 s) },
        ?_, hlv, Pointwise.set h2 (fun x hx => (h2.2 j x s hx hsj).trans hadv'),
        fun m hm s0 s'' hs0 hs'' => ?_, fun m hm => ?_⟩
      · simp [groupsAt_setGroup, hga, h1]
      · simp only [List.getElem?_set] at hs''
        by_cases e : j = m
        · subst e
          simp only [ite_true] at hs''
          split at hs''
          · cases hs''
            rw [getD_setOwed_self, ← h4 j hjd]
            rcases hos with hos | hos
            · exact .inl (SStep.after (h2.2 j s0 s hs0 hsj)
                (hos.mono hS.len_le (fun _ h => (hS.isDone h).1) (Nat.le_refl _) (Nat.le_refl _))
                hI.turns.depth)
            · exact .inr hos
          · cases hs''
        · simp only [e, ite_false] at hs''
          have hm' : m ∈ done := by
            rcases List.mem_append.1 hm with hm | hm
            · exact hm
            · exact absurd (List.mem_singleton.1 hm).symm e
          rw [getD_setOwed_ne _ _ (Ne.symm e)]
          exact (h3 m hm' s0 s'' hs0 hs'').mono (fun _ => Nat.le_refl _) (fun _ h => h)
            (Nat.le_refl _) hin.depth_le
      · have e : m ≠ j := fun e => hm (List.mem_append_right _ (List.mem_singleton.2 e))
        rw [getD_setOwed_ne _ _ e]
        exact h4 m fun h => hm (List.mem_append_left _ h)

/-! ## What a group that worked has spent -/

/-- Strategies that did anything have spent something. -/
theorem workStrats_spent (i : Nat) (g : GoalOf R Rel) (k : Nat)
    (st : StateOf R Rel (Ans D P)) :
    (workStrats (K := DerivationKernel.over D K hK P) i g k st).val.2.2 = true →
      0 < (workStrats (K := DerivationKernel.over D K hK P) i g k st).val.2.1 := by
  at_cost K hK
  simp only [workStrats]
  refine foldL_inv (fun (acc : StateOf R Rel (Ans D P) × Nat × Bool) =>
    acc.2.2 = true → 0 < acc.2.1) _ _ (fun b j _ hI => ?_) (st, 0, false) (fun h => by cases h)
  split
  · exact hI
  · next s o hs =>
    simp only [Cost.bind_val, Cost.pure_val]
    intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · have := hI h
      omega
    · omega

/-- What the round given to a table gives back. -/
theorem feed_val (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (h : Nat) (X : StateOf R Rel (Ans D P)) :
    (feed (K := DerivationKernel.over D K hK P) adv h X).val =
      ((adv h X).val.1.modify h fun t => { t with fed := t.fed + (adv h X).ticks },
        (adv h X).val.2, (adv h X).ticks) := by
  at_cost K hK
  simp only [feed, Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]

/-- A fold stays at a value every step leaves. -/
theorem foldL_fixed {α β : Type} (f : β → α → Cost β) (stop : β → Prop)
    (hf : ∀ b x, stop b → (f b x).val = b) :
    ∀ (xs : List α) (b : β), stop b → (Cost.foldL f b xs).val = b
  | [], _, _ => rfl
  | x :: xs, b, hb => by
    simp only [Cost.foldL, Cost.bind_val, hf b x hb]
    exact foldL_fixed f stop hf xs b hb

theorem feedFirst_nil (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (X : StateOf R Rel (Ans D P)) (d : Nat) :
    (feedFirst (K := DerivationKernel.over D K hK P) adv X d []).val = (X, d) := by
  at_cost K hK
  simp only [feedFirst, foldL_std, Cost.foldL, Cost.bind_val, Cost.pure_val]

/-- The offer of a round stops at the first table whose round cost
something. -/
theorem feedFirst_cons (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (X : StateOf R Rel (Ans D P)) (d h : Nat) (rest : List Nat) :
    (feedFirst (K := DerivationKernel.over D K hK P) adv X d (h :: rest)).val =
      if 0 < (feed (K := DerivationKernel.over D K hK P) adv h X).val.2.2 then
        ((feed (K := DerivationKernel.over D K hK P) adv h X).val.1,
          d + (feed (K := DerivationKernel.over D K hK P) adv h X).val.2.1)
      else (feedFirst (K := DerivationKernel.over D K hK P) adv
        (feed (K := DerivationKernel.over D K hK P) adv h X).val.1
        (d + (feed (K := DerivationKernel.over D K hK P) adv h X).val.2.1) rest).val := by
  at_cost K hK
  simp only [feedFirst, foldL_std, Cost.foldL, Cost.bind_val, Cost.pure_val, Bool.false_eq_true,
    ↓reduceIte]
  generalize (feed (K := DerivationKernel.over D _ hK P) adv h X).val = r
  by_cases hc : 0 < r.2.2
  · simp only [hc, ↓reduceIte, decide_true]
    rw [foldL_fixed _ (fun b : StateOf R Rel (Ans D P) × Nat × Bool => b.2.2 = true)
      (fun b x hb => by simp only [hb, ↓reduceIte, Cost.pure_val]) rest _ rfl]
  · simp only [hc, ↓reduceIte, decide_false]

/-- The rounds of the tables a group reads only add to what it spent. -/
theorem feedGroup_le (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (i k : Nat) (st : StateOf R Rel (Ans D P)) (d : Nat) :
    d ≤ (feedGroup (K := DerivationKernel.over D K hK P) adv i k st d).val.2 := by
  at_cost K hK
  simp only [feedGroup]
  split
  · simp only [feedFirst, Cost.bind_val, Cost.pure_val]
    refine foldL_inv (fun (acc : StateOf R Rel (Ans D P) × Nat × Bool) => d ≤ acc.2.1) _ _
      (fun b h _ hI => ?_) (st, d, false) (Nat.le_refl _)
    split
    · exact hI
    · simp only [Cost.bind_val, Cost.pure_val]
      omega
  · simp only [feedAll]
    refine foldL_inv (fun (acc : StateOf R Rel (Ans D P) × Nat) => d ≤ acc.2) _ _
      (fun b h _ hI => ?_) (st, d) (Nat.le_refl _)
    simp only [Cost.bind_val, Cost.pure_val]
    omega

/-- **A group did something exactly when its level rose**: the engine
charges itself for every unit of work that did anything, so this holds at a
kernel that charges nothing. -/
theorem workGroup_did (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (i : Nat) (g : GoalOf R Rel) (k : Nat) (st : StateOf R Rel (Ans D P)) :
    (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.2.2 = true ↔
      0 < (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.2.1 := by
  have h1 := workStrats_spent (K := K) (hK := hK) (P := P) i g k st
  have h2 := fun X d => feedGroup_le (K := K) (hK := hK) (P := P) adv i k X d
  at_cost K hK
  simp only [workGroup, Cost.bind_val, Cost.pure_val]
  generalize (workStrats (K := DerivationKernel.over D _ hK P) i g k st).val = r1 at h1 ⊢
  have h2' := h2 r1.1 r1.2.1
  generalize (feedGroup (K := DerivationKernel.over D _ hK P) adv i k r1.1 r1.2.1).val = r2
    at h2' ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · have := h1 h
      omega
    · exact h
  · exact fun h => .inr h

/-! ## A group works -/

/-- A table has its round, given what a round is known to do while no more
tables wait for one than `fuel`: the record of the round, the table needs no
round any more, and it has been fed what the round cost. -/
theorem turn_feed (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns (readNeed P) Rc st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {X : StateOf R Rel (Ans D P)} (hG : Good X) (i : Nat) (g : GoalOf R Rel)
    (hg : goalAt X i = some g) (hb : Busy X i) (hw : (waiting X).length ≤ fuel) (h : Nat) :
    Good (feed (K := DerivationKernel.over D K hK P) adv h X).val.1 ∧
    goalAt (feed (K := DerivationKernel.over D K hK P) adv h X).val.1 i = some g ∧
    Busy (feed (K := DerivationKernel.over D K hK P) adv h X).val.1 i ∧
    Turns (readNeed P) Rc X (feed (K := DerivationKernel.over D K hK P) adv h X).val.1 ∧
    Settled (feed (K := DerivationKernel.over D K hK P) adv h X).val.1 h ∧
    ∀ t, X.tables[h]? = some t →
      X.fedAt h + (feed (K := DerivationKernel.over D K hK P) adv h X).val.2.2 ≤
        (feed (K := DerivationKernel.over D K hK P) adv h X).val.1.fedAt h := by
  rw [feed_val]
  obtain ⟨ht, hs⟩ := hadv h X hG hw
  have hk := keep_modify (adv h X).val.1 h (fun t => { t with fed := t.fed + (adv h X).ticks })
    fun _ _ => ⟨rfl, rfl, rfl, fun h => h, fun h => ⟨h, fun h => h⟩⟩
  refine ⟨Good.modify (hadvG h X hG) h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ h => h) (fun _ => rfl),
    (goalAt_modify _ h i (fun t => { t with fed := t.fed + (adv h X).ticks }) fun _ => rfl).trans
      (ht.keep.stable.ext _ _ hg),
    hk.busy (ht.keep.busy hb), ht.trans (turnsBut_fed none _ h _ hs), hk.settled hs,
    fun t htX => ?_⟩
  obtain ⟨t', ht', -⟩ := ht.keep.2.1 h t htX
  simp only
  rw [fedAt_feed_self _ h _ ht']
  have := (ht.fed h).1
  omega

/-- What holds while the tables a group reads have their rounds, from the
state `st`, when those at `done` have had theirs. -/
structure FeedInv (Rc : RaceSem R Rel (Ans D P)) (st : StateOf R Rel (Ans D P)) (i : Nat) (g : GoalOf R Rel)
    (done : List Nat) (X : StateOf R Rel (Ans D P)) : Prop where
  good : Good X
  goal : goalAt X i = some g
  busy : Busy X i
  turns : Turns (readNeed P) Rc st X
  settled : ∀ h ∈ done, Settled X h

/-- The tables a group reads have their rounds, given what a round is known
to do while no more tables wait for one than `fuel`. -/
theorem turn_feedAll (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns (readNeed P) Rc st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat) (g : GoalOf R Rel)
    (hg : goalAt st i = some g) (hb : Busy st i) (hw : (waiting st).length ≤ fuel) (d : Nat)
    (feeds : List Nat) :
    FeedInv Rc st i g feeds
      (feedAll (K := DerivationKernel.over D K hK P) adv st d feeds).val.1 := by
  have hstep := fun X hGX hgX hbX hwX h =>
    turn_feed (K := K) (hK := hK) (P := P) (Rc := Rc) adv fuel hadvG hadv (X := X) hGX i g hgX
      hbX hwX h
  at_cost K hK
  simp only [feedAll]
  refine foldL_done (fun done (acc : StateOf R Rel (Ans D P) × Nat) =>
    FeedInv Rc st i g done acc.1) _ _ (fun done b h _ hI => ?_) (st, d)
    ⟨hG, hg, hb, TurnsBut.refl _ _, fun _ h => by cases h⟩
  simp only [Cost.bind_val, Cost.pure_val]
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := hstep b.1 hI.good hI.goal hI.busy
    ((waiting_le hI.turns.keep).trans hw) h
  refine ⟨k1, k2, k3, hI.turns.trans k4, fun h' hh' => ?_⟩
  rcases List.mem_append.1 hh' with hm | hm
  · exact k4.keep.settled (hI.settled h' hm)
  · obtain rfl := List.mem_singleton.1 hm
    exact k5

/-- The tables given are offered a round in order, the list sorted by `φ`:
each needs no round any more, or one that comes no later by `φ` had a round
that cost something. -/
theorem turn_feedFirst (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns (readNeed P) Rc st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    (i : Nat) (g : GoalOf R Rel) (φ : Nat → Nat) :
    ∀ (feeds : List Nat) (X : StateOf R Rel (Ans D P)) (d : Nat), Good X → goalAt X i = some g →
      Busy X i → (waiting X).length ≤ fuel → (∀ p ∈ feeds, ∃ t, X.tables[p]? = some t) →
      feeds.Pairwise (fun a b => φ a ≤ φ b) →
      Good (feedFirst (K := DerivationKernel.over D K hK P) adv X d feeds).val.1 ∧
      goalAt (feedFirst (K := DerivationKernel.over D K hK P) adv X d feeds).val.1 i = some g ∧
      Busy (feedFirst (K := DerivationKernel.over D K hK P) adv X d feeds).val.1 i ∧
      Turns (readNeed P) Rc X
        (feedFirst (K := DerivationKernel.over D K hK P) adv X d feeds).val.1 ∧
      ∀ p ∈ feeds,
        Settled (feedFirst (K := DerivationKernel.over D K hK P) adv X d feeds).val.1 p ∨
        ∃ q ∈ feeds, X.fedAt q <
          (feedFirst (K := DerivationKernel.over D K hK P) adv X d feeds).val.1.fedAt q ∧
          φ q ≤ φ p
  | [], X, d, hG, hg, hb, _, _, _ => by
    rw [feedFirst_nil]
    exact ⟨hG, hg, hb, TurnsBut.refl _ _, fun p hp => by cases hp⟩
  | h :: rest, X, d, hG, hg, hb, hw, hex, hsort => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      turn_feed (K := K) (hK := hK) (Rc := Rc) adv fuel hadvG hadv hG i g hg hb hw h
    obtain ⟨th, hth⟩ := hex h List.mem_cons_self
    have h6' := h6 th hth
    have ih := fun X' d' => turn_feedFirst adv fuel hadvG hadv i g φ rest X' d'
    rw [feedFirst_cons]
    generalize (feed (K := DerivationKernel.over D K hK P) adv h X).val = r
      at h1 h2 h3 h4 h5 h6' ⊢
    split
    · next hc =>
      refine ⟨h1, h2, h3, h4, fun p hp => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact .inl h5
      · refine .inr ⟨h, List.mem_cons_self, ?_, (List.pairwise_cons.1 hsort).1 p hp⟩
        show X.fedAt h < r.1.fedAt h
        omega
    · obtain ⟨k1, k2, k3, k4, k5⟩ := ih r.1 (d + r.2.1) h1 h2 h3
        ((waiting_le h4.keep).trans hw)
        (fun p hp => by
          obtain ⟨t, ht⟩ := hex p (List.mem_cons_of_mem _ hp)
          obtain ⟨t', ht', -⟩ := h4.keep.2.1 p t ht
          exact ⟨t', ht'⟩)
        (List.pairwise_cons.1 hsort).2
      refine ⟨k1, k2, k3, h4.trans k4, fun p hp => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact .inl (k4.keep.settled h5)
      · rcases k5 p hp with hs | ⟨q, hq, e1, e2⟩
        · exact .inl hs
        · exact .inr ⟨q, List.mem_cons_of_mem _ hq, Nat.lt_of_le_of_lt (h4.fed q).1 e1, e2⟩

/-- **The tables a group reads are fed**, given what a round is known to do
while no more tables wait for one than `fuel`. -/
theorem turn_feedGroup (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns (readNeed P) Rc st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {X : StateOf R Rel (Ans D P)} (hG : Good X) (i : Nat) (g : GoalOf R Rel) (k : Nat)
    (hg : goalAt X i = some g) (hb : Busy X i) (hw : (waiting X).length ≤ fuel) (d : Nat) :
    Good (feedGroup (K := DerivationKernel.over D K hK P) adv i k X d).val.1 ∧
    goalAt (feedGroup (K := DerivationKernel.over D K hK P) adv i k X d).val.1 i = some g ∧
    Busy (feedGroup (K := DerivationKernel.over D K hK P) adv i k X d).val.1 i ∧
    Turns (readNeed P) Rc X (feedGroup (K := DerivationKernel.over D K hK P) adv i k X d).val.1 ∧
    ∀ gr, (groupsAt X i)[k]? = some gr → ∀ s ∈ gr.strats,
      Fed X (feedGroup (K := DerivationKernel.over D K hK P) adv i k X d).val.1 s := by
  have hA := fun feeds => turn_feedAll (K := K) (hK := hK) (P := P) (Rc := Rc) adv fuel hadvG hadv
    hG i g hg hb hw d feeds
  have hF := fun feeds hex hsort => turn_feedFirst (K := K) (hK := hK) (P := P) (Rc := Rc) adv fuel
    hadvG hadv i g X.fedAt feeds X d hG hg hb hw hex hsort
  at_cost K hK
  simp only [feedGroup]
  split
  · next subs hsub =>
    cases hgk : (groupsAt X i)[k]? with
    | none => rw [hgk] at hsub; cases hsub
    | some gr0 =>
      rw [hgk] at hsub
      simp only [Option.map_some, Option.getD_some] at hsub
      have hpr := prog_of_groupsAt hG.prog hg
        (show ((groupsAt X i)[k]?).bind (·.strats[0]?) = some (.copy false subs) by
          rw [hgk]; simp [hsub])
      obtain ⟨-, -, -, h3⟩ := hpr
      have hex : ∀ p ∈ byFed X (subs.map Prod.fst).eraseDups, ∃ t, X.tables[p]? = some t := by
        intro p hp
        unfold byFed at hp
        rw [List.mem_mergeSort, List.mem_eraseDups] at hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨m, hm⟩ := List.getElem?_of_mem hq
        obtain ⟨x, -, hgj, -⟩ := h3 m q.1 q.2 hm
        unfold goalAt at hgj
        cases ht : X.tables[q.1]? with
        | none => rw [ht] at hgj; cases hgj
        | some t => exact ⟨t, rfl⟩
      have hsort : (byFed X (subs.map Prod.fst).eraseDups).Pairwise
          (fun a b => X.fedAt a ≤ X.fedAt b) :=
        (List.pairwise_mergeSort
          (le := fun a b => decide (X.fedAt a ≤ X.fedAt b))
          (fun a b c h1 h2 => by
            simp only [decide_eq_true_eq] at h1 h2 ⊢
            omega)
          (fun a b => by
            simp only [Bool.or_eq_true, decide_eq_true_eq]
            omega) _).imp fun h => of_decide_eq_true h
      obtain ⟨k1, k2, k3, k4, k5⟩ := hF _ hex hsort
      refine ⟨k1, k2, k3, k4, fun gr hgr s hs => ?_⟩
      cases hgr
      rw [hsub] at hs
      obtain rfl := List.mem_singleton.1 hs
      simp only [Fed]
      intro p hp
      have hmem : p.1 ∈ byFed X (subs.map Prod.fst).eraseDups := by
        unfold byFed
        rw [List.mem_mergeSort, List.mem_eraseDups]
        exact List.mem_map.2 ⟨p, hp, rfl⟩
      rcases k5 p.1 hmem with hs | ⟨q, hq, e1, e2⟩
      · exact .inl hs
      · unfold byFed at hq
        rw [List.mem_mergeSort, List.mem_eraseDups] at hq
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact .inr ⟨q', hq', e1, Nat.le_trans e2 (k4.fed p.1).1⟩
  · have h2' := hA ((((groupsAt X i)[k]?.map (·.strats)).getD []).flatMap
      (Strat.feeds X)).eraseDups
    refine ⟨h2'.good, h2'.goal, h2'.busy, h2'.turns, fun gr hgr s hs => Fed.of_sfed
      (sfed_of_feeds h2'.turns.keep.stable fun j hj => ?_)⟩
    · refine h2'.settled j (List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨s, ?_, hj⟩))
      rw [hgr]
      exact hs

/-- **A group works**: each of its strategies has worked, the tables they
read are fed, and nothing else of the groups of the table has changed. -/
theorem turn_workGroup (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns (readNeed P) Rc st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat) (g : GoalOf R Rel)
    (k : Nat) (hg : goalAt st i = some g) (hb : Busy st i) (hw : (waiting st).length ≤ fuel) :
    Good (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1 ∧
    goalAt (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1 i =
      some g ∧
    Busy (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1 i ∧
    TurnsBut (readNeed P) Rc (some i) st
      (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1 ∧
    (groupsAt (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1
      i).length = (groupsAt st i).length ∧
    (∀ k', k' ≠ k →
      (groupsAt (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1
        i)[k']? = (groupsAt st i)[k']?) ∧
    ∀ gr, (groupsAt st i)[k]? = some gr → ∃ gr',
      (groupsAt (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1
        i)[k]? = some gr' ∧
      gr'.level = gr.level +
        (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.2.1 ∧
      GrAdv gr gr' ∧
      GrStep (readNeed P) st.len st.isDone st.depth
        (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1.depth
        gr gr' ∧
      ∀ s ∈ gr'.strats,
        Fed st (workGroup (K := DerivationKernel.over D K hK P) adv i g k st).val.1 s := by
  have h1 := turn_workStrats (K := K) (hK := hK) (Rc := Rc) hL hR hG i g k hg hb
  have h2 := fun X hGX hgX hbX hwX d =>
    turn_feedGroup (K := K) (hK := hK) (P := P) (Rc := Rc) adv fuel hadvG hadv (X := X) hGX i g k
      hgX hbX hwX d
  clear hR
  at_cost K hK
  simp only [workGroup, Cost.bind_val, Cost.pure_val]
  generalize (workStrats (K := DerivationKernel.over D _ hK P) i g k st).val = r1 at h1 ⊢
  obtain ⟨f1, f2, f3, f4, f5⟩ := h2 r1.1 h1.good h1.goal h1.busy
    ((waiting_le h1.turns.keep).trans hw) r1.2.1
  generalize (feedGroup (K := DerivationKernel.over D _ hK P) adv i k r1.1 r1.2.1).val = r2
    at f1 f2 f3 f4 f5 ⊢
  have hks0 := keep_setGroup r2.1 i k (fun gr => { gr with level := gr.level + r2.2 })
  have hks : Keep r2.1 ((setGroup r2.1 i k fun gr => { gr with level := gr.level + r2.2 }).modify i
      fun t => { t with own := t.own + r1.2.1 }) :=
    hks0.trans (keep_modify _ _ _ fun _ _ => ⟨rfl, rfl, rfl, fun h => h, fun h => ⟨h, fun h => h⟩⟩)
  have hg2 : groupsAt r2.1 i = groupsAt r1.1 i := f4.groupsAt h1.busy
  have hgm := fun X : StateOf R Rel (Ans D P) => groupsAt_modify X i
    (fun t => { t with own := t.own + r1.2.1 }) (fun _ => rfl) i
  refine ⟨Good.modify (Good.setGroup f1 i k (fun gr => { gr with level := gr.level + r2.2 })
        (fun _ _ _ s hs => .inl hs) (fun _ _ => rfl))
      i (fun t => { t with own := t.own + r1.2.1 }) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ h => h) (fun _ => rfl),
    hks.stable.ext _ _ f2, hks.busy f3, ?_, ?_, fun k' hk' => ?_, fun gr hgr => ?_⟩
  · have m1 : TurnsBut (readNeed P) Rc (some i) r2.1
        (setGroup r2.1 i k fun gr => { gr with level := gr.level + r2.2 }) :=
      turnsBut_modify _ i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩) f3.open
    have m2 : TurnsBut (readNeed P) Rc (some i)
        (setGroup r2.1 i k fun gr => { gr with level := gr.level + r2.2 })
        ((setGroup r2.1 i k fun gr => { gr with level := gr.level + r2.2 }).modify i
          fun t => { t with own := t.own + r1.2.1 }) :=
      turnsBut_modify _ i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩) (hks0.busy f3).open
    exact h1.turns.trans ((f4.weaken (some i)).trans (m1.trans m2))
  · rw [hgm, groupsAt_setGroup, List.length_modify, hg2]
    exact h1.length
  · simp only [hgm, groupsAt_setGroup, List.getElem?_modify, Ne.symm hk', ite_false, hg2, id_map']
    exact h1.others k' hk'
  · obtain ⟨gr1, e1, hlv1, hadv1, hst⟩ := h1.group gr hgr
    have hn : ((groupsAt st i)[k]?.map (·.strats.length)).getD 0 = gr.strats.length := by
      rw [hgr]
      rfl
    refine ⟨{ gr1 with level := gr1.level + r2.2 }, by simp [hgm, groupsAt_setGroup, hg2, e1],
      by rw [← hlv1], hadv1, ⟨hadv1.1, fun m s0 s hs0 hs => ?_⟩, fun s hs => ?_⟩
    · have hm : m ∈ List.range (((groupsAt st i)[k]?.map (·.strats.length)).getD 0) := by
        rw [hn]
        exact List.mem_range.2 (List.getElem?_eq_some_iff.1 hs0).1
      exact (hst.1 m hm s0 s hs0 hs).mono (fun _ => Nat.le_refl _) (fun _ h => h) (Nat.le_refl _)
        f4.depth
    · refine ((f5 gr1 e1 s hs).start fun j => (h1.turns.fed j).1).finish hks.stable
        (fun _ => hks.settled) fun j => Nat.le_of_eq ?_
      exact ((fedAt_modify_same _ i (fun t => { t with own := t.own + r1.2.1 }) (fun _ => rfl)
        j).trans (fedAt_setGroup r2.1 i k _ j)).symm

/-! ## The groups of one level work -/

/-- What holds during the round of the table at `i`, which began in the
state `st0` with the groups `gs0`. -/
structure LevelInv (Rc : RaceSem R Rel (Ans D P)) (st0 : StateOf R Rel (Ans D P)) (gs0 : List (Group Rel (Ans D P))) (i : Nat)
    (g : GoalOf R Rel) (X : StateOf R Rel (Ans D P)) : Prop where
  good : Good X
  goal : goalAt X i = some g
  busy : Busy X i
  turns : TurnsBut (readNeed P) Rc (some i) st0 X
  groups : Pointwise (GrAdv) gs0 (groupsAt X i)
  levels : ∀ (k : Nat) (gr0 gr : Group Rel (Ans D P)), gs0[k]? = some gr0 →
    (groupsAt X i)[k]? = some gr → gr0.level ≤ gr.level
  owed : ∀ (k : Nat) (gr0 gr : Group Rel (Ans D P)), gs0[k]? = some gr0 →
    (groupsAt X i)[k]? = some gr → gr.owed = gr0.owed ∨ Tried (readNeed P) st0 X gr0 gr

/-- The group at the place `k` has worked since the round began, and the
tables it reads need no round any more. -/
def TriedAt (st0 : StateOf R Rel (Ans D P)) (gs0 : List (Group Rel (Ans D P))) (i : Nat)
    (X : StateOf R Rel (Ans D P)) (k : Nat) : Prop :=
  ∃ (gr0 gr1 : Group Rel (Ans D P)), gs0[k]? = some gr0 ∧ (groupsAt X i)[k]? = some gr1 ∧
    Tried (readNeed P) st0 X gr0 gr1

/-- One of the groups has worked since the round began. -/
def Worked (st0 : StateOf R Rel (Ans D P)) (gs0 : List (Group Rel (Ans D P))) (i : Nat)
    (X : StateOf R Rel (Ans D P)) : Prop :=
  ∃ k : Nat, TriedAt st0 gs0 i X k

theorem level_workGroup (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns (readNeed P) Rc st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {st0 X : StateOf R Rel (Ans D P)} {gs0 : List (Group Rel (Ans D P))} (i : Nat)
    (g : GoalOf R Rel) (hI : LevelInv Rc st0 gs0 i g X) (hw : (waiting st0).length ≤ fuel)
    (k : Nat) :
    LevelInv Rc st0 gs0 i g (workGroup (K := DerivationKernel.over D K hK P) adv i g k X).val.1 ∧
    (∀ k0, TriedAt st0 gs0 i X k0 →
      TriedAt st0 gs0 i (workGroup (K := DerivationKernel.over D K hK P) adv i g k X).val.1
        k0) ∧
    ((groupsAt X i)[k]? ≠ none →
      TriedAt st0 gs0 i (workGroup (K := DerivationKernel.over D K hK P) adv i g k X).val.1
        k) ∧
    (∀ k', k' ≠ k →
      (groupsAt (workGroup (K := DerivationKernel.over D K hK P) adv i g k X).val.1 i)[k']? =
        (groupsAt X i)[k']?) ∧
    (∀ gr, (groupsAt X i)[k]? = some gr → ∃ gr',
      (groupsAt (workGroup (K := DerivationKernel.over D K hK P) adv i g k X).val.1 i)[k]? =
        some gr' ∧
      gr'.level = gr.level +
        (workGroup (K := DerivationKernel.over D K hK P) adv i g k X).val.2.1) := by
  obtain ⟨hG', hg', hb', ht, hlen, hoth, hgrp⟩ := turn_workGroup (K := K) (hK := hK) hL hR adv
    fuel hadvG hadv hI.good i g k hI.goal hI.busy ((waiting_le hI.turns.keep).trans hw)
  generalize (workGroup (K := DerivationKernel.over D K hK P) adv i g k X).val = W at *
  have hS : Stable st0 X := hI.turns.keep.stable
  have stepK : ∀ gr0 grX, gs0[k]? = some gr0 → (groupsAt X i)[k]? = some grX →
      ∃ gr', (groupsAt W.1 i)[k]? = some gr' ∧ gr'.level = grX.level + W.2.1 ∧
        Tried (readNeed P) st0 W.1 gr0 gr' := by
    intro gr0 grX h0 hX
    obtain ⟨gr', e, hlv, hadvX, hstp, hf⟩ := hgrp grX hX
    have h1 : Pointwise (SAdv) gr0.strats grX.strats := hI.groups.2 k gr0 grX h0 hX
    refine ⟨gr', e, hlv, ⟨h1.1.trans hstp.1, fun m s s' hs hs' => ?_⟩,
      fun s hs => (hf s hs).start fun j => (hI.turns.fed j).1⟩
    obtain ⟨sX, hsX, hadv⟩ := h1.get hs
    have hstep := (hstp.2 m sX s' hsX hs').mono hS.len_le (fun _ h => (hS.isDone h).1)
      (Nat.le_refl _) (Nat.le_refl _)
    rcases hI.owed k gr0 grX h0 hX with ho | htr
    · rw [ho] at hstep
      exact hstep.imp (fun h => SStep.after hadv h hI.turns.depth) id
    · rcases hstep with h' | h'
      · exact .inl (SStep.after hadv h' hI.turns.depth)
      · rcases htr.1.2 m s sX hs hsX with h | h
        · exact .inl ((h.before (hadvX.2 m sX s' hsX hs')).mono
            (fun _ => Nat.le_refl _) (fun _ h => h) (Nat.le_refl _) ht.depth)
        · exact .inr (h'.trans h)
  refine ⟨⟨hG', hg', hb', hI.turns.trans ht, ⟨hI.groups.1.trans hlen.symm,
    fun m gr0 gr' h0 h' => ?_⟩, fun m gr0 gr' h0 h' => ?_, fun m gr0 gr' h0 h' => ?_⟩, ?_, ?_,
    hoth, fun gr hgr => ?_⟩
  · by_cases e : m = k
    · subst e
      obtain ⟨grX, hX, hadv0⟩ := hI.groups.get h0
      obtain ⟨gr'', e', -, hadvX, -⟩ := hgrp grX hX
      rw [h'] at e'
      cases e'
      exact Pointwise.comp (r₃ := SAdv) (fun _ _ _ a b => a.trans b)
        hadv0 hadvX
    · rw [hoth m e] at h'
      exact hI.groups.2 m gr0 gr' h0 h'
  · by_cases e : m = k
    · subst e
      obtain ⟨grX, hX, -⟩ := hI.groups.get h0
      obtain ⟨gr'', e', hlv, -⟩ := stepK gr0 grX h0 hX
      rw [h'] at e'
      cases e'
      have := hI.levels m gr0 grX h0 hX
      omega
    · rw [hoth m e] at h'
      exact hI.levels m gr0 gr' h0 h'
  · by_cases e : m = k
    · subst e
      obtain ⟨grX, hX, -⟩ := hI.groups.get h0
      obtain ⟨gr'', e', -, htr⟩ := stepK gr0 grX h0 hX
      rw [h'] at e'
      cases e'
      exact .inr htr
    · rw [hoth m e] at h'
      exact (hI.owed m gr0 gr' h0 h').imp id fun htr =>
        ⟨htr.1.mono (fun _ => Nat.le_refl _) (fun _ h => h) (Nat.le_refl _) ht.depth,
          fun s hs => (htr.2 s hs).finish ht.keep.stable (fun _ => ht.keep.settled)
            fun j => (ht.fed j).1⟩
  · rintro k0 ⟨gr0, gr1, e0, e1, hst, hf⟩
    by_cases e : k0 = k
    · subst e
      obtain ⟨gr', e', -, htr⟩ := stepK gr0 gr1 e0 e1
      exact ⟨gr0, gr', e0, e', htr⟩
    · exact ⟨gr0, gr1, e0, by rw [hoth k0 e]; exact e1,
        hst.mono (fun _ => Nat.le_refl _) (fun _ h => h) (Nat.le_refl _) ht.depth,
        fun s hs => (hf s hs).finish ht.keep.stable (fun _ => ht.keep.settled)
          fun j => (ht.fed j).1⟩
  · intro hne
    cases hX : (groupsAt X i)[k]? with
    | none => exact absurd hX hne
    | some grX =>
      obtain ⟨gr0, h0, -⟩ := hI.groups.get' hX
      obtain ⟨gr', e', -, htr⟩ := stepK gr0 grX h0 hX
      exact ⟨gr0, gr', h0, e', htr⟩
  · obtain ⟨gr', e, hlv, -⟩ := hgrp gr hgr
    exact ⟨gr', e, hlv⟩

/-- **The groups of one level work**: what holds during the round still
does; a group that had worked still has; every group that stands at the
level has worked, and no other group has changed; if anything was done, one
of them has risen above the level; and if nothing was done, no level has
changed. -/
theorem level_workLevel (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (fuel : Nat) (hadvG : ∀ h st, Good st → Good (adv h st).val.1)
    (hadv : ∀ h st, Good st → (waiting st).length ≤ fuel →
      Turns (readNeed P) Rc st (adv h st).val.1 ∧ Settled (adv h st).val.1 h)
    {st0 X : StateOf R Rel (Ans D P)} {gs0 : List (Group Rel (Ans D P))} (i : Nat)
    (g : GoalOf R Rel) (hI : LevelInv Rc st0 gs0 i g X) (hw : (waiting st0).length ≤ fuel)
    (lv : Nat) :
    LevelInv Rc st0 gs0 i g (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 ∧
    (∀ k0, TriedAt st0 gs0 i X k0 →
      TriedAt st0 gs0 i (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1
        k0) ∧
    (∀ (k : Nat) (gr : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr → gr.level = lv →
      TriedAt st0 gs0 i (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1
        k) ∧
    (∀ (k : Nat) (gr : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr → gr.level ≠ lv →
      (groupsAt (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 i)[k]? =
        some gr) ∧
    ((workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.2 = true →
      ∃ (k : Nat) (gr gr' : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr ∧ gr.level = lv ∧
        (groupsAt (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 i)[k]? =
          some gr' ∧ lv < gr'.level) ∧
    ((workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.2 = false →
      ∀ k : Nat,
        ((groupsAt (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1
          i)[k]?).map (·.level) = ((groupsAt X i)[k]?).map (·.level)) := by
  have hgl := fun (Y : StateOf R Rel (Ans D P)) hY k =>
    level_workGroup (K := K) (hK := hK) hL hR adv fuel hadvG hadv (st0 := st0) (gs0 := gs0)
      (X := Y) i g hY hw k
  have hdid := fun (Y : StateOf R Rel (Ans D P)) k =>
    workGroup_did (K := K) (hK := hK) (P := P) adv i g k Y
  have key : LevelInv Rc st0 gs0 i g (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 ∧
      (∀ k0, TriedAt st0 gs0 i X k0 → TriedAt st0 gs0 i (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 k0) ∧
      (∀ p ∈ (groupsAt X i).zipIdx, p.1.level = lv → TriedAt st0 gs0 i (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 p.2) ∧
      (∀ (k : Nat) (gr : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr → gr.level ≠ lv →
        (groupsAt (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 i)[k]? = some gr) ∧
      (∀ (k : Nat) (gr gr' : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr →
        (groupsAt (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 i)[k]? = some gr' →
        gr.level ≤ gr'.level) ∧
      ((workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.2 = true →
        ∃ (k : Nat) (gr gr' : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr ∧ gr.level = lv ∧
          (groupsAt (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 i)[k]? = some gr' ∧
          lv < gr'.level) ∧
      ((workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.2 = false →
        ∀ k : Nat,
          ((groupsAt (workLevel (K := DerivationKernel.over D K hK P) adv i g lv X).val.1 i)[k]?).map (·.level) =
            ((groupsAt X i)[k]?).map (·.level)) := by
    clear hR
    at_cost K hK
    refine foldL_done (fun done (acc : StateOf R Rel (Ans D P) × Bool) =>
      LevelInv Rc st0 gs0 i g acc.1 ∧ (∀ k0, TriedAt st0 gs0 i X k0 → TriedAt st0 gs0 i acc.1 k0) ∧
        (∀ p ∈ done, (p : Group Rel (Ans D P) × Nat).1.level = lv → TriedAt st0 gs0 i acc.1 p.2) ∧
        (∀ (k : Nat) (gr : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr → gr.level ≠ lv →
          (groupsAt acc.1 i)[k]? = some gr) ∧
        (∀ (k : Nat) (gr gr' : Group Rel (Ans D P)), (groupsAt X i)[k]? = some gr →
          (groupsAt acc.1 i)[k]? = some gr' → gr.level ≤ gr'.level) ∧
        (acc.2 = true → ∃ (k : Nat) (gr gr' : Group Rel (Ans D P)),
          (groupsAt X i)[k]? = some gr ∧ gr.level = lv ∧ (groupsAt acc.1 i)[k]? = some gr' ∧
          lv < gr'.level) ∧
        (acc.2 = false → ∀ k : Nat,
          ((groupsAt acc.1 i)[k]?).map (·.level) = ((groupsAt X i)[k]?).map (·.level)))
      _ _ (fun done b p hp hI' => ?_) (X, false)
      ⟨hI, fun _ h => h, (fun _ h => by cases h), fun _ _ h _ => h,
        (fun _ _ _ h h' => by rw [h] at h'; cases h'; exact Nat.le_refl _),
        (fun h => by cases h), fun _ _ => rfl⟩
    obtain ⟨J1, J2, J3, J4, J5, J6, J7⟩ := hI'
    have hpX : (groupsAt X i)[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hp
    split
    · next hlv =>
      simp only [Cost.bind_val, Cost.pure_val]
      obtain ⟨a, b', c, oth, lvl⟩ := hgl b.1 J1 p.2
      have hd := hdid b.1 p.2
      generalize (workGroup (K := DerivationKernel.over D _ hK P) adv i g p.2 b.1).val = W
        at a b' c oth lvl hd ⊢
      have hex : ∃ grA, (groupsAt b.1 i)[p.2]? = some grA := by
        have h2 := (List.getElem?_eq_some_iff.1 hpX).1
        have h3 := hI.groups.1
        have h4 := J1.groups.1
        exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨grA, hA⟩ := hex
      obtain ⟨grW, hW, hWl⟩ := lvl grA hA
      have hAl := J5 p.2 p.1 grA hpX hA
      refine ⟨a, fun k0 h => b' k0 (J2 k0 h), fun q hq hq' => ?_, fun k gr hk hne => ?_,
        fun k gr gr' hk hk' => ?_, fun hflag => ?_, fun hflag k => ?_⟩
      · rcases List.mem_append.1 hq with hq | hq
        · exact b' _ (J3 q hq hq')
        · obtain rfl := List.mem_singleton.1 hq
          exact c (by rw [hA]; exact fun h => by cases h)
      · have hkp : k ≠ p.2 := fun e => by
          subst e
          rw [hpX] at hk
          cases hk
          exact hne hlv
        rw [oth k hkp]
        exact J4 k gr hk hne
      · by_cases hkp : k = p.2
        · subst hkp
          rw [hpX] at hk
          cases hk
          rw [hW] at hk'
          cases hk'
          omega
        · rw [oth k hkp] at hk'
          exact J5 k gr gr' hk hk'
      · rcases Bool.or_eq_true_iff.1 hflag with h | h
        · obtain ⟨k, gr, gr', e1, e2, e3, e4⟩ := J6 h
          by_cases hkp : k = p.2
          · subst hkp
            rw [hA] at e3
            cases e3
            exact ⟨_, gr, grW, e1, e2, hW, by omega⟩
          · exact ⟨k, gr, gr', e1, e2, by rw [oth k hkp]; exact e3, e4⟩
        · have := hd.1 h
          exact ⟨p.2, p.1, grW, hpX, hlv, hW, by omega⟩
      · obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.1 hflag
        have hz : W.2.1 = 0 := by
          by_contra hne
          have := hd.2 (Nat.pos_of_ne_zero hne)
          rw [h2] at this
          cases this
        by_cases hkp : k = p.2
        · subst hkp
          rw [← J7 h1 _, hW, hA]
          simp only [Option.map_some, hWl, hz, Nat.add_zero]
        · rw [oth k hkp]
          exact J7 h1 k
    · next hlv =>
      refine ⟨J1, J2, fun q hq hq' => ?_, J4, J5, J6, J7⟩
      rcases List.mem_append.1 hq with hq | hq
      · exact J3 q hq hq'
      · obtain rfl := List.mem_singleton.1 hq
        exact absurd hq' hlv
  refine ⟨key.1, key.2.1, fun k gr hk hlv => ?_, key.2.2.2.1, key.2.2.2.2.2.1, key.2.2.2.2.2.2⟩
  exact key.2.2.1 (gr, k) (List.mem_zipIdx_iff_getElem?.2 hk) hlv

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
    (hd : t.done = false) (hs : t.stamp ≠ st.round) :
    Good (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
    goalAt (prepare (K := DerivationKernel.over D K hK P) i t st).val i = some t.goal ∧
    Busy (prepare (K := DerivationKernel.over D K hK P) i t st).val i ∧
    TurnsBut (readNeed P) Rc (some i) st (prepare (K := DerivationKernel.over D K hK P) i t st).val ∧
    (∀ gs, t.groups = some gs →
      groupsAt (prepare (K := DerivationKernel.over D K hK P) i t st).val i = gs) ∧
    (t.groups = none →
      Shaped (groupsAt (prepare (K := DerivationKernel.over D K hK P) i t st).val i)) ∧
    ∃ tp, (prepare (K := DerivationKernel.over D K hK P) i t st).val.tables[i]? = some tp ∧
      tp.rounds = t.rounds ∧
      tp.race = if t.groups.isNone then (raceOf (K := DerivationKernel.over D K hK P) t.goal).val
        else t.race := by
  have hg : goalAt st i = some t.goal := by unfold goalAt; rw [ht]; rfl
  obtain ⟨hk, hb⟩ := keep_prepare (K := K) (hK := hK) (P := P) i t st ht hd
  refine ⟨good_prepare hR hP hG i t ht hd, hk.stable.ext _ _ hg, hb, ?_⟩
  have hopen : ∀ t', st.tables[i]? = some t' → t'.done = false := fun t' h => by
    rw [ht] at h; cases h; exact hd
  have hexp := inner_expand (K := K) (hK := hK) (P := P) (w := i) t.goal st
  have hT := (hexp.turns (Rc := Rc) ⟨t, ht, hd⟩).weaken (some i)
  have hfr := hexp.frame
  have hrc := hexp.race
  have hsh := shaped_expand (K := K) (hK := hK) (P := P) t.goal st (hG.inv.core i t ht).1
  clear hR hk hb
  at_cost K hK
  unfold prepare
  cases hgs : t.groups with
  | some gs =>
    simp only [Cost.pure_val, Cost.bind_val]
    refine ⟨turnsBut_modify st i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inr rfl⟩)
        (fun t' h e => by rw [ht] at h; cases h; exact absurd e hs) hopen,
      fun gs' e => ?_, (fun e => by cases e),
      ⟨{ t with stamp := st.round, delta := 0 }, by unfold StateOf.modify; simp [ht],
        rfl, by simp⟩⟩
    cases e
    unfold groupsAt StateOf.modify
    simp [ht, hgs]
  | none =>
    simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨t1, ht1, -, d1, s1, -⟩ := hfr.2.1 i t ht
    have hrd : (expand (K := DerivationKernel.over D _ hK P) t.goal st).val.1.round = st.round :=
      hfr.1
    have hrc1 := hrc i t t1 ht ht1
    generalize (expand (K := DerivationKernel.over D _ hK P) t.goal st).val = e at *
    generalize (raceOf (K := DerivationKernel.over D _ hK P) t.goal).val = r0
    have h2 : (e.1.modify i fun t' => { t' with groups := some e.2, race := r0 }).tables[i]? =
        some { t1 with groups := some e.2, race := r0 } := by
      unfold StateOf.modify
      simp [ht1]
    refine ⟨hT.trans ((turnsBut_modify e.1 i (fun t' => { t' with groups := some e.2, race := r0 })
        (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩)
        (fun t' h e => by rw [ht1] at h; cases h; exact absurd (s1.symm.trans (e.trans hrd)) hs)
        (fun t' h => by rw [ht1] at h; cases h; exact d1.trans hd)).trans
      (turnsBut_modify (e.1.modify i fun t' => { t' with groups := some e.2, race := r0 }) i
        (fun t => { t with
          stamp := (e.1.modify i fun t' => { t' with groups := some e.2, race := r0 }).round,
          delta := 0 }) (fun _ => ⟨rfl, rfl, rfl, rfl, .inr rfl⟩)
        (fun t' h e => by rw [h2] at h; cases h; exact absurd (s1.symm.trans (e.trans hrd)) hs)
        (fun t' h => by rw [h2] at h; cases h; exact d1.trans hd))),
      (fun gs' e' => by cases e'), fun _ => ?_,
      ⟨{ t1 with groups := some e.2, race := r0, stamp := e.1.round, delta := 0 },
        by unfold StateOf.modify; simp [ht1], hrc1.2, by simp⟩⟩
    have : groupsAt ((e.1.modify i fun t' => { t' with groups := some e.2, race := r0 }).modify i
        fun t => { t with
          stamp := (e.1.modify i fun t' => { t' with groups := some e.2, race := r0 }).round,
          delta := 0 }) i = e.2 := by
      unfold groupsAt StateOf.modify
      simp [ht1]
    rw [this]
    exact hsh

omit [DecidableEq R] in
theorem modify_id (st : StateOf R Rel (Ans D P)) (i : Nat) : st.modify i id = st := by
  cases st
  simp [StateOf.modify]

omit [DecidableEq R] in
theorem modify_modify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f g : Table R Rel (Ans D P) → Table R Rel (Ans D P)) :
    (st.modify i f).modify i g = st.modify i (g ∘ f) := by
  cases st
  simp [StateOf.modify, List.modify_modify_eq]

omit [DecidableEq R] in
/-- A table changed back: the state before a change that left the goal, the
answers and the marks of the table. -/
theorem stable_unmodify (st : StateOf R Rel (Ans D P)) (i : Nat)
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P))
    (hf : ∀ t, (f t).goal = t.goal ∧ (f t).born = t.born ∧ (f t).answers = t.answers ∧
      (f t).done = t.done) : Stable (st.modify i f) st := by
  intro k t' hk
  rcases getElem?_modify_cases st i f hk with ⟨-, h⟩ | ⟨rfl, t, ht, rfl⟩
  · exact ⟨t', h, rfl, rfl, List.prefix_refl _, fun h => ⟨h, rfl⟩⟩
  · exact ⟨t, ht, (hf t).1.symm, (hf t).2.1.symm, by rw [(hf t).2.2.1],
      fun h => ⟨by rw [← (hf t).2.2.2]; exact h, (hf t).2.2.1.symm⟩⟩

/-- What the race of the machine means to the record of a run, with the
unfolding race `U`: a final verdict gives answers that relate every pair of
every derivation of the goal, the goal is a chain, and the verdict is final
at some depth. -/
def raceSem (U : GOracle R Rel (Ans D P) Cost) : RaceSem R Rel (Ans D P) where
  cov g l := hasRace g = true ∧ (∃ n, (U n g).val.1 = true) ∧
    ∀ k G, G ∈ GDn P k g.node → (pairsOf P g G).Nonempty → Cov l (pairsOf P g G)
  final g n := (U n g).val.1 = true
  has := hasRace
  cost g n := (U n g).ticks

/-- **What the race does at the end of a round**: the state it leaves is one
the work of a strategy could have left, but for the race of the table. A
final verdict has put into the table answers that relate every pair of every
derivation of its goal. A race that stood at a depth was not asked, having
spent more than the table has had rounds, or its verdict was final, or it
stands one depth further and its verdict at the depth it stood at was not
final. -/
theorem askRace_spec (hL : D.Lawful P.sorts.interp) (U : GOracle R Rel (Ans D P) Cost)
    (hU : UOk D P U) {st : StateOf R Rel (Ans D P)} (hG : Good st) (i : Nat) (g : GoalOf R Rel)
    (hg : goalAt st i = some g) (ho : Open st i) :
    ∃ (Y : StateOf R Rel (Ans D P)) (h : Table R Rel (Ans D P) → Table R Rel (Ans D P)),
      (askRace (K := DerivationKernel.over D K hK P) U i g st).val.1 = Y.modify i h ∧
      (∀ u, (h u).goal = u.goal ∧ (h u).born = u.born ∧ (h u).answers = u.answers ∧
        (h u).stamp = u.stamp ∧ (h u).groups = u.groups ∧ (h u).done = u.done ∧
        (h u).rounds = u.rounds ∧ (h u).fed = u.fed) ∧
      Inner K hK i st Y ∧
      ((askRace (K := DerivationKernel.over D K hK P) U i g st).val.2 = true →
        Raced (raceSem U) Y i) ∧
      ∀ u, Y.tables[i]? = some u → ∀ r, u.race = some r →
        ((h u).race = some r ∧ u.rounds < r.spent + max 1 (2 * r.gaveUp)) ∨
        (askRace (K := DerivationKernel.over D K hK P) U i g st).val.2 = true ∨
        (∃ c, (h u).race = some ⟨r.depth + 1, r.spent + c, 0⟩ ∧ ¬ (U r.depth g).val.1 = true) ∨
        ∃ left, (h u).race = some ⟨r.depth, r.spent + left, left⟩ ∧
          max 1 (2 * r.gaveUp) ≤ left ∧ left < (U r.depth g).ticks := by
  have hid : ∀ u : Table R Rel (Ans D P), (id u).goal = u.goal ∧ (id u).born = u.born ∧
      (id u).answers = u.answers ∧ (id u).stamp = u.stamp ∧ (id u).groups = u.groups ∧
      (id u).done = u.done ∧ (id u).rounds = u.rounds ∧ (id u).fed = u.fed :=
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [askRace_val]
  cases ht : st.tables[i]? with
  | none =>
    obtain ⟨t, ht', -⟩ := ho
    rw [ht] at ht'
    cases ht'
  | some t =>
    have egt : t.goal = g := by
      unfold goalAt at hg
      rw [ht] at hg
      exact Option.some.inj hg
    dsimp only
    cases hr : t.race with
    | none =>
      exact ⟨st, id, (modify_id st i).symm, hid, .refl st, (fun h => by cases h),
        fun u hu r hr' => by rw [ht] at hu; cases hu; rw [hr] at hr'; cases hr'⟩
    | some r =>
      dsimp only
      by_cases hlt : t.own + t.rounds - r.spent < max 1 (2 * r.gaveUp)
      · simp only [hlt, ↓reduceIte]
        exact ⟨st, id, (modify_id st i).symm, hid, .refl st, (fun h => by cases h),
          fun u hu r' hr' => by
            rw [ht] at hu
            cases hu
            rw [hr] at hr'
            cases hr'
            exact .inl ⟨hr, by omega⟩⟩
      · simp only [hlt, ↓reduceIte]
        by_cases hc : (U r.depth g).ticks ≤ t.own + t.rounds - r.spent
        swap
        · simp only [hc, ↓reduceIte]
          exact ⟨st, _, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, .refl st,
            (fun h => by cases h), fun u hu r' hr' => by
              rw [ht] at hu
              cases hu
              rw [hr] at hr'
              cases hr'
              exact .inr (.inr (.inr ⟨_, rfl, by omega, by omega⟩))⟩
        simp only [hc, ↓reduceIte]
        cases hv : (U r.depth g).val.1 with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          exact ⟨st, _, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, .refl st,
            (fun h => by cases h), fun u hu r' hr' => by
              rw [ht] at hu
              cases hu
              rw [hr] at hr'
              cases hr'
              exact .inr (.inr (.inl ⟨_, rfl, by simp [hv]⟩))⟩
        | true =>
          simp only [ite_true]
          have hin := inner_addAll (K := K) (hK := hK) (P := P) i st (U r.depth g).val.2
          refine ⟨_, _, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hin, fun _ => ?_,
            fun _ _ _ _ => .inr (.inl trivial)⟩
          obtain ⟨u, hu, e1, -⟩ := hin.frame.2.1 i t ht
          have hgood := hG.base.good i g hg
          have hok : GoalOk D g :=
            ⟨hgood.1, hgood.2.1, by rw [← egt]; exact (hG.inv.core i t ht).1, hgood.2.2⟩
          have hcov := (foldL_cov i (addAnswer (K := DerivationKernel.over D K hK P) i)
            (fun _ => True) (fun st a => CovS st i a.span)
            (fun st a _ ho => ⟨(Inner.add (K := K) (hK := hK) st a).frame,
              cov_addOption (K := K) (hK := hK) hL st i ho a⟩)
            (fun _ _ _ h hc => hc.mono h) (U r.depth g).val.2 st (fun _ _ => trivial) ho).2
          refine ⟨u, hu, u.answers, List.prefix_refl _, ?_, ⟨r.depth, ?_⟩, fun k G hGk hne => ?_⟩
          · rw [e1]
            exact hG.race i t ht (by rw [hr]; rfl)
          · rw [e1, egt]
            exact hv
          · rw [e1, egt]
            obtain ⟨a, ha, hX⟩ := hU.final r.depth g hok hv k G (by rw [← egt, ← e1]; exact hGk)
              (by rw [← egt, ← e1]; exact hne)
            obtain ⟨y, hy, hden⟩ := hcov a ha
            refine ⟨y, ?_, hX.trans hden⟩
            unfold StateOf.answers at hy
            rw [hu] at hy
            exact hy

/-- **The end of a round**: the groups with nothing left are removed, the
race may be asked, and the table may be marked complete. The record of the
whole round. -/
theorem turns_finish {st stp X Y : StateOf R Rel (Ans D P)} {i : Nat} {g : GoalOf R Rel}
    {t tp : Table R Rel (Ans D P)} {gs0 : List (Group Rel (Ans D P))}
    (ht : st.tables[i]? = some t) (hs : t.stamp ≠ st.round) (hd : t.done = false)
    (hbn : t.born ≠ st.round) (T1 : TurnsBut (readNeed P) Rc (some i) st stp)
    (htp : stp.tables[i]? = some tp) (hstp : tp.stamp = stp.round)
    (hp1 : ∀ gs, t.groups = some gs → gs0 = gs)
    (hp2 : t.groups = none → Shaped gs0) (LI : LevelInv Rc stp gs0 i g X)
    (hW : gs0 ≠ [] → Worked stp gs0 i X)
    (hB : ∀ (m : Nat) (gr0 gr1 : Group Rel (Ans D P)), gs0[m]? = some gr0 →
      (groupsAt X i)[m]? = some gr1 → TriedAt stp gs0 i X m ∨
        (gr1.level = gr0.level ∧ gr1.owed = gr0.owed ∧
          ∃ (k' : Nat) (gr0' gr1' : Group Rel (Ans D P)),
          gs0[k']? = some gr0' ∧ (groupsAt X i)[k']? = some gr1' ∧ gr0'.level < gr0.level ∧
          gr0'.level < gr1'.level))
    (T3 : TurnsBut (readNeed P) Rc (some i) X Y)
    (hgY : groupsAt Y i = (groupsAt X i).filter (fun gr => !gr.strats.all (Strat.dead X)))
    (f : Table R Rel (Ans D P) → Table R Rel (Ans D P)) (fin : Bool)
    (hf : ∀ u, (f u).goal = u.goal ∧ (f u).born = u.born ∧ (f u).answers = u.answers ∧
      (f u).stamp = u.stamp ∧ (f u).groups = u.groups ∧ (f u).done = (u.done || fin))
    (hfin : fin = true →
      (∃ gr ∈ groupsAt Y i, ∃ s ∈ gr.strats, s.quiet Y Y.isDone = true) ∨ Raced Rc Y i)
    (hA : ∀ u, Y.tables[i]? = some u → u.race = tp.race → u.rounds = tp.rounds →
      Asked Rc t (f u))
    (hffed : ∀ u, (f u).fed = u.fed := by intro _; rfl) :
    Turns (readNeed P) Rc st (Y.modify i f) ∧ Settled (Y.modify i f) i := by
  have T : TurnsBut (readNeed P) Rc (some i) st Y := T1.trans (LI.turns.trans T3)
  have hfedYZ : ∀ j, (Y.modify i f).fedAt j = Y.fedAt j := fedAt_modify_same Y i f hffed
  have T' : TurnsBut (readNeed P) Rc (some i) stp Y := LI.turns.trans T3
  obtain ⟨u, hu, hsu, hdu⟩ := T3.keep.busy LI.busy
  have hfd : ∀ v : Table R Rel (Ans D P), v.done = true → (f v).done = true := fun v h => by
    rw [(hf v).2.2.2.2.2, h]
    rfl
  have hSYZ : Stable Y (Y.modify i f) :=
    stable_modify Y i _ fun v _ => ⟨(hf v).1, (hf v).2.1, (hf v).2.2.1, hfd v⟩
  have hsetYZ : ∀ j, Settled Y j → Settled (Y.modify i f) j := by
    intro j hj t' ht'
    rcases getElem?_modify_cases Y i _ ht' with ⟨-, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact hj t' h'
    · rcases hj v hv with h | h | h
      · exact .inl (hfd v h)
      · exact .inr (.inl ((hf v).2.2.2.1.trans h))
      · exact .inr (.inr ((hf v).2.1.trans h))
  have hrY : Y.round = st.round := T.keep.1
  have hfu : fin = true → (∃ gs, (f u).groups = some gs ∧ ∃ gr ∈ gs, ∃ s ∈ gr.strats,
      s.quiet (Y.modify i f) (Y.modify i f).isDone = true ∧
      ∀ k l side o subs dead reads c fc, s = .push k l side o subs dead reads c fc → Y.isDone side = true) ∨
      Raced Rc (Y.modify i f) i := by
    intro hfn
    rcases hfin hfn with ⟨gr, hgr, s, hs1, hq⟩ | hrc
    · left
      simp only [groupsAt, hu] at hgr
      cases hgu : u.groups with
      | none => rw [hgu] at hgr; simp at hgr
      | some gs =>
        rw [hgu] at hgr
        exact ⟨gs, by rw [(hf u).2.2.2.2.1]; exact hgu, gr, hgr, s, hs1,
          quiet_mono (fun _ => hSYZ.isDone) (fun _ => hSYZ.isDone) hq,
          fun k l side o subs dead reads c e => by subst e; exact quiet_push_side hq⟩
    · exact .inr (hrc.mono hSYZ)
  have hfnu : (f u).done = true → fin = true := fun h => by
    rw [(hf u).2.2.2.2.2, hdu] at h
    simpa using h
  refine ⟨⟨keep_mark T.keep ht hs hd _ (fun v => ⟨(hf v).1, (hf v).2.1, (hf v).2.2.1,
      (hf v).2.2.2.1, hfd v⟩),
    T.depth, fun h k t' hk => ?_, fun k ta tz ha hz hyp => ?_, fun k tz hz hdz => ?_,
    fun k ta tz _ ha hz hs' hs'' => ?_, fun k tz _ hz hbz hyp => ?_, fun hF => ?_,
    fun k ta tz ha hz hyp => ?_, fun k ta tz _ ha hz hs' hs'' => ?_,
    fun k => by
      rw [hfedYZ k]
      exact ⟨(T.fed k).1, fun h => hsetYZ k ((T.fed k).2 h)⟩⟩,
    fun t' ht' => ?_⟩
  · rcases getElem?_modify_cases Y i _ hk with ⟨-, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact T.stamp h k t' h'
    · rw [(hf v).2.2.2.1]
      exact T.stamp h k v hv
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact T.groups k ta tz ha h' (hyp.imp id fun hh => ⟨fun e => hne (Option.some.inj e), hh.2⟩)
    · rw [ht] at ha
      cases ha
      rw [hu] at hv
      cases hv
      rcases hyp with h | ⟨-, h | h⟩
      · rw [hd] at h; cases h
      · exact absurd h hs
      · exact absurd ((hf u).2.2.2.1.trans (hsu.trans hrY)) h
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · rcases T.done k tz h' hdz with h | hq | hrc
      · exact .inl h
      · exact .inr (.inl (hq.mono hSYZ rfl))
      · exact .inr (.inr (hrc.mono hSYZ))
    · rw [hu] at hv
      cases hv
      rcases hfu (hfnu hdz) with ⟨gs, hgs, gr, hgr, s, hs1, hq, -⟩ | hrc
      · exact .inr (.inl ⟨gs, hgs, gr, hgr, s, hs1, hq⟩)
      · exact .inr (.inr hrc)
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact (T.turn k ta tz (fun e => hne (Option.some.inj e)) ha h' hs' hs'').finish hSYZ hsetYZ
        (Nat.le_refl _) fun j => Nat.le_of_eq (hfedYZ j).symm
    · rw [ht] at ha
      cases ha
      rw [hu] at hv
      cases hv
      rw [(hf u).2.2.2.2.1]
      have hSXZ : Stable X (Y.modify k f) := T3.keep.stable.trans hSYZ
      have hfinish : ∀ {gr0 gr1 : Group Rel (Ans D P)}, Tried (readNeed P) stp X gr0 gr1 →
          Tried (readNeed P) stp (Y.modify k f) gr0 gr1 := fun h =>
        ⟨h.1.mono (fun _ => Nat.le_refl _) (fun _ h => h) (Nat.le_refl _) T3.depth,
          fun s hs1 => (h.2 s hs1).finish hSXZ (fun j hj => hsetYZ j (T3.keep.settled hj))
            fun j => Nat.le_trans (T3.fed j).1 (Nat.le_of_eq (hfedYZ j).symm)⟩
      refine Turn.start T1.keep.stable T1.depth (fun j => (T1.fed j).1) ⟨gs0, groupsAt X k,
        (fun gr => !gr.strats.all (Strat.dead X)), fun gs h => (hp1 gs h).symm, hp2, ?_, ?_, ?_,
        fun m gr0 gr1 e0 e1 => ⟨LI.levels m gr0 gr1 e0 e1, ?_⟩⟩
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
        · obtain ⟨k, gr0, gr1, e0, e1, htr⟩ := hW he
          exact .inr ⟨k, gr0, gr1, e0, e1, hfinish htr⟩
      · rcases hB m gr0 gr1 e0 e1 with ⟨gr0', gr1', e0', e1', htr⟩ | h
        · rw [e0] at e0'
          rw [e1] at e1'
          cases e0'
          cases e1'
          exact .inl (hfinish htr)
        · exact .inr h
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact T.young k tz (fun e => hne (Option.some.inj e)) h' hbz hyp
    · obtain ⟨v', hv', -, e2, -⟩ := T.keep.2.1 k t ht
      rw [hv] at hv'
      cases hv'
      exact absurd (e2.symm.trans ((hf v).2.1.symm.trans (hbz.trans hrY))) hbn
  · refine Founded.step hSYZ (fun k ta tz ha hz _ => ?_) (fun k tz hz hdz => ?_) (T.founded hF)
    · rcases getElem?_modify_cases Y i _ hz with ⟨-, h'⟩ | ⟨rfl, v, hv, rfl⟩
      · rw [ha] at h'
        cases h'
        rfl
      · rw [ha] at hv
        cases hv
        exact (hf ta).2.2.2.2.1
    · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
      · exact .inl ⟨tz, h', hdz⟩
      · rw [hu] at hv
        cases hv
        exact .inr (hfu (hfnu hdz))
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact T.race k ta tz ha h'
        (hyp.imp id (Or.imp id fun hh => ⟨fun e => hne (Option.some.inj e), hh.2⟩))
    · rw [ht] at ha
      cases ha
      rw [hu] at hv
      cases hv
      rcases hyp with h | h | ⟨-, h⟩
      · rw [hd] at h; cases h
      · exact absurd h hs
      · exact absurd ((hf u).2.2.2.1.trans (hsu.trans hrY)) h
  · rcases getElem?_modify_cases Y i _ hz with ⟨hne, h'⟩ | ⟨rfl, v, hv, rfl⟩
    · exact T.asked k ta tz (fun e => hne (Option.some.inj e)) ha h' hs' hs''
    · rw [ht] at ha
      cases ha
      rw [hu] at hv
      cases hv
      obtain ⟨er, en⟩ := T'.race k tp u htp hu (.inr (.inl hstp))
      exact hA u hu er en
  · rcases getElem?_modify_cases Y i _ ht' with ⟨hne, -⟩ | ⟨-, v, hv, rfl⟩
    · exact absurd rfl hne
    · rw [hu] at hv
      cases hv
      exact .inr (.inl ((hf u).2.2.2.1.trans hsu))

/-- **The record of a round**: over the round of a table, with every round
nested in it, the record holds, and the table needs no round any more. -/
theorem turns_advance (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) (hP : ProgFO P)
    (U : GOracle R Rel (Ans D P) Cost) (hU : UOk D P U) :
    ∀ (fuel i : Nat) (st : StateOf R Rel (Ans D P)), Good st → (waiting st).length ≤ fuel →
      Turns (readNeed P) (raceSem U) st
        (advance (K := DerivationKernel.over D K hK P) U fuel i st).val.1 ∧
      Settled (advance (K := DerivationKernel.over D K hK P) U fuel i st).val.1 i
  | 0, i, st, _, hw => by
    clear hR
    at_cost K hK
    show Turns (readNeed P) (raceSem U) st st ∧ Settled st i
    refine ⟨TurnsBut.refl _ _, settled_of_not_waiting ?_⟩
    have : waiting st = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hw)
    rw [this]
    exact List.not_mem_nil
  | fuel + 1, i, st, hG, hw => by
    have ih := fun h st hG hw => turns_advance hL hR hP U hU fuel h st hG hw
    have ihG := fun h st => good_advance (K := K) (hK := hK) hL hR hP U hU fuel h st
    have hprep := fun t ht hd hs =>
      turn_prepare (K := K) (hK := hK) (Rc := raceSem U) hR hP hG i t ht hd hs
    have hspec := fun (X : StateOf R Rel (Ans D P)) hGX g hg ho =>
      askRace_spec (K := K) (hK := hK) hL U hU (st := X) hGX i g hg ho
    have hrv := raceOf_val (K := K) (hK := hK) (P := P)
    have hlev := fun g lv (st0 : StateOf R Rel (Ans D P)) gs0 X hI hw =>
      level_workLevel (K := K) (hK := hK) hL hR _ fuel ihG ih (st0 := st0) (X := X) (gs0 := gs0)
        i g hI hw lv
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
            obtain ⟨hGp, hgp, hbp, T1, hp1, hp2, tp, htp, hrn, hrc⟩ := hprep t ht hd' hs
            rw [hrv] at hrc
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
            have hsorted := pairwise_levelsOf (groupsAt stp i)
            have hmid := foldL_split (fun done (acc : StateOf R Rel (Ans D P) × Bool) =>
                LevelInv (raceSem U) stp (groupsAt stp i) i t.goal acc.1 ∧ (done = [] → acc = (stp, false)) ∧
                  (done ≠ [] → Worked stp (groupsAt stp i) i acc.1) ∧
                  (acc.2 = false →
                    (∀ k : Nat, ((groupsAt acc.1 i)[k]?).map (·.level) =
                      ((groupsAt stp i)[k]?).map (·.level)) ∧
                    ∀ (k : Nat) (gr0 : Group Rel (Ans D P)), (groupsAt stp i)[k]? = some gr0 →
                      gr0.level ∈ done → TriedAt stp (groupsAt stp i) i acc.1 k) ∧
                  (acc.2 = true → ∃ lv0 : Nat,
                    (∀ (k : Nat) (gr0 : Group Rel (Ans D P)), (groupsAt stp i)[k]? = some gr0 →
                      gr0.level ≤ lv0 → TriedAt stp (groupsAt stp i) i acc.1 k) ∧
                    (∀ (k : Nat) (gr0 : Group Rel (Ans D P)), (groupsAt stp i)[k]? = some gr0 →
                      lv0 < gr0.level → ∃ gr1, (groupsAt acc.1 i)[k]? = some gr1 ∧
                        gr1.level = gr0.level) ∧
                    ∃ (k' : Nat) (gr0' gr1' : Group Rel (Ans D P)),
                      (groupsAt stp i)[k']? = some gr0' ∧ (groupsAt acc.1 i)[k']? = some gr1' ∧
                      gr0'.level = lv0 ∧ lv0 < gr1'.level))
              (fun (acc : StateOf R Rel (Ans D P) × Bool) lv =>
                if acc.2 then pure acc
                else workLevel (K := DerivationKernel.over D _ hK P)
                  (advance (K := DerivationKernel.over D _ hK P) U fuel)
                  i t.goal lv acc.1)
              (levelsOf (groupsAt stp i))
              (fun done rest b lv hsplit hI => by
                obtain ⟨A1, A2, A3, A4, A5⟩ := hI
                have hlv : lv ∈ levelsOf (groupsAt stp i) := by rw [hsplit]; simp
                split
                · next hb2 =>
                  refine ⟨A1, fun h => absurd h (by simp), fun _ => A3 fun hdn => ?_,
                    (fun (h : b.2 = false) => by rw [hb2] at h; cases h), A5⟩
                  rw [A2 hdn] at hb2
                  cases hb2
                · next hb2 =>
                  have hb2' : b.2 = false := by simpa using hb2
                  obtain ⟨hlevels, htried⟩ := A4 hb2'
                  obtain ⟨a, b', c, dsame, wit, lvls⟩ :=
                    hlev t.goal lv stp
                    (groupsAt stp i) b.1 A1 hwp
                  generalize (workLevel (K := DerivationKernel.over D _ hK P)
                    (advance (K := DerivationKernel.over D _ hK P) U fuel)
                    i t.goal lv b.1).val = W
                    at a b' c dsame wit lvls ⊢
                  -- a group that stood at the level when the round began stands there now
                  have hat : ∀ (k : Nat) (gr0 : Group Rel (Ans D P)),
                      (groupsAt stp i)[k]? = some gr0 →
                      ∃ gr, (groupsAt b.1 i)[k]? = some gr ∧ gr.level = gr0.level := by
                    intro k gr0 h0
                    have := hlevels k
                    rw [h0] at this
                    cases hb1 : (groupsAt b.1 i)[k]? with
                    | none => rw [hb1] at this; cases this
                    | some gr =>
                      rw [hb1] at this
                      exact ⟨gr, rfl, Option.some.inj this⟩
                  refine ⟨a, fun h => absurd h (by simp), fun _ => ?_, fun hW2 =>
                    ⟨fun k => (lvls hW2 k).trans (hlevels k), fun k gr0 h0 hmem => ?_⟩,
                    fun hW2 => ⟨lv, fun k gr0 h0 hle => ?_, fun k gr0 h0 hlt => ?_, ?_⟩⟩
                  · by_cases hdn : done = []
                    · obtain ⟨gr, hgr, hl⟩ := mem_levelsOf hlv
                      obtain ⟨k, hk⟩ := List.getElem?_of_mem hgr
                      obtain ⟨grb, hgb, hlb⟩ := hat k gr hk
                      exact ⟨k, c k grb hgb (hlb.trans hl)⟩
                    · obtain ⟨k0, h⟩ := A3 hdn
                      exact ⟨k0, b' k0 h⟩
                  · rcases List.mem_append.1 hmem with hm | hm
                    · exact b' k (htried k gr0 h0 hm)
                    · obtain ⟨grb, hgb, hlb⟩ := hat k gr0 h0
                      exact c k grb hgb (hlb.trans (List.mem_singleton.1 hm))
                  · have hin : gr0.level ∈ levelsOf (groupsAt stp i) :=
                      level_mem_levelsOf (List.mem_of_getElem? h0)
                    rw [hsplit] at hin hsorted
                    rcases List.mem_append.1 hin with hm | hm
                    · exact b' k (htried k gr0 h0 hm)
                    · rcases List.mem_cons.1 hm with hm | hm
                      · obtain ⟨grb, hgb, hlb⟩ := hat k gr0 h0
                        exact c k grb hgb (hlb.trans hm)
                      · have := (List.pairwise_cons.1 (List.pairwise_append.1 hsorted).2.1).1 _ hm
                        omega
                  · obtain ⟨grb, hgb, hlb⟩ := hat k gr0 h0
                    exact ⟨grb, dsame k grb hgb (by omega), hlb⟩
                  · obtain ⟨k, gr, gr', e1, e2, e3, e4⟩ := wit hW2
                    have := hlevels k
                    rw [e1] at this
                    cases h0 : (groupsAt stp i)[k]? with
                    | none => rw [h0] at this; cases this
                    | some gr0 =>
                      rw [h0] at this
                      exact ⟨k, gr0, gr', h0, e3, ((Option.some.inj this).symm.trans e2), e4⟩)
              (stp, false)
              ⟨⟨hGp, hgp, hbp, TurnsBut.refl _ _, Pointwise.refl (fun gr =>
                  Pointwise.refl SAdv.refl gr.strats) _, fun k gr0 gr h0 h1 => by
                    rw [h0] at h1; cases h1; exact Nat.le_refl _,
                  fun k gr0 gr h0 h1 => by rw [h0] at h1; cases h1; exact .inl rfl⟩,
                fun _ => rfl, fun h => absurd rfl h,
                fun _ => ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩, (fun h => by cases h)⟩
            obtain ⟨M1, -, M3, M4, M5⟩ := hmid
            have hstp : tp.stamp = stp.round := by
              obtain ⟨v, hv, hsv, -⟩ := hbp
              rw [htp] at hv
              cases hv
              exact hsv
            generalize (foldL (fun (acc : StateOf R Rel (Ans D P) × Bool) lv =>
              if acc.2 then pure acc
              else workLevel (K := DerivationKernel.over D _ hK P)
                (advance (K := DerivationKernel.over D _ hK P) U fuel)
                i t.goal lv acc.1) (stp, false)
              (levelsOf (groupsAt stp i))).val = Z at M1 M3 M4 M5 ⊢
            have hGY0 : Good (Z.1.modify i fun t =>
                { t with groups := t.groups.map fun gs =>
                    gs.filter fun gr => !gr.strats.all (Strat.dead Z.1) }) :=
              Good.dropGroups M1.good i _ (fun gr hp s hs =>
                List.all_eq_true.1 (by simpa using hp) s hs)
            have T30 : TurnsBut (readNeed P) (raceSem U) (some i) Z.1 (Z.1.modify i fun t =>
                { t with groups := t.groups.map fun gs =>
                    gs.filter fun gr => !gr.strats.all (Strat.dead Z.1) }) :=
              turnsBut_modify Z.1 i _ (fun _ => ⟨rfl, rfl, rfl, rfl, .inl rfl⟩)
                (fun _ _ _ => ⟨rfl, rfl⟩) M1.busy.open
            have hgY0 : groupsAt (Z.1.modify i fun t =>
                { t with groups := t.groups.map fun gs =>
                    gs.filter fun gr => !gr.strats.all (Strat.dead Z.1) }) i =
                (groupsAt Z.1 i).filter fun gr => !gr.strats.all (Strat.dead Z.1) :=
              groupsAt_mapGroups Z.1 i _ rfl
            have hg0 : goalAt (Z.1.modify i fun t =>
                { t with groups := t.groups.map fun gs =>
                    gs.filter fun gr => !gr.strats.all (Strat.dead Z.1) }) i = some t.goal := by
              refine Eq.trans ?_ M1.goal
              exact goalAt_modify _ i i _ fun _ => rfl
            generalize (Z.1.modify i fun t =>
                { t with groups := t.groups.map fun gs =>
                    gs.filter fun gr => !gr.strats.all (Strat.dead Z.1) }) = Y0
              at hGY0 T30 hgY0 hg0 ⊢
            have hb0 : Busy Y0 i := T30.keep.busy M1.busy
            obtain ⟨Y, h, eY, hh, hin, hrcd, hask⟩ := hspec Y0 hGY0 t.goal hg0 hb0.isOpen
            generalize (askRace (K := DerivationKernel.over D _ hK P) U i t.goal Y0).val = A
              at eY hrcd hask ⊢
            rw [eY, modify_modify]
            have hgY : groupsAt Y i =
                (groupsAt Z.1 i).filter fun gr => !gr.strats.all (Strat.dead Z.1) := by
              obtain ⟨u0, hu0, -⟩ := hb0
              exact (hin.frame.groupsAt hu0).trans hgY0
            have hSu : Stable (Y.modify i h) Y := stable_unmodify Y i h fun u =>
              ⟨(hh u).1, (hh u).2.1, (hh u).2.2.1, (hh u).2.2.2.2.2.1⟩
            refine turns_finish ht hs hd' hb T1 htp hstp hp1 hp2 M1
              (fun hne => M3 (levelsOf_ne_nil hne))
              (fun m gr0 gr1 e0 e1 => by
                cases hz : Z.2 with
                | false =>
                  exact .inl ((M4 hz).2 m gr0 e0 (level_mem_levelsOf (List.mem_of_getElem? e0)))
                | true =>
                  obtain ⟨lv0, h1, h2, k', gr0', gr1', e0', e1', hl0, hl1⟩ := M5 hz
                  by_cases hle : gr0.level ≤ lv0
                  · exact .inl (h1 m gr0 e0 hle)
                  · obtain ⟨gr1x, ex, hx⟩ := h2 m gr0 e0 (by omega)
                    rw [e1] at ex
                    cases ex
                    rcases M1.owed m gr0 gr1 e0 e1 with ho | htr
                    · exact .inr ⟨hx, ho, k', gr0', gr1', e0', e1', by omega, by omega⟩
                    · exact .inl ⟨gr0, gr1, e0, e1, htr⟩)
              (T30.trans ((hin.turns (Rc := raceSem U) hb0.isOpen).weaken (some i))) hgY _ _
              (fun u => ⟨(hh u).1, (hh u).2.1, (hh u).2.2.1, (hh u).2.2.2.1, (hh u).2.2.2.2.1, by
                show ((h u).done || _) = _
                rw [(hh u).2.2.2.2.2.1]⟩)
              (fun hfn => ?_) (fun u hu er en => ⟨?_, fun r hr0 => ?_⟩)
              (fun u => (hh u).2.2.2.2.2.2.2)
            · rcases Bool.or_eq_true_iff.1 hfn with hq | h2
              · left
                obtain ⟨gr, hgr, hq⟩ := List.any_eq_true.1 hq
                obtain ⟨s, hs1, hq⟩ := List.any_eq_true.1 hq
                rw [groupsAt_modify Y i h (fun u => (hh u).2.2.2.2.1)] at hgr
                exact ⟨gr, hgr, s, hs1,
                  quiet_mono (fun _ => hSu.isDone) (fun _ => hSu.isDone) hq⟩
              · exact .inr (hrcd h2)
            · show (h u).rounds + 1 = t.rounds + 1
              rw [(hh u).2.2.2.2.2.2.1, en, hrn]
            · have hur : u.race = some r := by
                rw [er, hrc]
                exact hr0
              rcases hask u hu r hur with ⟨e1, e2⟩ | e | ⟨c, e1, e2⟩ | ⟨l, e1, e2⟩
              · exact .inl ⟨e1, by rw [← hrn, ← en]; exact e2⟩
              · refine .inr (.inl ?_)
                show ((h u).done || _) = true
                rw [e]
                simp
              · exact .inr (.inr (.inl ⟨c, e1, e2⟩))
              · exact .inr (.inr (.inr ⟨l, e1, e2⟩))

/-- **The record of a request**: the root has its round, with every round
nested in it, and the tables that complete together are marked. -/
theorem req_request (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK) (hP : ProgFO P)
    (U : GOracle R Rel (Ans D P) Cost) (hU : UOk D P U)
    {st : StateOf R Rel (Ans D P)} (hG : Good st) (hD : Dated st) :
    Req (readNeed P) (raceSem U) st
      (request (K := DerivationKernel.over D K hK P) U st).val.1 := by
  have h := fun (fuel : Nat) (st : StateOf R Rel (Ans D P)) hG hw =>
    turns_advance (K := K) (hK := hK) hL hR hP U hU fuel 0 st hG hw
  clear hR
  at_cost K hK
  simp only [request, Cost.bind_val, Cost.pure_val]
  have h0 : Good ({ st with round := st.round + 1 } : StateOf R Rel (Ans D P)) :=
    hG.of_map (fun _ t => t) (fun j => by simp) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ h => h) (fun _ _ => rfl) rfl
  have hw : (waiting ({ st with round := st.round + 1 } : StateOf R Rel (Ans D P))).length ≤
      st.tables.length := by
    unfold waiting
    exact (List.length_filter_le _ _).trans (by simp)
  obtain ⟨T, hs⟩ := h st.tables.length _ h0 hw
  exact req_of_turns hD T hs _

end kernel

end Symmetric

end RwLog
