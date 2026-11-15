/-
# What a run of requests holds, and when a table is served

`IsRun U σ`: the states `σ 0`, `σ 1`, … are each a request after the one
before, from a first state with no groups and no complete table, and every
one of them has what a run keeps (`Good`).

Of such a run, as `Rungs/Framework/Saturation.lean` asks: `held σ` is what
it holds for each goal at each time, the representatives of the answers of
the table of the goal; and `opened σ` the goals it opens and does not
neglect: those of the tables that are complete at some time (`EvDone`) or
have a round in infinitely many requests (`Live`).

A table is served (`Saturation.Served`) by one strategy that reaches
everything. For each kind of strategy there is one lemma that says what
reaching everything is, in terms of the strategy at later times
(`IsRun.served_span`, `served_copy`, `served_join`, `served_push`,
`served_check`). A complete table has a strategy with nothing left to do
that reads complete tables only, and that strategy has reached everything
(`IsRun.served_done`).
-/
import RwLog.Rungs.Symmetric.Lines
import RwLog.Rungs.Symmetric.Kept
import RwLog.Rungs.Framework.Saturation

namespace RwLog

namespace Symmetric

open Answer Saturation

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  {U : GOracle R Rel (Ans D P) Cost}

/-- A run of requests: each state is a request after the one before; the
first has no groups, no complete table and a depth to read edges to; and
every state has what a run keeps. -/
structure IsRun (U : GOracle R Rel (Ans D P) Cost) (σ : Nat → StateOf R Rel (Ans D P)) :
    Prop where
  req : Requests (readNeed P) (raceSem U) σ
  good : ∀ r, Good (σ r)
  depth : 0 < (σ 0).depth
  fresh : ∀ (k : Nat) (t : Table R Rel (Ans D P)), (σ 0).tables[k]? = some t → t.done = false

omit [DecidableEq R] [Answer R] in
theorem toGoal_inj {g g' : GoalOf R Rel} (e : toGoal g = toGoal g') : g = g' := by
  cases g
  cases g'
  cases e
  rfl

/-- The table at `k` is complete at some time. -/
def EvDone (σ : Nat → StateOf R Rel (Ans D P)) (k : Nat) : Prop := ∃ r, (σ r).isDone k = true

/-- The table at `k` has a round in infinitely many requests. -/
def Live (σ : Nat → StateOf R Rel (Ans D P)) (k : Nat) : Prop :=
  ∀ r', ∃ r, r' ≤ r ∧ HadRound σ r k

/-- The table at `k` is not neglected: it is complete at some time, or has a
round in infinitely many requests. -/
def Opened (σ : Nat → StateOf R Rel (Ans D P)) (k : Nat) : Prop := EvDone σ k ∨ Live σ k

/-- The goals of the tables that are not neglected. -/
def opened (σ : Nat → StateOf R Rel (Ans D P)) : Set (Goal R) :=
  {g | ∃ k r h, goalAt (σ r) k = some h ∧ toGoal h = g ∧ Opened σ k}

/-- What the run holds for a goal at a time: the representatives of the
answers of its table. -/
def held (σ : Nat → StateOf R Rel (Ans D P)) : Tables R := fun r g =>
  {a | ∃ k h, goalAt (σ r) k = some h ∧ toGoal h = g ∧ ∃ y ∈ (σ r).answers k, y.span = a}

/-- The strategy is one of the table at `k` in the state `r`. -/
def IsStrat (σ : Nat → StateOf R Rel (Ans D P)) (k r : Nat) (s : Strat Rel (Ans D P)) : Prop :=
  ∃ (t : Table R Rel (Ans D P)) (gs : List (Group Rel (Ans D P))) (gr : Group Rel (Ans D P)),
    (σ r).tables[k]? = some t ∧ t.groups = some gs ∧ gr ∈ gs ∧ s ∈ gr.strats

omit [DecidableEq R] in
theorem table_of_goalAt {st : StateOf R Rel (Ans D P)} {j : Nat} {g : GoalOf R Rel}
    (h : goalAt st j = some g) : ∃ t, st.tables[j]? = some t ∧ t.goal = g := by
  unfold goalAt at h
  cases ht : st.tables[j]? with
  | none => rw [ht] at h; cases h
  | some t => rw [ht] at h; exact ⟨t, rfl, Option.some.inj h⟩

omit [DecidableEq R] in
theorem goalAt_of_table {st : StateOf R Rel (Ans D P)} {j : Nat} {t : Table R Rel (Ans D P)}
    (h : st.tables[j]? = some t) : goalAt st j = some t.goal := by
  unfold goalAt
  rw [h]
  rfl

omit [DecidableEq R] in
theorem isDone_of_table {st : StateOf R Rel (Ans D P)} {j : Nat} {t : Table R Rel (Ans D P)}
    (h : st.tables[j]? = some t) : st.isDone j = t.done := by
  unfold StateOf.isDone
  rw [h]

variable {σ : Nat → StateOf R Rel (Ans D P)}

/-! ## The tables over time -/

theorem IsRun.stable (h : IsRun U σ) {r r' : Nat} (hr : r ≤ r') : Stable (σ r) (σ r') :=
  h.req.stable hr

theorem IsRun.goal_le (h : IsRun U σ) {r r' k : Nat} {g : GoalOf R Rel} (hr : r ≤ r')
    (hg : goalAt (σ r) k = some g) : goalAt (σ r') k = some g := (h.stable hr).ext _ _ hg

/-- A table has one goal, at all times. -/
theorem IsRun.goal_any (h : IsRun U σ) {r r' k : Nat} {g g' : GoalOf R Rel}
    (hg : goalAt (σ r) k = some g) (hg' : goalAt (σ r') k = some g') : g = g' := by
  have h1 := h.goal_le (Nat.le_max_left r r') hg
  have h2 := h.goal_le (Nat.le_max_right r r') hg'
  rw [h1] at h2
  exact Option.some.inj h2

/-- A goal has one table, at all times. -/
theorem IsRun.goal_inj (h : IsRun U σ) {r r' k k' : Nat} {g : GoalOf R Rel}
    (hg : goalAt (σ r) k = some g) (hg' : goalAt (σ r') k' = some g) : k = k' :=
  (h.good (max r r')).base.nodup k k' g (h.goal_le (Nat.le_max_left r r') hg)
    (h.goal_le (Nat.le_max_right r r') hg')

theorem IsRun.goal_at (h : IsRun U σ) {r0 r k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r0) k = some g) {t : Table R Rel (Ans D P)}
    (ht : (σ r).tables[k]? = some t) : goalAt (σ r) k = some g := by
  have := goalAt_of_table ht
  rw [h.goal_any hk this]
  exact this

theorem IsRun.normal (h : IsRun U σ) {r k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r) k = some g) : Normal g.node := by
  obtain ⟨t, ht, rfl⟩ := table_of_goalAt hk
  exact ((h.good r).inv.core k t ht).1

theorem IsRun.mem_le (h : IsRun U σ) {r r' : Nat} (hr : r ≤ r') {j : Nat} {y : Ans D P}
    (hy : y ∈ (σ r).answers j) : y ∈ (σ r').answers j := ((h.stable hr).answers j).subset hy

/-- An answer at a position that is inside the table at another time is
there at that time. -/
theorem IsRun.at_of_lt (h : IsRun U σ) {r r1 j n : Nat} {y : Ans D P}
    (hy : ((σ r1).answers j)[n]? = some y) (hn : n < ((σ r).answers j).length) :
    ((σ r).answers j)[n]? = some y := by
  rcases Nat.le_total r1 r with hle | hle
  · exact (h.stable hle).getElem? hy
  · exact (h.stable hle).getElem?_old hy hn

/-- A complete table has every answer it ever has. -/
theorem IsRun.done_answers (h : IsRun U σ) {r j : Nat} (hd : (σ r).isDone j = true) (r' : Nat) :
    (σ r').answers j ⊆ (σ r).answers j := by
  rcases Nat.le_total r r' with hr | hr
  · rw [((h.stable hr).isDone hd).2]
  · exact ((h.stable hr).answers j).subset

theorem IsRun.done_len (h : IsRun U σ) {r j : Nat} (hd : (σ r).isDone j = true) (r' : Nat) :
    (σ r').len j ≤ (σ r).len j := by
  unfold StateOf.len
  rcases Nat.le_total r r' with hr | hr
  · rw [((h.stable hr).isDone hd).2]
  · exact (h.stable hr).length_le j

/-! ## What the run holds -/

theorem IsRun.mem_opened (_ : IsRun U σ) {r k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r) k = some g) (ho : Opened σ k) : toGoal g ∈ opened σ :=
  ⟨k, r, g, hk, rfl, ho⟩

/-- What the run ever holds for the goal of a table: the representatives of
the answers the table ever has. -/
theorem IsRun.held_iff (h : IsRun U σ) {r0 k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r0) k = some g) (a : R) :
    Held (held σ) (toGoal g) a ↔ ∃ r, ∃ y ∈ (σ r).answers k, y.span = a := by
  constructor
  · rintro ⟨r, k', g', hg', e, y, hy, rfl⟩
    obtain rfl := toGoal_inj e
    obtain rfl := h.goal_inj hg' hk
    exact ⟨r, y, hy, rfl⟩
  · rintro ⟨r, y, hy, rfl⟩
    exact ⟨max r r0, k, g, h.goal_le (Nat.le_max_right _ _) hk, rfl, y,
      h.mem_le (Nat.le_max_left _ _) hy, rfl⟩

/-- What a table covers at some time the run covers for its goal. -/
theorem IsRun.ev (h : IsRun U σ) {r0 r k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r0) k = some g) {c : R} (hc : CovS (σ r) k c) :
    Ev P (held σ) (toGoal g) (den P.sorts.interp c) := by
  obtain ⟨y, hy, hs⟩ := hc
  exact ⟨y.span, (h.held_iff hk _).2 ⟨r, y, hy, rfl⟩, hs⟩

/-- What the cursors of a strategy of a table mean. -/
theorem IsRun.prog (h : IsRun U σ) {r0 r k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r0) k = some g) {s : Strat Rel (Ans D P)} (hs : IsStrat σ k r s) :
    Prog (σ r) k g s := by
  obtain ⟨t, gs, gr, ht, hg, hgr, hs⟩ := hs
  rw [h.goal_any hk (goalAt_of_table ht)]
  exact (h.good r).prog k t ht gs hg gr hgr s hs

/-- What a table has read of another it covers, whenever the answer read
was found. -/
theorem IsRun.read_cov (h : IsRun U σ) {r r1 i j pos n : Nat} {f : R → Option R} {y : Ans D P}
    (hr : Read (σ r) i j pos f) (hn : n < pos) (hy : ((σ r1).answers j)[n]? = some y) :
    ∀ z, f y.span = some z → CovS (σ r) i z :=
  hr.2 n y hn (h.at_of_lt hy (by have := hr.1; omega))

/-- The complete tables of a run stand in an order at every time: none is
complete only because of itself. -/
theorem IsRun.founded (h : IsRun U σ) : ∀ r, Founded (raceSem U) (σ r)
  | 0 => ⟨fun _ => 0, fun i t ht hd => by rw [h.fresh i t ht] at hd; cases hd⟩
  | r + 1 => (h.req.req r).founded (h.founded r)

/-- A table that needs no round in infinitely many requests is not
neglected. -/
theorem IsRun.opened_of_settled (h : IsRun U σ) {r0 j : Nat} {g : GoalOf R Rel}
    (hj : goalAt (σ r0) j = some g) (hs : ∀ r', ∃ r, r' ≤ r ∧ Settled (σ (r + 1)) j) :
    Opened σ j := by
  by_contra hno
  have hnd : ∀ r (t : Table R Rel (Ans D P)), (σ r).tables[j]? = some t → t.done = true →
      False := fun r t ht hd => hno (.inl ⟨r, by rw [isDone_of_table ht]; exact hd⟩)
  have hnl : ¬ Live σ j := fun hl => hno (.inr hl)
  simp only [Live, not_forall, not_exists, not_and] at hnl
  obtain ⟨r', hr'⟩ := hnl
  obtain ⟨r1, h1, hs1⟩ := hs (max r' r0)
  obtain ⟨t1, ht1, -⟩ := table_of_goalAt (h.goal_le (show r0 ≤ r1 + 1 by omega) hj)
  rcases hs1 t1 ht1 with hd | hst | hb
  · exact hnd _ t1 ht1 hd
  · exact hr' r1 (by omega) ⟨t1, ht1, hst⟩
  · obtain ⟨r2, h2, hs2⟩ := hs (r1 + 1)
    obtain ⟨t2, ht2, -, eb, -⟩ := h.stable (show r1 + 1 ≤ r2 + 1 by omega) j t1 ht1
    rcases hs2 t2 ht2 with hd | hst | hb2
    · exact hnd _ t2 ht2 hd
    · exact hr' r2 (by omega) ⟨t2, ht2, hst⟩
    · have e1 := h.req.round (r1 + 1)
      have e2 := h.req.round (r2 + 1)
      omega

/-! ## A strategy that reaches everything serves its table -/

/-- A span that has run. -/
theorem IsRun.served_span (h : IsRun U σ) {r0 r k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r0) k = some g) (hs : IsStrat σ k r (.span true)) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  have hp := h.prog hk hs
  dsimp only [Prog] at hp
  obtain ⟨⟨s, hn⟩, hc⟩ := hp
  exact .span s hn fun c hc' => h.ev hk (hc rfl s hn c hc')

/-- A call or a union that reads tables that are not neglected, each as far
as it ever gets. -/
theorem IsRun.served_copy (h : IsRun U σ) {r0 k : Nat} {g : GoalOf R Rel} {c : Bool}
    {subs0 : List (Nat × Nat)} (hk : goalAt (σ r0) k = some g)
    (hs : IsStrat σ k r0 (.copy c subs0))
    (hex : ∀ (m j pos0 : Nat), subs0[m]? = some (j, pos0) → Opened σ j ∧
      ∀ n r1, n < (σ r1).len j → ∃ (r : Nat) (subs : List (Nat × Nat)) (pos : Nat),
        IsStrat σ k r (.copy c subs) ∧
        subs[m]? = some (j, pos) ∧ n < pos) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  have hp := h.prog hk hs
  dsimp only [Prog] at hp
  obtain ⟨h0, h1, h2, h3⟩ := hp
  have key : ∀ (m j pos0 : Nat) (x : Rel), subs0[m]? = some (j, pos0) →
      (copyMembers P g.node c)[m]? = some x →
      toGoal (⟨g.lb, x, g.rb⟩ : GoalOf R Rel) ∈ opened σ ∧
      ∀ a, Held (held σ) (toGoal (⟨g.lb, x, g.rb⟩ : GoalOf R Rel)) a →
        Ev P (held σ) (toGoal g) (den P.sorts.interp a) := by
    intro m j pos0 x hm hx
    obtain ⟨x', hx', hgj, -⟩ := h3 m j pos0 hm
    rw [hx] at hx'
    cases hx'
    obtain ⟨ho, hread⟩ := hex m j pos0 hm
    refine ⟨h.mem_opened hgj ho, fun a ha => ?_⟩
    obtain ⟨r1, y, hy, rfl⟩ := (h.held_iff hgj a).1 ha
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hy
    obtain ⟨r, subs, pos, hs', hm', hlt⟩ := hread n r1
      (show n < (σ r1).len j from (List.getElem?_eq_some_iff.1 hn).1)
    have hp' := h.prog hk hs'
    dsimp only [Prog] at hp'
    obtain ⟨-, -, -, h3'⟩ := hp'
    obtain ⟨-, -, -, hrd⟩ := h3' m j pos hm'
    exact h.ev hk (h.read_cov hrd hlt hn y.span rfl)
  cases c with
  | true =>
    obtain ⟨b, hb⟩ := h0 rfl
    have hc : copyMembers P g.node true = [b] := by simp only [copyMembers, hb, Option.toList]
    rw [hc] at h2
    cases subs0 with
    | nil => cases h2
    | cons p rest =>
      have := key 0 p.1 p.2 b rfl (by rw [hc]; rfl)
      exact .call b hb this.1 this.2
  | false =>
    obtain ⟨xs, hv⟩ := h1 rfl
    have e := (h.normal hk).view_union_eq hv
    refine .union xs hv fun x hx => ?_
    obtain ⟨m, hm⟩ := List.getElem?_of_mem hx
    have hlt : m < subs0.length := by
      rw [h2]
      show m < g.node.unionParts.length
      rw [← e]
      exact (List.getElem?_eq_some_iff.1 hm).1
    exact key m subs0[m].1 subs0[m].2 x (List.getElem?_eq_getElem hlt) (by
      show g.node.unionParts[m]? = some x
      rw [← e]
      exact hm)

/-- A join of two tables that are not neglected that combines every pair
of answers they ever have. -/
theorem IsRun.served_join (h : IsRun U σ) {r0 k : Nat} {g : GoalOf R Rel} {kd : Kind} {a b : Nat}
    {c0 : Cursor} (hk : goalAt (σ r0) k = some g) (hs : IsStrat σ k r0 (.join kd a b c0))
    (ha : Opened σ a) (hb : Opened σ b)
    (hex : ∀ p q r1, p < (σ r1).len a → q < (σ r1).len b →
      ∃ r c, IsStrat σ k r (.join kd a b c) ∧ c.Before p q) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  have hp := h.prog hk hs
  dsimp only [Prog] at hp
  obtain ⟨L, Rg, hsp, hga, hgb, -, -⟩ := hp
  have key : ∀ x y, Held (held σ) (toGoal L) x → Held (held σ) (toGoal Rg) y →
      EvO P (held σ) (toGoal g) (opS D kd x y) := by
    intro x y hx hy z hz
    obtain ⟨r1, x', hx', rfl⟩ := (h.held_iff hga x).1 hx
    obtain ⟨r2, y', hy', rfl⟩ := (h.held_iff hgb y).1 hy
    obtain ⟨p, hp⟩ := List.getElem?_of_mem hx'
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hy'
    have hp3 := (h.stable (Nat.le_max_left r1 r2)).getElem? hp
    have hq3 := (h.stable (Nat.le_max_right r1 r2)).getElem? hq
    obtain ⟨r, c, hs', hbef⟩ := hex p q (max r1 r2) (List.getElem?_eq_some_iff.1 hp3).1
      (List.getElem?_eq_some_iff.1 hq3).1
    have hp' := h.prog hk hs'
    dsimp only [Prog] at hp'
    obtain ⟨-, -, -, -, -, hok, hcov⟩ := hp'
    have hlt := hok.before_lt hbef
    exact h.ev hk (hcov p q x' y' hbef (h.at_of_lt hp hlt.1) (h.at_of_lt hq hlt.2) z hz)
  cases kd with
  | seq =>
    obtain ⟨xs, i, l, r, hv, h0, hi, hl, hr, rfl, rfl⟩ := hsp
    exact .join xs i l r hv h0 hi hl hr (h.mem_opened hga ha) (h.mem_opened hgb hb) key
  | and =>
    obtain ⟨xs, i, x, r, hv, -, hx, hr, rfl, rfl⟩ := hsp
    exact .meet xs i x r hv hx hr (h.mem_opened hga ha) (h.mem_opened hgb hb) key

/-- A push of a complete table that has pushed every maximal answer and
read the complete table of each to its end. -/
theorem IsRun.served_push (h : IsRun U σ) {r k : Nat} {g : GoalOf R Rel} {kd : Kind} {left : Bool}
    {side : Nat} {other : Rel} {subs : List (Ans D P × Nat × Nat)}
    (hk : goalAt (σ r) k = some g)
    (hs : IsStrat σ k r (.push kd left side other (some []) subs))
    (hd : (σ r).isDone side = true)
    (hsub : ∀ e ∈ subs, (σ r).isDone e.2.1 = true ∧ (σ r).len e.2.1 ≤ e.2.2) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  have hp := h.prog hk hs
  dsimp only [Prog] at hp
  obtain ⟨L, Rg, hsp, hgs, ho, htodo, hsubs, -⟩ := hp
  obtain ⟨-, -, hcover⟩ := htodo [] rfl
  have key : ∀ a, Held (held σ) (toGoal (if left then L else Rg)) a → ∃ e ∈ subs,
      Held (held σ) (toGoal (if left then L else Rg)) e.1.span ∧
      den P.sorts.interp a ⊆ den P.sorts.interp e.1.span ∧
      toGoal (pushG D g other kd left e.1) ∈ opened σ ∧
      ∀ b, Held (held σ) (toGoal (pushG D g other kd left e.1)) b →
        EvO P (held σ) (toGoal g) (pushedS D kd left e.1.span b) := by
    intro a ha
    obtain ⟨r1, y, hy, rfl⟩ := (h.held_iff hgs a).1 ha
    obtain ⟨x', -, hmem, hden⟩ := hcover y (h.done_answers hd r1 hy)
    rcases hmem with hmem | hmem
    · cases hmem
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
    obtain ⟨he1, hge, hrd⟩ := hsubs e he
    refine ⟨e, he, (h.held_iff hgs _).2 ⟨r, e.1, he1, rfl⟩, hden,
      h.mem_opened hge (.inl ⟨r, (hsub e he).1⟩), fun b hb z hz => ?_⟩
    obtain ⟨r2, y2, hy2, rfl⟩ := (h.held_iff hge b).1 hb
    obtain ⟨n, hn⟩ := List.getElem?_of_mem (h.done_answers (hsub e he).1 r2 hy2)
    have hlt := (List.getElem?_eq_some_iff.1 hn).1
    have hle := (hsub e he).2
    unfold StateOf.len at hle
    exact h.ev hk (hrd.2 n y2 (by omega) hn z hz)
  have hside : toGoal (if left then L else Rg) ∈ opened σ := h.mem_opened hgs (.inl ⟨r, hd⟩)
  have push : ∀ a, Held (held σ) (toGoal (if left then L else Rg)) a → ∃ a',
      Held (held σ) (toGoal (if left then L else Rg)) a' ∧
      den P.sorts.interp a ⊆ den P.sorts.interp a' ∧ ∃ e : Ans D P × Nat × Nat, e.1.span = a' ∧
      toGoal (pushG D g other kd left e.1) ∈ opened σ ∧
      ∀ b, Held (held σ) (toGoal (pushG D g other kd left e.1)) b →
        EvO P (held σ) (toGoal g) (pushedS D kd left e.1.span b) := fun a ha => by
    obtain ⟨e, -, k1, k2, k3, k4⟩ := key a ha
    exact ⟨e.1.span, k1, k2, e, rfl, k3, k4⟩
  cases kd with
  | seq =>
    obtain ⟨xs, i, l, r', hv, h0, hi, hl, hr, rfl, rfl⟩ := hsp
    cases left with
    | true =>
      simp only [↓reduceIte] at ho hside push
      subst ho
      refine .pushL xs i _ _ hv h0 hi hl hr ⟨hside, fun a ha => ?_⟩
      obtain ⟨a', k1, k2, e, rfl, k3, k4⟩ := push a ha
      exact ⟨e.1.span, k1, k2, k3, k4⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at ho hside push
      subst ho
      refine .pushR xs i _ _ hv h0 hi hl hr ⟨hside, fun a ha => ?_⟩
      obtain ⟨a', k1, k2, e, rfl, k3, k4⟩ := push a ha
      exact ⟨e.1.span, k1, k2, k3, k4⟩
  | and =>
    obtain ⟨xs, i, x, r', hv, -, hx, hr, rfl, rfl⟩ := hsp
    cases left with
    | true =>
      simp only [↓reduceIte] at ho hside push
      subst ho
      refine .meetL xs i _ _ hv hx hr ⟨hside, fun a ha => ?_⟩
      obtain ⟨a', k1, k2, e, rfl, k3, k4⟩ := push a ha
      exact ⟨e.1.span, k1, k2, k3, k4⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at ho hside push
      subst ho
      refine .meetR xs i _ _ hv hx hr ⟨hside, fun a ha => ?_⟩
      obtain ⟨a', k1, k2, e, rfl, k3, k4⟩ := push a ha
      exact ⟨e.1.span, k1, k2, k3, k4⟩

/-- An interface check whose goals are not neglected and never have an
answer. -/
theorem IsRun.served_check (h : IsRun U σ) {r k : Nat} {g : GoalOf R Rel} {left : Bool}
    {side other : Rel} {subs : List Nat} (hk : goalAt (σ r) k = some g)
    (hs : IsStrat σ k r (.check left side other (.opened subs)))
    (hsub : ∀ j ∈ subs, (∀ r' h', goalAt (σ r') j = some h' → Opened σ j) ∧
      ∀ r', (σ r').answers j = []) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  have hp := h.prog hk hs
  dsimp only [Prog] at hp
  obtain ⟨L, Rg, hsp, hside, hother, ps, -, hedge, -, hps⟩ := hp
  have hn := h.normal hk
  have hfo := hsp.fo ((h.good r).base.good k g hk).2.2
  have none : ∀ p ∈ ps,
      toGoal (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩ : GoalOf R Rel) ∈
        opened σ ∧ ∀ a, ¬ Held (held σ)
          (toGoal (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩ : GoalOf R Rel))
          a := by
    intro p hp
    obtain ⟨n, hn'⟩ := List.getElem?_of_mem hp
    obtain ⟨j, hj, hgj⟩ := hps n p hn'
    have hj' := hsub j (List.mem_of_getElem? hj)
    refine ⟨h.mem_opened hgj (hj'.1 _ _ hgj), fun a ha => ?_⟩
    obtain ⟨r1, y, hy, -⟩ := (h.held_iff hgj a).1 ha
    rw [hj'.2 r1] at hy
    cases hy
  obtain ⟨xs, i, l, r', hv, h0, hi, hl, hr, rfl, rfl⟩ := hsp
  cases left with
  | true =>
    simp only [↓reduceIte] at hside hother none hedge
    subst hside
    subst hother
    exact .checkL xs i _ _ hv h0 hi hl hr ps
      (fun kk G hG x m hxm => hedge.2 (hn.interval hl) hfo.1 kk G hG x m hxm) none
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hside hother none hedge
    subst hside
    subst hother
    exact .checkR xs i _ _ hv h0 hi hl hr ps
      (fun kk G hG m z hmz => hedge.2 (hn.interval hr) hfo.2 kk G hG m z hmz) none

/-! ## A complete table is served -/

/-- A table that is complete had, when it became so, a strategy with
nothing left to do that reads complete tables only, or a final verdict of
its race. -/
theorem IsRun.quiet_of_done (h : IsRun U σ) {k : Nat} : ∀ r, (σ r).isDone k = true →
    ∃ r' t', (σ r').tables[k]? = some t' ∧ (QuietAt (σ r') t' ∨ Raced (raceSem U) (σ r') k)
  | 0, hd => by
    cases ht : (σ 0).tables[k]? with
    | none => simp [StateOf.isDone, ht] at hd
    | some t =>
      rw [isDone_of_table ht, h.fresh k t ht] at hd
      cases hd
  | r + 1, hd => by
    cases ht : (σ (r + 1)).tables[k]? with
    | none => simp [StateOf.isDone, ht] at hd
    | some t' =>
      rw [isDone_of_table ht] at hd
      rcases (h.req.req r).done k t' ht hd with ⟨t, ht0, hd0⟩ | hq
      · exact h.quiet_of_done r (by rw [isDone_of_table ht0]; exact hd0)
      · exact ⟨r + 1, t', ht, hq⟩

/-- **A complete table is served.** -/
theorem IsRun.served_done (h : IsRun U σ) {r0 k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r0) k = some g) (hd : EvDone σ k) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  obtain ⟨r1, hd1⟩ := hd
  obtain ⟨r, t', ht', ⟨gs, hg, gr, hgr, s, hs, hq⟩ | hrc⟩ := h.quiet_of_done r1 hd1
  swap
  · obtain ⟨t, ht, l, hl, -, -, hcov⟩ := hrc
    have hkr := h.goal_at hk ht
    have eg : t.goal = g := by
      have := hkr
      unfold goalAt at this
      rw [ht] at this
      exact Option.some.inj this
    rw [eg] at hcov
    refine .whole fun k' G hG hne => ?_
    obtain ⟨a, ha, hX⟩ := hcov k' G hG hne
    exact ⟨a.span, ⟨r, k, g, hkr, rfl, a, by
        unfold StateOf.answers; rw [ht]; exact hl.subset ha, rfl⟩, hX⟩
  have hst : IsStrat σ k r s := ⟨t', gs, gr, ht', hg, hgr, hs⟩
  have hkr := h.goal_at hk ht'
  have dn : ∀ j, (σ r).isDone j = true → Opened σ j := fun j hj => .inl ⟨r, hj⟩
  cases s with
  | span ran =>
    cases ran with
    | false => simp [Strat.quiet, Strat.pending] at hq
    | true => exact h.served_span hk hst
  | copy c subs =>
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
      List.any_eq_false, List.all_eq_true, decide_eq_true_eq] at hq
    refine h.served_copy hkr hst fun m j pos0 hm => ?_
    have hmem := List.mem_of_getElem? hm
    refine ⟨dn j (hq.2 _ hmem), fun n r1 hn => ⟨r, subs, pos0, hst, hm, ?_⟩⟩
    have h1 : ¬ pos0 < ((σ r).answers j).length := hq.1 _ hmem
    have h2 : (σ r1).len j ≤ (σ r).len j := h.done_len (hq.2 _ hmem) r1
    unfold StateOf.len at h2 hn
    omega
  | join kd a b c =>
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true'] at hq
    have hp := h.prog hk hst
    dsimp only [Prog] at hp
    obtain ⟨-, -, -, -, -, hok, -⟩ := hp
    refine h.served_join hkr hst (dn a hq.2.1) (dn b hq.2.2) fun p q r1 hp hq' =>
      ⟨r, c, hst, hok.pending_false.1 hq.1 p q ?_ ?_⟩
    · exact Nat.lt_of_lt_of_le hp (h.done_len hq.2.1 r1)
    · exact Nat.lt_of_lt_of_le hq' (h.done_len hq.2.2 r1)
  | push kd left side other todo subs =>
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true] at hq
    obtain ⟨hpend, ⟨hside, hsome⟩, hall⟩ := hq
    rw [hside, Bool.true_and] at hpend
    cases todo with
    | none => cases hsome
    | some l =>
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff, List.any_eq_false,
        decide_eq_true_eq] at hpend
      obtain ⟨rfl, hread⟩ := hpend
      exact h.served_push hkr hst hside fun e he => ⟨hall e he, by
        have := hread e he
        unfold StateOf.len
        omega⟩
  | check left side other c =>
    cases c with
    | reading => simp [Strat.quiet, Strat.pending] at hq
    | off => simp [Strat.quiet, Strat.pending] at hq
    | opened subs =>
      simp only [Strat.quiet, Strat.pending, Bool.not_false, Bool.true_and, List.all_eq_true,
        Bool.and_eq_true, List.isEmpty_iff] at hq
      exact h.served_check hkr hst fun j hj => ⟨fun _ _ _ => dn j (hq j hj).1, fun r' =>
        List.eq_nil_of_subset_nil (by
          have := h.done_answers (hq j hj).1 r'
          rwa [(hq j hj).2] at this)⟩

end Symmetric

end RwLog
