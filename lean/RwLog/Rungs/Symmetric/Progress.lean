/-
# Everything a strategy has done is covered in its table

What the cursors of a strategy mean. `CovS st i c` says some answer of the
table at `i` relates every pair the representative `c` relates. `Prog st i g
s` says, for the strategy `s` of the table at `i` of the goal `g`, which
tables it reads and that the table at `i` covers what its rule makes of
everything its cursors have passed:

* a span that has run covers the span between the boundaries;
* a call or a union covers the answers of each table it reads up to the
  position it has read to;
* a join covers what the rule makes of every pair its cursor has combined;
* a push that has taken the maximal answers of its side has, for every
  answer of the side, one that covers it and is pushed or still to push, and
  covers what the rule makes of each answer pushed and the answers of the
  goal opened for it, up to the position read;
* an interface check that has opened goals has opened one for each
  interface its side can show.

`Prog` holds in every later state of the run (`Prog.mono`).
-/
import RwLog.Rungs.Symmetric.Rounds
import RwLog.Rungs.Framework.RaceSpec
import RwLog.Rungs.Symmetric.Cursor
import RwLog.Kernel.NormalFormDepth
import RwLog.Kernel.NormalFormSpans

namespace RwLog

namespace Symmetric

open Traverse

section pure

variable {S N A : Type}

/-- The table at `i` is there and is not complete. -/
def Open (st : StateOf S N A) (i : Nat) : Prop := ∃ t, st.tables[i]? = some t ∧ t.done = false

theorem Busy.isOpen {st : StateOf S N A} {i : Nat} (h : Busy st i) : Open st i := by
  obtain ⟨t, ht, -, hd⟩ := h
  exact ⟨t, ht, hd⟩

theorem Frame.isOpen {j i : Nat} {st st' : StateOf S N A} (h : Frame j st st') (ho : Open st i) :
    Open st' i := by
  obtain ⟨t, ht, hd⟩ := ho
  obtain ⟨t', ht', -, e2, -⟩ := h.2.1 i t ht
  exact ⟨t', ht', e2.trans hd⟩

/-- Work on an open table changes nothing a later request relies on. -/
theorem Frame.stable {j : Nat} {st st' : StateOf S N A} (h : Frame j st st') (ho : Open st j) :
    Stable st st' := fun k t hk => by
  obtain ⟨t', ht', e1, e2, -, e4, -, e6, e7⟩ := h.2.1 k t hk
  refine ⟨t', ht', e1, e4, e7, fun hd => ⟨e2.trans hd, e6 fun e => ?_⟩⟩
  subst e
  obtain ⟨u, hu, hud⟩ := ho
  rw [hk] at hu
  cases hu
  rw [hd] at hud
  cases hud

/-- Giving paths to answers changes nothing a frame speaks of. -/
theorem Frame.stamp {j : Nat} {st st' : StateOf S N A} (h : Frame j st st') (i n : Nat)
    (pth : Path) : Frame j st (stamp i n pth st') :=
  h.trans (Frame.modify j st' i _ fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

@[simp] theorem answers_stamp (st : StateOf S N A) (i n : Nat) (pth : Path) (j : Nat) :
    (stamp i n pth st).answers j = st.answers j := by
  unfold stamp StateOf.answers StateOf.modify
  simp only [List.getElem?_modify]
  by_cases e : i = j
  · subst e; cases st.tables[i]? <;> simp
  · simp only [e, if_false]; cases st.tables[j]? <;> rfl

@[simp] theorem isDone_stamp (st : StateOf S N A) (i n : Nat) (pth : Path) (j : Nat) :
    (stamp i n pth st).isDone j = st.isDone j := by
  unfold stamp StateOf.isDone StateOf.modify
  simp only [List.getElem?_modify]
  by_cases e : i = j
  · subst e; cases st.tables[i]? <;> simp
  · simp only [e, if_false]; cases st.tables[j]? <;> rfl

@[simp] theorem goalAt_stamp (st : StateOf S N A) (i n : Nat) (pth : Path) (j : Nat) :
    goalAt (stamp i n pth st) j = goalAt st j :=
  goalAt_modify st i j _ fun _ => rfl

theorem pathsAt_length (st : StateOf S N A) (i : Nat) :
    (st.pathsAt i).length = (st.answers i).length := by
  unfold StateOf.pathsAt StateOf.answers
  cases st.tables[i]? <;> simp

theorem Stable.answers {st st' : StateOf S N A} (h : Stable st st') (i : Nat) :
    st.answers i <+: st'.answers i := by
  unfold StateOf.answers
  cases ht : st.tables[i]? with
  | none => exact List.nil_prefix
  | some t =>
    obtain ⟨t', ht', -, -, e3, -⟩ := h i t ht
    rw [ht']
    exact e3

theorem Stable.length_le {st st' : StateOf S N A} (h : Stable st st') (i : Nat) :
    (st.answers i).length ≤ (st'.answers i).length := (h.answers i).length_le

theorem Stable.getElem? {st st' : StateOf S N A} (h : Stable st st') {i n : Nat} {a : A}
    (ha : (st.answers i)[n]? = some a) : (st'.answers i)[n]? = some a := by
  obtain ⟨l, hl⟩ := h.answers i
  rw [← hl, List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1]
  exact ha

/-- An answer at a position below the length of the earlier table was
there. -/
theorem Stable.getElem?_old {st st' : StateOf S N A} (h : Stable st st') {i n : Nat} {a : A}
    (ha : (st'.answers i)[n]? = some a) (hn : n < (st.answers i).length) :
    (st.answers i)[n]? = some a := by
  obtain ⟨l, hl⟩ := h.answers i
  rw [← hl, List.getElem?_append_left hn] at ha
  exact ha

theorem Stable.isDone {st st' : StateOf S N A} (h : Stable st st') {i : Nat}
    (hd : st.isDone i = true) : st'.isDone i = true ∧ st'.answers i = st.answers i := by
  unfold StateOf.isDone StateOf.answers at *
  cases ht : st.tables[i]? with
  | none => rw [ht] at hd; cases hd
  | some t =>
    rw [ht] at hd
    obtain ⟨t', ht', -, -, -, e4⟩ := h i t ht
    rw [ht']
    exact e4 hd

theorem Stable.ext {st st' : StateOf S N A} (h : Stable st st') : Ext st st' := fun j g hg => by
  unfold goalAt at hg ⊢
  cases ht : st.tables[j]? with
  | none => rw [ht] at hg; cases hg
  | some t =>
    rw [ht] at hg
    obtain ⟨t', ht', e1, -⟩ := h j t ht
    rw [ht']
    cases hg
    exact congrArg some e1

theorem answers_modify_app (st : StateOf S N A) (i : Nat) (blk : List A) {t : Table S N A}
    (ht : st.tables[i]? = some t) : (st.modify i (app blk)).answers i = st.answers i ++ blk := by
  unfold StateOf.answers StateOf.modify
  simp [ht, app]

/-- A strategy without its cursors: what it is a strategy of. The work of a
strategy moves its cursors and nothing else. -/
def Strat.kind : Strat N A → Strat N A
  | .span _ => .span false
  | .copy c _ => .copy c []
  | .join k a b _ => .join k a b Cursor.start
  | .push k l side o _ _ => .push k l side o none []
  | .check l side o _ => .check l side o .reading

/-- The strategies of a group, without their cursors. -/
def Group.kinds (gr : Group N A) : List (Strat N A) := gr.strats.map Strat.kind

theorem kind_span {s : Strat N A} (h : s.kind = .span false) : ∃ ran, s = .span ran := by
  cases s <;> simp only [Strat.kind, reduceCtorEq] at h
  exact ⟨_, rfl⟩

theorem kind_copy {s : Strat N A} {c : Bool} (h : s.kind = .copy c []) :
    ∃ subs, s = .copy c subs := by
  cases s <;> simp only [Strat.kind, reduceCtorEq, Strat.copy.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨_, rfl⟩

theorem kind_join {s : Strat N A} {k : Kind} {a b : Nat} (h : s.kind = .join k a b Cursor.start) :
    ∃ c, s = .join k a b c := by
  cases s <;> simp only [Strat.kind, reduceCtorEq, Strat.join.injEq] at h
  obtain ⟨rfl, rfl, rfl, -⟩ := h
  exact ⟨_, rfl⟩

theorem kind_push {s : Strat N A} {k : Kind} {l : Bool} {side : Nat} {o : N}
    (h : s.kind = .push k l side o none []) : ∃ todo subs, s = .push k l side o todo subs := by
  cases s <;> simp only [Strat.kind, reduceCtorEq, Strat.push.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
  exact ⟨_, _, rfl⟩

theorem kind_check {s : Strat N A} {l : Bool} {side o : N}
    (h : s.kind = .check l side o .reading) : ∃ c, s = .check l side o c := by
  cases s <;> simp only [Strat.kind, reduceCtorEq, Strat.check.injEq] at h
  obtain ⟨rfl, rfl, rfl, -⟩ := h
  exact ⟨_, rfl⟩

end pure

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- Some answer of the table at `i` relates every pair `c` relates. -/
def CovS (st : StateOf R Rel (Ans D P)) (i : Nat) (c : R) : Prop :=
  ∃ y ∈ st.answers i, den P.sorts.interp c ⊆ den P.sorts.interp y.span

omit [DecidableEq R] in
theorem CovS.mono {st st' : StateOf R Rel (Ans D P)} (h : Stable st st') {i : Nat} {c : R}
    (hc : CovS st i c) : CovS st' i c := by
  obtain ⟨y, hy, hs⟩ := hc
  exact ⟨y, (h.answers i).subset hy, hs⟩

/-- The table at `i` has read the first `pos` answers of the table at `j`:
it covers what `f` makes of each. -/
def Read (st : StateOf R Rel (Ans D P)) (i j pos : Nat) (f : R → Option R) : Prop :=
  pos ≤ (st.answers j).length ∧
    ∀ n y, n < pos → (st.answers j)[n]? = some y → ∀ z, f y.span = some z → CovS st i z

omit [DecidableEq R] in
theorem Read.mono {st st' : StateOf R Rel (Ans D P)} (h : Stable st st') {i j pos : Nat}
    {f : R → Option R} (hr : Read st i j pos f) : Read st' i j pos f :=
  ⟨hr.1.trans (h.length_le j), fun n y hn hy z hz =>
    (hr.2 n y hn (h.getElem?_old hy (by have := hr.1; omega)) z hz).mono h⟩

omit [DecidableEq R] in
theorem Read.zero (st : StateOf R Rel (Ans D P)) (i j : Nat) (f : R → Option R) :
    Read st i j 0 f := ⟨Nat.zero_le _, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- What the rule of a join makes of two representatives. -/
def opS (D : Domain R) : Kind → R → R → Option R
  | .seq => D.compose
  | .and => D.meet

/-- What the rule of a push makes of the representative pushed and one of
the goal opened for it. -/
def pushedS (D : Domain R) : Kind → Bool → R → R → Option R
  | .seq, true, x, y => D.compose x y
  | .seq, false, x, y => D.compose y x
  | .and, _, x, y => D.meet x y

/-- The goals of the two sides of a split of the goal `g`: a chain at a
place inside it, with the middle left open; a meet into one member and the
others, at one of the members a meet is split at. -/
def SplitAt (g : GoalOf R Rel) : Kind → GoalOf R Rel → GoalOf R Rel → Prop
  | .seq, L, Rg => ∃ (xs : List Rel) (i : Nat) (l r : Rel), g.node.view = .chain xs ∧ 0 < i ∧
      i < xs.length ∧ g.node.interval 0 i = some l ∧ g.node.interval i xs.length = some r ∧
      L = ⟨g.lb, l, none⟩ ∧ Rg = ⟨none, r, g.rb⟩
  | .and, L, Rg => ∃ (xs : List Rel) (i : Nat) (x r : Rel), g.node.view = .meet xs ∧
      i ∈ andSplits xs.length ∧ xs[i]? = some x ∧ g.node.without i = some r ∧
      L = ⟨g.lb, x, g.rb⟩ ∧ Rg = ⟨g.lb, r, g.rb⟩

/-- The nodes a call (`true`) or a union reads. -/
def copyMembers (P : Program) (n : Rel) : Bool → List Rel
  | true => (Charged.bodyOf P n).toList
  | false => n.unionParts

/-- Each of the interfaces `ps` is a boundary, and if `n` is a node of the
normal form with first-order spans, every answer of `n` ends (`last`) or
begins inside one of them. An expression that is not a node reads as the
empty union, which says nothing of what it derives. -/
def EdgeOk (D : Domain R) (P : Program) (n : Rel) (last : Bool) (ps : List R) : Prop :=
  (∀ p ∈ ps, D.isBound p = true) ∧
    (Normal n → n.FO → ∀ k, ∀ G ∈ GDn P k n, ∀ x z, (x, z) ∈ G.at P.sorts.interp →
      ∃ p ∈ ps, (if last then (z, z) else (x, x)) ∈ bdenAt P.sorts.interp (some p))

/-- Some reading of the end of `n`, at some depth and some kernel, did not
give up and returned `e`. Every reading that does not give up returns the
same (`Reads.unique`), so this is a fact of the program alone. -/
def Reads (D : Domain R) (P : Program) (n : Rel) (last : Bool) (e : Option (List R)) : Prop :=
  ∃ (K : Kernel R Cost) (hK : K.Refines D) (d : Nat),
    (readEdge (K := DerivationKernel.over D K hK P) last d n).val = some e

/-- What the cursors of the strategy `s` of the table at `i`, of the goal
`g`, mean. -/
def Prog (st : StateOf R Rel (Ans D P)) (i : Nat) (g : GoalOf R Rel) :
    Strat Rel (Ans D P) → Prop
  | .span ran => (∃ s, g.node = .span s) ∧
      (ran = true → ∀ s, g.node = .span s → ∀ c, spanBoth D g.lb s g.rb = some c → CovS st i c)
  | .copy isCall subs =>
    (isCall = true → ∃ b, Charged.bodyOf P g.node = some b) ∧
    (isCall = false → ∃ xs, g.node.view = .union xs) ∧
    subs.length = (copyMembers P g.node isCall).length ∧
    ∀ (m j pos : Nat), subs[m]? = some (j, pos) → ∃ x, (copyMembers P g.node isCall)[m]? = some x ∧
      goalAt st j = some ⟨g.lb, x, g.rb⟩ ∧ Read st i j pos some
  | .join k a b c => ∃ L Rg, SplitAt g k L Rg ∧ goalAt st a = some L ∧ goalAt st b = some Rg ∧
      c.Ok (st.answers a).length (st.answers b).length ∧
      ∀ p q x y, c.Before p q → (st.answers a)[p]? = some x → (st.answers b)[q]? = some y →
        ∀ z, opS D k x.span y.span = some z → CovS st i z
  | .push k left side other todo subs => ∃ L Rg, SplitAt g k L Rg ∧
      goalAt st side = some (if left then L else Rg) ∧
      other = (if left then Rg.node else L.node) ∧
      (∀ l, todo = some l → st.isDone side = true ∧
        (∀ x, (x ∈ l ∨ x ∈ subs.map (·.1)) → x ∈ (st.answers side).maximaBy (covB D P)) ∧
        ∀ x ∈ st.answers side, ∃ x' ∈ st.answers side, (x' ∈ l ∨ x' ∈ subs.map (·.1)) ∧
          den P.sorts.interp x.span ⊆ den P.sorts.interp x'.span) ∧
      (∀ e ∈ subs, e.1 ∈ st.answers side ∧
        goalAt st e.2.1 = some (pushG D g other k left e.1) ∧
        Read st i e.2.1 e.2.2 (pushedS D k left e.1.span)) ∧
      (todo = none → subs = [])
  | .check left side other c => ∃ L Rg, SplitAt g .seq L Rg ∧
      side = (if left then L.node else Rg.node) ∧ other = (if left then Rg.node else L.node) ∧
      match c with
      | .opened subs => ∃ ps, Reads D P side left (some ps) ∧ EdgeOk D P side left ps ∧
          subs.length = ps.length ∧
          ∀ (n : Nat) (p : R), ps[n]? = some p → ∃ j, subs[n]? = some j ∧
            goalAt st j = some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩)
      | .off => Reads D P side left none
      | .reading => True

/-- What the cursors of a strategy mean stays so in every later state. -/
theorem Prog.mono {st st' : StateOf R Rel (Ans D P)} (h : Stable st st') {i : Nat}
    {g : GoalOf R Rel} {s : Strat Rel (Ans D P)} (hs : Prog st i g s) : Prog st' i g s := by
  have hE := h.ext
  cases s with
  | span ran =>
    dsimp only [Prog] at hs ⊢
    exact ⟨hs.1, fun hr s hn c hc => (hs.2 hr s hn c hc).mono h⟩
  | copy isCall subs =>
    dsimp only [Prog] at hs ⊢
    obtain ⟨h0, h1, h2, h3⟩ := hs
    refine ⟨h0, h1, h2, fun m j pos hm => ?_⟩
    obtain ⟨x, hx, hg, hr⟩ := h3 m j pos hm
    exact ⟨x, hx, hE _ _ hg, hr.mono h⟩
  | join k a b c =>
    dsimp only [Prog] at hs ⊢
    obtain ⟨L, Rg, h1, h2, h3, h4, h5⟩ := hs
    refine ⟨L, Rg, h1, hE _ _ h2, hE _ _ h3, h4.mono (h.length_le a) (h.length_le b),
      fun p q x y hb hx hy z hz => ?_⟩
    have hp := h4.before_lt hb
    exact (h5 p q x y hb (h.getElem?_old hx hp.1) (h.getElem?_old hy hp.2) z hz).mono h
  | push k left side other todo subs =>
    dsimp only [Prog] at hs ⊢
    obtain ⟨L, Rg, h1, h2, h3, h4, h5, h6⟩ := hs
    refine ⟨L, Rg, h1, hE _ _ h2, h3, fun l hl => ?_, fun e he => ?_, h6⟩
    · obtain ⟨d1, d2, d3⟩ := h4 l hl
      obtain ⟨e1, e2⟩ := h.isDone d1
      rw [e2]
      exact ⟨e1, d2, d3⟩
    · obtain ⟨d1, d2, d3⟩ := h5 e he
      exact ⟨(h.answers side).subset d1, hE _ _ d2, d3.mono h⟩
  | check left side other c =>
    dsimp only [Prog] at hs ⊢
    obtain ⟨L, Rg, h1, h2, h3, h4⟩ := hs
    refine ⟨L, Rg, h1, h2, h3, ?_⟩
    cases c with
    | opened subs =>
      obtain ⟨ps, p0, p1, p2, p3⟩ := h4
      refine ⟨ps, p0, p1, p2, fun n p hp => ?_⟩
      obtain ⟨j, hj, hg⟩ := p3 n p hp
      exact ⟨j, hj, hE _ _ hg⟩
    | reading => trivial
    | off => exact h4

/-! ## A strategy for every split -/

/-- The check of the node `side` of a split of `g` can never show `g`
empty: a check of it is not offered, or the other side has an answer under
one of the interfaces read. -/
def CheckGone (st : StateOf R Rel (Ans D P)) (g : GoalOf R Rel) (left : Bool)
    (side other : Rel) : Prop :=
  Reads D P side left none ∨ ∃ ps, Reads D P side left (some ps) ∧ ∃ p ∈ ps, ∃ j,
    goalAt st j = some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩) ∧
    st.answers j ≠ []

theorem CheckGone.mono {st st' : StateOf R Rel (Ans D P)} (h : Stable st st')
    {g : GoalOf R Rel} {left : Bool} {side other : Rel} (hc : CheckGone st g left side other) :
    CheckGone st' g left side other := by
  rcases hc with hc | ⟨ps, h1, p, hp, j, hj, hne⟩
  · exact .inl hc
  · refine .inr ⟨ps, h1, p, hp, j, h.ext _ _ hj, fun he => hne ?_⟩
    have := h.answers j
    rw [he] at this
    exact List.prefix_nil.1 this

/-- A check that is dead can never show the goal empty. -/
theorem prog_dead_gone {st : StateOf R Rel (Ans D P)} {i : Nat} {g : GoalOf R Rel} {left : Bool}
    {side other : Rel} {c : Check} (hp : Prog st i g (.check left side other c))
    (hd : (Strat.check left side other c : Strat Rel (Ans D P)).dead st = true) :
    CheckGone st g left side other := by
  dsimp only [Prog] at hp
  obtain ⟨L, Rg, -, -, -, hc⟩ := hp
  cases c with
  | reading => simp [Strat.dead] at hd
  | off => exact .inl hc
  | opened subs =>
    obtain ⟨ps, h1, -, hlen, hall⟩ := hc
    simp only [Strat.dead] at hd
    obtain ⟨j, hj, hne⟩ := List.any_eq_true.1 hd
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hj
    have hn' : n < ps.length := by omega
    obtain ⟨j', hj', hg⟩ := hall n ps[n] (List.getElem?_eq_getElem hn')
    rw [List.getElem?_eq_getElem hn] at hj'
    cases hj'
    refine .inr ⟨ps, h1, ps[n], List.getElem_mem hn', _, hg, fun he => ?_⟩
    rw [he] at hne
    simp at hne

/-- **The groups of a goal have a strategy for every way to answer it**: its
span; its call or its union; and for every split, a group with the join of
the two sides and the push of each into the other, and for a split of a
chain the check of each side, unless that check can never show the goal
empty. -/
structure Full (st : StateOf R Rel (Ans D P)) (g : GoalOf R Rel)
    (gs : List (Group Rel (Ans D P))) : Prop where
  span : (∃ s, g.node = .span s) → ∃ gr ∈ gs, .span false ∈ gr.kinds
  copy : ∀ c : Bool, (c = true → ∃ b, Charged.bodyOf P g.node = some b) →
    (c = false → ∃ xs, g.node.view = .union xs) → ∃ gr ∈ gs, .copy c [] ∈ gr.kinds
  split : ∀ k L Rg, SplitAt g k L Rg → ∃ gr ∈ gs, ∃ a b, goalAt st a = some L ∧
    goalAt st b = some Rg ∧ .join k a b Cursor.start ∈ gr.kinds ∧
    .push k true a Rg.node none [] ∈ gr.kinds ∧ .push k false b L.node none [] ∈ gr.kinds
  check : ∀ L Rg, SplitAt g .seq L Rg → ∀ left : Bool,
    CheckGone st g left (if left then L.node else Rg.node) (if left then Rg.node else L.node) ∨
      ∃ gr ∈ gs, .check left (if left then L.node else Rg.node)
        (if left then Rg.node else L.node) .reading ∈ gr.kinds

/-- The groups stay full when each group stays, with strategies of the same
kinds, or was all checks that can never show the goal empty. -/
theorem Full.keep {st st' : StateOf R Rel (Ans D P)} (hS : Stable st st') {g : GoalOf R Rel}
    {gs gs' : List (Group Rel (Ans D P))} (hF : Full st g gs)
    (h : ∀ gr ∈ gs, (∃ gr' ∈ gs', gr'.kinds = gr.kinds) ∨
      ∀ s ∈ gr.strats, ∃ l side o c, s = .check l side o c ∧ CheckGone st' g l side o) :
    Full st' g gs' := by
  have lead : ∀ gr ∈ gs, ∀ x ∈ gr.kinds, (∀ l side o, x ≠ .check l side o .reading) →
      ∃ gr' ∈ gs', x ∈ gr'.kinds := by
    intro gr hgr x hx hne
    rcases h gr hgr with ⟨gr', hgr', e⟩ | hall
    · exact ⟨gr', hgr', by rw [e]; exact hx⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      obtain ⟨l, side, o, c, rfl, -⟩ := hall s hs
      exact absurd rfl (hne l side o)
  refine ⟨fun hs => ?_, fun c h1 h2 => ?_, fun k L Rg hsp => ?_, fun L Rg hsp left => ?_⟩
  · obtain ⟨gr, hgr, hx⟩ := hF.span hs
    exact lead gr hgr _ hx (fun _ _ _ e => by cases e)
  · obtain ⟨gr, hgr, hx⟩ := hF.copy c h1 h2
    exact lead gr hgr _ hx (fun _ _ _ e => by cases e)
  · obtain ⟨gr, hgr, a, b, ha, hb, h1, h2, h3⟩ := hF.split k L Rg hsp
    rcases h gr hgr with ⟨gr', hgr', e⟩ | hall
    · exact ⟨gr', hgr', a, b, hS.ext _ _ ha, hS.ext _ _ hb, by rw [e]; exact h1,
        by rw [e]; exact h2, by rw [e]; exact h3⟩
    · obtain ⟨s, hs, hk⟩ := List.mem_map.1 h1
      obtain ⟨l, side, o, c, rfl, -⟩ := hall s hs
      cases hk
  · rcases hF.check L Rg hsp left with hg | ⟨gr, hgr, hx⟩
    · exact .inl (hg.mono hS)
    · rcases h gr hgr with ⟨gr', hgr', e⟩ | hall
      · exact .inr ⟨gr', hgr', by rw [e]; exact hx⟩
      · obtain ⟨s, hs, hk⟩ := List.mem_map.1 hx
        obtain ⟨l, side, o, c, rfl, hg⟩ := hall s hs
        simp only [Strat.kind, Strat.check.injEq, and_true] at hk
        obtain ⟨rfl, rfl, rfl⟩ := hk
        exact .inl hg

omit [Answer R] [DecidableEq R] in
/-- Only a chain and a meet have splits. -/
theorem SplitAt.view {g L Rg : GoalOf R Rel} {k : Kind} (h : SplitAt g k L Rg) :
    (k = .seq ∧ ∃ xs, g.node.view = .chain xs) ∨ (k = .and ∧ ∃ xs, g.node.view = .meet xs) := by
  cases k with
  | seq =>
    obtain ⟨xs, i, l, r, hv, -⟩ := h
    exact .inl ⟨rfl, xs, hv⟩
  | and =>
    obtain ⟨xs, i, l, r, hv, -⟩ := h
    exact .inr ⟨rfl, xs, hv⟩

/-- Only a call has a body. -/
theorem bodyOf_view {e b : Rel} (h : Charged.bodyOf P e = some b) : ∃ n f, e.view = .call n f := by
  cases e with
  | call m => exact ⟨_, _, rfl⟩
  | conv a =>
    cases a with
    | call m => exact ⟨_, _, rfl⟩
    | _ => simp [Charged.bodyOf] at h
  | _ => simp [Charged.bodyOf] at h

/-- The groups are full if they have the strategies of the kind of the
node. -/
theorem Full.of_view {st : StateOf R Rel (Ans D P)} {g : GoalOf R Rel}
    {gs : List (Group Rel (Ans D P))} {V : NodeView Span Rel} (hv : g.node.view = V)
    (hspan : ∀ s, V = .span s → ∃ gr ∈ gs, .span false ∈ gr.kinds)
    (hcall : ∀ n f, V = .call n f → ∃ gr ∈ gs, .copy true [] ∈ gr.kinds)
    (hunion : ∀ xs, V = .union xs → ∃ gr ∈ gs, .copy false [] ∈ gr.kinds)
    (hsplit : ∀ k L Rg, SplitAt g k L Rg → ∃ gr ∈ gs, ∃ a b, goalAt st a = some L ∧
      goalAt st b = some Rg ∧ .join k a b Cursor.start ∈ gr.kinds ∧
      .push k true a Rg.node none [] ∈ gr.kinds ∧ .push k false b L.node none [] ∈ gr.kinds)
    (hcheck : ∀ L Rg, SplitAt g .seq L Rg → ∀ left : Bool,
      CheckGone st g left (if left then L.node else Rg.node)
          (if left then Rg.node else L.node) ∨
        ∃ gr ∈ gs, .check left (if left then L.node else Rg.node)
          (if left then Rg.node else L.node) .reading ∈ gr.kinds) : Full st g gs := by
  refine ⟨fun ⟨s, hs⟩ => hspan s (by rw [← hv, hs]; rfl), fun c h1 h2 => ?_, hsplit, hcheck⟩
  cases c with
  | true =>
    obtain ⟨b, hb⟩ := h1 rfl
    obtain ⟨n, f, e⟩ := bodyOf_view hb
    exact hcall n f (by rw [← hv, e])
  | false =>
    obtain ⟨xs, e⟩ := h2 rfl
    exact hunion xs (by rw [← hv, e])

theorem Full.mono {st st' : StateOf R Rel (Ans D P)} (hS : Stable st st') {g : GoalOf R Rel}
    {gs : List (Group Rel (Ans D P))} (hF : Full st g gs) : Full st' g gs :=
  hF.keep hS fun gr hgr => .inl ⟨gr, hgr, rfl⟩

/-- Every table that has groups has a strategy for every way to answer its
goal. -/
def FullAll (st : StateOf R Rel (Ans D P)) : Prop :=
  ∀ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t → ∀ gs, t.groups = some gs →
    Full st t.goal gs

/-! ## What the rules return -/

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- An answer put into a table is covered there. -/
theorem cov_addOption (hL : D.Lawful P.sorts.interp) (st : StateOf R Rel (Ans D P)) (i : Nat)
    (ho : Open st i) (c : Ans D P) :
    CovS (addOption (K := DerivationKernel.over D K hK P) i st (some c)).val i c.span := by
  have hv := addAnswer_val (P := P) K hK i st c
  obtain ⟨t, ht, -⟩ := ho
  at_cost K hK
  show CovS (addAnswer (K := DerivationKernel.over D _ hK P) i st c).val i c.span
  rw [hv]
  have hin : c ∈ (st.modify i (app [c])).answers i := by
    rw [answers_modify_app st i [c] ht]; simp
  split
  · next h =>
    obtain ⟨y, hy, hc⟩ := List.any_eq_true.1 h
    exact ⟨y, hy, (hL.covers_iff _ _).1 hc⟩
  · split
    · split
      · exact ⟨c, hin, subset_rfl⟩
      · have ht' : (st.modify i (app [c])).tables[i]? = some (app [c] t) := by
          unfold StateOf.modify; simp [ht]
        exact ⟨c, by rw [answers_modify_app _ i _ ht']; exact List.mem_append_left _ hin,
          subset_rfl⟩
    · exact ⟨c, hin, subset_rfl⟩

omit [DecidableEq R] in
/-- A fold of steps on the table at `i`, each of which covers what it is
given, covers everything it is given. -/
theorem foldL_cov {α : Type} (i : Nat)
    (f : StateOf R Rel (Ans D P) → α → Cost (StateOf R Rel (Ans D P)))
    (ok : α → Prop) (C : StateOf R Rel (Ans D P) → α → Prop)
    (hstep : ∀ st x, ok x → Open st i → Frame i st (f st x).val ∧ C (f st x).val x)
    (hmono : ∀ st st' x, Stable st st' → C st x → C st' x) :
    ∀ (xs : List α) (st : StateOf R Rel (Ans D P)), (∀ x ∈ xs, ok x) → Open st i →
      Frame i st (foldL f st xs).val ∧ ∀ x ∈ xs, C (foldL f st xs).val x
  | [], st, _, _ => ⟨Frame.refl i st, fun _ h => by cases h⟩
  | x :: xs, st, hok, ho => by
    simp only [foldL, Cost.bind_val]
    obtain ⟨hf, hc⟩ := hstep st x (hok x List.mem_cons_self) ho
    obtain ⟨hf', hc'⟩ := foldL_cov i f ok C hstep hmono xs _
      (fun y hy => hok y (List.mem_cons_of_mem _ hy)) (hf.isOpen ho)
    refine ⟨hf.trans hf', fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hmono _ _ _ (hf'.stable (hf.isOpen ho)) hc
    · exact hc' y hy

omit [DecidableEq R] in
/-- The rule of a call or a union takes an answer of the member it reads. -/
theorem copy_ok {g : GoalOf R Rel} {isCall : Bool} {m : Nat} {x : Rel} {a : Ans D P}
    (hm : (copyMembers P g.node isCall)[m]? = some x) (ha : GoalIs ⟨g.lb, x, g.rb⟩ a) :
    ∃ c, (if isCall then Ans.unfold D P a g.node else Ans.inj D P a g.node m).val = some c ∧
      c.span = a.span := by
  unfold GoalIs at ha
  have hn : a.goal.node = x := by rw [ha]
  cases isCall with
  | true =>
    simp only [copyMembers] at hm
    cases hb : Charged.bodyOf P g.node with
    | none => rw [hb] at hm; simp at hm
    | some b =>
      rw [hb] at hm
      obtain rfl : b = x := by
        cases m with
        | zero => simpa using hm
        | succ m => simp at hm
      obtain ⟨c, h1, h2, -⟩ := Ans.unfold_ok (a := a) (hn ▸ hb)
      exact ⟨c, h1, h2⟩
  | false =>
    simp only [copyMembers] at hm
    obtain ⟨c, h1, h2, -⟩ := Ans.inj_ok (a := a) (hn ▸ hm)
    exact ⟨c, h1, h2⟩

/-- The rule of a join takes an answer of each side of the split. -/
theorem both_ok {k : Kind} {x y : Ans D P} {z : R} {g L Rg : GoalOf R Rel}
    (hs : SplitAt g k L Rg) (hx : GoalIs L x) (hy : GoalIs Rg y)
    (hz : opS D k x.span y.span = some z) :
    ∃ c, (both (K := DerivationKernel.over D K hK P) k x y).val = some c ∧ c.span = z := by
  unfold GoalIs at hx hy
  cases k with
  | seq =>
    obtain ⟨xs, i, l, r, -, -, -, -, -, rfl, rfl⟩ := hs
    obtain ⟨c, h1, h2, -⟩ := Ans.join_ok K hK (a := x) (b := y)
      (.inl ⟨by rw [hx], .inl (by rw [hy])⟩) hz
    exact ⟨c, h1, h2⟩
  | and =>
    obtain ⟨xs, i, m, r, -, -, -, -, rfl, rfl⟩ := hs
    obtain ⟨c, h1, h2, -⟩ := Ans.meetA_ok K hK (a := x) (b := y)
      (.inl ⟨by rw [hx, hy], by rw [hx, hy]⟩) hz
    exact ⟨c, h1, h2⟩

/-- The rule of a push takes the answer pushed and an answer of the goal
opened for it. -/
theorem pushed_ok {k : Kind} {left : Bool} {x y : Ans D P} {z : R} {g L Rg : GoalOf R Rel}
    {other : Rel} (hs : SplitAt g k L Rg) (hx : GoalIs (if left then L else Rg) x)
    (hy : GoalIs (pushG D g other k left x) y) (hz : pushedS D k left x.span y.span = some z) :
    ∃ c, (pushed (K := DerivationKernel.over D K hK P) k left x y).val = some c ∧ c.span = z := by
  unfold GoalIs at hx hy
  cases k with
  | seq =>
    obtain ⟨xs, i, l, r, -, -, -, -, -, rfl, rfl⟩ := hs
    cases left with
    | true =>
      simp only [pushG, ite_true] at hx hy
      obtain ⟨c, h1, h2, -⟩ := Ans.join_ok K hK (a := x) (b := y)
        (.inl ⟨by rw [hx], .inr (by rw [hy])⟩) hz
      exact ⟨c, h1, h2⟩
    | false =>
      simp only [pushG, Bool.false_eq_true, ite_false] at hx hy
      obtain ⟨c, h1, h2, -⟩ := Ans.join_ok K hK (a := y) (b := x)
        (.inr ⟨by rw [hx], by rw [hy]⟩) hz
      exact ⟨c, h1, h2⟩
  | and =>
    have hy' : y.goal = ⟨D.leftBound x.span, other, D.rightBound x.span⟩ := by
      cases left <;> exact hy
    obtain ⟨c, h1, h2, -⟩ := Ans.meetA_ok K hK (a := x) (b := y)
      (.inr ⟨by rw [hy'], by rw [hy']⟩) (by cases left <;> exact hz)
    exact ⟨c, h1, h2⟩

/-! ## What the work of a strategy covers -/

/-- A call or a union covers the answers it takes in. -/
theorem copyFrom_cov (hL : D.Lawful P.sorts.interp) (i : Nat) (g : GoalOf R Rel)
    (isCall : Bool) (m : Nat) (st : StateOf R Rel (Ans D P)) (as : List (Ans D P))
    (ho : Open st i)
    (happ : ∀ a ∈ as, ∃ c,
      (if isCall then Ans.unfold D P a g.node else Ans.inj D P a g.node m).val = some c ∧
        c.span = a.span) :
    Frame i st (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val ∧
      ∀ a ∈ as, CovS (copyFrom (K := DerivationKernel.over D K hK P) i g isCall m st as).val i
        a.span := by
  have hcov := fun st ho c => cov_addOption (K := K) (hK := hK) hL st i ho c
  have hin := fun st o => inner_addOption (K := K) (hK := hK) (P := P) st i o
  at_cost K hK
  unfold copyFrom
  refine foldL_cov i _ (fun a => a ∈ as) (fun st a => CovS st i a.span) (fun st a ha ho => ?_)
    (fun _ _ _ h hc => hc.mono h) as st (fun _ h => h) ho
  obtain ⟨c, hc, hs⟩ := happ a ha
  cases isCall <;>
  · simp only [ite_true, Bool.false_eq_true, ite_false] at hc ⊢
    erw [Cost.bind_val]
    refine ⟨(hin _ _).frame, ?_⟩
    erw [hc]
    rw [← hs]
    exact hcov _ ho c

/-- A join covers what its rule makes of the pairs it combines. -/
theorem joinPairs_cov (hL : D.Lawful P.sorts.interp) (i : Nat) (k : Kind)
    (xs ys : List (Ans D P)) (st : StateOf R Rel (Ans D P)) (ps : List (Nat × Nat))
    (ho : Open st i) {g L Rg : GoalOf R Rel} (hs : SplitAt g k L Rg)
    (hx : ∀ x ∈ xs, GoalIs L x) (hy : ∀ y ∈ ys, GoalIs Rg y) :
    Frame i st (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val ∧
      ∀ p ∈ ps, ∀ x y, xs[p.1]? = some x → ys[p.2]? = some y → ∀ z,
        opS D k x.span y.span = some z →
        CovS (joinPairs (K := DerivationKernel.over D K hK P) i k xs ys st ps).val i z := by
  have hcov := fun st ho c => cov_addOption (K := K) (hK := hK) hL st i ho c
  have hin := fun st o => inner_addOption (K := K) (hK := hK) (P := P) st i o
  have hb := fun (x y : Ans D P) (z : R) hx hy hz =>
    both_ok (K := K) (hK := hK) (x := x) (y := y) (z := z) hs hx hy hz
  at_cost K hK
  refine foldL_cov i _ (fun _ => True)
    (fun st p => ∀ (x y : Ans D P), xs[p.1]? = some x → ys[p.2]? = some y → ∀ z,
      opS D k x.span y.span = some z → CovS st i z)
    (fun st p _ ho => ?_)
    (fun _ _ _ h hc (x y : Ans D P) ex ey z hz => (hc x y ex ey z hz).mono h) ps st
    (fun _ _ => trivial) ho
  split
  · next x y ex ey =>
    erw [Cost.bind_val]
    refine ⟨(hin _ _).frame, fun x' y' ex' ey' z hz => ?_⟩
    obtain rfl : x = x' := Option.some.inj (ex.symm.trans ex')
    obtain rfl : y = y' := Option.some.inj (ey.symm.trans ey')
    obtain ⟨c, hc, hsp⟩ := hb x y z (hx x (List.mem_of_getElem? ex))
      (hy y (List.mem_of_getElem? ey)) hz
    rw [hc, ← hsp]
    exact hcov _ ho c
  · next hne =>
    exact ⟨Frame.refl i st, fun x y ex ey => absurd ey (by
      intro ey; exact hne x y ex ey)⟩

/-- A push covers what its rule makes of the answer pushed and the answers
it takes of the goal opened for it. -/
theorem pushTake_cov (hL : D.Lawful P.sorts.interp) (i : Nat) (k : Kind) (left : Bool)
    (x : Ans D P) (st : StateOf R Rel (Ans D P)) (ys : List (Ans D P)) (ho : Open st i)
    {g L Rg : GoalOf R Rel} {other : Rel} (hs : SplitAt g k L Rg)
    (hx : GoalIs (if left then L else Rg) x)
    (hy : ∀ y ∈ ys, GoalIs (pushG D g other k left x) y) :
    Frame i st (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val ∧
      ∀ y ∈ ys, ∀ z, pushedS D k left x.span y.span = some z →
        CovS (pushTake (K := DerivationKernel.over D K hK P) i k left x st ys).val i z := by
  have hcov := fun st ho c => cov_addOption (K := K) (hK := hK) hL st i ho c
  have hin := fun st o => inner_addOption (K := K) (hK := hK) (P := P) st i o
  have hb := fun (y : Ans D P) (z : R) hy hz =>
    pushed_ok (K := K) (hK := hK) (x := x) (y := y) (z := z) (other := other) hs hx hy hz
  at_cost K hK
  unfold pushTake
  refine foldL_cov i _ (fun y => y ∈ ys)
    (fun st y => ∀ z, pushedS D k left x.span y.span = some z → CovS st i z)
    (fun st y hmem ho => ?_) (fun _ _ _ h hc z hz => (hc z hz).mono h) ys st (fun _ h => h) ho
  erw [Cost.bind_val]
  refine ⟨(hin _ _).frame, fun z hz => ?_⟩
  obtain ⟨c, hc, hsp⟩ := hb y z (hy y hmem) hz
  rw [hc, ← hsp]
  exact hcov _ ho c

/-! ## Opening goals -/

theorem openGoal_goalAt (st : StateOf R Rel (Ans D P)) (h : GoalOf R Rel) :
    goalAt (openGoal (K := DerivationKernel.over D K hK P) st h).val.1
      (openGoal (K := DerivationKernel.over D K hK P) st h).val.2 = some h := by
  have hidx := indexFrom_some (P := P) K hK h st.tables 0
  at_cost K hK
  simp only [openGoal, Cost.bind_val]
  split
  · next i hi =>
    obtain ⟨-, t, ht, hg⟩ := hidx i hi
    simp only [Cost.pure_val]
    unfold goalAt
    rw [Nat.sub_zero] at ht
    rw [ht]; exact congrArg some hg
  · simp [goalAt]

omit [DecidableEq R] in
/-- A fold that opens a goal for each entry of a list and keeps what it
opened: the tables opened, one for each entry, in order. -/
theorem foldL_open {α γ : Type}
    (f : StateOf R Rel (Ans D P) × List γ → α → Cost (StateOf R Rel (Ans D P) × List γ))
    (Q : StateOf R Rel (Ans D P) → α → γ → Prop)
    (hf : ∀ acc x, Ext acc.1 (f acc x).val.1 ∧
      ∃ e, (f acc x).val.2 = acc.2 ++ [e] ∧ Q (f acc x).val.1 x e)
    (hQ : ∀ st st' x e, Ext st st' → Q st x e → Q st' x e) :
    ∀ (xs : List α) (acc : StateOf R Rel (Ans D P) × List γ),
      Ext acc.1 (foldL f acc xs).val.1 ∧ ∃ es, (foldL f acc xs).val.2 = acc.2 ++ es ∧
        List.Forall₂ (Q (foldL f acc xs).val.1) xs es
  | [], acc => ⟨fun _ _ h => h, [], (List.append_nil _).symm, .nil⟩
  | x :: xs, acc => by
    simp only [foldL, Cost.bind_val]
    obtain ⟨hE, e, he, hq⟩ := hf acc x
    obtain ⟨hE', es, hes, hall⟩ := foldL_open f Q hf hQ xs (f acc x).val
    exact ⟨fun j g h => hE' j g (hE j g h), e :: es, by rw [hes, he]; simp,
      .cons (hQ _ _ _ _ hE' hq) hall⟩

/-- What a push opens: a goal for each answer, in order, read from its
start. -/
theorem pushOpen_spec (g : GoalOf R Rel) (other : Rel) (k : Kind) (left : Bool)
    (st : StateOf R Rel (Ans D P)) (xs : List (Ans D P)) :
    (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.2.map (·.1) = xs ∧
      ∀ e ∈ (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.2,
        e.1 ∈ xs ∧ e.2.2 = 0 ∧
        goalAt (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1 e.2.1 =
          some (pushG D g other k left e.1) := by
  have hp := pushGoal_val (P := P) K hK g other k left
  have hog := fun st h => openGoal_goalAt (K := K) (hK := hK) (P := P) st h
  have hin := fun st h => (inner_openGoal (K := K) (hK := hK) (P := P) (w := 0) st h).reach.ext
  have key : Ext st (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1 ∧
      ∃ es, (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.2 =
        [] ++ es ∧ List.Forall₂ (fun x (e : Ans D P × Nat × Nat) => e.1 = x ∧ e.2.2 = 0 ∧
          goalAt (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1
            e.2.1 = some (pushG D g other k left x)) xs es := by
    at_cost K hK
    unfold pushOpen
    exact foldL_open _ (fun st x (e : Ans D P × Nat × Nat) => e.1 = x ∧ e.2.2 = 0 ∧
        goalAt st e.2.1 = some (pushG D g other k left x))
      (fun acc x => by
        simp only [Cost.bind_val, Cost.pure_val, hp]
        exact ⟨hin _ _, _, rfl, rfl, rfl, hog _ _⟩)
      (fun _ _ _ _ hE h => ⟨h.1, h.2.1, hE _ _ h.2.2⟩) xs (st, [])
  obtain ⟨-, es, hes, hall⟩ := key
  rw [List.nil_append] at hes
  rw [hes]
  refine ⟨?_, fun e he => ?_⟩
  · exact forall₂_map hall fun _ _ h => h.1
  · obtain ⟨x, hx, rfl, h2, h3⟩ := forall₂_mem_right hall he
    exact ⟨hx, h2, h3⟩

/-! ## Edges -/

/-- Every edge the state keeps is right about the program. -/
def EdgesOk (st : StateOf R Rel (Ans D P)) : Prop :=
  ∀ e ∈ st.edges, Reads D P e.1 e.2.1 e.2.2 ∧ ∀ ps, e.2.2 = some ps → EdgeOk D P e.1 e.2.1 ps

variable (D P K hK) in
/-- A reading of an edge that returns interfaces is right about the
program. -/
def ReadOk : Prop :=
  ∀ (last : Bool) (d : Nat) (n : Rel) (ps : List R),
    (readEdge (K := DerivationKernel.over D K hK P) last d n).val = some (some ps) →
      EdgeOk D P n last ps

theorem lookupEdge_mem (n : Rel) (last : Bool) :
    ∀ (es : List (Rel × Bool × Option (List R))) (e : Option (List R)),
      (lookupEdge (K := DerivationKernel.over D K hK P) n last es).val = some e →
        (n, last, e) ∈ es := by
  at_cost K hK
  intro es
  induction es with
  | nil => intro e h; cases h
  | cons x es ih =>
    intro e h
    simp only [lookupEdge] at h
    split at h
    · next hl =>
      simp only [Cost.bind_val, over_eqNode, Charged.eqNode, Charged.op] at h
      split at h
      · next hn =>
        cases h
        have hn' : x.1 = n := by simpa using hn
        obtain ⟨a, b, c⟩ := x
        simp only at hl hn'
        subst hl hn'
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih e h)
    · exact List.mem_cons_of_mem _ (ih e h)

/-- The edge of a node, as the state gives it, is right about the program,
and the state keeps only edges that are. -/
theorem edgeOf_spec (hR : ReadOk D P K hK) {st : StateOf R Rel (Ans D P)} (hE : EdgesOk st)
    (last : Bool) (n : Rel) :
    EdgesOk (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1 ∧
      (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.1.tables = st.tables ∧
      (∀ ps, (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.2 = some (some ps) →
        EdgeOk D P n last ps) ∧
      ∀ e, (edgeOf (K := DerivationKernel.over D K hK P) st last n).val.2 = some e →
        Reads D P n last e := by
  have hlk := lookupEdge_mem (K := K) (hK := hK) (P := P) n last st.edges
  have hR' := hR last st.depth n
  have hrd : ∀ e, (readEdge (K := DerivationKernel.over D K hK P) last st.depth n).val = some e →
      Reads D P n last e := fun e h => ⟨K, hK, st.depth, h⟩
  clear hR
  at_cost K hK
  simp only [edgeOf, Cost.bind_val]
  split
  · next e he =>
    exact ⟨hE, rfl, (fun ps hps => (hE _ (hlk e he)).2 ps (by cases hps; rfl)),
      fun e' he' => by cases he'; exact (hE _ (hlk e he)).1⟩
  · simp only [Cost.bind_val, Cost.pure_val]
    cases hr : (readEdge (K := DerivationKernel.over D _ hK P) last st.depth n).val with
    | none => exact ⟨hE, rfl, (fun ps hps => by cases hps), fun e he => by cases he⟩
    | some e =>
      refine ⟨fun x hx => ?_, rfl, fun ps hps => ?_, fun e' he' => ?_⟩
      · rcases List.mem_append.1 hx with hx | hx
        · exact hE x hx
        · obtain rfl := List.mem_singleton.1 hx
          refine ⟨hrd e hr, fun ps hps => ?_⟩
          simp only at hps
          subst hps
          exact hR' ps hr
      · cases hps
        exact hR' ps hr
      · cases he'
        exact hrd e hr

/-- What a check opens: the other side under each interface, in order. -/
theorem checkOpen_spec (g : GoalOf R Rel) (left : Bool) (other : Rel)
    (st : StateOf R Rel (Ans D P)) (ps : List R) :
    Ext st (checkOpen (K := DerivationKernel.over D K hK P) g left other st ps).val.1 ∧
      ∃ es, (checkOpen (K := DerivationKernel.over D K hK P) g left other st ps).val.2 =
        [] ++ es ∧ List.Forall₂ (fun p j =>
          goalAt (checkOpen (K := DerivationKernel.over D K hK P) g left other st ps).val.1 j =
            some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩)) ps es := by
  have hog := fun st h => openGoal_goalAt (K := K) (hK := hK) (P := P) st h
  have hin := fun st h => (inner_openGoal (K := K) (hK := hK) (P := P) (w := 0) st h).reach.ext
  at_cost K hK
  unfold checkOpen
  exact foldL_open _ (fun st p j =>
      goalAt st j = some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩))
    (fun acc x => by
      simp only [Cost.bind_val, Cost.pure_val]
      exact ⟨hin _ _, _, rfl, hog _ _⟩)
    (fun _ _ _ _ hE h => hE _ _ h) ps (st, [])

/-! ## The work of one strategy keeps what its cursors mean -/

/-- Giving paths to answers changes nothing `Prog` speaks of. -/
theorem prog_stamp (st : StateOf R Rel (Ans D P)) (j n : Nat) (pth : Path) (i : Nat)
    (g : GoalOf R Rel) (s : Strat Rel (Ans D P)) :
    Prog (stamp j n pth st) i g s = Prog st i g s := by
  cases s <;> simp only [Prog, CovS, Read, answers_stamp, isDone_stamp, goalAt_stamp]

theorem prog_work_span (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (i : Nat) (g : GoalOf R Rel) (ran : Bool) (ho : Open st i)
    (hb : IsBound D g.lb ∧ IsBound D g.rb) (hs : Prog st i g (.span ran)) :
    Prog (work (K := DerivationKernel.over D K hK P) i g st (.span ran)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) i g st (.span ran)).val.2.1 := by
  have hcov := fun c => cov_addOption (K := K) (hK := hK) hL st i ho c
  have hleaf := fun s z hz => Ans.leaf_ok (P := P) K hK (s := s) (z := z) hb.1 hb.2 hz
  at_cost K hK
  cases ran
  · simp only [work, Cost.bind_val, Cost.pure_val]
    dsimp only [Prog]
    refine ⟨hs.1, ?_⟩
    intro _ s hn c hc
    obtain ⟨c', h1, h2, -⟩ := hleaf s c hc
    rw [hn]
    erw [h1]
    rw [← h2]
    exact hcov c'
  · exact hs

theorem prog_work_copy (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (i : Nat) (g : GoalOf R Rel) (isCall : Bool)
    (subs : List (Nat × Nat)) (ho : Open st i) (hs : Prog st i g (.copy isCall subs)) :
    Prog (work (K := DerivationKernel.over D K hK P) i g st (.copy isCall subs)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) i g st (.copy isCall subs)).val.2.1 := by
  have hcf := fun m st' as ho happ =>
    copyFrom_cov (K := K) (hK := hK) hL i g isCall m st' as ho happ
  have hs0 := hs
  dsimp only [Prog] at hs
  obtain ⟨h0, h1, h2, h3⟩ := hs
  have happ : ∀ p ∈ subs.zipIdx, ∀ a ∈ st.answers p.1.1, ∃ c,
      (if isCall then Ans.unfold D P a g.node else Ans.inj D P a g.node p.2).val = some c ∧
        c.span = a.span := by
    intro p hp a ha
    obtain ⟨x, hx, hgx, -⟩ := h3 p.2 p.1.1 p.1.2 (List.mem_zipIdx_iff_getElem?.1 hp)
    exact copy_ok hx (hI.answers hgx a ha)
  at_cost K hK
  simp only [work]
  split
  · exact hs0
  · next p hp =>
    simp only [Cost.bind_val, Cost.pure_val]
    rw [prog_stamp]
    have hpm := mem_of_leastBy hp
    have hpok : p.1.2 < (st.answers p.1.1).length := by simpa using leastBy_ok hp
    obtain ⟨hf, hc⟩ := hcf p.2 st (((st.answers p.1.1).drop p.1.2).take 1) ho
      (fun a ha => happ p hpm a (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
    have hS := hf.stable ho
    dsimp only [Prog]
    refine ⟨h0, h1, by rw [List.length_modify]; exact h2, fun m j pos hm => ?_⟩
    rw [List.getElem?_modify] at hm
    have hq0 : subs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hpm
    by_cases e : p.2 = m
    · subst e
      rw [hq0] at hm
      simp only [ite_true] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨x, hx, hgx, hr⟩ := h3 p.2 p.1.1 p.1.2 hq0
      refine ⟨x, hx, hS.ext _ _ hgx,
        Nat.succ_le_of_lt (lt_of_lt_of_le hpok (hS.length_le _)), fun n y hn hy z hz => ?_⟩
      cases hz
      by_cases hlt : n < p.1.2
      · exact (hr.mono hS).2 n y hlt hy _ rfl
      · obtain rfl : n = p.1.2 := by omega
        have hy' := hS.getElem?_old hy hpok
        refine hc y (List.mem_iff_getElem?.2 ⟨0, ?_⟩)
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
        exact hy'
    · simp only [e, ite_false] at hm
      rw [id_map'] at hm
      obtain ⟨x, hx, hgx, hr⟩ := h3 m j pos hm
      exact ⟨x, hx, hS.ext _ _ hgx, hr.mono hS⟩

theorem prog_work_join (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (i : Nat) (g : GoalOf R Rel) (k : Kind) (a b : Nat)
    (c : Cursor) (ho : Open st i) (hs : Prog st i g (.join k a b c)) :
    Prog (work (K := DerivationKernel.over D K hK P) i g st (.join k a b c)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) i g st (.join k a b c)).val.2.1 := by
  have hs0 := hs
  dsimp only [Prog] at hs
  obtain ⟨L, Rg, h1, h2, h3, h4, h5⟩ := hs
  have hjp := fun ps => joinPairs_cov (K := K) (hK := hK) hL i k (st.answers a) (st.answers b)
    st ps ho h1 (hI.answers h2) (hI.answers h3)
  have fin : ∀ (ps : List (Nat × Nat)) (c' : Cursor) (st' : StateOf R Rel (Ans D P)),
      Frame i st st' →
      (∀ p ∈ ps, ∀ (x y : Ans D P), (st.answers a)[p.1]? = some x →
        (st.answers b)[p.2]? = some y → ∀ z, opS D k x.span y.span = some z → CovS st' i z) →
      c'.Ok (st.answers a).length (st.answers b).length →
      (∀ p q, c'.Before p q → c.Before p q ∨ (p, q) ∈ ps) →
      Prog st' i g (.join k a b c') := by
    intro ps c' st' hf hc hok hbef
    have hS := hf.stable ho
    dsimp only [Prog]
    refine ⟨L, Rg, h1, hS.ext _ _ h2, hS.ext _ _ h3,
      hok.mono (hS.length_le a) (hS.length_le b), fun p q x y hb hx hy z hz => ?_⟩
    have hlt := hok.before_lt hb
    have hx' := hS.getElem?_old hx hlt.1
    have hy' := hS.getElem?_old hy hlt.2
    rcases hbef p q hb with hb' | hb'
    · exact (h5 p q x y hb' hx' hy' z hz).mono hS
    · exact hc (p, q) hb' x y hx' hy' z hz
  at_cost K hK
  simp only [work]
  have ela : (st.pathsAt a).length = (st.answers a).length := pathsAt_length st a
  have elb : (st.pathsAt b).length = (st.answers b).length := pathsAt_length st b
  split
  · exact hs0
  · next pr hn =>
    simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
    rw [prog_stamp]
    obtain ⟨-, -, n3, -⟩ := Cursor.next_spec
      ((joinPairs (K := DerivationKernel.over D _ hK P) i k (st.answers a) (st.answers b) st
        [pr]).ticks + 1) (by rw [ela, elb]; exact h4) hn
    rw [ela, elb] at n3
    obtain ⟨hf, hc⟩ := hjp [pr]
    exact fin [pr] _ _ hf hc n3 (fun p q hb => by
      rcases Cursor.before_mark.1 hb with h | h
      · exact .inl h
      · exact .inr (h ▸ List.mem_cons_self))

theorem prog_work_push (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (i : Nat) (g : GoalOf R Rel) (k : Kind) (left : Bool)
    (side : Nat) (other : Rel) (todo : Option (List (Ans D P)))
    (subs : List (Ans D P × Nat × Nat)) (ho : Open st i) (hno : Normal other)
    (hs : Prog st i g (.push k left side other todo subs)) :
    Prog (work (K := DerivationKernel.over D K hK P) i g st
        (.push k left side other todo subs)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) i g st
        (.push k left side other todo subs)).val.2.1 := by
  have hs0 := hs
  dsimp only [Prog] at hs
  obtain ⟨L, Rg, h1, h2, h3, h4, h5, h6⟩ := hs
  have hpo := fun xs => pushOpen_spec (K := K) (hK := hK) (P := P) g other k left st xs
  have hpi := fun xs =>
    (inner_pushOpen (K := K) (hK := hK) (P := P) (w := i) g other k left st xs).frame
  have hpI := fun xs => (inv_pushOpen (K := K) (hK := hK) hI g other k left xs hno).1
  have hpt := fun (x : Ans D P) st' ys ho' hx hy =>
    pushTake_cov (K := K) (hK := hK) hL i k left x st' ys ho' (other := other) h1 hx hy
  have hmv := maxima_val (P := P) K hK (st.answers side)
  have hmm : ∀ x ∈ (maxima (K := DerivationKernel.over D K hK P) (st.answers side)).val,
      x ∈ st.answers side := fun x h => mem_maxima (K := K) (hK := hK) h
  have hcovmax : ∀ x ∈ st.answers side,
      ∃ x' ∈ (maxima (K := DerivationKernel.over D K hK P) (st.answers side)).val,
        den P.sorts.interp x.span ⊆ den P.sorts.interp x'.span := by
    intro x hx
    rw [hmv]
    obtain ⟨z, hz, hc⟩ := List.maximaBy_covers (cov := covB D P)
      (fun a => (hL.covers_iff _ _).2 subset_rfl)
      (fun a b c h1 h2 => (hL.covers_iff _ _).2
        (((hL.covers_iff _ _).1 h2).trans ((hL.covers_iff _ _).1 h1))) hx
    exact ⟨z, hz, (hL.covers_iff _ _).1 hc⟩
  at_cost K hK
  simp only [work]
  split
  · exact hs0
  · next hnd =>
    have hd : st.isDone side = true := by simpa using hnd
    split
    · simp only [Cost.bind_val, Cost.pure_val]
      dsimp only [Prog]
      exact ⟨L, Rg, h1, h2, h3, fun l hl => by
        cases hl
        exact ⟨hd, (fun x hx => by
            rcases hx with hx | hx
            · rw [hmv] at hx
              exact hx
            · rw [h6 rfl] at hx
              cases hx),
          fun x hx => (hcovmax x hx).imp fun x' h => ⟨hmm x' h.1, .inl h.1, h.2⟩⟩,
        h5, fun h => by cases h⟩
    · next x rest =>
      simp only [Cost.bind_val, Cost.pure_val]
      obtain ⟨hmap, hnew⟩ := hpo [x]
      have hF1 := hpi [x]
      have hS1 := hF1.stable ho
      obtain ⟨hd', hans⟩ := hS1.isDone hd
      obtain ⟨-, d2, d3⟩ := h4 (x :: rest) rfl
      dsimp only [Prog]
      refine ⟨L, Rg, h1, hS1.ext _ _ h2, h3, fun l hl => ?_, fun e he => ?_,
        fun h => by cases h⟩
      · cases hl
        rw [hans]
        refine ⟨hd', fun y hy => d2 y (by
          rcases hy with hy | hy
          · exact .inl (List.mem_cons_of_mem _ hy)
          · rw [List.map_append, hmap] at hy
            rcases List.mem_append.1 hy with h | h
            · exact .inr h
            · exact .inl (by rw [List.mem_singleton.1 h]; exact List.mem_cons_self)),
          fun y hy => ?_⟩
        obtain ⟨x', hx', hor, hsubset⟩ := d3 y hy
        refine ⟨x', hx', ?_, hsubset⟩
        rw [List.map_append, hmap]
        rcases hor with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inr (List.mem_append_right _ List.mem_cons_self)
          · exact .inl h
        · exact .inr (List.mem_append_left _ h)
      · rcases List.mem_append.1 he with he | he
        · obtain ⟨e1, e2, e3⟩ := h5 e he
          exact ⟨by rw [hans]; exact e1, hS1.ext _ _ e2, e3.mono hS1⟩
        · obtain ⟨e1, e2, e3⟩ := hnew e he
          refine ⟨?_, e3, by rw [e2]; exact Read.zero _ _ _ _⟩
          rw [hans]
          exact List.mem_maximaBy
            (d2 _ (.inl (by rw [List.mem_singleton.1 e1]; exact List.mem_cons_self)))
    · split
      · exact hs0
      · next p hp =>
        simp only [Cost.bind_val, Cost.pure_val]
        rw [prog_stamp]
        have hpm := mem_of_leastBy hp
        have hpok : p.1.2.2 < (st.answers p.1.2.1).length := by simpa using leastBy_ok hp
        have hq0 : subs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hpm
        obtain ⟨e1, e2, e3⟩ := h5 p.1 (List.mem_of_getElem? hq0)
        obtain ⟨hf, hc⟩ := hpt p.1.1 st (((st.answers p.1.2.1).drop p.1.2.2).take 1) ho
          (hI.answers h2 _ e1)
          (fun y hy => hI.answers e2 y (List.mem_of_mem_drop (List.mem_of_mem_take hy)))
        have hS := hf.stable ho
        obtain ⟨hd', hans⟩ := hS.isDone hd
        dsimp only [Prog]
        refine ⟨L, Rg, h1, hS.ext _ _ h2, h3, fun l hl => ?_, fun e he => ?_,
          fun h => by cases h⟩
        · obtain ⟨-, d2, d3⟩ := h4 l hl
          rw [hans, map_modify_eq (fun e : Ans D P × Nat × Nat => e.1)
            (fun e : Ans D P × Nat × Nat => (e.1, e.2.1, e.2.2 + 1)) (fun _ => rfl)]
          exact ⟨hd', d2, d3⟩
        · obtain ⟨n, hn⟩ := List.getElem?_of_mem he
          rw [List.getElem?_modify] at hn
          by_cases hpn : p.2 = n
          · subst hpn
            rw [hq0] at hn
            simp only [ite_true] at hn
            cases hn
            refine ⟨by rw [hans]; exact e1, hS.ext _ _ e2,
              Nat.succ_le_of_lt (lt_of_lt_of_le hpok (hS.length_le _)),
              fun n y hn hy z hz => ?_⟩
            by_cases hlt : n < p.1.2.2
            · exact (e3.mono hS).2 n y hlt hy z hz
            · have hn2 : n < p.1.2.2 + 1 := hn
              obtain rfl : n = p.1.2.2 := by omega
              have hy' := hS.getElem?_old hy hpok
              refine hc y (List.mem_iff_getElem?.2 ⟨0, ?_⟩) z hz
              rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
              exact hy'
          · simp only [hpn, ite_false] at hn
            rw [id_map'] at hn
            obtain ⟨d1, d2, d3⟩ := h5 e (List.mem_of_getElem? hn)
            exact ⟨by rw [hans]; exact d1, hS.ext _ _ d2, d3.mono hS⟩

theorem prog_work_check (hR : ReadOk D P K hK) {st : StateOf R Rel (Ans D P)}
    (hE : EdgesOk st) (i : Nat) (g : GoalOf R Rel) (left : Bool)
    (side other : Rel) (c : Check) (hs : Prog st i g (.check left side other c)) :
    Prog (work (K := DerivationKernel.over D K hK P) i g st
        (.check left side other c)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) i g st
        (.check left side other c)).val.2.1 := by
  have hs0 := hs
  dsimp only [Prog] at hs
  obtain ⟨L, Rg, h1, h2, h3, -⟩ := hs
  have hes := (edgeOf_spec hR hE left side).2.2.1
  have her := (edgeOf_spec hR hE left side).2.2.2
  have hco := fun st' ps => checkOpen_spec (K := K) (hK := hK) (P := P) g left other st' ps
  clear hR
  at_cost K hK
  cases c with
  | reading =>
    simp only [work, Cost.bind_val]
    split
    · dsimp only [Prog]
      exact ⟨L, Rg, h1, h2, h3, trivial⟩
    · next heq =>
      dsimp only [Prog]
      exact ⟨L, Rg, h1, h2, h3, her _ heq⟩
    · next ps heq =>
      simp only [Cost.bind_val, Cost.pure_val]
      obtain ⟨-, es, hes', hall⟩ := hco _ ps
      rw [List.nil_append] at hes'
      dsimp only [Prog]
      refine ⟨L, Rg, h1, h2, h3, ps, her _ heq, hes ps heq, by rw [hes']; exact hall.length_eq.symm,
        fun n p hp => ?_⟩
      rw [hes']
      exact forall₂_getElem? hall hp
  | off => exact hs0
  | opened subs => exact hs0

/-- **The work of a strategy keeps what its cursors mean.** -/
theorem prog_work (hL : D.Lawful P.sorts.interp) (hR : ReadOk D P K hK)
    {st : StateOf R Rel (Ans D P)} (hI : Inv st) (hE : EdgesOk st) (i : Nat)
    (g : GoalOf R Rel) (s : Strat Rel (Ans D P)) (ho : Open st i)
    (hb : IsBound D g.lb ∧ IsBound D g.rb) (hok : StratOk st g s) (hs : Prog st i g s) :
    Prog (work (K := DerivationKernel.over D K hK P) i g st s).val.1 i g
      (work (K := DerivationKernel.over D K hK P) i g st s).val.2.1 := by
  cases s with
  | span ran => exact prog_work_span hL i g ran ho hb hs
  | copy isCall subs => exact prog_work_copy hL hI i g isCall subs ho hs
  | join k a b c => exact prog_work_join hL hI i g k a b c ho hs
  | push k left side other todo subs =>
    obtain ⟨-, -, -, hno, -⟩ := hok
    exact prog_work_push hL hI i g k left side other todo subs ho hno hs
  | check left side other c => exact prog_work_check hR hE i g left side other c hs

end kernel

end Symmetric

end RwLog
