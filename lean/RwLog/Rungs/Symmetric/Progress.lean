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
* a push has seen the first answers of its side, in order, and covers what
  the rule makes of every pair its cursor has combined, of an answer of the
  side and an answer of the goal opened for it;
* an interface check that has opened goals has opened one for each
  interface its side can show.

`Prog` holds in every later state of the run (`Prog.mono`).
-/
import RwLog.Rungs.Symmetric.Rounds
import RwLog.Rungs.Framework.RaceSpec
import RwLog.Rungs.Symmetric.PushCursor
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
  · simp only [e, ite_false]; cases st.tables[j]? <;> rfl

@[simp] theorem isDone_stamp (st : StateOf S N A) (i n : Nat) (pth : Path) (j : Nat) :
    (stamp i n pth st).isDone j = st.isDone j := by
  unfold stamp StateOf.isDone StateOf.modify
  simp only [List.getElem?_modify]
  by_cases e : i = j
  · subst e; cases st.tables[i]? <;> simp
  · simp only [e, ite_false]; cases st.tables[j]? <;> rfl

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
  | .push k l side o _ _ _ _ _ => .push k l side o [] none [] Cursor.start Cursor.start
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
    (h : s.kind = .push k l side o [] none [] Cursor.start Cursor.start) :
    ∃ subs dead reads c fc, s = .push k l side o subs dead reads c fc := by
  cases s <;> simp only [Strat.kind, reduceCtorEq, Strat.push.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
  exact ⟨_, _, _, _, _, rfl⟩

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

/-- The positions `dead` are those of the first `n` answers of `xs` that a
later one of them covers. -/
def DeadOk (D : Domain R) (P : Program) (xs : List (Ans D P)) (n : Nat) (dead : List Nat) :
    Prop :=
  (∀ s ∈ dead, ∃ j x y, s < j ∧ j < n ∧ xs[s]? = some x ∧ xs[j]? = some y ∧
    covB D P y x = true) ∧
  ∀ s j x y, s < j → j < n → xs[s]? = some x → xs[j]? = some y → s ∉ dead →
    covB D P y x = false

/-- What a push knows of the answers of its side that are superseded: nothing
until the side is complete; from then on the side is complete, the push has
seen all `n` answers of it, and the positions are those a later one covers. -/
def DeadIs (D : Domain R) (P : Program) (st : StateOf R Rel (Ans D P)) (side n : Nat) :
    Option (List Nat) → Prop
  | none => True
  | some d => st.isDone side = true ∧ n = (st.answers side).length ∧
      DeadOk D P (st.answers side) (st.answers side).length d

omit [DecidableEq R] in
theorem DeadIs.mono {st st' : StateOf R Rel (Ans D P)} (h : Stable st st') {side n : Nat}
    {dead : Option (List Nat)} (hd : DeadIs D P st side n dead) : DeadIs D P st' side n dead := by
  cases dead with
  | none => exact True.intro
  | some d =>
    obtain ⟨h1, h2, h3⟩ := hd
    have e := (h.isDone h1).2
    exact ⟨(h.isDone h1).1, by rw [e]; exact h2, by rw [e]; exact h3⟩

omit [DecidableEq R] in
/-- The positions superseded are positions of answers seen. -/
theorem DeadIs.lt {st : StateOf R Rel (Ans D P)} {side n : Nat} {dead : Option (List Nat)}
    (hd : DeadIs D P st side n dead) : ∀ s ∈ dead.getD [], s < n := by
  cases dead with
  | none => exact fun s hs => by cases hs
  | some d =>
    obtain ⟨-, h2, h3⟩ := hd
    intro s hs
    obtain ⟨j, _, _, hj, hjn, -⟩ := h3.1 s hs
    omega

omit [DecidableEq R] in
/-- **Every answer is covered by one that is not superseded**, once all are
seen. -/
theorem DeadOk.live (hL : D.Lawful P.sorts.interp) {xs : List (Ans D P)} {dead : List Nat}
    (h : DeadOk D P xs xs.length dead) (n : Nat) (x : Ans D P) (hx : xs[n]? = some x) :
    ∃ (n' : Nat) (x' : Ans D P), n' ∉ dead ∧ xs[n']? = some x' ∧ covB D P x' x = true := by
  have main : ∀ (d n : Nat) (x : Ans D P), xs.length - n ≤ d → xs[n]? = some x →
      ∃ (n' : Nat) (x' : Ans D P), n' ∉ dead ∧ xs[n']? = some x' ∧ covB D P x' x = true := by
    intro d
    induction d with
    | zero =>
      intro n x hd hx
      have := (List.getElem?_eq_some_iff.1 hx).1
      omega
    | succ d ih =>
      intro n x hd hx
      by_cases hn : n ∈ dead
      · obtain ⟨j, x1, y, hj, hjn, hx1, hy, hc⟩ := h.1 n hn
        rw [hx] at hx1
        cases hx1
        obtain ⟨n', x', h1, h2, h3⟩ := ih j y (by omega) hy
        exact ⟨n', x', h1, h2, covB_trans hL _ _ _ h3 hc⟩
      · exact ⟨n, x, hn, hx, covB_refl hL x⟩
  exact main _ n x (Nat.le_refl _) hx

omit [DecidableEq R] in
theorem DeadOk.mono {xs xs' : List (Ans D P)} {n : Nat} {dead : List Nat}
    (h : DeadOk D P xs n dead) (hp : xs <+: xs') (hn : n ≤ xs.length) :
    DeadOk D P xs' n dead := by
  obtain ⟨tl, rfl⟩ := hp
  refine ⟨fun s hs => ?_, fun s j x y hsj hj hx hy hd => ?_⟩
  · obtain ⟨j, x, y, h1, h2, h3, h4, h5⟩ := h.1 s hs
    exact ⟨j, x, y, h1, h2, by rw [List.getElem?_append_left (by omega)]; exact h3,
      by rw [List.getElem?_append_left (by omega)]; exact h4, h5⟩
  · rw [List.getElem?_append_left (by omega)] at hx hy
    exact h.2 s j x y hsj hj hx hy hd

omit [DecidableEq R] in
theorem DeadOk.nil (xs : List (Ans D P)) : DeadOk D P xs 0 [] :=
  ⟨fun _ hs => (by cases hs), fun _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _)⟩

omit [DecidableEq R] in
theorem DeadOk.lt {xs : List (Ans D P)} {n : Nat} {dead : List Nat}
    (h : DeadOk D P xs n dead) : ∀ s ∈ dead, s < n := fun s hs => by
  obtain ⟨j, -, -, h1, h2, -⟩ := h.1 s hs
  omega

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
  | .push k left side other subs dead reads c _ => ∃ L Rg, SplitAt g k L Rg ∧
      goalAt st side = some (if left then L else Rg) ∧
      other = (if left then Rg.node else L.node) ∧
      subs.map (·.1) = (st.answers side).take subs.length ∧
      DeadIs D P st side subs.length dead ∧
      (∀ e ∈ subs, ∀ t, e.2 = some t →
        goalAt st t.1 = some (pushG D g other k left e.1) ∧ t.2 ≤ (st.answers t.1).length) ∧
      PushFits subs (dead.getD []) reads c ∧
      ∀ (s q : Nat) (x : Ans D P) (t : Nat × Nat) (r : Nat) (y : Ans D P), c.Before s q →
        subs[s]? = some (x, some t) → reads[q]? = some (s, some r) →
        (st.answers t.1)[r]? = some y →
        ∀ z, pushedS D k left x.span y.span = some z → CovS st i z
  | .check left side other c => ∃ L Rg, SplitAt g .seq L Rg ∧
      side = (if left then L.node else Rg.node) ∧ other = (if left then Rg.node else L.node) ∧
      match c with
      | .opened subs => ∃ ps, Reads D P side left (some ps) ∧ EdgeOk D P side left ps ∧
          subs.length = ps.length ∧
          ∀ (n : Nat) (p : R), ps[n]? = some p → ∃ j, subs[n]? = some j ∧
            goalAt st j = some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩)
      | .off => Reads D P side left none
      | .reading => True

/-- The first entries of a list are the first entries of a list it begins. -/
theorem take_of_prefix {α : Type} {l l' : List α} (h : l <+: l') {n : Nat} (hn : n ≤ l.length) :
    l'.take n = l.take n := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append_of_le_length hn]

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
  | push k left side other subs dead reads c fc =>
    dsimp only [Prog] at hs ⊢
    obtain ⟨L, Rg, h1, h2, h3, h4, hD, h5, h6, h7⟩ := hs
    have hlen : subs.length ≤ (st.answers side).length := by
      have := congrArg List.length h4
      simp only [List.length_map, List.length_take] at this
      omega
    refine ⟨L, Rg, h1, hE _ _ h2, h3, ?_, hD.mono h,
      fun e he t ht => ?_, h6, fun s q x t r y hb he hq hy z hz => ?_⟩
    · rw [h4]
      exact (take_of_prefix (h.answers side) hlen).symm
    · exact ⟨hE _ _ (h5 e he t ht).1, (h5 e he t ht).2.trans (h.length_le _)⟩
    · have hr : r < t.2 := by
        have := h6.2.filed q s r hq
        unfold cntOf at this
        rw [he] at this
        exact this
      exact (h7 s q x t r y hb he hq (h.getElem?_old hy
        (lt_of_lt_of_le hr (h5 _ (List.mem_of_getElem? he) t rfl).2)) z hz).mono h
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
    .push k true a Rg.node [] none [] Cursor.start Cursor.start ∈ gr.kinds ∧
      .push k false b L.node [] none [] Cursor.start Cursor.start ∈ gr.kinds
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
      .push k true a Rg.node [] none [] Cursor.start Cursor.start ∈ gr.kinds ∧
      .push k false b L.node [] none [] Cursor.start Cursor.start ∈ gr.kinds)
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

omit [DecidableEq R] in
theorem deadIs_stamp (st : StateOf R Rel (Ans D P)) (j n : Nat) (pth : Path) (side m : Nat)
    (dead : Option (List Nat)) :
    DeadIs D P (stamp j n pth st) side m dead = DeadIs D P st side m dead := by
  cases dead <;> simp only [DeadIs, answers_stamp, isDone_stamp]

/-- Giving paths to answers changes nothing `Prog` speaks of. -/
theorem prog_stamp (st : StateOf R Rel (Ans D P)) (j n : Nat) (pth : Path) (i : Nat)
    (g : GoalOf R Rel) (s : Strat Rel (Ans D P)) :
    Prog (stamp j n pth st) i g s = Prog st i g s := by
  cases s <;> simp only [Prog, CovS, Read, answers_stamp, goalAt_stamp, deadIs_stamp]

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
  have hsee := h4.see (pathsAt_length st a) (pathsAt_length st b)
  split
  · exact fin [] _ _ (Frame.refl i st) (fun _ hp => by cases hp) hsee.1
      fun p q hb => .inl hb
  · next pr hn =>
    simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
    rw [prog_stamp]
    obtain ⟨-, -, n3, -⟩ := Cursor.next_spec
      ((joinPairs (K := DerivationKernel.over D _ hK P) i k (st.answers a) (st.answers b) st
        [pr]).ticks + 1) hsee.1 hn
    obtain ⟨hf, hc⟩ := hjp [pr]
    exact fin [pr] _ _ hf hc n3 (fun p q hb => by
      rcases Cursor.before_mark.1 hb with h | h
      · exact .inl h
      · exact .inr (h ▸ List.mem_cons_self))

/-- One answer more seen: it supersedes the answers seen that it covers. -/
theorem supersede_cons (y : Ans D P) (rest seen : List (Ans D P)) (dead : List Nat) :
    (supersede (K := DerivationKernel.over D K hK P) (y :: rest) seen dead).val =
      (supersede (K := DerivationKernel.over D K hK P) rest (seen ++ [y])
        (dead ++ (seen.zipIdx.filter fun e => !dead.contains e.2 && covB D P y e.1).map
          (·.2))).val := by
  have hc := coversA_val (P := P) K hK
  at_cost K hK
  simp only [supersede, Cost.bind_val, filterL_std, Cost.filterL_val]
  congr 5
  funext e
  simp [hc]

/-- With no answer more to see, the answers superseded are the same. -/
theorem supersede_nil (seen : List (Ans D P)) (dead : List Nat) :
    (supersede (K := DerivationKernel.over D K hK P) [] seen dead).val = dead := by
  at_cost K hK
  rfl

/-- **The answers superseded are those a later answer seen covers**, once
the answers the side has gained are seen. -/
theorem supersede_ok : ∀ (new seen : List (Ans D P)) (dead : List Nat),
    DeadOk D P (seen ++ new) seen.length dead →
    DeadOk D P (seen ++ new) (seen ++ new).length
        (supersede (K := DerivationKernel.over D K hK P) new seen dead).val ∧
      ∀ s ∈ dead, s ∈ (supersede (K := DerivationKernel.over D K hK P) new seen dead).val
  | [], seen, dead, h => by
    have e : (supersede (K := DerivationKernel.over D K hK P) [] seen dead).val = dead := by
      at_cost K hK
      rfl
    rw [e]
    exact ⟨by simpa using h, fun _ hs => hs⟩
  | y :: rest, seen, dead, h => by
    rw [supersede_cons]
    have e : seen ++ y :: rest = (seen ++ [y]) ++ rest := by simp
    have hd' : DeadOk D P ((seen ++ [y]) ++ rest) (seen ++ [y]).length
        (dead ++ (seen.zipIdx.filter fun e => !dead.contains e.2 && covB D P y e.1).map
          (·.2)) := by
      rw [← e, List.length_append, List.length_singleton]
      refine ⟨fun s hs => ?_, fun s j x y' hsj hj hx hy hnd => ?_⟩
      · rcases List.mem_append.1 hs with hs | hs
        · obtain ⟨j, x, y', h1, h2, h3⟩ := h.1 s hs
          exact ⟨j, x, y', h1, by omega, h3⟩
        · obtain ⟨e', he', rfl⟩ := List.mem_map.1 hs
          obtain ⟨hm, hf⟩ := List.mem_filter.1 he'
          have hg : seen[e'.2]? = some e'.1 := List.mk_mem_zipIdx_iff_getElem?.1 hm
          have hlt := (List.getElem?_eq_some_iff.1 hg).1
          simp only [Bool.and_eq_true] at hf
          exact ⟨seen.length, e'.1, y, hlt, by omega,
            by rw [List.getElem?_append_left hlt]; exact hg, by simp, hf.2⟩
      · rw [List.mem_append, not_or] at hnd
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
        · exact h.2 s j x y' hsj hj' hx hy hnd.1
        · simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, Option.some.injEq] at hy
          subst hy
          rw [List.getElem?_append_left hsj] at hx
          cases hcv : covB D P y x with
          | false => rfl
          | true =>
            exfalso
            refine hnd.2 (List.mem_map.2 ⟨(x, s), List.mem_filter.2
              ⟨List.mk_mem_zipIdx_iff_getElem?.2 hx, ?_⟩, rfl⟩)
            simp [hcv, hnd.1]
    obtain ⟨a, b⟩ := supersede_ok rest (seen ++ [y]) _ hd'
    rw [e]
    exact ⟨a, fun s hs => b s (List.mem_append_left _ hs)⟩

/-- The first components of two lists zipped, from a position on. -/
theorem map_fst_zip_drop {α β : Type} (l : List α) (l' : List β) (h : l'.length = l.length)
    (n : Nat) : ((l.zip l').drop n).map Prod.fst = l.drop n := by
  rw [List.map_drop, List.map_fst_zip (by omega)]

/-- **The answers superseded are found once the side is complete, and
kept.** -/
theorem superseded_spec (st : StateOf R Rel (Ans D P)) (side : Nat) (dead : Option (List Nat)) :
    (∀ d, dead = some d →
      (superseded (K := DerivationKernel.over D K hK P) st side dead).val = some d) ∧
    (∀ d, (superseded (K := DerivationKernel.over D K hK P) st side dead).val = some d →
      dead = some d ∨ (dead = none ∧ st.isDone side = true ∧
        DeadOk D P (st.answers side) (st.answers side).length d)) ∧
    (st.isDone side = true →
      (superseded (K := DerivationKernel.over D K hK P) st side dead).val.isSome = true) := by
  cases dead with
  | some d0 =>
    have e : (superseded (K := DerivationKernel.over D K hK P) st side (some d0)).val =
        some d0 := by
      at_cost K hK
      rfl
    rw [e]
    exact ⟨fun d h => h, fun d h => .inl h, fun _ => rfl⟩
  | none =>
    by_cases hd : st.isDone side = true
    · have e : (superseded (K := DerivationKernel.over D K hK P) st side none).val =
          some (supersede (K := DerivationKernel.over D K hK P) (st.answers side) [] []).val := by
        at_cost K hK
        simp only [superseded, hd, ↓reduceIte, Cost.bind_val, Cost.pure_val]
      rw [e]
      refine ⟨fun d h => (by cases h), fun d h => .inr ⟨rfl, hd, ?_⟩, fun _ => rfl⟩
      cases h
      have := (supersede_ok (K := K) (hK := hK) (P := P) (st.answers side) [] []
        (by simpa using DeadOk.nil _)).1
      simpa using this
    · have e : (superseded (K := DerivationKernel.over D K hK P) st side none).val = none := by
        at_cost K hK
        simp only [superseded, hd, Bool.false_eq_true, ↓reduceIte, Cost.pure_val]
      rw [e]
      exact ⟨fun d h => (by cases h), fun d h => (by cases h), fun h => absurd h hd⟩

/-- What the cursors of a push mean stays so when it sees what its side has
gained, drops the answers superseded, and files what its tables have
gained. -/
theorem prog_push_file {st : StateOf R Rel (Ans D P)} (i : Nat) (g : GoalOf R Rel) (k : Kind)
    (left : Bool) (side : Nat) (other : Rel) (subs : List (Ans D P × Option (Nat × Nat)))
    (dead : Option (List Nat)) (reads : List (Nat × Option Nat)) (c : Cursor) (fc : Cursor)
    (dead' : Option (List Nat))
    (hD' : ∀ d, dead' = some d → st.isDone side = true ∧
      DeadOk D P (st.answers side) (st.answers side).length d)
    (hdsub : ∀ d, dead = some d → dead' = some d)
    (hs : Prog st i g (.push k left side other subs dead reads c fc)) :
    Prog st i g (.push k left side other
      (pushFile st (dead'.getD []) 0
        (seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).2.1
        ((seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).2.2.kill
          (dead'.getD []))
        (seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).1).1
      dead'
      (pushFile st (dead'.getD []) 0
        (seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).2.1
        ((seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).2.2.kill
          (dead'.getD []))
        (seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).1).2.1
      (pushFile st (dead'.getD []) 0
        (seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).2.1
        ((seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).2.2.kill
          (dead'.getD []))
        (seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs reads c).1).2.2
      fc) := by
  have hss0 := seeSide_subs (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
    reads c
  have hsd0 := seeSide_done (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
    reads c
  have hsp0 := seeSide_prefix (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
    reads c
  have hsf0 := fun h hd => PushFits.seeSide (dead := dead.getD [])
    (((st.answers side).zip (st.pathsAt side)).drop subs.length) (subs := subs) (reads := reads)
    (c := c) h hd
  generalize seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
    reads c = f0 at hss0 hsd0 hsp0 hsf0 ⊢
  have hfe0 := pushFile_getElem? st (dead'.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead'.getD []))
  have hflen0 := pushFile_length st (dead'.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead'.getD []))
  have hfd0 : (pushFile st (dead'.getD []) 0 f0.2.1 (f0.2.2.kill (dead'.getD [])) f0.1).2.2.done = f0.2.2.done :=
    pushFile_done st (dead'.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead'.getD []))
  have hfp0 := pushFile_prefix st (dead'.getD []) f0.1 0 f0.2.1 (f0.2.2.kill (dead'.getD []))
  have hff0 := fun h hle => PushFits.file (subs := f0.1) (dead := dead'.getD []) (reads := f0.2.1)
    (c := f0.2.2.kill (dead'.getD [])) h st hle
  generalize hfdef : pushFile st (dead'.getD []) 0 f0.2.1 (f0.2.2.kill (dead'.getD [])) f0.1 = f
  rw [hfdef] at hfe0 hflen0 hfd0 hfp0 hff0
  dsimp only [Prog] at hs ⊢
  obtain ⟨L, Rg, h1, h2, h3, h4, hD, h5, h6, h7⟩ := hs
  have hlen : subs.length ≤ (st.answers side).length := by
    have := congrArg List.length h4
    simp only [List.length_map, List.length_take] at this
    omega
  have hss := hss0
  have hfe := hfe0
  have hflen := hflen0
  have hdone : f.2.2.done = c.done := hfd0.trans hsd0
  have hpre : reads <+: f.2.1 := hsp0.trans hfp0
  have h50 : ∀ e ∈ f0.1, ∀ t, e.2 = some t →
      goalAt st t.1 = some (pushG D g other k left e.1) ∧ t.2 ≤ (st.answers t.1).length := by
    intro e he t ht
    rw [hss] at he
    rcases List.mem_append.1 he with he | he
    · exact h5 e he t ht
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 he
      cases ht
  have hsub0 : ∀ s ∈ dead.getD [], s ∈ dead'.getD [] := by
    cases dead with
    | none => exact fun s hs => by cases hs
    | some d =>
      rw [hdsub d rfl]
      exact fun s hs => hs
  have hfit : PushFits f.1 (dead'.getD []) f.2.1 f.2.2 :=
    hff0 ((hsf0 h6 hD.lt).kill (dead'.getD []) hsub0) fun e he t ht => by
      rw [pathsAt_length]; exact (h50 e he t ht).2
  have hsub : ∀ (s : Nat) (x : Ans D P) (t : Nat × Nat), f.1[s]? = some (x, some t) →
      ∃ t0, subs[s]? = some (x, some t0) ∧ t.1 = t0.1 ∧ t.2 ≤ (st.answers t0.1).length := by
    intro s x t he
    rw [hfe] at he
    cases h0 : f0.1[s]? with
    | none => rw [h0] at he; cases he
    | some e0 =>
      rw [h0] at he
      rcases e0 with ⟨x0, _ | t0⟩
      · cases he
      · cases he
        have h00 := h0
        rw [hss] at h0
        rcases Nat.lt_or_ge s subs.length with hl | hl
        · rw [List.getElem?_append_left hl] at h0
          refine ⟨t0, h0, rfl, ?_⟩
          dsimp only
          split
          · exact (h5 _ (List.mem_of_getElem? h0) t0 rfl).2
          · rw [pathsAt_length]
        · rw [List.getElem?_append_right hl, List.getElem?_map] at h0
          cases hh : (((st.answers side).zip (st.pathsAt side)).drop subs.length)[s -
            subs.length]? with
          | none => rw [hh] at h0; cases h0
          | some y => rw [hh] at h0; cases h0
  have hfl : f.1.length = (st.answers side).length := by
    rw [hflen, hss, List.length_append, List.length_map, List.length_drop, List.length_zip,
      pathsAt_length, Nat.min_self]
    omega
  have hDn : DeadIs D P st side f.1.length dead' := by
    cases dead' with
    | none => exact True.intro
    | some d => exact ⟨(hD' d rfl).1, hfl, (hD' d rfl).2⟩
  refine ⟨L, Rg, h1, h2, h3, ?_, hDn, fun e he t ht => ?_, hfit,
    fun s q x t r y hb he hq hy z hz => ?_⟩
  · have hm : f.1.map (·.1) = f0.1.map (·.1) := by
      refine List.ext_getElem? fun n => ?_
      rw [List.getElem?_map, List.getElem?_map, hfe]
      cases f0.1[n]? <;> rfl
    rw [hm, hflen, hss, List.map_append, List.map_map, h4, List.length_append, List.length_map,
      List.length_drop, List.length_zip, pathsAt_length, Nat.min_self,
      show subs.length + ((st.answers side).length - subs.length) = (st.answers side).length by
        omega, List.take_length]
    have := map_fst_zip_drop (st.answers side) (st.pathsAt side) (pathsAt_length _ _) subs.length
    rw [show (List.map ((fun x => x.1) ∘ fun x => (x.1, (none : Option (Nat × Nat))))
      (List.drop subs.length ((st.answers side).zip (st.pathsAt side)))) =
        List.map Prod.fst (List.drop subs.length ((st.answers side).zip (st.pathsAt side)))
      from rfl, this, List.take_append_drop]
  · obtain ⟨s, hs⟩ := List.getElem?_of_mem he
    rcases e with ⟨x, o⟩
    cases ht
    obtain ⟨t0, he0, e1, e2⟩ := hsub s x t hs
    rw [e1]
    exact ⟨(h5 _ (List.mem_of_getElem? he0) t0 rfl).1, e2⟩
  · have hb' : c.Before s q := by
      unfold Cursor.Before at hb ⊢
      rw [hdone] at hb
      exact hb
    obtain ⟨r', hr'⟩ := h6.2.done _ hb'
    obtain ⟨tl, htl⟩ := hpre
    have hq' : reads[q]? = some (s, some r) := by
      rw [← htl, List.getElem?_append_left (lt_of_getElem? hr')] at hq
      exact hq
    obtain ⟨t0, he0, e1, -⟩ := hsub s x t he
    rw [e1] at hy
    exact h7 s q x t0 r y hb' he0 hq' hy z hz

theorem prog_work_push (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (i : Nat) (g : GoalOf R Rel) (k : Kind) (left : Bool)
    (side : Nat) (other : Rel) (subs : List (Ans D P × Option (Nat × Nat)))
    (dead : Option (List Nat))
    (reads : List (Nat × Option Nat)) (c : Cursor) (fc : Cursor) (ho : Open st i)
    (hs : Prog st i g (.push k left side other subs dead reads c fc)) :
    Prog (work (K := DerivationKernel.over D K hK P) i g st
        (.push k left side other subs dead reads c fc)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) i g st
        (.push k left side other subs dead reads c fc)).val.2.1 := by
  have hsup := superseded_spec (K := K) (hK := hK) (P := P) st side dead
  have hD0 : DeadIs D P st side subs.length dead := by
    have hs' := hs
    dsimp only [Prog] at hs'
    obtain ⟨_, _, -, -, -, -, hD, -⟩ := hs'
    exact hD
  have hP := fun dead' (h1 : ∀ d, dead' = some d → st.isDone side = true ∧
      DeadOk D P (st.answers side) (st.answers side).length d)
      (h2 : ∀ d, dead = some d → dead' = some d) =>
    prog_push_file i g k left side other subs dead reads c fc dead' h1 h2 hs
  have hpo := fun xs => pushOpen_spec (K := K) (hK := hK) (P := P) g other k left st xs
  have hpi := fun xs =>
    (inner_pushOpen (K := K) (hK := hK) (P := P) (w := i) g other k left st xs).frame
  have hpt := fun (x : Ans D P) st' ys ho' L Rg (h1 : SplitAt g k L Rg) hx hy =>
    pushTake_cov (K := K) (hK := hK) hL i k left x st' ys ho' (other := other) h1 hx hy
  at_cost K hK
  simp only [work, Cost.bind_val]
  generalize (superseded (K := DerivationKernel.over D _ hK P) st side dead).val = dead'
    at hsup ⊢
  replace hP := hP dead' (fun d hd => by
    rcases hsup.2.1 d hd with h | ⟨-, h1, h2⟩
    · subst h
      exact ⟨hD0.1, hD0.2.2⟩
    · exact ⟨h1, h2⟩) hsup.1
  generalize seeSide (((st.answers side).zip (st.pathsAt side)).drop subs.length) subs
    reads c = f0 at hP ⊢
  generalize pushFile st (dead'.getD []) 0 f0.2.1 (f0.2.2.kill (dead'.getD [])) f0.1 = f
    at hP ⊢
  obtain ⟨subs', reads', c'⟩ := f
  dsimp only at hP ⊢
  have hP0 := hP
  dsimp only [Prog] at hP
  obtain ⟨L, Rg, h1, h2, h3, h4, hD, h5, hfit, h7⟩ := hP
  have hlen : subs'.length ≤ (st.answers side).length := by
    have := congrArg List.length h4
    simp only [List.length_map, List.length_take] at this
    omega
  split
  · exact hP0
  · next p hp =>
    obtain ⟨hnb, -, hcase⟩ := hfit.next hp
    split
    · next x a hx hr =>
      have hr' : reads'[p.2]? = some (p.1, none) := by
        rcases hcase with ⟨x', -, h⟩ | ⟨x', t, r, hx', -⟩
        · exact h
        · rw [hx] at hx'
          cases hx'
      simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      obtain ⟨hmap, hnew⟩ := hpo [x]
      have hS1 := (hpi [x]).stable ho
      obtain ⟨e0, he0, hx0⟩ := List.map_eq_singleton_iff.1 hmap
      obtain ⟨-, e02, e03⟩ := hnew e0 (by rw [he0]; exact List.mem_cons_self)
      have hop : openedAt (pushOpen (K := DerivationKernel.over D _ hK P) g other k left st
          [x]).val.2 = some (e0.2.1, 0) := by
        rw [he0]; rfl
      rw [hop]
      rw [hx0] at e03
      have hfit' := fun t => hfit.markOpen hx hr' e0.2.1 t
      dsimp only [Prog]
      refine ⟨L, Rg, h1, hS1.ext _ _ h2, h3, ?_,
        by rw [List.length_set]; exact hD.mono hS1,
        fun e he t ht => ?_, hfit' _, fun s q x' t r y hb he hq hy z hz => ?_⟩
      · have hm : (subs'.set p.1 (x, some (e0.2.1, 0))).map (·.1) = subs'.map (·.1) := by
          refine List.ext_getElem? fun n => ?_
          rw [List.getElem?_map, List.getElem?_map]
          by_cases e : p.1 = n
          · subst e
            rw [List.getElem?_set_self (lt_of_getElem? hx), hx]
            rfl
          · rw [List.getElem?_set_ne e]
        rw [hm, List.length_set, h4]
        exact (take_of_prefix (hS1.answers side) hlen).symm
      · rcases List.mem_or_eq_of_mem_set he with he | rfl
        · exact ⟨hS1.ext _ _ (h5 e he t ht).1, (h5 e he t ht).2.trans (hS1.length_le _)⟩
        · cases ht
          exact ⟨e03, Nat.zero_le _⟩
      · have hr2 : r < t.2 := by
          have := (hfit' 0).2.filed q s r hq
          unfold cntOf at this
          rw [he] at this
          exact this
        by_cases e : p.1 = s
        · subst e
          rw [List.getElem?_set_self (lt_of_getElem? hx)] at he
          cases he
          exact absurd hr2 (Nat.not_lt_zero _)
        · rw [List.getElem?_set_ne e] at he
          have hy' := hS1.getElem?_old hy
            (lt_of_lt_of_le hr2 (h5 _ (List.mem_of_getElem? he) t rfl).2)
          rcases Cursor.before_mark.1 hb with hb | hb
          · exact (h7 s q x' t r y hb he hq hy' z hz).mono hS1
          · exact absurd (congrArg Prod.fst hb) e
    · next x tb a r hx hr =>
      obtain ⟨hr', hrlt⟩ : reads'[p.2]? = some (p.1, some r) ∧ r < tb.2 := by
        rcases hcase with ⟨x', hx', -⟩ | ⟨x', t, r', hx', h, hlt⟩
        · rw [hx] at hx'
          cases hx'
        · rw [hx] at hx'
          cases hx'
          rw [hr] at h
          cases h
          exact ⟨hr, hlt⟩
      simp only [Cost.bind_val, Cost.pure_val, Kernel.metered, Cost.metered_val]
      rw [prog_stamp]
      have hgo := h5 (x, some tb) (List.mem_of_getElem? hx) tb rfl
      have hxs : x ∈ st.answers side := by
        have : x ∈ subs'.map (·.1) := List.mem_map.2 ⟨_, List.mem_of_getElem? hx, rfl⟩
        rw [h4] at this
        exact List.mem_of_mem_take this
      obtain ⟨hf, hc⟩ := hpt x st (((st.answers tb.1).drop r).take 1) ho L Rg h1
        (hI.answers h2 _ hxs)
        (fun y hy => hI.answers hgo.1 y (List.mem_of_mem_drop (List.mem_of_mem_take hy)))
      have hS := hf.stable ho
      dsimp only [Prog]
      refine ⟨L, Rg, h1, hS.ext _ _ h2, h3, ?_, hD.mono hS,
        fun e he t ht => ?_, hfit.markRead hr' _, fun s q x' t r'' y hb he hq hy z hz => ?_⟩
      · rw [h4]
        exact (take_of_prefix (hS.answers side) hlen).symm
      · exact ⟨hS.ext _ _ (h5 e he t ht).1, (h5 e he t ht).2.trans (hS.length_le _)⟩
      · have hr2 : r'' < t.2 := by
          have := hfit.2.filed q s r'' hq
          unfold cntOf at this
          rw [he] at this
          exact this
        have hy' := hS.getElem?_old hy
          (lt_of_lt_of_le hr2 (h5 _ (List.mem_of_getElem? he) t rfl).2)
        rcases Cursor.before_mark.1 hb with hb | hb
        · exact (h7 s q x' t r'' y hb he hq hy' z hz).mono hS
        · cases hb
          rw [hx] at he
          rw [hr'] at hq
          cases he
          cases hq
          refine hc y (List.mem_iff_getElem?.2 ⟨0, ?_⟩) z hz
          rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
          exact hy'
    · next hno1 hno2 =>
      rcases hcase with ⟨x', hx', h⟩ | ⟨x', t, r', hx', h, -⟩
      · exact absurd h (hno1 x' p.1 hx')
      · exact absurd h (hno2 x' t p.1 r' hx')

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
  | push k left side other subs dead reads c fc =>
    exact prog_work_push hL hI i g k left side other subs dead reads c fc ho hs
  | check left side other c => exact prog_work_check hR hE i g left side other c hs

end kernel

end Symmetric

end RwLog
