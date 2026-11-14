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
import RwLog.Rungs.Symmetric.Cursor
import RwLog.Kernel.NormalFormDepth

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
others. -/
def SplitAt (g : GoalOf R Rel) : Kind → GoalOf R Rel → GoalOf R Rel → Prop
  | .seq, L, Rg => ∃ (xs : List Rel) (i : Nat) (l r : Rel), g.node.view = .chain xs ∧ 0 < i ∧
      i < xs.length ∧ g.node.interval 0 i = some l ∧ g.node.interval i xs.length = some r ∧
      L = ⟨g.lb, l, none⟩ ∧ Rg = ⟨none, r, g.rb⟩
  | .and, L, Rg => ∃ (xs : List Rel) (i : Nat) (x r : Rel), g.node.view = .meet xs ∧
      xs[i]? = some x ∧ g.node.without i = some r ∧ L = ⟨g.lb, x, g.rb⟩ ∧ Rg = ⟨g.lb, r, g.rb⟩

/-- The nodes a call (`true`) or a union reads. -/
def copyMembers (P : Program) (n : Rel) : Bool → List Rel
  | true => (Charged.bodyOf P n).toList
  | false => n.unionParts

/-- Every answer of the node `n` ends (`last`) or begins inside one of the
interfaces `ps`, each of which is a boundary. -/
def EdgeOk (D : Domain R) (P : Program) (n : Rel) (last : Bool) (ps : List R) : Prop :=
  (∀ p ∈ ps, D.isBound p = true) ∧
    ∀ k, ∀ G ∈ GDn P k n, ∀ x z, (x, z) ∈ G.at P.sorts.interp →
      ∃ p ∈ ps, (if last then (z, z) else (x, x)) ∈ bdenAt P.sorts.interp (some p)

/-- What the cursors of the strategy `s` of the table at `i`, of the goal
`g`, mean. -/
def Prog (st : StateOf R Rel (Ans D P)) (i : Nat) (g : GoalOf R Rel) :
    Strat Rel (Ans D P) → Prop
  | .span ran => ran = true → ∀ s, g.node = .span s → ∀ c, spanBoth D g.lb s g.rb = some c →
      CovS st i c
  | .copy isCall subs =>
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
      (∀ l, todo = some l → st.isDone side = true ∧ (∀ x ∈ l, x ∈ st.answers side) ∧
        ∀ x ∈ st.answers side, ∃ x' ∈ st.answers side, (x' ∈ l ∨ x' ∈ subs.map (·.1)) ∧
          den P.sorts.interp x.span ⊆ den P.sorts.interp x'.span) ∧
      ∀ e ∈ subs, e.1 ∈ st.answers side ∧
        goalAt st e.2.1 = some (pushG D g other k left e.1) ∧
        Read st i e.2.1 e.2.2 (pushedS D k left e.1.span)
  | .check left side other c => ∃ L Rg, SplitAt g .seq L Rg ∧
      side = (if left then L.node else Rg.node) ∧ other = (if left then Rg.node else L.node) ∧
      match c with
      | .opened subs => ∃ ps, EdgeOk D P side left ps ∧ subs.length = ps.length ∧
          ∀ (n : Nat) (p : R), ps[n]? = some p → ∃ j, subs[n]? = some j ∧
            goalAt st j = some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩)
      | _ => True

omit [DecidableEq R] in
/-- What the cursors of a strategy mean stays so in every later state. -/
theorem Prog.mono {st st' : StateOf R Rel (Ans D P)} (h : Stable st st') {i : Nat}
    {g : GoalOf R Rel} {s : Strat Rel (Ans D P)} (hs : Prog st i g s) : Prog st' i g s := by
  have hE := h.ext
  cases s with
  | span ran =>
    dsimp only [Prog] at hs ⊢
    exact fun hr s hn c hc => (hs hr s hn c hc).mono h
  | copy isCall subs =>
    dsimp only [Prog] at hs ⊢
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨h1, h2, fun m j pos hm => ?_⟩
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
    obtain ⟨L, Rg, h1, h2, h3, h4, h5⟩ := hs
    refine ⟨L, Rg, h1, hE _ _ h2, h3, fun l hl => ?_, fun e he => ?_⟩
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
      obtain ⟨ps, p1, p2, p3⟩ := h4
      refine ⟨ps, p1, p2, fun n p hp => ?_⟩
      obtain ⟨j, hj, hg⟩ := p3 n p hp
      exact ⟨j, hj, hE _ _ hg⟩
    | reading => trivial
    | off => trivial

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
    obtain ⟨xs, i, m, r, -, -, -, rfl, rfl⟩ := hs
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

theorem forall₂_right {α γ : Type} {Q : α → γ → Prop} {xs : List α} {es : List γ}
    (h : List.Forall₂ Q xs es) : ∀ e ∈ es, ∃ x ∈ xs, Q x e := by
  induction h with
  | nil => intro e he; cases he
  | cons hq _ ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨_, List.mem_cons_self, hq⟩
    · obtain ⟨x, hx, hq'⟩ := ih e he
      exact ⟨x, List.mem_cons_of_mem _ hx, hq'⟩

theorem forall₂_map {α γ : Type} {Q : α → γ → Prop} {xs : List α} {es : List γ}
    (h : List.Forall₂ Q xs es) {f : γ → α} (hf : ∀ x e, Q x e → f e = x) : es.map f = xs := by
  induction h with
  | nil => rfl
  | cons hq _ ih => simp only [List.map_cons, hf _ _ hq, ih]

theorem forall₂_getElem? {α γ : Type} {Q : α → γ → Prop} {xs : List α} {es : List γ}
    (h : List.Forall₂ Q xs es) : ∀ (n : Nat) (x : α), xs[n]? = some x →
      ∃ e, es[n]? = some e ∧ Q x e := by
  induction h with
  | nil => intro n x hx; cases hx
  | cons hq _ ih =>
    intro n x hx
    cases n with
    | zero => cases hx; exact ⟨_, rfl, hq⟩
    | succ n => exact ih n x hx

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
  · obtain ⟨x, hx, rfl, h2, h3⟩ := forall₂_right hall e he
    exact ⟨hx, h2, h3⟩

/-! ## The work of one strategy keeps what its cursors mean -/

theorem prog_work_span (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (whole : Bool) (i : Nat) (g : GoalOf R Rel) (ran : Bool) (ho : Open st i)
    (hb : IsBound D g.lb ∧ IsBound D g.rb) (hs : Prog st i g (.span ran)) :
    Prog (work (K := DerivationKernel.over D K hK P) whole i g st (.span ran)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) whole i g st (.span ran)).val.2.1 := by
  have hcov := fun c => cov_addOption (K := K) (hK := hK) hL st i ho c
  have hleaf := fun s z hz => Ans.leaf_ok (P := P) K hK (s := s) (z := z) hb.1 hb.2 hz
  at_cost K hK
  cases ran
  · simp only [work, Cost.bind_val, Cost.pure_val]
    dsimp only [Prog]
    intro _ s hn c hc
    obtain ⟨c', h1, h2, -⟩ := hleaf s c hc
    rw [hn]
    erw [h1]
    rw [← h2]
    exact hcov c'
  · exact hs

theorem prog_work_copy (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (whole : Bool) (i : Nat) (g : GoalOf R Rel) (isCall : Bool)
    (subs : List (Nat × Nat)) (ho : Open st i) (hs : Prog st i g (.copy isCall subs)) :
    Prog (work (K := DerivationKernel.over D K hK P) whole i g st (.copy isCall subs)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) whole i g st (.copy isCall subs)).val.2.1 := by
  have hcf := fun m st' as ho happ =>
    copyFrom_cov (K := K) (hK := hK) hL i g isCall m st' as ho happ
  have hs0 := hs
  dsimp only [Prog] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  have happ : ∀ p ∈ subs.zipIdx, ∀ a ∈ st.answers p.1.1, ∃ c,
      (if isCall then Ans.unfold D P a g.node else Ans.inj D P a g.node p.2).val = some c ∧
        c.span = a.span := by
    intro p hp a ha
    obtain ⟨x, hx, hgx, -⟩ := h3 p.2 p.1.1 p.1.2 (List.mem_zipIdx_iff_getElem?.1 hp)
    exact copy_ok hx (hI.answers hgx a ha)
  at_cost K hK
  simp only [work]
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨hf, hc⟩ := foldL_cov i
      (fun acc (p : (Nat × Nat) × Nat) =>
        copyFrom (K := DerivationKernel.over D _ hK P) i g isCall p.2 acc
          ((st.answers p.1.1).drop p.1.2))
      (fun p => p ∈ subs.zipIdx)
      (fun st' p => ∀ a ∈ (st.answers p.1.1).drop p.1.2, CovS st' i a.span)
      (fun st' p hp ho' => hcf p.2 st' _ ho'
        (fun a ha => happ p hp a (List.mem_of_mem_drop ha)))
      (fun _ _ _ h hc a ha => (hc a ha).mono h) subs.zipIdx st (fun _ h => h) ho
    have hS := hf.stable ho
    dsimp only [Prog]
    refine ⟨h1, by rw [List.length_map]; exact h2, fun m j pos hm => ?_⟩
    rw [List.getElem?_map] at hm
    cases hq : subs[m]? with
    | none => rw [hq] at hm; cases hm
    | some q =>
      rw [hq] at hm
      obtain ⟨j0, pos0⟩ := q
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨x, hx, hgx, hr⟩ := h3 m j0 pos0 hq
      refine ⟨x, hx, hS.ext _ _ hgx, (max_le hr.1 (Nat.le_refl _)).trans (hS.length_le j0),
        fun n y hn hy z hz => ?_⟩
      cases hz
      by_cases hlt : n < pos0
      · exact (hr.mono hS).2 n y hlt hy _ rfl
      · have hn' : n < (st.answers j0).length := by
          have := lt_max_iff.1 hn
          omega
        have hy' := hS.getElem?_old hy hn'
        refine hc ((j0, pos0), m) (List.mem_zipIdx_iff_getElem?.2 hq) y ?_
        refine List.mem_iff_getElem?.2 ⟨n - pos0, ?_⟩
        rw [List.getElem?_drop, show pos0 + (n - pos0) = n by omega]
        exact hy'
  · split
    · exact hs0
    · next p hp =>
      simp only [Cost.bind_val, Cost.pure_val]
      have hpm := mem_of_leastBy hp
      have hpok : p.1.2 < (st.answers p.1.1).length := by simpa using leastBy_ok hp
      obtain ⟨hf, hc⟩ := hcf p.2 st (((st.answers p.1.1).drop p.1.2).take 1) ho
        (fun a ha => happ p hpm a (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
      have hS := hf.stable ho
      dsimp only [Prog]
      refine ⟨h1, by rw [List.length_modify]; exact h2, fun m j pos hm => ?_⟩
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
    (hI : Inv st) (whole : Bool) (i : Nat) (g : GoalOf R Rel) (k : Kind) (a b : Nat)
    (c : Cursor) (ho : Open st i) (hs : Prog st i g (.join k a b c)) :
    Prog (work (K := DerivationKernel.over D K hK P) whole i g st (.join k a b c)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) whole i g st (.join k a b c)).val.2.1 := by
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
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    obtain ⟨a1, -, -, a4⟩ := Cursor.all_spec (st.answers a).length (st.answers b).length
      ((st.answers a).length * (st.answers b).length + 1) c h4
    obtain ⟨hf, hc⟩ := hjp (Cursor.all (st.answers a).length (st.answers b).length
      ((st.answers a).length * (st.answers b).length + 1) c).1
    exact fin _ _ _ hf hc a1 a4
  · obtain ⟨n1, -, -, n4⟩ := Cursor.next_spec (st.answers a).length (st.answers b).length
      (c.room (st.answers a).length (st.answers b).length) c h4
    split
    · next c' hn =>
      rw [hn] at n1 n4
      exact fin [] c' st (Frame.refl i st) (fun _ h => by cases h) n1 (fun p q hb => by
        rcases n4 p q hb with h | h
        · exact .inl h
        · cases h)
    · next pr c' hn =>
      rw [hn] at n1 n4
      simp only [Cost.bind_val, Cost.pure_val]
      obtain ⟨hf, hc⟩ := hjp [pr]
      exact fin [pr] c' _ hf hc n1 (fun p q hb => by
        rcases n4 p q hb with h | h
        · exact .inl h
        · cases h
          exact .inr List.mem_cons_self)

theorem prog_work_push (hL : D.Lawful P.sorts.interp) {st : StateOf R Rel (Ans D P)}
    (hI : Inv st) (whole : Bool) (i : Nat) (g : GoalOf R Rel) (k : Kind) (left : Bool)
    (side : Nat) (other : Rel) (todo : Option (List (Ans D P)))
    (subs : List (Ans D P × Nat × Nat)) (ho : Open st i) (hno : Normal other)
    (hs : Prog st i g (.push k left side other todo subs)) :
    Prog (work (K := DerivationKernel.over D K hK P) whole i g st
        (.push k left side other todo subs)).val.1 i g
      (work (K := DerivationKernel.over D K hK P) whole i g st
        (.push k left side other todo subs)).val.2.1 := by
  have hs0 := hs
  dsimp only [Prog] at hs
  obtain ⟨L, Rg, h1, h2, h3, h4, h5⟩ := hs
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
  have main : ∀ xs : List (Ans D P), st.isDone side = true → (∀ x ∈ xs, x ∈ st.answers side) →
      (∀ x ∈ st.answers side, ∃ x' ∈ st.answers side, (x' ∈ xs ∨ x' ∈ subs.map (·.1)) ∧
        den P.sorts.interp x.span ⊆ den P.sorts.interp x'.span) →
      Prog (foldL (fun acc (e : Ans D P × Nat × Nat) =>
          pushTake (K := DerivationKernel.over D K hK P) i k left e.1 acc
            (((pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1.answers
              e.2.1).drop e.2.2))
          (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val.1
          (subs ++ (pushOpen (K := DerivationKernel.over D K hK P) g other k left st
            xs).val.2)).val i g
        (.push k left side other (some [])
          ((subs ++ (pushOpen (K := DerivationKernel.over D K hK P) g other k left st
            xs).val.2).map fun e => (e.1, e.2.1, max e.2.2
              ((pushOpen (K := DerivationKernel.over D K hK P) g other k left st
                xs).val.1.answers e.2.1).length))) := by
    intro xs hd hxs hcv
    obtain ⟨hmap, hnew⟩ := hpo xs
    have hF1 := hpi xs
    have hI1 := hpI xs
    generalize (pushOpen (K := DerivationKernel.over D K hK P) g other k left st xs).val = r at *
    have hS1 := hF1.stable ho
    have ho1 := hF1.isOpen ho
    have hsub' : ∀ e ∈ subs ++ r.2, e.1 ∈ st.answers side ∧
        goalAt r.1 e.2.1 = some (pushG D g other k left e.1) ∧
        Read r.1 i e.2.1 e.2.2 (pushedS D k left e.1.span) := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · obtain ⟨d1, d2, d3⟩ := h5 e he
        exact ⟨d1, hS1.ext _ _ d2, d3.mono hS1⟩
      · obtain ⟨d1, d2, d3⟩ := hnew e he
        exact ⟨hxs _ d1, d3, by rw [d2]; exact Read.zero _ _ _ _⟩
    obtain ⟨hF2, hc⟩ := foldL_cov i
      (fun acc (e : Ans D P × Nat × Nat) =>
        pushTake (K := DerivationKernel.over D K hK P) i k left e.1 acc
          ((r.1.answers e.2.1).drop e.2.2))
      (fun e => e ∈ subs ++ r.2)
      (fun st' e => ∀ y ∈ (r.1.answers e.2.1).drop e.2.2, ∀ z,
        pushedS D k left e.1.span y.span = some z → CovS st' i z)
      (fun st' e he ho' => hpt e.1 st' _ ho' (hI.answers h2 _ (hsub' e he).1)
        (fun y hy => hI1.answers (hsub' e he).2.1 y (List.mem_of_mem_drop hy)))
      (fun _ _ _ h hc y hy z hz => (hc y hy z hz).mono h) (subs ++ r.2) r.1 (fun _ h => h) ho1
    have hS2 := hF2.stable ho1
    have hS := hS1.trans hS2
    obtain ⟨hd', hans⟩ := hS.isDone hd
    dsimp only [Prog]
    refine ⟨L, Rg, h1, hS.ext _ _ h2, h3, fun l hl => ?_, fun e' he' => ?_⟩
    · cases hl
      rw [hans]
      refine ⟨hd', (fun _ h => by cases h), fun x hx => ?_⟩
      obtain ⟨x', hx', hor, hsubset⟩ := hcv x hx
      refine ⟨x', hx', .inr ?_, hsubset⟩
      simp only [List.map_map, List.map_append, Function.comp_def, hmap]
      rcases hor with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      obtain ⟨d1, d2, d3⟩ := hsub' e he
      refine ⟨by rw [hans]; exact d1, hS2.ext _ _ d2,
        (max_le d3.1 (Nat.le_refl _)).trans (hS2.length_le _), fun n y hn hy z hz => ?_⟩
      by_cases hlt : n < e.2.2
      · exact (d3.mono hS2).2 n y hlt hy z hz
      · have hn' : n < (r.1.answers e.2.1).length := by
          have := lt_max_iff.1 hn
          omega
        have hy' := hS2.getElem?_old hy hn'
        refine hc e he y (List.mem_iff_getElem?.2 ⟨n - e.2.2, ?_⟩) z hz
        rw [List.getElem?_drop, show e.2.2 + (n - e.2.2) = n by omega]
        exact hy'
  at_cost K hK
  simp only [work]
  split
  · exact hs0
  · next hnd =>
    have hd : st.isDone side = true := by simpa using hnd
    split
    · cases todo with
      | none =>
        erw [Cost.bind_val]
        simp only [Cost.bind_val, Cost.pure_val]
        exact main _ hd hmm (fun x hx => (hcovmax x hx).imp fun x' h => ⟨hmm x' h.1, .inl h.1, h.2⟩)
      | some l =>
        erw [Cost.bind_val]
        simp only [Cost.bind_val, Cost.pure_val]
        obtain ⟨-, d2, d3⟩ := h4 l rfl
        exact main l hd d2 d3
    · split
      · simp only [Cost.bind_val, Cost.pure_val]
        dsimp only [Prog]
        exact ⟨L, Rg, h1, h2, h3, fun l hl => by
          cases hl
          exact ⟨hd, hmm, fun x hx => (hcovmax x hx).imp fun x' h => ⟨hmm x' h.1, .inl h.1, h.2⟩⟩,
          h5⟩
      · next x rest =>
        simp only [Cost.bind_val, Cost.pure_val]
        obtain ⟨hmap, hnew⟩ := hpo [x]
        have hF1 := hpi [x]
        have hS1 := hF1.stable ho
        obtain ⟨hd', hans⟩ := hS1.isDone hd
        obtain ⟨-, d2, d3⟩ := h4 (x :: rest) rfl
        dsimp only [Prog]
        refine ⟨L, Rg, h1, hS1.ext _ _ h2, h3, fun l hl => ?_, fun e he => ?_⟩
        · cases hl
          rw [hans]
          refine ⟨hd', fun y hy => d2 y (List.mem_cons_of_mem _ hy), fun y hy => ?_⟩
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
            exact d2 _ (by rw [List.mem_singleton.1 e1]; exact List.mem_cons_self)
      · split
        · exact hs0
        · next p hp =>
          simp only [Cost.bind_val, Cost.pure_val]
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
          refine ⟨L, Rg, h1, hS.ext _ _ h2, h3, fun l hl => ?_, fun e he => ?_⟩
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

end kernel

end Symmetric

end RwLog
