/-
# The feed cursor of a push

A push gives the tables it opened their rounds through a cursor of its own
(`Strat.push`, `feedPush`): a unit of it is one round offered to the table
of one answer of the side, and the units are taken in the order of the
classes of those answers, as the pairs of a join are. This file has what the
cursor keeps whatever the tables are (`Cursor.Fits`, `Strat.FeedFits`): the
feeding of a group leaves every feed cursor fitting.
-/
import RwLog.Rungs.Symmetric.Cursor
import RwLog.Rungs.Symmetric.Invariant

namespace RwLog

namespace Symmetric

open Traverse

/-- The feed cursor of a push fits; of any other strategy nothing is
asked. -/
def Strat.FeedFits {N A : Type} : Strat N A → Prop
  | .push _ _ _ _ _ _ _ _ fc => fc.Fits
  | _ => True

section pure

variable {S N A : Type}

/-- Filing units for tables leaves the paths of the answers seen. -/
theorem fileToks_pa (st : StateOf S N A) (dead : List Nat) :
    ∀ (l : List ((A × Option (Nat × Nat)) × Nat)) (fc : Cursor),
      (fileToks st dead l fc).pa = fc.pa
  | [], _ => rfl
  | (e, n) :: rest, fc => by
    unfold fileToks
    split
    · split
      · exact fileToks_pa st dead rest fc
      · exact (fileToks_pa st dead rest _).trans rfl
    · exact fileToks_pa st dead rest fc

/-- Filing units for tables of answers seen keeps the feed cursor fitting. -/
theorem fileToks_fits (st : StateOf S N A) (dead : List Nat) :
    ∀ (l : List ((A × Option (Nat × Nat)) × Nat)) (fc : Cursor), fc.Fits →
      (∀ e ∈ l, e.2 < fc.pa.length) → (fileToks st dead l fc).Fits
  | [], _, h, _ => h
  | (e, n) :: rest, fc, h, hl => by
    have hr : ∀ e ∈ rest, e.2 < fc.pa.length := fun e he => hl e (List.mem_cons_of_mem _ he)
    unfold fileToks
    split
    · split
      · exact fileToks_fits st dead rest fc h hr
      · exact fileToks_fits st dead rest _ (h.read (hl _ List.mem_cons_self) []) hr
    · exact fileToks_fits st dead rest fc h hr

/-- The feed cursor brought up to date has the path of every answer seen. -/
theorem syncFeed_pa_length (st : StateOf S N A) (side : Nat) (dead : List Nat)
    (subs : List (A × Option (Nat × Nat))) (fc : Cursor) :
    (syncFeed st side dead subs fc).pa.length = fc.pa.length + (subs.length - fc.pa.length) := by
  unfold syncFeed
  rw [fileToks_pa]
  simp [Cursor.kill, Cursor.pad]

/-- Bringing a feed cursor up to date keeps it fitting. -/
theorem syncFeed_fits (st : StateOf S N A) (side : Nat) (dead : List Nat)
    (subs : List (A × Option (Nat × Nat))) {fc : Cursor} (h : fc.Fits) :
    (syncFeed st side dead subs fc).Fits := by
  unfold syncFeed
  refine fileToks_fits st dead _ _ ((h.pad _).kill dead) fun e he => ?_
  rcases e with ⟨a, n⟩
  have hn := (List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 he)).1
  simp only [Cursor.kill, Cursor.pad, List.length_append, List.length_map, List.length_range']
  omega

/-- Filing units keeps the units there are. -/
theorem fileToks_todo (st : StateOf S N A) (dead : List Nat) :
    ∀ (l : List ((A × Option (Nat × Nat)) × Nat)) (fc : Cursor) (x : Nat × Nat), x ∈ fc.todo →
      x ∈ (fileToks st dead l fc).todo
  | [], _, _, h => h
  | (e, n) :: rest, fc, x, h => by
    unfold fileToks
    split
    · split
      · exact fileToks_todo st dead rest fc x h
      · exact fileToks_todo st dead rest _ x (by
          simp only [Cursor.read, List.mem_append]
          exact .inl h)
    · exact fileToks_todo st dead rest fc x h

/-- Filing units leaves the measure of the units there are. -/
theorem fileToks_rank (st : StateOf S N A) (dead : List Nat) (p q : Nat) :
    ∀ (l : List ((A × Option (Nat × Nat)) × Nat)) (fc : Cursor), q < fc.pb.length →
      (fileToks st dead l fc).rank p q = fc.rank p q
  | [], _, _ => rfl
  | (e, n) :: rest, fc, h => by
    unfold fileToks
    split
    · split
      · exact fileToks_rank st dead p q rest fc h
      · refine (fileToks_rank st dead p q rest _ ?_).trans (Cursor.rank_read n [] fc h)
        simp only [Cursor.read, List.length_append, List.length_cons, List.length_nil]
        omega
    · exact fileToks_rank st dead p q rest fc h

/-- After the filing, a table opened that is not complete, of an answer not
superseded, has a unit. -/
theorem fileToks_has (st : StateOf S N A) (dead : List Nat) {x : A} {t : Nat × Nat} {n : Nat}
    (hn : n ∉ dead) (hd : st.isDone t.1 = false) :
    ∀ (l : List ((A × Option (Nat × Nat)) × Nat)) (fc : Cursor), ((x, some t), n) ∈ l →
      ∃ q, (n, q) ∈ (fileToks st dead l fc).todo
  | [], _, h => absurd h List.not_mem_nil
  | (e, m) :: rest, fc, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
      unfold fileToks
      simp only
      split
      · next hc =>
        simp only [Bool.or_eq_true, List.contains_iff_mem, hn, hd, false_or, Bool.false_eq_true,
          List.any_eq_true, beq_iff_eq] at hc
        obtain ⟨y, hy, rfl⟩ := hc
        exact ⟨y.2, fileToks_todo st dead rest fc _ hy⟩
      · exact ⟨fc.pb.length, fileToks_todo st dead rest _ _ (by simp [Cursor.read])⟩
    · unfold fileToks
      split
      · split
        · exact fileToks_has st dead hn hd rest fc h
        · exact fileToks_has st dead hn hd rest _ h
      · exact fileToks_has st dead hn hd rest fc h

/-- Bringing a feed cursor up to date keeps each unit that is not of an
answer superseded, as far from its turn as it was. -/
theorem syncFeed_tok (st : StateOf S N A) (side : Nat) (dead : List Nat)
    (subs : List (A × Option (Nat × Nat))) {fc : Cursor} (h : fc.Fits) {p q : Nat}
    (hpq : (p, q) ∈ fc.todo) :
    p ∈ dead ∨ ((p, q) ∈ (syncFeed st side dead subs fc).todo ∧
      (syncFeed st side dead subs fc).rank p q = fc.rank p q) := by
  by_cases hp : p ∈ dead
  · exact .inl hp
  · obtain ⟨h1, h2, -⟩ := h.1 (p, q) hpq
    refine .inr ⟨?_, ?_⟩
    · unfold syncFeed
      exact fileToks_todo st dead _ _ _ (Cursor.mem_kill.2 ⟨hpq, hp⟩)
    · unfold syncFeed
      have e1 := fileToks_rank st dead p q subs.zipIdx
        ((fc.pad ((List.range' fc.pa.length (subs.length - fc.pa.length)).map fun n =>
          (st.pathsAt side).getD n [])).kill dead) h2
      have e2 := Cursor.rank_pad ((List.range' fc.pa.length (subs.length - fc.pa.length)).map
        fun n => (st.pathsAt side).getD n []) fc (q := q) h1
      rw [Cursor.rank_kill] at e1
      exact e1.trans e2

/-- After a feed cursor is brought up to date, a table opened of an answer
not superseded is complete or has a unit. -/
theorem syncFeed_has (st : StateOf S N A) (side : Nat) (dead : List Nat)
    (subs : List (A × Option (Nat × Nat))) (fc : Cursor) {n : Nat} {x : A} {t : Nat × Nat}
    (he : subs[n]? = some (x, some t)) (hn : n ∉ dead) :
    st.isDone t.1 = true ∨ ∃ q, (n, q) ∈ (syncFeed st side dead subs fc).todo := by
  cases hd : st.isDone t.1 with
  | true => exact .inl rfl
  | false =>
    unfold syncFeed
    exact .inr (fileToks_has st dead hn hd _ _ (List.mk_mem_zipIdx_iff_getElem?.2 he))

end pure

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
variable {K : Kernel R Cost} {hK : K.Refines D}

/-- The rounds a push shares among the tables it opened keep its feed cursor
fitting. -/
theorem feedToks_fits (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (subs : List (Ans D P × Option (Nat × Nat))) (f : Nat) (st : StateOf R Rel (Ans D P))
    (d : Nat) (fc : Cursor) (h : fc.Fits) :
    (feedToks (K := DerivationKernel.over D K hK P) adv subs f st d fc).val.2.2.Fits := by
  at_cost K hK
  induction f generalizing st d fc with
  | zero =>
    simp only [feedToks, Cost.pure_val]
    exact h
  | succ f ih =>
    simp only [feedToks]
    split
    · simp only [Cost.pure_val]
      exact h
    · next x hx =>
      have hm := h.mark (Cursor.next_todo hx)
      split
      · exact ih _ _ _ (hm 0)
      · simp only [Cost.bind_val]
        split
        · simp only [Cost.pure_val]
          exact hm _
        · exact ih _ _ _ (hm _)

theorem feedPush_fits (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (st : StateOf R Rel (Ans D P)) (d : Nat) (s : Strat Rel (Ans D P)) (h : s.FeedFits) :
    (feedPush (K := DerivationKernel.over D K hK P) adv st d s).val.2.2.FeedFits := by
  have hT := fun subs f fc hf =>
    feedToks_fits (K := K) (hK := hK) (P := P) adv subs f st d fc hf
  at_cost K hK
  cases s with
  | push k left side other subs dead reads c fc =>
    simp only [feedPush, Cost.bind_val, Cost.pure_val]
    exact hT _ _ _ (syncFeed_fits st side _ subs h)
  | _ =>
    simp only [feedPush, Cost.pure_val]
    exact h

theorem feedOne_fits (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (x : Fedee) (a : Feeding R Rel (Ans D P)) (h : ∀ s ∈ a.2.2, s.FeedFits) :
    ∀ s ∈ (feedOne (K := DerivationKernel.over D K hK P) adv x a).val.1.2.2, s.FeedFits := by
  have hT := fun s hs => feedPush_fits (K := K) (hK := hK) (P := P) adv a.1 a.2.1 s hs
  at_cost K hK
  cases x with
  | inl t =>
    simp only [feedOne, Cost.bind_val, Cost.pure_val]
    exact h
  | inr j =>
    simp only [feedOne]
    split
    · simp only [Cost.pure_val]
      exact h
    · next s hs =>
      simp only [Cost.bind_val, Cost.pure_val]
      intro s' hs'
      rcases List.mem_or_eq_of_mem_set hs' with hm | rfl
      · exact h _ hm
      · exact hT s (h s (List.mem_of_getElem? hs))

/-- **The feeding of a group leaves every feed cursor fitting.** -/
theorem feedGroup_fits (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (i k : Nat) (st : StateOf R Rel (Ans D P)) (d : Nat)
    (h : ∀ s ∈ ((groupsAt st i)[k]?.map (·.strats)).getD [], s.FeedFits) :
    ∀ s ∈ (feedGroup (K := DerivationKernel.over D K hK P) adv i k st d).val.2.2, s.FeedFits := by
  have hT := fun x a hs => feedOne_fits (K := K) (hK := hK) (P := P) adv x a hs
  at_cost K hK
  simp only [feedGroup, Cost.bind_val, Cost.pure_val]
  exact Share.offer_inv _ (fun a : Feeding R Rel (Ans D P) => ∀ s ∈ a.2.2, s.FeedFits)
    hT _ _ h

end Symmetric

end RwLog
