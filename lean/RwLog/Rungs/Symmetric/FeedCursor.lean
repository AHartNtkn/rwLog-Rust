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

theorem feedPushes_fits (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (ss : List (Strat Rel (Ans D P))) (st : StateOf R Rel (Ans D P)) (d : Nat)
    (h : ∀ s ∈ ss, s.FeedFits) :
    ∀ s ∈ (feedPushes (K := DerivationKernel.over D K hK P) adv st d ss).val.2.2, s.FeedFits := by
  have hT := fun X d s hs => feedPush_fits (K := K) (hK := hK) (P := P) adv X d s hs
  at_cost K hK
  induction ss generalizing st d with
  | nil =>
    simp only [feedPushes, Cost.pure_val]
    exact fun _ hs => absurd hs List.not_mem_nil
  | cons s rest ih =>
    simp only [feedPushes, Cost.bind_val, Cost.pure_val]
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact hT st d s (h s List.mem_cons_self)
    · exact ih _ _ (fun s hs => h s (List.mem_cons_of_mem _ hs)) s' hs'

/-- **The feeding of a group leaves every feed cursor fitting.** -/
theorem feedGroup_fits (adv : Nat → StateOf R Rel (Ans D P) → Cost (StateOf R Rel (Ans D P) × Nat))
    (i k : Nat) (st : StateOf R Rel (Ans D P)) (d : Nat)
    (h : ∀ s ∈ ((groupsAt st i)[k]?.map (·.strats)).getD [], s.FeedFits) :
    ∀ s ∈ (feedGroup (K := DerivationKernel.over D K hK P) adv i k st d).val.2.2, s.FeedFits := by
  have hT := fun ss X d hs => feedPushes_fits (K := K) (hK := hK) (P := P) adv ss X d hs
  at_cost K hK
  simp only [feedGroup]
  split
  · simp only [Cost.bind_val, Cost.pure_val]
    exact h
  · simp only [Cost.bind_val]
    exact hT _ _ _ h

end Symmetric

end RwLog
