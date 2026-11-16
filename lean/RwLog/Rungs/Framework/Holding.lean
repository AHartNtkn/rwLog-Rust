/-
# Saying what a state holds

An engine has to say what its state holds, as the things that are counted
(`Holding`, `Trusted/Cost.lean`), and to prove that the state is determined by
it (`Engine.held_inj`). This file builds such a listing piece by piece.

`Pack S N A α` lists a value of `α` so that the listing can be told apart
from whatever follows it (`Pack.cancel`): two values whose listings, each
followed by anything, are the same, are the same value followed by the same
thing. So the listing of a pair is the listings of its parts one after the
other, a list is listed behind its length, and an alternative behind its
number. A type with a one-to-one map into a type that is listed is listed
through the map (`Pack.ofInj`).
-/
import RwLog.Trusted.Cost

namespace RwLog

namespace Holding

variable {S N A : Type}

/-- Nothing held. -/
def nil : Holding S N A := ⟨[], [], [], []⟩

/-- What two listings hold together, the first before the second. -/
def app (x y : Holding S N A) : Holding S N A :=
  ⟨x.reps ++ y.reps, x.nodes ++ y.nodes, x.answers ++ y.answers, x.words ++ y.words⟩

instance : Append (Holding S N A) := ⟨app⟩

theorem app_def (x y : Holding S N A) :
    x ++ y = ⟨x.reps ++ y.reps, x.nodes ++ y.nodes, x.answers ++ y.answers, x.words ++ y.words⟩ :=
  rfl

@[simp] theorem app_nil (x : Holding S N A) : x ++ nil = x := by
  cases x; simp [app_def, nil]

@[simp] theorem nil_app (x : Holding S N A) : nil ++ x = x := by
  cases x; simp [app_def, nil]

theorem app_assoc (x y z : Holding S N A) : x ++ y ++ z = x ++ (y ++ z) := by
  simp [app_def, List.append_assoc]

/-- A number alone. -/
def word (n : Nat) : Holding S N A := ⟨[], [], [], [n]⟩

theorem word_cancel {n m : Nat} {h h' : Holding S N A} (e : word n ++ h = word m ++ h') :
    n = m ∧ h = h' := by
  cases h; cases h'
  simp only [app_def, word, List.nil_append, List.cons_append, Holding.mk.injEq,
    List.cons.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e
  exact ⟨rfl, rfl⟩

end Holding

open Holding

/-- A listing of the values of `α` that can be told apart from whatever
follows it. -/
class Pack (S N A : Type) (α : Type) where
  pack : α → Holding S N A
  cancel : ∀ (x y : α) (h h' : Holding S N A), pack x ++ h = pack y ++ h' → x = y ∧ h = h'

namespace Pack

variable {S N A : Type}

/-- The listing determines the value. -/
theorem inj {α : Type} [Pack S N A α] : Function.Injective (pack : α → Holding S N A) :=
  fun x y e => (cancel x y nil nil (by rw [app_nil, app_nil]; exact e)).1

/-- A type with a one-to-one map into a type that is listed. -/
@[reducible] def ofInj {α β : Type} [Pack S N A β] (f : α → β) (hf : Function.Injective f) : Pack S N A α where
  pack x := pack (f x)
  cancel x y h h' e := ⟨hf (cancel (f x) (f y) h h' e).1, (cancel (f x) (f y) h h' e).2⟩

instance : Pack S N A Nat where
  pack n := word n
  cancel _ _ _ _ e := word_cancel e

instance : Pack S N A Bool :=
  ofInj (fun b : Bool => b.toNat) (fun a b e => by cases a <;> cases b <;> simp_all)

instance : Pack S N A Unit where
  pack _ := nil
  cancel _ _ h h' e := ⟨rfl, by simpa using e⟩

/-- A representative. -/
instance rep : Pack S N A S where
  pack s := ⟨[s], [], [], []⟩
  cancel x y h h' e := by
    cases h; cases h'
    simp only [app_def, List.nil_append, List.cons_append, Holding.mk.injEq, List.cons.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := e
    exact ⟨rfl, rfl⟩

/-- A node. -/
@[reducible] def node : Pack S N A N where
  pack n := ⟨[], [n], [], []⟩
  cancel x y h h' e := by
    cases h; cases h'
    simp only [app_def, List.nil_append, List.cons_append, Holding.mk.injEq, List.cons.injEq] at e
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩ := e
    exact ⟨rfl, rfl⟩

/-- An answer. -/
@[reducible] def answer : Pack S N A A where
  pack a := ⟨[], [], [a], []⟩
  cancel x y h h' e := by
    cases h; cases h'
    simp only [app_def, List.nil_append, List.cons_append, Holding.mk.injEq, List.cons.injEq] at e
    obtain ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨rfl, rfl⟩

instance prod {α β : Type} [Pack S N A α] [Pack S N A β] : Pack S N A (α × β) where
  pack x := pack x.1 ++ pack x.2
  cancel x y h h' e := by
    rw [app_assoc, app_assoc] at e
    obtain ⟨h1, e⟩ := cancel x.1 y.1 _ _ e
    obtain ⟨h2, e⟩ := cancel x.2 y.2 _ _ e
    exact ⟨Prod.ext h1 h2, e⟩

instance option {α : Type} [Pack S N A α] : Pack S N A (Option α) where
  pack
    | none => word 0
    | some x => word 1 ++ pack x
  cancel x y h h' e := by
    cases x with
    | none =>
      cases y with
      | none => exact ⟨rfl, (word_cancel e).2⟩
      | some y => rw [app_assoc] at e; exact absurd (word_cancel e).1 (by decide)
    | some x =>
      cases y with
      | none => rw [app_assoc] at e; exact absurd (word_cancel e).1 (by decide)
      | some y =>
        rw [app_assoc, app_assoc] at e
        obtain ⟨h1, e⟩ := cancel x y _ _ (word_cancel e).2
        exact ⟨congrArg some h1, e⟩

instance sum {α β : Type} [Pack S N A α] [Pack S N A β] : Pack S N A (α ⊕ β) where
  pack
    | .inl x => word 0 ++ pack x
    | .inr x => word 1 ++ pack x
  cancel x y h h' e := by
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        rw [app_assoc, app_assoc] at e
        obtain ⟨h1, e⟩ := cancel x y _ _ (word_cancel e).2
        exact ⟨congrArg Sum.inl h1, e⟩
      | inr y => rw [app_assoc, app_assoc] at e; exact absurd (word_cancel e).1 (by decide)
    | inr x =>
      cases y with
      | inl y => rw [app_assoc, app_assoc] at e; exact absurd (word_cancel e).1 (by decide)
      | inr y =>
        rw [app_assoc, app_assoc] at e
        obtain ⟨h1, e⟩ := cancel x y _ _ (word_cancel e).2
        exact ⟨congrArg Sum.inr h1, e⟩

/-- The members of a list one after the other. -/
def packAll {α : Type} [Pack S N A α] : List α → Holding S N A
  | [] => nil
  | x :: xs => pack x ++ packAll xs

theorem packAll_cancel {α : Type} [Pack S N A α] :
    ∀ (l l' : List α) (h h' : Holding S N A), l.length = l'.length →
      packAll l ++ h = packAll l' ++ h' → l = l' ∧ h = h'
  | [], [], h, h', _, e => ⟨rfl, by simpa [packAll] using e⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | x :: xs, y :: ys, h, h', hl, e => by
    simp only [packAll] at e
    rw [app_assoc, app_assoc] at e
    obtain ⟨h1, e⟩ := cancel x y _ _ e
    obtain ⟨h2, e⟩ := packAll_cancel xs ys h h' (by simpa using hl) e
    exact ⟨by rw [h1, h2], e⟩

instance list {α : Type} [Pack S N A α] : Pack S N A (List α) where
  pack l := word l.length ++ packAll l
  cancel x y h h' e := by
    rw [app_assoc, app_assoc] at e
    exact packAll_cancel x y h h' (word_cancel e).1 (word_cancel e).2

end Pack

end RwLog
