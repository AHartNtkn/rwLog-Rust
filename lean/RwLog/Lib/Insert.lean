/-
# Sorting by insertion into a list that is already known

`sortBy lt` builds a list by inserting its members one at a time, each before
the first member it is `lt` of. No property of `lt` as an order is assumed.
What is proved is what the rungs need: if the members come, without repeats,
from a list `F` whose members are pairwise in `lt` order, the result is `F`
with the members that did not come left out (`sortBy_eq_filter`), and so `F`
itself when all of them came (`sortBy_eq`).
-/
import Mathlib.Data.List.Basic

namespace RwLog

variable {α : Type}

/-- Insert `x` before the first member it is `lt` of. -/
def insertBy (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBy lt x ys

/-- Insert the members one at a time. -/
def sortBy (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertBy lt x acc) []

/-- `a` stands before `b`. -/
def Before (lt : α → α → Bool) (a b : α) : Prop := lt a b = true ∧ lt b a = false

variable {lt : α → α → Bool}

theorem not_mem_of_before {F : List α} {x : α} (h : ∀ y ∈ F, Before lt x y) : x ∉ F := by
  intro hx
  obtain ⟨h1, h2⟩ := h x hx
  rw [h1] at h2
  exact Bool.noConfusion h2

variable [DecidableEq α]

/-- Inserting a member of `F` into a part of `F` puts it where it stands in
`F`. -/
theorem insertBy_filter : ∀ {F : List α}, F.Pairwise (Before lt) → ∀ (p : α → Bool) (x : α),
    x ∈ F → p x = false →
    insertBy lt x (F.filter p) = F.filter fun y => p y || decide (y = x)
  | [], _, _, _, hx, _ => by cases hx
  | f :: F, hF, p, x, hx, hp => by
    obtain ⟨hf, hF'⟩ := List.pairwise_cons.mp hF
    by_cases hfx : f = x
    · subst hfx
      have hnot : f ∉ F := not_mem_of_before hf
      have hrest : (F.filter fun y => p y || decide (y = f)) = F.filter p :=
        List.filter_congr fun y hy => by
          have : y ≠ f := fun e => hnot (e ▸ hy)
          simp [this]
      rw [List.filter_cons, hp, List.filter_cons]
      simp only [Bool.false_eq_true, ↓reduceIte, decide_true, Bool.or_true, hrest]
      cases hfl : F.filter p with
      | nil => rfl
      | cons y ys =>
        have hy : y ∈ F := List.mem_of_mem_filter (hfl ▸ List.mem_cons_self)
        simp [insertBy, (hf y hy).1]
    · have hxF : x ∈ F := by
        rcases List.mem_cons.mp hx with h | h
        · exact (hfx h.symm).elim
        · exact h
      have ih := insertBy_filter hF' p x hxF hp
      rw [List.filter_cons, List.filter_cons]
      cases hpf : p f
      · simpa [hfx] using ih
      · simp only [↓reduceIte, Bool.true_or, insertBy, (hf x hxF).2, Bool.false_eq_true]
        rw [ih]

theorem foldl_insertBy {F : List α} (hF : F.Pairwise (Before lt)) : ∀ (L : List α) (p : α → Bool),
    (∀ x ∈ L, x ∈ F ∧ p x = false) → L.Nodup →
    L.foldl (fun acc x => insertBy lt x acc) (F.filter p) =
      F.filter fun y => p y || decide (y ∈ L)
  | [], p, _, _ => by simp
  | x :: L, p, h, hn => by
    obtain ⟨hx, hn'⟩ := List.nodup_cons.mp hn
    rw [List.foldl_cons, insertBy_filter hF p x (h x List.mem_cons_self).1 (h x List.mem_cons_self).2,
      foldl_insertBy hF L _ (fun z hz => ⟨(h z (List.mem_cons_of_mem _ hz)).1, by
        have : z ≠ x := fun e => hx (e ▸ hz)
        simp [(h z (List.mem_cons_of_mem _ hz)).2, this]⟩) hn']
    exact List.filter_congr fun y _ => by simp [Bool.or_assoc]

/-- Sorting members of `F` gives `F` without the members that are missing. -/
theorem sortBy_eq_filter {F : List α} (hF : F.Pairwise (Before lt)) {L : List α} (hn : L.Nodup)
    (hL : ∀ x ∈ L, x ∈ F) : sortBy lt L = F.filter fun y => decide (y ∈ L) := by
  have h := foldl_insertBy hF L (fun _ => false) (fun x hx => ⟨hL x hx, rfl⟩) hn
  have e : F.filter (fun _ => false) = [] := by simp
  rw [e] at h
  simpa [sortBy] using h

/-- Sorting all the members of `F` gives `F`. -/
theorem sortBy_eq {F : List α} (hF : F.Pairwise (Before lt)) {L : List α} (hn : L.Nodup)
    (hL : ∀ x, x ∈ L ↔ x ∈ F) : sortBy lt L = F := by
  rw [sortBy_eq_filter hF hn fun x hx => (hL x).mp hx]
  exact List.filter_eq_self.mpr fun y hy => by simpa using (hL y).mpr hy

end RwLog
