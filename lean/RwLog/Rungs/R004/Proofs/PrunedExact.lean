/-
# The evaluation pruned from the right computes R001's unfolding race

* The walk from the right hands `collect` the derivations of `WR`
  (`walkR_val`). `collect` stops at the first one whose product contains a
  call, and otherwise keeps every product under the key of its derivation
  (`run_collect_fst`, `run_collect_snd`).
* A derivation that is not in `WR` has no product (`norm_of_not_mem_WR`), so
  the products kept are all the products of the normal form, and the
  unfolding is final exactly when the walk did not stop (`all_closed_iff`).
* The keys of the derivations are in the normalizer's order
  (`paths_before`), so sorting the products by key lists them as the
  normalizer does (`sort_found`).

So the answers are R001's, and removing the repeats is all that differs
(`pruned_exact`).
-/
import RwLog.Rungs.R004.Proofs.Sound
import RwLog.Rungs.R003.Proofs.SharedExact

namespace RwLog

namespace R004

open R000 Cost

/-! ## Sorting, with the ticks forgotten -/

/-- The order of two products: the order of their keys. -/
def foundLt (a b : Found) : Bool := a.1.lt b.1

theorem insert_val (x : Found) : ∀ ys : List Found, (insert x ys).val = insertBy foundLt x ys
  | [] => rfl
  | y :: ys => by
    rw [insert, insertBy]
    by_cases h : x.1.lt y.1 = true
    · simp [before, foundLt, h]
    · simp [before, foundLt, h, insert_val x ys]

theorem sort_val (xs : List Found) : (sort xs).val = sortBy foundLt xs := by
  simp only [sort, foldL_val, sortBy]
  congr 1
  funext acc x
  exact insert_val x acc

/-! ## What `collect` keeps -/

/-- The product of a derivation, under its key. -/
def found (x : Path) : List Found := (norm false x.pe).map fun p => (x.key, p)

/-- The derivation's product contains no call. -/
def closedP (x : Path) : Bool := (norm false x.pe).all fun p => (toRel p).calls.isEmpty

theorem collect_val (x : Path) (acc : List Found) :
    (collect x acc).val = if closedP x then (false, found x ++ acc) else (true, acc) := by
  simp only [collect, bind_val, R002.Eager.norm_val, closedP, found]
  by_cases h : ((norm false x.pe).all fun p => (toRel p).calls.isEmpty) = true
  · simp [h]
  · simp [h]

theorem run_collect_fst : ∀ (xs : List Path) (acc : List Found),
    (run collect xs acc).1 = !xs.all closedP
  | [], _ => rfl
  | x :: xs, acc => by
    simp only [run, collect_val, List.all_cons]
    cases closedP x
    · simp
    · simpa using run_collect_fst xs _

theorem run_collect_snd : ∀ (xs : List Path) (acc : List Found), xs.all closedP = true →
    (run collect xs acc).2 = xs.reverse.flatMap found ++ acc
  | [], _, _ => rfl
  | x :: xs, acc, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [run, collect_val, h.1, ↓reduceIte, Bool.false_eq_true]
    rw [run_collect_snd xs _ h.2]
    simp

/-! ## The products, in the normalizer's order -/

theorem pairwise_of_length_le_one {α : Type} {r : α → α → Prop} {l : List α} (h : l.length ≤ 1) :
    l.Pairwise r := by
  match l, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

theorem length_found {e : Rel} {neg : Bool} {x : Path} (hx : x ∈ paths neg e) :
    (found x).length ≤ 1 := by
  simpa [found] using norm_path_le e neg x hx

/-- The products of all the derivations are in the order of their keys. -/
theorem found_before (e : Rel) (neg : Bool) :
    ((paths neg e).flatMap found).Pairwise (Before foundLt) := by
  rw [List.pairwise_flatMap]
  refine ⟨fun x hx => pairwise_of_length_le_one (length_found hx), ?_⟩
  exact (paths_before e neg).imp fun {x y} h a ha b hb => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    exact h

theorem key_ne {e : Rel} {neg : Bool} {x y : Path} (hx : x ∈ paths neg e) (hy : y ∈ paths neg e)
    (hne : x ≠ y) : x.key ≠ y.key := by
  have hk : ∀ {a b : Path}, KeyBefore a b → a.key ≠ b.key := fun {a b} h e' => by
    have h1 := h.1
    rw [e', Key.lt_irrefl] at h1
    exact Bool.noConfusion h1
  have h2 : (paths neg e).Pairwise fun a b : Path => a ≠ b → a.key ≠ b.key := by
    refine (paths_before e neg).imp ?_
    intro a b h _
    exact hk h
  have h3 : (paths neg e).Pairwise (flip fun a b : Path => a ≠ b → a.key ≠ b.key) := by
    refine (paths_before e neg).imp ?_
    intro a b h _
    exact (hk h).symm
  exact List.Pairwise.forall_of_forall_of_flip (fun a _ h => (h rfl).elim) h2 h3 hx hy hne

/-- Sorting the products the walk from the right keeps lists every product of
every derivation, in the normalizer's order. -/
theorem sort_found (e : Rel) (neg : Bool) :
    sortBy foundLt ((WR neg e []).reverse.flatMap found) = (paths neg e).flatMap found := by
  refine sortBy_eq (found_before e neg) ?_ fun z => ?_
  · rw [List.nodup_flatMap]
    refine ⟨fun x hx => ?_, ?_⟩
    · have hx' := mem_paths_of_WR e neg [] x (List.mem_reverse.mp hx)
      exact pairwise_of_length_le_one (length_found hx')
    · have hn : (WR neg e []).reverse.Nodup := List.nodup_reverse.mpr (nodup_WR e neg [])
      refine (List.Pairwise.and_mem.mp hn).imp fun {x y} h => ?_
      obtain ⟨hx, hy, hne⟩ := h
      rw [Function.onFun, List.disjoint_left]
      intro a ha hb
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨_, _, e'⟩ := List.mem_map.mp hb
      exact key_ne (mem_paths_of_WR e neg [] x (List.mem_reverse.mp hx))
        (mem_paths_of_WR e neg [] y (List.mem_reverse.mp hy)) hne
        (congrArg Prod.fst e').symm
  · simp only [List.mem_flatMap, List.mem_reverse]
    constructor
    · rintro ⟨x, hx, hz⟩
      exact ⟨x, mem_paths_of_WR e neg [] x hx, hz⟩
    · rintro ⟨x, hx, hz⟩
      refine ⟨x, ?_, hz⟩
      by_contra hn
      rw [found, norm_of_not_mem_WR hx hn] at hz
      cases hz

/-- The products kept, without their keys, are the normal form. -/
theorem found_products (e : Rel) (neg : Bool) :
    ((paths neg e).flatMap found).map Prod.snd = norm neg e := by
  rw [norm_paths, List.map_flatMap]
  refine List.flatMap_congr fun x _ => ?_
  simp [found, Function.comp_def]

/-- The walk does not stop exactly when no product contains a call. -/
theorem all_closed_iff (e : Rel) (neg : Bool) :
    (WR neg e []).all closedP = (norm neg e).all fun p => (toRel p).calls.isEmpty := by
  rw [norm_paths, List.all_flatMap, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h x hx
    by_cases hw : x ∈ WR neg e []
    · exact h x hw
    · rw [norm_of_not_mem_WR hx hw]; rfl
  · intro h x hx
    exact h x (mem_paths_of_WR e neg [] x hx)

/-! ## The race -/

/-- The evaluation pruned from the right computes R001's unfolding race,
without the repeats. -/
theorem pruned_exact : Obligation.pruned_exact := by
  intro P d g
  have hfst : (walkR P d false g.rel [] collect []).val.1 = !R001.unfoldFinal P d g := by
    rw [walkR_val, run_collect_fst, all_closed_iff]
    rfl
  unfold pruned
  simp only [bind_val]
  unfold R001.unfoldAnswers
  cases hf : R001.unfoldFinal P d g with
  | false =>
    rw [hf] at hfst
    simp [hfst]
  | true =>
    rw [hf] at hfst
    have hall : (WR false (unfoldN P d g.rel) []).all closedP = true := by
      rw [all_closed_iff]; exact hf
    have hsnd : (walkR P d false g.rel [] collect []).val.2 =
        (WR false (unfoldN P d g.rel) []).reverse.flatMap found := by
      rw [walkR_val, run_collect_snd _ _ hall, List.append_nil]
    have hspans : R002.closed ((sort (walkR P d false g.rel [] collect []).val.2).val.map
        Prod.snd) = R000.roundSpans P g.rel d := by
      rw [hsnd, sort_val, sort_found, found_products]
      exact R002.closed_eq_derivs _ _ hf
    simp only [hfst, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_val, pure_val,
      flatMapL_val, Tabled.live_val, R003.foldSpan_val, Prod.mk.injEq, true_and]
    rw [hspans, ← firsts_eq_eraseDups]
    rfl

end R004

end RwLog
