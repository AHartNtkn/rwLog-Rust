/-
# A side that halts with no answer makes `;` and `&` halt

For the tabled machine with an exact unfolding race that meets its
specification (`Tabled.emptySide`).

A query `a` that halts with no answer relates nothing (`pairs_empty`), so the
goal of its normal form is void (`void_of_pairs`), and that goal completes in
every run in which it has a table (`side_done`, by `host_done`: the verdict
of an exact race stays final at greater depths, `UEx.mono`). The normal
form of `a ; b` is a chain that starts with the members of the normal form of
`a`, that of `b ; a` a chain that ends with them, and that of `a & b` and of
`b & a` a meet that has them among its members; the ladders of
`Rungs/Tabled/Void.lean` complete the root.
-/
import RwLog.Rungs.Tabled.Void
import RwLog.Rungs.Tabled.Symmetry
import RwLog.Rungs.Framework.Unfolding.RacesExact
import RwLog.Rungs.Framework.SameTrace

namespace RwLog

namespace Tabled

open Answer Unfold

variable (U : Unfolder) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))

section theorems

variable {U dom K hK}
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp) (hG : Good @U)

include hD hG in
/-- The machine halts exactly when the root goal completes. -/
theorem terminates_iff {P : Program} {q : Rel} (wf : P.WellFormed q) :
    (Rt @U dom K hK).Terminates P q ↔
      ∃ r, isDone (T @U dom K hK P q.norm r) (bare q.norm) = true := by
  have hI := inv_of_wf (K := K) (hK := hK) hD hG wf
  have hd : ∀ r, RD @U dom K hK P q.norm r =
      isDone (T @U dom K hK P q.norm r) (bare q.norm) := fun r => by
    obtain ⟨_, e⟩ := isDone_of_idx
      (idx_root (K P.sorts) (hK P.sorts) (UAt @U dom K hK P) q.norm r)
    rw [RD, rootDone_eq]
    exact e.symm
  constructor
  · rintro ⟨n, hn⟩
    rw [init_eq] at hn
    rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, -, hdj, -⟩
    · simp [Runtime.Halts, Runtime.final, hr] at hn
    · exact ⟨j, by rw [← hd]; exact hdj⟩
  · rintro ⟨r, hr⟩
    refine ⟨r + 1, ?_⟩
    rw [init_eq]
    rcases run_cases hI (r + 1) with ⟨hall, -⟩ | ⟨j, -, -, hr'⟩
    · have := hall r (Nat.lt_succ_self r)
      rw [hd, hr] at this
      cases this
    · simp [Runtime.Halts, Runtime.final, hr']

include hD hG in
/-- A query that halts with no answer relates nothing. -/
theorem pairs_empty {P : Program} {a : Rel} (wf : P.WellFormed a)
    (ht : (Rt @U dom K hK).Terminates P a) (he : (Rt @U dom K hK).Answers P a = ∅) :
    P.pairs a = ∅ := by
  obtain ⟨n, hn⟩ := ht
  rw [honestExhaustion (K := K) (hK := hK) hD hG P a wf n hn]
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 hp
  have : x ∈ (Rt @U dom K hK).Answers P a := ⟨n, hx⟩
  rw [he] at this
  exact this

variable (hE : Exact @U)

include hD hG hE in
/-- The goal of a query that halts completes in every run in which it has a
table. -/
theorem side_done {P : Program} {a e : Rel} (wf : P.WellFormed a)
    (hroot : GoalOk (dom P.sorts) (bare e : GoalOf (R P.sorts) Rel))
    (hfo : ProgFO P) (ht : (Rt @U dom K hK).Terminates P a) :
    (∃ r i, idx (T @U dom K hK P e r) (bare a.norm) = some i) →
      ∃ r, isDone (T @U dom K hK P e r) (bare a.norm) = true := by
  obtain ⟨r, hr⟩ := (terminates_iff hD hG wf).1 ht
  have hL := hD _ wf.2.2.1
  exact host_done hL hfo (hG (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hfo)
    (hE (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hfo).mono (root_ok wf) hroot r _ hr

include hD hG hE in
/-- **A side that halts with no answer makes `;` and `&` halt**, on either
side. -/
theorem emptySide : (Rt @U dom K hK).EmptySide := fun P a b wf ht he => by
  have wfa : P.WellFormed a := wf.seq_left
  have wfba : P.WellFormed (.seq b a) := wf.seq_swap
  have wfand : P.WellFormed (.and a b) := wf.and_of_seq
  have wfand' : P.WellFormed (.and b a) := wf.seq_swap.and_of_seq
  have hL := hD _ wf.2.2.1
  have hfo := wf.progFO
  have hUk := hG (dom P.sorts) P (K P.sorts) (hK P.sorts) hL hfo
  have hv : Void P (bare a.norm : GoalOf (R P.sorts) Rel) :=
    void_of_pairs (pairs_empty hD hG wfa ht he)
  have hroot0 : ∀ e : Rel, ∃ r i, idx (T @U dom K hK P e r) (bare e) = some i := fun e =>
    ⟨0, 0, idx_root (K P.sorts) (hK P.sorts) (UAt @U dom K hK P) e 0⟩
  have hna : ∀ x ∈ seqParts a.norm ++ seqParts b.norm, NotSeq x := fun x hx =>
    (List.mem_append.1 hx).elim notSeq_of_mem_seqParts notSeq_of_mem_seqParts
  have hna' : ∀ x ∈ seqParts b.norm ++ seqParts a.norm, NotSeq x := fun x hx =>
    (List.mem_append.1 hx).elim notSeq_of_mem_seqParts notSeq_of_mem_seqParts
  have hpa := List.length_pos_iff.2 (seqParts_ne_nil a.norm)
  have hpb := List.length_pos_iff.2 (seqParts_ne_nil b.norm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `a ; b`: the chain starts with the members of `a`
    have hroot := root_ok (dom := dom) wf
    have e₁ : mkSeq ((seqParts a.norm ++ seqParts b.norm).take (seqParts a.norm).length) =
        a.norm := by rw [List.take_left' rfl, (normal_norm a).mkSeq_seqParts]
    have key := chain_ladder hL hfo hUk hroot hna hpa (by rw [e₁]; exact hv)
      (by rw [e₁]; exact side_done hD hG hE wfa hroot hfo ht) (seqParts b.norm).length
      (seqParts a.norm ++ seqParts b.norm).length (by simp) (Nat.le_refl _)
      (by rw [List.take_length]; exact hroot)
    rw [List.take_length] at key
    exact (terminates_iff hD hG wf).2 (key.2 (hroot0 _))
  · -- `b ; a`: the chain ends with the members of `a`
    have hroot := root_ok (dom := dom) wfba
    have e₁ : mkSeq ((seqParts b.norm ++ seqParts a.norm).drop (seqParts b.norm).length) =
        a.norm := by rw [List.drop_left' rfl, (normal_norm a).mkSeq_seqParts]
    have key := chain_ladder_right hL hfo hUk hroot hna' (q := (seqParts b.norm).length)
      (by simp; omega) (by rw [e₁]; exact hv)
      (by rw [e₁]; exact side_done hD hG hE wfa hroot hfo ht) (seqParts b.norm).length 0
      (by simp) hroot
    exact (terminates_iff hD hG wfba).2 (key.2 (hroot0 _))
  · -- `a & b`: the meet has the members of `a`
    have hroot := root_ok (dom := dom) wfand
    have e₁ : mkAnd (andParts a.norm) = a.norm := (normal_norm a).mkAnd_andParts
    have key := meet_ladder hL hfo hUk hroot (andParts_ne_nil a.norm)
      (normal_norm a).sorted_andParts (by rw [e₁]; exact hv)
      (by rw [e₁]; exact side_done hD hG hE wfa hroot hfo ht) (andParts b.norm).length
      (sortedParts (andParts a.norm ++ andParts b.norm)) (andParts b.norm) rfl
      (pairwise_sortedParts _) (sortedParts_perm _)
      (fun x hx => (List.mem_append.1 ((sortedParts_perm _).mem_iff.1 hx)).elim
        notAnd_of_mem_andParts notAnd_of_mem_andParts) hroot
    exact (terminates_iff hD hG wfand).2 (key.2 (hroot0 _))
  · -- `b & a`
    have hroot := root_ok (dom := dom) wfand'
    have e₁ : mkAnd (andParts a.norm) = a.norm := (normal_norm a).mkAnd_andParts
    have key := meet_ladder hL hfo hUk hroot (andParts_ne_nil a.norm)
      (normal_norm a).sorted_andParts (by rw [e₁]; exact hv)
      (by rw [e₁]; exact side_done hD hG hE wfa hroot hfo ht) (andParts b.norm).length
      (sortedParts (andParts b.norm ++ andParts a.norm)) (andParts b.norm) rfl
      (pairwise_sortedParts _) ((sortedParts_perm _).trans List.perm_append_comm)
      (fun x hx => (List.mem_append.1 ((sortedParts_perm _).mem_iff.1 hx)).elim
        notAnd_of_mem_andParts notAnd_of_mem_andParts) hroot
    exact (terminates_iff hD hG wfand').2 (key.2 (hroot0 _))

end theorems

end Tabled

end RwLog
