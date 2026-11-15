/-
# A side that halts with no answer makes `;` and `&` halt

For the symmetric engine (`Symmetric.emptySide`), in every lawful domain.

A query `a` that halts with no answer relates nothing (`pairs_empty`), so the
goal of its normal form is void (`void_of_pairs`), and the table of that goal
is complete in every run that does not neglect it (`IsRun.transfer`).

A goal that is not neglected and has a split one side of which is void, and
complete in the run whenever it is not neglected, completes
(`IsRun.done_of_side`): the group of that split works for ever, the push of
the void side takes its answers once the side is complete, there are none,
and so the push has nothing left to do and reads no table.

The normal form of `a ; b` is a chain that starts with the members of the
normal form of `a`, and the engine splits a chain at every place, so one
split has the goal of `a` as its left side; likewise `b ; a`. The normal form
of `a & b` is a meet that has the members of the normal form of `a` among its
members, and the engine splits a meet into one member and the others, so the
others are taken away one at a time (`IsRun.meet_ladder`).
-/
import RwLog.Rungs.Symmetric.Transfer
import RwLog.Rungs.Symmetric.Correct
import RwLog.Rungs.Framework.Void
import RwLog.Rungs.Framework.SameTrace

namespace RwLog

namespace Symmetric

open Answer Saturation Goals

section run

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

variable {τ : Nat → StateOf R Rel (Ans D P)}

omit [DecidableEq R] [Answer R] in
/-- A chain with no boundary is split at every place inside it. -/
theorem splitAt_mkSeq {xs : List Rel} (hx : ∀ x ∈ xs, NotSeq x) {p : Nat} (hp : 0 < p)
    (hp' : p < xs.length) :
    SplitAt (bare (mkSeq xs) : GoalOf R Rel) .seq (bare (mkSeq (xs.take p)))
      (bare (mkSeq (xs.drop p))) := by
  have hparts : seqParts (mkSeq xs) = xs :=
    seqParts_mkSeq (List.ne_nil_of_length_pos (by omega)) hx
  refine ⟨xs, p, _, _, view_mkSeq (by omega) hx, hp, hp', ?_, ?_, rfl, rfl⟩
  · show (mkSeq xs).interval 0 p = _
    unfold RelOf.interval RelOf.chainParts
    rw [hparts, ite_of_pos ⟨hp, by omega⟩, List.drop_zero]
  · show (mkSeq xs).interval p xs.length = _
    unfold RelOf.interval RelOf.chainParts
    rw [hparts, ite_of_pos ⟨hp', Nat.le_refl _⟩, List.take_length]

omit [DecidableEq R] [Answer R] in
/-- A meet with no boundary is split into each member it is split at and
the others. -/
theorem splitAt_mkAnd {ys : List Rel} (hy : ∀ x ∈ ys, NotAnd x) (h2 : 2 ≤ ys.length) {i : Nat}
    (hi : i < ys.length) (hs : i ∈ andSplits ys.length) :
    SplitAt (bare (mkAnd ys) : GoalOf R Rel) .and (bare ys[i])
      (bare (mkAnd (ys.eraseIdx i))) := by
  refine ⟨ys, i, _, _, view_mkAnd h2 hy, hs, List.getElem?_eq_getElem hi, ?_, rfl, rfl⟩
  show (mkAnd ys).without i = _
  unfold RelOf.without
  simp only [RelOf.meetParts]
  rw [andParts_mkAnd (List.ne_nil_of_length_pos (by omega)) hy, ite_of_pos ⟨hi, h2⟩]

variable (hL : D.Lawful P.sorts.interp)

include hL

/-- The table of a void goal never has an answer. -/
theorem IsRun.void_empty (hτ : IsRun τ) {r k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (τ r) k = some g) (hv : Void P g) (r2 : Nat) : (τ r2).answers k = [] := by
  cases hx : (τ r2).answers k with
  | nil => rfl
  | cons y l =>
    exfalso
    obtain ⟨t, ht, hyt⟩ := mem_answers (st := τ r2) (j := k) (y := y)
      (by rw [hx]; exact List.mem_cons_self)
    have hg : t.goal = g := (hτ.goal_any hk (goalAt_of_table ht)).symm
    have := ((hτ.good r2).inv.core k t ht).2.2 y hyt
    rw [hg] at this
    exact void_no_ans hL hv y this

/-- **A goal completes once a void side of one of its splits does.** The
goal is not neglected; the side is void, and complete in the run whenever it
is not neglected. -/
theorem IsRun.done_of_side (hτ : IsRun τ) {r k : Nat} {g Lg Rg sg : GoalOf R Rel} {kd : Kind}
    (hk : goalAt (τ r) k = some g) (ho : Opened τ k) (hsp : SplitAt g kd Lg Rg) (left : Bool)
    (hsg : sg = if left then Lg else Rg) (hv : Void P sg)
    (hside : ∀ r' j, goalAt (τ r') j = some sg → Opened τ j → EvDone τ j) : EvDone τ k := by
  by_contra hnd
  have hlive : Live τ k := ho.resolve_left hnd
  obtain ⟨r0, hfull, lk⟩ := hτ.live_strat hk hlive
  obtain ⟨gr', hgr', a', b', hga', hgb', -, hxl, hxr⟩ := hfull.split kd Lg Rg hsp
  obtain ⟨side', other, hgside', hx⟩ : ∃ side' other, goalAt (τ r0) side' = some sg ∧
      Strat.push kd left side' other none [] ∈ gr'.kinds := by
    subst hsg
    cases left
    · exact ⟨b', _, by simpa using hgb', hxr⟩
    · exact ⟨a', _, by simpa using hga', hxl⟩
  obtain ⟨Ln, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
  obtain ⟨todo0, subs0, rfl⟩ := kind_push e
  have hoS : Opened τ side' := hτ.opened_of_settled hgside' fun r' => by
    obtain ⟨r2, hr2', hr2, -, hfed, -⟩ := hLn.worked r'
    obtain ⟨todo2, subs2, hs2⟩ := hLn.push_kept h0 (show r0 ≤ r2 + 1 by omega)
    exact ⟨r2, hr2', (hfed _ (List.mem_of_getElem? hs2)).1⟩
  obtain ⟨Td, hTd⟩ := hside r0 side' hgside' hoS
  have hdn : ∀ r1, Td ≤ r1 → (τ r1).isDone side' = true := fun r1 hr1 =>
    ((hτ.stable hr1).isDone hTd).1
  obtain ⟨T1, subs1, hT1, h1⟩ := hLn.push_empty h0 (Nat.le_max_right Td r0)
    (fun r1 hr1 => hdn r1 (by omega))
  have hp1 := hτ.prog hk (hLn.mem T1 (by omega) _ (List.mem_of_getElem? h1))
  dsimp only [Prog] at hp1
  obtain ⟨_, _, -, -, -, -, hsubs1, -⟩ := hp1
  have hnil : subs1 = [] := by
    cases subs1 with
    | nil => rfl
    | cons e l =>
      have := (hsubs1 e List.mem_cons_self).1
      rw [hτ.void_empty hL hgside' hv T1] at this
      cases this
  subst hnil
  have hdone := (hτ.req.req T1).closed [k] (fun k' hk' => by
    obtain rfl := List.mem_singleton.1 hk'
    obtain ⟨subs2, hs2, -, hlen⟩ := hLn.push_fixed (show r0 ≤ T1 by omega) h1 (Nat.le_succ T1)
    obtain rfl : subs2 = [] := List.length_eq_zero_iff.1 hlen
    obtain ⟨t', gs, gr, ht', hg, hgr, hs⟩ :=
      hLn.mem (T1 + 1) (by omega) _ (List.mem_of_getElem? hs2)
    refine ⟨t', ht', gs, hg, gr, hgr, _, hs, ?_, fun _ _ _ _ _ _ e => ?_⟩
    · simp [Strat.quiet, Strat.pending, hdn (T1 + 1) (by omega)]
    · cases e
      exact hdn T1 (by omega)) k (List.mem_singleton.2 rfl)
  exact hnd ⟨T1 + 1, hdone⟩

/-- **Down a meet and back.** If the goal of the meet of some members is void
and complete in the run whenever it is not neglected, so is the goal of the
meet of those and any others: the others are taken away one at a time. -/
theorem IsRun.meet_ladder (hτ : IsRun τ) {A : List Rel} (hA : A ≠ [])
    (hAs : A.Pairwise RelLE) (hbv : Void P (bare (mkAnd A) : GoalOf R Rel))
    (hbd : ∀ r j, goalAt (τ r) j = some (bare (mkAnd A)) → Opened τ j → EvDone τ j) :
    ∀ (n : Nat) (ys C : List Rel), C.length = n → ys.Pairwise RelLE → ys.Perm (A ++ C) →
      (∀ x ∈ ys, NotAnd x) →
      ∀ r j, goalAt (τ r) j = some (bare (mkAnd ys)) → Opened τ j → EvDone τ j := by
  intro n
  induction n with
  | zero =>
    intro ys C hC hs hperm _
    obtain rfl : C = [] := List.length_eq_zero_iff.1 hC
    rw [List.append_nil] at hperm
    obtain rfl : ys = A := eq_of_perm_of_sorted hperm hs hAs
    exact hbd
  | succ n ih =>
    intro ys C hC hs hperm hna r j hj ho
    obtain ⟨c, C', rfl⟩ : ∃ c C', C = c :: C' := by
      cases C with
      | nil => simp at hC
      | cons c C' => exact ⟨c, C', rfl⟩
    have hC' : C'.length = n := by simpa using hC
    have hApos := List.length_pos_iff.2 hA
    have hlen : ys.length = A.length + (C'.length + 1) := by
      rw [hperm.length_eq]
      simp
    obtain ⟨i, hi, hci⟩ := List.getElem_of_mem (hperm.mem_iff.2 (by simp) : c ∈ ys)
    have hs' : (ys.eraseIdx i).Pairwise RelLE := hs.sublist (List.eraseIdx_sublist ys i)
    have hna' : ∀ x ∈ ys.eraseIdx i, NotAnd x := fun x h =>
      hna x (List.mem_of_mem_eraseIdx h)
    have hperm' : (ys.eraseIdx i).Perm (A ++ C') := by
      have h₁ : (ys[i] :: ys.eraseIdx i).Perm ys := List.getElem_cons_eraseIdx_perm hi
      have h₂ : ys.Perm (ys[i] :: (A ++ C')) := by
        rw [hci]
        exact hperm.trans List.perm_middle
      exact (h₁.trans h₂).cons_inv
    have hrest := ih (ys.eraseIdx i) C' hC' hs' hperm' hna'
    have hvoid : Void P (bare (mkAnd (ys.eraseIdx i)) : GoalOf R Rel) :=
      void_mkAnd hL hA hperm' hbv
    by_cases hsplit : i ∈ andSplits ys.length
    · exact hτ.done_of_side hL hj ho (splitAt_mkAnd hna (by omega) hi hsplit) false rfl hvoid
        hrest
    · have h2 : ys.length = 2 ∧ i = 1 := by
        unfold andSplits at hsplit
        split at hsplit
        · simp only [List.mem_singleton] at hsplit
          omega
        · exact absurd (List.mem_range.2 hi) hsplit
      obtain ⟨hl2, rfl⟩ := h2
      have h0 : 0 < ys.length := by omega
      have he : mkAnd (ys.eraseIdx 1) = ys[0] :=
        mkAnd_eraseIdx_one hl2 (List.getElem?_eq_getElem h0)
      rw [he] at hrest hvoid
      exact hτ.done_of_side hL hj ho
        (splitAt_mkAnd hna (by omega) h0 (by unfold andSplits; simp [hl2])) true rfl hvoid
        hrest

end run

section theorems

variable {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  {dom : ∀ S, Domain (R S)} {K : ∀ S, Kernel (R S) Cost} {hK : ∀ S, (K S).Refines (dom S)}
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp)
include hD

/-- The machine halts exactly when the root table completes. -/
theorem terminates_iff {P : Program} {q : Rel} (wf : P.WellFormed q) :
    (Rt dom K hK).Terminates P q ↔ EvDone (sAt dom K hK P q.norm) 0 := by
  have hI := isRun_of_wf (K := K) (hK := hK) hD wf
  constructor
  · rintro ⟨n, hn⟩
    rw [init_eq] at hn
    rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, -, hdj, -⟩
    · simp [Runtime.Halts, Runtime.final, hr] at hn
    · exact ⟨j, hdj⟩
  · rintro ⟨r, hr⟩
    refine ⟨r + 1, ?_⟩
    rw [init_eq]
    rcases run_cases hI (r + 1) with ⟨hall, -⟩ | ⟨j, -, -, hr'⟩
    · have := hall r (Nat.lt_succ_self r)
      rw [hr] at this
      cases this
    · simp [Runtime.Halts, Runtime.final, hr']

/-- A query that halts with no answer relates nothing. -/
theorem pairs_empty {P : Program} {a : Rel} (wf : P.WellFormed a)
    (ht : (Rt dom K hK).Terminates P a) (he : (Rt dom K hK).Answers P a = ∅) :
    P.pairs a = ∅ := by
  obtain ⟨n, hn⟩ := ht
  rw [honestExhaustion (K := K) (hK := hK) hD P a wf n hn]
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 hp
  have : x ∈ (Rt dom K hK).Answers P a := ⟨n, hx⟩
  rw [he] at this
  exact this

/-- **A side that halts with no answer makes `;` and `&` halt**, on either
side. -/
theorem emptySide : (Rt dom K hK).EmptySide := fun P a b wf ht he => by
  have wfa : P.WellFormed a := wf.seq_left
  have wfba : P.WellFormed (.seq b a) := wf.seq_swap
  have wfand : P.WellFormed (.and a b) := wf.and_of_seq
  have wfand' : P.WellFormed (.and b a) := wf.seq_swap.and_of_seq
  have hL := hD _ wf.2.2.1
  have hv : Void P (bare a.norm : GoalOf (R P.sorts) Rel) :=
    void_of_pairs (pairs_empty (K := K) (hK := hK) hD wfa ht he)
  have hσ := isRun_of_wf (K := K) (hK := hK) hD wfa
  obtain ⟨rσ, hrσ⟩ := (terminates_iff (K := K) (hK := hK) hD wfa).1 ht
  -- the goal of `a` completes in every run that does not neglect it
  have side : ∀ {e : Rel}, IsRun (sAt dom K hK P e) → ∀ r j,
      goalAt (sAt dom K hK P e r) j = some (bare a.norm) → Opened (sAt dom K hK P e) j →
      EvDone (sAt dom K hK P e) j := fun hτ r j hj ho =>
    hσ.transfer hL hτ (fun r j => nocov_stateAt r j) (root_at hσ rσ) hrσ hj ho
  have rootO : ∀ {e : Rel} (hτ : IsRun (sAt dom K hK P e)), Opened (sAt dom K hK P e) 0 :=
    fun hτ => hτ.opened_of_settled root_goal0 fun r' =>
      ⟨r', Nat.le_refl _, (hτ.req.req r').root⟩
  have hna : ∀ x ∈ seqParts a.norm ++ seqParts b.norm, NotSeq x := fun x hx =>
    (List.mem_append.1 hx).elim notSeq_of_mem_seqParts notSeq_of_mem_seqParts
  have hna' : ∀ x ∈ seqParts b.norm ++ seqParts a.norm, NotSeq x := fun x hx =>
    (List.mem_append.1 hx).elim notSeq_of_mem_seqParts notSeq_of_mem_seqParts
  have hpa := List.length_pos_iff.2 (seqParts_ne_nil a.norm)
  have hpb := List.length_pos_iff.2 (seqParts_ne_nil b.norm)
  have eA : mkAnd (andParts a.norm) = a.norm := (normal_norm a).mkAnd_andParts
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `a ; b`: the chain is split where the members of `a` end
    have hτ := isRun_of_wf (K := K) (hK := hK) hD wf
    have e₁ : mkSeq ((seqParts a.norm ++ seqParts b.norm).take (seqParts a.norm).length) =
        a.norm := by rw [List.take_left' rfl, (normal_norm a).mkSeq_seqParts]
    refine (terminates_iff (K := K) (hK := hK) hD wf).2 ?_
    exact hτ.done_of_side hL
      (show goalAt (sAt dom K hK P (.seq a b : Rel).norm 0) 0 =
        some (bare (mkSeq (seqParts a.norm ++ seqParts b.norm))) from root_goal0)
      (rootO hτ) (splitAt_mkSeq hna hpa (by simp; omega)) true (by rw [e₁]; rfl) hv (side hτ)
  · -- `b ; a`: the chain is split where the members of `a` begin
    have hτ := isRun_of_wf (K := K) (hK := hK) hD wfba
    have e₁ : mkSeq ((seqParts b.norm ++ seqParts a.norm).drop (seqParts b.norm).length) =
        a.norm := by rw [List.drop_left' rfl, (normal_norm a).mkSeq_seqParts]
    refine (terminates_iff (K := K) (hK := hK) hD wfba).2 ?_
    exact hτ.done_of_side hL
      (show goalAt (sAt dom K hK P (.seq b a : Rel).norm 0) 0 =
        some (bare (mkSeq (seqParts b.norm ++ seqParts a.norm))) from root_goal0)
      (rootO hτ) (splitAt_mkSeq hna' hpb (by simp; omega)) false (by rw [e₁]; rfl) hv
      (side hτ)
  · -- `a & b`: the meet has the members of `a`
    have hτ := isRun_of_wf (K := K) (hK := hK) hD wfand
    refine (terminates_iff (K := K) (hK := hK) hD wfand).2 ?_
    exact hτ.meet_ladder hL (andParts_ne_nil a.norm) (normal_norm a).sorted_andParts
      (by rw [eA]; exact hv) (by rw [eA]; exact side hτ) (andParts b.norm).length
      (sortedParts (andParts a.norm ++ andParts b.norm)) (andParts b.norm) rfl
      (pairwise_sortedParts _) (sortedParts_perm _)
      (fun x hx => (List.mem_append.1 ((sortedParts_perm _).mem_iff.1 hx)).elim
        notAnd_of_mem_andParts notAnd_of_mem_andParts) 0 0
      (show goalAt (sAt dom K hK P (.and a b : Rel).norm 0) 0 = _ from root_goal0) (rootO hτ)
  · -- `b & a`
    have hτ := isRun_of_wf (K := K) (hK := hK) hD wfand'
    refine (terminates_iff (K := K) (hK := hK) hD wfand').2 ?_
    exact hτ.meet_ladder hL (andParts_ne_nil a.norm) (normal_norm a).sorted_andParts
      (by rw [eA]; exact hv) (by rw [eA]; exact side hτ) (andParts b.norm).length
      (sortedParts (andParts b.norm ++ andParts a.norm)) (andParts b.norm) rfl
      (pairwise_sortedParts _) ((sortedParts_perm _).trans List.perm_append_comm)
      (fun x hx => (List.mem_append.1 ((sortedParts_perm _).mem_iff.1 hx)).elim
        notAnd_of_mem_andParts notAnd_of_mem_andParts) 0 0
      (show goalAt (sAt dom K hK P (.and b a : Rel).norm 0) 0 = _ from root_goal0) (rootO hτ)

end theorems

end Symmetric

end RwLog
