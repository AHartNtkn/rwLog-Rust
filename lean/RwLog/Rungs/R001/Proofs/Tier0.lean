/-
# Rung R001, Tier 0 and answer quality

Soundness, completeness up to refutation, honest exhaustion,
derivation-general answers (P0.1 to P0.3, P3.0), refuted spans cut at once
(P2.4), no subsumed answers and finitely many answers on halting queries
(P3.1 to P3.3).

All of them read the invariant every reachable table satisfies (`TInv`,
`Tier0/Inv.lean`, preserved by a round in `Tier0/Comp.lean`), and
completeness also reads fairness (`Tier0/Fair.lean`). They assume three
kernel obligations: simplification is exact and runs to the end, and
symbolic refutation is monotone.
-/
import RwLog.Rungs.R001.Proofs.Tier0.Fair
import Mathlib.Data.Set.Finite.Basic

namespace RwLog

namespace R001

open Tier0

/-- A run follows its rounds, and the runtime's initial state is a goal's. -/
theorem init_eq (P : Program) (q : Rel) : runtime.init P q = State.ofGoal P ⟨none, q, none⟩ := rfl

namespace Tier0

theorem root_goal (P : Program) (q : Rel) (k : Nat) :
    ∃ h : 0 < (iter (State.ofGoal P ⟨none, q, none⟩) k).tables.length,
      (iter (State.ofGoal P ⟨none, q, none⟩) k).tables[0].goal = (Goal.norm ⟨none, q, none⟩).2 := by
  obtain ⟨h, hg, -⟩ := iter_ext_le (State.ofGoal P ⟨none, q, none⟩) (Nat.zero_le k) 0
    (by simp [iter, State.ofGoal])
  exact ⟨h, hg⟩

theorem rootAns_iter (st : State) (k : Nat) (h : 0 < (iter st k).tables.length) :
    rootAns (iter st k) = (iter st k).tables[0].answers := by
  unfold rootAns
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h]
  rfl

theorem finished_iter (st : State) (k : Nat) (h : 0 < (iter st k).tables.length)
    (hf : (iter st k).finished = true) : (iter st k).tables[0].done = true := by
  unfold State.finished at hf
  rwa [List.head?_eq_getElem?, List.getElem?_eq_getElem h] at hf

/-- What a run has emitted after `n` steps is the root table's answers after
some `k ≤ n` rounds, oriented; if the run halted, that table is complete. -/
theorem emitted_root (P : Program) (q : Rel) (n : Nat) :
    ∃ k, ∃ h : 0 < (iter (State.ofGoal P ⟨none, q, none⟩) k).tables.length,
      runtime.emitted (runtime.init P q) n =
        orient (Goal.norm ⟨none, q, none⟩).1 (iter (State.ofGoal P ⟨none, q, none⟩) k).tables[0].answers ∧
      stateAfter (runtime.init P q) n = iter (State.ofGoal P ⟨none, q, none⟩) k ∧
      (runtime.Halts (runtime.init P q) n → (iter (State.ofGoal P ⟨none, q, none⟩) k).tables[0].done = true) ∧
      ((iter (State.ofGoal P ⟨none, q, none⟩) k).tables[0].done = true ∨ k = n) := by
  set st := State.ofGoal P ⟨none, q, none⟩
  have hne : st.tables ≠ [] := by simp [st, State.ofGoal]
  obtain ⟨e1, -, e3⟩ := run_root n st hne
  have hk : ∃ k, stateAfter st n = iter st k ∧
      ((runtime.run st n).2 = true → (iter st k).finished = true) ∧
      ((iter st k).finished = true ∨ k = n) := by
    rcases stateAfter_cases st n with ⟨k, -, hf, h⟩ | ⟨-, h⟩
    · exact ⟨k, h, fun _ => hf, .inl hf⟩
    · exact ⟨n, h, fun hr => h ▸ e3 hr, .inr rfl⟩
  obtain ⟨k, hk, hf, hkn⟩ := hk
  obtain ⟨h0, -⟩ := root_goal P q k
  refine ⟨k, h0, ?_, hk, fun hh => finished_iter st k h0 (hf hh), ?_⟩
  · unfold Runtime.emitted
    rw [init_eq, e1, hk, rootAns_iter st k h0]
    simp [st, State.ofGoal, rootAns]
  · rcases hkn with h | h
    · exact .inl (finished_iter st k h0 h)
    · exact .inr h

section
variable (hSE : Obligation.simplify_exact) (hSS : Obligation.simplify_stable)
  (hRM : Obligation.refutes_mono)
include hSE hSS hRM

theorem tinv_root {P : Program} {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) (k : Nat) :
    TInv P (iter (State.ofGoal P ⟨none, q, none⟩) k).tables :=
  tinv_iter hSE hSS hRM (st := State.ofGoal P ⟨none, q, none⟩) hwf
    (tinv_ofGoal (goodG_root q) ⟨fun _ h => (by simp at h), fun _ h => (by simp at h)⟩) k

/-- Every emitted answer refines one derivation of the query. -/
theorem emitted_ref {P : Program} {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {n : Nat} {a : Span}
    (ha : a ∈ runtime.emitted (runtime.init P q) n) :
    ∃ s, Derives P q s ∧ Ref P.theory a s.den := by
  obtain ⟨k, h0, he, -, -, -⟩ := emitted_root P q n
  rw [he, orient_eq, List.mem_map] at ha
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨_, hg⟩ := root_goal P q k
  obtain ⟨s, hs, hr⟩ := (tinv_root hSE hSS hRM hwf k).ref _ (List.getElem_mem h0) a₀ ha₀
  rw [hg] at hs hr
  obtain ⟨hd, heq⟩ := norm_back ⟨none, q, none⟩ hs
  refine ⟨_, hd, ?_⟩
  have := ref_oS (Goal.norm ⟨none, q, none⟩).1 hr
  rwa [← heq, gden_root] at this

/-- A complete root covers every derivation of the query. -/
theorem root_done_dc {P : Program} {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {k : Nat}
    (h0 : 0 < (iter (State.ofGoal P ⟨none, q, none⟩) k).tables.length)
    (hd : (iter (State.ofGoal P ⟨none, q, none⟩) k).tables[0].done = true) {s : Span}
    (hs : Derives P q s) :
    DC P.theory (orient (Goal.norm ⟨none, q, none⟩).1
      (iter (State.ofGoal P ⟨none, q, none⟩) k).tables[0].answers) s.den := by
  obtain ⟨w, hw⟩ := dw_of_derives hs
  obtain ⟨w', s', h1, -, h4⟩ := norm_meas (P := P) ⟨none, q, none⟩ hw
  rw [gden_root] at h4
  rw [h4]
  apply dc_orient
  obtain ⟨_, hgk⟩ := root_goal P q k
  have := (tinv_root hSE hSS hRM hwf k).comp _ (List.getElem_mem h0) hd s' (by rw [hgk]; exact h1.derives)
  rwa [hgk] at this

/-- After `k₀` rounds, or once the run halts, the root covers a derivation for
good: what the run has emitted after `k₀` steps covers it. -/
theorem emitted_dc {P : Program} {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {s : Span}
    (hs : Derives P q s) :
    ∃ n, DC P.theory (runtime.emitted (runtime.init P q) n) s.den := by
  set st := State.ofGoal P ⟨none, q, none⟩
  have hI := tinv_root hSE hSS hRM (q := q) hwf
  obtain ⟨w, hw⟩ := dw_of_derives hs
  obtain ⟨w', s', h1, -, h4⟩ := norm_meas (P := P) ⟨none, q, none⟩ hw
  rw [gden_root] at h4
  obtain ⟨h00, hg0⟩ := root_goal P q 0
  rw [← hg0] at h1
  obtain ⟨k₀, hk₀⟩ := fair hSE hSS hRM (st := st) hwf (hI 0) _ 0 0 h00 w' s' h1 le_rfl
  refine ⟨k₀, ?_⟩
  obtain ⟨k, h0, he, -, -, hkn⟩ := emitted_root P q k₀
  rw [he, h4]
  apply dc_orient
  obtain ⟨_, hgk⟩ := root_goal P q k
  have hdc : DC P.theory (iter st k).tables[0].answers (GDen (iter st 0).tables[0].goal s'.den) := by
    rcases hkn with hd | rfl
    · have := (hI k).comp _ (List.getElem_mem h0) hd s' (by rw [hgk, ← hg0]; exact h1.derives)
      rwa [hgk, ← hg0] at this
    · obtain ⟨_, hdc⟩ := hk₀ k le_rfl
      exact hdc
  rwa [hg0] at hdc

end

end Tier0

open Tier0

section
variable (hSE : Obligation.simplify_exact) (hSS : Obligation.simplify_stable)
  (hRM : Obligation.refutes_mono)
include hSE hSS hRM

/-- P0.1: every emitted answer denotes only triples of the query, up to the
theory. -/
theorem sound : Obligation.sound := by
  intro P q hP n a ha
  obtain ⟨s, hs, hr⟩ := emitted_ref hSE hSS hRM hP.2.2 ha
  exact Tier0.Backed.trans hr.1 (GRel.Backed.of_subset hs.den_subset)

/-- P3.0: every emitted answer refines the span of one derivation. -/
theorem derivation_general : Obligation.derivation_general := by
  intro P q hP a ⟨n, ha⟩
  obtain ⟨s, hs, hr⟩ := emitted_ref hSE hSS hRM hP.2.2 ha
  exact ⟨s, hs, hr.1, Lifting.coversLive_iff.2 hr.2⟩

/-- P0.2: every derivable span is covered by an emitted answer, unless it is
dead. -/
theorem complete : Obligation.complete := by
  intro P q hP s hs
  obtain ⟨n, hdc⟩ := emitted_dc hSE hSS hRM hP.2.2 hs
  rcases hdc with hd | ⟨a, ha, hdom⟩
  · exact .inl (deadR_den.1 hd)
  · exact .inr ⟨n, a, ha, Lifting.coversLive_iff.2 hdom⟩

/-- P0.3: on halting, the emitted answers are equivalent to the query. -/
theorem honest_exhaustion : Obligation.honest_exhaustion := by
  intro P q hP n hh
  obtain ⟨k, h0, he, -, hd, -⟩ := emitted_root P q n
  have hcov : ∀ s, Derives P q s → DC P.theory (runtime.emitted (runtime.init P q) n) s.den := by
    intro s hs; rw [he]; exact root_done_dc hSE hSS hRM hP.2.2 h0 (hd hh) hs
  have hback : ∀ a ∈ runtime.emitted (runtime.init P q) n, (a.den).Backed P.theory (P.sem q) := by
    intro a ha
    obtain ⟨s, hs, hr⟩ := emitted_ref hSE hSS hRM hP.2.2 ha
    exact Tier0.Backed.trans hr.1 (GRel.Backed.of_subset hs.den_subset)
  intro C
  ext ⟨u, v⟩
  simp only [GRel.liveIn, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨S, hS, hn⟩
    rw [sem_eq_derivable, mem_derivable] at hS
    obtain ⟨s, hs, hx⟩ := hS
    have hnS : ¬ Refutes P.theory S := fun h => hn (h.mono Finset.subset_union_left)
    rcases hcov s hs with hdead | ⟨a, ha, hdom⟩
    · exact absurd (hdead _ hx) hnS
    · obtain ⟨Y, hy, hns⟩ := hdom _ _ _ hx hnS
      exact ⟨Y, Set.mem_iUnion₂.2 ⟨a, ha, hy⟩, fun h => hn (hns C h)⟩
  · rintro ⟨S, hS, hn⟩
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 hS
    obtain ⟨⟨x₁, x₂, X⟩, hx', e1, e2, hns⟩ := hback a ha _ hx
    simp only at e1 e2 hns
    subst e1 e2
    exact ⟨X, hx', fun h => hn (hns C h)⟩

/-- P2.4: no table of a reachable state holds a refuted answer or has a
refuted boundary. -/
theorem prompt_pruning : Obligation.prompt_pruning := by
  intro P q hP n t ht
  obtain ⟨k, -, -, hsa, -, -⟩ := emitted_root P q n
  rw [hsa] at ht
  have hI := tinv_root hSE hSS hRM (q := q) hP.2.2 k
  refine ⟨hI.unref t ht, fun b hb => ?_⟩
  simp only [List.mem_append, Option.mem_toList] at hb
  rcases hb with hb | hb
  · exact (hI.bu t ht).1 b hb
  · exact (hI.bu t ht).2 b hb

/-- P3.1, P3.2: no emitted answer is covered by an earlier one. -/
theorem no_subsumed : Obligation.no_subsumed := by
  intro P q hP n
  obtain ⟨k, h0, he, -, -, -⟩ := emitted_root P q n
  rw [he, orient_eq]
  refine List.Pairwise.map _ (fun a b hab hc => ?_)
    ((tinv_root hSE hSS hRM (q := q) hP.2.2 k).pw _ (List.getElem_mem h0))
  cases hf : (Goal.norm ⟨none, q, none⟩).1
  · rw [hf] at hc
    simp only [oS, Bool.false_eq_true, ite_false] at hc
    exact absurd (covers?_complete hc) (by simp [hab])
  · rw [hf] at hc
    have := covers_swap hc
    simp only [oS, ite_true, Span.swap_swap] at this
    exact absurd (covers?_complete this) (by simp [hab])

end

/-- Emitting only appends. -/
theorem Runtime.run_prefix (R : Runtime) : ∀ (m j : Nat) (s : R.State),
    ∃ r, (R.run s (m + j)).1 = (R.run s m).1 ++ r
  | 0, j, s => ⟨(R.run s j).1, by simp [Runtime.run]⟩
  | m + 1, j, s => by
    rw [show m + 1 + j = (m + j) + 1 by omega]
    simp only [Runtime.run]
    split
    · rename_i as s' _
      obtain ⟨r, hr⟩ := Runtime.run_prefix R m j s'
      exact ⟨r, by rw [hr, List.append_assoc]⟩
    · exact ⟨[], by simp⟩

/-- P3.3: a halting query has finitely many answers. -/
theorem finite_answers : Obligation.finite_answers := by
  intro P q _ ⟨n, hn⟩
  refine (List.finite_toSet (runtime.emitted (runtime.init P q) n)).subset ?_
  rintro a ⟨m, ha⟩
  show a ∈ runtime.emitted (runtime.init P q) n
  rcases le_total m n with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨r, hr⟩ := Runtime.run_prefix runtime m j (runtime.init P q)
    unfold Runtime.emitted at ha ⊢
    rw [hr]; exact List.mem_append_left _ ha
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    unfold Runtime.emitted at ha ⊢
    rwa [runtime.run_halted hn j] at ha

end R001

end RwLog
