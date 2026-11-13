/-
# Rung R001, Tier 0 and answer quality

Soundness, completeness up to dead spans, honest exhaustion,
derivation-general answers (P0.1 to P0.3, P3.0), refuted spans cut at once
(P2.4), no subsumed answers and finitely many answers on halting queries
(P3.1 to P3.3). The table invariants shared with the termination group are
in `Tier0/Tables.lean`.

All of them read the invariant every reachable table satisfies (`TInv`,
`Tier0/Inv.lean`, preserved by a round in `Tier0/Comp.lean`), and
completeness also reads fairness (`Tier0/Fair.lean`). They assume that
simplification is exact; `prompt_pruning` also assumes that it runs to the end
(`UInv`).
-/
import RwLog.Rungs.R001.Proofs.Tier0.Tables
import RwLog.Rungs.Framework.Tier0

namespace RwLog

namespace R001

open Tier0

/-- A run follows its rounds, and the runtime's initial state is a goal's. -/
theorem init_eq (P : Program) (q : Rel) : runtime.init P q = StateOf.ofGoal P ⟨none, q, none⟩ := rfl

namespace Tier0

theorem root_goal (P : Program) (q : Rel) (k : Nat) :
    ∃ h : 0 < (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables.length,
      (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables[0].goal = (GoalOf.norm ⟨none, q, none⟩).2 := by
  obtain ⟨h, hg, -⟩ := iter_ext_le (StateOf.ofGoal P ⟨none, q, none⟩) (Nat.zero_le k) 0
    (by simp [iter, StateOf.ofGoal])
  exact ⟨h, hg⟩

theorem rootAns_iter (st : State) (k : Nat) (h : 0 < (iter st k).tables.length) :
    rootAns (iter st k) = (iter st k).tables[0].answers := by
  unfold rootAns
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h]
  rfl

theorem finished_iter (st : State) (k : Nat) (h : 0 < (iter st k).tables.length)
    (hf : (iter st k).finished = true) : (iter st k).tables[0].done = true := by
  unfold StateOf.finished at hf
  rwa [List.head?_eq_getElem?, List.getElem?_eq_getElem h] at hf

/-- What a run has emitted after `n` steps is the root table's answers after
some `k ≤ n` rounds, oriented; if the run halted, that table is complete. -/
theorem emitted_root (P : Program) (q : Rel) (n : Nat) :
    ∃ k, ∃ h : 0 < (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables.length,
      runtime.emitted (runtime.init P q) n =
        orient (GoalOf.norm ⟨none, q, none⟩).1 (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables[0].answers ∧
      stateAfter (runtime.init P q) n = iter (StateOf.ofGoal P ⟨none, q, none⟩) k ∧
      (runtime.Halts (runtime.init P q) n → (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables[0].done = true) ∧
      ((iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables[0].done = true ∨ k = n) := by
  set st := StateOf.ofGoal P ⟨none, q, none⟩
  have hne : st.tables ≠ [] := by simp [st, StateOf.ofGoal]
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
    simp [st, StateOf.ofGoal, rootAns]
  · rcases hkn with h | h
    · exact .inl (finished_iter st k h0 h)
    · exact .inr h

section

theorem tinv_root {P : Program} {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) (k : Nat) :
    TInv P (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables :=
  tinv_iter (st := StateOf.ofGoal P ⟨none, q, none⟩) hwf (tinv_ofGoal (goodG_root q)) k

/-- Every emitted answer refines one derivation of the query. -/
theorem emitted_ref {P : Program} {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {n : Nat} {a : Span}
    (ha : a ∈ runtime.emitted (runtime.init P q) n) :
    ∃ s, Derives P q s ∧ Ref P.theory a s.den := by
  obtain ⟨k, h0, he, -, -, -⟩ := emitted_root P q n
  rw [he, orient_eq, List.mem_map] at ha
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨_, hg⟩ := root_goal P q k
  obtain ⟨s, hs, hr⟩ := (tinv_root hwf k).ref _ (List.getElem_mem h0) a₀ ha₀
  rw [hg] at hs hr
  obtain ⟨hd, heq⟩ := norm_back ⟨none, q, none⟩ hs
  refine ⟨_, hd, ?_⟩
  have := ref_oS (GoalOf.norm ⟨none, q, none⟩).1 hr
  rwa [← heq, gden_root] at this

/-- A complete root covers every derivation of the query. -/
theorem root_done_dc {P : Program} {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {k : Nat}
    (h0 : 0 < (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables.length)
    (hd : (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables[0].done = true) {s : Span}
    (hs : Derives P q s) :
    DC P.theory (orient (GoalOf.norm ⟨none, q, none⟩).1
      (iter (StateOf.ofGoal P ⟨none, q, none⟩) k).tables[0].answers) s.den := by
  obtain ⟨w, hw⟩ := dw_of_derives hs
  obtain ⟨w', s', h1, -, h4⟩ := norm_meas (P := P) ⟨none, q, none⟩ hw
  rw [gden_root] at h4
  rw [h4]
  apply dc_orient
  obtain ⟨_, hgk⟩ := root_goal P q k
  have := (tinv_root hwf k).comp _ (List.getElem_mem h0) hd s' (by rw [hgk]; exact h1.derives)
  rwa [hgk] at this

/-- After `k₀` rounds, or once the run halts, the root covers a derivation for
good: what the run has emitted after `k₀` steps covers it. -/
theorem emitted_dc {P : Program} {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {s : Span}
    (hs : Derives P q s) :
    ∃ n, DC P.theory (runtime.emitted (runtime.init P q) n) s.den := by
  set st := StateOf.ofGoal P ⟨none, q, none⟩
  have hI := tinv_root (q := q) hwf
  obtain ⟨w, hw⟩ := dw_of_derives hs
  obtain ⟨w', s', h1, -, h4⟩ := norm_meas (P := P) ⟨none, q, none⟩ hw
  rw [gden_root] at h4
  obtain ⟨h00, hg0⟩ := root_goal P q 0
  rw [← hg0] at h1
  obtain ⟨k₀, hk₀⟩ := fair (st := st) hwf (hI 0) _ 0 0 h00 w' s' h1 le_rfl
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

/-- The Tier 0 certificate: every emitted answer stands for a derivation of
the query, every derivation is eventually dead or covered, and a complete root
covers every derivation. -/
theorem cert : runtime.Tier0Cert where
  sound := Runtime.Tier0Cert.sound_of_ref fun _ _ hP _ _ ha => emitted_ref hP.2.2 ha
  cover _ _ hP _ hs := emitted_dc hP.2.2 hs
  exhaust P q hP n hh s hs := by
    obtain ⟨k, h0, he, -, hd, -⟩ := emitted_root P q n
    rw [he]; exact root_done_dc hP.2.2 h0 (hd hh) hs

/-- P0.1: in every model of the theory, every emitted answer relates only
pairs the query relates. -/
theorem sound : Obligation.sound := cert.toSound

/-- P3.0: every emitted answer refines the span of one derivation. -/
theorem derivation_general : Obligation.derivation_general :=
  Runtime.derivationGeneral_of_ref fun _ _ hP _ _ ha => emitted_ref hP.2.2 ha

/-- P0.2: every derivable span is covered by an emitted answer, unless it is
dead. -/
theorem complete : Obligation.complete := cert.toComplete

/-- P0.3: on halting, the emitted answers are equivalent to the query. -/
theorem honest_exhaustion : Obligation.honest_exhaustion := cert.toHonest

/-- P2.3: adding rules to the theory only removes answers. -/
theorem theory_mono_answers : Obligation.theory_mono_answers :=
  Runtime.theory_mono_answers derivation_general complete

/-- P3.1, P3.2: no emitted answer is covered by an earlier one. -/
theorem no_subsumed : Obligation.no_subsumed := by
  intro P q hP n
  obtain ⟨k, h0, he, -, -, -⟩ := emitted_root P q n
  rw [he, orient_eq]
  refine List.Pairwise.map _ (fun a b hab hc => ?_)
    ((tinv_root (q := q) hP.2.2 k).pw _ (List.getElem_mem h0))
  cases hf : (GoalOf.norm ⟨none, q, none⟩).1
  · rw [hf] at hc
    simp only [oS, Bool.false_eq_true, ite_false] at hc
    exact absurd (covers?_complete hc) (by simp [hab])
  · rw [hf] at hc
    have := covers_swap hc
    simp only [oS, ite_true, Span.swap_swap] at this
    exact absurd (covers?_complete this) (by simp [hab])

end

/-- P2.4: no table of a reachable state holds a refuted answer or has a
refuted boundary. -/
theorem prompt_pruning : Obligation.prompt_pruning := by
  intro P q hP n t ht
  obtain ⟨k, -, -, hsa, -, -⟩ := emitted_root P q n
  rw [hsa] at ht
  have hI := uinv_iter (st := StateOf.ofGoal P ⟨none, q, none⟩) hP.2.2
    (uinv_ofGoal ⟨fun _ h => (by simp at h), fun _ h => (by simp at h)⟩) k
  refine ⟨hI.unref t ht, fun b hb => ?_⟩
  simp only [List.mem_append, Option.mem_toList] at hb
  rcases hb with hb | hb
  · exact (hI.bu t ht).1 b hb
  · exact (hI.bu t ht).2 b hb

/-- P3.3: a halting query has finitely many answers. -/
theorem finite_answers : Obligation.finite_answers := fun _ _ _ h => runtime.finite_answers h

end R001

end RwLog
