/-
# Rung zero is correct

* `sound`: every emitted answer denotes only triples of the query.
* `complete`: every derivable span with a ground instance is covered by one
  emitted answer after finitely many steps.
* `honest_exhaustion`: when the machine reports it is done, the emitted
  answers cover the query exactly.
* `terminates`: the machine reports it is done on every finitely normalising
  query (some number of unfoldings leaves a finite union of spans).
-/
import RwLog.Rungs.R000.Engine
import Mathlib.Data.Nat.Find

namespace RwLog

namespace R000

variable {P : Program} {q : Rel}

/-! ## Rounds -/

theorem roundFinal_iff {k : Nat} :
    roundFinal P q k = true ↔ ∀ p ∈ products P q k, (toRel p).calls = [] := by
  simp [roundFinal, List.all_eq_true]

theorem roundSpans_sound {k : Nat} {a : Span} (h : a ∈ roundSpans P q k) : a.den ⊆ P.sem q := by
  simp only [roundSpans, List.mem_flatMap] at h
  obtain ⟨p, hp, ha⟩ := h
  have hd : Derives P (toRel p) a := (mem_derivs.1 ha).derives
  refine hd.den_subset.trans ?_
  have := norm_sound P.meaning false (unfoldN P k q) p hp
  rw [← sem_unfoldN k q]
  exact this

theorem roundSpans_cover {k n : Nat} {s : Span} (h : DerivesN P (n + k) q s)
    (hne : (s.den).Nonempty) (hk : n = 0 ∨ roundFinal P q k = true) :
    ∃ a ∈ roundSpans P q k, s.den ⊆ a.den := by
  have h' := derivesN_unfoldN k n h
  obtain ⟨p, hp, s', hs', hsub⟩ := norm_complete h' false hne
  have h0 : DerivesN P 0 (toRel p) s' := by
    rcases hk with rfl | hk
    · exact hs'
    · exact derivesN_zero_of_callFree hs' (roundFinal_iff.1 hk p hp)
  exact ⟨s', List.mem_flatMap.2 ⟨p, hp, mem_derivs.2 h0⟩, hsub⟩

/-! ## Running the machine -/

theorem run_queue (st : State) (n : Nat) :
    runtime.run st (st.queue.length + n) =
      (st.queue ++ (runtime.run { st with queue := [] } n).1,
        (runtime.run { st with queue := [] } n).2) := by
  obtain ⟨P, q, k, l⟩ := st
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons]
    rw [show l.length + 1 + n = (l.length + n) + 1 by omega]
    simp only [Runtime.run, runtime, step]
    simp only [runtime] at ih
    rw [ih]; rfl

theorem run_empty (P : Program) (q : Rel) (k n : Nat) :
    runtime.run ⟨P, q, k, []⟩ (n + 1) =
      if roundFinal P q k then ([], true) else runtime.run (State.start P q (k + 1)) n := by
  by_cases hk : roundFinal P q k = true <;> simp [Runtime.run, runtime, step, hk]

theorem run_start_final {k : Nat} (hk : roundFinal P q k = true) :
    runtime.run (State.start P q k) ((roundSpans P q k).length + 1) = (roundSpans P q k, true) := by
  have := run_queue (State.start P q k) 1
  simp only [State.start] at this ⊢
  rw [this, run_empty, hk]
  simp

theorem run_start_next {k : Nat} (hk : roundFinal P q k = false) (n : Nat) :
    runtime.run (State.start P q k) ((roundSpans P q k).length + 1 + n) =
      (roundSpans P q k ++ (runtime.run (State.start P q (k + 1)) n).1,
        (runtime.run (State.start P q (k + 1)) n).2) := by
  have := run_queue (State.start P q k) (1 + n)
  simp only [State.start] at this ⊢
  rw [Nat.add_assoc, this, Nat.add_comm 1 n, run_empty]
  simp only [hk, Bool.false_eq_true, ite_false]
  rfl

/-- Reaching round `k`, when no earlier round is final. -/
theorem reach (k : Nat) (hk : ∀ j < k, roundFinal P q j = false) :
    ∃ N pre, k ≤ N ∧ ∀ n, runtime.run (State.start P q 0) (N + n) =
      (pre ++ (runtime.run (State.start P q k) n).1, (runtime.run (State.start P q k) n).2) := by
  induction k with
  | zero => exact ⟨0, [], le_rfl, fun n => by simp⟩
  | succ k ih =>
    obtain ⟨N, pre, hN, hrun⟩ := ih (fun j hj => hk j (by omega))
    refine ⟨N + ((roundSpans P q k).length + 1), pre ++ roundSpans P q k, by omega, fun n => ?_⟩
    rw [Nat.add_assoc, hrun, run_start_next (hk k (by omega))]
    simp

theorem run_sound_aux : ∀ (n : Nat) (st : State),
    (∀ a ∈ st.queue, a ∈ roundSpans st.P st.q st.round) →
    ∀ a ∈ (runtime.run st n).1, ∃ j, a ∈ roundSpans st.P st.q j
  | 0, _, _, a, ha => by simp [Runtime.run] at ha
  | n + 1, ⟨P, q, k, l⟩, hst, a, ha => by
    cases l with
    | cons b l =>
      simp only [Runtime.run, runtime, step, List.cons_append, List.nil_append, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨k, hst _ (List.mem_cons_self ..)⟩
      · exact run_sound_aux n ⟨P, q, k, l⟩ (fun x hx => hst x (List.mem_cons_of_mem _ hx)) a ha
    | nil =>
      rw [run_empty] at ha
      split at ha
      · simp at ha
      · exact run_sound_aux n (State.start P q (k + 1)) (fun x hx => hx) a ha

/-! ## The theorems -/

/-- Rung zero's answers denote only triples of the query, exactly. -/
theorem sound_subset {P : Program} {q : Rel} {n : Nat} {a : Span}
    (ha : a ∈ runtime.emitted (runtime.init P q) n) : a.den ⊆ P.sem q := by
  obtain ⟨j, hj⟩ := run_sound_aux n (State.start P q 0) (fun x hx => hx) a ha
  exact roundSpans_sound hj

theorem sound : runtime.Sound :=
  fun _ _ _ _ _ ha => GRel.Backed.of_subset (sound_subset ha)

theorem complete : runtime.Complete := by
  intro P q _ s hs
  have hne := Span.den_nonempty s
  obtain ⟨d, hd⟩ := hs.derivesN
  have hex : ∃ j, roundFinal P q j = true ∨ j = d := ⟨d, Or.inr rfl⟩
  classical
  let j := Nat.find hex
  have hj : roundFinal P q j = true ∨ j = d := Nat.find_spec hex
  have hjd : j ≤ d := Nat.find_min' hex (Or.inr rfl)
  have hbefore : ∀ i < j, roundFinal P q i = false := by
    intro i hi
    have := Nat.find_min hex hi
    simp only [not_or] at this
    simpa using this.1
  obtain ⟨N, pre, _, hrun⟩ := reach j hbefore
  obtain ⟨a, ha, hsub⟩ := roundSpans_cover (n := d - j) (k := j)
    (by rw [Nat.sub_add_cancel hjd]; exact hd) hne
    (by rcases hj with h | h
        · exact Or.inr h
        · exact Or.inl (by omega))
  refine Or.inr ⟨N + (roundSpans P q j).length, a, ?_, (Span.Covers.of_den_subset hsub).live⟩
  show a ∈ (runtime.run (State.start P q 0) _).1
  rw [hrun]
  have := run_queue (State.start P q j) 0
  rw [Nat.add_zero] at this
  change a ∈ pre ++ (runtime.run (State.start P q j) (State.start P q j).queue.length).1
  rw [this]
  simp [State.start, ha]

/-- When the machine halts, it has completed a final round, and has emitted
everything that round emits. -/
theorem halted_final {n : Nat} (h : runtime.Halts (runtime.init P q) n) :
    ∃ k, roundFinal P q k = true ∧ ∀ a ∈ roundSpans P q k, a ∈ runtime.emitted (runtime.init P q) n := by
  classical
  have hex : ∃ j, roundFinal P q j = true := by
    by_contra hno
    simp only [not_exists] at hno
    obtain ⟨N, pre, hN, hrun⟩ := reach (P := P) (q := q) (n + 1)
      (fun j _ => by simpa using hno j)
    have h1 := runtime.run_halted h (N - n)
    rw [show n + (N - n) = N + 0 by omega] at h1
    change runtime.run (State.start P q 0) (N + 0) = _ at h1
    have h2 := congrArg Prod.snd (hrun 0)
    rw [h1] at h2
    unfold Runtime.Halts at h
    rw [h] at h2
    exact absurd h2 (by simp [Runtime.run])
  let j := Nat.find hex
  have hj : roundFinal P q j = true := Nat.find_spec hex
  have hbefore : ∀ i < j, roundFinal P q i = false := by
    intro i hi; simpa using Nat.find_min hex hi
  obtain ⟨N, pre, _, hrun⟩ := reach j hbefore
  have hfin := hrun ((roundSpans P q j).length + 1)
  rw [run_start_final hj] at hfin
  have hh : runtime.Halts (runtime.init P q) (N + ((roundSpans P q j).length + 1)) := by
    unfold Runtime.Halts; change (runtime.run (State.start P q 0) _).2 = true; rw [hfin]
  have heq := runtime.run_halted_eq h hh
  refine ⟨j, hj, fun a ha => ?_⟩
  unfold Runtime.emitted
  rw [heq]; change a ∈ (runtime.run (State.start P q 0) _).1; rw [hfin]
  simp [ha]

/-- Rung zero's exhaustion is exact: the emitted answers carry exactly the
triples of the query. -/
theorem honest_exhaustion_eq {n : Nat} (h : runtime.Halts (runtime.init P q) n) :
    P.sem q = ⋃ a ∈ runtime.emitted (runtime.init P q) n, a.den := by
  apply le_antisymm
  · obtain ⟨k, hk, hall⟩ := halted_final h
    intro x hx
    rw [sem_eq_derivable] at hx
    obtain ⟨s, hs, hxs⟩ := mem_derivable.1 hx
    obtain ⟨d, hd⟩ := hs.derivesN
    obtain ⟨a, ha, hsub⟩ := roundSpans_cover (n := max d k - k) (k := k)
      (by rw [Nat.sub_add_cancel (le_max_right d k)]; exact hd.mono (le_max_left d k))
      ⟨x, hxs⟩ (Or.inr hk)
    exact Set.mem_biUnion (hall a ha) (hsub hxs)
  · exact Set.iUnion₂_subset fun a ha => sound_subset ha

theorem honest_exhaustion : runtime.HonestExhaustion := by
  intro P q hwf n h M
  rw [honest_exhaustion_eq h]

/-- The machine reports it is done exactly when some round is final. -/
theorem terminates_iff : runtime.Terminates P q ↔ ∃ k, roundFinal P q k = true := by
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨k, hk, _⟩ := halted_final h
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    classical
    have hex : ∃ j, roundFinal P q j = true := ⟨k, hk⟩
    let j := Nat.find hex
    have hj : roundFinal P q j = true := Nat.find_spec hex
    have hbefore : ∀ i < j, roundFinal P q i = false := by
      intro i hi; simpa using Nat.find_min hex hi
    obtain ⟨N, pre, _, hrun⟩ := reach j hbefore
    refine ⟨N + ((roundSpans P q j).length + 1), ?_⟩
    unfold Runtime.Halts; change (runtime.run (State.start P q 0) _).2 = true
    rw [hrun, run_start_final hj]

theorem terminates : runtime.TerminatesOn FinitelyNormalising :=
  fun _ _ _ ⟨k, hk⟩ => terminates_iff.2 ⟨k, roundFinal_iff.2 hk⟩

/-! ## Everything a run emits -/

theorem run_answers_aux : ∀ (n : Nat) (st : State),
    (∀ j < st.round, roundFinal st.P st.q j = false) →
    (∀ a ∈ st.queue, a ∈ roundSpans st.P st.q st.round) →
    ∀ a ∈ (runtime.run st n).1,
      ∃ k, (∀ j < k, roundFinal st.P st.q j = false) ∧ a ∈ roundSpans st.P st.q k
  | 0, _, _, _, a, ha => by simp [Runtime.run] at ha
  | n + 1, ⟨P, q, k, l⟩, hpre, hst, a, ha => by
    cases l with
    | cons b l =>
      simp only [Runtime.run, runtime, step, List.cons_append, List.nil_append, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨k, hpre, hst _ (List.mem_cons_self ..)⟩
      · exact run_answers_aux n ⟨P, q, k, l⟩ hpre (fun x hx => hst x (List.mem_cons_of_mem _ hx)) a ha
    | nil =>
      rw [run_empty] at ha
      split at ha
      · simp at ha
      · rename_i hk
        refine run_answers_aux n (State.start P q (k + 1)) (fun j hj => ?_) (fun x hx => hx) a ha
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hpre j hj
        · simpa [State.start] using hk

/-- The answers of a run are exactly the spans of the rounds up to the
first final one. -/
theorem mem_answers {a : Span} :
    a ∈ runtime.Answers P q ↔ ∃ k, (∀ j < k, roundFinal P q j = false) ∧ a ∈ roundSpans P q k := by
  constructor
  · rintro ⟨n, ha⟩
    exact run_answers_aux n (State.start P q 0) (fun j hj => absurd hj (Nat.not_lt_zero j))
      (fun x hx => hx) a ha
  · rintro ⟨k, hk, ha⟩
    obtain ⟨N, pre, _, hrun⟩ := reach k hk
    refine ⟨N + (roundSpans P q k).length, ?_⟩
    show a ∈ (runtime.run (State.start P q 0) _).1
    rw [hrun]
    have := run_queue (State.start P q k) 0
    rw [Nat.add_zero] at this
    change a ∈ pre ++ (runtime.run (State.start P q k) (State.start P q k).queue.length).1
    rw [this]
    simp [State.start, ha]

end R000

end RwLog
