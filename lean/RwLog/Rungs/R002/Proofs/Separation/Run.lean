/-
# The separating family: the whole run, and the separation

Both machines start in `st k 0` and take the same `k + 4` rounds through
`st k 1`, ..., `st k (k + 4)`, where the root table is complete.

* R002 pays at most `100 (k + 5)³` per round (`roundBound_le`), so it halts
  within `500 (k + 5)⁴`.
* R001 is still open at depth `k + 1`, and by `baseline_lower` that round
  alone costs at least the number of nodes of the query unfolded `k` times,
  which is at least `2 ^ k` because `w` doubles with every level.

R001 emits nothing in the `k + 2` rounds up to and including that one, so it
has paid `2 ^ k` before any answer arrives; R002 is honest about exhaustion,
so it has covered `(z, z)` by the time it halts. Together with well-formedness
this is obligation `separates`, and the halting bounds are
`separates_exhaustion`.
-/
import RwLog.Rungs.R002.Proofs.Separation.Round
import RwLog.Rungs.R002.Proofs.Lower
import RwLog.Rungs.R002.Proofs.Same
import RwLog.Rungs.Framework.Latency

namespace RwLog

namespace R002

namespace Sep

open Cost R001

/-! ## The steps -/

theorem init_eq (k : Nat) (U : Oracle) :
    (Tabled.machine U).init (sepFam k).1 (sepFam k).2 = st k 0 := by
  show State.ofGoal (prog k) (gR k) = st k 0
  simp [State.ofGoal, norm_gR, st, tabs, slots, tab, goal, ans, hasAns, isDone]

theorem head_tabs (k d : Nat) : (st k d).tables.head? = some (tab k d .root) := by
  obtain ⟨l, hl⟩ := slots_head k d
  simp [st, tabs, hl]

theorem finished_iff (k d : Nat) : (st k d).finished = true ↔ k + 4 ≤ d := by
  simp [State.finished, head_tabs, tab]

/-- A round of R002 while the root is open. -/
theorem step_open (k d : Nat) (h : d < k + 4) :
    Costs (costed.step (st k d)) (.emit (emit k d) (st k (d + 1))) (roundBound k d) := by
  have hf : (st k d).finished = false := by
    rw [Bool.eq_false_iff, ne_eq, finished_iff]; omega
  show Costs (Tabled.step onDemand (st k d)) _ _
  simp only [Tabled.step, hf, Bool.false_eq_true, ↓reduceIte]
  refine Costs.mono (c := roundBound k d + 0) ?_ (by omega)
  exact Costs.bind (round_costs k d) (Costs.pure _)

theorem step_done (k d : Nat) (h : k + 4 ≤ d) (U : Oracle) :
    Costs (Tabled.step U (st k d)) .done 0 := by
  have hf : (st k d).finished = true := (finished_iff k d).2 h
  simp only [Tabled.step, hf, ↓reduceIte]
  exact Costs.pure _

/-- R001 takes the same step. -/
theorem baseline_step_open (k d : Nat) (h : d < k + 4) :
    (baseline.step (st k d)).val = .emit (emit k d) (st k (d + 1)) := by
  have h1 : (baseline.step (st k d)).val = R001.step (st k d) :=
    Tabled.step_val eager eager_exact (st k d)
  have h2 : (costed.step (st k d)).val = R001.step (st k d) :=
    Tabled.step_val onDemand onDemand_exact (st k d)
  rw [h1, ← h2]
  exact (step_open k d h).1

/-! ## What R002 pays -/

theorem roundBound_le (k d : Nat) (h : d < k + 4) : roundBound k d ≤ 100 * (k + 5) ^ 3 := by
  have hn : (slots k d).length ≤ k + 5 := le_trans (length_slots k d) (by omega)
  unfold roundBound
  generalize (slots k d).length = n at hn
  have h1 : n * (2 * d + k + 8) ≤ (k + 5) * (3 * (k + 5)) := Nat.mul_le_mul hn (by omega)
  have h2 : n * (12 * n + 6) ≤ (k + 5) * (12 * (k + 5) + 6) := Nat.mul_le_mul hn (by omega)
  have h3 : n * n ≤ (k + 5) * (k + 5) := Nat.mul_le_mul hn hn
  have h4 : n * (n * (24 * n + 12)) ≤ (k + 5) * ((k + 5) * (24 * (k + 5) + 12)) :=
    Nat.mul_le_mul hn (Nat.mul_le_mul hn (by omega))
  have e : 100 * (k + 5) ^ 3 =
      1 + ((k + 5) * (3 * (k + 5)) + ((k + 5) * (12 * (k + 5) + 6) + ((k + 5) * 96 + ((k + 5) * 6 +
        (36 * ((k + 5) * (k + 5)) + ((k + 5) * ((k + 5) * (24 * (k + 5) + 12)) + 0)))))) +
      (76 * k ^ 3 + 1077 * k ^ 2 + 4962 * k + 7384) := by ring
  rw [e]
  show 1 + (n * (2 * d + k + 8) + (n * (12 * n + 6) + (n * 96 + (n * 6 + (36 * (n * n) +
    (n * (n * (24 * n + 12)) + 0)))))) ≤ _
  omega

/-- From `st k d`, R002 halts after the remaining rounds, having paid at most
`100 (k + 5)³` for each. -/
theorem costed_run (k : Nat) : ∀ (r d : Nat), d + r = k + 4 →
    costed.runtime.Halts (st k d) (r + 1) ∧
      costed.spent (st k d) (r + 1) ≤ r * (100 * (k + 5) ^ 3)
  | 0, d, h => by
    have hs := step_done k d (by omega) onDemand
    have hv : (costed.step (st k d)).val = .done := hs.1
    refine ⟨?_, ?_⟩
    · show (costed.runtime.run (st k d) 1).2 = true
      rw [costed.runtime.run_succ_done hv]
    · rw [costed.spent_succ_done hv]
      have := hs.2
      exact le_trans this (Nat.zero_le _)
  | r + 1, d, h => by
    have hs := step_open k d (by omega)
    have hv : (costed.step (st k d)).val = .emit (emit k d) (st k (d + 1)) := hs.1
    obtain ⟨ih1, ih2⟩ := costed_run k r (d + 1) (by omega)
    refine ⟨?_, ?_⟩
    · show (costed.runtime.run (st k d) (r + 1 + 1)).2 = true
      rw [costed.runtime.run_succ_emit hv]
      exact ih1
    · rw [costed.spent_succ_emit hv]
      have h1 := hs.2
      have h2 := roundBound_le k d (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem costed_halts (k : Nat) :
    costed.runtime.Halts (costed.init (sepFam k).1 (sepFam k).2) (k + 5) ∧
      costed.spent (costed.init (sepFam k).1 (sepFam k).2) (k + 5) ≤ 500 * (k + 5) ^ 4 := by
  have hi : costed.init (sepFam k).1 (sepFam k).2 = st k 0 := init_eq k onDemand
  rw [hi]
  obtain ⟨h1, h2⟩ := costed_run k (k + 4) 0 (by omega)
  refine ⟨h1, le_trans h2 ?_⟩
  have e : 500 * (k + 5) ^ 4 = (k + 4) * (100 * (k + 5) ^ 3) +
      (400 * (k + 5) ^ 4 + 100 * (k + 5) ^ 3) := by ring
  omega

/-! ## What R001 pays -/

/-- `w` doubles with every level of unfolding. -/
theorem nodes_w (k : Nat) : ∀ d, 2 ^ d ≤ nodes (R000.unfoldN (prog k) d (.call "w"))
  | 0 => by simp [nodes]
  | d + 1 => by
    have ih := nodes_w k d
    rw [R000.unfoldN_call, body_w, R000.unfoldN_or]
    simp only [nodes, pow_succ]
    omega

theorem nodes_root (k : Nat) : 2 ^ k ≤ nodes (R000.unfoldN (prog k) k (gR k).rel) := by
  have h := nodes_w k k
  have e : (gR k).rel = .or (.call (chainName k)) (.call "w") := rfl
  rw [e, R000.unfoldN_or]
  simp only [nodes]
  omega

/-- The round of R001 at depth `k + 1` costs at least `2 ^ k`. -/
theorem baseline_round (k : Nat) : 2 ^ k ≤ (baseline.step (st k (k + 1))).ticks := by
  have h := baseline_lower (st k (k + 1)) (tab k (k + 1) .root) (head_tabs k (k + 1))
    (by simp [tab, isDone]) k (by simp [st])
  exact le_trans (nodes_root k) h

/-- A halting run of R001 from `st k d` passes through depth `k + 1`. -/
theorem baseline_run (k : Nat) : ∀ (r d : Nat), d + r = k + 1 → ∀ n,
    baseline.runtime.Halts (st k d) n → 2 ^ k ≤ baseline.spent (st k d) n
  | _, _, _, 0, hn => by simp [Runtime.Halts, Runtime.run] at hn
  | 0, d, h, n + 1, _ => by
    have hd : d = k + 1 := by omega
    subst hd
    have hv := baseline_step_open k (k + 1) (by omega)
    rw [baseline.spent_succ_emit hv]
    exact le_trans (baseline_round k) (Nat.le_add_right _ _)
  | r + 1, d, h, n + 1, hn => by
    have hv := baseline_step_open k d (by omega)
    have hn' : baseline.runtime.Halts (st k (d + 1)) n := by
      unfold Runtime.Halts at hn ⊢
      rw [baseline.runtime.run_succ_emit hv] at hn
      exact hn
    rw [baseline.spent_succ_emit hv]
    exact le_trans (baseline_run k r (d + 1) (by omega) n hn') (Nat.le_add_left _ _)

/-- R001 emits nothing in the rounds up to depth `k + 1`. -/
theorem baseline_quiet (k : Nat) : ∀ (r d : Nat), d + r ≤ k + 2 →
    baseline.runtime.emitted (st k d) r = []
  | 0, _, _ => rfl
  | r + 1, d, h => by
    have hv := baseline_step_open k d (by omega)
    have ih := baseline_quiet k r (d + 1) (by omega)
    have he : emit k d = [] := by simp [emit]; omega
    show (baseline.runtime.run (st k d) (r + 1)).1 = []
    rw [baseline.runtime.run_succ_emit hv, he]
    exact ih

/-- R001 has paid `2 ^ k` once it has been through depth `k + 1`. -/
theorem baseline_spent (k : Nat) : ∀ (r d : Nat), d + r = k + 1 →
    2 ^ k ≤ baseline.spent (st k d) (r + 1)
  | 0, d, h => by
    have hd : d = k + 1 := by omega
    subst hd
    have hv := baseline_step_open k (k + 1) (by omega)
    rw [baseline.spent_succ_emit hv]
    exact le_trans (baseline_round k) (Nat.le_add_right _ _)
  | r + 1, d, h => by
    have hv := baseline_step_open k d (by omega)
    rw [baseline.spent_succ_emit hv]
    exact le_trans (baseline_spent k r (d + 1) (by omega)) (Nat.le_add_left _ _)

/-- R001 has paid `2 ^ k` at any step at which it has emitted an answer. -/
theorem baseline_late (k : Nat) {n : Nat} {a : Span}
    (ha : a ∈ baseline.runtime.emitted (baseline.init (sepFam k).1 (sepFam k).2) n) :
    2 ^ k ≤ baseline.spent (baseline.init (sepFam k).1 (sepFam k).2) n := by
  have hi : baseline.init (sepFam k).1 (sepFam k).2 = st k 0 := init_eq k eager
  rw [hi] at ha ⊢
  exact baseline.le_spent_of_covered (N := k + 1) (baseline_quiet k (k + 1) 0 (by omega))
    (baseline_spent k (k + 1) 0 (by omega)) ha

/-! ## The pair the query relates -/

theorem sem_chain (k : Nat) (M : Interp) : ∀ j, j ≤ k →
    ((.sym "z", .sym "z") : GTerm × GTerm) ∈ (prog k).meaningAt M (chainName j)
  | 0, _ => by
    rw [Program.meaningAt_eq, body_zero]
    exact ⟨fun _ => .sym "z", rfl, rfl, by simp⟩
  | j + 1, h => by
    rw [Program.meaningAt_eq, body_succ (by omega)]
    exact sem_chain k M j (by omega)

theorem sem_target (k : Nat) (M : Interp) {x : GTerm × GTerm} (hx : x ∈ sepTarget) :
    x ∈ (sepFam k).1.semAt M (sepFam k).2 := by
  obtain rfl : x = (.sym "z", .sym "z") := hx
  exact Or.inl (sem_chain k M k le_rfl)

/-! ## The size of the input -/

theorem size_le (k : Nat) : (sepFam k).1.size + (sepFam k).2.size ≤ 2 * k + 11 := by
  have h : ∀ n : Nat, ((List.range n).map fun i =>
      1 + (Rel.call (chainName i)).size).sum = 2 * n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [Rel.size]; omega
  have e : (sepFam k).1.size + (sepFam k).2.size = 2 * k + 11 := by
    simp only [sepFam, Program.size, sepDefs, List.map_append, List.map_map, List.sum_append,
      Function.comp_def, h k]
    simp [Rel.size, Rel.at_, Rel.rw, Span.size, Term.size, Store.size, Theory.size]
    omega
  exact e.le

theorem model_nil (k : Nat) : (sepFam k).1.theory.Model ∅ := by
  intro ρ h
  exact absurd h List.not_mem_nil

end Sep

/-- On `sepFam k`, R002 has covered `(z, z)` within `500 (k + 5)⁴` ticks, and
R001 has paid at least `2 ^ k` at any step at which it has covered it. -/
theorem separates : Obligation.separates := by
  intro k
  refine ⟨Sep.wellFormed k, Sep.size_le k, ⟨∅, Sep.model_nil k⟩, ⟨_, rfl⟩, ?_⟩
  intro M hM x hx
  obtain ⟨hh, hs⟩ := Sep.costed_halts k
  refine ⟨costed.coversWithin_of_halts honest_exhaustion (Sep.wellFormed k) hh hs hM
    (Sep.sem_target k M hx), ?_⟩
  rintro n ⟨a, ha, -⟩
  exact Sep.baseline_late k ha

/-- On `sepFam k`, R002 halts within `500 (k + 5)⁴` ticks, and R001 has paid
at least `2 ^ k` whenever it has halted. -/
theorem separates_exhaustion : Obligation.separates_exhaustion := by
  intro k
  refine ⟨Sep.wellFormed k, Sep.size_le k, ⟨k + 5, Sep.costed_halts k⟩, ?_⟩
  intro n hn
  have hi : baseline.init (sepFam k).1 (sepFam k).2 = Sep.st k 0 := Sep.init_eq k eager
  rw [hi] at hn ⊢
  exact Sep.baseline_run k (k + 1) 0 (by omega) n hn

end R002

end RwLog
