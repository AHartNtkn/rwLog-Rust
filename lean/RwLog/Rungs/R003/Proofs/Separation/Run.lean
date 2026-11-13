/-
# The separating family: the whole run, and the separation

Both machines start with the root table alone.

* R003's first round puts `$x -> z` in the root table and creates at most two
  tables; in its second round the root gains nothing and completes. The two
  rounds cost at most `2000 (k + 2)³`.
* R002's first round runs its walk on the root, which goes through all
  `2 ^ (k + 1)` products and costs at least `2 ^ k`.

Together with well-formedness this is obligation `separates`.
-/
import RwLog.Rungs.R003.Proofs.Separation.Round
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases

namespace RwLog

namespace R003

namespace Sep

open Cost R001

/-! ## The first state -/

theorem norm_root (k : Nat) : (⟨none, sepRel k, none⟩ : Goal).norm = (false, gC k) := by
  have h := norm_gC k
  simp only [Goal.norm, canon_cRel, canon_sepRel] at h ⊢
  exact h

theorem init_eq (k : Nat) (U : Oracle) :
    (Tabled.machine U).init (sepFam k).1 (sepFam k).2 = ⟨P0, tabs k [] [], false, 0⟩ := by
  show State.ofGoal P0 ⟨none, sepRel k, none⟩ = _
  simp [State.ofGoal, norm_root]

/-! ## What R003 pays -/

theorem roundBound_mono {k m n : Nat} (h : m ≤ n) : roundBound k m ≤ roundBound k n := by
  unfold roundBound lookBound
  gcongr

theorem freshBound_le (k : Nat) : 4 * freshBound (ansBound k + 1) ≤ 300 * (k + 2) ^ 3 := by
  by_cases hk : k < 4
  · interval_cases k <;> decide
  · have h1 : ansBound k + 1 ≤ 33 := by unfold ansBound; omega
    have h2 := freshBound_mono h1
    have h3 : freshBound 33 = 13200 := by decide
    have h4 : 6 ^ 3 ≤ (k + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega

/-- The two rounds cost at most `2000 (k + 2)³`. -/
theorem rounds_le (k : Nat) : roundBound k 1 + roundBound k 3 ≤ 2000 * (k + 2) ^ 3 := by
  have hf := freshBound_le k
  have e : (k + 2) ^ 3 = k * k * k + 6 * (k * k) + 12 * k + 8 := by ring
  have e2 : 16 * k * k = 16 * (k * k) := by ring
  unfold roundBound lookBound keyBound raceBound sharedBound
  rw [e] at hf ⊢
  rw [e2]
  generalize freshBound (ansBound k + 1) = F at hf ⊢
  generalize k * k * k = c at hf ⊢
  generalize k * k = b at hf ⊢
  omega

theorem step_emit {U : Oracle} {st : State} (h : st.finished = false) :
    (Tabled.step U st).val = .emit (Tabled.round U st).val.2 (Tabled.round U st).val.1 ∧
      (Tabled.step U st).ticks = (Tabled.round U st).ticks := by
  simp [Tabled.step, h]

theorem step_done {U : Oracle} {st : State} (h : st.finished = true) :
    (Tabled.step U st).val = .done ∧ (Tabled.step U st).ticks = 0 := by
  simp [Tabled.step, h]

/-- R003 halts after two rounds, within `2000 (k + 2)³`. -/
theorem costed_halts (k : Nat) :
    costed.runtime.Halts (costed.init (sepFam k).1 (sepFam k).2) 3 ∧
      costed.spent (costed.init (sepFam k).1 (sepFam k).2) 3 ≤ 2000 * (k + 2) ^ 3 := by
  have hi : costed.init (sepFam k).1 (sepFam k).2 = ⟨P0, tabs k [] [], false, 0⟩ :=
    init_eq k unfolder
  rw [hi]
  obtain ⟨t1, dn, tl, e1, h1, -⟩ := round_spends k 0 (a0 := []) (rest := []) (Or.inl rfl)
    (fun _ h => by simp at h)
  obtain ⟨hdn, htl⟩ := h1 rfl
  obtain ⟨hlen, hrest⟩ := htl rfl
  subst hdn
  obtain ⟨t2, dn2, tl2, e2, -, h2⟩ := round_spends k 1 (a0 := [xz]) (rest := tl) (Or.inr rfl) hrest
  have hdn2 := h2 rfl
  subst hdn2
  have s1 := step_emit (U := unfolder) (st := ⟨P0, tabs k [] [], false, 0⟩) rfl
  have s2 := step_emit (U := unfolder) (st := ⟨P0, tabs k [xz] tl, false, 1⟩) rfl
  have s3 := step_done (U := unfolder) (st := ⟨P0, ⟨gC k, [xz], true⟩ :: tl2, false, 1 + 1⟩) rfl
  rw [e1] at s1
  rw [e2] at s2
  have v1 : (costed.step ⟨P0, tabs k [] [], false, 0⟩).val = _ := s1.1
  have v2 : (costed.step ⟨P0, tabs k [xz] tl, false, 0 + 1⟩).val = _ := s2.1
  have v3 : (costed.step ⟨P0, ⟨gC k, [xz], true⟩ :: tl2, false, 1 + 1⟩).val = _ := s3.1
  refine ⟨?_, ?_⟩
  · show (costed.runtime.run _ 3).2 = true
    have r1 : costed.runtime.step ⟨P0, tabs k [] [], false, 0⟩ = _ := v1
    have r2 : costed.runtime.step ⟨P0, tabs k [xz] tl, false, 0 + 1⟩ = _ := v2
    have r3 : costed.runtime.step ⟨P0, ⟨gC k, [xz], true⟩ :: tl2, false, 1 + 1⟩ = _ := v3
    rw [costed.runtime.run_succ_emit r1, costed.runtime.run_succ_emit r2,
      costed.runtime.run_succ_done r3]
  · rw [costed.spent_succ_emit v1, costed.spent_succ_emit v2, costed.spent_succ_done v3]
    have t1' : (costed.step ⟨P0, tabs k [] [], false, 0⟩).ticks = _ := s1.2
    have t2' : (costed.step ⟨P0, tabs k [xz] tl, false, 0 + 1⟩).ticks = _ := s2.2
    have t3' : (costed.step ⟨P0, ⟨gC k, [xz], true⟩ :: tl2, false, 1 + 1⟩).ticks = _ := s3.2
    rw [t1', t2', t3']
    have hm : roundBound k (tl.length + 1) ≤ roundBound k 3 := roundBound_mono (by omega)
    have := rounds_le k
    simp only [List.length_nil, Nat.zero_add] at t1
    omega

/-! ## What R002 pays -/

/-- R002's first round costs at least its walk on the root. -/
theorem r002_first (k : Nat) :
    2 ^ k ≤ (R002.costed.step ⟨P0, tabs k [] [], false, 0⟩).ticks := by
  obtain ⟨-, -, hw⟩ := onDemand_gC 0 k
  obtain ⟨K, hK⟩ := Tabled.round_split ⟨P0, tabs k [] [], false, 0⟩
  have s1 := (step_emit (U := R002.onDemand) (st := ⟨P0, tabs k [] [], false, 0⟩) rfl).2
  have e : (R002.costed.step ⟨P0, tabs k [] [], false, 0⟩).ticks = _ := s1
  rw [e, hK R002.onDemand]
  simp only [bind_ticks, tick_ticks, mapL, Tabled.ask, Bool.false_eq_true, ↓reduceIte, pure_ticks]
  have h3 : 2 ^ k ≤ 2 ^ k * (16 * k + 3) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem spent_ge_step (C : CostedRuntime) (s : C.State) (n : Nat) :
    (C.step s).ticks ≤ C.spent s (n + 1) := by
  cases hs : (C.step s).val with
  | done => rw [C.spent_succ_done hs]
  | emit as s' => rw [C.spent_succ_emit hs]; omega

end Sep

/-- On `sepFam k`, R003 halts within `2000 (k + 2)³` ticks, and R002 has paid
at least `2 ^ k` whenever it has halted. -/
theorem separates : Obligation.separates := by
  intro k
  refine ⟨Sep.wellFormed k, ⟨3, Sep.costed_halts k⟩, ?_⟩
  intro n hn
  have hi : R002.costed.init (sepFam k).1 (sepFam k).2 = ⟨Sep.P0, Sep.tabs k [] [], false, 0⟩ :=
    Sep.init_eq k R002.onDemand
  rw [hi] at hn ⊢
  cases n with
  | zero => simp [Runtime.Halts, Runtime.run] at hn
  | succ n => exact le_trans (Sep.r002_first k) (Sep.spent_ge_step _ _ n)

end R003

end RwLog
