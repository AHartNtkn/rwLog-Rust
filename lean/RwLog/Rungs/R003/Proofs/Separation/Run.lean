/-
# The separating family: the whole run, and the separation

Both machines start with the root table alone.

* R003's first round puts `$x -> z` in the root table and creates at most two
  tables; in its second round the root gains nothing and completes. The two
  rounds cost at most `2000 (k + 2)³`.
* R002's first round runs its walk on the root, which goes through all
  `2 ^ (k + 1)` products and costs at least `2 ^ k`.

R002 emits nothing before that round is paid for, and R003 is honest about
exhaustion, so it has covered every pair of the query by the time it halts.
Together with well-formedness this is obligation `separates`, and the halting
bounds are `separates_exhaustion`.
-/
import RwLog.Rungs.R003.Proofs.Separation.Round
import RwLog.Rungs.Framework.Latency
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
    (Tabled.machine U).start (sepFam k).1 (sepFam k).2 = ⟨P0, tabs k [] [], false, 0⟩ := by
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
    costed.runtime.Halts (costed.start (sepFam k).1 (sepFam k).2) 3 ∧
      costed.spent (costed.start (sepFam k).1 (sepFam k).2) 3 ≤ 2000 * (k + 2) ^ 3 := by
  have hi : costed.start (sepFam k).1 (sepFam k).2 = ⟨P0, tabs k [] [], false, 0⟩ :=
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

/-! ## The pairs the query relates -/

theorem sem_target (M : Interp) {x : GTerm × GTerm} (hx : x ∈ sepTarget) :
    ∀ k, x ∈ (sepFam k).1.semAt M (sepFam k).2
  | 0 => Or.inr ⟨fun _ => x.1, rfl, hx, by simp⟩
  | k + 1 => by
    have ih : ((.sym "z", .sym "z") : GTerm × GTerm) ∈ (sepFam k).1.semAt M (sepFam k).2 :=
      sem_target M (x := (.sym "z", .sym "z")) rfl k
    exact ⟨.sym "z", Or.inr ⟨fun _ => x.1, rfl, rfl, by simp⟩, hx ▸ ih⟩

/-! ## The size of the input -/

theorem size_sepRel : ∀ k, (sepRel k).size = 8 * k + 7
  | 0 => by simp [sepRel, twoWays, Rel.size, Rel.at_, Rel.rw, Span.size, Term.size, Store.size]
  | k + 1 => by
    have ih := size_sepRel k
    have h0 := size_sepRel 0
    simp only [sepRel, Rel.size] at ih h0 ⊢
    omega

theorem size_le (k : Nat) : (sepFam k).1.size + (sepFam k).2.size ≤ 8 * k + 7 := by
  have e : (sepFam k).1.size = 0 := by simp [sepFam, Program.size, Theory.size]
  have := size_sepRel k
  simp only [sepFam] at e ⊢
  omega

theorem model_nil (k : Nat) : (sepFam k).1.theory.Model ∅ := by
  intro ρ h
  exact absurd h List.not_mem_nil

end Sep

/-- On `sepFam k`, R003 has covered every pair `(t, z)` within `2000 (k + 2)³`
ticks, and R002 has paid at least `2 ^ k` at any step at which it has covered
one. -/
theorem separates : Obligation.separates := by
  intro k
  refine ⟨Sep.wellFormed k, Sep.size_le k, ⟨∅, Sep.model_nil k⟩, ⟨(.sym "z", .sym "z"), rfl⟩, ?_⟩
  intro M hM x hx
  obtain ⟨hh, hs⟩ := Sep.costed_halts k
  refine ⟨costed.coversWithin_of_halts honest_exhaustion (Sep.wellFormed k) hh
    (le_of_eq_of_le (Tabled.paid_eq unfolder _ _ _) hs) hM (Sep.sem_target M hx k), ?_⟩
  rintro n ⟨a, ha, -⟩
  have hi : R002.costed.start (sepFam k).1 (sepFam k).2 = ⟨Sep.P0, Sep.tabs k [] [], false, 0⟩ :=
    Sep.init_eq k R002.onDemand
  have hp : R002.costed.paid (sepFam k).1 (sepFam k).2 n =
      R002.costed.spent (R002.costed.start (sepFam k).1 (sepFam k).2) n :=
    Tabled.paid_eq R002.onDemand _ _ n
  rw [hp]
  rw [hi] at ha ⊢
  exact R002.costed.le_spent_of_covered (N := 0) rfl
    (le_trans (Sep.r002_first k) (Sep.spent_ge_step _ _ 0)) ha

/-- On `sepFam k`, R003 halts within `2000 (k + 2)³` ticks, and R002 has paid
at least `2 ^ k` whenever it has halted. -/
theorem separates_exhaustion : Obligation.separates_exhaustion := by
  intro k
  obtain ⟨hh, hs⟩ := Sep.costed_halts k
  refine ⟨Sep.wellFormed k, Sep.size_le k,
    ⟨3, hh, le_of_eq_of_le (Tabled.paid_eq unfolder _ _ _) hs⟩, ?_⟩
  intro n hn
  have hi : R002.costed.start (sepFam k).1 (sepFam k).2 = ⟨Sep.P0, Sep.tabs k [] [], false, 0⟩ :=
    Sep.init_eq k R002.onDemand
  have hp : R002.costed.paid (sepFam k).1 (sepFam k).2 n =
      R002.costed.spent (R002.costed.start (sepFam k).1 (sepFam k).2) n :=
    Tabled.paid_eq R002.onDemand _ _ n
  rw [hp]
  rw [hi] at hn ⊢
  cases n with
  | zero => simp [Runtime.Halts, Runtime.run] at hn
  | succ n => exact le_trans (Sep.r002_first k) (Sep.spent_ge_step _ _ n)

end R003

end RwLog
