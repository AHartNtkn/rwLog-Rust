/-
# The separating family: the race on each goal

What R003's unfolding race returns and spends on the goals of the run. The
race costs at most 7 times the shared evaluation, which is quadratic. Its
answer is the walk's or the shared evaluation's: the same spans, but the walk
repeats them, `2 ^ (j + 1)` answers on `cRel j`. The walk can only win the
race when it costs at most twice the shared evaluation, and from `j = 5` on it
costs more than that, so the race never returns more than 32 answers.
-/
import RwLog.Rungs.R003.Proofs.Separation.Walk
import RwLog.Rungs.R003.Proofs.Separation.SharedEval

namespace RwLog

namespace R003

namespace Sep

open Cost R000 R001 R002

/-! ## Who wins a race -/

/-- From a budget that the second computation's cost has not been seen to
fit under twice, the race returns the second result, or the first when the
first costs at most twice the second. -/
theorem raceFrom_cases {α : Type} (x y : Cost α) : ∀ (n b : Nat), x.ticks - b ≤ n →
    b ≤ 2 * y.ticks →
    (raceFrom x y b).val = y.val ∨ ((raceFrom x y b).val = x.val ∧ x.ticks ≤ 2 * y.ticks)
  | n, b, hn, hb => by
    rw [raceFrom]
    by_cases hx : x.ticks ≤ b
    · right
      refine ⟨?_, by omega⟩
      simp [withinP, within, hx]
    · by_cases hy : y.ticks ≤ b
      · left
        simp [withinP, within, hx, hy]
      · cases n with
        | zero => omega
        | succ n =>
          have ih := raceFrom_cases x y n (2 * b + 1) (by omega) (by omega)
          simpa [withinP, within, hx, hy] using ih

theorem race_cases {α : Type} (x y : Cost α) :
    (race x y).val = y.val ∨ ((race x y).val = x.val ∧ x.ticks ≤ 2 * y.ticks) :=
  raceFrom_cases x y x.ticks 0 (by omega) (by omega)

/-! ## The walk loses on large members of the family -/

theorem sharedBound_succ (j : Nat) : sharedBound (j + 1) = sharedBound j + 32 * j + 157 := by
  unfold sharedBound; ring

theorem sharedBound_mono : ∀ {j k : Nat}, j ≤ k → sharedBound j ≤ sharedBound k := by
  intro j k h
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [sharedBound_succ]; omega

/-- From `j = 5` on, the walk costs more than twice the shared evaluation. -/
theorem walk_loses : ∀ j, 5 ≤ j → 2 * sharedBound j < 2 ^ j * (16 * j + 3) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    have e : 2 ^ (j + 1) * (16 * (j + 1) + 3) = 2 * (2 ^ j * (16 * j + 3)) + 32 * 2 ^ j := by ring
    have hb : 141 * j + 104 ≤ sharedBound j := by unfold sharedBound; omega
    rw [sharedBound_succ, e]
    omega

/-! ## The race on `cRel j` -/

/-- The most answers the race returns on a goal of the run for `sepFam k`. -/
def ansBound (k : Nat) : Nat := min 32 (2 ^ (k + 1))

theorem ansBound_mono {j k : Nat} (h : j ≤ k) : ansBound j ≤ ansBound k := by
  unfold ansBound
  have : 2 ^ (j + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem two_le_ansBound (k : Nat) : 2 ≤ ansBound k := by
  unfold ansBound
  have : 2 ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The race on `cRel j`: at most 7 times the shared evaluation; final; only
the two spans, `$x -> z` among them; at most `ansBound j` answers. -/
theorem unfolder_gC (hr : Obligation.race_ticks) (hs : Obligation.shared_exact) (d j : Nat) :
    (unfolder P0 d (gC j)).ticks ≤ 7 * sharedBound j ∧ (unfolder P0 d (gC j)).val.1 = true ∧
      (∀ x ∈ (unfolder P0 d (gC j)).val.2, Good x) ∧ xz ∈ (unfolder P0 d (gC j)).val.2 ∧
      (unfolder P0 d (gC j)).val.2.length ≤ ansBound j := by
  obtain ⟨sv, st⟩ := shared_gC d j
  obtain ⟨w1, w2, w3⟩ := onDemand_gC d j
  have hex := R002.onDemand_exact P0 d (gC j)
  have hsx := hs P0 d (gC j)
  rw [sv] at hsx
  have hdup : (unfoldAnswers P0 d (gC j)).eraseDups = [xz, zz] := (congrArg Prod.snd hsx).symm
  have hmem : ∀ x, x ∈ (onDemand P0 d (gC j)).val.2 ↔ x = xz ∨ x = zz := by
    intro x
    rw [hex, ← List.mem_eraseDups, hdup]
    simp
  have hlen2 : 2 ≤ ansBound j := two_le_ansBound j
  refine ⟨?_, ?_⟩
  · have := hr _ (onDemand P0 d (gC j)) (shared P0 d (gC j))
    show (Cost.race _ _).ticks ≤ _
    omega
  · show (Cost.race (onDemand P0 d (gC j)) (shared P0 d (gC j))).val.1 = true ∧ _
    rcases race_cases (onDemand P0 d (gC j)) (shared P0 d (gC j)) with h | ⟨h, hle⟩
    · show _ ∧ (∀ x ∈ (Cost.race (onDemand P0 d (gC j)) (shared P0 d (gC j))).val.2, Good x) ∧
        xz ∈ (Cost.race (onDemand P0 d (gC j)) (shared P0 d (gC j))).val.2 ∧
        (Cost.race (onDemand P0 d (gC j)) (shared P0 d (gC j))).val.2.length ≤ _
      rw [h, sv]
      refine ⟨rfl, ?_, by simp, by simpa using hlen2⟩
      intro x hx
      simpa [Good] using hx
    · show _ ∧ (∀ x ∈ (Cost.race (onDemand P0 d (gC j)) (shared P0 d (gC j))).val.2, Good x) ∧
        xz ∈ (Cost.race (onDemand P0 d (gC j)) (shared P0 d (gC j))).val.2 ∧
        (Cost.race (onDemand P0 d (gC j)) (shared P0 d (gC j))).val.2.length ≤ _
      rw [h]
      refine ⟨w1, fun x hx => (hmem x).1 hx, (hmem xz).2 (Or.inl rfl), ?_⟩
      have hj : j < 5 := by
        by_contra hj
        have := walk_loses j (by omega)
        omega
      unfold ansBound
      have : 2 ^ (j + 1) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
      omega

/-! ## The race on one span -/

theorem onDemand_gS (d : Nat) {s : Span} (hs : Good s) : (onDemand P0 d (gS s)).val = (true, [s]) := by
  have hrel : (gS s).rel = .span s := rfl
  have hl : RwLog.live [] s = [s] := (live_good hs).1
  rw [onDemand, hrel, walk]
  simp [R002.alive, aliveL, aliveR, toRel, Rel.calls, derivs, hl]

theorem unfolder_gS (hr : Obligation.race_ticks) (d : Nat) {s : Span} (hs : Good s) :
    (unfolder P0 d (gS s)).ticks ≤ 56 ∧ (unfolder P0 d (gS s)).val = (true, [s]) := by
  obtain ⟨sv, st⟩ := shared_gS d hs
  refine ⟨?_, ?_⟩
  · have := hr _ (onDemand P0 d (gS s)) (shared P0 d (gS s))
    show (Cost.race _ _).ticks ≤ _
    omega
  · show (Cost.race (onDemand P0 d (gS s)) (shared P0 d (gS s))).val = _
    rcases race_cases (onDemand P0 d (gS s)) (shared P0 d (gS s)) with h | ⟨h, -⟩
    · rw [h, sv]
    · rw [h, onDemand_gS d hs]

end Sep

end R003

end RwLog
