/-
# Tier 0 proofs, part 10: runs

`iter st k` runs `k` rounds unconditionally. A run of the machine follows it
until the root table is complete (`stateAfter_cases`), and what a run emits is
the root table's answers, oriented by the root's flip (`run_root`). Along
`iter`, tables keep their place and goal and only gain answers, and every
goal a table reads has a table one round later.
-/
import RwLog.Rungs.R001.Proofs.Tier0.Comp

namespace RwLog

namespace R001

namespace Tier0

/-- `k` rounds. -/
def iter (st : State) : Nat → State
  | 0 => st
  | k + 1 => (round (iter st k)).1

theorem iter_P (st : State) : ∀ k, (iter st k).P = st.P
  | 0 => rfl
  | k + 1 => (round_P _).trans (iter_P st k)

theorem iter_flip (st : State) : ∀ k, (iter st k).rootFlip = st.rootFlip
  | 0 => rfl
  | k + 1 => (round_rootFlip _).trans (iter_flip st k)

theorem iter_add (st : State) (k : Nat) : ∀ m, iter (iter st k) m = iter st (k + m)
  | 0 => rfl
  | m + 1 => by simp only [iter, iter_add st k m]; rfl

theorem iter_succ' (st : State) : ∀ k, iter (round st).1 k = iter st (k + 1)
  | 0 => rfl
  | k + 1 => by simp only [iter, iter_succ' st k]

theorem tinv_iter {st : State}
    (hwf : ∀ ρ ∈ st.P.theory, ρ.WellFormed) (hI : TInv st.P st.tables) :
    ∀ k, TInv st.P (iter st k).tables
  | 0 => hI
  | k + 1 => by
    have h := tinv_round (st := iter st k) (by rw [iter_P]; exact hwf)
      (by rw [iter_P]; exact tinv_iter hwf hI k)
    rw [iter_P] at h
    exact h

theorem uinv_iter {st : State}
    (hwf : ∀ ρ ∈ st.P.theory, ρ.WellFormed) (hU : UInv st.P st.tables) :
    ∀ k, UInv st.P (iter st k).tables
  | 0 => hU
  | k + 1 => by
    have h := uinv_round (st := iter st k) (by rw [iter_P]; exact hwf)
      (by rw [iter_P]; exact uinv_iter hwf hU k)
    rw [iter_P] at h
    exact h

/-! ## Tables only grow -/

/-- `t'` is `t` later: the same goal, more answers, and complete if `t` was. -/
def Ext (t t' : Table) : Prop :=
  t'.goal = t.goal ∧ (∃ r, t'.answers = t.answers ++ r) ∧ (t.done = true → t'.done = true)

theorem Ext.refl (t : Table) : Ext t t := ⟨rfl, ⟨[], by simp⟩, id⟩

theorem Ext.trans {t t' t'' : Table} (h : Ext t t') (h' : Ext t' t'') : Ext t t'' := by
  obtain ⟨g, ⟨r, hr⟩, d⟩ := h
  obtain ⟨g', ⟨r', hr'⟩, d'⟩ := h'
  exact ⟨g'.trans g, ⟨r ++ r', by rw [hr', hr, List.append_assoc]⟩, d' ∘ d⟩

theorem ext_after (st : State) (i : Nat) (t : Table) : Ext t (after st i t) :=
  ⟨after_goal _ _ _, ⟨_, after_answers _ _ _⟩, fun h => by rw [after_done, h]; rfl⟩

theorem iter_getElem_succ (st : State) (k i : Nat) (hi : i < (iter st k).tables.length) :
    ∃ hi' : i < (iter st (k + 1)).tables.length,
      (iter st (k + 1)).tables[i] = after (iter st k) i (iter st k).tables[i] := by
  have h := round_getElem (iter st k) i hi
  have hi' : i < (iter st (k + 1)).tables.length := (List.getElem?_eq_some_iff.1 h).1
  refine ⟨hi', ?_⟩
  have := (List.getElem?_eq_some_iff.1 h).2
  exact this

theorem iter_ext (st : State) (k i : Nat) (hi : i < (iter st k).tables.length) :
    ∀ m, ∃ hi' : i < (iter st (k + m)).tables.length,
      Ext (iter st k).tables[i] (iter st (k + m)).tables[i]
  | 0 => ⟨hi, Ext.refl _⟩
  | m + 1 => by
    obtain ⟨h1, e1⟩ := iter_ext st k i hi m
    obtain ⟨h2, e2⟩ := iter_getElem_succ st (k + m) i h1
    refine ⟨h2, ?_⟩
    show Ext _ (iter st (k + m + 1)).tables[i]
    rw [e2]
    exact e1.trans (ext_after _ _ _)

theorem iter_ext_le (st : State) {k k' : Nat} (hk : k ≤ k') (i : Nat)
    (hi : i < (iter st k).tables.length) :
    ∃ hi' : i < (iter st k').tables.length, Ext (iter st k).tables[i] (iter st k').tables[i] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact iter_ext st k i hi m

theorem indexOf_iter (st : State) {k k' : Nat} (hk : k ≤ k') {g : Goal} {j : Nat}
    (h : indexOf (iter st k).tables g = some j) : indexOf (iter st k').tables g = some j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction m with
  | zero => exact h
  | succ m ih =>
    show indexOf (round (iter st (k + m))).1.tables g = some j
    exact indexOf_round ih

/-- The answers a goal reads only grow. -/
theorem answersOf_iter (st : State) {k k' : Nat} (hk : k ≤ k') {d : Goal} {a : Span}
    (h : a ∈ answersOf (iter st k).tables d) : a ∈ answersOf (iter st k').tables d := by
  obtain ⟨t, hf, a₀, ha₀, rfl⟩ := answersOf_mem h
  obtain ⟨j, hj, hjl, rfl⟩ := find_indexOf hf
  obtain ⟨hjl', hf', -⟩ := indexOf_find (indexOf_iter st hk hj)
  obtain ⟨hjl'', ⟨-, ⟨r, hr⟩, -⟩⟩ := iter_ext_le st hk j hjl
  rw [answersOf_eq hf', orient_eq, List.mem_map]
  exact ⟨a₀, by rw [hr]; exact List.mem_append_left _ ha₀, rfl⟩

/-! ## The root -/

/-- The answers of the root table. -/
def rootAns (st : State) : List Span := (st.tables.head?.map TableOf.answers).getD []

theorem round_emit (st : State) (t₀ : Table) (rest : Tables) (h : st.tables = t₀ :: rest) :
    (round st).2 = orient st.rootFlip (fresh t₀.answers (outOf st t₀).1) ∧
      rootAns (round st).1 = t₀.answers ++ fresh t₀.answers (outOf st t₀).1 := by
  constructor
  · simp only [round, h, List.head?_cons, List.map_cons]
    congr 1
    simp [outOf, h]
  · have := round_getElem st 0 (by rw [h]; simp)
    unfold rootAns
    rw [List.head?_eq_getElem?, this]
    simp only [Option.map_some, Option.getD_some, after_answers]
    simp [h]

theorem round_ne_nil {st : State} (h : st.tables ≠ []) : (round st).1.tables ≠ [] := by
  intro h'
  have := round_length st
  rw [h'] at this
  exact h (List.eq_nil_of_length_eq_zero (Nat.le_zero.1 this))

theorem stateAfter_succ (st : State) (n : Nat) :
    stateAfter st (n + 1) = if st.finished = true then st else stateAfter (round st).1 n := by
  show (match step st with
    | .emit _ st' => stateAfter st' n
    | .done => st) = _
  unfold step
  by_cases hf : st.finished = true <;> simp [hf]

theorem run_succ (st : State) (n : Nat) :
    runtime.run st (n + 1) = if st.finished = true then ([], true) else
      ((round st).2 ++ (runtime.run (round st).1 n).1, (runtime.run (round st).1 n).2) := by
  erw [Runtime.run.eq_2]
  simp only [runtime]
  unfold step
  by_cases hf : st.finished = true <;> simp [hf]

/-- A run follows the rounds until the root table is complete. -/
theorem stateAfter_cases (st : State) : ∀ n,
    (∃ k ≤ n, (iter st k).finished = true ∧ stateAfter st n = iter st k) ∨
      ((∀ k < n, (iter st k).finished = false) ∧ stateAfter st n = iter st n)
  | 0 => .inr ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩
  | n + 1 => by
    rw [stateAfter_succ]
    by_cases hf : st.finished = true
    · simp only [hf, ite_true]
      exact .inl ⟨0, Nat.zero_le _, hf, rfl⟩
    · have hf' : st.finished = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, ite_false]
      rcases stateAfter_cases (round st).1 n with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩
      · rw [iter_succ'] at h1 h2
        exact .inl ⟨k + 1, by omega, h1, h2⟩
      · right
        refine ⟨fun k hk => ?_, by rw [h2, iter_succ']⟩
        cases k with
        | zero => show st.finished = false; simpa using hf
        | succ k => rw [← iter_succ']; exact h1 k (by omega)

/-- What a run emits is the root table's new answers, oriented. -/
theorem run_root : ∀ (n : Nat) (st : State), st.tables ≠ [] →
    (runtime.run st n).1 = orient st.rootFlip ((rootAns (stateAfter st n)).drop (rootAns st).length) ∧
      (∃ r, rootAns (stateAfter st n) = rootAns st ++ r) ∧
      ((runtime.run st n).2 = true → (stateAfter st n).finished = true)
  | 0, st, _ => ⟨by simp [Runtime.run, stateAfter, orient], ⟨[], by simp [stateAfter]⟩,
      fun h => by simp [Runtime.run] at h⟩
  | n + 1, st, hne => by
    rw [run_succ, stateAfter_succ]
    by_cases hf : st.finished = true
    · simp only [hf, ite_true]
      exact ⟨by simp [orient], ⟨[], by simp⟩, fun _ => trivial⟩
    · have hf' : st.finished = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, ite_false]
      obtain ⟨t₀, rest, h⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨e1, e2⟩ := round_emit st t₀ rest h
      obtain ⟨i1, ⟨r, i2⟩, i3⟩ := run_root n (round st).1 (round_ne_nil hne)
      have hr0 : rootAns st = t₀.answers := by simp [rootAns, h]
      refine ⟨?_, ⟨fresh t₀.answers (outOf st t₀).1 ++ r, ?_⟩, i3⟩
      · rw [i1, e1, round_rootFlip, i2, e2, hr0]
        simp [orient_eq, List.append_assoc]
      · rw [i2, e2, hr0, List.append_assoc]

theorem stateAfter_ne_nil {st : State} (h : st.tables ≠ []) : ∀ n, (stateAfter st n).tables ≠ []
  | 0 => h
  | n + 1 => by
    rw [stateAfter_succ]
    split
    · exact h
    · exact stateAfter_ne_nil (round_ne_nil h) n

theorem iter_ne_nil {st : State} (h : st.tables ≠ []) : ∀ k, (iter st k).tables ≠ []
  | 0 => h
  | k + 1 => round_ne_nil (iter_ne_nil h k)

end Tier0

end R001

end RwLog
