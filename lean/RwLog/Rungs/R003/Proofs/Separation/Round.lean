/-
# The separating family: the completion check, and one round

While the root table is open and holds nothing or `$x -> z`, a round of R003
leaves the root holding `$x -> z`. If the root gained it in this round the
root stays open; if it already held it, the root gains nothing, its race says
the unfolding is final, and so it completes. The round costs `roundBound`,
which is quadratic in `k` for a bounded number of tables.
-/
import RwLog.Rungs.R003.Proofs.Separation.Stages

namespace RwLog

namespace R003

namespace Sep

open Cost R001

/-! ## The completion check -/

abbrev dflt : Table := ⟨⟨none, .zero, none⟩, [], false⟩

/-- The test of one dependency, as the machine runs it. -/
def chk (ts ts' : Tables) (S : List Nat) (d : Goal) : Cost Bool := do
  let n ← Tabled.norm d
  let j ← Tabled.indexOf ts n.2
  pure (match j with
    | none => false
    | some j => !decide ((ts'.getD j dflt).answers.length ≠ (ts.getD j dflt).answers.length) &&
        ((ts.getD j dflt).done || S.contains j))

/-- The completion test of one table, as the machine runs it. -/
def okC (P : Program) (finals : List Bool) (ts ts' : Tables) (S : List Nat) (i : Nat) : Cost Bool := do
  let strats ← Tabled.strategies P (finals.getD i false) ts (ts.getD i dflt).goal
  anyL (allL (chk ts ts' S)) strats

/-- The tables the check starts from: open, and gained nothing. -/
def S0 (ts ts' : Tables) : List Nat :=
  (List.range ts.length).filter fun i => !(ts.getD i dflt).done &&
    !decide ((ts'.getD i dflt).answers.length ≠ (ts.getD i dflt).answers.length)

theorem completing_eq (P : Program) (finals : List Bool) (ts ts' : Tables) :
    Tabled.completing P finals ts ts' =
      Tabled.gfpFrom (okC P finals ts ts') (S0 ts ts').length (S0 ts ts') := rfl

/-- A table whose test holds whatever the set is survives the shrinking. -/
theorem mem_gfpFrom_of_always {ok : List Nat → Nat → Bool} {i : Nat} (h : ∀ S, ok S i = true) :
    ∀ (n : Nat) (S : List Nat), i ∈ S → i ∈ RwLog.gfpFrom ok n S
  | 0, _, hi => hi
  | n + 1, S, hi => by
    simp only [RwLog.gfpFrom]
    split
    · exact hi
    · exact mem_gfpFrom_of_always h n _ (List.mem_filter.2 ⟨hi, h S⟩)

/-- The root's test holds once its race says the unfolding is final. -/
theorem okC_root_val {P : Program} {finals : List Bool} {ts ts' : Tables} (S : List Nat)
    (h : finals.getD 0 false = true) : (okC P finals ts ts' S 0).val = true := by
  simp only [okC, Tabled.strategies, bind_val, pure_val, h, ↓reduceIte, List.cons_append,
    List.nil_append, anyL, allL]

theorem okC_ticks {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest)
    (finals : List Bool) (ts' : Tables) (S : List Nat) {i : Nat}
    (hi : i < (tabs k a0 rest).length) :
    (okC P0 finals (tabs k a0 rest) ts' S i).ticks ≤ 6 * lookBound k (tabs k a0 rest).length := by
  have hmem : (tabs k a0 rest).getD i dflt ∈ tabs k a0 rest := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨ds, ⟨hv, ht⟩, hsub, hlen⟩ := tstrat_costs (a0 := a0) hr (slot_of_mem hr hmem)
  have hdep : ∀ d ∈ ds, (chk (tabs k a0 rest) ts' S d).ticks ≤
      lookBound k (tabs k a0 rest).length := by
    intro d hd
    have h1 := goalSize_sub (hsub d hd)
    have h2 := indexOf_ticks (a0 := a0) hr (key_sub (hsub d hd))
    have e : (Tabled.norm d).val.2 = d := by rw [Tabled.norm_val, norm_sub (hsub d hd)]
    have e' : (Tabled.norm d).ticks = goalSize d := rfl
    simp only [chk, bind_ticks, pure_ticks, e, e', Nat.add_zero]
    unfold lookBound
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm]
    omega
  have hall : ∀ deps ∈ (if finals.getD i false = true then [[]] else []) ++ [ds],
      (allL (chk (tabs k a0 rest) ts' S) deps).ticks ≤
        2 * lookBound k (tabs k a0 rest).length := by
    intro deps hdeps
    have hds : deps = [] ∨ deps = ds := by
      rcases List.mem_append.1 hdeps with h | h
      · split at h
        · exact Or.inl (List.mem_singleton.1 h)
        · simp at h
      · exact Or.inr (List.mem_singleton.1 h)
    rcases hds with rfl | rfl
    · simp [allL]
    · exact le_trans (allL_ticks_le_mul hdep) (Nat.mul_le_mul_right _ hlen)
  have hany := anyL_ticks_le_mul hall
  have hl : ((if finals.getD i false = true then [[]] else []) ++ [ds]).length ≤ 2 := by
    split <;> simp
  have hmul := Nat.mul_le_mul_right (2 * lookBound k (tabs k a0 rest).length) hl
  simp only [okC, Tabled.strategies, bind_ticks, bind_val, pure_ticks, pure_val, hv, Nat.add_zero]
  omega

theorem completing_spends {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest)
    (finals : List Bool) (ts' : Tables) :
    Spends (Tabled.completing P0 finals (tabs k a0 rest) ts')
      ((tabs k a0 rest).length * ((tabs k a0 rest).length *
        (6 * lookBound k (tabs k a0 rest).length)))
      (fun S => (∀ i ∈ S, i ∈ S0 (tabs k a0 rest) ts') ∧
        (0 ∈ S0 (tabs k a0 rest) ts' → finals.getD 0 false = true → 0 ∈ S)) := by
  have hlt : ∀ i ∈ S0 (tabs k a0 rest) ts', i < (tabs k a0 rest).length := fun i hi =>
    List.mem_range.1 (List.mem_filter.1 hi).1
  have hc := R002.Sep.gfpFrom_costs (ok := okC P0 finals (tabs k a0 rest) ts')
    (okV := fun S i => (okC P0 finals (tabs k a0 rest) ts' S i).val)
    (c := 6 * lookBound k (tabs k a0 rest).length) (T := S0 (tabs k a0 rest) ts')
    (fun S i hi => ⟨rfl, okC_ticks hr finals ts' S (hlt i hi)⟩)
    (S0 (tabs k a0 rest) ts').length (S0 (tabs k a0 rest) ts') (List.Sublist.refl _)
  have hlen : (S0 (tabs k a0 rest) ts').length ≤ (tabs k a0 rest).length := by
    have := List.length_filter_le (fun i => !((tabs k a0 rest).getD i dflt).done &&
      !decide ((ts'.getD i dflt).answers.length ≠ ((tabs k a0 rest).getD i dflt).answers.length))
      (List.range (tabs k a0 rest).length)
    rw [List.length_range] at this
    exact this
  rw [completing_eq]
  refine ⟨le_trans hc.2 (Nat.mul_le_mul hlen (Nat.mul_le_mul_right _ hlen)), ?_⟩
  rw [hc.1]
  exact ⟨gfpFrom_sub _ _ _, fun h0 hf => mem_gfpFrom_of_always (fun S => okC_root_val S hf) _ _ h0⟩

/-! ## The round -/

/-- What a round with `n` tables costs at most, by stage: the tick of the
round, the races, the candidates, the fresh answers, the keys of the goals
asked for, the new tables, and the completion check. -/
def roundBound (k n : Nat) : Nat :=
  1 + (n * (keyBound k + raceBound k) + (n * (4 * lookBound k n) +
    (n * freshBound (ansBound k + 1) + (2 * n * keyBound k +
      (2 * n * ((n + 0 + 2 * n) * (2 * keyBound k)) + (n * (n * (6 * lookBound k n)) + 0))))))

theorem ans_of_mem {k : Nat} {a0 : List Span} {rest : Tables} (ha : a0 = [] ∨ a0 = [xz])
    (hr : RestOK k rest) {t : Table} (ht : t ∈ tabs k a0 rest) :
    t.answers = [] ∨ t.answers = [xz] := by
  rcases List.mem_cons.1 ht with rfl | h
  · exact ha
  · exact Or.inl (hr t h).1

/-- One round while the root is open. The root ends with `$x -> z`. If it had
nothing, it stays open, and when it was the only table the new tables are
empty, open, and at most two. If it had `$x -> z` already, it completes. -/
theorem round_spends (k d : Nat) {a0 : List Span} {rest : Tables} (ha : a0 = [] ∨ a0 = [xz])
    (hr : RestOK k rest) :
    Spends (Tabled.round unfolder ⟨P0, tabs k a0 rest, false, d⟩) (roundBound k (rest.length + 1))
      (fun r => ∃ (dn : Bool) (tl : Tables),
        r.1 = ⟨P0, ⟨gC k, [xz], dn⟩ :: tl, false, d + 1⟩ ∧
        (a0 = [] → dn = false ∧ (rest = [] → tl.length ≤ 2 ∧ RestOK k tl)) ∧
        (a0 = [xz] → dn = true)) := by
  have hn : (tabs k a0 rest).length = rest.length + 1 := rfl
  simp only [Tabled.round]
  unfold roundBound
  refine Spends.bind (Spends.of_costs (Costs.tick 1)) fun _ _ => ?_
  refine Spends.bind (us_spends hr d) fun us hus => ?_
  refine Spends.bind (Spends.mapL_zip hus fun t u ht hu => out_spends hr ht hu) fun outs houts => ?_
  refine Spends.bind (Spends.mapL_zip houts fun t o ht ho => ts1_spends (ans_of_mem ha hr ht) ho)
    fun ts1 hts1 => ?_
  refine Spends.bind (reqs_spends houts) fun reqs hreqs => ?_
  refine Spends.bind (Spends.mono (newGoals_spends (a0 := a0) hr reqs []
    (fun g hg => key_sub (hreqs.1 g hg)) (by simp))
    (Nat.mul_le_mul hreqs.2 (Nat.mul_le_mul_right _ (by
      have := hreqs.2
      simp only [List.length_nil, hn] at this ⊢
      omega))) fun _ h => h) fun ng hng => ?_
  refine Spends.bind (completing_spends hr (us.map Prod.fst) ts1) fun S hS => ?_
  refine Spends.pure ?_
  obtain ⟨u0, us', hu0, -, rfl⟩ := List.forall₂_cons_left_iff.1 hus
  obtain ⟨t1, rest1, ht1, hrest1, rfl⟩ := List.forall₂_cons_left_iff.1 hts1
  obtain ⟨hg1, hd1, han1⟩ := ht1
  have hans : t1.answers = [xz] := han1 ⟨k, rfl⟩ ha
  have hmemS0 : 0 ∈ S0 (tabs k a0 rest) (t1 :: rest1) ↔ a0 = [xz] := by
    simp only [S0, List.mem_filter, List.mem_range, List.length_cons, Nat.zero_lt_succ, true_and,
      List.getD_cons_zero, Bool.not_false, Bool.true_and, hans,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ne_eq, not_not]
    rcases ha with rfl | rfl <;> simp
  refine ⟨S.contains 0, rest1.mapIdx (fun i t => if S.contains (i + 1) then { t with done := true }
    else t) ++ ng.map (fun g => (⟨g, [], false⟩ : Table)), ?_, ?_, ?_⟩
  · simp only [List.mapIdx_cons, List.cons_append]
    have e : (if S.contains 0 = true then { t1 with done := true } else t1) =
        (⟨gC k, [xz], S.contains 0⟩ : Table) := by
      cases t1
      simp only at hg1 hd1 hans
      subst hg1 hd1 hans
      cases S.contains 0 <;> rfl
    rw [e]
  · intro h0
    subst h0
    refine ⟨?_, ?_⟩
    · have : 0 ∉ S := fun h => by
        have := (hmemS0.1 (hS.1 0 h))
        simp at this
      simpa using this
    · intro hrest
      subst hrest
      cases hrest1
      simp only [List.mapIdx_nil, List.nil_append, List.length_map]
      refine ⟨?_, ?_⟩
      · have h1 := hng.1
        have h2 := hreqs.2
        simp only [List.length_nil, List.length_cons] at h1 h2
        omega
      · intro t ht
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
        refine ⟨rfl, rfl, hreqs.1 g ?_⟩
        rcases hng.2 g hg with h | h
        · simp at h
        · exact h
  · intro h0
    have h1 := hS.2 (hmemS0.2 h0) (by simpa using hu0.1)
    simpa using h1

end Sep

end R003

end RwLog
