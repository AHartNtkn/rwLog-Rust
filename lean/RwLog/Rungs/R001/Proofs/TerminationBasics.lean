/-
# Rung R001: termination basics

The general machinery lives here: when a run is finished, table keys
(`Goal.same`) form an equivalence, the completion fixpoint contains every
closed set, and tables only grow from round to round.
-/
import RwLog.Rungs.R001.Proofs.Kernel
import RwLog.Rungs.R001.Proofs.Tier0

namespace RwLog

namespace R001

/-! ## Runs and finished states -/

theorem step_done_iff (st : State) : step st = .done ↔ st.finished = true := by
  unfold step
  by_cases h : st.finished = true <;> simp [h]

theorem step_of_not_finished {st : State} (h : st.finished = false) :
    step st = .emit (round st).2 (round st).1 := by
  unfold step; simp [h]

theorem stateAfter_finished {st : State} (h : st.finished = true) : ∀ k, stateAfter st k = st
  | 0 => rfl
  | k + 1 => by
    have : step st = .done := (step_done_iff st).2 h
    simp only [stateAfter, this]

theorem stateAfter_succ_of_not_finished {st : State} (h : st.finished = false) (k : Nat) :
    stateAfter st (k + 1) = stateAfter (round st).1 k := by
  simp only [stateAfter, step_of_not_finished h]

theorem stateAfter_add (st : State) : ∀ m k, stateAfter st (m + k) = stateAfter (stateAfter st m) k
  | 0, k => by simp [stateAfter]
  | m + 1, k => by
    cases hf : st.finished with
    | true =>
      rw [stateAfter_finished hf, stateAfter_finished hf, stateAfter_finished hf]
    | false =>
      rw [show m + 1 + k = (m + k) + 1 by omega, stateAfter_succ_of_not_finished hf,
        stateAfter_succ_of_not_finished hf, stateAfter_add _ m k]

/-- A run of `n + 1` steps reports that it is done exactly when one of the
first `n + 1` states is finished. -/
theorem run_succ_done_iff : ∀ (n : Nat) (st : State),
    (runtime.run st (n + 1)).2 = true ↔ ∃ k ≤ n, (stateAfter st k).finished = true
  | 0, st => by
    show (Runtime.run runtime st 1).2 = true ↔ _
    simp only [Runtime.run]
    cases hf : st.finished with
    | true =>
      have : runtime.step st = .done := (step_done_iff st).2 hf
      simp only [this]
      exact ⟨fun _ => ⟨0, le_rfl, hf⟩, fun _ => trivial⟩
    | false =>
      have : runtime.step st = .emit (round st).2 (round st).1 := step_of_not_finished hf
      simp only [this]
      constructor
      · intro h; cases h
      · rintro ⟨k, hk, h⟩
        rw [Nat.le_zero.1 hk] at h; simp [stateAfter, hf] at h
  | n + 1, st => by
    show (Runtime.run runtime st (n + 2)).2 = true ↔ _
    simp only [Runtime.run]
    cases hf : st.finished with
    | true =>
      have : runtime.step st = .done := (step_done_iff st).2 hf
      simp only [this]
      exact ⟨fun _ => ⟨0, Nat.zero_le _, hf⟩, fun _ => trivial⟩
    | false =>
      have : runtime.step st = .emit (round st).2 (round st).1 := step_of_not_finished hf
      simp only [this]
      have ih := run_succ_done_iff n (round st).1
      change (runtime.run (round st).1 (n + 1)).2 = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨k, hk, h⟩
        exact ⟨k + 1, by omega, by rw [stateAfter_succ_of_not_finished hf]; exact h⟩
      · rintro ⟨k, hk, h⟩
        cases k with
        | zero => simp [stateAfter, hf] at h
        | succ k =>
          rw [stateAfter_succ_of_not_finished hf] at h
          exact ⟨k, by omega, h⟩

theorem halts_iff (st : State) :
    (∃ n, (runtime.run st n).2 = true) ↔ ∃ k, (stateAfter st k).finished = true := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [Runtime.run] at h
    | succ n => obtain ⟨k, -, hk⟩ := (run_succ_done_iff n st).1 h; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, (run_succ_done_iff k st).2 ⟨k, le_rfl, hk⟩⟩

theorem terminates_iff (P : Program) (q : Rel) :
    runtime.Terminates P q ↔ ∃ k, (stateAfter (State.ofGoal P ⟨none, q, none⟩) k).finished = true :=
  halts_iff _

theorem goalTerminates_iff (P : Program) (g : Goal) :
    GoalTerminates P g ↔ ∃ k, (stateAfter (State.ofGoal P g) k).finished = true :=
  halts_iff _

/-! ## Table keys form an equivalence -/

theorem boundEq_refl : ∀ a : Option Span, boundEq a a = true
  | none => rfl
  | some a => by simp [boundEq, covers?_refl]

theorem boundEq_symm : ∀ {a b : Option Span}, boundEq a b = true → boundEq b a = true
  | none, none, _ => rfl
  | some a, some b, h => by
    simp only [boundEq, Bool.and_eq_true] at h ⊢; exact ⟨h.2, h.1⟩
  | none, some _, h => by simp [boundEq] at h
  | some _, none, h => by simp [boundEq] at h

theorem boundEq_trans : ∀ {a b c : Option Span}, boundEq a b = true → boundEq b c = true →
    boundEq a c = true
  | none, none, none, _, _ => rfl
  | some a, some b, some c, h₁, h₂ => by
    simp only [boundEq, Bool.and_eq_true] at h₁ h₂ ⊢
    exact ⟨covers?_trans h₁.1 h₂.1, covers?_trans h₂.2 h₁.2⟩
  | none, some _, _, h, _ => by simp [boundEq] at h
  | some _, none, _, h, _ => by simp [boundEq] at h
  | none, none, some _, _, h => by simp [boundEq] at h
  | some _, some _, none, _, h => by simp [boundEq] at h

theorem Goal.same_refl (g : Goal) : g.same g = true := by
  simp [Goal.same, boundEq_refl]

theorem Goal.same_symm {g h : Goal} (hs : g.same h = true) : h.same g = true := by
  simp only [Goal.same, Bool.and_eq_true, decide_eq_true_eq] at hs ⊢
  exact ⟨⟨hs.1.1.symm, boundEq_symm hs.1.2⟩, boundEq_symm hs.2⟩

theorem Goal.same_trans {g h k : Goal} (h₁ : g.same h = true) (h₂ : h.same k = true) :
    g.same k = true := by
  simp only [Goal.same, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
  exact ⟨⟨h₁.1.1.trans h₂.1.1, boundEq_trans h₁.1.2 h₂.1.2⟩, boundEq_trans h₁.2 h₂.2⟩

/-! ## The completion fixpoint -/

/-- `ok` only grows with its set argument. -/
def OkMono (ok : List Nat → Nat → Bool) : Prop :=
  ∀ S S' : List Nat, (∀ j ∈ S, j ∈ S') → ∀ i, ok S i = true → ok S' i = true

/-- Every set inside `S` that is closed under `ok` survives the shrinking. -/
theorem subset_gfpFrom {ok : List Nat → Nat → Bool} (hm : OkMono ok) (X : List Nat)
    (hX : ∀ i ∈ X, ok X i = true) : ∀ n S, (∀ i ∈ X, i ∈ S) → ∀ i ∈ X, i ∈ gfpFrom ok n S
  | 0, S, hS => hS
  | n + 1, S, hS => by
    have hS' : ∀ i ∈ X, i ∈ S.filter (ok S) := fun i hi =>
      List.mem_filter.2 ⟨hS i hi, hm X S hS i (hX i hi)⟩
    simp only [gfpFrom]
    split
    · exact hS
    · exact subset_gfpFrom hm X hX n _ hS'

theorem gfpFrom_sub (ok : List Nat → Nat → Bool) : ∀ n S, ∀ i ∈ gfpFrom ok n S, i ∈ S
  | 0, _ => fun _ h => h
  | n + 1, S => by
    simp only [gfpFrom]
    split
    · exact fun _ h => h
    · exact fun i hi => (List.mem_filter.1 (gfpFrom_sub ok n _ i hi)).1

/-- With enough passes the result is closed under `ok`. -/
theorem gfpFrom_closed (ok : List Nat → Nat → Bool) : ∀ n S, S.length ≤ n →
    ∀ i ∈ gfpFrom ok n S, ok (gfpFrom ok n S) i = true
  | 0, S, h => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]; simp [gfpFrom]
  | n + 1, S, h => by
    simp only [gfpFrom]
    split
    · rename_i hl
      intro i hi
      have := List.filter_eq_self.1 (List.Sublist.eq_of_length (List.filter_sublist) hl)
      simpa using this i hi
    · rename_i hl
      have : (S.filter (ok S)).length < S.length :=
        lt_of_le_of_ne (List.filter_sublist.length_le) hl
      exact gfpFrom_closed ok n _ (by omega)

end R001

end RwLog

namespace RwLog

namespace R001

/-! ## Tables only grow -/

theorem round_P (st : State) : (round st).1.P = st.P := rfl
theorem round_depth (st : State) : (round st).1.depth = st.depth + 1 := rfl
theorem round_rootFlip (st : State) : (round st).1.rootFlip = st.rootFlip := rfl

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun x => (x, f x)
  | [] => rfl
  | x :: l => by simp [zip_map_self f l]

theorem fresh_nil (old : List Span) : fresh old [] = [] := by
  simp [fresh, maxima]

/-- One round keeps every table at its position, with the same goal, extends
its answers, and leaves a complete table as it is. -/
theorem round_table (st : State) (i : Nat) (h : i < st.tables.length) :
    ∃ t', (round st).1.tables[i]? = some t' ∧ t'.goal = st.tables[i].goal ∧
      st.tables[i].answers <+: t'.answers ∧
      (st.tables[i].done = true → t'.done = true ∧ t'.answers = st.tables[i].answers) := by
  simp only [round]
  rw [List.getElem?_append_left (by simpa using h)]
  simp only [zip_map_self, List.map_map, List.getElem?_mapIdx, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Function.comp_def]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · split <;> rfl
  · split <;> exact List.prefix_append _ _
  · intro hd
    split
    · refine ⟨rfl, ?_⟩
      simp [fresh_nil]
    · refine ⟨by simp [hd], ?_⟩
      simp [fresh_nil]

theorem round_length (st : State) : st.tables.length ≤ (round st).1.tables.length := by
  simp [round]


/-- A table present in a state stays at its position in every later state,
with its goal, with answers that only grow, and complete once complete. -/
theorem stateAfter_table (st : State) (i : Nat) (h : i < st.tables.length) : ∀ k,
    ∃ t', (stateAfter st k).tables[i]? = some t' ∧ t'.goal = st.tables[i].goal ∧
      st.tables[i].answers <+: t'.answers ∧
      (st.tables[i].done = true → t'.done = true ∧ t'.answers = st.tables[i].answers)
  | 0 => ⟨_, List.getElem?_eq_getElem h, rfl, List.prefix_refl _, fun hd => ⟨hd, rfl⟩⟩
  | k + 1 => by
    cases hf : st.finished with
    | true =>
      rw [stateAfter_finished hf]
      exact ⟨_, List.getElem?_eq_getElem h, rfl, List.prefix_refl _, fun hd => ⟨hd, rfl⟩⟩
    | false =>
      rw [stateAfter_succ_of_not_finished hf]
      obtain ⟨t₁, h₁, g₁, a₁, d₁⟩ := round_table st i h
      have hi : i < (round st).1.tables.length := by
        rcases List.getElem?_eq_some_iff.1 h₁ with ⟨hi, -⟩; exact hi
      have ht₁ : (round st).1.tables[i] = t₁ := by
        rcases List.getElem?_eq_some_iff.1 h₁ with ⟨_, e⟩; exact e
      obtain ⟨t₂, h₂, g₂, a₂, d₂⟩ := stateAfter_table (round st).1 i hi k
      rw [ht₁] at g₂ a₂ d₂
      refine ⟨t₂, h₂, g₂.trans g₁, a₁.trans a₂, fun hd => ?_⟩
      obtain ⟨e₁, e₂⟩ := d₁ hd
      obtain ⟨e₃, e₄⟩ := d₂ e₁
      exact ⟨e₃, e₄.trans e₂⟩

theorem stateAfter_length_mono (st : State) : ∀ k, st.tables.length ≤ (stateAfter st k).tables.length
  | 0 => le_rfl
  | k + 1 => by
    cases hf : st.finished with
    | true => rw [stateAfter_finished hf]
    | false =>
      rw [stateAfter_succ_of_not_finished hf]
      exact (round_length st).trans (stateAfter_length_mono _ k)

theorem stateAfter_P (st : State) : ∀ k, (stateAfter st k).P = st.P
  | 0 => rfl
  | k + 1 => by
    cases hf : st.finished with
    | true => rw [stateAfter_finished hf]
    | false => rw [stateAfter_succ_of_not_finished hf, stateAfter_P _ k]; rfl

/-! ## Requested goals get tables -/

/-- The fold that collects new goals keeps every goal it is offered, up to
`same`, either as an existing table or as a collected goal. -/
theorem newGoals_cover (ts : Tables) : ∀ (reqs acc : List Goal), ∀ g ∈ acc ++ reqs,
    ts.any (fun t => t.goal.same g) = true ∨
      (reqs.foldl (fun acc g => if ts.any (fun t => t.goal.same g) || acc.any (fun h => h.same g)
        then acc else acc ++ [g]) acc).any (fun h => h.same g) = true
  | [], acc, g, hg => by
    simp only [List.append_nil] at hg
    exact .inr (List.any_eq_true.2 ⟨g, hg, Goal.same_refl g⟩)
  | r :: reqs, acc, g, hg => by
    simp only [List.foldl_cons]
    by_cases hc : (ts.any (fun t => t.goal.same r) || acc.any (fun h => h.same r)) = true
    · simp only [hc, ite_true]
      rcases List.mem_append.1 hg with hg | hg
      · exact newGoals_cover ts reqs acc g (List.mem_append_left _ hg)
      · rcases List.mem_cons.1 hg with rfl | hg
        · rcases Bool.or_eq_true_iff.1 hc with hc | hc
          · exact .inl hc
          · obtain ⟨h, hh, hs⟩ := List.any_eq_true.1 hc
            exact newGoals_cover ts reqs acc h (List.mem_append_left _ hh) |>.elim
              (fun e => .inl (by
                obtain ⟨t, ht, e⟩ := List.any_eq_true.1 e
                exact List.any_eq_true.2 ⟨t, ht, Goal.same_trans e hs⟩))
              (fun e => .inr (by
                obtain ⟨t, ht, e⟩ := List.any_eq_true.1 e
                exact List.any_eq_true.2 ⟨t, ht, Goal.same_trans e hs⟩))
        · exact newGoals_cover ts reqs acc g (List.mem_append_right _ hg)
    · simp only [Bool.eq_false_of_ne_true hc, Bool.false_eq_true, ite_false]
      rcases List.mem_append.1 hg with hg | hg
      · exact newGoals_cover ts reqs (acc ++ [r]) g (List.mem_append_left _ (List.mem_append_left _ hg))
      · rcases List.mem_cons.1 hg with rfl | hg
        · exact newGoals_cover ts reqs (acc ++ [g]) g
            (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
        · exact newGoals_cover ts reqs (acc ++ [r]) g (List.mem_append_right _ hg)

/-- After a round, every goal an incomplete table requested has a table, up
to `same`. -/
theorem round_requested (st : State) (i : Nat) (h : i < st.tables.length)
    (hnd : st.tables[i].done = false) (r : Goal)
    (hr : r ∈ (produce st.P st.depth st.tables st.tables[i].goal).2) :
    ∃ t ∈ (round st).1.tables, t.goal.same r.norm.2 = true := by
  have hreq : r.norm.2 ∈ ((st.tables.map fun t => if t.done then (([] : List Span), ([] : List Goal))
      else produce st.P st.depth st.tables t.goal).flatMap Prod.snd).map fun g => g.norm.2 := by
    refine List.mem_map.2 ⟨r, List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨st.tables[i],
      List.getElem_mem h, rfl⟩, ?_⟩, rfl⟩
    simp only [hnd, Bool.false_eq_true, ite_false]; exact hr
  rcases newGoals_cover st.tables _ [] r.norm.2 (by rw [List.nil_append]; exact hreq) with e | e
  · obtain ⟨t, ht, e⟩ := List.any_eq_true.1 e
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨t', h', g', -⟩ := round_table st j hj
    exact ⟨t', List.mem_of_getElem? h', by rw [g']; exact e⟩
  · obtain ⟨g, hg, e⟩ := List.any_eq_true.1 e
    refine ⟨⟨g, [], false⟩, ?_, e⟩
    simp only [round]
    exact List.mem_append_right _ (List.mem_map.2 ⟨g, hg, rfl⟩)

/-! ## Completion of a closed set of stable tables -/

/-- The default table `getD` falls back to. -/
abbrev noTable : Table := ⟨⟨none, .zero, none⟩, [], false⟩

/-- Table `j` gained answers between `ts` and `ts'`. -/
def gainedAt (ts ts' : Tables) (j : Nat) : Bool :=
  decide ((ts'.getD j noTable).answers.length ≠ (ts.getD j noTable).answers.length)

/-- The completion test of `completing`, for a candidate set `S`. -/
def okAt (P : Program) (d : Nat) (ts ts' : Tables) (S : List Nat) (i : Nat) : Bool :=
  (strategies P d ts (ts.getD i noTable).goal).any fun deps =>
    deps.all fun g =>
      match indexOf ts g.norm.2 with
      | none => false
      | some j => !gainedAt ts ts' j && ((ts.getD j noTable).done || S.contains j)

theorem okAt_mono (P : Program) (d : Nat) (ts ts' : Tables) : OkMono (okAt P d ts ts') := by
  intro S S' hS i h
  simp only [okAt, List.any_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨deps, hd, h⟩ := h
  refine ⟨deps, hd, fun g hg => ?_⟩
  have := h g hg
  split at this
  · exact absurd this (by simp)
  · rename_i j hj
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at this ⊢
    refine ⟨this.1, this.2.elim .inl fun h => .inr ?_⟩
    simp only [List.contains_iff_mem] at h ⊢
    exact hS j h

/-- Every set of incomplete tables that gained nothing and is closed under the
completion test is marked complete. -/
theorem completing_closed (P : Program) (d : Nat) (ts ts' : Tables) (X : List Nat)
    (hlt : ∀ i ∈ X, i < ts.length) (hnd : ∀ i ∈ X, (ts.getD i noTable).done = false)
    (hng : ∀ i ∈ X, gainedAt ts ts' i = false) (hok : ∀ i ∈ X, okAt P d ts ts' X i = true) :
    ∀ i ∈ X, i ∈ completing P d ts ts' := by
  intro i hi
  have := subset_gfpFrom (okAt_mono P d ts ts') X hok
    ((List.range ts.length).filter fun i => !(ts.getD i noTable).done && !gainedAt ts ts' i).length
    ((List.range ts.length).filter fun i => !(ts.getD i noTable).done && !gainedAt ts ts' i)
    (fun j hj => List.mem_filter.2 ⟨List.mem_range.2 (hlt j hj), by rw [hnd j hj, hng j hj]; rfl⟩) i hi
  exact this

/-- What completion guarantees: a table that completes in a round was
incomplete, gained nothing, and passes the completion test against the
completing set. -/
theorem completing_spec (P : Program) (d : Nat) (ts ts' : Tables) (i : Nat)
    (hi : i ∈ completing P d ts ts') :
    i < ts.length ∧ (ts.getD i noTable).done = false ∧ gainedAt ts ts' i = false ∧
      okAt P d ts ts' (completing P d ts ts') i = true := by
  have hsub := gfpFrom_sub (okAt P d ts ts') _ _ i hi
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at hsub
  exact ⟨hsub.1, hsub.2.1, hsub.2.2, gfpFrom_closed _ _ _ le_rfl i hi⟩

/-! ## Certificate covers are complete

A valid certificate's covers cover every derivation of their goals, for every
theory (up to the theory, as `Tier0.DC`). The proof is the completion
soundness argument of Tier 0 run on the certificate's tables, where every
table is complete: by induction on the weight of the derivation, the strategy
the certificate names reads goals listed in the certificate, whose covers
cover the lighter derivations of their pieces, so the goal's candidates cover
the derivation, and the closure condition moves that onto the cover. Ranks are
not needed for this: a push reads only the pieces of the one derivation. -/

theorem findTable_certTables (C : List CertEntry) (g : Goal) :
    findTable (certTables C) g = (C.find? fun e => e.goal.same g).map fun e => ⟨e.goal, e.cover, true⟩ := by
  unfold findTable certTables
  rw [List.find?_map]
  rfl

theorem answersOf_certTables (C : List CertEntry) (g : Goal) :
    answersOf (certTables C) g = certCover C g := by
  unfold answersOf certCover
  simp only [findTable_certTables]
  cases C.find? (fun e => e.goal.same g.norm.2) <;> rfl

theorem certTables_found {C : List CertEntry} {d : Goal}
    (h : ∃ e' ∈ C, e'.goal.same d.norm.2 = true) :
    ∃ e'' ∈ C, findTable (certTables C) d.norm.2 = some ⟨e''.goal, e''.cover, true⟩ := by
  rw [findTable_certTables]
  obtain ⟨e', he', hs⟩ := h
  cases hf : C.find? (fun e => e.goal.same d.norm.2) with
  | none => exact absurd hf (List.find?_isSome.2 ⟨e', he', hs⟩ |> Option.isSome_iff_ne_none.1)
  | some e'' => exact ⟨e'', List.mem_of_find?_eq_some hf, rfl⟩

theorem doneOf_certTables {C : List CertEntry} {d : Goal}
    (h : ∃ e' ∈ C, e'.goal.same d.norm.2 = true) : doneOf (certTables C) d = true := by
  obtain ⟨e'', -, hf⟩ := certTables_found h
  unfold doneOf; rw [hf]

section
variable {P : Program} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
include hwf

open Tier0 in
/-- Every cover of a valid certificate covers, up to the theory, every
derivation of its goal. -/
theorem cert_covers_complete {C : List CertEntry} {D : Nat} {root : Goal}
    (hC : Cert.Valid P C D root) :
    ∀ m, ∀ e ∈ C, ∀ (w : Nat) (s : Span), DW P w e.goal.e s → 2 * w + isOr e.goal.e ≤ m →
      DC P.theory e.cover (GDen e.goal s.den) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro e he w s hw hm
  obtain ⟨hint, -, hclos, hstrat⟩ := hC.2 e he
  have hgG : GoodG e.goal := goodG_of_interfaced hint
  -- the closure moves coverage of the candidates onto the cover
  suffices hc : DC P.theory (produce P D (certTables C) e.goal).1 (GDen e.goal s.den) from
    hc.covers hclos
  -- a listed goal covers its lighter derivations
  have hD : ∀ d : Goal, (∃ e' ∈ C, e'.goal.same d.norm.2 = true) → GoodG d → ∀ w' s',
      DW P w' d.e s' → 2 * w' + isOr d.e < 2 * w + isOr e.goal.e →
      DC P.theory (answersOf (certTables C) d) (GDen d s'.den) := by
    intro d hd hgd w' s' hw' hlt
    obtain ⟨e'', he'', hf⟩ := certTables_found hd
    have hgt : GoodG e''.goal := goodG_of_interfaced (hC.2 e'' he'').1
    exact dc_via_table hf hgd hgt hw' fun w'' s'' h'' hle =>
      IH _ (by simp only at hle; omega) e'' he'' w'' s'' h'' le_rfl
  clear IH hm hclos
  rcases hstrat with hf | ⟨st, hst, hdeps⟩
  · exact dc_unfold hwf hf hw.derives
  have hfound : ∀ d ∈ st, ∃ e' ∈ C, e'.goal.same d.1.norm.2 = true :=
    fun d hd => let ⟨e', he', hs, _⟩ := hdeps d hd; ⟨e', he', hs⟩
  clear hdeps
  generalize e.goal = G at *
  obtain ⟨lb, e, rb⟩ := G
  cases e with
  | zero => cases hw
  | span s₀ => cases hw with | span => exact dc_span hwf lb rb _
  | or a b =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    obtain ⟨l, hl, hwl⟩ := (dw_orBranches _).1 hw
    have hl' := orBranches_not_or _ l hl
    refine dc_or hl (hD ⟨lb, l, rb⟩ ?_ hgG w s hwl ?_)
    · exact hfound (⟨lb, l, rb⟩, false) (by simp only [orLeaves, List.mem_map]; exact ⟨_, ⟨l, hl, rfl⟩, rfl⟩)
    · rw [isOr_zero hl']; simp [isOr]
  | call n =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    cases hw with
    | call hw =>
      exact dc_call (hD _ (hfound _ (List.mem_singleton_self _)) hgG _ s hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl))
  | conv a =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    cases hw with
    | conv hw =>
      exact dc_conv (hD _ (hfound _ (List.mem_singleton_self _)) (goodG_convGoal hgG a) _ _ hw
        (meas_lt _ _ (Nat.lt_succ_self _) rfl))
  | seq a b =>
    cases hw with
    | seq hw₁ hw₂ hc =>
      rw [compose_some hc]
      have hL : GoodG ⟨lb, a, none⟩ := ⟨hgG.1, trivial⟩
      have hR : GoodG ⟨none, b, rb⟩ := ⟨trivial, hgG.2⟩
      simp only [certStrategies, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl | rfl
      · exact dc_seq_join hwf
          (hD _ (hfound (seqLeft ⟨lb, .seq a b, rb⟩ a, false) (by simp)) hL _ _ hw₁ (meas_lt _ _ (by omega) rfl))
          (hD _ (hfound (seqRight ⟨lb, .seq a b, rb⟩ b, false) (by simp)) hR _ _ hw₂ (meas_lt _ _ (by omega) rfl))
      · have hLf := hfound _ (List.mem_cons_self ..)
        refine dc_seq_pushL hwf (doneOf_certTables hLf)
          (hD _ hLf hL _ _ hw₁ (meas_lt _ _ (by omega) rfl)) fun x hx => ?_
        rw [answersOf_certTables] at hx
        exact hD _ (hfound (seqPushL ⟨lb, .seq a b, rb⟩ b x, false)
            (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩)))
          (Tier0.goodG_pushL hgG b x) _ _ hw₂ (meas_lt _ _ (by omega) rfl)
      · have hRf := hfound _ (List.mem_cons_self ..)
        refine dc_seq_pushR hwf (doneOf_certTables hRf)
          (hD _ hRf hR _ _ hw₂ (meas_lt _ _ (by omega) rfl)) fun y hy => ?_
        rw [answersOf_certTables] at hy
        exact hD _ (hfound (seqPushR ⟨lb, .seq a b, rb⟩ a y, false)
            (List.mem_cons_of_mem _ (List.mem_map.2 ⟨y, hy, rfl⟩)))
          (Tier0.goodG_pushR hgG a y) _ _ hw₁ (meas_lt _ _ (by omega) rfl)
  | and a b =>
    cases hw with
    | and hw₁ hw₂ hc =>
      rw [meet_some hc]
      simp only [certStrategies, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl | rfl
      · exact dc_and_join hwf hgG
          (hD ⟨lb, a, rb⟩ (hfound (andLeft ⟨lb, .and a b, rb⟩ a, false) (by simp)) hgG _ _ hw₁ (meas_lt _ _ (by omega) rfl))
          (hD ⟨lb, b, rb⟩ (hfound (andRight ⟨lb, .and a b, rb⟩ b, false) (by simp)) hgG _ _ hw₂ (meas_lt _ _ (by omega) rfl))
      · have hLf := hfound _ (List.mem_cons_self ..)
        refine dc_and_pushL hwf hgG (doneOf_certTables hLf)
          (hD ⟨lb, a, rb⟩ hLf hgG _ _ hw₁ (meas_lt _ _ (by omega) rfl)) fun x hx => ?_
        rw [answersOf_certTables] at hx
        exact hD _ (hfound (andPush b x, false) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩)))
          (goodG_andPush b x) _ _ hw₂ (meas_lt _ _ (by omega) rfl)
      · have hRf := hfound _ (List.mem_cons_self ..)
        refine dc_and_pushR hwf hgG (doneOf_certTables hRf)
          (hD ⟨lb, b, rb⟩ hRf hgG _ _ hw₂ (meas_lt _ _ (by omega) rfl)) fun y hy => ?_
        rw [answersOf_certTables] at hy
        exact hD _ (hfound (andPush a y, false) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨y, hy, rfl⟩)))
          (goodG_andPush a y) _ _ hw₁ (meas_lt _ _ (by omega) rfl)

/-- Every cover of a valid certificate covers, up to the theory, every
derivation of its goal. -/
theorem cert_covers_derives {C : List CertEntry} {D : Nat} {root : Goal}
    (hC : Cert.Valid P C D root) {e : CertEntry} (he : e ∈ C) {s : Span}
    (hs : Derives P e.goal.e s) : Tier0.DC P.theory e.cover (Tier0.GDen e.goal s.den) := by
  obtain ⟨w, hw⟩ := Tier0.dw_of_derives hs
  exact cert_covers_complete hwf hC _ e he w s hw le_rfl

end

end R001

end RwLog
