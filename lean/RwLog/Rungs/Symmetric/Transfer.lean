/-
# What one run completes, every run completes

Two runs of requests of one program need not open the same goals, nor in the
same order. But a goal whose table is complete in one run has a complete
table in every run that does not neglect it (`IsRun.transfer`), provided no
answer of a table of that run covers a later one.

The tables of the first run that are complete at a time stand in an order
(`Ranked`): each has a strategy with nothing left to do that reads only
complete tables that stand no higher. By induction along the order, take the
tables of the second run whose goals stand at one level and that never
complete (`Waits`). Each has a round in infinitely many requests, so its
groups work for ever (`Requests.lines`), and it has a strategy of the same
kind as the one that completed the goal in the first run (`Full`). That
strategy reads tables of the same goals:

* what an edge reads is a fact of the program (`Reads.unique`), so a check
  opens the same goals in both runs;
* two complete tables of one goal have the same maximal answers
  (`IsRun.maxima_done`), so a push opens the same goals in both runs.

The tables it reads have goals that stand no higher, so each is complete at
some time or is one of those that wait; and each gains no answer from some
time on (`IsRun.settles`): every answer a fair run finds is covered by the
answers of a complete table of the goal (`IsRun.covered`), which the run
then has covered itself. So the strategy runs out of work (`Settle.lean`),
and the tables that wait are closed under the condition of completion: they
complete (`Req.closed`).
-/
import RwLog.Rungs.Symmetric.Settle
import RwLog.Rungs.Symmetric.Fair
import RwLog.Rungs.Symmetric.EdgeSame

namespace RwLog

namespace Symmetric

open Answer Saturation Goals

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

variable {σ τ : Nat → StateOf R Rel (Ans D P)}

omit [DecidableEq R] in
theorem mem_answers {st : StateOf R Rel (Ans D P)} {j : Nat} {y : Ans D P}
    (hy : y ∈ st.answers j) : ∃ t, st.tables[j]? = some t ∧ y ∈ t.answers := by
  unfold StateOf.answers at hy
  cases ht : st.tables[j]? with
  | none =>
    rw [ht] at hy
    exact (List.not_mem_nil hy).elim
  | some t =>
    rw [ht] at hy
    exact ⟨t, rfl, hy⟩

omit [DecidableEq R] in
/-- The goal a push opens for an answer depends on its representative
alone. -/
theorem pushG_span (g : GoalOf R Rel) (other : Rel) (kd : Kind) (left : Bool) {x x' : Ans D P}
    (h : x.span = x'.span) : pushG D g other kd left x = pushG D g other kd left x' := by
  cases kd <;> cases left <;> simp only [pushG, h]

/-- The table at `k` of the run `τ` has the goal of the table at `i` of the
run `σ`, which is complete at the time `r` and stands at the level `n`; it
is not neglected, and never completes. -/
def WaitsOn (σ τ : Nat → StateOf R Rel (Ans D P)) (ρ : Nat → Nat) (r n i k : Nat) : Prop :=
  ∃ g r', goalAt (σ r) i = some g ∧ (σ r).isDone i = true ∧ ρ i = n ∧
    goalAt (τ r') k = some g ∧ Opened τ k ∧ ¬ EvDone τ k

/-- The tables of `τ` that wait at the level `n`. -/
def Waits (σ τ : Nat → StateOf R Rel (Ans D P)) (ρ : Nat → Nat) (r n k : Nat) : Prop :=
  ∃ i, WaitsOn σ τ ρ r n i k

/-- The tables that wait at a level are finitely many: one for each table
of the first run. -/
theorem waits_list (hτ : IsRun τ) (ρ : Nat → Nat) (r n : Nat) :
    ∃ X : List Nat, ∀ k, k ∈ X ↔ Waits σ τ ρ r n k := by
  classical
  refine ⟨(List.range (σ r).tables.length).filterMap fun i =>
    if h : ∃ k, WaitsOn σ τ ρ r n i k then some (Classical.choose h) else none, fun k => ?_⟩
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, -, hi⟩
    split at hi
    · next h =>
      cases hi
      exact ⟨i, Classical.choose_spec h⟩
    · cases hi
  · rintro ⟨i, g, r', h1, h2, h3, h4, h5, h6⟩
    have hlt : i < (σ r).tables.length := by
      obtain ⟨t, ht, -⟩ := table_of_goalAt h1
      exact (List.getElem?_eq_some_iff.1 ht).1
    refine ⟨i, List.mem_range.2 hlt, ?_⟩
    have h : ∃ k, WaitsOn σ τ ρ r n i k := ⟨k, g, r', h1, h2, h3, h4, h5, h6⟩
    split
    · next h' =>
      obtain ⟨g', r'', e1, -, -, e4, -, -⟩ := Classical.choose_spec h'
      rw [h1] at e1
      cases e1
      exact congrArg some (hτ.goal_inj e4 h4)
    · next h' => exact absurd h h'

/-- **A table that has rounds for ever keeps a strategy of every kind in a
group that works for ever**: from some state on its groups are full, and
each strategy of each of them is a place of a line. -/
theorem IsRun.live_strat (hτ : IsRun τ) {r' k : Nat} {g : GoalOf R Rel}
    (hgk : goalAt (τ r') k = some g) (hlive : Live τ k) :
    ∃ r0, Full (τ r0) g (groupsAt (τ r0) k) ∧ ∀ gr' ∈ groupsAt (τ r0) k, ∀ x ∈ gr'.kinds,
      ∃ (L : Nat → List (Strat Rel (Ans D P))) (q : Nat) (s0 : Strat Rel (Ans D P)),
        Line (readNeed P) τ k r0 L ∧ (L r0)[q]? = some s0 ∧ s0.kind = x := by
  obtain ⟨r0, hpos, hl⟩ := hτ.req.lines k hlive
  have hfull : Full (τ r0) g (groupsAt (τ r0) k) := by
    cases ht0 : (τ r0).tables[k]? with
    | none => simp [groupsAt, ht0] at hpos
    | some t0 =>
      cases hg0 : t0.groups with
      | none => simp [groupsAt, ht0, hg0] at hpos
      | some gs0 =>
        have := (hτ.good r0).full k t0 ht0 gs0 hg0
        rw [← hτ.goal_any hgk (goalAt_of_table ht0)] at this
        simpa only [groupsAt, ht0, hg0, Option.getD_some] using this
  have lk : ∀ gr' ∈ groupsAt (τ r0) k, ∀ x ∈ gr'.kinds,
      ∃ (L : Nat → List (Strat Rel (Ans D P))) (q : Nat) (s0 : Strat Rel (Ans D P)),
        Line (readNeed P) τ k r0 L ∧ (L r0)[q]? = some s0 ∧ s0.kind = x := by
    intro gr' hgr' x hx
    obtain ⟨m, hm⟩ := List.getElem?_of_mem hgr'
    obtain ⟨s0, hs0, e⟩ := List.mem_map.1 hx
    obtain ⟨q, hq'⟩ := List.getElem?_of_mem hs0
    refine ⟨_, q, s0, hl m (List.getElem?_eq_some_iff.1 hm).1, ?_, e⟩
    simp only [hm, Option.map_some, Option.getD_some]
    exact hq'
  exact ⟨r0, hfull, lk⟩

section

variable (hL : D.Lawful P.sorts.interp)

include hL

/-- **No run finds what another misses**: an answer of the table of a goal
in one run is covered by an answer of its table in a run that does not
neglect the goal. -/
theorem IsRun.covered (hσ : IsRun σ) (hτ : IsRun τ) {r r' r2 i k : Nat} {g : GoalOf R Rel}
    (hi : goalAt (σ r) i = some g) (ho : Opened σ i) (hk : goalAt (τ r') k = some g)
    {y : Ans D P} (hy : y ∈ (τ r2).answers k) :
    ∃ r3, ∃ x ∈ (σ r3).answers i, covB D P x y = true := by
  obtain ⟨t, ht, hyt⟩ := mem_answers hy
  have hg : t.goal = g := (hτ.goal_any hk (goalAt_of_table ht)).symm
  have hgi : y.goal = toGoal g := by
    have := ((hτ.good r2).inv.core k t ht).2.2 y hyt
    rw [hg] at this
    exact this
  have hv : Valid D P (toGoal g) y.span := by
    rw [← hgi]
    exact y.valid
  obtain ⟨a, ha, hsub⟩ := hσ.fair.covers_valid hL (hσ.mem_opened hi ho) hv
  obtain ⟨r3, x, hx, rfl⟩ := (hσ.held_iff hi a).1 ha
  exact ⟨r3, x, hx, (covB_iff hL x y).2 hsub⟩

/-- **The table of a goal another run has completed stops growing**, in a
run that does not neglect the goal and keeps no answer covered by an earlier
one: once it covers every answer of the complete table, an answer it gained
would be covered by one it has. -/
theorem IsRun.settles (hσ : IsRun σ) (hτ : IsRun τ)
    (hN : ∀ r j, NoCov D (((τ r).answers j).map Ans.span)) {r r' i k : Nat}
    {g : GoalOf R Rel} (hi : goalAt (σ r) i = some g) (hd : (σ r).isDone i = true)
    (hk : goalAt (τ r') k = some g) (ho : Opened τ k) : ∃ T, Still τ T k := by
  obtain ⟨T, hT⟩ := eventually_forall_mem ((σ r).answers i)
    (fun f r1 => ∃ x ∈ (τ r1).answers k, covB D P x f = true) (fun f hf => by
      obtain ⟨r3, x, hx, hc⟩ := hτ.covered hL hσ hk ho hi hf
      exact ⟨r3, fun r1 hr1 => ⟨x, hτ.mem_le hr1 hx, hc⟩⟩)
  refine ⟨T, fun r1 hr1 => ?_⟩
  obtain ⟨rest, e⟩ := (hτ.stable hr1).answers k
  cases rest with
  | nil =>
    unfold StateOf.len
    rw [← e, List.append_nil]
  | cons y rest =>
    exfalso
    have hy : y ∈ (τ r1).answers k := by
      rw [← e]
      simp
    obtain ⟨r3, f, hf, hc⟩ := hσ.covered hL hτ hi (.inl ⟨r, hd⟩) hk hy
    obtain ⟨x, hx, hc'⟩ := hT f (hσ.done_answers hd r3 hf) T (Nat.le_refl _)
    have hn := hN r1 k
    unfold NoCov at hn
    rw [← e, List.map_append] at hn
    have h1 := (List.pairwise_append.1 hn).2.2 x.span (List.mem_map_of_mem hx) y.span
      (List.mem_map_of_mem List.mem_cons_self)
    have h2 := covB_trans hL _ _ _ hc' hc
    unfold covB at h2
    rw [h1] at h2
    cases h2

/-- A goal whose complete table is empty in one run has no answer in any
run. -/
theorem IsRun.empty_of_done (hσ : IsRun σ) (hτ : IsRun τ) {r r' i k : Nat} {g : GoalOf R Rel}
    (hi : goalAt (σ r) i = some g) (hd : (σ r).isDone i = true)
    (he : (σ r).answers i = []) (hk : goalAt (τ r') k = some g) (r2 : Nat) :
    (τ r2).answers k = [] := by
  cases hx : (τ r2).answers k with
  | nil => rfl
  | cons y l =>
    obtain ⟨r3, f, hf, -⟩ := hσ.covered hL hτ hi (.inl ⟨r, hd⟩) hk (y := y) (r2 := r2)
      (by rw [hx]; exact List.mem_cons_self)
    have := hσ.done_answers hd r3 hf
    rw [he] at this
    cases this

/-- **Two complete tables of one goal have the same maximal answers.** -/
theorem IsRun.maxima_done (hσ : IsRun σ) (hτ : IsRun τ) {r r' r'' i k : Nat}
    {g : GoalOf R Rel} (hi : goalAt (σ r) i = some g) (hd : (σ r).isDone i = true)
    (hk : goalAt (τ r'') k = some g) (hd' : (τ r').isDone k = true) :
    ∀ x' ∈ ((τ r').answers k).maximaBy (covB D P),
      ∃ x ∈ ((σ r).answers i).maximaBy (covB D P), x.span = x'.span :=
  maxima_same hL
    (fun a ha => by
      obtain ⟨r3, f, hf, hc⟩ := hσ.covered hL hτ hi (.inl ⟨r, hd⟩) hk ha
      exact ⟨f, hσ.done_answers hd r3 hf, hc⟩)
    (fun a ha => by
      obtain ⟨r3, f, hf, hc⟩ := hτ.covered hL hσ hk (.inl ⟨r', hd'⟩) hi ha
      exact ⟨f, hτ.done_answers hd' r3 hf, hc⟩)

/-- **A table that waits has, from some time on, a strategy with nothing
left to do** that reads only tables that are complete or wait with it, if
the goals that stand lower are complete in the run. -/
theorem IsRun.waits_quiet (hσ : IsRun σ) (hτ : IsRun τ)
    (hN : ∀ r j, NoCov D (((τ r).answers j).map Ans.span)) {ρ : Nat → Nat} {r n : Nat}
    (hρ : Ranked (σ r) ρ)
    (ih : ∀ i g, goalAt (σ r) i = some g → (σ r).isDone i = true → ρ i < n →
      ∀ r' k, goalAt (τ r') k = some g → Opened τ k → EvDone τ k)
    {X : List Nat} (hX : ∀ k, k ∈ X ↔ Waits σ τ ρ r n k) {k : Nat}
    (hk : Waits σ τ ρ r n k) :
    ∃ T, ∀ r1, T ≤ r1 → ∃ s, IsStrat τ k (r1 + 1) s ∧
      s.quiet (τ (r1 + 1)) (fun j => (τ (r1 + 1)).isDone j || X.contains j) = true ∧
      ∀ kd l side o todo subs, s = .push kd l side o todo subs →
        (τ r1).isDone side = true := by
  obtain ⟨i, g, r', hi, hd, hn, hgk, hop, hnd⟩ := hk
  subst hn
  have hlive : Live τ k := hop.resolve_left hnd
  -- a table read whose goal stands no higher gains no answer, and is complete or waits
  have rd : ∀ j j' gj r2, goalAt (σ r) j = some gj → (σ r).isDone j = true → ρ j ≤ ρ i →
      goalAt (τ r2) j' = some gj → Opened τ j' →
      ∃ T, ∀ r1, T ≤ r1 → Still τ r1 j' ∧ ((τ r1).isDone j' || X.contains j') = true := by
    intro j j' gj r2 hj hdj hle hj' ho'
    obtain ⟨T, hT⟩ := hσ.settles hL hτ hN hj hdj hj' ho'
    by_cases hev : EvDone τ j'
    · obtain ⟨r3, h3⟩ := hev
      refine ⟨max T r3, fun r1 hr1 => ⟨hT.mono (by omega), ?_⟩⟩
      rw [((hτ.stable (show r3 ≤ r1 by omega)).isDone h3).1]
      rfl
    · have hw : Waits σ τ ρ r (ρ i) j' := by
        rcases Nat.lt_or_eq_of_le hle with hlt | he
        · exact absurd (ih j gj hj hdj hlt r2 j' hj' ho') hev
        · exact ⟨j, gj, r2, hj, hdj, he, hj', ho', hev⟩
      refine ⟨T, fun r1 hr1 => ⟨hT.mono hr1, ?_⟩⟩
      simp [(hX j').2 hw]
  -- the strategy that completed the goal in the first run
  obtain ⟨t, ht, -⟩ := table_of_goalAt hi
  have hdt : t.done = true := by
    rw [← isDone_of_table ht]
    exact hd
  obtain ⟨gs, hgs, gr, hgr, s, hs, hq, hpush⟩ := hρ i t ht hdt
  have hst : IsStrat σ i r s := ⟨t, gs, gr, ht, hgs, hgr, hs⟩
  have hp := hσ.prog hi hst
  -- the groups of the table that waits
  obtain ⟨r0, hfull, lk⟩ := hτ.live_strat hgk hlive
  cases s with
  | span ran =>
    dsimp only [Prog] at hp
    obtain ⟨gr', hgr', hx⟩ := hfull.span hp.1
    obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
    obtain ⟨ran0, rfl⟩ := kind_span e
    obtain ⟨T, hT, hall⟩ := hLn.span_ran h0
    exact ⟨T, fun r1 hr1 => ⟨.span true, hLn.mem (r1 + 1) (by omega) _
      (List.mem_of_getElem? (hall (r1 + 1) (by omega))), by simp [Strat.quiet, Strat.pending],
      fun _ _ _ _ _ _ e => by cases e⟩⟩
  | copy c subs =>
    dsimp only [Prog] at hp
    obtain ⟨p0, p1, plen, psub⟩ := hp
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
      List.any_eq_false, List.all_eq_true, decide_eq_true_eq] at hq
    obtain ⟨gr', hgr', hx⟩ := hfull.copy c p0 p1
    obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
    obtain ⟨subs0, rfl⟩ := kind_copy e
    have hp0 := hτ.prog hgk (hLn.mem r0 (Nat.le_refl _) _ (List.mem_of_getElem? h0))
    dsimp only [Prog] at hp0
    obtain ⟨-, -, qlen, qsub⟩ := hp0
    have each : ∀ p' ∈ subs0, ∃ T, ∀ r1, T ≤ r1 → Still τ r1 p'.1 ∧
        ((τ r1).isDone p'.1 || X.contains p'.1) = true := by
      intro p' hp'
      obtain ⟨m', hm'⟩ := List.getElem?_of_mem hp'
      obtain ⟨x, hx1, hgx, -⟩ := qsub m' p'.1 p'.2 hm'
      have hlt : m' < subs.length := by
        rw [plen, ← qlen]
        exact (List.getElem?_eq_some_iff.1 hm').1
      obtain ⟨x', hx1', hgx', -⟩ := psub m' subs[m'].1 subs[m'].2 (List.getElem?_eq_getElem hlt)
      rw [hx1] at hx1'
      cases hx1'
      have hok := hq.2 _ (List.getElem_mem hlt)
      refine rd _ _ _ r0 hgx' hok.1 hok.2 hgx (hτ.opened_of_settled hgx fun r' => ?_)
      obtain ⟨r2, hr2', hr2, -, hfed, -⟩ := hLn.worked r'
      obtain ⟨subs2, hs2, hadv⟩ := hLn.copy_kept (Nat.le_refl _) h0 (show r0 ≤ r2 + 1 by omega)
      obtain ⟨p2, hp2, hadv2⟩ := hadv.get hm'
      have := hfed _ (List.mem_of_getElem? hs2) p2 (List.mem_of_getElem? hp2)
      rw [hadv2.1] at this
      exact ⟨r2, hr2', this⟩
    obtain ⟨T, hT⟩ := eventually_forall_mem subs0 _ each
    obtain ⟨T', hT', hall⟩ := hLn.copy_read h0 (Nat.le_max_right T r0)
      (fun p hp' => (hT p hp' (max T r0) (Nat.le_max_left T r0)).1)
    refine ⟨T', fun r1 hr1 => ?_⟩
    obtain ⟨subs1, hs1, hadv, hrd⟩ := hall (r1 + 1) (by omega)
    refine ⟨_, hLn.mem (r1 + 1) (by omega) _ (List.mem_of_getElem? hs1), ?_,
      fun _ _ _ _ _ _ e => by cases e⟩
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
      List.any_eq_false, List.all_eq_true, decide_eq_true_eq]
    refine ⟨fun p hp' => ?_, fun p hp' => ?_⟩
    · have := hrd p hp'
      unfold StateOf.len at this
      omega
    · obtain ⟨m', hm'⟩ := List.getElem?_of_mem hp'
      obtain ⟨p0', hp0', hadv'⟩ := hadv.get' hm'
      rw [hadv'.1]
      exact (hT p0' (List.mem_of_getElem? hp0') (r1 + 1) (by omega)).2
  | join kd a b c =>
    dsimp only [Prog] at hp
    obtain ⟨Lg, Rg, hsp, hga, hgb, -, -⟩ := hp
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hq
    obtain ⟨gr', hgr', a', b', hga', hgb', hx, -, -⟩ := hfull.split kd Lg Rg hsp
    obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
    obtain ⟨c0, rfl⟩ := kind_join e
    have fed : ∀ r', ∃ r2, r' ≤ r2 ∧ Settled (τ (r2 + 1)) a' ∧ Settled (τ (r2 + 1)) b' :=
      fun r' => by
        obtain ⟨r2, hr2', hr2, -, hfed, -⟩ := hLn.worked r'
        obtain ⟨c2, hs2, -⟩ := hLn.join_kept (Nat.le_refl _) h0 (show r0 ≤ r2 + 1 by omega)
        exact ⟨r2, hr2', hfed _ (List.mem_of_getElem? hs2)⟩
    obtain ⟨Ta, hTa⟩ := rd a a' Lg r0 hga hq.2.1.1 hq.2.1.2 hga'
      (hτ.opened_of_settled hga' fun r' => (fed r').imp fun _ h => ⟨h.1, h.2.1⟩)
    obtain ⟨Tb, hTb⟩ := rd b b' Rg r0 hgb hq.2.2.1 hq.2.2.2 hgb'
      (hτ.opened_of_settled hgb' fun r' => (fed r').imp fun _ h => ⟨h.1, h.2.2⟩)
    obtain ⟨T', hT', hall⟩ := hLn.join_done h0 (show r0 ≤ max (max Ta Tb) r0 by omega)
      (hTa (max (max Ta Tb) r0) (by omega)).1 (hTb (max (max Ta Tb) r0) (by omega)).1
      (fun r1 c1 hr1 hs1 => by
        have := hτ.prog hgk (hLn.mem r1 (by omega) _ (List.mem_of_getElem? hs1))
        dsimp only [Prog] at this
        obtain ⟨_, _, -, -, -, hok, -⟩ := this
        exact hok)
    refine ⟨T', fun r1 hr1 => ?_⟩
    obtain ⟨c1, hs1, hpend⟩ := hall (r1 + 1) (by omega)
    refine ⟨_, hLn.mem (r1 + 1) (by omega) _ (List.mem_of_getElem? hs1), ?_,
      fun _ _ _ _ _ _ e => by cases e⟩
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hpend, (hTa (r1 + 1) (by omega)).2, (hTb (r1 + 1) (by omega)).2⟩
  | push kd left side other todo subs =>
    dsimp only [Prog] at hp
    obtain ⟨Lg, Rg, hsp, hgside, hother, htodo, hsubs, -⟩ := hp
    have hrank := hpush kd left side other todo subs rfl
    simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true, decide_eq_true_eq] at hq
    obtain ⟨hpend, ⟨hds, hsome⟩, hokσ⟩ := hq
    cases todo with
    | none => cases hsome
    | some l =>
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons x l => simp [hds] at hpend
    subst hl
    obtain ⟨-, -, hcovσ⟩ := htodo [] rfl
    obtain ⟨gr', hgr', a', b', hga', hgb', -, hxl, hxr⟩ := hfull.split kd Lg Rg hsp
    obtain ⟨side', hgside', hx⟩ : ∃ side', goalAt (τ r0) side' = some (if left then Lg else Rg) ∧
        Strat.push kd left side' other none [] ∈ gr'.kinds := by
      subst hother
      cases left
      · exact ⟨b', by simpa using hgb', by simpa using hxr⟩
      · exact ⟨a', by simpa using hga', by simpa using hxl⟩
    obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
    obtain ⟨todo0, subs0, rfl⟩ := kind_push e
    have hoS : Opened τ side' := hτ.opened_of_settled hgside' fun r' => by
      obtain ⟨r2, hr2', hr2, -, hfed, -⟩ := hLn.worked r'
      obtain ⟨todo2, subs2, hs2⟩ := hLn.push_kept h0 (show r0 ≤ r2 + 1 by omega)
      exact ⟨r2, hr2', (hfed _ (List.mem_of_getElem? hs2)).1⟩
    obtain ⟨Td, hTd⟩ := ih side _ hgside hds hrank r0 side' hgside' hoS
    have hdn : ∀ r1, Td ≤ r1 → (τ r1).isDone side' = true := fun r1 hr1 =>
      ((hτ.stable hr1).isDone hTd).1
    obtain ⟨T1, subs1, hT1, h1⟩ := hLn.push_empty h0 (Nat.le_max_right Td r0)
      (fun r1 hr1 => hdn r1 (by omega))
    have hp1 := hτ.prog hgk (hLn.mem T1 (by omega) _ (List.mem_of_getElem? h1))
    dsimp only [Prog] at hp1
    obtain ⟨Lg', Rg', -, -, -, htodo1, hsubs1, -⟩ := hp1
    obtain ⟨hd1, hmax1, -⟩ := htodo1 [] rfl
    have hmx := hσ.maxima_done hL hτ hgside hds hgside' hd1
    have each : ∀ e' ∈ subs1, ∃ T, ∀ r1, T ≤ r1 → Still τ r1 e'.2.1 ∧
        ((τ r1).isDone e'.2.1 || X.contains e'.2.1) = true := by
      intro e' he'
      obtain ⟨x, hxm, hxs⟩ := hmx e'.1 (hmax1 e'.1 (.inr (List.mem_map_of_mem he')))
      obtain ⟨x'', hx''m, hx''in, hx''c⟩ := hcovσ x (List.mem_maximaBy hxm)
      have hx''s : x'' ∈ subs.map (·.1) := hx''in.resolve_left (fun h => by cases h)
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx''s
      have hcv : covB D P e.1 x = true := (covB_iff hL e.1 x).2 hx''c
      have hspn : e.1.span = e'.1.span :=
        (hL.covers_antisymm hcv (maxima_max hxm hx''m hcv)).trans hxs
      obtain ⟨-, hge, -⟩ := hsubs e he
      obtain ⟨-, hge', -⟩ := hsubs1 e' he'
      rw [pushG_span g other kd left hspn] at hge
      have hok := hokσ e he
      obtain ⟨m', hm'⟩ := List.getElem?_of_mem he'
      refine rd _ _ _ T1 hge hok.1 hok.2 hge' (hτ.opened_of_settled hge' fun r' => ?_)
      obtain ⟨r2, hr2', hr2, -, hfed, -⟩ := hLn.worked (max r' T1)
      obtain ⟨subs2, hs2, hadv, -⟩ := hLn.push_fixed (show r0 ≤ T1 by omega) h1
        (show T1 ≤ r2 + 1 by omega)
      have hlt : m' < subs2.length :=
        Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hm').1 hadv.1
      have h2 := (hfed _ (List.mem_of_getElem? hs2)).2 rfl subs2[m'] (List.getElem_mem hlt)
      rw [(hadv.2 m' e' subs2[m'] hm' (List.getElem?_eq_getElem hlt)).2.1] at h2
      exact ⟨r2, by omega, h2⟩
    obtain ⟨T, hT⟩ := eventually_forall_mem subs1 _ each
    obtain ⟨T', hT', hall⟩ := hLn.push_read (show r0 ≤ T1 by omega) h1
      (fun r1 hr1 => hdn r1 (by omega)) (show T1 ≤ max T T1 by omega)
      (fun e he => (hT e he (max T T1) (Nat.le_max_left T T1)).1)
    refine ⟨T', fun r1 hr1 => ?_⟩
    obtain ⟨subs2, hs2, hadv, hlen, hrd⟩ := hall (r1 + 1) (by omega)
    refine ⟨_, hLn.mem (r1 + 1) (by omega) _ (List.mem_of_getElem? hs2), ?_,
      fun _ _ _ _ _ _ e => ?_⟩
    · have hdd := hdn (r1 + 1) (by omega)
      simp only [Strat.quiet, Strat.pending, hdd, Bool.true_and, Option.isSome_some,
        List.isEmpty_nil, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
        List.any_eq_false, List.all_eq_true, decide_eq_true_eq]
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · have := hrd e he
        unfold StateOf.len at this
        omega
      · obtain ⟨m', hm'⟩ := List.getElem?_of_mem he
        have hlt : m' < subs1.length := by
          rw [← hlen]
          exact (List.getElem?_eq_some_iff.1 hm').1
        rw [(hadv.2 m' subs1[m'] e (List.getElem?_eq_getElem hlt) hm').2.1]
        exact (hT subs1[m'] (List.getElem_mem hlt) (r1 + 1) (by omega)).2
    · cases e
      exact hdn r1 (by omega)
  | check left side other c =>
    dsimp only [Prog] at hp
    obtain ⟨Lg, Rg, hsp, hside, hother, hc⟩ := hp
    cases c with
    | reading => simp [Strat.quiet, Strat.pending] at hq
    | off => simp [Strat.quiet, Strat.pending] at hq
    | opened subs =>
    obtain ⟨ps, hreads, -, -, pall⟩ := hc
    simp only [Strat.quiet, Strat.pending, Bool.not_false, Bool.true_and, List.all_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hq
    have iface : ∀ (nn : Nat) (p : R), ps[nn]? = some p → ∀ j' r2,
        goalAt (τ r2) j' =
          some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩) →
        (∀ r3, (τ r3).answers j' = []) ∧ (Opened τ j' → ∃ T, ∀ r1, T ≤ r1 →
          Still τ r1 j' ∧ ((τ r1).isDone j' || X.contains j') = true) := by
      intro nn p hp' j' r2 hj'
      obtain ⟨j, hj, hgj⟩ := pall nn p hp'
      have hj3 := hq j (List.mem_of_getElem? hj)
      exact ⟨fun r3 => hσ.empty_of_done hL hτ hgj hj3.1.1 hj3.2 hj' r3,
        fun ho' => rd j j' _ r2 hgj hj3.1.1 hj3.1.2 hj' ho'⟩
    have hck := hfull.check Lg Rg hsp left
    rw [← hside, ← hother] at hck
    rcases hck with hgone | ⟨gr', hgr', hx⟩
    · exfalso
      rcases hgone with hnone | ⟨ps', hr', p, hp', j', hj', hne⟩
      · cases Reads.unique hreads hnone
      · cases Reads.unique hreads hr'
        obtain ⟨nn, hnn⟩ := List.getElem?_of_mem hp'
        exact hne ((iface nn p hnn j' r0 hj').1 r0)
    · obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
      obtain ⟨c0, rfl⟩ := kind_check e
      obtain ⟨T, c1, hT, hne, hconst⟩ := hLn.check_read hτ.req hτ.depth h0
      have hp1 := hτ.prog hgk
        (hLn.mem T hT _ (List.mem_of_getElem? (hconst T (Nat.le_refl _))))
      dsimp only [Prog] at hp1
      obtain ⟨Lg', Rg', -, -, -, hc1⟩ := hp1
      cases c1 with
      | reading => exact absurd rfl hne
      | off => cases Reads.unique hreads hc1
      | opened subs1 =>
        obtain ⟨ps', hr', -, qlen, qall⟩ := hc1
        cases Reads.unique hreads hr'
        have sub : ∀ j' ∈ subs1, ∃ (nn : Nat) (p : R), ps[nn]? = some p ∧ goalAt (τ T) j' =
            some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩) := by
          intro j' hj'
          obtain ⟨nn, hnn⟩ := List.getElem?_of_mem hj'
          have hlt : nn < ps.length := by
            rw [← qlen]
            exact (List.getElem?_eq_some_iff.1 hnn).1
          obtain ⟨j'', hj'', hg''⟩ := qall nn ps[nn] (List.getElem?_eq_getElem hlt)
          rw [hnn] at hj''
          cases hj''
          exact ⟨nn, _, List.getElem?_eq_getElem hlt, hg''⟩
        have hempty : ∀ j' ∈ subs1, ∀ r3, (τ r3).answers j' = [] := fun j' hj' => by
          obtain ⟨nn, p, hp', hg'⟩ := sub j' hj'
          exact (iface nn p hp' j' T hg').1
        have each : ∀ j' ∈ subs1, ∃ T', ∀ r1, T' ≤ r1 → Still τ r1 j' ∧
            ((τ r1).isDone j' || X.contains j') = true := fun j' hj' => by
          obtain ⟨nn, p, hp', hg'⟩ := sub j' hj'
          refine (iface nn p hp' j' T hg').2 (hτ.opened_of_settled hg' fun r' => ?_)
          obtain ⟨r2, hr2', hr2, -, hfed, -⟩ := hLn.worked (max r' T)
          have hs2 := hconst (r2 + 1) (by omega)
          exact ⟨r2, by omega, hfed _ (List.mem_of_getElem? hs2)
            (fun j2 hj2 => hempty j2 hj2 _) j' hj'⟩
        obtain ⟨T2, hT2⟩ := eventually_forall_mem subs1 _ each
        refine ⟨max T2 T, fun r1 hr1 => ⟨_, hLn.mem (r1 + 1) (by omega) _
          (List.mem_of_getElem? (hconst (r1 + 1) (by omega))), ?_,
          fun _ _ _ _ _ _ e => by cases e⟩⟩
        simp only [Strat.quiet, Strat.pending, Bool.not_false, Bool.true_and,
          List.all_eq_true, Bool.and_eq_true, List.isEmpty_iff]
        exact fun j' hj' => ⟨(hT2 j' hj' (r1 + 1) (by omega)).2, hempty j' hj' _⟩

/-- **What one run completes, every run completes.** A goal whose table is
complete in a run of requests has a complete table in every run of requests
that does not neglect it and keeps no answer covered by an earlier one. -/
theorem IsRun.transfer (hσ : IsRun σ) (hτ : IsRun τ)
    (hN : ∀ r j, NoCov D (((τ r).answers j).map Ans.span)) {r i : Nat} {g : GoalOf R Rel}
    (hi : goalAt (σ r) i = some g) (hd : (σ r).isDone i = true) {r' k : Nat}
    (hk : goalAt (τ r') k = some g) (ho : Opened τ k) : EvDone τ k := by
  obtain ⟨ρ, hρ⟩ := hσ.founded r
  have main : ∀ n i g, goalAt (σ r) i = some g → (σ r).isDone i = true → ρ i = n →
      ∀ r' k, goalAt (τ r') k = some g → Opened τ k → EvDone τ k := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro i g hi hd hn r' k hk ho
      by_contra hnd
      obtain ⟨X, hX⟩ := waits_list (σ := σ) hτ ρ r n
      have hkX : k ∈ X := (hX k).2 ⟨i, g, r', hi, hd, hn, hk, ho, hnd⟩
      obtain ⟨T, hT⟩ := eventually_forall_mem X
        (fun k r1 => ∃ s, IsStrat τ k (r1 + 1) s ∧
          s.quiet (τ (r1 + 1)) (fun j => (τ (r1 + 1)).isDone j || X.contains j) = true ∧
          ∀ kd l side o todo subs, s = .push kd l side o todo subs →
            (τ r1).isDone side = true)
        (fun k hk' => hσ.waits_quiet hL hτ hN hρ
          (fun i g hi hd hlt r' k hk ho => ih (ρ i) hlt i g hi hd rfl r' k hk ho) hX
          ((hX k).1 hk'))
      have := (hτ.req.req T).closed X (fun k hk' => by
        obtain ⟨s, ⟨t', gs, gr, ht', hg, hgr, hs⟩, hq, hp⟩ := hT k hk' T (Nat.le_refl _)
        exact ⟨t', ht', gs, hg, gr, hgr, s, hs, hq, hp⟩) k hkX
      exact hnd ⟨T + 1, this⟩
  exact main (ρ i) i g hi hd rfl r' k hk ho

end

end Symmetric

end RwLog
