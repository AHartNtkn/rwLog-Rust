/-
# A goal that completes in one run completes in every run that asks it

Two runs of the tabled machine on the same program, from different roots,
with an unfolding race whose verdict stays final at greater depths. A goal
that is complete in the first run and has a table in the second is complete
in the second in the end (`host_done`).

The rounds of the two runs do not line up: a goal gets its table in the
second run at another round, and its answers enter in another order. What
lines up is what cannot change any more. The tables of the first run are
finitely many, so there is a round of the second run after which none of
their goals gets a table, completes, or comes to cover an answer of the first
run for the first time (`stable`). At that round the goals that complete
together in the first run and are not yet complete in the second gain
nothing, because the table of the first run is full and its answers are
covered; and each has the strategy it completed with, because a complete
table of the first run is complete in the second by induction, and two full
tables of one goal have the same maximal answers (`maxima_same`), so the
goals pushed for them are the same goals. So they complete together in the
second run (`done_of_closed`).
-/
import RwLog.Rungs.Tabled.Reading
import RwLog.Rungs.Tabled.Eventually

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## A round, goal by goal -/

section round

variable (K : Kernel R Cost) (hK : K.Refines D) (U : GOracle R Rel (Ans D P) Cost)
  (ts : List (TableOf R Rel (Ans D P))) (depth : Nat)

/-- The answers that enter the table of an incomplete goal in the round. -/
def gainG (g : GoalOf R Rel) : List (Ans D P) :=
  (fresh (K := DerivationKernel.over D K hK P) (ansOf ts g) (prodG K hK U ts depth g).1).val

variable {K hK U ts depth}

theorem gain_goal {g : GoalOf R Rel} {i : Nat} (hi : idx ts g = some i)
    (hd : isDone ts g = false) :
    ∃ hil : i < ts.length, ts[i].done = false ∧ ts[i].goal = g ∧
      gainOf K hK U ts depth ts[i] = gainG K hK U ts depth g := by
  obtain ⟨hil, hg, -⟩ := idx_some.1 hi
  obtain ⟨_, ea⟩ := ansOf_of_idx hi
  obtain ⟨_, ed⟩ := isDone_of_idx hi
  have hd' : ts[i].done = false := by rw [← ed]; exact hd
  refine ⟨hil, hd', hg, ?_⟩
  unfold gainOf gainG
  rw [outOf_live K hK U ts depth hd', ea, hg]

/-- The goals whose tables complete in the round. -/
def Closes (K : Kernel R Cost) (hK : K.Refines D) (U : GOracle R Rel (Ans D P) Cost)
    (ts : List (TableOf R Rel (Ans D P))) (depth : Nat) (g : GoalOf R Rel) : Prop :=
  ∃ i, idx ts g = some i ∧ i ∈ closing K hK U ts depth

/-- A goal with a table is complete after the round when it was or its table
completes. -/
theorem isDone_next {g : GoalOf R Rel} {i : Nat} (hi : idx ts g = some i) :
    isDone (nextTables K hK U ts depth) g = true ↔
      isDone ts g = true ∨ Closes K hK U ts depth g := by
  obtain ⟨hil, -, e⟩ := ansOf_next (K := K) (hK := hK) (U := U) (depth := depth) hi
  obtain ⟨_, ed⟩ := isDone_of_idx hi
  rw [e, ed, Bool.or_eq_true, List.contains_iff_mem]
  refine or_congr Iff.rfl ⟨fun h => ⟨i, hi, h⟩, ?_⟩
  rintro ⟨j, hj, h⟩
  rw [hi] at hj
  cases hj
  exact h

/-- A goal that completes in the round was incomplete, gains nothing, and has
a strategy all of whose goals have a table and are complete or complete with
it. -/
theorem closes_spec {g : GoalOf R Rel} (h : Closes K hK U ts depth g) :
    (∃ i, idx ts g = some i) ∧ isDone ts g = false ∧ gainG K hK U ts depth g = [] ∧
      ∃ strat ∈ (prodG K hK U ts depth g).2, ∀ d ∈ strat, (∃ j, idx ts d = some j) ∧
        (isDone ts d = true ∨ Closes K hK U ts depth d) := by
  obtain ⟨i, hi, hc⟩ := h
  obtain ⟨hil, hd, hgain, strat, hs, hdeps⟩ := mem_closing K hK U ts depth hc
  obtain ⟨_, ed⟩ := isDone_of_idx hi
  have hd' : isDone ts g = false := by rw [ed]; exact hd
  obtain ⟨_, -, hg, eg⟩ := gain_goal (K := K) (hK := hK) (U := U) (depth := depth) hi hd'
  refine ⟨⟨i, hi⟩, hd', by rw [← eg]; exact hgain, strat, ?_, fun d hdm => ?_⟩
  · rw [outOf_live K hK U ts depth hd, hg] at hs
    exact hs
  · obtain ⟨j, hj, hc'⟩ := hdeps d hdm
    refine ⟨⟨j, hj⟩, hc'.imp (fun ⟨hjl, h⟩ => ?_) fun h => ⟨j, hj, h⟩⟩
    obtain ⟨_, e⟩ := isDone_of_idx hj
    rw [e]; exact h

/-- Goals that are incomplete, gain nothing and each have a strategy all of
whose goals have a table and are complete or among them, are complete after
the round. -/
theorem done_of_closed (Q : GoalOf R Rel → Prop)
    (hQ : ∀ g, Q g → (∃ i, idx ts g = some i) ∧ isDone ts g = false ∧
      gainG K hK U ts depth g = [] ∧
      ∃ strat ∈ (prodG K hK U ts depth g).2, ∀ d ∈ strat, (∃ j, idx ts d = some j) ∧
        (isDone ts d = true ∨ Q d)) :
    ∀ g, Q g → isDone (nextTables K hK U ts depth) g = true := by
  classical
  let S : List Nat := (List.range ts.length).filter fun i =>
    decide (∃ g, Q g ∧ idx ts g = some i)
  have hS : ∀ i, i ∈ S ↔ ∃ g, Q g ∧ idx ts g = some i := by
    intro i
    simp only [S, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun ⟨g, hg, hi⟩ => ⟨(idx_some.1 hi).1, g, hg, hi⟩⟩
  have key := closing_of_closed (K := K) (hK := hK) (U := U) (ts := ts) (depth := depth) S
    (fun i hi => by
      obtain ⟨g, hg, hgi⟩ := (hS i).1 hi
      obtain ⟨-, hd, hgain, strat, hs, hdeps⟩ := hQ g hg
      obtain ⟨hil, hd', hgg, eg⟩ := gain_goal (K := K) (hK := hK) (U := U) (depth := depth) hgi hd
      refine ⟨hil, hd', by rw [eg]; exact hgain, strat, ?_, fun d hdm => ?_⟩
      · rw [outOf_live K hK U ts depth hd', hgg]; exact hs
      · obtain ⟨⟨j, hj⟩, hc⟩ := hdeps d hdm
        refine ⟨j, hj, hc.imp (fun h => ?_) fun h => (hS j).2 ⟨d, h, hj⟩⟩
        obtain ⟨hjl, e⟩ := isDone_of_idx hj
        exact ⟨hjl, by rw [← e]; exact h⟩)
  intro g hg
  obtain ⟨⟨i, hi⟩, -⟩ := hQ g hg
  exact (isDone_next hi).2 (.inr ⟨i, hi, key i ((hS i).2 ⟨g, hg, hi⟩)⟩)

end round

/-! ## Full tables -/

section full

variable (hL : D.Lawful P.sorts.interp)
include hL

omit [DecidableEq R] in
/-- An answer of a goal relates the pairs of a derivation of its node between
its boundaries. -/
theorem ans_gdn {g : GoalOf R Rel} {a : Ans D P} (ha : a.goal = toGoal g) :
    ∃ k G, G ∈ GDn P k g.node ∧ den P.sorts.interp a.span = pairsOf P g G := by
  obtain ⟨s, hs, e⟩ := a.valid.2 hL
  rw [ha] at hs e
  obtain ⟨k, hk⟩ := mem_gd_iff.1 (show s.den ∈ GD P g.node from hs.derivesG)
  exact ⟨k, s.den, hk, e⟩

omit [DecidableEq R] in
/-- A full table covers every answer of its goal. -/
theorem full_covers {t : TableOf R Rel (Ans D P)} (hf : Full P t) {a : Ans D P}
    (ha : a.goal = toGoal t.goal) : ∃ b ∈ t.answers, covB D P b a = true := by
  obtain ⟨k, G, hG, e⟩ := ans_gdn hL ha
  obtain ⟨b, hb, hsub⟩ := hf k G hG (e ▸ hL.live a.span)
  exact ⟨b, hb, (covB_iff hL b a).2 (e ▸ hsub)⟩

omit [DecidableEq R] in
/-- Two lists of answers that cover each other have the same maximal
answers. -/
theorem maxima_same {xs xs' : List (Ans D P)}
    (h : ∀ a ∈ xs', ∃ b ∈ xs, covB D P b a = true)
    (h' : ∀ a ∈ xs, ∃ b ∈ xs', covB D P b a = true) :
    ∀ x' ∈ xs'.maximaBy (covB D P), ∃ x ∈ xs.maximaBy (covB D P), x.span = x'.span := by
  intro x' hx'
  obtain ⟨y, hy, hyx⟩ := h x' (List.mem_maximaBy hx')
  obtain ⟨z, hz, hzy⟩ := List.maximaBy_covers (covB_refl hL) (covB_trans hL) hy
  have hzx := covB_trans hL _ _ _ hzy hyx
  obtain ⟨w, hw, hwz⟩ := h' z (List.mem_maximaBy hz)
  have hxw := maxima_max hx' hw (covB_trans hL _ _ _ hwz hzx)
  exact ⟨z, hz, hL.covers_antisymm hzx (covB_trans hL _ _ _ hxw hwz)⟩

end full

/-! ## A strategy of a goal, from other tables -/

section strat

variable (K : Kernel R Cost) (hK : K.Refines D)

omit [DecidableEq R] in
theorem pushLG_span (g r : GoalOf R Rel) (k : Kind) {x x' : Ans D P} (h : x.span = x'.span) :
    pushLG D g r k x = pushLG D g r k x' := by
  cases k <;> simp [pushLG, h]

omit [DecidableEq R] in
theorem pushRG_span (g l : GoalOf R Rel) (k : Kind) {x x' : Ans D P} (h : x.span = x'.span) :
    pushRG D g l k x = pushRG D g l k x' := by
  cases k <;> simp [pushRG, h]

theorem way_trans {ts ts' : List (TableOf R Rel (Ans D P))} {g : GoalOf R Rel}
    {w : Kind × GoalOf R Rel × GoalOf R Rel} {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.2)
    (H : ∀ d ∈ strat, isDone ts d = true →
      (∃ s₀ ∈ (way (K := DerivationKernel.over D K hK P) ts' g w).val.2, d ∈ s₀) →
      isDone ts' d = true ∧ ∀ x' ∈ (ansOf ts' d).maximaBy (covB D P),
        ∃ x ∈ (ansOf ts d).maximaBy (covB D P), x.span = x'.span) :
    ∃ strat' ∈ (way (K := DerivationKernel.over D K hK P) ts' g w).val.2,
      ∀ d ∈ strat', d ∈ strat := by
  have h₀ : [w.2.1, w.2.2] ∈ (way (K := DerivationKernel.over D K hK P) ts' g w).val.2 :=
    (mem_way_strats K hK _ g w _).2 (.inl rfl)
  rcases (mem_way_strats K hK _ g w strat).1 hs with rfl | ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · exact ⟨_, h₀, fun d hd => hd⟩
  · obtain ⟨hd', hm⟩ := H w.2.1 (by simp) hd ⟨_, h₀, by simp⟩
    refine ⟨_, (mem_way_strats K hK _ g w _).2 (.inr (.inl ⟨hd', rfl⟩)), fun d hdm => ?_⟩
    rcases List.mem_cons.1 hdm with rfl | hdm
    · simp
    · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hdm
      obtain ⟨x, hx, e⟩ := hm x' hx'
      exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, pushLG_span g _ _ e⟩)
  · obtain ⟨hd', hm⟩ := H w.2.2 (by simp) hd ⟨_, h₀, by simp⟩
    refine ⟨_, (mem_way_strats K hK _ g w _).2 (.inr (.inr ⟨hd', rfl⟩)), fun d hdm => ?_⟩
    rcases List.mem_cons.1 hdm with rfl | hdm
    · simp
    · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hdm
      obtain ⟨x, hx, e⟩ := hm x' hx'
      exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, pushRG_span g _ _ e⟩)

/-- A strategy of a goal in some tables gives one in other tables with no
other goals, when each complete goal of it that the other tables ask for is
complete there with the same maximal answers. -/
theorem strat_trans {ts ts' : List (TableOf R Rel (Ans D P))} {g : GoalOf R Rel}
    {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.2)
    (H : ∀ d ∈ strat, isDone ts d = true →
      (∃ s₀ ∈ (produceTables (K := DerivationKernel.over D K hK P) ts' g).val.2, d ∈ s₀) →
      isDone ts' d = true ∧ ∀ x' ∈ (ansOf ts' d).maximaBy (covB D P),
        ∃ x ∈ (ansOf ts d).maximaBy (covB D P), x.span = x'.span) :
    ∃ strat' ∈ (produceTables (K := DerivationKernel.over D K hK P) ts' g).val.2,
      ∀ d ∈ strat', d ∈ strat := by
  cases hv : g.node.view.forget with
  | span u =>
    rw [produceTables_span K hK ts g hv] at hs
    exact ⟨strat, by rw [produceTables_span K hK ts' g hv]; exact hs, fun d hd => hd⟩
  | call n f =>
    obtain ⟨b0, hb0⟩ := forget_call (P := P) hv
    rw [produceTables_call K hK ts g hv hb0] at hs
    exact ⟨strat, by rw [produceTables_call K hK ts' g hv hb0]; exact hs, fun d hd => hd⟩
  | union xs =>
    rw [produceTables_union K hK ts g hv] at hs
    exact ⟨strat, by rw [produceTables_union K hK ts' g hv]; exact hs, fun d hd => hd⟩
  | chain xs =>
    rw [produceTables_chain K hK ts g hv] at hs
    rw [produceTables_chain K hK ts' g hv] at H ⊢
    obtain ⟨r, hr, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    obtain ⟨s', hs', hsub⟩ := way_trans K hK hs fun d hd hdn ⟨s₀, hs₀, hds⟩ =>
      H d hd hdn ⟨s₀, List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨w, hw, rfl⟩, hs₀⟩, hds⟩
    exact ⟨s', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨w, hw, rfl⟩, hs'⟩, hsub⟩
  | meet xs =>
    rw [produceTables_meet K hK ts g hv] at hs
    rw [produceTables_meet K hK ts' g hv] at H ⊢
    obtain ⟨r, hr, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    obtain ⟨s', hs', hsub⟩ := way_trans K hK hs fun d hd hdn ⟨s₀, hs₀, hds⟩ =>
      H d hd hdn ⟨s₀, List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨w, hw, rfl⟩, hs₀⟩, hds⟩
    exact ⟨s', List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨w, hw, rfl⟩, hs'⟩, hsub⟩

end strat

/-! ## What stops changing -/

/-- Finitely many facts that stay true once true are all true from some round
on, those that ever are. -/
theorem stable {ι : Type} (p : ι → Nat → Prop) (hp : ∀ i r r', r ≤ r' → p i r → p i r')
    (l : List ι) : ∃ R₀, ∀ i ∈ l, ∀ r, p i r → ∀ R, R₀ ≤ R → p i R := by
  classical
  induction l with
  | nil => exact ⟨0, fun i hi => by cases hi⟩
  | cons i l ih =>
    obtain ⟨R₀, h⟩ := ih
    by_cases hi : ∃ r, p i r
    · obtain ⟨r, hr⟩ := hi
      refine ⟨max R₀ r, fun j hj r' hr' R hR => ?_⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hp _ r R (le_trans (le_max_right _ _) hR) hr
      · exact h j hj r' hr' R (le_trans (le_max_left _ _) hR)
    · refine ⟨R₀, fun j hj r' hr' R hR => ?_⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact absurd ⟨r', hr'⟩ hi
      · exact h j hj r' hr' R hR

/-! ## Runs, goal by goal -/

section run

variable {K : Kernel R Cost} {hK : K.Refines D} {U : GOracle R Rel (Ans D P) Cost} {root : Rel}

/-- A complete goal stays complete. -/
theorem done_mono {r r' : Nat} (h : r ≤ r') {g : GoalOf R Rel}
    (hd : isDone (tablesAt K hK U root r) g = true) :
    isDone (tablesAt K hK U root r') g = true := by
  obtain ⟨i, hi⟩ := idx_of_done hd
  obtain ⟨hil, e⟩ := isDone_of_idx hi
  obtain ⟨_, e'⟩ := isDone_of_idx (idx_mono h hi)
  obtain ⟨_, -, -, hm⟩ := at_mono h hil
  rw [e']
  exact hm (by rw [← e]; exact hd)

/-- A goal keeps its answers. -/
theorem mem_ans_mono {r r' : Nat} (h : r ≤ r') {g : GoalOf R Rel} {a : Ans D P}
    (ha : a ∈ ansOf (tablesAt K hK U root r) g) : a ∈ ansOf (tablesAt K hK U root r') g := by
  obtain ⟨i, hi⟩ := idx_of_ans ha
  obtain ⟨hil, e⟩ := ansOf_of_idx hi
  obtain ⟨_, e'⟩ := ansOf_of_idx (idx_mono h hi)
  obtain ⟨_, -, hm, -⟩ := at_mono h hil
  rw [e']
  exact hm a (by rw [← e]; exact ha)

/-- No goal is complete before the first round. -/
theorem not_done_zero (g : GoalOf R Rel) : isDone (tablesAt K hK U root 0) g = false := by
  cases h : isDone (tablesAt K hK U root 0) g with
  | false => rfl
  | true =>
    obtain ⟨i, hi⟩ := idx_of_done h
    obtain ⟨hil, e⟩ := isDone_of_idx hi
    have h0 : i = 0 := by simpa [tablesAt] using hil
    subst h0
    rw [e] at h
    simp [tablesAt] at h

/-- A goal complete after a round was complete or completes in it. -/
theorem done_step {r : Nat} {g : GoalOf R Rel}
    (h : isDone (tablesAt K hK U root (r + 1)) g = true) :
    isDone (tablesAt K hK U root r) g = true ∨ Closes K hK U (tablesAt K hK U root r) r g := by
  obtain ⟨j, hj⟩ := idx_of_done h
  have hj' : idx (nextTables K hK U (tablesAt K hK U root r) r) g = some j := hj
  rcases idx_next_cases hj' with ⟨i, hi⟩ | ⟨hn, hg⟩
  · exact (isDone_next hi).1 h
  · have h' : isDone (nextTables K hK U (tablesAt K hK U root r) r) g = true := h
    rw [(idx_next_new hn hg).2.2] at h'
    cases h'

/-- The goals of the strategies of an incomplete goal have tables after the
round. -/
theorem asked {r : Nat} {g : GoalOf R Rel} {i : Nat} (hi : idx (tablesAt K hK U root r) g = some i)
    (hd : isDone (tablesAt K hK U root r) g = false) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (prodG K hK U (tablesAt K hK U root r) r g).2) {d : GoalOf R Rel}
    (hdm : d ∈ strat) : ∃ j, idx (tablesAt K hK U root (r + 1)) d = some j := by
  obtain ⟨hil, hd', hg, -⟩ := gain_goal (K := K) (hK := hK) (U := U) (depth := r) hi hd
  refine requested (List.getElem_mem hil) (strat := strat) ?_ hdm
  rw [outOf_live K hK U _ r hd', hg]
  exact hs

end run

section covered

variable {K : Kernel R Cost} {hK : K.Refines D} {U : GOracle R Rel (Ans D P) Cost}
  {ts : List (TableOf R Rel (Ans D P))} {depth : Nat}

/-- A table that covers every answer of its goal gains nothing. -/
theorem gain_nil_of_covered (hU : UOk D P U) (hT : TablesOk D ts) {g : GoalOf R Rel} {i : Nat}
    (hi : idx ts g = some i) (hd : isDone ts g = false)
    (hc : ∀ c : Ans D P, c.goal = toGoal g → ∃ b ∈ ansOf ts g, covB D P b c = true) :
    gainG K hK U ts depth g = [] := by
  obtain ⟨hil, hd', hg, e⟩ := gain_goal (K := K) (hK := hK) (U := U) (depth := depth) hi hd
  rw [← e]
  refine List.eq_nil_iff_forall_not_mem.2 fun a ha => ?_
  unfold gainOf at ha
  obtain ⟨hmem, hno⟩ := mem_fresh K hK ha
  have hgoal := out_goal K hK hU depth hT (List.getElem_mem hil) hmem
  rw [hg] at hgoal
  obtain ⟨b, hb, hcov⟩ := hc a hgoal
  obtain ⟨_, ea⟩ := ansOf_of_idx hi
  rw [ea] at hb
  rw [hno b hb] at hcov
  cases hcov

/-- The table of a complete goal covers every answer of the goal. -/
theorem done_covers (hL : D.Lawful P.sorts.interp) (hI : Inv D P ts) {g : GoalOf R Rel}
    (hd : isDone ts g = true) {a : Ans D P} (ha : a.goal = toGoal g) :
    ∃ b ∈ ansOf ts g, covB D P b a = true := by
  obtain ⟨i, hi⟩ := idx_of_done hd
  obtain ⟨hil, hg, -⟩ := idx_some.1 hi
  obtain ⟨_, ea⟩ := ansOf_of_idx hi
  obtain ⟨_, ed⟩ := isDone_of_idx hi
  rw [ea]
  exact full_covers hL (hI.full _ (List.getElem_mem hil) (by rw [← ed]; exact hd))
    (by rw [hg]; exact ha)

end covered

/-! ## The second run completes what the first completed -/

section host

variable {K : Kernel R Cost} {hK : K.Refines D} {U : GOracle R Rel (Ans D P) Cost} {ns nh : Rel}
  (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
  (hmono : ∀ n n' g, n ≤ n' → GoalOk D g → (U n g).val.1 = true → (U n' g).val.1 = true)
  (hns : GoalOk D (⟨none, ns, none⟩ : GoalOf R Rel))
  (hnh : GoalOk D (⟨none, nh, none⟩ : GoalOf R Rel))

include hL hP hU hmono hns hnh in
/-- The goals that complete together in a round of the first run, if those
complete before it are complete in the second run in the end. -/
theorem host_step (r : Nat)
    (ih : ∀ g, isDone (tablesAt K hK U ns r) g = true →
      (∃ r₁ j, idx (tablesAt K hK U nh r₁) g = some j) →
      ∃ r', isDone (tablesAt K hK U nh r') g = true) :
    ∀ g, Closes K hK U (tablesAt K hK U ns r) r g →
      (∃ r₁ j, idx (tablesAt K hK U nh r₁) g = some j) →
      ∃ r', isDone (tablesAt K hK U nh r') g = true := by
  classical
  have hIS := inv_at hL hP hU hns (K := K) (hK := hK)
  have hIH := inv_at hL hP hU hnh (K := K) (hK := hK)
  -- the goals and the answers of the first run
  obtain ⟨N₁, h₁⟩ := stable (fun (g : GoalOf R Rel) N => ∃ j, idx (tablesAt K hK U nh N) g = some j)
    (fun g a b hab ⟨j, hj⟩ => ⟨j, idx_mono hab hj⟩) ((tablesAt K hK U ns r).map (·.goal))
  obtain ⟨N₂, h₂⟩ := stable (fun (g : GoalOf R Rel) N => isDone (tablesAt K hK U nh N) g = true)
    (fun g a b hab h => done_mono hab h) ((tablesAt K hK U ns r).map (·.goal))
  obtain ⟨N₃, h₃⟩ := stable
    (fun (x : GoalOf R Rel × Ans D P) N =>
      ∃ b ∈ ansOf (tablesAt K hK U nh N) x.1, covB D P b x.2 = true)
    (fun x a b hab ⟨c, hc, h⟩ => ⟨c, mem_ans_mono hab hc, h⟩)
    ((tablesAt K hK U ns r).flatMap fun t => t.answers.map fun a => (t.goal, a))
  obtain ⟨N₀, hr, hN₁, hN₂, hN₃⟩ : ∃ N₀, r ≤ N₀ ∧ N₁ ≤ N₀ ∧ N₂ ≤ N₀ ∧ N₃ ≤ N₀ :=
    ⟨max r (max N₁ (max N₂ N₃)), by omega, by omega, by omega, by omega⟩
  have memGs : ∀ g, (∃ i, idx (tablesAt K hK U ns r) g = some i) →
      g ∈ (tablesAt K hK U ns r).map (·.goal) := fun g hg => by
    obtain ⟨t, ht, e⟩ := idx_isSome.1 hg
    exact List.mem_map.2 ⟨t, ht, e⟩
  have host : ∀ g, (∃ i, idx (tablesAt K hK U ns r) g = some i) →
      (∃ r₁ j, idx (tablesAt K hK U nh r₁) g = some j) →
      ∃ j, idx (tablesAt K hK U nh N₀) g = some j :=
    fun g hg ⟨r₁, hj⟩ => h₁ g (memGs g hg) r₁ hj N₀ hN₁
  have doneH : ∀ d, isDone (tablesAt K hK U ns r) d = true →
      (∃ r₁ j, idx (tablesAt K hK U nh r₁) d = some j) →
      isDone (tablesAt K hK U nh N₀) d = true := fun d hd hh => by
    obtain ⟨r', h⟩ := ih d hd hh
    exact h₂ d (memGs d (idx_of_done hd)) r' h N₀ hN₂
  -- the second run covers every answer of a goal that completes
  have cov : ∀ g, Closes K hK U (tablesAt K hK U ns r) r g → ∀ j,
      idx (tablesAt K hK U nh N₀) g = some j → ∀ c : Ans D P, c.goal = toGoal g →
      ∃ b ∈ ansOf (tablesAt K hK U nh N₀) g, covB D P b c = true := by
    intro g hg j hj c hc
    obtain ⟨⟨i, hi⟩, hnd, hgain, -⟩ := closes_spec hg
    have hdone : isDone (tablesAt K hK U ns (r + 1)) g = true := (isDone_next hi).2 (.inr hg)
    obtain ⟨a, ha, hac⟩ := done_covers hL (hIS (r + 1)) hdone hc
    obtain ⟨hil, ea, -⟩ := ansOf_next (K := K) (hK := hK) (U := U) (depth := r) hi
    obtain ⟨_, -, hgg, eg⟩ := gain_goal (K := K) (hK := hK) (U := U) (depth := r) hi hnd
    have ha' : a ∈ (tablesAt K hK U ns r)[i].answers := by
      have : a ∈ ansOf (nextTables K hK U (tablesAt K hK U ns r) r) g := ha
      rw [ea, eg, hgain, List.append_nil] at this
      exact this
    have hmem := List.getElem_mem hil
    have hag : a.goal = toGoal g := by rw [← hgg]; exact ((hIS r).ok _ hmem).2 a ha'
    obtain ⟨k, G, hG, e⟩ := ans_gdn hL hag
    obtain ⟨hjl, hjg, -⟩ := idx_some.1 hj
    obtain ⟨r', hr', hi', b', hb', hsub⟩ := eventually (K := K) (hK := hK) (U := U) (root := nh)
      hL hP hU hnh k _ N₀ j hjl rfl G (by rw [hjg]; exact hG)
      (by rw [hjg, ← e]; exact hL.live _)
    rw [hjg, ← e] at hsub
    obtain ⟨_, eb⟩ := ansOf_of_idx (idx_mono hr' hj)
    obtain ⟨b, hb, hba⟩ := h₃ (g, a)
      (List.mem_flatMap.2 ⟨_, hmem, List.mem_map.2 ⟨a, ha', by rw [hgg]⟩⟩) r'
      ⟨b', by rw [eb]; exact hb', (covB_iff hL b' a).2 hsub⟩ N₀ hN₃
    exact ⟨b, hb, covB_trans hL _ _ _ hba hac⟩
  -- the goals that complete together and are not complete in the second run
  have hQ := done_of_closed (K := K) (hK := hK) (U := U) (ts := tablesAt K hK U nh N₀)
    (depth := N₀)
    (fun g => Closes K hK U (tablesAt K hK U ns r) r g ∧
      (∃ j, idx (tablesAt K hK U nh N₀) g = some j) ∧
      isDone (tablesAt K hK U nh N₀) g = false)
    (fun g ⟨hg, ⟨j, hj⟩, hndH⟩ => by
      refine ⟨⟨j, hj⟩, hndH, gain_nil_of_covered hU (hIH N₀).ok hj hndH (cov g hg j hj), ?_⟩
      obtain ⟨⟨i, hi⟩, hnd, -, strat, hs, hdeps⟩ := closes_spec hg
      obtain ⟨hil, hgg, -⟩ := idx_some.1 hi
      have hgok : GoalOk D g := hgg ▸ ((hIS r).ok _ (List.getElem_mem hil)).1
      rcases (mem_prodG_snd K hK U _ r g strat).1 hs with ⟨hv, rfl⟩ | hs'
      · exact ⟨[], (mem_prodG_snd K hK U _ N₀ g []).2 (.inl ⟨hmono r N₀ g hr hgok hv, rfl⟩),
          fun d hd => by cases hd⟩
      · obtain ⟨strat', hs'', hsub⟩ := strat_trans K hK hs'
          (ts' := tablesAt K hK U nh N₀) (fun d hd hdn ⟨s₀, hs₀, hds⟩ => by
            have hask := asked hj hndH ((mem_prodG_snd K hK U _ N₀ g s₀).2 (.inr hs₀)) hds
            have hdh := doneH d hdn ⟨N₀ + 1, hask⟩
            exact ⟨hdh, maxima_same hL
              (fun a ha => done_covers hL (hIS r) hdn (ansOf_goal (hIH N₀).ok ha))
              (fun a ha => done_covers hL (hIH N₀) hdh (ansOf_goal (hIS r).ok ha))⟩)
        refine ⟨strat', (mem_prodG_snd K hK U _ N₀ g strat').2 (.inr hs''), fun d hd => ?_⟩
        obtain ⟨hdS, hc⟩ := hdeps d (hsub d hd)
        have hask := asked hj hndH ((mem_prodG_snd K hK U _ N₀ g strat').2 (.inr hs'')) hd
        have hdH := host d hdS ⟨N₀ + 1, hask⟩
        refine ⟨hdH, ?_⟩
        rcases hc with hc | hc
        · exact .inl (doneH d hc ⟨N₀ + 1, hask⟩)
        · rcases Bool.eq_false_or_eq_true (isDone (tablesAt K hK U nh N₀) d) with hdd | hdd
          · exact .inl hdd
          · exact .inr ⟨hc, hdH, hdd⟩)
  intro g hg hh
  have hjH := host g (closes_spec hg).1 hh
  rcases Bool.eq_false_or_eq_true (isDone (tablesAt K hK U nh N₀) g) with hdd | hdd
  · exact ⟨N₀, hdd⟩
  · exact ⟨N₀ + 1, hQ g ⟨hg, hjH, hdd⟩⟩

include hL hP hU hmono hns hnh in
/-- **A goal that is complete in one run is complete, in the end, in every
run in which it has a table.** -/
theorem host_done : ∀ (r : Nat) (g : GoalOf R Rel), isDone (tablesAt K hK U ns r) g = true →
    (∃ r₁ j, idx (tablesAt K hK U nh r₁) g = some j) →
    ∃ r', isDone (tablesAt K hK U nh r') g = true
  | 0, g, h, _ => by rw [not_done_zero] at h; cases h
  | r + 1, g, h, hh => by
    rcases done_step h with h | h
    · exact host_done r g h hh
    · exact host_step hL hP hU hmono hns hnh r (host_done r) g h hh

end host

end Tabled

end RwLog
