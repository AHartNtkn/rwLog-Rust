/-
# What is certified to complete, every run completes

Two runs of requests of one program need not open the same goals, nor in the
same order, and another machine has no requests at all. What every run of
the engine completes is stated with no run in it.

A certificate (`Cert`) is a finite set of goals `C`, an order `ρ` on them and
answers `A g` of each that cover every answer of the goal, with a reason for
each goal: every run completes it (`Completes`), or a rule completes it from
goals of the certificate that stand no higher (`Why`): a span; the body of a
call or the members of a union; the two sides of a split; one side of a
split, standing lower, and the goals pushed for its maximal answers; or a
check of an edge whose interfaces all have no answer.

A goal of a certificate has a complete table in every run that does not
neglect it, provided no answer of a table of that run covers a later one
(`Cert.completes`). By induction along the order, take the tables of the run
whose goals stand at one level and that never complete (`Waits`). Each has a
round in infinitely many requests, so its groups work for ever
(`Requests.lines`), and it has a strategy of the kind of its reason (`Full`).
That strategy reads tables of the goals the reason names:

* what an edge reads is a fact of the program (`Reads.unique`), so a check
  opens the goals of the reason;
* a complete table of a goal has the maximal answers the certificate has for
  it (`Cert.maxima`), so a push opens the goals of the reason.

The tables it reads have goals that stand no higher, so each is complete at
some time or is one of those that wait; and each gains no answer from some
time on (`Cert.settles`): every answer a run finds is covered by the answers
of the certificate (`Cert.covered`), which the run then has covered itself.
So the strategy runs out of work (`Settle.lean`), and the tables that wait
are closed under the condition of completion: they complete (`Req.closed`).

The tables of a run of the engine that are complete at a time are a
certificate (`IsRun.fcert`, from `Ranked`), one whose goals with no reason
among the others are chains with a final unfolding (`FCert`); so a goal
whose table is complete
in one run has a complete table in every run that does not neglect it
(`IsRun.transfer`). The complete tables of the tabled machine are another
(`Rungs/Symmetric/FromTabled.lean`).
-/
import RwLog.Rungs.Symmetric.Settle
import RwLog.Rungs.Symmetric.Fair
import RwLog.Rungs.Symmetric.EdgeSame

namespace RwLog

namespace Symmetric

open Answer Saturation Goals

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  {U : GOracle R Rel (Ans D P) Cost}

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

/-- **A table that has rounds for ever keeps a strategy of every kind in a
group that works for ever**: from some state on its groups are full, and
each strategy of each of them is a place of a line. -/
theorem IsRun.live_strat (hτ : IsRun U τ) {r' k : Nat} {g : GoalOf R Rel}
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

/-- **A table that has rounds for ever and a race with a final verdict
completes.** -/
theorem IsRun.race_done (hτ : IsRun U τ) {r' k : Nat} {g : GoalOf R Rel}
    (hgk : goalAt (τ r') k = some g) (hlive : Live τ k) (hh : hasRace g = true) {n : Nat}
    (hfin : (U n g).val.1 = true) : EvDone τ k := by
  obtain ⟨r, t, ht, hd⟩ := hτ.req.race_done (Rc := raceSem U) k hlive (g := g) (n := n)
    (fun r t ht => hτ.goal_any (goalAt_of_table ht) hgk) hh hfin
  exact ⟨r, by rw [isDone_of_table ht]; exact hd⟩

/-! ## Why a goal completes -/

/-- Every run of requests that does not neglect the goal `g`, and keeps no
answer covered by an earlier one, completes it. -/
def Completes (U : GOracle R Rel (Ans D P) Cost) (g : GoalOf R Rel) : Prop :=
  ∀ τ : Nat → StateOf R Rel (Ans D P), IsRun U τ →
    (∀ r j, NoCov D (((τ r).answers j).map Ans.span)) →
    ∀ r' k, goalAt (τ r') k = some g → Opened τ k → EvDone τ k

/-- Why the goal `g` completes, among goals `C` that complete in the order
`ρ` with the answers `A`: it is a span; or the body it calls, or every
member of the union it is, completes no later; or both sides of a split
complete no later; or one side of a split completes sooner, and the goal
pushed for each of its maximal answers completes no later; or the other
side of a split of a chain completes with no answer, no later, under every
interface one side can show. This is what a strategy of the engine with
nothing left to do says, with no engine in it. -/
inductive Why (C : GoalOf R Rel → Prop) (ρ : GoalOf R Rel → Nat)
    (A : GoalOf R Rel → List (Ans D P)) (g : GoalOf R Rel) : Prop
  | span (h : ∃ s, g.node = .span s)
  | copy (c : Bool) (h1 : c = true → ∃ b, Charged.bodyOf P g.node = some b)
      (h2 : c = false → ∃ xs, g.node.view = .union xs)
      (hs : ∀ x ∈ copyMembers P g.node c, C (⟨g.lb, x, g.rb⟩ : GoalOf R Rel) ∧
        ρ (⟨g.lb, x, g.rb⟩ : GoalOf R Rel) ≤ ρ g)
  | join (k : Kind) (L Rg : GoalOf R Rel) (hsp : SplitAt g k L Rg) (hl : C L ∧ ρ L ≤ ρ g)
      (hr : C Rg ∧ ρ Rg ≤ ρ g)
  | push (k : Kind) (L Rg : GoalOf R Rel) (left : Bool) (hsp : SplitAt g k L Rg)
      (hside : C (if left then L else Rg) ∧ ρ (if left then L else Rg) < ρ g)
      (hsub : ∀ x ∈ (A (if left then L else Rg)).maximaBy (covB D P),
        C (pushG D g (if left then Rg.node else L.node) k left x) ∧
          ρ (pushG D g (if left then Rg.node else L.node) k left x) ≤ ρ g)
  | check (L Rg : GoalOf R Rel) (hsp : SplitAt g .seq L Rg) (left : Bool) (ps : List R)
      (hreads : Reads D P (if left then L.node else Rg.node) left (some ps))
      (hall : ∀ p ∈ ps,
        C (if left then (⟨some p, if left then Rg.node else L.node, g.rb⟩ : GoalOf R Rel)
          else ⟨g.lb, if left then Rg.node else L.node, some p⟩) ∧
        ρ (if left then (⟨some p, if left then Rg.node else L.node, g.rb⟩ : GoalOf R Rel)
          else ⟨g.lb, if left then Rg.node else L.node, some p⟩) ≤ ρ g ∧
        A (if left then (⟨some p, if left then Rg.node else L.node, g.rb⟩ : GoalOf R Rel)
          else ⟨g.lb, if left then Rg.node else L.node, some p⟩) = [])

/-- A certificate that the goals `C` complete: they are finitely many; the
answers `A g` are answers of `g` and cover every answer of `g`; and each
goal is completed by every run, or completes for a reason among them
(`Why`), in an order `ρ` in which a side whose answers are pushed stands
lower. Nothing in it is about a run. -/
structure Cert (U : GOracle R Rel (Ans D P) Cost) (C : GoalOf R Rel → Prop)
    (ρ : GoalOf R Rel → Nat) (A : GoalOf R Rel → List (Ans D P)) : Prop where
  fin : ∃ l : List (GoalOf R Rel), ∀ g, C g → g ∈ l
  goal : ∀ g, C g → ∀ a ∈ A g, a.goal = toGoal g
  full : ∀ g, C g → ∀ y : Ans D P, y.goal = toGoal g → ∃ f ∈ A g, covB D P f y = true
  why : ∀ g, C g → Completes U g ∨ Why C ρ A g

variable {C : GoalOf R Rel → Prop} {ρ : GoalOf R Rel → Nat} {A : GoalOf R Rel → List (Ans D P)}

/-- The table at `k` of the run `τ` has the certified goal `g`, which stands
at the level `n`; it is not neglected, and never completes. -/
def WaitsFor (C : GoalOf R Rel → Prop) (ρ : GoalOf R Rel → Nat)
    (τ : Nat → StateOf R Rel (Ans D P)) (n : Nat) (g : GoalOf R Rel) (k : Nat) : Prop :=
  ∃ r', C g ∧ ρ g = n ∧ goalAt (τ r') k = some g ∧ Opened τ k ∧ ¬ EvDone τ k

/-- The tables of `τ` that wait at the level `n`. -/
def Waits (C : GoalOf R Rel → Prop) (ρ : GoalOf R Rel → Nat)
    (τ : Nat → StateOf R Rel (Ans D P)) (n k : Nat) : Prop :=
  ∃ g, WaitsFor C ρ τ n g k

/-- The tables that wait at a level are finitely many: one for each
certified goal. -/
theorem waits_list (hτ : IsRun U τ) (hfin : ∃ l : List (GoalOf R Rel), ∀ g, C g → g ∈ l)
    (ρ : GoalOf R Rel → Nat) (n : Nat) : ∃ X : List Nat, ∀ k, k ∈ X ↔ Waits C ρ τ n k := by
  classical
  obtain ⟨l, hl⟩ := hfin
  refine ⟨l.filterMap fun g =>
    if h : ∃ k, WaitsFor C ρ τ n g k then some (Classical.choose h) else none, fun k => ?_⟩
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨g, -, hg⟩
    split at hg
    · next h =>
      cases hg
      exact ⟨g, Classical.choose_spec h⟩
    · cases hg
  · rintro ⟨g, r', h1, h2, h3, h4, h5⟩
    refine ⟨g, hl g h1, ?_⟩
    have h : ∃ k, WaitsFor C ρ τ n g k := ⟨k, r', h1, h2, h3, h4, h5⟩
    split
    · next h' =>
      obtain ⟨r'', -, -, e3, -, -⟩ := Classical.choose_spec h'
      exact congrArg some (hτ.goal_inj e3 h3)
    · next h' => exact absurd h h'

/-- An answer of the table of a certified goal is covered by an answer of
the certificate. -/
theorem Cert.covers (hC : Cert U C ρ A) (hτ : IsRun U τ) {r' r2 k : Nat} {g : GoalOf R Rel}
    (hg : C g) (hk : goalAt (τ r') k = some g) {y : Ans D P} (hy : y ∈ (τ r2).answers k) :
    ∃ f ∈ A g, covB D P f y = true := by
  obtain ⟨t, ht, hyt⟩ := mem_answers hy
  have hgt : t.goal = g := (hτ.goal_any hk (goalAt_of_table ht)).symm
  have hgi : y.goal = toGoal g := by
    have := ((hτ.good r2).inv.core k t ht).2.2 y hyt
    rw [hgt] at this
    exact this
  exact hC.full g hg y hgi

/-- A goal certified with no answer has no answer in any run. -/
theorem Cert.empty (hC : Cert U C ρ A) (hτ : IsRun U τ) {r' k : Nat} {g : GoalOf R Rel}
    (hg : C g) (he : A g = []) (hk : goalAt (τ r') k = some g) (r2 : Nat) :
    (τ r2).answers k = [] := by
  cases hx : (τ r2).answers k with
  | nil => rfl
  | cons y l =>
    obtain ⟨f, hf, -⟩ := hC.covers hτ hg hk (y := y) (r2 := r2)
      (by rw [hx]; exact List.mem_cons_self)
    rw [he] at hf
    cases hf

section

variable (hL : D.Lawful P.sorts.interp)

include hL

/-- **No run misses what is certified**: an answer of the certificate is
covered by an answer of the table of the goal in a run that does not neglect
it. -/
theorem Cert.covered (hC : Cert U C ρ A) (hτ : IsRun U τ) {r' k : Nat} {g : GoalOf R Rel}
    (hg : C g) (hk : goalAt (τ r') k = some g) (ho : Opened τ k) {f : Ans D P}
    (hf : f ∈ A g) : ∃ r3, ∃ x ∈ (τ r3).answers k, covB D P x f = true := by
  have hv : Valid D P (toGoal g) f.span := by
    rw [← hC.goal g hg f hf]
    exact f.valid
  obtain ⟨a, ha, hsub⟩ := hτ.fair.covers_valid hL (hτ.mem_opened hk ho) hv
  obtain ⟨r3, x, hx, rfl⟩ := (hτ.held_iff hk a).1 ha
  exact ⟨r3, x, hx, (covB_iff hL x f).2 hsub⟩

/-- **The table of a certified goal stops growing**, in a run that does not
neglect the goal and keeps no answer covered by an earlier one: once it
covers every answer of the certificate, an answer it gained would be covered
by one it has. -/
theorem Cert.settles (hC : Cert U C ρ A) (hτ : IsRun U τ)
    (hN : ∀ r j, NoCov D (((τ r).answers j).map Ans.span)) {r' k : Nat}
    {g : GoalOf R Rel} (hg : C g) (hk : goalAt (τ r') k = some g) (ho : Opened τ k) :
    ∃ T, Still τ T k := by
  obtain ⟨T, hT⟩ := eventually_forall_mem (A g)
    (fun f r1 => ∃ x ∈ (τ r1).answers k, covB D P x f = true) (fun f hf => by
      obtain ⟨r3, x, hx, hc⟩ := hC.covered hL hτ hg hk ho hf
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
    obtain ⟨f, hf, hc⟩ := hC.covers hτ hg hk hy
    obtain ⟨x, hx, hc'⟩ := hT f hf T (Nat.le_refl _)
    have hn := hN r1 k
    unfold NoCov at hn
    rw [← e, List.map_append] at hn
    have h1 := (List.pairwise_append.1 hn).2.2 x.span (List.mem_map_of_mem hx) y.span
      (List.mem_map_of_mem List.mem_cons_self)
    have h2 := covB_trans hL _ _ _ hc' hc
    unfold covB at h2
    rw [h1] at h2
    cases h2

/-- **A complete table of a certified goal has the maximal answers of the
certificate.** -/
theorem Cert.maxima (hC : Cert U C ρ A) (hτ : IsRun U τ) {r' r'' k : Nat}
    {g : GoalOf R Rel} (hg : C g) (hk : goalAt (τ r'') k = some g)
    (hd' : (τ r').isDone k = true) :
    ∀ x' ∈ ((τ r').answers k).maximaBy (covB D P),
      ∃ x ∈ (A g).maximaBy (covB D P), x.span = x'.span :=
  maxima_same hL (fun a ha => hC.covers hτ hg hk ha)
    (fun a ha => by
      obtain ⟨r3, f, hf, hc⟩ := hC.covered hL hτ hg hk (.inl ⟨r', hd'⟩) ha
      exact ⟨f, hτ.done_answers hd' r3 hf, hc⟩)

/-- **A table that waits has, from some time on, a strategy with nothing
left to do** that reads only tables that are complete or wait with it, if
the certified goals that stand lower are complete in the run. -/
theorem Cert.waits_quiet (hC : Cert U C ρ A) (hτ : IsRun U τ)
    (hN : ∀ r j, NoCov D (((τ r).answers j).map Ans.span)) {n : Nat}
    (ih : ∀ g, C g → ρ g < n → ∀ r' k, goalAt (τ r') k = some g → Opened τ k → EvDone τ k)
    {X : List Nat} (hX : ∀ k, k ∈ X ↔ Waits C ρ τ n k) {k : Nat}
    (hk : Waits C ρ τ n k) :
    ∃ T, ∀ r1, T ≤ r1 → ∃ s, IsStrat τ k (r1 + 1) s ∧
      s.quiet (τ (r1 + 1)) (fun j => (τ (r1 + 1)).isDone j || X.contains j) = true ∧
      ∀ kd l side o todo subs, s = .push kd l side o todo subs →
        (τ r1).isDone side = true := by
  obtain ⟨g, r', hg, hn, hgk, hop, hnd⟩ := hk
  subst hn
  have hlive : Live τ k := hop.resolve_left hnd
  -- a table read whose goal stands no higher gains no answer, and is complete or waits
  have rd : ∀ j' gj r2, C gj → ρ gj ≤ ρ g → goalAt (τ r2) j' = some gj → Opened τ j' →
      ∃ T, ∀ r1, T ≤ r1 → Still τ r1 j' ∧ ((τ r1).isDone j' || X.contains j') = true := by
    intro j' gj r2 hgj hle hj' ho'
    obtain ⟨T, hT⟩ := hC.settles hL hτ hN hgj hj' ho'
    by_cases hev : EvDone τ j'
    · obtain ⟨r3, h3⟩ := hev
      refine ⟨max T r3, fun r1 hr1 => ⟨hT.mono (by omega), ?_⟩⟩
      rw [((hτ.stable (show r3 ≤ r1 by omega)).isDone h3).1]
      rfl
    · have hw : Waits C ρ τ (ρ g) j' := by
        rcases Nat.lt_or_eq_of_le hle with hlt | he
        · exact absurd (ih gj hgj hlt r2 j' hj' ho') hev
        · exact ⟨gj, r2, hgj, he, hj', ho', hev⟩
      refine ⟨T, fun r1 hr1 => ⟨hT.mono hr1, ?_⟩⟩
      simp [(hX j').2 hw]
  rcases hC.why g hg with hdone | hw
  · exact absurd (hdone τ hτ hN r' k hgk hop) hnd
  -- the groups of the table that waits
  obtain ⟨r0, hfull, lk⟩ := hτ.live_strat hgk hlive
  cases hw with
  | span hs =>
    obtain ⟨gr', hgr', hx⟩ := hfull.span hs
    obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
    obtain ⟨ran0, rfl⟩ := kind_span e
    obtain ⟨T, hT, hall⟩ := hLn.span_ran h0
    exact ⟨T, fun r1 hr1 => ⟨.span true, hLn.mem (r1 + 1) (by omega) _
      (List.mem_of_getElem? (hall (r1 + 1) (by omega))), by simp [Strat.quiet, Strat.pending],
      fun _ _ _ _ _ _ e => by cases e⟩⟩
  | copy c p0 p1 hsubs =>
    obtain ⟨gr', hgr', hx⟩ := hfull.copy c p0 p1
    obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
    obtain ⟨subs0, rfl⟩ := kind_copy e
    have hp0 := hτ.prog hgk (hLn.mem r0 (Nat.le_refl _) _ (List.mem_of_getElem? h0))
    dsimp only [Prog] at hp0
    obtain ⟨-, -, -, qsub⟩ := hp0
    have each : ∀ p' ∈ subs0, ∃ T, ∀ r1, T ≤ r1 → Still τ r1 p'.1 ∧
        ((τ r1).isDone p'.1 || X.contains p'.1) = true := by
      intro p' hp'
      obtain ⟨m', hm'⟩ := List.getElem?_of_mem hp'
      obtain ⟨x, hx1, hgx, -⟩ := qsub m' p'.1 p'.2 hm'
      obtain ⟨hcx, hrx⟩ := hsubs x (List.mem_of_getElem? hx1)
      refine rd _ _ r0 hcx hrx hgx (hτ.opened_of_settled hgx fun r' => ?_)
      cases c with
      | true =>
        obtain ⟨r2, hr2', hr2, hfed, -⟩ := hLn.worked r'
        obtain ⟨subs2, hs2, hadv⟩ := hLn.copy_kept (Nat.le_refl _) h0 (show r0 ≤ r2 + 1 by omega)
        obtain ⟨p2, hp2, hadv2⟩ := hadv.get hm'
        have := hfed _ (List.mem_of_getElem? hs2) p2 (List.mem_of_getElem? hp2)
        rw [hadv2.1] at this
        exact ⟨r2, hr2', this⟩
      | false =>
        refine hτ.req.union_settled hLn (m := q) (M := subs0.map Prod.fst) (fun r hr => ?_)
          (List.mem_map.2 ⟨p', hp', rfl⟩) r'
        obtain ⟨subs2, hs2, hadv⟩ := hLn.copy_kept (Nat.le_refl _) h0 hr
        exact ⟨subs2, hs2, map_fst_of_subAdv hadv⟩
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
  | join kd Lg Rg hsp hl hr =>
    obtain ⟨gr', hgr', a', b', hga', hgb', hx, -, -⟩ := hfull.split kd Lg Rg hsp
    obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
    obtain ⟨c0, rfl⟩ := kind_join e
    have fed : ∀ r', ∃ r2, r' ≤ r2 ∧ Settled (τ (r2 + 1)) a' ∧ Settled (τ (r2 + 1)) b' :=
      fun r' => by
        obtain ⟨r2, hr2', hr2, hfed, -⟩ := hLn.worked r'
        obtain ⟨c2, hs2, -⟩ := hLn.join_kept (Nat.le_refl _) h0 (show r0 ≤ r2 + 1 by omega)
        exact ⟨r2, hr2', hfed _ (List.mem_of_getElem? hs2)⟩
    obtain ⟨Ta, hTa⟩ := rd a' Lg r0 hl.1 hl.2 hga'
      (hτ.opened_of_settled hga' fun r' => (fed r').imp fun _ h => ⟨h.1, h.2.1⟩)
    obtain ⟨Tb, hTb⟩ := rd b' Rg r0 hr.1 hr.2 hgb'
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
  | push kd Lg Rg left hsp hside hsub =>
    obtain ⟨other, hother⟩ : ∃ o : Rel, o = (if left then Rg.node else Lg.node) := ⟨_, rfl⟩
    rw [← hother] at hsub
    obtain ⟨gr', hgr', a', b', hga', hgb', -, hxl, hxr⟩ := hfull.split kd Lg Rg hsp
    obtain ⟨side', hgside', hx⟩ : ∃ side', goalAt (τ r0) side' = some (if left then Lg else Rg) ∧
        Strat.push kd left side' other [] [] [] Cursor.start ∈ gr'.kinds := by
      subst hother
      cases left
      · exact ⟨b', by simpa using hgb', by simpa using hxr⟩
      · exact ⟨a', by simpa using hga', by simpa using hxl⟩
    obtain ⟨L, q, s0, hLn, h0, e⟩ := lk gr' hgr' _ hx
    obtain ⟨todo0, subs0, rfl⟩ := kind_push e
    have hoS : Opened τ side' := hτ.opened_of_settled hgside' fun r' => by
      obtain ⟨r2, hr2', hr2, hfed, -⟩ := hLn.worked r'
      obtain ⟨todo2, subs2, hs2⟩ := hLn.push_kept h0 (show r0 ≤ r2 + 1 by omega)
      exact ⟨r2, hr2', (hfed _ (List.mem_of_getElem? hs2)).1⟩
    obtain ⟨Td, hTd⟩ := ih _ hside.1 hside.2 r0 side' hgside' hoS
    have hdn : ∀ r1, Td ≤ r1 → (τ r1).isDone side' = true := fun r1 hr1 =>
      ((hτ.stable hr1).isDone hTd).1
    obtain ⟨T1, subs1, hT1, h1⟩ := hLn.push_empty h0 (Nat.le_max_right Td r0)
      (fun r1 hr1 => hdn r1 (by omega))
    have hp1 := hτ.prog hgk (hLn.mem T1 (by omega) _ (List.mem_of_getElem? h1))
    dsimp only [Prog] at hp1
    obtain ⟨Lg', Rg', -, -, -, htodo1, hsubs1, -⟩ := hp1
    obtain ⟨hd1, hmax1, -⟩ := htodo1 [] rfl
    have hmx := hC.maxima hL hτ hside.1 hgside' hd1
    have each : ∀ e' ∈ subs1, ∃ T, ∀ r1, T ≤ r1 → Still τ r1 e'.2.1 ∧
        ((τ r1).isDone e'.2.1 || X.contains e'.2.1) = true := by
      intro e' he'
      obtain ⟨x, hxm, hxs⟩ := hmx e'.1 (hmax1 e'.1 (.inr (List.mem_map_of_mem he')))
      obtain ⟨hcx, hrx⟩ := hsub x hxm
      rw [pushG_span g other kd left hxs] at hcx hrx
      obtain ⟨-, hge', -⟩ := hsubs1 e' he'
      obtain ⟨m', hm'⟩ := List.getElem?_of_mem he'
      refine rd _ _ T1 hcx hrx hge' (hτ.opened_of_settled hge' fun r' => ?_)
      obtain ⟨r2, hr2', hr2, hfed, -⟩ := hLn.worked (max r' T1)
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
  | check Lg Rg hsp left ps hreads hall =>
    obtain ⟨side, hside⟩ : ∃ s : Rel, s = (if left then Lg.node else Rg.node) := ⟨_, rfl⟩
    obtain ⟨other, hother⟩ : ∃ o : Rel, o = (if left then Rg.node else Lg.node) := ⟨_, rfl⟩
    rw [← hside] at hreads
    simp only [← hother] at hall
    have iface : ∀ (nn : Nat) (p : R), ps[nn]? = some p → ∀ j' r2,
        goalAt (τ r2) j' =
          some (if left then ⟨some p, other, g.rb⟩ else ⟨g.lb, other, some p⟩) →
        (∀ r3, (τ r3).answers j' = []) ∧ (Opened τ j' → ∃ T, ∀ r1, T ≤ r1 →
          Still τ r1 j' ∧ ((τ r1).isDone j' || X.contains j') = true) := by
      intro nn p hp' j' r2 hj'
      obtain ⟨hcp, hrp, hep⟩ := hall p (List.mem_of_getElem? hp')
      exact ⟨fun r3 => hC.empty hτ hcp hep hj' r3, fun ho' => rd j' _ r2 hcp hrp hj' ho'⟩
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
          obtain ⟨r2, hr2', hr2, hfed, -⟩ := hLn.worked (max r' T)
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

/-- **What is certified, every run completes.** The table of a certified
goal is complete at some time in every run of requests that does not neglect
it and keeps no answer covered by an earlier one. -/
theorem Cert.completes (hC : Cert U C ρ A) {g : GoalOf R Rel} (hg : C g) : Completes U g := by
  intro τ hτ hN
  have main : ∀ n g, C g → ρ g = n →
      ∀ r' k, goalAt (τ r') k = some g → Opened τ k → EvDone τ k := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro g hg hn r' k hk ho
      by_contra hnd
      obtain ⟨X, hX⟩ := waits_list hτ hC.fin ρ n
      have hkX : k ∈ X := (hX k).2 ⟨g, r', hg, hn, hk, ho, hnd⟩
      obtain ⟨T, hT⟩ := eventually_forall_mem X
        (fun k r1 => ∃ s, IsStrat τ k (r1 + 1) s ∧
          s.quiet (τ (r1 + 1)) (fun j => (τ (r1 + 1)).isDone j || X.contains j) = true ∧
          ∀ kd l side o todo subs, s = .push kd l side o todo subs →
            (τ r1).isDone side = true)
        (fun k hk' => hC.waits_quiet hL hτ hN
          (fun g hg hlt r' k hk ho => ih (ρ g) hlt g hg rfl r' k hk ho) hX
          ((hX k).1 hk'))
      have := (hτ.req.req T).closed X (fun k hk' => by
        obtain ⟨s, ⟨t', gs, gr, ht', hg, hgr, hs⟩, hq, hp⟩ := hT k hk' T (Nat.le_refl _)
        exact ⟨t', ht', gs, hg, gr, hgr, s, hs, hq, hp⟩) k hkX
      exact hnd ⟨T + 1, this⟩
  exact main (ρ g) g hg rfl

/-! ## Certificates whose races are final -/

/-- A certificate that the goals `C` complete, in which a goal with no
reason among the others is a chain whose unfolding is final at some depth:
its race completes it. The goals are goals a run may open. -/
structure FCert (U : GOracle R Rel (Ans D P) Cost) (C : GoalOf R Rel → Prop)
    (ρ : GoalOf R Rel → Nat) (A : GoalOf R Rel → List (Ans D P)) : Prop where
  fin : ∃ l : List (GoalOf R Rel), ∀ g, C g → g ∈ l
  goal : ∀ g, C g → ∀ a ∈ A g, a.goal = toGoal g
  full : ∀ g, C g → ∀ y : Ans D P, y.goal = toGoal g → ∃ f ∈ A g, covB D P f y = true
  ok : ∀ g, C g → GoalOk D g
  why : ∀ g, C g → (hasRace g = true ∧ ∃ d, (U d g).val.1 = true) ∨ Why C ρ A g

omit hL in
/-- **A certificate whose races are final is a certificate**
(`IsRun.race_done`). -/
theorem FCert.cert (h : FCert U C ρ A) : Cert U C ρ A :=
  ⟨h.fin, h.goal, h.full, fun g hg => (h.why g hg).imp
    (fun ⟨hh, _, hfin⟩ _ hτ _ _ _ hk ho => ho.elim id fun hlive => hτ.race_done hk hlive hh hfin)
    id⟩

/-! ## The certificate of a run -/

/-- **The complete tables of a state of a run are a certificate**, with the
answers they hold: a table with no reason among the others completed by its
race. -/
theorem IsRun.fcert (hσ : IsRun U σ) (r : Nat) :
    ∃ (ρ : GoalOf R Rel → Nat) (A : GoalOf R Rel → List (Ans D P)),
      FCert U (fun g => ∃ i, goalAt (σ r) i = some g ∧ (σ r).isDone i = true) ρ A := by
  classical
  obtain ⟨ρ0, hρ⟩ := hσ.founded r
  let ρ : GoalOf R Rel → Nat := fun g =>
    if h : ∃ i, goalAt (σ r) i = some g then ρ0 (Classical.choose h) else 0
  let A : GoalOf R Rel → List (Ans D P) := fun g =>
    if h : ∃ i, goalAt (σ r) i = some g then (σ r).answers (Classical.choose h) else []
  have key : ∀ i g, goalAt (σ r) i = some g → ρ g = ρ0 i ∧ A g = (σ r).answers i := by
    intro i g hi
    have h : ∃ i, goalAt (σ r) i = some g := ⟨i, hi⟩
    have e : Classical.choose h = i := hσ.goal_inj (Classical.choose_spec h) hi
    constructor
    · show (if h : ∃ i, goalAt (σ r) i = some g then ρ0 (Classical.choose h) else 0) = _
      simp only [h, ↓reduceDIte]
      rw [e]
    · show (if h : ∃ i, goalAt (σ r) i = some g then (σ r).answers (Classical.choose h)
        else []) = _
      simp only [h, ↓reduceDIte]
      rw [e]
  refine ⟨ρ, A, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(σ r).tables.map (·.goal), ?_⟩
    rintro g ⟨i, hi, -⟩
    obtain ⟨t, ht, e⟩ := table_of_goalAt hi
    exact List.mem_map.2 ⟨t, List.mem_of_getElem? ht, e⟩
  · rintro g ⟨i, hi, -⟩ a ha
    rw [(key i g hi).2] at ha
    obtain ⟨t, ht, hat⟩ := mem_answers ha
    have := ((hσ.good r).inv.core i t ht).2.2 a hat
    rw [← hσ.goal_any hi (goalAt_of_table ht)] at this
    exact this
  · rintro g ⟨i, hi, hd⟩ y hy
    have hv : Valid D P (toGoal g) y.span := by
      rw [← hy]
      exact y.valid
    obtain ⟨a, ha, hsub⟩ := hσ.fair.covers_valid hL (hσ.mem_opened hi (.inl ⟨r, hd⟩)) hv
    obtain ⟨r3, x, hx, rfl⟩ := (hσ.held_iff hi a).1 ha
    exact ⟨x, by rw [(key i g hi).2]; exact hσ.done_answers hd r3 hx,
      (covB_iff hL x y).2 hsub⟩
  · rintro g ⟨i, hi, -⟩
    obtain ⟨t, ht, e⟩ := table_of_goalAt hi
    have hgood := (hσ.good r).base.good i g hi
    exact ⟨hgood.1, hgood.2.1, e ▸ ((hσ.good r).inv.core i t ht).1, hgood.2.2⟩
  · rintro g ⟨i, hi, hd⟩
    have hρi := (key i g hi).1
    obtain ⟨t, ht, -⟩ := table_of_goalAt hi
    have hdt : t.done = true := by
      rw [← isDone_of_table ht]
      exact hd
    rcases hρ i t ht hdt with hquiet | ⟨t1, ht1, l, -, hh, ⟨n1, hfin⟩, -⟩
    swap
    · -- the table completed by its race
      left
      rw [ht] at ht1
      cases ht1
      rw [hσ.goal_any (goalAt_of_table ht) hi] at hh hfin
      exact ⟨hh, n1, hfin⟩
    right
    obtain ⟨gs, hgs, gr, hgr, s, hs, hq, hpush⟩ := hquiet
    have hst : IsStrat σ i r s := ⟨t, gs, gr, ht, hgs, hgr, hs⟩
    have hp := hσ.prog hi hst
    cases s with
    | span ran =>
      dsimp only [Prog] at hp
      exact .span hp.1
    | copy c subs =>
      dsimp only [Prog] at hp
      obtain ⟨p0, p1, plen, psub⟩ := hp
      simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
        List.any_eq_false, List.all_eq_true, decide_eq_true_eq] at hq
      refine .copy c p0 p1 fun x hx => ?_
      obtain ⟨m, hm⟩ := List.getElem?_of_mem hx
      have hlt : m < subs.length := by
        rw [plen]
        exact (List.getElem?_eq_some_iff.1 hm).1
      obtain ⟨x', hx', hgx', -⟩ := psub m subs[m].1 subs[m].2 (List.getElem?_eq_getElem hlt)
      rw [hm] at hx'
      cases hx'
      have hok := hq.2 _ (List.getElem_mem hlt)
      exact ⟨⟨_, hgx', hok.1⟩, by rw [(key _ _ hgx').1, hρi]; exact hok.2⟩
    | join kd a b c =>
      dsimp only [Prog] at hp
      obtain ⟨Lg, Rg, hsp, hga, hgb, -, -⟩ := hp
      simp only [Strat.quiet, Strat.pending, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at hq
      exact .join kd Lg Rg hsp
        ⟨⟨a, hga, hq.2.1.1⟩, by rw [(key _ _ hga).1, hρi]; exact hq.2.1.2⟩
        ⟨⟨b, hgb, hq.2.2.1⟩, by rw [(key _ _ hgb).1, hρi]; exact hq.2.2.2⟩
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
      subst hother
      refine .push kd Lg Rg left hsp
        ⟨⟨side, hgside, hds⟩, by rw [(key _ _ hgside).1, hρi]; exact hrank⟩ fun x hxm => ?_
      rw [(key _ _ hgside).2] at hxm
      obtain ⟨x'', hx''m, hx''in, hx''c⟩ := hcovσ x (List.mem_maximaBy hxm)
      have hx''s : x'' ∈ subs.map (·.1) := hx''in.resolve_left (fun h => by cases h)
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx''s
      have hcv : covB D P e.1 x = true := (covB_iff hL e.1 x).2 hx''c
      have hspn : e.1.span = x.span := hL.covers_antisymm hcv (maxima_max hxm hx''m hcv)
      obtain ⟨-, hge, -⟩ := hsubs e he
      rw [pushG_span g _ kd left hspn] at hge
      have hok := hokσ e he
      exact ⟨⟨_, hge, hok.1⟩, by rw [(key _ _ hge).1, hρi]; exact hok.2⟩
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
      subst hside
      subst hother
      refine .check Lg Rg hsp left ps hreads fun p hp' => ?_
      obtain ⟨nn, hnn⟩ := List.getElem?_of_mem hp'
      obtain ⟨j, hj, hgj⟩ := pall nn p hnn
      have hj3 := hq j (List.mem_of_getElem? hj)
      exact ⟨⟨j, hgj, hj3.1.1⟩, by rw [(key _ _ hgj).1, hρi]; exact hj3.1.2,
        by rw [(key _ _ hgj).2]; exact hj3.2⟩

/-- **What one run completes, every run completes.** A goal whose table is
complete in a run of requests has a complete table in every run of requests
that does not neglect it and keeps no answer covered by an earlier one. -/
theorem IsRun.transfer (hσ : IsRun U σ) (hτ : IsRun U τ)
    (hN : ∀ r j, NoCov D (((τ r).answers j).map Ans.span)) {r i : Nat} {g : GoalOf R Rel}
    (hi : goalAt (σ r) i = some g) (hd : (σ r).isDone i = true) {r' k : Nat}
    (hk : goalAt (τ r') k = some g) (ho : Opened τ k) : EvDone τ k := by
  obtain ⟨ρ, A, hC⟩ := hσ.fcert hL r
  exact hC.cert.completes hL ⟨i, hi, hd⟩ τ hτ hN r' k hk ho

end

end Symmetric

end RwLog
