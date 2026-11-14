/-
# What the tables of the tabled machine keep

An unfolding race meets its specification (`UOk`) when its answers are
answers of the goal it is asked about and, when it says the unfolding is
final, they cover every derivation of the goal.

With such a race, a round keeps (`inv_next`):

* every table has a goal the machine may hold, and its answers are answers
  of that goal;
* a complete table is *full*: its answers cover every derivation of its
  goal.

The second is why the machine may stop when the root table is complete. A
table completes with a strategy all of whose goals are complete or complete
with it; that its answers then cover a derivation is shown by induction on
the depth of unfolding of the derivation and the size of the node
(`closing_full`), with `strat_cov` as the step.
-/
import RwLog.Rungs.Tabled.Round

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The specification of an unfolding race at one kernel. -/
structure UOk (D : Domain R) (P : Program) (U : GOracle R Rel (Ans D P) Cost) : Prop where
  /-- Its answers are answers of the goal. -/
  goal : ∀ n g, GoalOk D g → ∀ a ∈ (U n g).val.2, a.goal = toGoal g
  /-- When it says the unfolding is final, its answers cover every derivation
  of the goal. -/
  final : ∀ n g, GoalOk D g → (U n g).val.1 = true → ∀ k G, G ∈ GDn P k g.node →
    (pairsOf P g G).Nonempty → Cov (U n g).val.2 (pairsOf P g G)

/-- The answers of the table cover every derivation of its goal. -/
def Full (P : Program) (t : TableOf R Rel (Ans D P)) : Prop :=
  ∀ k G, G ∈ GDn P k t.goal.node → (pairsOf P t.goal G).Nonempty →
    Cov t.answers (pairsOf P t.goal G)

/-- What the tables keep. -/
structure Inv (D : Domain R) (P : Program) (ts : List (TableOf R Rel (Ans D P))) : Prop where
  ok : TablesOk D ts
  full : ∀ t ∈ ts, t.done = true → Full P t

variable (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (K : Kernel R Cost) (hK : K.Refines D)
  {U : GOracle R Rel (Ans D P) Cost} (hU : UOk D P U) {ts : List (TableOf R Rel (Ans D P))}
  (depth : Nat)

/-! ## What a table produces in a round -/

include hU in
/-- The candidates of a table are answers of its goal. -/
theorem out_goal (hT : TablesOk D ts) {t : TableOf R Rel (Ans D P)} (ht : t ∈ ts) {c : Ans D P}
    (hc : c ∈ (outOf K hK U ts depth t).1) : c.goal = toGoal t.goal := by
  unfold outOf at hc
  split at hc
  · cases hc
  · next hd =>
    rw [produce_val] at hc
    rcases List.mem_append.1 hc with h | h
    · unfold askOf at h
      rw [ite_eq_right_iff.2 (fun h => absurd h hd)] at h
      exact hU.goal _ _ (hT t ht).1 c h
    · exact cand_goal K hK ts hT (hT t ht).1 h

include hL hP in
/-- The goals of the strategies of a table are goals the machine may hold. -/
theorem out_ok (hT : TablesOk D ts) {t : TableOf R Rel (Ans D P)} (ht : t ∈ ts)
    {strat : List (GoalOf R Rel)} (hs : strat ∈ (outOf K hK U ts depth t).2) {d : GoalOf R Rel}
    (hd : d ∈ strat) : GoalOk D d := by
  unfold outOf at hs
  split at hs
  · cases hs
  · rw [produce_val] at hs
    rcases List.mem_append.1 hs with h | h
    · split at h
      · obtain rfl : strat = [] := by simpa using h
        cases hd
      · cases h
    · exact strat_ok K hK ts hL hP (hT t ht).1 h hd

include hL hU in
/-- If the tables cover every smaller derivation of the goals of one
strategy of an incomplete table, its candidates cover every derivation of its
goal at depth `k`. -/
theorem out_cov (hT : TablesOk D ts) {t : TableOf R Rel (Ans D P)} (ht : t ∈ ts)
    (hd : t.done = false) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (outOf K hK U ts depth t).2) {k : Nat} {G : GRel}
    (hG : G ∈ GDn P k t.goal.node) (hne : (pairsOf P t.goal G).Nonempty)
    (H : Below P ts t.goal k strat) :
    Cov (outOf K hK U ts depth t).1 (pairsOf P t.goal G) := by
  unfold outOf at hs ⊢
  simp only [hd, Bool.false_eq_true, ite_false] at hs ⊢
  rw [produce_val] at hs ⊢
  rcases List.mem_append.1 hs with h | h
  · split at h
    · next hf =>
      unfold askOf at hf ⊢
      simp only [hd, Bool.false_eq_true, ite_false] at hf ⊢
      exact (hU.final _ _ (hT t ht).1 hf k G hG hne).mono
        (fun a ha => List.mem_append_left _ ha) subset_rfl
    · cases h
  · exact (strat_cov K hK ts hL hT (hT t ht).1 h hG hne H).mono
      (fun a ha => List.mem_append_right _ ha) subset_rfl

include hL in
/-- What the candidates of a table cover, the table covers after the
round. -/
theorem grow_cov {t : TableOf R Rel (Ans D P)} {X : PRel}
    (h : Cov (outOf K hK U ts depth t).1 X) :
    Cov (t.answers ++ gainOf K hK U ts depth t) X :=
  cov_fresh hL K hK h

/-! ## Tables that complete are full -/

include hL hU in
theorem closing_full (hI : Inv D P ts) : ∀ (k n j : Nat) (hj : j < ts.length),
    (ts[j].done = true ∨ j ∈ closing K hK U ts depth) → ts[j].goal.node.size = n →
    ∀ G, G ∈ GDn P k ts[j].goal.node → (pairsOf P ts[j].goal G).Nonempty →
      Cov ts[j].answers (pairsOf P ts[j].goal G) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro j hj hc hn G hG hne
  rcases hc with hd | hC
  · exact hI.full _ (List.getElem_mem hj) hd k G hG hne
  · obtain ⟨_, hnd, hgain, strat, hs, hdeps⟩ := mem_closing K hK U ts depth hC
    have hcov := out_cov hL K hK hU depth hI.ok (List.getElem_mem hj) hnd hs hG hne
      (fun d hd k' G' hsm hG' hne' => by
        obtain ⟨j', hj', hc'⟩ := hdeps d hd
        obtain ⟨hjl, hg', -⟩ := idx_some.1 hj'
        obtain ⟨_, ha⟩ := ansOf_of_idx hj'
        rw [ha]
        have hc'' : ts[j'].done = true ∨ j' ∈ closing K hK U ts depth :=
          hc'.imp (fun ⟨_, h⟩ => h) id
        subst hg'
        rcases hsm with hlt | ⟨rfl, hlt⟩
        · exact ihk k' hlt _ j' hjl hc'' rfl G' hG' hne'
        · exact ihn _ (hn ▸ hlt) j' hjl hc'' rfl G' hG' hne')
    have := grow_cov hL K hK depth hcov
    rwa [hgain, List.append_nil] at this

/-! ## A round keeps the invariant -/

include hL hP hU in
theorem inv_next (hI : Inv D P ts) : Inv D P (nextTables K hK U ts depth) := by
  constructor
  · intro t' ht'
    rcases mem_next.1 ht' with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · have hm := List.getElem_mem hi
      refine ⟨(hI.ok _ hm).1, fun a ha => ?_⟩
      rcases List.mem_append.1 ha with h | h
      · exact (hI.ok _ hm).2 a h
      · exact out_goal K hK hU depth hI.ok hm (mem_fresh K hK h).1
    · obtain ⟨t, ht, strat, hs, hd, -⟩ := (mem_newGoals K hK U ts depth g).1 hg
      exact ⟨out_ok hL hP K hK depth hI.ok ht hs hd, fun a ha => by cases ha⟩
  · intro t' ht' hdone
    rcases mem_next.1 ht' with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · intro k G hG hne
      have hc : ts[i].done = true ∨ i ∈ closing K hK U ts depth := by
        simpa [List.contains_iff_mem] using hdone
      exact (closing_full hL K hK hU depth hI k _ i hi hc rfl G hG hne).mono
        (fun a ha => List.mem_append_left _ ha) subset_rfl
    · cases hdone

/-! ## No answer of a table is covered by an earlier one -/

/-- No answer of a table is covered by an earlier answer of the table. -/
def NoCov (D : Domain R) (P : Program) (ts : List (TableOf R Rel (Ans D P))) : Prop :=
  ∀ t ∈ ts, t.answers.Pairwise fun y x => covB D P y x = false

theorem nocov_next (h : NoCov D P ts) : NoCov D P (nextTables K hK U ts depth) := by
  intro t' ht'
  rcases mem_next.1 ht' with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
  · refine List.pairwise_append.2 ⟨h _ (List.getElem_mem hi), ?_, fun a ha b hb => ?_⟩
    · exact (fresh_pairwise K hK _ _).imp fun h => h.1
    · exact (mem_fresh K hK hb).2 a ha
  · exact List.Pairwise.nil

end Tabled

end RwLog
