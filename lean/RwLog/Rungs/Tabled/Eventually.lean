/-
# Every derivation is covered in the end

The tables of the tabled machine round after round (`tablesAt`), from the
table of the root goal alone. They keep the invariant of
`Rungs/Tabled/Invariant.lean` (`inv_at`); a table keeps its position, its
goal and its answers, and stays complete (`at_mono`).

`eventually`: for every table and every derivation of the node of its goal,
some later round's table covers the pairs of the derivation between the
boundaries of the goal. If the table completes it is full. If it never does,
it recomputes its candidates every round; the goals of the strategy that is
always there get tables in the next round, by induction their tables come to
cover the smaller derivations this one is made of, and then the candidates
cover it.
-/
import RwLog.Rungs.Tabled.Invariant

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D) (U : GOracle R Rel (Ans D P) Cost) (root : Rel)

/-- The tables after `r` rounds. -/
def tablesAt : Nat → List (TableOf R Rel (Ans D P))
  | 0 => [⟨⟨none, root, none⟩, [], false⟩]
  | r + 1 => nextTables K hK U (tablesAt r) r

variable {K hK U root}

section mono

/-- A table keeps its position, its goal and its answers, and stays
complete. -/
theorem at_mono {r r' : Nat} (h : r ≤ r') {i : Nat} (hi : i < (tablesAt K hK U root r).length) :
    ∃ hi' : i < (tablesAt K hK U root r').length,
      (tablesAt K hK U root r')[i].goal = (tablesAt K hK U root r)[i].goal ∧
      (∀ a ∈ (tablesAt K hK U root r)[i].answers, a ∈ (tablesAt K hK U root r')[i].answers) ∧
      ((tablesAt K hK U root r)[i].done = true → (tablesAt K hK U root r')[i].done = true) := by
  induction r', h using Nat.le_induction with
  | base => exact ⟨hi, rfl, fun _ h => h, id⟩
  | succ r' _ ih =>
    obtain ⟨hi', hg, ha, hd⟩ := ih
    obtain ⟨hi'', e⟩ := next_getElem (K := K) (hK := hK) (U := U) (depth := r') hi'
    refine ⟨hi'', ?_, ?_, ?_⟩
    · show (nextTables K hK U (tablesAt K hK U root r') r')[i].goal = _
      rw [e]; exact hg
    · intro a h
      show a ∈ (nextTables K hK U (tablesAt K hK U root r') r')[i].answers
      rw [e]; exact List.mem_append_left _ (ha a h)
    · intro h
      show (nextTables K hK U (tablesAt K hK U root r') r')[i].done = true
      rw [e]; simp [hd h]

/-- A goal keeps the position of its table. -/
theorem idx_mono {r r' : Nat} (h : r ≤ r') {g : GoalOf R Rel} {j : Nat}
    (hj : idx (tablesAt K hK U root r) g = some j) : idx (tablesAt K hK U root r') g = some j := by
  induction r', h using Nat.le_induction with
  | base => exact hj
  | succ r' _ ih => exact next_idx ih

/-- What the table of a goal covers, it covers later. -/
theorem ans_mono {r r' : Nat} (h : r ≤ r') {g : GoalOf R Rel} {j : Nat}
    (hj : idx (tablesAt K hK U root r) g = some j) {X : PRel}
    (hc : Cov (ansOf (tablesAt K hK U root r) g) X) : Cov (ansOf (tablesAt K hK U root r') g) X := by
  obtain ⟨hl, e⟩ := ansOf_of_idx hj
  obtain ⟨hl', e'⟩ := ansOf_of_idx (idx_mono h hj)
  rw [e] at hc
  rw [e']
  exact hc.mono (at_mono h hl).2.2.1 subset_rfl

/-- The goals of the strategies of a table have tables after the round. -/
theorem requested {ts : List (TableOf R Rel (Ans D P))} {depth : Nat}
    {t : TableOf R Rel (Ans D P)} (ht : t ∈ ts) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (outOf K hK U ts depth t).2) {d : GoalOf R Rel} (hd : d ∈ strat) :
    ∃ j, idx (nextTables K hK U ts depth) d = some j := by
  cases h : idx ts d with
  | some j => exact ⟨j, next_idx h⟩
  | none =>
    have hn := (mem_newGoals K hK U ts depth d).2 ⟨t, ht, strat, hs, hd, h⟩
    have hm : (⟨d, [], false⟩ : TableOf R Rel (Ans D P)) ∈ nextTables K hK U ts depth :=
      mem_next.2 (.inr ⟨d, hn, rfl⟩)
    cases h' : idx (nextTables K hK U ts depth) d with
    | some j => exact ⟨j, rfl⟩
    | none => exact absurd rfl (idx_none.1 h' _ hm)

end mono

variable (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
  (hroot : GoalOk D (⟨none, root, none⟩ : GoalOf R Rel))

include hL hP hU hroot in
/-- The tables keep the invariant. -/
theorem inv_at : ∀ r, Inv D P (tablesAt K hK U root r)
  | 0 => by
    constructor
    · intro t ht
      obtain rfl : t = ⟨⟨none, root, none⟩, [], false⟩ := by simpa [tablesAt] using ht
      exact ⟨hroot, fun a ha => by cases ha⟩
    · intro t ht hd
      obtain rfl : t = ⟨⟨none, root, none⟩, [], false⟩ := by simpa [tablesAt] using ht
      cases hd
  | r + 1 => inv_next hL hP K hK hU r (inv_at r)

include hL hP hU hroot in
/-- Every derivation of the node of a table's goal is covered by the table in
some later round. -/
theorem eventually : ∀ (k n r i : Nat) (hi : i < (tablesAt K hK U root r).length),
    (tablesAt K hK U root r)[i].goal.node.size = n →
    ∀ G, G ∈ GDn P k (tablesAt K hK U root r)[i].goal.node →
      (pairsOf P (tablesAt K hK U root r)[i].goal G).Nonempty →
      ∃ r', r ≤ r' ∧ ∃ hi' : i < (tablesAt K hK U root r').length,
        Cov (tablesAt K hK U root r')[i].answers
          (pairsOf P (tablesAt K hK U root r)[i].goal G) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro r i hi hn G hG hne
  have hI := inv_at hL hP hU hroot (K := K) (hK := hK)
  by_cases hdone : ∃ r', r ≤ r' ∧ ∃ hi' : i < (tablesAt K hK U root r').length,
      (tablesAt K hK U root r')[i].done = true
  · obtain ⟨r', hr, hi', hd⟩ := hdone
    obtain ⟨_, hg, -, -⟩ := at_mono hr hi
    have := (hI r').full _ (List.getElem_mem hi') hd k G (by rw [hg]; exact hG)
      (by rw [hg]; exact hne)
    rw [hg] at this
    exact ⟨r', hr, hi', this⟩
  · have hnd : ∀ r', r ≤ r' → ∀ hi' : i < (tablesAt K hK U root r').length,
        (tablesAt K hK U root r')[i].done = false := fun r' hr hi' => by
      cases h : (tablesAt K hK U root r')[i].done with
      | false => rfl
      | true => exact absurd ⟨r', hr, hi', h⟩ hdone
    have hg := ((hI r).ok _ (List.getElem_mem hi)).1
    obtain ⟨needs, hneeds, hstat⟩ := static_cov K hK hL hg hG hne
    -- the candidates of the table in a later round
    have hout : ∀ r', r ≤ r' → ∀ hi' : i < (tablesAt K hK U root r').length,
        outOf K hK U (tablesAt K hK U root r') r' (tablesAt K hK U root r')[i] =
          ((askOf U r' (tablesAt K hK U root r')[i]).2 ++
              (produceTables (K := DerivationKernel.over D K hK P) (tablesAt K hK U root r')
                (tablesAt K hK U root r)[i].goal).val.1,
            (if (askOf U r' (tablesAt K hK U root r')[i]).1 then [[]] else []) ++
              (produceTables (K := DerivationKernel.over D K hK P) (tablesAt K hK U root r')
                (tablesAt K hK U root r)[i].goal).val.2) := fun r' hr hi' => by
      unfold outOf
      simp only [hnd r' hr hi', Bool.false_eq_true, ite_false]
      rw [produce_val, (at_mono hr hi).2.1]
    -- the goals the derivation needs have tables from the next round on
    have hidx : ∀ x ∈ needs, ∃ j, idx (tablesAt K hK U root (r + 1)) x.1 = some j := fun x hx => by
      obtain ⟨strat, hs, hall⟩ := (hstat _ (hI r).ok).1
      refine requested (List.getElem_mem hi) (strat := strat) ?_ (hall x hx)
      rw [hout r (Nat.le_refl r) hi]
      exact List.mem_append_right _ hs
    -- and their tables come to cover what it needs
    have hall : ∀ l : List (GoalOf R Rel × Nat × GRel), (∀ x ∈ l, x ∈ needs) →
        ∃ r', r + 1 ≤ r' ∧ ∀ x ∈ l,
          Cov (ansOf (tablesAt K hK U root r') x.1) (pairsOf P x.1 x.2.2) := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨r + 1, Nat.le_refl _, fun x hx => by cases hx⟩
      | cons x l ih =>
        intro hl
        obtain ⟨r₁, hr₁, h₁⟩ := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
        have hx := hl x List.mem_cons_self
        obtain ⟨hsm, hGx, hnex⟩ := hneeds x hx
        obtain ⟨j, hj⟩ := hidx x hx
        obtain ⟨hjl, hjg, -⟩ := idx_some.1 hj
        have hx₂ : ∃ r₂, r + 1 ≤ r₂ ∧
            Cov (ansOf (tablesAt K hK U root r₂) x.1) (pairsOf P x.1 x.2.2) := by
          have key : ∃ r₂, r + 1 ≤ r₂ ∧ ∃ hi' : j < (tablesAt K hK U root r₂).length,
              Cov (tablesAt K hK U root r₂)[j].answers
                (pairsOf P (tablesAt K hK U root (r + 1))[j].goal x.2.2) := by
            rcases hsm with hlt | ⟨he, hlt⟩
            · exact ihk x.2.1 hlt _ (r + 1) j hjl rfl x.2.2 (by rw [hjg]; exact hGx)
                (by rw [hjg]; exact hnex)
            · exact ihn x.1.node.size (hn ▸ hlt) (r + 1) j hjl (by rw [hjg]) x.2.2
                (by rw [hjg, ← he]; exact hGx) (by rw [hjg]; exact hnex)
          obtain ⟨r₂, hr₂, hi', hc⟩ := key
          rw [hjg] at hc
          obtain ⟨_, e⟩ := ansOf_of_idx (idx_mono hr₂ hj)
          exact ⟨r₂, hr₂, by rw [e]; exact hc⟩
        obtain ⟨r₂, hr₂, h₂⟩ := hx₂
        refine ⟨max r₁ r₂, Nat.le_trans hr₁ (Nat.le_max_left _ _), fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ans_mono (Nat.le_max_right _ _) (idx_mono hr₂ hj) h₂
        · obtain ⟨j', hj'⟩ := hidx y (hl y (List.mem_cons_of_mem _ hy))
          exact ans_mono (Nat.le_max_left _ _) (idx_mono hr₁ hj') (h₁ y hy)
    obtain ⟨r', hr', hcov⟩ := hall needs fun _ h => h
    have hr : r ≤ r' := Nat.le_of_succ_le hr'
    obtain ⟨hi', -, -, -⟩ := at_mono hr hi
    have hc := (hstat _ (hI r').ok).2 hcov
    have hc' : Cov (outOf K hK U (tablesAt K hK U root r') r' (tablesAt K hK U root r')[i]).1
        (pairsOf P (tablesAt K hK U root r)[i].goal G) := by
      rw [hout r' hr hi']
      exact hc.mono (fun a ha => List.mem_append_right _ ha) subset_rfl
    have hgrow := grow_cov hL K hK r' hc'
    obtain ⟨hi'', e⟩ := next_getElem (K := K) (hK := hK) (U := U) (depth := r') hi'
    refine ⟨r' + 1, Nat.le_succ_of_le hr, hi'', ?_⟩
    show Cov (nextTables K hK U (tablesAt K hK U root r') r')[i].answers _
    rw [e]
    exact hgrow

end Tabled

end RwLog
