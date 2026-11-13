/-
# Rung R001, Symmetry: tables of a run and of its mirror

The mirrored run keeps, for every table of the run with key `G`, a table
whose key is equivalent to `KD G`, the key of `G`'s mirror, holding the
swapped answers up to `StepEquiv` and complete at the same time (`TabRel`,
`TabsRel`). This file shows that table lookups agree under that
correspondence.
-/
import RwLog.Rungs.R001.Proofs.SymmetryGoals

namespace RwLog

namespace R001

namespace Symmetry

/-! ## Keys of mirrored goals -/

/-- The key of the mirror of a key. -/
def KD (G : Goal) : Goal := ⟨G.rb.map Span.swap, canon G.e.dual, G.lb.map Span.swap⟩

theorem IsKey.dual_norm {G : Goal} (h : IsKey G) : G.dual.norm = (false, KD G) := by
  obtain ⟨hc, hn⟩ := h.canonical
  simp only [GoalOf.norm, GoalOf.dual, KD]
  exact stripConv_other _ _ _ (canon_dual_not_conv hc hn)

theorem IsKey.kd {G : Goal} (h : IsKey G) : IsKey (KD G) := by
  have := isKey_norm G.dual
  rwa [h.dual_norm] at this

theorem IsKey.KD_KD {G : Goal} (h : IsKey G) : KD (KD G) = G := by
  obtain ⟨lb, e, rb⟩ := G
  have hc := h.canonical.1
  simp only at hc
  simp only [KD, Option.map_map, Function.comp_def, Span.swap_swap, Option.map_id']
  rw [← canon_dual e.dual, RelOf.dual_dual, hc]

theorem KD_same {G G' : Goal} (h : G.same G' = true) : (KD G).same (KD G') = true := by
  rw [GoalOf.same_iff] at h ⊢
  simp only [KD, boundEq_swap]
  exact ⟨by rw [h.1], h.2.2, h.2.1⟩

theorem same_of_KD_same {G G' : Goal} (hG : IsKey G) (hG' : IsKey G')
    (h : (KD G).same (KD G') = true) : G.same G' = true := by
  have := KD_same h
  rwa [hG.KD_KD, hG'.KD_KD] at this

/-- `h`, a goal of the mirrored run, mirrors `g`, a goal of the run: the key
of `h` is the key of `g`'s mirror, with the same orientation. -/
def Mirror (g h : Goal) : Prop := h.norm.1 = g.norm.1 ∧ h.norm.2.same (KD g.norm.2) = true

theorem mirror_dual (g : Goal) : Mirror g g.dual := by
  rw [Mirror, norm_dual, (isKey_norm g).dual_norm]
  exact ⟨Bool.xor_false _, GoalOf.same_refl _⟩

theorem Mirror.of_same {g h h' : Goal} (hm : Mirror g h) (e : h.same h' = true) : Mirror g h' := by
  have := norm_same e
  exact ⟨this.1 ▸ hm.1, GoalOf.same_trans (GoalOf.same_symm this.2) hm.2⟩

theorem norm_canon_congr (lb rb : Option Span) {e e' : Rel} (h : canon e = canon e') :
    GoalOf.norm ⟨lb, e, rb⟩ = GoalOf.norm ⟨lb, e', rb⟩ := by
  simp only [GoalOf.norm, h]

/-- The general way to build a mirror: equivalent swapped boundaries, and the
mirrored expression up to canonical form. -/
theorem mirror_mk {g h : Goal} (he : canon h.e = canon g.e.dual)
    (hl : boundEq (g.rb.map Span.swap) h.lb = true) (hr : boundEq (g.lb.map Span.swap) h.rb = true) :
    Mirror g h := by
  obtain ⟨lb, e, rb⟩ := h
  simp only at he hl hr
  rw [Mirror, norm_canon_congr lb rb he]
  exact (mirror_dual g).of_same (GoalOf.same_iff.2 ⟨rfl, hl, hr⟩)

/-! ## Corresponding tables -/

/-- A table of the mirrored run corresponding to a table of the run. -/
def TabRel (tA tB : Table) : Prop :=
  tB.goal.same (KD tA.goal) = true ∧ StepEquiv tB.answers (tA.answers.map Span.swap) ∧
    tB.done = tA.done

/-- The tables of a run and of its mirror correspond one to one. -/
structure TabsRel (tsA tsB : Tables) : Prop where
  keyA : ∀ t ∈ tsA, IsKey t.goal
  keyB : ∀ t ∈ tsB, IsKey t.goal
  ndA : tsA.Pairwise fun t t' => t.goal.same t'.goal = false
  ndB : tsB.Pairwise fun t t' => t.goal.same t'.goal = false
  fwd : ∀ tA ∈ tsA, ∃ tB ∈ tsB, TabRel tA tB
  bwd : ∀ tB ∈ tsB, ∃ tA ∈ tsA, TabRel tA tB

/-- In a list without two tables of equivalent keys, the tables of keys
equivalent to a given one are one table. -/
theorem eq_of_same {ts : Tables} (nd : ts.Pairwise fun t t' => t.goal.same t'.goal = false)
    {t t' : Table} {K : Goal} (ht : t ∈ ts) (ht' : t' ∈ ts) (h : t.goal.same K = true)
    (h' : t'.goal.same K = true) : t = t' := by
  induction ts with
  | nil => cases ht
  | cons u ts ih =>
    rw [List.pairwise_cons] at nd
    rcases List.mem_cons.1 ht with e₁ | h₁ <;> rcases List.mem_cons.1 ht' with e₂ | h₂
    · rw [e₁, e₂]
    · subst e₁
      have := nd.1 t' h₂
      rw [GoalOf.same_trans h (GoalOf.same_symm h')] at this; cases this
    · subst e₂
      have := nd.1 t h₁
      rw [GoalOf.same_trans h' (GoalOf.same_symm h)] at this; cases this
    · exact ih nd.2 h₁ h₂

theorem findTable_some {ts : Tables} {K : Goal} {t : Table} (h : findTable ts K = some t) :
    t ∈ ts ∧ t.goal.same K = true := by
  unfold findTable at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem findTable_of_mem {ts : Tables} (nd : ts.Pairwise fun t t' => t.goal.same t'.goal = false)
    {K : Goal} {t : Table} (ht : t ∈ ts) (h : t.goal.same K = true) : findTable ts K = some t := by
  unfold findTable
  cases hf : List.find? (fun t => t.goal.same K) ts with
  | none =>
    have := List.find?_eq_none.1 hf t ht
    rw [h] at this; exact absurd rfl this
  | some t' =>
    have := findTable_some (ts := ts) (K := K) hf
    rw [eq_of_same nd this.1 ht this.2 h]

theorem findTable_none {ts : Tables} {K : Goal} (h : findTable ts K = none) :
    ∀ t ∈ ts, t.goal.same K = false := by
  unfold findTable at h
  intro t ht
  simpa using List.find?_eq_none.1 h t ht

theorem orient_map_swap (f : Bool) (xs : List Span) :
    orient f (xs.map Span.swap) = (orient f xs).map Span.swap := by
  cases f <;> simp [orient]

/-- A key of the run and a key of the mirror that correspond find
corresponding tables, or none. -/
theorem findTable_mirror {tsA tsB : Tables} (R : TabsRel tsA tsB) {K K' : Goal} (hK : IsKey K)
    (hK' : K'.same (KD K) = true) :
    (∃ tA tB, findTable tsA K = some tA ∧ findTable tsB K' = some tB ∧ TabRel tA tB) ∨
      (findTable tsA K = none ∧ findTable tsB K' = none) := by
  cases hA : findTable tsA K with
  | some tA =>
    obtain ⟨htA, hs⟩ := findTable_some hA
    obtain ⟨tB, htB, hr⟩ := R.fwd tA htA
    refine .inl ⟨tA, tB, rfl, findTable_of_mem R.ndB htB ?_, hr⟩
    exact GoalOf.same_trans hr.1 (GoalOf.same_trans (KD_same hs) (GoalOf.same_symm hK'))
  | none =>
    refine .inr ⟨rfl, ?_⟩
    cases hB : findTable tsB K' with
    | none => rfl
    | some tB =>
      exfalso
      obtain ⟨htB, hs⟩ := findTable_some hB
      obtain ⟨tA, htA, hr⟩ := R.bwd tB htB
      have : tA.goal.same K = true :=
        same_of_KD_same (R.keyA tA htA) hK
          (GoalOf.same_trans (GoalOf.same_symm hr.1) (GoalOf.same_trans hs hK'))
      rw [findTable_none hA tA htA] at this; cases this

theorem answersOf_mirror {tsA tsB : Tables} (R : TabsRel tsA tsB) {g h : Goal} (hm : Mirror g h) :
    StepEquiv (answersOf tsB h) ((answersOf tsA g).map Span.swap) := by
  unfold answersOf
  rcases findTable_mirror R (isKey_norm g) hm.2 with ⟨tA, tB, hA, hB, hr⟩ | ⟨hA, hB⟩
  · simp only [hA, hB, hm.1, ← orient_map_swap]
    cases g.norm.1
    · exact hr.2.1
    · exact hr.2.1.map_swap
  · simp only [hA, hB, List.map_nil]; exact StepEquiv.refl _

theorem doneOf_mirror {tsA tsB : Tables} (R : TabsRel tsA tsB) {g h : Goal} (hm : Mirror g h) :
    doneOf tsB h = doneOf tsA g := by
  unfold doneOf
  rcases findTable_mirror R (isKey_norm g) hm.2 with ⟨tA, tB, hA, hB, hr⟩ | ⟨hA, hB⟩
  · simp only [hA, hB, hr.2.2]
  · simp only [hA, hB]

end Symmetry

end R001

end RwLog
