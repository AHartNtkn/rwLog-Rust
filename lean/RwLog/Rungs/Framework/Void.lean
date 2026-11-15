/-
# Goals that relate nothing

A goal `⟨lb, node, rb⟩` and a ground relation `G` its node derives stand for
the pairs of `lb ; G ; rb` (`pairsOf`). A goal is *void* when no derivation
of its node relates a pair between its boundaries (`Void`). A void goal has
no answer (`void_no_ans`): the representative of an answer relates a pair.

The goal of the normal form of a query that relates nothing is void
(`void_of_pairs`); a chain with no boundary one side of which is void is
void (`void_mkSeq_left`, `void_mkSeq_right`), and so is a meet with no
boundary some members of which make a void meet (`void_mkAnd`).

Nothing here is about a machine.
-/
import RwLog.Rungs.Framework.Goals
import RwLog.Kernel.NormalFormMap
import RwLog.Kernel.NormalFormDepth
import RwLog.Kernel.DomainLaws
import RwLog.Kernel.Wrap

namespace RwLog

open Answer Goals

variable {R : Type} [Answer R] {D : Domain R} {P : Program}

/-- The pairs of `lb ; G ; rb`, for a ground relation `G` the node of the
goal derives. -/
def pairsOf (P : Program) (g : GoalOf R Rel) (G : GRel) : PRel :=
  wrapAt P.sorts.interp g.lb (G.at P.sorts.interp) g.rb

/-- The goal of a node with no boundary. -/
abbrev bare (e : Rel) : GoalOf R Rel := ⟨none, e, none⟩

/-- No derivation of the node of the goal relates a pair between its
boundaries. -/
def Void (P : Program) (g : GoalOf R Rel) : Prop :=
  ∀ k G, G ∈ GDn P k g.node → pairsOf P g G = ∅

theorem comp_empty_left (Y : PRel) : PRel.comp ∅ Y = ∅ :=
  Set.eq_empty_of_forall_notMem fun ⟨_, _⟩ ⟨_, h, _⟩ => h

theorem comp_empty_right (X : PRel) : PRel.comp X ∅ = ∅ :=
  Set.eq_empty_of_forall_notMem fun ⟨_, _⟩ ⟨_, _, h⟩ => h

/-- An answer of a goal relates the pairs of a derivation of its node between
its boundaries. -/
theorem ans_gdn (hL : D.Lawful P.sorts.interp) {g : GoalOf R Rel} {a : Ans D P}
    (ha : a.goal = toGoal g) :
    ∃ k G, G ∈ GDn P k g.node ∧ den P.sorts.interp a.span = pairsOf P g G := by
  obtain ⟨s, hs, e⟩ := a.valid.2 hL
  rw [ha] at hs e
  obtain ⟨k, hk⟩ := mem_gd_iff.1 (show s.den ∈ GD P g.node from hs.derivesG)
  exact ⟨k, s.den, hk, e⟩

/-- A void goal has no answer. -/
theorem void_no_ans (hL : D.Lawful P.sorts.interp) {g : GoalOf R Rel} (hv : Void P g)
    (a : Ans D P) : a.goal ≠ toGoal g := by
  intro ha
  obtain ⟨k, G, hG, e⟩ := ans_gdn hL ha
  have := hL.live a.span
  rw [e, hv k G hG] at this
  exact Set.not_nonempty_empty this

/-- The goal of the normal form of a query that relates nothing is void. -/
theorem void_of_pairs {q : Rel} (h : P.pairs q = ∅) : Void P (bare q.norm : GoalOf R Rel) := by
  intro k G hG
  unfold pairsOf
  rw [show wrapAt P.sorts.interp (none : Option R) (G.at P.sorts.interp) none = _ from
    wrapAt_none _]
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  have hmem : p ∈ P.pairs q := by
    unfold ProgramOf.pairs
    rw [ProgramOf.semAt_eq, sem_eq_sUnion_gd]
    obtain ⟨S, hS, hM⟩ := hp
    exact ⟨S, ⟨G, by rw [← gd_norm]; exact gdn_sub_gd k _ hG, hS⟩, hM⟩
  rw [h] at hmem
  exact hmem

/-- A chain with no boundary whose first members make a void chain is
void. -/
theorem void_mkSeq_left {xs : List Rel} {p : Nat} (hp : 0 < p) (hp' : p < xs.length)
    (hv : Void P (bare (mkSeq (xs.take p)) : GoalOf R Rel)) :
    Void P (bare (mkSeq xs) : GoalOf R Rel) := by
  intro k G hG
  have hne : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
  have ht : xs.take p ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_take]; omega)
  change G ∈ GDn P k (mkSeq xs) at hG
  rw [(gdn_laws P k).gd_mkSeq hne, ← List.take_append_drop p xs, List.map_append,
    seqAll_append, ← (gdn_laws P k).gd_mkSeq ht] at hG
  obtain ⟨G₁, hG₁, G₂, -, rfl⟩ := hG
  have := hv k G₁ hG₁
  unfold pairsOf at this ⊢
  rw [wrap_comp, this, comp_empty_left]

/-- A chain with no boundary whose last members make a void chain is
void. -/
theorem void_mkSeq_right {xs : List Rel} {p : Nat} (hp : 0 < p) (hp' : p < xs.length)
    (hv : Void P (bare (mkSeq (xs.drop p)) : GoalOf R Rel)) :
    Void P (bare (mkSeq xs) : GoalOf R Rel) := by
  intro k G hG
  have hne : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
  have ht : xs.drop p ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_drop]; omega)
  change G ∈ GDn P k (mkSeq xs) at hG
  rw [(gdn_laws P k).gd_mkSeq hne, ← List.take_append_drop p xs, List.map_append,
    seqAll_append, ← (gdn_laws P k).gd_mkSeq ht] at hG
  obtain ⟨G₁, -, G₂, hG₂, rfl⟩ := hG
  have := hv k G₂ hG₂
  unfold pairsOf at this ⊢
  rw [wrap_comp, this, comp_empty_right]

/-- A meet with no boundary some members of which make a void meet is
void. -/
theorem void_mkAnd (hL : D.Lawful P.sorts.interp) {A C ys : List Rel} (hA : A ≠ [])
    (hperm : ys.Perm (A ++ C)) (hv : Void P (bare (mkAnd A) : GoalOf R Rel)) :
    Void P (bare (mkAnd ys) : GoalOf R Rel) := by
  intro k G hG
  have hne : ys ≠ [] := by
    intro h
    have := hperm.length_eq
    rw [h] at this
    have := List.length_pos_iff.2 hA
    simp at *
    omega
  change G ∈ GDn P k (mkAnd ys) at hG
  rw [(gdn_laws P k).gd_mkAnd hne, andAll_perm (hperm.map (GDn P k)), List.map_append,
    andAll_append, ← (gdn_laws P k).gd_mkAnd hA] at hG
  obtain ⟨G₁, hG₁, G₂, -, rfl⟩ := hG
  have := hv k G₁ hG₁
  unfold pairsOf at this ⊢
  rw [wrap_meet hL (fun _ h => by cases h) (fun _ h => by cases h), this, Set.empty_inter]

theorem mkAnd_eraseIdx_one : ∀ {ys : List Rel} {l : Rel}, ys.length = 2 → ys[0]? = some l →
    mkAnd (ys.eraseIdx 1) = l
  | [y, y'], l, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl

end RwLog
