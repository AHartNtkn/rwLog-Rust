/-
# Splitting a node of the normal form

A chain split in two anywhere inside it, and a meet split into a member and
the meet of the others: the two sides are nodes, they are smaller, and
joining them (`mkSeq` of the members of both, `mkAnd` of the sorted members
of both, in either order) gives the node back. So the answer the kernel's
`join` or `meetA` makes of answers of the two sides is an answer of the node
that was split.
-/
import RwLog.Kernel.NormalFormSize
import RwLog.Trusted.Kernel

namespace RwLog

theorem forget_span {e : Rel} (h : e.view.forget = .span ()) : ∃ s, e = .span s := by
  cases e with
  | span s => exact ⟨s, rfl⟩
  | conv a => cases a <;> simp [RelOf.view, NodeView.forget] at h
  | _ => simp [RelOf.view, NodeView.forget] at h

theorem forget_chain {e : Rel} {xs : List Rel} (h : e.view.forget = .chain xs) :
    e.view = .chain xs := by
  cases hv : e.view <;> rw [hv] at h <;> simp only [NodeView.forget] at h <;> cases h
  rfl

theorem forget_meet {e : Rel} {xs : List Rel} (h : e.view.forget = .meet xs) :
    e.view = .meet xs := by
  cases hv : e.view <;> rw [hv] at h <;> simp only [NodeView.forget] at h <;> cases h
  rfl

theorem forget_union {e : Rel} {xs : List Rel} (h : e.view.forget = .union xs) :
    e.view = .union xs := by
  cases hv : e.view <;> rw [hv] at h <;> simp only [NodeView.forget] at h <;> cases h
  rfl

/-- A node read as a call has a body. -/
theorem forget_call {P : Program} {e : Rel} {n : Name} {f : Bool}
    (h : e.view.forget = .call n f) : ∃ b, Charged.bodyOf P e = some b := by
  cases e with
  | call m => exact ⟨_, rfl⟩
  | conv a =>
    cases a with
    | call m => exact ⟨_, rfl⟩
    | _ => simp [RelOf.view, NodeView.forget] at h
  | _ => simp [RelOf.view, NodeView.forget] at h

/-- A chain split in two inside it. -/
theorem Normal.chain_split {e : Rel} {xs : List Rel} {i : Nat} (hn : Normal e)
    (hv : e.view = .chain xs) (h0 : 0 < i) (hi : i < xs.length) :
    (seqParts e).length = xs.length ∧
    ∃ l r, e.interval 0 i = some l ∧ e.interval i xs.length = some r ∧
      mkSeq (seqParts l ++ seqParts r) = e ∧ l.size < e.size ∧ r.size < e.size := by
  obtain ⟨h2, hmem, hmk⟩ := hn.view_chain hv
  have hne : xs ≠ [] := by intro h; rw [h] at h2; simp at h2
  have hparts : seqParts e = xs := by
    rw [← hmk]; exact seqParts_mkSeq hne fun x hx => (hmem x hx).2
  have hl : e.interval 0 i = some (mkSeq ((xs.take i).drop 0)) := by
    unfold RelOf.interval
    simp only [RelOf.chainParts, hparts]
    exact ite_eq_left_iff.2 fun h => absurd ⟨h0, by omega⟩ h
  have hr : e.interval i xs.length = some (mkSeq ((xs.take xs.length).drop i)) := by
    unfold RelOf.interval
    simp only [RelOf.chainParts, hparts]
    exact ite_eq_left_iff.2 fun h => absurd ⟨hi, Nat.le_refl _⟩ h
  refine ⟨by rw [hparts], _, _, hl, hr, ?_, ?_, ?_⟩
  · have h₁ : seqParts (mkSeq ((xs.take i).drop 0)) = xs.take i := by
      rw [List.drop_zero]
      exact seqParts_mkSeq (by simp only [ne_eq, List.take_eq_nil_iff, not_or]; exact ⟨by omega, hne⟩)
        fun x hx => (hmem x (List.mem_of_mem_take hx)).2
    have h₂ : seqParts (mkSeq ((xs.take xs.length).drop i)) = xs.drop i := by
      rw [List.take_length]
      exact seqParts_mkSeq (by simp only [ne_eq, List.drop_eq_nil_iff, not_le]; exact hi)
        fun x hx => (hmem x (List.mem_of_mem_drop hx)).2
    rw [h₁, h₂, List.take_append_drop, hmk]
  · exact size_interval_lt hl (by rw [hparts]; omega)
  · exact size_interval_lt hr (by rw [hparts]; omega)

/-- A meet split into a member and the meet of the others. -/
theorem Normal.meet_split {e : Rel} {xs : List Rel} {i : Nat} (hn : Normal e)
    (hv : e.view = .meet xs) (hi : i < xs.length) :
    andParts e = xs ∧
    ∃ l r, xs[i]? = some l ∧ e.without i = some r ∧
      mkAnd (sortedParts (andParts l ++ andParts r)) = e ∧
      mkAnd (sortedParts (andParts r ++ andParts l)) = e ∧ l.size < e.size ∧ r.size < e.size := by
  obtain ⟨h2, hmem, hsorted, hmk⟩ := hn.view_meet hv
  have hne : xs ≠ [] := by intro h; rw [h] at h2; simp at h2
  have hparts : andParts e = xs := by
    rw [← hmk]; exact andParts_mkAnd hne fun x hx => (hmem x hx).2
  have hr : e.without i = some (mkAnd (xs.eraseIdx i)) := by
    unfold RelOf.without
    simp only [RelOf.meetParts, hparts]
    exact ite_eq_left_iff.2 fun h => absurd ⟨hi, h2⟩ h
  have hene : xs.eraseIdx i ≠ [] := by
    intro h'
    have := List.length_eraseIdx_of_lt hi
    rw [h'] at this; simp at this; omega
  have h₁ : andParts xs[i] = [xs[i]] := andParts_notAnd (hmem _ (List.getElem_mem hi)).2
  have h₂ : andParts (mkAnd (xs.eraseIdx i)) = xs.eraseIdx i :=
    andParts_mkAnd hene fun x hx => (hmem x (List.mem_of_mem_eraseIdx hx)).2
  have hp : ([xs[i]] ++ xs.eraseIdx i).Perm xs := List.getElem_cons_eraseIdx_perm hi
  refine ⟨hparts, xs[i], _, List.getElem?_eq_getElem hi, hr, ?_, ?_, ?_, ?_⟩
  · rw [h₁, h₂, sortedParts_eq hp, sortedParts_of_sorted hsorted, hmk]
  · rw [h₁, h₂, sortedParts_eq (List.perm_append_comm.trans hp), sortedParts_of_sorted hsorted,
      hmk]
  · exact size_andPart_lt (by rw [hparts]; exact List.getElem_mem hi) (by rw [hparts]; exact h2)
  · exact size_without_lt hr

/-- A member of a union is smaller than the union. -/
theorem Normal.union_member_lt {e x : Rel} {xs : List Rel} (hn : Normal e)
    (hv : e.view = .union xs) (hx : x ∈ xs) : x.size < e.size := by
  cases e with
  | zero =>
    have : xs = [] := by simpa [RelOf.view] using hv.symm
    rw [this] at hx; cases hx
  | or a b =>
    have hxs : orBranches (.or a b) = xs := by simpa [RelOf.view] using hv
    refine size_orBranch_lt (hxs ▸ hx) ?_
    have ha := List.length_pos_iff.2 (orBranches_ne_nil a)
    have hb := List.length_pos_iff.2 (orBranches_ne_nil b)
    simp only [orBranches, List.length_append]; omega
  | conv a => obtain ⟨n, rfl⟩ := normal_conv.1 hn; simp [RelOf.view] at hv
  | _ => simp [RelOf.view] at hv

end RwLog
