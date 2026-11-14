/-
# The parts of a node are smaller than the node

A proper stretch of a chain, a meet without a member, a member of a meet of
two or more and a member of a union of two or more are smaller than the node
(`RelOf.size`). Proofs about a machine that descends a node part by part go
by induction on the size.
-/
import RwLog.Kernel.NormalFormStable
import RwLog.Trusted.Charged

namespace RwLog

/-- The sizes of the members of a list, added. -/
def sumSize (L : List Rel) : Nat := (L.map RelOf.size).sum

theorem sumSize_append (L₁ L₂ : List Rel) : sumSize (L₁ ++ L₂) = sumSize L₁ + sumSize L₂ := by
  simp [sumSize]

theorem sumSize_sublist {L₁ L₂ : List Rel} (h : L₁.Sublist L₂) : sumSize L₁ ≤ sumSize L₂ := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a _ ih => simp only [sumSize, List.map_cons, List.sum_cons] at ih ⊢; omega
  | cons_cons a _ ih => simp only [sumSize, List.map_cons, List.sum_cons] at ih ⊢; omega

theorem size_le_sumSize : ∀ {L : List Rel} {x : Rel}, x ∈ L → x.size ≤ sumSize L
  | a :: L, x, h => by
    simp only [sumSize, List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := size_le_sumSize h
      simp only [sumSize] at this; omega

theorem size_mkSeq : ∀ {L : List Rel}, L ≠ [] → (mkSeq L).size + 1 = sumSize L + L.length
  | [], h => absurd rfl h
  | [e], _ => by simp [mkSeq, sumSize]
  | e :: e' :: es, _ => by
    have ih := size_mkSeq (L := e' :: es) (by simp)
    rw [show mkSeq (e :: e' :: es) = .seq e (mkSeq (e' :: es)) from rfl]
    simp only [RelOf.size, sumSize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

theorem size_mkAnd : ∀ {L : List Rel}, L ≠ [] → (mkAnd L).size + 1 = sumSize L + L.length
  | [], h => absurd rfl h
  | [e], _ => by simp [mkAnd, sumSize]
  | e :: e' :: es, _ => by
    have ih := size_mkAnd (L := e' :: es) (by simp)
    rw [show mkAnd (e :: e' :: es) = .and e (mkAnd (e' :: es)) from rfl]
    simp only [RelOf.size, sumSize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

theorem size_seqParts : ∀ e : Rel, e.size + 1 = sumSize (seqParts e) + (seqParts e).length
  | .seq a b => by
    have ha := size_seqParts a
    have hb := size_seqParts b
    simp only [seqParts, sumSize_append, List.length_append, RelOf.size]
    omega
  | .zero | .span _ | .or _ _ | .and _ _ | .conv _ | .call _ => by simp [seqParts, sumSize]

theorem size_andParts : ∀ e : Rel, e.size + 1 = sumSize (andParts e) + (andParts e).length
  | .and a b => by
    have ha := size_andParts a
    have hb := size_andParts b
    simp only [andParts, sumSize_append, List.length_append, RelOf.size]
    omega
  | .zero | .span _ | .or _ _ | .seq _ _ | .conv _ | .call _ => by simp [andParts, sumSize]

theorem size_orBranches : ∀ e : Rel, e.size + 1 = sumSize (orBranches e) + (orBranches e).length
  | .or a b => by
    have ha := size_orBranches a
    have hb := size_orBranches b
    simp only [orBranches, sumSize_append, List.length_append, RelOf.size]
    omega
  | .zero | .span _ | .and _ _ | .seq _ _ | .conv _ | .call _ => by simp [orBranches, sumSize]

/-- A proper stretch of a chain is smaller than the chain. -/
theorem size_interval_lt {e m : Rel} {i j : Nat} (hm : e.interval i j = some m)
    (hlt : j - i < (seqParts e).length) : m.size < e.size := by
  unfold RelOf.interval at hm
  split at hm
  · next h =>
    cases hm
    have h : i < j ∧ j ≤ (seqParts e).length := h
    show (mkSeq (((seqParts e).take j).drop i)).size < e.size
    have hne : ((seqParts e).take j).drop i ≠ [] := by
      intro h'
      have := congrArg List.length h'
      simp only [List.length_drop, List.length_take, List.length_nil] at this
      omega
    have h₁ := size_mkSeq hne
    have h₂ := size_seqParts e
    have h₃ : sumSize (((seqParts e).take j).drop i) ≤ sumSize (seqParts e) :=
      sumSize_sublist ((List.drop_sublist _ _).trans (List.take_sublist _ _))
    have h₄ : (((seqParts e).take j).drop i).length = j - i := by
      simp only [List.length_drop, List.length_take]; omega
    omega
  · cases hm

/-- A meet without a member is smaller than the meet. -/
theorem size_without_lt {e m : Rel} {i : Nat} (hm : e.without i = some m) : m.size < e.size := by
  unfold RelOf.without at hm
  split at hm
  · next h =>
    cases hm
    have h : i < (andParts e).length ∧ 2 ≤ (andParts e).length := h
    show (mkAnd ((andParts e).eraseIdx i)).size < e.size
    have hne : (andParts e).eraseIdx i ≠ [] := by
      intro h'
      have := List.length_eraseIdx_of_lt h.1
      rw [h'] at this; simp at this; omega
    have h₁ := size_mkAnd hne
    have h₂ := size_andParts e
    have h₃ : sumSize ((andParts e).eraseIdx i) ≤ sumSize (andParts e) :=
      sumSize_sublist (List.eraseIdx_sublist _ _)
    have h₄ := List.length_eraseIdx_of_lt h.1
    omega
  · cases hm

/-- A member of a meet of two or more is smaller than the meet. -/
theorem size_andPart_lt {e x : Rel} (hx : x ∈ andParts e) (h2 : 2 ≤ (andParts e).length) :
    x.size < e.size := by
  have := size_andParts e
  have := size_le_sumSize hx
  omega

/-- A member of a union of two or more is smaller than the union. -/
theorem size_orBranch_lt {e x : Rel} (hx : x ∈ orBranches e) (h2 : 2 ≤ (orBranches e).length) :
    x.size < e.size := by
  have := size_orBranches e
  have := size_le_sumSize hx
  omega

end RwLog
