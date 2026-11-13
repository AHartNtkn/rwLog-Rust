/-
# The separating family: which tables complete in a round

Completion is a greatest fixpoint: the largest set of open tables that gained
nothing in the round and each have a strategy all of whose dependencies exist,
gained nothing, and are complete or in the set. Here the fixpoint is found on
the tables of the run, by name: it is exactly the set of tables that
`isDone` says are complete after the round and not before
(`closed_completes`, `completes_closed`).

A link `c j` below the depth completes through the unfolding race, with no
dependency. A link above the depth depends on the link below it, and so on
down to the last link created, whose dependency has no table yet: none of
them can be in the set. This chain is what makes the fixpoint take a pass per
link.
-/
import RwLog.Rungs.R002.Proofs.Separation.NewTables

namespace RwLog

namespace R002

namespace Sep

/-- The table gains its answer in the round at depth `d`. -/
def gainedS (k d : Nat) (s : Slot) : Bool :=
  decide ((ans k (d + 1) s).length ≠ (ans k d s).length)

theorem gainedS_iff (k d : Nat) (s : Slot) :
    gainedS k d s = true ↔ ¬ hasAns k d s = true ∧ hasAns k (d + 1) s = true := by
  unfold gainedS ans
  by_cases h : hasAns k d s = true
  · simp [h, hasAns_mono k d s h]
  · by_cases h' : hasAns k (d + 1) s = true <;> simp [h, h']

/-- The table completes in the round at depth `d`. -/
def completes (k d : Nat) (s : Slot) : Bool := !isDone k d s && isDone k (d + 1) s

theorem completes_iff (k d : Nat) (s : Slot) :
    completes k d s = true ↔ ¬ isDone k d s = true ∧ isDone k (d + 1) s = true := by
  simp [completes]

/-- The completion test of one table, given which tables are in the set. -/
def okS (k d : Nat) (X : Slot → Bool) (s : Slot) : Bool :=
  (uval d s).1 || (dep k s).all fun r =>
    decide (r ∈ slots k d) && !gainedS k d r && (isDone k d r || X r)

theorem okS_mono (k d : Nat) {X Y : Slot → Bool} (h : ∀ r, X r = true → Y r = true) (s : Slot)
    (hs : okS k d X s = true) : okS k d Y s = true := by
  unfold okS at hs ⊢
  rw [Bool.or_eq_true] at hs ⊢
  rcases hs with h1 | h1
  · exact Or.inl h1
  · right
    rw [List.all_eq_true] at h1 ⊢
    intro r hr
    have := h1 r hr
    simp only [Bool.and_eq_true, Bool.or_eq_true] at this ⊢
    exact ⟨this.1, this.2.imp id (h r)⟩

/-- A link of the chain in a closed set completes this round. -/
theorem chain_completes (k d : Nat) (X : Slot → Bool)
    (hX : ∀ s, s.inAt k d → X s = true →
      ¬ isDone k d s = true ∧ ¬ gainedS k d s = true ∧ okS k d X s = true) :
    ∀ j, (Slot.c j).inAt k d → X (.c j) = true → completes k d (.c j) = true := by
  intro j
  induction j with
  | zero =>
    intro hin hx
    obtain ⟨hd, hg, hok⟩ := hX _ hin hx
    simp only [Slot.inAt] at hin
    rw [gainedS_iff, hasAns_c, hasAns_c] at hg
    rw [isDone_c] at hd
    rw [completes_iff, isDone_c, isDone_c]
    omega
  | succ j ih =>
    intro hin hx
    obtain ⟨hd, hg, hok⟩ := hX _ hin hx
    simp only [Slot.inAt] at hin
    rw [gainedS_iff, hasAns_c, hasAns_c] at hg
    rw [isDone_c] at hd
    rw [completes_iff, isDone_c, isDone_c]
    by_cases hf : j + 1 + 1 ≤ d
    · omega
    · exfalso
      simp only [okS, uval, hf, ↓reduceIte, Bool.false_or, dep, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hmem, _⟩, hdx⟩ := hok
      have hin' := mem_slots.1 hmem
      rcases hdx with hdn | hx'
      · rw [isDone_c] at hdn; omega
      · have := ih hin' hx'
        rw [completes_iff, isDone_c, isDone_c] at this
        omega

/-- Every table in a closed set completes this round. -/
theorem closed_completes (k d : Nat) (X : Slot → Bool)
    (hX : ∀ s, s.inAt k d → X s = true →
      ¬ isDone k d s = true ∧ ¬ gainedS k d s = true ∧ okS k d X s = true) :
    ∀ s, s.inAt k d → X s = true → completes k d s = true := by
  intro s hin hx
  cases s with
  | c j => exact chain_completes k d X hX j hin hx
  | root =>
    obtain ⟨hd, hg, hok⟩ := hX _ hin hx
    rw [gainedS_iff, hasAns_root, hasAns_root] at hg
    rw [isDone_root] at hd
    rw [completes_iff, isDone_root, isDone_root]
    simp only [okS, uval, Bool.false_or, dep, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hmem, _⟩, hdx⟩, _⟩ := hok
    rcases hdx with hdn | hx'
    · rw [isDone_c] at hdn; omega
    · have := chain_completes k d X hX k (mem_slots.1 hmem) hx'
      rw [completes_iff, isDone_c, isDone_c] at this
      omega
  | w =>
    obtain ⟨hd, _, _⟩ := hX _ hin hx
    simp only [Slot.inAt] at hin
    rw [isDone_w] at hd
    rw [completes_iff, isDone_w, isDone_w]
    omega
  | z =>
    obtain ⟨hd, hg, _⟩ := hX _ hin hx
    simp only [Slot.inAt] at hin
    rw [gainedS_iff, hasAns_z, hasAns_z] at hg
    rw [isDone_z] at hd
    rw [completes_iff, isDone_z, isDone_z]
    omega

/-- A table that completes this round gained nothing in it. -/
theorem completes_not_gained (k d : Nat) (s : Slot) (h : completes k d s = true) :
    ¬ gainedS k d s = true := by
  rw [gainedS_iff]
  rw [completes_iff] at h
  cases s with
  | root => rw [isDone_root, isDone_root] at h; rw [hasAns_root, hasAns_root]; omega
  | c j => rw [isDone_c, isDone_c] at h; rw [hasAns_c, hasAns_c]; omega
  | w => simp
  | z => rw [isDone_z, isDone_z] at h; rw [hasAns_z, hasAns_z]; omega

/-- The tables that complete this round form a closed set. -/
theorem completes_closed (k d : Nat) (X : Slot → Bool)
    (hX : ∀ s, s.inAt k d → completes k d s = true → X s = true) :
    ∀ s, s.inAt k d → completes k d s = true → okS k d X s = true := by
  intro s hin hc
  have hc' := (completes_iff k d s).1 hc
  cases s with
  | root =>
    rw [isDone_root, isDone_root] at hc'
    have h1 : Slot.c k ∈ slots k d := mem_slots.2 ⟨le_rfl, by omega⟩
    have h2 : Slot.w ∈ slots k d := mem_slots.2 (by simp only [Slot.inAt]; omega)
    have h3 : gainedS k d (.c k) = false := by
      rw [Bool.eq_false_iff, ne_eq, gainedS_iff, hasAns_c, hasAns_c]; omega
    have h4 : gainedS k d .w = false := by
      rw [Bool.eq_false_iff, ne_eq, gainedS_iff]; simp
    have h5 : isDone k d (.c k) = true := by rw [isDone_c]; omega
    have h6 : isDone k d .w = true := by rw [isDone_w]; omega
    simp [okS, dep, h1, h2, h3, h4, h5, h6]
  | c j =>
    rw [isDone_c, isDone_c] at hc'
    have : j + 1 ≤ d := by omega
    simp [okS, uval, this]
  | w =>
    simp only [Slot.inAt] at hin
    rw [isDone_w, isDone_w] at hc'
    have h2 : Slot.w ∈ slots k d := mem_slots.2 hin
    have h4 : gainedS k d .w = false := by
      rw [Bool.eq_false_iff, ne_eq, gainedS_iff]; simp
    have h5 := hX .w hin hc
    simp [okS, dep, h2, h4, h5]
  | z => simp [okS, dep]

end Sep

end R002

end RwLog
