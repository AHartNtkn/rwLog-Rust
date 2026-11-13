/-
# The separating family: the stages of a round

A round of the charged machine asks the oracle about every open table,
recomputes each table's candidates, keeps the fresh ones, collects the goals
asked for, and creates tables for the new ones. Here is what each of these
stages returns and spends on the tables `tabs k d` of the run. Completion is
in `Completion.lean`.
-/
import RwLog.Rungs.R002.Proofs.Separation.Lookups

namespace RwLog

namespace R002

namespace Sep

open Cost R001

/-! ## Reading a dependency -/

/-- A name of the family: a link `c j` has `j ≤ k`. -/
def Slot.ok (k : Nat) : Slot → Prop
  | .c j => j ≤ k
  | _ => True

theorem Slot.inAt.ok {k d : Nat} {s : Slot} (h : s.inAt k d) : s.ok k := by
  cases s with
  | c j => exact h.1
  | _ => trivial

theorem dep_ok {k : Nat} {s r : Slot} (hs : s.ok k) (hr : r ∈ dep k s) : r.ok k := by
  cases s with
  | root => simp [dep] at hr; rcases hr with rfl | rfl <;> simp [Slot.ok]
  | c j =>
    cases j with
    | zero => simp [dep] at hr; subst hr; trivial
    | succ j => simp [dep] at hr; subst hr; simp only [Slot.ok] at hs ⊢; omega
  | w => simp [dep] at hr; subst hr; trivial
  | z => simp [dep] at hr

/-- A table that does not exist yet has no answer. -/
theorem ans_of_mem {k d : Nat} {s : Slot} (hs : s.ok k) :
    (if s ∈ slots k d then ans k d s else []) = ans k d s := by
  by_cases h : s ∈ slots k d
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [mem_slots] at h
    cases s with
    | root => exact absurd trivial h
    | c j =>
      simp only [Slot.inAt, Slot.ok] at h hs
      simp only [ans, hasAns, decide_eq_true_eq]
      split <;> first | omega | rfl
    | w => rfl
    | z =>
      simp only [Slot.inAt] at h
      simp only [ans, hasAns, decide_eq_true_eq]
      split <;> first | omega | rfl

/-- The answers of the table of a name of the family. -/
theorem answers_costs (k d : Nat) {s : Slot} (hs : s.ok k) :
    Costs (Tabled.answersOf (tabs k d) (goal k s)) (ans k d s) (3 + (slots k d).length * 6) :=
  (answersOf_costs k d s (goalSize_goal k s) (norm_goal k s)).congr_val (ans_of_mem hs)

/-! ## Candidates -/

/-- The candidates a table reads from other tables. -/
def tcands (k d : Nat) : Slot → List Span
  | .z => [zz]
  | s => (dep k s).flatMap (ans k d)

/-- The goals a table asks for. -/
def reqG (k : Nat) : Slot → List Goal
  | .root => [gC k, gW]
  | .c (j + 1) => [gC j]
  | .c 0 => [gZ]
  | .w => [wBody]
  | .z => []

theorem produce_costs (k d : Nat) {s : Slot} (hs : s.inAt k d) :
    Costs (Tabled.produceStrategies (prog k) (tabs k d) (goal k s)) (tcands k d s, reqG k s)
      (12 * (slots k d).length + 6) := by
  cases s with
  | root =>
    have h1 := answers_costs k d (s := .c k) (by simp [Slot.ok])
    have h2 := answers_costs k d (s := .w) trivial
    simp only [goal, Tabled.produceStrategies, orLeaves, orBranches, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil, flatMapL]
    refine Costs.congr_val (Costs.mono
      (Costs.bind (Costs.bind h1 (Costs.bind (Costs.bind h2 (Costs.bind (Costs.pure _)
        (Costs.pure _))) (Costs.pure _))) (Costs.pure _)) (by omega)) ?_
    simp [tcands, dep, reqG]
  | c j =>
    cases j with
    | zero =>
      have h1 := answers_costs k d (s := .z) trivial
      simp only [goal, Tabled.produceStrategies, callGoal, body_zero]
      refine Costs.congr_val (Costs.mono (Costs.bind h1 (Costs.pure _)) (by omega)) ?_
      simp [tcands, dep, reqG]
    | succ j =>
      have h1 := answers_costs k d (s := .c j) (by have := hs.1; simp only [Slot.ok]; omega)
      simp only [goal, Tabled.produceStrategies, callGoal, body_succ (Nat.lt_of_succ_le hs.1)]
      refine Costs.congr_val (Costs.mono (Costs.bind h1 (Costs.pure _)) (by omega)) ?_
      simp [tcands, dep, reqG]
  | w =>
    have h1 := (answersOf_costs k d .w goalSize_wBody norm_wBody).congr_val
      (ans_of_mem (k := k) (d := d) (s := .w) trivial)
    simp only [goal, Tabled.produceStrategies, callGoal, body_w]
    refine Costs.congr_val (Costs.mono (Costs.bind h1 (Costs.pure _)) (by omega)) ?_
    simp [tcands, dep, reqG]
  | z =>
    have hv : RwLog.live [] zz = [zz] := live_zz.1
    have ht := live_zz_ticks
    refine ⟨?_, ?_⟩
    · simp [goal, Tabled.produceStrategies, R001.spanAnswer, hv, tcands, reqG]
    · simp [goal, Tabled.produceStrategies, Tabled.spanAnswer]
      omega

/-! ## Fresh candidates

Every candidate of the run is `z -> z`, so a table gains that one answer the
first time it has a candidate, and nothing afterwards. -/

theorem zz_size : zz.size = 2 := by simp [Span.size, Store.size, Term.size]

theorem covers_zz_val : zz.covers? zz = true := RwLog.covers?_refl zz

theorem maxima_zz {xs : List Span} (h : ∀ x ∈ xs, x = zz) :
    Costs (Tabled.maxima xs) (if xs = [] then [] else [zz])
      (xs.length * (xs.length * 8) + xs.length * 4) := by
  unfold Tabled.maxima
  have htop : Costs (filterL (fun x => do
      let b ← anyL (fun y => do
        let c ← Charged.covers y x
        if c then do
          let c' ← Charged.covers x y
          pure !c'
        else pure false) xs
      pure !b) xs) xs (xs.length * (xs.length * 8)) := by
    have := Costs.filterL (xs := xs) (g := fun _ => true) (c := xs.length * 8)
      (f := fun x => do
        let b ← anyL (fun y => do
          let c ← Charged.covers y x
          if c then do
            let c' ← Charged.covers x y
            pure !c'
          else pure false) xs
        pure !b) (by
        intro x hx
        have hin := Costs.anyL (xs := xs) (g := fun _ => false) (c := 8)
          (f := fun y => do
            let c ← Charged.covers y x
            if c then do
              let c' ← Charged.covers x y
              pure !c'
            else pure false) (by
            intro y hy
            rw [h x hx, h y hy]
            exact ⟨by simp [Charged.covers, covers_zz_val],
              by simp [Charged.covers, covers_zz_val, zz_size]⟩)
        refine Costs.congr_val (Costs.mono (Costs.bind hin (Costs.pure _)) (Nat.le_refl _)) ?_
        simp)
    simpa using this
  have hfold : Costs (foldL (fun acc x => do
      let b ← anyL (fun y => Charged.covers y x) acc
      pure (if b then acc else acc ++ [x])) [] xs) (xs.foldl (fun _ _ => [zz]) []) (xs.length * 4) := by
    refine Costs.foldL (fun acc => acc = [] ∨ acc = [zz]) (Or.inl rfl) ?_
    intro acc hacc x hx
    refine ⟨?_, Or.inr rfl⟩
    rw [h x hx]
    rcases hacc with rfl | rfl
    · exact ⟨rfl, by simp [anyL]⟩
    · exact ⟨by simp [anyL, Charged.covers, covers_zz_val],
        by simp [anyL, Charged.covers, covers_zz_val, zz_size]⟩
  refine Costs.congr_val (Costs.bind htop hfold) ?_
  cases xs with
  | nil => rfl
  | cons x xs =>
    have : ∀ (l : List Span) (a : List Span), l.foldl (fun _ _ => [zz]) [zz] = [zz] := by
      intro l _; induction l with
      | nil => rfl
      | cons _ _ ih => exact ih
    simpa using this xs []

theorem fresh_zz {old cands : List Span} (ho : old = [] ∨ old = [zz]) (hc : ∀ x ∈ cands, x = zz) :
    Costs (Tabled.fresh old cands) (if old = [] ∧ cands ≠ [] then [zz] else [])
      (cands.length * 4 + (cands.length * (cands.length * 8) + cands.length * 4)) := by
  unfold Tabled.fresh
  rcases ho with rfl | rfl
  · have hf := Costs.filterL (xs := cands) (g := fun _ => true) (c := 0)
      (f := fun c => do
        let b ← anyL (fun t => Charged.covers t c) []
        pure !b) (fun c _ => ⟨rfl, by simp [anyL]⟩)
    rw [List.filter_true] at hf
    refine Costs.congr_val (Costs.mono (Costs.bind hf (maxima_zz hc)) (by omega)) ?_
    by_cases h : cands = [] <;> simp [h]
  · have hf := Costs.filterL (xs := cands) (g := fun _ => false) (c := 4)
      (f := fun c => do
        let b ← anyL (fun t => Charged.covers t c) [zz]
        pure !b) (fun c hc' => by
          rw [hc c hc']
          exact ⟨by simp [anyL, Charged.covers, covers_zz_val],
            by simp [anyL, Charged.covers, covers_zz_val, zz_size]⟩)
    rw [List.filter_false] at hf
    refine Costs.congr_val (Costs.mono (Costs.bind hf (maxima_zz (xs := []) (by simp))) (by simp)) ?_
    simp

/-! ## The stages -/

/-- What the oracle stage returns for a table. -/
def usV (k d : Nat) (s : Slot) : Bool × List Span := if isDone k d s then (false, []) else uval d s

theorem us_costs (k d : Nat) :
    Costs (mapL (fun t : Table => if t.done then pure (false, []) else do
        tick (goalSize t.goal)
        onDemand (prog k) d t.goal) (tabs k d))
      ((slots k d).map (usV k d)) ((slots k d).length * (2 * d + k + 8)) := by
  rw [tabs]
  refine Costs.mapL_map fun s hs => ?_
  simp only [tab, usV]
  by_cases h : isDone k d s = true
  · simp only [h]
    exact (Costs.pure _).mono (Nat.zero_le _)
  · simp only [h]
    refine Costs.mono (c := 3 + (2 * d + k + 5)) ?_ (by omega)
    exact Costs.bind ⟨rfl, goalSize_goal k s⟩ (race k d s (mem_slots.1 hs))

/-- The candidates and the goals asked for by a table. -/
def outV (k d : Nat) (s : Slot) : List Span × List Goal :=
  if isDone k d s then ([], []) else ((usV k d s).2 ++ tcands k d s, reqG k s)

theorem outs_costs (k d : Nat) :
    Costs (mapL (fun p : Table × (Bool × List Span) =>
        if p.1.done then pure ([], []) else Tabled.produce (prog k) (tabs k d) p.1.goal p.2)
        ((tabs k d).zip ((slots k d).map (usV k d))))
      ((slots k d).map (outV k d)) ((slots k d).length * (12 * (slots k d).length + 6)) := by
  conv => arg 1; arg 2; rw [tabs, List.zip_map']
  refine Costs.mapL_map fun s hs => ?_
  simp only [tab, outV]
  by_cases h : isDone k d s = true
  · simp only [h]
    exact (Costs.pure _).mono (Nat.zero_le _)
  · simp only [h]
    refine Costs.mono (c := 12 * (slots k d).length + 6 + 0) ?_ (by omega)
    exact Costs.bind (produce_costs k d (mem_slots.1 hs)) (Costs.pure _)

/-- The table after this round's answers were added. -/
def tab1 (k d : Nat) (s : Slot) : Table := ⟨goal k s, ans k (d + 1) s, isDone k d s⟩

theorem ans_zz (k d : Nat) (s : Slot) : ∀ x ∈ ans k d s, x = zz := by
  unfold ans; split <;> simp

theorem ans_length (k d : Nat) (s : Slot) : (ans k d s).length ≤ 1 := by
  unfold ans; split <;> simp

theorem ans_cases (k d : Nat) (s : Slot) : ans k d s = [] ∨ ans k d s = [zz] := by
  unfold ans; split <;> simp

theorem cands_zz (k d : Nat) (s : Slot) : ∀ x ∈ (outV k d s).1, x = zz := by
  intro x hx
  unfold outV at hx
  split at hx
  · simp at hx
  · simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · unfold usV at hx
      split at hx
      · simp at hx
      · cases s <;> simp only [uval] at hx
        · simp at hx
        · split at hx <;> simp at hx; exact hx
        · simp at hx
        · simpa using hx
    · cases s with
      | z => simpa [tcands] using hx
      | root | c _ | w =>
        simp only [tcands, List.mem_flatMap] at hx
        obtain ⟨r, _, hr⟩ := hx
        exact ans_zz k d r x hr

theorem cands_length (k d : Nat) (s : Slot) : (outV k d s).1.length ≤ 3 := by
  unfold outV
  split
  · simp
  · have h1 : (usV k d s).2.length ≤ 1 := by
      unfold usV; split
      · simp
      · cases s <;> simp only [uval]
        · simp
        · split <;> simp
        · simp
        · simp
    have h2 : (tcands k d s).length ≤ 2 := by
      cases s with
      | z => simp [tcands]
      | root =>
        have := ans_length k d (.c k); have := ans_length k d .w
        simp [tcands, dep]; omega
      | c j =>
        cases j with
        | zero => have := ans_length k d .z; simp [tcands, dep]; omega
        | succ j => have := ans_length k d (.c j); simp [tcands, dep]; omega
      | w => have := ans_length k d .w; simp [tcands, dep]; omega
    simp only [List.length_append]; omega

theorem outV_fst_done {k d : Nat} {s : Slot} (h : isDone k d s = true) : (outV k d s).1 = [] := by
  simp [outV, h]

theorem outV_fst_open {k d : Nat} {s : Slot} (h : ¬ isDone k d s = true) :
    (outV k d s).1 = (uval d s).2 ++ tcands k d s := by
  simp [outV, usV, h]

/-- A table without an answer has a candidate exactly when it has its answer
after the round. -/
theorem cands_ne (k d : Nat) (s : Slot) (hs : s.inAt k d) (hn : ¬ hasAns k d s = true) :
    (outV k d s).1 ≠ [] ↔ hasAns k (d + 1) s = true := by
  by_cases hd : isDone k d s = true
  · rw [outV_fst_done hd]
    cases s with
    | root => rw [hasAns_root] at hn; rw [isDone_root] at hd; omega
    | c j => rw [hasAns_c] at hn; rw [isDone_c] at hd; omega
    | w => simp
    | z => rw [hasAns_z] at hn; rw [isDone_z] at hd; omega
  · rw [outV_fst_open hd]
    cases s with
    | root =>
      have e : (uval d .root).2 ++ tcands k d .root = ans k d (.c k) := by
        simp [uval, tcands, dep, ans_of_not (s := .w) (k := k) (d := d) (by simp)]
      rw [e, ne_eq, ans_eq_nil, not_not, hasAns_c, hasAns_root]
      omega
    | c j =>
      simp only [Slot.inAt] at hs
      rw [hasAns_c] at hn ⊢
      cases j with
      | zero =>
        have h1 : 0 + 1 ≤ d := by omega
        have e : (uval d (.c 0)).2 = [zz] := by simp only [uval, h1, ↓reduceIte]
        rw [e]
        constructor
        · intro; omega
        · intro; simp
      | succ j =>
        by_cases h' : j + 2 ≤ d
        · have e : (uval d (.c (j + 1))).2 = [zz] := by simp [uval, h']
          rw [e]
          constructor
          · intro; omega
          · intro; simp
        · have e : (uval d (.c (j + 1))).2 = [] := by simp [uval, h']
          have e' : tcands k d (.c (j + 1)) = [] := by
            simp only [tcands, dep, List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact ans_of_not (by rw [hasAns_c]; omega)
          rw [e, e']
          constructor
          · intro h; exact absurd rfl h
          · intro; omega
    | w =>
      have e : (uval d .w).2 ++ tcands k d .w = [] := by
        simp [uval, tcands, dep, ans_of_not (s := .w) (k := k) (d := d) (by simp)]
      rw [e]; simp
    | z =>
      simp only [Slot.inAt] at hs
      rw [hasAns_z]
      constructor
      · intro; omega
      · intro; simp [uval]

theorem hasAns_mono (k d : Nat) (s : Slot) (h : hasAns k d s = true) : hasAns k (d + 1) s = true := by
  cases s with
  | root => rw [hasAns_root] at h ⊢; omega
  | c j => rw [hasAns_c] at h ⊢; omega
  | w => simp at h
  | z => rw [hasAns_z] at h ⊢; omega

/-- A table gains `z -> z` in the round where it first has a candidate. -/
theorem ans_step (k d : Nat) (s : Slot) (hs : s.inAt k d) :
    ans k d s ++ (if ans k d s = [] ∧ (outV k d s).1 ≠ [] then [zz] else []) = ans k (d + 1) s := by
  by_cases hn : hasAns k d s = true
  · rw [ans_of_has hn, ans_of_has (hasAns_mono k d s hn)]
    simp
  · have hc := cands_ne k d s hs hn
    rw [ans_of_not hn]
    by_cases h1 : hasAns k (d + 1) s = true
    · rw [ans_of_has h1]; simp [hc.2 h1]
    · have : ¬ (outV k d s).1 ≠ [] := fun h => h1 (hc.1 h)
      rw [ans_of_not h1]; simp [this]

theorem ts1_costs (k d : Nat) :
    Costs (mapL (fun p : Table × (List Span × List Goal) => do
        let f ← Tabled.fresh p.1.answers p.2.1
        pure { p.1 with answers := p.1.answers ++ f })
        ((tabs k d).zip ((slots k d).map (outV k d))))
      ((slots k d).map (tab1 k d)) ((slots k d).length * 96) := by
  conv => arg 1; arg 2; rw [tabs, List.zip_map']
  refine Costs.mapL_map fun s hs => ?_
  have hl := cands_length k d s
  have hf := fresh_zz (ans_cases k d s) (cands_zz k d s)
  refine Costs.congr_val (Costs.mono (c' := 96) (Costs.bind hf (Costs.pure _)) ?_) ?_
  · have h1 : (outV k d s).1.length * (outV k d s).1.length ≤ 9 :=
      Nat.mul_le_mul hl hl
    have h2 : (outV k d s).1.length * ((outV k d s).1.length * 8) =
        (outV k d s).1.length * (outV k d s).1.length * 8 := by ring
    omega
  · simp only [tab, tab1]
    rw [ans_step k d s (mem_slots.1 hs)]

end Sep

end R002

end RwLog
