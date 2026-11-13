/-
# The separating family: names, bodies, table keys

Facts about `sepFam k` that mention no machine: the chain names are distinct
and sort before `w`, what each name's body is, the family is well formed, and
each goal the run meets is its own table key.
-/
import RwLog.Rungs.R002.Spec

namespace RwLog

namespace R002

namespace Sep

/-! ## Names -/

theorem chainName_inj {i j : Nat} (h : chainName i = chainName j) : i = j := by
  have h1 : toString i = toString j := (String.append_right_inj "c").1 h
  rw [Nat.toString_eq_ofList_toDigits, Nat.toString_eq_ofList_toDigits] at h1
  have h2 : Nat.toDigits 10 i = Nat.toDigits 10 j := String.ofList_injective h1
  have := congrArg (fun l => Nat.ofDigitChars 10 l 0) h2
  simpa [Nat.ofDigitChars_ten_toDigits] using this

theorem chainName_toList (i : Nat) : (chainName i).toList = 'c' :: (toString i).toList := by
  simp [chainName, String.toList_append]

theorem chainName_ne_w (i : Nat) : chainName i ≠ "w" := by
  intro h
  have := congrArg String.toList h
  rw [chainName_toList] at this
  simp at this

theorem chainName_lt_w (i : Nat) : compare (chainName i) "w" = .lt := by
  have : chainName i < "w" := by
    rw [String.lt_iff, chainName_toList]
    exact List.Lex.rel (by decide)
  show compareOfLessAndEq _ _ = _
  simp [compareOfLessAndEq, this]

/-! ## The program -/

/-- The family's program. -/
abbrev prog (k : Nat) : Program := ⟨sepDefs k, []⟩

/-- `z -> z`, the one answer. -/
abbrev zz : Span := ⟨.sym "z", .sym "z", []⟩

theorem body_w (k : Nat) : (prog k).body "w" = .or (.call "w") (.call "w") := by
  simp [ProgramOf.body, sepDefs]

theorem lookup_chain (i : Nat) : ∀ l : List Nat, i ∈ l →
    (l.map fun i => (chainName (i + 1), (RelOf.call (chainName i) : Rel))).lookup (chainName (i + 1)) =
      some (.call (chainName i))
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : a = i
    · subst ha; simp
    · have hne : (chainName (i + 1) == chainName (a + 1)) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h'; exact ha (by have := chainName_inj h'; omega)
      have hi : i ∈ l := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm ha
        · exact h
      simp only [List.map_cons, List.lookup, hne]
      exact lookup_chain i l hi

theorem body_zero (k : Nat) : (prog k).body (chainName 0) = .span zz := by
  have : (chainName 0 == "w") = false := by simpa using chainName_ne_w 0
  simp [ProgramOf.body, sepDefs, List.lookup, this, RelOf.at_, RelOf.rw]

theorem body_succ {k i : Nat} (h : i < k) :
    (prog k).body (chainName (i + 1)) = .call (chainName i) := by
  have h1 : (chainName (i + 1) == "w") = false := by simpa using chainName_ne_w (i + 1)
  have h2 : (chainName (i + 1) == chainName 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h'; have := chainName_inj h'; omega
  have h3 := lookup_chain i (List.range k) (List.mem_range.2 h)
  simp only [ProgramOf.body, sepDefs, List.cons_append, List.nil_append, List.lookup, h1, h2, h3]
  rfl

theorem wellFormed (k : Nat) : (sepFam k).1.WellFormed (sepFam k).2 := by
  have hmem : ∀ i, i ≤ k → chainName i ∈ (sepDefs k).map Prod.fst := by
    intro i hi
    cases i with
    | zero => simp [sepDefs]
    | succ i =>
      simp only [sepDefs, List.cons_append, List.nil_append, List.map_cons, List.map_map,
        List.mem_cons, List.mem_map, List.mem_range, Function.comp]
      exact Or.inr (Or.inr ⟨i, by omega, rfl⟩)
  refine ⟨?_, ?_, by simp [sepFam]⟩
  · simp only [sepFam, sepDefs, List.cons_append, List.nil_append, List.map_cons, List.map_map,
      List.nodup_cons, List.mem_cons, List.mem_map, List.mem_range, Function.comp, not_or,
      not_exists, not_and]
    refine ⟨⟨fun h => chainName_ne_w 0 h.symm, fun i _ h => chainName_ne_w _ h⟩,
      fun i _ h => by have := chainName_inj h; omega, ?_⟩
    refine (List.nodup_range).map_on ?_
    intro a _ b _ h
    have := chainName_inj h; omega
  · intro n hn
    simp only [sepFam, List.mem_append, List.mem_flatMap] at hn
    rcases hn with hn | ⟨d, hd, hn⟩
    · simp only [RelOf.calls, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl
      · exact hmem k le_rfl
      · simp [sepFam, sepDefs]
    · simp only [sepDefs, List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
        List.mem_range] at hd
      rcases hd with rfl | rfl | ⟨i, hi, rfl⟩
      · simp only [RelOf.calls, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false, or_self] at hn
        subst hn; simp [sepFam, sepDefs]
      · simp [RelOf.calls, RelOf.at_, RelOf.rw] at hn
      · simp only [RelOf.calls, List.mem_cons, List.not_mem_nil, or_false] at hn
        subst hn; exact hmem i (by omega)

/-! ## Goals and their table keys -/

open R001

/-- The goals of the run: the query, a link of the chain, `w`, and `@z`. -/
abbrev gR (k : Nat) : Goal := ⟨none, .or (.call (chainName k)) (.call "w"), none⟩
abbrev gC (j : Nat) : Goal := ⟨none, .call (chainName j), none⟩
abbrev gW : Goal := ⟨none, .call "w", none⟩
abbrev gZ : Goal := ⟨none, .span zz, none⟩

theorem norm_gC (j : Nat) : (gC j).norm = (false, gC j) := by
  simp [GoalOf.norm, canon, GoalOf.stripConv]

theorem norm_gW : gW.norm = (false, gW) := by
  simp [GoalOf.norm, canon, GoalOf.stripConv]

theorem norm_gZ : gZ.norm = (false, gZ) := by
  simp [GoalOf.norm, canon, GoalOf.stripConv]

theorem canon_root (k : Nat) :
    canon (.or (.call (chainName k)) (.call "w")) = .or (.call (chainName k)) (.call "w") := by
  have h1 : (RelOf.call (chainName k) : Rel) ≠ RelOf.call "w" := by
    simpa using chainName_ne_w k
  have h2 : ((RelOf.call "w" : Rel) == RelOf.call (chainName k)) = false := by
    simpa using fun h => chainName_ne_w k h.symm
  simp [canon, orBranches, sortedBranches, relCmp, chainName_lt_w, List.eraseDups_cons,
    h2, mkOr]

theorem norm_gR (k : Nat) : (gR k).norm = (false, gR k) := by
  simp [GoalOf.norm, canon_root, GoalOf.stripConv]

/-- The body of `w` has the key of `w`. -/
theorem norm_wBody : (⟨none, .or (.call "w") (.call "w"), none⟩ : Goal).norm = (false, gW) := by
  simp [GoalOf.norm, canon, orBranches, sortedBranches, relCmp, List.eraseDups_cons, mkOr,
    GoalOf.stripConv]

end Sep

end R002

end RwLog
