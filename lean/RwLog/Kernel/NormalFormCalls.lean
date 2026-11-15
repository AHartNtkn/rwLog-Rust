/-
# The calls of the normal form are calls of the expression

The normal form of an expression calls only names the expression calls
(`calls_normB`). So the normal form of a well-formed input is well formed,
with the program in normal form (`ProgramOf.WellFormed.normed`).
-/
import RwLog.Kernel.NormalFormSpans
import RwLog.Trusted.Cost

namespace RwLog

theorem calls_seqParts : ∀ (e : Rel) (n : Name), n ∈ e.calls ↔ ∃ x ∈ seqParts e, n ∈ x.calls
  | .seq a b, n => by
    simp only [RelOf.calls, seqParts, List.mem_append, calls_seqParts a, calls_seqParts b]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | .zero, s | .span _, s | .or _ _, s | .and _ _, s | .conv _, s | .call _, n => by
    simp [seqParts]

theorem calls_andParts : ∀ (e : Rel) (n : Name), n ∈ e.calls ↔ ∃ x ∈ andParts e, n ∈ x.calls
  | .and a b, n => by
    simp only [RelOf.calls, andParts, List.mem_append, calls_andParts a, calls_andParts b]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | .zero, s | .span _, s | .or _ _, s | .seq _ _, s | .conv _, s | .call _, n => by
    simp [andParts]

theorem calls_orBranches : ∀ (e : Rel) (n : Name), n ∈ e.calls ↔ ∃ x ∈ orBranches e, n ∈ x.calls
  | .or a b, n => by
    simp only [RelOf.calls, orBranches, List.mem_append, calls_orBranches a, calls_orBranches b]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | .zero, s | .span _, s | .and _ _, s | .seq _ _, s | .conv _, s | .call _, n => by
    simp [orBranches]

theorem calls_mkSeq : ∀ (L : List Rel) (n : Name), n ∈ (mkSeq L).calls ↔ ∃ x ∈ L, n ∈ x.calls
  | [], n => by simp [mkSeq, RelOf.calls]
  | [e], n => by simp [mkSeq]
  | e :: e' :: es, n => by
    rw [show mkSeq (e :: e' :: es) = .seq e (mkSeq (e' :: es)) from rfl]
    simp only [RelOf.calls, List.mem_append, calls_mkSeq (e' :: es), List.mem_cons,
      exists_eq_or_imp]

theorem calls_mkAnd : ∀ (L : List Rel) (n : Name), n ∈ (mkAnd L).calls ↔ ∃ x ∈ L, n ∈ x.calls
  | [], n => by simp [mkAnd, RelOf.calls]
  | [e], n => by simp [mkAnd]
  | e :: e' :: es, n => by
    rw [show mkAnd (e :: e' :: es) = .and e (mkAnd (e' :: es)) from rfl]
    simp only [RelOf.calls, List.mem_append, calls_mkAnd (e' :: es), List.mem_cons,
      exists_eq_or_imp]

theorem calls_mkOr : ∀ (L : List Rel) (n : Name), n ∈ (mkOr L).calls ↔ ∃ x ∈ L, n ∈ x.calls
  | [], n => by simp [mkOr, RelOf.calls]
  | [e], n => by simp [mkOr]
  | e :: e' :: es, n => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl]
    simp only [RelOf.calls, List.mem_append, calls_mkOr (e' :: es), List.mem_cons,
      exists_eq_or_imp]

/-- A name the normal form calls is called by the expression. -/
theorem calls_normB : ∀ (b : Bool) (e : Rel) (n : Name), n ∈ (normB b e).calls → n ∈ e.calls
  | b, .zero, n, h => by cases b <;> simp [normB, RelOf.calls] at h
  | false, .span t, n, h => by simp [normB, RelOf.calls] at h
  | true, .span t, n, h => by simp [normB, RelOf.calls] at h
  | b, .or x y, n, h => by
    rw [normB, calls_mkOr] at h
    obtain ⟨z, hz, hs⟩ := h
    rcases List.mem_append.1 (mem_sortedBranches.1 hz).1 with hz | hz
    · have := calls_normB b x n ((calls_orBranches _ n).2 ⟨z, hz, hs⟩)
      simp [RelOf.calls, this]
    · have := calls_normB b y n ((calls_orBranches _ n).2 ⟨z, hz, hs⟩)
      simp [RelOf.calls, this]
  | b, .and x y, n, h => by
    rw [normB, calls_mkAnd] at h
    obtain ⟨z, hz, hs⟩ := h
    rcases List.mem_append.1 ((sortedParts_perm _).mem_iff.1 hz) with hz | hz
    · have := calls_normB b x n ((calls_andParts _ n).2 ⟨z, hz, hs⟩)
      simp [RelOf.calls, this]
    · have := calls_normB b y n ((calls_andParts _ n).2 ⟨z, hz, hs⟩)
      simp [RelOf.calls, this]
  | false, .seq x y, n, h => by
    rw [normB, calls_mkSeq] at h
    obtain ⟨z, hz, hs⟩ := h
    rcases List.mem_append.1 hz with hz | hz
    · have := calls_normB false x n ((calls_seqParts _ n).2 ⟨z, hz, hs⟩)
      simp [RelOf.calls, this]
    · have := calls_normB false y n ((calls_seqParts _ n).2 ⟨z, hz, hs⟩)
      simp [RelOf.calls, this]
  | true, .seq x y, n, h => by
    rw [normB, calls_mkSeq] at h
    obtain ⟨z, hz, hs⟩ := h
    rcases List.mem_append.1 hz with hz | hz
    · have := calls_normB true y n ((calls_seqParts _ n).2 ⟨z, hz, hs⟩)
      simp [RelOf.calls, this]
    · have := calls_normB true x n ((calls_seqParts _ n).2 ⟨z, hz, hs⟩)
      simp [RelOf.calls, this]
  | b, .conv x, n, h => by
    rw [normB] at h
    simpa [RelOf.calls] using calls_normB (!b) x n h
  | false, .call m, n, h => by simpa [normB, RelOf.calls] using h
  | true, .call m, n, h => by simpa [normB, RelOf.calls] using h

theorem calls_norm {e : Rel} {n : Name} (h : n ∈ e.norm.calls) : n ∈ e.calls :=
  calls_normB false e n h

theorem calls_normConv {e : Rel} {n : Name} (h : n ∈ e.normConv.calls) : n ∈ e.calls :=
  calls_normB true e n h

/-- A first-order query that calls no more than a well-formed one is well
formed. -/
theorem ProgramOf.WellFormed.of_calls_fo {P : Program} {q q' : Rel} (h : P.WellFormed q)
    (hc : ∀ n ∈ q'.calls, n ∈ q.calls) (hf : q'.FO) : P.WellFormed q' := by
  refine ⟨h.1, fun n hn => h.2.1 n ?_, h.2.2.1, fun s hs' => ?_⟩
  · rcases List.mem_append.1 hn with hn | hn
    · exact List.mem_append_left _ (hc n hn)
    · exact List.mem_append_right _ hn
  · rcases List.mem_append.1 hs' with hs' | hs'
    · exact hf s hs'
    · exact h.2.2.2 s (List.mem_append_right _ hs')

/-- **The normal form of a well-formed input is well formed**, with the
program in normal form. -/
theorem ProgramOf.WellFormed.normed {P : Program} {q : Rel} (h : P.WellFormed q) :
    P.normed.WellFormed q.norm := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hfst : P.normed.defs.map Prod.fst = P.defs.map Prod.fst := by
    simp only [ProgramOf.normed, List.map_map]
    exact List.map_congr_left fun d _ => rfl
  refine ⟨by rw [hfst]; exact h1, fun n hn => ?_, h3, fun s hs => ?_⟩
  · rw [hfst]
    refine h2 n ?_
    rcases List.mem_append.1 hn with hn | hn
    · exact List.mem_append_left _ (calls_norm hn)
    · refine List.mem_append_right _ ?_
      obtain ⟨d, hd, hnd⟩ := List.mem_flatMap.1 hn
      simp only [ProgramOf.normed, List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      exact List.mem_flatMap.2 ⟨d0, hd0, calls_norm hnd⟩
  · rcases List.mem_append.1 hs with hs | hs
    · exact RelOf.FO.norm (fun s' hs' => h4 s' (List.mem_append_left _ hs')) s hs
    · obtain ⟨d, hd, hsd⟩ := List.mem_flatMap.1 hs
      simp only [ProgramOf.normed, List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      exact RelOf.FO.norm (fun s' hs' => h4 s'
        (List.mem_append_right _ (List.mem_flatMap.2 ⟨d0, hd0, hs'⟩))) s hsd

end RwLog
