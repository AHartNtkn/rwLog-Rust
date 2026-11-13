/-
# The spans of the normal form are first-order

The normal form of an expression has the spans of the expression or their
converses, and the nodes the kernel reads off a node (its members, a stretch
of a chain, a meet without a member) have spans of that node. So every node
an engine reaches from a well-formed program and query has first-order spans
(`RelOf.FO`), which is where a constraint domain must return a representative
(`Domain.Lawful.rep_none`).
-/
import RwLog.Kernel.NormalFormStable
import RwLog.SpanLayer.Sorts
import RwLog.Trusted.Charged

namespace RwLog

/-- Every span of the expression is first-order. -/
def RelOf.FO (e : Rel) : Prop := ∀ s ∈ e.spans, s.firstOrder = true

theorem spans_seqParts : ∀ (e : Rel) (s : Span), s ∈ e.spans ↔ ∃ x ∈ seqParts e, s ∈ x.spans
  | .seq a b, s => by
    simp only [RelOf.spans, seqParts, List.mem_append, spans_seqParts a, spans_seqParts b]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | .zero, s | .span _, s | .or _ _, s | .and _ _, s | .conv _, s | .call _, s => by
    simp [seqParts]

theorem spans_andParts : ∀ (e : Rel) (s : Span), s ∈ e.spans ↔ ∃ x ∈ andParts e, s ∈ x.spans
  | .and a b, s => by
    simp only [RelOf.spans, andParts, List.mem_append, spans_andParts a, spans_andParts b]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | .zero, s | .span _, s | .or _ _, s | .seq _ _, s | .conv _, s | .call _, s => by
    simp [andParts]

theorem spans_orBranches : ∀ (e : Rel) (s : Span), s ∈ e.spans ↔ ∃ x ∈ orBranches e, s ∈ x.spans
  | .or a b, s => by
    simp only [RelOf.spans, orBranches, List.mem_append, spans_orBranches a, spans_orBranches b]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | .zero, s | .span _, s | .and _ _, s | .seq _ _, s | .conv _, s | .call _, s => by
    simp [orBranches]

theorem spans_mkSeq : ∀ (L : List Rel) (s : Span), s ∈ (mkSeq L).spans ↔ ∃ x ∈ L, s ∈ x.spans
  | [], s => by simp [mkSeq, RelOf.spans]
  | [e], s => by simp [mkSeq]
  | e :: e' :: es, s => by
    rw [show mkSeq (e :: e' :: es) = .seq e (mkSeq (e' :: es)) from rfl]
    simp only [RelOf.spans, List.mem_append, spans_mkSeq (e' :: es), List.mem_cons,
      exists_eq_or_imp]

theorem spans_mkAnd : ∀ (L : List Rel) (s : Span), s ∈ (mkAnd L).spans ↔ ∃ x ∈ L, s ∈ x.spans
  | [], s => by simp [mkAnd, RelOf.spans]
  | [e], s => by simp [mkAnd]
  | e :: e' :: es, s => by
    rw [show mkAnd (e :: e' :: es) = .and e (mkAnd (e' :: es)) from rfl]
    simp only [RelOf.spans, List.mem_append, spans_mkAnd (e' :: es), List.mem_cons,
      exists_eq_or_imp]

theorem spans_mkOr : ∀ (L : List Rel) (s : Span), s ∈ (mkOr L).spans ↔ ∃ x ∈ L, s ∈ x.spans
  | [], s => by simp [mkOr, RelOf.spans]
  | [e], s => by simp [mkOr]
  | e :: e' :: es, s => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl]
    simp only [RelOf.spans, List.mem_append, spans_mkOr (e' :: es), List.mem_cons,
      exists_eq_or_imp]

/-- A span of the normal form is a span of the expression or the converse of
one. -/
theorem spans_normB : ∀ (b : Bool) (e : Rel) (s : Span), s ∈ (normB b e).spans →
    ∃ s' ∈ e.spans, s = s' ∨ s = s'.swap
  | b, .zero, s, h => by cases b <;> simp [normB, RelOf.spans] at h
  | false, .span t, s, h => by
    simp only [normB, RelOf.spans, List.mem_singleton] at h
    exact ⟨t, by simp [RelOf.spans], .inl h⟩
  | true, .span t, s, h => by
    simp only [normB, RelOf.spans, List.mem_singleton] at h
    exact ⟨t, by simp [RelOf.spans], .inr h⟩
  | b, .or x y, s, h => by
    rw [normB, spans_mkOr] at h
    obtain ⟨z, hz, hs⟩ := h
    rcases List.mem_append.1 (mem_sortedBranches.1 hz).1 with hz | hz
    · obtain ⟨s', h', e⟩ := spans_normB b x s ((spans_orBranches _ s).2 ⟨z, hz, hs⟩)
      exact ⟨s', by simp [RelOf.spans, h'], e⟩
    · obtain ⟨s', h', e⟩ := spans_normB b y s ((spans_orBranches _ s).2 ⟨z, hz, hs⟩)
      exact ⟨s', by simp [RelOf.spans, h'], e⟩
  | b, .and x y, s, h => by
    rw [normB, spans_mkAnd] at h
    obtain ⟨z, hz, hs⟩ := h
    rcases List.mem_append.1 ((sortedParts_perm _).mem_iff.1 hz) with hz | hz
    · obtain ⟨s', h', e⟩ := spans_normB b x s ((spans_andParts _ s).2 ⟨z, hz, hs⟩)
      exact ⟨s', by simp [RelOf.spans, h'], e⟩
    · obtain ⟨s', h', e⟩ := spans_normB b y s ((spans_andParts _ s).2 ⟨z, hz, hs⟩)
      exact ⟨s', by simp [RelOf.spans, h'], e⟩
  | false, .seq x y, s, h => by
    rw [normB, spans_mkSeq] at h
    obtain ⟨z, hz, hs⟩ := h
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨s', h', e⟩ := spans_normB false x s ((spans_seqParts _ s).2 ⟨z, hz, hs⟩)
      exact ⟨s', by simp [RelOf.spans, h'], e⟩
    · obtain ⟨s', h', e⟩ := spans_normB false y s ((spans_seqParts _ s).2 ⟨z, hz, hs⟩)
      exact ⟨s', by simp [RelOf.spans, h'], e⟩
  | true, .seq x y, s, h => by
    rw [normB, spans_mkSeq] at h
    obtain ⟨z, hz, hs⟩ := h
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨s', h', e⟩ := spans_normB true y s ((spans_seqParts _ s).2 ⟨z, hz, hs⟩)
      exact ⟨s', by simp [RelOf.spans, h'], e⟩
    · obtain ⟨s', h', e⟩ := spans_normB true x s ((spans_seqParts _ s).2 ⟨z, hz, hs⟩)
      exact ⟨s', by simp [RelOf.spans, h'], e⟩
  | b, .conv x, s, h => by
    rw [normB] at h
    obtain ⟨s', h', e⟩ := spans_normB (!b) x s h
    exact ⟨s', by simpa [RelOf.spans] using h', e⟩
  | false, .call n, s, h => by simp [normB, RelOf.spans] at h
  | true, .call n, s, h => by simp [normB, RelOf.spans] at h

namespace RelOf.FO

theorem normB {e : Rel} (h : e.FO) (b : Bool) : (normB b e).FO := fun s hs => by
  obtain ⟨s', h', rfl | rfl⟩ := spans_normB b e s hs
  · exact h _ h'
  · rw [Span.firstOrder_swap]; exact h s' h'

theorem norm {e : Rel} (h : e.FO) : e.norm.FO := h.normB false

theorem normConv {e : Rel} (h : e.FO) : e.normConv.FO := h.normB true

theorem of_mem_seqParts {e x : Rel} (h : e.FO) (hx : x ∈ seqParts e) : x.FO :=
  fun s hs => h s ((spans_seqParts e s).2 ⟨x, hx, hs⟩)

theorem of_mem_andParts {e x : Rel} (h : e.FO) (hx : x ∈ andParts e) : x.FO :=
  fun s hs => h s ((spans_andParts e s).2 ⟨x, hx, hs⟩)

theorem of_mem_orBranches {e x : Rel} (h : e.FO) (hx : x ∈ orBranches e) : x.FO :=
  fun s hs => h s ((spans_orBranches e s).2 ⟨x, hx, hs⟩)

/-- The members `view` lists of a node have its spans. -/
theorem view_members {e x : Rel} (h : e.FO) (hx : x ∈ e.view.members) : x.FO := by
  cases e with
  | zero => simp [RelOf.view, NodeView.members] at hx
  | span s => simp [RelOf.view, NodeView.members] at hx
  | call n => simp [RelOf.view, NodeView.members] at hx
  | conv a => cases a <;> simp [RelOf.view, NodeView.members] at hx
  | seq a b => exact h.of_mem_seqParts hx
  | and a b => exact h.of_mem_andParts hx
  | or a b => exact h.of_mem_orBranches hx

theorem interval {e m : Rel} {i j : Nat} (h : e.FO) (hm : e.interval i j = some m) : m.FO := by
  unfold RelOf.interval at hm
  split at hm
  · cases hm
    intro s hs
    obtain ⟨x, hx, hs⟩ := (spans_mkSeq _ s).1 hs
    exact h.of_mem_seqParts (List.mem_of_mem_take (List.mem_of_mem_drop hx)) s hs
  · cases hm

theorem without {e m : Rel} {i : Nat} (h : e.FO) (hm : e.without i = some m) : m.FO := by
  unfold RelOf.without at hm
  split at hm
  · cases hm
    intro s hs
    obtain ⟨x, hx, hs⟩ := (spans_mkAnd _ s).1 hs
    exact h.of_mem_andParts (List.mem_of_mem_eraseIdx hx) s hs
  · cases hm

end RelOf.FO

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] : ∀ (l : List (α × β)) (n : α) (e : β),
    l.lookup n = some e → (n, e) ∈ l
  | [], _, _, h => by simp at h
  | (a, b) :: l, n, e, h => by
    rw [List.lookup_cons] at h
    by_cases hn : n == a
    · simp only [hn] at h; cases h; rw [eq_of_beq hn]; exact List.mem_cons_self
    · simp only [hn] at h; exact List.mem_cons_of_mem _ (mem_of_lookup l n e h)

/-- The bodies of a program with first-order spans have first-order spans. -/
theorem ProgramOf.body_fo {P : Program}
    (h : ∀ s ∈ P.defs.flatMap fun d => d.2.spans, s.firstOrder = true) (n : Name) :
    (P.body n).FO := by
  intro s hs
  unfold ProgramOf.body at hs
  cases hl : P.defs.lookup n with
  | none => rw [hl] at hs; simp [RelOf.spans] at hs
  | some e =>
    rw [hl] at hs
    refine h s (List.mem_flatMap.2 ⟨(n, e), ?_, hs⟩)
    exact mem_of_lookup _ _ _ hl

/-- The node of the body of a call node has first-order spans. -/
theorem bodyOf_fo {P : Program}
    (h : ∀ s ∈ P.defs.flatMap fun d => d.2.spans, s.firstOrder = true) {e b : Rel}
    (hb : Charged.bodyOf P e = some b) : b.FO := by
  unfold Charged.bodyOf at hb
  split at hb
  · cases hb; exact (P.body_fo h _).norm
  · cases hb; exact (P.body_fo h _).normConv
  · cases hb

end RwLog
