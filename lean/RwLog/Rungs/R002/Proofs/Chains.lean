/-
# Why pruning loses nothing

The on-demand walk drops a product when its first span does not compose with
the chain on its left or its last span does not compose with the chain on its
right. This file proves the facts about products that make that exact:

* a chain of spans composes exactly when the composition of the ground
  relations of its spans is not empty (`Span.chain_isSome_iff`), so being alive is a
  statement about ground relations (`AL`, `AR`, `keep_iff`);
* how the first and the last span of a joined product come from the two
  products joined (`joinSeq_head`, `joinSeq_last`, `joinSeq_junction`);
* the pruning step of a sequence: filtering the products of the first factor
  against the chain `R'` read off the second factor, then the products of the
  second factor against the chain left by the first, and testing the joined
  product on the right, leaves exactly the joined products that are alive
  between the chains of the sequence (`seq_filter`).
-/
import RwLog.Rungs.R002.Proofs.Eager
import RwLog.Kernel.Chain
import RwLog.Rungs.R000.Products

namespace RwLog

namespace R002

open Cost

/-! ## Chains as ground relations -/

theorem chain_concat (xs : List Span) (s : Span) :
    GRel.chain ((xs ++ [s]).map Span.den) = (GRel.chain (xs.map Span.den)).comp s.den := by
  rw [List.map_append, GRel.chain_append, List.map_cons, List.map_nil, GRel.chain_cons,
    GRel.chain_nil, GRel.comp_id]

theorem comp_nonempty_of_compose {a b c : Span} (h : a.compose b = some c) :
    (a.den.comp b.den).Nonempty := compose_some h ▸ c.den_nonempty

/-! ## Being alive -/

/-- The first span of the product, if it has one, composes with the chain. -/
def AL (L : List Span) (p : List Rel) : Prop :=
  L ≠ [] → ∀ s, headSpan p = some s → ((GRel.chain (L.map Span.den)).comp s.den).Nonempty

/-- The last span of the product, if it has one, composes with the chain. -/
def AR (p : List Rel) (R : List Span) : Prop :=
  R ≠ [] → ∀ s, lastSpan p = some s → (s.den.comp (GRel.chain (R.map Span.den))).Nonempty

theorem aliveL_iff (L : List Span) (p : List Rel) : (aliveL L p).val = true ↔ AL L p := by
  unfold aliveL AL
  cases L with
  | nil => simp
  | cons x L =>
    cases h : headSpan p with
    | none => simp
    | some s =>
      simp only [Charged.composable, Span.chain_isSome_iff, chain_concat]
      constructor
      · intro hn _ t ht
        cases ht
        exact hn
      · intro hn
        exact hn (List.cons_ne_nil _ _) s rfl

theorem aliveR_iff (p : List Rel) (R : List Span) : (aliveR p R).val = true ↔ AR p R := by
  unfold aliveR AR
  cases R with
  | nil => simp
  | cons x R =>
    cases h : lastSpan p with
    | none => simp
    | some s =>
      simp only [Charged.composable, Span.chain_isSome_iff]
      rw [List.map_cons, GRel.chain_cons]
      constructor
      · intro hn _ t ht
        cases ht
        exact hn
      · intro hn
        exact hn (List.cons_ne_nil _ _) s rfl

/-- The walk's test, with the ticks forgotten. -/
def keep (L R : List Span) (p : List Rel) : Bool := (alive L p R).val

theorem keep_eq (L R : List Span) (p : List Rel) :
    keep L R p = ((aliveL L p).val && (aliveR p R).val) := by
  unfold keep alive
  simp only [bind_val]
  cases (aliveL L p).val <;> rfl

theorem keep_iff {L R : List Span} {p : List Rel} : keep L R p = true ↔ AL L p ∧ AR p R := by
  rw [keep_eq, Bool.and_eq_true, aliveL_iff, aliveR_iff]

theorem keep_nil (p : List Rel) : keep [] [] p = true :=
  keep_iff.mpr ⟨fun h => (h rfl).elim, fun h => (h rfl).elim⟩

theorem filter_keep_nil (xs : List (List Rel)) : xs.filter (keep [] []) = xs :=
  List.filter_eq_self.mpr fun p _ => keep_nil p

/-! ## The ends of a joined product -/

theorem headSpan_cons (x : Rel) (l l' : List Rel) : headSpan (x :: l) = headSpan (x :: l') := by
  cases x <;> rfl

theorem headSpan_eq_some {q : List Rel} {s : Span} (h : headSpan q = some s) :
    ∃ q', q = .span s :: q' := by
  unfold headSpan at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

theorem lastSpan_eq_some {p : List Rel} {s : Span} (h : lastSpan p = some s) :
    p.getLast? = some (.span s) := by
  unfold lastSpan at h
  split at h
  · rename_i h'
    cases h
    exact h'
  · cases h

theorem lastSpan_of_getLast? {p : List Rel} {a : Span} (h : p.getLast? = some (.span a)) :
    lastSpan p = some a := by
  unfold lastSpan
  rw [h]

theorem lastSpan_append {p q : List Rel} (hq : q ≠ []) : lastSpan (p ++ q) = lastSpan q := by
  unfold lastSpan
  rw [List.getLast?_append]
  cases h : q.getLast? with
  | none => exact (hq (List.getLast?_eq_none_iff.mp h)).elim
  | some x => rfl

theorem joinSeq_fused {p : List Rel} {a : Span} (h : p.getLast? = some (.span a)) (b : Span)
    (q' : List Rel) :
    R000.joinSeq p (.span b :: q') = (a.compose b).map fun c => p.dropLast ++ .span c :: q' := by
  unfold R000.joinSeq
  rw [h]

/-- The first span of a joined product is the first span of its first part,
unless the first part is a single span that was fused. -/
theorem joinSeq_head {p q r : List Rel} (h : R000.joinSeq p q = some r) (hp : p ≠ []) :
    (∃ a b q' c, p = [.span a] ∧ q = .span b :: q' ∧ a.compose b = some c ∧
      r = .span c :: q') ∨ headSpan r = headSpan p := by
  rcases R000.joinSeq_cases h with ⟨a, b, q', c, hl, rfl, hc, rfl⟩ | rfl
  · match p, hp, hl with
    | [x], _, hl =>
      have hx : x = .span a := by simpa using hl
      subst hx
      exact .inl ⟨a, b, q', c, rfl, rfl, hc, rfl⟩
    | x :: y :: p', _, _ => exact .inr (headSpan_cons x _ _)
  · match p, hp with
    | x :: p', _ => exact .inr (headSpan_cons x _ _)

/-- The last span of a joined product is the last span of its second part,
unless the second part is a single span that was fused. -/
theorem joinSeq_last {p q r : List Rel} (h : R000.joinSeq p q = some r) (hq : q ≠ []) :
    (∃ a b c, lastSpan p = some a ∧ q = [.span b] ∧ a.compose b = some c ∧
      lastSpan r = some c) ∨ lastSpan r = lastSpan q := by
  rcases R000.joinSeq_cases h with ⟨a, b, q', c, hl, rfl, hc, rfl⟩ | rfl
  · cases q' with
    | nil =>
      exact .inl ⟨a, b, c, lastSpan_of_getLast? hl, rfl, hc, lastSpan_of_getLast? (by simp)⟩
    | cons y q'' =>
      right
      rw [lastSpan_append (List.cons_ne_nil _ _)]
      exact (lastSpan_append (p := [Rel.span c]) (List.cons_ne_nil y q'')).trans
        (lastSpan_append (p := [Rel.span b]) (List.cons_ne_nil y q'')).symm
  · exact .inr (lastSpan_append hq)

/-- Two spans that meet are fused. -/
theorem joinSeq_junction {p q r : List Rel} {a b : Span} (h : R000.joinSeq p q = some r)
    (ha : lastSpan p = some a) (hb : headSpan q = some b) :
    ∃ c q', a.compose b = some c ∧ q = .span b :: q' ∧ r = p.dropLast ++ .span c :: q' := by
  obtain ⟨q', rfl⟩ := headSpan_eq_some hb
  rw [joinSeq_fused (lastSpan_eq_some ha)] at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨c, q', hc, rfl, rfl⟩

theorem leftAfter_other {L : List Span} {p : List Rel} (h : ∀ a, p ≠ [.span a]) :
    leftAfter L p = (lastSpan p).toList := by
  unfold leftAfter
  split
  · exact (h _ rfl).elim
  · rfl

/-! ## The pruning step of a sequence -/

/-- A joined product alive on the left: its second part was alive after its
first. -/
theorem AL_join {L : List Span} {p q r : List Rel} (h : R000.joinSeq p q = some r) (hp : p ≠ [])
    (hLp : AL L p) (hq : AL (leftAfter L p) q) : AL L r := by
  intro hL s hs
  rcases joinSeq_head h hp with ⟨a, b, q', c, rfl, rfl, hc, rfl⟩ | hh
  · obtain rfl : c = s := by simpa [headSpan] using hs
    have := hq (by simp [leftAfter]) b rfl
    rw [show leftAfter L [.span a] = L ++ [a] from rfl, chain_concat, GRel.comp_assoc,
      ← compose_some hc] at this
    exact this
  · exact hLp hL s (hh ▸ hs)

/-- If a joined product is alive, its second part was alive after its
first. -/
theorem alive_second {L R : List Span} {p q r : List Rel} (h : R000.joinSeq p q = some r)
    (hL : AL L r) (hR : AR r R) : AL (leftAfter L p) q ∧ AR q R := by
  constructor
  · intro hne s hs
    obtain ⟨q', rfl⟩ := headSpan_eq_some hs
    by_cases hp : ∃ a, p = [.span a]
    · obtain ⟨a, rfl⟩ := hp
      rw [joinSeq_fused (a := a) rfl] at h
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [show leftAfter L [.span a] = L ++ [a] from rfl, chain_concat, GRel.comp_assoc,
        ← compose_some hc]
      by_cases hL0 : L = []
      · subst hL0
        rw [List.map_nil, GRel.chain_nil, GRel.id_comp]
        exact c.den_nonempty
      · exact hL hL0 c rfl
    · have hp' : ∀ a, p ≠ [.span a] := fun a ha => hp ⟨a, ha⟩
      rw [leftAfter_other hp'] at hne ⊢
      cases hl : lastSpan p with
      | none => rw [hl] at hne; exact (hne rfl).elim
      | some a =>
        obtain ⟨c, _, hc, _, _⟩ := joinSeq_junction h hl rfl
        rw [show (some a).toList = [a] from rfl, List.map_cons, GRel.chain_cons, List.map_nil, GRel.chain_nil, GRel.comp_id]
        exact comp_nonempty_of_compose hc
  · intro hne s hs
    have hq : q ≠ [] := by
      rintro rfl
      simp [lastSpan] at hs
    rcases joinSeq_last h hq with ⟨a, b, c, _, rfl, hc, hr⟩ | hr
    · obtain rfl : b = s := by simpa [lastSpan] using hs
      have := hR hne c hr
      rw [compose_some hc, GRel.comp_assoc] at this
      exact GRel.comp_nonempty_right this
    · exact hR hne s (hr ▸ hs)

/-- Every product starts with a span whose ground relation factors through
`t` on the left. -/
def HeadFrom (t : Span) (q : List Rel) : Prop :=
  ∃ h G, headSpan q = some h ∧ h.den = t.den.comp G

/-- What the chain `R'` to the right of the first factor of a sequence says
about the products `Nb` of the second factor, whose own right chain is `R`. -/
def Static (Nb : List (List Rel)) (R R' : List Span) : Prop :=
  R' = [] ∨ (∃ t, R' = t :: R ∧ Nb = [[.span t]]) ∨
    (∃ t, R' = [t] ∧ ∀ q ∈ Nb, HeadFrom t q)

/-- If a joined product is alive, its first part was alive before the
second. -/
theorem alive_first {L R R' : List Span} {Nb : List (List Rel)} {p q r : List Rel}
    (hst : Static Nb R R') (hq : q ∈ Nb) (h : R000.joinSeq p q = some r) (hp : p ≠ [])
    (hL : AL L r) (hR : AR r R) : AL L p ∧ AR p R' := by
  constructor
  · intro hL0 s hs
    rcases joinSeq_head h hp with ⟨a, b, q', c, rfl, rfl, hc, rfl⟩ | hh
    · obtain rfl : a = s := by simpa [headSpan] using hs
      have := hL hL0 c rfl
      rw [compose_some hc, ← GRel.comp_assoc] at this
      exact GRel.comp_nonempty_left this
    · exact hL hL0 s (hh.trans hs)
  · intro hne s hs
    rcases hst with rfl | ⟨t, rfl, rfl⟩ | ⟨t, rfl, hQ⟩
    · exact (hne rfl).elim
    · obtain rfl : q = [.span t] := by simpa using hq
      obtain ⟨c, q', hc, hq', rfl⟩ := joinSeq_junction h hs rfl
      obtain rfl : q' = [] := by simpa using hq'.symm
      rw [List.map_cons, GRel.chain_cons, ← GRel.comp_assoc, ← compose_some hc]
      by_cases hR0 : R = []
      · subst hR0
        rw [List.map_nil, GRel.chain_nil, GRel.comp_id]
        exact c.den_nonempty
      · exact hR hR0 c (lastSpan_of_getLast? (by simp))
    · obtain ⟨hh, G, hhq, hG⟩ := hQ q hq
      obtain ⟨c, q', hc, -, -⟩ := joinSeq_junction h hs hhq
      rw [List.map_cons, GRel.chain_cons, List.map_nil, GRel.chain_nil, GRel.comp_id]
      have := comp_nonempty_of_compose hc
      rw [hG, ← GRel.comp_assoc] at this
      exact GRel.comp_nonempty_left this

theorem headFrom_join {t : Span} {p q r : List Rel} (hp : HeadFrom t p)
    (h : R000.joinSeq p q = some r) : HeadFrom t r := by
  obtain ⟨hh, G, hhp, hG⟩ := hp
  have hne : p ≠ [] := by
    rintro rfl
    simp [headSpan] at hhp
  rcases joinSeq_head h hne with ⟨a, b, q', c, rfl, rfl, hc, rfl⟩ | hr
  · obtain rfl : a = hh := by simpa [headSpan] using hhp
    exact ⟨c, G.comp b.den, rfl, by rw [compose_some hc, hG, GRel.comp_assoc]⟩
  · exact ⟨hh, G, hr.trans hhp, hG⟩

/-- Filtering the products of the second factor before joining, and testing
the joined product on the right only, is filtering the joined products. -/
theorem second_filter (L R : List Span) (p : List Rel) (hp : p ≠ []) (hLp : AL L p)
    (X : List (List Rel)) :
    ((X.filter (keep (leftAfter L p) R)).filterMap (R000.joinSeq p)).filter
        (fun r => (aliveR r R).val) =
      (X.filterMap (R000.joinSeq p)).filter (keep L R) := by
  induction X with
  | nil => rfl
  | cons q X ih =>
    rw [List.filter_cons, List.filterMap_cons (l := X)]
    by_cases hk : keep (leftAfter L p) R q = true
    · rw [ite_eq_left hk, List.filterMap_cons]
      cases hj : R000.joinSeq p q with
      | none => exact ih
      | some r =>
        simp only [List.filter_cons]
        have hLr : AL L r := AL_join hj hp hLp (keep_iff.mp hk).1
        rw [ih, keep_eq L R r, (aliveL_iff L r).mpr hLr, Bool.true_and]
    · rw [ite_eq_right hk]
      cases hj : R000.joinSeq p q with
      | none => exact ih
      | some r =>
        simp only [List.filter_cons]
        have hr : ¬ keep L R r = true := fun hkr =>
          hk (keep_iff.mpr (alive_second hj (keep_iff.mp hkr).1 (keep_iff.mp hkr).2))
        rw [ite_eq_right hr, ih]

/-- The pruning step of a sequence is exact. -/
theorem seq_filter (Na Nb : List (List Rel)) (L R R' : List Span) (hne : ∀ p ∈ Na, p ≠ [])
    (hst : Static Nb R R') :
    ((Na.filter (keep L R')).flatMap fun p =>
        ((Nb.filter (keep (leftAfter L p) R)).filterMap (R000.joinSeq p)).filter
          fun r => (aliveR r R).val) =
      (Na.flatMap fun p => Nb.filterMap (R000.joinSeq p)).filter (keep L R) := by
  rw [List.filter_flatMap]
  induction Na with
  | nil => rfl
  | cons p Na ih =>
    have ih := ih fun p hp => hne p (List.mem_cons_of_mem _ hp)
    have hp : p ≠ [] := hne p List.mem_cons_self
    rw [List.filter_cons, List.flatMap_cons]
    by_cases hk : keep L R' p = true
    · rw [ite_eq_left hk, List.flatMap_cons, ih, second_filter L R p hp (keep_iff.mp hk).1]
    · rw [ite_eq_right hk, ih]
      have hnil : (Nb.filterMap (R000.joinSeq p)).filter (keep L R) = [] := by
        rw [List.filter_eq_nil_iff]
        intro r hr hkr
        obtain ⟨q, hq, hj⟩ := List.mem_filterMap.mp hr
        exact hk (keep_iff.mpr
          (alive_first hst hq hj hp (keep_iff.mp hkr).1 (keep_iff.mp hkr).2))
      rw [hnil]
      rfl

end R002

end RwLog
