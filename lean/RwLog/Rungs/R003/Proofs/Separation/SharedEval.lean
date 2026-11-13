/-
# The separating family: the shared evaluation

The shared evaluation of `cRel j` evaluates each of its `j + 1` levels once
for the interface `z`, which is what both spans of a choice leave to their
right, and looks the result up the second time. The memo it carries is
followed exactly: after the level `i` has been evaluated its entry stands at
the front, where the second span of the level above finds it at the first
comparison. So a level costs a constant number of key comparisons, each
linear in the size of the expression, and the whole evaluation is quadratic.
-/
import RwLog.Rungs.R003.Proofs.Separation.Family

namespace RwLog

namespace R003

namespace Sep

open Cost R001

/-- The summary of every sub-expression of the family: the two spans, and no
product with a call. -/
abbrev G : Summary := ⟨[xz, zz], []⟩

/-- The memo key of `cRel j` after the interface `c`. -/
abbrev kC (d j : Nat) (c : Option Span) : Key := ⟨false, cRel j, d, c⟩

/-! ## Comparing keys -/

theorem sameKey_ne {d : Nat} {e e' : Rel} (c c' : Option Span) (h : e ≠ e') :
    Costs (sameKey ⟨false, e, d, c⟩ ⟨false, e', d, c'⟩) false (1 + (e.size + e'.size)) := by
  refine ⟨?_, ?_⟩ <;> simp [sameKey, h]

theorem sameKey_zz (d : Nat) (e : Rel) :
    Costs (sameKey ⟨false, e, d, some zz⟩ ⟨false, e, d, some zz⟩) true (2 * e.size + 9) := by
  refine ⟨?_, ?_⟩
  · simp [sameKey, sameCtx, Charged.covers, covers_zz_zz]
  · simp [sameKey, sameCtx, Charged.covers, covers_zz_zz, Span.size, Store.size, Term.size]
    omega

theorem sameKey_none_zz (d : Nat) (e : Rel) :
    Costs (sameKey ⟨false, e, d, none⟩ ⟨false, e, d, some zz⟩) false (2 * e.size + 1) := by
  refine ⟨?_, ?_⟩
  · simp [sameKey, sameCtx]
  · simp [sameKey, sameCtx]; omega

/-! ## Looking a key up -/

theorem lookup_nil (k : Key) : Costs (lookup [] k) none 0 := ⟨rfl, le_rfl⟩

theorem lookup_hit {p : Key × Summary} {m : Memo} {k : Key} {c : Nat}
    (h : Costs (sameKey p.1 k) true c) : Costs (lookup (p :: m) k) (some p.2) c := by
  obtain ⟨hv, ht⟩ := h
  refine ⟨?_, ?_⟩
  · simp [lookup, findL, hv]
  · simpa [lookup, findL, hv] using ht

theorem lookup_miss {p : Key × Summary} {m : Memo} {k : Key} {c c' : Nat} {v : Option Summary}
    (h : Costs (sameKey p.1 k) false c) (h' : Costs (lookup m k) v c') :
    Costs (lookup (p :: m) k) v (c + c') := by
  obtain ⟨hv, ht⟩ := h
  obtain ⟨hv', ht'⟩ := h'
  refine ⟨?_, ?_⟩
  · simpa [lookup, findL, hv] using hv'
  · simp only [lookup, findL, bind_ticks, hv, Bool.false_eq_true, ↓reduceIte, pure_ticks,
      Nat.add_zero] at ht' ⊢
    omega

theorem memo_hit {k : Key} {m : Memo} {s : Summary} {c : Nat}
    (body : Memo → Cost (Summary × Memo)) (h : Costs (lookup m k) (some s) c) :
    Costs (memo k m body) (s, m) c := by
  obtain ⟨hv, ht⟩ := h
  refine ⟨?_, ?_⟩
  · simp [memo, hv]
  · simpa [memo, hv] using ht

theorem memo_miss {k : Key} {m m' : Memo} {s : Summary} {c c' : Nat}
    {body : Memo → Cost (Summary × Memo)} (h : Costs (lookup m k) none c)
    (hb : Costs (body m) (s, m') c') : Costs (memo k m body) (s, (k, s) :: m') (c + c') := by
  obtain ⟨hv, ht⟩ := h
  obtain ⟨hbv, hbt⟩ := hb
  refine ⟨?_, ?_⟩
  · simp [memo, hv, hbv]
  · simp only [memo, bind_ticks, hv, pure_ticks, Nat.add_zero]
    omega

/-! ## A span, a choice -/

/-- An interface of the evaluation: none, or `z`. -/
def Ctx (c : Option Span) : Prop := c = none ∨ c = some zz

theorem alive_ctx {c : Option Span} (hc : Ctx c) {s : Span} (hs : Good s) :
    Costs (alive c s) true 4 := by
  rcases hc with rfl | rfl
  · exact ⟨rfl, Nat.zero_le _⟩
  · have hg : ∀ t ∈ [zz, s], Good t := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact good_zz
      · exact hs
    refine ⟨chain_good hg, ?_⟩
    simp [alive, Charged.composable, size_good hs, size_good good_zz]

theorem eval_span {c : Option Span} (hc : Ctx c) {s : Span} (hs : Good s) (d : Nat) (m : Memo) :
    Costs (eval P0 d false (.span s) c m) (⟨[s], []⟩, m) 5 := by
  obtain ⟨hv, ht⟩ := alive_ctx hc hs
  rw [eval]
  refine ⟨?_, ?_⟩
  · simp [hv]
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ticks, tick_ticks, pure_ticks, Nat.add_zero]
    omega

theorem addSpan_xz_zz : Costs (foldL addSpan [xz] [zz]) [xz, zz] 4 := by
  refine ⟨?_, ?_⟩ <;> simp [foldL, addSpan, anyL, Span.size, Store.size, Term.size]

/-- A choice that is not in the memo: both spans. -/
theorem eval_tw_miss {c : Option Span} (hc : Ctx c) (d : Nat) {m : Memo} {cl : Nat}
    (h : Costs (lookup m (kC d 0 c)) none cl) :
    Costs (eval P0 d false tw c m) (G, (kC d 0 c, G) :: m) (cl + 15) := by
  rw [eval]
  refine Costs.mono (c := cl + (1 + (5 + (5 + (4 + (0 + 0)))))) ?_ (by omega)
  refine memo_miss h ?_
  refine Costs.bind (Costs.tick 1) ?_
  refine Costs.bind (eval_span hc good_xz d m) ?_
  refine Costs.bind (eval_span hc good_zz d m) ?_
  refine Costs.bind addSpan_xz_zz ?_
  refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
  exact Costs.pure _

/-- An expression of the family that is in the memo. -/
theorem eval_hit (d j : Nat) {c : Option Span} {m : Memo} {cl : Nat}
    (h : Costs (lookup m (kC d j c)) (some G) cl) :
    Costs (eval P0 d false (cRel j) c m) (G, m) cl := by
  cases j with
  | zero =>
    show Costs (eval P0 d false (.or (.span xz) (.span zz)) c m) _ _
    rw [eval]
    exact memo_hit _ h
  | succ j =>
    rw [cRel, eval]
    exact memo_hit _ h

/-! ## A sequence -/

theorem extend_ctx {c : Option Span} (hc : Ctx c) {x : Span} (hx : Good x) :
    Costs (extend c x) (some zz) 8 := by
  rcases hc with rfl | rfl
  · refine ⟨?_, ?_⟩
    · simp [extend, rightIface_good hx, bound_zz]
    · simp [extend, size_good hx]
  · have hcomp := compose_zz hx
    refine ⟨?_, ?_⟩
    · simp [extend, Charged.compose, hcomp, rightIface_good good_zz, bound_zz]
    · simp [extend, Charged.compose, hcomp, Charged.outSize, size_good hx, size_good good_zz]

theorem composes_xz : Costs (filterMapL (fun y => Charged.compose xz y) [xz, zz]) [xz, xz] 12 := by
  refine ⟨?_, ?_⟩
  · simp [filterMapL, Charged.compose, compose_xz good_xz, compose_xz good_zz]
  · simp [filterMapL, Charged.compose, compose_xz good_xz, compose_xz good_zz, Charged.outSize,
      Span.size, Store.size, Term.size]

theorem composes_zz : Costs (filterMapL (fun y => Charged.compose zz y) [xz, zz]) [zz, zz] 12 := by
  refine ⟨?_, ?_⟩
  · simp [filterMapL, Charged.compose, compose_zz good_xz, compose_zz good_zz]
  · simp [filterMapL, Charged.compose, compose_zz good_xz, compose_zz good_zz, Charged.outSize,
      Span.size, Store.size, Term.size]

theorem addSpan_nil_xz_xz : Costs (foldL addSpan [] [xz, xz]) [xz] 4 := by
  refine ⟨?_, ?_⟩ <;> simp [foldL, addSpan, anyL, Span.size, Store.size, Term.size]

theorem addSpan_xz_zz_zz : Costs (foldL addSpan [xz] [zz, zz]) [xz, zz] 12 := by
  refine ⟨?_, ?_⟩ <;> simp [foldL, addSpan, anyL, Span.size, Store.size, Term.size]

/-- After the first span of a choice: the second factor is evaluated. -/
theorem afterSpan_xz {c : Option Span} (hc : Ctx c)
    {second : Option Span → Memo → Cost (Summary × Memo)} {m m' : Memo} {c2 : Nat}
    (h : Costs (second (some zz) m) (G, m') c2) :
    Costs (afterSpan c second ([], [], m) xz) ([xz], [], m') (c2 + 24) := by
  unfold afterSpan
  refine Costs.mono (c := 8 + (c2 + (12 + (4 + (0 + 0))))) ?_ (by omega)
  refine Costs.bind (extend_ctx hc good_xz) ?_
  refine Costs.bind h ?_
  refine Costs.bind composes_xz ?_
  refine Costs.bind addSpan_nil_xz_xz ?_
  refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
  exact Costs.pure _

/-- After the second span of a choice: the second factor is looked up. -/
theorem afterSpan_zz {c : Option Span} (hc : Ctx c)
    {second : Option Span → Memo → Cost (Summary × Memo)} {m m' : Memo} {c3 : Nat}
    (h : Costs (second (some zz) m) (G, m') c3) :
    Costs (afterSpan c second ([xz], [], m) zz) ([xz, zz], [], m') (c3 + 32) := by
  unfold afterSpan
  refine Costs.mono (c := 8 + (c3 + (12 + (12 + (0 + 0))))) ?_ (by omega)
  refine Costs.bind (extend_ctx hc good_zz) ?_
  refine Costs.bind h ?_
  refine Costs.bind composes_zz ?_
  refine Costs.bind addSpan_xz_zz_zz ?_
  refine Costs.bind (v := []) ⟨rfl, le_rfl⟩ ?_
  exact Costs.pure _

/-- A sequence that is not in the memo: the choice, then the rest once for
each of its two spans. -/
theorem eval_seq (d j : Nat) {c : Option Span} (hc : Ctx c) {m m1 m2 m3 : Memo}
    {c0 c1 c2 c3 : Nat} (h0 : Costs (lookup m (kC d (j + 1) c)) none c0)
    (h1 : Costs (eval P0 d false tw c m) (G, m1) c1)
    (h2 : Costs (eval P0 d false (cRel j) (some zz) m1) (G, m2) c2)
    (h3 : Costs (eval P0 d false (cRel j) (some zz) m2) (G, m3) c3) :
    Costs (eval P0 d false (cRel (j + 1)) c m) (G, (kC d (j + 1) c, G) :: m3)
      (c0 + c1 + c2 + c3 + 57) := by
  rw [cRel, eval]
  refine Costs.mono (c := c0 + (1 + (c1 + ((c2 + 24) + ((c3 + 32) + 0) + (0 + 0))))) ?_ (by omega)
  refine memo_miss h0 ?_
  refine Costs.bind (Costs.tick 1) ?_
  refine Costs.bind h1 ?_
  unfold seqSummary
  refine Costs.bind (v := ([xz, zz], [], m3)) ?_ ?_
  · simp only [foldL]
    refine Costs.bind (afterSpan_xz hc h2) ?_
    refine Costs.bind (afterSpan_zz hc h3) ?_
    exact Costs.pure _
  · refine Costs.bind (v := ([xz, zz], [], m3)) ⟨rfl, le_rfl⟩ ?_
    exact Costs.pure _

/-! ## The memo -/

/-- The memo once a choice has been evaluated with nothing to its left. -/
abbrev memoA (d : Nat) : Memo := [(kC d 0 none, G)]

/-- The memo once a choice has been evaluated after the interface `z` too. -/
abbrev memoB (d : Nat) : Memo := (kC d 0 (some zz), G) :: memoA d

/-- The memo once `cRel j` has been evaluated after the interface `z`: the
entries of the levels, the last one evaluated first. -/
def mu (d : Nat) : Nat → Memo
  | 0 => memoB d
  | j + 1 => (kC d (j + 1) (some zz), G) :: mu d j

/-- The level just evaluated is found at the first comparison. -/
theorem lookup_mu (d : Nat) : ∀ j, Costs (lookup (mu d j) (kC d j (some zz))) (some G) (16 * j + 23)
  | 0 => (lookup_hit (sameKey_zz d (cRel 0))).mono (by rw [size_cRel])
  | j + 1 => (lookup_hit (sameKey_zz d (cRel (j + 1)))).mono (by rw [size_cRel]; omega)

theorem lookup_B_miss (d j : Nat) :
    Costs (lookup (memoB d) (kC d (j + 1) (some zz))) none (16 * j + 46) := by
  have h := sameKey_ne (d := d) (some zz) (some zz) (cRel_zero_ne_succ j)
  have h' := sameKey_ne (d := d) none (some zz) (cRel_zero_ne_succ j)
  refine (lookup_miss h (lookup_miss h' (lookup_nil _))).mono ?_
  rw [size_cRel, size_cRel]; omega

theorem lookup_A_miss (d j : Nat) :
    Costs (lookup (memoA d) (kC d (j + 1) (some zz))) none (8 * j + 23) := by
  have h' := sameKey_ne (d := d) none (some zz) (cRel_zero_ne_succ j)
  refine (lookup_miss h' (lookup_nil _)).mono ?_
  rw [size_cRel, size_cRel]; omega

theorem lookup_A_zero (d : Nat) : Costs (lookup (memoA d) (kC d 0 (some zz))) none 15 :=
  (lookup_miss (sameKey_none_zz d (cRel 0)) (lookup_nil _)).mono (by rw [size_cRel])

/-! ## The evaluation of `cRel j` -/

/-- After the interface `z`, once the choice is in the memo for both
interfaces. -/
theorem eval_B (d : Nat) : ∀ j,
    Costs (eval P0 d false (cRel j) (some zz) (memoB d)) (G, mu d j) (16 * j * j + 133 * j + 23)
  | 0 => (eval_hit d 0 (lookup_mu d 0)).mono (by omega)
  | j + 1 => by
    have h := eval_seq d j (Or.inr rfl) (lookup_B_miss d j) (eval_hit d 0 (lookup_mu d 0))
      (eval_B d j) (eval_hit d j (lookup_mu d j))
    refine h.mono ?_
    have e : 16 * (j + 1) * (j + 1) + 133 * (j + 1) + 23 =
        16 * j * j + 133 * j + 23 + (32 * j + 149) := by ring
    omega

/-- After the interface `z`, when the choice is in the memo only with nothing
to its left. -/
theorem eval_A (d : Nat) : ∀ j,
    Costs (eval P0 d false (cRel j) (some zz) (memoA d)) (G, mu d j) (16 * j * j + 157 * j + 156)
  | 0 => (eval_tw_miss (Or.inr rfl) d (lookup_A_zero d)).mono (by omega)
  | j + 1 => by
    have h := eval_seq d j (Or.inr rfl) (lookup_A_miss d j)
      (eval_tw_miss (Or.inr rfl) d (lookup_A_zero d)) (eval_B d j) (eval_hit d j (lookup_mu d j))
    refine h.mono ?_
    have e : 16 * (j + 1) * (j + 1) + 157 * (j + 1) + 156 =
        16 * j * j + 133 * j + 23 + (56 * j + 306) := by ring
    omega

/-- With nothing to its left and an empty memo. -/
theorem eval_top (d : Nat) : ∀ j, ∃ m : Memo,
    Costs (eval P0 d false (cRel j) none []) (G, m) (16 * j * j + 141 * j + 94)
  | 0 => ⟨_, (eval_tw_miss (Or.inl rfl) d (lookup_nil _)).mono (by omega)⟩
  | j + 1 => by
    have h := eval_seq d j (Or.inl rfl) (lookup_nil _)
      (eval_tw_miss (Or.inl rfl) d (lookup_nil _)) (eval_A d j) (eval_hit d j (lookup_mu d j))
    refine ⟨_, h.mono ?_⟩
    have e : 16 * (j + 1) * (j + 1) + 141 * (j + 1) + 94 =
        16 * j * j + 157 * j + 156 + (16 * j + 95) := by ring
    omega

/-! ## The shared evaluation -/

theorem lives : Costs (flatMapL (Tabled.live []) [xz, zz]) [xz, zz] 6 := by
  have h := Costs.flatMapL (f := Tabled.live []) (g := fun s => [s]) (c := 3) (xs := [xz, zz])
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact live_good good_xz
      · exact live_good good_zz)
  simpa using h

theorem addSpan_nil_xz_zz : Costs (foldL addSpan [] [xz, zz]) [xz, zz] 4 := by
  refine ⟨?_, ?_⟩ <;> simp [foldL, addSpan, anyL, Span.size, Store.size, Term.size]

/-- What the shared evaluation of `cRel j` costs at most. -/
def sharedBound (j : Nat) : Nat := 16 * j * j + 141 * j + 104

/-- The shared evaluation of `cRel j`: final, the two spans, quadratic. -/
theorem shared_gC (d j : Nat) : Costs (shared P0 d (gC j)) (true, [xz, zz]) (sharedBound j) := by
  obtain ⟨m, hm⟩ := eval_top d j
  have hrel : (gC j).rel = cRel j := rfl
  unfold shared sharedBound
  rw [hrel]
  refine Costs.mono (c := 16 * j * j + 141 * j + 94 + (6 + (4 + 0))) ?_ (by omega)
  refine Costs.bind hm ?_
  simp only [List.isEmpty_nil, ↓reduceIte]
  refine Costs.bind lives ?_
  refine Costs.bind addSpan_nil_xz_zz ?_
  exact Costs.pure _

/-- The shared evaluation of one span. -/
theorem shared_gS (d : Nat) {s : Span} (hs : Good s) : Costs (shared P0 d (gS s)) (true, [s]) 8 := by
  have hrel : (gS s).rel = .span s := rfl
  unfold shared
  rw [hrel]
  refine Costs.mono (c := 5 + (3 + (0 + 0))) ?_ (by omega)
  refine Costs.bind (eval_span (Or.inl rfl) hs d []) ?_
  simp only [List.isEmpty_nil, ↓reduceIte]
  refine Costs.bind (v := [s]) ?_ ?_
  · have h := live_good hs
    refine ⟨?_, ?_⟩
    · simp [flatMapL, h.1]
    · simpa [flatMapL] using h.2
  · refine Costs.bind (v := [s]) ⟨rfl, le_rfl⟩ ?_
    exact Costs.pure _

end Sep

end R003

end RwLog
