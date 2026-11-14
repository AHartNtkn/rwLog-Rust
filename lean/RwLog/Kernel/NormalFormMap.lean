/-
# Reading the nodes of a program as the nodes of its mirror image

A run of a machine on the converse of a query, or on the mirror image of a
query in the mirrored program, goes through the nodes of the run on the
query, each read another way. This file says which way, for the four cases
at once.

`e.flip` is `e` with every call read the other way round: `call n` becomes
the converse of `call n`. `nmap b t e` is the normal form of `e`, of its
converse when `b`, with every call flipped when `t`:

* `nmap false false` is the normal form, the identity on nodes;
* `nmap true false` is the converse node (`RelOf.normConv`);
* `nmap true true e` is the normal form of the mirror image `e.dual`
  (`normB_dual`), read in the mirrored program;
* `nmap false true` is the two together.

For a node `e`:

* `nmap b t e` is a node, and `nmap b t` is its own inverse
  (`Normal.nmap_nmap`);
* it is a node of the same kind, with the members of `e` mapped: a span
  swapped when `b` (`view_span`), a call with its sense changed
  (`view_call`), a chain of the mapped members, reversed when `b`
  (`view_chain`), a meet of the mapped members in the structural order
  (`view_meet`), a union of the mapped members (`view_union`);
* the stretch of a chain and a meet without a member are the mapped stretch
  and the mapped meet without the mapped member (`interval`, `without`);
* the body a call node reads in the program, mirrored when `t`, is the
  mapped body (`bodyOf_nmap`).
-/
import RwLog.Kernel.NormalFormStable
import RwLog.Trusted.Charged
import RwLog.SpanLayer.Dual

namespace RwLog

/-- Every call read the other way round. -/
def RelOf.flip : Rel → Rel
  | .zero => .zero
  | .span s => .span s
  | .or a b => .or a.flip b.flip
  | .and a b => .and a.flip b.flip
  | .seq a b => .seq a.flip b.flip
  | .conv a => .conv a.flip
  | .call n => .conv (.call n)

/-- Flip the calls, or not. -/
def tf : Bool → Rel → Rel
  | true, e => e.flip
  | false, e => e

theorem tf_false : tf false = id := funext fun _ => rfl

theorem tf_true : tf true = RelOf.flip := funext fun _ => rfl

/-- The normal form of `e`, of its converse when `b`, with every call
flipped when `t`. -/
def nmap (b t : Bool) (e : Rel) : Rel := normB b (tf t e)

/-! ## Flipping and the members of a node -/

theorem seqParts_flip : ∀ e : Rel, seqParts e.flip = (seqParts e).map RelOf.flip
  | .seq a b => by simp [RelOf.flip, seqParts, seqParts_flip a, seqParts_flip b]
  | .zero | .span _ | .or _ _ | .and _ _ | .conv _ | .call _ => by simp [RelOf.flip, seqParts]

theorem andParts_flip : ∀ e : Rel, andParts e.flip = (andParts e).map RelOf.flip
  | .and a b => by simp [RelOf.flip, andParts, andParts_flip a, andParts_flip b]
  | .zero | .span _ | .or _ _ | .seq _ _ | .conv _ | .call _ => by simp [RelOf.flip, andParts]

theorem orBranches_flip : ∀ e : Rel, orBranches e.flip = (orBranches e).map RelOf.flip
  | .or a b => by simp [RelOf.flip, orBranches, orBranches_flip a, orBranches_flip b]
  | .zero | .span _ | .and _ _ | .seq _ _ | .conv _ | .call _ => by simp [RelOf.flip, orBranches]

theorem flip_mkSeq : ∀ L : List Rel, (mkSeq L).flip = mkSeq (L.map RelOf.flip)
  | [] => rfl
  | [_] => rfl
  | e :: e' :: es => by
    have := flip_mkSeq (e' :: es)
    simp only [mkSeq, RelOf.flip, List.map_cons] at this ⊢
    rw [this]

theorem flip_mkAnd : ∀ L : List Rel, (mkAnd L).flip = mkAnd (L.map RelOf.flip)
  | [] => rfl
  | [_] => rfl
  | e :: e' :: es => by
    have := flip_mkAnd (e' :: es)
    simp only [mkAnd, RelOf.flip, List.map_cons] at this ⊢
    rw [this]

theorem flip_mkOr : ∀ L : List Rel, (mkOr L).flip = mkOr (L.map RelOf.flip)
  | [] => rfl
  | [_] => rfl
  | e :: e' :: es => by
    have := flip_mkOr (e' :: es)
    simp only [mkOr, RelOf.flip, List.map_cons] at this ⊢
    rw [this]

theorem seqParts_tf (t : Bool) (e : Rel) : seqParts (tf t e) = (seqParts e).map (tf t) := by
  cases t
  · simp [tf_false]
  · rw [tf_true]; exact seqParts_flip e

theorem andParts_tf (t : Bool) (e : Rel) : andParts (tf t e) = (andParts e).map (tf t) := by
  cases t
  · simp [tf_false]
  · rw [tf_true]; exact andParts_flip e

theorem orBranches_tf (t : Bool) (e : Rel) : orBranches (tf t e) = (orBranches e).map (tf t) := by
  cases t
  · simp [tf_false]
  · rw [tf_true]; exact orBranches_flip e

theorem tf_mkSeq (t : Bool) (L : List Rel) : tf t (mkSeq L) = mkSeq (L.map (tf t)) := by
  cases t
  · simp [tf_false]
  · rw [tf_true]; exact flip_mkSeq L

theorem tf_mkAnd (t : Bool) (L : List Rel) : tf t (mkAnd L) = mkAnd (L.map (tf t)) := by
  cases t
  · simp [tf_false]
  · rw [tf_true]; exact flip_mkAnd L

theorem tf_mkOr (t : Bool) (L : List Rel) : tf t (mkOr L) = mkOr (L.map (tf t)) := by
  cases t
  · simp [tf_false]
  · rw [tf_true]; exact flip_mkOr L

/-! ## The normal form of a chain, a meet and a union of anything -/

theorem seqParts_mkSeq_flatMap : ∀ {L : List Rel}, L ≠ [] →
    seqParts (mkSeq L) = L.flatMap seqParts
  | [], h => absurd rfl h
  | [e], _ => by simp [mkSeq]
  | e :: e' :: es, _ => by
    have := seqParts_mkSeq_flatMap (L := e' :: es) (by simp)
    simp only [mkSeq, seqParts, List.flatMap_cons] at this ⊢
    rw [this]

theorem andParts_mkAnd_flatMap : ∀ {L : List Rel}, L ≠ [] →
    andParts (mkAnd L) = L.flatMap andParts
  | [], h => absurd rfl h
  | [e], _ => by simp [mkAnd]
  | e :: e' :: es, _ => by
    have := andParts_mkAnd_flatMap (L := e' :: es) (by simp)
    simp only [mkAnd, andParts, List.flatMap_cons] at this ⊢
    rw [this]

theorem orBranches_mkOr_flatMap : ∀ {L : List Rel}, L ≠ [] →
    orBranches (mkOr L) = L.flatMap orBranches
  | [], h => absurd rfl h
  | [e], _ => by simp [mkOr]
  | e :: e' :: es, _ => by
    have := orBranches_mkOr_flatMap (L := e' :: es) (by simp)
    simp only [mkOr, orBranches, List.flatMap_cons] at this ⊢
    rw [this]

/-- The normal form of a chain of anything. -/
theorem normB_mkSeq (b : Bool) {L : List Rel} (hL : L ≠ []) :
    normB b (mkSeq L) =
      mkSeq ((if b then L.reverse else L).flatMap fun x => seqParts (normB b x)) := by
  rw [← (normal_normB b (mkSeq L)).mkSeq_seqParts, seqParts_normB, seqParts_mkSeq_flatMap hL]
  congr 1
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.flatMap_assoc]
    refine List.flatMap_congr fun x _ => ?_
    rw [seqParts_normB]; simp
  · simp only [ite_true, List.reverse_flatMap, List.flatMap_assoc]
    refine List.flatMap_congr fun x _ => ?_
    rw [seqParts_normB]; simp

theorem sortedParts_congr {L L' : List Rel} (h : L.Perm L') : sortedParts L = sortedParts L' :=
  eq_of_perm_of_sorted ((sortedParts_perm L).trans (h.trans (sortedParts_perm L').symm))
    (pairwise_sortedParts L) (pairwise_sortedParts L')

theorem sortedBranches_congr {L L' : List Rel} (h : ∀ z, z ≠ .zero → (z ∈ L ↔ z ∈ L')) :
    sortedBranches L = sortedBranches L' :=
  eq_of_mem_iff_of_strict (fun z => by
    rw [mem_sortedBranches, mem_sortedBranches]
    exact and_congr_left fun hz => h z hz) (pairwise_sortedBranches L) (pairwise_sortedBranches L')

/-- The normal form of a meet of anything. -/
theorem normB_mkAnd (b : Bool) {L : List Rel} (hL : L ≠ []) :
    normB b (mkAnd L) = mkAnd (sortedParts (L.flatMap fun x => andParts (normB b x))) := by
  have hN := normal_normB b (mkAnd L)
  rw [← hN.mkAnd_andParts]
  congr 1
  refine eq_of_perm_of_sorted ?_ hN.sorted_andParts (pairwise_sortedParts _)
  refine (andParts_normB_perm b _).trans ?_
  rw [andParts_mkAnd_flatMap hL, List.flatMap_assoc]
  refine (List.Perm.flatMap_left _ fun x _ => (andParts_normB_perm b x).symm).trans ?_
  exact (sortedParts_perm _).symm

/-- The normal form of a union of anything. -/
theorem normB_mkOr (b : Bool) (L : List Rel) :
    normB b (mkOr L) = mkOr (sortedBranches (L.flatMap fun x => orBranches (normB b x))) := by
  by_cases hL : L = []
  · subst hL
    have h0 : sortedBranches [] = [] :=
      List.eq_nil_iff_forall_not_mem.2 fun z hz => by simp [mem_sortedBranches] at hz
    cases b <;> simp [mkOr, normB, h0]
  have hN := normal_normB b (mkOr L)
  rw [← hN.mkOr_unionParts]
  congr 1
  refine eq_of_mem_iff_of_strict (fun z => ?_) hN.strict_unionParts (pairwise_sortedBranches _)
  rw [hN.mem_unionParts, mem_sortedBranches]
  refine and_congr_left fun hz => ?_
  rw [mem_orBranches_normB b hz, orBranches_mkOr_flatMap hL]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨w, ⟨x, hx, hw⟩, h⟩
    exact ⟨x, hx, (mem_orBranches_normB b hz x).2 ⟨w, hw, h⟩⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨w, hw, h'⟩ := (mem_orBranches_normB b hz x).1 h
    exact ⟨w, ⟨x, hx, hw⟩, h'⟩

/-! ## Flipping commutes with the normal form -/

/-- The normal form of a flipped normal form is the normal form of the
flipped expression, with the two converses cancelling. -/
theorem normB_flip_normB : ∀ (b c : Bool) (e : Rel),
    normB b (normB c e).flip = normB (b ^^ c) e.flip
  | b, c, .zero => by cases b <;> cases c <;> rfl
  | b, c, .span s => by cases b <;> cases c <;> simp [normB, RelOf.flip]
  | b, c, .call n => by cases b <;> cases c <;> simp [normB, RelOf.flip]
  | b, c, .conv x => by
    rw [normB, RelOf.flip, normB, normB_flip_normB b (!c) x]
    cases b <;> cases c <;> rfl
  | b, c, .seq x y => by
    have hx : seqParts (normB (b ^^ c) x.flip) =
        (if b then ((seqParts (normB c x)).map RelOf.flip).reverse
          else (seqParts (normB c x)).map RelOf.flip).flatMap fun w => seqParts (normB b w) := by
      rw [← normB_flip_normB b c x, seqParts_normB, seqParts_flip]
    have hy : seqParts (normB (b ^^ c) y.flip) =
        (if b then ((seqParts (normB c y)).map RelOf.flip).reverse
          else (seqParts (normB c y)).map RelOf.flip).flatMap fun w => seqParts (normB b w) := by
      rw [← normB_flip_normB b c y, seqParts_normB, seqParts_flip]
    have hne : ∀ c, seqParts (normB c x) ++ seqParts (normB c y) ≠ [] := fun c => by
      simp [seqParts_ne_nil]
    have hne' : ∀ c, seqParts (normB c y) ++ seqParts (normB c x) ≠ [] := fun c => by
      simp [seqParts_ne_nil]
    cases b <;> cases c <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, normB, RelOf.flip] at hx hy ⊢
    · rw [flip_mkSeq, normB_mkSeq false (by simpa using hne false), hx, hy]
      simp
    · rw [flip_mkSeq, normB_mkSeq false (by simpa using hne' true), hx, hy]
      simp
    · rw [flip_mkSeq, normB_mkSeq true (by simpa using hne false), hx, hy]
      simp
    · rw [flip_mkSeq, normB_mkSeq true (by simpa using hne' true), hx, hy]
      simp
  | b, c, .and x y => by
    have hne : sortedParts (andParts (normB c x) ++ andParts (normB c y)) ≠ [] := by
      intro h
      have h1 := (sortedParts_perm (andParts (normB c x) ++ andParts (normB c y))).length_eq
      rw [h, List.length_nil, List.length_append] at h1
      have h2 := List.length_pos_iff.2 (andParts_ne_nil (normB c x))
      omega
    have hx := (andParts_normB_perm b (normB c x).flip)
    have hy := (andParts_normB_perm b (normB c y).flip)
    rw [normB_flip_normB b c x, andParts_flip] at hx
    rw [normB_flip_normB b c y, andParts_flip] at hy
    conv => lhs; rw [normB, flip_mkAnd, normB_mkAnd b (by simpa using hne)]
    conv => rhs; rw [RelOf.flip, normB]
    congr 1
    refine sortedParts_congr ?_
    refine (((sortedParts_perm _).map _).flatMap_right _).trans ?_
    rw [List.map_append, List.flatMap_append]
    exact hx.symm.append hy.symm
  | b, c, .or x y => by
    conv => lhs; rw [normB, flip_mkOr, normB_mkOr b]
    conv => rhs; rw [RelOf.flip, normB]
    congr 1
    refine sortedBranches_congr fun z hz => ?_
    have h0 : z ∉ orBranches (normB b RelOf.zero.flip) := by
      cases b <;> simpa [normB, orBranches, RelOf.flip] using hz
    rw [List.mem_append, ← normB_flip_normB b c x, ← normB_flip_normB b c y,
      mem_orBranches_normB b hz, mem_orBranches_normB b hz, orBranches_flip, orBranches_flip]
    simp only [List.mem_flatMap, List.mem_map, mem_sortedBranches, List.mem_append]
    constructor
    · rintro ⟨w, ⟨v, ⟨hv, -⟩, rfl⟩, h⟩
      rcases hv with hv | hv
      · exact .inl ⟨_, ⟨v, hv, rfl⟩, h⟩
      · exact .inr ⟨_, ⟨v, hv, rfl⟩, h⟩
    · rintro (⟨w, ⟨v, hv, rfl⟩, h⟩ | ⟨w, ⟨v, hv, rfl⟩, h⟩)
      · exact ⟨_, ⟨v, ⟨.inl hv, fun e => h0 (e ▸ h)⟩, rfl⟩, h⟩
      · exact ⟨_, ⟨v, ⟨.inr hv, fun e => h0 (e ▸ h)⟩, rfl⟩, h⟩

/-- Flipping twice changes nothing a normal form keeps. -/
theorem normB_flip_flip : ∀ (b : Bool) (e : Rel), normB b e.flip.flip = normB b e
  | b, .zero => rfl
  | b, .span _ => rfl
  | b, .call n => by cases b <;> rfl
  | b, .conv x => by simp only [RelOf.flip, normB, normB_flip_flip (!b) x]
  | b, .seq x y => by
    cases b <;> simp only [RelOf.flip, normB, normB_flip_flip _ x, normB_flip_flip _ y]
  | b, .and x y => by simp only [RelOf.flip, normB, normB_flip_flip b x, normB_flip_flip b y]
  | b, .or x y => by simp only [RelOf.flip, normB, normB_flip_flip b x, normB_flip_flip b y]

/-- The normal form of the mirror image: the converse of the normal form
with every call flipped. -/
theorem normB_dual : ∀ (b : Bool) (e : Rel), normB b e.dual = normB (!b) e.flip
  | b, .zero => by cases b <;> rfl
  | b, .span s => by cases b <;> simp [RelOf.dual, RelOf.flip, normB, Span.swap]
  | b, .call n => by cases b <;> rfl
  | b, .conv x => by
    simp only [RelOf.dual, RelOf.flip, normB, normB_dual (!b) x]
  | b, .seq x y => by
    cases b <;> simp only [RelOf.dual, RelOf.flip, normB, normB_dual _ x, normB_dual _ y,
      Bool.not_false, Bool.not_true]
  | b, .and x y => by simp only [RelOf.dual, RelOf.flip, normB, normB_dual b x, normB_dual b y]
  | b, .or x y => by simp only [RelOf.dual, RelOf.flip, normB, normB_dual b x, normB_dual b y]

/-! ## The map on nodes -/

theorem nmap_ff {e : Rel} (h : Normal e) : nmap false false e = e := h.normB_false

theorem nmap_tf (e : Rel) : nmap true false e = e.normConv := rfl

/-- With the converse and the flip, the map is the normal form of the mirror
image. -/
theorem nmap_tt (e : Rel) : nmap true true e = e.dual.norm := (normB_dual false e).symm

theorem normal_nmap (b t : Bool) (e : Rel) : Normal (nmap b t e) := normal_normB b _

/-- Mapping a normal form is normalising the expression that way. -/
theorem nmap_normB (b t c : Bool) (e : Rel) : nmap b t (normB c e) = normB (b ^^ c) (tf t e) := by
  cases t
  · exact normB_normB b c e
  · exact normB_flip_normB b c e

theorem tf_tf_normB (b t : Bool) (e : Rel) : normB b (tf t (tf t e)) = normB b e := by
  cases t
  · rfl
  · exact normB_flip_flip b e

/-- The map is its own inverse on nodes. -/
theorem Normal.nmap_nmap {e : Rel} (h : Normal e) (b t : Bool) : nmap b t (nmap b t e) = e := by
  rw [nmap, nmap, ← nmap, nmap_normB, Bool.xor_self, tf_tf_normB]
  exact h.normB_false

theorem Normal.nmap_inj {a c : Rel} (ha : Normal a) (hc : Normal c) {b t : Bool}
    (h : nmap b t a = nmap b t c) : a = c := by
  rw [← ha.nmap_nmap b t, ← hc.nmap_nmap b t, h]

theorem tf_seq (t : Bool) (x y : Rel) : tf t (.seq x y) = .seq (tf t x) (tf t y) := by
  cases t <;> rfl

theorem tf_and (t : Bool) (x y : Rel) : tf t (.and x y) = .and (tf t x) (tf t y) := by
  cases t <;> rfl

theorem tf_or (t : Bool) (x y : Rel) : tf t (.or x y) = .or (tf t x) (tf t y) := by
  cases t <;> rfl

theorem mkSeq_two : ∀ {L : List Rel}, 2 ≤ L.length → ∃ a c, mkSeq L = .seq a c
  | [], h => by simp at h
  | [_], h => by simp at h
  | a :: c :: L, _ => ⟨a, mkSeq (c :: L), rfl⟩

theorem mkAnd_two : ∀ {L : List Rel}, 2 ≤ L.length → ∃ a c, mkAnd L = .and a c
  | [], h => by simp at h
  | [_], h => by simp at h
  | a :: c :: L, _ => ⟨a, mkAnd (c :: L), rfl⟩

theorem mkOr_two : ∀ {L : List Rel}, 2 ≤ L.length → ∃ a c, mkOr L = .or a c
  | [], h => by simp at h
  | [_], h => by simp at h
  | a :: c :: L, _ => ⟨a, mkOr (c :: L), rfl⟩

/-- The map of a `;` is a `;`. -/
theorem nmap_seq_isSeq (b t : Bool) (x y : Rel) : ∃ a c, nmap b t (.seq x y) = .seq a c := by
  have h1 := fun c z => List.length_pos_iff.2 (seqParts_ne_nil (normB c z))
  rw [nmap, tf_seq]
  cases b
  · exact mkSeq_two (by
      have := h1 false (tf t x); have := h1 false (tf t y)
      simp only [List.length_append]; omega)
  · exact mkSeq_two (by
      have := h1 true (tf t x); have := h1 true (tf t y)
      simp only [List.length_append]; omega)

/-- The map of a `&` is a `&`. -/
theorem nmap_and_isAnd (b t : Bool) (x y : Rel) : ∃ a c, nmap b t (.and x y) = .and a c := by
  rw [nmap, tf_and, normB]
  refine mkAnd_two ?_
  rw [(sortedParts_perm _).length_eq, List.length_append]
  have := List.length_pos_iff.2 (andParts_ne_nil (normB b (tf t x)))
  have := List.length_pos_iff.2 (andParts_ne_nil (normB b (tf t y)))
  omega

theorem nmap_zero (b t : Bool) : nmap b t .zero = .zero := by cases b <;> cases t <;> rfl

theorem nmap_span (b t : Bool) (s : Span) :
    nmap b t (.span s) = .span (if b then s.swap else s) := by
  cases b <;> cases t <;> rfl

theorem nmap_call (b t : Bool) (n : Name) :
    nmap b t (.call n) = if b ^^ t then .conv (.call n) else .call n := by
  cases b <;> cases t <;> rfl

theorem nmap_conv_call (b t : Bool) (n : Name) :
    nmap b t (.conv (.call n)) = if b ^^ t then .call n else .conv (.call n) := by
  cases b <;> cases t <;> rfl

theorem Normal.notSeq_nmap {e : Rel} (h : Normal e) (hs : NotSeq e) (b t : Bool) :
    NotSeq (nmap b t e) := by
  intro a c he
  have := h.nmap_nmap b t
  rw [he] at this
  obtain ⟨a', c', h'⟩ := nmap_seq_isSeq b t a c
  exact hs a' c' (this.symm.trans h')

theorem Normal.notAnd_nmap {e : Rel} (h : Normal e) (hs : NotAnd e) (b t : Bool) :
    NotAnd (nmap b t e) := by
  intro a c he
  have := h.nmap_nmap b t
  rw [he] at this
  obtain ⟨a', c', h'⟩ := nmap_and_isAnd b t a c
  exact hs a' c' (this.symm.trans h')

theorem Normal.notOr_nmap {e : Rel} (h : Normal e) (hs : NotOr e) (b t : Bool) :
    NotOr (nmap b t e) := by
  intro a c he
  cases e with
  | zero => rw [nmap_zero] at he; cases he
  | span s => rw [nmap_span] at he; cases he
  | call n => rw [nmap_call] at he; split at he <;> cases he
  | conv x =>
    obtain ⟨n, rfl⟩ := normal_conv.1 h
    rw [nmap_conv_call] at he; split at he <;> cases he
  | seq x y =>
    obtain ⟨a', c', h'⟩ := nmap_seq_isSeq b t x y
    rw [h'] at he; cases he
  | and x y =>
    obtain ⟨a', c', h'⟩ := nmap_and_isAnd b t x y
    rw [h'] at he; cases he
  | or x y => exact hs x y rfl

theorem Normal.nmap_ne_zero {e : Rel} (h : Normal e) (hz : e ≠ .zero) (b t : Bool) :
    nmap b t e ≠ .zero := by
  intro he
  have := h.nmap_nmap b t
  rw [he, nmap_zero] at this
  exact hz this.symm

/-! ## The members of a mapped node -/

theorem flatMap_single {α β : Type} (f : α → β) : ∀ l : List α, (l.flatMap fun x => [f x]) = l.map f
  | [] => rfl
  | a :: l => by simp [flatMap_single f l]


/-- The members of a mapped chain. -/
theorem Normal.seqParts_nmap {e : Rel} (h : Normal e) (b t : Bool) :
    seqParts (nmap b t e) =
      (if b then (seqParts e).reverse else seqParts e).map (nmap b t) := by
  have hone : ∀ x ∈ seqParts e, seqParts (normB b (tf t x)) = [nmap b t x] := fun x hx =>
    seqParts_notSeq ((h.of_mem_seqParts hx).notSeq_nmap (notSeq_of_mem_seqParts hx) b t)
  rw [nmap, seqParts_normB, seqParts_tf]
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.flatMap_map]
    rw [List.flatMap_congr hone, flatMap_single]
  · simp only [ite_true, ← List.map_reverse, List.flatMap_map]
    rw [List.flatMap_congr fun x hx => hone x (List.mem_reverse.1 hx), flatMap_single]

/-- The members of a mapped meet. -/
theorem Normal.andParts_nmap {e : Rel} (h : Normal e) (b t : Bool) :
    andParts (nmap b t e) = sortedParts ((andParts e).map (nmap b t)) := by
  have hone : ∀ x ∈ andParts e, andParts (normB b (tf t x)) = [nmap b t x] := fun x hx =>
    andParts_notAnd ((h.of_mem_andParts hx).notAnd_nmap (notAnd_of_mem_andParts hx) b t)
  refine eq_of_perm_of_sorted ?_ (normal_nmap b t e).sorted_andParts (pairwise_sortedParts _)
  refine (andParts_normB_perm b _).trans ?_
  rw [andParts_tf, List.flatMap_map, List.flatMap_congr hone, flatMap_single]
  exact (sortedParts_perm _).symm

/-- The map of a chain of nodes. -/
theorem nmap_mkSeq (b t : Bool) {L : List Rel} (hL : L ≠ [])
    (hx : ∀ x ∈ L, Normal x ∧ NotSeq x) :
    nmap b t (mkSeq L) = mkSeq ((if b then L.reverse else L).map (nmap b t)) := by
  have hN := normal_mkSeq hL hx
  rw [← (normal_nmap b t (mkSeq L)).mkSeq_seqParts, hN.seqParts_nmap,
    seqParts_mkSeq hL fun x h => (hx x h).2]

/-- The map of a meet of nodes. -/
theorem nmap_mkAnd (b t : Bool) {L : List Rel} (hL : L ≠ [])
    (hx : ∀ x ∈ L, Normal x ∧ NotAnd x) (hs : L.Pairwise RelLE) :
    nmap b t (mkAnd L) = mkAnd (sortedParts (L.map (nmap b t))) := by
  have hN := normal_mkAnd hL hx hs
  rw [← (normal_nmap b t (mkAnd L)).mkAnd_andParts, hN.andParts_nmap,
    andParts_mkAnd hL fun x h => (hx x h).2]

/-! ## The view of a mapped node -/

theorem view_mkSeq {L : List Rel} (h2 : 2 ≤ L.length) (hL : ∀ x ∈ L, NotSeq x) :
    (mkSeq L).view = .chain L := by
  obtain ⟨a, c, e⟩ := mkSeq_two h2
  have hp := seqParts_mkSeq (L := L) (by rintro rfl; simp at h2) hL
  rw [e] at hp ⊢
  simp only [RelOf.view, hp]

theorem view_mkAnd {L : List Rel} (h2 : 2 ≤ L.length) (hL : ∀ x ∈ L, NotAnd x) :
    (mkAnd L).view = .meet L := by
  obtain ⟨a, c, e⟩ := mkAnd_two h2
  have hp := andParts_mkAnd (L := L) (by rintro rfl; simp at h2) hL
  rw [e] at hp ⊢
  simp only [RelOf.view, hp]

theorem view_mkOr {L : List Rel} (h2 : 2 ≤ L.length) (hL : ∀ x ∈ L, NotOr x) :
    (mkOr L).view = .union L := by
  obtain ⟨a, c, e⟩ := mkOr_two h2
  have hp := orBranches_mkOr (L := L) (by rintro rfl; simp at h2) hL
  rw [e] at hp ⊢
  simp only [RelOf.view, hp]

/-- A mapped span is the span, swapped when the converse is taken. -/
theorem Normal.view_span {e : Rel} {s : Span} (hv : e.view = .span s) (b t : Bool) :
    (nmap b t e).view = .span (if b then s.swap else s) := by
  cases e with
  | span s' =>
    obtain rfl : s' = s := by simpa [RelOf.view] using hv
    rw [nmap_span]; rfl
  | conv x => cases x <;> simp [RelOf.view] at hv
  | _ => simp [RelOf.view] at hv

/-- A mapped call is the call, with its sense changed by the converse and by
the flip. -/
theorem Normal.view_call {e : Rel} {n : Name} {f : Bool} (hv : e.view = .call n f) (b t : Bool) :
    (nmap b t e).view = .call n (f ^^ (b ^^ t)) := by
  cases e with
  | call m =>
    obtain ⟨rfl, rfl⟩ : m = n ∧ false = f := by simpa [RelOf.view] using hv
    rw [nmap_call]
    cases b <;> cases t <;> rfl
  | conv x =>
    cases x with
    | call m =>
      obtain ⟨rfl, rfl⟩ : m = n ∧ true = f := by simpa [RelOf.view] using hv
      rw [nmap_conv_call]
      cases b <;> cases t <;> rfl
    | _ => simp [RelOf.view] at hv
  | _ => simp [RelOf.view] at hv

/-- A mapped chain is the chain of the mapped members, reversed when the
converse is taken. -/
theorem Normal.view_chain_nmap {e : Rel} {xs : List Rel} (h : Normal e)
    (hv : e.view = .chain xs) (b t : Bool) :
    (nmap b t e).view = .chain ((if b then xs.reverse else xs).map (nmap b t)) := by
  obtain ⟨h2, hmem, rfl⟩ := h.view_chain hv
  rw [nmap_mkSeq b t (by rintro rfl; simp at h2) hmem]
  refine view_mkSeq (by cases b <;> simpa using h2) fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have hx' : x ∈ xs := by cases b <;> simpa using hx
  exact (hmem x hx').1.notSeq_nmap (hmem x hx').2 b t

/-- A mapped meet is the meet of the mapped members, in the structural
order. -/
theorem Normal.view_meet_nmap {e : Rel} {xs : List Rel} (h : Normal e)
    (hv : e.view = .meet xs) (b t : Bool) :
    (nmap b t e).view = .meet (sortedParts (xs.map (nmap b t))) := by
  obtain ⟨h2, hmem, hs, rfl⟩ := h.view_meet hv
  rw [nmap_mkAnd b t (by rintro rfl; simp at h2) hmem hs]
  refine view_mkAnd (by rw [(sortedParts_perm _).length_eq]; simpa using h2) fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ((sortedParts_perm _).mem_iff.1 hy)
  exact (hmem x hx).1.notAnd_nmap (hmem x hx).2 b t

theorem two_le_length_of_mem {α : Type} {L : List α} {a c : α} (ha : a ∈ L) (hc : c ∈ L)
    (h : a ≠ c) : 2 ≤ L.length := by
  match L, ha, hc with
  | [x], ha, hc =>
    simp only [List.mem_singleton] at ha hc
    exact absurd (ha.trans hc.symm) h
  | _ :: _ :: _, _, _ => simp

/-- A mapped union is the union of the mapped members. -/
theorem Normal.view_union_nmap {e : Rel} {xs : List Rel} (h : Normal e)
    (hv : e.view = .union xs) (b t : Bool) :
    (nmap b t e).view = .union (sortedBranches (xs.map (nmap b t))) := by
  obtain ⟨hmem, hs, rfl⟩ := h.view_union hv
  have hone : ∀ x ∈ xs, orBranches (normB b (tf t x)) = [nmap b t x] := fun x hx =>
    orBranches_notOr ((hmem x hx).1.notOr_nmap (hmem x hx).2.1 b t)
  have hmk : nmap b t (mkOr xs) = mkOr (sortedBranches (xs.map (nmap b t))) := by
    rw [nmap, tf_mkOr, normB_mkOr, List.flatMap_map, List.flatMap_congr hone, flatMap_single]
  rw [hmk]
  have hall : ∀ y ∈ sortedBranches (xs.map (nmap b t)), NotOr y := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (mem_sortedBranches.1 hy).1
    exact (hmem x hx).1.notOr_nmap (hmem x hx).2.1 b t
  match xs, hmem, hs, hv, hall with
  | [], _, _, _, _ =>
    have h0 : sortedBranches [] = [] :=
      List.eq_nil_iff_forall_not_mem.2 fun z hz => by simp [mem_sortedBranches] at hz
    simp [h0, mkOr, RelOf.view]
  | [x], hmem, _, hv, _ =>
    have hx := (hmem x (by simp)).2.1
    exfalso
    cases x with
    | or a c => exact hx a c rfl
    | conv y => cases y <;> simp [mkOr, RelOf.view] at hv
    | _ => simp [mkOr, RelOf.view] at hv
  | x :: y :: rest, hmem, hs, _, hall =>
    refine view_mkOr ?_ hall
    have hxy : x ≠ y := ((List.pairwise_cons.1 hs).1 y (by simp)).2
    refine two_le_length_of_mem (a := nmap b t x) (c := nmap b t y) ?_ ?_ ?_
    · exact mem_sortedBranches.2 ⟨by simp, (hmem x (by simp)).1.nmap_ne_zero (hmem x (by simp)).2.2 b t⟩
    · exact mem_sortedBranches.2 ⟨by simp, (hmem y (by simp)).1.nmap_ne_zero (hmem y (by simp)).2.2 b t⟩
    · exact fun e => hxy ((hmem x (by simp)).1.nmap_inj (hmem y (by simp)).1 e)

/-! ## Stretches, meets without a member, and bodies -/

theorem ite_of_pos {α : Type} {c : Prop} [Decidable c] {x y : α} (h : c) :
    (if c then x else y) = x := by simp [h]

theorem drop_take_reverse {α : Type} (l : List α) {i j : Nat} (hij : i < j) (hj : j ≤ l.length) :
    (l.reverse.take j).drop i = ((l.take (l.length - i)).drop (l.length - j)).reverse := by
  rw [List.take_reverse, List.drop_reverse, List.drop_take, List.length_drop]
  congr 2
  omega

/-- The stretch of a mapped chain is the mapped stretch, counted from the
other end when the converse is taken. -/
theorem Normal.nmap_interval {e : Rel} (h : Normal e) (b t : Bool) {i j : Nat} (hij : i < j)
    (hj : j ≤ (seqParts e).length) :
    (nmap b t e).interval i j =
      (e.interval (if b then (seqParts e).length - j else i)
        (if b then (seqParts e).length - i else j)).map (nmap b t) := by
  have hlen : (seqParts (nmap b t e)).length = (seqParts e).length := by
    rw [h.seqParts_nmap]; cases b <;> simp
  have hin : ∀ x ∈ seqParts e, Normal x ∧ NotSeq x := fun x hx =>
    ⟨h.of_mem_seqParts hx, notSeq_of_mem_seqParts hx⟩
  unfold RelOf.interval RelOf.chainParts
  rw [ite_of_pos ⟨hij, by rw [hlen]; exact hj⟩, h.seqParts_nmap]
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [ite_of_pos ⟨hij, hj⟩, Option.map_some, nmap_mkSeq false t]
    · simp [List.map_take, List.map_drop]
    · intro hnil
      have := congrArg List.length hnil
      simp only [List.length_drop, List.length_take, List.length_nil] at this
      omega
    · exact fun x hx => hin x (List.mem_of_mem_take (List.mem_of_mem_drop hx))
  · simp only [ite_true]
    rw [ite_of_pos ⟨by omega, by omega⟩, Option.map_some, nmap_mkSeq true t]
    · simp only [ite_true]
      rw [← drop_take_reverse (seqParts e) hij hj]
      simp [List.map_take, List.map_drop]
    · intro hnil
      have := congrArg List.length hnil
      simp only [List.length_drop, List.length_take, List.length_nil] at this
      omega
    · exact fun x hx => hin x (List.mem_of_mem_take (List.mem_of_mem_drop hx))

theorem cons_eraseIdx_perm {α : Type} : ∀ (l : List α) (i : Nat) (v : α), l[i]? = some v →
    (v :: l.eraseIdx i).Perm l
  | [], _, _, h => by simp at h
  | a :: l, 0, v, h => by
    obtain rfl : a = v := by simpa using h
    simp
  | a :: l, i + 1, v, h => by
    have := cons_eraseIdx_perm l i v (by simpa using h)
    simp only [List.eraseIdx_cons_succ]
    exact (List.Perm.swap a v _).trans (this.cons a)

theorem perm_eraseIdx {α : Type} {l l' : List α} (h : l.Perm l') {i j : Nat} {v : α}
    (hj : l[j]? = some v) (hi : l'[i]? = some v) : (l.eraseIdx j).Perm (l'.eraseIdx i) :=
  List.Perm.cons_inv (((cons_eraseIdx_perm l j v hj).trans h).trans
    (cons_eraseIdx_perm l' i v hi).symm)

/-- A mapped meet without a member is the mapped meet without the member it
is the map of. -/
theorem Normal.nmap_without {e : Rel} (h : Normal e) (b t : Bool) {i j : Nat} {x : Rel}
    (h2 : 2 ≤ (andParts e).length) (hi : (andParts e)[i]? = some x)
    (hj : (andParts (nmap b t e))[j]? = some (nmap b t x)) :
    (nmap b t e).without j = (e.without i).map (nmap b t) := by
  have hperm : (andParts (nmap b t e)).Perm ((andParts e).map (nmap b t)) := by
    rw [h.andParts_nmap]; exact sortedParts_perm _
  have hin : ∀ x ∈ andParts e, Normal x ∧ NotAnd x := fun x hx =>
    ⟨h.of_mem_andParts hx, notAnd_of_mem_andParts hx⟩
  have hilt : i < (andParts e).length := (List.getElem?_eq_some_iff.1 hi).1
  have hjlt : j < (andParts (nmap b t e)).length := (List.getElem?_eq_some_iff.1 hj).1
  unfold RelOf.without RelOf.meetParts
  rw [ite_of_pos ⟨hjlt, by rw [hperm.length_eq, List.length_map]; exact h2⟩,
    ite_of_pos ⟨hilt, h2⟩,
    Option.map_some, nmap_mkAnd b t]
  · congr 2
    refine eq_of_perm_of_sorted ?_
      ((normal_nmap b t e).sorted_andParts.sublist (List.eraseIdx_sublist _ _))
      (pairwise_sortedParts _)
    refine (perm_eraseIdx hperm hj (i := i) (by simp [hi])).trans ?_
    rw [← List.eraseIdx_map]
    exact (sortedParts_perm _).symm
  · intro hnil
    have := congrArg List.length hnil
    rw [List.length_eraseIdx_of_lt hilt, List.length_nil] at this
    omega
  · exact fun y hy => hin y (List.mem_of_mem_eraseIdx hy)
  · exact h.sorted_andParts.sublist (List.eraseIdx_sublist _ _)

/-- The body a mapped call node reads, in the mirrored program when the calls
are flipped, is the mapped body. -/
theorem Normal.bodyOf_nmap {e : Rel} (h : Normal e) (P : Program) (b t : Bool) :
    Charged.bodyOf (if t then P.dual else P) (nmap b t e) =
      (Charged.bodyOf P e).map (nmap b t) := by
  have hbody : ∀ (n : Name) (c : Bool),
      normB c ((if t then P.dual else P).body n) = normB (c ^^ t) (tf t (P.body n)) := by
    intro n c
    cases t
    · simp [tf]
    · simp only [ite_true, ProgramOf.dual_body, normB_dual, tf, Bool.xor_true]
  cases e with
  | call n =>
    rw [nmap_call]
    simp only [Charged.bodyOf, Option.map_some, RelOf.norm, nmap_normB]
    cases hbt : b ^^ t
    · simp only [Bool.false_eq_true, ite_false, hbody]
      cases b <;> cases t <;> simp_all
    · simp only [ite_true, RelOf.normConv, hbody]
      cases b <;> cases t <;> simp_all
  | conv x =>
    obtain ⟨n, rfl⟩ := normal_conv.1 h
    rw [nmap_conv_call]
    simp only [Charged.bodyOf, Option.map_some, RelOf.normConv, nmap_normB]
    cases hbt : b ^^ t
    · simp only [Bool.false_eq_true, ite_false, hbody]
      cases b <;> cases t <;> simp_all
    · simp only [ite_true, RelOf.norm, hbody]
      cases b <;> cases t <;> simp_all
  | zero => rw [nmap_zero]; rfl
  | span s => rw [nmap_span]; rfl
  | seq x y =>
    obtain ⟨a', c', h'⟩ := nmap_seq_isSeq b t x y
    rw [h']; rfl
  | and x y =>
    obtain ⟨a', c', h'⟩ := nmap_and_isAnd b t x y
    rw [h']; rfl
  | or x y =>
    cases hb : Charged.bodyOf (if t then P.dual else P) (nmap b t (.or x y)) with
    | none => rfl
    | some m =>
      exfalso
      have hcall : ∃ n, nmap b t (.or x y) = .call n ∨ nmap b t (.or x y) = .conv (.call n) := by
        generalize nmap b t (.or x y) = z at hb
        unfold Charged.bodyOf at hb
        split at hb
        · exact ⟨_, .inl rfl⟩
        · exact ⟨_, .inr rfl⟩
        · cases hb
      obtain ⟨n, hc | hc⟩ := hcall
      · have := h.nmap_nmap b t
        rw [hc, nmap_call] at this
        split at this <;> cases this
      · have := h.nmap_nmap b t
        rw [hc, nmap_conv_call] at this
        split at this <;> cases this

end RwLog
