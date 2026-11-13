/-
# The derivation kernel: what an answer is, and the rules that make one

Everything here is for a constraint domain `D` on a type `R` of
representatives (`Trusted/Domain.lean`).

A *goal* `⟨lb, node, rb⟩` is a node of the normal form
(`Kernel/NormalForm.lean`) between two optional boundaries. A boundary is a
representative that passes `D.isBound`; no boundary is the identity. The goal
stands for the relation `lb ; node ; rb`.

`Valid D P g a` says the representative `a` is an answer of the goal `g` in
the program `P`: its boundaries are boundaries, and, the domain being lawful
in the interpretation of the sorts of `P`, there is a derivable span `s` of
the node (`Derives`) such that `a` relates exactly the pairs of
`lb ; s ; rb`. So an answer is never less general than its derivation.

The rules below are the only ways the kernel makes an answer
(`Trusted/Kernel.lean`). Each is proved to keep `Valid`, from the laws of the
domain alone:

* `Valid.leaf`: the representative of a span node, composed with the
  boundaries;
* `Valid.join`: two answers of adjacent stretches of a chain, composed. The
  inner boundaries are absent, or one of them is the interface of the other
  answer (a push), the same representative. The answer is for the chain of
  the members of both, so the grouping of `;` is not part of a derivation;
* `Valid.meet`: two answers of two parts of a meet, conjoined. Both have the
  boundaries of the goal, or the second has the interfaces of the first;
* `Valid.inj`: an answer of a member of a union is an answer of the union;
* `Valid.unfold`, `Valid.unfoldConv`: an answer of the normal form of a body,
  or of its converse, is an answer of the call;
* `Valid.swap`: the converse of an answer, which is the converse of the
  representative, is an answer of the converse node between the exchanged
  boundaries.

`Valid.sound` and `Valid.general` are what an answer of the root goal
`⟨none, q.norm, none⟩` gives for the query `q` as written: it relates only
pairs `q` relates, and exactly the pairs of a derivable span of `q`.
-/
import RwLog.Kernel.NormalFormCorrect
import RwLog.SpanLayer.Modulo
import RwLog.Trusted.Domain

namespace RwLog

open Answer

/-! ## Goals -/

/-- The goal `lb ; node ; rb`, with boundaries of type `R`. -/
structure Goal (R : Type) where
  lb : Option R
  node : Rel
  rb : Option R
  deriving DecidableEq

section

variable {R : Type} [Answer R]

/-- The pairs of a boundary: no boundary is the identity. -/
def bdenAt (M : Interp) : Option R → PRel
  | none => {p | p.2 = p.1}
  | some b => den M b

/-- The pairs of `lb ; X ; rb`. -/
def wrapAt (M : Interp) (lb : Option R) (X : PRel) (rb : Option R) : PRel :=
  (bdenAt M lb).comp (X.comp (bdenAt M rb))

/-- An optional boundary passes the domain's test. -/
def IsBound (D : Domain R) (b : Option R) : Prop := ∀ r, b = some r → D.isBound r = true

instance (D : Domain R) (b : Option R) : Decidable (IsBound D b) :=
  match b with
  | none => .isTrue (fun _ h => by cases h)
  | some r => if h : D.isBound r = true then .isTrue (fun _ e => by cases e; exact h)
      else .isFalse (fun k => h (k r rfl))

omit [Answer R] in
theorem isBound_none (D : Domain R) : IsBound D none := fun _ h => by cases h

/-- The goal's boundaries are boundaries. -/
def Goal.Wf (D : Domain R) (g : Goal R) : Prop := IsBound D g.lb ∧ IsBound D g.rb

/-- The representative `a` is an answer of the goal `g`. -/
def Valid (D : Domain R) (P : Program) (g : Goal R) (a : R) : Prop :=
  g.Wf D ∧ (D.Lawful P.sorts.interp → ∃ s, Derives P g.node s ∧
    den P.sorts.interp a = wrapAt P.sorts.interp g.lb (s.den.at P.sorts.interp) g.rb)

/-! ## Pairs of wrapped relations -/

variable {D : Domain R} {M : Interp}

theorem mem_wrapAt {lb rb : Option R} {X : PRel} {x z : GTerm} :
    (x, z) ∈ wrapAt M lb X rb ↔
      ∃ u v, (x, u) ∈ bdenAt M lb ∧ (u, v) ∈ X ∧ (v, z) ∈ bdenAt M rb := by
  constructor
  · rintro ⟨u, h₁, v, h₂, h₃⟩; exact ⟨u, v, h₁, h₂, h₃⟩
  · rintro ⟨u, v, h₁, h₂, h₃⟩; exact ⟨u, h₁, v, h₂, h₃⟩

theorem mem_bden_none {x y : GTerm} : (x, y) ∈ bdenAt M (none : Option R) ↔ y = x := Iff.rfl

/-- A boundary relates a term only to itself. -/
theorem bden_eq (hL : D.Lawful M) {b : Option R} (hb : IsBound D b) {x y : GTerm}
    (h : (x, y) ∈ bdenAt M b) : y = x := by
  cases b with
  | none => exact h
  | some r => exact hL.isBound_sub r (hb r rfl) _ h

theorem wrapAt_none (X : PRel) : wrapAt M (none : Option R) X none = X := by
  ext ⟨x, z⟩
  rw [mem_wrapAt]
  constructor
  · rintro ⟨u, v, h₁, h₂, h₃⟩
    obtain rfl := mem_bden_none.1 h₁
    obtain rfl := mem_bden_none.1 h₃
    exact h₂
  · intro h; exact ⟨x, z, rfl, h, rfl⟩

theorem wrapAt_mid_nonempty {lb rb : Option R} {X : PRel} (h : (wrapAt M lb X rb).Nonempty) :
    X.Nonempty := by
  obtain ⟨⟨x, z⟩, hp⟩ := h
  obtain ⟨u, v, -, h₂, -⟩ := mem_wrapAt.1 hp
  exact ⟨_, h₂⟩

theorem wrapAt_inv (hL : D.Lawful M) {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb)
    (X : PRel) : (wrapAt M lb X rb).inv = wrapAt M rb X.inv lb := by
  ext ⟨x, z⟩
  show (z, x) ∈ wrapAt M lb X rb ↔ _
  rw [mem_wrapAt, mem_wrapAt]
  constructor
  · rintro ⟨u, v, h₁, h₂, h₃⟩
    obtain rfl := bden_eq hL hl h₁
    obtain rfl := bden_eq hL hr h₃
    exact ⟨_, _, h₃, h₂, h₁⟩
  · rintro ⟨u, v, h₁, h₂, h₃⟩
    obtain rfl := bden_eq hL hr h₁
    obtain rfl := bden_eq hL hl h₃
    exact ⟨_, _, h₃, h₂, h₁⟩

/-- A pair of a representative has its right end in the right interface. -/
theorem rightBound_at (hL : D.Lawful M) {a : R} {x y : GTerm} (h : (x, y) ∈ den M a) :
    (y, y) ∈ bdenAt M (D.rightBound a) := by
  cases hb : D.rightBound a with
  | none => rfl
  | some b => exact hL.rightBound_mem a b hb x y h

/-- A pair of a representative has its left end in the left interface. -/
theorem leftBound_at (hL : D.Lawful M) {a : R} {x y : GTerm} (h : (x, y) ∈ den M a) :
    (x, x) ∈ bdenAt M (D.leftBound a) :=
  rightBound_at hL (a := swap a) (x := y) (by rw [den_swap]; exact h)

/-- A relation of derivations that relates a pair is the relation of a
derivable span. -/
theorem exists_derives {P : Program} {e : Rel} {G : GRel} (hG : G ∈ GD P e)
    (hne : (G.at M).Nonempty) : ∃ s, Derives P e s ∧ s.den = G := by
  obtain ⟨p, S, hS, -⟩ := hne
  exact derives_iff_derivesG.2 ⟨hG, ⟨_, hS⟩⟩

/-! ## The rules -/

variable {P : Program}

/-- The representative a goal `⟨lb, s, rb⟩` on a span node composes to, if
any. -/
def spanBoth (D : Domain R) (lb : Option R) (s : Span) (rb : Option R) : Option R :=
  (D.rep s).bind fun r =>
    (match lb with
      | none => some r
      | some l => D.compose l r).bind fun x => match rb with
        | none => some x
        | some t => D.compose x t

theorem spanBoth_den (hL : D.Lawful M) {lb rb : Option R} {s : Span} {z : R}
    (h : spanBoth D lb s rb = some z) : den M z = wrapAt M lb (s.den.at M) rb := by
  unfold spanBoth at h
  cases hr : D.rep s with
  | none => rw [hr] at h; cases h
  | some r =>
    rw [hr] at h
    have er : den M r = s.den.at M := by rw [hL.rep_some s r hr, Span.denAt_eq]
    simp only [Option.bind_some] at h
    have key : ∀ (x : R) (X : PRel), den M x = X → ∀ z, (match rb with
        | none => some x
        | some t => D.compose x t) = some z → den M z = X.comp (bdenAt M rb) := by
      intro x X ex z hz
      cases rb with
      | none =>
        cases hz
        rw [ex]; ext ⟨p, q⟩
        constructor
        · intro hp; exact ⟨q, hp, rfl⟩
        · rintro ⟨m, hp, hm⟩; obtain rfl := mem_bden_none.1 hm; exact hp
      | some t => rw [hL.compose_some _ _ _ hz, ex]; rfl
    cases lb with
    | none =>
      simp only [Option.bind_some] at h
      rw [key r _ er z h]
      ext ⟨p, q⟩
      constructor
      · intro hp; exact ⟨p, rfl, hp⟩
      · rintro ⟨m, hm, hp⟩; obtain rfl := mem_bden_none.1 hm; exact hp
    | some l =>
      simp only at h
      cases hl : D.compose l r with
      | none => rw [hl] at h; cases h
      | some x =>
        rw [hl] at h
        simp only [Option.bind_some] at h
        rw [key x _ (by rw [hL.compose_some _ _ _ hl, er]) z h]
        ext ⟨p, q⟩
        constructor
        · rintro ⟨m, ⟨u, h₁, h₂⟩, h₃⟩; exact ⟨u, h₁, m, h₂, h₃⟩
        · rintro ⟨u, h₁, m, h₂, h₃⟩; exact ⟨m, ⟨u, h₁, h₂⟩, h₃⟩

/-- The representative of a span node, composed with the boundaries. -/
theorem Valid.leaf {lb rb : Option R} {s : Span} {z : R} (hl : IsBound D lb) (hr : IsBound D rb)
    (h : spanBoth D lb s rb = some z) : Valid D P ⟨lb, .span s, rb⟩ z :=
  ⟨⟨hl, hr⟩, fun hL => ⟨s, .span s, spanBoth_den hL h⟩⟩

/-- The side condition of `join`: the inner boundaries are absent, or one of
them is the interface of the other answer. -/
def JoinOk (D : Domain R) (a : R) (rb₁ lb₂ : Option R) (b : R) : Prop :=
  (rb₁ = none ∧ (lb₂ = none ∨ lb₂ = D.rightBound a)) ∨ (lb₂ = none ∧ rb₁ = D.leftBound b)

instance [DecidableEq R] (D : Domain R) (a : R) (rb₁ lb₂ : Option R) (b : R) :
    Decidable (JoinOk D a rb₁ lb₂ b) := by
  unfold JoinOk; infer_instance

/-- Two answers of adjacent stretches of a chain, composed. -/
theorem Valid.join {lb rb₁ lb₂ rb : Option R} {x y : Rel} {a b c : R}
    (ha : Valid D P ⟨lb, x, rb₁⟩ a) (hb : Valid D P ⟨lb₂, y, rb⟩ b)
    (hok : JoinOk D a rb₁ lb₂ b) (hc : D.compose a b = some c) :
    Valid D P ⟨lb, mkSeq (seqParts x ++ seqParts y), rb⟩ c := by
  refine ⟨⟨ha.1.1, hb.1.2⟩, fun hL => ?_⟩
  obtain ⟨s₁, hd₁, e₁⟩ := ha.2 hL
  obtain ⟨s₂, hd₂, e₂⟩ := hb.2 hL
  have hB₁ : IsBound D rb₁ := ha.1.2
  have hB₂ : IsBound D lb₂ := hb.1.1
  simp only at e₁ e₂
  have key : den P.sorts.interp c =
      wrapAt P.sorts.interp lb ((s₁.den.comp s₂.den).at P.sorts.interp) rb := by
    rw [hL.compose_some _ _ _ hc, at_comp]
    ext ⟨p, q⟩
    constructor
    · rintro ⟨m, h₁, h₂⟩
      rw [e₁] at h₁; rw [e₂] at h₂
      obtain ⟨u, v, p₁, p₂, p₃⟩ := mem_wrapAt.1 h₁
      obtain ⟨u', v', q₁, q₂, q₃⟩ := mem_wrapAt.1 h₂
      obtain rfl := bden_eq hL hB₁ p₃
      obtain rfl := bden_eq hL hB₂ q₁
      exact mem_wrapAt.2 ⟨u, v', p₁, ⟨_, p₂, q₂⟩, q₃⟩
    · intro h
      obtain ⟨u, v, p₁, ⟨m, p₂, p₂'⟩, p₃⟩ := mem_wrapAt.1 h
      rcases hok with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨m, by rw [e₁]; exact mem_wrapAt.2 ⟨u, m, p₁, p₂, rfl⟩,
          by rw [e₂]; exact mem_wrapAt.2 ⟨m, v, rfl, p₂', p₃⟩⟩
      · have hxm : (p, m) ∈ den P.sorts.interp a := by
          rw [e₁]; exact mem_wrapAt.2 ⟨u, m, p₁, p₂, rfl⟩
        exact ⟨m, hxm, by rw [e₂]; exact mem_wrapAt.2 ⟨m, v, rightBound_at hL hxm, p₂', p₃⟩⟩
      · have hmz : (m, q) ∈ den P.sorts.interp b := by
          rw [e₂]; exact mem_wrapAt.2 ⟨m, v, rfl, p₂', p₃⟩
        exact ⟨m, by rw [e₁]; exact mem_wrapAt.2 ⟨u, m, p₁, p₂, leftBound_at hL hmz⟩, hmz⟩
  have hG : s₁.den.comp s₂.den ∈ GD P (mkSeq (seqParts x ++ seqParts y)) := by
    rw [gd_mkSeq_append]; exact ⟨_, hd₁.derivesG, _, hd₂.derivesG, rfl⟩
  obtain ⟨s, hs, hsd⟩ := exists_derives hG (wrapAt_mid_nonempty (key ▸ hL.live c))
  exact ⟨s, hs, hsd ▸ key⟩

/-- The side condition of `meet`: the second answer has the boundaries of the
first, or the interfaces of the first answer. -/
def MeetOk (D : Domain R) (a : R) (lb rb lb' rb' : Option R) : Prop :=
  (lb' = lb ∧ rb' = rb) ∨ (lb' = D.leftBound a ∧ rb' = D.rightBound a)

instance [DecidableEq R] (D : Domain R) (a : R) (lb rb lb' rb' : Option R) :
    Decidable (MeetOk D a lb rb lb' rb') := by
  unfold MeetOk; infer_instance

/-- Two answers of two parts of a meet, conjoined. -/
theorem Valid.meet {lb rb lb' rb' : Option R} {x y : Rel} {a b c : R}
    (ha : Valid D P ⟨lb, x, rb⟩ a) (hb : Valid D P ⟨lb', y, rb'⟩ b)
    (hok : MeetOk D a lb rb lb' rb') (hc : D.meet a b = some c) :
    Valid D P ⟨lb, mkAnd (sortedParts (andParts x ++ andParts y)), rb⟩ c := by
  refine ⟨ha.1, fun hL => ?_⟩
  obtain ⟨s₁, hd₁, e₁⟩ := ha.2 hL
  obtain ⟨s₂, hd₂, e₂⟩ := hb.2 hL
  have hl : IsBound D lb := ha.1.1
  have hr : IsBound D rb := ha.1.2
  have hl' : IsBound D lb' := hb.1.1
  have hr' : IsBound D rb' := hb.1.2
  simp only at e₁ e₂
  have key : den P.sorts.interp c =
      wrapAt P.sorts.interp lb ((s₁.den.meet s₂.den).at P.sorts.interp) rb := by
    rw [hL.meet_some _ _ _ hc, at_meet]
    ext ⟨p, q⟩
    constructor
    · rintro ⟨h₁, h₂⟩
      rw [e₁] at h₁; rw [e₂] at h₂
      obtain ⟨u, v, p₁, p₂, p₃⟩ := mem_wrapAt.1 h₁
      obtain ⟨u', v', q₁, q₂, q₃⟩ := mem_wrapAt.1 h₂
      obtain rfl := bden_eq hL hl p₁
      obtain rfl := bden_eq hL hr p₃
      obtain rfl := bden_eq hL hl' q₁
      obtain rfl := bden_eq hL hr' q₃
      exact mem_wrapAt.2 ⟨_, _, p₁, ⟨p₂, q₂⟩, p₃⟩
    · intro h
      obtain ⟨u, v, p₁, ⟨p₂, p₂'⟩, p₃⟩ := mem_wrapAt.1 h
      obtain rfl := bden_eq hL hl p₁
      obtain rfl := bden_eq hL hr p₃
      have hxa := mem_wrapAt.2 ⟨_, _, p₁, p₂, p₃⟩
      rw [← e₁] at hxa
      refine ⟨hxa, ?_⟩
      rw [e₂]
      rcases hok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact mem_wrapAt.2 ⟨_, _, p₁, p₂', p₃⟩
      · exact mem_wrapAt.2 ⟨_, _, leftBound_at hL hxa, p₂', rightBound_at hL hxa⟩
  have hG : s₁.den.meet s₂.den ∈ GD P (mkAnd (sortedParts (andParts x ++ andParts y))) := by
    rw [gd_mkAnd_sorted_append]; exact ⟨_, hd₁.derivesG, _, hd₂.derivesG, rfl⟩
  obtain ⟨s, hs, hsd⟩ := exists_derives hG (wrapAt_mid_nonempty (key ▸ hL.live c))
  exact ⟨s, hs, hsd ▸ key⟩

/-- An answer stays one when the node is replaced by a node that derives the
same ground relation. -/
theorem Valid.move {lb rb : Option R} {x y : Rel} {a : R} (h : Valid D P ⟨lb, x, rb⟩ a)
    (hxy : ∀ s, Derives P x s → s.den ∈ GD P y) : Valid D P ⟨lb, y, rb⟩ a := by
  refine ⟨h.1, fun hL => ?_⟩
  obtain ⟨s, hd, hr⟩ := h.2 hL
  obtain ⟨s', hs', hsd⟩ := derives_iff_derivesG.2 ⟨hxy s hd, s.den_nonempty⟩
  exact ⟨s', hs', hsd ▸ hr⟩

/-- An answer of a member of a union is an answer of the union. -/
theorem Valid.inj {lb rb : Option R} {x u : Rel} {a : R} (h : Valid D P ⟨lb, x, rb⟩ a)
    (hx : x ∈ u.unionParts) : Valid D P ⟨lb, u, rb⟩ a :=
  h.move fun s hs => by
    rw [← gd_unionParts]
    exact Set.mem_biUnion hx hs.derivesG

/-- An answer of the normal form of a body is an answer of the call. -/
theorem Valid.unfold {lb rb : Option R} {n : Name} {a : R}
    (h : Valid D P ⟨lb, (P.body n).norm, rb⟩ a) : Valid D P ⟨lb, .call n, rb⟩ a :=
  h.move fun s hs => by
    rw [gd_call, ← gd_norm]; exact hs.derivesG

/-- An answer of the normal form of the converse of a body is an answer of
the converse of the call. -/
theorem Valid.unfoldConv {lb rb : Option R} {n : Name} {a : R}
    (h : Valid D P ⟨lb, (P.body n).normConv, rb⟩ a) : Valid D P ⟨lb, .conv (.call n), rb⟩ a :=
  h.move fun s hs => by
    rw [gd_conv, gd_call, ← gd_normConv]; exact hs.derivesG

/-- The converse of an answer is an answer of the converse node between the
exchanged boundaries. -/
theorem Valid.swap {lb rb : Option R} {x : Rel} {a : R} (h : Valid D P ⟨lb, x, rb⟩ a) :
    Valid D P ⟨rb, x.normConv, lb⟩ (swap a) := by
  refine ⟨⟨h.1.2, h.1.1⟩, fun hL => ?_⟩
  obtain ⟨s, hd, hr⟩ := h.2 hL
  have hG : s.swap.den ∈ GD P x.normConv := by
    rw [gd_normConv, swap_den]; exact ⟨_, hd.derivesG, rfl⟩
  obtain ⟨s', hs', hsd⟩ := derives_iff_derivesG.2 ⟨hG, s.swap.den_nonempty⟩
  refine ⟨s', hs', ?_⟩
  simp only at hr ⊢
  rw [den_swap, hr, wrapAt_inv hL h.1.1 h.1.2, hsd, swap_den, at_inv]

/-! ## What an answer of the root goal gives -/

/-- An answer of the root goal relates exactly the pairs of a derivable span
of the query as written. -/
theorem Valid.general {q : Rel} {a : R} (h : Valid D P ⟨none, q.norm, none⟩ a)
    (hL : D.Lawful P.sorts.interp) :
    ∃ s, Derives P q s ∧ Answer.Refines P.sorts.interp a s := by
  obtain ⟨s₀, hd, hr⟩ := h.2 hL
  obtain ⟨s, hs, hsd⟩ := derives_norm_iff.1 ⟨s₀, hd, rfl⟩
  refine ⟨s, hs, ?_⟩
  simp only [wrapAt_none] at hr
  show den P.sorts.interp a = s.denAt P.sorts.interp
  rw [hr, Span.denAt_eq, hsd]

/-- An answer of the root goal relates only pairs the query relates. -/
theorem Valid.sound {q : Rel} {a : R} (h : Valid D P ⟨none, q.norm, none⟩ a)
    (hL : D.Lawful P.sorts.interp) : den P.sorts.interp a ⊆ P.pairs q := by
  obtain ⟨s, hs, hr⟩ := h.general hL
  have hr' : den P.sorts.interp a = s.denAt P.sorts.interp := hr
  rw [hr', Span.denAt_eq]
  unfold ProgramOf.pairs
  rw [ProgramOf.semAt_eq]
  exact GRel.at_mono hs.den_subset _

end

end RwLog
