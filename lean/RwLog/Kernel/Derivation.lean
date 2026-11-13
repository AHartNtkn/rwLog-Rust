/-
# The derivation kernel: what an answer is, and the rules that make one

A *goal* `⟨lb, node, rb⟩` is a node of the normal form
(`Kernel/NormalForm.lean`) between two optional boundaries. A boundary is an
interface span `p {c} -> p`; no boundary is the identity. The goal stands for
the relation `lb ; node ; rb`.

`Valid P g a` says the span `a` is an answer of the goal `g` in the program
`P`: there is a derivable span `s` of the node (`Derives`) such that `a`
stands for `lb ; s ; rb` (`Ref`): `a` relates only pairs of it, and in every
model of the theory exactly its pairs. So an answer is never less general
than its derivation.

The rules below are the only ways the kernel makes an answer
(`Trusted/Kernel.lean`). Each is proved to keep `Valid`:

* `Valid.leaf`: a span node, composed with the boundaries;
* `Valid.simp`: an answer simplified by the theory;
* `Valid.join`: two answers of adjacent stretches of a chain, composed. The
  inner boundaries are absent, or one of them is the interface of the other
  answer (a push). The answer is for the chain of the members of both, so
  the grouping of `;` is not part of a derivation;
* `Valid.meet`: two answers of two parts of a meet, conjoined. Both have the
  boundaries of the goal, or the second has the interfaces of the first;
* `Valid.inj`: an answer of a member of a union is an answer of the union;
* `Valid.unfold`, `Valid.unfoldConv`: an answer of the normal form of a body,
  or of its converse, is an answer of the call;
* `Valid.swap`: the converse of an answer is an answer of the converse node
  between the exchanged boundaries.

`Valid.sound` and `Valid.general` are what an answer of the root goal
`⟨none, q.norm, none⟩` gives for the query `q` as written: it relates only
pairs `q` relates, and it stands for a derivable span of `q`.
-/
import RwLog.Kernel.NormalFormCorrect
import RwLog.Kernel.Live
import RwLog.Kernel.Iface

namespace RwLog

/-! ## Goals -/

/-- The goal `lb ; node ; rb`. -/
structure Goal where
  lb : Option Span
  node : Rel
  rb : Option Span
  deriving DecidableEq, Repr

/-- An optional boundary is an interface span: its two sides are the same
pattern. -/
def IsBound (b : Option Span) : Prop := ∀ s, b = some s → s.l = s.r

instance (b : Option Span) : Decidable (IsBound b) :=
  match b with
  | none => .isTrue (fun _ h => by cases h)
  | some s => if h : s.l = s.r then .isTrue (fun _ e => by cases e; exact h)
      else .isFalse (fun k => h (k s rfl))

/-- The meaning of a boundary: no boundary is the identity. -/
def bden : Option Span → GRel
  | none => GRel.id
  | some s => s.den

theorem isBound_none : IsBound none := fun _ h => by cases h

theorem pid_bden {b : Option Span} (h : IsBound b) : PId (bden b) := by
  cases b with
  | none => exact pid_id
  | some s => exact pid_diag (h s rfl)

theorem GRel.inv_id : GRel.id.inv = GRel.id := by
  ext ⟨a, b, X⟩
  simp only [GRel.inv, GRel.id, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂⟩

theorem bden_inv {b : Option Span} (h : IsBound b) : (bden b).inv = bden b := by
  cases b with
  | none => exact GRel.inv_id
  | some s =>
    have hlr := h s rfl
    have : s.swap = s := by cases s; simp only at hlr; subst hlr; rfl
    show s.den.inv = s.den
    rw [← swap_den, this]

/-- An interface taken as a boundary means the interface. -/
theorem bden_bound_rightIface (a : Span) : bden (bound a.rightIface) = a.rightIface.den := by
  unfold bound
  split
  · next v hl hc => exact (den_trivial hl hl hc).symm
  · rfl

theorem bden_bound_leftIface (a : Span) : bden (bound a.leftIface) = a.leftIface.den := by
  unfold bound
  split
  · next v hl hc => exact (den_trivial hl hl hc).symm
  · rfl

theorem isBound_bound_rightIface (a : Span) : IsBound (bound a.rightIface) := by
  intro s h
  unfold bound at h
  split at h
  · cases h
  · cases h; rfl

theorem isBound_bound_leftIface (a : Span) : IsBound (bound a.leftIface) := by
  intro s h
  unfold bound at h
  split at h
  · cases h
  · cases h; rfl

/-! ## Pairs of wrapped relations -/

variable {T : Theory}

theorem at_id (M : Interp) : GRel.id.at M = {p | p.2 = p.1} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨S, h, -⟩; exact h.1
  · intro h; exact ⟨∅, ⟨h, rfl⟩, by simp⟩

theorem mem_at_wrap {L A R : GRel} {M : Interp} {x z : GTerm} :
    (x, z) ∈ (wrap L A R).at M ↔
      ∃ u v, (x, u) ∈ L.at M ∧ (u, v) ∈ A.at M ∧ (v, z) ∈ R.at M := by
  unfold wrap
  rw [at_comp, at_comp]
  constructor
  · rintro ⟨u, h₁, v, h₂, h₃⟩; exact ⟨u, v, h₁, h₂, h₃⟩
  · rintro ⟨u, v, h₁, h₂, h₃⟩; exact ⟨u, h₁, v, h₂, h₃⟩

theorem PId.at_eq {B : GRel} (h : PId B) {M : Interp} {x y : GTerm} (hxy : (x, y) ∈ B.at M) :
    y = x := by
  obtain ⟨S, hS, -⟩ := hxy; exact h _ _ _ hS

theorem mem_at_id {M : Interp} {x y : GTerm} : (x, y) ∈ GRel.id.at M ↔ y = x := by
  rw [at_id]; rfl

/-- A pair of a span has its right end in the right interface. -/
theorem rightIface_at {a : Span} {M : Interp} {x y : GTerm} (h : (x, y) ∈ a.den.at M) :
    (y, y) ∈ a.rightIface.den.at M := by
  rw [← comp_rightIface a, at_comp] at h
  obtain ⟨m, -, hm⟩ := h
  have : y = m := (pid_diag (s := a.rightIface) rfl).at_eq hm
  subst this; exact hm

/-- A pair of a span has its left end in the left interface. -/
theorem leftIface_at {a : Span} {M : Interp} {x y : GTerm} (h : (x, y) ∈ a.den.at M) :
    (x, x) ∈ a.leftIface.den.at M := by
  rw [← leftIface_comp a, at_comp] at h
  obtain ⟨m, hm, -⟩ := h
  have : m = x := (pid_diag (s := a.leftIface) rfl).at_eq hm
  subst this; exact hm

/-- `a` relates only pairs of `X`, in every model of the theory and among all
pairs. -/
def Below (T : Theory) (A X : GRel) : Prop :=
  ∀ M, T.Model M ∨ M = Set.univ → A.at M ⊆ X.at M

theorem ref_iff {a : Span} {X : GRel} : Ref T a X ↔ Below T a.den X ∧ LCov T a.den X := by
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨fun M hM => ?_, h₃⟩
    rcases hM with hM | rfl
    · exact h₁ M hM
    · exact h₂
  · rintro ⟨h₁, h₃⟩
    exact ⟨⟨fun M hM => h₁ M (.inl hM), h₁ _ (.inr rfl)⟩, h₃⟩

/-! ## Valid answers -/

variable (P : Program)

/-- The goal's boundaries are interface spans. -/
def Goal.Wf (g : Goal) : Prop := IsBound g.lb ∧ IsBound g.rb

/-- The span `a` is an answer of the goal `g`. -/
def Valid (g : Goal) (a : Span) : Prop :=
  g.Wf ∧ ((∀ ρ ∈ P.theory, ρ.WellFormed) →
    ∃ s, Derives P g.node s ∧ Ref P.theory a (wrap (bden g.lb) s.den (bden g.rb)))

variable {P}

/-- The span a goal `⟨lb, s, rb⟩` on a span node composes to, if any. -/
def spanBoth (lb : Option Span) (s : Span) (rb : Option Span) : Option Span :=
  (match lb with
    | none => some s
    | some l => l.compose s).bind fun s' => match rb with
      | none => some s'
      | some r => s'.compose r

theorem spanBoth_den {lb rb : Option Span} {s z : Span} (h : spanBoth lb s rb = some z) :
    z.den = wrap (bden lb) s.den (bden rb) := by
  unfold spanBoth at h
  unfold wrap
  cases lb with
  | none =>
    cases rb with
    | none =>
      simp only [Option.bind_some, Option.some.injEq] at h
      subst h; simp [bden, GRel.id_comp, GRel.comp_id]
    | some r =>
      simp only [Option.bind_some] at h
      rw [compose_some h]; simp [bden, GRel.id_comp]
  | some l =>
    simp only at h
    cases hl : l.compose s with
    | none => rw [hl] at h; cases h
    | some s' =>
      rw [hl] at h
      cases rb with
      | none =>
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h; rw [compose_some hl]; simp [bden, GRel.comp_id]
      | some r =>
        simp only [Option.bind_some] at h
        rw [compose_some h, compose_some hl, GRel.comp_assoc]; rfl

/-- A span node, composed with the boundaries. -/
theorem Valid.leaf {lb rb : Option Span} {s z : Span} (hl : IsBound lb) (hr : IsBound rb)
    (h : spanBoth lb s rb = some z) : Valid P ⟨lb, .span s, rb⟩ z :=
  ⟨⟨hl, hr⟩, fun _ => ⟨s, .span s, (Ref.self z).of_eq (spanBoth_den h)⟩⟩

/-- An answer simplified by the theory. -/
theorem Valid.simp {g : Goal} {a a' : Span} (h : Valid P g a)
    (hs : P.theory.simplify a = some a') : Valid P g a' := by
  refine ⟨h.1, fun hwf => ?_⟩
  obtain ⟨s, hd, hr⟩ := h.2 hwf
  exact ⟨s, hd, (live_ref hwf (by simp [live, hs])).trans hr.1 hr.2⟩

/-- The side condition of `join`: the inner boundaries are absent, or one of
them is the interface of the other answer. -/
def JoinOk (a : Span) (rb₁ lb₂ : Option Span) (b : Span) : Prop :=
  (rb₁ = none ∧ (lb₂ = none ∨ lb₂ = bound a.rightIface)) ∨
    (lb₂ = none ∧ rb₁ = bound b.leftIface)

instance (a : Span) (rb₁ lb₂ : Option Span) (b : Span) : Decidable (JoinOk a rb₁ lb₂ b) := by
  unfold JoinOk; infer_instance

theorem join_ref {a b c : Span} {L S₁ S₂ R B₁ B₂ : GRel}
    (ha : Ref T a (wrap L S₁ B₁)) (hb : Ref T b (wrap B₂ S₂ R)) (hc : a.compose b = some c)
    (hB₁ : PId B₁) (hB₂ : PId B₂)
    (hok : (B₁ = GRel.id ∧ (B₂ = GRel.id ∨ B₂ = a.rightIface.den)) ∨
      (B₂ = GRel.id ∧ B₁ = b.leftIface.den)) :
    Ref T c (wrap L (S₁.comp S₂) R) := by
  obtain ⟨ha₁, ha₂⟩ := ref_iff.1 ha
  obtain ⟨hb₁, hb₂⟩ := ref_iff.1 hb
  rw [ref_iff, compose_some hc]
  constructor
  · intro M hM
    rw [at_comp]
    rintro ⟨x, z⟩ ⟨m, hxm, hmz⟩
    obtain ⟨u, v, h₁, h₂, h₃⟩ := mem_at_wrap.1 (ha₁ M hM hxm)
    obtain ⟨u', v', k₁, k₂, k₃⟩ := mem_at_wrap.1 (hb₁ M hM hmz)
    obtain rfl := hB₁.at_eq h₃
    obtain rfl := hB₂.at_eq k₁
    exact mem_at_wrap.2 ⟨u, v', h₁, (at_comp _ _ _).symm ▸ ⟨_, h₂, k₂⟩, k₃⟩
  · intro M hM
    rw [at_comp]
    rintro ⟨x, z⟩ hxz
    obtain ⟨u, v, h₁, h₂, h₃⟩ := mem_at_wrap.1 hxz
    rw [at_comp] at h₂
    obtain ⟨m, h₂, h₂'⟩ := h₂
    rcases hok with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨m, ha₂ M hM (mem_at_wrap.2 ⟨u, m, h₁, h₂, mem_at_id.2 rfl⟩),
        hb₂ M hM (mem_at_wrap.2 ⟨m, v, mem_at_id.2 rfl, h₂', h₃⟩)⟩
    · have hxm := ha₂ M hM (mem_at_wrap.2 ⟨u, m, h₁, h₂, mem_at_id.2 rfl⟩)
      exact ⟨m, hxm, hb₂ M hM (mem_at_wrap.2 ⟨m, v, rightIface_at hxm, h₂', h₃⟩)⟩
    · have hmz := hb₂ M hM (mem_at_wrap.2 ⟨m, v, mem_at_id.2 rfl, h₂', h₃⟩)
      exact ⟨m, ha₂ M hM (mem_at_wrap.2 ⟨u, m, h₁, h₂, leftIface_at hmz⟩), hmz⟩

theorem wrap_mid_nonempty {L A R : GRel} (h : (wrap L A R).Nonempty) : A.Nonempty :=
  GRel.comp_nonempty_left (GRel.comp_nonempty_right h)

/-- Two answers of adjacent stretches of a chain, composed. -/
theorem Valid.join {lb rb₁ lb₂ rb : Option Span} {x y : Rel} {a b c : Span}
    (ha : Valid P ⟨lb, x, rb₁⟩ a) (hb : Valid P ⟨lb₂, y, rb⟩ b)
    (hok : JoinOk a rb₁ lb₂ b) (hc : a.compose b = some c) :
    Valid P ⟨lb, mkSeq (seqParts x ++ seqParts y), rb⟩ c := by
  refine ⟨⟨ha.1.1, hb.1.2⟩, fun hwf => ?_⟩
  obtain ⟨s₁, hd₁, hr₁⟩ := ha.2 hwf
  obtain ⟨s₂, hd₂, hr₂⟩ := hb.2 hwf
  have hok' : (bden rb₁ = GRel.id ∧ (bden lb₂ = GRel.id ∨ bden lb₂ = a.rightIface.den)) ∨
      (bden lb₂ = GRel.id ∧ bden rb₁ = b.leftIface.den) := by
    rcases hok with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, .inl rfl⟩
    · exact .inl ⟨rfl, .inr (bden_bound_rightIface a)⟩
    · exact .inr ⟨rfl, bden_bound_leftIface b⟩
  have href := join_ref hr₁ hr₂ hc (pid_bden ha.1.2) (pid_bden hb.1.1) hok'
  have hne := wrap_mid_nonempty href.nonempty
  have hG : s₁.den.comp s₂.den ∈ GD P (mkSeq (seqParts x ++ seqParts y)) := by
    rw [gd_mkSeq_append]; exact ⟨_, hd₁.derivesG, _, hd₂.derivesG, rfl⟩
  obtain ⟨s, hs, hsd⟩ := derives_iff_derivesG.2 ⟨hG, hne⟩
  exact ⟨s, hs, hsd ▸ href⟩

/-- The side condition of `meet`: the second answer has the boundaries of the
first, or the interfaces of the first answer. -/
def MeetOk (a : Span) (lb rb lb' rb' : Option Span) : Prop :=
  (lb' = lb ∧ rb' = rb) ∨ (lb' = bound a.leftIface ∧ rb' = bound a.rightIface)

instance (a : Span) (lb rb lb' rb' : Option Span) : Decidable (MeetOk a lb rb lb' rb') := by
  unfold MeetOk; infer_instance

theorem meet_ref {a b c : Span} {L S₁ S₂ R L' R' : GRel}
    (ha : Ref T a (wrap L S₁ R)) (hb : Ref T b (wrap L' S₂ R')) (hc : a.meet b = some c)
    (hL : PId L) (hR : PId R) (hL' : PId L') (hR' : PId R')
    (hok : (L' = L ∧ R' = R) ∨ (L' = a.leftIface.den ∧ R' = a.rightIface.den)) :
    Ref T c (wrap L (S₁.meet S₂) R) := by
  obtain ⟨ha₁, ha₂⟩ := ref_iff.1 ha
  obtain ⟨hb₁, hb₂⟩ := ref_iff.1 hb
  rw [ref_iff, meet_some hc]
  constructor
  · intro M hM
    rw [at_meet]
    rintro ⟨x, z⟩ ⟨hx, hy⟩
    obtain ⟨u, v, h₁, h₂, h₃⟩ := mem_at_wrap.1 (ha₁ M hM hx)
    obtain ⟨u', v', k₁, k₂, k₃⟩ := mem_at_wrap.1 (hb₁ M hM hy)
    obtain rfl := hL.at_eq h₁
    obtain rfl := hR.at_eq h₃
    obtain rfl := hL'.at_eq k₁
    obtain rfl := hR'.at_eq k₃
    exact mem_at_wrap.2 ⟨_, _, h₁, (at_meet _ _ _).symm ▸ ⟨h₂, k₂⟩, h₃⟩
  · intro M hM
    rw [at_meet]
    rintro ⟨x, z⟩ hxz
    obtain ⟨u, v, h₁, h₂, h₃⟩ := mem_at_wrap.1 hxz
    rw [at_meet] at h₂
    obtain rfl := hL.at_eq h₁
    obtain rfl := hR.at_eq h₃
    have hxa := ha₂ M hM (mem_at_wrap.2 ⟨_, _, h₁, h₂.1, h₃⟩)
    refine ⟨hxa, hb₂ M hM ?_⟩
    rcases hok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact mem_at_wrap.2 ⟨_, _, h₁, h₂.2, h₃⟩
    · exact mem_at_wrap.2 ⟨_, _, leftIface_at hxa, h₂.2, rightIface_at hxa⟩

/-- Two answers of two parts of a meet, conjoined. -/
theorem Valid.meet {lb rb lb' rb' : Option Span} {x y : Rel} {a b c : Span}
    (ha : Valid P ⟨lb, x, rb⟩ a) (hb : Valid P ⟨lb', y, rb'⟩ b)
    (hok : MeetOk a lb rb lb' rb') (hc : a.meet b = some c) :
    Valid P ⟨lb, mkAnd (sortedParts (andParts x ++ andParts y)), rb⟩ c := by
  refine ⟨ha.1, fun hwf => ?_⟩
  obtain ⟨s₁, hd₁, hr₁⟩ := ha.2 hwf
  obtain ⟨s₂, hd₂, hr₂⟩ := hb.2 hwf
  have hok' : (bden lb' = bden lb ∧ bden rb' = bden rb) ∨
      (bden lb' = a.leftIface.den ∧ bden rb' = a.rightIface.den) := by
    rcases hok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨bden_bound_leftIface a, bden_bound_rightIface a⟩
  have href := meet_ref hr₁ hr₂ hc (pid_bden ha.1.1) (pid_bden ha.1.2) (pid_bden hb.1.1)
    (pid_bden hb.1.2) hok'
  have hne := wrap_mid_nonempty href.nonempty
  have hG : s₁.den.meet s₂.den ∈ GD P (mkAnd (sortedParts (andParts x ++ andParts y))) := by
    rw [gd_mkAnd_sorted_append]; exact ⟨_, hd₁.derivesG, _, hd₂.derivesG, rfl⟩
  obtain ⟨s, hs, hsd⟩ := derives_iff_derivesG.2 ⟨hG, hne⟩
  exact ⟨s, hs, hsd ▸ href⟩

/-- An answer stays one when the node is replaced by a node that derives the
same ground relation. -/
theorem Valid.move {lb rb : Option Span} {x y : Rel} {a : Span} (h : Valid P ⟨lb, x, rb⟩ a)
    (hxy : ∀ s, Derives P x s → s.den ∈ GD P y) : Valid P ⟨lb, y, rb⟩ a := by
  refine ⟨h.1, fun hwf => ?_⟩
  obtain ⟨s, hd, hr⟩ := h.2 hwf
  obtain ⟨s', hs', hsd⟩ := derives_iff_derivesG.2 ⟨hxy s hd, s.den_nonempty⟩
  exact ⟨s', hs', hsd ▸ hr⟩

/-- An answer of a member of a union is an answer of the union. -/
theorem Valid.inj {lb rb : Option Span} {x u : Rel} {a : Span} (h : Valid P ⟨lb, x, rb⟩ a)
    (hx : x ∈ u.unionParts) : Valid P ⟨lb, u, rb⟩ a :=
  h.move fun s hs => by
    rw [← gd_unionParts]
    exact Set.mem_biUnion hx hs.derivesG

/-- An answer of the normal form of a body is an answer of the call. -/
theorem Valid.unfold {lb rb : Option Span} {n : Name} {a : Span}
    (h : Valid P ⟨lb, (P.body n).norm, rb⟩ a) : Valid P ⟨lb, .call n, rb⟩ a :=
  h.move fun s hs => by
    rw [gd_call, ← gd_norm]; exact hs.derivesG

/-- An answer of the normal form of the converse of a body is an answer of
the converse of the call. -/
theorem Valid.unfoldConv {lb rb : Option Span} {n : Name} {a : Span}
    (h : Valid P ⟨lb, (P.body n).normConv, rb⟩ a) : Valid P ⟨lb, .conv (.call n), rb⟩ a :=
  h.move fun s hs => by
    rw [gd_conv, gd_call, ← gd_normConv]; exact hs.derivesG

theorem wrap_inv (L A R : GRel) : (wrap L A R).inv = wrap R.inv A.inv L.inv := by
  unfold wrap
  rw [GRel.inv_comp, GRel.inv_comp, GRel.comp_assoc]

/-- The converse of an answer is an answer of the converse node between the
exchanged boundaries. -/
theorem Valid.swap {lb rb : Option Span} {x : Rel} {a : Span} (h : Valid P ⟨lb, x, rb⟩ a) :
    Valid P ⟨rb, x.normConv, lb⟩ a.swap := by
  refine ⟨⟨h.1.2, h.1.1⟩, fun hwf => ?_⟩
  obtain ⟨s, hd, hr⟩ := h.2 hwf
  have hG : s.swap.den ∈ GD P x.normConv := by
    rw [gd_normConv, swap_den]; exact ⟨_, hd.derivesG, rfl⟩
  obtain ⟨s', hs', hsd⟩ := derives_iff_derivesG.2 ⟨hG, s.swap.den_nonempty⟩
  refine ⟨s', hs', ?_⟩
  have := hr.swap
  rw [wrap_inv, bden_inv h.1.1, bden_inv h.1.2, ← swap_den, ← hsd] at this
  exact this

/-! ## What an answer of the root goal gives -/

theorem wrap_id (A : GRel) : wrap GRel.id A GRel.id = A := by
  unfold wrap; rw [GRel.comp_id, GRel.id_comp]

/-- An answer of the root goal stands for a derivable span of the query as
written. -/
theorem Valid.general {q : Rel} {a : Span} (h : Valid P ⟨none, q.norm, none⟩ a)
    (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) : ∃ s, Derives P q s ∧ a.Refines P.theory s := by
  obtain ⟨s₀, hd, hr⟩ := h.2 hwf
  obtain ⟨s, hs, hsd⟩ := derives_norm_iff.1 ⟨s₀, hd, rfl⟩
  refine ⟨s, hs, fun M hM => ?_⟩
  have hr' : Ref P.theory a s.den := by
    have := hr; simp only [bden, wrap_id] at this; rw [hsd]; exact this
  rw [Span.denAt_eq, Span.denAt_eq]
  exact le_antisymm (hr'.1.1 M hM) (hr'.2 M hM)

/-- An answer of the root goal relates only pairs the query relates. -/
theorem Valid.sound {q : Rel} {a : Span} (h : Valid P ⟨none, q.norm, none⟩ a)
    (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) (M : Interp) (hM : P.theory.Model M) :
    a.denAt M ⊆ P.semAt M q := by
  obtain ⟨s, hs, hr⟩ := h.general hwf
  rw [hr M hM, Span.denAt_eq, ProgramOf.semAt_eq]
  exact GRel.at_mono hs.den_subset M

end RwLog
