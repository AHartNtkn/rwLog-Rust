/-
# A reading, rule by rule

The reading of the diving engine (`Dive.read`) at a kernel that returns what
a domain returns: what one level of it is in the monad of `Cost`
(`rd_succ`, `jl_cons`), and with that what the reading of a span node, a
call, a union and a chain returns and costs, from what the readings of the
parts return and cost (`Reads`).
-/
import RwLog.Rungs.Dive.Engine
import RwLog.Rungs.Framework.Rules

namespace RwLog

namespace Dive

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  (K : Kernel R Cost) (hK : K.Refines D)

/-- The reading at the derivation kernel of `P`. -/
abbrev rd (d k : Nat) (n : Rel) : Cost (Option (Ans D P) × Nat) :=
  @read R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) d k n

/-- Joining at the derivation kernel of `P`. -/
abbrev jl (ev : Nat → Rel → Cost (Option (Ans D P) × Nat)) (a : Ans D P) (k : Nat)
    (xs : List Rel) : Cost (Option (Ans D P) × Nat) :=
  @joinL R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) ev a k xs

/-- Meeting at the derivation kernel of `P`. -/
abbrev ml (ev : Nat → Rel → Cost (Option (Ans D P) × Nat)) (a : Ans D P) (k : Nat)
    (xs : List Rel) : Cost (Option (Ans D P) × Nat) :=
  @meetL R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) ev a k xs

theorem rd_zero (k : Nat) (n : Rel) : rd (P := P) K hK 0 k n = pure (none, k) := by
  at_cost K hK
  rfl

theorem jl_nil (ev : Nat → Rel → Cost (Option (Ans D P) × Nat)) (a : Ans D P) (k : Nat) :
    jl K hK ev a k [] = pure (some a, k) := by
  at_cost K hK
  rfl

theorem jl_cons (ev : Nat → Rel → Cost (Option (Ans D P) × Nat)) (a : Ans D P) (k : Nat)
    (x : Rel) (xs : List Rel) :
    jl K hK ev a k (x :: xs) = (do
      let r ← ev k x
      match r.1 with
      | none => pure (none, r.2)
      | some b =>
        match ← Ans.join D P K hK a b with
        | none => pure (none, r.2)
        | some c => jl K hK ev c r.2 xs) := by
  at_cost K hK
  conv_lhs => unfold jl joinL
  congr! 2 with r
  cases r.1 with
  | none => rfl
  | some b =>
    simp only
    congr! 2 with z
    cases z with
    | none => rfl
    | some c => rfl

theorem rd_succ (d k : Nat) (n : Rel) :
    rd (P := P) K hK (d + 1) k n = (do
      match ← Charged.viewNode n with
      | .span _ => do
        let a ← Ans.leaf D P K hK none n none
        pure (a, k)
      | .call _ _ =>
        match ← Charged.body P n with
        | none => pure (none, k)
        | some b => do
          let r ← rd K hK d k b
          match r.1 with
          | none => pure (none, r.2)
          | some a => do
            let c ← Ans.unfold D P a n
            pure (c, r.2)
      | .union xs =>
        match xs[k % xs.length]? with
        | none => pure (none, k)
        | some x => do
          let r ← rd K hK d (k / xs.length) x
          match r.1 with
          | none => pure (none, r.2)
          | some a => do
            let c ← Ans.inj D P a n (k % xs.length)
            pure (c, r.2)
      | .chain xs =>
        match xs with
        | [] => pure (none, k)
        | x :: rest => do
          let r ← rd K hK d k x
          match r.1 with
          | none => pure (none, r.2)
          | some a => do
            let r' ← jl K hK (rd K hK d) a r.2 rest
            match r'.1 with
            | none => pure (none, r'.2)
            | some c => do
              let c' ← Ans.inj D P c n 0
              pure (c', r'.2)
      | .meet xs =>
        match xs with
        | [] => pure (none, k)
        | x :: rest => do
          let r ← rd K hK d k x
          match r.1 with
          | none => pure (none, r.2)
          | some a => do
            let r' ← ml K hK (rd K hK d) a r.2 rest
            match r'.1 with
            | none => pure (none, r'.2)
            | some c => do
              let c' ← Ans.inj D P c n 0
              pure (c', r'.2)) := by
  at_cost K hK
  conv_lhs => unfold rd read
  congr! 2 with v
  cases v with
  | span s => rfl
  | call nm f =>
    simp only
    congr! 2 with b
    cases b with
    | none => rfl
    | some b =>
      simp only
      congr! 2 with r
      cases r.1 <;> rfl
  | union xs =>
    simp only
    cases xs[k % xs.length]? with
    | none => rfl
    | some x =>
      simp only
      congr! 2 with r
      cases r.1 <;> rfl
  | chain xs =>
    cases xs with
    | nil => rfl
    | cons x rest =>
      simp only
      congr! 2 with r
      cases r.1 with
      | none => rfl
      | some a =>
        simp only
        congr! 2 with r'
        cases r'.1 <;> rfl
  | meet xs =>
    cases xs with
    | nil => rfl
    | cons x rest =>
      simp only
      congr! 2 with r
      cases r.1 with
      | none => rfl
      | some a =>
        simp only
        congr! 2 with r'
        cases r'.1 <;> rfl

/-! ## What the rules cost -/

theorem leaf_ticks (s : Span) :
    (Ans.leaf D P K hK none (.span s) none).ticks = 2 + (K.rep s).ticks := by
  have hb : IsBound D (none : Option R) ∧ IsBound D (none : Option R) :=
    ⟨isBound_none D, isBound_none D⟩
  unfold Ans.leaf
  simp only [Cost.bind_ticks, Cost.tick_ticks]
  rw [dite_eq_left_of_eq_true (eq_true hb)]
  show 2 + (Ans.spanBothK K none s none).ticks = _
  unfold Ans.spanBothK
  simp only [Cost.bind_ticks]
  cases (K.rep s).val <;> simp

theorem join_ticks {a b : Ans D P} (ha : a.goal.rb = none) (hb : b.goal.lb = none) :
    (Ans.join D P K hK a b).ticks =
      3 + (seqParts a.goal.node ++ seqParts b.goal.node).length +
        (K.compose a.span b.span).ticks := by
  have hok : JoinOk D a.span none none b.span := .inl ⟨rfl, .inl rfl⟩
  unfold Ans.join
  simp only [Cost.bind_ticks, ha, hb, Ans.check, Cost.tick_ticks, Charged.op_ticks]
  rw [dite_eq_left_of_eq_true (eq_true hok)]
  show 1 + (1 + (1 + _ + (K.compose a.span b.span).ticks)) = _
  omega

omit [DecidableEq R] in
theorem inj_ticks (a : Ans D P) (u : Rel) (i : Nat) : (Ans.inj D P a u i).ticks = 2 := rfl

omit [DecidableEq R] in
theorem unfold_ticks (a : Ans D P) (n : Rel) : (Ans.unfold D P a n).ticks = 2 := rfl

/-! ## What a reading returns and costs -/

variable (P)

/-- The reading of `n` to the depth `d` by the number `k` makes an answer of
the goal `g` with the representative `r`, leaves `k'` of the number and
costs `c` ticks. -/
def Reads (d k : Nat) (n : Rel) (g : Goal R) (r : R) (k' c : Nat) : Prop :=
  ∃ a : Ans D P, (rd (P := P) K hK d k n).val = (some a, k') ∧ a.goal = g ∧ a.span = r ∧
    (rd (P := P) K hK d k n).ticks = c

/-- Joining the answers of the members `xs`, read to the depth `d`, onto an
answer of the goal `g₀` with the representative `r₀` makes an answer of the
goal `g` with the representative `r`, leaves `k'` of the number and costs
`c` ticks. -/
def Joins (d : Nat) (g₀ : Goal R) (r₀ : R) (k : Nat) (xs : List Rel) (g : Goal R) (r : R)
    (k' c : Nat) : Prop :=
  ∀ a : Ans D P, a.goal = g₀ → a.span = r₀ →
    ∃ z : Ans D P, (jl K hK (rd K hK d) a k xs).val = (some z, k') ∧ z.goal = g ∧ z.span = r ∧
      (jl K hK (rd K hK d) a k xs).ticks = c

variable {P}

/-- A span node with a representative. -/
theorem reads_span {s : Span} {r : R} (h : D.rep s = some r) (d k : Nat) :
    Reads P K hK (d + 1) k (.span s) ⟨none, .span s, none⟩ r k (3 + (K.rep s).ticks) := by
  have hs : spanBoth D none s none = some r := by simp [spanBoth, h]
  obtain ⟨c, hc, hsp, hg⟩ := Ans.leaf_ok (P := P) K hK (isBound_none D) (isBound_none D) hs
  refine ⟨c, ?_, hg, hsp, ?_⟩
  · rw [rd_succ]
    simp only [Cost.bind_val, Charged.viewNode, Charged.op_val, RelOf.view, NodeView.forget, hc,
      Cost.pure_val]
  · rw [rd_succ]
    simp only [Cost.bind_ticks, Charged.viewNode, Charged.op_val, Charged.op_ticks,
      RelOf.view, NodeView.forget, Charged.members, leaf_ticks, Cost.pure_ticks]
    omega

/-- A call: the reading of its body, unfolded. -/
theorem reads_call {n b : Rel} {nm : Name} {f : Bool} (hv : n.view = .call nm f)
    (hb : Charged.bodyOf P n = some b) {d k : Nat} {g : Goal R} {r : R} {k' c : Nat}
    (h : Reads P K hK d k b g r k' c) (hg : g.node = b) :
    Reads P K hK (d + 1) k n ⟨g.lb, n, g.rb⟩ r k' (c + 4) := by
  obtain ⟨a, hval, rfl, rfl, htk⟩ := h
  obtain ⟨z, hz, hsp, hzg⟩ := Ans.unfold_ok (P := P) (a := a) (n := n) (hg ▸ hb)
  refine ⟨z, ?_, hzg, hsp, ?_⟩
  · rw [rd_succ]
    simp only [Cost.bind_val, Charged.viewNode, Charged.op_val, hv, NodeView.forget, Charged.body,
      hb, hval, hz, Cost.pure_val]
  · rw [rd_succ]
    simp only [Cost.bind_ticks, Charged.viewNode, Charged.op_val, Charged.op_ticks,
      hv, NodeView.forget, Charged.members, Charged.body, hb, hval, htk, unfold_ticks,
      Cost.pure_ticks]
    omega

/-- A union: the reading of the member the number chooses, as an answer of
the union. -/
theorem reads_union {n x : Rel} {xs : List Rel} {d k : Nat} (hv : n.view = .union xs)
    (hx : xs[k % xs.length]? = some x) {g : Goal R} {r : R} {k' c : Nat}
    (h : Reads P K hK d (k / xs.length) x g r k' c) (hg : g.node = x)
    (hu : n.unionParts[k % xs.length]? = some x) :
    Reads P K hK (d + 1) k n ⟨g.lb, n, g.rb⟩ r k' (c + xs.length + 3) := by
  obtain ⟨a, hval, rfl, rfl, htk⟩ := h
  obtain ⟨z, hz, hsp, hzg⟩ :=
    Ans.inj_ok (P := P) (a := a) (u := n) (i := k % xs.length) (hg ▸ hu)
  refine ⟨z, ?_, hzg, hsp, ?_⟩
  · rw [rd_succ]
    simp only [Cost.bind_val, Charged.viewNode, Charged.op_val, hv, NodeView.forget, hx, hval, hz,
      Cost.pure_val]
  · rw [rd_succ]
    simp only [Cost.bind_ticks, Charged.viewNode, Charged.op_val, Charged.op_ticks,
      hv, NodeView.forget, Charged.members, hx, hval, htk, inj_ticks, Cost.pure_ticks]
    omega

/-- A union read by the number 0: the reading of its first member. -/
theorem reads_union_zero {n x : Rel} {xs : List Rel} {d : Nat} (hv : n.view = .union xs)
    (hx : xs[0]? = some x) {g : Goal R} {r : R} {k' c : Nat}
    (h : Reads P K hK d 0 x g r k' c) (hg : g.node = x) (hu : n.unionParts[0]? = some x) :
    Reads P K hK (d + 1) 0 n ⟨g.lb, n, g.rb⟩ r k' (c + xs.length + 3) :=
  reads_union K hK (k := 0) hv (by rwa [Nat.zero_mod]) (by rwa [Nat.zero_div]) hg
    (by rwa [Nat.zero_mod])

theorem joins_nil (d : Nat) (g : Goal R) (r : R) (k : Nat) : Joins P K hK d g r k [] g r k 0 := by
  intro a hg hr
  exact ⟨a, by rw [jl_nil]; rfl, hg, hr, by rw [jl_nil]; rfl⟩

/-- Joining the next member: its reading, composed onto the answer so
far. -/
theorem joins_cons {d k : Nat} {x : Rel} {xs : List Rel} {g₀ gx g : Goal R} {r₀ rx z r : R}
    {k₁ k' c₁ c₂ L : Nat} (hx : Reads P K hK d k x gx rx k₁ c₁) (hrb : g₀.rb = none)
    (hlb : gx.lb = none) (hc : D.compose r₀ rx = some z)
    (hlen : (seqParts g₀.node ++ seqParts gx.node).length = L) {g₁ : Goal R}
    (hg₁ : g₁ = ⟨g₀.lb, mkSeq (seqParts g₀.node ++ seqParts gx.node), gx.rb⟩)
    (hrest : Joins P K hK d g₁ z k₁ xs g r k' c₂) :
    Joins P K hK d g₀ r₀ k (x :: xs) g r k' (c₁ + (3 + L + (K.compose r₀ rx).ticks) + c₂) := by
  intro a hg hr
  subst hg hr hlen hg₁
  obtain ⟨b, hval, rfl, rfl, htk⟩ := hx
  obtain ⟨ab, hab, hsp, habg⟩ := Ans.join_ok (P := P) K hK (a := a) (b := b)
    (.inl ⟨hrb, .inl hlb⟩) hc
  obtain ⟨w, hw, hwg, hwr, hwt⟩ := hrest ab habg hsp
  refine ⟨w, ?_, hwg, hwr, ?_⟩
  · rw [jl_cons]
    simp only [Cost.bind_val, hval, hab, hw]
  · rw [jl_cons]
    simp only [Cost.bind_ticks, hval, htk, hab, join_ticks K hK hrb hlb, hwt]
    omega

/-- A chain: the reading of its first member, the others joined onto it,
and the answer checked to be an answer of the chain. -/
theorem reads_chain {n x : Rel} {rest : List Rel} {d k : Nat} (hv : n.view = .chain (x :: rest))
    {gx g : Goal R} {rx r : R} {k₁ k' c₁ c₂ : Nat} (hx : Reads P K hK d k x gx rx k₁ c₁)
    (hj : Joins P K hK d gx rx k₁ rest g r k' c₂) (hu : n.unionParts[0]? = some g.node) :
    Reads P K hK (d + 1) k n ⟨g.lb, n, g.rb⟩ r k' (c₁ + c₂ + rest.length + 4) := by
  obtain ⟨a, hval, rfl, rfl, htk⟩ := hx
  obtain ⟨w, hw, rfl, rfl, hwt⟩ := hj a rfl rfl
  obtain ⟨z, hz, hsp, hzg⟩ := Ans.inj_ok (P := P) (a := w) (u := n) (i := 0) hu
  refine ⟨z, ?_, hzg, hsp, ?_⟩
  · rw [rd_succ]
    simp only [Cost.bind_val, Charged.viewNode, Charged.op_val, hv, NodeView.forget, hval, hw, hz,
      Cost.pure_val]
  · rw [rd_succ]
    simp only [Cost.bind_ticks, Charged.viewNode, Charged.op_val, Charged.op_ticks,
      hv, NodeView.forget, Charged.members, hval, htk, hw, hwt, inj_ticks, Cost.pure_ticks,
      List.length_cons]
    omega

end Dive

end RwLog
