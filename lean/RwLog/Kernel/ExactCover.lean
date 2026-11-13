/-
# Simplified spans under syntactic coverage

Termination arguments compare answers by `Span.Covers`, the coverage a
machine decides when it drops a candidate, not up to the theory. A candidate
is simplified, and simplification changes a span's ground triples, so the
comparison goes through what simplification keeps (`SimpLaws`).

* `Under T X a`: the answer `a` lies under the simplification of a span that
  `X` dominates. Every answer a machine computes for a goal lies under one
  derivation of the goal in this sense.
* `XC T A X`: some member of `A` covers the simplification of every span that
  `X` dominates. A complete table has this for every derivation of its goal.

`Under` and `XC` meet in `XC.cover`: a member of `A` covers `a`.
-/
import RwLog.Kernel.Live

namespace RwLog

/-- Composition is monotone in coverage. -/
theorem compose_mono {a b x y z : Span} (ha : a.Covers x) (hb : b.Covers y)
    (hz : x.compose y = some z) : ∃ z', a.compose b = some z' ∧ z'.Covers z := by
  have hd : Dom ((a.den).comp b.den) z.den := by
    rw [compose_some hz]; exact (dom_of_covers ha).comp (dom_of_covers hb)
  obtain ⟨z', hz', hzd⟩ := compose_isSome (hd.nonempty z.den_nonempty)
  exact ⟨z', hz', covers_of_dom (by rw [hzd]; exact hd)⟩

/-- Conjunction is monotone in coverage. -/
theorem meet_mono {a b x y z : Span} (ha : a.Covers x) (hb : b.Covers y)
    (hz : x.meet y = some z) : ∃ z', a.meet b = some z' ∧ z'.Covers z := by
  have hd : Dom ((a.den).meet b.den) z.den := by
    rw [meet_some hz]; exact (dom_of_covers ha).meet (dom_of_covers hb)
  obtain ⟨z', hz', hzd⟩ := meet_isSome (hd.nonempty z.den_nonempty)
  exact ⟨z', hz', covers_of_dom (by rw [hzd]; exact hd)⟩

/-! ## The laws, unfolded -/

theorem rel_some {o o' : Option Span} {c' : Span} (h : Option.Rel Span.Equiv o o') (hc : o' = some c') :
    ∃ c, o = some c ∧ c.Equiv c' := by
  subst hc
  cases h with
  | some h => exact ⟨_, rfl, h⟩

theorem rel_some' {o o' : Option Span} {c : Span} (h : Option.Rel Span.Equiv o o') (hc : o = some c) :
    ∃ c', o' = some c' ∧ c.Equiv c' := by
  subst hc
  cases h with
  | some h => exact ⟨_, rfl, h⟩


section Laws

variable {T : Theory} (hL : SimpLaws T)
include hL

theorem simp_mono {f x x' : Span} (h : f.Covers x) (hx : T.simplify x = some x') :
    ∃ f', T.simplify f = some f' ∧ f'.Covers x' := by
  rcases hL.mono f x h with h' | ⟨f', x'', hf, hx'', hc⟩
  · rw [hx] at h'; exact absurd h' (by simp)
  · rw [hx] at hx''
    cases hx''
    exact ⟨f', hf, hc⟩

/-- Simplifying both sides before composing: `simp (simp a ; simp b)` is
`simp (a ; b)`, up to equivalence. -/
theorem simp_comp_both {a b z c : Span} (hz : a.compose b = some z) (hc : T.simplify z = some c) :
    ∃ a' b' z' c', T.simplify a = some a' ∧ T.simplify b = some b' ∧ a'.compose b' = some z' ∧
      T.simplify z' = some c' ∧ c'.Equiv c := by
  obtain ⟨c₁, h₁, e₁⟩ := rel_some (hL.compR a b) (by rw [hz]; exact hc)
  cases hb : T.simplify b with
  | none => rw [hb] at h₁; simp at h₁
  | some b' =>
    rw [hb] at h₁
    simp only [Option.bind_some] at h₁
    obtain ⟨c₂, h₂, e₂⟩ := rel_some (hL.compL a b') h₁
    cases ha : T.simplify a with
    | none => rw [ha] at h₂; simp at h₂
    | some a' =>
      rw [ha] at h₂
      simp only [Option.bind_some, Option.bind_eq_some_iff] at h₂
      obtain ⟨z', hz', hc'⟩ := h₂
      exact ⟨a', b', z', c₂, rfl, rfl, hz', hc', ⟨e₂.1.trans e₁.1, e₁.2.trans e₂.2⟩⟩

theorem simp_comp_both' {a b a' b' z' c' : Span} (ha : T.simplify a = some a')
    (hb : T.simplify b = some b') (hz' : a'.compose b' = some z') (hc' : T.simplify z' = some c') :
    ∃ z c, a.compose b = some z ∧ T.simplify z = some c ∧ c.Equiv c' := by
  obtain ⟨c₂, h₂, e₂⟩ := rel_some' (hL.compL a b')
    (by rw [ha]; simp only [Option.bind_some, hz']; exact hc')
  obtain ⟨c₁, h₁, e₁⟩ := rel_some' (hL.compR a b) (by rw [hb]; exact h₂)
  simp only [Option.bind_eq_some_iff] at h₁
  obtain ⟨z, hz, hc⟩ := h₁
  exact ⟨z, c₁, hz, hc, ⟨e₁.2.trans e₂.2, e₂.1.trans e₁.1⟩⟩

theorem simp_meet_both {a b z c : Span} (hz : a.meet b = some z) (hc : T.simplify z = some c) :
    ∃ a' b' z' c', T.simplify a = some a' ∧ T.simplify b = some b' ∧ a'.meet b' = some z' ∧
      T.simplify z' = some c' ∧ c'.Equiv c := by
  obtain ⟨c₁, h₁, e₁⟩ := rel_some (hL.meetR a b) (by rw [hz]; exact hc)
  cases hb : T.simplify b with
  | none => rw [hb] at h₁; simp at h₁
  | some b' =>
    rw [hb] at h₁
    simp only [Option.bind_some] at h₁
    obtain ⟨c₂, h₂, e₂⟩ := rel_some (hL.meetL a b') h₁
    cases ha : T.simplify a with
    | none => rw [ha] at h₂; simp at h₂
    | some a' =>
      rw [ha] at h₂
      simp only [Option.bind_some, Option.bind_eq_some_iff] at h₂
      obtain ⟨z', hz', hc'⟩ := h₂
      exact ⟨a', b', z', c₂, rfl, rfl, hz', hc', ⟨e₂.1.trans e₁.1, e₁.2.trans e₂.2⟩⟩

theorem simp_meet_both' {a b a' b' z' c' : Span} (ha : T.simplify a = some a')
    (hb : T.simplify b = some b') (hz' : a'.meet b' = some z') (hc' : T.simplify z' = some c') :
    ∃ z c, a.meet b = some z ∧ T.simplify z = some c ∧ c.Equiv c' := by
  obtain ⟨c₂, h₂, e₂⟩ := rel_some' (hL.meetL a b')
    (by rw [ha]; simp only [Option.bind_some, hz']; exact hc')
  obtain ⟨c₁, h₁, e₁⟩ := rel_some' (hL.meetR a b) (by rw [hb]; exact h₂)
  simp only [Option.bind_eq_some_iff] at h₁
  obtain ⟨z, hz, hc⟩ := h₁
  exact ⟨z, c₁, hz, hc, ⟨e₁.2.trans e₂.2, e₂.1.trans e₁.1⟩⟩

/-- Simplifying only the right side first. -/
theorem simp_compR {a b b' z' c' : Span} (hb : T.simplify b = some b') (hz' : a.compose b' = some z')
    (hc' : T.simplify z' = some c') :
    ∃ z c, a.compose b = some z ∧ T.simplify z = some c ∧ c.Equiv c' := by
  obtain ⟨c₁, h₁, e₁⟩ := rel_some' (hL.compR a b) (by rw [hb]; simp only [Option.bind_some, hz']; exact hc')
  simp only [Option.bind_eq_some_iff] at h₁
  obtain ⟨z, hz, hc⟩ := h₁
  exact ⟨z, c₁, hz, hc, ⟨e₁.2, e₁.1⟩⟩

/-- Simplifying only the left side first. -/
theorem simp_compL {a a' b z' c' : Span} (ha : T.simplify a = some a') (hz' : a'.compose b = some z')
    (hc' : T.simplify z' = some c') :
    ∃ z c, a.compose b = some z ∧ T.simplify z = some c ∧ c.Equiv c' := by
  obtain ⟨c₁, h₁, e₁⟩ := rel_some' (hL.compL a b) (by rw [ha]; simp only [Option.bind_some, hz']; exact hc')
  simp only [Option.bind_eq_some_iff] at h₁
  obtain ⟨z, hz, hc⟩ := h₁
  exact ⟨z, c₁, hz, hc, ⟨e₁.2, e₁.1⟩⟩

theorem simp_meetR {a b b' z' c' : Span} (hb : T.simplify b = some b') (hz' : a.meet b' = some z')
    (hc' : T.simplify z' = some c') :
    ∃ z c, a.meet b = some z ∧ T.simplify z = some c ∧ c.Equiv c' := by
  obtain ⟨c₁, h₁, e₁⟩ := rel_some' (hL.meetR a b) (by rw [hb]; simp only [Option.bind_some, hz']; exact hc')
  simp only [Option.bind_eq_some_iff] at h₁
  obtain ⟨z, hz, hc⟩ := h₁
  exact ⟨z, c₁, hz, hc, ⟨e₁.2, e₁.1⟩⟩

theorem simp_meetL {a a' b z' c' : Span} (ha : T.simplify a = some a') (hz' : a'.meet b = some z')
    (hc' : T.simplify z' = some c') :
    ∃ z c, a.meet b = some z ∧ T.simplify z = some c ∧ c.Equiv c' := by
  obtain ⟨c₁, h₁, e₁⟩ := rel_some' (hL.meetL a b) (by rw [ha]; simp only [Option.bind_some, hz']; exact hc')
  simp only [Option.bind_eq_some_iff] at h₁
  obtain ⟨z, hz, hc⟩ := h₁
  exact ⟨z, c₁, hz, hc, ⟨e₁.2, e₁.1⟩⟩

theorem simp_compL_rev {a b z c : Span} (hz : a.compose b = some z) (hc : T.simplify z = some c) :
    ∃ a' z' c', T.simplify a = some a' ∧ a'.compose b = some z' ∧ T.simplify z' = some c' ∧
      c'.Equiv c := by
  obtain ⟨c', h, e⟩ := rel_some (hL.compL a b) (by rw [hz]; exact hc)
  cases ha : T.simplify a with
  | none => rw [ha] at h; simp at h
  | some a' =>
    rw [ha] at h
    simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨z', hz', hc'⟩ := h
    exact ⟨a', z', c', rfl, hz', hc', e⟩

theorem simp_compR_rev {a b z c : Span} (hz : a.compose b = some z) (hc : T.simplify z = some c) :
    ∃ b' z' c', T.simplify b = some b' ∧ a.compose b' = some z' ∧ T.simplify z' = some c' ∧
      c'.Equiv c := by
  obtain ⟨c', h, e⟩ := rel_some (hL.compR a b) (by rw [hz]; exact hc)
  cases hb : T.simplify b with
  | none => rw [hb] at h; simp at h
  | some b' =>
    rw [hb] at h
    simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨z', hz', hc'⟩ := h
    exact ⟨b', z', c', rfl, hz', hc', e⟩

theorem simp_meetL_rev {a b z c : Span} (hz : a.meet b = some z) (hc : T.simplify z = some c) :
    ∃ a' z' c', T.simplify a = some a' ∧ a'.meet b = some z' ∧ T.simplify z' = some c' ∧
      c'.Equiv c := by
  obtain ⟨c', h, e⟩ := rel_some (hL.meetL a b) (by rw [hz]; exact hc)
  cases ha : T.simplify a with
  | none => rw [ha] at h; simp at h
  | some a' =>
    rw [ha] at h
    simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨z', hz', hc'⟩ := h
    exact ⟨a', z', c', rfl, hz', hc', e⟩

theorem simp_meetR_rev {a b z c : Span} (hz : a.meet b = some z) (hc : T.simplify z = some c) :
    ∃ b' z' c', T.simplify b = some b' ∧ a.meet b' = some z' ∧ T.simplify z' = some c' ∧
      c'.Equiv c := by
  obtain ⟨c', h, e⟩ := rel_some (hL.meetR a b) (by rw [hz]; exact hc)
  cases hb : T.simplify b with
  | none => rw [hb] at h; simp at h
  | some b' =>
    rw [hb] at h
    simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨z', hz', hc'⟩ := h
    exact ⟨b', z', c', rfl, hz', hc', e⟩

end Laws

/-! ## Answers under derivations, and coverage of derivations -/

/-- `a` lies under the simplification of a span that `X` dominates. -/
def Under (T : Theory) (X : GRel) (a : Span) : Prop :=
  ∃ w, Dom X w.den ∧ ∃ w', T.simplify w = some w' ∧ w'.Covers a

/-- Some member of `A` covers the simplification of every span `X`
dominates. -/
def XC (T : Theory) (A : List Span) (X : GRel) : Prop :=
  ∀ w, Dom X w.den → ∀ w', T.simplify w = some w' → ∃ f ∈ A, f.Covers w'

variable {T : Theory}

theorem Under.dom {X Y : GRel} {a : Span} (hd : Dom Y X) (h : Under T X a) : Under T Y a := by
  obtain ⟨w, hw, w', hs, hc⟩ := h
  exact ⟨w, hd.trans hw, w', hs, hc⟩

theorem Under.of_eq {X Y : GRel} {a : Span} (h : Under T X a) (e : X = Y) : Under T Y a := e ▸ h

theorem Under.covers {X : GRel} {a b : Span} (h : Under T X a) (hab : a.Covers b) : Under T X b := by
  obtain ⟨w, hw, w', hs, hc⟩ := h
  exact ⟨w, hw, w', hs, hc.trans hab⟩

theorem Under.nonempty {X : GRel} {a : Span} (h : Under T X a) : X.Nonempty := by
  obtain ⟨w, hw, -⟩ := h
  exact hw.nonempty w.den_nonempty

theorem XC.dom {A : List Span} {X Y : GRel} (hd : Dom Y X) (h : XC T A Y) : XC T A X :=
  fun w hw => h w (hd.trans hw)

theorem XC.of_eq {A : List Span} {X Y : GRel} (h : XC T A X) (e : X = Y) : XC T A Y := e ▸ h

theorem XC.mono {A A' : List Span} {X : GRel} (h : XC T A X) (hA : ∀ a ∈ A, a ∈ A') : XC T A' X := by
  intro w hw w' hs
  obtain ⟨f, hf, hc⟩ := h w hw w' hs
  exact ⟨f, hA f hf, hc⟩

theorem XC.covers {A A' : List Span} {X : GRel} (h : XC T A X)
    (hA : ∀ a ∈ A, ∃ b ∈ A', b.Covers a) : XC T A' X := by
  intro w hw w' hs
  obtain ⟨f, hf, hc⟩ := h w hw w' hs
  obtain ⟨b, hb, hbc⟩ := hA f hf
  exact ⟨b, hb, hbc.trans hc⟩

theorem XC.of_empty {A : List Span} {X : GRel} (h : X = ∅) : XC T A X := by
  intro w hw
  obtain ⟨_, hx⟩ := hw.nonempty w.den_nonempty
  rw [h] at hx; exact absurd hx (Set.notMem_empty _)

/-- An answer under a derivation is covered by whatever covers the
derivation. -/
theorem XC.cover {A : List Span} {X : GRel} {a : Span} (h : XC T A X) (ha : Under T X a) :
    ∃ f ∈ A, f.Covers a := by
  obtain ⟨w, hw, w', hs, hc⟩ := ha
  obtain ⟨f, hf, hfc⟩ := h w hw w' hs
  exact ⟨f, hf, hfc.trans hc⟩

section
variable (hL : SimpLaws T)
include hL

/-- To cover everything `X` dominates, it is enough to cover the
simplification of one span that dominates `X`. -/
theorem xc_of_rep {A : List Span} {X : GRel} {u : Span} (hu : Dom u.den X)
    (h : ∀ u', T.simplify u = some u' → ∃ f ∈ A, f.Covers u') : XC T A X := by
  intro w hw w' hs
  obtain ⟨u', hu', hc⟩ := simp_mono hL (covers_of_dom (hu.trans hw)) hs
  obtain ⟨f, hf, hfc⟩ := h u' hu'
  exact ⟨f, hf, hfc.trans hc⟩

omit hL in
/-- An answer under a span that `X` dominates lies under `X`. -/
theorem sub_of_rep {X : GRel} {u u' a : Span} (hu : Dom X u.den) (hs : T.simplify u = some u')
    (hc : u'.Covers a) : Under T X a := ⟨u, hu, u', hs, hc⟩

omit hL in
theorem live_sub {z c : Span} (h : c ∈ live T z) : Under T z.den c := by
  have hs : T.simplify z = some c := by simpa [live] using h
  exact ⟨z, LCov.refl _, c, hs, Span.Covers.refl c⟩

theorem live_xc {z : Span} {X : GRel} (h : Dom z.den X) : XC T (live T z) X :=
  xc_of_rep hL h fun u' hu' => ⟨u', by simp [live, hu'], Span.Covers.refl _⟩

theorem composeLive_sub {x y c : Span} {X Y : GRel} (hx : Under T X x) (hy : Under T Y y)
    (hc : c ∈ composeLive T x y) : Under T (X.comp Y) c := by
  obtain ⟨w₁, hw₁, v₁, hv₁, hcx⟩ := hx
  obtain ⟨w₂, hw₂, v₂, hv₂, hcy⟩ := hy
  unfold composeLive at hc
  split at hc
  · rename_i z hz
    have hcz : T.simplify z = some c := by simpa [live] using hc
    obtain ⟨z', hz', hzc⟩ := compose_mono hcx hcy hz
    obtain ⟨c', hc', hcc⟩ := simp_mono hL hzc hcz
    obtain ⟨w, d, hw, hd, hde⟩ := simp_comp_both' hL hv₁ hv₂ hz' hc'
    refine ⟨w, ?_, d, hd, hde.1.trans hcc⟩
    rw [compose_some hw]
    exact hw₁.comp hw₂
  · simp at hc

theorem meetLive_sub {x y c : Span} {X Y : GRel} (hx : Under T X x) (hy : Under T Y y)
    (hc : c ∈ meetLive T x y) : Under T (X.meet Y) c := by
  obtain ⟨w₁, hw₁, v₁, hv₁, hcx⟩ := hx
  obtain ⟨w₂, hw₂, v₂, hv₂, hcy⟩ := hy
  unfold meetLive at hc
  split at hc
  · rename_i z hz
    have hcz : T.simplify z = some c := by simpa [live] using hc
    obtain ⟨z', hz', hzc⟩ := meet_mono hcx hcy hz
    obtain ⟨c', hc', hcc⟩ := simp_mono hL hzc hcz
    obtain ⟨w, d, hw, hd, hde⟩ := simp_meet_both' hL hv₁ hv₂ hz' hc'
    refine ⟨w, ?_, d, hd, hde.1.trans hcc⟩
    rw [meet_some hw]
    exact hw₁.meet hw₂
  · simp at hc

theorem sub_swap {X : GRel} {a : Span} (h : Under T X a) : Under T X.inv a.swap := by
  obtain ⟨w, hw, w', hs, hc⟩ := h
  refine ⟨w.swap, ?_, w'.swap, ?_, covers_swap hc⟩
  · rw [swap_den]; exact hw.inv
  · rw [hL.swap, hs]; rfl

theorem xc_swap {A : List Span} {X : GRel} (h : XC T A X) : XC T (A.map Span.swap) X.inv := by
  intro w hw w' hs
  have hw' : Dom X w.swap.den := by
    rw [swap_den]
    have := hw.inv
    rwa [GRel.inv_inv] at this
  have hs' : T.simplify w.swap = some w'.swap := by rw [hL.swap, hs]; rfl
  obtain ⟨f, hf, hc⟩ := h w.swap hw' w'.swap hs'
  exact ⟨f.swap, List.mem_map_of_mem hf, by simpa using covers_swap hc⟩

/-- Joining every answer of one side with every answer of the other covers
the composition of two spans the sides cover. -/
theorem join_comp_xc {xs ys : List Span} {u₁ u₂ u : Span} (hx : XC T xs u₁.den) (hy : XC T ys u₂.den)
    (hu : u₁.compose u₂ = some u) :
    XC T (xs.flatMap fun x => ys.flatMap fun y => composeLive T x y) u.den := by
  refine xc_of_rep hL (LCov.refl _) fun u' hu' => ?_
  obtain ⟨v₁, v₂, z', c', hv₁, hv₂, hz', hc', he⟩ := simp_comp_both hL hu hu'
  obtain ⟨f₁, hf₁, hc₁⟩ := hx u₁ (LCov.refl _) v₁ hv₁
  obtain ⟨f₂, hf₂, hc₂⟩ := hy u₂ (LCov.refl _) v₂ hv₂
  obtain ⟨z'', hz'', hzc⟩ := compose_mono hc₁ hc₂ hz'
  obtain ⟨c'', hc'', hcc⟩ := simp_mono hL hzc hc'
  refine ⟨c'', ?_, hcc.trans he.1⟩
  simp only [List.mem_flatMap]
  exact ⟨f₁, hf₁, f₂, hf₂, by simp [composeLive, hz'', live, hc'']⟩

theorem join_meet_xc {xs ys : List Span} {u₁ u₂ u : Span} (hx : XC T xs u₁.den) (hy : XC T ys u₂.den)
    (hu : u₁.meet u₂ = some u) :
    XC T (xs.flatMap fun x => ys.flatMap fun y => meetLive T x y) u.den := by
  refine xc_of_rep hL (LCov.refl _) fun u' hu' => ?_
  obtain ⟨v₁, v₂, z', c', hv₁, hv₂, hz', hc', he⟩ := simp_meet_both hL hu hu'
  obtain ⟨f₁, hf₁, hc₁⟩ := hx u₁ (LCov.refl _) v₁ hv₁
  obtain ⟨f₂, hf₂, hc₂⟩ := hy u₂ (LCov.refl _) v₂ hv₂
  obtain ⟨z'', hz'', hzc⟩ := meet_mono hc₁ hc₂ hz'
  obtain ⟨c'', hc'', hcc⟩ := simp_mono hL hzc hc'
  refine ⟨c'', ?_, hcc.trans he.1⟩
  simp only [List.mem_flatMap]
  exact ⟨f₁, hf₁, f₂, hf₂, by simp [meetLive, hz'', live, hc'']⟩

/-! ## Pushes: an answer composed with what runs under its interface -/

/-- A candidate `x ; y` where `y` lies under `Bx`, the right side as it runs
under `x`'s interface, and `x ; Bx` is dominated by `x ; u`. -/
theorem push_comp_subL {x y c u : Span} {X Bx Q : GRel} (hx : Under T X x) (hy : Under T Bx y)
    (hB : Dom ((x.den).comp u.den) ((x.den).comp Bx))
    (hQ : ∀ w : Span, Dom X w.den → Dom Q ((w.den).comp u.den)) (hc : c ∈ composeLive T x y) :
    Under T Q c := by
  obtain ⟨w₁, hw₁, v₁, hv₁, hcx⟩ := hx
  obtain ⟨w₂, hw₂, v₂, hv₂, hcy⟩ := hy
  unfold composeLive at hc
  split at hc
  · rename_i z hz
    have hcz : T.simplify z = some c := by simpa [live] using hc
    obtain ⟨z₁, hz₁, hzc₁⟩ := compose_mono (Span.Covers.refl x) hcy hz
    obtain ⟨c₁, hc₁, hcc₁⟩ := simp_mono hL hzc₁ hcz
    obtain ⟨z₂, c₂, hz₂, hc₂, he₂⟩ := simp_compR hL hv₂ hz₁ hc₁
    have hd₂ : Dom ((x.den).comp u.den) z₂.den := by
      rw [compose_some hz₂]; exact hB.trans ((LCov.refl _).comp hw₂)
    obtain ⟨z₃, hz₃, hz₃d⟩ := compose_isSome (hd₂.nonempty z₂.den_nonempty)
    obtain ⟨c₃, hc₃, hcc₃⟩ := simp_mono hL (covers_of_dom (by rw [hz₃d]; exact hd₂)) hc₂
    obtain ⟨z₄, hz₄, hzc₄⟩ := compose_mono hcx (Span.Covers.refl u) hz₃
    obtain ⟨c₄, hc₄, hcc₄⟩ := simp_mono hL hzc₄ hc₃
    obtain ⟨z₅, c₅, hz₅, hc₅, he₅⟩ := simp_compL hL hv₁ hz₄ hc₄
    refine ⟨z₅, ?_, c₅, hc₅, he₅.1.trans (hcc₄.trans (hcc₃.trans (he₂.1.trans hcc₁)))⟩
    rw [compose_some hz₅]; exact hQ w₁ hw₁
  · simp at hc

/-- The mirror image: a candidate `x ; y` where `x` runs under `y`'s
interface. -/
theorem push_comp_subR {x y c u : Span} {Y Bx Q : GRel} (hx : Under T Bx x) (hy : Under T Y y)
    (hB : Dom ((u.den).comp y.den) (Bx.comp y.den))
    (hQ : ∀ w : Span, Dom Y w.den → Dom Q ((u.den).comp w.den)) (hc : c ∈ composeLive T x y) :
    Under T Q c := by
  obtain ⟨w₂, hw₂, v₂, hv₂, hcx⟩ := hx
  obtain ⟨w₁, hw₁, v₁, hv₁, hcy⟩ := hy
  unfold composeLive at hc
  split at hc
  · rename_i z hz
    have hcz : T.simplify z = some c := by simpa [live] using hc
    obtain ⟨z₁, hz₁, hzc₁⟩ := compose_mono hcx (Span.Covers.refl y) hz
    obtain ⟨c₁, hc₁, hcc₁⟩ := simp_mono hL hzc₁ hcz
    obtain ⟨z₂, c₂, hz₂, hc₂, he₂⟩ := simp_compL hL hv₂ hz₁ hc₁
    have hd₂ : Dom ((u.den).comp y.den) z₂.den := by
      rw [compose_some hz₂]; exact hB.trans (hw₂.comp (LCov.refl _))
    obtain ⟨z₃, hz₃, hz₃d⟩ := compose_isSome (hd₂.nonempty z₂.den_nonempty)
    obtain ⟨c₃, hc₃, hcc₃⟩ := simp_mono hL (covers_of_dom (by rw [hz₃d]; exact hd₂)) hc₂
    obtain ⟨z₄, hz₄, hzc₄⟩ := compose_mono (Span.Covers.refl u) hcy hz₃
    obtain ⟨c₄, hc₄, hcc₄⟩ := simp_mono hL hzc₄ hc₃
    obtain ⟨z₅, c₅, hz₅, hc₅, he₅⟩ := simp_compR hL hv₁ hz₄ hc₄
    refine ⟨z₅, ?_, c₅, hc₅, he₅.1.trans (hcc₄.trans (hcc₃.trans (he₂.1.trans hcc₁)))⟩
    rw [compose_some hz₅]; exact hQ w₁ hw₁
  · simp at hc

theorem push_meet_subL {x y c u : Span} {X Bx Q : GRel} (hx : Under T X x) (hy : Under T Bx y)
    (hB : Dom ((x.den).meet u.den) ((x.den).meet Bx))
    (hQ : ∀ w : Span, Dom X w.den → Dom Q ((w.den).meet u.den)) (hc : c ∈ meetLive T x y) :
    Under T Q c := by
  obtain ⟨w₁, hw₁, v₁, hv₁, hcx⟩ := hx
  obtain ⟨w₂, hw₂, v₂, hv₂, hcy⟩ := hy
  unfold meetLive at hc
  split at hc
  · rename_i z hz
    have hcz : T.simplify z = some c := by simpa [live] using hc
    obtain ⟨z₁, hz₁, hzc₁⟩ := meet_mono (Span.Covers.refl x) hcy hz
    obtain ⟨c₁, hc₁, hcc₁⟩ := simp_mono hL hzc₁ hcz
    obtain ⟨z₂, c₂, hz₂, hc₂, he₂⟩ := simp_meetR hL hv₂ hz₁ hc₁
    have hd₂ : Dom ((x.den).meet u.den) z₂.den := by
      rw [meet_some hz₂]; exact hB.trans ((LCov.refl _).meet hw₂)
    obtain ⟨z₃, hz₃, hz₃d⟩ := meet_isSome (hd₂.nonempty z₂.den_nonempty)
    obtain ⟨c₃, hc₃, hcc₃⟩ := simp_mono hL (covers_of_dom (by rw [hz₃d]; exact hd₂)) hc₂
    obtain ⟨z₄, hz₄, hzc₄⟩ := meet_mono hcx (Span.Covers.refl u) hz₃
    obtain ⟨c₄, hc₄, hcc₄⟩ := simp_mono hL hzc₄ hc₃
    obtain ⟨z₅, c₅, hz₅, hc₅, he₅⟩ := simp_meetL hL hv₁ hz₄ hc₄
    refine ⟨z₅, ?_, c₅, hc₅, he₅.1.trans (hcc₄.trans (hcc₃.trans (he₂.1.trans hcc₁)))⟩
    rw [meet_some hz₅]; exact hQ w₁ hw₁
  · simp at hc

theorem push_meet_subR {x y c u : Span} {Y Bx Q : GRel} (hx : Under T Bx x) (hy : Under T Y y)
    (hB : Dom ((u.den).meet y.den) (Bx.meet y.den))
    (hQ : ∀ w : Span, Dom Y w.den → Dom Q ((u.den).meet w.den)) (hc : c ∈ meetLive T x y) :
    Under T Q c := by
  obtain ⟨w₂, hw₂, v₂, hv₂, hcx⟩ := hx
  obtain ⟨w₁, hw₁, v₁, hv₁, hcy⟩ := hy
  unfold meetLive at hc
  split at hc
  · rename_i z hz
    have hcz : T.simplify z = some c := by simpa [live] using hc
    obtain ⟨z₁, hz₁, hzc₁⟩ := meet_mono hcx (Span.Covers.refl y) hz
    obtain ⟨c₁, hc₁, hcc₁⟩ := simp_mono hL hzc₁ hcz
    obtain ⟨z₂, c₂, hz₂, hc₂, he₂⟩ := simp_meetL hL hv₂ hz₁ hc₁
    have hd₂ : Dom ((u.den).meet y.den) z₂.den := by
      rw [meet_some hz₂]; exact hB.trans (hw₂.meet (LCov.refl _))
    obtain ⟨z₃, hz₃, hz₃d⟩ := meet_isSome (hd₂.nonempty z₂.den_nonempty)
    obtain ⟨c₃, hc₃, hcc₃⟩ := simp_mono hL (covers_of_dom (by rw [hz₃d]; exact hd₂)) hc₂
    obtain ⟨z₄, hz₄, hzc₄⟩ := meet_mono (Span.Covers.refl u) hcy hz₃
    obtain ⟨c₄, hc₄, hcc₄⟩ := simp_mono hL hzc₄ hc₃
    obtain ⟨z₅, c₅, hz₅, hc₅, he₅⟩ := simp_meetR hL hv₁ hz₄ hc₄
    refine ⟨z₅, ?_, c₅, hc₅, he₅.1.trans (hcc₄.trans (hcc₃.trans (he₂.1.trans hcc₁)))⟩
    rw [meet_some hz₅]; exact hQ w₁ hw₁
  · simp at hc

end

end RwLog
