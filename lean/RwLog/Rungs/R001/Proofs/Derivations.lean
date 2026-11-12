/-
# Rung R001, Derivations: boundary lifting

`boundary_lifting` relates what a goal `lb ; e ; rb` with interface boundaries
derives to what `e` derives without boundaries. The proof goes through the
span layer's `Derives`, and is entirely semantic, up to the theory:

* `toDerives`: every live answer the machine can derive for a goal with
  interface boundaries is equivalent, up to the theory, to the boundaries
  composed with one span `Derives` gives the goal's expression. The pushes
  are absorbed by `iface_exact` (`x ; x.rightIface = x`), and conjunctions
  use that interface boundaries are sub-identities.
* `toGDerives`: conversely, for every span `Derives` gives an expression and
  any boundaries under which it is live, the machine derives, through join
  strategies only, an answer covering the boundaries composed with that span
  up to the theory (and equivalent to it when the boundaries are
  sub-identities).

Boundary lifting is the composite of the two. Liveness is what makes the
machine's pruning invisible: `simplify` drops only dead spans
(`Kernel.simplify_exact`), and every intermediate span of a derivation of a
live answer is live.

Relations are compared by `LCov`: `LCov T R S` says every triple of `S` whose
store the theory cannot refute is matched by a triple of `R` with the same
pair and a store no stronger. `Span.CoversLive` is `LCov` on denotations.
-/
import RwLog.Rungs.R001.Proofs.Kernel
import RwLog.Rungs.R000.Properties

namespace RwLog

namespace R001

namespace Lifting

variable {T : Theory}

/-! ## Stores no stronger than others -/

theorem ns_refl (S : GStore) : GStore.NoStronger T S S := fun _ h => h

theorem ns_trans {A B C : GStore} (h₁ : GStore.NoStronger T A B) (h₂ : GStore.NoStronger T B C) :
    GStore.NoStronger T A C := fun D h => h₂ D (h₁ D h)

theorem ns_union {A A' B B' : GStore} (ha : GStore.NoStronger T A A')
    (hb : GStore.NoStronger T B B') : GStore.NoStronger T (A ∪ B) (A' ∪ B') := by
  intro C h
  have e₁ : A ∪ B ∪ C = A ∪ (B ∪ C) := Finset.union_assoc _ _ _
  have h₁ : Refutes T (A' ∪ (B ∪ C)) := ha (B ∪ C) (e₁ ▸ h)
  have e₂ : A' ∪ (B ∪ C) = B ∪ (A' ∪ C) := Finset.union_left_comm _ _ _
  have h₂ : Refutes T (B' ∪ (A' ∪ C)) := hb (A' ∪ C) (e₂ ▸ h₁)
  have e₃ : B' ∪ (A' ∪ C) = A' ∪ B' ∪ C := by
    rw [Finset.union_left_comm, ← Finset.union_assoc]
  exact e₃ ▸ h₂

theorem ns_live {A B : GStore} (h : GStore.NoStronger T A B) (hB : ¬ Refutes T B) :
    ¬ Refutes T A := fun hA => hB (by simpa using h ∅ (by simpa using hA))

/-! ## Covering up to the theory -/

/-- `R` covers the live triples of `S`: every triple of `S` whose store the
theory cannot refute is matched by a triple of `R` with the same pair and a
store no stronger. -/
def LCov (T : Theory) (R S : GRel) : Prop :=
  ∀ a b X, (a, b, X) ∈ S → ¬ Refutes T X → ∃ Y, (a, b, Y) ∈ R ∧ GStore.NoStronger T Y X

/-- Equivalence up to the theory: each covers the live triples of the other. -/
def LEq (T : Theory) (R S : GRel) : Prop := LCov T R S ∧ LCov T S R

/-- Some triple's store is not refuted. -/
def Live (T : Theory) (R : GRel) : Prop := ∃ a b X, (a, b, X) ∈ R ∧ ¬ Refutes T X

theorem coversLive_iff {a s : Span} : a.CoversLive T s ↔ LCov T a.den s.den := by
  constructor
  · intro h x y X hx hn
    obtain ⟨⟨x', y', Y⟩, hy, h₁, h₂, h₃⟩ := h (x, y, X) hx hn
    simp only at h₁ h₂
    subst h₁ h₂
    exact ⟨Y, hy, h₃⟩
  · rintro h ⟨x, y, X⟩ hx hn
    obtain ⟨Y, hy, hY⟩ := h x y X hx hn
    exact ⟨(x, y, Y), hy, rfl, rfl, hY⟩

theorem not_dead_iff {s : Span} : ¬ s.Dead T ↔ Live T s.den := by
  constructor
  · intro h
    simp only [Span.Dead, not_forall] at h
    obtain ⟨σ, hσ⟩ := h
    exact ⟨_, _, _, ⟨σ, rfl⟩, hσ⟩
  · rintro ⟨a, b, X, ⟨σ, he⟩, hn⟩ hd
    simp only [Prod.mk.injEq] at he
    exact hn (he.2.2 ▸ hd σ)

theorem LCov.refl (R : GRel) : LCov T R R := fun _ _ X h _ => ⟨X, h, ns_refl X⟩

theorem LCov.trans {R S U : GRel} (h₁ : LCov T R S) (h₂ : LCov T S U) : LCov T R U := by
  intro a b X hx hn
  obtain ⟨Y, hy, hYX⟩ := h₂ a b X hx hn
  obtain ⟨Z, hz, hZY⟩ := h₁ a b Y hy (ns_live hYX hn)
  exact ⟨Z, hz, ns_trans hZY hYX⟩

theorem LCov.of_eq {R S : GRel} (h : R = S) : LCov T R S := h ▸ LCov.refl R

theorem LCov.of_sub {R S : GRel} (h : ∀ a b X, (a, b, X) ∈ S → ∃ Y, (a, b, Y) ∈ R ∧ Y ⊆ X) :
    LCov T R S := fun a b X hx _ =>
  let ⟨Y, hy, hYX⟩ := h a b X hx
  ⟨Y, hy, GStore.NoStronger.of_subset hYX⟩

theorem LCov.live {R S : GRel} (h : LCov T R S) (hS : Live T S) : Live T R := by
  obtain ⟨a, b, X, hx, hn⟩ := hS
  obtain ⟨Y, hy, hYX⟩ := h a b X hx hn
  exact ⟨a, b, Y, hy, ns_live hYX hn⟩

theorem LCov.comp {R R' S S' : GRel} (h₁ : LCov T R R') (h₂ : LCov T S S') :
    LCov T (R.comp S) (R'.comp S') := by
  rintro a b X ⟨m, X₁, X₂, hx₁, hx₂, hX⟩ hn
  have hX : X = X₁ ∪ X₂ := hX
  subst hX
  obtain ⟨Y₁, hy₁, e₁⟩ := h₁ a m X₁ hx₁ fun h => hn (h.mono Finset.subset_union_left)
  obtain ⟨Y₂, hy₂, e₂⟩ := h₂ m b X₂ hx₂ fun h => hn (h.mono Finset.subset_union_right)
  exact ⟨Y₁ ∪ Y₂, ⟨m, Y₁, Y₂, hy₁, hy₂, rfl⟩, ns_union e₁ e₂⟩

theorem LCov.meet {R R' S S' : GRel} (h₁ : LCov T R R') (h₂ : LCov T S S') :
    LCov T (R.meet S) (R'.meet S') := by
  rintro a b X ⟨X₁, X₂, hx₁, hx₂, hX⟩ hn
  have hX : X = X₁ ∪ X₂ := hX
  subst hX
  obtain ⟨Y₁, hy₁, e₁⟩ := h₁ a b X₁ hx₁ fun h => hn (h.mono Finset.subset_union_left)
  obtain ⟨Y₂, hy₂, e₂⟩ := h₂ a b X₂ hx₂ fun h => hn (h.mono Finset.subset_union_right)
  exact ⟨Y₁ ∪ Y₂, ⟨Y₁, Y₂, hy₁, hy₂, rfl⟩, ns_union e₁ e₂⟩

theorem LCov.inv {R S : GRel} (h : LCov T R S) : LCov T R.inv S.inv :=
  fun a b X hx hn => h b a X hx hn

theorem LEq.refl (R : GRel) : LEq T R R := ⟨LCov.refl R, LCov.refl R⟩

theorem LEq.symm {R S : GRel} (h : LEq T R S) : LEq T S R := ⟨h.2, h.1⟩

theorem LEq.trans {R S U : GRel} (h₁ : LEq T R S) (h₂ : LEq T S U) : LEq T R U :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem LEq.of_eq {R S : GRel} (h : R = S) : LEq T R S := h ▸ LEq.refl R

theorem LEq.comp {R R' S S' : GRel} (h₁ : LEq T R R') (h₂ : LEq T S S') :
    LEq T (R.comp S) (R'.comp S') := ⟨h₁.1.comp h₂.1, h₁.2.comp h₂.2⟩

theorem LEq.meet {R R' S S' : GRel} (h₁ : LEq T R R') (h₂ : LEq T S S') :
    LEq T (R.meet S) (R'.meet S') := ⟨h₁.1.meet h₂.1, h₁.2.meet h₂.2⟩

theorem LEq.inv {R S : GRel} (h : LEq T R S) : LEq T R.inv S.inv := ⟨h.1.inv, h.2.inv⟩

theorem live_comp {R S : GRel} (h : Live T (R.comp S)) : Live T R ∧ Live T S := by
  obtain ⟨a, b, X, ⟨m, X₁, X₂, h₁, h₂, hX⟩, hn⟩ := h
  have hX : X = X₁ ∪ X₂ := hX
  subst hX
  exact ⟨⟨a, m, X₁, h₁, fun h => hn (h.mono Finset.subset_union_left)⟩,
    ⟨m, b, X₂, h₂, fun h => hn (h.mono Finset.subset_union_right)⟩⟩

theorem live_meet {R S : GRel} (h : Live T (R.meet S)) : Live T R ∧ Live T S := by
  obtain ⟨a, b, X, ⟨X₁, X₂, h₁, h₂, hX⟩, hn⟩ := h
  have hX : X = X₁ ∪ X₂ := hX
  subst hX
  exact ⟨⟨a, b, X₁, h₁, fun h => hn (h.mono Finset.subset_union_left)⟩,
    ⟨a, b, X₂, h₂, fun h => hn (h.mono Finset.subset_union_right)⟩⟩

theorem live_inv {R : GRel} (h : Live T R.inv) : Live T R := by
  obtain ⟨a, b, X, hx, hn⟩ := h
  exact ⟨b, a, X, hx, hn⟩

theorem live_inv' {R : GRel} (h : Live T R) : Live T R.inv := by
  obtain ⟨a, b, X, hx, hn⟩ := h
  exact ⟨b, a, X, hx, hn⟩

theorem Live.nonempty {R : GRel} (h : Live T R) : R.Nonempty := by
  obtain ⟨a, b, X, hx, _⟩ := h
  exact ⟨_, hx⟩

/-! ## Sub-identities -/

/-- A sub-identity: every triple relates a term to itself. Interface spans
(`l = r`) and the identity are sub-identities. -/
def PId (R : GRel) : Prop := ∀ a b X, (a, b, X) ∈ R → b = a

theorem pid_id : PId GRel.id := fun _ _ _ h => h.1

theorem PId.inv {R : GRel} (h : PId R) : PId R.inv := fun a b X hx => (h b a X hx).symm

theorem pid_diag {s : Span} (h : s.l = s.r) : PId s.den := by
  rintro a b X ⟨σ, he⟩
  simp only [Prod.mk.injEq] at he
  rw [he.1, he.2.1, h]

theorem empty_comp (R : GRel) : (∅ : GRel).comp R = ∅ := by
  ext ⟨a, b, X⟩
  simp only [GRel.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, _, _, h, _⟩
  exact h

theorem meet_comm (R S : GRel) : R.meet S = S.meet R := by
  ext ⟨a, b, X⟩
  constructor <;> rintro ⟨X₁, X₂, h₁, h₂, hX⟩ <;>
    exact ⟨X₂, X₁, h₂, h₁, hX.trans (Finset.union_comm _ _)⟩

/-- `L ; A ; R`. -/
def wrap (L A R : GRel) : GRel := L.comp (A.comp R)

theorem live_wrap_mid {L A R : GRel} (h : Live T (wrap L A R)) : Live T A :=
  (live_comp (live_comp h).2).1

theorem lcov_wrap_pid {L A R : GRel} (hL : PId L) (hR : PId R) : LCov T A (wrap L A R) := by
  refine LCov.of_sub ?_
  rintro a b X ⟨m, XL, XAR, hl, ⟨n, XA, XR, ha, hr, e₂⟩, e₁⟩
  obtain rfl := (hL _ _ _ hl).symm
  obtain rfl := hR _ _ _ hr
  refine ⟨XA, ha, ?_⟩
  have e₁ : X = XL ∪ XAR := e₁
  have e₂ : XAR = XA ∪ XR := e₂
  subst e₁ e₂
  exact Finset.subset_union_left.trans Finset.subset_union_right

/-- `(L;A;R) & (L;B;R)` covers `L;(A & B);R`, for any `L` and `R`. -/
theorem meet_wrap_le (L A B R : GRel) :
    LCov T ((wrap L A R).meet (wrap L B R)) (wrap L (A.meet B) R) := by
  refine LCov.of_sub ?_
  rintro a b X ⟨m, XL, XABR, hl, ⟨n, XAB, XR, ⟨XA, XB, ha, hb, e₃⟩, hr, e₂⟩, e₁⟩
  refine ⟨(XL ∪ (XA ∪ XR)) ∪ (XL ∪ (XB ∪ XR)),
    ⟨XL ∪ (XA ∪ XR), XL ∪ (XB ∪ XR), ⟨m, XL, XA ∪ XR, hl, ⟨n, XA, XR, ha, hr, rfl⟩, rfl⟩,
      ⟨m, XL, XB ∪ XR, hl, ⟨n, XB, XR, hb, hr, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  have e₁ : X = XL ∪ XABR := e₁
  have e₂ : XABR = XAB ∪ XR := e₂
  have e₃ : XAB = XA ∪ XB := e₃
  subst e₁ e₂ e₃
  intro t; simp only [Finset.mem_union]; tauto

/-- For sub-identities, `L;(A & B);R` covers `(L;A;R) & (L;B;R)`. -/
theorem meet_wrap_ge {L A B R : GRel} (hL : PId L) (hR : PId R) :
    LCov T (wrap L (A.meet B) R) ((wrap L A R).meet (wrap L B R)) := by
  refine LCov.of_sub ?_
  rintro a b X ⟨X₁, X₂, ⟨m₁, XL₁, XAR, hl₁, ⟨n₁, XA, XR₁, ha, hr₁, e₂⟩, e₁⟩,
    ⟨m₂, XL₂, XBR, hl₂, ⟨n₂, XB, XR₂, hb, hr₂, e₄⟩, e₃⟩, e₀⟩
  obtain rfl := (hL _ _ _ hl₁).symm
  obtain rfl := (hL _ _ _ hl₂).symm
  obtain rfl := hR _ _ _ hr₁
  obtain rfl := hR _ _ _ hr₂
  refine ⟨XL₁ ∪ ((XA ∪ XB) ∪ XR₁),
    ⟨a, XL₁, (XA ∪ XB) ∪ XR₁, hl₁, ⟨b, XA ∪ XB, XR₁, ⟨XA, XB, ha, hb, rfl⟩, hr₁, rfl⟩, rfl⟩, ?_⟩
  have e₀ : X = X₁ ∪ X₂ := e₀
  have e₁ : X₁ = XL₁ ∪ XAR := e₁
  have e₂ : XAR = XA ∪ XR₁ := e₂
  have e₃ : X₂ = XL₂ ∪ XBR := e₃
  have e₄ : XBR = XB ∪ XR₂ := e₄
  subst e₀ e₁ e₂ e₃ e₄
  intro t; simp only [Finset.mem_union]; tauto

/-- For sub-identities, `(L;A;R) & B` and `L;(A & B);R` are equivalent. -/
theorem meet_wrap_one {L A B R : GRel} (hL : PId L) (hR : PId R) :
    LEq T ((wrap L A R).meet B) (wrap L (A.meet B) R) := by
  constructor
  · refine LCov.of_sub ?_
    rintro a b X ⟨m, XL, XABR, hl, ⟨n, XAB, XR, ⟨XA, XB, ha, hb, e₃⟩, hr, e₂⟩, e₁⟩
    obtain rfl := (hL _ _ _ hl).symm
    obtain rfl := hR _ _ _ hr
    refine ⟨(XL ∪ (XA ∪ XR)) ∪ XB,
      ⟨XL ∪ (XA ∪ XR), XB, ⟨a, XL, XA ∪ XR, hl, ⟨b, XA, XR, ha, hr, rfl⟩, rfl⟩, hb, rfl⟩, ?_⟩
    have e₁ : X = XL ∪ XABR := e₁
    have e₂ : XABR = XAB ∪ XR := e₂
    have e₃ : XAB = XA ∪ XB := e₃
    subst e₁ e₂ e₃
    intro t; simp only [Finset.mem_union]; tauto
  · refine LCov.of_sub ?_
    rintro a b X ⟨X₁, XB, ⟨m, XL, XAR, hl, ⟨n, XA, XR, ha, hr, e₂⟩, e₁⟩, hb, e₀⟩
    obtain rfl := (hL _ _ _ hl).symm
    obtain rfl := hR _ _ _ hr
    refine ⟨XL ∪ ((XA ∪ XB) ∪ XR),
      ⟨a, XL, (XA ∪ XB) ∪ XR, hl, ⟨b, XA ∪ XB, XR, ⟨XA, XB, ha, hb, rfl⟩, hr, rfl⟩, rfl⟩, ?_⟩
    have e₀ : X = X₁ ∪ XB := e₀
    have e₁ : X₁ = XL ∪ XAR := e₁
    have e₂ : XAR = XA ∪ XR := e₂
    subst e₀ e₁ e₂
    intro t; simp only [Finset.mem_union]; tauto

/-- Conjoining with `Li ; W ; Ri` is conjoining with `W`, when `Li` and `Ri`
are sub-identities that `X` already absorbs on both sides. -/
theorem meet_iface {X Li W Ri : GRel} (hLi : PId Li) (hRi : PId Ri)
    (hlx : Li.comp X = X) (hxr : X.comp Ri = X) :
    LEq T (X.meet (wrap Li W Ri)) (X.meet W) := by
  constructor
  · refine LCov.of_sub ?_
    rintro a b Z ⟨XX, XW, hx, hw, e₀⟩
    have hx₁ : (a, b, XX) ∈ Li.comp X := by rw [hlx]; exact hx
    have hx₂ : (a, b, XX) ∈ X.comp Ri := by rw [hxr]; exact hx
    obtain ⟨m, XLi, X', hli, -, e₁⟩ := hx₁
    obtain ⟨n, X'', XRi, -, hri, e₂⟩ := hx₂
    obtain rfl := (hLi _ _ _ hli).symm
    obtain rfl := hRi _ _ _ hri
    refine ⟨XX ∪ (XLi ∪ (XW ∪ XRi)),
      ⟨XX, XLi ∪ (XW ∪ XRi), hx, ⟨a, XLi, XW ∪ XRi, hli, ⟨b, XW, XRi, hw, hri, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    have e₀ : Z = XX ∪ XW := e₀
    have e₁ : XX = XLi ∪ X' := e₁
    have e₂ : XX = X'' ∪ XRi := e₂
    have hl : XLi ⊆ XX := e₁ ▸ Finset.subset_union_left
    have hr : XRi ⊆ XX := e₂ ▸ Finset.subset_union_right
    subst e₀
    intro t ht
    simp only [Finset.mem_union] at ht ⊢
    rcases ht with ht | ht | ht | ht
    · exact Or.inl ht
    · exact Or.inl (hl ht)
    · exact Or.inr ht
    · exact Or.inl (hr ht)
  · refine LCov.of_sub ?_
    rintro a b Z ⟨XX, XWW, hx, ⟨m, XLi, XWR, hli, ⟨n, XW, XRi, hw, hri, e₂⟩, e₁⟩, e₀⟩
    obtain rfl := (hLi _ _ _ hli).symm
    obtain rfl := hRi _ _ _ hri
    refine ⟨XX ∪ XW, ⟨XX, XW, hx, hw, rfl⟩, ?_⟩
    have e₀ : Z = XX ∪ XWW := e₀
    have e₁ : XWW = XLi ∪ XWR := e₁
    have e₂ : XWR = XW ∪ XRi := e₂
    subst e₀ e₁ e₂
    intro t; simp only [Finset.mem_union]; tauto

/-! ## Boundaries -/

/-- The meaning of an optional boundary: none is the identity. -/
def bden : Option Span → GRel
  | none => GRel.id
  | some s => s.den

/-- `lb ; A ; rb`. -/
def W (lb : Option Span) (A : GRel) (rb : Option Span) : GRel := wrap (bden lb) A (bden rb)

theorem pid_bden {o : Option Span} (h : ∀ b, o = some b → b.l = b.r) : PId (bden o) := by
  cases o with
  | none => exact pid_id
  | some b => exact pid_diag (h b rfl)

theorem bden_swap (o : Option Span) : bden (o.map Span.swap) = (bden o).inv := by
  cases o with
  | none =>
    ext ⟨a, b, X⟩
    simp only [bden, GRel.id, GRel.inv, Option.map_none, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂⟩
  | some s => exact swap_den s

theorem pid_bden_swap {o : Option Span} (h : PId (bden o)) : PId (bden (o.map Span.swap)) := by
  rw [bden_swap]; exact h.inv

/-- A boundary built from a span with `l = r` denotes that span. -/
theorem bden_bound {s : Span} (h : s.l = s.r) : bden (bound s) = s.den := by
  cases hb : bound s with
  | none =>
    obtain ⟨⟨v, hv⟩, hc⟩ := bound_none hb
    exact (den_trivial hv (h ▸ hv) hc).symm
  | some s' => rw [bound_some hb]; rfl

theorem pid_bound {s : Span} (h : s.l = s.r) : PId (bden (bound s)) := by
  rw [bden_bound h]; exact pid_diag h

theorem W_none (A : GRel) : W none A none = A := by
  simp only [W, wrap, bden, GRel.id_comp, GRel.comp_id]

theorem W_inv (lb rb : Option Span) (A : GRel) :
    (W (rb.map Span.swap) A (lb.map Span.swap)).inv = W lb A.inv rb := by
  simp only [W, wrap, GRel.inv_comp, bden_swap, _root_.RwLog.GRel.inv_inv, GRel.comp_assoc]

theorem LEq.W {A B : GRel} (h : LEq T A B) (lb rb : Option Span) : LEq T (W lb A rb) (W lb B rb) :=
  (LEq.refl _).comp (h.comp (LEq.refl _))

theorem LCov.W {A B : GRel} (h : LCov T A B) (lb rb : Option Span) :
    LCov T (W lb A rb) (W lb B rb) :=
  (LCov.refl _).comp (h.comp (LCov.refl _))

/-! ## Kernel steps with pruning, up to the theory -/

/-- Simplify an optional span. -/
def liveO (T : Theory) : Option Span → List Span
  | some z => live T z
  | none => []

section Kernel

variable (hS : Obligation.simplify_exact) (hT : ∀ ρ ∈ T, ρ.WellFormed)
include hS hT

/-- Simplifying keeps a span's meaning up to the theory, and keeps every live
span. -/
theorem liveO_spec {o : Option Span} {D : GRel} (hD : Span.denO o = D) :
    (∀ z ∈ liveO T o, LEq T z.den D) ∧ (Live T D → ∃ z, z ∈ liveO T o) := by
  cases o with
  | none =>
    subst hD
    refine ⟨fun z hz => by simp [liveO] at hz, ?_⟩
    rintro ⟨_, _, _, h, _⟩
    exact absurd h (Set.notMem_empty _)
  | some u =>
    subst hD
    refine ⟨fun z hz => ?_, fun hl => ?_⟩
    · have hz : T.simplify u = some z := by simpa [liveO, live] using hz
      obtain ⟨hb, hc⟩ := (hS T u hT).2 z hz
      refine ⟨coversLive_iff.1 hc, fun a b X hx _ => ?_⟩
      obtain ⟨⟨a', b', Y⟩, hy, h₁, h₂, h₃⟩ := hb (a, b, X) hx
      simp only at h₁ h₂
      subst h₁ h₂
      exact ⟨Y, hy, h₃⟩
    · cases hs : T.simplify u with
      | none => exact absurd ((hS T u hT).1 hs) (not_dead_iff.2 hl)
      | some z => exact ⟨z, by simp [liveO, live, hs]⟩

theorem composeLive_spec (x y : Span) :
    (∀ z ∈ composeLive T x y, LEq T z.den ((x.den).comp y.den)) ∧
      (Live T ((x.den).comp y.den) → ∃ z, z ∈ composeLive T x y) :=
  liveO_spec hS hT (o := x.compose y) (compose_den x y)

theorem meetLive_spec (x y : Span) :
    (∀ z ∈ meetLive T x y, LEq T z.den ((x.den).meet y.den)) ∧
      (Live T ((x.den).meet y.den) → ∃ z, z ∈ meetLive T x y) :=
  liveO_spec hS hT (o := x.meet y) (meet_den x y)

/-- The composite `lb ; s ; rb` before simplification. -/
def rawO (lb : Option Span) (s : Span) (rb : Option Span) : Option Span :=
  (match lb with
    | none => some s
    | some l => l.compose s).bind fun s' => match rb with
      | none => some s'
      | some r => s'.compose r

omit hS hT in
theorem spanAnswer_eq (lb : Option Span) (s : Span) (rb : Option Span) :
    spanAnswer T lb s rb = liveO T (rawO lb s rb) := by
  cases lb <;> cases rb <;> rfl

omit hS hT in
theorem rawO_den (lb : Option Span) (s : Span) (rb : Option Span) :
    Span.denO (rawO lb s rb) = W lb s.den rb := by
  cases lb with
  | none =>
    cases rb with
    | none => simp only [rawO, Option.bind_some, Span.denO, W_none]
    | some r =>
      simp only [rawO, Option.bind_some, compose_den, W, wrap, bden, GRel.id_comp]
  | some l =>
    cases rb with
    | none =>
      have : rawO (some l) s none = l.compose s := by
        cases h : l.compose s <;> simp [rawO, h]
      rw [this, compose_den]
      simp only [W, wrap, bden, GRel.comp_id]
    | some r =>
      simp only [rawO, W, wrap, bden]
      cases hc : l.compose s with
      | none =>
        rw [← GRel.comp_assoc, compose_none hc, empty_comp]; rfl
      | some u =>
        simp only [Option.bind_some, compose_den]
        rw [compose_some hc, GRel.comp_assoc]

theorem spanAnswer_spec (lb : Option Span) (s : Span) (rb : Option Span) :
    (∀ z ∈ spanAnswer T lb s rb, LEq T z.den (W lb s.den rb)) ∧
      (Live T (W lb s.den rb) → ∃ z, z ∈ spanAnswer T lb s rb) := by
  rw [spanAnswer_eq]
  exact liveO_spec hS hT (rawO_den lb s rb)

theorem live_leq {u z : Span} (hz : z ∈ live T u) : LEq T z.den u.den :=
  (liveO_spec hS hT (o := some u) rfl).1 z hz

end Kernel

/-! ## Unfolding and the expression of a goal -/

variable {P : Program}

theorem derives_of_unfold : ∀ (e : Rel) {s : Span}, Derives P (R000.unfold P e) s → Derives P e s
  | .zero, _, h => by cases h
  | .span _, _, h => h
  | .or a b, _, h => by
    cases h with
    | orl h => exact .orl (derives_of_unfold a h)
    | orr h => exact .orr (derives_of_unfold b h)
  | .and a b, _, h => by
    cases h with
    | and h₁ h₂ hc => exact .and (derives_of_unfold a h₁) (derives_of_unfold b h₂) hc
  | .seq a b, _, h => by
    cases h with
    | seq h₁ h₂ hc => exact .seq (derives_of_unfold a h₁) (derives_of_unfold b h₂) hc
  | .conv a, _, h => by
    cases h with
    | conv h => exact .conv (derives_of_unfold a h)
  | .call _, _, h => .call h

theorem derives_of_unfoldN : ∀ (k : Nat) (e : Rel) {s : Span},
    Derives P (R000.unfoldN P k e) s → Derives P e s
  | 0, _, _, h => h
  | k + 1, e, _, h => by
    rw [R000.unfoldN, Function.iterate_succ_apply] at h
    exact derives_of_unfold e (derives_of_unfoldN k _ h)

/-- Every span rung zero emits denotes what a span the query derives
denotes. -/
theorem roundSpans_derives {q : Rel} {k : Nat} {s : Span} (h : s ∈ R000.roundSpans P q k) :
    ∃ s', Derives P q s' ∧ s.den = s'.den := by
  simp only [R000.roundSpans, List.mem_flatMap] at h
  obtain ⟨p, hp, hs⟩ := h
  obtain ⟨s', hd, he⟩ := R000.norm_reflect (P := P) false _ p hp s (R000.mem_derivs.1 hs)
  exact ⟨s', derives_of_unfoldN k q hd.derives, he⟩

/-- A span `lb ; e ; rb` derives composes the boundaries with a span `e`
derives. -/
theorem derives_rel {g : Goal} {s : Span} (h : Derives P g.rel s) :
    ∃ s₀, Derives P g.e s₀ ∧ s.den = W g.lb s₀.den g.rb := by
  obtain ⟨lb, e, rb⟩ := g
  cases lb with
  | none =>
    cases rb with
    | none => exact ⟨s, h, (W_none _).symm⟩
    | some r =>
      cases h with
      | seq h₁ h₂ hc =>
        cases h₂
        refine ⟨_, h₁, ?_⟩
        simp only [W, wrap, bden, GRel.id_comp]
        exact compose_some hc
  | some l =>
    cases rb with
    | none =>
      cases h with
      | seq h₁ h₂ hc =>
        cases h₁
        refine ⟨_, h₂, ?_⟩
        simp only [W, wrap, bden, GRel.comp_id]
        exact compose_some hc
    | some r =>
      cases h with
      | seq h₁ h₂ hc =>
        cases h₁
        cases h₂ with
        | seq h₃ h₄ hc' =>
          cases h₄
          refine ⟨_, h₃, ?_⟩
          simp only [W, wrap, bden]
          rw [compose_some hc, compose_some hc']

theorem derives_of_branch : ∀ {e c : Rel}, c ∈ orBranches e → ∀ {s}, Derives P c s → Derives P e s
  | .or a b, c, hc, _, h => by
    simp only [orBranches, List.mem_append] at hc
    rcases hc with hc | hc
    · exact .orl (derives_of_branch hc h)
    · exact .orr (derives_of_branch hc h)
  | .zero, _, hc, _, h => by simp only [orBranches, List.mem_singleton] at hc; subst hc; exact h
  | .span _, _, hc, _, h => by simp only [orBranches, List.mem_singleton] at hc; subst hc; exact h
  | .and _ _, _, hc, _, h => by simp only [orBranches, List.mem_singleton] at hc; subst hc; exact h
  | .seq _ _, _, hc, _, h => by simp only [orBranches, List.mem_singleton] at hc; subst hc; exact h
  | .conv _, _, hc, _, h => by simp only [orBranches, List.mem_singleton] at hc; subst hc; exact h
  | .call _, _, hc, _, h => by simp only [orBranches, List.mem_singleton] at hc; subst hc; exact h

/-- An answer of a branch of a `|` nest is an answer of the nest. -/
theorem lift_leaf {e c : Rel} {lb rb : Option Span} {y : Span} (hc : c ∈ orBranches e)
    (h : GDerives P ⟨lb, c, rb⟩ y) : GDerives P ⟨lb, e, rb⟩ y := by
  cases e with
  | or a b => exact GDerives.or (g := ⟨lb, .or a b, rb⟩) rfl (List.mem_map.2 ⟨c, hc, rfl⟩) h
  | _ => simp only [orBranches, List.mem_singleton] at hc; subst hc; exact h

theorem mem_orBranches_self {e : Rel} (h : ∀ a b, e ≠ .or a b) : e ∈ orBranches e := by
  cases e with
  | or a b => exact absurd rfl (h a b)
  | _ => simp [orBranches]

/-! ## Machine derivations are derivations -/

section Lift

variable (hS : Obligation.simplify_exact) (hT : ∀ ρ ∈ P.theory, ρ.WellFormed)
include hS hT

/-- Every live answer the machine derives for a goal with sub-identity
boundaries is, up to the theory, the boundaries composed with one span the
goal's expression derives. -/
theorem toDerives {g : Goal} {y : Span} (h : GDerives P g y) :
    PId (bden g.lb) → PId (bden g.rb) → Live P.theory y.den →
    ∃ s₀, Derives P g.e s₀ ∧ LEq P.theory y.den (W g.lb s₀.den g.rb) := by
  induction h with
  | @unfold g d y hy =>
    intro _ _ _
    unfold unfoldAnswers at hy
    split at hy
    · simp only [List.mem_flatMap] at hy
      obtain ⟨s, hs, hy⟩ := hy
      obtain ⟨s', hd, he⟩ := roundSpans_derives hs
      obtain ⟨s₀, hd₀, he₀⟩ := derives_rel hd
      exact ⟨s₀, hd₀, (live_leq hS hT hy).trans (LEq.of_eq (he.trans he₀))⟩
    · simp at hy
  | @span lb rb s y hy =>
    intro _ _ _
    exact ⟨s, .span s, (spanAnswer_spec hS hT lb s rb).1 y hy⟩
  | @or g a b h' y hg hh _ ih =>
    intro hL hR hl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hh
    obtain ⟨s₀, hd, he⟩ := ih hL hR hl
    exact ⟨s₀, by rw [hg]; exact derives_of_branch hc hd, he⟩
  | @call g n y hg _ ih =>
    intro hL hR hl
    obtain ⟨s₀, hd, he⟩ := ih hL hR hl
    exact ⟨s₀, by rw [hg]; exact .call hd, he⟩
  | @conv g a x hg _ ih =>
    intro hL hR hl
    rw [swap_den] at hl
    obtain ⟨s₀, hd, he⟩ := ih (pid_bden_swap hR) (pid_bden_swap hL) (live_inv hl)
    refine ⟨s₀.swap, by rw [hg]; exact .conv hd, ?_⟩
    rw [swap_den, swap_den, ← W_inv]
    exact he.inv
  | @seq g a b x w z hg _ _ hz ihx ihw =>
    intro hL hR hl
    have hzc := (composeLive_spec hS hT x w).1 z hz
    obtain ⟨lx, lw⟩ := live_comp (hzc.2.live hl)
    obtain ⟨sa, hda, hea⟩ := ihx hL pid_id lx
    obtain ⟨sb, hdb, heb⟩ := ihw pid_id hR lw
    have hzW : LEq P.theory z.den (W g.lb ((sa.den).comp sb.den) g.rb) :=
      hzc.trans ((hea.comp heb).trans (LEq.of_eq (by
        simp only [seqLeft, seqRight, W, wrap, bden, GRel.comp_id, GRel.id_comp, GRel.comp_assoc])))
    obtain ⟨s₀, hc, hs₀⟩ := compose_isSome (live_wrap_mid (hzW.2.live hl)).nonempty
    exact ⟨s₀, by rw [hg]; exact .seq hda hdb hc, by rw [hs₀]; exact hzW⟩
  | @seqPushL g a b x w z hg _ _ hz ihx ihw =>
    intro hL hR hl
    have hzc := (composeLive_spec hS hT x w).1 z hz
    obtain ⟨lx, lw⟩ := live_comp (hzc.2.live hl)
    obtain ⟨sa, hda, hea⟩ := ihx hL pid_id lx
    obtain ⟨sb, hdb, heb⟩ := ihw (pid_bound rfl) hR lw
    simp only [seqLeft, seqPushL, W, wrap, bden_bound (s := x.rightIface) rfl] at hea heb
    have e₁ : (x.den).comp ((x.rightIface.den).comp ((sb.den).comp (bden g.rb))) =
        (x.den).comp ((sb.den).comp (bden g.rb)) := by
      rw [← GRel.comp_assoc, comp_rightIface]
    have hzW : LEq P.theory z.den (W g.lb ((sa.den).comp sb.den) g.rb) :=
      hzc.trans (((LEq.refl _).comp heb).trans ((LEq.of_eq e₁).trans
        ((hea.comp (LEq.refl _)).trans (LEq.of_eq (by
          simp only [W, wrap, bden, GRel.comp_id, GRel.comp_assoc])))))
    obtain ⟨s₀, hc, hs₀⟩ := compose_isSome (live_wrap_mid (hzW.2.live hl)).nonempty
    exact ⟨s₀, by rw [hg]; exact .seq hda hdb hc, by rw [hs₀]; exact hzW⟩
  | @seqPushR g a b x w z hg _ _ hz ihw ihx =>
    intro hL hR hl
    have hzc := (composeLive_spec hS hT x w).1 z hz
    obtain ⟨lx, lw⟩ := live_comp (hzc.2.live hl)
    obtain ⟨sb, hdb, heb⟩ := ihw pid_id hR lw
    obtain ⟨sa, hda, hea⟩ := ihx hL (pid_bound rfl) lx
    simp only [seqRight, seqPushR, W, wrap, bden_bound (s := w.leftIface) rfl] at hea heb
    have e₁ : ((bden g.lb).comp ((sa.den).comp w.leftIface.den)).comp w.den =
        (bden g.lb).comp ((sa.den).comp w.den) := by
      rw [GRel.comp_assoc, GRel.comp_assoc, leftIface_comp]
    have hzW : LEq P.theory z.den (W g.lb ((sa.den).comp sb.den) g.rb) :=
      hzc.trans ((hea.comp (LEq.refl _)).trans ((LEq.of_eq e₁).trans
        (((LEq.refl _).comp ((LEq.refl _).comp heb)).trans (LEq.of_eq (by
          simp only [W, wrap, bden, GRel.id_comp, GRel.comp_assoc])))))
    obtain ⟨s₀, hc, hs₀⟩ := compose_isSome (live_wrap_mid (hzW.2.live hl)).nonempty
    exact ⟨s₀, by rw [hg]; exact .seq hda hdb hc, by rw [hs₀]; exact hzW⟩
  | @and g a b x w z hg _ _ hz ihx ihw =>
    intro hL hR hl
    have hzc := (meetLive_spec hS hT x w).1 z hz
    obtain ⟨lx, lw⟩ := live_meet (hzc.2.live hl)
    obtain ⟨sa, hda, hea⟩ := ihx hL hR lx
    obtain ⟨sb, hdb, heb⟩ := ihw hL hR lw
    simp only [andLeft, andRight] at hea heb
    have hzW : LEq P.theory z.den (W g.lb ((sa.den).meet sb.den) g.rb) :=
      hzc.trans ((hea.meet heb).trans ⟨meet_wrap_le _ _ _ _, meet_wrap_ge hL hR⟩)
    obtain ⟨s₀, hc, hs₀⟩ := meet_isSome (live_wrap_mid (hzW.2.live hl)).nonempty
    exact ⟨s₀, by rw [hg]; exact .and hda hdb hc, by rw [hs₀]; exact hzW⟩
  | @andPushL g a b x w z hg _ _ hz ihx ihw =>
    intro hL hR hl
    have hzc := (meetLive_spec hS hT x w).1 z hz
    obtain ⟨lx, lw⟩ := live_meet (hzc.2.live hl)
    obtain ⟨sa, hda, hea⟩ := ihx hL hR lx
    obtain ⟨sb, hdb, heb⟩ := ihw (pid_bound rfl) (pid_bound rfl) lw
    simp only [andPush, W, bden_bound (s := x.leftIface) rfl,
      bden_bound (s := x.rightIface) rfl] at heb
    have hzW : LEq P.theory z.den (W g.lb ((sa.den).meet sb.den) g.rb) :=
      hzc.trans (((LEq.refl _).meet heb).trans ((meet_iface (pid_diag rfl) (pid_diag rfl)
        (leftIface_comp x) (comp_rightIface x)).trans ((hea.meet (LEq.refl _)).trans
          (meet_wrap_one hL hR))))
    obtain ⟨s₀, hc, hs₀⟩ := meet_isSome (live_wrap_mid (hzW.2.live hl)).nonempty
    exact ⟨s₀, by rw [hg]; exact .and hda hdb hc, by rw [hs₀]; exact hzW⟩
  | @andPushR g a b x w z hg _ _ hz ihw ihx =>
    intro hL hR hl
    have hzc := (meetLive_spec hS hT x w).1 z hz
    obtain ⟨lx, lw⟩ := live_meet (hzc.2.live hl)
    obtain ⟨sb, hdb, heb⟩ := ihw hL hR lw
    obtain ⟨sa, hda, hea⟩ := ihx (pid_bound rfl) (pid_bound rfl) lx
    simp only [andPush, W, bden_bound (s := w.leftIface) rfl,
      bden_bound (s := w.rightIface) rfl] at hea
    have hzW : LEq P.theory z.den (W g.lb ((sa.den).meet sb.den) g.rb) := by
      refine hzc.trans ((hea.meet (LEq.refl _)).trans ?_)
      rw [meet_comm]
      refine (meet_iface (pid_diag rfl) (pid_diag rfl) (leftIface_comp w)
        (comp_rightIface w)).trans ?_
      rw [meet_comm]
      refine ((LEq.refl _).meet heb).trans ?_
      rw [meet_comm]
      refine (meet_wrap_one hL hR).trans (LEq.of_eq ?_)
      rw [meet_comm]
      rfl
    obtain ⟨s₀, hc, hs₀⟩ := meet_isSome (live_wrap_mid (hzW.2.live hl)).nonempty
    exact ⟨s₀, by rw [hg]; exact .and hda hdb hc, by rw [hs₀]; exact hzW⟩

/-! ## Derivations are machine derivations -/

/-- For every span an expression derives and any boundaries under which it
is live, the machine derives, by join strategies alone, an answer of a
branch of the expression covering the boundaries composed with the span up to
the theory, and equivalent to it when the boundaries are sub-identities. -/
theorem toGDerives {e : Rel} {s₀ : Span} (h : Derives P e s₀) :
    ∀ lb rb, Live P.theory (W lb s₀.den rb) →
    ∃ c ∈ orBranches e, ∃ y, GDerives P ⟨lb, c, rb⟩ y ∧
      LCov P.theory y.den (W lb s₀.den rb) ∧
      (PId (bden lb) → PId (bden rb) → LCov P.theory (W lb s₀.den rb) y.den) := by
  induction h with
  | span s =>
    intro lb rb hl
    obtain ⟨y, hy⟩ := (spanAnswer_spec hS hT lb s rb).2 hl
    have he := (spanAnswer_spec hS hT lb s rb).1 y hy
    exact ⟨.span s, by simp [orBranches], y, .span hy, he.1, fun _ _ => he.2⟩
  | orl _ ih =>
    intro lb rb hl
    obtain ⟨c, hc, rest⟩ := ih lb rb hl
    exact ⟨c, by simp only [orBranches, List.mem_append]; exact Or.inl hc, rest⟩
  | orr _ ih =>
    intro lb rb hl
    obtain ⟨c, hc, rest⟩ := ih lb rb hl
    exact ⟨c, by simp only [orBranches, List.mem_append]; exact Or.inr hc, rest⟩
  | @seq a b s₁ s₂ s _ _ hc ih₁ ih₂ =>
    intro lb rb hl
    have hsplit : W lb s.den rb = (W lb s₁.den none).comp (W none s₂.den rb) := by
      rw [compose_some hc]
      simp only [W, wrap, bden, GRel.comp_id, GRel.id_comp, GRel.comp_assoc]
    rw [hsplit] at hl ⊢
    obtain ⟨l₁, l₂⟩ := live_comp hl
    obtain ⟨c₁, hc₁, x, hx, hx₁, hx₂⟩ := ih₁ lb none l₁
    obtain ⟨c₂, hc₂, w, hw, hw₁, hw₂⟩ := ih₂ none rb l₂
    have hcov : LCov P.theory ((x.den).comp w.den) _ := hx₁.comp hw₁
    obtain ⟨z, hz⟩ := (composeLive_spec hS hT x w).2 (hcov.live hl)
    have hze := (composeLive_spec hS hT x w).1 z hz
    refine ⟨.seq a b, by simp [orBranches], z,
      GDerives.seq (g := ⟨lb, .seq a b, rb⟩) rfl (lift_leaf hc₁ hx) (lift_leaf hc₂ hw) hz,
      hze.1.trans hcov, fun hL hR => ((hx₂ hL pid_id).comp (hw₂ pid_id hR)).trans hze.2⟩
  | @and a b s₁ s₂ s _ _ hc ih₁ ih₂ =>
    intro lb rb hl
    rw [meet_some hc] at hl ⊢
    obtain ⟨l₁, l₂⟩ := live_meet ((meet_wrap_le (T := P.theory) _ _ _ _).live hl)
    obtain ⟨c₁, hc₁, x, hx, hx₁, hx₂⟩ := ih₁ lb rb l₁
    obtain ⟨c₂, hc₂, w, hw, hw₁, hw₂⟩ := ih₂ lb rb l₂
    have hcov : LCov P.theory ((x.den).meet w.den) (W lb ((s₁.den).meet s₂.den) rb) :=
      (hx₁.meet hw₁).trans (meet_wrap_le _ _ _ _)
    obtain ⟨z, hz⟩ := (meetLive_spec hS hT x w).2 (hcov.live hl)
    have hze := (meetLive_spec hS hT x w).1 z hz
    refine ⟨.and a b, by simp [orBranches], z,
      GDerives.and (g := ⟨lb, .and a b, rb⟩) rfl (lift_leaf hc₁ hx) (lift_leaf hc₂ hw) hz,
      hze.1.trans hcov, fun hL hR => ?_⟩
    exact (meet_wrap_ge hL hR).trans (((hx₂ hL hR).meet (hw₂ hL hR)).trans hze.2)
  | @conv a s _ ih =>
    intro lb rb hl
    rw [swap_den, ← W_inv] at hl ⊢
    obtain ⟨c, hc, x, hx, hx₁, hx₂⟩ :=
      ih (rb.map Span.swap) (lb.map Span.swap) (live_inv hl)
    refine ⟨.conv a, by simp [orBranches], x.swap,
      GDerives.conv (g := ⟨lb, .conv a, rb⟩) rfl (lift_leaf hc hx), ?_, fun hL hR => ?_⟩
    · rw [swap_den]; exact hx₁.inv
    · rw [swap_den]; exact (hx₂ (pid_bden_swap hR) (pid_bden_swap hL)).inv
  | @call n s _ ih =>
    intro lb rb hl
    obtain ⟨c, hc, x, hx, hx₁, hx₂⟩ := ih lb rb hl
    exact ⟨.call n, by simp [orBranches], x,
      GDerives.call (g := ⟨lb, .call n, rb⟩) rfl (lift_leaf hc hx), hx₁, hx₂⟩

end Lift

end Lifting

open Lifting in
/-- Boundary lifting, from `Kernel.simplify_exact`: machine derivations are
derivations up to the theory (`Lifting.toDerives`), and derivations are
machine derivations up to the theory (`Lifting.toGDerives`). -/
theorem boundary_lifting (hS : Obligation.simplify_exact) : Obligation.boundary_lifting := by
  intro P g hT hdiag
  obtain ⟨lb, e, rb⟩ := g
  have hL : PId (bden lb) := pid_bden fun b hb => hdiag b (by simp [hb])
  have hR : PId (bden rb) := pid_bden fun b hb => hdiag b (by simp [hb])
  refine ⟨fun y hy hnd => ?_, fun y₀ hy₀ z hz hnd => ?_⟩
  · have hl := not_dead_iff.1 hnd
    obtain ⟨s₀, hd, he⟩ := toDerives hS hT hy hL hR hl
    have hls : Live P.theory (W none s₀.den none) := by
      rw [W_none]; exact live_wrap_mid (he.2.live hl)
    obtain ⟨c, hc, y₀, hy₀, h₁, h₂⟩ := toGDerives hS hT hd none none hls
    rw [W_none] at h₁ h₂
    have hW : LEq P.theory (W lb y₀.den rb) y.den :=
      (LEq.W ⟨h₁, h₂ pid_id pid_id⟩ lb rb).trans he.symm
    obtain ⟨z, hz⟩ := (spanAnswer_spec hS hT lb y₀ rb).2 (hW.1.live hl)
    have hzW := (spanAnswer_spec hS hT lb y₀ rb).1 z hz
    exact ⟨y₀, lift_leaf hc hy₀, z, hz, coversLive_iff.2 (hzW.1.trans hW.1),
      coversLive_iff.2 (hW.2.trans hzW.2)⟩
  · have hl := not_dead_iff.1 hnd
    have hzW := (spanAnswer_spec hS hT lb y₀ rb).1 z hz
    have hlW := hzW.2.live hl
    obtain ⟨s₀, hd, he⟩ := toDerives hS hT hy₀ pid_id pid_id (live_wrap_mid hlW)
    rw [W_none] at he
    have hWs : LEq P.theory (W lb s₀.den rb) (W lb y₀.den rb) := LEq.W he.symm lb rb
    obtain ⟨c, hc, y, hy, h₁, -⟩ := toGDerives hS hT hd lb rb (hWs.1.live hlW)
    exact ⟨y, lift_leaf hc hy, coversLive_iff.2 (h₁.trans (hWs.1.trans hzW.2))⟩

end R001

end RwLog
