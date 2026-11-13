/-
# Relations up to the theory, and up to stores

The vocabulary proofs about answers are written in. All of it is about sets
of ground triples (`GRel`) and is independent of any rung.

* In every model of the theory: `LCov T R S` (`R` relates every pair `S`
  relates), `LEq` (both ways), `Live T R` (some model lets `R` relate a
  pair), `DeadR T R` (none does). `Span.CoversLive` is `LCov` on
  denotations.
* Sub-identities (`PId`) and wrapping a relation in two of them (`wrap`):
  what boundaries are.
* Answers standing for relations: `Backed T Y X` (the converse inclusion,
  also for the pairs of the triples whatever their stores), `Ref T a X` (the
  answer `a` is backed by `X` and covers it), `DC T A X` (`X` is dead or some
  answer of `A` covers it). Soundness is `Ref`, completeness is `DC`
  (`Rungs/Framework/Tier0.lean`).
* Exactly, whatever the theory: `GCov R S` (every triple of `S` is matched by
  one of `R` with the same pair and a smaller store; `Span.Covers` is `GCov`
  on denotations), `GEq` (both ways), and `Dom`, the same thing read as
  `LCov` for the empty theory so that the algebra above applies.

Every operator of the relation algebra preserves these.
-/
import RwLog.SpanLayer.Coverage
import RwLog.SpanLayer.Algebra

namespace RwLog

variable {T : Theory}

/-! ## Pairs in a model -/

theorem at_comp (R S : GRel) (M : Interp) : (R.comp S).at M = PRel.comp (R.at M) (S.at M) := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨_, ⟨m, S₁, S₂, h₁, h₂, rfl⟩, hM⟩
    obtain ⟨hM₁, hM₂⟩ := union_subset_iff_coe.1 hM
    exact ⟨m, ⟨S₁, h₁, hM₁⟩, ⟨S₂, h₂, hM₂⟩⟩
  · rintro ⟨m, ⟨S₁, h₁, hM₁⟩, ⟨S₂, h₂, hM₂⟩⟩
    exact ⟨S₁ ∪ S₂, ⟨m, S₁, S₂, h₁, h₂, rfl⟩, union_subset_iff_coe.2 ⟨hM₁, hM₂⟩⟩

theorem at_meet (R S : GRel) (M : Interp) : (R.meet S).at M = R.at M ∩ S.at M := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨_, ⟨S₁, S₂, h₁, h₂, rfl⟩, hM⟩
    obtain ⟨hM₁, hM₂⟩ := union_subset_iff_coe.1 hM
    exact ⟨⟨S₁, h₁, hM₁⟩, ⟨S₂, h₂, hM₂⟩⟩
  · rintro ⟨⟨S₁, h₁, hM₁⟩, ⟨S₂, h₂, hM₂⟩⟩
    exact ⟨S₁ ∪ S₂, ⟨S₁, S₂, h₁, h₂, rfl⟩, union_subset_iff_coe.2 ⟨hM₁, hM₂⟩⟩

theorem at_inv (R : GRel) (M : Interp) : R.inv.at M = PRel.inv (R.at M) := by
  ext ⟨a, b⟩
  exact ⟨fun ⟨S, h, hM⟩ => ⟨S, h, hM⟩, fun ⟨S, h, hM⟩ => ⟨S, h, hM⟩⟩

/-! ## Covering up to the theory -/

/-- In every model of the theory, `R` relates every pair `S` relates. -/
def LCov (T : Theory) (R S : GRel) : Prop := ∀ M, T.Model M → S.at M ⊆ R.at M

/-- In every model of the theory, `R` and `S` relate the same pairs. -/
def LEq (T : Theory) (R S : GRel) : Prop := LCov T R S ∧ LCov T S R

/-- Some model of the theory lets `R` relate a pair. -/
def Live (T : Theory) (R : GRel) : Prop := ∃ M, T.Model M ∧ (R.at M).Nonempty

theorem coversLive_iff {a s : Span} : a.CoversLive T s ↔ LCov T a.den s.den := by
  simp only [Span.CoversLive, LCov, Span.denAt_eq]

theorem not_dead_iff {s : Span} : ¬ s.Dead T ↔ Live T s.den := by
  simp only [Span.Dead, Live, Span.denAt_eq, not_forall, Set.nonempty_iff_ne_empty, exists_prop]

theorem LCov.refl (R : GRel) : LCov T R R := fun _ _ => le_rfl

theorem LCov.trans {R S U : GRel} (h₁ : LCov T R S) (h₂ : LCov T S U) : LCov T R U :=
  fun M hM => (h₂ M hM).trans (h₁ M hM)

theorem LCov.of_eq {R S : GRel} (h : R = S) : LCov T R S := h ▸ LCov.refl R

theorem LCov.of_sub {R S : GRel} (h : ∀ a b X, (a, b, X) ∈ S → ∃ Y, (a, b, Y) ∈ R ∧ Y ⊆ X) :
    LCov T R S := by
  rintro M - ⟨a, b⟩ ⟨X, hx, hM⟩
  obtain ⟨Y, hy, hYX⟩ := h a b X hx
  exact ⟨Y, hy, fun t ht => hM (hYX ht)⟩

theorem LCov.live {R S : GRel} (h : LCov T R S) (hS : Live T S) : Live T R := by
  obtain ⟨M, hM, p, hp⟩ := hS
  exact ⟨M, hM, p, h M hM hp⟩

theorem LCov.comp {R R' S S' : GRel} (h₁ : LCov T R R') (h₂ : LCov T S S') :
    LCov T (R.comp S) (R'.comp S') := by
  intro M hM
  rw [at_comp, at_comp]
  rintro p ⟨m, ha, hb⟩
  exact ⟨m, h₁ M hM ha, h₂ M hM hb⟩

theorem LCov.meet {R R' S S' : GRel} (h₁ : LCov T R R') (h₂ : LCov T S S') :
    LCov T (R.meet S) (R'.meet S') := by
  intro M hM
  rw [at_meet, at_meet]
  exact Set.inter_subset_inter (h₁ M hM) (h₂ M hM)

theorem LCov.inv {R S : GRel} (h : LCov T R S) : LCov T R.inv S.inv := by
  intro M hM
  rw [at_inv, at_inv]
  exact fun p hp => h M hM hp

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
  obtain ⟨M, hM, p, hp⟩ := h
  rw [at_comp] at hp
  obtain ⟨m, ha, hb⟩ := hp
  exact ⟨⟨M, hM, _, ha⟩, ⟨M, hM, _, hb⟩⟩

theorem live_meet {R S : GRel} (h : Live T (R.meet S)) : Live T R ∧ Live T S := by
  obtain ⟨M, hM, p, hp⟩ := h
  rw [at_meet] at hp
  exact ⟨⟨M, hM, _, hp.1⟩, ⟨M, hM, _, hp.2⟩⟩

theorem live_inv {R : GRel} (h : Live T R.inv) : Live T R := by
  obtain ⟨M, hM, p, hp⟩ := h
  rw [at_inv] at hp
  exact ⟨M, hM, _, hp⟩

theorem live_inv' {R : GRel} (h : Live T R) : Live T R.inv := by
  obtain ⟨M, hM, ⟨a, b⟩, hp⟩ := h
  refine ⟨M, hM, (b, a), ?_⟩
  rw [at_inv]
  exact hp

theorem Live.nonempty {R : GRel} (h : Live T R) : R.Nonempty := by
  obtain ⟨M, -, p, S, hS, -⟩ := h
  exact ⟨_, hS⟩

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

/-! ## Dead relations, answers and coverage -/

/-- No model of the theory lets the relation relate a pair. -/
def DeadR (T : Theory) (X : GRel) : Prop := ∀ M, T.Model M → X.at M = ∅

/-- `Y` relates only pairs `X` relates: in every model of the theory, and
among the pairs of their triples. -/
def Backed (T : Theory) (Y X : GRel) : Prop := LCov T X Y ∧ Y.at Set.univ ⊆ X.at Set.univ

/-- The answer `a` stands for `X`: it relates only pairs of `X`, and in every
model of the theory every pair of `X`. -/
def Ref (T : Theory) (a : Span) (X : GRel) : Prop := Backed T a.den X ∧ LCov T a.den X

/-- `X` is dead, or one answer of `A` covers it. -/
def DC (T : Theory) (A : List Span) (X : GRel) : Prop := DeadR T X ∨ ∃ a ∈ A, LCov T a.den X

theorem lcov_of_subset {X Y : GRel} (h : X ⊆ Y) : LCov T Y X := fun M _ => GRel.at_mono h M

theorem lcov_of_covers {a b : Span} (h : a.Covers b) : LCov T a.den b.den :=
  coversLive_iff.1 h.live

theorem Backed.of_subset {Y X : GRel} (h : Y ⊆ X) : Backed T Y X :=
  ⟨lcov_of_subset h, GRel.at_mono h _⟩

theorem Backed.refl (X : GRel) : Backed T X X := ⟨LCov.refl X, le_rfl⟩

theorem Backed.trans {Z Y X : GRel} (h₁ : Backed T Z Y) (h₂ : Backed T Y X) : Backed T Z X :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem Backed.comp {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Backed T Y₁ X₁) (h₂ : Backed T Y₂ X₂) :
    Backed T (Y₁.comp Y₂) (X₁.comp X₂) := by
  refine ⟨h₁.1.comp h₂.1, ?_⟩
  rw [at_comp, at_comp]
  rintro p ⟨m, ha, hb⟩
  exact ⟨m, h₁.2 ha, h₂.2 hb⟩

theorem Backed.meet {Y₁ X₁ Y₂ X₂ : GRel} (h₁ : Backed T Y₁ X₁) (h₂ : Backed T Y₂ X₂) :
    Backed T (Y₁.meet Y₂) (X₁.meet X₂) := by
  refine ⟨h₁.1.meet h₂.1, ?_⟩
  rw [at_meet, at_meet]
  exact Set.inter_subset_inter h₁.2 h₂.2

theorem Backed.inv {Y X : GRel} (h : Backed T Y X) : Backed T Y.inv X.inv := by
  refine ⟨h.1.inv, ?_⟩
  rw [at_inv, at_inv]
  exact fun p hp => h.2 hp

theorem Ref.trans {a : Span} {Y X : GRel} (h : Ref T a Y) (hb : Backed T Y X) (hd : LCov T Y X) :
    Ref T a X := ⟨h.1.trans hb, h.2.trans hd⟩

theorem Ref.of_eq {a : Span} {Y X : GRel} (h : Ref T a Y) (e : Y = X) : Ref T a X := e ▸ h

theorem Ref.self (a : Span) : Ref T a a.den := ⟨Backed.refl _, LCov.refl _⟩

theorem Ref.swap {a : Span} {X : GRel} (h : Ref T a X) : Ref T a.swap X.inv := by
  unfold Ref; rw [swap_den]; exact ⟨h.1.inv, h.2.inv⟩

/-- An answer stands for a relation with a triple. -/
theorem Ref.nonempty {a : Span} {X : GRel} (h : Ref T a X) : X.Nonempty := by
  obtain ⟨y, hy⟩ := Span.den_nonempty a
  obtain ⟨S, hx, -⟩ := h.1.2 (show (y.1, y.2.1) ∈ a.den.at Set.univ from
    ⟨y.2.2, hy, Set.subset_univ _⟩)
  exact ⟨_, hx⟩

theorem at_empty (M : Interp) : (∅ : GRel).at M = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ => h

theorem DeadR.of_dom {X Y : GRel} (hd : LCov T Y X) (h : DeadR T Y) : DeadR T X :=
  fun M hM => Set.subset_eq_empty (hd M hM) (h M hM)

/-- A relation covered by nothing is dead. -/
theorem DeadR.of_empty {X : GRel} (hd : LCov T ∅ X) : DeadR T X :=
  fun M hM => Set.subset_eq_empty (hd M hM) (at_empty M)

theorem DC.dom {A : List Span} {X Y : GRel} (hd : LCov T Y X) (h : DC T A Y) : DC T A X := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl (h.of_dom hd)
  · exact Or.inr ⟨a, ha, h.trans hd⟩

theorem DC.of_eq {A : List Span} {X Y : GRel} (h : DC T A Y) (e : Y = X) : DC T A X := e ▸ h

theorem DC.mono {A A' : List Span} {X : GRel} (h : DC T A X) (hA : ∀ a ∈ A, a ∈ A') :
    DC T A' X := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, hA a ha, h⟩

theorem DC.covers {A A' : List Span} {X : GRel} (h : DC T A X)
    (hA : ∀ a ∈ A, ∃ b ∈ A', b.Covers a) : DC T A' X := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · obtain ⟨b, hb, hc⟩ := hA a ha
    exact Or.inr ⟨b, hb, (lcov_of_covers hc).trans h⟩

theorem DeadR.inv {X : GRel} (h : DeadR T X) : DeadR T X.inv := by
  intro M hM
  rw [at_inv, h M hM]
  exact Set.eq_empty_of_forall_notMem fun _ h => h

theorem DC.swap {A : List Span} {X : GRel} (h : DC T A X) : DC T (A.map Span.swap) X.inv := by
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl h.inv
  · refine Or.inr ⟨a.swap, List.mem_map_of_mem ha, ?_⟩
    rw [swap_den]; exact h.inv

theorem DeadR.comp_left {X Y : GRel} (h : DeadR T X) : DeadR T (X.comp Y) := by
  intro M hM
  rw [at_comp, h M hM]
  exact Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ => h

theorem DeadR.comp_right {X Y : GRel} (h : DeadR T Y) : DeadR T (X.comp Y) := by
  intro M hM
  rw [at_comp, h M hM]
  exact Set.eq_empty_of_forall_notMem fun _ ⟨_, _, h⟩ => h

theorem DeadR.meet_left {X Y : GRel} (h : DeadR T X) : DeadR T (X.meet Y) := by
  intro M hM
  rw [at_meet, h M hM, Set.empty_inter]

theorem DeadR.meet_right {X Y : GRel} (h : DeadR T Y) : DeadR T (X.meet Y) := by
  intro M hM
  rw [at_meet, h M hM, Set.inter_empty]

theorem deadR_den {s : Span} : DeadR T s.den ↔ s.Dead T := by
  simp only [DeadR, Span.Dead, Span.denAt_eq]

/-! ## Exact coverage of ground relations -/

/-- `R` covers `S`: every triple of `S` is matched by a triple of `R` with the
same pair and a contained store. `Span.Covers a s` is `GCov a.den s.den`. -/
def GCov (R S : GRel) : Prop :=
  ∀ x ∈ S, ∃ y ∈ R, y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 ⊆ x.2.2

def GEq (R S : GRel) : Prop := GCov R S ∧ GCov S R

theorem GCov.refl (R : GRel) : GCov R R := fun x hx => ⟨x, hx, rfl, rfl, le_rfl⟩

theorem GCov.trans {R S U : GRel} (h₁ : GCov R S) (h₂ : GCov S U) : GCov R U := by
  intro x hx
  obtain ⟨y, hy, a1, a2, a3⟩ := h₂ x hx
  obtain ⟨z, hz, b1, b2, b3⟩ := h₁ y hy
  exact ⟨z, hz, b1.trans a1, b2.trans a2, b3.trans a3⟩

theorem GCov.of_eq {R S : GRel} (h : R = S) : GCov R S := h ▸ GCov.refl R

theorem GCov.comp {R R' S S' : GRel} (h₁ : GCov R R') (h₂ : GCov S S') :
    GCov (R.comp S) (R'.comp S') := by
  rintro ⟨a, b, U⟩ ⟨m, U₁, U₂, hR, hS, rfl⟩
  obtain ⟨⟨a', m', V₁⟩, hy, e1, e2, e3⟩ := h₁ _ hR
  obtain ⟨⟨m'', b', V₂⟩, hz, f1, f2, f3⟩ := h₂ _ hS
  simp only at e1 e2 e3 f1 f2 f3
  refine ⟨(a', b', V₁ ∪ V₂), ⟨m', V₁, V₂, hy, ?_, rfl⟩, e1, f2, Finset.union_subset_union e3 f3⟩
  rw [e2, ← f1]; exact hz

theorem GCov.meet {R R' S S' : GRel} (h₁ : GCov R R') (h₂ : GCov S S') :
    GCov (R.meet S) (R'.meet S') := by
  rintro ⟨a, b, U⟩ ⟨U₁, U₂, hR, hS, rfl⟩
  obtain ⟨⟨a', b', V₁⟩, hy, e1, e2, e3⟩ := h₁ _ hR
  obtain ⟨⟨a'', b'', V₂⟩, hz, f1, f2, f3⟩ := h₂ _ hS
  simp only at e1 e2 e3 f1 f2 f3
  refine ⟨(a', b', V₁ ∪ V₂), ⟨V₁, V₂, hy, ?_, rfl⟩, e1, e2, Finset.union_subset_union e3 f3⟩
  rw [e1, e2, ← f1, ← f2]; exact hz

theorem GCov.inv {R S : GRel} (h : GCov R S) : GCov R.inv S.inv := by
  rintro ⟨a, b, U⟩ hx
  obtain ⟨⟨b', a', V⟩, hy, e1, e2, e3⟩ := h (b, a, U) hx
  exact ⟨(a', b', V), hy, e2, e1, e3⟩

theorem GEq.refl (R : GRel) : GEq R R := ⟨GCov.refl R, GCov.refl R⟩
theorem GEq.symm {R S : GRel} (h : GEq R S) : GEq S R := ⟨h.2, h.1⟩
theorem GEq.trans {R S U : GRel} (h₁ : GEq R S) (h₂ : GEq S U) : GEq R U :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
theorem GEq.of_eq {R S : GRel} (h : R = S) : GEq R S := h ▸ GEq.refl R
theorem GEq.comp {R R' S S' : GRel} (h₁ : GEq R R') (h₂ : GEq S S') : GEq (R.comp S) (R'.comp S') :=
  ⟨h₁.1.comp h₂.1, h₁.2.comp h₂.2⟩
theorem GEq.meet {R R' S S' : GRel} (h₁ : GEq R R') (h₂ : GEq S S') : GEq (R.meet S) (R'.meet S') :=
  ⟨h₁.1.meet h₂.1, h₁.2.meet h₂.2⟩
theorem GEq.inv {R S : GRel} (h : GEq R S) : GEq R.inv S.inv := ⟨h.1.inv, h.2.inv⟩

theorem GCov.eq_empty {R S : GRel} (h : GCov R S) (hR : R = ∅) : S = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨y, hy, -⟩ := h x hx
  rw [hR] at hy; exact hy

theorem Span.Equiv.geq {a b : Span} (h : a.Equiv b) : GEq a.den b.den := ⟨h.1, h.2⟩

theorem Span.Equiv.of_geq {a b : Span} (h : GEq a.den b.den) : a.Equiv b := ⟨h.1, h.2⟩

theorem swap_geq (a : Span) : GEq a.swap.den a.den.inv := GEq.of_eq (swap_den a)

/-! ## Domination -/

/-- `X` dominates `Y`: each triple of `Y` is matched by one of `X` with the
same pair and a smaller store. -/
abbrev Dom (X Y : GRel) : Prop := LCov ([] : Theory) X Y

theorem model_nil (M : Interp) : Theory.Model [] M := fun _ h => absurd h List.not_mem_nil

theorem dom_iff {X Y : GRel} : Dom X Y ↔ ∀ a b S, (a, b, S) ∈ Y → ∃ S', (a, b, S') ∈ X ∧ S' ⊆ S := by
  constructor
  · intro h a b S hS
    obtain ⟨S', hS', hM⟩ := h (↑S) (model_nil _) (show (a, b) ∈ Y.at ↑S from ⟨S, hS, le_rfl⟩)
    exact ⟨S', hS', fun t ht => hM ht⟩
  · intro h
    exact LCov.of_sub h

theorem covers_iff_dom {a s : Span} : a.Covers s ↔ Dom a.den s.den := by
  rw [dom_iff]
  constructor
  · intro h x y S hx
    obtain ⟨u, hu, h1, h2, h3⟩ := h _ hx
    obtain ⟨u1, u2, u3⟩ := u
    simp only at h1 h2 h3
    subst h1 h2
    exact ⟨u3, hu, h3⟩
  · rintro h ⟨x, y, S⟩ hx
    obtain ⟨S', hS', hsub⟩ := h x y S hx
    exact ⟨(x, y, S'), hS', rfl, rfl, hsub⟩

theorem dom_of_covers {a s : Span} (h : a.Covers s) : Dom a.den s.den := covers_iff_dom.1 h

theorem covers_of_dom {a s : Span} (h : Dom a.den s.den) : a.Covers s := covers_iff_dom.2 h

theorem dom_of_subset {X Y : GRel} (h : Y ⊆ X) : Dom X Y := fun M _ => GRel.at_mono h M

theorem dom_of_eq {X Y : GRel} (h : X = Y) : Dom X Y := LCov.of_eq h

theorem Dom.nonempty {X Y : GRel} (h : Dom X Y) (hY : Y.Nonempty) : X.Nonempty := by
  obtain ⟨⟨a, b, S⟩, hS⟩ := hY
  obtain ⟨S', hS', -⟩ := dom_iff.1 h a b S hS
  exact ⟨_, hS'⟩

end RwLog
