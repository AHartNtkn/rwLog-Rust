/-
# Rung R001, Symmetry: rung-zero unfolding of mirrored goals

Every goal races rung zero's unfolding (`unfoldAnswers`, `unfoldFinal`). This
file compares rung zero's products of a goal of the run with those of the
corresponding goal of the mirrored run.

Products are compared factor by factor (`FE`, `PD`, `PCorr`), in two
directions: `m = true` compares a product with a product of the mirror, read
in reverse with converse spans, and `m = false` compares two products of the
same direction. Spans correspond up to mutual coverage of their meanings
(`GEq`), and a factor that is not a span corresponds to one that contains
calls exactly when it does and derives corresponding spans (`DCorr`). Within
one direction, products are invariant under the canonical form of `|`, under
re-association of `;` and under equivalent boundary spans; across directions,
the products of an expression correspond to those of its mirror in the
mirrored program. So a goal and its mirror finish rung zero in the same
round, and derive corresponding spans.
-/
import RwLog.Rungs.R001.Proofs.SymmetryCands
import RwLog.Rungs.R000.Properties

namespace RwLog

namespace R001

namespace Symmetry

open R000

/-! ## Orientation of meanings -/

/-- A meaning, or its converse when `m` holds. -/
def fm : Bool → GRel → GRel
  | true, R => R.inv
  | false, R => R

@[simp] theorem fm_false (R : GRel) : fm false R = R := rfl
@[simp] theorem fm_true (R : GRel) : fm true R = R.inv := rfl

theorem fm_fm (m₁ m₂ : Bool) (R : GRel) : fm m₂ (fm m₁ R) = fm (m₁ ^^ m₂) R := by
  cases m₁ <;> cases m₂ <;> simp [GRel.inv_inv]

theorem GEq.fm {R S : GRel} (m : Bool) (h : GEq R S) : GEq (fm m R) (fm m S) := by
  cases m
  · exact h
  · exact h.inv

theorem fm_empty (m : Bool) : fm m ∅ = ∅ := by
  cases m
  · rfl
  · ext ⟨a, b, X⟩; simp [GRel.inv]

/-- Corresponding optional fusion results: both absent, or both present with
corresponding meanings. -/
def OC (m : Bool) : Span → Span → Prop := fun c c' => GEq c'.den (fm m c.den)

theorem optRel_of {m : Bool} {o o' : Option Span} (h : GEq (Span.denO o') (fm m (Span.denO o))) :
    Option.Rel (OC m) o o' := by
  cases o with
  | none =>
    have : Span.denO o' = ∅ :=
      h.2.eq_empty (by rw [show Span.denO none = ∅ from rfl, fm_empty])
    rw [(denO_empty_iff _).1 this]; exact .none
  | some a =>
    cases o' with
    | none =>
      have he : fm m a.den = ∅ := h.1.eq_empty rfl
      obtain ⟨⟨x, y, U⟩, hx⟩ := Span.den_nonempty a
      cases m
      · rw [fm_false] at he; rw [he] at hx; exact hx.elim
      · rw [fm_true] at he
        have : (y, x, U) ∈ (a.den).inv := hx
        rw [he] at this; exact this.elim
    | some b => exact .some h

/-- Fusing two pairs of corresponding spans, in reverse order under a
mirror. -/
def cf : Bool → Span → Span → Option Span
  | true, a', b' => b'.compose a'
  | false, a', b' => a'.compose b'

theorem compose_corr {m : Bool} {a b a' b' : Span} (ha : OC m a a') (hb : OC m b b') :
    Option.Rel (OC m) (a.compose b) (cf m a' b') := by
  apply optRel_of
  rw [compose_den]
  cases m
  · simp only [cf, compose_den, fm_false]; exact ha.comp hb
  · simp only [cf, compose_den, fm_true, GRel.inv_comp]; exact hb.comp ha

theorem meet_corr {m : Bool} {a b a' b' : Span} (ha : OC m a a') (hb : OC m b b') :
    Option.Rel (OC m) (a.meet b) (a'.meet b') := by
  apply optRel_of
  rw [meet_den, meet_den]
  cases m
  · exact ha.meet hb
  · simp only [fm_true, GRel.inv_meet]; exact ha.meet hb

/-! ## Corresponding lists of derived spans -/

/-- Every span of either list has a corresponding span in the other. -/
def DCorr (m : Bool) (xs ys : List Span) : Prop :=
  (∀ s ∈ xs, ∃ s' ∈ ys, OC m s s') ∧ (∀ s' ∈ ys, ∃ s ∈ xs, OC m s s')

theorem OC.symm {m : Bool} {a b : Span} (h : OC m a b) : OC m b a := by
  unfold OC at *
  have := (h.fm m).symm
  rwa [fm_fm, Bool.xor_self, fm_false] at this

theorem OC.trans {m₁ m₂ : Bool} {a b c : Span} (h₁ : OC m₁ a b) (h₂ : OC m₂ b c) :
    OC (m₁ ^^ m₂) a c := by
  unfold OC at *
  rw [← fm_fm]; exact h₂.trans (h₁.fm m₂)

theorem OC.refl (a : Span) : OC false a a := GEq.refl _

theorem DCorr.refl (xs : List Span) : DCorr false xs xs :=
  ⟨fun s hs => ⟨s, hs, OC.refl s⟩, fun s hs => ⟨s, hs, OC.refl s⟩⟩

theorem DCorr.symm {m : Bool} {xs ys : List Span} (h : DCorr m xs ys) : DCorr m ys xs :=
  ⟨fun s hs => let ⟨t, ht, e⟩ := h.2 s hs; ⟨t, ht, e.symm⟩,
   fun s hs => let ⟨t, ht, e⟩ := h.1 s hs; ⟨t, ht, e.symm⟩⟩

theorem DCorr.trans {m₁ m₂ : Bool} {xs ys zs : List Span} (h₁ : DCorr m₁ xs ys)
    (h₂ : DCorr m₂ ys zs) : DCorr (m₁ ^^ m₂) xs zs := by
  constructor
  · intro s hs
    obtain ⟨t, ht, e⟩ := h₁.1 s hs
    obtain ⟨u, hu, e'⟩ := h₂.1 t ht
    exact ⟨u, hu, e.trans e'⟩
  · intro u hu
    obtain ⟨t, ht, e'⟩ := h₂.2 u hu
    obtain ⟨s, hs, e⟩ := h₁.2 t ht
    exact ⟨s, hs, e.trans e'⟩

theorem DCorr.trans' {m : Bool} {xs ys zs : List Span} (h₁ : DCorr m xs ys)
    (h₂ : DCorr false ys zs) : DCorr m xs zs := by
  simpa using h₁.trans h₂

theorem DCorr.trans'' {m : Bool} {xs ys zs : List Span} (h₁ : DCorr false xs ys)
    (h₂ : DCorr m ys zs) : DCorr m xs zs := by
  simpa using h₁.trans h₂

theorem DCorr.append {m : Bool} {xs ys xs' ys' : List Span} (h₁ : DCorr m xs xs')
    (h₂ : DCorr m ys ys') : DCorr m (xs ++ ys) (xs' ++ ys') := by
  constructor
  · intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨t, ht, e⟩ := h₁.1 s hs; exact ⟨t, List.mem_append_left _ ht, e⟩
    · obtain ⟨t, ht, e⟩ := h₂.1 s hs; exact ⟨t, List.mem_append_right _ ht, e⟩
  · intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨t, ht, e⟩ := h₁.2 s hs; exact ⟨t, List.mem_append_left _ ht, e⟩
    · obtain ⟨t, ht, e⟩ := h₂.2 s hs; exact ⟨t, List.mem_append_right _ ht, e⟩

theorem DCorr.of_subset {xs ys : List Span} (h₁ : ∀ x ∈ xs, x ∈ ys) (h₂ : ∀ y ∈ ys, y ∈ xs) :
    DCorr false xs ys :=
  ⟨fun s hs => ⟨s, h₁ s hs, OC.refl s⟩, fun s hs => ⟨s, h₂ s hs, OC.refl s⟩⟩

/-- All fusions of a span of one list with a span of another. -/
def cmp (xs ys : List Span) : List Span := xs.flatMap fun s => ys.filterMap s.compose

def mcmp (xs ys : List Span) : List Span := xs.flatMap fun s => ys.filterMap s.meet

/-- `cmp` in the order of a direction: reversed under a mirror. -/
def cmpD : Bool → List Span → List Span → List Span
  | true, xs, ys => cmp ys xs
  | false, xs, ys => cmp xs ys

theorem mem_cmp {xs ys : List Span} {u : Span} :
    u ∈ cmp xs ys ↔ ∃ s ∈ xs, ∃ t ∈ ys, s.compose t = some u := by
  simp [cmp]

theorem mem_mcmp {xs ys : List Span} {u : Span} :
    u ∈ mcmp xs ys ↔ ∃ s ∈ xs, ∃ t ∈ ys, s.meet t = some u := by
  simp [mcmp]

theorem cmp_corr {m : Bool} {xs ys xs' ys' : List Span} (hx : DCorr m xs xs')
    (hy : DCorr m ys ys') : DCorr m (cmp xs ys) (cmpD m xs' ys') := by
  constructor
  · intro u hu
    obtain ⟨s, hs, t, ht, hst⟩ := mem_cmp.1 hu
    obtain ⟨s', hs', es⟩ := hx.1 s hs
    obtain ⟨t', ht', et⟩ := hy.1 t ht
    have hc := compose_corr es et
    rw [hst] at hc
    cases hcf : cf m s' t' with
    | none => rw [hcf] at hc; cases hc
    | some u' =>
      rw [hcf] at hc
      cases hc with
      | some e =>
        refine ⟨u', ?_, e⟩
        cases m
        · exact mem_cmp.2 ⟨s', hs', t', ht', hcf⟩
        · exact mem_cmp.2 ⟨t', ht', s', hs', hcf⟩
  · intro u' hu'
    have : ∃ s' ∈ xs', ∃ t' ∈ ys', cf m s' t' = some u' := by
      cases m
      · exact mem_cmp.1 hu'
      · obtain ⟨t', ht', s', hs', h⟩ := mem_cmp.1 hu'
        exact ⟨s', hs', t', ht', h⟩
    obtain ⟨s', hs', t', ht', hst⟩ := this
    obtain ⟨s, hs, es⟩ := hx.2 s' hs'
    obtain ⟨t, ht, et⟩ := hy.2 t' ht'
    have hc := compose_corr es et
    rw [hst] at hc
    cases hcs : s.compose t with
    | none => rw [hcs] at hc; cases hc
    | some u =>
      rw [hcs] at hc
      cases hc with
      | some e => exact ⟨u, mem_cmp.2 ⟨s, hs, t, ht, hcs⟩, e⟩

theorem mcmp_corr {m : Bool} {xs ys xs' ys' : List Span} (hx : DCorr m xs xs')
    (hy : DCorr m ys ys') : DCorr m (mcmp xs ys) (mcmp xs' ys') := by
  constructor
  · intro u hu
    obtain ⟨s, hs, t, ht, hst⟩ := mem_mcmp.1 hu
    obtain ⟨s', hs', es⟩ := hx.1 s hs
    obtain ⟨t', ht', et⟩ := hy.1 t ht
    have hc := meet_corr es et
    rw [hst] at hc
    cases hcf : s'.meet t' with
    | none => rw [hcf] at hc; cases hc
    | some u' =>
      rw [hcf] at hc
      cases hc with
      | some e => exact ⟨u', mem_mcmp.2 ⟨s', hs', t', ht', hcf⟩, e⟩
  · intro u' hu'
    obtain ⟨s', hs', t', ht', hst⟩ := mem_mcmp.1 hu'
    obtain ⟨s, hs, es⟩ := hx.2 s' hs'
    obtain ⟨t, ht, et⟩ := hy.2 t' ht'
    have hc := meet_corr es et
    rw [hst] at hc
    cases hcs : s.meet t with
    | none => rw [hcs] at hc; cases hc
    | some u =>
      rw [hcs] at hc
      cases hc with
      | some e => exact ⟨u, mem_mcmp.2 ⟨s, hs, t, ht, hcs⟩, e⟩

theorem cmp_assoc (xs ys zs : List Span) : DCorr false (cmp (cmp xs ys) zs) (cmp xs (cmp ys zs)) := by
  constructor
  · intro u hu
    obtain ⟨v, hv, z, hz, hvz⟩ := mem_cmp.1 hu
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_cmp.1 hv
    have hd : u.den = (x.den).comp ((y.den).comp z.den) := by
      rw [compose_some hvz, compose_some hxy, GRel.comp_assoc]
    obtain ⟨w, hw, hwd⟩ := compose_isSome (GRel.comp_nonempty_right (hd ▸ Span.den_nonempty u))
    obtain ⟨u', hu', hud⟩ := compose_isSome (s₁ := x) (s₂ := w) (by rw [hwd, ← hd]; exact Span.den_nonempty u)
    refine ⟨u', mem_cmp.2 ⟨x, hx, w, mem_cmp.2 ⟨y, hy, z, hz, hw⟩, hu'⟩, GEq.of_eq ?_⟩
    rw [hud, hwd, hd]; rfl
  · intro u hu
    obtain ⟨x, hx, w, hw, hxw⟩ := mem_cmp.1 hu
    obtain ⟨y, hy, z, hz, hyz⟩ := mem_cmp.1 hw
    have hd : u.den = ((x.den).comp y.den).comp z.den := by
      rw [compose_some hxw, compose_some hyz, GRel.comp_assoc]
    obtain ⟨v, hv, hvd⟩ := compose_isSome (GRel.comp_nonempty_left (hd ▸ Span.den_nonempty u))
    obtain ⟨u', hu', hud⟩ := compose_isSome (s₁ := v) (s₂ := z) (by rw [hvd, ← hd]; exact Span.den_nonempty u)
    refine ⟨u', mem_cmp.2 ⟨v, mem_cmp.2 ⟨x, hx, y, hy, hv⟩, z, hz, hu'⟩, GEq.of_eq ?_⟩
    rw [hd, hud, hvd]; rfl

theorem cmp_id_left (xs : List Span) : DCorr false (cmp [Span.idSpan] xs) xs := by
  constructor
  · intro u hu
    obtain ⟨i, hi, t, ht, h⟩ := mem_cmp.1 hu
    rw [List.mem_singleton] at hi; subst hi
    refine ⟨t, ht, GEq.of_eq ?_⟩
    rw [compose_some h, Span.den_idSpan, GRel.id_comp]; rfl
  · intro t ht
    obtain ⟨u, hu, hd⟩ := compose_isSome (s₁ := Span.idSpan) (s₂ := t)
      (by rw [Span.den_idSpan, GRel.id_comp]; exact Span.den_nonempty t)
    refine ⟨u, mem_cmp.2 ⟨_, List.mem_singleton_self _, t, ht, hu⟩, GEq.of_eq ?_⟩
    rw [hd, Span.den_idSpan, GRel.id_comp]; rfl

theorem cmp_id_right (xs : List Span) : DCorr false (cmp xs [Span.idSpan]) xs := by
  constructor
  · intro u hu
    obtain ⟨t, ht, i, hi, h⟩ := mem_cmp.1 hu
    rw [List.mem_singleton] at hi; subst hi
    refine ⟨t, ht, GEq.of_eq ?_⟩
    rw [compose_some h, Span.den_idSpan, GRel.comp_id]; rfl
  · intro t ht
    obtain ⟨u, hu, hd⟩ := compose_isSome (s₁ := t) (s₂ := Span.idSpan)
      (by rw [Span.den_idSpan, GRel.comp_id]; exact Span.den_nonempty t)
    refine ⟨u, mem_cmp.2 ⟨t, ht, _, List.mem_singleton_self _, hu⟩, GEq.of_eq ?_⟩
    rw [hd, Span.den_idSpan, GRel.comp_id]; rfl

/-! ## Spans derived by chains -/

theorem derivs_seq (a b : Rel) : derivs (.seq a b) = cmp (derivs a) (derivs b) := rfl

theorem derivs_and (a b : Rel) : derivs (.and a b) = mcmp (derivs a) (derivs b) := rfl

theorem derivs_toRel_cons (f : Rel) (r : List Rel) :
    DCorr false (derivs (toRel (f :: r))) (cmp (derivs f) (derivs (toRel r))) := by
  cases r with
  | nil => exact (cmp_id_right _).symm
  | cons g r => exact DCorr.refl _

theorem cmp_congr {xs ys xs' ys' : List Span} (hx : DCorr false xs xs') (hy : DCorr false ys ys') :
    DCorr false (cmp xs ys) (cmp xs' ys') := cmp_corr hx hy

theorem derivs_toRel_append : ∀ (p q : List Rel),
    DCorr false (derivs (toRel (p ++ q))) (cmp (derivs (toRel p)) (derivs (toRel q)))
  | [], q => (cmp_id_left _).symm
  | f :: p, q => by
    rw [List.cons_append]
    refine (derivs_toRel_cons f (p ++ q)).trans'' ?_
    refine (cmp_congr (DCorr.refl _) (derivs_toRel_append p q)).trans'' ?_
    refine (cmp_assoc _ _ _).symm.trans'' ?_
    exact cmp_congr (derivs_toRel_cons f p).symm (DCorr.refl _)

theorem id_inv : GRel.id.inv = GRel.id := by
  ext ⟨a, b, X⟩
  simp only [GRel.inv, GRel.id, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂⟩

/-! ## Corresponding factors and products -/

/-- Corresponding factors: spans with corresponding meanings, or two factors
that are not spans, contain calls on both sides or on neither, and derive
corresponding spans. -/
inductive FE (m : Bool) : Rel → Rel → Prop
  | span {a b : Span} : OC m a b → FE m (.span a) (.span b)
  | other {x y : Rel} : x.isSpan = false → y.isSpan = false → (x.calls = [] ↔ y.calls = []) →
      DCorr m (derivs x) (derivs y) → FE m x y

/-- A list read in the order of a direction: reversed under a mirror. -/
def rv : Bool → List Rel → List Rel
  | true, p => p.reverse
  | false, p => p

/-- Corresponding products: corresponding factors, in reverse order under a
mirror. -/
def PD (m : Bool) (p p' : List Rel) : Prop := List.Forall₂ (FE m) p (rv m p')

/-- Corresponding lists of products. -/
def PCorr (m : Bool) (L L' : List (List Rel)) : Prop :=
  (∀ p ∈ L, ∃ p' ∈ L', PD m p p') ∧ (∀ p' ∈ L', ∃ p ∈ L, PD m p p')

theorem FE.derivs {m : Bool} {x y : Rel} (h : FE m x y) : DCorr m (R000.derivs x) (R000.derivs y) := by
  cases h with
  | span e =>
    exact ⟨fun s hs => ⟨_, List.mem_singleton_self _, by simp_all [R000.derivs]⟩,
      fun s hs => ⟨_, List.mem_singleton_self _, by simp_all [R000.derivs]⟩⟩
  | other _ _ _ hd => exact hd

theorem FE.calls {m : Bool} {x y : Rel} (h : FE m x y) : x.calls = [] ↔ y.calls = [] := by
  cases h with
  | span _ => simp [Rel.calls]
  | other _ _ hc _ => exact hc

theorem FE.isSpan {m : Bool} {x y : Rel} (h : FE m x y) : x.isSpan = y.isSpan := by
  cases h with
  | span _ => rfl
  | other h₁ h₂ _ _ => rw [h₁, h₂]

theorem FE.refl (x : Rel) : FE false x x := by
  cases x with
  | span a => exact .span (OC.refl a)
  | _ => exact .other rfl rfl Iff.rfl (DCorr.refl _)

theorem FE.symm {m : Bool} {x y : Rel} (h : FE m x y) : FE m y x := by
  cases h with
  | span e => exact .span e.symm
  | other h₁ h₂ hc hd => exact .other h₂ h₁ hc.symm hd.symm

theorem FE.trans {m₁ m₂ : Bool} {x y z : Rel} (h₁ : FE m₁ x y) (h₂ : FE m₂ y z) : FE (m₁ ^^ m₂) x z := by
  cases h₁ with
  | span e =>
    cases h₂ with
    | span e' => exact .span (e.trans e')
    | other h => simp [Rel.isSpan] at h
  | other hx hy hc hd =>
    cases h₂ with
    | span _ => simp [Rel.isSpan] at hy
    | other _ hz hc' hd' => exact .other hx hz (hc.trans hc') (hd.trans hd')

theorem rv_rv (m : Bool) (p : List Rel) : rv m (rv m p) = p := by
  cases m <;> simp [rv]

theorem PD.calls {m : Bool} {p p' : List Rel} (h : PD m p p') :
    (toRel p).calls = [] ↔ (toRel p').calls = [] := by
  rw [calls_toRel, calls_toRel]
  have aux : ∀ {p q : List Rel}, List.Forall₂ (FE m) p q →
      ((∀ x ∈ p, x.calls = []) ↔ (∀ y ∈ q, y.calls = [])) := by
    intro p q h
    induction h with
    | nil => simp
    | cons hxy _ ih => simp only [List.mem_cons, forall_eq_or_imp, hxy.calls, ih]
  rw [aux h]
  cases m <;> simp [rv]

theorem PD.refl (p : List Rel) : PD false p p := by
  unfold PD rv
  induction p with
  | nil => exact .nil
  | cons x p ih => exact .cons (FE.refl x) ih

theorem forall₂_rv_symm {m : Bool} {p p' : List Rel} (h : List.Forall₂ (FE m) p (rv m p')) :
    List.Forall₂ (FE m) p' (rv m p) := by
  cases m
  · exact List.Forall₂.flip (h.imp fun _ _ e => e.symm)
  · simp only [rv] at h ⊢
    rw [← List.forall₂_reverse_iff, List.reverse_reverse] at h
    exact List.Forall₂.flip (h.imp fun _ _ e => e.symm)

theorem PD.symm {m : Bool} {p p' : List Rel} (h : PD m p p') : PD m p' p := forall₂_rv_symm h

theorem forall₂_trans {m₁ m₂ : Bool} : ∀ {p q r : List Rel}, List.Forall₂ (FE m₁) p q →
    List.Forall₂ (FE m₂) q r → List.Forall₂ (FE (m₁ ^^ m₂)) p r
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons e h, .cons e' h' => .cons (e.trans e') (forall₂_trans h h')

theorem PD.trans {m₁ m₂ : Bool} {p q r : List Rel} (h₁ : PD m₁ p q) (h₂ : PD m₂ q r) :
    PD (m₁ ^^ m₂) p r := by
  unfold PD at *
  have h₂' : List.Forall₂ (FE m₂) (rv m₁ q) (rv m₁ (rv m₂ r)) := by
    cases m₁
    · exact h₂
    · simp only [rv]; exact List.forall₂_reverse_iff.2 h₂
  have : rv m₁ (rv m₂ r) = rv (m₁ ^^ m₂) r := by
    cases m₁ <;> cases m₂ <;> simp [rv]
  rw [this] at h₂'
  exact forall₂_trans h₁ h₂'

theorem PCorr.refl (L : List (List Rel)) : PCorr false L L :=
  ⟨fun p hp => ⟨p, hp, PD.refl p⟩, fun p hp => ⟨p, hp, PD.refl p⟩⟩

theorem PCorr.symm {m : Bool} {L L' : List (List Rel)} (h : PCorr m L L') : PCorr m L' L :=
  ⟨fun p hp => let ⟨q, hq, e⟩ := h.2 p hp; ⟨q, hq, e.symm⟩,
   fun p hp => let ⟨q, hq, e⟩ := h.1 p hp; ⟨q, hq, e.symm⟩⟩

theorem PCorr.trans {m₁ m₂ : Bool} {L₁ L₂ L₃ : List (List Rel)} (h₁ : PCorr m₁ L₁ L₂)
    (h₂ : PCorr m₂ L₂ L₃) : PCorr (m₁ ^^ m₂) L₁ L₃ := by
  constructor
  · intro p hp
    obtain ⟨q, hq, e⟩ := h₁.1 p hp
    obtain ⟨r, hr, e'⟩ := h₂.1 q hq
    exact ⟨r, hr, e.trans e'⟩
  · intro r hr
    obtain ⟨q, hq, e'⟩ := h₂.2 r hr
    obtain ⟨p, hp, e⟩ := h₁.2 q hq
    exact ⟨p, hp, e.trans e'⟩

theorem PCorr.append {m : Bool} {L₁ L₁' L₂ L₂' : List (List Rel)} (h₁ : PCorr m L₁ L₁')
    (h₂ : PCorr m L₂ L₂') : PCorr m (L₁ ++ L₂) (L₁' ++ L₂') := by
  constructor
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨p', hp', hd⟩ := h₁.1 p hp; exact ⟨p', List.mem_append_left _ hp', hd⟩
    · obtain ⟨p', hp', hd⟩ := h₂.1 p hp; exact ⟨p', List.mem_append_right _ hp', hd⟩
  · intro p' hp'
    rcases List.mem_append.1 hp' with hp' | hp'
    · obtain ⟨p, hp, hd⟩ := h₁.2 p' hp'; exact ⟨p, List.mem_append_left _ hp, hd⟩
    · obtain ⟨p, hp, hd⟩ := h₂.2 p' hp'; exact ⟨p, List.mem_append_right _ hp, hd⟩

theorem PCorr.of_subset {L L' : List (List Rel)} (h₁ : ∀ p ∈ L, p ∈ L') (h₂ : ∀ p ∈ L', p ∈ L) :
    PCorr false L L' :=
  ⟨fun p hp => ⟨p, h₁ p hp, PD.refl p⟩, fun p hp => ⟨p, h₂ p hp, PD.refl p⟩⟩

/-- Corresponding products derive corresponding spans. -/
theorem PD.derivs {m : Bool} {p p' : List Rel} (h : PD m p p') :
    DCorr m (R000.derivs (toRel p)) (R000.derivs (toRel p')) := by
  cases m
  · simp only [PD, rv] at h
    induction h with
    | nil => exact DCorr.refl _
    | @cons x x' p p' hx _ ih =>
      refine (derivs_toRel_cons x p).trans'' ?_
      refine DCorr.trans' (cmp_corr hx.derivs ih) ?_
      exact (derivs_toRel_cons x' p').symm
  · simp only [PD, rv] at h
    suffices ∀ q, List.Forall₂ (FE true) p q →
        DCorr true (R000.derivs (toRel p)) (R000.derivs (toRel q.reverse)) by
      simpa using this _ h
    intro q hq
    clear h
    induction hq with
    | nil =>
      have : OC true Span.idSpan Span.idSpan := by
        unfold OC; rw [fm_true, Span.den_idSpan, id_inv]; exact GEq.refl _
      exact ⟨fun s hs => ⟨s, hs, by simp_all [toRel, idRel, R000.derivs]⟩,
        fun s hs => ⟨s, hs, by simp_all [toRel, idRel, R000.derivs]⟩⟩
    | @cons x x' p q hx _ ih =>
      refine (derivs_toRel_cons x p).trans'' ?_
      rw [List.reverse_cons]
      exact DCorr.trans' (cmp_corr hx.derivs ih) (derivs_toRel_append q.reverse [x']).symm

/-! ## Joining and conjoining corresponding products -/

theorem fe_concat_left {m : Bool} {A : List Rel} {x : Rel} {r : List Rel}
    (h : List.Forall₂ (FE m) (A ++ [x]) r) :
    ∃ A' x', r = A' ++ [x'] ∧ List.Forall₂ (FE m) A A' ∧ FE m x x' := by
  rw [← List.forall₂_reverse_iff, List.reverse_append] at h
  obtain ⟨x', R, hx, hR, hr⟩ := List.forall₂_cons_left_iff.1 h
  refine ⟨R.reverse, x', List.reverse_eq_cons_iff.1 hr, ?_, hx⟩
  rw [← List.forall₂_reverse_iff, List.reverse_reverse]
  simpa using hR

theorem joinSeq_fe_false {pa pa' pb pb' : List Rel} (ha : List.Forall₂ (FE false) pa pa')
    (hb : List.Forall₂ (FE false) pb pb') :
    Option.Rel (List.Forall₂ (FE false)) (joinSeq pa pb) (joinSeq pa' pb') := by
  rcases List.eq_nil_or_concat pa with rfl | ⟨A, x, rfl⟩
  · cases ha
    rw [joinSeq_nofuse (by simp), joinSeq_nofuse (by simp)]
    exact .some (by simpa using hb)
  · rw [List.concat_eq_append] at ha ⊢
    obtain ⟨A', x', rfl, hA, hx⟩ := fe_concat_left ha
    cases hb with
    | nil =>
      rw [joinSeq_nofuse (by simp), joinSeq_nofuse (by simp)]
      exact .some (by simpa using ha)
    | @cons y y' B B' hy hB =>
      have hD : x.isSpan = false ∨ y.isSpan = false →
          Option.Rel (List.Forall₂ (FE false)) (joinSeq (A ++ [x]) (y :: B))
            (joinSeq (A' ++ [x']) (y' :: B')) := by
        intro h₁
        have h₂ : x'.isSpan = false ∨ y'.isSpan = false := by rwa [← hx.isSpan, ← hy.isSpan]
        rw [joinSeq_nofuse' h₁, joinSeq_nofuse' h₂]
        exact .some (List.rel_append ha (.cons hy hB))
      cases hx with
      | @span a a' hxa =>
        cases hy with
        | @span b b' hyb =>
          simp only [joinSeq, List.getLast?_concat, List.dropLast_concat]
          have hc := compose_corr hxa hyb
          simp only [cf] at hc
          revert hc
          cases a.compose b <;> cases a'.compose b' <;> intro hc <;> cases hc
          · exact .none
          · rename_i c c' hcc
            exact .some (List.rel_append hA (.cons (.span hcc) hB))
        | other hy₁ _ _ _ => exact hD (.inr hy₁)
      | other hx₁ _ _ _ => exact hD (.inl hx₁)

theorem joinSeq_fe_true_aux {pa ra pb rb : List Rel} (ha : List.Forall₂ (FE true) pa ra)
    (hb : List.Forall₂ (FE true) pb rb) :
    Option.Rel (PD true) (joinSeq pa pb) (joinSeq rb.reverse ra.reverse) := by
  rcases List.eq_nil_or_concat pa with rfl | ⟨A, x, rfl⟩
  · cases ha
    rw [joinSeq_nofuse (by simp), joinSeq_nofuse (by simp)]
    exact .some (by simpa [PD, rv] using hb)
  · rw [List.concat_eq_append] at ha
    obtain ⟨A', x', rfl, hA, hx⟩ := fe_concat_left ha
    cases hb with
    | nil =>
      rw [joinSeq_nofuse (by simp), joinSeq_nofuse (by simp)]
      exact .some (by simpa [PD, rv] using List.rel_append hA (.cons hx .nil))
    | @cons y y' B B' hy hB =>
      simp only [List.reverse_cons, List.reverse_append, List.reverse_nil, List.nil_append,
        List.singleton_append, List.concat_eq_append]
      have hD : x.isSpan = false ∨ y.isSpan = false →
          Option.Rel (PD true) (joinSeq (A ++ [x]) (y :: B))
            (joinSeq (B'.reverse ++ [y']) (x' :: A'.reverse)) := by
        intro h₁
        have h₂ : y'.isSpan = false ∨ x'.isSpan = false := by
          rw [← hx.isSpan, ← hy.isSpan]; exact h₁.symm
        rw [joinSeq_nofuse' h₁, joinSeq_nofuse' h₂]
        refine .some ?_
        simp only [PD, rv, List.reverse_append, List.reverse_cons, List.reverse_reverse,
          List.nil_append, List.append_assoc, List.cons_append]
        exact List.rel_append hA (.cons hx (.cons hy hB))
      cases hx with
      | @span a a' hxa =>
        cases hy with
        | @span b b' hyb =>
          simp only [joinSeq, List.getLast?_concat, List.dropLast_concat]
          have hc := compose_corr hxa hyb
          simp only [cf] at hc
          revert hc
          cases a.compose b <;> cases b'.compose a' <;> intro hc <;> cases hc
          · exact .none
          · rename_i c c' hcc
            refine .some ?_
            simp only [PD, rv, List.reverse_append, List.reverse_cons, List.reverse_reverse,
              List.nil_append, List.append_assoc, List.cons_append]
            exact List.rel_append hA (.cons (.span hcc) hB)
        | other hy₁ _ _ _ => exact hD (.inr hy₁)
      | other hx₁ _ _ _ => exact hD (.inl hx₁)

/-- Joining in the order of a direction: reversed under a mirror. -/
def joinD : Bool → List Rel → List Rel → Option (List Rel)
  | true, p, q => joinSeq q p
  | false, p, q => joinSeq p q

theorem joinSeq_PD {m : Bool} {pa pa' pb pb' : List Rel} (ha : PD m pa pa') (hb : PD m pb pb') :
    Option.Rel (PD m) (joinSeq pa pb) (joinD m pa' pb') := by
  cases m
  · exact joinSeq_fe_false ha hb
  · have := joinSeq_fe_true_aux ha hb
    simp only [rv, List.reverse_reverse] at this
    exact this

theorem PD.isSingleSpan {m : Bool} {p p' : List Rel} (h : PD m p p') :
    isSingleSpan p = isSingleSpan p' := by
  have hl := h.length_eq
  have : (rv m p').length = p'.length := by cases m <;> simp [rv]
  rw [this] at hl
  match p, p', h, hl with
  | [], [], _, _ => rfl
  | [x], [x'], h, _ =>
    have : FE m x x' := by
      cases m <;> simpa [PD, rv] using h
    cases this with
    | span _ => rfl
    | other h₁ h₂ _ _ => simp [R000.isSingleSpan, h₁, h₂]
  | _ :: _ :: _, _ :: _ :: _, _, _ => rfl

theorem PD.single {m : Bool} {x x' : Rel} (h : PD m [x] [x']) : FE m x x' := by
  cases m <;> simpa [PD, rv] using h

theorem PD.of_single {m : Bool} {x x' : Rel} (h : FE m x x') : PD m [x] [x'] := by
  cases m <;> simpa [PD, rv] using h

theorem mkAnd_PD {m : Bool} {p p' q q' : List Rel} (hp : PD m p p') (hq : PD m q q') :
    Option.Rel (PD m) (mkAnd p q) (mkAnd p' q') := by
  by_cases hs : isSingleSpan p = true ∧ isSingleSpan q = true
  · obtain ⟨a, rfl⟩ := eq_single_of_isSingleSpan hs.1
    obtain ⟨b, rfl⟩ := eq_single_of_isSingleSpan hs.2
    obtain ⟨a', rfl⟩ := eq_single_of_isSingleSpan (hp.isSingleSpan ▸ hs.1)
    obtain ⟨b', rfl⟩ := eq_single_of_isSingleSpan (hq.isSingleSpan ▸ hs.2)
    have ha : OC m a a' := by
      cases hp.single with
      | span h => exact h
      | other h => simp [Rel.isSpan] at h
    have hb : OC m b b' := by
      cases hq.single with
      | span h => exact h
      | other h => simp [Rel.isSpan] at h
    simp only [mkAnd]
    have hc := meet_corr ha hb
    revert hc
    cases a.meet b <;> cases a'.meet b' <;> intro hc <;> cases hc
    · exact .none
    · rename_i c c' hcc
      exact .some (PD.of_single (.span hcc))
  · have h : isSingleSpan p = false ∨ isSingleSpan q = false := by
      cases h₁ : isSingleSpan p <;> cases h₂ : isSingleSpan q <;> simp_all
    have h' : isSingleSpan p' = false ∨ isSingleSpan q' = false := by
      rwa [← hp.isSingleSpan, ← hq.isSingleSpan]
    rw [mkAnd_other h, mkAnd_other h']
    refine .some (PD.of_single (.other rfl rfl ?_ ?_))
    · simp only [Rel.calls, List.append_eq_nil_iff, hp.calls, hq.calls]
    · rw [derivs_and, derivs_and]; exact mcmp_corr hp.derivs hq.derivs

/-! ## Lists of products -/

/-- The products of a sequence, from the products of its two sides. -/
def seqP (L₁ L₂ : List (List Rel)) : List (List Rel) := L₁.flatMap fun p => L₂.filterMap (joinSeq p)

def andP (L₁ L₂ : List (List Rel)) : List (List Rel) := L₁.flatMap fun p => L₂.filterMap (mkAnd p)

def seqPD : Bool → List (List Rel) → List (List Rel) → List (List Rel)
  | true, L₁, L₂ => seqP L₂ L₁
  | false, L₁, L₂ => seqP L₁ L₂

theorem mem_seqP {L₁ L₂ : List (List Rel)} {r : List Rel} :
    r ∈ seqP L₁ L₂ ↔ ∃ p ∈ L₁, ∃ q ∈ L₂, joinSeq p q = some r := by
  simp [seqP]

theorem mem_andP {L₁ L₂ : List (List Rel)} {r : List Rel} :
    r ∈ andP L₁ L₂ ↔ ∃ p ∈ L₁, ∃ q ∈ L₂, mkAnd p q = some r := by
  simp [andP]

theorem seqP_corr {m : Bool} {L₁ L₁' L₂ L₂' : List (List Rel)} (h₁ : PCorr m L₁ L₁')
    (h₂ : PCorr m L₂ L₂') : PCorr m (seqP L₁ L₂) (seqPD m L₁' L₂') := by
  have memD : ∀ r', r' ∈ seqPD m L₁' L₂' ↔ ∃ p' ∈ L₁', ∃ q' ∈ L₂', joinD m p' q' = some r' := by
    intro r'
    cases m
    · exact mem_seqP
    · simp only [seqPD, joinD, mem_seqP]
      exact ⟨fun ⟨q, hq, p, hp, h⟩ => ⟨p, hp, q, hq, h⟩, fun ⟨p, hp, q, hq, h⟩ => ⟨q, hq, p, hp, h⟩⟩
  constructor
  · intro r hr
    obtain ⟨p, hp, q, hq, hj⟩ := mem_seqP.1 hr
    obtain ⟨p', hp', ep⟩ := h₁.1 p hp
    obtain ⟨q', hq', eq⟩ := h₂.1 q hq
    have hrel := joinSeq_PD ep eq
    rw [hj] at hrel
    cases h' : joinD m p' q' with
    | none => rw [h'] at hrel; cases hrel
    | some r' =>
      rw [h'] at hrel
      cases hrel with
      | some hd => exact ⟨r', (memD r').2 ⟨p', hp', q', hq', h'⟩, hd⟩
  · intro r' hr'
    obtain ⟨p', hp', q', hq', hj⟩ := (memD r').1 hr'
    obtain ⟨p, hp, ep⟩ := h₁.2 p' hp'
    obtain ⟨q, hq, eq⟩ := h₂.2 q' hq'
    have hrel := joinSeq_PD ep eq
    rw [hj] at hrel
    cases h' : joinSeq p q with
    | none => rw [h'] at hrel; cases hrel
    | some r =>
      rw [h'] at hrel
      cases hrel with
      | some hd => exact ⟨r, mem_seqP.2 ⟨p, hp, q, hq, h'⟩, hd⟩

theorem andP_corr {m : Bool} {L₁ L₁' L₂ L₂' : List (List Rel)} (h₁ : PCorr m L₁ L₁')
    (h₂ : PCorr m L₂ L₂') : PCorr m (andP L₁ L₂) (andP L₁' L₂') := by
  constructor
  · intro r hr
    obtain ⟨p, hp, q, hq, hj⟩ := mem_andP.1 hr
    obtain ⟨p', hp', ep⟩ := h₁.1 p hp
    obtain ⟨q', hq', eq⟩ := h₂.1 q hq
    have hrel := mkAnd_PD ep eq
    rw [hj] at hrel
    cases h' : mkAnd p' q' with
    | none => rw [h'] at hrel; cases hrel
    | some r' =>
      rw [h'] at hrel
      cases hrel with
      | some hd => exact ⟨r', mem_andP.2 ⟨p', hp', q', hq', h'⟩, hd⟩
  · intro r' hr'
    obtain ⟨p', hp', q', hq', hj⟩ := mem_andP.1 hr'
    obtain ⟨p, hp, ep⟩ := h₁.2 p' hp'
    obtain ⟨q, hq, eq⟩ := h₂.2 q' hq'
    have hrel := mkAnd_PD ep eq
    rw [hj] at hrel
    cases h' : mkAnd p q with
    | none => rw [h'] at hrel; cases hrel
    | some r =>
      rw [h'] at hrel
      cases hrel with
      | some hd => exact ⟨r, mem_andP.2 ⟨p, hp, q, hq, h'⟩, hd⟩

theorem norm_seq (neg : Bool) (a b : Rel) :
    norm neg (.seq a b) = if neg then seqP (norm true b) (norm true a) else seqP (norm false a) (norm false b) := by
  cases neg <;> rfl

theorem norm_and (neg : Bool) (a b : Rel) : norm neg (.and a b) = andP (norm neg a) (norm neg b) := by
  cases neg <;> rfl

/-! ## Products are non-empty, and joining is associative -/

theorem joinSeq_ne_nil {p q r : List Rel} (h : joinSeq p q = some r) (hp : p ≠ []) : r ≠ [] := by
  unfold joinSeq at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨c, -, rfl⟩ := h
    simp
  · cases h; simp [hp]

theorem mkAnd_ne_nil {p q r : List Rel} (h : mkAnd p q = some r) : r ≠ [] := by
  unfold mkAnd at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨c, -, rfl⟩ := h
    simp
  · cases h; simp

theorem norm_ne_nil : ∀ (neg : Bool) (e : Rel), ∀ p ∈ norm neg e, p ≠ []
  | _, .zero, p, hp => by simp [norm] at hp
  | _, .span _, p, hp => by simp only [norm, List.mem_singleton] at hp; subst hp; simp
  | neg, .or a b, p, hp => by
    simp only [norm, List.mem_append] at hp
    rcases hp with hp | hp
    · exact norm_ne_nil neg a p hp
    · exact norm_ne_nil neg b p hp
  | false, .seq a b, p, hp => by
    obtain ⟨p₁, h₁, p₂, -, hj⟩ := mem_seqP.1 hp
    exact joinSeq_ne_nil hj (norm_ne_nil false a p₁ h₁)
  | true, .seq a b, p, hp => by
    obtain ⟨p₁, h₁, p₂, -, hj⟩ := mem_seqP.1 hp
    exact joinSeq_ne_nil hj (norm_ne_nil true b p₁ h₁)
  | neg, .and a b, p, hp => by
    obtain ⟨p₁, -, p₂, -, hj⟩ := mem_andP.1 (by rw [← norm_and]; exact hp)
    exact mkAnd_ne_nil hj
  | neg, .conv a, p, hp => norm_ne_nil (!neg) a p hp
  | neg, .call _, p, hp => by simp only [norm, List.mem_singleton] at hp; subst hp; simp

/-- The fusion of the two factors where two chains meet. -/
def fuse : Rel → Rel → Option (List Rel)
  | .span a, .span b => (a.compose b).map fun c => [.span c]
  | x, y => some [x, y]

theorem fuse_other {x y : Rel} (h : x.isSpan = false ∨ y.isSpan = false) : fuse x y = some [x, y] := by
  cases x <;> cases y <;> simp_all [fuse, Rel.isSpan]

theorem fuse_left {x : Rel} (h : x.isSpan = false) (y : Rel) : fuse x y = some [x, y] :=
  fuse_other (.inl h)

theorem fuse_right {y : Rel} (h : y.isSpan = false) (x : Rel) : fuse x y = some [x, y] :=
  fuse_other (.inr h)

theorem fuse_span (a b : Span) : fuse (.span a) (.span b) = (a.compose b).map fun c => [.span c] := rfl

theorem joinSeq_fuse (P : List Rel) (x y : Rel) (B : List Rel) :
    joinSeq (P ++ [x]) (y :: B) = (fuse x y).map fun F => P ++ F ++ B := by
  by_cases h : x.isSpan = false ∨ y.isSpan = false
  · rw [joinSeq_nofuse' h, fuse_other h]; simp
  · simp only [not_or, Bool.not_eq_false] at h
    match x, y, h with
    | .span a, .span b, _ =>
      simp only [joinSeq, List.getLast?_concat, List.dropLast_concat, fuse, Option.map_map]
      congr 1; funext c; simp

theorem compose_assoc_rel (a b c : Span) :
    Option.Rel (OC false) ((a.compose b).bind fun ab => ab.compose c)
      ((b.compose c).bind fun bc => a.compose bc) := by
  apply optRel_of
  have e₁ : Span.denO ((a.compose b).bind fun ab => ab.compose c) = ((a.den).comp b.den).comp c.den := by
    cases h : a.compose b with
    | none => rw [compose_none h]; simp [Span.denO, GRel.comp]
    | some ab => simp only [Option.bind_some, compose_den, compose_some h]
  have e₂ : Span.denO ((b.compose c).bind fun bc => a.compose bc) = (a.den).comp ((b.den).comp c.den) := by
    cases h : b.compose c with
    | none => rw [compose_none h]; simp [Span.denO, GRel.comp]
    | some bc => simp only [Option.bind_some, compose_den, compose_some h]
  rw [e₁, e₂, GRel.comp_assoc]; exact GEq.refl _

theorem forall₂_fe_refl (p : List Rel) : List.Forall₂ (FE false) p p := PD.refl p

theorem spanOr (x : Rel) : (∃ a, x = .span a) ∨ x.isSpan = false := by
  cases x <;> simp [Rel.isSpan]

theorem optRel_refl (o : Option (List Rel)) : Option.Rel (List.Forall₂ (FE false)) o o := by
  cases o
  · exact .none
  · exact .some (forall₂_fe_refl _)

theorem joinSeq_single (P : List Rel) (x y : Rel) :
    joinSeq (P ++ [x]) [y] = (fuse x y).map fun F => P ++ F := by
  rw [joinSeq_fuse]; simp

theorem optRel_of_eq {o o' : Option (List Rel)} (h : o = o') :
    Option.Rel (List.Forall₂ (FE false)) o o' := h ▸ optRel_refl o

theorem optMap_rel {P R : List Rel} {o₁ o₂ : Option Span} (h : Option.Rel (OC false) o₁ o₂) :
    Option.Rel (List.Forall₂ (FE false)) (o₁.map fun u => P ++ .span u :: R)
      (o₂.map fun u => P ++ .span u :: R) := by
  cases h with
  | none => exact .none
  | some e => exact .some (List.rel_append (forall₂_fe_refl P) (.cons (.span e) (forall₂_fe_refl R)))

theorem joinSeq_fuse_pair (P : List Rel) (x y z : Rel) (B : List Rel) :
    joinSeq (P ++ [x, y]) (z :: B) = (fuse y z).map fun F => P ++ x :: F ++ B := by
  rw [show P ++ [x, y] = (P ++ [x]) ++ [y] by simp, joinSeq_fuse]; simp

theorem joinSeq_assoc {p q r : List Rel} (hp : p ≠ []) (hq : q ≠ []) (hr : r ≠ []) :
    Option.Rel (List.Forall₂ (FE false)) ((joinSeq p q).bind fun pq => joinSeq pq r)
      ((joinSeq q r).bind fun qr => joinSeq p qr) := by
  obtain ⟨P, x, rfl⟩ : ∃ P x, p = P ++ [x] := by
    rcases List.eq_nil_or_concat p with h | ⟨P, x, h⟩
    · exact absurd h hp
    · exact ⟨P, x, by simpa using h⟩
  obtain ⟨z, R, rfl⟩ := List.exists_cons_of_ne_nil hr
  obtain ⟨y, Q, rfl⟩ := List.exists_cons_of_ne_nil hq
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q₀, w, rfl⟩
  · -- `q` is a single factor `y`
    rw [joinSeq_single, show [y] = [] ++ [y] from rfl, joinSeq_fuse]
    rcases spanOr y with ⟨b, rfl⟩ | hy
    · rcases spanOr x with ⟨a, rfl⟩ | hx <;> rcases spanOr z with ⟨c, rfl⟩ | hz
      · have hL : ((fuse (.span a) (.span b)).map (fun F => P ++ F)).bind (fun pq => joinSeq pq (.span c :: R)) =
            ((a.compose b).bind fun ab => ab.compose c).map fun u => P ++ .span u :: R := by
          simp only [fuse]
          cases a.compose b
          · rfl
          · simp only [Option.map_some, Option.bind_some]
            rw [joinSeq_fuse]; simp [fuse, Function.comp_def]
        have hR : ((fuse (.span b) (.span c)).map (fun F => [] ++ F ++ R)).bind
              (fun qr => joinSeq (P ++ [.span a]) qr) =
            ((b.compose c).bind fun bc => a.compose bc).map fun u => P ++ .span u :: R := by
          simp only [fuse]
          cases b.compose c
          · rfl
          · simp only [Option.map_some, Option.bind_some, List.nil_append, List.singleton_append]
            rw [joinSeq_fuse]; simp [fuse, Function.comp_def]
        rw [hL, hR]
        exact optMap_rel (compose_assoc_rel a b c)
      · apply optRel_of_eq
        rw [fuse_span, fuse_right hz]
        cases h : a.compose b <;> simp [h, joinSeq_fuse, fuse_right hz, fuse_span]
      · apply optRel_of_eq
        rw [fuse_left hx, fuse_span]
        cases h : b.compose c <;> simp [h, joinSeq_fuse, joinSeq_fuse_pair, fuse_left hx, fuse_span]
      · apply optRel_of_eq
        simp [fuse_left hx, fuse_right hz, joinSeq_fuse, joinSeq_fuse_pair]
    · apply optRel_of_eq
      simp [fuse_left hy, fuse_right hy, joinSeq_fuse, joinSeq_fuse_pair]
  · -- `q` has at least two factors: the two fusions are independent
    apply optRel_of_eq
    rw [List.concat_eq_append, joinSeq_fuse, show y :: (Q₀ ++ [w]) = (y :: Q₀) ++ [w] from rfl,
      joinSeq_fuse]
    cases hf : fuse x y with
    | none =>
      simp only [Option.map_none, Option.bind_none]
      cases fuse w z
      · rfl
      · simp only [Option.map_some, Option.bind_some, List.cons_append, List.append_assoc]
        rw [joinSeq_fuse, hf]; rfl
    | some F =>
      simp only [Option.map_some, Option.bind_some]
      rw [show P ++ F ++ (Q₀ ++ [w]) = (P ++ F ++ Q₀) ++ [w] by simp, joinSeq_fuse]
      cases fuse w z
      · rfl
      · simp only [Option.map_some, Option.bind_some, List.cons_append, List.append_assoc]
        rw [joinSeq_fuse, hf]; simp

theorem seqP_assoc {A B C : List (List Rel)} (hA : ∀ p ∈ A, p ≠ []) (hB : ∀ p ∈ B, p ≠ [])
    (hC : ∀ p ∈ C, p ≠ []) : PCorr false (seqP (seqP A B) C) (seqP A (seqP B C)) := by
  constructor
  · intro r hr
    obtain ⟨pq, hpq, s, hs, h₂⟩ := mem_seqP.1 hr
    obtain ⟨p, hp, q, hq, h₁⟩ := mem_seqP.1 hpq
    have key := joinSeq_assoc (hA p hp) (hB q hq) (hC s hs)
    rw [h₁, Option.bind_some, h₂] at key
    cases hqs : joinSeq q s with
    | none => rw [hqs] at key; cases key
    | some qs =>
      rw [hqs, Option.bind_some] at key
      cases hr' : joinSeq p qs with
      | none => rw [hr'] at key; cases key
      | some r' =>
        rw [hr'] at key
        cases key with
        | some e => exact ⟨r', mem_seqP.2 ⟨p, hp, qs, mem_seqP.2 ⟨q, hq, s, hs, hqs⟩, hr'⟩, e⟩
  · intro r' hr'
    obtain ⟨p, hp, qs, hqs, h₂⟩ := mem_seqP.1 hr'
    obtain ⟨q, hq, s, hs, h₁⟩ := mem_seqP.1 hqs
    have key := joinSeq_assoc (hA p hp) (hB q hq) (hC s hs)
    rw [h₁, Option.bind_some, h₂] at key
    cases hpq : joinSeq p q with
    | none => rw [hpq] at key; cases key
    | some pq =>
      rw [hpq, Option.bind_some] at key
      cases hr : joinSeq pq s with
      | none => rw [hr] at key; cases key
      | some r =>
        rw [hr] at key
        cases key with
        | some e => exact ⟨r, mem_seqP.2 ⟨pq, mem_seqP.2 ⟨p, hp, q, hq, hpq⟩, s, hs, hr⟩, e⟩

/-! ## Unfolding -/

section Unfold

variable (P : Program)

theorem unfoldN_zero' (k : Nat) : unfoldN P k .zero = .zero := by
  induction k with
  | zero => rfl
  | succ k ih => rw [unfoldN, Function.iterate_succ_apply', ← unfoldN, ih]; rfl

theorem unfoldN_span (k : Nat) (s : Span) : unfoldN P k (.span s) = .span s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [unfoldN, Function.iterate_succ_apply', ← unfoldN, ih]; rfl

theorem unfoldN_seq (k : Nat) (a b : Rel) :
    unfoldN P k (.seq a b) = .seq (unfoldN P k a) (unfoldN P k b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldN, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]; rfl

theorem unfoldN_and (k : Nat) (a b : Rel) :
    unfoldN P k (.and a b) = .and (unfoldN P k a) (unfoldN P k b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldN, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]; rfl

theorem unfoldN_or' (k : Nat) (a b : Rel) :
    unfoldN P k (.or a b) = .or (unfoldN P k a) (unfoldN P k b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldN, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]; rfl

theorem unfoldN_conv' (k : Nat) (a : Rel) : unfoldN P k (.conv a) = .conv (unfoldN P k a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldN, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]; rfl

theorem unfold_dual : ∀ e : Rel, unfold P.dual e.dual = (unfold P e).dual
  | .zero => rfl
  | .span _ => rfl
  | .or a b => by simp only [Rel.dual, unfold, unfold_dual a, unfold_dual b]
  | .and a b => by simp only [Rel.dual, unfold, unfold_dual a, unfold_dual b]
  | .seq a b => by simp only [Rel.dual, unfold, unfold_dual a, unfold_dual b]
  | .conv a => by simp only [Rel.dual, unfold, unfold_dual a]
  | .call n => by simp only [Rel.dual, unfold, Program.dual_body]

theorem unfoldN_dual (k : Nat) (e : Rel) : unfoldN P.dual k e.dual = (unfoldN P k e).dual := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldN, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, unfold_dual]

end Unfold

/-! ## Corresponding expressions -/

/-- Two expressions, of the programs `P` and `Q`, have corresponding
products at every unfolding depth and orientation. -/
def Mk (m : Bool) (P Q : Program) (X Y : Rel) : Prop :=
  ∀ neg k, PCorr m (norm neg (unfoldN P k X)) (norm neg (unfoldN Q k Y))

variable {P Q R : Program}

theorem Mk.refl (X : Rel) : Mk false Q Q X X := fun _ _ => PCorr.refl _

theorem Mk.symm {m : Bool} {X Y : Rel} (h : Mk m P Q X Y) : Mk m Q P Y X := fun neg k => (h neg k).symm

theorem Mk.trans {m₁ m₂ : Bool} {X Y Z : Rel} (h₁ : Mk m₁ P Q X Y) (h₂ : Mk m₂ Q R Y Z) :
    Mk (m₁ ^^ m₂) P R X Z := fun neg k => (h₁ neg k).trans (h₂ neg k)

theorem OC.swap {m : Bool} {a b : Span} (h : OC m a b) : OC m a.swap b.swap := by
  unfold OC at *
  rw [swap_den, swap_den]
  cases m
  · exact h.inv
  · simpa using h.inv

theorem pcorr_single {m : Bool} {x y : Rel} (h : FE m x y) : PCorr m [[x]] [[y]] :=
  ⟨fun p hp => ⟨[y], List.mem_singleton_self _, by rw [List.mem_singleton.1 hp]; exact PD.of_single h⟩,
   fun p hp => ⟨[x], List.mem_singleton_self _, by rw [List.mem_singleton.1 hp]; exact PD.of_single h⟩⟩

theorem Mk.span {m : Bool} {a b : Span} (h : OC m a b) : Mk m P Q (.span a) (.span b) := by
  intro neg k
  rw [unfoldN_span, unfoldN_span]
  cases neg
  · exact pcorr_single (.span h)
  · exact pcorr_single (.span h.swap)

theorem Mk.zero {m : Bool} : Mk m P Q .zero .zero := by
  intro neg k
  rw [unfoldN_zero', unfoldN_zero']
  exact ⟨fun p hp => by simp [norm] at hp, fun p hp => by simp [norm] at hp⟩

theorem Mk.or {m : Bool} {a b a' b' : Rel} (ha : Mk m P Q a a') (hb : Mk m P Q b b') :
    Mk m P Q (.or a b) (.or a' b') := by
  intro neg k
  rw [unfoldN_or', unfoldN_or']
  exact (ha neg k).append (hb neg k)

theorem Mk.and {m : Bool} {a b a' b' : Rel} (ha : Mk m P Q a a') (hb : Mk m P Q b b') :
    Mk m P Q (.and a b) (.and a' b') := by
  intro neg k
  rw [unfoldN_and, unfoldN_and, norm_and, norm_and]
  exact andP_corr (ha neg k) (hb neg k)

theorem Mk.conv {m : Bool} {a a' : Rel} (ha : Mk m P Q a a') : Mk m P Q (.conv a) (.conv a') := by
  intro neg k
  rw [unfoldN_conv', unfoldN_conv']
  exact ha (!neg) k

/-- A sequence in the order of a direction: reversed under a mirror. -/
def sqD : Bool → Rel → Rel → Rel
  | true, a', b' => .seq b' a'
  | false, a', b' => .seq a' b'

theorem Mk.seq {m : Bool} {a b a' b' : Rel} (ha : Mk m P Q a a') (hb : Mk m P Q b b') :
    Mk m P Q (.seq a b) (sqD m a' b') := by
  intro neg k
  cases m
  · simp only [sqD]
    rw [unfoldN_seq, unfoldN_seq, norm_seq, norm_seq]
    cases neg
    · exact seqP_corr (ha false k) (hb false k)
    · exact seqP_corr (hb true k) (ha true k)
  · simp only [sqD]
    rw [unfoldN_seq, unfoldN_seq, norm_seq, norm_seq]
    cases neg
    · exact seqP_corr (ha false k) (hb false k)
    · exact seqP_corr (hb true k) (ha true k)

theorem Mk.assoc (a b c : Rel) : Mk false Q Q (.seq (.seq a b) c) (.seq a (.seq b c)) := by
  intro neg k
  simp only [unfoldN_seq, norm_seq]
  cases neg
  · exact seqP_assoc (norm_ne_nil _ _) (norm_ne_nil _ _) (norm_ne_nil _ _)
  · exact (seqP_assoc (norm_ne_nil _ _) (norm_ne_nil _ _) (norm_ne_nil _ _)).symm

/-- The products of an expression correspond to those of its mirror. -/
theorem pcorr_dual : ∀ (neg : Bool) (e : Rel), PCorr true (norm neg e) (norm neg e.dual)
  | _, .zero => ⟨fun p hp => by simp [norm] at hp, fun p hp => by simp [Rel.dual, norm] at hp⟩
  | neg, .span s => by
    have : OC true s s.swap := swap_geq s
    cases neg
    · exact pcorr_single (.span this)
    · exact pcorr_single (.span this.swap)
  | neg, .or a b => (pcorr_dual neg a).append (pcorr_dual neg b)
  | neg, .and a b => by
    simp only [Rel.dual, norm_and]
    exact andP_corr (pcorr_dual neg a) (pcorr_dual neg b)
  | false, .seq a b => by
    simp only [Rel.dual, norm_seq]
    exact seqP_corr (pcorr_dual false a) (pcorr_dual false b)
  | true, .seq a b => by
    simp only [Rel.dual, norm_seq]
    exact seqP_corr (pcorr_dual true b) (pcorr_dual true a)
  | neg, .conv a => pcorr_dual (!neg) a
  | neg, .call n => by
    simp only [Rel.dual, norm]
    refine pcorr_single (.other ?_ ?_ Iff.rfl ⟨fun s hs => ?_, fun s hs => ?_⟩) <;>
      cases neg <;> simp_all [Rel.isSpan, R000.derivs]

theorem Mk.dual (X : Rel) : Mk true P P.dual X X.dual := by
  intro neg k
  rw [unfoldN_dual]
  exact pcorr_dual neg _

/-! ## The canonical form of `|` keeps the products -/

section Canon

variable (Q : Program) (neg : Bool) (k : Nat)

theorem mem_prods_mkOr : ∀ (Ls : List Rel) (p : List Rel),
    p ∈ norm neg (unfoldN Q k (mkOr Ls)) ↔ ∃ e ∈ Ls, p ∈ norm neg (unfoldN Q k e)
  | [], p => by simp [mkOr, unfoldN_zero', norm]
  | [e], p => by simp [mkOr]
  | e :: e' :: es, p => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, unfoldN_or']
    simp only [norm, List.mem_append, mem_prods_mkOr (e' :: es) p, List.mem_cons]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨e, .inl rfl, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, rfl | hx, h⟩
      · exact .inl h
      · exact .inr ⟨x, hx, h⟩

theorem mem_prods_branches : ∀ (X : Rel) (p : List Rel),
    p ∈ norm neg (unfoldN Q k X) ↔ ∃ e ∈ orBranches X, p ∈ norm neg (unfoldN Q k e)
  | .or a b, p => by
    rw [unfoldN_or']
    simp only [norm, List.mem_append, orBranches, mem_prods_branches a p, mem_prods_branches b p]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | .zero, p | .span _, p | .and _ _, p | .seq _ _, p | .conv _, p | .call _, p => by
    simp [orBranches]

theorem mem_prods_sorted (L : List Rel) (p : List Rel) :
    (∃ e ∈ sortedBranches L, p ∈ norm neg (unfoldN Q k e)) ↔ ∃ e ∈ L, p ∈ norm neg (unfoldN Q k e) := by
  constructor
  · rintro ⟨e, he, h⟩; exact ⟨e, (mem_sortedBranches.1 he).1, h⟩
  · rintro ⟨e, he, h⟩
    refine ⟨e, mem_sortedBranches.2 ⟨he, ?_⟩, h⟩
    rintro rfl
    simp [unfoldN_zero', norm] at h

end Canon

theorem mk_canon : ∀ Y : Rel, Mk false Q Q (canon Y) Y
  | .zero => Mk.refl _
  | .span _ => Mk.refl _
  | .call _ => Mk.refl _
  | .and a b => Mk.and (mk_canon a) (mk_canon b)
  | .seq a b => Mk.seq (mk_canon a) (mk_canon b)
  | .conv a => Mk.conv (mk_canon a)
  | .or a b => by
    have h₁ : Mk false Q Q (canon (.or a b)) (.or (canon a) (canon b)) := by
      intro neg k
      apply PCorr.of_subset <;> intro p hp
      · rw [canon, mem_prods_mkOr, mem_prods_sorted] at hp
        obtain ⟨e, he, h⟩ := hp
        rw [mem_prods_branches]
        exact ⟨e, by simpa [orBranches] using he, h⟩
      · rw [canon, mem_prods_mkOr, mem_prods_sorted]
        rw [mem_prods_branches] at hp
        obtain ⟨e, he, h⟩ := hp
        exact ⟨e, by simpa [orBranches] using he, h⟩
    simpa using h₁.trans (Mk.or (mk_canon a) (mk_canon b))

/-! ## Mirrored goals -/

theorem Mk.bound {a b : Span} (h : boundEq (some a) (some b) = true) : Mk false Q Q (.span a) (.span b) := by
  have := boundEq_equiv h
  cases this with
  | some e => exact Mk.span (Span.Equiv.geq e).symm

theorem Mk.goal {g h : Goal} (he : h.e = canon g.e.dual) (hl : boundEq (g.rb.map Span.swap) h.lb = true)
    (hr : boundEq (g.lb.map Span.swap) h.rb = true) : Mk true P P.dual g.rel h.rel := by
  obtain ⟨glb, ge, grb⟩ := g
  obtain ⟨hlb, he', hrb⟩ := h
  simp only at he hl hr
  subst he
  have hd := Mk.dual (P := P) (Goal.rel ⟨glb, ge, grb⟩)
  have hc : Mk false P.dual P.dual ge.dual (canon ge.dual) := (mk_canon ge.dual).symm
  suffices Mk false P.dual P.dual (Goal.rel ⟨glb, ge, grb⟩).dual (Goal.rel ⟨hlb, canon ge.dual, hrb⟩) by
    simpa using hd.trans this
  cases glb with
  | none =>
    cases hrb with
    | some _ => simp [boundEq] at hr
    | none =>
      cases grb with
      | none =>
        cases hlb with
        | some _ => simp [boundEq] at hl
        | none => simpa [Goal.rel, Rel.dual] using hc
      | some r =>
        cases hlb with
        | none => simp [boundEq] at hl
        | some r' =>
          simp only [Goal.rel, Rel.dual, Option.map_some] at hl ⊢
          exact Mk.seq (Mk.bound hl) hc
  | some l =>
    cases hrb with
    | none => simp [boundEq] at hr
    | some l' =>
      simp only [Option.map_some] at hr
      cases grb with
      | none =>
        cases hlb with
        | some _ => simp [boundEq] at hl
        | none =>
          simp only [Goal.rel, Rel.dual]
          exact Mk.seq hc (Mk.bound hr)
      | some r =>
        cases hlb with
        | none => simp [boundEq] at hl
        | some r' =>
          simp only [Goal.rel, Rel.dual, Option.map_some] at hl ⊢
          simpa [sqD] using (Mk.assoc _ _ _).trans (Mk.seq (Mk.bound hl) (Mk.seq hc (Mk.bound hr)))

/-! ## The unfolding strategy of mirrored goals -/

theorem pcorr_final {m : Bool} {L L' : List (List Rel)} (h : PCorr m L L') :
    (L.all fun p => (toRel p).calls.isEmpty) = (L'.all fun p => (toRel p).calls.isEmpty) := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.isEmpty_iff]
  constructor
  · intro hL p' hp'
    obtain ⟨p, hp, e⟩ := h.2 p' hp'
    exact e.calls.1 (hL p hp)
  · intro hL p hp
    obtain ⟨p', hp', e⟩ := h.1 p hp
    exact e.calls.2 (hL p' hp')

theorem pcorr_spans {m : Bool} {L L' : List (List Rel)} (h : PCorr m L L') :
    DCorr m (L.flatMap fun p => derivs (toRel p)) (L'.flatMap fun p => derivs (toRel p)) := by
  constructor
  · intro s hs
    obtain ⟨p, hp, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨p', hp', e⟩ := h.1 p hp
    obtain ⟨s', hs', e'⟩ := e.derivs.1 s hs
    exact ⟨s', List.mem_flatMap.2 ⟨p', hp', hs'⟩, e'⟩
  · intro s' hs'
    obtain ⟨p', hp', hs'⟩ := List.mem_flatMap.1 hs'
    obtain ⟨p, hp, e⟩ := h.2 p' hp'
    obtain ⟨s, hs, e'⟩ := e.derivs.2 s' hs'
    exact ⟨s, List.mem_flatMap.2 ⟨p, hp, hs⟩, e'⟩

theorem Mk.roundFinal {X Y : Rel} (h : Mk true P Q X Y) (k : Nat) :
    R000.roundFinal Q Y k = R000.roundFinal P X k :=
  (pcorr_final (h false k)).symm

theorem Mk.roundSpans {X Y : Rel} (h : Mk true P Q X Y) (k : Nat) :
    DCorr true (R000.roundSpans P X k) (R000.roundSpans Q Y k) :=
  pcorr_spans (h false k)

/-- Corresponding spans give the same classes of live candidates, up to
swapping. -/
theorem classEq_live {T : Theory} (hK : Obligation.SimplifyRespectsEquiv T) {xs ys : List Span}
    (h : DCorr true xs ys) :
    ClassEq (ys.flatMap (live T)) ((xs.flatMap (live T)).map Span.swap) := by
  have one : ∀ {a b : Span}, OC true a b → ClassEq (live T b) ((live T a).map Span.swap) := by
    intro a b e
    have := liveO_mirror (T := T) hK (o' := some b) (o := some a) e
    simpa [liveO] using this
  constructor
  · intro x hx
    obtain ⟨b, hb, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨a, ha, e⟩ := h.2 b hb
    obtain ⟨y, hy, exy⟩ := (one e).1 x hx
    obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.1 hy
    exact ⟨_, List.mem_map.2 ⟨y₀, List.mem_flatMap.2 ⟨a, ha, hy₀⟩, rfl⟩, exy⟩
  · intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.1 hy
    obtain ⟨a, ha, hy₀⟩ := List.mem_flatMap.1 hy₀
    obtain ⟨b, hb, e⟩ := h.1 a ha
    obtain ⟨x, hx, exy⟩ := (one e).2 _ (List.mem_map.2 ⟨y₀, hy₀, rfl⟩)
    exact ⟨x, List.mem_flatMap.2 ⟨b, hb, hx⟩, exy⟩

theorem _root_.RwLog.Program.dual_theory (P : Program) : P.dual.theory = P.theory := rfl

/-- A goal and the corresponding goal of the mirrored run finish rung zero
in the same round and give the same classes of answers, swapped. -/
theorem unfold_mirror (hK : Obligation.SimplifyRespectsEquiv P.theory) {g h : Goal}
    (he : h.e = canon g.e.dual) (hl : boundEq (g.rb.map Span.swap) h.lb = true)
    (hr : boundEq (g.lb.map Span.swap) h.rb = true) (d : Nat) :
    unfoldFinal P.dual d h = unfoldFinal P d g ∧
      ClassEq (unfoldAnswers P.dual d h) ((unfoldAnswers P d g).map Span.swap) := by
  have hm := Mk.goal (P := P) he hl hr
  have hf : unfoldFinal P.dual d h = unfoldFinal P d g := hm.roundFinal d
  refine ⟨hf, ?_⟩
  unfold unfoldAnswers
  rw [hf]
  split
  · rw [Program.dual_theory]
    exact classEq_live hK (hm.roundSpans d)
  · exact ClassEq.refl _

end Symmetry

end R001

end RwLog
