/-
# Tier 0 proofs, part 2: goals and their boundaries

A goal `⟨lb, e, rb⟩` stands for `lb ; e ; rb` (`GDen`). Every boundary the
engine creates is an interface `p {c} -> p` whose store only mentions the
variables of `p` (`Bnd`): a sub-identity in which the store is a function of
the term (`Fn`). This is what makes `&` with boundaries distribute
(`meet_bound`), equivalent boundaries denote the same relation
(`same_gden`), and interfaces absorb into the span they come from.
-/
import RwLog.Rungs.R001.Proofs.Tier0.Rel

namespace RwLog

namespace R001

namespace Tier0

open Lifting (bden)

variable {T : Theory}

/-! ## Boundaries -/

/-- The relation `lb ; R ; rb` of a goal whose expression denotes `R`
(`Lifting.W` of the goal's boundaries). -/
def GDen (g : Goal) (R : GRel) : GRel := (bden g.lb).comp (R.comp (bden g.rb))

theorem gden_W (g : Goal) (R : GRel) : GDen g R = Lifting.W g.lb R g.rb := rfl

/-- An interface: both sides are one pattern and the store only mentions its
variables. -/
def Bnd (b : Span) : Prop := b.l = b.r ∧ ∀ a ∈ b.c, ∀ v ∈ a.vars, v ∈ b.l.vars

/-- A boundary the engine may create: an interface. -/
def GoodB (b : Span) : Prop := Bnd b

def GoodBO : Option Span → Prop
  | none => True
  | some b => GoodB b

def GoodG (g : Goal) : Prop := GoodBO g.lb ∧ GoodBO g.rb

/-- A sub-identity whose store is a function of the term. -/
def Fn (B : GRel) : Prop :=
  ∀ u u' S, (u, u', S) ∈ B → u' = u ∧ ∀ S', (u, u, S') ∈ B → S' = S

theorem store_at_congr' {c : Store} {σ τ : Nat → GTerm}
    (h : ∀ a ∈ c, ∀ v ∈ a.vars, σ v = τ v) : c.at σ = c.at τ := by
  unfold Store.at
  congr 1
  exact List.map_congr_left fun a ha => Term.bind_congr (h a ha)

theorem Bnd.fn {b : Span} (h : Bnd b) : Fn b.den := by
  rintro u u' S ⟨σ, he⟩
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  refine ⟨by rw [h.1], ?_⟩
  rintro S' ⟨τ, he'⟩
  simp only [Prod.mk.injEq] at he'
  obtain ⟨h1, -, rfl⟩ := he'
  have hag := bind_agree h1
  exact store_at_congr' fun a ha v hv => (hag v (h.2 a ha v hv)).symm

theorem fn_id : Fn GRel.id := by
  rintro u u' S ⟨h1, h2⟩
  simp only at h1 h2
  refine ⟨h1, ?_⟩
  rintro S' ⟨-, h3⟩
  simp only at h3
  rw [h2, h3]

theorem bnd_fn : ∀ {o : Option Span}, GoodBO o → Fn (bden o)
  | none, _ => fn_id
  | some _, h => Bnd.fn h

theorem Fn.inv {B : GRel} (h : Fn B) : Fn B.inv := by
  intro u u' S hx
  obtain ⟨e, h'⟩ := h u' u S hx
  subst e
  exact ⟨rfl, h'⟩

theorem Bnd.swap {b : Span} (h : Bnd b) : Bnd b.swap :=
  ⟨h.1.symm, fun a ha v hv => by
    simp only [Span.swap]; rw [← h.1]; exact h.2 a ha v hv⟩

theorem bnd_rightIface (s : Span) : Bnd s.rightIface :=
  ⟨rfl, fun _ ha v hv => (mem_storeOn.1 ha).2 v hv⟩

theorem bnd_leftIface (s : Span) : Bnd s.leftIface :=
  ⟨rfl, fun _ ha v hv => (mem_storeOn.1 ha).2 v hv⟩

theorem goodBO_map_swap : ∀ {o : Option Span}, GoodBO o → GoodBO (o.map Span.swap)
  | none, _ => trivial
  | some _, h => Bnd.swap h

/-- The boundary of an interface denotes the interface. -/
theorem goodBO_bound {s : Span} (h : GoodB s) : GoodBO (bound s) := by
  cases hb : bound s with
  | none => trivial
  | some s' => rw [bound_some hb]; exact h

/-! ## Distributing a conjunction over boundaries -/

theorem meet_bound {B C : GRel} (hB : Fn B) (hC : Fn C) (A A' : GRel) :
    (B.comp (A.comp C)).meet (B.comp (A'.comp C)) = B.comp ((A.meet A').comp C) := by
  ext ⟨u, v, S⟩
  constructor
  · rintro ⟨S₁, S₂, h₁, h₂, hS⟩
    obtain ⟨m, Sb, Sac, hb, hac, e₁⟩ := h₁
    obtain ⟨m', Sa, Sc, ha, hc, e₂⟩ := hac
    obtain ⟨n, Sb', Sac', hb', hac', e₃⟩ := h₂
    obtain ⟨n', Sa', Sc', ha', hc', e₄⟩ := hac'
    simp only at hS hb hc hb' hc' ha ha' e₁ e₂ e₃ e₄
    obtain ⟨hm, hbu⟩ := hB _ _ _ hb
    subst m
    obtain ⟨hn, -⟩ := hB _ _ _ hb'
    subst n
    obtain ⟨hm', hcu⟩ := hC _ _ _ hc
    subst m'
    obtain ⟨hn', -⟩ := hC _ _ _ hc'
    subst n'
    have f₁ := hbu Sb' hb'
    have f₂ := hcu Sc' hc'
    subst Sb' Sc' S₁ S₂ Sac Sac'
    refine ⟨u, Sb, Sa ∪ Sa' ∪ Sc, hb, ⟨v, Sa ∪ Sa', Sc, ⟨Sa, Sa', ha, ha', rfl⟩, hc, rfl⟩, ?_⟩
    rw [hS]; ext x; simp only [Finset.mem_union]; tauto
  · rintro ⟨m, Sb, Smc, hb, hmc, hS⟩
    obtain ⟨m', Sm, Sc, hm, hc, e₁⟩ := hmc
    obtain ⟨Sa, Sa', ha, ha', e₂⟩ := hm
    simp only at hS hb hc ha ha' e₁ e₂
    obtain ⟨hmu, -⟩ := hB _ _ _ hb
    subst m
    refine ⟨Sb ∪ (Sa ∪ Sc), Sb ∪ (Sa' ∪ Sc), ⟨u, Sb, Sa ∪ Sc, hb, ⟨m', Sa, Sc, ha, hc, rfl⟩, rfl⟩,
      ⟨u, Sb, Sa' ∪ Sc, hb, ⟨m', Sa', Sc, ha', hc, rfl⟩, rfl⟩, ?_⟩
    rw [hS, e₁, e₂]; ext x; simp only [Finset.mem_union]; tauto

/-- An answer conjoined with what runs inside its interfaces is the answer
conjoined with what runs there unrestricted. -/
theorem meet_ifaces (x : Span) (B : GRel) :
    (x.den).meet (x.leftIface.den.comp (B.comp x.rightIface.den)) = (x.den).meet B := by
  ext ⟨u, v, S⟩
  constructor
  · rintro ⟨Sx, Sy, hx, hy, hS⟩
    obtain ⟨m, S₁, S₂₃, hl, hbr, e₁⟩ := hy
    obtain ⟨m', S₂, S₃, hb, hr, e₂⟩ := hbr
    obtain ⟨σ, hσ⟩ := hx
    obtain ⟨τ, hτ⟩ := hl
    obtain ⟨ρ, hρ⟩ := hr
    simp only [Prod.mk.injEq, Span.leftIface, Span.rightIface] at hσ hτ hρ hS e₁ e₂ hb
    obtain ⟨rfl, rfl, rfl⟩ := hσ
    obtain ⟨hl1, hl2, hl3⟩ := hτ
    obtain ⟨hr1, hr2, hr3⟩ := hρ
    subst m m' S₁ S₃ S₂₃ Sy
    have e₁ := storeOn_at_congr x x.l hl1
    have e₃ := storeOn_at_congr x x.r hr2
    have h₁ := storeOn_sub x x.l σ
    have h₃ := storeOn_sub x x.r σ
    rw [← hl1, ← hr2] at hb
    refine ⟨x.c.at σ, S₂, ⟨σ, rfl⟩, hb, ?_⟩
    rw [hS, ← e₁, ← e₃]
    ext g; simp only [Finset.mem_union]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inl (h₁ h)
      · exact Or.inr h
      · exact Or.inl (h₃ h)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
  · rintro ⟨Sx, S₂, hx, hb, hS⟩
    obtain ⟨σ, hσ⟩ := hx
    simp only [Prod.mk.injEq] at hσ hS hb
    obtain ⟨rfl, rfl, rfl⟩ := hσ
    have h₁ := storeOn_sub x x.l σ
    have h₃ := storeOn_sub x x.r σ
    refine ⟨x.c.at σ, (x.storeOn x.l).at σ ∪ (S₂ ∪ (x.storeOn x.r).at σ), ⟨σ, rfl⟩,
      ⟨x.l.bind σ, (x.storeOn x.l).at σ, S₂ ∪ (x.storeOn x.r).at σ, ⟨σ, rfl⟩,
        ⟨x.r.bind σ, S₂, (x.storeOn x.r).at σ, hb, ⟨σ, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    rw [hS]
    ext g; simp only [Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inl (h₁ h)
      · exact Or.inr h
      · exact Or.inl (h₃ h)

/-- Conjoining an answer with what runs inside its own interfaces, transferred
to the boundaries of the goal the answer came from. -/
theorem andPush_backed {T : Theory} {B C A A' : GRel} {xd : GRel} (hB : Fn B) (hC : Fn C)
    (hx : xd.Backed T (B.comp (A.comp C))) :
    (xd.meet A').Backed T ((B.comp (A.comp C)).meet (B.comp (A'.comp C))) := by
  rintro ⟨u, v, S⟩ ⟨Sx, S₂, hxd, ha', hS⟩
  simp only at hS hxd ha'
  obtain ⟨⟨u', v', Sb⟩, hb, e1, e2, hns⟩ := hx _ hxd
  simp only at e1 e2 hns
  subst e1 e2
  obtain ⟨m, S₁, S₂₃, hb₁, hac, e₃⟩ := hb
  obtain ⟨m', Sa, Sc, ha, hc, e₄⟩ := hac
  simp only at hb₁ ha hc e₃ e₄
  obtain ⟨hm, -⟩ := hB _ _ _ hb₁
  subst m
  obtain ⟨hm', -⟩ := hC _ _ _ hc
  subst m'
  subst S₂₃
  refine ⟨(u', v', (S₁ ∪ (Sa ∪ Sc)) ∪ (S₁ ∪ (S₂ ∪ Sc))),
    ⟨S₁ ∪ (Sa ∪ Sc), S₁ ∪ (S₂ ∪ Sc), ⟨u', S₁, Sa ∪ Sc, hb₁, ⟨v', Sa, Sc, ha, hc, rfl⟩, rfl⟩,
      ⟨u', S₁, S₂ ∪ Sc, hb₁, ⟨v', S₂, Sc, ha', hc, rfl⟩, rfl⟩, rfl⟩, rfl, rfl, ?_⟩
  have e : (S₁ ∪ (Sa ∪ Sc)) ∪ (S₁ ∪ (S₂ ∪ Sc)) = (S₁ ∪ (Sa ∪ Sc)) ∪ S₂ := by
    ext x; simp only [Finset.mem_union]; tauto
  simp only
  rw [e, hS, ← e₃]
  exact Lifting.ns_union hns (Lifting.ns_refl _)

theorem andPush_dom {T : Theory} {B C A A' : GRel} {xd : GRel} (hB : Fn B) (hC : Fn C)
    (hx : Lifting.LCov T xd (B.comp (A.comp C))) :
    Lifting.LCov T (xd.meet A') ((B.comp (A.comp C)).meet (B.comp (A'.comp C))) := by
  rintro u v S ⟨S₁, S₂, h₁, h₂, hS⟩ hn
  simp only at hS h₁ h₂
  subst hS
  obtain ⟨m, Sb, S', hb, hac, e₁⟩ := h₂
  obtain ⟨m', Sa', Sc', ha', hc', e₂⟩ := hac
  simp only at hb ha' hc' e₁ e₂
  obtain ⟨hm, -⟩ := hB _ _ _ hb
  subst m
  obtain ⟨hm', -⟩ := hC _ _ _ hc'
  subst m'
  obtain ⟨Sx, hxd, hns⟩ := hx _ _ _ h₁ (fun h => hn (h.mono Finset.subset_union_left))
  refine ⟨Sx ∪ Sa', ⟨Sx, Sa', hxd, ha', rfl⟩,
    Lifting.ns_union hns (GStore.NoStronger.of_subset ?_)⟩
  rw [e₁, e₂]
  intro x hx; simp only [Finset.mem_union]; tauto

/-! ## Goals as table keys -/

theorem boundEq_den {a b : Option Span} (ha : GoodBO a) (hb : GoodBO b)
    (h : boundEq a b = true) : bden a = bden b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some _ => simp [boundEq] at h
  | some a => cases b with
    | none => simp [boundEq] at h
    | some b =>
      simp only [boundEq, Bool.and_eq_true] at h
      have hab := covers?_sound h.1
      have hba := covers?_sound h.2
      have fa := Bnd.fn ha
      have fb := Bnd.fn hb
      simp only [bden]
      ext ⟨u, u', S⟩
      constructor
      · intro hx
        obtain ⟨y, hy, e1, e2, e3⟩ := hba _ hx
        obtain ⟨z, hz, f1, f2, f3⟩ := hab _ hy
        obtain ⟨rfl, hfa⟩ := fa _ _ _ hx
        obtain ⟨y1, y2, y3⟩ := y
        obtain ⟨z1, z2, z3⟩ := z
        simp only at e1 e2 e3 f1 f2 f3
        subst e1 e2 f1 f2
        have := hfa z3 hz
        subst z3
        have : y3 = S := le_antisymm e3 f3
        subst this
        exact hy
      · intro hx
        obtain ⟨y, hy, e1, e2, e3⟩ := hab _ hx
        obtain ⟨z, hz, f1, f2, f3⟩ := hba _ hy
        obtain ⟨rfl, hfb⟩ := fb _ _ _ hx
        obtain ⟨y1, y2, y3⟩ := y
        obtain ⟨z1, z2, z3⟩ := z
        simp only at e1 e2 e3 f1 f2 f3
        subst e1 e2 f1 f2
        have := hfb z3 hz
        subst z3
        have : y3 = S := le_antisymm e3 f3
        subst this
        exact hy

theorem same_e {h g : Goal} (hs : h.same g = true) : h.e = g.e := by
  simp only [Goal.same, Bool.and_eq_true, decide_eq_true_eq] at hs
  exact hs.1.1

theorem same_gden {h g : Goal} (hs : h.same g = true) (hh : GoodG h) (hg : GoodG g)
    (R : GRel) : GDen h R = GDen g R := by
  simp only [Goal.same, Bool.and_eq_true, decide_eq_true_eq] at hs
  simp only [GDen, boundEq_den hh.1 hg.1 hs.1.2, boundEq_den hh.2 hg.2 hs.2]

theorem boundEq_refl : ∀ o : Option Span, boundEq o o = true
  | none => rfl
  | some a => by simp [boundEq, covers?_complete (Span.Covers.refl a)]

theorem same_refl (g : Goal) : g.same g = true := by
  simp [Goal.same, boundEq_refl]

theorem gden_root (e : Rel) (R : GRel) : GDen ⟨none, e, none⟩ R = R := by
  simp [GDen, bden, GRel.comp_id, GRel.id_comp]

theorem goodG_convGoal {g : Goal} (h : GoodG g) (a : Rel) : GoodG (convGoal g a) :=
  ⟨goodBO_map_swap h.2, goodBO_map_swap h.1⟩

theorem gden_conv (g : Goal) (a : Rel) (R : GRel) :
    GDen ⟨g.lb, .conv a, g.rb⟩ R.inv = (GDen (convGoal g a) R).inv := by
  simp only [GDen, convGoal, Lifting.bden_swap, RwLog.GRel.inv_comp, RwLog.GRel.inv_inv,
    RwLog.GRel.comp_assoc]

/-- A span oriented by a flag. -/
def oS (f : Bool) (s : Span) : Span := if f then s.swap else s

/-- A relation oriented by a flag. -/
def oR (f : Bool) (R : GRel) : GRel := if f then R.inv else R

theorem orient_eq (f : Bool) (xs : List Span) : orient f xs = xs.map (oS f) := by
  have h₁ : oS false = id := rfl
  have h₂ : oS true = Span.swap := rfl
  cases f
  · rw [h₁, List.map_id]; rfl
  · rw [h₂]; rfl

theorem oS_den (f : Bool) (s : Span) : (oS f s).den = oR f s.den := by
  cases f <;> simp [oS, oR, swap_den]

theorem oS_not (f : Bool) (s : Span) : oS (!f) s = (oS f s).swap := by
  cases f <;> simp [oS]

theorem oR_not (f : Bool) (R : GRel) : oR (!f) R = (oR f R).inv := by
  cases f <;> simp [oR, RwLog.GRel.inv_inv]

theorem orient_not (f : Bool) (xs : List Span) : orient (!f) xs = (orient f xs).map Span.swap := by
  rw [orient_eq, orient_eq, List.map_map]
  congr 1; funext s; exact oS_not f s

theorem ref_oS {a : Span} {X : GRel} (f : Bool) (h : Ref T a X) : Ref T (oS f a) (oR f X) := by
  cases f
  · exact h
  · exact h.swap

theorem dc_orient {A : List Span} {X : GRel} (f : Bool) (h : DC T A X) : DC T (orient f A) (oR f X) := by
  cases f
  · exact h
  · exact h.swap

end Tier0

end R001

end RwLog
