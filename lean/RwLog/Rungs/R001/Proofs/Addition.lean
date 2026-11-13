/-
# Rung R001: addition in its fixed modes

Forwards, `@(cons n m) ; add` pushes the pair through `add`: the goal
`add` under a left boundary at `(cons j t)` reads its body, whose recursive
branch peels one `s` and pushes `(cons j' t)` with `j = j' + 1` into `add`
again. Backwards, `add ; @k` pushes `k` in from the right, and the recursive
branch pushes `k'` with `k = k' + 1`. Both are inductions on the fixed number,
over every boundary whose terms have that shape (`forward`, `backward`),
built from the goal-level certificate rules.

What a push can carry is read off semantically: an answer in the cover of a
span goal lies under the goal's relation (`cover_sub`), so the terms of its
interface are images of the boundary's terms under the span (`span_push_right`,
`span_push_left`).
-/
import RwLog.Rungs.R001.Proofs.CertGoals

namespace RwLog

namespace R001

namespace Addition

open Tier0 Exact CertHalts CertOfHalt Combine Lifting

variable {P : Program}

/-! ## What a push carries -/

/-- The terms a boundary lets through. -/
def InDom (o : Option Span) (u : GTerm) : Prop := ∃ S, (u, u, S) ∈ bden o

/-- An answer under a relation relates only pairs of the relation. -/
theorem sub_pairs {T : Theory} {X : GRel} {x : Span} (h : Under T X x) {u u' : GTerm} {S : GStore}
    (hx : (u, u', S) ∈ x.den) : ∃ S', (u, u', S') ∈ X := by
  obtain ⟨w, hdom, w', hsimp, hcov⟩ := h
  obtain ⟨S₁, hS₁, -⟩ := dom_iff.1 (covers_iff_dom.1 hcov) u u' S hx
  obtain ⟨S₂, hS₂, -⟩ := simplify_pairs hsimp (show (u, u') ∈ (w'.den).at Set.univ from
    ⟨S₁, hS₁, Set.subset_univ _⟩)
  obtain ⟨S', hS', -⟩ := dom_iff.1 hdom u u' S₂ hS₂
  exact ⟨S', hS'⟩

/-- A cover answer lets a term through its right interface. -/
theorem inDom_right (x : Span) : ∃ u, InDom (bound x.rightIface) u :=
  ⟨x.r.bind fun _ => .sym "", _, by
    rw [bden_bound rfl]; exact ⟨fun _ => .sym "", rfl⟩⟩

theorem inDom_left (y : Span) : ∃ u, InDom (bound y.leftIface) u :=
  ⟨y.l.bind fun _ => .sym "", _, by
    rw [bden_bound rfl]; exact ⟨fun _ => .sym "", rfl⟩⟩

section Laws

variable (hL : SimpLaws P.theory)
include hL

/-- An answer of the cover a certificate gives its root lies under a
derivation of the root. -/
theorem cover_sub {C : List CertEntry} {D : Nat} {L : Goal} (hg : GoodG L)
    (hC : Cert.Valid P C D L) {x : Span} (hx : x ∈ certCover C L) :
    ∃ s, Derives P L.e s ∧ Under P.theory (GDen L s.den) x := by
  obtain ⟨e, he, hs, hcc⟩ := certCover_spec hC.1
  rw [hcc, orient_eq] at hx
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
  have hge := goodG_of_interfaced (hC.2 e he).1
  obtain ⟨s', hd, hsub⟩ := gderives_sub hL ((hC.2 e he).2.1 f hf) hge
  rw [same_e hs] at hd
  rw [same_gden hs hge (goodG_norm hg)] at hsub
  obtain ⟨hder, hden⟩ := norm_back L hd
  refine ⟨_, hder, ?_⟩
  rw [hden]
  exact sub_oS hL _ hsub

/-- A term the right interface of a cover answer of `lb ; s₀` lets through is
the image under `s₀` of a term `lb` lets through. -/
theorem span_push_right {lb : Option Span} {s₀ : Span} (hlb : GoodBO lb) {C : List CertEntry}
    {D : Nat} (hC : Cert.Valid P C D ⟨lb, .span s₀, none⟩) {x : Span}
    (hx : x ∈ certCover C ⟨lb, .span s₀, none⟩) {u : GTerm} (hu : InDom (bound x.rightIface) u) :
    ∃ σ : Nat → GTerm, InDom lb (s₀.l.bind σ) ∧ u = s₀.r.bind σ := by
  obtain ⟨s, hder, hsub⟩ := cover_sub hL (L := ⟨lb, .span s₀, none⟩) ⟨hlb, trivial⟩ hC hx
  cases hder
  obtain ⟨S, hS⟩ := hu
  rw [bden_bound rfl] at hS
  obtain ⟨σ, hσ⟩ := hS
  simp only [Span.rightIface, Prod.mk.injEq] at hσ
  obtain ⟨S', hS'⟩ := sub_pairs hsub (show (x.l.bind σ, x.r.bind σ, x.c.at σ) ∈ x.den from ⟨σ, rfl⟩)
  obtain ⟨m, S₁, S₂, h1, h2, -⟩ := hS'
  obtain ⟨m', S₃, S₄, h3, h4, -⟩ := h2
  have hm : m = x.l.bind σ := pid_of_goodBO hlb _ _ _ h1
  have hm' : x.r.bind σ = m' := h4.1
  obtain ⟨τ, hτ⟩ := h3
  simp only [Prod.mk.injEq] at hτ
  refine ⟨τ, ⟨S₁, ?_⟩, ?_⟩
  · rw [← hτ.1]; simp only at h1; rw [hm] at h1 ⊢; exact h1
  · rw [hσ.1, hm', hτ.2.1]

/-- The mirror image, for the left interface of a cover answer of `s₀ ; rb`. -/
theorem span_push_left {rb : Option Span} {s₀ : Span} (hrb : GoodBO rb) {C : List CertEntry}
    {D : Nat} (hC : Cert.Valid P C D ⟨none, .span s₀, rb⟩) {y : Span}
    (hy : y ∈ certCover C ⟨none, .span s₀, rb⟩) {u : GTerm} (hu : InDom (bound y.leftIface) u) :
    ∃ σ : Nat → GTerm, InDom rb (s₀.r.bind σ) ∧ u = s₀.l.bind σ := by
  obtain ⟨s, hder, hsub⟩ := cover_sub hL (L := ⟨none, .span s₀, rb⟩) ⟨trivial, hrb⟩ hC hy
  cases hder
  obtain ⟨S, hS⟩ := hu
  rw [bden_bound rfl] at hS
  obtain ⟨σ, hσ⟩ := hS
  simp only [Span.leftIface, Prod.mk.injEq] at hσ
  obtain ⟨S', hS'⟩ := sub_pairs hsub (show (y.l.bind σ, y.r.bind σ, y.c.at σ) ∈ y.den from ⟨σ, rfl⟩)
  obtain ⟨m, S₁, S₂, h1, h2, -⟩ := hS'
  obtain ⟨m', S₃, S₄, h3, h4, -⟩ := h2
  have hm : y.l.bind σ = m := h1.1.symm
  have hm' : y.r.bind σ = m' := pid_of_goodBO hrb _ _ _ h4
  obtain ⟨τ, hτ⟩ := h3
  simp only [Prod.mk.injEq] at hτ
  refine ⟨τ, ⟨S₄, ?_⟩, ?_⟩
  · rw [← hτ.2.1]; simp only at h4; rw [hm'] at h4; exact h4
  · rw [hσ.1, hm, hτ.1]

end Laws

/-! ## The addition program -/

open Examples

/-- The ground numeral. -/
def gnum : Nat → GTerm
  | 0 => .sym "z"
  | n + 1 => .app (.sym "s") (gnum n)

theorem num_bind (σ : Nat → GTerm) (n : Nat) : (num n).bind σ = gnum n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [num, gnum, Term.mk, Term.bind, ih]

/-- The ground pair `(cons a b)`. -/
def gcons (a b : GTerm) : GTerm := .app (.app (.sym "cons") a) b

def r1 : Span := ⟨Term.mk "cons" [.sym "z", .var 0], .var 0, []⟩
def r2 : Span :=
  ⟨Term.mk "cons" [Term.mk "s" [.var 0], .var 1], Term.mk "cons" [.var 0, .var 1], []⟩
def r3 : Span := ⟨.var 0, Term.mk "s" [.var 0], []⟩

theorem add_eq : add = .or (.span r1) (.seq (.span r2) (.seq (.call "add") (.span r3))) := rfl

theorem body_add : addProg.body "add" = add := by
  simp [Program.body, addProg]

theorem laws : SimpLaws addProg.theory := simpLaws_of_wf (fun _ h => nomatch h)

/-- Forwards: `add` under a left boundary whose terms are pairs with a first
component below `n` has a certificate. -/
theorem forward (n : Nat) : ∀ lb : Option Span, GoodBO lb →
    (∀ u, InDom lb u → ∃ j, j < n ∧ ∃ t, u = gcons (gnum j) t) →
    HasCert addProg ⟨lb, .call "add", none⟩ := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lb hlb hdom
    have hg : ∀ e, GoodG ⟨lb, e, none⟩ := fun _ => ⟨hlb, trivial⟩
    refine hasCert_call laws (hg _) ?_
    rw [body_add, add_eq]
    refine hasCert_or laws (hg _) fun l hl => ?_
    simp only [orBranches, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hl
    rcases hl with rfl | rfl
    · exact hasCert_span laws (hg _)
    · obtain ⟨CL, DL, hCL⟩ := hasCert_span (P := addProg) laws (s := r2) (hg _)
      refine seqL_cert laws (hg _) hCL fun x hx => ?_
      have hx' := maxima_sub hx
      have hpush : ∀ u, InDom (bound x.rightIface) u →
          ∃ j, j + 1 < n ∧ ∃ t, u = gcons (gnum j) t := by
        intro u hu
        obtain ⟨σ, hσ, rfl⟩ := span_push_right laws hlb hCL hx' hu
        obtain ⟨j, hj, t, ht⟩ := hdom _ hσ
        cases j with
        | zero => simp [r2, gcons, gnum, Term.mk, Term.bind] at ht
        | succ j =>
          simp only [r2, gcons, gnum, Term.mk, Term.bind, List.foldl, Term.app.injEq,
            true_and] at ht
          exact ⟨j, hj, t, by simp [r2, gcons, Term.mk, Term.bind, ht.1, ht.2]⟩
      obtain ⟨u₀, hu₀⟩ := inDom_right x
      obtain ⟨j₀, hj₀, -⟩ := hpush u₀ hu₀
      have hgx : GoodBO (bound x.rightIface) := goodBO_bound (bnd_rightIface x)
      refine hasCert_seq laws ⟨hgx, trivial⟩ ?_ (hasCert_span laws (goodG_root _))
      refine ih (n - 1) (by omega) _ hgx fun u hu => ?_
      obtain ⟨j, hj, t, ht⟩ := hpush u hu
      exact ⟨j, by omega, t, ht⟩

/-- Backwards: `add` under a right boundary whose terms are numerals below
`n` has a certificate. -/
theorem backward (n : Nat) : ∀ rb : Option Span, GoodBO rb →
    (∀ u, InDom rb u → ∃ j, j < n ∧ u = gnum j) →
    HasCert addProg ⟨none, .call "add", rb⟩ := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro rb hrb hdom
    have hg : ∀ e, GoodG ⟨none, e, rb⟩ := fun _ => ⟨trivial, hrb⟩
    refine hasCert_call laws (hg _) ?_
    rw [body_add, add_eq]
    refine hasCert_or laws (hg _) fun l hl => ?_
    simp only [orBranches, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hl
    rcases hl with rfl | rfl
    · exact hasCert_span laws (hg _)
    · refine hasCert_seq laws (hg _) (hasCert_span laws (goodG_root _)) ?_
      obtain ⟨CL, DL, hCL⟩ := hasCert_span (P := addProg) laws (s := r3) (hg _)
      refine seqR_cert laws (hg _) hCL fun y hy => ?_
      have hy' := maxima_sub hy
      have hpush : ∀ u, InDom (bound y.leftIface) u → ∃ j, j + 1 < n ∧ u = gnum j := by
        intro u hu
        obtain ⟨σ, hσ, rfl⟩ := span_push_left laws hrb hCL hy' hu
        obtain ⟨j, hj, ht⟩ := hdom _ hσ
        cases j with
        | zero => simp [r3, gnum, Term.mk, Term.bind] at ht
        | succ j =>
          simp only [r3, gnum, Term.mk, Term.bind, List.foldl, Term.app.injEq, true_and] at ht
          exact ⟨j, hj, by simp [r3, ht]⟩
      obtain ⟨u₀, hu₀⟩ := inDom_left y
      obtain ⟨j₀, hj₀, -⟩ := hpush u₀ hu₀
      have hgy : GoodBO (bound y.leftIface) := goodBO_bound (bnd_leftIface y)
      refine ih (n - 1) (by omega) _ hgy fun u hu => ?_
      obtain ⟨j, hj, ht⟩ := hpush u hu
      exact ⟨j, by omega, ht⟩

/-- `@(cons n m) ; add` has a certificate. -/
theorem forward_root (n m : Nat) :
    HasCert addProg ⟨none, .seq (.at_ (Term.mk "cons" [num n, num m])) (.call "add"), none⟩ := by
  obtain ⟨CL, DL, hCL⟩ := hasCert_span (P := addProg) laws
    (s := ⟨Term.mk "cons" [num n, num m], Term.mk "cons" [num n, num m], []⟩) (goodG_root _)
  refine seqL_cert laws (goodG_root _) hCL fun x hx => ?_
  refine forward (n + 1) _ (goodBO_bound (bnd_rightIface x)) fun u hu => ?_
  obtain ⟨σ, -, rfl⟩ := span_push_right laws (lb := none) trivial hCL (maxima_sub hx) hu
  exact ⟨n, Nat.lt_succ_self n, gnum m, by simp [gcons, Term.mk, Term.bind, num_bind]⟩

/-- `add ; @k` has a certificate. -/
theorem backward_root (k : Nat) :
    HasCert addProg ⟨none, .seq (.call "add") (.at_ (num k)), none⟩ := by
  obtain ⟨CL, DL, hCL⟩ := hasCert_span (P := addProg) laws
    (s := ⟨num k, num k, []⟩) (goodG_root _)
  refine seqR_cert laws (goodG_root _) hCL fun y hy => ?_
  refine backward (k + 1) _ (goodBO_bound (bnd_leftIface y)) fun u hu => ?_
  obtain ⟨σ, -, rfl⟩ := span_push_left laws (rb := none) trivial hCL (maxima_sub hy) hu
  exact ⟨k, Nat.lt_succ_self k, num_bind σ k⟩

end Addition

end R001

end RwLog
