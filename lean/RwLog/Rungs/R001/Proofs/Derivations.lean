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

Relations are compared by `LCov`: `LCov T R S` says that in every model of
the theory, `R` relates every pair `S` relates (`GRel.at`). `Span.CoversLive`
is `LCov` on denotations.
-/
import RwLog.Rungs.R001.Proofs.Kernel
import RwLog.Kernel.Live
import RwLog.Rungs.R000.Properties

namespace RwLog

namespace R001

namespace Lifting

variable {T : Theory}

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

/-! ## The span goal, up to the theory -/

section Kernel

variable (hT : ∀ ρ ∈ T, ρ.WellFormed)
include hT

/-- The composite `lb ; s ; rb` before simplification. -/
def rawO (lb : Option Span) (s : Span) (rb : Option Span) : Option Span :=
  (match lb with
    | none => some s
    | some l => l.compose s).bind fun s' => match rb with
      | none => some s'
      | some r => s'.compose r

omit hT in
theorem spanAnswer_eq (lb : Option Span) (s : Span) (rb : Option Span) :
    spanAnswer T lb s rb = liveO T (rawO lb s rb) := by
  cases lb <;> cases rb <;> rfl

omit hT in
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
  exact liveO_spec hT (rawO_den lb s rb)

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

variable (hT : ∀ ρ ∈ P.theory, ρ.WellFormed)
include hT

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
      exact ⟨s₀, hd₀, (live_leq hT hy).trans (LEq.of_eq (he.trans he₀))⟩
    · simp at hy
  | @span lb rb s y hy =>
    intro _ _ _
    exact ⟨s, .span s, (spanAnswer_spec hT lb s rb).1 y hy⟩
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
    have hzc := (composeLive_spec hT x w).1 z hz
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
    have hzc := (composeLive_spec hT x w).1 z hz
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
    have hzc := (composeLive_spec hT x w).1 z hz
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
    have hzc := (meetLive_spec hT x w).1 z hz
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
    have hzc := (meetLive_spec hT x w).1 z hz
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
    have hzc := (meetLive_spec hT x w).1 z hz
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
    obtain ⟨y, hy⟩ := (spanAnswer_spec hT lb s rb).2 hl
    have he := (spanAnswer_spec hT lb s rb).1 y hy
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
    obtain ⟨z, hz⟩ := (composeLive_spec hT x w).2 (hcov.live hl)
    have hze := (composeLive_spec hT x w).1 z hz
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
    obtain ⟨z, hz⟩ := (meetLive_spec hT x w).2 (hcov.live hl)
    have hze := (meetLive_spec hT x w).1 z hz
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
theorem boundary_lifting : Obligation.boundary_lifting := by
  intro P g hT hdiag
  obtain ⟨lb, e, rb⟩ := g
  have hL : PId (bden lb) := pid_bden fun b hb => hdiag b (by simp [hb])
  have hR : PId (bden rb) := pid_bden fun b hb => hdiag b (by simp [hb])
  refine ⟨fun y hy hnd => ?_, fun y₀ hy₀ z hz hnd => ?_⟩
  · have hl := not_dead_iff.1 hnd
    obtain ⟨s₀, hd, he⟩ := toDerives hT hy hL hR hl
    have hls : Live P.theory (W none s₀.den none) := by
      rw [W_none]; exact live_wrap_mid (he.2.live hl)
    obtain ⟨c, hc, y₀, hy₀, h₁, h₂⟩ := toGDerives hT hd none none hls
    rw [W_none] at h₁ h₂
    have hW : LEq P.theory (W lb y₀.den rb) y.den :=
      (LEq.W ⟨h₁, h₂ pid_id pid_id⟩ lb rb).trans he.symm
    obtain ⟨z, hz⟩ := (spanAnswer_spec hT lb y₀ rb).2 (hW.1.live hl)
    have hzW := (spanAnswer_spec hT lb y₀ rb).1 z hz
    exact ⟨y₀, lift_leaf hc hy₀, z, hz, coversLive_iff.2 (hzW.1.trans hW.1),
      coversLive_iff.2 (hW.2.trans hzW.2)⟩
  · have hl := not_dead_iff.1 hnd
    have hzW := (spanAnswer_spec hT lb y₀ rb).1 z hz
    have hlW := hzW.2.live hl
    obtain ⟨s₀, hd, he⟩ := toDerives hT hy₀ pid_id pid_id (live_wrap_mid hlW)
    rw [W_none] at he
    have hWs : LEq P.theory (W lb s₀.den rb) (W lb y₀.den rb) := LEq.W he.symm lb rb
    obtain ⟨c, hc, y, hy, h₁, -⟩ := toGDerives hT hd lb rb (hWs.1.live hlW)
    exact ⟨y, lift_leaf hc hy, coversLive_iff.2 (h₁.trans (hWs.1.trans hzW.2))⟩

end R001

end RwLog
