/-
# The program where one name derives nothing

`P.withBody h .zero` is the program `P` with the body of `h` replaced by the
relation that relates nothing. This file says what it means beside `P`.

* It is carried through the choice of the input to run (`orient`): the input
  chosen for `(P, q)`, with `h` deriving nothing, relates the pairs `q`
  relates in the program where `h` derives nothing, the other way round when
  the run is swapped (`orient_gd_zero`, `orient_pairs_zero`).
* A pair that needs pairs of a call of `h` in a context (`Context.Demands`)
  is not related by the context's query in the program where `h` derives
  nothing (`not_demands_zero`).
-/
import RwLog.Rungs.Framework.OrientedLaws
import RwLog.Rungs.Framework.Admission
import RwLog.Rungs.Framework.Unfolding.Never

namespace RwLog

/-- Programs with the same bodies derive the same. -/
theorem gd_congr {P P' : Program} (h : ∀ n, P.body n = P'.body n) (e : Rel) :
    GD P e = GD P' e := by
  ext G
  exact ⟨DerivesG.mono fun n G hG => by rw [← h n]; exact hG,
    DerivesG.mono fun n G hG => by rw [h n]; exact hG⟩

variable (P : Program) (h : Name)

theorem body_normed_zero (n : Name) :
    (P.normed.withBody h .zero).body n = ((P.withBody h .zero).normed).body n := by
  rw [ProgramOf.normed_body]
  by_cases hn : n = h
  · subst hn
    rw [ProgramOf.withBody_self, ProgramOf.withBody_self]
    rfl
  · rw [ProgramOf.withBody_ne _ _ hn, ProgramOf.withBody_ne _ _ hn, ProgramOf.normed_body]

theorem body_dual_normed_zero (n : Name) :
    (P.dual.normed.withBody h .zero).body n = ((P.withBody h .zero).dual.normed).body n := by
  rw [ProgramOf.normed_body, ProgramOf.dual_body]
  by_cases hn : n = h
  · subst hn
    rw [ProgramOf.withBody_self, ProgramOf.withBody_self]
    rfl
  · rw [ProgramOf.withBody_ne _ _ hn, ProgramOf.withBody_ne _ _ hn, ProgramOf.normed_body,
      ProgramOf.dual_body]

theorem gd_normed_zero (e : Rel) :
    GD (P.normed.withBody h .zero) e = GD (P.withBody h .zero) e :=
  (gd_congr (body_normed_zero P h) e).trans (gd_normed _ e)

theorem gd_dual_normed_zero (e : Rel) :
    GD (P.dual.normed.withBody h .zero) e.dual = GRel.inv '' GD (P.withBody h .zero) e :=
  (gd_congr (body_dual_normed_zero P h) e.dual).trans ((gd_normed _ _).trans (gd_dual _ e))

/-- The root and the swap of a choice do not depend on the program. -/
theorem pick_root_swap (Pn Q : Program) (f : Rel × Bool) (r : List (Rel × Bool)) :
    (pick Q f r).root = (pick Pn f r).root ∧ (pick Q f r).swap = (pick Pn f r).swap := by
  unfold pick
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- The candidate picked, read in another program `Q`. -/
theorem pick_gd_in (Pn Q : Program) (X : Set GRel) (f : Rel × Bool) (r : List (Rel × Bool))
    (hc : ∀ c ∈ f :: r, GD Q c.1 = if c.2 then GRel.inv '' X else X) :
    GD Q (pick Pn f r).root = if (pick Pn f r).swap then GRel.inv '' X else X := by
  obtain ⟨e₁, e₂⟩ := pick_root_swap Pn Q f r
  have := pick_gd Q X f r hc
  rwa [pick_P, e₁, e₂] at this

/-- **The input chosen to run, with `h` deriving nothing, derives what the
input derives with `h` deriving nothing**, or the converses when the run is
swapped. -/
theorem orient_gd_zero (q : Rel) :
    GD ((orient P q).P.withBody h .zero) (orient P q).root =
      if (orient P q).swap then GRel.inv '' GD (P.withBody h .zero) q
      else GD (P.withBody h .zero) q := by
  unfold orient
  cases hc : listCmp relCmp (P.defs.map fun d => d.2.norm) (P.dual.defs.map fun d => d.2.norm)
  · rw [pick_P]
    refine pick_gd_in _ _ _ _ _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [gd_normed_zero, gd_norm, gd_conv]
  · have e := normed_dual_of_eq (listCmp_eq (f := relCmp) hc)
    have hd : GD (P.normed.withBody h .zero) q.dual.norm =
        GRel.inv '' GD (P.withBody h .zero) q := by
      rw [← e, gd_norm, gd_dual_normed_zero]
    have hd' : GD (P.normed.withBody h .zero) (RelOf.conv q.dual).norm =
        GD (P.withBody h .zero) q := by
      rw [← e, gd_norm, gd_conv, gd_dual_normed_zero, inv_image_inv_image]
    rw [pick_P]
    refine pick_gd_in _ _ _ _ _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp [gd_normed_zero, gd_norm, gd_conv, hd, hd']
  · rw [pick_P]
    refine pick_gd_in _ _ _ _ _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simp [gd_norm, gd_conv, gd_dual_normed_zero, inv_image_inv_image]

/-- **The input chosen to run, with `h` deriving nothing, relates the pairs
the input relates with `h` deriving nothing**, the other way round when the
run is swapped. -/
theorem orient_pairs_zero (q : Rel) :
    ((orient P q).P.withBody h .zero).pairs (orient P q).root =
      ((P.withBody h .zero).pairs q).as (orient P q).swap := by
  ext p
  rw [mem_pairs_iff, orient_gd_zero]
  have es : ((orient P q).P.withBody h .zero).sorts = (P.withBody h .zero).sorts :=
    orient_sorts P q
  rw [es]
  cases hb : (orient P q).swap
  · simp only [Bool.false_eq_true, ↓reduceIte, PRel.as]
    exact (mem_pairs_iff _ q p).symm
  · simp only [↓reduceIte, PRel.as]
    show _ ↔ (p.2, p.1) ∈ (P.withBody h .zero).pairs q
    rw [mem_pairs_iff]
    constructor
    · rintro ⟨_, ⟨G, hG, rfl⟩, hp⟩
      exact ⟨G, hG, by rw [at_inv] at hp; exact hp⟩
    · rintro ⟨G, hG, hp⟩
      exact ⟨G.inv, ⟨G, hG, rfl⟩, by rw [at_inv]; exact hp⟩

/-! ## In a context -/

/-- A context relates more when its hole and the names relate more. -/
theorem Ctx.denAt_mono_names (M : Interp) {ρ ρ' : Name → PRel} (hρ : ρ ≤ ρ') {X X' : PRel}
    (hX : X ⊆ X') : ∀ K : Ctx, K.denAt M ρ X ⊆ K.denAt M ρ' X'
  | .hole => hX
  | .orL K b => Set.union_subset_union (Ctx.denAt_mono_names M hρ hX K) (denoteAt_mono M hρ b)
  | .orR a K => Set.union_subset_union (denoteAt_mono M hρ a) (Ctx.denAt_mono_names M hρ hX K)
  | .andL K b => Set.inter_subset_inter (Ctx.denAt_mono_names M hρ hX K) (denoteAt_mono M hρ b)
  | .andR a K => Set.inter_subset_inter (denoteAt_mono M hρ a) (Ctx.denAt_mono_names M hρ hX K)
  | .seqL K b => fun _ ⟨m, h1, h2⟩ => ⟨m, Ctx.denAt_mono_names M hρ hX K h1, denoteAt_mono M hρ b h2⟩
  | .seqR a K => fun _ ⟨m, h1, h2⟩ => ⟨m, denoteAt_mono M hρ a h1, Ctx.denAt_mono_names M hρ hX K h2⟩
  | .conv K => fun _ hp => Ctx.denAt_mono_names M hρ hX K hp

/-- The names mean no more in the program where `h` derives nothing. -/
theorem meaningAt_zero_le (M : Interp) : (P.withBody h .zero).meaningAt M ≤ P.meaningAt M := by
  refine OrderHom.lfp_le _ fun n => ?_
  show denoteAt M (P.meaningAt M) ((P.withBody h .zero).body n) ⊆ P.meaningAt M n
  by_cases hn : n = h
  · subst hn
    rw [ProgramOf.withBody_self]
    exact Set.empty_subset _
  · rw [ProgramOf.withBody_ne _ _ hn, ← ProgramOf.meaningAt_eq]

theorem meaningAt_zero_self (M : Interp) : (P.withBody h .zero).meaningAt M h = ∅ := by
  rw [ProgramOf.meaningAt_eq, ProgramOf.withBody_self]
  rfl

/-- **A pair that needs pairs of a call of `h` is not related where `h`
derives nothing.** -/
theorem not_demands_zero (K : Context) {M : Interp} {X : PRel} {y : GTerm × GTerm}
    (hd : K.Demands P (.call h) M X y) :
    y ∉ ((K.program P).withBody h .zero).semAt M (K.query (.call h)) := by
  intro hy
  refine hd.2 ?_
  unfold ProgramOf.semAt Context.query at hy
  rw [← Ctx.denAt_fill] at hy
  refine Ctx.denAt_mono_names M (meaningAt_zero_le _ h M) ?_ _ hy
  show ((K.program P).withBody h .zero).meaningAt M h ⊆ _
  rw [meaningAt_zero_self]
  exact Set.empty_subset _

end RwLog
