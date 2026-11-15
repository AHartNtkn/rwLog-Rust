/-
# What the input chosen to run means

`orient` (`Trusted/Cost.lean`) chooses one of the inputs an input stands
with. The input chosen derives the ground relations the input derives, or
their converses when what the run shows is to be swapped (`orient_gd`), and
it is well formed if the input is (`wf_orient`).
-/
import RwLog.Rungs.Framework.Oriented
import RwLog.Rungs.Framework.GroundMirror
import RwLog.Rungs.Framework.SameTrace
import RwLog.Kernel.NormalFormCalls

namespace RwLog

/-- The candidate picked derives `X`, or its converses when the run is to be
swapped, if every candidate does. -/
theorem pick_gd (Pn : Program) (X : Set GRel) (f : Rel × Bool) (r : List (Rel × Bool))
    (h : ∀ c ∈ f :: r, GD Pn c.1 = if c.2 then GRel.inv '' X else X) :
    GD (pick Pn f r).P (pick Pn f r).root =
      if (pick Pn f r).swap then GRel.inv '' X else X := by
  obtain ⟨c, hc, hcm⟩ : ∃ c ∈ f :: r, c.1 = leastRel f.1 (r.map Prod.fst) := by
    rcases List.mem_cons.1 (leastRel_mem f.1 (r.map Prod.fst)) with h | h
    · exact ⟨f, by simp, h.symm⟩
    · obtain ⟨c, hc, e⟩ := List.mem_map.1 h
      exact ⟨c, List.mem_cons_of_mem _ hc, e⟩
  have hcw : c.2 ∈ ((f :: r).filter fun x => x.1 = leastRel f.1 (r.map Prod.fst)).map Prod.snd :=
    List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simpa using hcm⟩, rfl⟩
  unfold pick
  dsimp only
  split
  · rename_i hall
    have hf : c.2 = false := by simpa using List.all_eq_true.1 hall c.2 hcw
    have h' := h c hc
    rw [hcm, hf] at h'
    simpa using h'
  · rename_i h1
    split
    · rename_i hall
      have hf : c.2 = true := by simpa using List.all_eq_true.1 hall c.2 hcw
      have h' := h c hc
      rw [hcm, hf] at h'
      simpa using h'
    · rename_i h2
      have ex : ∀ w : Bool, ∃ c ∈ f :: r, c.1 = leastRel f.1 (r.map Prod.fst) ∧ c.2 = w := by
        intro w
        by_contra hno
        have key : ∀ b ∈ ((f :: r).filter fun x => x.1 = leastRel f.1 (r.map Prod.fst)).map
            Prod.snd, b = !w := by
          intro b hb
          obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hb
          obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc'
          have : c'.2 ≠ w := fun e => hno ⟨c', hc1, by simpa using hc2, e⟩
          cases hw : w <;> cases hb' : c'.2 <;> simp_all
        cases w
        · exact h2 (List.all_eq_true.2 fun b hb => by simpa using key b hb)
        · exact h1 (List.all_eq_true.2 fun b hb => by simpa using key b hb)
      obtain ⟨c1, hc1, e1, w1⟩ := ex false
      obtain ⟨c2, hc2, e2, w2⟩ := ex true
      have g1 := h c1 hc1
      have g2 := h c2 hc2
      rw [e1, w1] at g1
      rw [e2, w2] at g2
      simp only [Bool.false_eq_true, ↓reduceIte] at g1 g2 ⊢
      rw [gd_norm, gd_or, gd_normConv, g1, ← g2, g1, Set.union_self]

/-- **The input chosen to run derives what the input derives**, or the
converses when what the run shows is to be swapped. -/
theorem orient_gd (P : Program) (q : Rel) :
    GD (orient P q).P (orient P q).root =
      if (orient P q).swap then GRel.inv '' GD P q else GD P q := by
  unfold orient
  cases hc : listCmp relCmp (P.defs.map fun d => d.2.norm) (P.dual.defs.map fun d => d.2.norm)
  · refine pick_gd _ _ _ _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [gd_normed, gd_norm, gd_conv]
  · have hd : GD P.normed q.dual.norm = GRel.inv '' GD P q := by
      rw [← normed_dual_of_eq (listCmp_eq (f := relCmp) hc), gd_normed, gd_norm, gd_dual]
    have hd' : GD P.normed (RelOf.conv q.dual).norm = GD P q := by
      rw [← normed_dual_of_eq (listCmp_eq (f := relCmp) hc), gd_normed, gd_norm, gd_conv,
        gd_dual, inv_image_inv_image]
    refine pick_gd _ _ _ _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp [gd_normed, gd_norm, gd_conv, hd, hd']
  · refine pick_gd _ _ _ _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simp [gd_normed, gd_norm, gd_conv, gd_dual, inv_image_inv_image]

/-! ## The input chosen is well formed -/

theorem pick_wf (Pn : Program) {f : Rel × Bool} {r : List (Rel × Bool)}
    (h : ∀ c ∈ f :: r, Pn.WellFormed c.1) : (pick Pn f r).P.WellFormed (pick Pn f r).root := by
  have hm : Pn.WellFormed (leastRel f.1 (r.map Prod.fst)) := by
    have := leastRel_mem f.1 (r.map Prod.fst)
    have e : f.1 :: r.map Prod.fst = (f :: r).map Prod.fst := rfl
    rw [e, List.mem_map] at this
    obtain ⟨y, hy, hy'⟩ := this
    rw [← hy']; exact h y hy
  unfold pick
  dsimp only
  split
  · exact hm
  · split
    · exact hm
    · refine hm.of_calls_fo (fun n hn => ?_) (RelOf.FO.norm fun s hs => ?_)
      · rcases List.mem_append.1 (calls_norm hn) with hn | hn
        · exact hn
        · exact calls_normConv hn
      · rcases List.mem_append.1 hs with hs | hs
        · exact hm.fo s hs
        · exact hm.fo.normConv s hs

/-- **The input chosen from a well-formed input is well formed.** -/
theorem wf_orient {P : Program} {q : Rel} (wf : P.WellFormed q) :
    (orient P q).P.WellFormed (orient P q).root := by
  unfold orient
  cases hc : listCmp relCmp (P.defs.map fun d => d.2.norm) (P.dual.defs.map fun d => d.2.norm)
  · refine pick_wf _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact wf.normed
    · exact wf.conv.normed
  · have e := normed_dual_of_eq (listCmp_eq (f := relCmp) hc)
    refine pick_wf _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact wf.normed
    · exact wf.conv.normed
    · exact e ▸ wf.dual.normed
    · exact e ▸ wf.dual.conv.normed
  · refine pick_wf _ fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact wf.dual.normed
    · exact wf.dual.conv.normed

end RwLog
