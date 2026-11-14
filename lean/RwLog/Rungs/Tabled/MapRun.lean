/-
# Two runs of the tabled machine that correspond, round after round

From the table of a root node and the table of its image, the tables of the
two runs correspond after every round (`tied_at`). So the root tables are
complete in the same rounds (`rootDone_map`), gain corresponding answers in
every round (`rootGain_map`), and have corresponding maximal answers
(`rootMax_map`): the representatives of one list are those of the other,
conversed when the node map is the converse, up to order (`SpansPerm`).

`Link.of_ex`: two unfolding races that say what the unfolding is (`UEx`) are
linked when the unfolding of the image of a node is the image of the
unfolding of the node.
-/
import RwLog.Rungs.Tabled.MapRound
import RwLog.Rungs.Tabled.Run
import RwLog.Rungs.Tabled.Unfolding.ModelMap
import RwLog.Rungs.Tabled.Unfolding.RacesExact

namespace RwLog

namespace Tabled

open Answer Unfold

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P P' : Program}

/-! ## Races that say what the unfolding is -/

omit [DecidableEq R] in
theorem bset_ite (M : Interp) (b : Bool) (x y : Option R) :
    bset M (if b then x else y) = if b then bset M x else bset M y := by
  cases b <;> rfl

omit [DecidableEq R] in
theorem den_smap (M : Interp) (b : Bool) (r : R) :
    den M (smap b r) = if b then (den M r).inv else den M r := by
  cases b
  · rfl
  · exact Answer.den_swap M r

omit [DecidableEq R] in
theorem Link.of_ex {b t : Bool} {U : GOracle R Rel (Ans D P) Cost}
    {U' : GOracle R Rel (Ans D P') Cost} (hL' : D.Lawful P'.sorts.interp)
    (hM : P'.sorts.interp = P.sorts.interp) (hU : UEx D P U) (hU' : UEx D P' U')
    (hbody : ∀ e, Normal e →
      Charged.bodyOf P' (nmap b t e) = (Charged.bodyOf P e).map (nmap b t))
    (hfin : ∀ d e, Normal e → ∀ A B : Set GTerm,
      Final P' P.sorts.interp d (if b then B else A) (nmap b t e) (if b then A else B) ↔
        Final P P.sorts.interp d A e B)
    (hcl : ∀ d e, Normal e → ∀ (A B : Set GTerm) (X : PRel),
      X ∈ closedPart (SE P' P.sorts.interp d (if b then B else A) (nmap b t e)
          (if b then A else B)) ↔
        (if b then X.inv else X) ∈ closedPart (SE P P.sorts.interp d A e B)) :
    Link D P P' b t U U' := by
  have hv : ∀ d g, GoalOk D g → (U' d (gmap b t g)).val.1 = (U d g).val.1 := by
    intro d g hg
    rw [Bool.eq_iff_iff, hU'.final d _ (hg.gmap b t), hU.final d g hg, hM]
    show Final P' _ d (bset _ (if b then g.rb else g.lb)) (nmap b t g.node)
      (bset _ (if b then g.lb else g.rb)) ↔ _
    rw [bset_ite, bset_ite]
    exact hfin d g.node hg.normal _ _
  refine ⟨hbody, hv, fun d g hg a ha => ?_⟩
  have hf : (U d g).val.1 = true := by
    cases h : (U d g).val.1 with
    | true => rfl
    | false => rw [hU.none d g h] at ha; cases ha
  have hX := (hU.closed d g hg hf _).1 ⟨a, ha, rfl⟩
  have hf' : (U' d (gmap b t g)).val.1 = true := (hv d g hg).trans hf
  have hX' : den P'.sorts.interp (smap b a.span) ∈
      closedPart (SE P' P'.sorts.interp d (bset P'.sorts.interp (gmap b t g).lb)
        (gmap b t g).node (bset P'.sorts.interp (gmap b t g).rb)) := by
    rw [hM]
    show _ ∈ closedPart (SE P' _ d (bset _ (if b then g.rb else g.lb)) (nmap b t g.node)
      (bset _ (if b then g.lb else g.rb)))
    rw [bset_ite, bset_ite, hcl d g.node hg.normal, den_smap]
    cases b
    · exact hX
    · exact hX
  obtain ⟨a', ha', e⟩ := (hU'.closed d _ (hg.gmap b t) hf' _).2 hX'
  exact ⟨a', ha', hL'.canon _ _ e⟩

/-! ## The runs -/

variable (K : Kernel R Cost) (hK : K.Refines D)
  {b t : Bool} {U : GOracle R Rel (Ans D P) Cost} {U' : GOracle R Rel (Ans D P') Cost}

/-- The representatives of the second list are those of the first, conversed
when `b`, up to order. -/
def SpansPerm (b : Bool) (xs : List (Ans D P)) (ys : List (Ans D P')) : Prop :=
  (ys.map (·.span)).Perm (xs.map fun a => smap b a.span)

omit [DecidableEq R] in
/-- Two lists of answers none of which covers another, with corresponding
representatives. -/
theorem spansPerm_of {M : Interp} (hL : D.Lawful M) {xs : List (Ans D P)} {ys : List (Ans D P')}
    (hx : xs.Pairwise fun y x => covB D P y x = false ∧ covB D P x y = false)
    (hy : ys.Pairwise fun y x => covB D P' y x = false ∧ covB D P' x y = false)
    (h₁ : ∀ a ∈ xs, ∃ a' ∈ ys, a'.span = smap b a.span)
    (h₂ : ∀ a' ∈ ys, ∃ a ∈ xs, a'.span = smap b a.span) : SpansPerm b xs ys := by
  have hne : ∀ {Q : Program} {y x : Ans D Q}, covB D Q y x = false → y.span ≠ x.span := by
    intro Q y x h e
    unfold covB at h
    rw [e, hL.covers_refl] at h; cases h
  refine (List.perm_ext_iff_of_nodup ?_ ?_).2 fun r => ?_
  · exact List.pairwise_map.2 (hy.imp fun {y x} h => hne (y := y) (x := x) h.1)
  · exact List.pairwise_map.2 (hx.imp fun {y x} h e => hne (y := y) (x := x) h.1 (smap_inj hL e))
  · simp only [List.mem_map]
    constructor
    · rintro ⟨a', ha', rfl⟩
      obtain ⟨a, ha, e⟩ := h₂ a' ha'
      exact ⟨a, ha, e.symm⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨a', ha', e⟩ := h₁ a ha
      exact ⟨a', ha', e⟩

section run

variable (hW : Twin D P P' b t U U') (root : Rel)
  (hroot : GoalOk D (⟨none, root, none⟩ : GoalOf R Rel))
include hW hroot

/-- The tables of the two runs correspond after every round. -/
theorem tied_at : ∀ r, Tied b t (tablesAt K hK U root r) (tablesAt K hK U' (nmap b t root) r)
  | 0 => by
    have hroot' : GoalOk D (⟨none, nmap b t root, none⟩ : GoalOf R Rel) := by
      have := hroot.gmap b t
      cases b <;> exact this
    have key : ∀ {Q Q' : Program} (n n' : Rel)
        (_ : gmap b t (⟨none, n, none⟩ : GoalOf R Rel) = ⟨none, n', none⟩),
        Fwd b t ([⟨⟨none, n, none⟩, [], false⟩] : List (TableOf R Rel (Ans D Q)))
          ([⟨⟨none, n', none⟩, [], false⟩] : List (TableOf R Rel (Ans D Q'))) := by
      intro Q Q' n n' e
      refine ⟨fun g i h => ?_, fun g h => ?_, fun g a ha => ?_⟩
      · obtain ⟨_, hg, -⟩ := idx_some.1 h
        obtain rfl : (⟨none, n, none⟩ : GoalOf R Rel) = g := by simpa using hg
        exact ⟨0, idx_some.2 ⟨by simp, by simpa using e.symm, fun j hj => by omega⟩⟩
      · obtain ⟨i, hi⟩ := idx_of_done h
        obtain ⟨hil, e'⟩ := isDone_of_idx hi
        rw [e'] at h
        have : i = 0 := by simpa using hil
        subst this
        cases h
      · obtain ⟨i, hi⟩ := idx_of_ans ha
        obtain ⟨hil, e'⟩ := ansOf_of_idx hi
        rw [e'] at ha
        have : i = 0 := by simpa using hil
        subst this
        cases ha
    have e₁ : gmap b t (⟨none, root, none⟩ : GoalOf R Rel) = ⟨none, nmap b t root, none⟩ := by
      cases b <;> rfl
    have e₂ : gmap b t (⟨none, nmap b t root, none⟩ : GoalOf R Rel) = ⟨none, root, none⟩ := by
      rw [← e₁, gmap_gmap hroot.normal]
    exact ⟨inv_at hW.law hW.fo hW.uok hroot 0, inv_at hW.law' hW.fo' hW.uok' hroot' 0,
      by simp [GoalsNodup, tablesAt], by simp [GoalsNodup, tablesAt], key _ _ e₁, key _ _ e₂⟩
  | r + 1 => tied_next K hK hW (tied_at r) r

omit hW hroot in
theorem idx_root (U : GOracle R Rel (Ans D P) Cost) (root : Rel) (r : Nat) :
    idx (tablesAt K hK U root r) ⟨none, root, none⟩ = some 0 :=
  idx_mono (Nat.zero_le r) (idx_some.2 ⟨by simp [tablesAt], by simp [tablesAt],
    fun j hj => by omega⟩)

omit hroot in
theorem idx_root' (r : Nat) :
    idx (tablesAt K hK U' (nmap b t root) r) (gmap b t ⟨none, root, none⟩) = some 0 := by
  have : gmap b t (⟨none, root, none⟩ : GoalOf R Rel) = ⟨none, nmap b t root, none⟩ := by
    cases b <;> rfl
  rw [this]
  exact idx_root K hK U' _ r

/-- The two root tables are complete in the same rounds. -/
theorem rootDone_map (r : Nat) :
    rootDone K hK U' (nmap b t root) r = rootDone K hK U root r := by
  obtain ⟨_, j, _, hj, -, -, hd, -⟩ := pair_tab (tied_at K hK hW root hroot r) (idx_root K hK U root r)
  obtain rfl : j = 0 := Option.some.inj (hj.symm.trans (idx_root' K hK hW root r))
  rw [rootDone_eq, rootDone_eq]
  exact hd

/-- What the two root tables gain in a round. -/
theorem rootGain_map (r : Nat) :
    SpansPerm b
      (gainOf K hK U (tablesAt K hK U root r) r ((tablesAt K hK U root r)[0]'(root_pos r)))
      (gainOf K hK U' (tablesAt K hK U' (nmap b t root) r) r
        ((tablesAt K hK U' (nmap b t root) r)[0]'(root_pos r))) := by
  have hT := tied_at K hK hW root hroot r
  have h₀ := idx_root K hK U root r
  have h₀' := idx_root' K hK hW root r
  refine spansPerm_of hW.law (fresh_pairwise K hK _ _) (fresh_pairwise K hK _ _)
    (fun a ha => gain_fwd K hK hW hT r h₀ h₀' (root_pos r) (root_pos r) ha) fun a' ha' => ?_
  have hback : idx (tablesAt K hK U root r) (gmap b t (gmap b t ⟨none, root, none⟩)) = some 0 := by
    rw [gmap_gmap hroot.normal]; exact h₀
  obtain ⟨a, ha, e⟩ := gain_fwd K hK hW.symm hT.symm r h₀' hback (root_pos r) (root_pos r) ha'
  exact ⟨a, ha, by rw [e, smap_smap hW.law']⟩

/-- The maximal answers of the two root tables. -/
theorem rootMax_map (r : Nat) :
    SpansPerm b ((rootAns K hK U root r).maximaBy (covB D P))
      ((rootAns K hK U' (nmap b t root) r).maximaBy (covB D P')) := by
  have hT := tied_at K hK hW root hroot r
  obtain ⟨_, e₁⟩ := ansOf_of_idx (idx_root K hK U root r)
  obtain ⟨_, e₂⟩ := ansOf_of_idx (idx_root' K hK hW root r)
  rw [rootAns_eq, rootAns_eq, ← e₁, ← e₂]
  exact spansPerm_of hW.law (List.maximaBy_pairwise _) (List.maximaBy_pairwise _)
    (fun a ha => maxima_fwd hW hT hroot.normal ha)
    (fun a' ha' => maxima_back hW hT hroot.normal ha')

end run

end Tabled

end RwLog
