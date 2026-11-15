/-
# A certificate of completion, read on the mirror image

A certificate that goals of a program complete (`Cert`,
`Rungs/Symmetric/Transfer.lean`) has no run in it, so it can be read on
another program: the same program for the converse of every node, or the
mirrored program for the mirror image of every node (`nmap b t`,
`Kernel/NormalFormMap.lean`).

`Mirror` is what links the two programs and their unfolding races: what links
two runs of the tabled machine (`Tabled.Twin`), that the two programs have
one interpretation, that the image of a node derives the relations the node
derives, conversed when the converse is taken, and that an edge of the image
of a node is read when the edge of the node is, with no other interface.

`FCert` is a certificate whose goals with no reason among the others have a
final unfolding. It is a certificate (`FCert.cert`, by `final_completes`),
and its image under the map of goals (`gmap b t`) is one of the other
program (`FCert.map`): every reason is read on the image.

* A span, the body of a call and the members of a union are mapped
  (`Tabled.Link`, `Normal.view_union_nmap`).
* A split of a chain is the split of the mapped chain at the mirrored place,
  with the sides exchanged when the converse is taken; a split of a meet is a
  split of the mapped meet, with the sides exchanged or not (`splitAt_gmap`).
* The goal pushed for an answer is mapped to the goal pushed for the mapped
  answer, into the other side when the sides are exchanged (`pushG_gmap`).
* The answers are mapped by their representatives (`amap`); an answer is one
  by what it relates (`Valid`), which the map keeps (`Mirror.valid`).
-/
import RwLog.Rungs.Symmetric.FromTabled
import RwLog.Rungs.Tabled.MapSplit
import RwLog.Rungs.Framework.GroundMirror

namespace RwLog

namespace Symmetric

open Answer Saturation Goals Unfold
open Tabled (gmap smap gmap_gmap smap_smap covers_smap leftBound_swap)

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P P' : Program} {b t : Bool}
  {U : GOracle R Rel (Ans D P) Cost} {U' : GOracle R Rel (Ans D P') Cost}

/-- What links a program and its unfolding race to another, for the map of
nodes `nmap b t`. -/
structure Mirror (D : Domain R) (P P' : Program) (b t : Bool)
    (U : GOracle R Rel (Ans D P) Cost) (U' : GOracle R Rel (Ans D P') Cost) : Prop where
  twin : Tabled.Twin D P P' b t U U'
  interp : P'.sorts.interp = P.sorts.interp
  gd : ∀ e, Normal e → GD P' (nmap b t e) = if b then GRel.inv '' GD P e else GD P e
  reads : ∀ (n : Rel) (last : Bool) (ps : List R), Normal n → Reads D P n last (some ps) →
    ∃ ps', Reads D P' (nmap b t n) (last ^^ b) (some ps') ∧ ∀ p ∈ ps', p ∈ ps
  reads' : ∀ (n : Rel) (last : Bool) (ps : List R), Normal n → Reads D P' n last (some ps) →
    ∃ ps', Reads D P (nmap b t n) (last ^^ b) (some ps') ∧ ∀ p ∈ ps', p ∈ ps

theorem Mirror.symm (hM : Mirror D P P' b t U U') : Mirror D P' P b t U' U where
  twin := hM.twin.symm
  interp := hM.interp.symm
  gd := fun e he => by
    have h := hM.gd (nmap b t e) (normal_nmap b t e)
    rw [he.nmap_nmap] at h
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact h.symm
    · simp only [↓reduceIte] at h ⊢
      rw [h, inv_image_inv_image]
  reads := hM.reads'
  reads' := hM.reads

/-- **The image of an answer is an answer of the image of the goal.** -/
theorem Mirror.valid (hM : Mirror D P P' b t U U') {g : GoalOf R Rel} (hg : Normal g.node)
    {s : R} (h : Valid D P (toGoal g) s) : Valid D P' (toGoal (gmap b t g)) (smap b s) := by
  obtain ⟨⟨hl, hr⟩, hd⟩ := h
  refine ⟨?_, fun _ => ?_⟩
  · cases b
    · exact ⟨hl, hr⟩
    · exact ⟨hr, hl⟩
  obtain ⟨s0, hs0, e⟩ := hd hM.twin.law
  have hG : (if b then s0.den.inv else s0.den) ∈ GD P' (nmap b t g.node) := by
    rw [hM.gd _ hg]
    cases b
    · exact hs0.derivesG
    · exact ⟨_, hs0.derivesG, rfl⟩
  have hne : (if b then s0.den.inv else s0.den).Nonempty := by
    cases b
    · exact s0.den_nonempty
    · exact GRel.inv_nonempty.2 s0.den_nonempty
  obtain ⟨s', hs', e'⟩ := derives_iff_derivesG.2 ⟨hG, hne⟩
  refine ⟨s', hs', ?_⟩
  rw [hM.interp, e']
  cases b
  · exact e
  · show den P.sorts.interp (Answer.swap s) = wrapAt P.sorts.interp g.rb _ g.lb
    rw [den_swap, e, wrapAt_inv hM.twin.law hl hr]
    simp only [↓reduceIte, at_inv]
    rfl

/-! ## Splits and pushed goals -/

omit [Answer R] [DecidableEq R] in
/-- **A split of a goal is a split of its image**, into the images of the
two sides: exchanged for a chain when the converse is taken, and exchanged
or not for a meet. -/
theorem splitAt_gmap {g L Rg : GoalOf R Rel} (hg : GoalOk D g) (b t : Bool) {k : Kind}
    (h : SplitAt g k L Rg) :
    ∃ sw : Bool, (k = .seq → sw = b) ∧
      SplitAt (gmap b t g) k (if sw then gmap b t Rg else gmap b t L)
        (if sw then gmap b t L else gmap b t Rg) := by
  cases k with
  | seq =>
    obtain ⟨xs, i, l, r, hv, h0, hin, hl, hr, rfl, rfl⟩ := h
    have hlen := (hg.normal.chain_split hv h0 hin).1
    have hview := hg.normal.view_chain_nmap hv b t
    refine ⟨b, fun _ => rfl, ?_⟩
    cases b
    · refine ⟨xs.map (nmap false t), i, nmap false t l, nmap false t r, by simpa [gmap] using hview, h0,
        by simpa using hin, ?_, ?_, rfl, rfl⟩
      · show (nmap false t g.node).interval 0 i = _
        rw [hg.normal.nmap_interval false t h0 (by omega)]
        simp [hl]
      · show (nmap false t g.node).interval i (xs.map (nmap false t)).length = _
        rw [List.length_map, hg.normal.nmap_interval false t hin (by omega)]
        simp [hr]
    · refine ⟨xs.reverse.map (nmap true t), xs.length - i, nmap true t r, nmap true t l,
        by simpa [gmap] using hview, by omega, by simp; omega, ?_, ?_, rfl, rfl⟩
      · show (nmap true t g.node).interval 0 (xs.length - i) = _
        rw [hg.normal.nmap_interval true t (by omega) (by omega), hlen]
        simp only [ite_true, Nat.sub_zero, Nat.sub_sub_self (Nat.le_of_lt hin), hr,
          Option.map_some]
      · show (nmap true t g.node).interval (xs.length - i) (xs.reverse.map (nmap true t)).length = _
        rw [List.length_map, List.length_reverse,
          hg.normal.nmap_interval true t (by omega) (by omega), hlen]
        simp only [ite_true, Nat.sub_self, Nat.sub_sub_self (Nat.le_of_lt hin), hl,
          Option.map_some]
  | and =>
    obtain ⟨xs, i, l, r, hv, hi, hl, hr, rfl, rfl⟩ := h
    obtain ⟨h2, -, -, -⟩ := hg.normal.view_meet hv
    have hilt := Tabled.mem_andSplits h2 hi
    have hparts := (hg.normal.meet_split hv hilt).1
    have hview := hg.normal.view_meet_nmap hv b t
    have hparts' : andParts (nmap b t g.node) = sortedParts (xs.map (nmap b t)) := by
      rw [hg.normal.andParts_nmap, hparts]
    have hperm : (sortedParts (xs.map (nmap b t))).Perm (xs.map (nmap b t)) := sortedParts_perm _
    have hlen : (sortedParts (xs.map (nmap b t))).length = xs.length := by
      rw [hperm.length_eq, List.length_map]
    have key : ∀ (i j : Nat) (x y : Rel), xs[i]? = some x → g.node.without i = some y →
        (sortedParts (xs.map (nmap b t)))[j]? = some (nmap b t x) →
        (nmap b t g.node).without j = some (nmap b t y) := by
      intro i j x y hx hy hj
      rw [hg.normal.nmap_without b t (by rw [hparts]; exact h2) (by rw [hparts]; exact hx)
        (by rw [hparts']; exact hj), hy]
      rfl
    have same : ∀ x : Rel, (⟨(gmap b t g).lb, nmap b t x, (gmap b t g).rb⟩ : GoalOf R Rel) =
        gmap b t ⟨g.lb, x, g.rb⟩ := fun x => by cases b <;> rfl
    obtain ⟨j, hjlt, hj⟩ := List.getElem_of_mem
      (hperm.mem_iff.2 (List.mem_map_of_mem (List.mem_of_getElem? hl)))
    have hj' : (sortedParts (xs.map (nmap b t)))[j]? = some (nmap b t l) := by
      rw [List.getElem?_eq_getElem hjlt, hj]
    by_cases hjs : j ∈ andSplits (sortedParts (xs.map (nmap b t))).length
    · exact ⟨false, (fun h => by cases h),
        _, j, _, _, hview, hjs, hj', key _ _ _ _ hl hr hj', (same l).symm, (same r).symm⟩
    · refine ⟨true, (fun h => by cases h), ?_⟩
      rw [hlen] at hjs hjlt
      have hn : xs.length = 2 := by
        by_contra hne
        exact hjs (by unfold andSplits; rw [ite_of_neg (by omega)]; exact List.mem_range.2 hjlt)
      have hi0 : i = 0 := by
        unfold andSplits at hi; rw [ite_of_pos (by omega)] at hi; simpa using hi
      have hj1 : j = 1 := by
        have : j ≠ 0 := fun h => hjs (by unfold andSplits; rw [ite_of_pos (by omega)]; simp [h])
        omega
      subst hi0 hj1
      match xs, hn, hl, hr, hparts, hperm, hlen, hj', key, hview with
      | [a, m], _, hl, hr, hparts, hperm, hlen, hj', key, hview =>
        obtain rfl : a = l := by simpa using hl
        have hr0 := Tabled.without_eq hparts (i := 0) (by simp) (by simp)
        have hr1 := Tabled.without_eq hparts (i := 1) (by simp) (by simp)
        obtain rfl : m = r := by
          rw [hr0] at hr; simpa [mkAnd] using hr
        have hr1' : g.node.without 1 = some a := by rw [hr1]; rfl
        match hs : sortedParts ([a, m].map (nmap b t)), hlen with
        | [u, v], _ =>
          rw [hs] at hperm hj' key hview
          obtain rfl : v = nmap b t a := by simpa using hj'
          have hu : u = nmap b t m := by
            have hu' : u ∈ [nmap b t a, nmap b t m] := by
              simpa using hperm.mem_iff.1 (List.mem_cons_self ..)
            rcases List.mem_cons.1 hu' with rfl | hu'
            · have : nmap b t m ∈ [nmap b t a, nmap b t a] :=
                hperm.mem_iff.2 (by simp)
              exact (by simpa using this : nmap b t m = nmap b t a).symm
            · simpa using hu'
          subst hu
          exact ⟨_, 0, nmap b t m, nmap b t a, hview, by simp [andSplits], by simp,
            key 1 0 m a (by simp) hr1' (by simp), (same m).symm, (same a).symm⟩

section laws

variable (hL : D.Lawful P.sorts.interp)
include hL

omit [DecidableEq R] in
/-- **The goal pushed for the image of an answer is the image of the goal
pushed for the answer**: in a chain, into the other side when the converse
is taken. -/
theorem pushG_gmap (g : GoalOf R Rel) (other : Rel) (k : Kind) (left sw : Bool)
    (hsw : k = .seq → sw = b) {x : Ans D P} {x' : Ans D P'} (e : x'.span = smap b x.span) :
    pushG D (gmap b t g) (nmap b t other) k (left ^^ sw) x' =
      gmap b t (pushG D g other k left x) := by
  cases k with
  | seq =>
    obtain rfl := hsw rfl
    cases sw
    · cases left <;> simp [pushG, gmap, e, smap]
    · cases left <;> simp [pushG, gmap, e, smap, Domain.leftBound, hL.swap_swap]
  | and =>
    cases b
    · cases left <;> cases sw <;> simp [pushG, gmap, e, smap]
    · cases left <;> cases sw <;> simp [pushG, gmap, e, smap, Domain.leftBound, hL.swap_swap]

end laws

/-! ## The image of an answer -/

open Classical in
/-- The image of an answer, as an answer of the goal `g'`, if it is one. -/
noncomputable def amap (P' : Program) (b : Bool) (g' : GoalOf R Rel) (a : Ans D P) :
    Option (Ans D P') :=
  if h : Valid D P' (toGoal g') (smap b a.span) then some ⟨toGoal g', smap b a.span, h⟩ else none

omit [DecidableEq R] in
theorem amap_spec {g' : GoalOf R Rel} {a : Ans D P} {a' : Ans D P'}
    (h : amap P' b g' a = some a') : a'.goal = toGoal g' ∧ a'.span = smap b a.span := by
  unfold amap at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-- An answer of the image of a goal has an image that is an answer of the
goal. -/
theorem Mirror.amap_some (hM : Mirror D P P' b t U U') {g' : GoalOf R Rel} (hn : Normal g'.node)
    {a : Ans D P} (ha : a.goal = toGoal (gmap b t g')) :
    ∃ a', amap P' b g' a = some a' ∧ a'.goal = toGoal g' ∧ a'.span = smap b a.span := by
  have hv : Valid D P' (toGoal g') (smap b a.span) := by
    have := hM.valid (g := gmap b t g') (normal_nmap b t _) (ha ▸ a.valid)
    rwa [gmap_gmap hn] at this
  exact ⟨⟨toGoal g', smap b a.span, hv⟩, by unfold amap; simp only [hv, ↓reduceDIte], rfl, rfl⟩

/-! ## Certificates with final unfoldings -/

/-- A certificate that the goals `C` complete, in which a goal with no
reason among the others has an unfolding that is final at some depth. -/
structure FCert (U : GOracle R Rel (Ans D P) Cost) (C : GoalOf R Rel → Prop)
    (ρ : GoalOf R Rel → Nat) (A : GoalOf R Rel → List (Ans D P)) : Prop where
  fin : ∃ l : List (GoalOf R Rel), ∀ g, C g → g ∈ l
  goal : ∀ g, C g → ∀ a ∈ A g, a.goal = toGoal g
  full : ∀ g, C g → ∀ y : Ans D P, y.goal = toGoal g → ∃ f ∈ A g, covB D P f y = true
  ok : ∀ g, C g → GoalOk D g
  why : ∀ g, C g → (∃ d, (U d g).val.1 = true) ∨ Why C ρ A g

variable {C : GoalOf R Rel → Prop} {ρ : GoalOf R Rel → Nat} {A : GoalOf R Rel → List (Ans D P)}

/-- **A certificate with final unfoldings is a certificate.** -/
theorem FCert.cert (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
    (hE : UEx D P U) (h : FCert U C ρ A) : Cert U C ρ A :=
  ⟨h.fin, h.goal, h.full, fun g hg => (h.why g hg).imp
    (fun ⟨d, hd⟩ => final_completes hL hP hU hE d g (h.ok g hg) hd) id⟩

/-- The goals whose images are the goals `C`. -/
def cmap (b t : Bool) (C : GoalOf R Rel → Prop) : GoalOf R Rel → Prop :=
  fun g' => Normal g'.node ∧ C (gmap b t g')

/-- The images of the answers `A`. -/
noncomputable def amaps (P' : Program) (b t : Bool) (A : GoalOf R Rel → List (Ans D P)) :
    GoalOf R Rel → List (Ans D P') :=
  fun g' => (A (gmap b t g')).filterMap (amap P' b g')

/-- **The image of a certificate is a certificate.** -/
theorem FCert.map (hM : Mirror D P P' b t U U') (h : FCert U C ρ A) :
    FCert U' (cmap b t C) (fun g' => ρ (gmap b t g')) (amaps P' b t A) := by
  have hL := hM.twin.law
  have hL' := hM.twin.law'
  -- the image of an answer of the certificate
  have img : ∀ g', cmap b t C g' → ∀ a ∈ A (gmap b t g'),
      ∃ a' ∈ amaps P' b t A g', a'.goal = toGoal g' ∧ a'.span = smap b a.span := by
    intro g' hg' a ha
    obtain ⟨a', e, h1, h2⟩ := hM.amap_some hg'.1 (h.goal _ hg'.2 a ha)
    exact ⟨a', List.mem_filterMap.2 ⟨a, ha, e⟩, h1, h2⟩
  have pre : ∀ g', ∀ a' ∈ amaps P' b t A g',
      ∃ a ∈ A (gmap b t g'), a'.goal = toGoal g' ∧ a'.span = smap b a.span := by
    intro g' a' ha'
    obtain ⟨a, ha, e⟩ := List.mem_filterMap.1 ha'
    exact ⟨a, ha, amap_spec e⟩
  have back : ∀ x, C x → cmap b t C (gmap b t x) ∧ gmap b t (gmap b t x) = x := fun x hx =>
    have e := gmap_gmap (b := b) (t := t) (h.ok x hx).normal
    ⟨⟨normal_nmap b t _, by rw [e]; exact hx⟩, e⟩
  -- the maximal answers of the image
  have maxi : ∀ g', cmap b t C g' → ∀ x' ∈ (amaps P' b t A g').maximaBy (covB D P'),
      ∃ x ∈ (A (gmap b t g')).maximaBy (covB D P), x'.span = smap b x.span := by
    intro g' hg' x' hx'
    obtain ⟨c, hc, -, ec⟩ := pre g' x' (List.mem_maximaBy hx')
    obtain ⟨z, hz, hzc⟩ := Tabled.maxima_of_max hL hc fun y hy hyc => by
      obtain ⟨y', hy', -, ey⟩ := img g' hg' y hy
      have h1 : covB D P' y' x' = true := by
        unfold covB at hyc ⊢
        rw [ey, ec, covers_smap hL]
        exact hyc
      have h2 := maxima_max hx' hy' h1
      unfold covB at h2 ⊢
      rw [ey, ec, covers_smap hL] at h2
      exact h2
    exact ⟨z, hz, by rw [ec, hzc]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨l, hl⟩ := h.fin
    refine ⟨l.map (gmap b t), fun g' hg' => ?_⟩
    exact List.mem_map.2 ⟨_, hl _ hg'.2, gmap_gmap hg'.1⟩
  · intro g' _ a' ha'
    obtain ⟨a, -, e, -⟩ := pre g' a' ha'
    exact e
  · intro g' hg' y' hy'
    have hv : Valid D P (toGoal (gmap b t g')) (smap b y'.span) :=
      hM.symm.valid hg'.1 (hy' ▸ y'.valid)
    obtain ⟨f, hf, hfy⟩ := h.full _ hg'.2 ⟨_, _, hv⟩ rfl
    obtain ⟨f', hf', -, ef⟩ := img g' hg' f hf
    refine ⟨f', hf', ?_⟩
    unfold covB at hfy ⊢
    rw [← covers_smap hL b, smap_smap hL] at hfy
    rw [ef]
    exact hfy
  · intro g' hg'
    have := (h.ok _ hg'.2).gmap b t
    rwa [gmap_gmap hg'.1] at this
  · intro g' hg'
    obtain ⟨hn, hc⟩ := hg'
    have hok := h.ok _ hc
    have hgg : gmap b t (gmap b t g') = g' := gmap_gmap hn
    have hnn : nmap b t (gmap b t g').node = g'.node := hn.nmap_nmap b t
    rcases h.why _ hc with ⟨d, hd⟩ | hw
    · left
      have := hM.twin.link.verdict d _ hok
      rw [hgg] at this
      exact ⟨d, this.trans hd⟩
    right
    cases hw with
    | span hs =>
      obtain ⟨s, hs⟩ := hs
      have e : g'.node = nmap b t (.span s) := by
        rw [← hs]
        exact hnn.symm
      exact .span ⟨_, e.trans (nmap_span b t s)⟩
    | copy c h1 h2 hs =>
      have hbody : Charged.bodyOf P' g'.node =
          (Charged.bodyOf P (gmap b t g').node).map (nmap b t) := by
        have := hM.twin.link.body _ hok.normal
        rwa [hnn] at this
      refine .copy c (fun hc1 => ?_) (fun hc0 => ?_) fun x' hx' => ?_
      · obtain ⟨bd, hbd⟩ := h1 hc1
        exact ⟨nmap b t bd, by rw [hbody, hbd]; rfl⟩
      · obtain ⟨xs, hxs⟩ := h2 hc0
        have := hok.normal.view_union_nmap hxs b t
        rw [hnn] at this
        exact ⟨_, this⟩
      · have key : Normal x' ∧ nmap b t x' ∈ copyMembers P (gmap b t g').node c := by
          cases c with
          | true =>
            have hx'' : x' ∈ (Charged.bodyOf P' g'.node).toList := hx'
            rw [hbody] at hx''
            cases hbd : Charged.bodyOf P (gmap b t g').node with
            | none => rw [hbd] at hx''; cases hx''
            | some bd =>
              rw [hbd] at hx''
              obtain rfl : x' = nmap b t bd := by simpa using hx''
              have hbn : Normal bd := by
                revert hbd
                cases (gmap b t g').node with
                | call n =>
                  intro hbd
                  obtain rfl : (P.body n).norm = bd := by simpa [Charged.bodyOf] using hbd
                  exact normal_norm _
                | conv y =>
                  cases y with
                  | call n =>
                    intro hbd
                    obtain rfl : (P.body n).normConv = bd := by
                      simpa [Charged.bodyOf] using hbd
                    exact normal_normConv _
                  | _ => intro hbd; simp [Charged.bodyOf] at hbd
                | _ => intro hbd; simp [Charged.bodyOf] at hbd
              refine ⟨normal_nmap b t _, ?_⟩
              show nmap b t (nmap b t bd) ∈ (Charged.bodyOf P (gmap b t g').node).toList
              rw [hbn.nmap_nmap, hbd]
              simp
          | false =>
            have hx'' : x' ∈ g'.node.unionParts := hx'
            obtain ⟨xs, hxs⟩ := h2 rfl
            have hv' := hok.normal.view_union_nmap hxs b t
            rw [hnn] at hv'
            rw [← hn.view_union_eq hv'] at hx''
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (mem_sortedBranches.1 hx'').1
            have hxn := ((hok.normal.view_union hxs).1 x hx).1
            refine ⟨normal_nmap b t _, ?_⟩
            show nmap b t (nmap b t x) ∈ (gmap b t g').node.unionParts
            rw [hxn.nmap_nmap, ← hok.normal.view_union_eq hxs]
            exact hx
        obtain ⟨hC, hρ⟩ := hs _ key.2
        have e : gmap b t (⟨g'.lb, x', g'.rb⟩ : GoalOf R Rel) =
            ⟨(gmap b t g').lb, nmap b t x', (gmap b t g').rb⟩ := by cases b <;> rfl
        exact ⟨⟨key.1, by rw [e]; exact hC⟩, by rw [e]; exact hρ⟩
    | join k L Rg hsp hl hr =>
      obtain ⟨sw, -, hsp'⟩ := splitAt_gmap hok b t hsp
      rw [hgg] at hsp'
      have bl := back L hl.1
      have br := back Rg hr.1
      cases sw
      · simp only [Bool.false_eq_true, ↓reduceIte] at hsp'
        exact .join k _ _ hsp' ⟨bl.1, by rw [bl.2]; exact hl.2⟩ ⟨br.1, by rw [br.2]; exact hr.2⟩
      · simp only [↓reduceIte] at hsp'
        exact .join k _ _ hsp' ⟨br.1, by rw [br.2]; exact hr.2⟩ ⟨bl.1, by rw [bl.2]; exact hl.2⟩
    | push k L Rg left hsp hside hsub =>
      obtain ⟨sw, hsw, hsp'⟩ := splitAt_gmap hok b t hsp
      rw [hgg] at hsp'
      have bs := back _ hside.1
      have eside : (if (left ^^ sw) = true
          then (if sw = true then gmap b t Rg else gmap b t L)
          else (if sw = true then gmap b t L else gmap b t Rg)) =
          gmap b t (if left = true then L else Rg) := by cases left <;> cases sw <;> rfl
      have eother : (if (left ^^ sw) = true
          then (if sw = true then gmap b t L else gmap b t Rg).node
          else (if sw = true then gmap b t Rg else gmap b t L).node) =
          nmap b t (if left = true then Rg.node else L.node) := by
        cases left <;> cases sw <;> rfl
      refine .push k _ _ (left ^^ sw) hsp' ?_ fun x' hx' => ?_
      · rw [eside]
        exact ⟨bs.1, by rw [bs.2]; exact hside.2⟩
      · rw [eside] at hx'
        obtain ⟨x, hx, ex⟩ := maxi _ bs.1 x' hx'
        rw [bs.2] at hx
        obtain ⟨hC, hρ⟩ := hsub x hx
        have e := pushG_gmap (P' := P') (t := t) hL (gmap b t g')
          (if left = true then Rg.node else L.node) k left sw hsw ex
        rw [hgg] at e
        have bp := back _ hC
        rw [eother, e]
        exact ⟨bp.1, by rw [bp.2]; exact hρ⟩
    | check L Rg hsp left ps hreads hall =>
      obtain ⟨sw, hsw, hsp'⟩ := splitAt_gmap hok b t hsp
      obtain rfl := hsw rfl
      rw [hgg] at hsp'
      have hside : Normal (if left = true then L.node else Rg.node) := by
        obtain ⟨xs, i, l, r, -, -, -, hl, hr, rfl, rfl⟩ := hsp
        cases left
        · exact hok.normal.interval hr
        · exact hok.normal.interval hl
      obtain ⟨ps', hreads', hsub⟩ := hM.reads _ left ps hside hreads
      have eside : (if (left ^^ sw) = true
          then (if sw = true then gmap sw t Rg else gmap sw t L).node
          else (if sw = true then gmap sw t L else gmap sw t Rg).node) =
          nmap sw t (if left = true then L.node else Rg.node) := by
        cases left <;> cases sw <;> rfl
      refine .check _ _ hsp' (left ^^ sw) ps' (by rw [eside]; exact hreads') fun p hp => ?_
      obtain ⟨hC, hρ, hA⟩ := hall p (hsub p hp)
      have bp := back _ hC
      have egoal : (if (left ^^ sw) = true
          then (⟨some p, if (left ^^ sw) = true
              then (if sw = true then gmap sw t L else gmap sw t Rg).node
              else (if sw = true then gmap sw t Rg else gmap sw t L).node, g'.rb⟩ : GoalOf R Rel)
          else ⟨g'.lb, if (left ^^ sw) = true
              then (if sw = true then gmap sw t L else gmap sw t Rg).node
              else (if sw = true then gmap sw t Rg else gmap sw t L).node, some p⟩) =
          gmap sw t (if left = true
            then (⟨some p, if left = true then Rg.node else L.node, (gmap sw t g').rb⟩ :
              GoalOf R Rel)
            else ⟨(gmap sw t g').lb, if left = true then Rg.node else L.node, some p⟩) := by
        rw [← hgg]
        cases left <;> cases sw <;> simp [gmap, hn.nmap_nmap]
      rw [egoal]
      refine ⟨bp.1, by rw [bp.2]; exact hρ, ?_⟩
      show (A (gmap sw t (gmap sw t _))).filterMap _ = []
      rw [bp.2, hA]
      rfl

end Symmetric

end RwLog
