/-
# Reading an edge from the far end

`faces` reads the interfaces the answers of a node show at one end from the
other end of the node, carrying interfaces only (`Machine.lean`). Here: it is
right about the program (`readFaces_sound`) and it does not give up for ever
(`readFaces_some`), so the reading that runs it side by side with the runs of
the first rung is a reading the machine can be given (`good_bothReader`).

What `faces` is given is what the part of a chain beyond the node shows:
`FacesOk C T` says that every pair of every relation of `T` has its near end
in one of the interfaces `C`. What it returns is that of the node followed
by that part (`faces_ok`).
-/
import RwLog.Rungs.Symmetric.ReadLive
import RwLog.Rungs.Framework.Race

namespace RwLog

namespace Symmetric

open Traverse Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## What interfaces say of a set of relations -/

/-- Every pair of every relation of the set has its right end (`last`) or
its left end in one of the interfaces. Nothing is the interface that
restricts nothing. -/
def FacesOk (M : Interp) (last : Bool) (C : List (Option R)) (T : Set GRel) : Prop :=
  ∀ G ∈ T, ∀ x z, (x, z) ∈ G.at M → ∃ p ∈ C, (if last then (z, z) else (x, x)) ∈ bdenAt M p

omit [DecidableEq R] in
theorem FacesOk.mono {M : Interp} {last : Bool} {C C' : List (Option R)} {T : Set GRel}
    (h : FacesOk M last C T) (hs : C ⊆ C') : FacesOk M last C' T := fun G hG x z hx => by
  obtain ⟨p, hp, h'⟩ := h G hG x z hx
  exact ⟨p, hs hp, h'⟩

omit [DecidableEq R] in
/-- The interface that restricts nothing is right about everything. -/
theorem FacesOk.top (M : Interp) (last : Bool) (T : Set GRel) :
    FacesOk M last ([none] : List (Option R)) T := fun G _ x z _ =>
  ⟨none, List.mem_singleton_self _, by cases last <;> rfl⟩

/-- A relation of a node followed by what is beyond it, and a pair of it. -/
theorem stepSet_elim {M : Interp} {last : Bool} {X T : Set GRel} {G : GRel}
    (hG : G ∈ stepSet last X T) {x z : GTerm} (hx : (x, z) ∈ G.at M) :
    ∃ A ∈ X, ∃ B ∈ T, G ∈ stepSet last {A} T ∧ ∃ m,
      if last then (x, m) ∈ B.at M ∧ (m, z) ∈ A.at M else (x, m) ∈ A.at M ∧ (m, z) ∈ B.at M := by
  cases last
  · obtain ⟨A, hA, B, hB, rfl⟩ := hG
    rw [at_comp] at hx
    obtain ⟨m, h1, h2⟩ := hx
    exact ⟨A, hA, B, hB, ⟨A, rfl, B, hB, rfl⟩, m, h1, h2⟩
  · obtain ⟨B, hB, A, hA, rfl⟩ := hG
    rw [at_comp] at hx
    obtain ⟨m, h1, h2⟩ := hx
    exact ⟨A, hA, B, hB, ⟨B, hB, A, rfl, rfl⟩, m, h1, h2⟩

theorem stepSet_mono {last : Bool} {X X' : Set GRel} (h : X ⊆ X') (T : Set GRel) :
    stepSet last X T ⊆ stepSet last X' T := by
  cases last
  · exact Set.image2_subset_right h
  · exact Set.image2_subset_left h

theorem stepSet_empty (last : Bool) (T : Set GRel) : stepSet last ∅ T = ∅ := by
  cases last
  · exact Set.image2_empty_left
  · exact Set.image2_empty_right

theorem stepSet_id (last : Bool) (X : Set GRel) : stepSet last X {GRel.id} = X := by
  cases last
  · exact image2_comp_id X
  · exact image2_id_comp X

/-- The members of a chain taken from the far end, each put before (after)
what was beyond it, are the chain put before (after) it. -/
theorem stepSet_fold (last : Bool) (f : Rel → Set GRel) (xs : List Rel) (T : Set GRel) :
    (if last then xs else xs.reverse).foldl (fun T x => stepSet last (f x) T) T =
      stepSet last (seqAll (xs.map f)) T := by
  cases last
  · simp only [Bool.false_eq_true, ite_false, List.foldl_reverse]
    induction xs with
    | nil => exact (image2_id_comp T).symm
    | cons x xs ih =>
      simp only [List.foldr_cons, List.map_cons]
      rw [ih]
      exact (image2_comp_assoc _ _ _).symm
  · simp only [ite_true]
    induction xs generalizing T with
    | nil => exact (image2_comp_id T).symm
    | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih]
      exact image2_comp_assoc _ _ _

omit [DecidableEq R] in
/-- **The interfaces of a span followed by something**: the span composed
with each interface of what follows, read at the edge. -/
theorem FacesOk.span {M : Interp} (hL : D.Lawful M) {last : Bool} {s : R}
    {C C' : List (Option R)} {T : Set GRel} {A : GRel}
    (hden : ∀ x z, (x, z) ∈ A.at M → (x, z) ∈ den M s) (h : FacesOk M last C T)
    (hn : none ∈ C → (if last then D.rightBound s else D.leftBound s) ∈ C')
    (hs : ∀ q, some q ∈ C → ∀ c, (if last then D.compose q s else D.compose s q) = some c →
      (if last then D.rightBound c else D.leftBound c) ∈ C') :
    FacesOk M last C' (stepSet last {A} T) := by
  intro G hG x z hx
  obtain ⟨A', hA', B, hB, -, m, hm⟩ := stepSet_elim hG hx
  obtain rfl := Set.mem_singleton_iff.1 hA'
  cases last
  · simp only [Bool.false_eq_true, ite_false] at hm hn hs ⊢
    obtain ⟨h1, h2⟩ := hm
    obtain ⟨p, hp, hpm⟩ := h B hB m z h2
    simp only [Bool.false_eq_true, ite_false] at hpm
    cases p with
    | none => exact ⟨_, hn hp, leftBound_at hL (hden _ _ h1)⟩
    | some q =>
      have hq : (m, m) ∈ den M q := hpm
      cases hc : D.compose s q with
      | none =>
        have := hL.compose_none s q hc
        exact absurd (show (x, m) ∈ (den M s).comp (den M q) from ⟨m, hden _ _ h1, hq⟩)
          (by rw [this]; exact fun h => h)
      | some c =>
        have hd := hL.compose_some s q c hc
        exact ⟨_, hs q hp c hc, leftBound_at hL (y := m) (by rw [hd]; exact ⟨m, hden _ _ h1, hq⟩)⟩
  · simp only [ite_true] at hm hn hs ⊢
    obtain ⟨h1, h2⟩ := hm
    obtain ⟨p, hp, hpm⟩ := h B hB x m h1
    simp only [ite_true] at hpm
    cases p with
    | none => exact ⟨_, hn hp, rightBound_at hL (hden _ _ h2)⟩
    | some q =>
      have hq : (m, m) ∈ den M q := hpm
      cases hc : D.compose q s with
      | none =>
        have := hL.compose_none q s hc
        exact absurd (show (m, z) ∈ (den M q).comp (den M s) from ⟨m, hq, hden _ _ h2⟩)
          (by rw [this]; exact fun h => h)
      | some c =>
        have hd := hL.compose_some q s c hc
        exact ⟨_, hs q hp c hc, rightBound_at hL (x := m) (by rw [hd]; exact ⟨m, hq, hden _ _ h2⟩)⟩

/-! ## The interfaces of a list -/

omit [Answer R] [DecidableEq R] in
theorem allFaces_spec : ∀ (C : List (Option R)) (ps : List R), allFaces C = some ps →
    (∀ p ∈ C, ∃ q ∈ ps, p = some q) ∧ ∀ q ∈ ps, some q ∈ C
  | [], ps, h => by
    simp only [allFaces, Option.some.injEq] at h
    subst h
    exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  | none :: C, ps, h => by cases h
  | some p :: C, ps, h => by
    simp only [allFaces, Option.map_eq_some_iff] at h
    obtain ⟨qs, hqs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := allFaces_spec C qs hqs
    refine ⟨fun r hr => ?_, fun q hq => ?_⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨p, List.mem_cons_self, rfl⟩
      · obtain ⟨q, hq, e⟩ := h1 r hr
        exact ⟨q, List.mem_cons_of_mem _ hq, e⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h2 q hq)

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-! ## The steps of the reading -/

theorem addFace_spec (acc : List (Option R)) (p : Option R) :
    acc ⊆ (addFace (K := DerivationKernel.over D K hK P) acc p).val ∧
      p ∈ (addFace (K := DerivationKernel.over D K hK P) acc p).val ∧
      ∀ q ∈ (addFace (K := DerivationKernel.over D K hK P) acc p).val, q ∈ acc ∨ q = p := by
  have hsb := fun a b => Goals.sameBound_val (P := P) K hK a b
  at_cost K hK
  simp only [addFace, Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val]
  split
  · next hb =>
    refine ⟨fun _ h => h, ?_, fun q hq => .inl hq⟩
    obtain ⟨q, hq, hqr⟩ := List.any_eq_true.1 hb
    rw [hsb] at hqr
    exact (of_decide_eq_true hqr) ▸ hq
  · exact ⟨List.subset_append_left _ _, by simp, fun q hq => by simpa using hq⟩

/-- Adding interfaces one by one keeps what holds of each. -/
theorem addFaces_all (Q : Option R → Prop) (acc r : List (Option R)) (ha : ∀ q ∈ acc, Q q)
    (hr : ∀ q ∈ r, Q q) :
    ∀ q ∈ (foldL (addFace (K := DerivationKernel.over D K hK P)) acc r).val, Q q := by
  refine foldL_inv (fun b : List (Option R) => ∀ q ∈ b, Q q) _ _ (fun b x hx hb q hq => ?_) _ ha
  rcases (addFace_spec (K := K) (hK := hK) (P := P) b x).2.2 q hq with h | rfl
  · exact hb q h
  · exact hr _ hx

theorem spanFaces_spec (last : Bool) (s : R) (C : List (Option R)) :
    (none ∈ C → (if last then D.rightBound s else D.leftBound s) ∈
        (spanFaces (K := DerivationKernel.over D K hK P) last s C).val) ∧
      ∀ q, some q ∈ C → ∀ c, (if last then D.compose q s else D.compose s q) = some c →
        (if last then D.rightBound c else D.leftBound c) ∈
          (spanFaces (K := DerivationKernel.over D K hK P) last s C).val := by
  have hadd := fun acc p => addFace_spec (K := K) (hK := hK) (P := P) acc p
  at_cost K hK
  simp only [spanFaces, foldL_std, Cost.foldL_val]
  refine ⟨fun hn => ?_, fun q hq c hc => ?_⟩
  · refine (foldl_grow _ (fun acc p => ?_) C []).2 none hn _ fun acc' => ?_
    · cases p <;> cases last <;>
        simp only [Cost.bind_val, Cost.pure_val, Bool.false_eq_true, ite_false, ite_true] <;>
        first
        | exact (hadd _ _).1
        | (split <;> first | exact fun _ h => h | exact (hadd _ _).1)
    · cases last
      · simp only [Cost.bind_val, Cost.pure_val, Bool.false_eq_true, ite_false]
        rw [hK.leftBound s]
        exact (hadd _ _).2.1
      · simp only [Cost.bind_val, Cost.pure_val, ite_true]
        rw [hK.rightBound s]
        exact (hadd _ _).2.1
  · refine (foldl_grow _ (fun acc p => ?_) C []).2 (some q) hq _ fun acc' => ?_
    · cases p <;> cases last <;>
        simp only [Cost.bind_val, Cost.pure_val, Bool.false_eq_true, ite_false, ite_true] <;>
        first
        | exact (hadd _ _).1
        | (split <;> first | exact fun _ h => h | exact (hadd _ _).1)
    · cases last
      · simp only [Cost.bind_val, Bool.false_eq_true, ite_false] at hc ⊢
        rw [hK.compose, hc]
        simp only [Cost.bind_val]
        rw [hK.leftBound c]
        exact (hadd _ _).2.1
      · simp only [Cost.bind_val, ite_true] at hc ⊢
        rw [hK.compose, hc]
        simp only [Cost.bind_val]
        rw [hK.rightBound c]
        exact (hadd _ _).2.1

theorem addFace_all (Q : Option R → Prop) (acc : List (Option R)) (p : Option R)
    (ha : ∀ q ∈ acc, Q q) (hp : Q p) :
    ∀ q ∈ (addFace (K := DerivationKernel.over D K hK P) acc p).val, Q q := fun q hq => by
  rcases (addFace_spec (K := K) (hK := hK) (P := P) acc p).2.2 q hq with h | rfl
  · exact ha q h
  · exact hp

/-- The interfaces of a span followed by something are boundaries. -/
theorem spanFaces_bound {M : Interp} (hL : D.Lawful M) (last : Bool) (s : R)
    (C : List (Option R)) :
    ∀ q ∈ (spanFaces (K := DerivationKernel.over D K hK P) last s C).val, IsBound D q := by
  have hadd := fun acc p => addFace_all (K := K) (hK := hK) (P := P) (IsBound D) acc p
  at_cost K hK
  simp only [spanFaces]
  refine foldL_inv (fun b : List (Option R) => ∀ q ∈ b, IsBound D q) _ _ (fun b p _ hb => ?_) _
    (fun _ h => (by cases h))
  cases p <;> cases last <;>
    simp only [Cost.bind_val, Cost.pure_val, Bool.false_eq_true, ite_false, ite_true] <;>
    first
    | exact hadd _ _ hb (by rw [hK.leftBound]; exact isBound_left hL _)
    | exact hadd _ _ hb (by rw [hK.rightBound]; exact isBound_right hL _)
    | (split <;> first
        | exact hb
        | exact hadd _ _ hb (by rw [hK.leftBound]; exact isBound_left hL _)
        | exact hadd _ _ hb (by rw [hK.rightBound]; exact isBound_right hL _))

/-! ## The reading is right about the program -/

/-- What is read is boundaries, if what it was given is. -/
theorem faces_bound {M : Interp} (hL : D.Lawful M) (last : Bool) :
    ∀ (d : Nat) (seen : List Rel) (n : Rel) (C C' : List (Option R)),
      (faces (K := DerivationKernel.over D K hK P) last d seen n C).val = some C' →
      (∀ p ∈ C, IsBound D p) → ∀ p ∈ C', IsBound D p := by
  have hspan := fun s C => spanFaces_bound (K := K) (hK := hK) (P := P) hL last s C
  have hall := fun acc r => addFaces_all (K := K) (hK := hK) (P := P) (IsBound D) acc r
  have htop : ∀ p ∈ ([none] : List (Option R)), IsBound D p := fun p hp => by
    obtain rfl := List.mem_singleton.1 hp
    exact isBound_none D
  at_cost K hK
  intro d
  induction d with
  | zero =>
    intro seen n C C' h
    simp only [faces, Cost.pure_val] at h
    cases h
  | succ d ih =>
    intro seen n C C' h hC
    simp only [faces, Cost.bind_val] at h
    split at h
    · simp only [Cost.bind_val] at h
      split at h
      · simp only [Cost.pure_val, Option.some.injEq] at h
        subst h
        exact fun _ h => (by cases h)
      · simp only [Cost.bind_val, Cost.pure_val, Option.some.injEq] at h
        subst h
        exact hspan _ _
    · simp only [Cost.pure_val, Option.some.injEq] at h
      subst h
      exact htop
    · next xs hv =>
      simp only [foldL_std, Cost.foldL_val] at h
      have key := foldl_option_inv _ (fun (_ : List Rel) (b : List (Option R)) =>
        ∀ p ∈ b, IsBound D p) xs ?_ ?_ xs (fun _ h => h) [] _ C' h
      · obtain ⟨b0, hb0, hI⟩ := key
        cases hb0
        exact hI (fun _ h => (by cases h))
      · exact fun x => rfl
      · intro done b x b' _ hg hI
        simp only [Cost.bind_val] at hg
        split at hg
        · cases hg
        · next r hr =>
          simp only [Cost.bind_val, Cost.pure_val, Option.some.injEq] at hg
          subst hg
          have h' := hall b r hI (ih seen x C r hr hC)
          rwa [foldL_std] at h'
    · simp only [Cost.bind_val, anyL_std] at h
      split at h
      · simp only [Cost.pure_val, Option.some.injEq] at h
        subst h
        exact htop
      · simp only [Cost.bind_val] at h
        split at h
        · simp only [Cost.pure_val, Option.some.injEq] at h
          subst h
          exact fun _ h => (by cases h)
        · exact ih _ _ C C' h hC
    · split at h
      · simp only [Cost.pure_val, Option.some.injEq] at h
        subst h
        exact htop
      · simp only [foldL_std, Cost.foldL_val] at h
        have key := foldl_option_inv _ (fun (_ : List Rel) (b : List (Option R)) =>
          ∀ p ∈ b, IsBound D p) _ ?_ ?_ _ (fun _ h => h) [] _ C' h
        · obtain ⟨b0, hb0, hI⟩ := key
          cases hb0
          exact hI hC
        · exact fun x => rfl
        · intro done b x b' _ hg hI
          exact ih seen x b b' hg hI

/-- **What is read from the far end is right**: if `C` is right about what
is beyond a node of the normal form with first-order spans, what `faces`
returns is right about the node followed by it. -/
theorem faces_ok (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (last : Bool) :
    ∀ (d : Nat) (seen : List Rel) (n : Rel) (C C' : List (Option R)), Normal n → n.FO →
      (faces (K := DerivationKernel.over D K hK P) last d seen n C).val = some C' →
      ∀ (k : Nat) (T : Set GRel), FacesOk P.sorts.interp last C T →
        FacesOk P.sorts.interp last C' (stepSet last (GDn P k n) T) := by
  have hadd := fun acc p => addFace_spec (K := K) (hK := hK) (P := P) acc p
  have hspan := fun s C => spanFaces_spec (K := K) (hK := hK) (P := P) last s C
  have hleaf := fun (s : Span) (c : Ans D P) =>
    Ans.leaf_val (P := P) K hK (lb := none) (rb := none) (n := .span s) (c := c)
  have hleafok := fun (s : Span) (z : R) hz =>
    Ans.leaf_ok (P := P) K hK (s := s) (z := z) (isBound_none D) (isBound_none D) hz
  at_cost K hK
  intro d
  induction d with
  | zero =>
    intro seen n C C' _ _ h
    simp only [faces, Cost.pure_val] at h
    cases h
  | succ d ih =>
    intro seen n C C' hn hfo h k T hT
    simp only [faces, Cost.bind_val] at h
    split at h
    · next hv =>
      obtain ⟨s, rfl⟩ := forget_span hv
      simp only [Cost.bind_val, over_leaf, over_span] at h
      rw [(gdn_laws P k).span]
      split at h
      · next ha =>
        intro G hG x z hx
        obtain ⟨A, hA, B, hB, -, m, hm⟩ := stepSet_elim hG hx
        obtain rfl := Set.mem_singleton_iff.1 hA
        have hne : ∃ u v, (u, v) ∈ GRel.at (Span.den s) P.sorts.interp := by
          cases last
          · exact ⟨_, _, hm.1⟩
          · exact ⟨_, _, hm.2⟩
        obtain ⟨u, v, huv⟩ := hne
        cases hr : D.rep s with
        | some r =>
          obtain ⟨c, hc, -⟩ := hleafok s r (by simp [spanBoth, hr])
          rw [ha] at hc
          cases hc
        | none =>
          have := hL.rep_none s (hfo s (by simp [RelOf.spans])) hr
          rw [← Span.denAt_eq, this] at huv
          exact absurd huv (Set.notMem_empty _)
      · next a ha =>
        simp only [Cost.bind_val, Cost.pure_val, Option.some.injEq] at h
        subst h
        obtain ⟨s1, e, -, -, hsb, -⟩ := (hleaf s a).1 ha
        cases e
        refine FacesOk.span hL (fun x z hx => ?_) hT (hspan _ _).1 (hspan _ _).2
        show (x, z) ∈ den P.sorts.interp a.span
        rw [spanBoth_den hL hsb, wrapAt_none]
        exact hx
    · simp only [Cost.pure_val, Option.some.injEq] at h
      subst h
      exact FacesOk.top _ _ _
    · next xs hv =>
      have hvu := forget_union hv
      have hxs := hn.view_union_eq hvu
      simp only [foldL_std, Cost.foldL_val] at h
      have key := foldl_option_inv _ (fun (done : List Rel) (b : List (Option R)) =>
        ∀ x ∈ done, FacesOk P.sorts.interp last b (stepSet last (GDn P k x) T)) xs ?_ ?_ xs
        (fun _ h => h) [] _ C' h
      · obtain ⟨b0, hb0, hI⟩ := key
        have hall := hI (fun x hx => (by cases hx))
        intro G hG x z hxz
        obtain ⟨A, hA, B, hB, hGA, m, hm⟩ := stepSet_elim hG hxz
        rw [← (gdn_laws P k).gd_unionParts n, ← hxs] at hA
        simp only [Set.mem_iUnion, exists_prop] at hA
        obtain ⟨y, hy, hA⟩ := hA
        exact hall y (by simpa using hy) G
          (stepSet_mono (Set.singleton_subset_iff.2 hA) T hGA) x z hxz
      · exact fun x => rfl
      · intro done b x b' hx hg hI
        simp only [Cost.bind_val] at hg
        split at hg
        · cases hg
        · next r hr =>
          simp only [Cost.bind_val, Cost.pure_val, Cost.foldL_val, Option.some.injEq] at hg
          subst hg
          obtain ⟨h1, h2⟩ := foldl_grow
            (fun acc r => (addFace (K := DerivationKernel.over D _ hK P) acc r).val)
            (fun acc r => (hadd acc r).1) r b
          intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact (hI y hy).mono h1
          · obtain rfl := List.mem_singleton.1 hy
            have hmem : y ∈ n.view.members := by rw [hvu]; exact hx
            exact (ih seen y C r (hn.view_members hmem) (hfo.view_members hmem) hr k T hT).mono
              fun q hq => h2 q hq q fun acc' => (hadd acc' q).2.1
    · next f fl hv =>
      simp only [Cost.bind_val, anyL_std] at h
      split at h
      · simp only [Cost.pure_val, Option.some.injEq] at h
        subst h
        exact FacesOk.top _ _ _
      · simp only [Cost.bind_val, over_body] at h
        split at h
        · next hb =>
          obtain ⟨b, hb'⟩ := forget_call (P := P) hv
          rw [show Charged.bodyOf P n = none from hb] at hb'
          cases hb'
        · next bd hb =>
          have hb' : Charged.bodyOf P n = some bd := hb
          have hbd := ih _ bd C C' (normal_bodyOf hb') (bodyOf_fo hP hb') h
          cases k with
          | zero =>
            intro G hG
            rw [(gdn_bodyOf hb' 0).2, stepSet_empty] at hG
            cases hG
          | succ k =>
            rw [(gdn_bodyOf hb' k).1]
            exact hbd k T hT
    · next xs hv =>
      have hvc := forget_chain hv
      obtain ⟨h2, hmem, hmk⟩ := hn.view_chain hvc
      have hne : xs ≠ [] := by intro e; rw [e] at h2; simp at h2
      have hparts : seqParts n = xs := by
        rw [← hmk]; exact seqParts_mkSeq hne fun x hx => (hmem x hx).2
      split at h
      · simp only [Cost.pure_val, Option.some.injEq] at h
        subst h
        exact FacesOk.top _ _ _
      · simp only [foldL_std, Cost.foldL_val] at h
        have hsub : ∀ y ∈ (if last then xs else xs.reverse), y ∈ xs := by
          intro y hy
          cases last <;> simpa using hy
        have key := foldl_option_inv _ (fun (done : List Rel) (b : List (Option R)) =>
          FacesOk P.sorts.interp last b
            (done.foldl (fun T x => stepSet last (GDn P k x) T) T)) _ ?_ ?_ _
          (fun _ h => h) [] _ C' h
        · obtain ⟨b0, hb0, hI⟩ := key
          cases hb0
          have hfin := hI hT
          rw [List.nil_append, stepSet_fold last (GDn P k) xs T, ← hparts,
            (gdn_laws P k).gd_seqParts n] at hfin
          exact hfin
        · exact fun x => rfl
        · intro done b x b' hx hg hI
          rw [List.foldl_append]
          have hxm : x ∈ n.view.members := by rw [hvc]; exact hsub x hx
          exact ih seen x b b' (hn.view_members hxm) (hfo.view_members hxm) hg k _ hI

/-- **Reading an edge from the far end is right about the program.** -/
theorem readFaces_sound (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) :
    ∀ (last : Bool) (d : Nat) (n : Rel) (ps : List R),
      (readFaces (K := DerivationKernel.over D K hK P) last d n).val = some (some ps) →
        EdgeOk D P n last ps := by
  intro last d n ps h
  have hok := fun C' => faces_ok (K := K) (hK := hK) hL hP last d [] n [none] C'
  have hbd := fun C' => faces_bound (K := K) (hK := hK) (P := P) hL last d [] n [none] C'
  at_cost K hK
  simp only [readFaces, Cost.bind_val, Cost.pure_val, Option.map_eq_some_iff] at h
  obtain ⟨C', hC', hps⟩ := h
  obtain ⟨h1, h2⟩ := allFaces_spec C' ps hps
  refine ⟨fun p hp => ?_, fun hn hfo k G hG x z hx => ?_⟩
  · exact hbd C' hC' (fun q hq => by
      obtain rfl := List.mem_singleton.1 hq
      exact isBound_none D) (some p) (h2 p hp) p rfl
  · have := hok C' hn hfo hC' k {GRel.id} (FacesOk.top _ _ _) G (by rw [stepSet_id]; exact hG)
      x z hx
    obtain ⟨p, hp, hpx⟩ := this
    obtain ⟨q, hq, rfl⟩ := h1 p hp
    exact ⟨q, hq, hpx⟩

/-! ## The reading does not give up for ever -/

/-- **An edge is read from the far end** at any depth past the size of the
node and what the calls still to pass can need. -/
theorem faces_some (last : Bool) : ∀ (d : Nat) (seen : List Rel) (n : Rel) (C : List (Option R)),
    n.size + 1 + underCalls P (rem P seen) ≤ d →
    (faces (K := DerivationKernel.over D K hK P) last d seen n C).val ≠ none := by
  at_cost K hK
  intro d
  induction d with
  | zero => intro seen n C h; omega
  | succ d ih =>
    intro seen n C hd
    have hmem : ∀ x, x ∈ n.view.members → ∀ C',
        (faces (K := DerivationKernel.over D _ hK P) last d seen x C').val ≠ none := fun x hx C' =>
      ih seen x C' (by have := size_view_member_lt hx; omega)
    simp only [faces, Cost.bind_val]
    split
    · simp only [Cost.bind_val]
      split <;> simp
    · simp
    · next xs hv =>
      have hvu := forget_union hv
      refine foldL_inv (fun acc : Option (List (Option R)) => acc ≠ none) _ _
        (fun b x hx hb => ?_) _ (by simp)
      split
      · exact absurd rfl hb
      · simp only [Cost.bind_val]
        have := hmem x (by rw [hvu]; exact hx) C
        split
        · next hr => exact absurd hr this
        · simp
    · next f fl hv =>
      simp only [Cost.bind_val, anyL_std]
      split
      · simp
      · next hseen =>
        simp only [Cost.bind_val, over_body]
        split
        · simp
        · next bd hb =>
          have hb' : Charged.bodyOf P n = some bd := hb
          have hpos := RelOf.size_pos' n
          rcases bodyOf_cases hb' with ⟨hn, hbd⟩ | rfl
          · have hns : n ∉ seen := by
              intro hin
              apply hseen
              simp only [Cost.anyL_val, List.any_eq_true]
              exact ⟨n, hin, by simp [over_eqNode, Charged.eqNode, Charged.op]⟩
            have := underCalls_step (P := P) (rem_cons_lt hn hns)
            exact ih (n :: seen) bd C (by omega)
          · cases d with
            | zero => unfold underCalls at hd; omega
            | succ d =>
              simp [faces, Cost.bind_val, over_view, Charged.viewNode, Charged.op, RelOf.view,
                NodeView.forget, foldL_std, Cost.foldL_val]
    · next xs hv =>
      have hvc := forget_chain hv
      split
      · simp
      · have hsub : ∀ y ∈ (if last then xs else xs.reverse), y ∈ n.view.members := by
          intro y hy
          rw [hvc]
          cases last <;> simpa [NodeView.members] using hy
        refine foldL_inv (fun acc : Option (List (Option R)) => acc ≠ none) _ _
          (fun b x hx hb => ?_) _ (by simp)
        split
        · exact absurd rfl hb
        · exact hmem x (hsub x hx) _

theorem readFaces_some (last : Bool) (d : Nat) (n : Rel) (hd : readNeed P n ≤ d) :
    (readFaces (K := DerivationKernel.over D K hK P) last d n).val ≠ none := by
  have h2 := faces_some (K := K) (hK := hK) (P := P) last d [] n [none] hd
  at_cost K hK
  simp only [readFaces, Cost.bind_val, Cost.pure_val, ne_eq, Option.map_eq_none_iff]
  exact h2

/-! ## Both ways side by side -/

/-- **The reading that reads both ways is right about the program and does
not give up for ever**: it returns what one of the two returns. -/
theorem readBoth_ok (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) :
    ReadOk D P K hK @bothReader := by
  have hs1 := readRuns_sound (K := K) (hK := hK) hL hP
  have hs2 := readFaces_sound (K := K) (hK := hK) hL hP
  have hl1 := fun last d n hd => readRuns_some (K := K) (hK := hK) (P := P) last d n hd
  have hl2 := fun last d n hd => readFaces_some (K := K) (hK := hK) (P := P) last d n hd
  have hval : ∀ (last : Bool) (d : Nat) (n : Rel),
      ((DerivationKernel.over D K hK P).race
          (readRuns (K := DerivationKernel.over D K hK P) last d n)
          (readFaces (K := DerivationKernel.over D K hK P) last d n)).val =
        (readRuns (K := DerivationKernel.over D K hK P) last d n).val ∨
      ((DerivationKernel.over D K hK P).race
          (readRuns (K := DerivationKernel.over D K hK P) last d n)
          (readFaces (K := DerivationKernel.over D K hK P) last d n)).val =
        (readFaces (K := DerivationKernel.over D K hK P) last d n).val := by
    intro last d n
    at_cost K hK
    exact Cost.race_val _ _
  refine ⟨offered_sound fun last d n ps h => ?_, fun last d n hd => offered_some
    (fun last d n hd => ?_) last d n hd⟩
  · rcases hval last d n with e | e
    · exact hs1 last d n ps (e ▸ h)
    · exact hs2 last d n ps (e ▸ h)
  · rcases hval last d n with e | e
    · rw [e]; exact hl1 last d n hd
    · rw [e]; exact hl2 last d n hd

end kernel

/-- The reading that reads both ways is good. -/
theorem good_bothReader : GoodReader @bothReader := fun _ _ hL hP => readBoth_ok hL hP

end Symmetric

end RwLog
