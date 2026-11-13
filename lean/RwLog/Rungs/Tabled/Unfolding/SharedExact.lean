/-
# The shared evaluation holds exactly the products of the unfolding

When interfaces are exact (`Domain.ExactIface`), what the summary of a node
holds (`SemS`: the pairs of its answers, the terms each interface of an open
product lets through) is what a left-to-right walk holds of the products of
the unfolding (`evalS_ex`), whatever the memo held, as long as the memo was
right (`MemoEx`).

So the race answered with shared work says the unfolding is final exactly
when the model has no open product (`sharedRace_final`): the same verdict as
the whole unfolding and as the walks.

Where a walk follows each product of the first members of a chain by the
next member, the shared evaluation follows each product of the first member
by the summary of all the rest; the two are the same products because
sequencing sets of products is associative (`wsuf_cons`).
-/
import RwLog.Rungs.Tabled.Unfolding.Shared
import RwLog.Rungs.Tabled.Unfolding.WalkExact

namespace RwLog

namespace Tabled

namespace Unfold

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## What a summary holds -/

/-- What a summary holds, by what it relates. -/
def SemS (M : Interp) (s : Sm D P) : Set SI :=
  {i | (∃ a ∈ s.closed, i = .closed (den M a.span)) ∨ ∃ o ∈ s.opens, i = .opn (bset M o)}

section sems

variable {M : Interp}

omit [DecidableEq R] in
theorem sems_closed_iff {s : Sm D P} {X : PRel} :
    SI.closed X ∈ SemS M s ↔ ∃ a ∈ s.closed, den M a.span = X := by
  constructor
  · rintro (⟨a, ha, e⟩ | ⟨o, -, e⟩)
    · exact ⟨a, ha, (SI.closed.inj e).symm⟩
    · cases e
  · rintro ⟨a, ha, rfl⟩
    exact .inl ⟨a, ha, rfl⟩

omit [DecidableEq R] in
theorem sems_opn_iff {s : Sm D P} {F : Set GTerm} :
    SI.opn F ∈ SemS M s ↔ ∃ o ∈ s.opens, bset M o = F := by
  constructor
  · rintro (⟨a, -, e⟩ | ⟨o, ho, e⟩)
    · cases e
    · exact ⟨o, ho, (SI.opn.inj e).symm⟩
  · rintro ⟨o, ho, rfl⟩
    exact .inr ⟨o, ho, rfl⟩

variable {s : Sm D P} {W : Set SP}

omit [DecidableEq R] in
theorem sems_ne (h : SemS M s = farD false '' W) :
    (!s.closed.isEmpty || !s.opens.isEmpty) = true ↔ W.Nonempty := by
  constructor
  · intro hne
    have : ∃ i, i ∈ SemS M s := by
      cases hc : s.closed with
      | cons a _ => exact ⟨_, .inl ⟨a, by rw [hc]; simp, rfl⟩⟩
      | nil =>
        cases ho : s.opens with
        | cons o _ => exact ⟨_, .inr ⟨o, by rw [ho]; simp, rfl⟩⟩
        | nil => simp [hc, ho] at hne
    obtain ⟨i, hi⟩ := this
    rw [h] at hi
    obtain ⟨p, hp, -⟩ := hi
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    have hm : farD false p ∈ SemS M s := by
      rw [h]
      exact ⟨p, hp, rfl⟩
    rcases hm with ⟨a, ha, -⟩ | ⟨o, ho, -⟩
    · simp [isEmpty_of_mem ha]
    · simp [isEmpty_of_mem ho]

omit [DecidableEq R] in
theorem sems_opn (h : SemS M s = farD false '' W) : (!s.opens.isEmpty) = true ↔ HasOpn W := by
  constructor
  · intro hne
    cases ho : s.opens with
    | nil => simp [ho] at hne
    | cons o _ =>
      have hm : SI.opn (bset M o) ∈ SemS M s := .inr ⟨o, by rw [ho]; simp, rfl⟩
      rw [h] at hm
      obtain ⟨A, B, hAB, -⟩ := farD_opn_iff.1 hm
      exact ⟨A, B, hAB⟩
  · rintro ⟨A, B, hAB⟩
    have hm : SI.opn (farE false A B) ∈ SemS M s := by
      rw [h]
      exact ⟨_, hAB, rfl⟩
    obtain ⟨o, ho, -⟩ := sems_opn_iff.1 hm
    simp [isEmpty_of_mem ho]

omit [DecidableEq R] in
theorem sems_cl (h : SemS M s = farD false '' W) :
    {X | ∃ a ∈ s.closed, den M a.span = X} = closedPart W := by
  ext X
  show (∃ a ∈ s.closed, den M a.span = X) ↔ SP.closed X ∈ W
  rw [← sems_closed_iff, h, farD_closed_iff]

omit [DecidableEq R] in
/-- A rule that keeps the representative of every answer keeps what the
summary holds. -/
theorem sems_lift {f : Ans D P → Option (Ans D P)}
    (h₁ : ∀ a c, f a = some c → c.span = a.span) (h₂ : ∀ a ∈ s.closed, ∃ c, f a = some c) :
    SemS M (⟨s.closed.filterMap f, s.opens⟩ : Sm D P) = SemS M s := by
  apply si_ext
  · intro X
    rw [sems_closed_iff, sems_closed_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, ha, e⟩ := List.mem_filterMap.1 hc
      exact ⟨a, ha, by rw [h₁ a c e]⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨c, hc⟩ := h₂ a ha
      exact ⟨c, List.mem_filterMap.2 ⟨a, ha, hc⟩, by rw [h₁ a c hc]⟩
  · intro F
    rw [sems_opn_iff, sems_opn_iff]

omit [DecidableEq R] in
/-- What a summary holds after a fold that added the products of each member
of a list: what it held, and what each member's products hold. -/
theorem fold_sem {ι : Type} {Q : ι → List (Ans D P) → List (Option R) → Prop} {L : List ι}
    {init r : Sm D P} (h : FoldOk Q L init r) (T : ι → Set SI)
    (hQ : ∀ x cs os, Q x cs os → SemS M (⟨cs, os⟩ : Sm D P) = T x) :
    SemS M r = SemS M init ∪ {i | ∃ x ∈ L, i ∈ T x} := by
  apply si_ext
  · intro X
    constructor
    · intro hX
      obtain ⟨b, hb, rfl⟩ := sems_closed_iff.1 hX
      rcases h.from_c b hb with h' | ⟨x, hx, cs, os, q, hb'⟩
      · exact .inl (.inl ⟨b, h', rfl⟩)
      · refine .inr ⟨x, hx, ?_⟩
        rw [← hQ x cs os q]
        exact .inl ⟨b, hb', rfl⟩
    · rintro (hX | ⟨x, hx, hX⟩)
      · obtain ⟨a, ha, rfl⟩ := sems_closed_iff.1 hX
        obtain ⟨b, hb, e⟩ := h.keep_c a ha
        exact sems_closed_iff.2 ⟨b, hb, by rw [e]⟩
      · obtain ⟨cs, os, q, hcs, -⟩ := h.into x hx
        rw [← hQ x cs os q] at hX
        obtain ⟨a, ha, rfl⟩ := sems_closed_iff.1 hX
        obtain ⟨b, hb, e⟩ := hcs a ha
        exact sems_closed_iff.2 ⟨b, hb, by rw [e]⟩
  · intro F
    constructor
    · intro hF
      obtain ⟨o, ho, rfl⟩ := sems_opn_iff.1 hF
      rcases h.from_o o ho with h' | ⟨x, hx, cs, os, q, ho'⟩
      · exact .inl (.inr ⟨o, h', rfl⟩)
      · refine .inr ⟨x, hx, ?_⟩
        rw [← hQ x cs os q]
        exact .inr ⟨o, ho', rfl⟩
    · rintro (hF | ⟨x, hx, hF⟩)
      · obtain ⟨o, ho, rfl⟩ := sems_opn_iff.1 hF
        exact sems_opn_iff.2 ⟨o, h.keep_o o ho, rfl⟩
      · obtain ⟨cs, os, q, -, hos⟩ := h.into x hx
        rw [← hQ x cs os q] at hF
        obtain ⟨o, ho, rfl⟩ := sems_opn_iff.1 hF
        exact sems_opn_iff.2 ⟨o, hos o ho, rfl⟩

end sems

/-! ## The rest of a chain -/

/-- The products of the members `ys` of a chain under a near context. -/
def WSuf (P : Program) (M : Interp) (d : Nat) (c : Near R) (ys : List Rel) (far : Option R) :
    Set SP :=
  if c.pushed then
    pushSet false (bset M c.bound) (chainS (membS (SED P M false d) Set.univ (bset M far) ys))
  else chainS (membS (SED P M false d) (bset M c.bound) (bset M far) ys)

section suf

variable {M : Interp}

theorem membS_ne_nil (S : Set GTerm → Rel → Set GTerm → Set SP) (A B : Set GTerm) :
    ∀ {ys : List Rel}, ys ≠ [] → membS S A B ys ≠ []
  | [], h => absurd rfl h
  | [_], _ => by simp [membS]
  | _ :: _ :: _, _ => by simp [membS]

theorem membS_live {d : Nat} : ∀ (ys : List Rel) {A B : Set GTerm}, A.Nonempty → B.Nonempty →
    ∀ T ∈ membS (SED P M false d) A B ys, ∀ p ∈ T, p.Live
  | [], _, _, _, _ => by simp [membS]
  | [x], _, _, hA, hB => by
    intro T hT
    obtain rfl : T = SED P M false d _ x _ := by simpa [membS] using hT
    exact sed_live d x hA hB
  | x :: y :: zs, _, _, hA, hB => by
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact sed_live d x hA univ_nonempty'
    · exact membS_live (y :: zs) univ_nonempty' hB T hT

omit [DecidableEq R] in
theorem wsuf_one (d : Nat) (c : Near R) (x : Rel) (far : Option R) :
    WSuf P M d c [x] far = WS P M false d c x far := rfl

omit [DecidableEq R] in
/-- The products of a chain: each product of its first member followed by
the products of the rest. -/
theorem wsuf_cons (d : Nat) (c : Near R) (x y : Rel) (zs : List Rel) (far : Option R) :
    WSuf P M d c (x :: y :: zs) far =
      seqSets (WS P M false d c x none)
        (chainS (membS (SED P M false d) Set.univ (bset M far) (y :: zs))) := by
  have hne := membS_ne_nil (SED P M false d) Set.univ (bset M far) (ys := y :: zs) (by simp)
  have e : ∀ A, chainS (membS (SED P M false d) A (bset M far) (x :: y :: zs)) =
      seqSets (SED P M false d A x Set.univ)
        (chainS (membS (SED P M false d) Set.univ (bset M far) (y :: zs))) := by
    intro A
    rw [membS, chainS_eq_chainR, chainR_cons _ hne, ← chainS_eq_chainR]
  unfold WSuf WS
  rw [e, e]
  split
  · exact pushSet_seq false _ _ _
  · rfl

omit [DecidableEq R] in
theorem ws_chain_suf {d : Nat} {c : Near R} {e : Rel} {xs : List Rel} {far : Option R}
    (h : e.view.forget = .chain xs) :
    WS P M false (d + 1) c e far = WSuf P M d c xs far := by
  unfold WS WSuf
  rw [sed_chain h, sed_chain h]
  simp only [Bool.false_eq_true, ite_false, chainD_false]

theorem farD_seqSets (W T : Set SP) :
    farD false '' seqSets W T = {i | ∃ p ∈ W, ∃ q ∈ T, SeqI false (farD false p) q i} := by
  ext i
  constructor
  · rintro ⟨r, ⟨p, hp, q, hq, hs⟩, rfl⟩
    exact ⟨p, hp, q, hq, seqD_far (rev := false) hs⟩
  · rintro ⟨p, hp, q, hq, hs⟩
    obtain ⟨r, hr, rfl⟩ := seqI_lift hs
    exact ⟨r, ⟨p, hp, q, hq, hr⟩, rfl⟩

/-- What a walk holds followed by a set of products: restrict them to what
it pushes, then extend. -/
theorem seq_ext (i₀ : SI) (T : Set SP) :
    {i | ∃ q ∈ T, SeqI false i₀ q i} =
      {i | ∃ j ∈ farD false '' pushSet false (ifaceI false i₀) T, ExtI false i₀ j i} := by
  ext i
  constructor
  · rintro ⟨q, hq, hs⟩
    obtain ⟨q', hpush, hext⟩ := seqI_iff_push_ext.1 hs
    exact ⟨_, ⟨q', ⟨q, hq, hpush⟩, rfl⟩, hext⟩
  · rintro ⟨_, ⟨q', ⟨q, hq, hpush⟩, rfl⟩, hext⟩
    exact ⟨q, hq, seqI_iff_push_ext.2 ⟨q', hpush, hext⟩⟩

end suf

section laws

variable (hL : D.Lawful P.sorts.interp) (hE : D.ExactIface P.sorts.interp)
  (K : Kernel R Cost) (hK : K.Refines D)

local notation "𝕄" => P.sorts.interp

include hL hE in
omit [DecidableEq R] in
theorem wsuf_after_closed (d : Nat) (a : R) (tl : List Rel) (far : Option R) :
    WSuf P 𝕄 d ⟨D.rightBound a, true⟩ tl far =
      pushSet false (ifaceI false (.closed (den 𝕄 a)))
        (chainS (membS (SED P 𝕄 false d) Set.univ (bset 𝕄 far) tl)) := by
  show pushSet false (bset 𝕄 (D.rightBound a)) _ = _
  rw [bset_rightBound hL hE]
  rfl

include hL in
omit [DecidableEq R] in
theorem wsuf_after_open (d : Nat) (o : Option R) {tl : List Rel} {far : Option R}
    (hf : IsBound D far) :
    WSuf P 𝕄 d ⟨o, o.isSome⟩ tl far =
      pushSet false (ifaceI false (.opn (bset 𝕄 o)))
        (chainS (membS (SED P 𝕄 false d) Set.univ (bset 𝕄 far) tl)) := by
  cases o with
  | none =>
    show chainS _ = _
    exact (pushSet_univ false (chainS_live
      (membS_live tl univ_nonempty' (bset_nonempty hL hf)))).symm
  | some b => rfl

include hL in
/-- The joins of an answer with the answers of a summary, and its open
products. -/
theorem ext_closed {a : Ans D P} {l fr : Option R} {n₁ n₂ : Rel} {t : Sm D P}
    (ha : a.goal = ⟨l, n₁, none⟩)
    (ht : ∀ b ∈ t.closed, b.goal = ⟨D.rightBound a.span, n₂, fr⟩) :
    SemS 𝕄 (⟨t.closed.filterMap fun b => (Ans.join D P K hK a b).val, t.opens⟩ : Sm D P) =
      {i | ∃ j ∈ SemS 𝕄 t, ExtI false (.closed (den 𝕄 a.span)) j i} := by
  apply si_ext
  · intro Z
    rw [sems_closed_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hc
      have hd := joinAt_den hL K hK false (a := a) (b := b) e
      refine ⟨.closed (den 𝕄 b.span), .inl ⟨b, hb, rfl⟩, ?_⟩
      rw [hd]
      exact .cc (by rw [← hd]; exact hL.live _)
    · rintro ⟨j, hj, hext⟩
      generalize hi : SI.closed Z = i at hext
      cases hext with
      | cc hne =>
        obtain ⟨b, hb, rfl⟩ := sems_closed_iff.1 hj
        obtain ⟨c, hc, -, -⟩ := joinD hL K hK false (a := a) (b := b) (l := l) (n₁ := n₁)
          (n₂ := n₂) (fr := fr) ha (ht b hb) subset_rfl subset_rfl hne
        refine ⟨c, List.mem_filterMap.2 ⟨b, hb, hc⟩, ?_⟩
        rw [joinAt_den hL K hK false hc]
        exact (SI.closed.inj hi).symm
      | co => cases hi
  · intro F
    rw [sems_opn_iff]
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨_, .inr ⟨o, ho, rfl⟩, .co⟩
    · rintro ⟨j, hj, hext⟩
      generalize hi : SI.opn F = i at hext
      cases hext with
      | cc hne => cases hi
      | co =>
        obtain ⟨o, ho, e⟩ := sems_opn_iff.1 hj
        exact ⟨o, ho, e.trans (SI.opn.inj hi).symm⟩

include hL hE in
omit [DecidableEq R] in
/-- After an open product: the interfaces of the answers of a summary, and
its open products. -/
theorem ext_open (F₀ : Set GTerm) (t : Sm D P) :
    SemS 𝕄 (⟨[], t.closed.map (fun b => D.rightBound b.span) ++ t.opens⟩ : Sm D P) =
      {i | ∃ j ∈ SemS 𝕄 t, ExtI false (.opn F₀) j i} := by
  apply si_ext
  · intro Z
    rw [sems_closed_iff]
    constructor
    · rintro ⟨c, hc, -⟩
      cases hc
    · rintro ⟨j, -, hext⟩
      generalize hi : SI.closed Z = i at hext
      cases hext <;> cases hi
  · intro F
    rw [sems_opn_iff]
    constructor
    · rintro ⟨o, ho, rfl⟩
      rcases List.mem_append.1 ho with h | h
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
        refine ⟨.closed (den 𝕄 b.span), .inl ⟨b, hb, rfl⟩, ?_⟩
        rw [bset_rightBound hL hE]
        exact .oc
      · exact ⟨_, .inr ⟨o, h, rfl⟩, .oo⟩
    · rintro ⟨j, hj, hext⟩
      generalize hi : SI.opn F = i at hext
      cases hext with
      | oc =>
        obtain ⟨b, hb, rfl⟩ := sems_closed_iff.1 hj
        refine ⟨D.rightBound b.span, List.mem_append_left _ (List.mem_map.2 ⟨b, hb, rfl⟩), ?_⟩
        rw [bset_rightBound hL hE]
        exact (SI.opn.inj hi).symm
      | oo =>
        obtain ⟨o, ho, e⟩ := sems_opn_iff.1 hj
        exact ⟨o, List.mem_append_right _ ho, e.trans (SI.opn.inj hi).symm⟩

/-! ## A chain -/

include hL hE in
/-- The first member's summary, each of its products followed by the summary
of the rest. -/
theorem suf_body_ex (Inv : Mm D P → Prop) {c : Near R} {x : Rel} {tl : List Rel} {far : Option R}
    {d : Nat} (hf : IsBound D far) {C₁ O₁ C₂ O₂ : Set GRel} {n₂ : Rel} (s₁ : Sm D P × Mm D P)
    (h₁ : SmOk c.bound x none C₁ O₁ s₁.1)
    (hs₁ : SemS 𝕄 s₁.1 = farD false '' WS P 𝕄 false d c x none) (hm₁ : Inv s₁.2)
    (sv : Near R → Mm D P → Sm D P × Mm D P)
    (hsv : ∀ c' m, Inv m → IsBound D c'.bound →
      (SmOk c'.bound n₂ far C₂ O₂ (sv c' m).1 ∧
        SemS 𝕄 (sv c' m).1 = farD false '' WSuf P 𝕄 d c' tl far) ∧ Inv (sv c' m).2) :
    SemS 𝕄 (sufBodyV K hK sv s₁).1 =
        farD false '' seqSets (WS P 𝕄 false d c x none)
          (chainS (membS (SED P 𝕄 false d) Set.univ (bset 𝕄 far) tl)) ∧
      Inv (sufBodyV K hK sv s₁).2 := by
  obtain ⟨hmF₁, F₁⟩ := fold_spec (ι := Ans D P)
    (fun a m => ((sv ⟨D.rightBound a.span, true⟩ m).1.closed.filterMap
        fun b => (Ans.join D P K hK a b).val,
      (sv ⟨D.rightBound a.span, true⟩ m).1.opens, (sv ⟨D.rightBound a.span, true⟩ m).2))
    (fun a cs os => SemS 𝕄 (⟨cs, os⟩ : Sm D P) =
      {i | ∃ q ∈ chainS (membS (SED P 𝕄 false d) Set.univ (bset 𝕄 far) tl),
        SeqI false (.closed (den 𝕄 a.span)) q i})
    Inv s₁.1.closed (⟨[], []⟩, s₁.2) hm₁
    (fun a ha m hm => by
      obtain ⟨⟨hok, hex⟩, hinv⟩ := hsv ⟨D.rightBound a.span, true⟩ m hm (isBound_right hL _)
      refine ⟨?_, hinv⟩
      rw [ext_closed hL K hK (h₁.goal a ha) hok.goal, hex, wsuf_after_closed hL hE, seq_ext])
  obtain ⟨hmF₂, F₂⟩ := fold_spec (ι := Option R)
    (fun o m => ([], (sv ⟨o, o.isSome⟩ m).1.closed.map (fun b => D.rightBound b.span) ++
        (sv ⟨o, o.isSome⟩ m).1.opens, (sv ⟨o, o.isSome⟩ m).2))
    (fun o cs os => SemS 𝕄 (⟨cs, os⟩ : Sm D P) =
      {i | ∃ q ∈ chainS (membS (SED P 𝕄 false d) Set.univ (bset 𝕄 far) tl),
        SeqI false (.opn (bset 𝕄 o)) q i})
    Inv s₁.1.opens _ hmF₁
    (fun o ho m hm => by
      obtain ⟨⟨-, hex⟩, hinv⟩ := hsv ⟨o, o.isSome⟩ m hm (h₁.bound o ho)
      refine ⟨?_, hinv⟩
      rw [ext_open hL hE (bset 𝕄 o), hex, wsuf_after_open hL d o hf, seq_ext])
  refine ⟨?_, hmF₂⟩
  unfold sufBodyV
  rw [fold_sem F₂ _ (fun _ _ _ q => q), fold_sem F₁ _ (fun _ _ _ q => q), farD_seqSets]
  ext i
  constructor
  · rintro ((h | ⟨a, ha, q, hq, hs⟩) | ⟨o, ho, q, hq, hs⟩)
    · rcases h with ⟨a, ha, -⟩ | ⟨o, ho, -⟩
      · cases ha
      · cases ho
    · have hm : SI.closed (den 𝕄 a.span) ∈ SemS 𝕄 s₁.1 := .inl ⟨a, ha, rfl⟩
      rw [hs₁] at hm
      obtain ⟨p, hp, e⟩ := hm
      exact ⟨p, hp, q, hq, by rw [e]; exact hs⟩
    · have hm : SI.opn (bset 𝕄 o) ∈ SemS 𝕄 s₁.1 := .inr ⟨o, ho, rfl⟩
      rw [hs₁] at hm
      obtain ⟨p, hp, e⟩ := hm
      exact ⟨p, hp, q, hq, by rw [e]; exact hs⟩
  · rintro ⟨p, hp, q, hq, hs⟩
    have hm : farD false p ∈ SemS 𝕄 s₁.1 := by
      rw [hs₁]
      exact ⟨p, hp, rfl⟩
    rcases hm with ⟨a, ha, e⟩ | ⟨o, ho, e⟩
    · exact .inl (.inr ⟨a, ha, q, hq, by rw [← e]; exact hs⟩)
    · exact .inr ⟨o, ho, q, hq, by rw [← e]; exact hs⟩

/-! ## The memo -/

/-- What the summary recorded for a key holds: the products of a node, or of
the members of a chain from the `idx`-th on. -/
def MeansEx (k : Key R Rel) (s : Sm D P) : Prop :=
  IsBound D k.near.bound → IsBound D k.far → Normal k.node → k.node.FO →
    (k.idx = 0 → SemS 𝕄 s = WT P 𝕄 false k.d k.near k.node k.far) ∧
      (k.idx ≠ 0 → ∀ xs, k.node.view.forget = .chain xs → 2 ≤ (xs.drop k.idx).length →
        SemS 𝕄 s = farD false '' WSuf P 𝕄 k.d k.near (xs.drop k.idx) k.far)

/-- Every summary of the memo holds what its key says. -/
def MemoEx (m : Mm D P) : Prop := ∀ p ∈ m, MeansEx p.1 p.2

theorem memo_spec_ex {k : Key R Rel} {m : Mm D P} {body : Mm D P → Sm D P × Mm D P}
    (hm : MemoEx m) (hb : MeansEx k (body m).1 ∧ MemoEx (body m).2) :
    MeansEx k (memoV k m body).1 ∧ MemoEx (memoV k m body).2 := by
  unfold memoV
  cases h : lookupV m k with
  | some s =>
    unfold lookupV at h
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
    have hk : p.1 = k := sameKeyV_eq (by simpa using List.find?_some hp)
    have := hm p (List.mem_of_find?_eq_some hp)
    rw [hk] at this
    exact ⟨this, hm⟩
  | none =>
    refine ⟨hb.1, fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hb.1
    · exact hb.2 p hp

/-- The summary of a node, looked up or computed. -/
theorem memo_node_ex {c : Near R} {n : Rel} {far : Option R} {d : Nat} {m : Mm D P}
    {body : Mm D P → Sm D P × Mm D P} (hm : MemoEx m) (hc : IsBound D c.bound)
    (hf : IsBound D far) (hn : Normal n) (hfo : n.FO)
    (hb : SemS 𝕄 (body m).1 = WT P 𝕄 false d c n far ∧ MemoEx (body m).2) :
    SemS 𝕄 (memoV ⟨n, 0, d, c, far⟩ m body).1 = WT P 𝕄 false d c n far ∧
      MemoEx (memoV ⟨n, 0, d, c, far⟩ m body).2 := by
  obtain ⟨h₁, h₂⟩ := memo_spec_ex (k := ⟨n, 0, d, c, far⟩) (body := body) hm
    ⟨fun _ _ _ _ => ⟨fun _ => hb.1, fun h => absurd rfl h⟩, hb.2⟩
  exact ⟨(h₁ hc hf hn hfo).1 rfl, h₂⟩

section chain

variable (wv : Near R → Rel → Option R → Mm D P → Sm D P × Mm D P)

/-- The members hold their products in every context, at every memo that is
right. -/
def MembersEx (d : Nat) (ys : List Rel) : Prop :=
  ∀ x ∈ ys, ∀ (c : Near R) (fr : Option R) (m : Mm D P), MemoOk m → MemoEx m →
    IsBound D c.bound → IsBound D fr →
    SemS 𝕄 (wv c x fr m).1 = WT P 𝕄 false d c x fr ∧ MemoEx (wv c x fr m).2

include hL hE in
/-- The summary of the members of a chain from the `i`-th on. -/
theorem suf_ex {n : Rel} {d : Nat} {far : Option R} (hfar : IsBound D far) (hn : Normal n)
    (hfo : n.FO) {xsAll : List Rel} (hv : n.view.forget = .chain xsAll) :
    ∀ (ys : List Rel) (i : Nat) (c : Near R) (m : Mm D P), ys ≠ [] → xsAll.drop i = ys →
      MembersS wv d ys → MembersEx (P := P) wv d ys → (∀ x ∈ ys, NotSeq x) → MemoOk m →
      MemoEx m → IsBound D c.bound →
      SemS 𝕄 (sufSV K hK wv n d far i ys c m).1 = farD false '' WSuf P 𝕄 d c ys far ∧
        MemoEx (sufSV K hK wv n d far i ys c m).2
  | [], _, _, _, h, _, _, _, _, _, _, _ => absurd rfl h
  | [x], i, c, m, _, _, _, HX, _, hm, hmx, hc => by
    simp only [sufSV]
    exact HX x (by simp) c far m hm hmx hc hfar
  | x :: y :: zs, i, c, m, _, hi, HW, HX, hns, hm, hmx, hc => by
    have hi' : xsAll.drop (i + 1) = y :: zs := by
      rw [← List.tail_drop, hi]
      rfl
    have HW' : MembersS wv d (y :: zs) := fun z hz => HW z (List.mem_cons_of_mem _ hz)
    have HX' : MembersEx (P := P) wv d (y :: zs) := fun z hz => HX z (List.mem_cons_of_mem _ hz)
    have hns' : ∀ z ∈ y :: zs, NotSeq z := fun z hz => hns z (List.mem_cons_of_mem _ hz)
    have body : ∀ m', MemoOk m' → MemoEx m' →
        SemS 𝕄 (sufBodyV K hK (sufSV K hK wv n d far (i + 1) (y :: zs)) (wv c x none m')).1 =
            farD false '' WSuf P 𝕄 d c (x :: y :: zs) far ∧
          MemoEx (sufBodyV K hK (sufSV K hK wv n d far (i + 1) (y :: zs))
            (wv c x none m')).2 := by
      intro m' hm' hmx'
      obtain ⟨h₁, hm₁⟩ := HW x (by simp) c none m' hm' hc (isBound_none D)
      obtain ⟨hs₁, hx₁⟩ := HX x (by simp) c none m' hm' hmx' hc (isBound_none D)
      have := suf_body_ex hL hE K hK (fun m => MemoOk m ∧ MemoEx m) hfar _ h₁ hs₁ ⟨hm₁, hx₁⟩
        (sufSV K hK wv n d far (i + 1) (y :: zs))
        (fun c' m₂ hm₂ hc' => by
          obtain ⟨hok, hmok⟩ := suf_ok hL K hK wv hfar hn hfo hv (y :: zs) (i + 1) c' m₂ (by simp)
            hi' HW' hns' hm₂.1 hc'
          obtain ⟨hex, hmex⟩ := suf_ex hfar hn hfo hv (y :: zs) (i + 1) c' m₂ (by simp) hi' HW'
            HX' hns' hm₂.1 hm₂.2 hc'
          exact ⟨⟨hok, hex⟩, hmok, hmex⟩)
      rw [wsuf_cons]
      exact ⟨this.1, this.2.2⟩
    by_cases hi0 : i = 0
    · simp only [sufSV, hi0, ite_true]
      rw [hi0] at body
      exact body m hm hmx
    · simp only [sufSV, hi0, ite_false]
      obtain ⟨h₁, h₂⟩ := memo_spec_ex (P := P) (k := ⟨n, i, d, c, far⟩)
        (body := fun m => sufBodyV K hK (sufSV K hK wv n d far (i + 1) (y :: zs))
          (wv c x none m)) hmx
        ⟨fun _ _ _ _ => ⟨fun h => absurd h hi0, fun _ xs' hxs' _ => by
          obtain rfl : xs' = xsAll := by
            rw [hv] at hxs'
            exact (NodeView.chain.inj hxs').symm
          show SemS 𝕄 _ = farD false '' WSuf P 𝕄 d c (xs'.drop i) far
          rw [hi]
          exact (body m hm hmx).1⟩, (body m hm hmx).2⟩
      have := (h₁ hc hfar hn hfo).2 hi0 xsAll hv (by rw [hi]; simp)
      refine ⟨?_, h₂⟩
      have e : xsAll.drop i = x :: y :: zs := hi
      simp only [e] at this
      exact this

end chain

/-! ## A meet -/

omit [DecidableEq R] in
/-- The summaries of the members of a meet, one for each. -/
theorem members_inv (wv : Rel → Mm D P → Sm D P × Mm D P) (Q : Rel → Sm D P → Prop)
    (Inv : Mm D P → Prop) : ∀ (xs : List Rel) (m : Mm D P), Inv m →
      (∀ x ∈ xs, ∀ m, Inv m → Q x (wv x m).1 ∧ Inv (wv x m).2) →
      List.Forall₂ Q xs (membersSV wv xs m).1 ∧ Inv (membersSV wv xs m).2
  | [], _, hm, _ => ⟨.nil, hm⟩
  | x :: xs, m, hm, H => by
    obtain ⟨h₁, h₂⟩ := H x (by simp) m hm
    obtain ⟨h₃, h₄⟩ := members_inv wv Q Inv xs _ h₂ (fun y hy => H y (List.mem_cons_of_mem _ hy))
    exact ⟨.cons h₁ h₃, h₄⟩

include hL in
/-- The answers of a meet relate the meets of what one answer of every member
relates. -/
theorem meet_closed_sx {near far : Option R} {xs : List Rel} (hne : xs ≠ []) (W : Rel → Set SP)
    {ss : List (Sm D P)}
    (h : List.Forall₂ (fun x s => (∀ a ∈ s.closed, a.goal = ⟨near, x, far⟩) ∧
      SemS 𝕄 s = farD false '' W x) xs ss) (X : PRel) :
    (∃ a ∈ (meetAllV K hK (ss.map (·.closed))).foldl keepNew [], den 𝕄 a.span = X) ↔
      X ∈ meetAllS (xs.map fun x => closedPart (W x)) := by
  have hA : AEx near far (meetAllS (xs.map fun x => closedPart (W x)))
      (meetAllV K hK (ss.map (·.closed))) := by
    refine meetAll_ex hL K hK ?_ (by simpa using hne)
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.Forall₂.imp (fun x s hxs => ?_) h
    obtain ⟨hg, hs⟩ := hxs
    have hcl := sems_cl hs
    refine ⟨fun a ha => by rw [hg a ha], fun a ha => by rw [hg a ha], fun a ha => ?_,
      fun Y hY => ?_⟩
    · rw [← hcl]
      exact ⟨a, ha, rfl⟩
    · rw [← hcl] at hY
      exact hY
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hA.sound a (((keepNew_spec _ []).1 a ha).resolve_left (by simp))
  · intro hX
    obtain ⟨a, ha, rfl⟩ := hA.complete X hX
    obtain ⟨b, hb, e⟩ := (keepNew_spec _ []).2 a (.inr ha)
    exact ⟨b, hb, by rw [e]⟩

omit [DecidableEq R] in
/-- A meet is opaque exactly when every member has a product and one of them
an open one. -/
theorem opaque_sx {xs : List Rel} (W : Rel → Set SP) {ss : List (Sm D P)}
    (h : List.Forall₂ (fun x s => SemS 𝕄 s = farD false '' W x) xs ss) :
    opaqueS ss = true ↔ (∀ T ∈ xs.map W, T.Nonempty) ∧ ∃ T ∈ xs.map W, HasOpn T := by
  unfold opaqueS
  rw [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hall, s, hs, hop⟩
    refine ⟨fun T hT => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
      obtain ⟨s', hs', e⟩ := f2_left h x hx
      exact (sems_ne e).1 (hall s' hs')
    · obtain ⟨x, hx, e⟩ := f2_right h s hs
      exact ⟨W x, List.mem_map_of_mem hx, (sems_opn e).1 hop⟩
  · rintro ⟨hall, T, hT, hop⟩
    refine ⟨fun s hs => ?_, ?_⟩
    · obtain ⟨x, hx, e⟩ := f2_right h s hs
      exact (sems_ne e).2 (hall _ (List.mem_map_of_mem hx))
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
      obtain ⟨s, hs, e⟩ := f2_left h x hx
      exact ⟨s, hs, (sems_opn e).2 hop⟩

/-- A meet where nothing was pushed, from its answers and whether it is
opaque. -/
theorem meet_assemble_plain {T : Set SI} {xs : List Rel} (W : Rel → Set SP) {A B φ : Set GTerm}
    (hAB : farE false A B = φ)
    (hc : ∀ X, SI.closed X ∈ T ↔ X ∈ meetAllS (xs.map fun x => closedPart (W x)))
    (ho : ∀ F, SI.opn F ∈ T ↔
      F = φ ∧ (∀ S ∈ xs.map W, S.Nonempty) ∧ ∃ S ∈ xs.map W, HasOpn S) :
    T = farD false '' meetS A B (xs.map W) := by
  apply si_ext
  · intro X
    have hcl : (xs.map fun x => closedPart (W x)) = (xs.map W).map closedPart := by
      rw [List.map_map]; rfl
    rw [hc, farD_closed_iff, hcl, ← closedPart_meetS A B]
    rfl
  · intro F
    rw [ho, farD_opn_iff]
    constructor
    · rintro ⟨rfl, hall, hop⟩
      exact ⟨A, B, .inr ⟨rfl, hall, hop⟩, hAB⟩
    · rintro ⟨A', B', hm, e⟩
      rcases hm with ⟨X, -, e'⟩ | ⟨e', hall, hop⟩
      · cases e'
      · cases e'
        exact ⟨by rw [← hAB, e], hall, hop⟩

/-- A meet under a pushed boundary, from its answers under it and whether it
is opaque without it. -/
theorem meet_assemble_pushed {T : Set SI} {xs : List Rel} (S : Rel → Set SP) {π A B φ : Set GTerm}
    (hπ : π.Nonempty) (hN : nearE false A B = Set.univ) (hAB : farE false A B = φ)
    (hc : ∀ X, SI.closed X ∈ T ↔
      X ∈ meetAllS (xs.map fun x => closedPart (pushSet false π (S x))))
    (ho : ∀ F, SI.opn F ∈ T ↔
      F = φ ∧ (∀ S' ∈ xs.map S, S'.Nonempty) ∧ ∃ S' ∈ xs.map S, HasOpn S') :
    T = farD false '' pushSet false π (meetS A B (xs.map S)) := by
  apply si_ext
  · intro X
    have hcl : (xs.map fun x => closedPart (pushSet false π (S x))) =
        ((xs.map S).map closedPart).map (pushC false π) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun x _ => closedPart_pushSet false π (S x)
    rw [hc, farD_closed_iff, hcl, ← pushC_meetAllS, ← closedPart_meetS A B, ← closedPart_pushSet]
    rfl
  · intro F
    rw [ho]
    constructor
    · rintro ⟨rfl, hall, hop⟩
      have hmem : SP.opn A B ∈ meetS A B (xs.map S) := .inr ⟨rfl, hall, hop⟩
      have hpush : PushD false π (.opn A B) (pushO false π A B) :=
        .opn (by rw [hN, Set.univ_inter]; exact hπ)
      exact ⟨pushO false π A B, ⟨_, hmem, hpush⟩, by rw [farD_pushO, hAB]⟩
    · rintro ⟨r, ⟨p, hp, hpush⟩, e⟩
      rcases hp with ⟨X, -, rfl⟩ | ⟨rfl, hall, hop⟩
      · cases hpush with
        | closed hne => simp [farD] at e
      · cases hpush with
        | opn hne =>
          rw [farD_pushO, hAB] at e
          exact ⟨(SI.opn.inj e).symm, hall, hop⟩

/-! ## The whole unfolding -/

include hL hE in
/-- The summary of a node holds the products of its unfolding, and the memo
stays right. -/
theorem evalS_ex (hP : ProgFO P) : ∀ (d : Nat) (c : Near R) (n : Rel) (far : Option R)
    (m : Mm D P), MemoOk m → MemoEx m → IsBound D c.bound → IsBound D far → Normal n → n.FO →
    SemS 𝕄 (evalSV K hK d c n far m).1 = WT P 𝕄 false d c n far ∧
      MemoEx (evalSV K hK d c n far m).2
  | 0, c, n, far, m, _, hmx, hc, _, _, _ => by
    simp only [evalSV]
    refine ⟨?_, hmx⟩
    rw [wt_zero hL hc]
    apply si_ext
    · intro X
      rw [sems_closed_iff]
      constructor
      · rintro ⟨a, ha, -⟩; cases ha
      · intro h; cases h
    · intro F
      rw [sems_opn_iff]
      constructor
      · rintro ⟨o, ho, rfl⟩
        obtain rfl : o = far := by simpa using ho
        rfl
      · intro h
        exact ⟨far, by simp, (SI.opn.inj h).symm⟩
  | d + 1, c, n, far, m, hm, hmx, hc, hf, hn, hfo => by
    have ih := evalS_ex hP d
    have ok := evalS_ok hL K hK hP d
    simp only [evalSV]
    refine memo_node_ex hmx hc hf hn hfo ?_
    cases hv : n.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      dsimp only
      refine ⟨?_, hmx⟩
      rw [WT, ws_span]
      show _ = farD false '' SE P 𝕄 (d + 1) (bset 𝕄 c.bound) (.span s) (bset 𝕄 far)
      rw [← leaf_sem hL K hK hc hf (hfo s (by simp [RelOf.spans])) d]
      apply si_ext
      · intro X
        rw [sems_closed_iff, farD_closed_iff]
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ⟨a, Option.mem_toList.1 ha, rfl⟩
        · rintro ⟨a, ha, e⟩
          exact ⟨a, Option.mem_toList.2 ha, (SP.closed.inj e).symm⟩
      · intro F
        rw [sems_opn_iff, farD_opn_iff]
        constructor
        · rintro ⟨o, ho, -⟩; cases ho
        · rintro ⟨A, B, ⟨a, -, e⟩, -⟩; cases e
    | call f b₀ =>
      obtain ⟨b, hb⟩ := forget_call (P := P) hv
      simp only [hb]
      have hbn := bodyOf_normal hb
      have hbf := bodyOf_fo hP hb
      obtain ⟨h₁, h₂⟩ := ih c b far m hm hmx hc hf hbn hbf
      obtain ⟨hok, -⟩ := ok c b far m hm hc hf hbn hbf
      refine ⟨?_, h₂⟩
      rw [sems_lift (fun a c e => (Ans.unfold_val.1 e).2.1) (fun a ha => by
        obtain ⟨c', hc', -⟩ := Ans.unfold_ok (a := a) (n := n) (by rw [hb, hok.goal a ha])
        exact ⟨c', hc'⟩), h₁, WT, WT, ws_call hv hb]
    | union xs =>
      have hvu := forget_union hv
      have hparts := hn.view_union_eq hvu
      dsimp only
      obtain ⟨hmF, F⟩ := fold_spec (ι := Rel × Nat)
        (fun p m => ((evalSV K hK d c p.1 far m).1.closed.filterMap
            fun a => (Ans.inj D P a n p.2).val,
          (evalSV K hK d c p.1 far m).1.opens, (evalSV K hK d c p.1 far m).2))
        (fun p cs os => SemS 𝕄 (⟨cs, os⟩ : Sm D P) = WT P 𝕄 false d c p.1 far)
        (fun m => MemoOk m ∧ MemoEx m) xs.zipIdx (⟨[], []⟩, m) ⟨hm, hmx⟩
        (fun p hp m₂ hm₂ => by
          have hx : xs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hp
          have hmem : p.1 ∈ n.view.members := by rw [hvu]; exact List.mem_of_getElem? hx
          obtain ⟨h₁, h₂⟩ := ih c p.1 far m₂ hm₂.1 hm₂.2 hc hf (hn.view_members hmem)
            (hfo.view_members hmem)
          obtain ⟨hok, hmok⟩ := ok c p.1 far m₂ hm₂.1 hc hf (hn.view_members hmem)
            (hfo.view_members hmem)
          refine ⟨?_, hmok, h₂⟩
          rw [sems_lift (fun a c e => (Ans.inj_val.1 e).2.1) (fun a ha => by
            obtain ⟨c', hc', -⟩ := Ans.inj_ok (a := a) (u := n) (i := p.2) (by
              rw [← hparts, hok.goal a ha]; exact hx)
            exact ⟨c', hc'⟩), h₁])
      refine ⟨?_, hmF.2⟩
      rw [fold_sem F _ (fun _ _ _ q => q), WT, ws_union hv]
      ext i
      constructor
      · rintro (h | ⟨p, hp, r, hr, rfl⟩)
        · rcases h with ⟨a, ha, -⟩ | ⟨o, ho, -⟩
          · cases ha
          · cases ho
        · exact ⟨r, ⟨p.1, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp), hr⟩, rfl⟩
      · rintro ⟨r, ⟨x, hx, hr⟩, rfl⟩
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
        exact .inr ⟨(x, j), List.mem_zipIdx_iff_getElem?.2 hj, r, hr, rfl⟩
    | chain xs =>
      have hvc := forget_chain hv
      obtain ⟨h2, hmem, -⟩ := hn.view_chain hvc
      dsimp only
      have hxs : xs ≠ [] := by rintro rfl; simp at h2
      have key := suf_ex hL hE K hK (evalSV K hK d) hf hn hfo hv xs 0 c m hxs rfl
        (fun x hx c' fr m₂ hm₂ hc' hfr => ok c' x fr m₂ hm₂ hc' hfr (hmem x hx).1
          (hfo.view_members (by rw [hvc]; exact hx)))
        (fun x hx c' fr m₂ hm₂ hmx₂ hc' hfr => ih c' x fr m₂ hm₂ hmx₂ hc' hfr (hmem x hx).1
          (hfo.view_members (by rw [hvc]; exact hx)))
        (fun x hx => (hmem x hx).2) hm hmx hc
      rw [WT, ws_chain_suf hv]
      exact key
    | meet xs =>
      have hvm := forget_meet hv
      obtain ⟨h2, hmem, -, -⟩ := hn.view_meet hvm
      dsimp only
      have hxs : xs ≠ [] := by rintro rfl; simp at h2
      have mem : ∀ c' : Near R, IsBound D c'.bound → ∀ x ∈ xs, ∀ m₂, MemoOk m₂ ∧ MemoEx m₂ →
          ((∀ a ∈ (evalSV K hK d c' x far m₂).1.closed, a.goal = ⟨c'.bound, x, far⟩) ∧
            SemS 𝕄 (evalSV K hK d c' x far m₂).1 = farD false '' WS P 𝕄 false d c' x far) ∧
            (MemoOk (evalSV K hK d c' x far m₂).2 ∧ MemoEx (evalSV K hK d c' x far m₂).2) :=
        fun c' hc' x hx m₂ hm₂ => by
          have hxn := (hmem x hx).1
          have hxf := hfo.view_members (by rw [hvm]; exact hx)
          obtain ⟨hok, hmok⟩ := ok c' x far m₂ hm₂.1 hc' hf hxn hxf
          obtain ⟨hex, hmex⟩ := ih c' x far m₂ hm₂.1 hm₂.2 hc' hf hxn hxf
          exact ⟨⟨hok.goal, hex⟩, hmok, hmex⟩
      obtain ⟨hA, hmA⟩ := members_inv (fun x m => evalSV K hK d c x far m)
        (fun x s => (∀ a ∈ s.closed, a.goal = ⟨c.bound, x, far⟩) ∧
          SemS 𝕄 s = farD false '' WS P 𝕄 false d c x far)
        (fun m => MemoOk m ∧ MemoEx m) xs m ⟨hm, hmx⟩ (mem c hc)
      have hcl := meet_closed_sx hL K hK hxs (fun x => WS P 𝕄 false d c x far) hA
      cases hp : c.isPushed with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        refine ⟨?_, hmA.2⟩
        have hW : ∀ x, WS P 𝕄 false d c x far =
            SED P 𝕄 false d (bset 𝕄 c.bound) x (bset 𝕄 far) := fun x => ws_plain hL hp hf
        simp only [hW] at hA hcl
        rw [WT, ws_plain hL hp hf, sed_meet hv]
        refine meet_assemble_plain (fun x => SED P 𝕄 false d (bset 𝕄 c.bound) x (bset 𝕄 far))
          rfl (fun X => ?_) (fun F => ?_)
        · rw [sems_closed_iff]
          exact hcl X
        · rw [sems_opn_iff, ← opaque_sx _ (List.Forall₂.imp (fun _ _ h => h.2) hA)]
          constructor
          · rintro ⟨o, ho, rfl⟩
            split at ho
            · next hq =>
              obtain rfl : o = far := by simpa using ho
              exact ⟨rfl, hq⟩
            · cases ho
          · rintro ⟨rfl, hq⟩
            exact ⟨far, by simp [hq], rfl⟩
      | true =>
        simp only [ite_true]
        have hpp : c.pushed = true := by
          have h := hp
          simp only [Near.isPushed, Bool.and_eq_true] at h
          exact h.1
        have ho : c.own = ⟨none, false⟩ := by simp [Near.own, hpp]
        have hco : IsBound D c.own.bound := by rw [ho]; exact isBound_none D
        obtain ⟨hB, hmB⟩ := members_inv (fun x m => evalSV K hK d c.own x far m)
          (fun x s => SemS 𝕄 s = farD false '' SED P 𝕄 false d Set.univ x (bset 𝕄 far))
          (fun m => MemoOk m ∧ MemoEx m) xs _ hmA
          (fun x hx m₂ hm₂ => by
            obtain ⟨⟨-, hex⟩, hinv⟩ := mem c.own hco x hx m₂ hm₂
            rw [ws_none hL (by rw [ho]) hf] at hex
            exact ⟨hex, hinv⟩)
        refine ⟨?_, hmB.2⟩
        have hW : ∀ (d' : Nat) (x : Rel), WS P 𝕄 false d' c x far =
            pushSet false (bset 𝕄 c.bound) (SED P 𝕄 false d' Set.univ x (bset 𝕄 far)) := by
          intro d' x
          simp only [WS, hpp, ite_true]
        simp only [hW] at hcl
        rw [WT, hW, sed_meet hv]
        refine meet_assemble_pushed (fun x => SED P 𝕄 false d Set.univ x (bset 𝕄 far))
          (bset_nonempty hL hc) rfl rfl (fun X => ?_) (fun F => ?_)
        · rw [sems_closed_iff]
          exact hcl X
        · rw [sems_opn_iff, ← opaque_sx _ hB]
          constructor
          · rintro ⟨o, ho', rfl⟩
            split at ho'
            · next hq =>
              obtain rfl : o = far := by simpa using ho'
              exact ⟨rfl, hq⟩
            · cases ho'
          · rintro ⟨rfl, hq⟩
            exact ⟨far, by simp [hq], rfl⟩

/-! ## The race -/

include hL hE in
/-- The race answered with shared work says the unfolding is final exactly
when it has no open product. -/
theorem sharedRace_final (hP : ProgFO P) (d : Nat) (g : GoalOf R Rel) (hg : GoalOk D g) :
    (sharedRace (K := DerivationKernel.over D K hK P) d g).val.1 = true ↔
      Final P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb) := by
  obtain ⟨hex, -⟩ := evalS_ex hL hE K hK hP d ⟨g.lb, false⟩ g.node g.rb []
    (fun p hp => by cases hp) (fun p hp => by cases hp) hg.lb hg.rb hg.normal hg.fo
  have hS : WS P 𝕄 false d ⟨g.lb, false⟩ g.node g.rb =
      SE P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb) := rfl
  rw [WT, hS] at hex
  have hop := sems_opn hex
  rw [sharedRace_val, Final, ← hop]
  generalize (evalSV (P := P) K hK d ⟨g.lb, false⟩ g.node g.rb []).1.opens.isEmpty = o
  cases o <;> simp

end laws

end Unfold

end Tabled

end RwLog
