/-
# The shared evaluation is R001's unfolding race, without the repeats

`eval_ok` is the invariant of the shared evaluation. With the ticks forgotten,
the summary of `e` at depth `d` after the interface `ctx` describes rung
zero's normal form `N` of the unfolding of `e` to depth `d` (`GoodS`):

* its spans are the products of `N` that are a single span and are alive
  after `ctx`, in the normalizer's order, each kept at its first occurrence;
* its open interfaces let through exactly what the other products of `N`
  that are alive after `ctx` let through.

Both depend on `ctx` only through the terms it lets through (`rng`), so a
summary recorded for one interface is right for every interface the memo
takes for the same (`lookup_ok`), and every entry of the memo is right
(`MemoOK`).

The spans are computed exactly; the open interfaces are only described,
because which span represents an interface depends on what the memo held.
That is enough: at the top only whether there is one is asked, and inside a
sequence an open interface is used only through what it lets through.

At the top nothing stands to the left, so nothing is pruned: there is no open
interface exactly when no product contains a call, and then the spans are
those of the products. `shared_exact` follows.
-/
import RwLog.Rungs.R003.Spec
import RwLog.Rungs.R003.Proofs.Products
import RwLog.Rungs.R000.Unfold
import RwLog.Rungs.Tabled.Exact
import RwLog.Lib.Firsts

namespace RwLog

namespace R003

open R001 Cost
open R002 (headSpan lastSpan)

/-! ## The traversals, with the ticks forgotten -/

theorem addSpan_val (xs : List Span) (x : Span) : (addSpan xs x).val = addNew xs x := by
  simp only [addSpan, bind_val, pure_val, anyL_val, addNew]
  by_cases h : x ∈ xs
  · have : (xs.any fun y => decide (y = x)) = true := List.any_eq_true.mpr ⟨x, h, by simp⟩
    simp [this, h]
  · have : (xs.any fun y => decide (y = x)) = false := by
      rw [List.any_eq_false]
      intro y hy hyx
      obtain rfl := of_decide_eq_true hyx
      exact h hy
    simp [this, h]

theorem addOpen_val (xs : List (Option Span)) (x : Option Span) :
    (addOpen xs x).val = addNew xs x := by
  simp only [addOpen, bind_val, pure_val, anyL_val, addNew]
  by_cases h : x ∈ xs
  · have : (xs.any fun y => decide (y = x)) = true := List.any_eq_true.mpr ⟨x, h, by simp⟩
    simp [this, h]
  · have : (xs.any fun y => decide (y = x)) = false := by
      rw [List.any_eq_false]
      intro y hy hyx
      obtain rfl := of_decide_eq_true hyx
      exact h hy
    simp [this, h]

theorem foldSpan_val (acc xs : List Span) : (foldL addSpan acc xs).val = addAll acc xs := by
  rw [foldL_val]
  simp only [addSpan_val]
  rfl

theorem foldOpen_val (acc xs : List (Option Span)) :
    (foldL addOpen acc xs).val = addAll acc xs := by
  rw [foldL_val]
  simp only [addOpen_val]
  rfl

/-! ## What a summary says -/

/-- What the interfaces of a list let through. -/
def ranges (os : List (Option Span)) : Set (Set GTerm) := {t | ∃ o ∈ os, t = rng o}

@[simp] theorem ranges_nil : ranges [] = ∅ := by
  ext t; simp [ranges]

theorem ranges_addAll (acc xs : List (Option Span)) :
    ranges (addAll acc xs) = ranges acc ∪ ranges xs := by
  ext t
  simp only [ranges, mem_addAll, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨o, ho | ho, h⟩
    · exact .inl ⟨o, ho, h⟩
    · exact .inr ⟨o, ho, h⟩
  · rintro (⟨o, ho, h⟩ | ⟨o, ho, h⟩)
    · exact ⟨o, .inl ho, h⟩
    · exact ⟨o, .inr ho, h⟩

theorem ranges_eq_empty {os : List (Option Span)} : ranges os = ∅ ↔ os = [] := by
  constructor
  · intro h
    cases os with
    | nil => rfl
    | cons o os =>
      have : rng o ∈ ranges (o :: os) := ⟨o, List.mem_cons_self, rfl⟩
      rw [h] at this
      exact this.elim
  · rintro rfl; exact ranges_nil

/-- The summary describes the normal form `N` after an interface that lets
`ρ` through. -/
def GoodS (N : List (List Rel)) (ρ : Set GTerm) (s : Summary) : Prop :=
  s.spans = firsts ((closed N).filter (aliveB ρ)) ∧ ranges s.opens = OpenR N ρ

/-- Every entry of the memo describes the normal form of its key. -/
def MemoOK (P : Program) (m : Memo) : Prop :=
  ∀ k s, (k, s) ∈ m → GoodS (R000.norm k.neg (R000.unfoldN P k.d k.e)) (rng k.ctx) s

/-- A memoized evaluation describes `N` and keeps the memo right. -/
def EvalOK (P : Program) (N : List (List Rel))
    (f : Option Span → Memo → Cost (Summary × Memo)) : Prop :=
  ∀ ctx m, MemoOK P m → GoodS N (rng ctx) (f ctx m).val.1 ∧ MemoOK P (f ctx m).val.2

theorem memoOK_nil (P : Program) : MemoOK P [] := fun _ _ h => by cases h

/-! ## The memo -/

theorem sameKey_spec {k k' : Key} (h : (sameKey k k').val = true) :
    k.neg = k'.neg ∧ k.d = k'.d ∧ k.e = k'.e ∧ rng k.ctx = rng k'.ctx := by
  simp only [sameKey, bind_val] at h
  by_cases h₁ : k.neg = k'.neg ∧ k.d = k'.d
  · rw [ite_eq_left h₁] at h
    simp only [bind_val] at h
    by_cases h₂ : k.e = k'.e
    · rw [ite_eq_left h₂] at h
      exact ⟨h₁.1, h₁.2, h₂, sameCtx_rng h⟩
    · rw [ite_eq_right h₂] at h
      cases h
  · rw [ite_eq_right h₁] at h
    cases h

/-- What the memo returns for a key describes the normal form of the key. -/
theorem lookup_ok {P : Program} {m : Memo} (hm : MemoOK P m) {k : Key} {s : Summary}
    (h : (lookup m k).val = some s) :
    GoodS (R000.norm k.neg (R000.unfoldN P k.d k.e)) (rng k.ctx) s := by
  simp only [lookup, bind_val, pure_val, findL_val, Option.map_eq_some_iff] at h
  obtain ⟨⟨k', s'⟩, hf, rfl⟩ := h
  have hk : (sameKey k' k).val = true := by
    have := List.find?_some hf
    exact this
  obtain ⟨hn, hd, he, hc⟩ := sameKey_spec hk
  have := hm k' s' (List.mem_of_find?_eq_some hf)
  rwa [hn, hd, he, hc] at this

theorem memo_ok {P : Program} (k : Key) (body : Memo → Cost (Summary × Memo))
    (hbody : ∀ m, MemoOK P m →
      GoodS (R000.norm k.neg (R000.unfoldN P k.d k.e)) (rng k.ctx) (body m).val.1 ∧
        MemoOK P (body m).val.2)
    {m : Memo} (hm : MemoOK P m) :
    GoodS (R000.norm k.neg (R000.unfoldN P k.d k.e)) (rng k.ctx) (memo k m body).val.1 ∧
      MemoOK P (memo k m body).val.2 := by
  simp only [memo, bind_val]
  cases hl : (lookup m k).val with
  | some s => exact ⟨lookup_ok hm hl, hm⟩
  | none =>
    obtain ⟨hg, hm'⟩ := hbody m hm
    refine ⟨hg, fun k' s' h => ?_⟩
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact hg
    · exact hm' k' s' h

/-! ## Leaves and choices -/

theorem goodS_zero (ρ : Set GTerm) : GoodS [] ρ ⟨[], []⟩ := by
  refine ⟨rfl, ?_⟩
  ext t
  simp [OpenR]

theorem goodS_span (ctx : Option Span) (s : Span) :
    GoodS [[.span s]] (rng ctx) ⟨if (alive ctx s).val then [s] else [], []⟩ := by
  constructor
  · show _ = firsts ([s].filter (aliveB (rng ctx)))
    rw [← alive_eq ctx, List.filter_cons]
    cases (alive ctx s).val <;> rfl
  · ext t
    simp only [ranges_nil, Set.mem_empty_iff_false, OpenR, List.mem_singleton,
      Set.mem_ofPred_eq, false_iff, not_exists, not_and]
    rintro p rfl h
    cases h

theorem goodS_call (ρ : Set GTerm) (x : Rel) (hx : ∀ s, x ≠ .span s) : GoodS [[x]] ρ ⟨[], [none]⟩ := by
  have hs : single [x] = none := by
    cases x <;> first | rfl | exact (hx _ rfl).elim
  have hh : headSpan [x] = none := by
    cases x <;> first | rfl | exact (hx _ rfl).elim
  have hl : lastSpan [x] = none := by
    cases x <;> first | rfl | exact (hx _ rfl).elim
  constructor
  · show [] = firsts ((closed [[x]]).filter _)
    simp [closed, hs]
  · ext t
    simp only [ranges, List.mem_singleton, exists_eq_left, Set.mem_ofPred_eq, OpenR]
    constructor
    · rintro rfl
      exact ⟨hs, fun h hh' => (by rw [hh] at hh'; cases hh'), by rw [hl]⟩
    · rintro ⟨-, -, rfl⟩
      rw [hl]

theorem goodS_or {Na Nb : List (List Rel)} {ρ : Set GTerm} {x y : Summary}
    (hx : GoodS Na ρ x) (hy : GoodS Nb ρ y) :
    GoodS (Na ++ Nb) ρ ⟨(foldL addSpan x.spans y.spans).val, (foldL addOpen x.opens y.opens).val⟩ := by
  constructor
  · show (foldL addSpan x.spans y.spans).val = _
    rw [foldSpan_val, hx.1, hy.1, addAll_firsts, ← firsts_append, closed_append,
      List.filter_append]
  · show ranges (foldL addOpen x.opens y.opens).val = _
    rw [foldOpen_val, ranges_addAll, hx.2, hy.2, openR_append]

/-! ## Conjunctions -/

theorem filter_filterMap_eq_flatMap {α β : Type} (f : α → Option β) (g : β → Bool) (l : List α) :
    (l.filterMap f).filter g = l.flatMap fun y => (f y).toList.filter g := by
  rw [List.filterMap_eq_flatMap_toList, List.filter_flatMap]

theorem goodS_and {Na Nb : List (List Rel)} {a b : Summary} (ctx : Option Span)
    (ha : GoodS Na Set.univ a) (hb : GoodS Nb Set.univ b) :
    GoodS (Na.flatMap fun p => Nb.filterMap (R000.mkAnd p)) (rng ctx) (andSummary ctx a b).val := by
  have huniv : ∀ N : List (List Rel), (closed N).filter (aliveB Set.univ) = closed N :=
    fun N => List.filter_eq_self.mpr fun x _ => aliveB_iff.mpr (aliveP_univ x)
  have has : a.spans = firsts (closed Na) := by rw [ha.1, huniv]
  have hbs : b.spans = firsts (closed Nb) := by rw [hb.1, huniv]
  have hopen : ∀ {N : List (List Rel)} {s : Summary}, GoodS N Set.univ s →
      (s.opens.isEmpty = false ↔ ∃ p ∈ N, single p = none) := by
    intro N s hs
    rw [← Bool.not_eq_true, List.isEmpty_iff, ← ranges_eq_empty, hs.2,
      Set.eq_empty_iff_forall_notMem]
    constructor
    · intro h
      by_contra hne
      refine h fun t ht => ?_
      obtain ⟨p, hp, hsp, -, -⟩ := ht
      exact hne ⟨p, hp, hsp⟩
    · rintro ⟨p, hp, hsp⟩ h
      exact h _ ⟨p, hp, hsp, headOK_univ p, rfl⟩
  have hspan : ∀ {N : List (List Rel)} {s : Summary}, GoodS N Set.univ s →
      (s.spans.isEmpty = false ↔ ∃ p ∈ N, single p ≠ none) := by
    intro N s hs
    rw [← Bool.not_eq_true, List.isEmpty_iff, hs.1, huniv]
    constructor
    · intro h
      cases hc : closed N with
      | nil => rw [hc] at h; exact (h rfl).elim
      | cons x _ =>
        have hx : x ∈ closed N := by rw [hc]; exact List.mem_cons_self
        exact ⟨_, mem_closed.mp hx, by simp⟩
    · rintro ⟨p, hp, hsp⟩ h
      cases hs' : single p with
      | none => exact hsp hs'
      | some x =>
        have hx : x ∈ closed N := List.mem_filterMap.mpr ⟨p, hp, hs'⟩
        have : x ∈ firsts (closed N) := mem_firsts.mpr hx
        rw [h] at this
        cases this
  simp only [andSummary, bind_val, pure_val, flatMapL_val, filterMapL_val, filterL_val,
    foldSpan_val]
  constructor
  · show addAll [] _ = _
    simp only [show ∀ x y : Span, (Charged.meet x y).val = x.meet y from fun _ _ => rfl]
    rw [alive_eq ctx, has, hbs, List.filter_flatMap]
    show addAll [] ((firsts _).flatMap _) = addAll [] _
    rw [addAll_flatMap_firsts, closed_and, List.filter_flatMap]
    refine addAll_flatMap_congr _ _ _ _ fun x _ => ?_
    rw [filter_filterMap_eq_flatMap, filter_filterMap_eq_flatMap]
    exact addAll_flatMap_firsts [] _ _
  · rw [openR_and]
    have hsome : ∀ {N : List (List Rel)} {s : Summary}, GoodS N Set.univ s →
        ((!s.spans.isEmpty || !s.opens.isEmpty) = true ↔ ∃ p, p ∈ N) := by
      intro N s hs
      rw [Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_true', hspan hs, hopen hs]
      constructor
      · rintro (⟨p, hp, -⟩ | ⟨p, hp, -⟩) <;> exact ⟨p, hp⟩
      · rintro ⟨p, hp⟩
        cases hsp : single p with
        | none => exact .inr ⟨p, hp, hsp⟩
        | some x => exact .inl ⟨p, hp, by simp [hsp]⟩
    have hcond : ((!a.opens.isEmpty && (!b.spans.isEmpty || !b.opens.isEmpty)) ||
        ((!a.spans.isEmpty || !a.opens.isEmpty) && !b.opens.isEmpty)) = true ↔
        ∃ p ∈ Na, ∃ q ∈ Nb, single p = none ∨ single q = none := by
      rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, hsome ha, hsome hb,
        Bool.not_eq_true', Bool.not_eq_true', hopen ha, hopen hb]
      constructor
      · rintro (⟨⟨p, hp, hsp⟩, q, hq⟩ | ⟨⟨p, hp⟩, q, hq, hsq⟩)
        · exact ⟨p, hp, q, hq, .inl hsp⟩
        · exact ⟨p, hp, q, hq, .inr hsq⟩
      · rintro ⟨p, hp, q, hq, hsp | hsq⟩
        · exact .inl ⟨⟨p, hp, hsp⟩, q, hq⟩
        · exact .inr ⟨⟨p, hp⟩, q, hq, hsq⟩
    ext t
    by_cases hc : ∃ p ∈ Na, ∃ q ∈ Nb, single p = none ∨ single q = none
    · rw [ite_eq_left (hcond.mpr hc)]
      simp only [ranges, List.mem_singleton, exists_eq_left, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h, hc⟩, fun h => h.1⟩
    · rw [ite_eq_right (fun h => hc (hcond.mp h))]
      simp only [ranges_nil, Set.mem_empty_iff_false, Set.mem_ofPred_eq, false_iff]
      exact fun h => hc h.2

/-! ## Sequences -/

section Seq

variable {P : Program} {Nb : List (List Rel)} {second : Option Span → Memo → Cost (Summary × Memo)}

/-- The spans of the second factor that can follow the span `x` of the
first, composed with it. -/
noncomputable def after (Nb : List (List Rel)) (ρ : Set GTerm) (x : Span) : List Span :=
  ((closed Nb).filter (aliveB (img ρ x))).filterMap x.compose

theorem afterSpan_ok (hsec : EvalOK P Nb second) (ctx : Option Span) (acc : Acc) (x : Span)
    (hm : MemoOK P acc.2.2) (hx : AliveP (rng ctx) x) :
    (afterSpan ctx second acc x).val.1 = addAll acc.1 (after Nb (rng ctx) x) ∧
      ranges (afterSpan ctx second acc x).val.2.1 = ranges acc.2.1 ∪ OpenR Nb (img (rng ctx) x) ∧
      MemoOK P (afterSpan ctx second acc x).val.2.2 := by
  obtain ⟨⟨hs, ho⟩, hm'⟩ := hsec (extend ctx x).val acc.2.2 hm
  rw [rng_extend hx] at hs ho
  simp only [afterSpan, bind_val, pure_val, filterMapL_val, foldSpan_val, foldOpen_val]
  refine ⟨?_, ?_, hm'⟩
  · rw [hs, show (fun y => (Charged.compose x y).val) = x.compose from rfl,
      addAll_filterMap_firsts]
    rfl
  · rw [ranges_addAll, ho]

theorem foldSpan_ok (hsec : EvalOK P Nb second) (ctx : Option Span) : ∀ (xs : List Span) (acc : Acc),
    MemoOK P acc.2.2 → (∀ x ∈ xs, AliveP (rng ctx) x) →
    (foldL (afterSpan ctx second) acc xs).val.1 = addAll acc.1 (xs.flatMap (after Nb (rng ctx))) ∧
      ranges (foldL (afterSpan ctx second) acc xs).val.2.1 =
        ranges acc.2.1 ∪ {t | ∃ x ∈ xs, t ∈ OpenR Nb (img (rng ctx) x)} ∧
      MemoOK P (foldL (afterSpan ctx second) acc xs).val.2.2
  | [], acc, hm, _ => by
    refine ⟨rfl, ?_, hm⟩
    ext t
    simp [foldL]
  | x :: xs, acc, hm, hal => by
    obtain ⟨h₁, h₂, h₃⟩ := afterSpan_ok hsec ctx acc x hm (hal x List.mem_cons_self)
    obtain ⟨k₁, k₂, k₃⟩ := foldSpan_ok hsec ctx xs (afterSpan ctx second acc x).val h₃
      fun x hx => hal x (List.mem_cons_of_mem _ hx)
    simp only [foldL, bind_val]
    refine ⟨?_, ?_, k₃⟩
    · rw [k₁, h₁, List.flatMap_cons, addAll_append]
    · rw [k₂, h₂, Set.union_assoc]
      congr 1
      ext t
      simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons, exists_eq_or_imp]

/-- What follows a product of the first factor that is not a single span and
lets `τ` through. -/
def afterOpenR (Nb : List (List Rel)) (τ : Set GTerm) : Set (Set GTerm) :=
  {t | t ∈ OpenR Nb τ ∨ ∃ h ∈ closed Nb, AliveP τ h ∧ t = img τ h}

theorem afterOpen_ok (hsec : EvalOK P Nb second) (acc : Acc) (c : Option Span)
    (hm : MemoOK P acc.2.2) :
    (afterOpen second acc c).val.1 = acc.1 ∧
      ranges (afterOpen second acc c).val.2.1 = ranges acc.2.1 ∪ afterOpenR Nb (rng c) ∧
      MemoOK P (afterOpen second acc c).val.2.2 := by
  obtain ⟨⟨hs, ho⟩, hm'⟩ := hsec c acc.2.2 hm
  refine ⟨rfl, ?_, hm'⟩
  simp only [afterOpen, bind_val, pure_val, mapL_val, foldOpen_val]
  rw [ranges_addAll]
  congr 1
  ext t
  constructor
  · rintro ⟨o, ho', rfl⟩
    rcases List.mem_append.mp ho' with ho' | ho'
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ho'
      rw [hs, mem_firsts, List.mem_filter, aliveB_iff] at hh
      exact .inr ⟨h, hh.1, hh.2, rng_extend hh.2⟩
    · left
      rw [← ho]
      exact ⟨o, ho', rfl⟩
  · rintro (h | ⟨h, hh, hal, rfl⟩)
    · rw [← ho] at h
      obtain ⟨o, ho', rfl⟩ := h
      exact ⟨o, List.mem_append_right _ ho', rfl⟩
    · refine ⟨(extend c h).val, List.mem_append_left _ (List.mem_map.mpr ⟨h, ?_, rfl⟩),
        (rng_extend hal).symm⟩
      rw [hs, mem_firsts, List.mem_filter, aliveB_iff]
      exact ⟨hh, hal⟩

theorem foldOpen_ok (hsec : EvalOK P Nb second) : ∀ (cs : List (Option Span)) (acc : Acc),
    MemoOK P acc.2.2 →
    (foldL (afterOpen second) acc cs).val.1 = acc.1 ∧
      ranges (foldL (afterOpen second) acc cs).val.2.1 =
        ranges acc.2.1 ∪ {t | ∃ c ∈ cs, t ∈ afterOpenR Nb (rng c)} ∧
      MemoOK P (foldL (afterOpen second) acc cs).val.2.2
  | [], acc, hm => by
    refine ⟨rfl, ?_, hm⟩
    ext t
    simp [foldL]
  | c :: cs, acc, hm => by
    obtain ⟨h₁, h₂, h₃⟩ := afterOpen_ok hsec acc c hm
    obtain ⟨k₁, k₂, k₃⟩ := foldOpen_ok hsec cs (afterOpen second acc c).val h₃
    simp only [foldL, bind_val]
    refine ⟨k₁.trans h₁, ?_, k₃⟩
    rw [k₂, h₂, Set.union_assoc]
    congr 1
    ext t
    simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons, exists_eq_or_imp]

/-- Pruning the spans of the second factor after a span of the first is
pruning the composed spans. -/
theorem after_filter_one (x : Span) (ρ : Set GTerm) : ∀ Cb : List Span,
    (Cb.filter (aliveB (img ρ x))).filterMap x.compose =
      (Cb.filterMap x.compose).filter (aliveB ρ)
  | [] => rfl
  | y :: Cb => by
    have ihb := after_filter_one x ρ Cb
    rw [List.filter_cons, List.filterMap_cons]
    cases hc : x.compose y with
    | none =>
      have : ¬ aliveB (img ρ x) y = true :=
        fun h => not_aliveP_of_compose_none hc ρ (aliveB_iff.mp h)
      rw [ite_eq_right this]
      exact ihb
    | some z =>
      rw [List.filter_cons]
      by_cases hy : AliveP (img ρ x) y
      · rw [ite_eq_left (aliveB_iff.mpr hy), List.filterMap_cons, hc,
          ite_eq_left (aliveB_iff.mpr ((aliveP_compose hc ρ).mpr hy)), ihb]
      · rw [ite_eq_right (fun h => hy (aliveB_iff.mp h)),
          ite_eq_right (fun h => hy ((aliveP_compose hc ρ).mp (aliveB_iff.mp h))), ihb]

/-- Pruning the spans of the first factor, then those of the second after
each of them, is pruning the composed spans. -/
theorem after_filter (Ca Cb : List Span) (ρ : Set GTerm) :
    ((Ca.filter (aliveB ρ)).flatMap fun x => ((Cb.filter (aliveB (img ρ x))).filterMap x.compose)) =
      (Ca.flatMap fun x => Cb.filterMap x.compose).filter (aliveB ρ) := by
  rw [List.filter_flatMap]
  induction Ca with
  | nil => rfl
  | cons x Ca ih =>
    rw [List.filter_cons, List.flatMap_cons]
    by_cases hx : AliveP ρ x
    · rw [ite_eq_left (aliveB_iff.mpr hx), List.flatMap_cons, ih, after_filter_one]
    · rw [ite_eq_right (fun h => hx (aliveB_iff.mp h)), ih]
      have : (Cb.filterMap x.compose).filter (aliveB ρ) = [] := by
        rw [List.filter_eq_nil_iff]
        intro z hz hal
        obtain ⟨y, -, hc⟩ := List.mem_filterMap.mp hz
        exact hx ((aliveP_compose hc ρ).mp (aliveB_iff.mp hal)).of_img
      rw [this]
      rfl

theorem seqSummary_ok {Na : List (List Rel)} (ha : ∀ p ∈ Na, p ≠ []) (hb : ∀ q ∈ Nb, q ≠ [])
    (hsec : EvalOK P Nb second) (ctx : Option Span) {first : Summary}
    (hfirst : GoodS Na (rng ctx) first) {m : Memo} (hm : MemoOK P m) :
    GoodS (Na.flatMap fun p => Nb.filterMap (R000.joinSeq p)) (rng ctx)
        (seqSummary ctx first second m).val.1 ∧
      MemoOK P (seqSummary ctx first second m).val.2 := by
  have hal : ∀ x ∈ first.spans, AliveP (rng ctx) x := by
    intro x hx
    rw [hfirst.1, mem_firsts, List.mem_filter, aliveB_iff] at hx
    exact hx.2
  obtain ⟨h₁, h₂, h₃⟩ := foldSpan_ok hsec ctx first.spans ([], [], m) hm hal
  obtain ⟨k₁, k₂, k₃⟩ := foldOpen_ok hsec first.opens _ h₃
  simp only [seqSummary, bind_val, pure_val]
  refine ⟨⟨?_, ?_⟩, k₃⟩
  · show (foldL (afterOpen second) _ first.opens).val.1 = _
    rw [k₁, h₁, hfirst.1]
    show addAll [] ((firsts _).flatMap _) = addAll [] _
    rw [addAll_flatMap_firsts, closed_seq Na Nb ha hb, ← after_filter]
    rfl
  · show ranges (foldL (afterOpen second) _ first.opens).val.2.1 = _
    rw [k₂, h₂, openR_seq Na Nb ha hb, ranges_nil, Set.empty_union]
    congr 1
    · ext t
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x, hx, ht⟩
        rw [hfirst.1, mem_firsts, List.mem_filter, aliveB_iff] at hx
        exact ⟨x, hx.1, hx.2, ht⟩
      · rintro ⟨x, hx, hax, ht⟩
        refine ⟨x, ?_, ht⟩
        rw [hfirst.1, mem_firsts, List.mem_filter, aliveB_iff]
        exact ⟨hx, hax⟩
    · ext t
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨c, hc, ht⟩
        have : rng c ∈ ranges first.opens := ⟨c, hc, rfl⟩
        rw [hfirst.2] at this
        obtain ⟨p, hp, hsp, hok, he⟩ := this
        rw [he] at ht
        exact ⟨p, hp, hsp, hok, ht⟩
      · rintro ⟨p, hp, hsp, hok, ht⟩
        have : rng (lastSpan p) ∈ ranges first.opens := by
          rw [hfirst.2]
          exact ⟨p, hp, hsp, hok, rfl⟩
        obtain ⟨c, hc, he⟩ := this
        rw [he] at ht
        exact ⟨c, hc, ht⟩

end Seq

/-! ## The invariant of the evaluation -/

/-- The invariant at one depth, given it for the calls at that depth. -/
theorem eval_step (P : Program) (d : Nat)
    (hcall : ∀ n neg, EvalOK P (R000.norm neg (R000.unfoldN P d (.call n)))
      fun ctx m => eval P d neg (.call n) ctx m) :
    ∀ e neg, EvalOK P (R000.norm neg (R000.unfoldN P d e)) fun ctx m => eval P d neg e ctx m := by
  intro e
  induction e with
  | zero =>
    intro neg ctx m hm
    rw [R000.unfoldN_zero]
    show GoodS _ _ (eval P d neg .zero ctx m).val.1 ∧ MemoOK P (eval P d neg .zero ctx m).val.2
    rw [eval]
    exact ⟨goodS_zero _, hm⟩
  | span s =>
    intro neg ctx m hm
    rw [R000.unfoldN_span]
    show GoodS _ _ (eval P d neg (.span s) ctx m).val.1 ∧
      MemoOK P (eval P d neg (.span s) ctx m).val.2
    rw [eval]
    exact ⟨goodS_span ctx _, hm⟩
  | or a b iha ihb =>
    intro neg ctx m hm
    show GoodS _ _ (eval P d neg (.or a b) ctx m).val.1 ∧
      MemoOK P (eval P d neg (.or a b) ctx m).val.2
    rw [eval]
    refine memo_ok ⟨neg, .or a b, d, ctx⟩ _ (fun m hm => ?_) hm
    show GoodS (R000.norm neg (R000.unfoldN P d (.or a b))) (rng ctx) _ ∧ _
    rw [R000.unfoldN_or, R000.norm]
    obtain ⟨hx, hmx⟩ := iha neg ctx m hm
    obtain ⟨hy, hmy⟩ := ihb neg ctx _ hmx
    simp only [bind_val, pure_val]
    exact ⟨goodS_or hx hy, hmy⟩
  | seq a b iha ihb =>
    intro neg ctx m hm
    show GoodS _ _ (eval P d neg (.seq a b) ctx m).val.1 ∧
      MemoOK P (eval P d neg (.seq a b) ctx m).val.2
    cases neg
    · rw [eval]
      refine memo_ok ⟨false, .seq a b, d, ctx⟩ _ (fun m hm => ?_) hm
      show GoodS (R000.norm false (R000.unfoldN P d (.seq a b))) (rng ctx) _ ∧ _
      rw [R000.unfoldN_seq, R000.norm]
      obtain ⟨hx, hmx⟩ := iha false ctx m hm
      simp only [bind_val]
      exact seqSummary_ok (R000.norm_ne_nil _ false) (R000.norm_ne_nil _ false) (ihb false) ctx
        hx hmx
    · rw [eval]
      refine memo_ok ⟨true, .seq a b, d, ctx⟩ _ (fun m hm => ?_) hm
      show GoodS (R000.norm true (R000.unfoldN P d (.seq a b))) (rng ctx) _ ∧ _
      rw [R000.unfoldN_seq, R000.norm]
      obtain ⟨hx, hmx⟩ := ihb true ctx m hm
      simp only [bind_val]
      exact seqSummary_ok (R000.norm_ne_nil _ true) (R000.norm_ne_nil _ true) (iha true) ctx
        hx hmx
  | and a b iha ihb =>
    intro neg ctx m hm
    show GoodS _ _ (eval P d neg (.and a b) ctx m).val.1 ∧
      MemoOK P (eval P d neg (.and a b) ctx m).val.2
    rw [eval]
    refine memo_ok ⟨neg, .and a b, d, ctx⟩ _ (fun m hm => ?_) hm
    show GoodS (R000.norm neg (R000.unfoldN P d (.and a b))) (rng ctx) _ ∧ _
    rw [R000.unfoldN_and, R000.norm]
    obtain ⟨hx, hmx⟩ := iha neg none m hm
    obtain ⟨hy, hmy⟩ := ihb neg none _ hmx
    simp only [bind_val, pure_val]
    exact ⟨goodS_and ctx hx hy, hmy⟩
  | conv a iha =>
    intro neg ctx m hm
    show GoodS _ _ (eval P d neg (.conv a) ctx m).val.1 ∧
      MemoOK P (eval P d neg (.conv a) ctx m).val.2
    rw [eval, R000.unfoldN_conv, R000.norm]
    exact iha (!neg) ctx m hm
  | call n => exact hcall n

/-- The invariant of the shared evaluation: the summary describes the normal
form of the unfolding, and every entry of the memo stays right. -/
theorem eval_ok (P : Program) : ∀ (d : Nat) (e : Rel) (neg : Bool),
    EvalOK P (R000.norm neg (R000.unfoldN P d e)) fun ctx m => eval P d neg e ctx m := by
  intro d
  induction d with
  | zero =>
    refine eval_step P 0 fun n neg ctx m hm => ?_
    show GoodS _ _ (eval P 0 neg (.call n) ctx m).val.1 ∧
      MemoOK P (eval P 0 neg (.call n) ctx m).val.2
    rw [eval]
    refine ⟨goodS_call _ _ fun s hs => ?_, hm⟩
    cases neg <;> cases hs
  | succ d ih =>
    refine eval_step P (d + 1) fun n neg ctx m hm => ?_
    show GoodS _ _ (eval P (d + 1) neg (.call n) ctx m).val.1 ∧
      MemoOK P (eval P (d + 1) neg (.call n) ctx m).val.2
    rw [eval]
    refine memo_ok ⟨neg, .call n, d + 1, ctx⟩ _ (fun m hm => ?_) hm
    exact ih (P.body n) neg ctx m hm

/-! ## The race -/

/-- The shared evaluation computes R001's unfolding race, without the
repeats. -/
theorem shared_exact : Obligation.shared_exact := by
  intro P d g
  obtain ⟨⟨hs, ho⟩, -⟩ := eval_ok P d g.rel false none [] (memoOK_nil P)
  have hfin : (eval P d false g.rel none []).val.1.opens.isEmpty = R001.unfoldFinal P d g := by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, ← ranges_eq_empty, ho]
    exact (all_callFree_iff _ false).symm
  unfold shared
  simp only [bind_val]
  rw [hfin]
  unfold R001.unfoldAnswers
  cases hf : R001.unfoldFinal P d g with
  | false => rfl
  | true =>
    have hall : ∀ p ∈ R000.products P g.rel d, single p ≠ none := by
      have hempty := (all_callFree_iff (R000.unfoldN P d g.rel) false).mp hf
      intro p hp hsp
      have : rng (lastSpan p) ∈ OpenR (R000.norm false (R000.unfoldN P d g.rel)) Set.univ :=
        ⟨p, hp, hsp, headOK_univ p, rfl⟩
      rw [hempty] at this
      exact this
    have hspans : (eval P d false g.rel none []).val.1.spans =
        firsts (R000.roundSpans P g.rel d) := by
      rw [hs, R000.roundSpans, derivs_of_closed _ hall]
      congr 1
      exact List.filter_eq_self.mpr fun x _ => aliveB_iff.mpr (aliveP_univ x)
    simp only [↓reduceIte, bind_val, pure_val, flatMapL_val, Tabled.live_val, foldSpan_val,
      Prod.mk.injEq, true_and]
    rw [hspans, ← firsts_eq_eraseDups]
    exact addAll_flatMap_firsts [] _ _

end R003

end RwLog
