/-
# Whether every member of a conjunction of sorts is in a sort, on the store

`sorts::out` goes through the keys the pair of the conjunction with the sort
reaches (`Sorts.ReachG`): pairs of a conjunction with a sort, and
conjunctions alone, of which only whether they have a member is asked. For
each it keeps its alternatives, and then marks in rounds the keys that hold
(`Sorts.TrueG`). `out_spec` says it answers whether the conjunction has a
member outside the sort (`Sorts.Out`), and `included_spec` whether it has
none (`Sorts.Incl`), and what they spend in terms of the number of keys
reached.

Table `B` flags the keys reached, and table `A` then the keys that hold.
-/
import RwLogVerified.Live
import RwLog.Sorts.ReachOut

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## Keys as the store has them -/

/-- A key: a conjunction with a sort or with none. -/
abbrev Key := Sorts.OutKey

/-- A key as the store has it: the conjunction with the sort, or with the end
of a list. -/
noncomputable def keyPat (z : Sym) (U : List Name) (p : Key) : Pat :=
  .app (cpat z U p.1) (kidPat z p.2)

/-- The conjunction of a key is of names of the list, and its sort is not
the end of a list. -/
def KeyOK (z : Sym) (U : List Name) (p : Key) : Prop := Sub U p.1 ∧ ∀ m, p.2 = some m → m ≠ z

theorem kidPat_inj {z : Sym} {a b : Option Name} (ha : ∀ m, a = some m → m ≠ z)
    (hb : ∀ m, b = some m → m ≠ z) (h : kidPat z a = kidPat z b) : a = b := by
  cases a <;> cases b <;> simp only [kidPat, Term.sym.injEq] at h
  · rfl
  · exact absurd h.symm (hb _ rfl)
  · exact absurd h (ha _ rfl)
  · rw [h]

theorem keyPat_patInj (z : Sym) (U : List Name) : PatInj (keyPat z U) (KeyOK z U) := by
  rintro ⟨c, k⟩ ⟨d, l⟩ ⟨hc, hk⟩ ⟨hd, hl⟩ h
  simp only [keyPat, Term.app.injEq] at h
  have e1 : c = d := cpat_inj hc hd h.1
  have e2 : k = l := kidPat_inj hk hl h.2
  rw [e1, e2]

/-- A list of keys as the store has it. -/
noncomputable def keysPat (z : Sym) (U : List Name) (l : List Key) : Pat :=
  encList z (l.map (keyPat z U))

/-! ## The pairs of a list with the end of a list -/

theorem bare_loop_spec : ∀ (ps acc : List Pat) (s : store.Store) (args nil out : store.TermId),
    Wf s → Repr nm s.nodes.val args.val (encList (nm none) ps) →
    Repr nm s.nodes.val nil.val (.sym (nm none)) →
    Repr nm s.nodes.val out.val (encList (nm none) acc) → Room s (3 * ps.length + 1) →
    sorts.bare_loop args s nil out ⦃ r s' =>
      Ran s s' (3 * ps.length + 1) ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) ((ps.map fun p => (.app p (.sym (nm none)) : Pat)).reverse ++ acc)) ⦄ := by
  intro ps
  induction ps with
  | nil =>
    intro acc s args nil out hW ha hn ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.bare_loop
    rw [loop]
    simp only [sorts.bare_loop.body]
    step with uncons_repr s args hW ha (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    subst hu
    have hfin : Ran s s1 (3 * ([] : List Pat).length + 1) ∧ Repr nm s1.nodes.val out.val
        (encList (nm none) ((([] : List Pat).map fun p => (.app p (.sym (nm none)) : Pat)).reverse
          ++ acc)) :=
      ⟨hK.ran, by rw [hK.nodes]; simpa using ho⟩
    step*
  | cons p ps ih =>
    intro acc s args nil out hW ha hn ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.bare_loop
    rw [loop]
    simp only [sorts.bare_loop.body]
    step with uncons_repr s args hW ha (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    obtain ⟨a, t, rfl, ra, rt⟩ := hu
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    step with alloc_w s1 (.App a nil) hK.wf ⟨by rw [hn1]; exact ra.lt, by rw [hn1]; exact hn.lt⟩
      (by unfold Room; omega) as ⟨r2, hW2, ht2, htb2, hx2, hid2, hst2⟩
    obtain ⟨p1, s2⟩ := r2
    simp only at hW2 ht2 htb2 hx2 hid2 hst2
    have hx02 : Extends s s2 := hK.ran.ext.trans hx2
    have rp1 : Repr nm s2.nodes.val p1.val (.app p (.sym (nm none))) :=
      .app hid2 (hx02.repr ra) (hx02.repr hn)
    step with alloc_w s2 (.App p1 out) hW2 ⟨rp1.lt, (hx02.repr ho).lt⟩
      (by unfold Room; omega) as ⟨r3, hW3, ht3, htb3, hx3, hid3, hst3⟩
    obtain ⟨out1, s3⟩ := r3
    simp only at hW3 ht3 htb3 hx3 hid3 hst3
    have hx03 : Extends s s3 := hx02.trans hx3
    have R3 : Ran s s3 3 :=
      ⟨hW3, hx03, by rw [htb3, htb2, hK.tbl], by rw [hst3, hst2, hK.stk], by omega⟩
    have ro : Repr nm s3.nodes.val out1.val
        (encList (nm none) ((.app p (.sym (nm none)) : Pat) :: acc)) :=
      .app hid3 (hx3.repr rp1) (hx03.repr ho)
    have IH := ih (.app p (.sym (nm none)) :: acc) s3 t nil out1 hW3 (hx03.repr rt) (hx03.repr hn) ro
      (by unfold Room; omega)
    unfold sorts.bare_loop at IH
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r, s'⟩ ⟨hR, hr⟩
    refine ⟨(R3.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
    simpa using hr

/-- The pairs of the conjunctions of a list with no sort, the first last. -/
def bareKeys (a : List Sorts.Conj) : List Key := (a.map fun c => (c, none)).reverse

theorem bare_spec {U : List Name} (a : List Sorts.Conj) (s : store.Store) (args : store.TermId)
    (hW : Wf s) (ha : Repr nm s.nodes.val args.val (altPat (nm none) U a))
    (hroom : Room s (3 * a.length + 2)) :
    sorts.bare s args ⦃ r s' =>
      Ran s s' (3 * a.length + 2) ∧
        Repr nm s'.nodes.val r.val (keysPat (nm none) U (bareKeys a)) ⦄ := by
  unfold sorts.bare
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨nil, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have R1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  have rn : Repr nm s1.nodes.val nil.val (.sym (nm none)) := .nil hid
  refine WP.spec_mono (bare_loop_spec (a.map (cpat (nm none) U)) [] s1 args nil nil hW1
    (hx1.repr ha) rn rn (by simp only [List.length_map]; unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  simp only [List.length_map] at hR
  refine ⟨(R1.trans hR).mono (by omega), ?_⟩
  simpa [keysPat, bareKeys, keyPat, kidPat, Function.comp_def] using hr

/-! ## The pairs of a list with the sorts asked of its members -/

/-- The pairs of the patterns with the sorts at their places, where there is
one. -/
def pairPats : List Pat → List (Option Name) → List Pat
  | p :: ps, some m :: ks => .app p (.sym m) :: pairPats ps ks
  | _ :: ps, none :: ks => pairPats ps ks
  | _, _ => []

theorem pair_up_loop_spec (hnm : Function.Injective nm) :
    ∀ (ps : List Pat) (ks : List (Option Name)) (acc : List Pat) (s : store.Store)
      (args out kids : store.TermId),
    Wf s → Repr nm s.nodes.val args.val (encList (nm none) ps) →
    Repr nm s.nodes.val kids.val (encList (nm none) (ks.map (kidPat (nm none)))) →
    ps.length = ks.length → (∀ m, some m ∈ ks → m ≠ nm none) →
    Repr nm s.nodes.val out.val (encList (nm none) acc) → Room s (5 * ps.length + 1) →
    sorts.pair_up_loop args s out kids ⦃ r s' =>
      Ran s s' (5 * ps.length + 1) ∧
        Repr nm s'.nodes.val r.val (encList (nm none) ((pairPats ps ks).reverse ++ acc)) ⦄ := by
  intro ps
  induction ps with
  | nil =>
    intro ks acc s args out kids hW ha hk hlen hz ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.pair_up_loop
    rw [loop]
    simp only [sorts.pair_up_loop.body]
    step with uncons_repr s args hW ha (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    subst hu
    have hfin : Ran s s1 (5 * ([] : List Pat).length + 1) ∧ Repr nm s1.nodes.val out.val
        (encList (nm none) ((pairPats [] ks).reverse ++ acc)) :=
      ⟨hK.ran, by rw [hK.nodes]; simpa [pairPats] using ho⟩
    step*
  | cons p ps ih =>
    intro ks acc s args out kids hW ha hk hlen hz ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    obtain _ | ⟨k0, ks⟩ := ks
    · simp at hlen
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    unfold sorts.pair_up_loop
    rw [loop]
    simp only [sorts.pair_up_loop.body]
    step with uncons_repr s args hW ha (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    obtain ⟨a, ta, rfl, ra, rta⟩ := hu
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    step with uncons_repr s1 kids hK.wf (by rw [hn1]; exact hk) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hK2
    obtain ⟨k, tk, rfl, rk, rtk⟩ := hu2
    rw [hn1] at rk rtk
    have ht2 := hK2.ticks
    have R2 := hK.ran.trans hK2.ran
    have hk0 : ∀ m, k0 = some m → m ≠ nm none := fun m e => hz m (by rw [e]; exact List.mem_cons_self)
    have hz' : ∀ m, some m ∈ ks → m ≠ nm none := fun m hm => hz m (List.mem_cons_of_mem _ hm)
    step with is_nil_kid hnm s2 k hK2.wf (R2.ext.repr rk) hk0 (by unfold Room; omega)
      as ⟨r3, hb, hK3⟩
    obtain ⟨b, s3⟩ := r3
    simp only at hb hK3 ⊢
    have ht3 := hK3.ticks
    have R3 := R2.trans hK3.ran
    cases k0 with
    | none =>
      rw [show b = true from hb.2 rfl]
      simp only [uncurry, ↓reduceIte, bind_ok]
      have IH := ih ks acc s3 ta out tk R3.wf (R3.ext.repr rta) (R3.ext.repr rtk) hlen hz'
        (R3.ext.repr ho) (by unfold Room; omega)
      unfold sorts.pair_up_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hr⟩
      exact ⟨(R3.trans hR).mono (by simp only [List.length_cons]; omega), by simpa [pairPats] using hr⟩
    | some m =>
      have hbf : b = false := by
        cases b
        · rfl
        · exact absurd (hb.1 rfl) (by simp)
      rw [hbf]
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
      simp only [kidPat] at rk
      step with alloc_w s3 (.App a k) R3.wf ⟨(R3.ext.repr ra).lt, (R3.ext.repr rk).lt⟩
        (by unfold Room; omega) as ⟨r4, hW4, ht4, htb4, hx4, hid4, hst4⟩
      obtain ⟨p1, s4⟩ := r4
      simp only at hW4 ht4 htb4 hx4 hid4 hst4
      have hx04 : Extends s s4 := R3.ext.trans hx4
      have rp1 : Repr nm s4.nodes.val p1.val (.app p (.sym m)) :=
        .app hid4 (hx04.repr ra) (hx04.repr rk)
      step with alloc_w s4 (.App p1 out) hW4 ⟨rp1.lt, (hx04.repr ho).lt⟩
        (by unfold Room; omega) as ⟨r5, hW5, ht5, htb5, hx5, hid5, hst5⟩
      obtain ⟨out1, s5⟩ := r5
      simp only at hW5 ht5 htb5 hx5 hid5 hst5
      have hx05 : Extends s s5 := hx04.trans hx5
      have R5 : Ran s s5 5 :=
        ⟨hW5, hx05, by rw [htb5, htb4, R3.tbl], by rw [hst5, hst4, R3.stk], by
          have := R3.ticks; omega⟩
      have ro : Repr nm s5.nodes.val out1.val (encList (nm none) ((.app p (.sym m) : Pat) :: acc)) :=
        .app hid5 (hx5.repr rp1) (hx05.repr ho)
      have IH := ih ks (.app p (.sym m) :: acc) s5 ta out1 tk hW5 (hx05.repr rta) (hx05.repr rtk)
        hlen hz' ro (by unfold Room; omega)
      unfold sorts.pair_up_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hr⟩
      exact ⟨(R5.trans hR).mono (by simp only [List.length_cons]; omega), by simpa [pairPats] using hr⟩

/-- The pairs of the conjunctions with the sorts at their places, where
there is one; the first last. -/
def pairKeys : List Sorts.Conj → List (Option Name) → List Key
  | c :: cs, some m :: ks => pairKeys cs ks ++ [(c, some m)]
  | _ :: cs, none :: ks => pairKeys cs ks
  | _, _ => []

theorem pairKeys_pat (z : Sym) (U : List Name) : ∀ (a : List Sorts.Conj) (ks : List (Option Name)),
    (pairKeys a ks).map (keyPat z U) = (pairPats (a.map (cpat z U)) ks).reverse
  | [], _ => by simp [pairKeys, pairPats]
  | _ :: _, [] => by simp [pairKeys, pairPats]
  | c :: cs, none :: ks => by simpa [pairKeys, pairPats] using pairKeys_pat z U cs ks
  | c :: cs, some m :: ks => by
    simp [pairKeys, pairPats, pairKeys_pat z U cs ks, keyPat, kidPat]

theorem mem_pairKeys {a : List Sorts.Conj} {ks : List (Option Name)} {q : Key} :
    q ∈ pairKeys a ks ↔ ∃ i, ∃ h : i < a.length, ∃ m, ks[i]? = some (some m) ∧ q = (a[i], some m) := by
  induction a generalizing ks with
  | nil => simp [pairKeys]
  | cons c cs ih =>
    cases ks with
    | nil => simp [pairKeys]
    | cons k ks =>
      cases k with
      | none =>
        simp only [pairKeys, ih, List.length_cons]
        constructor
        · rintro ⟨i, h, m, hk, rfl⟩
          exact ⟨i + 1, by omega, m, by simpa using hk, by simp⟩
        · rintro ⟨i, h, m, hk, rfl⟩
          cases i with
          | zero => simp at hk
          | succ i => exact ⟨i, by omega, m, by simpa using hk, by simp⟩
      | some m' =>
        simp only [pairKeys, List.mem_append, ih, List.mem_singleton, List.length_cons]
        constructor
        · rintro (⟨i, h, m, hk, rfl⟩ | rfl)
          · exact ⟨i + 1, by omega, m, by simpa using hk, by simp⟩
          · exact ⟨0, by omega, m', by simp, by simp⟩
        · rintro ⟨i, h, m, hk, rfl⟩
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
            subst hk
            exact Or.inr (by simp)
          | succ i => exact Or.inl ⟨i, by omega, m, by simpa using hk, by simp⟩

theorem pair_up_spec (hnm : Function.Injective nm) {U : List Name} (a : List Sorts.Conj)
    (ks : List (Option Name)) (s : store.Store) (args kids : store.TermId) (hW : Wf s)
    (ha : Repr nm s.nodes.val args.val (altPat (nm none) U a))
    (hk : Repr nm s.nodes.val kids.val (encList (nm none) (ks.map (kidPat (nm none)))))
    (hlen : a.length = ks.length) (hz : ∀ m, some m ∈ ks → m ≠ nm none)
    (hroom : Room s (5 * a.length + 2)) :
    sorts.pair_up s args kids ⦃ r s' =>
      Ran s s' (5 * a.length + 2) ∧
        Repr nm s'.nodes.val r.val (keysPat (nm none) U (pairKeys a ks)) ⦄ := by
  unfold sorts.pair_up
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨nil, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have R1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  refine WP.spec_mono (pair_up_loop_spec hnm (a.map (cpat (nm none) U)) ks [] s1 args nil kids hW1
    (hx1.repr ha) (hx1.repr hk) (by simpa using hlen) hz (.nil hid)
    (by simp only [List.length_map]; unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  simp only [List.length_map] at hR
  refine ⟨(R1.trans hR).mono (by omega), ?_⟩
  simpa [keysPat, pairKeys_pat] using hr

/-! ## The sorts the rests of a conjunction ask of arguments -/

theorem rest_kids_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (hz : ∀ m ∈ Sorts.names S, m ≠ nm none) :
    ∀ (xs acc : List Name) (s : store.Store) (c decls list : store.TermId),
    Wf s → Repr nm s.nodes.val decls.val sp → Repr nm s.nodes.val c.val (namesPat (nm none) xs) →
    Repr nm s.nodes.val list.val (namesPat (nm none) acc) →
    Room s (xs.length * (3 * S.length + 6) + 1) →
    sorts.rest_kids_loop c s decls list ⦃ r =>
      Ran s r.1 (xs.length * (3 * S.length + 6) + 1) ∧
        Repr nm r.1.nodes.val r.2.val
          (namesPat (nm none) ((xs.filterMap (Sorts.restKid S)).reverse ++ acc)) ⦄ := by
  intro xs
  induction xs with
  | nil =>
    intro acc s c decls list hW hd hc hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.rest_kids_loop
    rw [loop]
    simp only [sorts.rest_kids_loop.body]
    step with uncons_repr s c hW hc (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    subst hu
    have hfin : Ran s s1 (([] : List Name).length * (3 * S.length + 6) + 1) ∧
        Repr nm s1.nodes.val list.val
          (namesPat (nm none) ((([] : List Name).filterMap (Sorts.restKid S)).reverse ++ acc)) :=
      ⟨hK.ran.mono (by simp), by rw [hK.nodes]; simpa using hl⟩
    step*
  | cons x xs ih =>
    intro acc s c decls list hW hd hc hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    unfold sorts.rest_kids_loop
    rw [loop]
    simp only [sorts.rest_kids_loop.body]
    step with uncons_repr s c hW hc (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    obtain ⟨n, t, rfl, rn, rt⟩ := hu
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    step with lookup_spec hnm S hS s1 decls n hK.wf (by rw [hn1]; exact hd) (by rw [hn1]; exact rn)
      (by unfold Room; omega) as ⟨r1, hR2, hlk⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hR2 hlk
    have ht2 := hR2.ticks
    have R2 : Ran s s2 (3 * S.length + 3) := (hK.ran.trans hR2).mono (by omega)
    -- the rest of the list
    have rest : ∀ (s' : store.Store) (list' : store.TermId) (acc' : List Name),
        Ran s s' (3 * S.length + 6) → Repr nm s'.nodes.val list'.val (namesPat (nm none) acc') →
        ((xs.filterMap (Sorts.restKid S)).reverse ++ acc' =
          ((x :: xs).filterMap (Sorts.restKid S)).reverse ++ acc) →
        loop (fun x => match x with
          | (c1, s1, list1) => sorts.rest_kids_loop.body decls c1 s1 list1) (t, s', list') ⦃ r =>
          Ran s r.1 ((x :: xs).length * (3 * S.length + 6) + 1) ∧
            Repr nm r.1.nodes.val r.2.val
              (namesPat (nm none) (((x :: xs).filterMap (Sorts.restKid S)).reverse ++ acc)) ⦄ := by
      intro s' list' acc' R0 hl' he
      have := R0.ticks
      have IH := ih acc' s' t decls list' R0.wf (R0.ext.repr hd) (R0.ext.repr rt) hl'
        (by unfold Room; omega)
      unfold sorts.rest_kids_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R0.trans hR).mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega), ?_⟩
      rw [← he]; exact hr
    cases hd' : S.lookup x with
    | none =>
      rw [hd'] at hlk
      subst hlk
      have hrk : Sorts.restKid S x = none := by simp [Sorts.restKid, hd']
      simp only [uncurry, bind_ok]
      exact rest s2 list acc (R2.mono (by omega)) (R2.ext.repr hl) (by simp [hrk])
    | some dd =>
      rw [hd'] at hlk
      obtain ⟨cc, r, rp, rfl, -, rr, hrest⟩ := hlk
      simp only [uncurry]
      step with uncons_repr s2 r hR2.wf (hR2.ext.repr rr) (by unfold Room; omega) as ⟨r3, hK3, hu3⟩
      obtain ⟨o3, s3⟩ := r3
      simp only at hK3
      have ht3 := hK3.ticks
      have R3 : Ran s s3 (3 * S.length + 4) := (R2.trans hK3.ran).mono (by omega)
      cases hre : dd.rest with
      | none =>
        rw [hre] at hrest
        simp only [RestAt] at hrest
        subst hrest
        simp only at hu3
        subst hu3
        have hrk : Sorts.restKid S x = none := by simp [Sorts.restKid, hd', hre]
        simp only [uncurry, bind_ok]
        exact rest s3 list acc (R3.mono (by omega)) (R3.ext.repr hl) (by simp [hrk])
      | some er =>
        obtain ⟨ex, k⟩ := er
        rw [hre] at hrest
        simp only [RestAt] at hrest
        obtain ⟨es, -, rfl⟩ := hrest
        simp only at hu3
        obtain ⟨e, rk, rfl, -, rrk⟩ := hu3
        have hrk : Sorts.restKid S x = k := by simp [Sorts.restKid, hd', hre]
        have hk0 : ∀ m, k = some m → m ≠ nm none := fun m e =>
          hz m (Sorts.restKid_mem_names (n := x) (by rw [hrk, e]))
        simp only [uncurry]
        step with is_nil_kid hnm s3 rk hK3.wf (by rw [hK3.nodes]; exact rrk) hk0
          (by unfold Room; omega) as ⟨r4, hb, hK4⟩
        obtain ⟨b, s4⟩ := r4
        simp only at hb hK4 ⊢
        have ht4 := hK4.ticks
        have R4 : Ran s s4 (3 * S.length + 5) := (R3.trans hK4.ran).mono (by omega)
        cases k with
        | none =>
          rw [show b = true from hb.2 rfl]
          simp only [uncurry, ↓reduceIte, bind_ok]
          exact rest s4 list acc (R4.mono (by omega)) (R4.ext.repr hl) (by simp [hrk])
        | some m =>
          have hbf : b = false := by
            cases b
            · rfl
            · exact absurd (hb.1 rfl) (by simp)
          rw [hbf]
          simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
          simp only [kidPat] at rrk
          have rrk4 : Repr nm s4.nodes.val rk.val (.sym m) := by
            rw [hK4.nodes, hK3.nodes]; exact rrk
          step with alloc_w s4 (.App rk list) R4.wf ⟨rrk4.lt, (R4.ext.repr hl).lt⟩
            (by unfold Room; omega) as ⟨r5, hW5, ht5, htb5, hx5, hid5, hst5⟩
          obtain ⟨list1, s5⟩ := r5
          simp only at hW5 ht5 htb5 hx5 hid5 hst5
          have R5 : Ran s s5 (3 * S.length + 6) :=
            ⟨hW5, R4.ext.trans hx5, by rw [htb5, R4.tbl], by rw [hst5, R4.stk], by
              have := R4.ticks; omega⟩
          have rl : Repr nm s5.nodes.val list1.val (namesPat (nm none) (m :: acc)) := by
            simp only [namesPat, List.map_cons, encList]
            exact .app hid5 (hx5.repr rrk4) (R5.ext.repr hl)
          simp only [uncurry, bind_ok]
          exact rest s5 list1 (m :: acc) R5 rl (by simp [hrk])

/-- What going through the rests of a conjunction may spend. -/
def restKidsCost (S : Sorts) (u : Nat) : Nat := u * (3 * S.length + 11) + 6

theorem rest_kids_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (hz : ∀ m ∈ Sorts.names S, m ≠ nm none) {U : List Name}
    (d : Sorts.Conj) (hd : Sub U d) (s : store.Store) (decls names ci : store.TermId) (hW : Wf s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (hroom : Room s (restKidsCost S U.length)) :
    sorts.rest_kids s decls names ci ⦃ r s' =>
      RanA s s' (restKidsCost S U.length) ∧
        Repr nm s'.nodes.val r.val (cpat (nm none) U (Sorts.restKids S d)) ⦄ := by
  unfold sorts.rest_kids
  have hroom' := hroom
  unfold Room restKidsCost at hroom'
  have hlen := length_conjList_le U (· ∈ d)
  have hmul := Nat.mul_le_mul_right (3 * S.length + 6) hlen
  have hfl : ((conjList U (· ∈ d)).filterMap (Sorts.restKid S)).length ≤ U.length :=
    Nat.le_trans (List.length_filterMap_le _ _) hlen
  simp only [Nat.mul_add] at hroom' hmul
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨nil, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have R1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  step with rest_kids_loop_spec hnm S hS hz (conjList U (· ∈ d)) [] s1 ci decls nil hW1
    (hx1.repr hde) (hx1.repr hci) (by simpa [namesPat, encList] using (Repr.nil hid : Repr nm _ _ _))
    (by unfold Room; simp only [Nat.mul_add]; omega) as ⟨s2, list1, hR2, hr2⟩
  simp only [List.append_nil] at hr2
  have ht2 := hR2.ticks
  have R2 := R1.trans hR2
  refine WP.spec_mono (conj_of_spec hnm U _ s2 names list1 hR2.wf (R2.ext.repr hU) hr2
    (by simp only [List.length_reverse]; unfold Room; simp only [Nat.mul_add] at ht2 ⊢; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  simp only [List.length_reverse] at hR
  refine ⟨(R2.ranA.trans hR).mono (by unfold restKidsCost; simp only [Nat.mul_add]; omega), ?_⟩
  simp only [cpat]
  rw [conjList_congr (G := fun n => n ∈ (List.filterMap (Sorts.restKid S)
    (conjList U (· ∈ d))).reverse)]
  · exact hr
  · intro n _
    simp only [List.mem_reverse, List.mem_filterMap, mem_conjList, Sorts.mem_restKids,
      Sorts.restKid_eq]
    constructor
    · rintro ⟨x, hx, dd, ex, h1, h2⟩
      exact ⟨x, ⟨hd x hx, hx⟩, dd, ex, h1, h2⟩
    · rintro ⟨x, ⟨-, hx⟩, dd, ex, h1, h2⟩
      exact ⟨x, hx, dd, ex, h1, h2⟩

/-! ## The alternatives the roots of a list give a key -/

/-- Table `B` flags the keys as `m` says. -/
abbrev FlagsK (nm : Option Nat → RwLog.Sym) (s : store.Store) (U : List Name)
    (m : Key → Option Bool) : Prop :=
  Flags nm s .B (keyPat (nm none) U) (KeyOK (nm none) U) m

/-- A list of lists of keys as the store has it. -/
noncomputable def nowsPat (z : Sym) (U : List Name) (l : List (List Key)) : Pat :=
  encList z (l.map (keysPat z U))

/-- Guards and edges. -/
abbrev Step := List Key × List Key

noncomputable def stepPat (z : Sym) (U : List Name) (a : Step) : Pat :=
  .app (keysPat z U a.1) (keysPat z U a.2)

noncomputable def stepsPat (z : Sym) (U : List Name) (l : List Step) : Pat :=
  encList z (l.map (stepPat z U))

/-- The guards of the roots of a list that the conjunction accepts and the
sort has no step at. -/
def keyNows (S : Sorts) (d : Sorts.Conj) (μ : Name) : List (Sym × Nat) → List (List Key)
  | [] => []
  | k :: K =>
    (if Sorts.Accepts S d k.1 k.2 ∧ Sorts.step S μ k.1 k.2 = none then
      [bareKeys (altOf S d k.1 k.2)] else []) ++ keyNows S d μ K

/-- The guards and edges of the roots of a list that the conjunction accepts
and the sort has a step at. -/
def keySteps (S : Sorts) (d : Sorts.Conj) (μ : Name) : List (Sym × Nat) → List Step
  | [] => []
  | k :: K =>
    (if Sorts.Accepts S d k.1 k.2 then
      match Sorts.step S μ k.1 k.2 with
      | some kids => [(bareKeys (altOf S d k.1 k.2), pairKeys (altOf S d k.1 k.2) kids)]
      | none => []
    else []) ++ keySteps S d μ K

/-- The ticks going through the roots of a list may spend. -/
def keysWork (S : Sorts) (u : Nat) : List (Sym × Nat) → Nat
  | [] => 1
  | k :: K => stepConjCost S u u k.2 + stepCost S k.2 + 16 * k.2 + 10 + keysWork S u K

theorem length_pairKeys_le : ∀ (a : List Sorts.Conj) (ks : List (Option Name)),
    (pairKeys a ks).length ≤ a.length
  | [], _ => by simp [pairKeys]
  | _ :: _, [] => by simp [pairKeys]
  | _ :: cs, none :: ks => by
    have := length_pairKeys_le cs ks
    simp only [pairKeys, List.length_cons]; omega
  | _ :: cs, some _ :: ks => by
    have := length_pairKeys_le cs ks
    simp only [pairKeys, List.length_append, List.length_cons, List.length_nil]; omega

theorem expand_keys_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (k : Option Name) (μ : Name) (hd : Sub U d)
    (hμ : ∀ f a, Sorts.step S μ f a ≠ none → k = some μ) :
    ∀ (es : List (Sym × List Pat)) (s : store.Store)
      (keys decls names ci mi nows steps todo : store.TermId) (accN : List (List Key))
      (accS : List Step) (T : List Key) (m : Key → Option Bool), Inv s → FlagsK nm s U m →
    (∀ e ∈ es, (e.1, e.2.length) ∈ Sorts.keysOf S (d, k)) →
    Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val ci.val (cpat (nm none) U d) →
    Repr nm s.nodes.val mi.val (.sym μ) →
    Repr nm s.nodes.val keys.val
      (encList (nm none) (es.map fun e => entPat (nm none) (.sym e.1, e.2))) →
    Repr nm s.nodes.val nows.val (nowsPat (nm none) U accN) →
    Repr nm s.nodes.val steps.val (stepsPat (nm none) U accS) →
    Repr nm s.nodes.val todo.val (keysPat (nm none) U T) →
    Room s (keysWork S U.length (es.map fun e => (e.1, e.2.length))) →
    sorts.expand_keys_loop keys s decls names ci mi nows steps todo ⦃ r => ∃ m' T',
      RanB s r.1 (keysWork S U.length (es.map fun e => (e.1, e.2.length))) ∧ FlagsK nm r.1 U m' ∧
        Repr nm r.1.nodes.val r.2.1.val (nowsPat (nm none) U
          ((keyNows S d μ (es.map fun e => (e.1, e.2.length))).reverse ++ accN)) ∧
        Repr nm r.1.nodes.val r.2.2.1.val (stepsPat (nm none) U
          ((keySteps S d μ (es.map fun e => (e.1, e.2.length))).reverse ++ accS)) ∧
        Repr nm r.1.nodes.val r.2.2.2.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ keyNows S d μ (es.map fun e => (e.1, e.2.length)), ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ keySteps S d μ (es.map fun e => (e.1, e.2.length)),
          (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
  intro es
  induction es with
  | nil =>
    intro s keys decls names ci mi nows steps todo accN accS T m hI hF hkeys hde hU hci hmi hks
      hnw hst htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.map_nil, keysWork] at hroom'
    unfold sorts.expand_keys_loop
    rw [loop]
    simp only [sorts.expand_keys_loop.body]
    step with uncons_repr s keys hI.toWf hks (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    have hfin : ∃ m' T', RanB s s1 (keysWork S U.length
          (([] : List (Sym × List Pat)).map fun e => (e.1, e.2.length))) ∧ FlagsK nm s1 U m' ∧
        Repr nm s1.nodes.val nows.val (nowsPat (nm none) U ((keyNows S d μ
          (([] : List (Sym × List Pat)).map fun e => (e.1, e.2.length))).reverse ++ accN)) ∧
        Repr nm s1.nodes.val steps.val (stepsPat (nm none) U ((keySteps S d μ
          (([] : List (Sym × List Pat)).map fun e => (e.1, e.2.length))).reverse ++ accS)) ∧
        Repr nm s1.nodes.val todo.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ keyNows S d μ (([] : List (Sym × List Pat)).map fun e => (e.1, e.2.length)),
          ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ keySteps S d μ (([] : List (Sym × List Pat)).map fun e => (e.1, e.2.length)),
          (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none :=
      ⟨m, T, hK.ran.ranB.mono (by simp [keysWork]), hF.mono hK.ran.ext (by rw [hK.tbl]),
        by rw [hK.nodes]; simpa [keyNows] using hnw, by rw [hK.nodes]; simpa [keySteps] using hst,
        by rw [hK.nodes]; exact htd, Enq.refl _ m T, fun _ h => (by simp [keyNows] at h),
        fun _ h => (by simp [keySteps] at h)⟩
    step*
  | cons x es ih =>
    intro s keys decls names ci mi nows steps todo accN accS T m hI hF hkeys hde hU hci hmi hks
      hnw hst htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.map_cons, keysWork] at hroom'
    have hW := hI.toWf
    unfold sorts.expand_keys_loop
    rw [loop]
    simp only [sorts.expand_keys_loop.body]
    step with uncons_repr s keys hW hks (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨kn, t, rfl, rkn, rt⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 kn hK.wf (by rw [hK.nodes]; exact rkn) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [entPat] at hu2
    simp only at hK2
    obtain ⟨f, ks, rfl, rf, rks⟩ := hu2
    rw [hK.nodes] at rf rks
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
    have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK.tbl]
    have R2 : Ran s s2 2 := hK.ran.trans hK2.ran
    have hI2 : Inv s2 := R2.ranB.inv hI
    step with step_conj_conj_spec hC.inj S hC.sorts (f := x.1) (ag := x.2)
      U d s2 decls names ci f ks hI2 (by rw [hn2]; exact hde) (by rw [hn2]; exact hU) hd
      (by rw [hn2]; exact hci) (by rw [hn2]; exact rf) (by rw [hn2]; exact rks)
      (fun n _ ks' hs m' hm' => hC.nz m' (step_kid_names hs hm'))
      (by unfold Room; omega) as ⟨r3, hI3, hx3, htb3, ht3, hres⟩
    obtain ⟨o2, s3⟩ := r3
    simp only at hI3 hx3 htb3 ht3 hres
    have R3 : RanB s s3 (stepConjCost S U.length U.length x.2.length + 2) :=
      ⟨hI3.toWf, R2.ext.trans hx3, by rw [hI3.empty, hI.empty], by have := R2.ticks; omega⟩
    have hF3 : FlagsK nm s3 U m := (hF.mono R2.ext (by rw [htb2])).mono hx3 htb3
    have hkeys' : ∀ e ∈ es, (e.1, e.2.length) ∈ Sorts.keysOf S (d, k) :=
      fun e he => hkeys e (List.mem_cons_of_mem _ he)
    have hkx : (x.1, x.2.length) ∈ Sorts.keysOf S (d, k) := hkeys x List.mem_cons_self
    -- the rest of the roots
    have rest : ∀ (s' : store.Store) (nows' steps' todo' : store.TermId)
        (accN' : List (List Key)) (accS' : List Step) (m₁ : Key → Option Bool) (T₁ : List Key),
        RanB s s' (stepConjCost S U.length U.length x.2.length + stepCost S x.2.length +
          16 * x.2.length + 10) →
        FlagsK nm s' U m₁ →
        Repr nm s'.nodes.val nows'.val (nowsPat (nm none) U accN') →
        Repr nm s'.nodes.val steps'.val (stepsPat (nm none) U accS') →
        Repr nm s'.nodes.val todo'.val (keysPat (nm none) U T₁) →
        Enq (Sorts.KidG S (d, k)) m m₁ T T₁ →
        ((keyNows S d μ (es.map fun e => (e.1, e.2.length))).reverse ++ accN' =
          (keyNows S d μ ((x :: es).map fun e => (e.1, e.2.length))).reverse ++ accN) →
        ((keySteps S d μ (es.map fun e => (e.1, e.2.length))).reverse ++ accS' =
          (keySteps S d μ ((x :: es).map fun e => (e.1, e.2.length))).reverse ++ accS) →
        (∀ g ∈ keyNows S d μ ((x :: es).map fun e => (e.1, e.2.length)),
          g ∈ keyNows S d μ (es.map fun e => (e.1, e.2.length)) ∨ ∀ q ∈ g, m₁ q ≠ none) →
        (∀ a ∈ keySteps S d μ ((x :: es).map fun e => (e.1, e.2.length)),
          a ∈ keySteps S d μ (es.map fun e => (e.1, e.2.length)) ∨
            ((∀ q ∈ a.1, m₁ q ≠ none) ∧ ∀ q ∈ a.2, m₁ q ≠ none)) →
        loop (fun x => match x with
          | (keys1, s1, nows1, steps1, todo1) =>
            sorts.expand_keys_loop.body decls names ci mi keys1 s1 nows1 steps1 todo1)
          (t, s', nows', steps', todo') ⦃ r => ∃ m' T',
          RanB s r.1 (keysWork S U.length ((x :: es).map fun e => (e.1, e.2.length))) ∧
            FlagsK nm r.1 U m' ∧
            Repr nm r.1.nodes.val r.2.1.val (nowsPat (nm none) U
              ((keyNows S d μ ((x :: es).map fun e => (e.1, e.2.length))).reverse ++ accN)) ∧
            Repr nm r.1.nodes.val r.2.2.1.val (stepsPat (nm none) U
              ((keySteps S d μ ((x :: es).map fun e => (e.1, e.2.length))).reverse ++ accS)) ∧
            Repr nm r.1.nodes.val r.2.2.2.val (keysPat (nm none) U T') ∧
            Enq (Sorts.KidG S (d, k)) m m' T T' ∧
            (∀ g ∈ keyNows S d μ ((x :: es).map fun e => (e.1, e.2.length)),
              ∀ q ∈ g, m' q ≠ none) ∧
            ∀ a ∈ keySteps S d μ ((x :: es).map fun e => (e.1, e.2.length)),
              (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
      intro s' nows' steps' todo' accN' accS' m₁ T₁ R0 hF' hnw' hst' htd' hE hN hSt hfN hfS
      have := R0.ticks
      have IH := ih s' t decls names ci mi nows' steps' todo' accN' accS' T₁ m₁ (R0.inv hI) hF'
        hkeys' (R0.ext.repr hde) (R0.ext.repr hU) (R0.ext.repr hci) (R0.ext.repr hmi)
        (R0.ext.repr rt) hnw' hst' htd' (by unfold Room; omega)
      unfold sorts.expand_keys_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨m', T', hR, hFm, hrn, hrs, hrt, hE', hallN, hallS⟩
      refine ⟨m', T', (R0.trans hR).mono (by simp only [List.map_cons, keysWork]; omega), hFm,
        by rw [← hN]; exact hrn, by rw [← hSt]; exact hrs, hrt, hE.trans hE', ?_, ?_⟩
      · intro g hg q hq
        rcases hfN g hg with h | h
        · exact hallN g h q hq
        · exact hE'.flagged (h q hq)
      · intro a ha
        rcases hfS a ha with h | h
        · exact hallS a h
        · exact ⟨fun q hq => hE'.flagged (h.1 q hq), fun q hq => hE'.flagged (h.2 q hq)⟩
    by_cases hacc : Sorts.Accepts S d x.1 x.2.length
    · simp only [hacc, ↓reduceIte] at hres
      obtain ⟨r, kids, rfl, hkl, rkids, hk⟩ := hres
      have hkids : kids = (altOf S d x.1 x.2.length).map (cpat (nm none) U) := by
        apply List.ext_getElem
        · simp [altOf, hkl]
        · intro i h₁ h₂
          obtain ⟨k', rk', ck'⟩ := hk i h₁
          simp only [altOf, List.getElem_map, List.getElem_range]
          exact rk'.unique ck'
      have rargs : Repr nm s3.nodes.val r.val (altPat (nm none) U (altOf S d x.1 x.2.length)) := by
        have := rkids
        rw [hkids] at this
        exact this
      have hlen2 : (altOf S d x.1 x.2.length).length = x.2.length := by simp [altOf]
      have hlenb : (bareKeys (altOf S d x.1 x.2.length)).length = x.2.length := by
        simp [bareKeys, altOf]
      simp only [uncurry]
      step with bare_spec (altOf S d x.1 x.2.length) s3 r hI3.toWf rargs
        (by rw [hlen2]; unfold Room; omega) as ⟨r4, hR4, rg⟩
      obtain ⟨guards, s4⟩ := r4
      simp only at hR4 rg
      rw [hlen2] at hR4
      have R4 := R3.trans hR4.ranB
      have hF4 : FlagsK nm s4 U m := hF3.mono hR4.ext (by rw [hR4.tbl])
      have hsG : ∀ q ∈ bareKeys (altOf S d x.1 x.2.length),
          KeyOK (nm none) U q ∧ Sorts.KidG S (d, k) q := by
        intro q hq
        simp only [bareKeys, List.mem_reverse, List.mem_map] at hq
        obtain ⟨c, hc, rfl⟩ := hq
        refine ⟨⟨altOf_sub hC d _ _ c hc, fun _ h => (by cases h)⟩, ?_⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
        exact Or.inl ⟨(x.1, x.2.length), hkx, hacc, i, List.mem_range.1 hi, rfl⟩
      step with enqueue_spec_gen hC.inj (keyPat_patInj (nm none) U)
        (bareKeys (altOf S d x.1 x.2.length)) s4 guards todo T m hR4.wf hF4 hsG rg
        (R4.ext.repr htd) (by rw [hlenb]; have := R4.ticks; unfold Room; omega)
        as ⟨r5, m₁, T₁, hR5, hF5, rtd5, hE5, hall5⟩
      obtain ⟨todo1, s5⟩ := r5
      simp only at hR5 hF5 rtd5
      rw [hlenb] at hR5
      have R5 := R4.trans hR5
      have ht5 := R5.ticks
      step with step_spec hC.inj S hC.sorts s5 decls mi f ks (n := μ) (f := x.1) (ag := x.2)
        hR5.wf (R5.ext.repr hde) (R5.ext.repr hmi) (R5.ext.repr rf) (R5.ext.repr rks)
        (by unfold Room; omega) as ⟨r6, hR6, hstp⟩
      obtain ⟨o3, s6⟩ := r6
      simp only at hR6 hstp
      have R6 := R5.trans hR6.ranB
      have ht6 := R6.ticks
      have hF6 : FlagsK nm s6 U m₁ := hF5.mono hR6.ext (by rw [hR6.tbl])
      have rg6 : Repr nm s6.nodes.val guards.val
          (keysPat (nm none) U (bareKeys (altOf S d x.1 x.2.length))) :=
        hR6.ext.repr (hR5.ext.repr rg)
      cases hsm : Sorts.step S μ x.1 x.2.length with
      | none =>
        rw [hsm] at hstp
        simp only at hstp
        subst hstp
        simp only [uncurry]
        step with alloc_w s6 (.App guards nows) hR6.wf ⟨rg6.lt, (R6.ext.repr hnw).lt⟩
          (by unfold Room; omega) as ⟨r7, hW7, ht7, htb7, hx7, hid7, hst7⟩
        obtain ⟨nows1, s7⟩ := r7
        simp only at hW7 ht7 htb7 hx7 hid7 hst7 ⊢
        have R7 : RanB s s7 (stepConjCost S U.length U.length x.2.length + stepCost S x.2.length +
            16 * x.2.length + 10) :=
          ⟨hW7, R6.ext.trans hx7, by rw [hst7, R6.stk], by omega⟩
        have rn1 : Repr nm s7.nodes.val nows1.val
            (nowsPat (nm none) U (bareKeys (altOf S d x.1 x.2.length) :: accN)) := by
          simp only [nowsPat, List.map_cons, encList]
          exact .app hid7 (hx7.repr rg6) (R7.ext.repr hnw)
        simp only [uncurry, bind_ok]
        exact rest s7 nows1 steps todo1 _ accS m₁ T₁ R7 (hF6.mono hx7 (by rw [htb7])) rn1
          (R7.ext.repr hst) (hx7.repr (hR6.ext.repr rtd5)) hE5
          (by simp [keyNows, hacc, hsm]) (by simp [keySteps, hacc, hsm])
          (fun g hg => by
            simp only [List.map_cons, keyNows, hacc, hsm, and_self, ↓reduceIte,
              List.singleton_append, List.mem_cons] at hg
            rcases hg with rfl | hg
            · exact Or.inr hall5
            · exact Or.inl hg)
          (fun a ha => by
            simp only [List.map_cons, keySteps, hacc, hsm, ↓reduceIte, List.nil_append] at ha
            exact Or.inl ha)
      | some kd =>
        rw [hsm] at hstp
        obtain ⟨ki, rfl, rki⟩ := hstp
        have hkdl : kd.length = x.2.length := Sorts.step_length hsm
        have hkz : ∀ m', some m' ∈ kd → m' ≠ nm none := fun m' hm' =>
          hC.nz m' (step_kid_names hsm hm')
        have hkμ : k = some μ := hμ x.1 x.2.length (by rw [hsm]; simp)
        simp only [uncurry]
        step with pair_up_spec hC.inj (altOf S d x.1 x.2.length) kd s6 r ki hR6.wf
          (hR6.ext.repr (hR5.ext.repr (hR4.ext.repr rargs))) rki (by rw [hlen2, hkdl]) hkz
          (by rw [hlen2]; unfold Room; omega) as ⟨r7, hR7, re⟩
        obtain ⟨edges, s7⟩ := r7
        simp only at hR7 re
        rw [hlen2] at hR7
        have R7 := R6.trans hR7.ranB
        have ht7 := R7.ticks
        have hF7 : FlagsK nm s7 U m₁ := hF6.mono hR7.ext (by rw [hR7.tbl])
        have hlenp := length_pairKeys_le (altOf S d x.1 x.2.length) kd
        rw [hlen2] at hlenp
        have hsE : ∀ q ∈ pairKeys (altOf S d x.1 x.2.length) kd,
            KeyOK (nm none) U q ∧ Sorts.KidG S (d, k) q := by
          intro q hq
          obtain ⟨i, hi, m', hki, rfl⟩ := mem_pairKeys.1 hq
          have hi' : i < x.2.length := by rw [← hlen2]; exact hi
          have hgi : (altOf S d x.1 x.2.length)[i] = Sorts.kidC S d x.1 x.2.length i := by
            simp [altOf]
          refine ⟨⟨altOf_sub hC d _ _ _ (List.getElem_mem hi), fun m'' h => ?_⟩, ?_⟩
          · simp only [Option.some.injEq] at h
            subst h
            exact hkz m' (List.mem_of_getElem? hki)
          · have hkx' : (x.1, x.2.length) ∈
                Sorts.caseKeys S d ∪ Sorts.caseKeys S {μ} ∪ Sorts.exKeys S μ := by
              have := hkx
              rw [hkμ] at this
              exact this
            exact Or.inr ⟨μ, m', hkμ, rfl, Or.inr ⟨(x.1, x.2.length), hkx', hacc, i, hi',
              Sorts.stepKid_eq.2 ⟨kd, hsm, hki⟩, hgi⟩⟩
        step with enqueue_spec_gen hC.inj (keyPat_patInj (nm none) U)
          (pairKeys (altOf S d x.1 x.2.length) kd) s7 edges todo1 T₁ m₁ hR7.wf hF7 hsE re
          (hR7.ext.repr (hR6.ext.repr rtd5)) (by unfold Room; omega)
          as ⟨r8, m₂, T₂, hR8, hF8, rtd8, hE8, hall8⟩
        obtain ⟨todo2, s8⟩ := r8
        simp only at hR8 hF8 rtd8
        have R8 := R7.trans hR8
        have ht8 := R8.ticks
        have rg8 : Repr nm s8.nodes.val guards.val
            (keysPat (nm none) U (bareKeys (altOf S d x.1 x.2.length))) :=
          hR8.ext.repr (hR7.ext.repr rg6)
        have re8 : Repr nm s8.nodes.val edges.val
            (keysPat (nm none) U (pairKeys (altOf S d x.1 x.2.length) kd)) := hR8.ext.repr re
        step with alloc_w s8 (.App guards edges) hR8.wf ⟨rg8.lt, re8.lt⟩
          (by unfold Room; omega) as ⟨r9, hW9, ht9, htb9, hx9, hid9, hst9⟩
        obtain ⟨alt, s9⟩ := r9
        simp only at hW9 ht9 htb9 hx9 hid9 hst9
        have ralt : Repr nm s9.nodes.val alt.val (stepPat (nm none) U
            (bareKeys (altOf S d x.1 x.2.length), pairKeys (altOf S d x.1 x.2.length) kd)) :=
          .app hid9 (hx9.repr rg8) (hx9.repr re8)
        have hx09 : Extends s s9 := R8.ext.trans hx9
        step with alloc_w s9 (.App alt steps) hW9 ⟨ralt.lt, (hx09.repr hst).lt⟩
          (by unfold Room; omega) as ⟨r10, hW10, ht10, htb10, hx10, hid10, hst10⟩
        obtain ⟨steps1, s10⟩ := r10
        simp only at hW10 ht10 htb10 hx10 hid10 hst10 ⊢
        have R10 : RanB s s10 (stepConjCost S U.length U.length x.2.length +
            stepCost S x.2.length + 16 * x.2.length + 10) :=
          ⟨hW10, hx09.trans hx10, by rw [hst10, hst9, R8.stk], by omega⟩
        have rs1 : Repr nm s10.nodes.val steps1.val (stepsPat (nm none) U
            ((bareKeys (altOf S d x.1 x.2.length), pairKeys (altOf S d x.1 x.2.length) kd)
              :: accS)) := by
          simp only [stepsPat, List.map_cons, encList]
          exact .app hid10 (hx10.repr ralt) (R10.ext.repr hst)
        simp only [uncurry, bind_ok]
        exact rest s10 nows steps1 todo2 accN _ m₂ T₂ R10
          ((hF8.mono hx9 (by rw [htb9])).mono hx10 (by rw [htb10])) (R10.ext.repr hnw) rs1
          (hx10.repr (hx9.repr rtd8)) (hE5.trans hE8)
          (by simp [keyNows, hacc, hsm]) (by simp [keySteps, hacc, hsm])
          (fun g hg => by
            simp only [List.map_cons, keyNows, hacc, hsm, reduceCtorEq, and_false, ↓reduceIte,
              List.nil_append] at hg
            exact Or.inl hg)
          (fun a ha => by
            simp only [List.map_cons, keySteps, hacc, hsm, ↓reduceIte, List.singleton_append,
              List.mem_cons] at ha
            rcases ha with rfl | ha
            · exact Or.inr ⟨fun q hq => hE8.flagged (hall5 q hq), hall8⟩
            · exact Or.inl ha)
    · simp only [hacc, ↓reduceIte] at hres
      subst hres
      simp only [uncurry, bind_ok]
      exact rest s3 nows steps todo accN accS m T (R3.mono (by omega)) hF3 (R3.ext.repr hnw)
        (R3.ext.repr hst) (R3.ext.repr htd) (Enq.refl _ m T) (by simp [keyNows, hacc])
        (by simp [keySteps, hacc])
        (fun g hg => by
          simp only [List.map_cons, keyNows, hacc, false_and, ↓reduceIte, List.nil_append] at hg
          exact Or.inl hg)
        (fun a ha => by
          simp only [List.map_cons, keySteps, hacc, ↓reduceIte, List.nil_append] at ha
          exact Or.inl ha)

theorem expand_keys_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (k : Option Name) (μ : Name) (hd : Sub U d)
    (hμ : ∀ f a, Sorts.step S μ f a ≠ none → k = some μ)
    (es : List (Sym × List Pat)) (s : store.Store)
    (keys decls names ci mi nows steps todo : store.TermId) (accN : List (List Key))
    (accS : List Step) (T : List Key) (m : Key → Option Bool) (hI : Inv s) (hF : FlagsK nm s U m)
    (hkeys : ∀ e ∈ es, (e.1, e.2.length) ∈ Sorts.keysOf S (d, k))
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (hmi : Repr nm s.nodes.val mi.val (.sym μ))
    (hks : Repr nm s.nodes.val keys.val
      (encList (nm none) (es.map fun e => entPat (nm none) (.sym e.1, e.2))))
    (hnw : Repr nm s.nodes.val nows.val (nowsPat (nm none) U accN))
    (hst : Repr nm s.nodes.val steps.val (stepsPat (nm none) U accS))
    (htd : Repr nm s.nodes.val todo.val (keysPat (nm none) U T))
    (hroom : Room s (keysWork S U.length (es.map fun e => (e.1, e.2.length)))) :
    sorts.expand_keys s decls names ci mi keys nows steps todo ⦃ r s' => ∃ m' T',
      RanB s s' (keysWork S U.length (es.map fun e => (e.1, e.2.length))) ∧ FlagsK nm s' U m' ∧
        Repr nm s'.nodes.val r.1.val (nowsPat (nm none) U
          ((keyNows S d μ (es.map fun e => (e.1, e.2.length))).reverse ++ accN)) ∧
        Repr nm s'.nodes.val r.2.1.val (stepsPat (nm none) U
          ((keySteps S d μ (es.map fun e => (e.1, e.2.length))).reverse ++ accS)) ∧
        Repr nm s'.nodes.val r.2.2.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ keyNows S d μ (es.map fun e => (e.1, e.2.length)), ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ keySteps S d μ (es.map fun e => (e.1, e.2.length)),
          (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
  unfold sorts.expand_keys
  step with expand_keys_loop_spec hC d k μ hd hμ es s keys decls names ci mi nows steps todo accN
    accS T m hI hF hkeys hde hU hci hmi hks hnw hst htd hroom
    as ⟨s1, nows1, steps1, todo1, m', T', h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨m', T', h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## What the roots no declaration names give a key -/

/-- The declaration of a sort as `lookup` gives it. -/
def OwnAt (nm : Option Nat → RwLog.Sym) (nodes : List store.Node) (S : Sorts) (μ : Name)
    (own : Option (store.TermId × store.TermId)) : Prop :=
  match S.lookup μ with
  | some dd => ∃ c r rp, own = some (c, r) ∧
      Repr nm nodes c.val
        (encList (nm none) ((dd.cases.map (caseEnt (nm none))).map (entPat (nm none)))) ∧
      Repr nm nodes r.val rp ∧ RestAt (nm none) dd.rest rp
  | none => own = none

theorem OwnAt.mono {S : Sorts} {μ : Name} {own : Option (store.TermId × store.TermId)}
    {s s' : store.Store} (h : OwnAt nm s.nodes.val S μ own) (hx : Extends s s') :
    OwnAt nm s'.nodes.val S μ own := by
  unfold OwnAt at h ⊢
  cases hl : S.lookup μ with
  | none => rw [hl] at h; exact h
  | some dd =>
    rw [hl] at h
    obtain ⟨c, r, rp, e, rc, rr, hr⟩ := h
    exact ⟨c, r, rp, e, hx.repr rc, hx.repr rr, hr⟩

theorem own_rest_spec {S : Sorts} {μ : Name} (s : store.Store)
    (own : Option (store.TermId × store.TermId)) (hW : Wf s)
    (ho : OwnAt nm s.nodes.val S μ own) (hroom : Room s 1) :
    sorts.own_rest s own ⦃ o s' => Ran s s' 1 ∧
      match (S.lookup μ).bind (·.rest) with
      | some r => ∃ e kk, o = some (e, kk) ∧ Repr nm s'.nodes.val kk.val (kidPat (nm none) r.2)
      | none => o = none ⦄ := by
  unfold sorts.own_rest
  unfold OwnAt at ho
  cases hl : S.lookup μ with
  | none =>
    rw [hl] at ho
    subst ho
    simp only [WP.spec_ok, Option.bind_none]
    exact ⟨(Ran.refl hW).mono (by omega), rfl⟩
  | some dd =>
    rw [hl] at ho
    obtain ⟨c, r, rp, rfl, -, rr, hr⟩ := ho
    simp only [Option.bind_some]
    refine WP.spec_mono (uncons_repr s r hW rr hroom) ?_
    rintro ⟨o, s'⟩ ⟨hK, hu⟩
    refine ⟨hK.ran, ?_⟩
    cases hre : dd.rest with
    | none =>
      rw [hre] at hr
      simp only [RestAt] at hr
      subst hr
      exact hu
    | some er =>
      rw [hre] at hr
      simp only [RestAt] at hr
      obtain ⟨xs, -, rfl⟩ := hr
      obtain ⟨e, kk, rfl, -, rk⟩ := hu
      exact ⟨e, kk, rfl, by rw [hK.nodes]; exact rk⟩

/-- When every sort of the conjunction has a rest and the sort has none: no
guard. -/
def restNows (S : Sorts) (d : Sorts.Conj) (μ : Name) : List (List Key) :=
  if Sorts.RestOK S d ∧ ((S.lookup μ).bind (·.rest)).isSome = false then [[]] else []

/-- When every sort of the conjunction has a rest and the rest of the sort
asks a sort of arguments: the pair of what the rests of the conjunction ask
with it. -/
def restSteps (S : Sorts) (d : Sorts.Conj) (μ : Name) : List Step :=
  if Sorts.RestOK S d then
    match Sorts.restKid S μ with
    | some r => [([], [(Sorts.restKids S d, some r)])]
    | none => []
  else []

/-- The ticks `rest_alts` may spend. -/
def restAltsCost (S : Sorts) (u : Nat) : Nat := u * (3 * S.length + 4) + restKidsCost S u + 13

theorem rest_alts_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (k : Option Name) (μ : Name) (hd : Sub U d)
    (hμ : (S.lookup μ).isSome = true → k = some μ)
    (s : store.Store) (decls names ci todo : store.TermId)
    (own : Option (store.TermId × store.TermId)) (T : List Key) (m : Key → Option Bool)
    (hI : Inv s) (hF : FlagsK nm s U m)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (ho : OwnAt nm s.nodes.val S μ own)
    (htd : Repr nm s.nodes.val todo.val (keysPat (nm none) U T))
    (hroom : Room s (restAltsCost S U.length)) :
    sorts.rest_alts s decls names ci own todo ⦃ r s' => ∃ m' T',
      RanB s s' (restAltsCost S U.length) ∧ FlagsK nm s' U m' ∧
        Repr nm s'.nodes.val r.1.val (nowsPat (nm none) U (restNows S d μ)) ∧
        Repr nm s'.nodes.val r.2.1.val (stepsPat (nm none) U (restSteps S d μ)) ∧
        Repr nm s'.nodes.val r.2.2.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        ∀ a ∈ restSteps S d μ, ∀ q ∈ a.2, m' q ≠ none ⦄ := by
  unfold sorts.rest_alts
  have hroom' := hroom
  unfold Room restAltsCost at hroom'
  have hW := hI.toWf
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨nil, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have R1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  have rn1 : Repr nm s1.nodes.val nil.val (.sym (nm none)) := .nil hid
  step with rest_ok_spec hC.inj S hC.sorts d hd s1 decls ci hW1 (hx1.repr hde) (hx1.repr hci)
    (by unfold Room; omega) as ⟨b, s2, hR2, hb⟩
  have ht2 := hR2.ticks
  have R2 := R1.trans hR2
  have hF2 : FlagsK nm s2 U m := hF.mono R2.ext (by rw [R2.tbl])
  have rn2 : Repr nm s2.nodes.val nil.val (.sym (nm none)) := hR2.ext.repr rn1
  by_cases hro : Sorts.RestOK S d
  · rw [show b = true from hb.2 hro]
    simp only [↓reduceIte]
    step with own_rest_spec (S := S) (μ := μ) s2 own hR2.wf (ho.mono R2.ext)
      (by unfold Room; omega) as ⟨o, s3, hR3, hor⟩
    have ht3 := hR3.ticks
    have R3 := R2.trans hR3
    have hF3 : FlagsK nm s3 U m := hF2.mono hR3.ext (by rw [hR3.tbl])
    have rn3 : Repr nm s3.nodes.val nil.val (.sym (nm none)) := hR3.ext.repr rn2
    cases hre : (S.lookup μ).bind (·.rest) with
    | none =>
      rw [hre] at hor
      simp only at hor
      subst hor
      simp only
      step with alloc_w s3 (.App nil nil) hR3.wf ⟨rn3.lt, rn3.lt⟩ (by unfold Room; omega)
        as ⟨nows, s4, hW4, ht4, htb4, hx4, hid4, hst4⟩
      have R4 : RanB s s4 (restAltsCost S U.length) :=
        ⟨hW4, R3.ext.trans hx4, by rw [hst4, R3.stk], by unfold restAltsCost; omega⟩
      have hrk : Sorts.restKid S μ = none := by simp [Sorts.restKid, hre]
      refine ⟨m, T, R4, hF3.mono hx4 (by rw [htb4]), ?_, ?_, R4.ext.repr htd, Enq.refl _ m T, ?_⟩
      · simp only [restNows, hro, hre, Option.isSome_none, and_self, ↓reduceIte, nowsPat,
          List.map_cons, List.map_nil, encList, keysPat]
        exact .app hid4 (hx4.repr rn3) (hx4.repr rn3)
      · simp only [restSteps, hro, hrk, ↓reduceIte, stepsPat, List.map_nil, encList]
        exact hx4.repr rn3
      · intro a ha
        simp [restSteps, hro, hrk] at ha
    | some er =>
      obtain ⟨ex, kk⟩ := er
      rw [hre] at hor
      obtain ⟨e, ki, rfl, rki⟩ := hor
      have hrk : Sorts.restKid S μ = kk := by simp [Sorts.restKid, hre]
      have hk0 : ∀ m', kk = some m' → m' ≠ nm none := fun m' e' =>
        hC.nz m' (Sorts.restKid_mem_names (n := μ) (by rw [hrk, e']))
      simp only
      step with is_nil_kid hC.inj s3 ki hR3.wf rki hk0 (by unfold Room; omega) as ⟨b1, s4, hb1, hK4⟩
      have ht4 := hK4.ticks
      have R4 := R3.trans hK4.ran
      have hF4 : FlagsK nm s4 U m := hF3.mono hK4.ran.ext (by rw [hK4.tbl])
      have rn4 : Repr nm s4.nodes.val nil.val (.sym (nm none)) := hK4.ran.ext.repr rn3
      have hno : ¬ (Sorts.RestOK S d ∧ ((S.lookup μ).bind (·.rest)).isSome = false) := by
        rw [hre]; simp
      cases kk with
      | none =>
        rw [show b1 = true from hb1.2 rfl]
        simp only [↓reduceIte, WP.spec_ok]
        refine ⟨m, T, R4.ranB.mono (by unfold restAltsCost; omega), hF4, ?_, ?_, R4.ext.repr htd,
          Enq.refl _ m T, ?_⟩
        · simp only [restNows, hno, ↓reduceIte, nowsPat, List.map_nil, encList]
          exact rn4
        · simp only [restSteps, hro, hrk, ↓reduceIte, stepsPat, List.map_nil, encList]
          exact rn4
        · intro a ha
          simp [restSteps, hro, hrk] at ha
      | some r' =>
        have hbf : b1 = false := by
          cases b1
          · rfl
          · exact absurd (hb1.1 rfl) (by simp)
        rw [hbf]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [kidPat] at rki
        have hkμ : k = some μ := hμ (by
          cases hl : S.lookup μ with
          | none => rw [hl] at hre; simp at hre
          | some _ => rfl)
        step with rest_kids_spec hC.inj S hC.sorts hC.nz d hd s4 decls names ci hK4.wf
          (R4.ext.repr hde) (R4.ext.repr hU) (R4.ext.repr hci) (by unfold Room; omega)
          as ⟨dk, s5, hR5, rdk⟩
        have ht5 := hR5.ticks
        have hF5 : FlagsK nm s5 U m := hF4.mono hR5.ext hR5.tbl
        have rki5 : Repr nm s5.nodes.val ki.val (.sym r') := hR5.ext.repr (hK4.ran.ext.repr rki)
        have rn5 : Repr nm s5.nodes.val nil.val (.sym (nm none)) := hR5.ext.repr rn4
        step with alloc_w s5 (.App dk ki) hR5.wf ⟨rdk.lt, rki5.lt⟩ (by unfold Room; omega)
          as ⟨q, s6, hW6, ht6, htb6, hx6, hid6, hst6⟩
        have rq : Repr nm s6.nodes.val q.val
            (keyPat (nm none) U (Sorts.restKids S d, some r')) :=
          .app hid6 (hx6.repr rdk) (hx6.repr rki5)
        step with alloc_w s6 (.App q nil) hW6 ⟨rq.lt, (hx6.repr rn5).lt⟩ (by unfold Room; omega)
          as ⟨edges, s7, hW7, ht7, htb7, hx7, hid7, hst7⟩
        have re : Repr nm s7.nodes.val edges.val
            (keysPat (nm none) U [(Sorts.restKids S d, some r')]) := by
          simp only [keysPat, List.map_cons, List.map_nil, encList]
          exact .app hid7 (hx7.repr rq) (hx7.repr (hx6.repr rn5))
        have hx07 : Extends s s7 := ((R4.ext.trans hR5.ext).trans hx6).trans hx7
        have hF7 : FlagsK nm s7 U m :=
          (hF5.mono hx6 (by rw [htb6])).mono hx7 (by rw [htb7])
        have hsE : ∀ q' ∈ [((Sorts.restKids S d, some r') : Key)],
            KeyOK (nm none) U q' ∧ Sorts.KidG S (d, k) q' := by
          intro q' hq'
          rw [List.mem_singleton.1 hq']
          refine ⟨⟨fun n hn => hC.names n (Sorts.restKids_subset_names hn), fun m' e' => ?_⟩, ?_⟩
          · simp only [Option.some.injEq] at e'
            subst e'
            exact hk0 _ rfl
          · exact Or.inr ⟨μ, r', hkμ, rfl, Or.inl ⟨hro, hrk, rfl⟩⟩
        step with enqueue_spec_gen hC.inj (keyPat_patInj (nm none) U)
          [((Sorts.restKids S d, some r') : Key)] s7 edges todo T m hW7 hF7 hsE re
          (hx07.repr htd) (by simp only [List.length_cons, List.length_nil]; unfold Room; omega)
          as ⟨todo1, s8, m₁, T₁, hR8, hF8, rtd8, hE8, hall8⟩
        simp only [List.length_cons, List.length_nil] at hR8
        have ht8 := hR8.ticks
        have rn8 : Repr nm s8.nodes.val nil.val (.sym (nm none)) :=
          hR8.ext.repr (hx7.repr (hx6.repr rn5))
        have re8 := hR8.ext.repr re
        step with alloc_w s8 (.App nil edges) hR8.wf ⟨rn8.lt, re8.lt⟩ (by unfold Room; omega)
          as ⟨alt, s9, hW9, ht9, htb9, hx9, hid9, hst9⟩
        have ralt : Repr nm s9.nodes.val alt.val
            (stepPat (nm none) U ([], [(Sorts.restKids S d, some r')])) :=
          .app hid9 (hx9.repr rn8) (hx9.repr re8)
        step with alloc_w s9 (.App alt nil) hW9 ⟨ralt.lt, (hx9.repr rn8).lt⟩
          (by unfold Room; omega) as ⟨steps, s10, hW10, ht10, htb10, hx10, hid10, hst10⟩
        have hx010 : Extends s s10 := ((hx07.trans hR8.ext).trans hx9).trans hx10
        have R10 : RanB s s10 (restAltsCost S U.length) :=
          ⟨hW10, hx010, by rw [hst10, hst9, hR8.stk, hst7, hst6, hR5.stk, R4.stk], by
            unfold restAltsCost; omega⟩
        refine ⟨m₁, T₁, R10, (hF8.mono hx9 (by rw [htb9])).mono hx10 (by rw [htb10]), ?_, ?_,
          hx10.repr (hx9.repr rtd8), hE8, ?_⟩
        · simp only [restNows, hno, ↓reduceIte, nowsPat, List.map_nil, encList]
          exact hx10.repr (hx9.repr rn8)
        · simp only [restSteps, hro, hrk, ↓reduceIte, stepsPat, List.map_cons, List.map_nil,
            encList]
          exact .app hid10 (hx10.repr ralt) (hx10.repr (hx9.repr rn8))
        · intro a ha q' hq'
          simp only [restSteps, hro, hrk, ↓reduceIte, List.mem_singleton] at ha
          subst ha
          exact hall8 q' hq'
  · have hbf : b = false := by
      cases b
      · rfl
      · exact absurd (hb.1 rfl) hro
    rw [hbf]
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨m, T, R2.ranB.mono (by unfold restAltsCost; omega), hF2, ?_, ?_, R2.ext.repr htd,
      Enq.refl _ m T, ?_⟩
    · simp only [restNows, hro, false_and, ↓reduceIte, nowsPat, List.map_nil, encList]
      exact rn2
    · simp only [restSteps, hro, ↓reduceIte, stepsPat, List.map_nil, encList]
      exact rn2
    · intro a ha
      simp [restSteps, hro] at ha

/-! ## The alternatives of a key -/

theorem keyNows_append (S : Sorts) (d : Sorts.Conj) (μ : Name) : ∀ K K' : List (Sym × Nat),
    keyNows S d μ (K ++ K') = keyNows S d μ K ++ keyNows S d μ K'
  | [], _ => rfl
  | k :: K, K' => by simp [keyNows, keyNows_append S d μ K K']

theorem keySteps_append (S : Sorts) (d : Sorts.Conj) (μ : Name) : ∀ K K' : List (Sym × Nat),
    keySteps S d μ (K ++ K') = keySteps S d μ K ++ keySteps S d μ K'
  | [], _ => rfl
  | k :: K, K' => by simp [keySteps, keySteps_append S d μ K K']

theorem keysWork_append (S : Sorts) (u : Nat) : ∀ K K' : List (Sym × Nat),
    keysWork S u (K ++ K') + 1 = keysWork S u K + keysWork S u K'
  | [], K' => by simp [keysWork]; omega
  | k :: K, K' => by
    have := keysWork_append S u K K'
    simp only [List.cons_append, keysWork]; omega

/-- The roots a declaration has a case for. -/
def caseKeysL (dd : SortDef) : List (Sym × Nat) := dd.cases.map fun c => (c.1, c.2.length)

/-- The roots a sort has a case for. -/
def defKeys (S : Sorts) (n : Name) : List (Sym × Nat) :=
  match S.lookup n with
  | some dd => caseKeysL dd
  | none => []

/-- The roots a sort has a case for, and those its rest excludes. -/
def ownKeys (S : Sorts) (μ : Name) : List (Sym × Nat) :=
  match S.lookup μ with
  | some dd => caseKeysL dd ++ (match dd.rest with | some r => r.1 | none => [])
  | none => []

theorem lookup_of_step {S : Sorts} {μ : Name} {f : Sym} {a : Nat}
    (h : Sorts.step S μ f a ≠ none) : (S.lookup μ).isSome = true := by
  obtain ⟨ks, hks⟩ := Option.ne_none_iff_exists'.1 h
  obtain ⟨dd, hl, -⟩ := Sorts.step_cases hks
  rw [hl]; rfl

theorem caseKeys_sub_keysOf {S : Sorts} {d : Sorts.Conj} {κ : Sym × Nat} (k : Option Name)
    (h : κ ∈ Sorts.caseKeys S d) : κ ∈ Sorts.keysOf S (d, k) := by
  cases k with
  | none => exact h
  | some n => simp only [Sorts.keysOf, Finset.mem_union]; exact Or.inl (Or.inl h)

theorem defKeys_sub {S : Sorts} {d : Sorts.Conj} {n : Name} (hn : n ∈ d) {κ : Sym × Nat}
    (h : κ ∈ defKeys S n) : κ ∈ Sorts.caseKeys S d := by
  unfold defKeys at h
  cases hl : S.lookup n with
  | none => rw [hl] at h; cases h
  | some dd =>
    rw [hl] at h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
    exact Sorts.mem_caseKeys.2 ⟨n, hn, dd, hl, c, hc, rfl, rfl⟩

theorem ownKeys_sub {S : Sorts} {d : Sorts.Conj} {μ : Name} {κ : Sym × Nat}
    (h : κ ∈ ownKeys S μ) : κ ∈ Sorts.keysOf S (d, some μ) := by
  unfold ownKeys at h
  simp only [Sorts.keysOf, Finset.mem_union]
  cases hl : S.lookup μ with
  | none => rw [hl] at h; cases h
  | some dd =>
    rw [hl] at h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact Or.inl (Or.inr (Sorts.mem_caseKeys.2 ⟨μ, by simp, dd, hl, c, hc, rfl, rfl⟩))
    · refine Or.inr ?_
      cases hre : dd.rest with
      | none => rw [hre] at h; cases h
      | some r =>
        rw [hre] at h
        obtain ⟨ex, kk⟩ := r
        simp [Sorts.exKeys, hl, hre, h]

/-- `expand_keys` on the cases of a declaration. -/
theorem expand_keys_cases_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (k : Option Name) (μ : Name) (hd : Sub U d)
    (hμ : (S.lookup μ).isSome = true → k = some μ)
    (cs : List (Sym × List (Option Name))) (s : store.Store)
    (keys decls names ci mi nows steps todo : store.TermId) (accN : List (List Key))
    (accS : List Step) (T : List Key) (m : Key → Option Bool) (hI : Inv s) (hF : FlagsK nm s U m)
    (hkeys : ∀ κ ∈ cs.map (fun c => (c.1, c.2.length)), κ ∈ Sorts.keysOf S (d, k))
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (hmi : Repr nm s.nodes.val mi.val (.sym μ))
    (hks : Repr nm s.nodes.val keys.val
      (encList (nm none) ((cs.map (caseEnt (nm none))).map (entPat (nm none)))))
    (hnw : Repr nm s.nodes.val nows.val (nowsPat (nm none) U accN))
    (hst : Repr nm s.nodes.val steps.val (stepsPat (nm none) U accS))
    (htd : Repr nm s.nodes.val todo.val (keysPat (nm none) U T))
    (hroom : Room s (keysWork S U.length (cs.map fun c => (c.1, c.2.length)))) :
    sorts.expand_keys s decls names ci mi keys nows steps todo ⦃ r s' => ∃ m' T',
      RanB s s' (keysWork S U.length (cs.map fun c => (c.1, c.2.length))) ∧ FlagsK nm s' U m' ∧
        Repr nm s'.nodes.val r.1.val (nowsPat (nm none) U
          ((keyNows S d μ (cs.map fun c => (c.1, c.2.length))).reverse ++ accN)) ∧
        Repr nm s'.nodes.val r.2.1.val (stepsPat (nm none) U
          ((keySteps S d μ (cs.map fun c => (c.1, c.2.length))).reverse ++ accS)) ∧
        Repr nm s'.nodes.val r.2.2.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ keyNows S d μ (cs.map fun c => (c.1, c.2.length)), ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ keySteps S d μ (cs.map fun c => (c.1, c.2.length)),
          (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
  have e1 : (cs.map fun c => (c.1, c.2.map (kidPat (nm none)))).map
      (fun e => entPat (nm none) (.sym e.1, e.2)) =
      (cs.map (caseEnt (nm none))).map (entPat (nm none)) := by
    simp [caseEnt, Function.comp_def]
  have e2 : (cs.map fun c => (c.1, c.2.map (kidPat (nm none)))).map
      (fun e => (e.1, e.2.length)) = cs.map fun c => (c.1, c.2.length) := by
    simp [Function.comp_def]
  have h := expand_keys_spec hC d k μ hd (fun f a h => hμ (lookup_of_step h))
    (cs.map fun c => (c.1, c.2.map (kidPat (nm none)))) s keys decls names ci mi nows steps todo
    accN accS T m hI hF
    (fun e he => hkeys _ (by rw [← e2]; exact List.mem_map_of_mem he)) hde hU hci hmi
    (by rw [e1]; exact hks) hnw hst htd (by rw [e2]; exact hroom)
  rw [e2] at h
  exact h

/-- The ticks going through the cases of the sorts of a list may spend. -/
def conjWork (S : Sorts) (u : Nat) : List Name → Nat
  | [] => 1
  | n :: ns => 3 * S.length + 3 + keysWork S u (defKeys S n) + conjWork S u ns

theorem conj_keys_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (k : Option Name) (μ : Name) (hd : Sub U d)
    (hμ : (S.lookup μ).isSome = true → k = some μ) :
    ∀ (xs : List Name) (s : store.Store)
      (ns decls names ci mi nows steps todo : store.TermId) (accN : List (List Key))
      (accS : List Step) (T : List Key) (m : Key → Option Bool), Inv s → FlagsK nm s U m →
    (∀ n ∈ xs, n ∈ d) →
    Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val ci.val (cpat (nm none) U d) →
    Repr nm s.nodes.val mi.val (.sym μ) →
    Repr nm s.nodes.val ns.val (namesPat (nm none) xs) →
    Repr nm s.nodes.val nows.val (nowsPat (nm none) U accN) →
    Repr nm s.nodes.val steps.val (stepsPat (nm none) U accS) →
    Repr nm s.nodes.val todo.val (keysPat (nm none) U T) →
    Room s (conjWork S U.length xs) →
    sorts.conj_keys_loop ns s decls names ci mi nows steps todo ⦃ r => ∃ m' T',
      RanB s r.1 (conjWork S U.length xs) ∧ FlagsK nm r.1 U m' ∧
        Repr nm r.1.nodes.val r.2.1.val (nowsPat (nm none) U
          ((keyNows S d μ (xs.flatMap (defKeys S))).reverse ++ accN)) ∧
        Repr nm r.1.nodes.val r.2.2.1.val (stepsPat (nm none) U
          ((keySteps S d μ (xs.flatMap (defKeys S))).reverse ++ accS)) ∧
        Repr nm r.1.nodes.val r.2.2.2.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ keyNows S d μ (xs.flatMap (defKeys S)), ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ keySteps S d μ (xs.flatMap (defKeys S)),
          (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
  intro xs
  induction xs with
  | nil =>
    intro s ns decls names ci mi nows steps todo accN accS T m hI hF hxs hde hU hci hmi hns
      hnw hst htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [conjWork] at hroom'
    unfold sorts.conj_keys_loop
    rw [loop]
    simp only [sorts.conj_keys_loop.body]
    step with uncons_repr s ns hI.toWf hns (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    subst hu
    have hfin : ∃ m' T', RanB s s1 (conjWork S U.length []) ∧ FlagsK nm s1 U m' ∧
        Repr nm s1.nodes.val nows.val (nowsPat (nm none) U
          ((keyNows S d μ (([] : List Name).flatMap (defKeys S))).reverse ++ accN)) ∧
        Repr nm s1.nodes.val steps.val (stepsPat (nm none) U
          ((keySteps S d μ (([] : List Name).flatMap (defKeys S))).reverse ++ accS)) ∧
        Repr nm s1.nodes.val todo.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ keyNows S d μ (([] : List Name).flatMap (defKeys S)), ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ keySteps S d μ (([] : List Name).flatMap (defKeys S)),
          (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none :=
      ⟨m, T, hK.ran.ranB.mono (by simp [conjWork]), hF.mono hK.ran.ext (by rw [hK.tbl]),
        by rw [hK.nodes]; simpa [keyNows] using hnw, by rw [hK.nodes]; simpa [keySteps] using hst,
        by rw [hK.nodes]; exact htd, Enq.refl _ m T, fun _ h => (by simp [keyNows] at h),
        fun _ h => (by simp [keySteps] at h)⟩
    step*
  | cons x xs ih =>
    intro s ns decls names ci mi nows steps todo accN accS T m hI hF hxs hde hU hci hmi hns
      hnw hst htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [conjWork] at hroom'
    have hW := hI.toWf
    unfold sorts.conj_keys_loop
    rw [loop]
    simp only [sorts.conj_keys_loop.body]
    step with uncons_repr s ns hW hns (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    obtain ⟨n, t, rfl, rn, rt⟩ := hu
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    step with lookup_spec hC.inj S hC.sorts s1 decls n hK.wf (by rw [hn1]; exact hde)
      (by rw [hn1]; exact rn) (by unfold Room; omega) as ⟨r1, hR2, hlk⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hR2 hlk
    have ht2 := hR2.ticks
    have R2 : Ran s s2 (3 * S.length + 3) := (hK.ran.trans hR2).mono (by omega)
    have hF2 : FlagsK nm s2 U m := hF.mono R2.ext (by rw [R2.tbl])
    have hxs' : ∀ n ∈ xs, n ∈ d := fun n hn => hxs n (List.mem_cons_of_mem _ hn)
    -- the rest of the sorts
    have rest : ∀ (s' : store.Store) (nows' steps' todo' : store.TermId)
        (accN' : List (List Key)) (accS' : List Step) (m₁ : Key → Option Bool) (T₁ : List Key),
        RanB s s' (3 * S.length + 3 + keysWork S U.length (defKeys S x)) →
        FlagsK nm s' U m₁ →
        Repr nm s'.nodes.val nows'.val (nowsPat (nm none) U accN') →
        Repr nm s'.nodes.val steps'.val (stepsPat (nm none) U accS') →
        Repr nm s'.nodes.val todo'.val (keysPat (nm none) U T₁) →
        Enq (Sorts.KidG S (d, k)) m m₁ T T₁ →
        (accN' = (keyNows S d μ (defKeys S x)).reverse ++ accN) →
        (accS' = (keySteps S d μ (defKeys S x)).reverse ++ accS) →
        (∀ g ∈ keyNows S d μ (defKeys S x), ∀ q ∈ g, m₁ q ≠ none) →
        (∀ a ∈ keySteps S d μ (defKeys S x), (∀ q ∈ a.1, m₁ q ≠ none) ∧ ∀ q ∈ a.2, m₁ q ≠ none) →
        loop (fun x => match x with
          | (ns1, s1, nows1, steps1, todo1) =>
            sorts.conj_keys_loop.body decls names ci mi ns1 s1 nows1 steps1 todo1)
          (t, s', nows', steps', todo') ⦃ r => ∃ m' T',
          RanB s r.1 (conjWork S U.length (x :: xs)) ∧ FlagsK nm r.1 U m' ∧
            Repr nm r.1.nodes.val r.2.1.val (nowsPat (nm none) U
              ((keyNows S d μ ((x :: xs).flatMap (defKeys S))).reverse ++ accN)) ∧
            Repr nm r.1.nodes.val r.2.2.1.val (stepsPat (nm none) U
              ((keySteps S d μ ((x :: xs).flatMap (defKeys S))).reverse ++ accS)) ∧
            Repr nm r.1.nodes.val r.2.2.2.val (keysPat (nm none) U T') ∧
            Enq (Sorts.KidG S (d, k)) m m' T T' ∧
            (∀ g ∈ keyNows S d μ ((x :: xs).flatMap (defKeys S)), ∀ q ∈ g, m' q ≠ none) ∧
            ∀ a ∈ keySteps S d μ ((x :: xs).flatMap (defKeys S)),
              (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
      intro s' nows' steps' todo' accN' accS' m₁ T₁ R0 hF' hnw' hst' htd' hE hN hSt hfN hfS
      have := R0.ticks
      have IH := ih s' t decls names ci mi nows' steps' todo' accN' accS' T₁ m₁ (R0.inv hI) hF'
        hxs' (R0.ext.repr hde) (R0.ext.repr hU) (R0.ext.repr hci) (R0.ext.repr hmi)
        (R0.ext.repr rt) hnw' hst' htd' (by unfold Room; omega)
      unfold sorts.conj_keys_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨m', T', hR, hFm, hrn, hrs, hrt, hE', hallN, hallS⟩
      refine ⟨m', T', (R0.trans hR).mono (by simp only [conjWork]; omega), hFm, ?_, ?_, hrt,
        hE.trans hE', ?_, ?_⟩
      · rw [hN] at hrn
        simpa [keyNows_append] using hrn
      · rw [hSt] at hrs
        simpa [keySteps_append] using hrs
      · intro g hg q hq
        simp only [List.flatMap_cons, keyNows_append, List.mem_append] at hg
        rcases hg with h | h
        · exact hE'.flagged (hfN g h q hq)
        · exact hallN g h q hq
      · intro a ha
        simp only [List.flatMap_cons, keySteps_append, List.mem_append] at ha
        rcases ha with h | h
        · exact ⟨fun q hq => hE'.flagged ((hfS a h).1 q hq),
            fun q hq => hE'.flagged ((hfS a h).2 q hq)⟩
        · exact hallS a h
    cases hl : S.lookup x with
    | none =>
      rw [hl] at hlk
      subst hlk
      have hdk : defKeys S x = [] := by simp [defKeys, hl]
      simp only [uncurry, bind_ok]
      exact rest s2 nows steps todo accN accS m T (R2.ranB.mono (by omega)) hF2 (R2.ext.repr hnw)
        (R2.ext.repr hst) (R2.ext.repr htd) (Enq.refl _ m T) (by simp [hdk, keyNows])
        (by simp [hdk, keySteps]) (fun g hg => (by simp [hdk, keyNows] at hg))
        (fun a ha => (by simp [hdk, keySteps] at ha))
    | some dd =>
      rw [hl] at hlk
      obtain ⟨c, r, rp, rfl, rc, -, -⟩ := hlk
      have hdk : defKeys S x = dd.cases.map fun c => (c.1, c.2.length) := by
        simp [defKeys, hl, caseKeysL]
      rw [hdk] at rest
      simp only [uncurry]
      step with expand_keys_cases_spec hC d k μ hd hμ dd.cases s2 c decls names ci mi nows steps
        todo accN accS T m (R2.ranB.inv hI) hF2
        (fun κ hκ => caseKeys_sub_keysOf k
          (defKeys_sub (hxs x List.mem_cons_self) (by rw [hdk]; exact hκ)))
        (R2.ext.repr hde) (R2.ext.repr hU) (R2.ext.repr hci) (R2.ext.repr hmi)
        (hR2.ext.repr rc) (R2.ext.repr hnw) (R2.ext.repr hst) (R2.ext.repr htd)
        (by have := R2.ticks; rw [hdk] at hroom'; unfold Room; omega)
        as ⟨r3, m₁, T₁, hR3, hF3, rn3, rs3, rt3, hE3, hN3, hS3⟩
      obtain ⟨⟨a, b, c'⟩, s3⟩ := r3
      simp only at hR3 hF3 rn3 rs3 rt3 ⊢
      simp only [uncurry, bind_ok]
      exact rest s3 a b c' _ _ m₁ T₁ (R2.ranB.trans hR3) hF3 rn3 rs3 rt3 hE3 rfl rfl hN3 hS3

theorem conj_keys_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (k : Option Name) (μ : Name) (hd : Sub U d)
    (hμ : (S.lookup μ).isSome = true → k = some μ)
    (xs : List Name) (s : store.Store)
    (ns decls names ci mi nows steps todo : store.TermId) (accN : List (List Key))
    (accS : List Step) (T : List Key) (m : Key → Option Bool) (hI : Inv s) (hF : FlagsK nm s U m)
    (hxs : ∀ n ∈ xs, n ∈ d)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (hmi : Repr nm s.nodes.val mi.val (.sym μ))
    (hns : Repr nm s.nodes.val ns.val (namesPat (nm none) xs))
    (hnw : Repr nm s.nodes.val nows.val (nowsPat (nm none) U accN))
    (hst : Repr nm s.nodes.val steps.val (stepsPat (nm none) U accS))
    (htd : Repr nm s.nodes.val todo.val (keysPat (nm none) U T))
    (hroom : Room s (conjWork S U.length xs)) :
    sorts.conj_keys s decls names ci mi ns nows steps todo ⦃ r s' => ∃ m' T',
      RanB s s' (conjWork S U.length xs) ∧ FlagsK nm s' U m' ∧
        Repr nm s'.nodes.val r.1.val (nowsPat (nm none) U
          ((keyNows S d μ (xs.flatMap (defKeys S))).reverse ++ accN)) ∧
        Repr nm s'.nodes.val r.2.1.val (stepsPat (nm none) U
          ((keySteps S d μ (xs.flatMap (defKeys S))).reverse ++ accS)) ∧
        Repr nm s'.nodes.val r.2.2.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ keyNows S d μ (xs.flatMap (defKeys S)), ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ keySteps S d μ (xs.flatMap (defKeys S)),
          (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
  unfold sorts.conj_keys
  step with conj_keys_loop_spec hC d k μ hd hμ xs s ns decls names ci mi nows steps todo accN
    accS T m hI hF hxs hde hU hci hmi hns hnw hst htd hroom
    as ⟨s1, nows1, steps1, todo1, m', T', h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨m', T', h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem exEnts {ex : List (Sym × Nat)} {xs : List (Pat × List Pat)}
    (h : List.Forall₂ ExAt ex xs) :
    ∃ es : List (Sym × List Pat), xs = es.map (fun e => ((.sym e.1 : Pat), e.2)) ∧
      es.map (fun e => (e.1, e.2.length)) = ex := by
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons e x ex xs hex _ ih =>
    obtain ⟨es, rfl, rfl⟩ := ih
    obtain ⟨x1, x2⟩ := x
    obtain ⟨h1, h2⟩ := hex
    simp only at h1 h2
    subst h1
    refine ⟨(e.1, x2) :: es, rfl, ?_⟩
    simp [h2]

/-- The ticks `own_keys` may spend. -/
def ownWork (S : Sorts) (u : Nat) (μ : Name) : Nat := keysWork S u (ownKeys S μ) + 2

theorem own_keys_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (k : Option Name) (μ : Name) (hd : Sub U d)
    (hμ : (S.lookup μ).isSome = true → k = some μ)
    (s : store.Store) (decls names ci mi nows steps todo : store.TermId)
    (own : Option (store.TermId × store.TermId)) (accN : List (List Key))
    (accS : List Step) (T : List Key) (m : Key → Option Bool) (hI : Inv s) (hF : FlagsK nm s U m)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (hmi : Repr nm s.nodes.val mi.val (.sym μ))
    (ho : OwnAt nm s.nodes.val S μ own)
    (hnw : Repr nm s.nodes.val nows.val (nowsPat (nm none) U accN))
    (hst : Repr nm s.nodes.val steps.val (stepsPat (nm none) U accS))
    (htd : Repr nm s.nodes.val todo.val (keysPat (nm none) U T))
    (hroom : Room s (ownWork S U.length μ)) :
    sorts.own_keys s decls names ci mi own nows steps todo ⦃ r s' => ∃ m' T',
      RanB s s' (ownWork S U.length μ) ∧ FlagsK nm s' U m' ∧
        Repr nm s'.nodes.val r.1.val (nowsPat (nm none) U
          ((keyNows S d μ (ownKeys S μ)).reverse ++ accN)) ∧
        Repr nm s'.nodes.val r.2.1.val (stepsPat (nm none) U
          ((keySteps S d μ (ownKeys S μ)).reverse ++ accS)) ∧
        Repr nm s'.nodes.val r.2.2.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ keyNows S d μ (ownKeys S μ), ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ keySteps S d μ (ownKeys S μ),
          (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
  unfold sorts.own_keys
  have hroom' := hroom
  unfold Room ownWork at hroom'
  unfold OwnAt at ho
  cases hl : S.lookup μ with
  | none =>
    rw [hl] at ho
    subst ho
    have hok : ownKeys S μ = [] := by simp [ownKeys, hl]
    simp only [WP.spec_ok]
    refine ⟨m, T, (RanB.refl hI.toWf).mono (by omega), hF, by simpa [hok, keyNows] using hnw,
      by simpa [hok, keySteps] using hst, htd, Enq.refl _ m T,
      fun g hg => (by simp [hok, keyNows] at hg), fun a ha => (by simp [hok, keySteps] at ha)⟩
  | some dd =>
    rw [hl] at ho
    obtain ⟨c, r, rp, rfl, rc, rr, hr⟩ := ho
    have hkμ : k = some μ := hμ (by rw [hl]; rfl)
    have hsub : ∀ κ ∈ ownKeys S μ, κ ∈ Sorts.keysOf S (d, k) := fun κ hκ => by
      rw [hkμ]; exact ownKeys_sub hκ
    have hok : ownKeys S μ =
        caseKeysL dd ++ (match dd.rest with | some r => r.1 | none => []) := by
      simp [ownKeys, hl]
    have hwork := keysWork_append S U.length (caseKeysL dd)
      (match dd.rest with | some r => r.1 | none => [])
    rw [← hok] at hwork
    simp only
    step with expand_keys_cases_spec hC d k μ hd hμ dd.cases s c decls names ci mi nows steps
      todo accN accS T m hI hF
      (fun κ hκ => hsub κ (by rw [hok]; exact List.mem_append_left _ hκ))
      hde hU hci hmi rc hnw hst htd
      (by unfold caseKeysL at hwork; unfold Room; omega)
      as ⟨a, b, c1, s1, m₁, T₁, hR1, hF1, rn1, rs1, rt1, hE1, hN1, hS1⟩
    have ht1 := hR1.ticks
    step with uncons_repr s1 r hR1.wf (hR1.ext.repr rr)
      (by unfold caseKeysL at hwork; unfold Room; omega) as ⟨o, s2, hK2, hu⟩
    have ht2 := hK2.ticks
    have R2 := hR1.trans hK2.ran.ranB
    have hF2 : FlagsK nm s2 U m₁ := hF1.mono hK2.ran.ext (by rw [hK2.tbl])
    cases hre : dd.rest with
    | none =>
      rw [hre] at hr
      simp only [RestAt] at hr
      subst hr
      simp only at hu
      subst hu
      rw [hre] at hok hwork
      simp only [List.append_nil] at hok
      simp only [WP.spec_ok]
      refine ⟨m₁, T₁, R2.mono (by unfold ownWork caseKeysL at *; simp only [keysWork] at hwork; omega),
        hF2, ?_, ?_, by rw [hK2.nodes]; exact rt1, hE1, ?_, ?_⟩
      · rw [hok, hK2.nodes]; exact rn1
      · rw [hok, hK2.nodes]; exact rs1
      · rw [hok]; exact hN1
      · rw [hok]; exact hS1
    | some er =>
      rw [hre] at hr
      simp only [RestAt] at hr
      obtain ⟨xs, hfa, rfl⟩ := hr
      simp only at hu
      obtain ⟨exi, kk, rfl, rex, -⟩ := hu
      obtain ⟨es, rfl, hes⟩ := exEnts hfa
      rw [hre] at hok hwork
      simp only at hok hwork
      simp only
      have hx : (es.map fun e => ((.sym e.1 : Pat), e.2)).map (entPat (nm none)) =
          es.map fun e => entPat (nm none) (.sym e.1, e.2) := by simp [Function.comp_def]
      step with expand_keys_spec hC d k μ hd (fun f a h => hμ (lookup_of_step h)) es s2 exi decls
        names ci mi a b c1 _ _ T₁ m₁ (R2.inv hI) hF2
        (fun e he => hsub _ (by
          rw [hok]; exact List.mem_append_right _ (by rw [← hes]; exact List.mem_map_of_mem he)))
        (R2.ext.repr hde) (R2.ext.repr hU) (R2.ext.repr hci) (R2.ext.repr hmi)
        (by rw [← hx, hK2.nodes]; exact rex) (by rw [hK2.nodes]; exact rn1)
        (by rw [hK2.nodes]; exact rs1) (by rw [hK2.nodes]; exact rt1)
        (by rw [hes]; unfold caseKeysL at hwork; unfold Room; omega)
        as ⟨r3, s3, m₂, T₂, hR3, hF3, rn3, rs3, rt3, hE3, hN3, hS3⟩
      rw [hes] at hR3 rn3 rs3 hN3 hS3
      refine ⟨m₂, T₂, (R2.trans hR3).mono (by unfold ownWork caseKeysL at *; omega), hF3, ?_, ?_,
        rt3, hE1.trans hE3, ?_, ?_⟩
      · rw [hok, keyNows_append]
        simpa [caseKeysL] using rn3
      · rw [hok, keySteps_append]
        simpa [caseKeysL] using rs3
      · intro g hg q hq
        rw [hok, keyNows_append] at hg
        rcases List.mem_append.1 hg with h | h
        · exact hE3.flagged (hN1 g h q hq)
        · exact hN3 g h q hq
      · intro a' ha
        rw [hok, keySteps_append] at ha
        rcases List.mem_append.1 ha with h | h
        · exact ⟨fun q hq => hE3.flagged ((hS1 a' h).1 q hq),
            fun q hq => hE3.flagged ((hS1 a' h).2 q hq)⟩
        · exact hS3 a' h

/-- The lists of guards of a key that make it hold with no edge. -/
noncomputable def pairNows (S : Sorts) (U : List Name) (d : Sorts.Conj) (μ : Name) :
    List (List Key) :=
  (keyNows S d μ (ownKeys S μ)).reverse ++
    ((keyNows S d μ ((conjList U (· ∈ d)).flatMap (defKeys S))).reverse ++ restNows S d μ)

/-- The guards with edges of a key. -/
noncomputable def pairSteps (S : Sorts) (U : List Name) (d : Sorts.Conj) (μ : Name) : List Step :=
  (keySteps S d μ (ownKeys S μ)).reverse ++
    ((keySteps S d μ ((conjList U (· ∈ d)).flatMap (defKeys S))).reverse ++ restSteps S d μ)

/-- The ticks the alternatives of a key may spend. -/
noncomputable def keyCost (S : Sorts) (U : List Name) (d : Sorts.Conj) (μ : Name) : Nat :=
  3 * S.length + 3 + restAltsCost S U.length + conjWork S U.length (conjList U (· ∈ d)) +
    ownWork S U.length μ

theorem expand_pair_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (k : Option Name) (μ : Name) (hd : Sub U d)
    (hμ : (S.lookup μ).isSome = true → k = some μ)
    (s : store.Store) (decls names ci mi todo : store.TermId) (T : List Key)
    (m : Key → Option Bool) (hI : Inv s) (hF : FlagsK nm s U m)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (hmi : Repr nm s.nodes.val mi.val (.sym μ))
    (htd : Repr nm s.nodes.val todo.val (keysPat (nm none) U T))
    (hroom : Room s (keyCost S U d μ)) :
    sorts.expand_pair s decls names ci mi todo ⦃ r s' => ∃ m' T',
      RanB s s' (keyCost S U d μ) ∧ FlagsK nm s' U m' ∧
        Repr nm s'.nodes.val r.1.val
          (.app (nowsPat (nm none) U (pairNows S U d μ)) (stepsPat (nm none) U (pairSteps S U d μ))) ∧
        Repr nm s'.nodes.val r.2.val (keysPat (nm none) U T') ∧
        Enq (Sorts.KidG S (d, k)) m m' T T' ∧
        (∀ g ∈ pairNows S U d μ, ∀ q ∈ g, m' q ≠ none) ∧
        ∀ a ∈ pairSteps S U d μ, (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none ⦄ := by
  unfold sorts.expand_pair
  have hroom' := hroom
  unfold Room keyCost at hroom'
  have hW := hI.toWf
  step with lookup_spec hC.inj S hC.sorts s decls mi hW hde hmi (by unfold Room; omega)
    as ⟨own, s1, hR1, hlk⟩
  have ho : OwnAt nm s.nodes.val S μ own := hlk
  have ht1 := hR1.ticks
  have hF1 : FlagsK nm s1 U m := hF.mono hR1.ext (by rw [hR1.tbl])
  step with rest_alts_spec hC d k μ hd hμ s1 decls names ci todo own T m (hR1.ranB.inv hI) hF1
    (hR1.ext.repr hde) (hR1.ext.repr hU) (hR1.ext.repr hci) (ho.mono hR1.ext) (hR1.ext.repr htd)
    (by unfold Room; omega) as ⟨n0, st0, t0, s2, m₁, T₁, hR2, hF2, rn2, rs2, rt2, hE2, hS2⟩
  have R2 := hR1.ranB.trans hR2
  have ht2 := R2.ticks
  step with conj_keys_spec hC d k μ hd hμ (conjList U (· ∈ d)) s2 ci decls names ci mi n0 st0 t0
    _ _ T₁ m₁ (R2.inv hI) hF2 (fun n hn => (mem_conjList.1 hn).2) (R2.ext.repr hde)
    (R2.ext.repr hU) (R2.ext.repr hci) (R2.ext.repr hmi) (R2.ext.repr hci) rn2 rs2 rt2
    (by unfold Room; omega) as ⟨n1, st1, t1, s3, m₂, T₂, hR3, hF3, rn3, rs3, rt3, hE3, hN3, hS3⟩
  have R3 := R2.trans hR3
  have ht3 := R3.ticks
  step with own_keys_spec hC d k μ hd hμ s3 decls names ci mi n1 st1 t1 own _ _ T₂ m₂ (R3.inv hI)
    hF3 (R3.ext.repr hde) (R3.ext.repr hU) (R3.ext.repr hci) (R3.ext.repr hmi) (ho.mono R3.ext)
    rn3 rs3 rt3 (by unfold Room; omega)
    as ⟨n2, st2, t2, s4, m₃, T₃, hR4, hF4, rn4, rs4, rt4, hE4, hN4, hS4⟩
  have R4 := R3.trans hR4
  have ht4 := R4.ticks
  step with alloc_w s4 (.App n2 st2) hR4.wf ⟨rn4.lt, rs4.lt⟩ (by unfold Room; omega)
    as ⟨alts, s5, hW5, ht5, htb5, hx5, hid5, hst5⟩
  refine ⟨m₃, T₃, ⟨hW5, R4.ext.trans hx5, by rw [hst5, R4.stk], by unfold keyCost; omega⟩,
    hF4.mono hx5 (by rw [htb5]), .app hid5 (hx5.repr rn4) (hx5.repr rs4), hx5.repr rt4,
    (hE2.trans hE3).trans hE4, ?_, ?_⟩
  · intro g hg q hq
    simp only [pairNows, List.mem_append, List.mem_reverse] at hg
    rcases hg with h | h | h
    · exact hN4 g h q hq
    · exact hE4.flagged (hN3 g h q hq)
    · simp only [restNows] at h
      split at h
      · rw [List.mem_singleton.1 h] at hq; cases hq
      · cases h
  · intro a ha
    simp only [pairSteps, List.mem_append, List.mem_reverse] at ha
    rcases ha with h | h | h
    · exact hS4 a h
    · exact ⟨fun q hq => hE4.flagged ((hS3 a h).1 q hq), fun q hq => hE4.flagged ((hS3 a h).2 q hq)⟩
    · refine ⟨fun q hq => ?_, fun q hq => hE4.flagged (hE3.flagged (hS2 a h q hq))⟩
      simp only [restSteps] at h
      split at h
      · split at h
        · rw [List.mem_singleton.1 h] at hq; cases hq
        · cases h
      · cases h

end RwLogVerified
