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

/-! ## What the alternatives of a key say -/

/-- The alternatives make a key hold, given the keys in `M`: every guard of
a list with no edges, or every guard and one edge of a list with edges. -/
def Sat (M : Key → Prop) (nows : List (List Key)) (steps : List Step) : Prop :=
  (∃ g ∈ nows, ∀ q ∈ g, M q) ∨ ∃ a ∈ steps, (∀ q ∈ a.1, M q) ∧ ∃ q ∈ a.2, M q

theorem mem_keyNows {S : Sorts} {d : Sorts.Conj} {μ : Name} {g : List Key} :
    ∀ {K : List (Sym × Nat)}, g ∈ keyNows S d μ K ↔
      ∃ κ ∈ K, Sorts.Accepts S d κ.1 κ.2 ∧ Sorts.step S μ κ.1 κ.2 = none ∧
        g = bareKeys (altOf S d κ.1 κ.2)
  | [] => by simp [keyNows]
  | κ :: K => by
    simp only [keyNows, List.mem_append, mem_keyNows (K := K), List.mem_cons, exists_eq_or_imp]
    refine or_congr ?_ Iff.rfl
    split
    · rename_i h
      simp [h.1, h.2]
    · rename_i h
      simp only [List.not_mem_nil, false_iff, not_and]
      exact fun h1 h2 _ => h ⟨h1, h2⟩

theorem mem_keySteps {S : Sorts} {d : Sorts.Conj} {μ : Name} {a : Step} :
    ∀ {K : List (Sym × Nat)}, a ∈ keySteps S d μ K ↔
      ∃ κ ∈ K, Sorts.Accepts S d κ.1 κ.2 ∧ ∃ kids, Sorts.step S μ κ.1 κ.2 = some kids ∧
        a = (bareKeys (altOf S d κ.1 κ.2), pairKeys (altOf S d κ.1 κ.2) kids)
  | [] => by simp [keySteps]
  | κ :: K => by
    simp only [keySteps, List.mem_append, mem_keySteps (K := K), List.mem_cons, exists_eq_or_imp]
    refine or_congr ?_ Iff.rfl
    by_cases hacc : Sorts.Accepts S d κ.1 κ.2
    · cases hs : Sorts.step S μ κ.1 κ.2 with
      | none => simp [hacc]
      | some kids => simp [hacc]
    · simp [hacc]

theorem bare_all {S : Sorts} {d : Sorts.Conj} {f : Sym} {a : Nat} {M : Key → Prop} :
    (∀ q ∈ bareKeys (altOf S d f a), M q) ↔ ∀ i < a, M (Sorts.kidC S d f a i, none) := by
  simp only [bareKeys, altOf, List.map_map, List.mem_reverse, List.mem_map, List.mem_range,
    Function.comp_apply]
  constructor
  · intro h i hi
    exact h _ ⟨i, hi, rfl⟩
  · rintro h q ⟨i, hi, rfl⟩
    exact h i hi

theorem pair_any {S : Sorts} {d : Sorts.Conj} {f : Sym} {a : Nat} {kids : List (Option Name)}
    {M : Key → Prop} :
    (∃ q ∈ pairKeys (altOf S d f a) kids, M q) ↔
      ∃ i < a, ∃ m, kids[i]? = some (some m) ∧ M (Sorts.kidC S d f a i, some m) := by
  have hlen : (altOf S d f a).length = a := by simp [altOf]
  constructor
  · rintro ⟨q, hq, hM⟩
    obtain ⟨i, hi, m, hk, rfl⟩ := mem_pairKeys.1 hq
    refine ⟨i, by rw [← hlen]; exact hi, m, hk, ?_⟩
    simpa [altOf] using hM
  · rintro ⟨i, hi, m, hk, hM⟩
    refine ⟨_, mem_pairKeys.2 ⟨i, by rw [hlen]; exact hi, m, hk, rfl⟩, ?_⟩
    simpa [altOf] using hM

theorem mem_conjKeys {S : Sorts} {U : List Name} {d : Sorts.Conj} (hd : Sub U d)
    {κ : Sym × Nat} :
    κ ∈ (conjList U (· ∈ d)).flatMap (defKeys S) ↔ κ ∈ Sorts.caseKeys S d := by
  constructor
  · intro h
    obtain ⟨n, hn, hκ⟩ := List.mem_flatMap.1 h
    exact defKeys_sub (mem_conjList.1 hn).2 hκ
  · intro h
    obtain ⟨f, a⟩ := κ
    obtain ⟨n, hn, dd, hl, c, hc, rfl, rfl⟩ := Sorts.mem_caseKeys.1 h
    refine List.mem_flatMap.2 ⟨n, mem_conjList.2 ⟨hd n hn, hn⟩, ?_⟩
    simp only [defKeys, hl, caseKeysL]
    exact List.mem_map_of_mem hc

theorem mem_ownKeys {S : Sorts} {μ : Name} {κ : Sym × Nat} :
    κ ∈ ownKeys S μ ↔ κ ∈ Sorts.caseKeys S {μ} ∪ Sorts.exKeys S μ := by
  constructor
  · intro h
    have := ownKeys_sub (d := ∅) h
    simp only [Sorts.keysOf, Finset.mem_union] at this ⊢
    rcases this with (h | h) | h
    · simp [Sorts.caseKeys] at h
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    obtain ⟨f, a⟩ := κ
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨n, hn, dd, hl, c, hc, rfl, rfl⟩ := Sorts.mem_caseKeys.1 h
      rw [Finset.mem_singleton.1 hn] at hl
      simp only [ownKeys, hl, caseKeysL]
      exact List.mem_append_left _ (List.mem_map_of_mem hc)
    · unfold Sorts.exKeys at h
      cases hl : S.lookup μ with
      | none => simp [hl] at h
      | some dd =>
        cases hre : dd.rest with
        | none => simp [hl, hre] at h
        | some r =>
          simp only [hl, hre, Option.bind_some, List.mem_toFinset] at h
          simp only [ownKeys, hl, hre]
          exact List.mem_append_right _ h

theorem mem_pairNows {S : Sorts} {U : List Name} {d : Sorts.Conj} (hd : Sub U d) {μ : Name}
    {g : List Key} :
    g ∈ pairNows S U d μ ↔ g ∈ restNows S d μ ∨
      ∃ κ ∈ Sorts.caseKeys S d ∪ Sorts.caseKeys S {μ} ∪ Sorts.exKeys S μ,
        Sorts.Accepts S d κ.1 κ.2 ∧ Sorts.step S μ κ.1 κ.2 = none ∧
          g = bareKeys (altOf S d κ.1 κ.2) := by
  simp only [pairNows, List.mem_append, List.mem_reverse, mem_keyNows, mem_ownKeys,
    mem_conjKeys hd, Finset.mem_union]
  constructor
  · rintro (⟨κ, h, r⟩ | ⟨κ, h, r⟩ | h)
    · exact Or.inr ⟨κ, by tauto, r⟩
    · exact Or.inr ⟨κ, by tauto, r⟩
    · exact Or.inl h
  · rintro (h | ⟨κ, (h | h) | h, r⟩)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ⟨κ, h, r⟩)
    · exact Or.inl ⟨κ, Or.inl h, r⟩
    · exact Or.inl ⟨κ, Or.inr h, r⟩

theorem mem_pairSteps {S : Sorts} {U : List Name} {d : Sorts.Conj} (hd : Sub U d) {μ : Name}
    {a : Step} :
    a ∈ pairSteps S U d μ ↔ a ∈ restSteps S d μ ∨
      ∃ κ ∈ Sorts.caseKeys S d ∪ Sorts.caseKeys S {μ} ∪ Sorts.exKeys S μ,
        Sorts.Accepts S d κ.1 κ.2 ∧ ∃ kids, Sorts.step S μ κ.1 κ.2 = some kids ∧
          a = (bareKeys (altOf S d κ.1 κ.2), pairKeys (altOf S d κ.1 κ.2) kids) := by
  simp only [pairSteps, List.mem_append, List.mem_reverse, mem_keySteps, mem_ownKeys,
    mem_conjKeys hd, Finset.mem_union]
  constructor
  · rintro (⟨κ, h, r⟩ | ⟨κ, h, r⟩ | h)
    · exact Or.inr ⟨κ, by tauto, r⟩
    · exact Or.inr ⟨κ, by tauto, r⟩
    · exact Or.inl h
  · rintro (h | ⟨κ, (h | h) | h, r⟩)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ⟨κ, h, r⟩)
    · exact Or.inl ⟨κ, Or.inl h, r⟩
    · exact Or.inl ⟨κ, Or.inr h, r⟩

/-- The alternatives of a pair say what a round asks of it. -/
theorem sat_pair_iff {S : Sorts} {U : List Name} {d : Sorts.Conj} (hd : Sub U d) (μ : Name)
    (M : Key → Prop) :
    Sat M (pairNows S U d μ) (pairSteps S U d μ) ↔ Sorts.GrowsG S M (d, some μ) := by
  show _ ↔ Sorts.GrowsOut S (fun e => M (e, none)) (fun e m => M (e, some m)) d μ
  unfold Sat Sorts.GrowsOut
  constructor
  · rintro (⟨g, hg, hall⟩ | ⟨a, ha, hall, q, hq, hMq⟩)
    · rcases (mem_pairNows hd).1 hg with h | ⟨κ, hκ, hacc, hs, rfl⟩
      · simp only [restNows] at h
        split at h
        · rename_i hr; exact Or.inl hr
        · cases h
      · exact Or.inr (Or.inr ⟨κ, hκ, hacc, bare_all.1 hall, Or.inl (by rw [hs]; rfl)⟩)
    · rcases (mem_pairSteps hd).1 ha with h | ⟨κ, hκ, hacc, kids, hs, rfl⟩
      · simp only [restSteps] at h
        split at h
        · rename_i hr
          split at h
          · rename_i r hrk
            rw [List.mem_singleton.1 h] at hq
            rw [List.mem_singleton.1 hq] at hMq
            exact Or.inr (Or.inl ⟨hr, r, hrk, hMq⟩)
          · cases h
        · cases h
      · obtain ⟨i, hi, m, hk, hM⟩ := pair_any.1 ⟨q, hq, hMq⟩
        exact Or.inr (Or.inr ⟨κ, hκ, hacc, bare_all.1 hall,
          Or.inr ⟨i, hi, m, Sorts.stepKid_eq.2 ⟨kids, hs, hk⟩, hM⟩⟩)
  · rintro (hr | ⟨hr, m, hrk, hM⟩ | ⟨κ, hκ, hacc, hall, hn | ⟨i, hi, m, hsk, hM⟩⟩)
    · exact Or.inl ⟨[], (mem_pairNows hd).2 (Or.inl (by simp [restNows, hr])),
        fun _ h => (by cases h)⟩
    · exact Or.inr ⟨([], [(Sorts.restKids S d, some m)]),
        (mem_pairSteps hd).2 (Or.inl (by simp [restSteps, hr, hrk])),
        fun _ h => (by cases h), _, List.mem_singleton.2 rfl, hM⟩
    · have hs : Sorts.step S μ κ.1 κ.2 = none := by
        cases h : Sorts.step S μ κ.1 κ.2 with
        | none => rfl
        | some _ => rw [h] at hn; cases hn
      exact Or.inl ⟨_, (mem_pairNows hd).2 (Or.inr ⟨κ, hκ, hacc, hs, rfl⟩), bare_all.2 hall⟩
    · obtain ⟨kids, hs, hk⟩ := Sorts.stepKid_eq.1 hsk
      obtain ⟨q, hq, hMq⟩ := pair_any.2 ⟨i, hi, m, hk, hM⟩
      exact Or.inr ⟨_, (mem_pairSteps hd).2 (Or.inr ⟨κ, hκ, hacc, kids, hs, rfl⟩),
        bare_all.2 hall, q, hq, hMq⟩

/-- The alternatives of a conjunction with a name no declaration is of say
what a round asks of the conjunction alone. -/
theorem sat_bare_iff {S : Sorts} {U : List Name} {d : Sorts.Conj} (hd : Sub U d) {z : Name}
    (hz : S.lookup z = none) (M : Key → Prop) :
    Sat M (pairNows S U d z) (pairSteps S U d z) ↔ Sorts.GrowsG S M (d, none) := by
  show _ ↔ Sorts.Grows S (fun e => M (e, none)) d
  have hstep : ∀ f a, Sorts.step S z f a = none := fun f a => by simp [Sorts.step, hz]
  have hck : Sorts.caseKeys S {z} = ∅ := by simp [Sorts.caseKeys, hz]
  have hex : Sorts.exKeys S z = ∅ := by simp [Sorts.exKeys, hz]
  have hrk : Sorts.restKid S z = none := by simp [Sorts.restKid, hz]
  unfold Sat Sorts.Grows
  constructor
  · rintro (⟨g, hg, hall⟩ | ⟨a, ha, hall, q, hq, hMq⟩)
    · rcases (mem_pairNows hd).1 hg with h | ⟨κ, hκ, hacc, hs, rfl⟩
      · simp only [restNows] at h
        split at h
        · rename_i hr; exact Or.inl hr.1
        · cases h
      · rw [hck, hex] at hκ
        simp only [Finset.union_empty] at hκ
        exact Or.inr ⟨κ, hκ, hacc, bare_all.1 hall⟩
    · rcases (mem_pairSteps hd).1 ha with h | ⟨κ, hκ, hacc, kids, hs, rfl⟩
      · simp only [restSteps, hrk] at h
        split at h <;> cases h
      · rw [hstep] at hs; cases hs
  · rintro (hr | ⟨κ, hκ, hacc, hall⟩)
    · exact Or.inl ⟨[], (mem_pairNows hd).2 (Or.inl (by simp [restNows, hr, hz])),
        fun _ h => (by cases h)⟩
    · exact Or.inl ⟨_, (mem_pairNows hd).2 (Or.inr ⟨κ, by
        rw [hck, hex]; simpa using hκ, hacc, hstep _ _, rfl⟩), bare_all.2 hall⟩

/-! ## The keys a key reaches, with their alternatives -/

/-- A key with its alternatives. -/
abbrev KEntry := Key × List (List Key) × List Step

/-- The key of a graph with the alternatives the store gives it. -/
noncomputable def entryOf (S : Sorts) (U : List Name) (z : Name) (p : Key) : KEntry :=
  (p, pairNows S U p.1 (p.2.getD z), pairSteps S U p.1 (p.2.getD z))

noncomputable def entryKPat (z : Sym) (U : List Name) (e : KEntry) : Pat :=
  .app (keyPat z U e.1) (.app (nowsPat z U e.2.1) (stepsPat z U e.2.2))

/-- The keys gone through with their alternatives, as the store has them. -/
noncomputable def graphKPat (z : Sym) (U : List Name) (G : List KEntry) : Pat :=
  encList z (G.map (entryKPat z U))

theorem kidPat_getD (z : Sym) (k : Option Name) : kidPat z k = .sym (k.getD z) := by
  cases k <;> rfl

theorem Ctx.lookup_z {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) :
    S.lookup (nm none) = none := by
  cases h : S.lookup (nm none) with
  | none => rfl
  | some dd =>
    have hm := Sorts.mem_of_lookup h
    refine absurd rfl (hC.nz (nm none) ?_)
    simp only [Sorts.names, List.mem_toFinset, List.mem_flatMap]
    exact ⟨_, hm, List.mem_cons_self⟩

/-- A key one step away is named by an alternative. -/
theorem kidG_mem {S : Sorts} {U : List Name} {d : Sorts.Conj} (hd : Sub U d) {z : Name}
    {k : Option Name} {q : Key} (h : Sorts.KidG S (d, k) q) :
    (∃ g ∈ pairNows S U d (k.getD z), q ∈ g) ∨
      ∃ a ∈ pairSteps S U d (k.getD z), q ∈ a.1 ∨ q ∈ a.2 := by
  have hbare : ∀ f a i, i < a → ((Sorts.kidC S d f a i, none) : Key) ∈ bareKeys (altOf S d f a) :=
    fun f a i hi => by
      simp only [bareKeys, altOf, List.map_map, List.mem_reverse, List.mem_map, List.mem_range,
        Function.comp_apply]
      exact ⟨i, hi, rfl⟩
  rcases h with ⟨key, hkey, hacc, i, hi, rfl⟩ | ⟨n, m', hk, hm, hko⟩
  · have hkey' : key ∈ Sorts.caseKeys S d ∪ Sorts.caseKeys S {k.getD z} ∪
        Sorts.exKeys S (k.getD z) := by
      cases k with
      | none => exact Finset.mem_union_left _ (Finset.mem_union_left _ hkey)
      | some n => exact hkey
    cases hs : Sorts.step S (k.getD z) key.1 key.2 with
    | none =>
      exact Or.inl ⟨_, (mem_pairNows hd).2 (Or.inr ⟨key, hkey', hacc, hs, rfl⟩), hbare _ _ i hi⟩
    | some kids =>
      exact Or.inr ⟨_, (mem_pairSteps hd).2 (Or.inr ⟨key, hkey', hacc, kids, hs, rfl⟩),
        Or.inl (hbare _ _ i hi)⟩
  · simp only at hk hm hko
    subst hk
    obtain ⟨e, k'⟩ := q
    simp only at hm hko
    subst hm
    simp only [Option.getD_some]
    rcases hko with ⟨hr, hrk, rfl⟩ | ⟨key, hkey, hacc, i, hi, hsk, rfl⟩
    · exact Or.inr ⟨([], [(Sorts.restKids S d, some m')]),
        (mem_pairSteps hd).2 (Or.inl (by simp [restSteps, hr, hrk])),
        Or.inr (List.mem_singleton.2 rfl)⟩
    · obtain ⟨kids, hs, hki⟩ := Sorts.stepKid_eq.1 hsk
      refine Or.inr ⟨_, (mem_pairSteps hd).2 (Or.inr ⟨key, hkey, hacc, kids, hs, rfl⟩),
        Or.inr (mem_pairKeys.2 ⟨i, by simpa [altOf] using hi, m', hki, by simp [altOf]⟩)⟩

/-- What holds while the keys are gone through: `T` are still to go
through, `Dn` are done, and table `B` flags exactly these. Every key flagged
is reached from `p₀`, and the keys the alternatives of a key done name are
flagged. -/
structure WalkG (S : Sorts) (U : List Name) (z : Name) (p₀ : Key) (T Dn : List Key)
    (m : Key → Option Bool) : Prop where
  nodup : (T ++ Dn).Nodup
  dom : ∀ q, m q ≠ none ↔ q ∈ T ∨ q ∈ Dn
  root : m p₀ ≠ none
  reach : ∀ q, m q ≠ none → Sorts.ReachG S p₀ q
  done : ∀ p ∈ Dn, (∀ g ∈ (entryOf S U z p).2.1, ∀ q ∈ g, m q ≠ none) ∧
    ∀ a ∈ (entryOf S U z p).2.2, (∀ q ∈ a.1, m q ≠ none) ∧ ∀ q ∈ a.2, m q ≠ none

theorem WalkG.expand {S : Sorts} {U : List Name} {z : Name} {p₀ p : Key} {T T' Dn : List Key}
    {m m' : Key → Option Bool} (h : WalkG S U z p₀ (p :: T) Dn m)
    (hE : Enq (Sorts.KidG S p) m m' T T')
    (hN : ∀ g ∈ (entryOf S U z p).2.1, ∀ q ∈ g, m' q ≠ none)
    (hS : ∀ a ∈ (entryOf S U z p).2.2, (∀ q ∈ a.1, m' q ≠ none) ∧ ∀ q ∈ a.2, m' q ≠ none) :
    WalkG S U z p₀ T' (p :: Dn) m' := by
  obtain ⟨new, rfl, nd, hnew, hm'⟩ := hE
  have hmd : m p ≠ none := (h.dom p).2 (Or.inl List.mem_cons_self)
  have hne : ∀ c, m' c ≠ none ↔ c ∈ new ∨ m c ≠ none := by
    intro c
    rw [hm']
    by_cases hc : c ∈ new <;> simp [hc]
  have hnd : ((new ++ T) ++ p :: Dn).Nodup := by
    rw [List.append_assoc]
    refine List.nodup_append.2 ⟨nd, (List.perm_middle.nodup_iff).2 (by simpa using h.nodup), ?_⟩
    intro x hx y hy e
    subst e
    have h0 := (hnew x hx).1
    have : m x ≠ none := (h.dom x).2 (by
      simp only [List.mem_append, List.mem_cons] at hy ⊢
      tauto)
    exact this h0
  refine ⟨hnd, fun c => ?_, (hne p₀).2 (Or.inr h.root), ?_, ?_⟩
  · rw [hne, h.dom]
    simp only [List.mem_append, List.mem_cons]
    tauto
  · intro c hc
    rcases (hne c).1 hc with hc | hc
    · exact (h.reach p hmd).step (hnew c hc).2
    · exact h.reach c hc
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨hN, hS⟩
    · obtain ⟨h1, h2⟩ := h.done c hc
      exact ⟨fun g hg q hq => (hne q).2 (Or.inr (h1 g hg q hq)),
        fun a ha => ⟨fun q hq => (hne q).2 (Or.inr ((h2 a ha).1 q hq)),
          fun q hq => (hne q).2 (Or.inr ((h2 a ha).2 q hq))⟩⟩

theorem WalkG.lt_card {S : Sorts} {U : List Name} {z : Name} {p₀ p : Key} {T Dn : List Key}
    {m : Key → Option Bool} (h : WalkG S U z p₀ (p :: T) Dn m) :
    Dn.length < (Sorts.reachGSet S p₀).card := by
  have hnd : (p :: Dn).Nodup := by
    have := h.nodup
    simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at this
    exact List.nodup_cons.2 ⟨this.1.2, (List.nodup_append.1 this.2).2.1⟩
  have hsub : (p :: Dn).toFinset ⊆ Sorts.reachGSet S p₀ := by
    intro c hc
    rw [List.mem_toFinset] at hc
    refine Sorts.mem_reachGSet.2 (h.reach c ((h.dom c).2 ?_))
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Or.inl List.mem_cons_self
    · exact Or.inr hc
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  simpa using this

theorem WalkG.len_le {S : Sorts} {U : List Name} {z : Name} {p₀ : Key} {T Dn : List Key}
    {m : Key → Option Bool} (h : WalkG S U z p₀ T Dn m) :
    Dn.length ≤ (Sorts.reachGSet S p₀).card := by
  have hnd : Dn.Nodup := (List.nodup_append.1 h.nodup).2.1
  have hsub : Dn.toFinset ⊆ Sorts.reachGSet S p₀ := by
    intro c hc
    rw [List.mem_toFinset] at hc
    exact Sorts.mem_reachGSet.2 (h.reach c ((h.dom c).2 (Or.inr hc)))
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd] at this

/-- When nothing is still to go through, the keys an alternative of a key
done names are done. -/
theorem WalkG.closed {S : Sorts} {U : List Name} {z : Name} {p₀ : Key} {Dn : List Key}
    {m : Key → Option Bool} (h : WalkG S U z p₀ [] Dn m) {p : Key} (hp : p ∈ Dn) :
    (∀ g ∈ (entryOf S U z p).2.1, ∀ q ∈ g, q ∈ Dn) ∧
      ∀ a ∈ (entryOf S U z p).2.2, (∀ q ∈ a.1, q ∈ Dn) ∧ ∀ q ∈ a.2, q ∈ Dn := by
  have hin : ∀ c, m c ≠ none → c ∈ Dn := fun c hc => by
    rcases (h.dom c).1 hc with h | h
    · cases h
    · exact h
  obtain ⟨h1, h2⟩ := h.done p hp
  exact ⟨fun g hg q hq => hin q (h1 g hg q hq),
    fun a ha => ⟨fun q hq => hin q ((h2 a ha).1 q hq), fun q hq => hin q ((h2 a ha).2 q hq)⟩⟩

/-- When nothing is still to go through, every key reached is done. -/
theorem WalkG.reached {S : Sorts} {U : List Name} {z : Name}
    {p₀ : Key} {Dn : List Key} {m : Key → Option Bool} (h : WalkG S U z p₀ [] Dn m)
    (hsub : ∀ c ∈ Dn, Sub U c.1) {q : Key} (hq : Sorts.ReachG S p₀ q) : q ∈ Dn := by
  induction hq with
  | refl =>
    rcases (h.dom p₀).1 h.root with h | h
    · cases h
    · exact h
  | @step p q _ hk ih =>
    obtain ⟨d, k⟩ := p
    obtain ⟨h1, h2⟩ := h.closed ih
    rcases kidG_mem (hsub _ ih) hk with ⟨g, hg, hq⟩ | ⟨a, ha, hq | hq⟩
    · exact h1 g hg q hq
    · exact (h2 a ha).1 q hq
    · exact (h2 a ha).2 q hq

/-! ## What going through a key may spend -/

/-- The roots of a declaration: its cases and what its rest excludes. -/
def defKeysL (dd : SortDef) : List (Sym × Nat) :=
  caseKeysL dd ++ (match dd.rest with | some r => r.1 | none => [])

/-- A bound on the ticks going through the roots of one declaration may
spend: those of all of them together. -/
def sortsKW (S : Sorts) (u : Nat) : Nat := (S.map fun p => keysWork S u (defKeysL p.2)).sum + 1

theorem keysWork_pos (S : Sorts) (u : Nat) : ∀ K : List (Sym × Nat), 1 ≤ keysWork S u K
  | [] => by simp [keysWork]
  | _ :: K => by simp only [keysWork]; omega

theorem keysWork_le_append (S : Sorts) (u : Nat) (K K' : List (Sym × Nat)) :
    keysWork S u K ≤ keysWork S u (K ++ K') := by
  have := keysWork_append S u K K'
  have := keysWork_pos S u K'
  omega

theorem defKeys_work_le (S : Sorts) (u : Nat) (n : Name) :
    keysWork S u (defKeys S n) ≤ sortsKW S u := by
  cases h : S.lookup n with
  | none =>
    have e : defKeys S n = [] := by simp [defKeys, h]
    rw [e]; simp [keysWork, sortsKW]
  | some dd =>
    have e : defKeys S n = caseKeysL dd := by simp [defKeys, h]
    have hm := Sorts.mem_of_lookup h
    have h1 : keysWork S u (defKeysL dd) ≤ (S.map fun p => keysWork S u (defKeysL p.2)).sum :=
      List.le_sum_of_mem (List.mem_map.2 ⟨(n, dd), hm, rfl⟩)
    have h2 : keysWork S u (caseKeysL dd) ≤ keysWork S u (defKeysL dd) :=
      keysWork_le_append S u (caseKeysL dd) _
    rw [e]; unfold sortsKW
    omega

theorem ownKeys_work_le (S : Sorts) (u : Nat) (μ : Name) :
    keysWork S u (ownKeys S μ) ≤ sortsKW S u := by
  cases h : S.lookup μ with
  | none =>
    have e : ownKeys S μ = [] := by simp [ownKeys, h]
    rw [e]; simp [keysWork, sortsKW]
  | some dd =>
    have e : ownKeys S μ = defKeysL dd := by simp [ownKeys, h, defKeysL]
    have hm := Sorts.mem_of_lookup h
    have h1 : keysWork S u (defKeysL dd) ≤ (S.map fun p => keysWork S u (defKeysL p.2)).sum :=
      List.le_sum_of_mem (List.mem_map.2 ⟨(μ, dd), hm, rfl⟩)
    rw [e]; unfold sortsKW
    omega

theorem conjWork_le (S : Sorts) (u : Nat) : ∀ xs : List Name,
    conjWork S u xs ≤ xs.length * (3 * S.length + 3 + sortsKW S u) + 1
  | [] => by simp [conjWork]
  | n :: xs => by
    have h1 := conjWork_le S u xs
    have h2 := defKeys_work_le S u n
    simp only [conjWork, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The ticks the alternatives of any key may spend. -/
def keyW (S : Sorts) (u : Nat) : Nat :=
  3 * S.length + 6 + restAltsCost S u + u * (3 * S.length + 3 + sortsKW S u) + sortsKW S u

theorem keyCost_le (S : Sorts) (U : List Name) (d : Sorts.Conj) (μ : Name) :
    keyCost S U d μ ≤ keyW S U.length := by
  have h1 := conjWork_le S U.length (conjList U (· ∈ d))
  have h2 := ownKeys_work_le S U.length μ
  have h3 := Nat.mul_le_mul_right (3 * S.length + 3 + sortsKW S U.length)
    (length_conjList_le U (· ∈ d))
  unfold keyCost keyW ownWork
  omega

/-- The ticks going through one key may spend. -/
def nodeGCost (S : Sorts) (u : Nat) : Nat := keyW S u + 4

theorem out_graph_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (p₀ : Key) (decls names : store.TermId) :
    ∀ (n : Nat) (s : store.Store) (todo graph : store.TermId) (T Dn : List Key)
      (m : Key → Option Bool),
    (Sorts.reachGSet S p₀).card ≤ Dn.length + n → Inv s → FlagsK nm s U m →
    WalkG S U (nm none) p₀ T Dn m → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val todo.val (keysPat (nm none) U T) →
    Repr nm s.nodes.val graph.val (graphKPat (nm none) U (Dn.map (entryOf S U (nm none)))) →
    Room s (n * nodeGCost S U.length + 1) →
    sorts.out_graph_loop todo s decls names graph ⦃ r => ∃ m' Dn',
      RanB s r.2 (n * nodeGCost S U.length + 1) ∧ FlagsK nm r.2 U m' ∧
        Repr nm r.2.nodes.val r.1.val
          (graphKPat (nm none) U (Dn'.map (entryOf S U (nm none)))) ∧
        WalkG S U (nm none) p₀ [] Dn' m' ⦄ := by
  intro n
  induction n with
  | zero =>
    intro s todo graph T Dn m hcard hI hF hInv hde hU htd hg hroom
    cases T with
    | cons d T => have := hInv.lt_card; omega
    | nil =>
      have hroom' := hroom
      unfold Room at hroom'
      unfold sorts.out_graph_loop
      rw [loop]
      simp only [sorts.out_graph_loop.body]
      step with uncons_repr s todo hI.toWf htd (by unfold Room; omega) as ⟨r0, hK, hu⟩
      obtain ⟨o, s1⟩ := r0
      simp only [keysPat] at hu
      simp only at hK
      subst hu
      have hfin : ∃ m' Dn', RanB s s1 (0 * nodeGCost S U.length + 1) ∧ FlagsK nm s1 U m' ∧
          Repr nm s1.nodes.val graph.val
            (graphKPat (nm none) U (Dn'.map (entryOf S U (nm none)))) ∧
          WalkG S U (nm none) p₀ [] Dn' m' :=
        ⟨m, Dn, hK.ran.ranB.mono (by omega), hF.mono hK.ran.ext (by rw [hK.tbl]),
          by rw [hK.nodes]; exact hg, hInv⟩
      step*
  | succ n ih =>
    intro s todo graph T Dn m hcard hI hF hInv hde hU htd hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [Nat.add_mul, Nat.one_mul, nodeGCost] at hroom'
    have hW := hI.toWf
    unfold sorts.out_graph_loop
    rw [loop]
    simp only [sorts.out_graph_loop.body]
    step with uncons_repr s todo hW htd (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [keysPat] at hu
    simp only at hK
    cases T with
    | nil =>
      subst hu
      have hfin : ∃ m' Dn', RanB s s1 ((n + 1) * nodeGCost S U.length + 1) ∧
          FlagsK nm s1 U m' ∧ Repr nm s1.nodes.val graph.val
            (graphKPat (nm none) U (Dn'.map (entryOf S U (nm none)))) ∧
          WalkG S U (nm none) p₀ [] Dn' m' :=
        ⟨m, Dn, hK.ran.ranB.mono (by omega), hF.mono hK.ran.ext (by rw [hK.tbl]),
          by rw [hK.nodes]; exact hg, hInv⟩
      step*
    | cons p T =>
      obtain ⟨d, k⟩ := p
      obtain ⟨pi, t, rfl, rp, rt⟩ := hu
      have ht1 := hK.ticks
      have hmd : m (d, k) ≠ none := (hInv.dom (d, k)).2 (Or.inl List.mem_cons_self)
      have hok : KeyOK (nm none) U (d, k) := (hF.has (d, k) hmd).1
      have hsub : Sub U d := hok.1
      step with uncons_repr s1 pi hK.wf (by rw [hK.nodes]; exact rp) (by unfold Room; omega)
        as ⟨r1, hK2, hu2⟩
      obtain ⟨o1, s2⟩ := r1
      simp only [keyPat] at hu2
      simp only at hK2
      obtain ⟨di, mi, rfl, rd, rmi⟩ := hu2
      rw [hK.nodes] at rd rmi
      rw [kidPat_getD] at rmi
      have ht2 := hK2.ticks
      have R2 : Ran s s2 2 := hK.ran.trans hK2.ran
      have hF2 : FlagsK nm s2 U m := hF.mono R2.ext (by rw [R2.tbl])
      have hμ : (S.lookup (k.getD (nm none))).isSome = true → k = some (k.getD (nm none)) := by
        cases k with
        | none => intro h; simp [hC.lookup_z] at h
        | some n => intro _; rfl
      have hkc := keyCost_le S U d (k.getD (nm none))
      simp only [uncurry]
      step with expand_pair_spec hC d k (k.getD (nm none)) hsub hμ s2 decls names di mi t T m
        (R2.ranB.inv hI) hF2 (R2.ext.repr hde) (R2.ext.repr hU) (R2.ext.repr rd)
        (R2.ext.repr rmi) (R2.ext.repr rt) (by unfold Room; omega)
        as ⟨r3, m₁, T₁, hR3, hF3, ral, rtd, hE, hallN, hallS⟩
      obtain ⟨⟨alts, td⟩, s3⟩ := r3
      simp only at hR3 hF3 ral rtd
      have ht3 := hR3.ticks
      have R3 := R2.ranB.trans hR3
      have rp3 : Repr nm s3.nodes.val pi.val (keyPat (nm none) U (d, k)) := R3.ext.repr rp
      step with alloc_w s3 (.App pi alts) hR3.wf ⟨rp3.lt, ral.lt⟩
        (by unfold Room; omega) as ⟨r4, hW4, ht4, htb4, hx4, hid4, hst4⟩
      obtain ⟨entry, s4⟩ := r4
      simp only at hW4 ht4 htb4 hx4 hid4 hst4 ⊢
      have rentry : Repr nm s4.nodes.val entry.val
          (entryKPat (nm none) U (entryOf S U (nm none) (d, k))) :=
        .app hid4 (hx4.repr rp3) (hx4.repr ral)
      step with alloc_w s4 (.App entry graph) hW4 ⟨rentry.lt, (hx4.repr (R3.ext.repr hg)).lt⟩
        (by unfold Room; omega) as ⟨r5, hW5, ht5, htb5, hx5, hid5, hst5⟩
      obtain ⟨graph1, s5⟩ := r5
      simp only at hW5 ht5 htb5 hx5 hid5 hst5 ⊢
      have R5 : RanB s s5 (nodeGCost S U.length) :=
        ⟨hW5, (R3.ext.trans hx4).trans hx5, by rw [hst5, hst4, R3.stk], by
          simp only [nodeGCost]; omega⟩
      have rg1 : Repr nm s5.nodes.val graph1.val
          (graphKPat (nm none) U (((d, k) :: Dn).map (entryOf S U (nm none)))) := by
        simp only [graphKPat, List.map_cons, encList]
        exact .app hid5 (hx5.repr rentry) (R5.ext.repr hg)
      have hInv' : WalkG S U (nm none) p₀ T₁ ((d, k) :: Dn) m₁ := hInv.expand hE hallN hallS
      have := R5.ticks
      simp only [nodeGCost] at this
      have IH := ih s5 td graph1 T₁ ((d, k) :: Dn) m₁
        (by simp only [List.length_cons]; omega) (R5.inv hI)
        ((hF3.mono hx4 (by rw [htb4])).mono hx5 (by rw [htb5])) hInv' (R5.ext.repr hde)
        (R5.ext.repr hU) (hx5.repr (hx4.repr rtd)) rg1
        (by unfold Room; simp only [nodeGCost]; omega)
      unfold sorts.out_graph_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro r ⟨m', Dn', hR, hFm, hrg, hInv''⟩
      exact ⟨m', Dn', (R5.trans hR).mono (by simp only [Nat.add_mul, Nat.one_mul]; omega),
        hFm, hrg, hInv''⟩

/-- `out_graph` goes through the keys the key reaches, each once, and gives
them with their alternatives. Table `B` flags the keys gone through. -/
theorem out_graph_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (p₀ : Key) (hp : KeyOK (nm none) U p₀) (s : store.Store) (decls names pi : store.TermId)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hpi : Repr nm s.nodes.val pi.val (keyPat (nm none) U p₀))
    (hroom : Room s ((Sorts.reachGSet S p₀).card * nodeGCost S U.length + 5)) :
    sorts.out_graph s decls names pi ⦃ r => ∃ m Dn,
      RanB s r.2 ((Sorts.reachGSet S p₀).card * nodeGCost S U.length + 5) ∧
        FlagsK nm r.2 U m ∧
        Repr nm r.2.nodes.val r.1.val
          (graphKPat (nm none) U (Dn.map (entryOf S U (nm none)))) ∧
        WalkG S U (nm none) p₀ [] Dn m ⦄ := by
  unfold sorts.out_graph
  have hroom' := hroom
  unfold Room at hroom'
  have hW := hI.toWf
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨nil, s1, hW1, ht1, htb1, hx1, hid1, hst1⟩
  step with clear_w s1 .B hW1 (by unfold Room; omega) as ⟨s2, hn2, ht2, hW2, hcl, hoth, hst2⟩
  have hx2 : Extends s s2 := hx1.trans (Extends.of_eq hn2 (by omega))
  step with set_flag_w s2 .B pi false hW2 (hx2.repr hpi).lt (by unfold Room; omega)
    as ⟨s3, hn3, ht3, hW3, htb3, htbo3, hst3⟩
  have hx3 : Extends s s3 := hx2.trans (Extends.of_eq hn3 (by omega))
  have hF2 : FlagsK nm s2 U fun _ => none := Flags.clear hcl
  have hF3 := hF2.set hC.inj (keyPat_patInj (nm none) U) hW2 (b := false) hp (hx2.repr hpi) hn3
    (by simpa using htb3)
  have rnil : Repr nm s3.nodes.val nil.val (.sym (nm none)) := by
    rw [hn3, hn2]; exact .nil hid1
  step with alloc_w s3 (.App pi nil) hW3 ⟨(hx3.repr hpi).lt, rnil.lt⟩ (by unfold Room; omega)
    as ⟨todo, s4, hW4, ht4, htb4, hx4, hid4, hst4⟩
  have R4 : RanB s s4 4 := ⟨hW4, hx3.trans hx4, by rw [hst4, hst3, hst2, hst1], by omega⟩
  have hInv : WalkG S U (nm none) p₀ [p₀] [] (Function.update (fun _ => none) p₀ (some false)) := by
    have hne : ∀ q, Function.update (fun _ : Key => (none : Option Bool)) p₀ (some false) q
        ≠ none ↔ q = p₀ := by
      intro q
      by_cases h : q = p₀
      · subst h; simp
      · simp [h]
    refine ⟨by simp, fun q => by rw [hne]; simp, (hne p₀).2 rfl, fun q h => ?_,
      fun q h => (by cases h)⟩
    rw [(hne q).1 h]; exact .refl
  have rtodo : Repr nm s4.nodes.val todo.val (keysPat (nm none) U [p₀]) := by
    simp only [keysPat, List.map_cons, List.map_nil, encList]
    exact .app hid4 (hx4.repr (hx3.repr hpi)) (hx4.repr rnil)
  have rgraph : Repr nm s4.nodes.val nil.val
      (graphKPat (nm none) U (([] : List Key).map (entryOf S U (nm none)))) := hx4.repr rnil
  refine WP.spec_mono (out_graph_loop_spec hC p₀ decls names (Sorts.reachGSet S p₀).card s4 todo
    nil [p₀] [] _ (by simp) (R4.inv hI) (hF3.mono hx4 (by rw [htb4])) hInv (R4.ext.repr hde)
    (R4.ext.repr hU) rtodo rgraph (by unfold Room; omega)) ?_
  rintro r ⟨m', Dn', hR, hFm, hrg, hInv'⟩
  exact ⟨m', Dn', (R4.trans hR).mono (by omega), hFm, hrg, hInv'⟩

/-! ## Is every key of a list flagged, is some key -/

/-- Table `A` flags the keys as `m` says. -/
abbrev FlagsO (nm : Option Nat → RwLog.Sym) (s : store.Store) (U : List Name)
    (m : Key → Option Bool) : Prop :=
  Flags nm s .A (keyPat (nm none) U) (KeyOK (nm none) U) m

theorem all_out_done (s : store.Store) (pairs : store.TermId) (ok1 : Bool) :
    sorts.all_out_loop s pairs ok1 false ⦃ r => r = (ok1, s) ⦄ := by
  unfold sorts.all_out_loop
  rw [loop]
  simp only [sorts.all_out_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem all_out_loop_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Key → Option Bool} :
    ∀ (g : List Key) (s : store.Store) (pairs : store.TermId), Wf s → FlagsO nm s U m →
    (∀ q ∈ g, KeyOK (nm none) U q) → Repr nm s.nodes.val pairs.val (keysPat (nm none) U g) →
    Room s (2 * g.length + 1) →
    sorts.all_out_loop s pairs true true ⦃ r =>
      Ran s r.2 (2 * g.length + 1) ∧ (r.1 = true ↔ ∀ q ∈ g, m q ≠ none) ⦄ := by
  intro g
  induction g with
  | nil =>
    intro s pairs hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.all_out_loop
    rw [loop]
    simp only [sorts.all_out_loop.body, ↓reduceIte]
    step with uncons_repr s pairs hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [keysPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := all_out_done s1 pairs true
    unfold sorts.all_out_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by omega), by simp⟩
  | cons x g ih =>
    intro s pairs hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.all_out_loop
    rw [loop]
    simp only [sorts.all_out_loop.body, ↓reduceIte]
    step with uncons_repr s pairs hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [keysPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with get_flag_w s1 .A k hK.wf (by rw [hK.nodes]; exact rk.lt) (by unfold Room; omega)
      as ⟨r1, hfl, hK2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hfl hK2
    have ht2 := hK2.ticks
    have hmx : o1 = m x := by
      rw [hfl]
      have := hF.get hnm (keyPat_patInj (nm none) U) hW (hs x List.mem_cons_self) rk
      simp only [flagT] at this
      rw [hK.tbl]; exact this
    have R2 : Ran s s2 2 := (hK.ran.trans hK2.ran)
    cases o1 with
    | none =>
      simp only [uncurry, bind_ok]
      have hdn := all_out_done s2 pairs false
      unfold sorts.all_out_loop at hdn
      refine WP.spec_mono hdn ?_
      rintro r rfl
      exact ⟨R2.mono (by simp only [List.length_cons]; omega),
        fun h => (by cases h), fun h => absurd hmx.symm (h x List.mem_cons_self)⟩
    | some b =>
      simp only [uncurry, bind_ok]
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
      have IH := ih s2 t hK2.wf (hF.mono R2.ext (by rw [R2.tbl]))
        (fun c hc => hs c (List.mem_cons_of_mem _ hc)) (by rw [hn2]; exact rt)
        (by unfold Room; omega)
      unfold sorts.all_out_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R2.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
      rw [hr]
      constructor
      · intro h q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [← hmx]; simp
        · exact h q hq
      · intro h q hq
        exact h q (List.mem_cons_of_mem _ hq)

/-- `all_out` answers whether table `A` flags every key of the list. -/
theorem all_out_spec (hnm : Function.Injective nm) {U : List Name} {m : Key → Option Bool}
    (g : List Key) (s : store.Store) (pairs : store.TermId) (hW : Wf s) (hF : FlagsO nm s U m)
    (hs : ∀ q ∈ g, KeyOK (nm none) U q)
    (hk : Repr nm s.nodes.val pairs.val (keysPat (nm none) U g))
    (hroom : Room s (2 * g.length + 1)) :
    sorts.all_out s pairs ⦃ r =>
      Ran s r.2 (2 * g.length + 1) ∧ (r.1 = true ↔ ∀ q ∈ g, m q ≠ none) ⦄ :=
  all_out_loop_spec hnm g s pairs hW hF hs hk hroom

theorem any_out_done (s : store.Store) (pairs : store.TermId) (found : Bool) :
    sorts.any_out_loop s pairs found false ⦃ r => r = (found, s) ⦄ := by
  unfold sorts.any_out_loop
  rw [loop]
  simp only [sorts.any_out_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem any_out_loop_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Key → Option Bool} :
    ∀ (g : List Key) (s : store.Store) (pairs : store.TermId), Wf s → FlagsO nm s U m →
    (∀ q ∈ g, KeyOK (nm none) U q) → Repr nm s.nodes.val pairs.val (keysPat (nm none) U g) →
    Room s (2 * g.length + 1) →
    sorts.any_out_loop s pairs false true ⦃ r =>
      Ran s r.2 (2 * g.length + 1) ∧ (r.1 = true ↔ ∃ q ∈ g, m q ≠ none) ⦄ := by
  intro g
  induction g with
  | nil =>
    intro s pairs hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.any_out_loop
    rw [loop]
    simp only [sorts.any_out_loop.body, ↓reduceIte]
    step with uncons_repr s pairs hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [keysPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := any_out_done s1 pairs false
    unfold sorts.any_out_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by omega), by simp⟩
  | cons x g ih =>
    intro s pairs hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.any_out_loop
    rw [loop]
    simp only [sorts.any_out_loop.body, ↓reduceIte]
    step with uncons_repr s pairs hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [keysPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with get_flag_w s1 .A k hK.wf (by rw [hK.nodes]; exact rk.lt) (by unfold Room; omega)
      as ⟨r1, hfl, hK2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hfl hK2
    have ht2 := hK2.ticks
    have hmx : o1 = m x := by
      rw [hfl]
      have := hF.get hnm (keyPat_patInj (nm none) U) hW (hs x List.mem_cons_self) rk
      simp only [flagT] at this
      rw [hK.tbl]; exact this
    have R2 : Ran s s2 2 := (hK.ran.trans hK2.ran)
    cases o1 with
    | some b =>
      simp only [uncurry, bind_ok]
      have hdn := any_out_done s2 pairs true
      unfold sorts.any_out_loop at hdn
      refine WP.spec_mono hdn ?_
      rintro r rfl
      exact ⟨R2.mono (by simp only [List.length_cons]; omega),
        fun _ => ⟨x, List.mem_cons_self, by rw [← hmx]; simp⟩, fun _ => rfl⟩
    | none =>
      simp only [uncurry, bind_ok]
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
      have IH := ih s2 t hK2.wf (hF.mono R2.ext (by rw [R2.tbl]))
        (fun c hc => hs c (List.mem_cons_of_mem _ hc)) (by rw [hn2]; exact rt)
        (by unfold Room; omega)
      unfold sorts.any_out_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R2.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
      rw [hr]
      constructor
      · rintro ⟨q, hq, h⟩
        exact ⟨q, List.mem_cons_of_mem _ hq, h⟩
      · rintro ⟨q, hq, h⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact absurd hmx.symm h
        · exact ⟨q, hq, h⟩

/-- `any_out` answers whether table `A` flags some key of the list. -/
theorem any_out_spec (hnm : Function.Injective nm) {U : List Name} {m : Key → Option Bool}
    (g : List Key) (s : store.Store) (pairs : store.TermId) (hW : Wf s) (hF : FlagsO nm s U m)
    (hs : ∀ q ∈ g, KeyOK (nm none) U q)
    (hk : Repr nm s.nodes.val pairs.val (keysPat (nm none) U g))
    (hroom : Room s (2 * g.length + 1)) :
    sorts.any_out s pairs ⦃ r =>
      Ran s r.2 (2 * g.length + 1) ∧ (r.1 = true ↔ ∃ q ∈ g, m q ≠ none) ⦄ :=
  any_out_loop_spec hnm g s pairs hW hF hs hk hroom

/-! ## Has some alternative all it asks -/

/-- The ticks going through lists of guards may spend. -/
def nowsW : List (List Key) → Nat
  | [] => 1
  | g :: l => 2 * g.length + 2 + nowsW l

theorem any_now_done (s : store.Store) (nows : store.TermId) (found : Bool) :
    sorts.any_now_loop s nows found false ⦃ r => r = (found, s) ⦄ := by
  unfold sorts.any_now_loop
  rw [loop]
  simp only [sorts.any_now_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem any_now_loop_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Key → Option Bool} :
    ∀ (l : List (List Key)) (s : store.Store) (nows : store.TermId), Wf s → FlagsO nm s U m →
    (∀ g ∈ l, ∀ q ∈ g, KeyOK (nm none) U q) →
    Repr nm s.nodes.val nows.val (nowsPat (nm none) U l) → Room s (nowsW l) →
    sorts.any_now_loop s nows false true ⦃ r =>
      Ran s r.2 (nowsW l) ∧ (r.1 = true ↔ ∃ g ∈ l, ∀ q ∈ g, m q ≠ none) ⦄ := by
  intro l
  induction l with
  | nil =>
    intro s nows hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [nowsW] at hroom'
    unfold sorts.any_now_loop
    rw [loop]
    simp only [sorts.any_now_loop.body, ↓reduceIte]
    step with uncons_repr s nows hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [nowsPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := any_now_done s1 nows false
    unfold sorts.any_now_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by simp only [nowsW]; omega), by simp⟩
  | cons x l ih =>
    intro s nows hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [nowsW] at hroom'
    unfold sorts.any_now_loop
    rw [loop]
    simp only [sorts.any_now_loop.body, ↓reduceIte]
    step with uncons_repr s nows hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [nowsPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with all_out_spec hnm x s1 k hK.wf (hF.mono hK.ran.ext (by rw [hK.tbl]))
      (hs x List.mem_cons_self) (by rw [hK.nodes]; exact rk) (by unfold Room; omega)
      as ⟨r1, hR2, hb⟩
    obtain ⟨b, s2⟩ := r1
    simp only at hR2 hb
    have ht2 := hR2.ticks
    have R2 : Ran s s2 (2 * x.length + 2) := (hK.ran.trans hR2).mono (by omega)
    cases b with
    | true =>
      have hdn := any_now_done s2 nows true
      unfold sorts.any_now_loop at hdn
      simp only [uncurry, ↓reduceIte, bind_ok]
      refine WP.spec_mono hdn ?_
      rintro r rfl
      exact ⟨R2.mono (by simp only [nowsW]; omega),
        fun _ => ⟨x, List.mem_cons_self, hb.1 rfl⟩, fun _ => rfl⟩
    | false =>
      have IH := ih s2 t hR2.wf (hF.mono R2.ext (by rw [R2.tbl]))
        (fun a ha => hs a (List.mem_cons_of_mem _ ha)) (R2.ext.repr rt) (by unfold Room; omega)
      unfold sorts.any_now_loop at IH
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R2.trans hR).mono (by simp only [nowsW]; omega), ?_⟩
      rw [hr]
      have hx : ¬ ∀ q ∈ x, m q ≠ none := fun h => Bool.noConfusion (hb.2 h)
      simp only [List.mem_cons, exists_eq_or_imp, hx, false_or]

/-- `any_now` answers whether table `A` flags every key of some list. -/
theorem any_now_spec (hnm : Function.Injective nm) {U : List Name} {m : Key → Option Bool}
    (l : List (List Key)) (s : store.Store) (nows : store.TermId) (hW : Wf s)
    (hF : FlagsO nm s U m) (hs : ∀ g ∈ l, ∀ q ∈ g, KeyOK (nm none) U q)
    (hk : Repr nm s.nodes.val nows.val (nowsPat (nm none) U l)) (hroom : Room s (nowsW l)) :
    sorts.any_now s nows ⦃ r =>
      Ran s r.2 (nowsW l) ∧ (r.1 = true ↔ ∃ g ∈ l, ∀ q ∈ g, m q ≠ none) ⦄ :=
  any_now_loop_spec hnm l s nows hW hF hs hk hroom

/-- The ticks going through guards with edges may spend. -/
def stepsW : List Step → Nat
  | [] => 1
  | a :: l => 2 * a.1.length + 2 * a.2.length + 4 + stepsW l

theorem any_step_done (s : store.Store) (steps : store.TermId) (found : Bool) :
    sorts.any_step_loop s steps found false ⦃ r => r = (found, s) ⦄ := by
  unfold sorts.any_step_loop
  rw [loop]
  simp only [sorts.any_step_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem any_step_loop_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Key → Option Bool} :
    ∀ (l : List Step) (s : store.Store) (steps : store.TermId), Wf s → FlagsO nm s U m →
    (∀ a ∈ l, (∀ q ∈ a.1, KeyOK (nm none) U q) ∧ ∀ q ∈ a.2, KeyOK (nm none) U q) →
    Repr nm s.nodes.val steps.val (stepsPat (nm none) U l) → Room s (stepsW l) →
    sorts.any_step_loop s steps false true ⦃ r =>
      Ran s r.2 (stepsW l) ∧
        (r.1 = true ↔ ∃ a ∈ l, (∀ q ∈ a.1, m q ≠ none) ∧ ∃ q ∈ a.2, m q ≠ none) ⦄ := by
  intro l
  induction l with
  | nil =>
    intro s steps hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [stepsW] at hroom'
    unfold sorts.any_step_loop
    rw [loop]
    simp only [sorts.any_step_loop.body, ↓reduceIte]
    step with uncons_repr s steps hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [stepsPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := any_step_done s1 steps false
    unfold sorts.any_step_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by simp only [stepsW]; omega), by simp⟩
  | cons x l ih =>
    intro s steps hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [stepsW] at hroom'
    obtain ⟨hs1, hs2⟩ := hs x List.mem_cons_self
    unfold sorts.any_step_loop
    rw [loop]
    simp only [sorts.any_step_loop.body, ↓reduceIte]
    step with uncons_repr s steps hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [stepsPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 k hK.wf (by rw [hK.nodes]; exact rk) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [stepPat] at hu2
    simp only at hK2
    obtain ⟨gi, ei, rfl, rg, re⟩ := hu2
    rw [hK.nodes] at rg re
    have ht2 := hK2.ticks
    have R2 : Ran s s2 2 := hK.ran.trans hK2.ran
    have rest : ∀ (s' : store.Store) (c : Nat), Ran s s' c →
        c ≤ 2 * x.1.length + 2 * x.2.length + 4 →
        ¬ ((∀ q ∈ x.1, m q ≠ none) ∧ ∃ q ∈ x.2, m q ≠ none) →
        loop (fun y => match y with
          | (s1, steps1, found1, go1) => sorts.any_step_loop.body s1 steps1 found1 go1)
          (s', t, false, true) ⦃ r =>
          Ran s r.2 (stepsW (x :: l)) ∧
            (r.1 = true ↔ ∃ a ∈ x :: l, (∀ q ∈ a.1, m q ≠ none) ∧ ∃ q ∈ a.2, m q ≠ none) ⦄ := by
      intro s' c R0 hc hx
      have htk := R0.ticks
      have IH := ih s' t R0.wf (hF.mono R0.ext (by rw [R0.tbl]))
        (fun a ha => hs a (List.mem_cons_of_mem _ ha)) (R0.ext.repr rt) (by unfold Room; omega)
      unfold sorts.any_step_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R0.trans hR).mono (by simp only [stepsW]; omega), ?_⟩
      rw [hr]
      simp only [List.mem_cons, exists_eq_or_imp, hx, false_or]
    step with all_out_spec hnm x.1 s2 gi hK2.wf (hF.mono R2.ext (by rw [R2.tbl])) hs1
      (R2.ext.repr rg) (by unfold Room; omega) as ⟨r3, hR3, hb⟩
    obtain ⟨b, s3⟩ := r3
    simp only at hR3 hb
    have ht3 := hR3.ticks
    have R3 := R2.trans hR3
    cases b with
    | false =>
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
      exact rest s3 _ R3 (by omega) fun h => Bool.noConfusion (hb.2 h.1)
    | true =>
      simp only [uncurry, ↓reduceIte]
      step with any_out_spec hnm x.2 s3 ei hR3.wf (hF.mono R3.ext (by rw [R3.tbl])) hs2
        (R3.ext.repr re) (by unfold Room; omega) as ⟨r4, hR4, hb1⟩
      obtain ⟨b1, s4⟩ := r4
      simp only at hR4 hb1
      have ht4 := hR4.ticks
      have R4 := R3.trans hR4
      cases b1 with
      | false =>
        simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
        exact rest s4 _ R4 (by omega) fun h => Bool.noConfusion (hb1.2 h.2)
      | true =>
        have hdn := any_step_done s4 steps true
        unfold sorts.any_step_loop at hdn
        simp only [uncurry, ↓reduceIte, bind_ok]
        refine WP.spec_mono hdn ?_
        rintro r rfl
        exact ⟨R4.mono (by simp only [stepsW]; omega),
          fun _ => ⟨x, List.mem_cons_self, hb.1 rfl, hb1.1 rfl⟩, fun _ => rfl⟩

/-- `any_step` answers whether table `A` flags, for some member, every guard
and one of the edges. -/
theorem any_step_spec (hnm : Function.Injective nm) {U : List Name} {m : Key → Option Bool}
    (l : List Step) (s : store.Store) (steps : store.TermId) (hW : Wf s)
    (hF : FlagsO nm s U m)
    (hs : ∀ a ∈ l, (∀ q ∈ a.1, KeyOK (nm none) U q) ∧ ∀ q ∈ a.2, KeyOK (nm none) U q)
    (hk : Repr nm s.nodes.val steps.val (stepsPat (nm none) U l)) (hroom : Room s (stepsW l)) :
    sorts.any_step s steps ⦃ r =>
      Ran s r.2 (stepsW l) ∧
        (r.1 = true ↔ ∃ a ∈ l, (∀ q ∈ a.1, m q ≠ none) ∧ ∃ q ∈ a.2, m q ≠ none) ⦄ :=
  any_step_loop_spec hnm l s steps hW hF hs hk hroom

/-! ## One round -/

/-- The ticks one key of a round may spend. -/
def entW (e : KEntry) : Nat := nowsW e.2.1 + stepsW e.2.2 + 5

/-- The ticks one round may spend. -/
def passW : List KEntry → Nat
  | [] => 1
  | e :: E => entW e + passW E

/-- Every key of an entry is over the names. -/
def EntOK (z : Sym) (U : List Name) (e : KEntry) : Prop :=
  KeyOK z U e.1 ∧ (∀ g ∈ e.2.1, ∀ q ∈ g, KeyOK z U q) ∧
    ∀ a ∈ e.2.2, (∀ q ∈ a.1, KeyOK z U q) ∧ ∀ q ∈ a.2, KeyOK z U q

/-- Every key flagged is flagged with yes and has `P`. -/
def GoodO (P : Key → Prop) (m : Key → Option Bool) : Prop :=
  ∀ q, m q ≠ none → m q = some true ∧ P q

/-- Flags are only added. -/
def LeO (m m' : Key → Option Bool) : Prop := ∀ q, m q = none ∨ m' q = m q

theorem LeO.refl (m : Key → Option Bool) : LeO m m := fun _ => Or.inr rfl

theorem LeO.trans {a b c : Key → Option Bool} (h₁ : LeO a b) (h₂ : LeO b c) : LeO a c := by
  intro q
  rcases h₁ q with h | h
  · exact Or.inl h
  · rcases h₂ q with h' | h'
    · exact Or.inl (by rw [← h]; exact h')
    · exact Or.inr (by rw [h', h])

theorem LeO.set {m : Key → Option Bool} {d : Key} (h : m d = none) :
    LeO m (Function.update m d (some true)) := by
  intro q
  by_cases hq : q = d
  · subst hq; exact Or.inl h
  · exact Or.inr (Function.update_of_ne hq _ _)

/-- No key without a flag has an alternative with all it asks flagged. -/
def StableO (m : Key → Option Bool) (E : List KEntry) : Prop :=
  ∀ e ∈ E, m e.1 = none → ¬ Sat (fun q => m q ≠ none) e.2.1 e.2.2

theorem pass_out_loop_spec (hnm : Function.Injective nm) {U : List Name} (P : Key → Prop) :
    ∀ (E : List KEntry) (s : store.Store) (graph : store.TermId) (ch : Bool)
      (m : Key → Option Bool), Wf s → FlagsO nm s U m → GoodO P m →
    (∀ e ∈ E, EntOK (nm none) U e) →
    (∀ e ∈ E, ∀ M : Key → Prop, (∀ q, M q → P q) → Sat M e.2.1 e.2.2 → P e.1) →
    Repr nm s.nodes.val graph.val (graphKPat (nm none) U E) → Room s (passW E) →
    sorts.pass_out_loop graph s ch ⦃ r => ∃ m',
      RanB s r.2 (passW E) ∧ FlagsO nm r.2 U m' ∧ GoodO P m' ∧
        LeO m m' ∧ (ch = true → r.1 = true) ∧ (r.1 = false → m' = m ∧ StableO m E) ∧
        (r.1 = true → ch = true ∨ ∃ e ∈ E, m e.1 = none ∧ m' e.1 ≠ none) ⦄ := by
  intro E
  induction E with
  | nil =>
    intro s graph ch m hW hF hGd hE hP hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [passW] at hroom'
    unfold sorts.pass_out_loop
    rw [loop]
    simp only [sorts.pass_out_loop.body]
    step with uncons_repr s graph hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [graphKPat] at hu
    simp only at hK
    subst hu
    have hfin : ∃ m', RanB s s1 (passW []) ∧ FlagsO nm s1 U m' ∧
        GoodO P m' ∧ LeO m m' ∧ (ch = true → ch = true) ∧
        (ch = false → m' = m ∧ StableO m []) ∧
        (ch = true → ch = true ∨ ∃ e ∈ ([] : List KEntry), m e.1 = none ∧ m' e.1 ≠ none) :=
      ⟨m, hK.ran.ranB, hF.mono hK.ran.ext (by rw [hK.tbl]), hGd, LeO.refl m, id,
        fun _ => ⟨rfl, fun e he => by cases he⟩, fun h => Or.inl h⟩
    step*
  | cons e E ih =>
    intro s graph ch m hW hF hGd hE hP hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [passW, entW] at hroom'
    obtain ⟨hk1, hkN, hkS⟩ := hE e List.mem_cons_self
    have hEt : ∀ e' ∈ E, EntOK (nm none) U e' := fun e' he' => hE e' (List.mem_cons_of_mem _ he')
    unfold sorts.pass_out_loop
    rw [loop]
    simp only [sorts.pass_out_loop.body]
    step with uncons_repr s graph hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [graphKPat] at hu
    simp only at hK
    obtain ⟨en, t, rfl, ren, rt⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 en hK.wf (by rw [hK.nodes]; exact ren) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [entryKPat] at hu2
    simp only at hK2
    obtain ⟨d, alts, rfl, rd, ralts⟩ := hu2
    rw [hK.nodes] at rd ralts
    have ht2 := hK2.ticks
    have R2 : Ran s s2 2 := hK.ran.trans hK2.ran
    step with get_flag_w s2 .A d hK2.wf (R2.ext.repr rd).lt (by unfold Room; omega)
      as ⟨r2, hfl, hK3⟩
    obtain ⟨o2, s3⟩ := r2
    simp only at hfl hK3
    have ht3 := hK3.ticks
    have R3 : Ran s s3 3 := R2.trans hK3.ran
    have hmd : o2 = m e.1 := by
      rw [hfl]
      have := hF.get hnm (keyPat_patInj (nm none) U) hW hk1 rd
      simp only [flagT] at this
      rw [R2.tbl]; exact this
    have hF3 : FlagsO nm s3 U m := hF.mono R3.ext (by rw [R3.tbl])
    -- the rest of the round
    have rest : ∀ (s' : store.Store) (ch' : Bool) (m₁ : Key → Option Bool) (k : Nat),
        RanB s s' k → k ≤ entW e → FlagsO nm s' U m₁ → GoodO P m₁ → LeO m m₁ →
        (ch = true → ch' = true) →
        (ch' = false → m₁ = m ∧
          (m e.1 = none → ¬ Sat (fun q => m q ≠ none) e.2.1 e.2.2)) →
        (ch' = true → ch = true ∨ (m e.1 = none ∧ m₁ e.1 ≠ none)) →
        loop (fun x => match x with
          | (graph1, s1, changed1) => sorts.pass_out_loop.body graph1 s1 changed1)
          (t, s', ch') ⦃ r =>
          ∃ m', RanB s r.2 (passW (e :: E)) ∧
            FlagsO nm r.2 U m' ∧ GoodO P m' ∧ LeO m m' ∧ (ch = true → r.1 = true) ∧
            (r.1 = false → m' = m ∧ StableO m (e :: E)) ∧
            (r.1 = true → ch = true ∨ ∃ e' ∈ e :: E, m e'.1 = none ∧ m' e'.1 ≠ none) ⦄ := by
      intro s' ch' m₁ k R0 hk hF' hG' hLe hch hst hflip
      have htk' := R0.ticks
      simp only [entW] at hk
      have IH := ih s' t ch' m₁ R0.wf hF' hG' hEt
        (fun e' he' => hP e' (List.mem_cons_of_mem _ he')) (R0.ext.repr rt)
        (by unfold Room; omega)
      unfold sorts.pass_out_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨m', hR, hFm, hGm, hLm, hc, hs, hf⟩
      refine ⟨m', (R0.trans hR).mono (by simp only [passW, entW]; omega), hFm, hGm,
        hLe.trans hLm, fun h => hc (hch h), ?_, ?_⟩
      · intro hr
        obtain ⟨e₁, hstG⟩ := hs hr
        have hch' : ch' = false := by
          cases hc' : ch' with
          | false => rfl
          | true => rw [hc hc'] at hr; cases hr
        obtain ⟨e₂, hste⟩ := hst hch'
        subst e₂
        refine ⟨e₁, ?_⟩
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · exact hste
        · exact hstG e' he'
      · intro hr
        rcases hf hr with hc' | ⟨e', he', h₁, h₂⟩
        · rcases hflip hc' with h | ⟨h₁, h₂⟩
          · exact Or.inl h
          · refine Or.inr ⟨e, List.mem_cons_self, h₁, ?_⟩
            rcases hLm e.1 with h | h
            · exact absurd h h₂
            · rw [h]; exact h₂
        · refine Or.inr ⟨e', List.mem_cons_of_mem _ he', ?_, h₂⟩
          rcases hLe e'.1 with h | h
          · exact h
          · rw [← h]; exact h₁
    cases o2 with
    | some b =>
      simp only [uncurry, bind_ok]
      exact rest s3 ch m 3 R3.ranB (by simp only [entW]; omega) hF3 hGd (LeO.refl m) id
        (fun _ => ⟨rfl, fun h => by rw [← hmd] at h; cases h⟩) (fun h => Or.inl h)
    | none =>
      have hmn : m e.1 = none := hmd.symm
      step with uncons_repr s3 alts hK3.wf (R3.ext.repr ralts) (by unfold Room; omega)
        as ⟨r4, hK4, hu4⟩
      obtain ⟨o4, s4⟩ := r4
      simp only at hK4 hu4
      obtain ⟨ni, si, rfl, rn, rs⟩ := hu4
      have ht4 := hK4.ticks
      have R4 : Ran s s4 4 := R3.trans hK4.ran
      step with any_now_spec hnm e.2.1 s4 ni hK4.wf (hF.mono R4.ext (by rw [R4.tbl])) hkN
        (hK4.ran.ext.repr rn) (by unfold Room; omega) as ⟨r5, hR5, hb⟩
      obtain ⟨b, s5⟩ := r5
      simp only at hR5 hb
      have ht5 := hR5.ticks
      have R5 := R4.trans hR5
      have hF5 : FlagsO nm s5 U m := hF.mono R5.ext (by rw [R5.tbl])
      have hGs : Sat (fun q => m q ≠ none) e.2.1 e.2.2 →
          GoodO P (Function.update m e.1 (some true)) := by
        intro hsat q hq
        by_cases hqe : q = e.1
        · subst hqe
          exact ⟨by simp, hP e List.mem_cons_self _ (fun q h => (hGd q h).2) hsat⟩
        · rw [Function.update_of_ne hqe] at hq ⊢
          exact hGd q hq
      cases b with
      | true =>
        simp only [uncurry, ↓reduceIte]
        step with set_flag_w s5 .A d true hR5.wf (R5.ext.repr rd).lt (by unfold Room; omega)
          as ⟨s6, hn6, ht6, hW6, htb6, htbo6, hst6⟩
        have R6 : RanB s s6 (4 + nowsW e.2.1 + 1) :=
          ⟨hW6, R5.ext.trans (Extends.of_eq hn6 (by omega)), by rw [hst6, R5.stk], by
            have := R5.ticks; omega⟩
        have hF6 := hF5.set hnm (keyPat_patInj (nm none) U) hR5.wf (b := true) hk1
          (R5.ext.repr rd) hn6 (by simpa using htb6)
        exact rest s6 true _ _ R6 (by simp only [entW]; omega) hF6 (hGs (Or.inl (hb.1 rfl)))
          (LeO.set hmn) (fun _ => rfl) (fun h => by cases h) (fun _ => Or.inr ⟨hmn, by simp⟩)
      | false =>
        simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
        step with any_step_spec hnm e.2.2 s5 si hR5.wf hF5 hkS
          (hR5.ext.repr (hK4.ran.ext.repr rs)) (by unfold Room; omega) as ⟨r6, hR6, hb1⟩
        obtain ⟨b1, s6⟩ := r6
        simp only at hR6 hb1
        have ht6 := hR6.ticks
        have R6 := R5.trans hR6
        have hF6 : FlagsO nm s6 U m := hF.mono R6.ext (by rw [R6.tbl])
        cases b1 with
        | true =>
          simp only [uncurry, ↓reduceIte]
          step with set_flag_w s6 .A d true hR6.wf (R6.ext.repr rd).lt (by unfold Room; omega)
            as ⟨s7, hn7, ht7, hW7, htb7, htbo7, hst7⟩
          have R7 : RanB s s7 (4 + nowsW e.2.1 + stepsW e.2.2 + 1) :=
            ⟨hW7, R6.ext.trans (Extends.of_eq hn7 (by omega)), by rw [hst7, R6.stk], by
              have := R6.ticks; omega⟩
          have hF7 := hF6.set hnm (keyPat_patInj (nm none) U) hR6.wf (b := true) hk1
            (R6.ext.repr rd) hn7 (by simpa using htb7)
          exact rest s7 true _ _ R7 (by simp only [entW]; omega) hF7
            (hGs (Or.inr (hb1.1 rfl))) (LeO.set hmn) (fun _ => rfl) (fun h => by cases h)
            (fun _ => Or.inr ⟨hmn, by simp⟩)
        | false =>
          simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
          exact rest s6 ch m _ R6.ranB (by simp only [entW]; omega) hF6 hGd (LeO.refl m) id
            (fun _ => ⟨rfl, fun _ hsat => by
              rcases hsat with h | h
              · exact Bool.noConfusion (hb.2 h)
              · exact Bool.noConfusion (hb1.2 h)⟩) (fun h => Or.inl h)

/-- `pass_out` flags each key without a flag that has an alternative with
all it asks flagged, and answers whether it flagged any. -/
theorem pass_out_spec (hnm : Function.Injective nm) {U : List Name} (P : Key → Prop)
    (E : List KEntry) (s : store.Store) (graph : store.TermId) (m : Key → Option Bool)
    (hW : Wf s) (hF : FlagsO nm s U m) (hGd : GoodO P m)
    (hE : ∀ e ∈ E, EntOK (nm none) U e)
    (hP : ∀ e ∈ E, ∀ M : Key → Prop, (∀ q, M q → P q) → Sat M e.2.1 e.2.2 → P e.1)
    (hg : Repr nm s.nodes.val graph.val (graphKPat (nm none) U E)) (hroom : Room s (passW E)) :
    sorts.pass_out s graph ⦃ r => ∃ m',
      RanB s r.2 (passW E) ∧ FlagsO nm r.2 U m' ∧ GoodO P m' ∧ LeO m m' ∧
        (r.1 = false → m' = m ∧ StableO m E) ∧
        (r.1 = true → ∃ e ∈ E, m e.1 = none ∧ m' e.1 ≠ none) ⦄ := by
  refine WP.spec_mono (pass_out_loop_spec hnm P E s graph false m hW hF hGd hE hP hg hroom) ?_
  rintro r ⟨m', hR, hFm, hGm, hLm, -, hs, hf⟩
  exact ⟨m', hR, hFm, hGm, hLm, hs, fun h => (hf h).resolve_left (by simp)⟩

/-! ## Rounds until nothing changes -/

/-- The keys of a list without a flag. -/
def unmarked (m : Key → Option Bool) : List Key → Nat
  | [] => 0
  | x :: Dn => (if m x = none then 1 else 0) + unmarked m Dn

theorem unmarked_le_length (m : Key → Option Bool) : ∀ Dn : List Key, unmarked m Dn ≤ Dn.length
  | [] => by simp [unmarked]
  | x :: Dn => by
    have ih := unmarked_le_length m Dn
    simp only [unmarked, List.length_cons]
    split <;> omega

theorem unmarked_cons_none {m : Key → Option Bool} {x : Key} (h : m x = none) (Dn : List Key) :
    unmarked m (x :: Dn) = 1 + unmarked m Dn := by simp [unmarked, h]

theorem unmarked_cons_some {m : Key → Option Bool} {x : Key} (h : m x ≠ none) (Dn : List Key) :
    unmarked m (x :: Dn) = unmarked m Dn := by simp [unmarked, h]

theorem unmarked_cons_le (m : Key → Option Bool) (x : Key) (Dn : List Key) :
    unmarked m Dn ≤ unmarked m (x :: Dn) := by
  simp only [unmarked]; omega

theorem unmarked_le {m m' : Key → Option Bool} (hLe : LeO m m') :
    ∀ Dn : List Key, unmarked m' Dn ≤ unmarked m Dn
  | [] => by simp [unmarked]
  | x :: Dn => by
    have ih := unmarked_le hLe Dn
    by_cases h1 : m' x = none
    · have h0 : m x = none := by
        rcases hLe x with h | h
        · exact h
        · rw [← h]; exact h1
      rw [unmarked_cons_none h1, unmarked_cons_none h0]; omega
    · have := unmarked_cons_le m x Dn
      rw [unmarked_cons_some h1]; omega

theorem unmarked_lt {m m' : Key → Option Bool} (hLe : LeO m m') {p : Key} (h₁ : m p = none)
    (h₂ : m' p ≠ none) : ∀ Dn : List Key, p ∈ Dn → unmarked m' Dn < unmarked m Dn
  | x :: Dn, hp => by
    by_cases hx : p = x
    · subst hx
      have := unmarked_le hLe Dn
      rw [unmarked_cons_none h₁, unmarked_cons_some h₂]; omega
    · have ih := unmarked_lt hLe h₁ h₂ Dn ((List.mem_cons.1 hp).resolve_left hx)
      by_cases h1 : m' x = none
      · have h0 : m x = none := by
          rcases hLe x with h | h
          · exact h
          · rw [← h]; exact h1
        rw [unmarked_cons_none h1, unmarked_cons_none h0]; omega
      · have := unmarked_cons_le m x Dn
        rw [unmarked_cons_some h1]; omega

theorem out_loop_done (s : store.Store) (graph : store.TermId) :
    sorts.out_loop s graph false ⦃ r => r = s ⦄ := by
  unfold sorts.out_loop
  rw [loop]
  simp only [sorts.out_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem out_loop_spec (hnm : Function.Injective nm) {U : List Name} (P : Key → Prop)
    (E : List KEntry) (Dn : List Key) (graph : store.TermId)
    (hE : ∀ e ∈ E, EntOK (nm none) U e)
    (hP : ∀ e ∈ E, ∀ M : Key → Prop, (∀ q, M q → P q) → Sat M e.2.1 e.2.2 → P e.1)
    (hDn : ∀ e ∈ E, e.1 ∈ Dn) :
    ∀ (n : Nat) (s : store.Store) (m : Key → Option Bool), unmarked m Dn < n → Wf s →
    FlagsO nm s U m → GoodO P m →
    Repr nm s.nodes.val graph.val (graphKPat (nm none) U E) → Room s (n * passW E) →
    sorts.out_loop s graph true ⦃ s' => ∃ m',
      RanB s s' (n * passW E) ∧ FlagsO nm s' U m' ∧ GoodO P m' ∧ StableO m' E ⦄ := by
  intro n
  induction n with
  | zero => intro s m h; cases h
  | succ n ih =>
    intro s m hlt hW hF hGd hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    rw [Nat.add_mul, Nat.one_mul] at hroom'
    unfold sorts.out_loop
    rw [loop]
    simp only [sorts.out_loop.body, ↓reduceIte]
    step with pass_out_spec hnm P E s graph m hW hF hGd hE hP hg (by unfold Room; omega)
      as ⟨r1, m₁, hR, hF₁, hG₁, hLe, hs, hf⟩
    obtain ⟨go1, s1⟩ := r1
    simp only at hR hF₁ hs hf
    have ht1 := hR.ticks
    cases go1 with
    | false =>
      obtain ⟨rfl, hst⟩ := hs rfl
      have hdn := out_loop_done s1 graph
      unfold sorts.out_loop at hdn
      simp only [uncurry, bind_ok]
      refine WP.spec_mono hdn ?_
      rintro r rfl
      exact ⟨m₁, hR.mono (by rw [Nat.add_mul, Nat.one_mul]; omega), hF₁, hG₁, hst⟩
    | true =>
      obtain ⟨e, he, h₁, h₂⟩ := hf rfl
      have hlt' : unmarked m₁ Dn < n := by
        have := unmarked_lt hLe h₁ h₂ Dn (hDn e he); omega
      have IH := ih s1 m₁ hlt' hR.wf hF₁ hG₁ (hR.ext.repr hg) (by unfold Room; omega)
      unfold sorts.out_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro r ⟨m', hR', hF', hG', hst⟩
      exact ⟨m', (hR.trans hR').mono (by rw [Nat.add_mul, Nat.one_mul]; omega), hF', hG', hst⟩

/-! ## What the rounds may spend -/

/-- The keys of lists of guards, counted with what going through them
spends. -/
def nowsS (l : List (List Key)) : Nat := (l.map fun g => 2 * g.length + 2).sum

/-- The keys of guards with edges, counted with what going through them
spends. -/
def stepsS (l : List Step) : Nat := (l.map fun a => 2 * a.1.length + 2 * a.2.length + 4).sum

theorem nowsW_eq : ∀ l : List (List Key), nowsW l = nowsS l + 1
  | [] => rfl
  | g :: l => by
    have := nowsW_eq l
    simp only [nowsS] at this
    simp only [nowsW, nowsS, List.map_cons, List.sum_cons]
    omega

theorem stepsW_eq : ∀ l : List Step, stepsW l = stepsS l + 1
  | [] => rfl
  | a :: l => by
    have := stepsW_eq l
    simp only [stepsS] at this
    simp only [stepsW, stepsS, List.map_cons, List.sum_cons]
    omega

theorem nowsS_append (l l' : List (List Key)) : nowsS (l ++ l') = nowsS l + nowsS l' := by
  simp [nowsS]

theorem stepsS_append (l l' : List Step) : stepsS (l ++ l') = stepsS l + stepsS l' := by
  simp [stepsS]

theorem nowsS_reverse (l : List (List Key)) : nowsS l.reverse = nowsS l := by
  simp [nowsS]

theorem stepsS_reverse (l : List Step) : stepsS l.reverse = stepsS l := by
  simp [stepsS]

theorem length_bareKeys (a : List Sorts.Conj) : (bareKeys a).length = a.length := by
  simp [bareKeys]

theorem length_altOf (S : Sorts) (d : Sorts.Conj) (f : Sym) (k : Nat) :
    (altOf S d f k).length = k := by
  simp [altOf]

theorem nowsS_keyNows_cons_le (S : Sorts) (d : Sorts.Conj) (μ : Name) (k : Sym × Nat)
    (K : List (Sym × Nat)) :
    nowsS (keyNows S d μ (k :: K)) ≤ 2 * k.2 + 2 + nowsS (keyNows S d μ K) := by
  by_cases hc : Sorts.Accepts S d k.1 k.2 ∧ Sorts.step S μ k.1 k.2 = none
  · rw [show keyNows S d μ (k :: K) = bareKeys (altOf S d k.1 k.2) :: keyNows S d μ K by
      simp [keyNows, hc]]
    simp only [nowsS, List.map_cons, List.sum_cons, length_bareKeys, length_altOf]
    omega
  · rw [show keyNows S d μ (k :: K) = keyNows S d μ K by simp [keyNows, hc]]
    omega

theorem stepsS_keySteps_cons_le (S : Sorts) (d : Sorts.Conj) (μ : Name) (k : Sym × Nat)
    (K : List (Sym × Nat)) :
    stepsS (keySteps S d μ (k :: K)) ≤ 4 * k.2 + 4 + stepsS (keySteps S d μ K) := by
  by_cases hacc : Sorts.Accepts S d k.1 k.2
  · cases hst : Sorts.step S μ k.1 k.2 with
    | none =>
      rw [show keySteps S d μ (k :: K) = keySteps S d μ K by simp [keySteps, hst]]
      omega
    | some kids =>
      rw [show keySteps S d μ (k :: K) =
        (bareKeys (altOf S d k.1 k.2), pairKeys (altOf S d k.1 k.2) kids) :: keySteps S d μ K by
        simp [keySteps, hacc, hst]]
      have := length_pairKeys_le (altOf S d k.1 k.2) kids
      simp only [stepsS, List.map_cons, List.sum_cons, length_bareKeys, length_altOf] at this ⊢
      omega
  · rw [show keySteps S d μ (k :: K) = keySteps S d μ K by simp [keySteps, hacc]]
    omega

/-- The alternatives the roots of a list give are no more than the ticks
going through the roots may spend. -/
theorem key_sums_le (S : Sorts) (u : Nat) (d : Sorts.Conj) (μ : Name) :
    ∀ K : List (Sym × Nat),
      nowsS (keyNows S d μ K) + stepsS (keySteps S d μ K) + 1 ≤ keysWork S u K
  | [] => by simp [keyNows, keySteps, keysWork, nowsS, stepsS]
  | k :: K => by
    have ih := key_sums_le S u d μ K
    have h1 := nowsS_keyNows_cons_le S d μ k K
    have h2 := stepsS_keySteps_cons_le S d μ k K
    simp only [keysWork]
    omega

theorem keysWork_flatMap_le (S : Sorts) (u : Nat) : ∀ xs : List Name,
    keysWork S u (xs.flatMap (defKeys S)) ≤ conjWork S u xs
  | [] => by simp [keysWork, conjWork]
  | n :: xs => by
    have ih := keysWork_flatMap_le S u xs
    have := keysWork_append S u (defKeys S n) (xs.flatMap (defKeys S))
    simp only [List.flatMap_cons, conjWork]
    omega

theorem nowsS_restNows_le (S : Sorts) (d : Sorts.Conj) (μ : Name) :
    nowsS (restNows S d μ) ≤ 2 := by
  unfold restNows
  split <;> simp [nowsS]

theorem stepsS_restSteps_le (S : Sorts) (d : Sorts.Conj) (μ : Name) :
    stepsS (restSteps S d μ) ≤ 6 := by
  unfold restSteps
  split
  · split <;> simp [stepsS]
  · simp [stepsS]

/-- The ticks one key of a round may spend, with `u` names. -/
def entGCost (S : Sorts) (u : Nat) : Nat := keyW S u + 13

theorem entW_entryOf_le (S : Sorts) (U : List Name) (z : Name) (p : Key) :
    entW (entryOf S U z p) ≤ entGCost S U.length := by
  have h1 := key_sums_le S U.length p.1 (p.2.getD z) (ownKeys S (p.2.getD z))
  have h2 := key_sums_le S U.length p.1 (p.2.getD z) ((conjList U (· ∈ p.1)).flatMap (defKeys S))
  have h3 := keysWork_flatMap_le S U.length (conjList U (· ∈ p.1))
  have h4 := nowsS_restNows_le S p.1 (p.2.getD z)
  have h5 := stepsS_restSteps_le S p.1 (p.2.getD z)
  have h6 := keyCost_le S U p.1 (p.2.getD z)
  unfold keyCost ownWork at h6
  simp only [entW, entGCost, entryOf, pairNows, pairSteps, nowsW_eq, stepsW_eq, nowsS_append,
    stepsS_append, nowsS_reverse, stepsS_reverse]
  omega

theorem passW_le {B : Nat} : ∀ E : List KEntry, (∀ e ∈ E, entW e ≤ B) →
    passW E ≤ E.length * B + 1
  | [], _ => by simp [passW]
  | e :: E, h => by
    have ih := passW_le E fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have := h e List.mem_cons_self
    simp only [passW, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-! ## Has a conjunction a member outside a sort -/

/-- The alternatives of a key have all they ask among `M` exactly when a
round over `M` adds the key. -/
theorem sat_entry_iff {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {p : Key}
    (hp : KeyOK (nm none) U p) (M : Key → Prop) :
    Sat M (entryOf S U (nm none) p).2.1 (entryOf S U (nm none) p).2.2 ↔ Sorts.GrowsG S M p := by
  obtain ⟨d, k⟩ := p
  cases k with
  | none => exact sat_bare_iff hp.1 hC.lookup_z M
  | some μ => exact sat_pair_iff hp.1 μ M

/-- The ticks deciding whether a conjunction has a member outside a sort may
spend, when the key of the two reaches `r` keys, with `u` names. -/
def outCost (S : Sorts) (u r : Nat) : Nat :=
  r * nodeGCost S u + (r + 1) * (r * entGCost S u + 1) + 8

/-- `out` answers whether the conjunction has a member that is not in the
sort (`Sorts.Out`). It spends a number of ticks that is polynomial in the
size of the sorts and in the number of keys the key of the two reaches. -/
theorem out_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (c : Sorts.Conj) (n : Name) (hc : Sub U c) (hn : n ≠ nm none) (s : store.Store)
    (decls names ci ni : store.TermId) (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hni : Repr nm s.nodes.val ni.val (.sym n))
    (hroom : Room s (outCost S U.length (Sorts.reachGSet S (c, some n)).card)) :
    sorts.out s decls names ci ni ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + outCost S U.length (Sorts.reachGSet S (c, some n)).card ∧
        (r = true ↔ Sorts.Out S c n) ⦄ := by
  unfold sorts.out
  have hroom' := hroom
  unfold Room at hroom'
  simp only [outCost] at hroom'
  have hW := hI.toWf
  have hp : KeyOK (nm none) U (c, some n) := ⟨hc, fun m h => by cases h; exact hn⟩
  step with alloc_w s (.App ci ni) hW ⟨hci.lt, hni.lt⟩ (by unfold Room; omega)
    as ⟨p0, s1, hW1, ht1, htb1, hx1, hid1, hst1⟩
  have rp : Repr nm s1.nodes.val p0.val (keyPat (nm none) U (c, some n)) :=
    .app hid1 (hx1.repr hci) (hx1.repr hni)
  have I1 : Inv s1 := ⟨hW1, by rw [hst1]; exact hI.empty⟩
  step with out_graph_spec hC (c, some n) hp s1 decls names p0 I1 (hx1.repr hde) (hx1.repr hU)
    rp (by unfold Room; omega) as ⟨graph, s2, m, Dn, hR2, hF2, rg, hInv⟩
  have ht2 := hR2.ticks
  have hkey : ∀ p ∈ Dn, KeyOK (nm none) U p := fun p hpd =>
    (hF2.has p ((hInv.dom p).2 (Or.inr hpd))).1
  have hE : ∀ e ∈ Dn.map (entryOf S U (nm none)), EntOK (nm none) U e := by
    intro e he
    obtain ⟨p, hpd, rfl⟩ := List.mem_map.1 he
    obtain ⟨hN, hS⟩ := hInv.done p hpd
    exact ⟨hkey p hpd, fun g hg q hq => (hF2.has q (hN g hg q hq)).1, fun a ha =>
      ⟨fun q hq => (hF2.has q ((hS a ha).1 q hq)).1, fun q hq => (hF2.has q ((hS a ha).2 q hq)).1⟩⟩
  have hP : ∀ e ∈ Dn.map (entryOf S U (nm none)), ∀ M : Key → Prop,
      (∀ q, M q → Sorts.TrueG S q) → Sat M e.2.1 e.2.2 → Sorts.TrueG S e.1 := by
    intro e he M hM hsat
    obtain ⟨p, hpd, rfl⟩ := List.mem_map.1 he
    exact Sorts.trueG_of_growsG hM ((sat_entry_iff hC (hkey p hpd) M).1 hsat)
  have hDn : ∀ e ∈ Dn.map (entryOf S U (nm none)), e.1 ∈ Dn := by
    intro e he
    obtain ⟨p, hpd, rfl⟩ := List.mem_map.1 he
    exact hpd
  have hDl : Dn.length ≤ (Sorts.reachGSet S (c, some n)).card := hInv.len_le
  have hpc : passW (Dn.map (entryOf S U (nm none))) ≤
      (Sorts.reachGSet S (c, some n)).card * entGCost S U.length + 1 := by
    have h₁ := passW_le (B := entGCost S U.length) (Dn.map (entryOf S U (nm none))) fun e he => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
      exact entW_entryOf_le S U (nm none) p
    have h₂ := Nat.mul_le_mul_right (entGCost S U.length) hDl
    rw [List.length_map] at h₁
    omega
  have hfl : unmarked (fun _ => none) Dn + 1 ≤ (Sorts.reachGSet S (c, some n)).card + 1 := by
    have := unmarked_le_length (fun _ => none) Dn; omega
  have hloop : (unmarked (fun _ => none) Dn + 1) * passW (Dn.map (entryOf S U (nm none))) ≤
      ((Sorts.reachGSet S (c, some n)).card + 1) *
        ((Sorts.reachGSet S (c, some n)).card * entGCost S U.length + 1) :=
    Nat.mul_le_mul hfl hpc
  step with clear_w s2 .A hR2.wf (by unfold Room; omega) as ⟨s3, hn3, ht3, hW3, hcl, hoth, hst3⟩
  have hx3 : Extends s2 s3 := Extends.of_eq hn3 (by omega)
  have hF3 : FlagsO nm s3 U fun _ => none := Flags.clear hcl
  step with out_loop_spec hC.inj (Sorts.TrueG S) (Dn.map (entryOf S U (nm none))) Dn graph hE hP
    hDn (unmarked (fun _ => none) Dn + 1) s3 (fun _ => none) (Nat.lt_succ_self _) hW3 hF3
    (fun q h => absurd rfl h) (hx3.repr rg) (by unfold Room; omega)
    as ⟨s4, m', hR4, hF4, hG4, hst⟩
  have ht4 := hR4.ticks
  have rp4 : Repr nm s4.nodes.val p0.val (keyPat (nm none) U (c, some n)) :=
    hR4.ext.repr (hx3.repr (hR2.ext.repr rp))
  step with get_flag_w s4 .A p0 hR4.wf rp4.lt (by unfold Room; omega) as ⟨o, s5, hfl5, hK5⟩
  have ht5 := hK5.ticks
  have hfin : Inv s5 ∧ Extends s s5 ∧
      s5.ticks.val ≤ s.ticks.val + outCost S U.length (Sorts.reachGSet S (c, some n)).card :=
    ⟨⟨hK5.wf, by rw [hK5.stk, hR4.stk, hst3, hR2.stk, hst1]; exact hI.empty⟩,
      ((hx1.trans hR2.ext).trans hx3).trans (hR4.ext.trans hK5.ran.ext), by
      simp only [outCost]; omega⟩
  have ho : o = m' (c, some n) := by
    rw [hfl5]
    have := hF4.get hC.inj (keyPat_patInj (nm none) U) hR4.wf hp rp4
    simpa only [flagT] using this
  have hiff : m' (c, some n) ≠ none ↔ Sorts.Out S c n :=
    Sorts.trueG_iff_of_stable (S := S) (p₀ := (c, some n)) (M := fun q => m' q ≠ none)
      (fun q h => (hG4 q h).2)
      (fun q hq hg => by
        by_contra h0
        have hqD := hInv.reached (fun p hpd => (hkey p hpd).1) hq
        exact hst (entryOf S U (nm none) q) (List.mem_map_of_mem hqD) h0
          ((sat_entry_iff hC (hkey q hqD) _).2 hg))
      (c, some n) .refl
  cases o with
  | none =>
    simp only [WP.spec_ok]
    exact ⟨hfin.1, hfin.2.1, hfin.2.2, fun h => (by cases h), fun h => absurd ho.symm (hiff.2 h)⟩
  | some b =>
    cases b with
    | true =>
      simp only [↓reduceIte, WP.spec_ok]
      exact ⟨hfin.1, hfin.2.1, hfin.2.2, fun _ => hiff.1 (by rw [← ho]; simp), fun _ => rfl⟩
    | false =>
      have := (hG4 (c, some n) (by rw [← ho]; simp)).1
      rw [← ho] at this
      cases this

/-- The ticks deciding whether a conjunction lies inside a sort may spend. -/
def inclCost (S : Sorts) (u r : Nat) : Nat := outCost S u r

/-- `included` answers whether every member of the conjunction is in the
sort (`Sorts.Incl`), within the ticks of `out`. -/
theorem included_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (c : Sorts.Conj) (n : Name) (hc : Sub U c) (hn : n ≠ nm none) (s : store.Store)
    (decls names ci ni : store.TermId) (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hni : Repr nm s.nodes.val ni.val (.sym n))
    (hroom : Room s (inclCost S U.length (Sorts.reachGSet S (c, some n)).card)) :
    sorts.included s decls names ci ni ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + inclCost S U.length (Sorts.reachGSet S (c, some n)).card ∧
        (r = true ↔ Sorts.Incl S c n) ⦄ := by
  unfold sorts.included
  step with out_spec hC c n hc hn s decls names ci ni hI hde hU hci hni hroom
    as ⟨b, s1, hI1, hx1, ht1, hb⟩
  refine ⟨hI1, hx1, ht1, ?_⟩
  rw [Sorts.incl_iff_not_out, ← hb]
  simp

end RwLogVerified
