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

end RwLogVerified
