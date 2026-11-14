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

end RwLogVerified
