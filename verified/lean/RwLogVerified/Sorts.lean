/-
# Sorts on the store

The declarations of a program are lists of the store (`rust/src/sorts.rs`).
This file proves the functions that read them against the specification:
one step of a sort on a root (`Sorts.step`) and membership (`Sorts.mem`).
-/
import RwLogVerified.Compose
import RwLog.Sorts.Decl
import RwLog.Trusted.Cost

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-- `uncons` reads one node: the two parts of an application, or nothing. -/
theorem uncons_w (s : store.Store) (l : store.TermId) (hI : Wf s)
    (hl : l.val < s.nodes.val.length) (hroom : Room s 1) :
    sorts.uncons s l ⦃ o s' => KeptW s s' 1 ∧
      match o with
      | some (h, t) => s.nodes.val[l.val]? = some (.App h t)
      | none => ∀ h t, s.nodes.val[l.val]? ≠ some (.App h t) ⦄ := by
  unfold sorts.uncons
  step with read_w s l hI hl hroom as ⟨n, s1, hn, hK⟩
  cases n <;> simp_all

/-- What a function that reads and adds nodes leaves: the invariant, the nodes
there were, the tables and the stack, and at most `n` ticks spent. -/
structure Ran (s s' : store.Store) (n : Nat) : Prop where
  wf : Wf s'
  ext : Extends s s'
  tbl : tbl s' = tbl s
  stk : stk s' = stk s
  ticks : s'.ticks.val ≤ s.ticks.val + n

theorem KeptW.ran {s s' : store.Store} {n : Nat} (h : KeptW s s' n) : Ran s s' n :=
  ⟨h.wf, Extends.of_eq h.nodes (by have := h.ticks; omega), h.tbl, h.stk, Nat.le_of_eq h.ticks⟩

theorem Ran.refl {s : store.Store} (h : Wf s) : Ran s s 0 :=
  ⟨h, Extends.refl s, rfl, rfl, Nat.le_refl _⟩

theorem Ran.trans {a b c : store.Store} {n m : Nat} (h₁ : Ran a b n) (h₂ : Ran b c m) :
    Ran a c (n + m) :=
  ⟨h₂.wf, h₁.ext.trans h₂.ext, by rw [h₂.tbl, h₁.tbl], by rw [h₂.stk, h₁.stk], by
    have := h₁.ticks; have := h₂.ticks; omega⟩

theorem Ran.mono {a b : store.Store} {n m : Nat} (h : Ran a b n) (hnm : n ≤ m) : Ran a b m :=
  ⟨h.wf, h.ext, h.tbl, h.stk, by have := h.ticks; omega⟩

theorem Ran.room {a b : store.Store} {n k : Nat} (h : Ran a b n) (hr : Room a (n + k)) :
    Room b k := by
  have := h.ticks
  unfold Room at hr ⊢; omega

theorem Repr.not_app_of_sym {nodes : List store.Node} {i : Nat} {f : Sym} {a b : store.TermId}
    (h : Repr nm nodes i (.sym f)) : nodes[i]? ≠ some (.App a b) := by
  intro hn
  obtain ⟨ta, tb, e, -, -⟩ := h.of_app hn
  cases e

theorem Repr.not_app_of_var {nodes : List store.Node} {i v : Nat} {a b : store.TermId}
    (h : Repr nm nodes i (.var v)) : nodes[i]? ≠ some (.App a b) := by
  intro hn
  obtain ⟨ta, tb, e, -, -⟩ := h.of_app hn
  cases e

/-- `uncons` on a represented term: its two parts when it is an application. -/
theorem uncons_repr (s : store.Store) (l : store.TermId) {p : Pat} (hI : Wf s)
    (hl : Repr nm s.nodes.val l.val p) (hroom : Room s 1) :
    sorts.uncons s l ⦃ o s' => KeptW s s' 1 ∧
      match p with
      | .app a b => ∃ h t, o = some (h, t) ∧ Repr nm s.nodes.val h.val a ∧
          Repr nm s.nodes.val t.val b
      | _ => o = none ⦄ := by
  refine WP.spec_mono (uncons_w s l hI hl.lt hroom) ?_
  rintro ⟨o, s'⟩ ⟨hK, ho⟩
  refine ⟨hK, ?_⟩
  cases p with
  | var v =>
    cases o with
    | none => rfl
    | some x => exact absurd ho hl.not_app_of_var
  | sym f =>
    cases o with
    | none => rfl
    | some x => exact absurd ho hl.not_app_of_sym
  | app a b =>
    obtain ⟨h, t, hn, ha, hb⟩ := Repr.app_inv hl
    cases o with
    | none => exact absurd hn (ho h t)
    | some x =>
      obtain ⟨h', t'⟩ := x
      simp only at ho
      rw [hn] at ho
      cases ho
      exact ⟨_, _, rfl, ha, hb⟩

/-! ## The head of a term and its arguments -/

/-- The head of a term and its arguments, before the arguments `acc`. -/
def unspine : Pat → List Pat → Pat × List Pat
  | .app g u, acc => unspine g (u :: acc)
  | .var v, acc => (.var v, acc)
  | .sym f, acc => (.sym f, acc)

/-- The number of arguments of a term. -/
def nargs : Pat → Nat
  | .app g _ => nargs g + 1
  | _ => 0

theorem spine_loop_spec : ∀ (p : Pat) (acc : List Pat) (s : store.Store) (h args : store.TermId),
    Wf s → Repr nm s.nodes.val h.val p → Repr nm s.nodes.val args.val (encList (nm none) acc) →
    Room s (2 * nargs p + 1) →
    sorts.spine_loop h s args ⦃ s' args' h' =>
      Ran s s' (2 * nargs p + 1) ∧ Repr nm s'.nodes.val h'.val (unspine p acc).1 ∧
        Repr nm s'.nodes.val args'.val (encList (nm none) (unspine p acc).2) ⦄ := by
  unfold sorts.spine_loop
  intro p
  induction p with
  | var v =>
    intro acc s h args hW hh ha hroom
    rw [loop]
    simp only [sorts.spine_loop.body]
    step with uncons_repr s h hW hh (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hK ho ⊢
    subst ho
    have hfin : Ran s s1 (2 * 0 + 1) ∧ Repr nm s1.nodes.val h.val (.var v) ∧
        Repr nm s1.nodes.val args.val (encList (nm none) acc) :=
      ⟨hK.ran, by rw [hK.nodes]; exact hh, by rw [hK.nodes]; exact ha⟩
    step*
    simpa only [unspine, nargs] using hfin
  | sym f =>
    intro acc s h args hW hh ha hroom
    rw [loop]
    simp only [sorts.spine_loop.body]
    step with uncons_repr s h hW hh (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hK ho ⊢
    subst ho
    have hfin : Ran s s1 (2 * 0 + 1) ∧ Repr nm s1.nodes.val h.val (.sym f) ∧
        Repr nm s1.nodes.val args.val (encList (nm none) acc) :=
      ⟨hK.ran, by rw [hK.nodes]; exact hh, by rw [hK.nodes]; exact ha⟩
    step*
    simpa only [unspine, nargs] using hfin
  | app g u ihg _ =>
    intro acc s h args hW hh ha hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [nargs] at hroom'
    rw [loop]
    simp only [sorts.spine_loop.body]
    step with uncons_repr s h hW hh (by unfold Room; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hK ho ⊢
    obtain ⟨hg, hu, rfl, rg, ru⟩ := ho
    have ht1 := hK.ticks
    step with alloc_w s1 (.App hu args) hK.wf
      (by rw [hK.nodes]; exact ⟨ru.lt, ha.lt⟩) (by unfold Room; omega)
      as ⟨r1, hW2, ht2, htb2, hx2, hid, hst2⟩
    obtain ⟨args1, s2⟩ := r1
    simp only at hW2 ht2 htb2 hx2 hid hst2 ⊢
    have hx : Extends s s2 := (Extends.of_eq hK.nodes (by omega)).trans hx2
    have hargs1 : Repr nm s2.nodes.val args1.val (encList (nm none) (u :: acc)) :=
      .app hid (hx.repr ru) (hx.repr ha)
    simp only [uncurry, bind_ok]
    refine WP.spec_mono (ihg (u :: acc) s2 hg args1 hW2 (hx.repr rg) hargs1
      (by unfold Room; omega)) ?_
    rintro ⟨s3, args3, h3⟩ ⟨hR, r1, r2⟩
    have hR2 : Ran s s2 2 := ⟨hW2, hx, by rw [htb2, hK.tbl], by rw [hst2, hK.stk], by omega⟩
    exact ⟨(hR2.trans hR).mono (by simp only [nargs]; omega), r1, r2⟩

/-- `spine` gives the head of a term and the list of its arguments. -/
theorem spine_spec (s : store.Store) (t : store.TermId) {p : Pat} (hW : Wf s)
    (ht : Repr nm s.nodes.val t.val p) (hroom : Room s (2 * nargs p + 2)) :
    sorts.spine s t ⦃ r s' =>
      Ran s s' (2 * nargs p + 2) ∧ Repr nm s'.nodes.val r.1.val (unspine p []).1 ∧
        Repr nm s'.nodes.val r.2.val (encList (nm none) (unspine p []).2) ⦄ := by
  unfold sorts.spine
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨args, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  step with spine_loop_spec (nm := nm) p [] s1 t args hW1 (hx1.repr ht) (.nil hid)
    (by unfold Room; omega) as ⟨s2, args2, h2, hR, r1, r2⟩
  have hR1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  exact ⟨(hR1.trans hR).mono (by omega), r1, r2⟩

/-! ## Two lists of the same length -/

theorem same_len_done (s : store.Store) (a b : store.TermId) (same : Bool) :
    sorts.same_len_loop s a b same false ⦃ r s' => r = same ∧ s' = s ⦄ := by
  unfold sorts.same_len_loop
  rw [loop]
  simp only [sorts.same_len_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem same_len_loop_spec : ∀ (xs ys : List Pat) (s : store.Store) (a b : store.TermId)
    (same : Bool), Wf s → Repr nm s.nodes.val a.val (encList (nm none) xs) →
    Repr nm s.nodes.val b.val (encList (nm none) ys) → Room s (2 * xs.length + 2) →
    sorts.same_len_loop s a b same true ⦃ r s' =>
      r = decide (xs.length = ys.length) ∧ Ran s s' (2 * xs.length + 2) ⦄ := by
  intro xs
  induction xs with
  | nil =>
    intro ys s a b same hW ha hb hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.same_len_loop
    rw [loop]
    simp only [sorts.same_len_loop.body, ↓reduceIte]
    step with uncons_repr s a hW ha (by unfold Room; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hK ho ⊢
    subst ho
    have ht1 := hK.ticks
    step with uncons_repr s1 b hK.wf (by rw [hK.nodes]; exact hb) (by unfold Room; omega)
      as ⟨r1, hK2, ho2⟩
    obtain ⟨o2, s2⟩ := r1
    simp only at hK2 ho2 ⊢
    have ht2 := hK2.ticks
    simp only [uncurry, bind_ok]
    have hd := same_len_done s2 a b o2.isNone
    unfold sorts.same_len_loop at hd
    refine WP.spec_mono hd ?_
    rintro ⟨r, s'⟩ ⟨rfl, rfl⟩
    refine ⟨?_, (hK.ran.trans hK2.ran).mono (by simp)⟩
    cases ys with
    | nil => simp only [encList] at ho2; subst ho2; rfl
    | cons y ys =>
      simp only [encList] at ho2
      obtain ⟨h, t, rfl, -, -⟩ := ho2
      simp
  | cons x xs ih =>
    intro ys s a b same hW ha hb hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.same_len_loop
    rw [loop]
    simp only [sorts.same_len_loop.body, ↓reduceIte]
    step with uncons_repr s a hW ha (by unfold Room; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hK ho ⊢
    obtain ⟨ha', ta, rfl, -, rta⟩ := ho
    have ht1 := hK.ticks
    step with uncons_repr s1 b hK.wf (by rw [hK.nodes]; exact hb) (by unfold Room; omega)
      as ⟨r1, hK2, ho2⟩
    obtain ⟨o2, s2⟩ := r1
    simp only at hK2 ho2 ⊢
    have ht2 := hK2.ticks
    cases ys with
    | nil =>
      simp only [encList] at ho2
      subst ho2
      simp only [uncurry, bind_ok]
      have hd := same_len_done s2 a b false
      unfold sorts.same_len_loop at hd
      refine WP.spec_mono hd ?_
      rintro ⟨r, s'⟩ ⟨rfl, rfl⟩
      exact ⟨by simp, (hK.ran.trans hK2.ran).mono (by simp only [List.length_cons]; omega)⟩
    | cons y ys =>
      simp only [encList] at ho2
      obtain ⟨hb', tb, rfl, -, rtb⟩ := ho2
      simp only [uncurry, bind_ok]
      have IH := ih ys s2 ta tb same hK2.wf (by rw [hK2.nodes, hK.nodes]; exact rta)
        (by rw [hK2.nodes]; exact rtb) (by unfold Room; omega)
      unfold sorts.same_len_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨rfl, hR⟩
      exact ⟨by simp, ((hK.ran.trans hK2.ran).trans hR).mono (by simp only [List.length_cons]; omega)⟩

/-- `same_len` compares the lengths of two lists. -/
theorem same_len_spec (xs ys : List Pat) (s : store.Store) (a b : store.TermId) (hW : Wf s)
    (ha : Repr nm s.nodes.val a.val (encList (nm none) xs))
    (hb : Repr nm s.nodes.val b.val (encList (nm none) ys)) (hroom : Room s (2 * xs.length + 2)) :
    sorts.same_len s a b ⦃ r s' =>
      r = decide (xs.length = ys.length) ∧ Ran s s' (2 * xs.length + 2) ⦄ :=
  same_len_loop_spec xs ys s a b true hW ha hb hroom

/-! ## Finding a member of a list by its first part and a length -/

/-- A member of a list that is searched: a first part and a list. -/
def entPat (z : Sym) (e : Pat × List Pat) : Pat := .app e.1 (encList z e.2)

/-- The ticks a search may spend. -/
def entsCost : List (Pat × List Pat) → Nat
  | [] => 1
  | e :: es => 5 + 2 * e.2.length + entsCost es

theorem find_done (s : store.Store) (key args list : store.TermId) (found : Option store.TermId) :
    sorts.find_loop s key args list found false ⦃ r s' => r = found ∧ s' = s ⦄ := by
  unfold sorts.find_loop
  rw [loop]
  simp only [sorts.find_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem find_loop_spec (hnm : Function.Injective nm) {k : Pat} {ag : List Pat} :
    ∀ (es : List (Pat × List Pat)) (s : store.Store) (key args list : store.TermId)
    (found : Option store.TermId), Wf s →
    Repr nm s.nodes.val list.val (encList (nm none) (es.map (entPat (nm none)))) →
    Repr nm s.nodes.val key.val k → Repr nm s.nodes.val args.val (encList (nm none) ag) →
    Room s (entsCost es) →
    sorts.find_loop s key args list found true ⦃ o s' =>
      Ran s s' (entsCost es) ∧
        match es.find? (fun e => decide (e.1 = k ∧ e.2.length = ag.length)) with
        | some e => ∃ v, o = some v ∧ Repr nm s'.nodes.val v.val (encList (nm none) e.2)
        | none => o = found ⦄ := by
  intro es
  induction es with
  | nil =>
    intro s key args list found hW hl hk ha hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [entsCost] at hroom'
    unfold sorts.find_loop
    rw [loop]
    simp only [sorts.find_loop.body, ↓reduceIte]
    step with uncons_repr s list hW hl (by unfold Room; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hK ho ⊢
    subst ho
    simp only [uncurry, bind_ok]
    have hd := find_done s1 key args list found
    unfold sorts.find_loop at hd
    refine WP.spec_mono hd ?_
    rintro ⟨r, s'⟩ ⟨rfl, rfl⟩
    exact ⟨hK.ran, by simp⟩
  | cons e es ih =>
    intro s key args list found hW hl hk ha hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [entsCost] at hroom'
    unfold sorts.find_loop
    rw [loop]
    simp only [sorts.find_loop.body, ↓reduceIte]
    step with uncons_repr s list hW hl (by unfold Room; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hK ho ⊢
    obtain ⟨e', rest, rfl, re, rrest⟩ := ho
    have ht1 := hK.ticks
    step with uncons_repr s1 e' hK.wf (by rw [hK.nodes]; exact re) (by unfold Room; omega)
      as ⟨r1, hK2, ho2⟩
    obtain ⟨o2, s2⟩ := r1
    simp only [entPat] at hK2 ho2 ⊢
    obtain ⟨k', v, rfl, rk, rv⟩ := ho2
    rw [hK.nodes] at rk rv
    have ht2 := hK2.ticks
    step with same_w s2 k' key hK2.wf (by unfold Room; omega) as ⟨r2, hb, hK3⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hb hK3 ⊢
    have ht3 := hK3.ticks
    have R3 : Ran s s3 3 := (hK.ran.trans hK2.ran).trans hK3.ran
    have hkey : k'.val = key.val ↔ e.1 = k :=
      ⟨fun h => Repr.unique (h ▸ rk) hk, fun h => Repr.inj hnm hW.nodesOK (h ▸ rk) hk⟩
    by_cases hkk : k'.val = key.val
    · rw [show b = true by rw [hb]; exact decide_eq_true hkk]
      simp only [uncurry, ↓reduceIte]
      step with same_len_spec (nm := nm) e.2 ag s3 v args R3.wf (R3.ext.repr rv) (R3.ext.repr ha)
        (by unfold Room; omega) as ⟨r4, hb1, hR4⟩
      obtain ⟨b1, s4⟩ := r4
      simp only at hb1 hR4 ⊢
      have ht4 := hR4.ticks
      have R4 := R3.trans hR4
      by_cases hlen : e.2.length = ag.length
      · rw [show b1 = true by rw [hb1]; exact decide_eq_true hlen]
        simp only [↓reduceIte, uncurry, bind_ok]
        have hd := find_done s4 key args list (some v)
        unfold sorts.find_loop at hd
        refine WP.spec_mono hd ?_
        rintro ⟨r, s'⟩ ⟨rfl, rfl⟩
        refine ⟨R4.mono (by simp only [entsCost]; omega), ?_⟩
        rw [List.find?_cons_of_pos (by simp [hkey.1 hkk, hlen])]
        exact ⟨v, rfl, R4.ext.repr rv⟩
      · rw [show b1 = false by rw [hb1]; exact decide_eq_false hlen]
        simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
        have IH := ih s4 key args rest found R4.wf (R4.ext.repr rrest) (R4.ext.repr hk)
          (R4.ext.repr ha) (by unfold Room; omega)
        unfold sorts.find_loop at IH
        refine WP.spec_mono IH ?_
        rintro ⟨r, s'⟩ ⟨hR, hm⟩
        refine ⟨(R4.trans hR).mono (by simp only [entsCost]; omega), ?_⟩
        rw [List.find?_cons_of_neg (by simp [hlen])]
        exact hm
    · rw [show b = false by rw [hb]; exact decide_eq_false hkk]
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih s3 key args rest found R3.wf (R3.ext.repr rrest) (R3.ext.repr hk)
        (R3.ext.repr ha) (by unfold Room; omega)
      unfold sorts.find_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hm⟩
      refine ⟨(R3.trans hR).mono (by simp only [entsCost]; omega), ?_⟩
      rw [List.find?_cons_of_neg (by simp [mt hkey.2 hkk])]
      exact hm

/-- `find` gives the list of the first member with that first part and that
length. -/
theorem find_spec (hnm : Function.Injective nm) {k : Pat} {ag : List Pat}
    (es : List (Pat × List Pat)) (s : store.Store) (list key args : store.TermId) (hW : Wf s)
    (hl : Repr nm s.nodes.val list.val (encList (nm none) (es.map (entPat (nm none)))))
    (hk : Repr nm s.nodes.val key.val k) (ha : Repr nm s.nodes.val args.val (encList (nm none) ag))
    (hroom : Room s (entsCost es)) :
    sorts.find s list key args ⦃ o s' =>
      Ran s s' (entsCost es) ∧
        match es.find? (fun e => decide (e.1 = k ∧ e.2.length = ag.length)) with
        | some e => ∃ v, o = some v ∧ Repr nm s'.nodes.val v.val (encList (nm none) e.2)
        | none => o = none ⦄ :=
  find_loop_spec hnm es s key args list none hW hl hk ha hroom

/-! ## The declarations as a term -/

/-- A sort or any term: the nme, or the end of a list. -/
def kidPat (z : Sym) : Option Name → Pat
  | none => .sym z
  | some m => .sym m

/-- A case as a member of a list that is searched. -/
def caseEnt (z : Sym) (c : Sym × List (Option Name)) : Pat × List Pat :=
  (.sym c.1, c.2.map (kidPat z))

/-- An excluded symbol with its number of arguments is a member whose list
has that length. -/
def ExAt (e : Sym × Nat) (x : Pat × List Pat) : Prop := x.1 = .sym e.1 ∧ x.2.length = e.2

/-- The rest of a declaration as a term. -/
def RestAt (z : Sym) : Option (List (Sym × Nat) × Option Name) → Pat → Prop
  | none, p => p = .sym z
  | some r, p => ∃ xs, List.Forall₂ ExAt r.1 xs ∧
      p = .app (encList z (xs.map (entPat z))) (kidPat z r.2)

/-- A declaration as a term. -/
def DefAt (z : Sym) (d : Name × SortDef) (p : Pat) : Prop :=
  ∃ r, RestAt z d.2.rest r ∧
    p = .app (.sym d.1) (.app (encList z ((d.2.cases.map (caseEnt z)).map (entPat z))) r)

/-- The sorts of a program as a term. -/
def SortsAt (z : Sym) (S : Sorts) (p : Pat) : Prop :=
  ∃ ds, List.Forall₂ (DefAt z) S ds ∧ p = encList z ds

theorem lookup_done (s : store.Store) (nme decls : store.TermId)
    (found : Option (store.TermId × store.TermId)) :
    sorts.lookup_loop s nme decls found false ⦃ r s' => r = found ∧ s' = s ⦄ := by
  unfold sorts.lookup_loop
  rw [loop]
  simp only [sorts.lookup_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem lookup_loop_spec (hnm : Function.Injective nm) {n : Name} :
    ∀ (S : Sorts) (ds : List Pat) (s : store.Store) (nme decls : store.TermId)
    (found : Option (store.TermId × store.TermId)), Wf s →
    List.Forall₂ (DefAt (nm none)) S ds →
    Repr nm s.nodes.val decls.val (encList (nm none) ds) →
    Repr nm s.nodes.val nme.val (.sym n) → Room s (3 * S.length + 2) →
    sorts.lookup_loop s nme decls found true ⦃ o s' =>
      Ran s s' (3 * S.length + 2) ∧
        match S.lookup n with
        | some d => ∃ c r rp, o = some (c, r) ∧
            Repr nm s.nodes.val c.val
              (encList (nm none) ((d.cases.map (caseEnt (nm none))).map (entPat (nm none)))) ∧
            Repr nm s.nodes.val r.val rp ∧ RestAt (nm none) d.rest rp
        | none => o = found ⦄ := by
  intro S
  induction S with
  | nil =>
    intro ds s nme decls found hW hF hl hn hroom
    cases hF
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.lookup_loop
    rw [loop]
    simp only [sorts.lookup_loop.body, ↓reduceIte]
    step with uncons_repr s decls hW hl (by unfold Room; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hK ho ⊢
    subst ho
    simp only [uncurry, bind_ok]
    have hd := lookup_done s1 nme decls found
    unfold sorts.lookup_loop at hd
    refine WP.spec_mono hd ?_
    rintro ⟨r, s'⟩ ⟨rfl, rfl⟩
    exact ⟨hK.ran.mono (by omega), by simp [List.lookup]⟩
  | cons d S ih =>
    intro ds s nme decls found hW hF hl hn hroom
    obtain ⟨n', d⟩ := d
    cases hF with
    | cons hd hF' =>
    rename_i dp ds'
    obtain ⟨rp, hrest, rfl⟩ := hd
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.lookup_loop
    rw [loop]
    simp only [sorts.lookup_loop.body, ↓reduceIte]
    step with uncons_repr s decls hW hl (by unfold Room; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hK ho ⊢
    obtain ⟨e', more, rfl, re, rmore⟩ := ho
    have ht1 := hK.ticks
    step with uncons_repr s1 e' hK.wf (by rw [hK.nodes]; exact re) (by unfold Room; omega)
      as ⟨r1, hK2, ho2⟩
    obtain ⟨o2, s2⟩ := r1
    simp only at hK2 ho2 ⊢
    obtain ⟨nn, dd, rfl, rnn, rdd⟩ := ho2
    rw [hK.nodes] at rnn rdd
    have ht2 := hK2.ticks
    step with same_w s2 nn nme hK2.wf (by unfold Room; omega) as ⟨r2, hb, hK3⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hb hK3 ⊢
    have ht3 := hK3.ticks
    have R3 : Ran s s3 3 := (hK.ran.trans hK2.ran).trans hK3.ran
    have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hK2.nodes, hK.nodes]
    have hkey : nn.val = nme.val ↔ n' = n :=
      ⟨fun h => by have := Repr.unique (h ▸ rnn) hn; simpa using this,
        fun h => Repr.inj hnm hW.nodesOK (h ▸ rnn) hn⟩
    by_cases hkk : nn.val = nme.val
    · rw [show b = true by rw [hb]; exact decide_eq_true hkk]
      simp only [uncurry, ↓reduceIte]
      step with uncons_repr s3 dd R3.wf (by rw [hn3]; exact rdd) (by unfold Room; omega)
        as ⟨r4, hK4, ho4⟩
      obtain ⟨o4, s4⟩ := r4
      simp only at hK4 ho4 ⊢
      obtain ⟨c, r, rfl, rc, rr⟩ := ho4
      rw [hn3] at rc rr
      have ht4 := hK4.ticks
      simp only [uncurry, bind_ok]
      have hd := lookup_done s4 nme decls (some (c, r))
      unfold sorts.lookup_loop at hd
      refine WP.spec_mono hd ?_
      rintro ⟨o, s'⟩ ⟨rfl, rfl⟩
      refine ⟨(R3.trans hK4.ran).mono (by simp only [List.length_cons]; omega), ?_⟩
      have hl' : List.lookup n ((n', d) :: S) = some d := by
        rw [hkey.1 hkk]; simp [List.lookup]
      rw [hl']
      exact ⟨c, r, rp, rfl, rc, rr, hrest⟩
    · rw [show b = false by rw [hb]; exact decide_eq_false hkk]
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      have IH := ih ds' s3 nme more found R3.wf hF' (by rw [hn3]; exact rmore)
        (by rw [hn3]; exact hn) (by unfold Room; omega)
      unfold sorts.lookup_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨o, s'⟩ ⟨hR, hm⟩
      refine ⟨(R3.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
      have hne : (n == n') = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => hkk (hkey.2 h.symm)
      have hl' : List.lookup n ((n', d) :: S) = List.lookup n S := by
        simp [List.lookup, hne]
      rw [hl']
      rw [hn3] at hm
      exact hm

/-- `lookup` gives the cases and the rest of the declaration of a nme. -/
theorem lookup_spec (hnm : Function.Injective nm) {n : Name} (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (s : store.Store) (decls nme : store.TermId) (hW : Wf s)
    (hl : Repr nm s.nodes.val decls.val sp) (hn : Repr nm s.nodes.val nme.val (.sym n))
    (hroom : Room s (3 * S.length + 2)) :
    sorts.lookup s decls nme ⦃ o s' =>
      Ran s s' (3 * S.length + 2) ∧
        match S.lookup n with
        | some d => ∃ c r rp, o = some (c, r) ∧
            Repr nm s.nodes.val c.val
              (encList (nm none) ((d.cases.map (caseEnt (nm none))).map (entPat (nm none)))) ∧
            Repr nm s.nodes.val r.val rp ∧ RestAt (nm none) d.rest rp
        | none => o = none ⦄ := by
  obtain ⟨ds, hF, rfl⟩ := hS
  exact lookup_loop_spec hnm S ds s nme decls none hW hF hl hn hroom

/-! ## A list with the same member for each argument -/

theorem fill_loop_spec {kp : Pat} : ∀ (ag : List Pat) (j : Nat) (s : store.Store)
    (args kid out : store.TermId), Wf s →
    Repr nm s.nodes.val args.val (encList (nm none) ag) → Repr nm s.nodes.val kid.val kp →
    Repr nm s.nodes.val out.val (encList (nm none) (List.replicate j kp)) →
    Room s (2 * ag.length + 1) →
    sorts.fill_loop args s kid out ⦃ r s' =>
      Ran s s' (2 * ag.length + 1) ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (List.replicate (j + ag.length) kp)) ⦄ := by
  intro ag
  induction ag with
  | nil =>
    intro j s args kid out hW ha hk ho hroom
    unfold sorts.fill_loop
    rw [loop]
    simp only [sorts.fill_loop.body]
    step with uncons_repr s args hW ha (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hK hu ⊢
    subst hu
    have hfin : Ran s s1 (2 * ([] : List Pat).length + 1) ∧
        Repr nm s1.nodes.val out.val
          (encList (nm none) (List.replicate (j + ([] : List Pat).length) kp)) :=
      ⟨hK.ran, by rw [hK.nodes]; simpa using ho⟩
    step*
  | cons a ag ih =>
    intro j s args kid out hW ha hk ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.fill_loop
    rw [loop]
    simp only [sorts.fill_loop.body]
    step with uncons_repr s args hW ha (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hK hu ⊢
    obtain ⟨a', t, rfl, -, rt⟩ := hu
    have ht1 := hK.ticks
    step with alloc_w s1 (.App kid out) hK.wf
      (by rw [hK.nodes]; exact ⟨hk.lt, ho.lt⟩) (by unfold Room; omega)
      as ⟨r1, hW2, ht2, htb2, hx2, hid, hst2⟩
    obtain ⟨out1, s2⟩ := r1
    simp only at hW2 ht2 htb2 hx2 hid hst2 ⊢
    have hx : Extends s s2 := (Extends.of_eq hK.nodes (by omega)).trans hx2
    have hout1 : Repr nm s2.nodes.val out1.val (encList (nm none) (List.replicate (j + 1) kp)) := by
      rw [List.replicate_succ]
      exact .app hid (hx.repr hk) (hx.repr ho)
    have IH := ih (j + 1) s2 t kid out1 hW2 (hx.repr rt) (hx.repr hk) hout1
      (by unfold Room; omega)
    unfold sorts.fill_loop at IH
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r, s'⟩ ⟨hR, hr⟩
    have hR2 : Ran s s2 2 := ⟨hW2, hx, by rw [htb2, hK.tbl], by rw [hst2, hK.stk], by omega⟩
    refine ⟨(hR2.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
    have e : j + 1 + ag.length = j + (a :: ag).length := by simp only [List.length_cons]; omega
    rw [← e]
    exact hr

/-- `fill` gives a list with the member `kid` for each member of `args`. -/
theorem fill_spec {kp : Pat} (ag : List Pat) (s : store.Store) (args kid : store.TermId)
    (hW : Wf s) (ha : Repr nm s.nodes.val args.val (encList (nm none) ag))
    (hk : Repr nm s.nodes.val kid.val kp) (hroom : Room s (2 * ag.length + 2)) :
    sorts.fill s args kid ⦃ r s' =>
      Ran s s' (2 * ag.length + 2) ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (List.replicate ag.length kp)) ⦄ := by
  unfold sorts.fill
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨out, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have IH := fill_loop_spec (nm := nm) (kp := kp) ag 0 s1 args kid out hW1 (hx1.repr ha)
    (hx1.repr hk) (.nil hid) (by unfold Room; omega)
  refine WP.spec_mono IH ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  have hR1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  exact ⟨(hR1.trans hR).mono (by omega), by simpa using hr⟩

/-! ## One step of a sort -/

/-- The ticks searching the cases of a declaration may spend. -/
def casesCost : List (Sym × List (Option Name)) → Nat
  | [] => 1
  | c :: cs => 5 + 2 * c.2.length + casesCost cs

/-- The ticks searching the excluded symbols of a declaration may spend. -/
def exCost : List (Sym × Nat) → Nat
  | [] => 1
  | e :: es => 5 + 2 * e.2 + exCost es

/-- The ticks one declaration may cost a step. -/
def defCost (d : SortDef) : Nat :=
  casesCost d.cases + 1 +
    match d.rest with
    | none => 0
    | some r => exCost r.1

/-- The ticks the declarations may cost a step. -/
def sortsCost : Sorts → Nat
  | [] => 2
  | d :: S => 3 + defCost d.2 + sortsCost S

/-- The ticks one step of a sort on a term with `m` arguments may spend. -/
def stepCost (S : Sorts) (m : Nat) : Nat := sortsCost S + 2 * m + 2

theorem entsCost_cases (z : Sym) (cs : List (Sym × List (Option Name))) :
    entsCost (cs.map (caseEnt z)) = casesCost cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, entsCost, casesCost, ih, caseEnt, List.length_map]

theorem entsCost_ex {ex : List (Sym × Nat)} {xs : List (Pat × List Pat)}
    (h : List.Forall₂ ExAt ex xs) : entsCost xs = exCost ex := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp only [entsCost, exCost, ih, hx.2]

theorem sortsCost_ge (S : Sorts) : 3 * S.length + 2 ≤ sortsCost S := by
  induction S with
  | nil => simp [sortsCost]
  | cons d S ih => simp only [List.length_cons, sortsCost]; omega

theorem lookup_cost {S : Sorts} {n : Name} {d : SortDef} (h : S.lookup n = some d) :
    3 * S.length + 2 + defCost d ≤ sortsCost S := by
  induction S with
  | nil => simp [List.lookup] at h
  | cons e S ih =>
    obtain ⟨m, d'⟩ := e
    simp only [List.lookup] at h
    have hge := sortsCost_ge S
    split at h
    · cases h
      simp only [List.length_cons, sortsCost]; omega
    · have := ih h
      simp only [List.length_cons, sortsCost]; omega

theorem find_cases (z : Sym) (f : Sym) (m : Nat) (cs : List (Sym × List (Option Name))) :
    (cs.map (caseEnt z)).find? (fun e => decide (e.1 = .sym f ∧ e.2.length = m)) =
      (cs.find? (fun c => c.1 = f ∧ c.2.length = m)).map (caseEnt z) := by
  rw [List.find?_map]
  congr 2
  funext c
  simp [caseEnt]

theorem find_ex (f : Sym) (m : Nat) {ex : List (Sym × Nat)} {xs : List (Pat × List Pat)}
    (h : List.Forall₂ ExAt ex xs) :
    (xs.find? (fun e => decide (e.1 = .sym f ∧ e.2.length = m))).isSome = decide ((f, m) ∈ ex) := by
  induction h with
  | nil => simp
  | @cons e x ex' xs' hx _ ih =>
    obtain ⟨g, k⟩ := e
    obtain ⟨x1, x2⟩ := x
    have h1 : x1 = .sym g := hx.1
    have h2 : x2.length = k := hx.2
    subst h1 h2
    by_cases hc : g = f ∧ x2.length = m
    · simp [hc.1, hc.2]
    · have h1 : ¬((f, m) = (g, x2.length)) := fun h => hc (by cases h; exact ⟨rfl, rfl⟩)
      have h2 : ¬((Term.sym g : Pat) = Term.sym f ∧ x2.length = m) :=
        fun h => hc ⟨by simpa using h.1, h.2⟩
      rw [List.find?_cons_of_neg (by simp only [decide_eq_true_eq]; exact h2), ih]
      simp [h1]

theorem step_of_lookup {S : Sorts} {n : Name} {d : SortDef} (f : Sym) (m : Nat)
    (h : S.lookup n = some d) : Sorts.step S n f m = d.step f m := by
  unfold Sorts.step
  rw [h]
  rfl

theorem defStep_case {d : SortDef} {f : Sym} {m : Nat} {c : Sym × List (Option Name)}
    (h : d.cases.find? (fun c => c.1 = f ∧ c.2.length = m) = some c) : d.step f m = some c.2 := by
  unfold SortDef.step
  rw [h]

theorem defStep_none {d : SortDef} {f : Sym} {m : Nat}
    (h : d.cases.find? (fun c => c.1 = f ∧ c.2.length = m) = none) (hr : d.rest = none) :
    d.step f m = none := by
  unfold SortDef.step
  rw [h, hr]

theorem defStep_rest {d : SortDef} {f : Sym} {m : Nat} {ex : List (Sym × Nat)} {k : Option Name}
    (h : d.cases.find? (fun c => c.1 = f ∧ c.2.length = m) = none) (hr : d.rest = some (ex, k)) :
    d.step f m = if (f, m) ∈ ex then none else some (List.replicate m k) := by
  unfold SortDef.step
  rw [h, hr]

/-- `step` is one step of a sort: the sort of each argument of a term with
that symbol and those arguments, or nothing. -/
theorem step_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (s : store.Store) (decls nme head args : store.TermId)
    {n f : Sym} {ag : List Pat} (hW : Wf s) (hd : Repr nm s.nodes.val decls.val sp)
    (hn : Repr nm s.nodes.val nme.val (.sym n)) (hh : Repr nm s.nodes.val head.val (.sym f))
    (ha : Repr nm s.nodes.val args.val (encList (nm none) ag))
    (hroom : Room s (stepCost S ag.length)) :
    sorts.step s decls nme head args ⦃ o s' =>
      Ran s s' (stepCost S ag.length) ∧
        match Sorts.step S n f ag.length with
        | some ks => ∃ k, o = some k ∧
            Repr nm s'.nodes.val k.val (encList (nm none) (ks.map (kidPat (nm none))))
        | none => o = none ⦄ := by
  unfold sorts.step
  have hroom' := hroom
  unfold Room stepCost at hroom'
  have hge := sortsCost_ge S
  step with lookup_spec hnm S hS s decls nme hW hd hn (by unfold Room; omega) as ⟨o, s1, hR1, hl⟩
  have ht1 := hR1.ticks
  cases hlk : S.lookup n with
  | none =>
    rw [hlk] at hl
    simp only at hl
    subst hl
    simp only [WP.spec_ok]
    refine ⟨hR1.mono (by unfold stepCost; omega), ?_⟩
    simp [Sorts.step, hlk]
  | some d =>
    rw [hlk] at hl
    obtain ⟨c, r, rp, rfl, rc, rr, hrest⟩ := hl
    have hcost := lookup_cost hlk
    have hcs := entsCost_cases (nm none) d.cases
    have hdc : casesCost d.cases + 1 ≤ defCost d := by unfold defCost; omega
    step with find_spec hnm (d.cases.map (caseEnt (nm none))) s1 c head args hR1.wf
      (hR1.ext.repr rc) (hR1.ext.repr hh) (hR1.ext.repr ha) (by unfold Room; omega)
      as ⟨o1, s2, hR2, hf⟩
    have ht2 := hR2.ticks
    have R2 := hR1.trans hR2
    rw [find_cases] at hf
    cases hfc : d.cases.find? (fun c => c.1 = f ∧ c.2.length = ag.length) with
    | some cs =>
      rw [hfc] at hf
      obtain ⟨v, rfl, rv⟩ := hf
      simp only [WP.spec_ok]
      refine ⟨R2.mono (by unfold stepCost; omega), ?_⟩
      rw [step_of_lookup f ag.length hlk, defStep_case hfc]
      exact ⟨v, rfl, rv⟩
    | none =>
      rw [hfc] at hf
      simp only [Option.map_none] at hf
      subst hf
      simp only
      step with uncons_repr s2 r R2.wf (R2.ext.repr rr) (by unfold Room; omega) as ⟨o3, s3, hK3, ho3⟩
      have ht3 := hK3.ticks
      have R3 := R2.trans hK3.ran
      cases hdr : d.rest with
      | none =>
        rw [hdr] at hrest
        simp only [RestAt] at hrest
        subst hrest
        simp only at ho3
        subst ho3
        simp only [WP.spec_ok]
        refine ⟨R3.mono (by unfold stepCost; omega), ?_⟩
        rw [step_of_lookup f ag.length hlk, defStep_none hfc hdr]
      | some rk =>
        obtain ⟨ex, kd⟩ := rk
        rw [hdr] at hrest
        obtain ⟨xs, hxs, rfl⟩ := hrest
        simp only at ho3
        obtain ⟨exid, kid, rfl, rex, rkid⟩ := ho3
        have hxc : entsCost xs = exCost ex := entsCost_ex hxs
        have hdc' : casesCost d.cases + 1 + exCost ex = defCost d := by simp only [defCost, hdr]
        step with find_spec hnm xs s3 exid head args R3.wf (hK3.ran.ext.repr rex)
          (R3.ext.repr hh) (R3.ext.repr ha) (by unfold Room; omega) as ⟨o4, s4, hR4, hf4⟩
        have ht4 := hR4.ticks
        have R4 := R3.trans hR4
        have hex := find_ex f ag.length hxs
        by_cases hin : (f, ag.length) ∈ ex
        · rw [decide_eq_true hin, Option.isSome_iff_exists] at hex
          obtain ⟨e, he⟩ := hex
          rw [he] at hf4
          obtain ⟨v, rfl, -⟩ := hf4
          simp only [WP.spec_ok]
          refine ⟨R4.mono (by unfold stepCost; omega), ?_⟩
          rw [step_of_lookup f ag.length hlk, defStep_rest hfc hdr]
          simp only [hin, ↓reduceIte]
        · rw [decide_eq_false hin] at hex
          have he : List.find? (fun e => decide (e.1 = Term.sym f ∧ e.2.length = ag.length)) xs
              = none := by
            cases h : List.find? (fun e => decide (e.1 = Term.sym f ∧ e.2.length = ag.length)) xs
            · rfl
            · rw [h] at hex; cases hex
          rw [he] at hf4
          simp only at hf4
          subst hf4
          step with fill_spec (nm := nm) (kp := kidPat (nm none) kd) ag s4 args kid R4.wf
            (R4.ext.repr ha) ((hK3.ran.trans hR4).ext.repr rkid) (by unfold Room; omega)
            as ⟨ti, s5, hR5, hr5⟩
          have ht5 := hR5.ticks
          refine ⟨(R4.trans hR5).mono (by unfold stepCost; omega), ?_⟩
          rw [step_of_lookup f ag.length hlk, defStep_rest hfc hdr]
          simp only [hin, ↓reduceIte]
          exact ⟨ti, rfl, by simpa [List.map_replicate] using hr5⟩

/-! ## Ground terms: head, arguments, and membership by the arguments -/

theorem toPat_inj : ∀ {a b : GTerm}, (GTerm.toPat a) = (GTerm.toPat b) → a = b
  | .var v, _, _ => v.elim
  | _, .var v, _ => v.elim
  | .sym f, .sym g, h => by simpa [GTerm.toPat, Term.rename] using h
  | .sym f, .app c d, h => by simp [GTerm.toPat, Term.rename] at h
  | .app a b, .sym g, h => by simp [GTerm.toPat, Term.rename] at h
  | .app a b, .app c d, h => by
    simp only [GTerm.toPat, Term.rename, Term.bind_app, Term.app.injEq] at h
    rw [toPat_inj (a := a) (b := c) h.1, toPat_inj (a := b) (b := d) h.2]

/-- The symbol at the head of a ground term and its arguments, before the
arguments `acc`. -/
def gspine : GTerm → List GTerm → Sym × List GTerm
  | .var v, _ => v.elim
  | .sym f, acc => (f, acc)
  | .app g u, acc => gspine g (u :: acc)

theorem unspine_toPat : ∀ (g : GTerm) (acc : List GTerm),
    unspine (GTerm.toPat g) (acc.map GTerm.toPat) =
      (.sym (gspine g acc).1, (gspine g acc).2.map GTerm.toPat)
  | .var v, _ => v.elim
  | .sym f, acc => rfl
  | .app g u, acc => by
    have := unspine_toPat g (u :: acc)
    simpa [GTerm.toPat, Term.rename, unspine, gspine] using this

theorem nargs_toPat : ∀ (g : GTerm) (acc : List GTerm),
    nargs (GTerm.toPat g) + acc.length = (gspine g acc).2.length
  | .var v, _ => v.elim
  | .sym f, acc => by simp [GTerm.toPat, Term.rename, nargs, gspine]
  | .app g u, acc => by
    have := nargs_toPat g (u :: acc)
    simp only [GTerm.toPat, Term.rename, Term.bind_app, nargs, gspine, List.length_cons] at this ⊢
    omega

theorem gspine_mk : ∀ (g : GTerm) (acc : List GTerm),
    acc.foldl .app g = Term.mk (gspine g acc).1 (gspine g acc).2
  | .var v, _ => v.elim
  | .sym f, acc => rfl
  | .app g u, acc => by
    have := gspine_mk g (u :: acc)
    simpa [gspine] using this

theorem gspine_mem : ∀ (g : GTerm) (acc : List GTerm) (a : GTerm), a ∈ (gspine g acc).2 →
    a ∈ acc ∨ (a ∈ g.subs ∧ a.size < g.size)
  | .var v, _, _, _ => v.elim
  | .sym f, acc, a, h => Or.inl h
  | .app g u, acc, a, h => by
    rcases gspine_mem g (u :: acc) a h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨by simp [Term.subs, Term.self_mem_subs], by simp only [Term.size]; omega⟩
      · exact Or.inl h
    · exact Or.inr ⟨by simp [Term.subs, h.1], by simp only [Term.size]; omega⟩

/-- Membership of a ground term by its head and its arguments. -/
theorem mem_iff_zip {S : Sorts} {n : Name} {g : GTerm} :
    Sorts.mem S n g = true ↔
      ∃ ks, Sorts.step S n (gspine g []).1 (gspine g []).2.length = some ks ∧
        ∀ m a, (some m, a) ∈ ks.zip (gspine g []).2 → Sorts.mem S m a = true := by
  have hg : g = Term.mk (gspine g []).1 (gspine g []).2 := by simpa using gspine_mk g []
  generalize (gspine g []).1 = f at hg ⊢
  generalize (gspine g []).2 = ts at hg ⊢
  subst hg
  rw [Sorts.mem_mk]
  constructor
  · rintro ⟨ks, hs, hall⟩
    refine ⟨ks, hs, ?_⟩
    intro m a hz
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hz
    rw [List.getElem_zip] at e
    simp only [List.length_zip, Nat.lt_min] at hi
    simp only [Prod.mk.injEq] at e
    have := hall i hi.2
    rw [List.getElem?_eq_getElem hi.1, e.1, e.2] at this
    simpa [Sorts.memO] using this
  · rintro ⟨ks, hs, hz⟩
    refine ⟨ks, hs, ?_⟩
    intro i hi
    have hl := Sorts.step_length hs
    have hik : i < ks.length := by omega
    rw [List.getElem?_eq_getElem hik]
    cases hk : ks[i] with
    | none => simp [Sorts.memO]
    | some m =>
      simp only [Option.getD_some, Sorts.memO]
      apply hz m ts[i]
      refine List.mem_iff_getElem.2 ⟨i, by simp only [List.length_zip, Nat.lt_min]; exact ⟨hik, hi⟩, ?_⟩
      rw [List.getElem_zip, hk]

/-- Every pair of a set is a member when each pair of the set has a step and
the pairs of its arguments are in the set. -/
theorem closed_mem {S : Sorts} (F : Name × GTerm → Prop)
    (h : ∀ x, F x → ∃ ks, Sorts.step S x.1 (gspine x.2 []).1 (gspine x.2 []).2.length = some ks ∧
      ∀ m a, (some m, a) ∈ ks.zip (gspine x.2 []).2 → F (m, a)) :
    ∀ (k : Nat) (x : Name × GTerm), x.2.size ≤ k → F x → Sorts.mem S x.1 x.2 = true := by
  intro k
  induction k with
  | zero =>
    intro x hk hx
    obtain ⟨m, g⟩ := x
    cases g with
    | var v => exact v.elim
    | sym f => simp [Term.size] at hk
    | app a b => simp [Term.size] at hk
  | succ k ih =>
    intro x hk hx
    obtain ⟨ks, hs, hall⟩ := h x hx
    rw [mem_iff_zip]
    refine ⟨ks, hs, ?_⟩
    intro m a hz
    have ha := (List.of_mem_zip hz).2
    rcases gspine_mem x.2 [] a ha with h' | h'
    · cases h'
    · exact ih (m, a) (by simp only; omega) (hall m a hz)

/-! ## Putting the arguments on the stack -/

theorem Repr.sym_node {nodes : List store.Node} {i : Nat} {c : Sym} (h : Repr nm nodes i (.sym c)) :
    (nodes[i]? = some .Nil ∧ c = nm none) ∨ ∃ f : U32, nodes[i]? = some (.Sym f) ∧ c = nm (some f.val) := by
  generalize ht : Term.sym c = t at h
  cases h with
  | var _ => cases ht
  | sym h => cases ht; exact Or.inr ⟨_, h, rfl⟩
  | nil h => cases ht; exact Or.inl ⟨h, rfl⟩
  | app _ _ _ => cases ht

theorem is_nil_w (s : store.Store) (p : store.TermId) (hI : Wf s)
    (hp : p.val < s.nodes.val.length) (hroom : Room s 1) :
    sorts.is_nil s p ⦃ b s' => (b = true ↔ s.nodes.val[p.val]? = some .Nil) ∧ KeptW s s' 1 ⦄ := by
  unfold sorts.is_nil
  step with read_w s p hI hp hroom as ⟨n, s1, hn, hK⟩
  cases n <;> simp_all

/-- `is_nil` on a sort or any term: is it any term? -/
theorem is_nil_kid (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId)
    {k : Option Name} (hI : Wf s) (hp : Repr nm s.nodes.val p.val (kidPat (nm none) k))
    (hk : ∀ m, k = some m → m ≠ nm none) (hroom : Room s 1) :
    sorts.is_nil s p ⦃ b s' => (b = true ↔ k = none) ∧ KeptW s s' 1 ⦄ := by
  refine WP.spec_mono (is_nil_w s p hI hp.lt hroom) ?_
  rintro ⟨b, s'⟩ ⟨hb, hK⟩
  refine ⟨?_, hK⟩
  rw [hb]
  cases k with
  | none =>
    simp only [kidPat] at hp
    rcases hp.sym_node with h | ⟨f, -, e⟩
    · simp [h.1]
    · cases hnm e
  | some m =>
    simp only [kidPat] at hp
    rcases hp.sym_node with h | ⟨f, h, -⟩
    · exact absurd h.2 (hk m rfl)
    · simp [h]

theorem push_args_loop_spec (hnm : Function.Injective nm) :
    ∀ (ks : List (Option Name)) (ag : List Pat) (s : store.Store) (kids args : store.TermId),
    Wf s → ks.length = ag.length →
    Repr nm s.nodes.val kids.val (encList (nm none) (ks.map (kidPat (nm none)))) →
    Repr nm s.nodes.val args.val (encList (nm none) ag) →
    (∀ m, some m ∈ ks → m ≠ nm none) → Room s (4 * ks.length + 1) →
    sorts.push_args_loop kids s args ⦃ s' =>
      Wf s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 4 * ks.length + 1 ∧ s.ticks.val ≤ s'.ticks.val ∧
        ∃ fs, stk s' = fs ++ stk s ∧ fs.length ≤ ks.length ∧
          (∀ f ∈ fs, ∃ m a, (some m, a) ∈ ks.zip ag ∧ Repr nm s.nodes.val (fkey f) (.sym m) ∧
            Repr nm s.nodes.val (faux f) a) ∧
          ∀ m a, (some m, a) ∈ ks.zip ag → ∃ f ∈ fs, Repr nm s.nodes.val (fkey f) (.sym m) ∧
            Repr nm s.nodes.val (faux f) a ⦄ := by
  intro ks
  induction ks with
  | nil =>
    intro ag s kids args hW hlen hk ha hz hroom
    unfold sorts.push_args_loop
    rw [loop]
    simp only [sorts.push_args_loop.body]
    step with uncons_repr s kids hW hk (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hK ho ⊢
    subst ho
    have ht := hK.ticks
    have hfin : Wf s1 ∧ s1.nodes.val = s.nodes.val ∧ tbl s1 = tbl s ∧
        s1.ticks.val ≤ s.ticks.val + 4 * ([] : List (Option Name)).length + 1 ∧
        s.ticks.val ≤ s1.ticks.val ∧
        ∃ fs, stk s1 = fs ++ stk s ∧ fs.length ≤ ([] : List (Option Name)).length ∧
          (∀ f ∈ fs, ∃ m a, (some m, a) ∈ ([] : List (Option Name)).zip ag ∧
            Repr nm s.nodes.val (fkey f) (.sym m) ∧ Repr nm s.nodes.val (faux f) a) ∧
          ∀ m a, (some m, a) ∈ ([] : List (Option Name)).zip ag →
            ∃ f ∈ fs, Repr nm s.nodes.val (fkey f) (.sym m) ∧ Repr nm s.nodes.val (faux f) a :=
      ⟨hK.wf, hK.nodes, hK.tbl, by simp; omega, by omega, [], by simp [hK.stk], by simp, by simp,
        by simp⟩
    step*
    exact hfin
  | cons k ks ih =>
    intro ag s kids args hW hlen hk ha hz hroom
    cases ag with
    | nil => simp at hlen
    | cons a ag =>
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom' hlen
    unfold sorts.push_args_loop
    rw [loop]
    simp only [sorts.push_args_loop.body]
    step with uncons_repr s kids hW hk (by unfold Room; omega) as ⟨r0, hK, ho⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hK ho ⊢
    obtain ⟨kk, kt, rfl, rkk, rkt⟩ := ho
    have ht1 := hK.ticks
    step with uncons_repr s1 args hK.wf (by rw [hK.nodes]; exact ha) (by unfold Room; omega)
      as ⟨r1, hK2, ho2⟩
    obtain ⟨o2, s2⟩ := r1
    simp only [encList] at hK2 ho2 ⊢
    obtain ⟨aa, at', rfl, raa, rat⟩ := ho2
    rw [hK.nodes] at raa rat
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
    step with is_nil_kid hnm s2 kk hK2.wf (by rw [hn2]; exact rkk)
      (fun m hm => hz m (by simp [hm])) (by unfold Room; omega) as ⟨r2, hb, hK3⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hb hK3 ⊢
    have ht3 := hK3.ticks
    have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
    have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, hK2.tbl, hK.tbl]
    have hst3 : stk s3 = stk s := by rw [hK3.stk, hK2.stk, hK.stk]
    have hz' : ∀ m, some m ∈ ks → m ≠ nm none := fun m hm => hz m (List.mem_cons_of_mem _ hm)
    cases k with
    | none =>
      rw [show b = true from hb.2 rfl]
      simp only [uncurry, ↓reduceIte, bind_ok]
      have IH := ih ag s3 kt at' hK3.wf (by omega) (by rw [hn3]; exact rkt)
        (by rw [hn3]; exact rat) hz' (by unfold Room; omega)
      unfold sorts.push_args_loop at IH
      refine WP.spec_mono IH ?_
      rintro s' ⟨hW', e1, e2, e3, e3', fs, e4, e5, e6, e7⟩
      rw [hn3] at e6 e7
      refine ⟨hW', by rw [e1, hn3], by rw [e2, htb3], by simp only [List.length_cons]; omega,
        by omega, fs, by rw [e4, hst3], by simp only [List.length_cons]; omega, ?_, ?_⟩
      · intro f hf
        obtain ⟨m, a', hm, h1, h2⟩ := e6 f hf
        exact ⟨m, a', by simp [hm], h1, h2⟩
      · intro m a' hm
        simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq, reduceCtorEq, false_and,
          false_or] at hm
        exact e7 m a' hm
    | some m0 =>
      have hbf : b = false := by
        cases b
        · rfl
        · exact absurd (hb.1 rfl) (by simp)
      rw [hbf]
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
      step with push_w s3 (.Visit kk aa) hK3.wf (by unfold Room; omega) as ⟨s4, p1, p2, p3, hW4, p5⟩
      have hn4 : s4.nodes.val = s.nodes.val := by rw [p1, hn3]
      have IH := ih ag s4 kt at' hW4 (by omega) (by rw [hn4]; exact rkt)
        (by rw [hn4]; exact rat) hz' (by unfold Room; omega)
      unfold sorts.push_args_loop at IH
      refine WP.spec_mono IH ?_
      rintro s' ⟨hW', e1, e2, e3, e3', fs, e4, e5, e6, e7⟩
      rw [hn4] at e6 e7
      simp only [kidPat] at rkk
      refine ⟨hW', by rw [e1, hn4], by rw [e2, p2, htb3], by simp only [List.length_cons]; omega,
        by omega, fs ++ [.Visit kk aa], by rw [e4, p5, hst3]; simp,
        by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_, ?_⟩
      · intro f hf
        rcases List.mem_append.1 hf with hf | hf
        · obtain ⟨m, a', hm, h1, h2⟩ := e6 f hf
          exact ⟨m, a', by simp [hm], h1, h2⟩
        · simp only [List.mem_singleton] at hf
          subst hf
          exact ⟨m0, a, by simp, rkk, raa⟩
      · intro m a' hm
        simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq, Option.some.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | hm
        · exact ⟨.Visit kk aa, by simp, rkk, raa⟩
        · obtain ⟨f, hf, h1, h2⟩ := e7 m a' hm
          exact ⟨f, by simp [hf], h1, h2⟩

end RwLogVerified
