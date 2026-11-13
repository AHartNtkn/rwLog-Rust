/-
# Sorts on the store

The declarations of a program are lists of the store (`rust/src/sorts.rs`).
This file proves the functions that read them against the specification:
one step of a sort on a root (`Sorts.step`) and membership (`Sorts.mem`).
-/
import RwLogVerified.Compose
import RwLog.Sorts.Decl

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

end RwLogVerified
