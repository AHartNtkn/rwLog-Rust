/-
# Whether every member of a conjunction but for some terms is in a sort

`sorts::included_but` asks, one root at a time, whether every member of a
conjunction of sorts other than the ground terms of a list is in a sort
(`Sorts.Hold`, which `Sorts.inclBut` decides for well-formed sorts). What a
root asks again of an argument waits on a list, and is asked of smaller
terms (`Sorts.sum_proj_le`).
-/
import RwLogVerified.Incl
import RwLogVerified.Count
import RwLog.Sorts.ButStep

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## A list the other way round -/

theorem rev_loop_spec : ∀ (ps acc : List Pat) (s : store.Store) (l out : store.TermId),
    Wf s → Repr nm s.nodes.val l.val (encList (nm none) ps) →
    Repr nm s.nodes.val out.val (encList (nm none) acc) → Room s (2 * ps.length + 1) →
    sorts.rev_loop l s out ⦃ r s' =>
      Ran s s' (2 * ps.length + 1) ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (ps.reverse ++ acc)) ⦄ := by
  intro ps
  induction ps with
  | nil =>
    intro acc s l out hW hl ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.rev_loop
    rw [loop]
    simp only [sorts.rev_loop.body]
    step with uncons_repr s l hW hl (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    subst hu
    have hfin : Ran s s1 (2 * ([] : List Pat).length + 1) ∧ Repr nm s1.nodes.val out.val
        (encList (nm none) (([] : List Pat).reverse ++ acc)) :=
      ⟨hK.ran, by rw [hK.nodes]; simpa using ho⟩
    step*
  | cons p ps ih =>
    intro acc s l out hW hl ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.rev_loop
    rw [loop]
    simp only [sorts.rev_loop.body]
    step with uncons_repr s l hW hl (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    obtain ⟨a, t, rfl, ra, rt⟩ := hu
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    step with alloc_w s1 (.App a out) hK.wf ⟨by rw [hn1]; exact ra.lt, by rw [hn1]; exact ho.lt⟩
      (by unfold Room; omega) as ⟨r2, hW2, ht2, htb2, hx2, hid2, hst2⟩
    obtain ⟨out1, s2⟩ := r2
    simp only at hW2 ht2 htb2 hx2 hid2 hst2
    have hx02 : Extends s s2 := hK.ran.ext.trans hx2
    have R2 : Ran s s2 2 := ⟨hW2, hx02, by rw [htb2, hK.tbl], by rw [hst2, hK.stk], by omega⟩
    have ro : Repr nm s2.nodes.val out1.val (encList (nm none) (p :: acc)) :=
      .app hid2 (hx02.repr ra) (hx02.repr ho)
    have IH := ih (p :: acc) s2 t out1 hW2 (hx02.repr rt) ro (by unfold Room; omega)
    unfold sorts.rev_loop at IH
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r, s'⟩ ⟨hR, hr⟩
    refine ⟨(R2.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
    simpa using hr

/-- `rev` gives the list with its members in the other order. -/
theorem rev_spec (ps : List Pat) (s : store.Store) (l : store.TermId) (hW : Wf s)
    (hl : Repr nm s.nodes.val l.val (encList (nm none) ps)) (hroom : Room s (2 * ps.length + 2)) :
    sorts.rev s l ⦃ r s' =>
      Ran s s' (2 * ps.length + 2) ∧ Repr nm s'.nodes.val r.val (encList (nm none) ps.reverse) ⦄ := by
  unfold sorts.rev
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨out, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have IH := rev_loop_spec (nm := nm) ps [] s1 l out hW1 (hx1.repr hl) (.nil hid)
    (by unfold Room; omega)
  refine WP.spec_mono IH ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  have hR1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  exact ⟨(hR1.trans hR).mono (by omega), by simpa using hr⟩

/-! ## Roots, each once -/

/-- The ticks a search of roots may spend. -/
def keysCost : List (Sym × Nat) → Nat
  | [] => 1
  | κ :: K => 5 + 2 * κ.2 + keysCost K

theorem entsCost_eq {K : List (Sym × Nat)} {es : List (Pat × List Pat)}
    (h : List.Forall₂ ExAt K es) : entsCost es = keysCost K := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp only [entsCost, keysCost, ih, hx.2]

theorem find_keys_none {K : List (Sym × Nat)} {es : List (Pat × List Pat)}
    (h : List.Forall₂ ExAt K es) (f : Sym) (a : Nat) :
    es.find? (fun e => decide (e.1 = .sym f ∧ e.2.length = a)) = none ↔ (f, a) ∉ K := by
  induction h with
  | nil => simp
  | @cons κ e K es hx _ ih =>
    obtain ⟨f', a'⟩ := κ
    obtain ⟨h1, h2⟩ := hx
    simp only at h1 h2
    by_cases hd : f' = f ∧ a' = a
    · obtain ⟨rfl, rfl⟩ := hd
      simp [h1, h2]
    · have hd' : ¬ (e.1 = Term.sym f ∧ e.2.length = a) := by
        rw [h1, h2]; rintro ⟨e1, e2⟩; exact hd ⟨by injection e1, e2⟩
      have hne : ¬ ((f, a) = (f', a')) := by
        rintro e0; injection e0 with e1 e2; exact hd ⟨e1.symm, e2.symm⟩
      simp only [List.find?_cons, hd', decide_false, ih, List.mem_cons, hne, false_or]

/-- A root put in front of roots that have it not. -/
def addKey (K : List (Sym × Nat)) (κ : Sym × Nat) : List (Sym × Nat) :=
  if κ ∈ K then K else κ :: K

theorem mem_addKey {K : List (Sym × Nat)} {κ x : Sym × Nat} :
    x ∈ addKey K κ ↔ x = κ ∨ x ∈ K := by
  unfold addKey
  split
  · rename_i h
    constructor
    · exact Or.inr
    · rintro (rfl | h')
      · exact h
      · exact h'
  · simp

theorem addKey_nodup {K : List (Sym × Nat)} (h : K.Nodup) (κ : Sym × Nat) :
    (addKey K κ).Nodup := by
  unfold addKey
  split
  · exact h
  · rename_i hn; exact List.nodup_cons.2 ⟨hn, h⟩

theorem keysCost_addKey_le (K : List (Sym × Nat)) (κ : Sym × Nat) :
    keysCost (addKey K κ) ≤ keysCost K + 5 + 2 * κ.2 := by
  unfold addKey
  split
  · omega
  · simp only [keysCost]; omega

/-- `add_key` puts a root in front of roots that have it not. -/
theorem add_key_spec (hnm : Function.Injective nm) {K : List (Sym × Nat)}
    {es : List (Pat × List Pat)} (hK : List.Forall₂ ExAt K es) (s : store.Store)
    (keys head args : store.TermId) {f : Sym} {ag : List Pat} (hW : Wf s)
    (hl : Repr nm s.nodes.val keys.val (encList (nm none) (es.map (entPat (nm none)))))
    (hh : Repr nm s.nodes.val head.val (.sym f))
    (ha : Repr nm s.nodes.val args.val (encList (nm none) ag))
    (hroom : Room s (keysCost K + 2)) :
    sorts.add_key s keys head args ⦃ r s' =>
      Ran s s' (keysCost K + 2) ∧ ∃ es', List.Forall₂ ExAt (addKey K (f, ag.length)) es' ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (es'.map (entPat (nm none)))) ⦄ := by
  unfold sorts.add_key
  have hroom' := hroom
  unfold Room at hroom'
  have hec := entsCost_eq hK
  step with find_spec hnm es s keys head args hW hl hh ha (by unfold Room; omega)
    as ⟨o, s1, hR1, hm⟩
  have ht1 := hR1.ticks
  cases hf : es.find? (fun e => decide (e.1 = .sym f ∧ e.2.length = ag.length)) with
  | some e =>
    rw [hf] at hm
    obtain ⟨v, rfl, -⟩ := hm
    have hin : (f, ag.length) ∈ K := by
      by_contra hn
      rw [(find_keys_none hK f ag.length).2 hn] at hf
      cases hf
    have e1 : addKey K (f, ag.length) = K := by simp [addKey, hin]
    have hfin : Ran s s1 (keysCost K + 2) ∧ ∃ es', List.Forall₂ ExAt (addKey K (f, ag.length)) es' ∧
        Repr nm s1.nodes.val keys.val (encList (nm none) (es'.map (entPat (nm none)))) :=
      ⟨hR1.mono (by omega), es, by rw [e1]; exact hK, hR1.ext.repr hl⟩
    step*
  | none =>
    rw [hf] at hm
    subst hm
    have hnot : (f, ag.length) ∉ K := (find_keys_none hK f ag.length).1 hf
    have e1 : addKey K (f, ag.length) = (f, ag.length) :: K := by simp [addKey, hnot]
    step with alloc_w s1 (.App head args) hR1.wf ⟨(hR1.ext.repr hh).lt, (hR1.ext.repr ha).lt⟩
      (by unfold Room; omega) as ⟨k, s2, hW2, ht2, htb2, hx2, hid2, hst2⟩
    have rk : Repr nm s2.nodes.val k.val (entPat (nm none) (.sym f, ag)) :=
      .app hid2 (hx2.repr (hR1.ext.repr hh)) (hx2.repr (hR1.ext.repr ha))
    refine WP.spec_mono (alloc_w s2 (.App k keys) hW2
      ⟨rk.lt, (hx2.repr (hR1.ext.repr hl)).lt⟩ (by unfold Room; omega)) ?_
    rintro ⟨r, s3⟩ ⟨hW3, ht3, htb3, hx3, hid3, hst3⟩
    refine ⟨⟨hW3, (hR1.ext.trans hx2).trans hx3, by rw [htb3, htb2, hR1.tbl],
      by rw [hst3, hst2, hR1.stk], by omega⟩, (.sym f, ag) :: es, ?_, ?_⟩
    · rw [e1]; exact .cons ⟨rfl, rfl⟩ hK
    · simp only [List.map_cons, encList]
      exact .app hid3 (hx3.repr rk) (hx3.repr (hx2.repr (hR1.ext.repr hl)))

/-- The roots with each root of a list they have not. -/
def addKeys (K : List (Sym × Nat)) (ks : List (Sym × Nat)) : List (Sym × Nat) :=
  ks.foldl addKey K

/-- The ticks adding roots may spend. -/
def addCost : List (Sym × Nat) → List (Sym × Nat) → Nat
  | _, [] => 1
  | K, κ :: ks => keysCost K + 4 + addCost (addKey K κ) ks

theorem add_keys_loop_spec (hnm : Function.Injective nm) :
    ∀ (ks : List (Sym × Nat)) (ents : List (Pat × List Pat)) (K : List (Sym × Nat))
      (es : List (Pat × List Pat)) (s : store.Store) (entries keys : store.TermId),
    List.Forall₂ ExAt ks ents → List.Forall₂ ExAt K es → Wf s →
    Repr nm s.nodes.val entries.val (encList (nm none) (ents.map (entPat (nm none)))) →
    Repr nm s.nodes.val keys.val (encList (nm none) (es.map (entPat (nm none)))) →
    Room s (addCost K ks) →
    sorts.add_keys_loop entries s keys ⦃ r s' =>
      Ran s s' (addCost K ks) ∧ ∃ es', List.Forall₂ ExAt (addKeys K ks) es' ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (es'.map (entPat (nm none)))) ⦄ := by
  intro ks
  induction ks with
  | nil =>
    intro ents K es s entries keys hks hK hW he hl hroom
    cases hks
    have hroom' := hroom
    unfold Room at hroom'
    simp only [addCost] at hroom'
    unfold sorts.add_keys_loop
    rw [loop]
    simp only [sorts.add_keys_loop.body]
    step with uncons_repr s entries hW he (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have hfin : Ran s s1 (addCost K []) ∧ ∃ es', List.Forall₂ ExAt (addKeys K []) es' ∧
        Repr nm s1.nodes.val keys.val (encList (nm none) (es'.map (entPat (nm none)))) :=
      ⟨hK0.ran, es, hK, by rw [hK0.nodes]; exact hl⟩
    step*
  | cons κ ks ih =>
    intro ents K es s entries keys hks hK hW he hl hroom
    obtain ⟨e, ents', hx, hks', rfl⟩ := List.forall₂_cons_left_iff.1 hks
    have hroom' := hroom
    unfold Room at hroom'
    simp only [addCost] at hroom'
    unfold sorts.add_keys_loop
    rw [loop]
    simp only [sorts.add_keys_loop.body]
    step with uncons_repr s entries hW he (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨en, t, rfl, ren, rt⟩ := hu
    have ht1 := hK0.ticks
    step with uncons_repr s1 en hK0.wf (by rw [hK0.nodes]; exact ren) (by unfold Room; omega)
      as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [entPat] at hu1
    simp only at hK1
    obtain ⟨fi, ki, rfl, rf, rk⟩ := hu1
    rw [hK0.nodes] at rf rk
    rw [hx.1] at rf
    have ht2 := hK1.ticks
    have R2 : Ran s s2 2 := hK0.ran.trans hK1.ran
    step with add_key_spec hnm hK s2 keys fi ki R2.wf (R2.ext.repr hl) (R2.ext.repr rf)
      (R2.ext.repr rk) (by unfold Room; omega) as ⟨r3, hR3, es1, hK1', rkeys⟩
    obtain ⟨keys1, s3⟩ := r3
    simp only at hR3 rkeys
    rw [hx.2] at hK1'
    have ht3 := hR3.ticks
    have R3 := R2.trans hR3
    have IH := ih ents' (addKey K κ) es1 s3 t keys1 hks' hK1' hR3.wf (R3.ext.repr rt) rkeys
      (by unfold Room; omega)
    unfold sorts.add_keys_loop at IH
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r, s'⟩ ⟨hR, es', hK', hr⟩
    exact ⟨(R3.trans hR).mono (by simp only [addCost]; omega), es', hK', hr⟩

/-- `add_keys` puts in front of roots each root of a list they have not. -/
theorem add_keys_spec (hnm : Function.Injective nm) (ks : List (Sym × Nat))
    (ents : List (Pat × List Pat)) (K : List (Sym × Nat)) (es : List (Pat × List Pat))
    (s : store.Store) (keys entries : store.TermId) (hks : List.Forall₂ ExAt ks ents)
    (hK : List.Forall₂ ExAt K es) (hW : Wf s)
    (hl : Repr nm s.nodes.val keys.val (encList (nm none) (es.map (entPat (nm none)))))
    (he : Repr nm s.nodes.val entries.val (encList (nm none) (ents.map (entPat (nm none)))))
    (hroom : Room s (addCost K ks)) :
    sorts.add_keys s keys entries ⦃ r s' =>
      Ran s s' (addCost K ks) ∧ ∃ es', List.Forall₂ ExAt (addKeys K ks) es' ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (es'.map (entPat (nm none)))) ⦄ :=
  add_keys_loop_spec hnm ks ents K es s entries keys hks hK hW he hl hroom

end RwLogVerified
