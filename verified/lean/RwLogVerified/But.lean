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

theorem rev_onto_loop_spec : ∀ (ps acc : List Pat) (s : store.Store) (l out : store.TermId),
    Wf s → Repr nm s.nodes.val l.val (encList (nm none) ps) →
    Repr nm s.nodes.val out.val (encList (nm none) acc) → Room s (2 * ps.length + 1) →
    sorts.rev_onto_loop l s out ⦃ r s' =>
      Ran s s' (2 * ps.length + 1) ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (ps.reverse ++ acc)) ⦄ := by
  intro ps
  induction ps with
  | nil =>
    intro acc s l out hW hl ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.rev_onto_loop
    rw [loop]
    simp only [sorts.rev_onto_loop.body]
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
    unfold sorts.rev_onto_loop
    rw [loop]
    simp only [sorts.rev_onto_loop.body]
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
    unfold sorts.rev_onto_loop at IH
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r, s'⟩ ⟨hR, hr⟩
    refine ⟨(R2.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
    simpa using hr

/-- `rev_onto` gives the first list with its members in the other order,
followed by the second. -/
theorem rev_onto_spec (ps acc : List Pat) (s : store.Store) (l out : store.TermId) (hW : Wf s)
    (hl : Repr nm s.nodes.val l.val (encList (nm none) ps))
    (ho : Repr nm s.nodes.val out.val (encList (nm none) acc)) (hroom : Room s (2 * ps.length + 1)) :
    sorts.rev_onto s l out ⦃ r s' =>
      Ran s s' (2 * ps.length + 1) ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (ps.reverse ++ acc)) ⦄ := by
  unfold sorts.rev_onto
  exact rev_onto_loop_spec ps acc s l out hW hl ho hroom

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
  have IH := rev_onto_loop_spec (nm := nm) ps [] s1 l out hW1 (hx1.repr hl) (.nil hid)
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

theorem addKeys_nil (K : List (Sym × Nat)) : addKeys K [] = K := rfl

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

/-! ## The roots of the cases of a conjunction -/

theorem caseKeys_exAt (z : Sym) (cs : List (Sym × List (Option Name))) :
    List.Forall₂ ExAt (cs.map fun c => (c.1, c.2.length)) (cs.map (caseEnt z)) := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih => exact .cons ⟨rfl, by simp [caseEnt]⟩ ih

/-- The roots with those of the cases of each sort of a list they have not. -/
def conjKeys (S : Sorts) (K : List (Sym × Nat)) (ns : List Name) : List (Sym × Nat) :=
  ns.foldl (fun K n => addKeys K (defKeys S n)) K

/-- The ticks adding the roots of the cases of sorts may spend. -/
def conjKeysCost (S : Sorts) : List (Sym × Nat) → List Name → Nat
  | _, [] => 1
  | K, n :: ns =>
    3 * S.length + 3 + addCost K (defKeys S n) + conjKeysCost S (addKeys K (defKeys S n)) ns

theorem add_conj_keys_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) :
    ∀ (ns : List Name) (K : List (Sym × Nat)) (es : List (Pat × List Pat)) (s : store.Store)
      (decls c keys : store.TermId),
    List.Forall₂ ExAt K es → Wf s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val c.val (namesPat (nm none) ns) →
    Repr nm s.nodes.val keys.val (encList (nm none) (es.map (entPat (nm none)))) →
    Room s (conjKeysCost S K ns) →
    sorts.add_conj_keys_loop c s decls keys ⦃ r s' =>
      Ran s s' (conjKeysCost S K ns) ∧ ∃ es', List.Forall₂ ExAt (conjKeys S K ns) es' ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (es'.map (entPat (nm none)))) ⦄ := by
  intro ns
  induction ns with
  | nil =>
    intro K es s decls c keys hK hW hd hc hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [conjKeysCost] at hroom'
    unfold sorts.add_conj_keys_loop
    rw [loop]
    simp only [sorts.add_conj_keys_loop.body]
    step with uncons_repr s c hW hc (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK0
    subst hu
    have hfin : Ran s s1 (conjKeysCost S K []) ∧ ∃ es', List.Forall₂ ExAt (conjKeys S K []) es' ∧
        Repr nm s1.nodes.val keys.val (encList (nm none) (es'.map (entPat (nm none)))) :=
      ⟨hK0.ran, es, hK, by rw [hK0.nodes]; exact hl⟩
    step*
  | cons x ns ih =>
    intro K es s decls c keys hK hW hd hc hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [conjKeysCost] at hroom'
    unfold sorts.add_conj_keys_loop
    rw [loop]
    simp only [sorts.add_conj_keys_loop.body]
    step with uncons_repr s c hW hc (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK0
    obtain ⟨n, t, rfl, rn, rt⟩ := hu
    have ht1 := hK0.ticks
    have hx1 := hK0.ran.ext
    step with lookup_spec hnm S hS s1 decls n hK0.wf (hx1.repr hd) (hx1.repr rn)
      (by unfold Room; omega) as ⟨r1, hR2, hlk⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hR2 hlk
    have ht2 := hR2.ticks
    have R2 := hK0.ran.trans hR2
    have hpos : 1 ≤ addCost K (defKeys S x) := by
      cases defKeys S x <;> simp only [addCost] <;> omega
    cases hl' : S.lookup x with
    | none =>
      rw [hl'] at hlk
      subst hlk
      have e : defKeys S x = [] := by simp [defKeys, hl']
      rw [e] at hroom' hpos
      simp only [addKeys, List.foldl_nil] at hroom'
      have IH := ih K es s2 decls t keys hK hR2.wf (R2.ext.repr hd) (R2.ext.repr rt)
        (R2.ext.repr hl) (by unfold Room; omega)
      unfold sorts.add_conj_keys_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, es', hK', hr⟩
      refine ⟨(R2.trans hR).mono (by simp only [conjKeysCost, e, addKeys, List.foldl_nil]; omega),
        es', ?_, hr⟩
      simpa only [conjKeys, List.foldl_cons, e, addKeys, List.foldl_nil] using hK'
    | some d =>
      rw [hl'] at hlk
      obtain ⟨cc, r, rp, rfl, rc, -, -⟩ := hlk
      have e : defKeys S x = caseKeysL d := by simp [defKeys, hl']
      rw [e] at hroom' hpos
      step with add_keys_spec hnm (caseKeysL d) (d.cases.map (caseEnt (nm none))) K es s2 keys cc
        (caseKeys_exAt (nm none) d.cases) hK hR2.wf (R2.ext.repr hl) (hR2.ext.repr rc)
        (by unfold Room; omega) as ⟨r3, hR3, es1, hK1, rkeys⟩
      obtain ⟨keys1, s3⟩ := r3
      simp only at hR3 rkeys
      have ht3 := hR3.ticks
      have R3 := R2.trans hR3
      have IH := ih (addKeys K (caseKeysL d)) es1 s3 decls t keys1 hK1 hR3.wf (R3.ext.repr hd)
        (R3.ext.repr rt) rkeys (by unfold Room; omega)
      unfold sorts.add_conj_keys_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, es', hK', hr⟩
      refine ⟨(R3.trans hR).mono (by simp only [conjKeysCost, e]; omega), es', ?_, hr⟩
      simpa only [conjKeys, List.foldl_cons, e] using hK'

/-! ## The roots of terms -/

/-- The root of a ground term. -/
def termKey (t : GTerm) : Sym × Nat := ((gspine t []).1, (gspine t []).2.length)

theorem key_eq_termKey (t : GTerm) : Term.key t = some (termKey t) := by
  have hg : t = Term.mk (gspine t []).1 (gspine t []).2 := by simpa using gspine_mk t []
  conv_lhs => rw [hg]
  simp [Term.key, Term.spine_mk, termKey]

/-- The ticks adding the roots of terms may spend. -/
def termKeysCost : List (Sym × Nat) → List GTerm → Nat
  | _, [] => 1
  | K, t :: G => 2 * (termKey t).2 + 5 + keysCost K + termKeysCost (addKey K (termKey t)) G

theorem add_term_keys_loop_spec (hnm : Function.Injective nm) :
    ∀ (G : List GTerm) (K : List (Sym × Nat)) (es : List (Pat × List Pat)) (s : store.Store)
      (g keys : store.TermId),
    List.Forall₂ ExAt K es → Wf s →
    Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)) →
    Repr nm s.nodes.val keys.val (encList (nm none) (es.map (entPat (nm none)))) →
    Room s (termKeysCost K G) →
    sorts.add_term_keys_loop g s keys ⦃ r s' =>
      Ran s s' (termKeysCost K G) ∧ ∃ es', List.Forall₂ ExAt (addKeys K (G.map termKey)) es' ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (es'.map (entPat (nm none)))) ⦄ := by
  intro G
  induction G with
  | nil =>
    intro K es s g keys hK hW hg hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [termKeysCost] at hroom'
    unfold sorts.add_term_keys_loop
    rw [loop]
    simp only [sorts.add_term_keys_loop.body]
    step with uncons_repr s g hW hg (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have hfin : Ran s s1 (termKeysCost K []) ∧
        ∃ es', List.Forall₂ ExAt (addKeys K (([] : List GTerm).map termKey)) es' ∧
        Repr nm s1.nodes.val keys.val (encList (nm none) (es'.map (entPat (nm none)))) :=
      ⟨hK0.ran, es, hK, by rw [hK0.nodes]; exact hl⟩
    step*
  | cons t G ih =>
    intro K es s g keys hK hW hg hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [termKeysCost] at hroom'
    unfold sorts.add_term_keys_loop
    rw [loop]
    simp only [sorts.add_term_keys_loop.body]
    step with uncons_repr s g hW hg (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨ti, more, rfl, rti, rmore⟩ := hu
    have ht1 := hK0.ticks
    have hx1 := hK0.ran.ext
    have hna : nargs (GTerm.toPat t) = (termKey t).2 := by simpa [termKey] using nargs_toPat t []
    have hun := unspine_toPat t []
    simp only [List.map_nil] at hun
    step with spine_spec s1 ti hK0.wf (hx1.repr rti) (by unfold Room; omega)
      as ⟨r1, hR2, rh, ra⟩
    obtain ⟨⟨h, args⟩, s2⟩ := r1
    simp only at hR2 rh ra
    rw [hun] at rh ra
    simp only at rh ra
    have ht2 := hR2.ticks
    have R2 := hK0.ran.trans hR2
    step with add_key_spec hnm hK s2 keys h args hR2.wf (R2.ext.repr hl) rh ra
      (by unfold Room; omega) as ⟨r3, hR3, es1, hK1, rkeys⟩
    obtain ⟨keys1, s3⟩ := r3
    simp only at hR3 rkeys
    rw [List.length_map] at hK1
    have ht3 := hR3.ticks
    have R3 := R2.trans hR3
    have IH := ih (addKey K (termKey t)) es1 s3 more keys1 hK1 hR3.wf (R3.ext.repr rmore) rkeys
      (by unfold Room; omega)
    unfold sorts.add_term_keys_loop at IH
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r, s'⟩ ⟨hR, es', hK', hr⟩
    refine ⟨(R3.trans hR).mono (by simp only [termKeysCost]; omega), es', ?_, hr⟩
    simpa only [List.map_cons, addKeys, List.foldl_cons] using hK'

/-! ## The roots to ask about -/

/-- The roots the rest of a declaration excludes. -/
def exL (d : SortDef) : List (Sym × Nat) :=
  match d.rest with
  | some r => r.1
  | none => []

/-- The roots to ask about, as `but_keys` lists them. -/
def butKeysL (S : Sorts) (cl : List Name) (n : Name) (G : List GTerm) : List (Sym × Nat) :=
  addKeys
    (match S.lookup n with
      | none => conjKeys S [] cl
      | some d => addKeys (addKeys (conjKeys S [] cl) (caseKeysL d)) (exL d))
    (G.map termKey)

/-- The ticks `but_keys` may spend. -/
def butKeysX (S : Sorts) (cl : List Name) (n : Name) (G : List GTerm) : Nat :=
  3 * S.length + 4 + conjKeysCost S [] cl +
    (match S.lookup n with
      | none => termKeysCost (conjKeys S [] cl) G
      | some d => addCost (conjKeys S [] cl) (caseKeysL d) +
          addCost (addKeys (conjKeys S [] cl) (caseKeysL d)) (exL d) +
          termKeysCost (addKeys (addKeys (conjKeys S [] cl) (caseKeysL d)) (exL d)) G)

theorem addCost_pos (K ks : List (Sym × Nat)) : 1 ≤ addCost K ks := by
  cases ks <;> simp only [addCost] <;> omega

/-- `but_keys` lists the roots to ask about. -/
theorem but_keys_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (cl : List Name) (n : Name) (G : List GTerm) (s : store.Store)
    (decls c ni g : store.TermId) (hW : Wf s) (hd : Repr nm s.nodes.val decls.val sp)
    (hc : Repr nm s.nodes.val c.val (namesPat (nm none) cl))
    (hn : Repr nm s.nodes.val ni.val (.sym n))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hroom : Room s (butKeysX S cl n G)) :
    sorts.but_keys s decls c ni g ⦃ r s' =>
      Ran s s' (butKeysX S cl n G) ∧ ∃ es', List.Forall₂ ExAt (butKeysL S cl n G) es' ∧
        Repr nm s'.nodes.val r.val (encList (nm none) (es'.map (entPat (nm none)))) ⦄ := by
  unfold sorts.but_keys
  have hroom' := hroom
  unfold Room at hroom'
  have hge : 3 * S.length + 5 + conjKeysCost S [] cl ≤ butKeysX S cl n G := by
    unfold butKeysX
    cases S.lookup n with
    | none =>
      have : 1 ≤ termKeysCost (conjKeys S [] cl) G := by
        cases G <;> simp only [termKeysCost] <;> omega
      simp only; omega
    | some d =>
      have := addCost_pos (conjKeys S [] cl) (caseKeysL d)
      simp only; omega
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨nil, s1, hW1, ht1, htb1, hx1, hid1, hst1⟩
  have rnil : Repr nm s1.nodes.val nil.val
      (encList (nm none) (([] : List (Pat × List Pat)).map (entPat (nm none)))) := .nil hid1
  have R1 : Ran s s1 1 := ⟨hW1, hx1, htb1, hst1, by omega⟩
  step with add_conj_keys_loop_spec hnm S hS cl [] [] s1 decls c nil .nil hW1 (hx1.repr hd)
    (hx1.repr hc) rnil (by unfold Room; omega)
    as ⟨keys, s2, hR2, es1, hK1, rk1⟩
  have ht2 := hR2.ticks
  have R2 := R1.trans hR2
  step with lookup_spec hnm S hS s2 decls ni hR2.wf (R2.ext.repr hd) (R2.ext.repr hn)
    (by unfold Room; omega)
    as ⟨o, s3, hR3, hlk⟩
  have ht3 := hR3.ticks
  have R3 := R2.trans hR3
  cases hl' : S.lookup n with
  | none =>
    rw [hl'] at hlk
    subst hlk
    have hk : butKeysX S cl n G =
        3 * S.length + 4 + conjKeysCost S [] cl + termKeysCost (conjKeys S [] cl) G := by
      simp only [butKeysX, hl']
    simp only [bind_ok]
    refine WP.spec_mono (add_term_keys_loop_spec hnm G _ es1 s3 g keys hK1 hR3.wf
      (R3.ext.repr hg) (hR3.ext.repr rk1) (by unfold Room; omega)) ?_
    rintro ⟨r, s'⟩ ⟨hR, es', hK', hr⟩
    refine ⟨(R3.trans hR).mono (by omega), es', ?_, hr⟩
    simpa only [butKeysL, hl'] using hK'
  | some d =>
    rw [hl'] at hlk
    obtain ⟨cc, rest, rp, rfl, rc, rr, hrest⟩ := hlk
    have hk : butKeysX S cl n G =
        3 * S.length + 4 + conjKeysCost S [] cl + (addCost (conjKeys S [] cl) (caseKeysL d) +
          addCost (addKeys (conjKeys S [] cl) (caseKeysL d)) (exL d) +
          termKeysCost (addKeys (addKeys (conjKeys S [] cl) (caseKeysL d)) (exL d)) G) := by
      simp only [butKeysX, hl']
    have hp2 := addCost_pos (addKeys (conjKeys S [] cl) (caseKeysL d)) (exL d)
    step with add_keys_spec hnm (caseKeysL d) (d.cases.map (caseEnt (nm none))) _ es1 s3 keys cc
      (caseKeys_exAt (nm none) d.cases) hK1 hR3.wf (hR3.ext.repr rk1) (hR3.ext.repr rc)
      (by unfold Room; omega) as ⟨r4, hR4, es2, hK2, rk2⟩
    obtain ⟨keys2, s5⟩ := r4
    simp only at hR4 rk2
    have ht4 := hR4.ticks
    have R4 := R3.trans hR4
    step with uncons_repr s5 rest hR4.wf ((hR3.trans hR4).ext.repr rr) (by unfold Room; omega)
      as ⟨r5, hK5, hu⟩
    obtain ⟨o1, s6⟩ := r5
    simp only at hK5
    have ht5 := hK5.ticks
    have R5 := R4.trans hK5.ran
    cases hr : d.rest with
    | none =>
      rw [hr] at hrest
      simp only [RestAt] at hrest
      subst hrest
      simp only at hu
      subst hu
      have e : exL d = [] := by simp [exL, hr]
      rw [e] at hk hp2
      simp only [addKeys_nil, addCost] at hk
      simp only [uncurry, bind_ok]
      refine WP.spec_mono (add_term_keys_loop_spec hnm G _ es2 s6 g keys2 hK2 hK5.wf
        (R5.ext.repr hg) (hK5.ran.ext.repr rk2) (by unfold Room; omega)) ?_
      rintro ⟨r, s'⟩ ⟨hR, es', hK', hr'⟩
      refine ⟨(R5.trans hR).mono (by omega), es', ?_, hr'⟩
      simpa only [butKeysL, hl', e, addKeys_nil] using hK'
    | some rv =>
      rw [hr] at hrest
      obtain ⟨xs, hxs, rfl⟩ := hrest
      simp only at hu
      obtain ⟨exi, kk, rfl, rex, -⟩ := hu
      have e : exL d = rv.1 := by simp [exL, hr]
      rw [e] at hk hp2
      step with add_keys_spec hnm rv.1 xs _ es2 s6 keys2 exi hxs hK2 hK5.wf
        (hK5.ran.ext.repr rk2) (by rw [hK5.nodes]; exact rex) (by unfold Room; omega)
        as ⟨r7, hR7, es3, hK3, rk3⟩
      obtain ⟨keys3, s7⟩ := r7
      simp only at hR7 rk3
      have ht7 := hR7.ticks
      have R7 := R5.trans hR7
      simp only [uncurry, bind_ok]
      refine WP.spec_mono (add_term_keys_loop_spec hnm G _ es3 s7 g keys3 hK3 hR7.wf
        (R7.ext.repr hg) rk3 (by unfold Room; omega)) ?_
      rintro ⟨r, s'⟩ ⟨hR, es', hK', hr'⟩
      refine ⟨(R7.trans hR).mono (by omega), es', ?_, hr'⟩
      simpa only [butKeysL, hl', e] using hK'

/-! ## What the roots listed are, and what listing them costs -/

theorem mem_addKeys {x : Sym × Nat} : ∀ (ks K : List (Sym × Nat)),
    x ∈ addKeys K ks ↔ x ∈ K ∨ x ∈ ks
  | [], K => by simp [addKeys]
  | κ :: ks, K => by
    have h := mem_addKeys (x := x) ks (addKey K κ)
    simp only [addKeys, List.foldl_cons] at h ⊢
    rw [h, mem_addKey, List.mem_cons]
    tauto

theorem addKeys_nodup : ∀ (ks K : List (Sym × Nat)), K.Nodup → (addKeys K ks).Nodup
  | [], _, h => h
  | κ :: ks, K, h => addKeys_nodup ks (addKey K κ) (addKey_nodup h κ)

theorem mem_conjKeysL (S : Sorts) {x : Sym × Nat} : ∀ (ns : List Name) (K : List (Sym × Nat)),
    x ∈ conjKeys S K ns ↔ x ∈ K ∨ ∃ n ∈ ns, x ∈ defKeys S n
  | [], K => by simp [conjKeys]
  | n :: ns, K => by
    have h := mem_conjKeysL S (x := x) ns (addKeys K (defKeys S n))
    simp only [conjKeys, List.foldl_cons] at h ⊢
    rw [h, mem_addKeys]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem conjKeys_nodup (S : Sorts) : ∀ (ns : List Name) (K : List (Sym × Nat)),
    K.Nodup → (conjKeys S K ns).Nodup
  | [], _, h => h
  | n :: ns, K, h => conjKeys_nodup S ns _ (addKeys_nodup (defKeys S n) K h)

theorem butKeysL_nodup (S : Sorts) (cl : List Name) (n : Name) (G : List GTerm) :
    (butKeysL S cl n G).Nodup := by
  unfold butKeysL
  refine addKeys_nodup _ _ ?_
  cases S.lookup n with
  | none => exact conjKeys_nodup S cl [] List.nodup_nil
  | some d => exact addKeys_nodup _ _ (addKeys_nodup _ _ (conjKeys_nodup S cl [] List.nodup_nil))

theorem mem_caseKeys_def {S : Sorts} {c : Sorts.Conj} {x : Sym × Nat} :
    x ∈ Sorts.caseKeys S c ↔ ∃ n ∈ c, x ∈ defKeys S n := by
  obtain ⟨f, k⟩ := x
  rw [Sorts.mem_caseKeys]
  constructor
  · rintro ⟨s, hs, d, hl, cs, hcs, rfl, rfl⟩
    exact ⟨s, hs, by simp only [defKeys, hl, caseKeysL]; exact List.mem_map.2 ⟨cs, hcs, rfl⟩⟩
  · rintro ⟨s, hs, hx⟩
    cases hl : S.lookup s with
    | none => simp [defKeys, hl] at hx
    | some d =>
      simp only [defKeys, hl, caseKeysL, List.mem_map, Prod.mk.injEq] at hx
      obtain ⟨cs, hcs, rfl, rfl⟩ := hx
      exact ⟨s, hs, d, hl, cs, hcs, rfl, rfl⟩

theorem mem_exKeys {S : Sorts} {n : Name} {x : Sym × Nat} :
    x ∈ Sorts.exKeys S n ↔ ∃ d, S.lookup n = some d ∧ x ∈ exL d := by
  unfold Sorts.exKeys
  cases hl : S.lookup n with
  | none => simp
  | some d =>
    cases hr : d.rest with
    | none => simp [exL, hr]
    | some r => simp [exL, hr]

theorem filterMap_key (G : List GTerm) : G.filterMap Term.key = G.map termKey := by
  induction G with
  | nil => rfl
  | cons t G ih => simp [key_eq_termKey]

/-- The roots listed are those the specification asks about. -/
theorem mem_butKeysL {S : Sorts} {U : List Name} {c : Sorts.Conj} (hc : Sub U c) (n : Name)
    (G : List GTerm) {x : Sym × Nat} :
    x ∈ butKeysL S (conjList U (· ∈ c)) n G ↔ x ∈ Sorts.butKeys S c n G := by
  have hcl : (∃ m ∈ conjList U (· ∈ c), x ∈ defKeys S m) ↔ ∃ m ∈ c, x ∈ defKeys S m := by
    constructor
    · rintro ⟨m, hm, hx⟩; exact ⟨m, (mem_conjList.1 hm).2, hx⟩
    · rintro ⟨m, hm, hx⟩; exact ⟨m, mem_conjList.2 ⟨hc m hm, hm⟩, hx⟩
  have hcK : x ∈ conjKeys S [] (conjList U (· ∈ c)) ↔ ∃ m ∈ c, x ∈ defKeys S m := by
    rw [mem_conjKeysL, hcl]; simp
  have hdn : x ∈ defKeys S n ↔ ∃ d, S.lookup n = some d ∧ x ∈ caseKeysL d := by
    cases hl : S.lookup n <;> simp [defKeys, hl]
  simp only [Sorts.butKeys, Finset.mem_union, List.mem_toFinset, mem_caseKeys_def, mem_exKeys,
    filterMap_key, Finset.mem_singleton, exists_eq_left, hdn]
  unfold butKeysL
  cases hl : S.lookup n with
  | none => simp [mem_addKeys, hcK]
  | some d => simp [mem_addKeys, hcK]

/-- The weight of roots: what searching all of them costs. -/
def kw (ks : List (Sym × Nat)) : Nat := (ks.map fun κ => 5 + 2 * κ.2).sum

theorem kw_append (a b : List (Sym × Nat)) : kw (a ++ b) = kw a + kw b := by simp [kw]

theorem length_le_kw : ∀ ks : List (Sym × Nat), ks.length ≤ kw ks
  | [] => by simp [kw]
  | κ :: ks => by
    have := length_le_kw ks
    simp only [kw, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    omega

theorem keysCost_addKeys_le : ∀ (ks K : List (Sym × Nat)),
    keysCost (addKeys K ks) ≤ keysCost K + kw ks
  | [], K => by simp [addKeys, kw]
  | κ :: ks, K => by
    have h1 := keysCost_addKeys_le ks (addKey K κ)
    have h2 := keysCost_addKey_le K κ
    simp only [addKeys, List.foldl_cons, kw, List.map_cons, List.sum_cons] at h1 ⊢
    omega

theorem addCost_le : ∀ (ks K : List (Sym × Nat)) (B : Nat), keysCost K + kw ks ≤ B →
    addCost K ks ≤ ks.length * (B + 4) + 1
  | [], _, _, _ => by simp [addCost]
  | κ :: ks, K, B, h => by
    have h2 := keysCost_addKey_le K κ
    simp only [kw, List.map_cons, List.sum_cons] at h
    have h1 := addCost_le ks (addKey K κ) B (by simp only [kw]; omega)
    simp only [addCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A bound on the weight of the roots of one declaration: that of all of
them together. -/
def sortsW (S : Sorts) : Nat := (S.map fun p => kw (defKeysL p.2)).sum

theorem kw_defKeys_le (S : Sorts) (n : Name) : kw (defKeys S n) ≤ sortsW S := by
  cases h : S.lookup n with
  | none =>
    have e : defKeys S n = [] := by simp [defKeys, h]
    rw [e]; simp [kw]
  | some dd =>
    have e : defKeys S n = caseKeysL dd := by simp [defKeys, h]
    have hm := Sorts.mem_of_lookup h
    have h1 : kw (defKeysL dd) ≤ sortsW S :=
      List.le_sum_of_mem (List.mem_map.2 ⟨(n, dd), hm, rfl⟩)
    have h2 : kw (defKeysL dd) = kw (caseKeysL dd) + kw (exL dd) := by
      unfold defKeysL exL; exact kw_append _ _
    rw [e]; omega

theorem conjKeys_le (S : Sorts) : ∀ (ns : List Name) (K : List (Sym × Nat)) (B : Nat),
    keysCost K + ns.length * sortsW S ≤ B →
    keysCost (conjKeys S K ns) ≤ keysCost K + ns.length * sortsW S ∧
      conjKeysCost S K ns ≤ ns.length * (3 * S.length + 5) + ns.length * sortsW S * (B + 4) + 1
  | [], _, _, _ => by simp [conjKeys, conjKeysCost]
  | n :: ns, K, B, h => by
    have hw := kw_defKeys_le S n
    have hl := length_le_kw (defKeys S n)
    have h2 := keysCost_addKeys_le (defKeys S n) K
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at h
    have h3 := addCost_le (defKeys S n) K B (by omega)
    obtain ⟨h4, h5⟩ := conjKeys_le S ns (addKeys K (defKeys S n)) B (by omega)
    have h6 := Nat.mul_le_mul_right (B + 4) (Nat.le_trans hl hw)
    refine ⟨?_, ?_⟩
    · simp only [conjKeys, List.foldl_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at h4 ⊢
      omega
    · simp only [conjKeysCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem termKeysCost_le : ∀ (G : List GTerm) (K : List (Sym × Nat)) (B : Nat),
    keysCost K + kw (G.map termKey) ≤ B →
    termKeysCost K G ≤ kw (G.map termKey) + G.length * B + 1
  | [], _, _, _ => by simp [termKeysCost, kw]
  | t :: G, K, B, h => by
    have h2 := keysCost_addKey_le K (termKey t)
    simp only [kw, List.map_cons, List.sum_cons] at h
    have h1 := termKeysCost_le G (addKey K (termKey t)) B (by simp only [kw]; omega)
    simp only [termKeysCost, kw, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
      Nat.one_mul] at h1 ⊢
    omega

/-- A bound on the weight of the roots listed. -/
def butKeysW (S : Sorts) (u gw : Nat) : Nat := 1 + (u + 1) * sortsW S + gw

/-- A bound on the ticks `but_keys` may spend, for `u` names and terms whose
roots weigh `gw`. -/
def butKeysCost (S : Sorts) (u gw : Nat) : Nat :=
  u * (3 * S.length + 5) + 3 * S.length + 8 + butKeysW S u gw * (butKeysW S u gw + 5)

theorem butKeysX_le (S : Sorts) {U : List Name} (c : Sorts.Conj) (n : Name) (G : List GTerm) :
    butKeysX S (conjList U (· ∈ c)) n G ≤ butKeysCost S U.length (kw (G.map termKey)) ∧
      keysCost (butKeysL S (conjList U (· ∈ c)) n G) ≤ butKeysW S U.length (kw (G.map termKey)) := by
  set cl := conjList U (· ∈ c) with hcl
  set gw := kw (G.map termKey) with hgw
  set B := butKeysW S U.length gw with hB
  have hlen : cl.length ≤ U.length := length_conjList_le U (· ∈ c)
  have hm1 := Nat.mul_le_mul_right (sortsW S) hlen
  have hm2 := Nat.mul_le_mul_right (3 * S.length + 5) hlen
  have hBe : B = 1 + (U.length * sortsW S + sortsW S) + gw := by
    rw [hB]; unfold butKeysW; rw [Nat.add_mul, Nat.one_mul]
  obtain ⟨hc1, hc2⟩ := conjKeys_le S cl [] B (by simp only [keysCost]; omega)
  simp only [keysCost] at hc1
  have hm3 := Nat.mul_le_mul_right (B + 4) hm1
  have hG := length_le_kw (G.map termKey)
  rw [List.length_map] at hG
  have hsq : B * (B + 5) = B * (B + 4) + B := by rw [Nat.mul_add, Nat.mul_add]; omega
  unfold butKeysCost butKeysX butKeysL
  rw [← hB, hsq]
  cases hl : S.lookup n with
  | none =>
    simp only
    have h1 := termKeysCost_le G (conjKeys S [] cl) B (by omega)
    have h2 := keysCost_addKeys_le (G.map termKey) (conjKeys S [] cl)
    have h3 : (cl.length * sortsW S + G.length) * (B + 4) ≤ B * (B + 4) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : G.length * B ≤ G.length * (B + 4) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul] at h3
    refine ⟨by omega, by omega⟩
  | some d =>
    simp only
    have hd : kw (caseKeysL d) + kw (exL d) ≤ sortsW S := by
      have hm := Sorts.mem_of_lookup hl
      have h1 : kw (defKeysL d) ≤ sortsW S :=
        List.le_sum_of_mem (List.mem_map.2 ⟨(n, d), hm, rfl⟩)
      have h2 : kw (defKeysL d) = kw (caseKeysL d) + kw (exL d) := by
        unfold defKeysL exL; exact kw_append _ _
      omega
    have hl1 := length_le_kw (caseKeysL d)
    have hl2 := length_le_kw (exL d)
    have k1 := keysCost_addKeys_le (caseKeysL d) (conjKeys S [] cl)
    have k2 := keysCost_addKeys_le (exL d) (addKeys (conjKeys S [] cl) (caseKeysL d))
    have k3 := keysCost_addKeys_le (G.map termKey)
      (addKeys (addKeys (conjKeys S [] cl) (caseKeysL d)) (exL d))
    have a1 := addCost_le (caseKeysL d) (conjKeys S [] cl) B (by omega)
    have a2 := addCost_le (exL d) (addKeys (conjKeys S [] cl) (caseKeysL d)) B (by omega)
    have a3 := termKeysCost_le G (addKeys (addKeys (conjKeys S [] cl) (caseKeysL d)) (exL d)) B
      (by omega)
    have h3 : (cl.length * sortsW S + (caseKeysL d).length + (exL d).length + G.length) * (B + 4) ≤
        B * (B + 4) := Nat.mul_le_mul_right _ (by omega)
    have h4 : G.length * B ≤ G.length * (B + 4) := Nat.mul_le_mul_left _ (by omega)
    simp only [Nat.add_mul] at h3
    refine ⟨by omega, by omega⟩

/-! ## A member outside at the roots no declaration names -/

theorem outCost_mono (S : Sorts) (u : Nat) {r r' : Nat} (h : r ≤ r') :
    outCost S u r ≤ outCost S u r' := by
  unfold outCost
  have h1 := Nat.mul_le_mul_right (nodeGCost S u) h
  have h2 : r * entGCost S u + 1 ≤ r' * entGCost S u + 1 := by
    have := Nat.mul_le_mul_right (entGCost S u) h; omega
  have h3 : (r + 1) * (r * entGCost S u + 1) ≤ (r' + 1) * (r' * entGCost S u + 1) :=
    Nat.mul_le_mul (Nat.succ_le_succ h) h2
  omega

/-- The ticks `fresh_out` may spend, where a key reaches at most `r` keys. -/
def freshCost (S : Sorts) (u r : Nat) : Nat :=
  u * (3 * S.length + 4) + 3 * S.length + 5 + restKidsCost S u + outCost S u r

/-- `fresh_out` answers whether the conjunction has a member outside the
sort at the roots no declaration names (`Sorts.FreshOut`). -/
theorem fresh_out_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (c : Sorts.Conj) (n : Name) (hc : Sub U c) {r : Nat}
    (hr : ∀ m, (Sorts.reachGSet S (Sorts.restKids S c, some m)).card ≤ r) (s : store.Store)
    (decls names ci ni : store.TermId) (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hni : Repr nm s.nodes.val ni.val (.sym n))
    (hroom : Room s (freshCost S U.length r)) :
    sorts.fresh_out s decls names ci ni ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + freshCost S U.length r ∧
        (b = true ↔ Sorts.FreshOut S c n) ⦄ := by
  unfold sorts.fresh_out
  have hroom' := hroom
  unfold Room at hroom'
  simp only [freshCost] at hroom'
  have hW := hI.toWf
  step with rest_ok_spec hC.inj S hC.sorts c hc s decls ci hW hde hci (by unfold Room; omega)
    as ⟨b, s1, hR1, hb⟩
  have ht1 := hR1.ticks
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hR1.ranB.inv hI, hR1.ext, by simp only [freshCost]; omega, ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro h
    exact absurd (hb.2 h.1) (by simp)
  | true =>
    have hok : Sorts.RestOK S c := hb.1 rfl
    simp only [↓reduceIte]
    step with lookup_spec hC.inj S hC.sorts s1 decls ni hR1.wf (hR1.ext.repr hde)
      (hR1.ext.repr hni) (by unfold Room; omega) as ⟨own, s2, hR2, hlk⟩
    have ht2 := hR2.ticks
    have ho : OwnAt nm s1.nodes.val S n own := hlk
    step with own_rest_spec s2 own hR2.wf (ho.mono hR2.ext) (by unfold Room; omega)
      as ⟨o, s3, hR3, ho3⟩
    have ht3 := hR3.ticks
    have R3 := (hR1.trans hR2).trans hR3
    cases hrest : (S.lookup n).bind (·.rest) with
    | none =>
      rw [hrest] at ho3
      subst ho3
      simp only [WP.spec_ok]
      refine ⟨R3.ranB.inv hI, R3.ext, by simp only [freshCost]; omega, ?_⟩
      simp only [true_iff]
      exact ⟨hok, Or.inl (by rw [hrest]; rfl)⟩
    | some rv =>
      rw [hrest] at ho3
      obtain ⟨e, kk, rfl, rkk⟩ := ho3
      have hrk : Sorts.restKid S n = rv.2 := by simp [Sorts.restKid, hrest]
      have hnz : ∀ m, rv.2 = some m → m ≠ nm none := fun m hm =>
        hC.nz m (Sorts.restKid_mem_names (by rw [hrk, hm]))
      simp only
      step with is_nil_kid hC.inj s3 kk hR3.wf rkk hnz (by unfold Room; omega)
        as ⟨b1, s4, hb1, hK4⟩
      have ht4 := hK4.ticks
      have R4 := R3.trans hK4.ran
      cases b1 with
      | true =>
        have hnone : rv.2 = none := hb1.1 rfl
        simp only [↓reduceIte, WP.spec_ok]
        refine ⟨R4.ranB.inv hI, R4.ext, by simp only [freshCost]; omega, ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨-, h | ⟨m, -, hm, -⟩⟩
        · rw [hrest] at h; cases h
        · rw [hrk, hnone] at hm; cases hm
      | false =>
        obtain ⟨m, hm⟩ : ∃ m, rv.2 = some m := by
          cases h : rv.2 with
          | none => exact absurd (hb1.2 h) (by simp)
          | some m => exact ⟨m, rfl⟩
        rw [hm] at rkk
        simp only [kidPat] at rkk
        have hmn : m ∈ Sorts.names S := Sorts.restKid_mem_names (by rw [hrk, hm])
        have hsub : Sub U (Sorts.restKids S c) := fun x hx =>
          hC.names x (Sorts.restKids_subset_names hx)
        have hrm := outCost_mono S U.length (hr m)
        simp only [Bool.false_eq_true, ↓reduceIte]
        step with rest_kids_spec hC.inj S hC.sorts hC.nz c hc s4 decls names ci hK4.wf
          (R4.ext.repr hde) (R4.ext.repr hU) (R4.ext.repr hci) (by unfold Room; omega)
          as ⟨dk, s5, hR5, rdk⟩
        have ht5 := hR5.ticks
        have I5 : Inv s5 := ⟨hR5.wf, by rw [hR5.stk, R4.stk]; exact hI.empty⟩
        have hx5 := R4.ext.trans hR5.ext
        refine WP.spec_mono (out_spec hC (Sorts.restKids S c) m hsub (hC.nz m hmn) s5 decls names
          dk kk I5 (hx5.repr hde) (hx5.repr hU) rdk (hR5.ext.repr (hK4.ran.ext.repr rkk))
          (by unfold Room; omega)) ?_
        rintro ⟨b, s'⟩ ⟨hI', hx', ht', hb'⟩
        refine ⟨hI', hx5.trans hx', by simp only [freshCost]; omega, ?_⟩
        rw [hb']
        constructor
        · intro h; exact ⟨hok, Or.inr ⟨m, hmn, by rw [hrk, hm], h⟩⟩
        · rintro ⟨-, h | ⟨m', -, hm', h⟩⟩
          · rw [hrest] at h; cases h
          · rw [hrk, hm] at hm'; cases hm'; exact h

/-! ## The one member of each argument conjunction -/

theorem countCost_mono (S : Sorts) (u : Nat) {r r' : Nat} (h : r ≤ r') :
    countCost S u r ≤ countCost S u r' := by
  unfold countCost flagCost
  have h1 := Nat.mul_le_mul_right (nodeCost S u) h
  have h2 : r * (u * altW S + 5) + 1 ≤ r' * (u * altW S + 5) + 1 := by
    have := Nat.mul_le_mul_right (u * altW S + 5) h; omega
  have h3 : (r + 1) * (r * (u * altW S + 5) + 1) ≤ (r' + 1) * (r' * (u * altW S + 5) + 1) :=
    Nat.mul_le_mul (Nat.succ_le_succ h) h2
  have h4 : (r + 1) * (4 * (r * (u * altW S + 5) + 1)) ≤
      (r' + 1) * (4 * (r' * (u * altW S + 5) + 1)) :=
    Nat.mul_le_mul (Nat.succ_le_succ h) (by omega)
  omega

/-- The one member of a conjunction, when it has one and no more. -/
noncomputable def oneOf (S : Sorts) (c : Sorts.Conj) : Option GTerm :=
  match Sorts.count S c with
  | .one t => some t
  | _ => none

/-- What `soles` lists for a conjunction: its one member in a list, or the
end of a list. -/
def solePat (z : Sym) : Option GTerm → Pat
  | some t => .app (GTerm.toPat t) (.sym z)
  | none => .sym z

theorem soles_done (s : store.Store) (decls names nil out kids : store.TermId) (okb : Bool) :
    sorts.soles_loop s decls names nil out kids okb false ⦃ r => r = (s, out, okb) ⦄ := by
  unfold sorts.soles_loop
  rw [loop]
  simp only [sorts.soles_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem soles_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Nat}
    (decls names nil : store.TermId) :
    ∀ (cs : List Sorts.Conj) (acc : List Pat) (s : store.Store) (out kids : store.TermId)
      (okb : Bool),
    (∀ c ∈ cs, Sub U c) → (∀ c ∈ cs, (Sorts.reachSet S c).card ≤ r) → Inv s →
    Repr nm s.nodes.val decls.val sp → Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val nil.val (.sym (nm none)) →
    Repr nm s.nodes.val out.val (encList (nm none) acc) →
    Repr nm s.nodes.val kids.val (encList (nm none) (cs.map (cpat (nm none) U))) →
    Room s (cs.length * (countCost S U.length r + 3) + 1) →
    sorts.soles_loop s decls names nil out kids okb true ⦃ res =>
      Inv res.1 ∧ Extends s res.1 ∧
        res.1.ticks.val ≤ s.ticks.val + (cs.length * (countCost S U.length r + 3) + 1) ∧
        ((∀ c ∈ cs, Sorts.count S c ≠ .none) → res.2.2 = okb ∧
          Repr nm res.1.nodes.val res.2.1.val
            (encList (nm none) ((cs.map fun c => solePat (nm none) (oneOf S c)).reverse ++ acc))) ∧
        (∀ c ∈ cs, Sorts.count S c = .none → res.2.2 = false) ⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro acc s out kids okb _ _ hI hde hU hnil ho hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.soles_loop
    rw [loop]
    simp only [sorts.soles_loop.body, ↓reduceIte]
    step with uncons_repr s kids hI.toWf hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := soles_done s1 decls names nil out kids okb
    unfold sorts.soles_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro res rfl
    have := hK.ticks
    exact ⟨hK.ran.ranB.inv hI, hK.ran.ext, by simp only; omega,
      fun _ => ⟨rfl, by simpa using hK.ran.ext.repr ho⟩, by simp⟩
  | cons x cs ih =>
    intro acc s out kids okb hsub hr hI hde hU hnil ho hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    have hmono := countCost_mono S U.length (hr x List.mem_cons_self)
    unfold sorts.soles_loop
    rw [loop]
    simp only [sorts.soles_loop.body, ↓reduceIte]
    step with uncons_repr s kids hI.toWf hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    have hx1 := hK.ran.ext
    have hI1 : Inv s1 := hK.ran.ranB.inv hI
    step with count_spec hC x (hsub x List.mem_cons_self) s1 decls names k hI1 (hx1.repr hde)
      (hx1.repr hU) (hx1.repr rk) (by unfold Room; omega) as ⟨r1, hI2, hx2, ht2, hcnt⟩
    obtain ⟨cnt, s2⟩ := r1
    simp only at hI2 hx2 ht2 hcnt
    have hx12 := hx1.trans hx2
    have next : ∀ (s3 : store.Store) (out1 : store.TermId), Inv s3 → Extends s s3 →
        s3.ticks.val ≤ s.ticks.val + (countCost S U.length r + 3) →
        Sorts.count S x ≠ .none →
        Repr nm s3.nodes.val out1.val
          (encList (nm none) (solePat (nm none) (oneOf S x) :: acc)) →
        loop (fun x => match x with
          | (s1, out1, kids1, ok2, go1) => sorts.soles_loop.body decls names nil s1 out1 kids1 ok2 go1)
          (s3, out1, t, okb, true) ⦃ res =>
          Inv res.1 ∧ Extends s res.1 ∧
            res.1.ticks.val ≤ s.ticks.val + ((x :: cs).length * (countCost S U.length r + 3) + 1) ∧
            ((∀ c ∈ x :: cs, Sorts.count S c ≠ .none) → res.2.2 = okb ∧
              Repr nm res.1.nodes.val res.2.1.val (encList (nm none)
                (((x :: cs).map fun c => solePat (nm none) (oneOf S c)).reverse ++ acc))) ∧
            (∀ c ∈ x :: cs, Sorts.count S c = .none → res.2.2 = false) ⦄ := by
      intro s3 out1 hI3 hx3 ht3 hne ro
      have IH := ih (solePat (nm none) (oneOf S x) :: acc) s3 out1 t okb
        (fun c hc => hsub c (List.mem_cons_of_mem _ hc))
        (fun c hc => hr c (List.mem_cons_of_mem _ hc)) hI3 (hx3.repr hde) (hx3.repr hU)
        (hx3.repr hnil) ro (hx3.repr rt) (by unfold Room; omega)
      unfold sorts.soles_loop at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hI', hx', ht', h1, h2⟩
      refine ⟨hI', hx3.trans hx', by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_, ?_⟩
      · intro hall
        obtain ⟨e1, e2⟩ := h1 fun c hc => hall c (List.mem_cons_of_mem _ hc)
        refine ⟨e1, ?_⟩
        simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
          using e2
      · intro c hc hcn
        rcases List.mem_cons.1 hc with rfl | hc
        · exact absurd hcn hne
        · exact h2 c hc hcn
    cases cnt with
    | None =>
      simp only at hcnt
      simp only [uncurry, bind_ok]
      have hdn := soles_done s2 decls names nil out kids false
      unfold sorts.soles_loop at hdn
      refine WP.spec_mono hdn ?_
      rintro res rfl
      refine ⟨hI2, hx12, by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega,
        fun hall => absurd hcnt (hall x List.mem_cons_self), by intros; rfl⟩
    | One m =>
      simp only at hcnt
      obtain ⟨tm, hc1, rm⟩ := hcnt
      have hso : oneOf S x = some tm := by simp [oneOf, hc1]
      step with alloc_w s2 (.App m nil) hI2.toWf ⟨rm.lt, (hx12.repr hnil).lt⟩
        (by unfold Room; omega) as ⟨r3, hW3, ht3, htb3, hx3, hid3, hst3⟩
      obtain ⟨e, s3⟩ := r3
      simp only at hW3 ht3 htb3 hx3 hid3 hst3
      have re : Repr nm s3.nodes.val e.val (solePat (nm none) (some tm)) :=
        .app hid3 (hx3.repr rm) (hx3.repr (hx12.repr hnil))
      step with alloc_w s3 (.App e out) hW3 ⟨re.lt, (hx3.repr (hx12.repr ho)).lt⟩
        (by unfold Room; omega) as ⟨r4, hW4, ht4, htb4, hx4, hid4, hst4⟩
      obtain ⟨out1, s4⟩ := r4
      simp only at hW4 ht4 htb4 hx4 hid4 hst4
      simp only [uncurry, bind_ok]
      refine next s4 out1 ⟨hW4, by rw [hst4, hst3]; exact hI2.empty⟩
        ((hx12.trans hx3).trans hx4) (by omega) (by rw [hc1]; simp) ?_
      rw [hso]
      exact .app hid4 (hx4.repr re) (hx4.repr (hx3.repr (hx12.repr ho)))
    | Many =>
      simp only at hcnt
      have hso : oneOf S x = none := by simp [oneOf, hcnt]
      step with alloc_w s2 (.App nil out) hI2.toWf ⟨(hx12.repr hnil).lt, (hx12.repr ho).lt⟩
        (by unfold Room; omega) as ⟨r3, hW3, ht3, htb3, hx3, hid3, hst3⟩
      obtain ⟨out1, s3⟩ := r3
      simp only at hW3 ht3 htb3 hx3 hid3 hst3
      simp only [uncurry, bind_ok]
      refine next s3 out1 ⟨hW3, by rw [hst3]; exact hI2.empty⟩ (hx12.trans hx3) (by omega)
        (by rw [hcnt]; simp) ?_
      rw [hso]
      exact .app hid3 (hx3.repr (hx12.repr hnil)) (hx3.repr (hx12.repr ho))

/-- The ticks `soles` may spend on `k` conjunctions that each reach at most
`r`. -/
def solesCost (S : Sorts) (u r k : Nat) : Nat := k * (countCost S u r + 5) + 4

/-- `soles` lists the one member of each conjunction that has one and no
more, and gives nothing when a conjunction has no member. -/
theorem soles_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Nat}
    (cs : List Sorts.Conj) (hsub : ∀ c ∈ cs, Sub U c)
    (hr : ∀ c ∈ cs, (Sorts.reachSet S c).card ≤ r) (s : store.Store)
    (decls names kids : store.TermId) (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hk : Repr nm s.nodes.val kids.val (encList (nm none) (cs.map (cpat (nm none) U))))
    (hroom : Room s (solesCost S U.length r cs.length)) :
    sorts.soles s decls names kids ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + solesCost S U.length r cs.length ∧
        ((∀ c ∈ cs, Sorts.count S c ≠ .none) → ∃ so, o = some so ∧
          Repr nm s'.nodes.val so.val
            (encList (nm none) (cs.map fun c => solePat (nm none) (oneOf S c)))) ∧
        ((∃ c ∈ cs, Sorts.count S c = .none) → o = none) ⦄ := by
  unfold sorts.soles
  have hroom' := hroom
  unfold Room at hroom'
  simp only [solesCost, Nat.mul_add] at hroom'
  step with alloc_w s .Nil hI.toWf trivial (by unfold Room; omega)
    as ⟨nil, s1, hW1, ht1, htb1, hx1, hid1, hst1⟩
  have rnil : Repr nm s1.nodes.val nil.val (.sym (nm none)) := .nil hid1
  have hI1 : Inv s1 := ⟨hW1, by rw [hst1]; exact hI.empty⟩
  step with soles_loop_spec hC decls names nil cs [] s1 nil kids true hsub hr hI1 (hx1.repr hde)
    (hx1.repr hU) rnil rnil (hx1.repr hk) (by unfold Room; simp only [Nat.mul_add]; omega)
    as ⟨s2, out, okb, hI2, hx2, ht2, h1, h2⟩
  simp only [Nat.mul_add] at ht2
  by_cases hall : ∀ c ∈ cs, Sorts.count S c ≠ .none
  · obtain ⟨rfl, ro⟩ := h1 hall
    simp only [List.append_nil] at ro
    simp only [↓reduceIte]
    step with rev_spec _ s2 out hI2.toWf ro
      (by rw [List.length_reverse, List.length_map]; unfold Room; omega) as ⟨ti, s3, hR3, rti⟩
    rw [List.length_reverse, List.length_map] at hR3
    have ht3 := hR3.ticks
    rw [List.reverse_reverse] at rti
    exact ⟨hR3.ranB.inv hI2, (hx1.trans hx2).trans hR3.ext,
      by simp only [solesCost, Nat.mul_add]; omega, fun _ => ⟨ti, rfl, rti⟩,
      fun c hc hcn => absurd hcn (hall c hc)⟩
  · have hex : ∃ c ∈ cs, Sorts.count S c = .none := by
      by_contra h0
      exact hall fun c hc hcn => h0 ⟨c, hc, hcn⟩
    obtain ⟨c, hc, hcn⟩ := hex
    have := h2 c hc hcn
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨hI2, hx1.trans hx2, by simp only [solesCost, Nat.mul_add]; omega,
      fun h => absurd hcn (h c hc), by intros; rfl⟩

/-! ## Which arguments are not the one member of their conjunction -/

/-- `is_sole` answers whether the term is the one member held. -/
theorem is_sole_spec (hnm : Function.Injective nm) (s : store.Store) (e a : store.TermId)
    {o : Option GTerm} {t : GTerm} (hW : Wf s)
    (he : Repr nm s.nodes.val e.val (solePat (nm none) o))
    (ha : Repr nm s.nodes.val a.val (GTerm.toPat t)) (hroom : Room s 2) :
    sorts.is_sole s e a ⦃ b s' => b = decide (o = some t) ∧ Ran s s' 2 ⦄ := by
  unfold sorts.is_sole
  have hroom' := hroom
  unfold Room at hroom'
  step with uncons_repr s e hW he (by unfold Room; omega) as ⟨o1, s1, hK, hu⟩
  cases o with
  | none =>
    simp only [solePat] at hu
    subst hu
    simp only [WP.spec_ok]
    exact ⟨by simp, hK.ran.mono (by omega)⟩
  | some t' =>
    simp only [solePat] at hu
    obtain ⟨m, tl, rfl, rm, -⟩ := hu
    simp only
    refine WP.spec_mono (same_w s1 m a hK.wf (by have := hK.ticks; unfold Room; omega)) ?_
    rintro ⟨b, s'⟩ ⟨hb, hK2⟩
    refine ⟨?_, hK.ran.trans hK2.ran⟩
    rw [hb]
    have : m.val = a.val ↔ t' = t :=
      ⟨fun h => toPat_inj (Repr.unique (h ▸ rm) ha), fun h => Repr.inj hnm hW.nodesOK (h ▸ rm) ha⟩
    simp [this]

/-- How many arguments are not the one member held for them. -/
def missCount : List (Option GTerm) → List GTerm → Nat
  | o :: sl, a :: ar => (if o = some a then 0 else 1) + missCount sl ar
  | _, _ => 0

theorem misses_loop_spec (hnm : Function.Injective nm) :
    ∀ (sl : List (Option GTerm)) (args : List GTerm) (k : Nat) (s : store.Store)
      (so ai : store.TermId) (any two : Bool),
    sl.length ≤ args.length → any = decide (0 < k) → two = decide (1 < k) → Wf s →
    Repr nm s.nodes.val so.val (encList (nm none) (sl.map (solePat (nm none)))) →
    Repr nm s.nodes.val ai.val (encList (nm none) (args.map GTerm.toPat)) →
    Room s (4 * sl.length + 1) →
    sorts.misses_loop so s any two ai ⦃ r =>
      Ran s r.1 (4 * sl.length + 1) ∧ r.2.1 = decide (0 < k + missCount sl args) ∧
        r.2.2 = decide (1 < k + missCount sl args) ⦄ := by
  intro sl
  induction sl with
  | nil =>
    intro args k s so ai any two _ hany htwo hW hso _ hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.misses_loop
    rw [loop]
    simp only [sorts.misses_loop.body]
    step with uncons_repr s so hW hso (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    have hfin : Ran s s1 (4 * ([] : List (Option GTerm)).length + 1) ∧
        any = decide (0 < k + missCount [] args) ∧ two = decide (1 < k + missCount [] args) :=
      ⟨hK.ran, by simpa [missCount] using hany, by simpa [missCount] using htwo⟩
    step*
  | cons o sl ih =>
    intro args k s so ai any two hlen hany htwo hW hso hai hroom
    obtain ⟨a, ar, rfl⟩ : ∃ a ar, args = a :: ar := by
      cases args with
      | nil => simp at hlen
      | cons a ar => exact ⟨a, ar, rfl⟩
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.mul_add] at hroom'
    unfold sorts.misses_loop
    rw [loop]
    simp only [sorts.misses_loop.body]
    step with uncons_repr s so hW hso (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o1, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨e, st, rfl, re, rst⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 ai hK.wf (hK.ran.ext.repr hai) (by unfold Room; omega)
      as ⟨r1, hK1, hu1⟩
    obtain ⟨o2, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨ae, ati, rfl, rae, rat⟩ := hu1
    have ht2 := hK1.ticks
    have R2 := hK.ran.trans hK1.ran
    step with is_sole_spec hnm s2 e ae R2.wf (R2.ext.repr re) (hK1.ran.ext.repr rae)
      (by unfold Room; omega) as ⟨r2, hb, hR3⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hb hR3
    have ht3 := hR3.ticks
    have R3 := R2.trans hR3
    simp only [uncurry, bind_ok]
    have IH := ih ar (k + (if o = some a then 0 else 1)) s3 st ati
    unfold sorts.misses_loop at IH
    refine WP.spec_mono (IH _ _ (by simpa using hlen) ?_ ?_ hR3.wf (R3.ext.repr rst)
      (hR3.ext.repr (hK1.ran.ext.repr rat)) (by unfold Room; omega)) ?_
    · subst hany hb
      by_cases h : o = some a <;> rcases k with _ | _ | k <;> simp [h]
    · subst hany htwo hb
      by_cases h : o = some a <;> rcases k with _ | _ | k <;> simp [h]
    · rintro r ⟨hR, h1, h2⟩
      refine ⟨(R3.trans hR).mono (by simp only [List.length_cons, Nat.mul_add]; omega), ?_, ?_⟩
      · rw [h1, missCount, Nat.add_assoc]
      · rw [h2, missCount, Nat.add_assoc]

/-- `misses` answers whether some argument is not the one member held for
it, and whether two are not. -/
theorem misses_spec (hnm : Function.Injective nm) (sl : List (Option GTerm)) (args : List GTerm)
    (s : store.Store) (so ai : store.TermId) (hlen : sl.length ≤ args.length) (hW : Wf s)
    (hso : Repr nm s.nodes.val so.val (encList (nm none) (sl.map (solePat (nm none)))))
    (hai : Repr nm s.nodes.val ai.val (encList (nm none) (args.map GTerm.toPat)))
    (hroom : Room s (4 * sl.length + 1)) :
    sorts.misses s so ai ⦃ r s' =>
      Ran s s' (4 * sl.length + 1) ∧ r.1 = decide (0 < missCount sl args) ∧
        r.2 = decide (1 < missCount sl args) ⦄ := by
  unfold sorts.misses
  step with misses_loop_spec hnm sl args 0 s so ai false false hlen (by simp) (by simp) hW hso hai
    hroom as ⟨s1, any, two, hR, h1, h2⟩
  simp only [Nat.zero_add] at h1 h2
  exact ⟨hR, h1, h2⟩

/-! ## Is the one member with a root among the terms -/

/-- Has the list a term with the root whose arguments are each the one
member held for them. -/
def onlyInL (sl : List (Option GTerm)) (f : Sym) (k : Nat) (G : List GTerm) : Bool :=
  G.any fun t =>
    decide ((termKey t).1 = f ∧ (termKey t).2 = k ∧ missCount sl (gspine t []).2 = 0)

/-- The ticks `only_in` may spend, where `L` members are held. -/
def onlyCost (L : Nat) : List GTerm → Nat
  | [] => 1
  | t :: G => 4 * (termKey t).2 + 4 * L + 7 + onlyCost L G

theorem only_in_done (s : store.Store) (so f ks g : store.TermId) (found : Bool) :
    sorts.only_in_loop s so f ks g found false ⦃ r => r = (found, s) ⦄ := by
  unfold sorts.only_in_loop
  rw [loop]
  simp only [sorts.only_in_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem only_in_loop_spec (hnm : Function.Injective nm) (sl : List (Option GTerm)) (f : Sym)
    (ksp : List Pat) (hsl : sl.length = ksp.length) (so fi ks : store.TermId) :
    ∀ (G : List GTerm) (s : store.Store) (g : store.TermId), Wf s →
    Repr nm s.nodes.val so.val (encList (nm none) (sl.map (solePat (nm none)))) →
    Repr nm s.nodes.val fi.val (.sym f) → Repr nm s.nodes.val ks.val (encList (nm none) ksp) →
    Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)) →
    Room s (onlyCost sl.length G) →
    sorts.only_in_loop s so fi ks g false true ⦃ r =>
      Ran s r.2 (onlyCost sl.length G) ∧ r.1 = onlyInL sl f ksp.length G ⦄ := by
  intro G
  induction G with
  | nil =>
    intro s g hW hso hf hks hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [onlyCost] at hroom'
    unfold sorts.only_in_loop
    rw [loop]
    simp only [sorts.only_in_loop.body, ↓reduceIte]
    step with uncons_repr s g hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := only_in_done s1 so fi ks g false
    unfold sorts.only_in_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran, by simp [onlyInL]⟩
  | cons t G ih =>
    intro s g hW hso hf hks hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [onlyCost] at hroom'
    unfold sorts.only_in_loop
    rw [loop]
    simp only [sorts.only_in_loop.body, ↓reduceIte]
    step with uncons_repr s g hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨ti, more, rfl, rti, rmore⟩ := hu
    have ht1 := hK.ticks
    have hx1 := hK.ran.ext
    have hna : nargs (GTerm.toPat t) = (termKey t).2 := by simpa [termKey] using nargs_toPat t []
    have hun := unspine_toPat t []
    simp only [List.map_nil] at hun
    have next : ∀ s3 : store.Store, Ran s s3 (4 * (termKey t).2 + 4 * sl.length + 7) →
        ¬ ((termKey t).1 = f ∧ (termKey t).2 = ksp.length ∧ missCount sl (gspine t []).2 = 0) →
        loop (fun x => match x with
          | (s1, g1, found1, go1) => sorts.only_in_loop.body so fi ks s1 g1 found1 go1)
          (s3, more, false, true) ⦃ r =>
            Ran s r.2 (onlyCost sl.length (t :: G)) ∧
              r.1 = onlyInL sl f ksp.length (t :: G) ⦄ := by
      intro s3 R3 hneg
      have := R3.ticks
      have IH := ih s3 more R3.wf (R3.ext.repr hso) (R3.ext.repr hf) (R3.ext.repr hks)
        (R3.ext.repr rmore) (by unfold Room; omega)
      unfold sorts.only_in_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R3.trans hR).mono (by simp only [onlyCost]; omega), ?_⟩
      rw [hr]
      simp only [onlyInL, List.any_cons, hneg, decide_false, Bool.false_or]
    step with spine_spec s1 ti hK.wf (hx1.repr rti) (by unfold Room; omega)
      as ⟨r1, hR2, rh, ra⟩
    obtain ⟨⟨h, args⟩, s2⟩ := r1
    simp only at hR2 rh ra
    rw [hun] at rh ra
    simp only at rh ra
    have rh' : Repr nm s2.nodes.val h.val (.sym (termKey t).1) := rh
    have ht2 := hR2.ticks
    have R2 := hK.ran.trans hR2
    step with same_w s2 h fi hR2.wf (by unfold Room; omega) as ⟨r2, hb, hK3⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hb hK3
    have ht3 := hK3.ticks
    have R3 := R2.trans hK3.ran
    have hbe : h.val = fi.val ↔ (termKey t).1 = f :=
      ⟨fun e => Term.sym.inj (Repr.unique (e ▸ rh') (R2.ext.repr hf)),
        fun e => Repr.inj hnm hR2.wf.nodesOK (e ▸ rh') (R2.ext.repr hf)⟩
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      refine next s3 (R3.mono (by omega)) fun hk => ?_
      have := hbe.2 hk.1
      simp [this] at hb
    | true =>
      have hlm : ((gspine t []).2.map GTerm.toPat).length = (termKey t).2 := by simp [termKey]
      simp only [uncurry, ↓reduceIte]
      step with same_len_spec ((gspine t []).2.map GTerm.toPat) ksp s3 args ks hK3.wf
        (hK3.ran.ext.repr ra) (R3.ext.repr hks) (by rw [hlm]; unfold Room; omega)
        as ⟨r4, hb1, hR4⟩
      obtain ⟨b1, s4⟩ := r4
      simp only at hb1 hR4
      rw [hlm] at hb1 hR4
      have ht4 := hR4.ticks
      have R4 := R3.trans hR4
      cases b1 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
        refine next s4 (R4.mono (by omega)) fun hk => ?_
        simp [hk.2.1] at hb1
      | true =>
        have hk2 : (termKey t).2 = ksp.length := by simpa using hb1.symm
        simp only [uncurry, ↓reduceIte]
        step with misses_spec hnm sl (gspine t []).2 s4 so args
          (by rw [hsl, ← hk2]; exact Nat.le_refl _) hR4.wf (R4.ext.repr hso)
          (hR4.ext.repr (hK3.ran.ext.repr ra)) (by unfold Room; omega) as ⟨r5, hR5, h1, h2⟩
        obtain ⟨⟨any, two⟩, s5⟩ := r5
        simp only at hR5 h1 h2
        have ht5 := hR5.ticks
        have R5 := R4.trans hR5
        cases any with
        | true =>
          simp only [↓reduceIte, uncurry, bind_ok]
          refine next s5 (R5.mono (by omega)) fun hk => ?_
          simp [hk.2.2] at h1
        | false =>
          have hm0 : missCount sl (gspine t []).2 = 0 := by simpa using h1.symm
          simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
          have hdn := only_in_done s5 so fi ks g true
          unfold sorts.only_in_loop at hdn
          refine WP.spec_mono hdn ?_
          rintro r rfl
          have hpos : 1 ≤ onlyCost sl.length G := by cases G <;> simp only [onlyCost] <;> omega
          refine ⟨R5.mono (by simp only [onlyCost]; omega), ?_⟩
          have hf' : (termKey t).1 = f := hbe.1 (by simpa using hb.symm)
          simp [onlyInL, hf', hk2, hm0]

/-- `only_in` answers whether a term of the list has the root and each
argument the one member held for it. -/
theorem only_in_spec (hnm : Function.Injective nm) (sl : List (Option GTerm)) (f : Sym)
    (ksp : List Pat) (hsl : sl.length = ksp.length) (G : List GTerm) (s : store.Store)
    (so fi ks g : store.TermId) (hW : Wf s)
    (hso : Repr nm s.nodes.val so.val (encList (nm none) (sl.map (solePat (nm none)))))
    (hf : Repr nm s.nodes.val fi.val (.sym f))
    (hks : Repr nm s.nodes.val ks.val (encList (nm none) ksp))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hroom : Room s (onlyCost sl.length G)) :
    sorts.only_in s so fi ks g ⦃ r s' =>
      Ran s s' (onlyCost sl.length G) ∧ r = onlyInL sl f ksp.length G ⦄ :=
  only_in_loop_spec hnm sl f ksp hsl so fi ks G s g hW hso hf hks hg hroom

/-! ## The arguments of the terms that are left to ask about -/

theorem alloc_ran (s : store.Store) (n : store.Node) (hW : Wf s) (hn : ArgOK s.nodes.val n)
    (hroom : Room s 1) :
    store.Store.alloc s n ⦃ id s' => Ran s s' 1 ∧ s'.nodes.val[id.val]? = some (norm n) ⦄ := by
  refine WP.spec_mono (alloc_w s n hW hn hroom) ?_
  rintro ⟨id, s'⟩ ⟨hW', ht, htb, hx, hid, hst⟩
  exact ⟨⟨hW', hx, htb, hst, Nat.le_of_eq ht⟩, hid⟩

/-- The lists, each with its argument in front unless `any` holds and the
argument is the one member held for it. -/
def contribL (any : Bool) :
    List (Option GTerm) → List GTerm → List (List GTerm) → List (List GTerm)
  | o :: sl, a :: ar, acc :: accs =>
    (if any = true ∧ o = some a then acc else a :: acc) :: contribL any sl ar accs
  | _, _, _ => []

theorem length_contribL (any : Bool) : ∀ (sl : List (Option GTerm)) (args : List GTerm)
    (accs : List (List GTerm)), sl.length ≤ args.length → sl.length ≤ accs.length →
    (contribL any sl args accs).length = sl.length
  | [], _, _, _, _ => by simp [contribL]
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | o :: sl, a :: ar, acc :: accs, h1, h2 => by
    simp only [contribL, List.length_cons]
    rw [length_contribL any sl ar accs (by simpa using h1) (by simpa using h2)]

/-- A list of ground terms as a term. -/
def accPat (z : Sym) (l : List GTerm) : Pat := encList z (l.map GTerm.toPat)

theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem contrib_loop_spec (hnm : Function.Injective nm) (any : Bool) :
    ∀ (sl : List (Option GTerm)) (args : List GTerm) (accs : List (List GTerm)) (outs : List Pat)
      (s : store.Store) (so ai ci out : store.TermId),
    sl.length ≤ args.length → sl.length ≤ accs.length → Wf s →
    Repr nm s.nodes.val so.val (encList (nm none) (sl.map (solePat (nm none)))) →
    Repr nm s.nodes.val ai.val (encList (nm none) (args.map GTerm.toPat)) →
    Repr nm s.nodes.val ci.val (encList (nm none) (accs.map (accPat (nm none)))) →
    Repr nm s.nodes.val out.val (encList (nm none) outs) →
    Room s (7 * sl.length + 1) →
    sorts.contrib_loop so s any out ai ci ⦃ r =>
      Ran s r.1 (7 * sl.length + 1) ∧ Repr nm r.1.nodes.val r.2.val (encList (nm none)
        (((contribL any sl args accs).map (accPat (nm none))).reverse ++ outs)) ⦄ := by
  intro sl
  induction sl with
  | nil =>
    intro args accs outs s so ai ci out _ _ hW hso _ _ ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.contrib_loop
    rw [loop]
    simp only [sorts.contrib_loop.body]
    step with uncons_repr s so hW hso (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    have hfin : Ran s s1 (7 * ([] : List (Option GTerm)).length + 1) ∧
        Repr nm s1.nodes.val out.val (encList (nm none)
          (((contribL any [] args accs).map (accPat (nm none))).reverse ++ outs)) :=
      ⟨hK.ran, by simpa [contribL] using hK.ran.ext.repr ho⟩
    step*
  | cons o sl ih =>
    intro args accs outs s so ai ci out hl1 hl2 hW hso hai hci ho hroom
    obtain ⟨a, ar, rfl⟩ : ∃ a ar, args = a :: ar := by
      cases args with
      | nil => simp at hl1
      | cons a ar => exact ⟨a, ar, rfl⟩
    obtain ⟨acc, accs', rfl⟩ : ∃ acc accs', accs = acc :: accs' := by
      cases accs with
      | nil => simp at hl2
      | cons acc accs' => exact ⟨acc, accs', rfl⟩
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.mul_add] at hroom'
    unfold sorts.contrib_loop
    rw [loop]
    simp only [sorts.contrib_loop.body]
    step with uncons_repr s so hW hso (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o1, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨e, st, rfl, re, rst⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 ai hK.wf (hK.ran.ext.repr hai) (by unfold Room; omega)
      as ⟨r1, hK1, hu1⟩
    obtain ⟨o2, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨ae, ati, rfl, rae, rat⟩ := hu1
    rw [hK.nodes] at rae rat
    have ht2 := hK1.ticks
    have R2 := hK.ran.trans hK1.ran
    step with uncons_repr s2 ci hK1.wf (R2.ext.repr hci) (by unfold Room; omega)
      as ⟨r2, hK2, hu2⟩
    obtain ⟨o3, s3⟩ := r2
    simp only at hu2
    simp only at hK2
    obtain ⟨acci, cti, rfl, racc, rct⟩ := hu2
    rw [hK1.nodes, hK.nodes] at racc rct
    have ht3 := hK2.ticks
    have R3 := R2.trans hK2.ran
    have rae3 : Repr nm s3.nodes.val ae.val (GTerm.toPat a) := R3.ext.repr rae
    have racc3 : Repr nm s3.nodes.val acci.val (accPat (nm none) acc) := R3.ext.repr racc
    have ro3 : Repr nm s3.nodes.val out.val (encList (nm none) outs) := R3.ext.repr ho
    have tail : ∀ (s6 : store.Store) (out1 : store.TermId) (l1 : List GTerm), Ran s s6 7 →
        Repr nm s6.nodes.val out1.val (encList (nm none) (accPat (nm none) l1 :: outs)) →
        l1 = (if any = true ∧ o = some a then acc else a :: acc) →
        loop (fun x => match x with
          | (so1, s1, out1, args1, accs1) => sorts.contrib_loop.body any so1 s1 out1 args1 accs1)
          (st, s6, out1, ati, cti) ⦃ r =>
          Ran s r.1 (7 * (o :: sl).length + 1) ∧ Repr nm r.1.nodes.val r.2.val (encList (nm none)
            (((contribL any (o :: sl) (a :: ar) (acc :: accs')).map (accPat (nm none))).reverse ++
              outs)) ⦄ := by
      intro s6 out1 l1 R6 ro1 hl
      have := R6.ticks
      have IH := ih ar accs' (accPat (nm none) l1 :: outs) s6 st ati cti out1
        (by simpa using hl1) (by simpa using hl2) R6.wf (R6.ext.repr rst)
        (R6.ext.repr rat) (R6.ext.repr rct) ro1
        (by unfold Room; omega)
      unfold sorts.contrib_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R6.trans hR).mono (by simp only [List.length_cons, Nat.mul_add]; omega), ?_⟩
      simpa only [contribL, ← hl, List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hr
    simp only [uncurry]
    by_cases hany : any = true
    swap
    · rw [ite_neg' hany]
      simp only [bind_ok, uncurry, ↓reduceIte]
      step with alloc_ran s3 (.App ae acci) hK2.wf ⟨rae3.lt, racc3.lt⟩ (by unfold Room; omega)
        as ⟨r4, hR4, hid4⟩
      obtain ⟨acc1, s4⟩ := r4
      simp only at hR4 hid4
      have ht4 := hR4.ticks
      have rl : Repr nm s4.nodes.val acc1.val (accPat (nm none) (a :: acc)) :=
        .app hid4 (hR4.ext.repr rae3) (hR4.ext.repr racc3)
      step with alloc_ran s4 (.App acc1 out) hR4.wf ⟨rl.lt, (hR4.ext.repr ro3).lt⟩
        (by unfold Room; omega) as ⟨r5, hR5, hid5⟩
      obtain ⟨out1, s5⟩ := r5
      simp only at hR5 hid5
      simp only [uncurry, bind_ok]
      exact tail s5 out1 (a :: acc) (((R3.trans hR4).trans hR5).mono (by omega))
        (.app hid5 (hR5.ext.repr rl) (hR5.ext.repr (hR4.ext.repr ro3))) (by simp [hany])
    · rw [ite_pos' hany]
      step with is_sole_spec hnm s3 e ae hK2.wf (R3.ext.repr re) rae3 (by unfold Room; omega)
        as ⟨r4, hb, hR4⟩
      obtain ⟨b, s4⟩ := r4
      simp only at hb hR4
      have ht4 := hR4.ticks
      cases b with
      | true =>
        have hoa : o = some a := by simpa using hb.symm
        simp only [uncurry, bind_ok, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        step with alloc_ran s4 (.App acci out) hR4.wf
          ⟨(hR4.ext.repr racc3).lt, (hR4.ext.repr ro3).lt⟩ (by unfold Room; omega)
          as ⟨r5, hR5, hid5⟩
        obtain ⟨out1, s5⟩ := r5
        simp only at hR5 hid5
        simp only [uncurry, bind_ok]
        exact tail s5 out1 acc (((R3.trans hR4).trans hR5).mono (by omega))
          (.app hid5 (hR5.ext.repr (hR4.ext.repr racc3)) (hR5.ext.repr (hR4.ext.repr ro3)))
          (by simp [hoa, hany])
      | false =>
        have hoa : o ≠ some a := by simpa using hb.symm
        simp only [uncurry, bind_ok, Bool.false_eq_true, not_false_eq_true, decide_true,
          ↓reduceIte]
        step with alloc_ran s4 (.App ae acci) hR4.wf
          ⟨(hR4.ext.repr rae3).lt, (hR4.ext.repr racc3).lt⟩ (by unfold Room; omega)
          as ⟨r5, hR5, hid5⟩
        obtain ⟨acc1, s5⟩ := r5
        simp only at hR5 hid5
        have ht5 := hR5.ticks
        have rl : Repr nm s5.nodes.val acc1.val (accPat (nm none) (a :: acc)) :=
          .app hid5 (hR5.ext.repr (hR4.ext.repr rae3)) (hR5.ext.repr (hR4.ext.repr racc3))
        step with alloc_ran s5 (.App acc1 out) hR5.wf
          ⟨rl.lt, (hR5.ext.repr (hR4.ext.repr ro3)).lt⟩ (by unfold Room; omega)
          as ⟨r6, hR6, hid6⟩
        obtain ⟨out1, s6⟩ := r6
        simp only at hR6 hid6
        simp only [uncurry, bind_ok]
        exact tail s6 out1 (a :: acc) ((((R3.trans hR4).trans hR5).trans hR6).mono (by omega))
          (.app hid6 (hR6.ext.repr rl) (hR6.ext.repr (hR5.ext.repr (hR4.ext.repr ro3))))
          (by simp [hoa, hany])

/-- `contrib` puts each argument in front of its list, unless `any` holds
and the argument is the one member held for it. -/
theorem contrib_spec (hnm : Function.Injective nm) (any : Bool) (sl : List (Option GTerm))
    (args : List GTerm) (accs : List (List GTerm)) (s : store.Store) (so ai ci : store.TermId)
    (hl1 : sl.length ≤ args.length) (hl2 : sl.length ≤ accs.length) (hW : Wf s)
    (hso : Repr nm s.nodes.val so.val (encList (nm none) (sl.map (solePat (nm none)))))
    (hai : Repr nm s.nodes.val ai.val (encList (nm none) (args.map GTerm.toPat)))
    (hci : Repr nm s.nodes.val ci.val (encList (nm none) (accs.map (accPat (nm none)))))
    (hroom : Room s (9 * sl.length + 4)) :
    sorts.contrib s so ai ci any ⦃ r s' =>
      Ran s s' (9 * sl.length + 4) ∧ Repr nm s'.nodes.val r.val
        (encList (nm none) ((contribL any sl args accs).map (accPat (nm none)))) ⦄ := by
  unfold sorts.contrib
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_ran s .Nil hW trivial (by unfold Room; omega) as ⟨out, s1, hR1, hid1⟩
  have ht1 := hR1.ticks
  step with contrib_loop_spec hnm any sl args accs [] s1 so ai ci out hl1 hl2 hR1.wf
    (hR1.ext.repr hso) (hR1.ext.repr hai) (hR1.ext.repr hci) (.nil hid1) (by unfold Room; omega)
    as ⟨s2, out1, hR2, ro⟩
  have ht2 := hR2.ticks
  simp only [List.append_nil] at ro
  have hlen := length_contribL any sl args accs hl1 hl2
  refine WP.spec_mono (rev_spec _ s2 out1 hR2.wf ro
    (by rw [List.length_reverse, List.length_map, hlen]; unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hR3, rr⟩
  rw [List.length_reverse, List.length_map, hlen] at hR3
  rw [List.reverse_reverse] at rr
  exact ⟨((hR1.trans hR2).trans hR3).mono (by omega), rr⟩

/-- The lists with the arguments of a term in front, when the term has the
root and at most one argument is not the one member held for it. -/
def projStep (sl : List (Option GTerm)) (f : Sym) (k : Nat) (accs : List (List GTerm))
    (t : GTerm) : List (List GTerm) :=
  if (termKey t).1 = f ∧ (termKey t).2 = k ∧ missCount sl (gspine t []).2 ≤ 1 then
    contribL (decide (0 < missCount sl (gspine t []).2)) sl (gspine t []).2 accs
  else accs

/-- What `projs` gives, from lists to start with. -/
def projsL (sl : List (Option GTerm)) (f : Sym) (k : Nat) (G : List GTerm)
    (accs : List (List GTerm)) : List (List GTerm) :=
  G.foldl (projStep sl f k) accs

theorem length_projStep {sl : List (Option GTerm)} {f : Sym} {k : Nat} (hsl : sl.length = k)
    {accs : List (List GTerm)} (ha : accs.length = k) (t : GTerm) :
    (projStep sl f k accs t).length = k := by
  unfold projStep
  split
  · rename_i h
    rw [length_contribL _ _ _ _ (by have := h.2.1; simp only [termKey] at this; omega)
      (by omega), hsl]
  · exact ha

/-- The ticks the loop of `projs` may spend, where `L` members are held. -/
def projsCost (L : Nat) : List GTerm → Nat
  | [] => 1
  | t :: G => 4 * (termKey t).2 + 13 * L + 11 + projsCost L G

theorem projs_loop_spec (hnm : Function.Injective nm) (sl : List (Option GTerm)) (f : Sym)
    (ksp : List Pat) (hsl : sl.length = ksp.length) (so fi ks : store.TermId) :
    ∀ (G : List GTerm) (accs : List (List GTerm)) (s : store.Store) (g ai : store.TermId),
    accs.length = ksp.length → Wf s →
    Repr nm s.nodes.val so.val (encList (nm none) (sl.map (solePat (nm none)))) →
    Repr nm s.nodes.val fi.val (.sym f) → Repr nm s.nodes.val ks.val (encList (nm none) ksp) →
    Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)) →
    Repr nm s.nodes.val ai.val (encList (nm none) (accs.map (accPat (nm none)))) →
    Room s (projsCost sl.length G) →
    sorts.projs_loop g s so fi ks ai ⦃ r s' =>
      Ran s s' (projsCost sl.length G) ∧ Repr nm s'.nodes.val r.val
        (encList (nm none) ((projsL sl f ksp.length G accs).map (accPat (nm none)))) ⦄ := by
  intro G
  induction G with
  | nil =>
    intro accs s g ai _ hW hso hf hks hg hai hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [projsCost] at hroom'
    unfold sorts.projs_loop
    rw [loop]
    simp only [sorts.projs_loop.body]
    step with uncons_repr s g hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    have hfin : Ran s s1 (projsCost sl.length []) ∧ Repr nm s1.nodes.val ai.val
        (encList (nm none) ((projsL sl f ksp.length [] accs).map (accPat (nm none)))) :=
      ⟨hK.ran, by rw [hK.nodes]; exact hai⟩
    step*
  | cons t G ih =>
    intro accs s g ai hal hW hso hf hks hg hai hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [projsCost] at hroom'
    unfold sorts.projs_loop
    rw [loop]
    simp only [sorts.projs_loop.body]
    step with uncons_repr s g hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨ti, more, rfl, rti, rmore⟩ := hu
    have ht1 := hK.ticks
    have hx1 := hK.ran.ext
    have hna : nargs (GTerm.toPat t) = (termKey t).2 := by simpa [termKey] using nargs_toPat t []
    have hun := unspine_toPat t []
    simp only [List.map_nil] at hun
    have next : ∀ (s3 : store.Store) (a1 : store.TermId),
        Ran s s3 (4 * (termKey t).2 + 13 * sl.length + 11) →
        Repr nm s3.nodes.val a1.val (encList (nm none)
          ((projStep sl f ksp.length accs t).map (accPat (nm none)))) →
        loop (fun x => match x with
          | (g1, s1, accs1) => sorts.projs_loop.body so fi ks g1 s1 accs1)
          (more, s3, a1) ⦃ r s' =>
            Ran s s' (projsCost sl.length (t :: G)) ∧ Repr nm s'.nodes.val r.val (encList (nm none)
              ((projsL sl f ksp.length (t :: G) accs).map (accPat (nm none)))) ⦄ := by
      intro s3 a1 R3 ra1
      have := R3.ticks
      have IH := ih (projStep sl f ksp.length accs t) s3 more a1
        (length_projStep hsl hal t) R3.wf (R3.ext.repr hso) (R3.ext.repr hf) (R3.ext.repr hks)
        (R3.ext.repr rmore) ra1 (by unfold Room; omega)
      unfold sorts.projs_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hr⟩
      exact ⟨(R3.trans hR).mono (by simp only [projsCost]; omega), hr⟩
    have same : ∀ (s3 : store.Store),
        Ran s s3 (4 * (termKey t).2 + 13 * sl.length + 11) →
        ¬ ((termKey t).1 = f ∧ (termKey t).2 = ksp.length ∧ missCount sl (gspine t []).2 ≤ 1) →
        loop (fun x => match x with
          | (g1, s1, accs1) => sorts.projs_loop.body so fi ks g1 s1 accs1)
          (more, s3, ai) ⦃ r s' =>
            Ran s s' (projsCost sl.length (t :: G)) ∧ Repr nm s'.nodes.val r.val (encList (nm none)
              ((projsL sl f ksp.length (t :: G) accs).map (accPat (nm none)))) ⦄ := by
      intro s3 R3 hneg
      refine next s3 ai R3 ?_
      rw [projStep, ite_neg' hneg]
      exact R3.ext.repr hai
    step with spine_spec s1 ti hK.wf (hx1.repr rti) (by unfold Room; omega)
      as ⟨r1, hR2, rh, ra⟩
    obtain ⟨⟨h, args⟩, s2⟩ := r1
    simp only at hR2 rh ra
    rw [hun] at rh ra
    simp only at rh ra
    have rh' : Repr nm s2.nodes.val h.val (.sym (termKey t).1) := rh
    have ht2 := hR2.ticks
    have R2 := hK.ran.trans hR2
    step with same_w s2 h fi hR2.wf (by unfold Room; omega) as ⟨r2, hb, hK3⟩
    obtain ⟨b, s3⟩ := r2
    simp only at hb hK3
    have ht3 := hK3.ticks
    have R3 := R2.trans hK3.ran
    have hbe : h.val = fi.val ↔ (termKey t).1 = f :=
      ⟨fun e => Term.sym.inj (Repr.unique (e ▸ rh') (R2.ext.repr hf)),
        fun e => Repr.inj hnm hR2.wf.nodesOK (e ▸ rh') (R2.ext.repr hf)⟩
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      refine same s3 (R3.mono (by omega)) fun hk => ?_
      have := hbe.2 hk.1
      simp [this] at hb
    | true =>
      have hlm : ((gspine t []).2.map GTerm.toPat).length = (termKey t).2 := by simp [termKey]
      simp only [uncurry, ↓reduceIte]
      step with same_len_spec ((gspine t []).2.map GTerm.toPat) ksp s3 args ks hK3.wf
        (hK3.ran.ext.repr ra) (R3.ext.repr hks) (by rw [hlm]; unfold Room; omega)
        as ⟨r4, hb1, hR4⟩
      obtain ⟨b1, s4⟩ := r4
      simp only at hb1 hR4
      rw [hlm] at hb1 hR4
      have ht4 := hR4.ticks
      have R4 := R3.trans hR4
      cases b1 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
        refine same s4 (R4.mono (by omega)) fun hk => ?_
        simp [hk.2.1] at hb1
      | true =>
        have hk2 : (termKey t).2 = ksp.length := by simpa using hb1.symm
        have hf' : (termKey t).1 = f := hbe.1 (by simpa using hb.symm)
        have hal2 : sl.length ≤ (gspine t []).2.length := by
          rw [hsl, ← hk2]; exact Nat.le_refl _
        simp only [uncurry, ↓reduceIte]
        step with misses_spec hnm sl (gspine t []).2 s4 so args hal2 hR4.wf (R4.ext.repr hso)
          (hR4.ext.repr (hK3.ran.ext.repr ra)) (by unfold Room; omega) as ⟨r5, hR5, h1, h2⟩
        obtain ⟨⟨any, two⟩, s5⟩ := r5
        simp only at hR5 h1 h2
        have ht5 := hR5.ticks
        have R5 := R4.trans hR5
        cases two with
        | true =>
          simp only [↓reduceIte, uncurry, bind_ok]
          refine same s5 (R5.mono (by omega)) fun hk => ?_
          have : ¬ (1 < missCount sl (gspine t []).2) := by omega
          simp [this] at h2
        | false =>
          have hm1 : missCount sl (gspine t []).2 ≤ 1 := by
            have : ¬ (1 < missCount sl (gspine t []).2) := by simpa using h2.symm
            omega
          simp only [Bool.false_eq_true, ↓reduceIte, uncurry]
          step with contrib_spec hnm any sl (gspine t []).2 accs s5 so args ai hal2
            (by rw [hal, hsl]) hR5.wf (R5.ext.repr hso)
            (hR5.ext.repr (hR4.ext.repr (hK3.ran.ext.repr ra))) (R5.ext.repr hai)
            (by unfold Room; omega) as ⟨r6, hR6, racc⟩
          obtain ⟨accs1, s6⟩ := r6
          simp only at hR6 racc
          have ht6 := hR6.ticks
          simp only [uncurry, bind_ok]
          refine next s6 accs1 ((R5.trans hR6).mono (by omega)) ?_
          rw [projStep, ite_pos' ⟨hf', hk2, hm1⟩, ← h1]
          exact racc

/-- The ticks `projs` may spend. -/
def projsAllCost (L k : Nat) (G : List GTerm) : Nat := 2 * k + 3 + projsCost L G

/-- `projs` gives, for each argument of the root, that argument of the terms
with the root whose other arguments are each the one member held for them. -/
theorem projs_spec (hnm : Function.Injective nm) (sl : List (Option GTerm)) (f : Sym)
    (ksp : List Pat) (hsl : sl.length = ksp.length) (G : List GTerm) (s : store.Store)
    (so fi ks g : store.TermId) (hW : Wf s)
    (hso : Repr nm s.nodes.val so.val (encList (nm none) (sl.map (solePat (nm none)))))
    (hf : Repr nm s.nodes.val fi.val (.sym f))
    (hks : Repr nm s.nodes.val ks.val (encList (nm none) ksp))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hroom : Room s (projsAllCost sl.length ksp.length G)) :
    sorts.projs s so fi ks g ⦃ r s' =>
      Ran s s' (projsAllCost sl.length ksp.length G) ∧ Repr nm s'.nodes.val r.val
        (encList (nm none) ((projsL sl f ksp.length G (List.replicate ksp.length [])).map
          (accPat (nm none)))) ⦄ := by
  unfold sorts.projs
  have hroom' := hroom
  unfold Room at hroom'
  simp only [projsAllCost] at hroom'
  step with alloc_ran s .Nil hW trivial (by unfold Room; omega) as ⟨nil, s1, hR1, hid1⟩
  have ht1 := hR1.ticks
  have rnil : Repr nm s1.nodes.val nil.val (.sym (nm none)) := .nil hid1
  step with fill_spec ksp s1 ks nil hR1.wf (hR1.ext.repr hks) rnil (by unfold Room; omega)
    as ⟨accs, s2, hR2, racc⟩
  have ht2 := hR2.ticks
  have R2 := hR1.trans hR2
  have racc' : Repr nm s2.nodes.val accs.val (encList (nm none)
      ((List.replicate ksp.length ([] : List GTerm)).map (accPat (nm none)))) := by
    simpa [accPat, encList] using racc
  refine WP.spec_mono (projs_loop_spec hnm sl f ksp hsl so fi ks G _ s2 g accs
    (List.length_replicate ..) hR2.wf (R2.ext.repr hso) (R2.ext.repr hf) (R2.ext.repr hks)
    (R2.ext.repr hg) racc' (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨hR, hr⟩
  exact ⟨(R2.trans hR).mono (by simp only [projsAllCost]; omega), hr⟩

/-! ## What a root leaves to ask -/

theorem is_nil_list (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId)
    {ps : List Pat} (hW : Wf s) (hp : Repr nm s.nodes.val p.val (encList (nm none) ps))
    (hroom : Room s 1) :
    sorts.is_nil s p ⦃ b s' => (b = true ↔ ps = []) ∧ KeptW s s' 1 ⦄ := by
  refine WP.spec_mono (is_nil_w s p hW hp.lt hroom) ?_
  rintro ⟨b, s'⟩ ⟨hb, hK⟩
  refine ⟨?_, hK⟩
  rw [hb]
  cases ps with
  | nil =>
    simp only [encList] at hp
    rcases hp.sym_node with h | ⟨f, -, e⟩
    · simp [h.1]
    · cases hnm e
  | cons a l =>
    simp only [encList] at hp
    obtain ⟨a', b', h, -, -⟩ := Repr.app_inv hp
    simp [h]

/-- What is left to ask: whether a conjunction, but for the terms, is in a
sort. -/
abbrev Ask := Sorts.Conj × Name × List GTerm

/-- What is left to ask as a term. -/
noncomputable def askPat (z : Sym) (U : List Name) (a : Ask) : Pat :=
  .app (cpat z U a.1) (.app (.sym a.2.1) (accPat z a.2.2))

/-- What an argument leaves to ask, when its sort is given and terms are
left. -/
def askOf : Sorts.Conj × Option Name × List GTerm → Option Ask
  | (c, some m, a :: l) => some (c, m, a :: l)
  | _ => none

/-- What is left to ask with what the arguments leave in front. -/
def pushL (items : List (Sorts.Conj × Option Name × List GTerm)) (T : List Ask) : List Ask :=
  (items.filterMap askOf).reverse ++ T

/-- Every argument whose sort is given and that leaves no term is in its
sort. -/
def pushOK (S : Sorts) (items : List (Sorts.Conj × Option Name × List GTerm)) : Prop :=
  ∀ x ∈ items, ∀ m, x.2.1 = some m → x.2.2 = [] → Sorts.Incl S x.1 m

theorem pushL_cons (x : Sorts.Conj × Option Name × List GTerm)
    (items : List (Sorts.Conj × Option Name × List GTerm)) (T : List Ask) :
    pushL (x :: items) T = pushL items ((askOf x).toList ++ T) := by
  unfold pushL
  cases h : askOf x <;> simp [h]

theorem push_asks_done (s : store.Store) (decls names todo kids kn accs : store.TermId)
    (okb : Bool) :
    sorts.push_asks_loop s decls names todo kids kn accs okb false ⦃ r => r = (s, todo, okb) ⦄ := by
  unfold sorts.push_asks_loop
  rw [loop]
  simp only [sorts.push_asks_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem push_asks_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Nat}
    (decls names : store.TermId) :
    ∀ (cs : List Sorts.Conj) (ks : List (Option Name)) (accs : List (List GTerm)) (T : List Ask)
      (s : store.Store) (todo kids kn ai : store.TermId) (okb : Bool),
    cs.length = ks.length → cs.length = accs.length → (∀ c ∈ cs, Sub U c) →
    (∀ m, some m ∈ ks → m ∈ Sorts.names S) →
    (∀ c ∈ cs, ∀ m, (Sorts.reachGSet S (c, some m)).card ≤ r) → Inv s →
    Repr nm s.nodes.val decls.val sp → Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val todo.val (encList (nm none) (T.map (askPat (nm none) U))) →
    Repr nm s.nodes.val kids.val (encList (nm none) (cs.map (cpat (nm none) U))) →
    Repr nm s.nodes.val kn.val (encList (nm none) (ks.map (kidPat (nm none)))) →
    Repr nm s.nodes.val ai.val (encList (nm none) (accs.map (accPat (nm none)))) →
    Room s (cs.length * (inclCost S U.length r + 8) + 1) →
    sorts.push_asks_loop s decls names todo kids kn ai okb true ⦃ res =>
      Inv res.1 ∧ Extends s res.1 ∧
        res.1.ticks.val ≤ s.ticks.val + (cs.length * (inclCost S U.length r + 8) + 1) ∧
        (pushOK S (cs.zip (ks.zip accs)) → res.2.2 = okb ∧
          Repr nm res.1.nodes.val res.2.1.val
            (encList (nm none) ((pushL (cs.zip (ks.zip accs)) T).map (askPat (nm none) U)))) ∧
        (¬ pushOK S (cs.zip (ks.zip accs)) → res.2.2 = false) ⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro ks accs T s todo kids kn ai okb _ _ _ _ _ hI hde hU htd hk _ _ hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.push_asks_loop
    rw [loop]
    simp only [sorts.push_asks_loop.body, ↓reduceIte]
    step with uncons_repr s kids hI.toWf hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := push_asks_done s1 decls names todo kids kn ai okb
    unfold sorts.push_asks_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro res rfl
    have := hK.ticks
    exact ⟨hK.ran.ranB.inv hI, hK.ran.ext, by simp only; omega,
      fun _ => ⟨rfl, by simpa [pushL] using hK.ran.ext.repr htd⟩,
      fun h => absurd (by simp [pushOK]) h⟩
  | cons c cs ih =>
    intro ks accs T s todo kids kn ai okb hl1 hl2 hsub hnames hr hI hde hU htd hk hkn hai hroom
    obtain ⟨k, ks', rfl⟩ : ∃ k ks', ks = k :: ks' := by
      cases ks with
      | nil => simp at hl1
      | cons k ks' => exact ⟨k, ks', rfl⟩
    obtain ⟨l, accs', rfl⟩ : ∃ l accs', accs = l :: accs' := by
      cases accs with
      | nil => simp at hl2
      | cons l accs' => exact ⟨l, accs', rfl⟩
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    have hW := hI.toWf
    unfold sorts.push_asks_loop
    rw [loop]
    simp only [sorts.push_asks_loop.body, ↓reduceIte]
    step with uncons_repr s kids hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨ki, kt, rfl, rki, rkt⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 kn hK.wf (hK.ran.ext.repr hkn) (by unfold Room; omega)
      as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨mi, mt, rfl, rmi, rmt⟩ := hu1
    rw [hK.nodes] at rmi rmt
    have ht2 := hK1.ticks
    have R2 := hK.ran.trans hK1.ran
    step with uncons_repr s2 ai hK1.wf (R2.ext.repr hai) (by unfold Room; omega)
      as ⟨r2, hK2, hu2⟩
    obtain ⟨o2, s3⟩ := r2
    simp only at hu2
    simp only at hK2
    obtain ⟨acci, cti, rfl, racc, rct⟩ := hu2
    rw [hK1.nodes, hK.nodes] at racc rct
    have ht3 := hK2.ticks
    have R3 := R2.trans hK2.ran
    have hkz : ∀ m, k = some m → m ≠ nm none := fun m hm =>
      hC.nz m (hnames m (by rw [hm]; exact List.mem_cons_self))
    step with is_nil_kid hC.inj s3 mi hK2.wf (R3.ext.repr rmi) hkz (by unfold Room; omega)
      as ⟨r3, hb, hK4⟩
    obtain ⟨b, s4⟩ := r3
    simp only at hb hK4
    have ht4 := hK4.ticks
    have R4 := R3.trans hK4.ran
    have next : ∀ (s' : store.Store) (todo' : store.TermId) (T' : List Ask), Inv s' →
        Extends s s' → s'.ticks.val ≤ s.ticks.val + (inclCost S U.length r + 8) →
        Repr nm s'.nodes.val todo'.val (encList (nm none) (T'.map (askPat (nm none) U))) →
        T' = (askOf (c, k, l)).toList ++ T → (∀ m, k = some m → l = [] → Sorts.Incl S c m) →
        loop (fun x => match x with
          | (s1, todo1, kids1, kn1, accs1, ok2, go1) =>
            sorts.push_asks_loop.body decls names s1 todo1 kids1 kn1 accs1 ok2 go1)
          (s', todo', kt, mt, cti, okb, true) ⦃ res =>
          Inv res.1 ∧ Extends s res.1 ∧
            res.1.ticks.val ≤ s.ticks.val + ((c :: cs).length * (inclCost S U.length r + 8) + 1) ∧
            (pushOK S ((c :: cs).zip ((k :: ks').zip (l :: accs'))) → res.2.2 = okb ∧
              Repr nm res.1.nodes.val res.2.1.val (encList (nm none)
                ((pushL ((c :: cs).zip ((k :: ks').zip (l :: accs'))) T).map
                  (askPat (nm none) U)))) ∧
            (¬ pushOK S ((c :: cs).zip ((k :: ks').zip (l :: accs'))) → res.2.2 = false) ⦄ := by
      intro s' todo' T' hI' hx' ht' rtd hT hhead
      have IH := ih ks' accs' T' s' todo' kt mt cti okb (by simpa using hl1) (by simpa using hl2)
        (fun d hd => hsub d (List.mem_cons_of_mem _ hd))
        (fun m hm => hnames m (List.mem_cons_of_mem _ hm))
        (fun d hd => hr d (List.mem_cons_of_mem _ hd)) hI' (hx'.repr hde) (hx'.repr hU) rtd
        (hx'.repr rkt) (hx'.repr rmt) (hx'.repr rct) (by unfold Room; omega)
      unfold sorts.push_asks_loop at IH
      refine WP.spec_mono IH ?_
      rintro res ⟨hI'', hx'', ht'', h1, h2⟩
      have hiff : pushOK S ((c :: cs).zip ((k :: ks').zip (l :: accs'))) ↔
          pushOK S (cs.zip (ks'.zip accs')) := by
        simp only [pushOK, List.zip_cons_cons, List.forall_mem_cons]
        exact ⟨fun h => h.2, fun h => ⟨hhead, h⟩⟩
      refine ⟨hI'', hx'.trans hx'', by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_, ?_⟩
      · intro hok
        obtain ⟨e1, e2⟩ := h1 (hiff.1 hok)
        refine ⟨e1, ?_⟩
        rw [List.zip_cons_cons, List.zip_cons_cons, pushL_cons, ← hT]
        exact e2
      · intro hno
        exact h2 fun h => hno (hiff.2 h)
    cases b with
    | true =>
      have hkn0 : k = none := hb.1 rfl
      simp only [uncurry, ↓reduceIte, bind_ok]
      refine next s4 todo T (R4.ranB.inv hI) R4.ext (by have := R4.ticks; omega)
        (R4.ext.repr htd) (by simp [hkn0, askOf]) (fun m hm => by rw [hkn0] at hm; cases hm)
    | false =>
      obtain ⟨m, rfl⟩ : ∃ m, k = some m := by
        cases k with
        | none => exact absurd (hb.2 rfl) (by simp)
        | some m => exact ⟨m, rfl⟩
      have hmn : m ∈ Sorts.names S := hnames m List.mem_cons_self
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
      step with is_nil_list hC.inj s4 acci hK4.wf (R4.ext.repr racc) (by unfold Room; omega)
        as ⟨r4, hb1, hK5⟩
      obtain ⟨b1, s5⟩ := r4
      simp only at hb1 hK5
      rw [List.map_eq_nil_iff] at hb1
      have ht5 := hK5.ticks
      have R5 := R4.trans hK5.ran
      have I5 : Inv s5 := R5.ranB.inv hI
      cases b1 with
      | true =>
        have hl0 : l = [] := hb1.1 rfl
        have hmono : inclCost S U.length (Sorts.reachGSet S (c, some m)).card ≤
            inclCost S U.length r := outCost_mono S U.length (hr c List.mem_cons_self m)
        simp only [uncurry, ↓reduceIte]
        step with included_spec hC c m (hsub c List.mem_cons_self) (hC.nz m hmn) s5 decls names
          ki mi I5 (R5.ext.repr hde) (R5.ext.repr hU) (R5.ext.repr rki) (R5.ext.repr rmi)
          (by unfold Room; omega) as ⟨r5, hI6, hx6, ht6, hb2⟩
        obtain ⟨b2, s6⟩ := r5
        simp only at hI6 hx6 ht6 hb2
        cases b2 with
        | true =>
          simp only [uncurry, ↓reduceIte, bind_ok]
          refine next s6 todo T hI6 (R5.ext.trans hx6) (by have := R5.ticks; omega)
            ((R5.ext.trans hx6).repr htd) (by simp [hl0, askOf])
            (fun m' hm' _ => by cases hm'; exact hb2.1 rfl)
        | false =>
          simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
          have hdn := push_asks_done s6 decls names todo kt mt cti false
          unfold sorts.push_asks_loop at hdn
          refine WP.spec_mono hdn ?_
          rintro res rfl
          have := R5.ticks
          refine ⟨hI6, R5.ext.trans hx6, by
            simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_, fun _ => rfl⟩
          intro hok
          have := hok (c, some m, l) (by simp) m rfl hl0
          exact absurd (hb2.2 this) (by simp)
      | false =>
        obtain ⟨a, l', rfl⟩ : ∃ a l', l = a :: l' := by
          cases l with
          | nil => exact absurd (hb1.2 rfl) (by simp)
          | cons a l' => exact ⟨a, l', rfl⟩
        simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
        have rm5 : Repr nm s5.nodes.val mi.val (.sym m) := R5.ext.repr rmi
        have ra5 := R5.ext.repr racc
        step with alloc_ran s5 (.App mi acci) hK5.wf ⟨rm5.lt, ra5.lt⟩ (by unfold Room; omega)
          as ⟨r5, hR6, hid6⟩
        obtain ⟨ri, s6⟩ := r5
        simp only at hR6 hid6
        have ht6 := hR6.ticks
        have rr : Repr nm s6.nodes.val ri.val
            (.app (.sym m) (accPat (nm none) (a :: l'))) :=
          .app hid6 (hR6.ext.repr rm5) (hR6.ext.repr ra5)
        have R6 := R5.trans hR6
        step with alloc_ran s6 (.App ki ri) hR6.wf ⟨(R6.ext.repr rki).lt, rr.lt⟩
          (by unfold Room; omega) as ⟨r6, hR7, hid7⟩
        obtain ⟨aski, s7⟩ := r6
        simp only at hR7 hid7
        have ht7 := hR7.ticks
        have rask : Repr nm s7.nodes.val aski.val (askPat (nm none) U (c, m, a :: l')) :=
          .app hid7 (hR7.ext.repr (R6.ext.repr rki)) (hR7.ext.repr rr)
        have R7 := R6.trans hR7
        step with alloc_ran s7 (.App aski todo) hR7.wf ⟨rask.lt, (R7.ext.repr htd).lt⟩
          (by unfold Room; omega) as ⟨r7, hR8, hid8⟩
        obtain ⟨todo1, s8⟩ := r7
        simp only at hR8 hid8
        have ht8 := hR8.ticks
        have R8 := R7.trans hR8
        simp only [uncurry, bind_ok]
        refine next s8 todo1 ((c, m, a :: l') :: T) (R8.ranB.inv hI) R8.ext
          (by have := R8.ticks; omega)
          (.app hid8 (hR8.ext.repr rask) (hR8.ext.repr (R7.ext.repr htd))) (by simp [askOf])
          (fun _ _ h => by cases h)

/-- `push_asks` puts what the arguments leave to ask in front, and gives
nothing when an argument that leaves no term is not in its sort. -/
theorem push_asks_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r : Nat}
    (cs : List Sorts.Conj) (ks : List (Option Name)) (accs : List (List GTerm)) (T : List Ask)
    (s : store.Store) (decls names kids kn ai todo : store.TermId)
    (hl1 : cs.length = ks.length) (hl2 : cs.length = accs.length) (hsub : ∀ c ∈ cs, Sub U c)
    (hnames : ∀ m, some m ∈ ks → m ∈ Sorts.names S)
    (hr : ∀ c ∈ cs, ∀ m, (Sorts.reachGSet S (c, some m)).card ≤ r) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (htd : Repr nm s.nodes.val todo.val (encList (nm none) (T.map (askPat (nm none) U))))
    (hk : Repr nm s.nodes.val kids.val (encList (nm none) (cs.map (cpat (nm none) U))))
    (hkn : Repr nm s.nodes.val kn.val (encList (nm none) (ks.map (kidPat (nm none)))))
    (hai : Repr nm s.nodes.val ai.val (encList (nm none) (accs.map (accPat (nm none)))))
    (hroom : Room s (cs.length * (inclCost S U.length r + 8) + 1)) :
    sorts.push_asks s decls names kids kn ai todo ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + (cs.length * (inclCost S U.length r + 8) + 1) ∧
        (pushOK S (cs.zip (ks.zip accs)) → ∃ td, o = some td ∧
          Repr nm s'.nodes.val td.val
            (encList (nm none) ((pushL (cs.zip (ks.zip accs)) T).map (askPat (nm none) U)))) ∧
        (¬ pushOK S (cs.zip (ks.zip accs)) → o = none) ⦄ := by
  unfold sorts.push_asks
  step with push_asks_loop_spec hC decls names cs ks accs T s todo kids kn ai true hl1 hl2 hsub
    hnames hr hI hde hU htd hk hkn hai hroom as ⟨s1, td, okb, hI1, hx1, ht1, h1, h2⟩
  by_cases hok : pushOK S (cs.zip (ks.zip accs))
  · obtain ⟨rfl, rtd⟩ := h1 hok
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨hI1, hx1, ht1, fun _ => ⟨td, rfl, rtd⟩, fun h => absurd hok h⟩
  · have := h2 hok
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨hI1, hx1, ht1, fun h => absurd h hok, fun _ => rfl⟩

/-! ## What one root leaves to ask -/

theorem length_projsL {sl : List (Option GTerm)} {f : Sym} {k : Nat} (hsl : sl.length = k) :
    ∀ (G : List GTerm) (A : List (List GTerm)), A.length = k → (projsL sl f k G A).length = k
  | [], _, h => h
  | t :: G, _, h => length_projsL hsl G _ (length_projStep hsl h t)

/-- The one member of each argument conjunction of a root, where there is
one and no more. -/
noncomputable def keySoles (S : Sorts) (c : Sorts.Conj) (key : Sym × Nat) : List (Option GTerm) :=
  (altOf S c key.1 key.2).map (oneOf S)

/-- For each argument of a root: its conjunction, the sort the sort gives it
and the terms left for it. -/
noncomputable def keyItems (S : Sorts) (c : Sorts.Conj) (G : List GTerm) (key : Sym × Nat)
    (kn : List (Option Name)) : List (Sorts.Conj × Option Name × List GTerm) :=
  (altOf S c key.1 key.2).zip
    (kn.zip (projsL (keySoles S c key) key.1 key.2 G (List.replicate key.2 [])))

open Classical in
/-- What a root leaves to ask, or nothing when the conjunction has a member
with the root that is outside the sort and not among the terms. -/
noncomputable def keyAsks (S : Sorts) (c : Sorts.Conj) (n : Name) (G : List GTerm)
    (key : Sym × Nat) : Option (List Ask) :=
  if Sorts.LiveKey S (Sorts.live S) c key then
    match Sorts.step S n key.1 key.2 with
    | none => if onlyInL (keySoles S c key) key.1 key.2 G = true then some [] else none
    | some kn =>
      if pushOK S (keyItems S c G key kn) then
        some ((keyItems S c G key kn).filterMap askOf).reverse
      else none
  else some []

/-- The ticks `but_key` may spend on a root with `k` arguments. -/
def butKeyCost (S : Sorts) (u r q k : Nat) (G : List GTerm) : Nat :=
  stepConjCost S u u k + solesCost S u r k + stepCost S k + onlyCost k G + projsAllCost k k G +
    (k * (inclCost S u q + 8) + 1)

/-- `but_key` puts what a root leaves to ask in front, or gives nothing. -/
theorem but_key_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (c : Sorts.Conj) (n : Name) (G : List GTerm) (f : Sym) (ksp : List Pat) (T : List Ask)
    (hc : Sub U c) (s : store.Store) (decls names ci ni g fi ks todo : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hni : Repr nm s.nodes.val ni.val (.sym n))
    (hg : Repr nm s.nodes.val g.val (encList (nm none) (G.map GTerm.toPat)))
    (hf : Repr nm s.nodes.val fi.val (.sym f))
    (hks : Repr nm s.nodes.val ks.val (encList (nm none) ksp))
    (htd : Repr nm s.nodes.val todo.val (encList (nm none) (T.map (askPat (nm none) U))))
    (hroom : Room s (butKeyCost S U.length r q ksp.length G)) :
    sorts.but_key s decls names ci ni g fi ks todo ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + butKeyCost S U.length r q ksp.length G ∧
        match keyAsks S c n G (f, ksp.length) with
        | some A => ∃ td, o = some td ∧
            Repr nm s'.nodes.val td.val (encList (nm none) ((A ++ T).map (askPat (nm none) U)))
        | none => o = none ⦄ := by
  unfold sorts.but_key
  have hroom' := hroom
  unfold Room at hroom'
  simp only [butKeyCost] at hroom'
  have hal : (altOf S c f ksp.length).length = ksp.length := by simp [altOf]
  have hsl : (keySoles S c (f, ksp.length)).length = ksp.length := by simp [keySoles, altOf]
  have hsub : ∀ d ∈ altOf S c f ksp.length, Sub U d := by
    intro d hd
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
    exact fun x hx => hC.names x (Sorts.kidC_subset_names hx)
  step with step_conj_conj_spec hC.inj S hC.sorts (f := f) (ag := ksp) U c s decls names ci fi ks
    hI hde hU hc hci hf hks (fun n _ ks' hs m' hm' => hC.nz m' (step_kid_names hs hm'))
    (by unfold Room; omega) as ⟨o, s1, hI1, hx1, htb1, ht1, hres⟩
  by_cases hacc : Sorts.Accepts S c f ksp.length
  swap
  · simp only [hacc, ↓reduceIte] at hres
    subst hres
    have hnl : ¬ Sorts.LiveKey S (Sorts.live S) c (f, ksp.length) := fun h => hacc h.1
    have hka : keyAsks S c n G (f, ksp.length) = some [] := by
      unfold keyAsks; rw [ite_neg' hnl]
    simp only [WP.spec_ok]
    rw [hka]
    exact ⟨hI1, hx1, by simp only [butKeyCost]; omega, todo, rfl, hx1.repr htd⟩
  simp only [hacc, ↓reduceIte] at hres
  obtain ⟨kidsi, kids, rfl, hkl, rkids, hk⟩ := hres
  have hkids : kids = (altOf S c f ksp.length).map (cpat (nm none) U) := by
    apply List.ext_getElem
    · simp [altOf, hkl]
    · intro i h₁ h₂
      obtain ⟨k', rk', ck'⟩ := hk i h₁
      simp only [altOf, List.getElem_map, List.getElem_range]
      exact rk'.unique ck'
  subst hkids
  simp only
  step with soles_spec hC (altOf S c f ksp.length) hsub (fun d _ => hr d) s1 decls names kidsi
    hI1 (hx1.repr hde) (hx1.repr hU) rkids (by rw [hal]; unfold Room; omega)
    as ⟨o1, s2, hI2, hx2, ht2, hso1, hso2⟩
  rw [hal] at ht2
  have hx12 := hx1.trans hx2
  by_cases hall : ∀ d ∈ altOf S c f ksp.length, Sorts.count S d ≠ .none
  swap
  · obtain ⟨d, hd, hdn⟩ : ∃ d ∈ altOf S c f ksp.length, Sorts.count S d = .none := by
      by_contra h0
      exact hall fun d hd hdn => h0 ⟨d, hd, hdn⟩
    have := hso2 d hd hdn
    subst this
    have hnl : ¬ Sorts.LiveKey S (Sorts.live S) c (f, ksp.length) := by
      intro h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
      exact Sorts.count_none.1 hdn (Sorts.mem_live_iff.1 (h.2 i (List.mem_range.1 hi)))
    have hka : keyAsks S c n G (f, ksp.length) = some [] := by
      unfold keyAsks; rw [ite_neg' hnl]
    simp only [WP.spec_ok]
    rw [hka]
    exact ⟨hI2, hx12, by simp only [butKeyCost]; omega, todo, rfl, hx12.repr htd⟩
  obtain ⟨so, rfl, rso⟩ := hso1 hall
  have hlive : Sorts.LiveKey S (Sorts.live S) c (f, ksp.length) := by
    refine ⟨hacc, fun i hi => ?_⟩
    by_contra hn
    exact hall _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
      (Sorts.count_none.2 fun h => hn (Sorts.mem_live_iff.2 h))
  have rso' : Repr nm s2.nodes.val so.val
      (encList (nm none) ((keySoles S c (f, ksp.length)).map (solePat (nm none)))) := by
    rw [keySoles, List.map_map]; exact rso
  simp only
  step with step_spec hC.inj S hC.sorts s2 decls ni fi ks hI2.toWf (hx12.repr hde)
    (hx12.repr hni) (hx12.repr hf) (hx12.repr hks) (by unfold Room; omega)
    as ⟨o2, s3, hR3, hst⟩
  have ht3 := hR3.ticks
  have hI3 : Inv s3 := hR3.ranB.inv hI2
  have hx3 := hx12.trans hR3.ext
  cases hs : Sorts.step S n f ksp.length with
  | none =>
    rw [hs] at hst
    subst hst
    simp only
    step with only_in_spec hC.inj (keySoles S c (f, ksp.length)) f ksp hsl G s3 so fi ks g
      hR3.wf (hR3.ext.repr rso') (hx3.repr hf) (hx3.repr hks) (hx3.repr hg)
      (by rw [hsl]; unfold Room; omega) as ⟨b, s4, hR4, hb⟩
    rw [hsl] at hR4
    have ht4 := hR4.ticks
    have hka : keyAsks S c n G (f, ksp.length) =
        if onlyInL (keySoles S c (f, ksp.length)) f ksp.length G = true then some [] else none := by
      unfold keyAsks; rw [ite_pos' hlive]; simp only [hs]
    rw [hka, ← hb]
    cases b with
    | true =>
      simp only [↓reduceIte, WP.spec_ok]
      exact ⟨hR4.ranB.inv hI3, hx3.trans hR4.ext, by simp only [butKeyCost]; omega, todo, rfl,
        (hx3.trans hR4.ext).repr htd⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨hR4.ranB.inv hI3, hx3.trans hR4.ext, by simp only [butKeyCost]; omega, rfl⟩
  | some kn =>
    rw [hs] at hst
    obtain ⟨kni, rfl, rkn⟩ := hst
    have hknl : kn.length = ksp.length := Sorts.step_length hs
    simp only
    step with projs_spec hC.inj (keySoles S c (f, ksp.length)) f ksp hsl G s3 so fi ks g hR3.wf
      (hR3.ext.repr rso') (hx3.repr hf) (hx3.repr hks) (hx3.repr hg)
      (by rw [hsl]; unfold Room; omega) as ⟨accs, s4, hR4, racc⟩
    rw [hsl] at hR4
    have ht4 := hR4.ticks
    have hx4 := hx3.trans hR4.ext
    have hpl : (projsL (keySoles S c (f, ksp.length)) f ksp.length G
        (List.replicate ksp.length [])).length = ksp.length :=
      length_projsL hsl G _ (List.length_replicate ..)
    refine WP.spec_mono (push_asks_spec hC (altOf S c f ksp.length) kn _ T s4 decls names kidsi
      kni accs todo (by rw [hal, hknl]) (by rw [hal, hpl]) hsub
      (fun m hm => step_kid_names hs hm) (fun d _ m => hq d m) (hR4.ranB.inv hI3)
      (hx4.repr hde) (hx4.repr hU) (hx4.repr htd) ((hx2.trans (hR3.ext.trans hR4.ext)).repr rkids)
      (hR4.ext.repr rkn) racc (by rw [hal]; unfold Room; omega)) ?_
    rintro ⟨o, s'⟩ ⟨hI', hx', ht', h1, h2⟩
    rw [hal] at ht'
    refine ⟨hI', hx4.trans hx', by simp only [butKeyCost]; omega, ?_⟩
    by_cases hok : pushOK S (keyItems S c G (f, ksp.length) kn)
    · obtain ⟨td, rfl, rtd⟩ := h1 hok
      have hka : keyAsks S c n G (f, ksp.length) =
          some ((keyItems S c G (f, ksp.length) kn).filterMap askOf).reverse := by
        unfold keyAsks; rw [ite_pos' hlive]; simp only [hs, hok, ↓reduceIte]
      rw [hka]
      exact ⟨td, rfl, rtd⟩
    · have hka : keyAsks S c n G (f, ksp.length) = none := by
        unfold keyAsks; rw [ite_pos' hlive]; simp only [hs, hok, ↓reduceIte]
      rw [hka]
      exact h2 hok

end RwLogVerified
