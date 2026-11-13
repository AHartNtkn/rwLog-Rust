import RwLogVerified.Store
import RwLogVerified.Repr

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core

variable {nm : Nat → RwLog.Sym}


/-- What a node read at an identifier says about the term the identifier
stands for. -/
def NodeRepr (nm : Nat → RwLog.Sym) (nodes : List store.Node) : store.Node → RwLog.Pat → Prop
  | .Var x, .var v => v = x.val
  | .Sym f, .sym g => g = nm f.val
  | .App a b, .app ta tb => Repr nm nodes a.val ta ∧ Repr nm nodes b.val tb
  | _, _ => False

theorem Repr.node {nodes : List store.Node} {i : Nat} {t : RwLog.Pat} (h : Repr nm nodes i t) :
    NodeRepr nm nodes (nodes[i]'h.lt) t := by
  cases h with
  | var hx => obtain ⟨_, hx⟩ := List.getElem?_eq_some_iff.1 hx; simp [hx, NodeRepr]
  | sym hf => obtain ⟨_, hf⟩ := List.getElem?_eq_some_iff.1 hf; simp [hf, NodeRepr]
  | app hn ha hb => obtain ⟨_, hn⟩ := List.getElem?_eq_some_iff.1 hn; simp [hn, NodeRepr, ha, hb]

/-- Reading an identifier that stands for a term. -/
theorem read_repr (s : store.Store) (i : store.TermId) {t : RwLog.Pat}
    (hi : Repr nm s.nodes.val i.val t) (h : s.ticks.val < U64.max) :
    store.Store.read s i ⦃ n s' =>
      NodeRepr nm s.nodes.val n t ∧ s'.nodes = s.nodes ∧ s'.ticks.val = s.ticks.val + 1 ⦄ := by
  have := hi.lt
  step with read_spec as ⟨n, s', hn, hs, ht⟩
  exact ⟨hn ▸ hi.node, hs, ht⟩

/-- `term_eq` decides equality of the terms the two identifiers stand for,
and spends at most three ticks for each node of the second. -/
theorem term_eq_spec (hnm : Function.Injective nm) (s : store.Store) (a b : store.TermId)
    {ta tb : RwLog.Pat} (ha : Repr nm s.nodes.val a.val ta) (hb : Repr nm s.nodes.val b.val tb)
    (hroom : s.ticks.val + 3 * tb.size ≤ U64.max) :
    matching.term_eq s a b ⦃ r s' =>
      r = decide (ta = tb) ∧ s'.nodes = s.nodes ∧ s'.ticks.val ≤ s.ticks.val + 3 * tb.size ⦄ := by
  induction hsize : ta.size using Nat.strong_induction_on generalizing s a b ta tb with
  | _ k ih => ?_
  unfold matching.term_eq
  have hsz := RwLog.Term.size_pos tb
  step with read_repr s a ha as ⟨n, s1, hn, hs1, ht1⟩
  step with read_repr s1 b (hs1 ▸ hb) as ⟨n1, s2, hn1, hs2, ht2⟩
  rw [hs1] at hn1
  cases n <;> cases n1 <;> cases ta <;> cases tb <;> simp only [NodeRepr] at hn hn1
  case Var.Var.var.var =>
    rename_i x y v w
    dsimp only
    step as ⟨r, s3, hr, hs3, ht3⟩
    simp only [RwLog.Term.size] at hroom ⊢
    refine ⟨?_, by simp [*], by omega⟩
    simp [hr, hn, hn1, UScalar.eq_equiv]
  case Sym.Sym.sym.sym =>
    rename_i f g v w
    dsimp only
    step as ⟨r, s3, hr, hs3, ht3⟩
    simp only [RwLog.Term.size] at hroom ⊢
    refine ⟨?_, by simp [*], by omega⟩
    simp [hr, hn, hn1, hnm.eq_iff, UScalar.eq_equiv]
  case App.App.app.app =>
    rename_i a1 a2 b1 b2 ta1 ta2 tb1 tb2
    dsimp only
    simp only [RwLog.Term.size] at hroom hsize ⊢
    step with ih ta1.size (by omega) s2 a1 b1 (ta := ta1) (tb := tb1) (by rw [hs2, hs1]; exact hn.1)
      (by rw [hs2, hs1]; exact hn1.1) (by omega) rfl as ⟨r1, s3, hr1, hs3, ht3⟩
    by_cases h1 : ta1 = tb1
    · simp only [hr1, h1, decide_true, ↓reduceIte]
      step with ih ta2.size (by omega) s3 a2 b2 (ta := ta2) (tb := tb2) (by rw [hs3, hs2, hs1]; exact hn.2)
        (by rw [hs3, hs2, hs1]; exact hn1.2) (by omega) rfl as ⟨r2, s4, hr2, hs4, ht4⟩
      refine ⟨by simp [hr2], by simp [*], by omega⟩
    · simp only [hr1, h1, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine (WP.spec_ok _).2 ⟨by simp [h1], by simp [*], by omega⟩
  all_goals
    dsimp only
    simp only [RwLog.Term.size] at hroom ⊢
    refine (WP.spec_ok _).2 ⟨by simp, by simp [*], by omega⟩

/-! ## Substitutions -/

/-- The newest binding of `v` in a list of bindings, oldest first. -/
def lookupL (bs : List (U32 × store.TermId)) (v : U32) : Option store.TermId :=
  bs.reverse.lookup v

theorem lookupL_take_succ (bs : List (U32 × store.TermId)) (v : U32) (j : Nat) (hj : j < bs.length) :
    lookupL (bs.take (j + 1)) v = if bs[j].1 = v then some bs[j].2 else lookupL (bs.take j) v := by
  simp only [lookupL, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  rw [show bs[j] = (bs[j].1, bs[j].2) from rfl, List.lookup_cons]
  by_cases h : bs[j].1 = v
  · simp [h]
  · have : (v == bs[j].1) = false := by
      rw [beq_eq_false_iff_ne]; exact fun e => h e.symm
    simp [h, this]

theorem lookup_loop_spec (bs : alloc.vec.Vec (U32 × store.TermId)) (s : store.Store) (v : U32)
    (i : Usize) (hi : i.val ≤ bs.length) (hroom : s.ticks.val + i.val ≤ U64.max) :
    matching.Subst.lookup_loop bs s v i ⦃ o s' =>
      o = lookupL (bs.val.take i.val) v ∧ s'.nodes = s.nodes ∧
        s'.ticks.val ≤ s.ticks.val + i.val ⦄ := by
  unfold matching.Subst.lookup_loop
  apply loop.spec_decr_nat (measure := fun p => p.2.val)
    (inv := fun p => p.2.val ≤ i.val ∧ p.1.nodes = s.nodes ∧
      p.1.ticks.val + p.2.val ≤ s.ticks.val + i.val ∧
      lookupL (bs.val.take i.val) v = lookupL (bs.val.take p.2.val) v)
  · rintro ⟨s1, i1⟩ ⟨h1, h2, h3, h4⟩
    unfold matching.Subst.lookup_loop.body
    dsimp only at h1 h2 h3 h4 ⊢
    split
    · rename_i hpos
      step as ⟨i2, hi2⟩
      step as ⟨w, t, hwt⟩
      step as ⟨b, s2, hb, hs2, ht2⟩
      have hi2' : i1.val = i2.val + 1 := by scalar_tac
      have hlt : i2.val < bs.val.length := by
        have : bs.length = bs.val.length := rfl
        omega
      have hstep := lookupL_take_succ bs.val v i2.val hlt
      rw [← hi2'] at hstep
      by_cases hw : w = v
      · subst hw
        simp only [hb, decide_true, ↓reduceIte]
        refine (WP.spec_ok _).2 ?_
        dsimp only
        refine ⟨?_, by simp [*], by omega⟩
        rw [h4, hstep, ← hwt]; simp
      · simp only [hb, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine (WP.spec_ok _).2 ?_
        dsimp only
        refine ⟨by omega, by simp [*], by omega, ?_, by omega⟩
        rw [h4, hstep, ← hwt]; simp [hw]
    · rename_i hpos
      have h0 : i1.val = 0 := by scalar_tac
      refine (WP.spec_ok _).2 ⟨?_, h2, by omega⟩
      rw [h4, h0]; rfl
  · exact ⟨le_refl _, rfl, le_refl _, rfl⟩

@[step]
theorem lookup_spec (th : matching.Subst) (s : store.Store) (v : U32)
    (hroom : s.ticks.val + th.binds.val.length ≤ U64.max) :
    matching.Subst.lookup th s v ⦃ o s' =>
      o = lookupL th.binds.val v ∧ s'.nodes = s.nodes ∧
        s'.ticks.val ≤ s.ticks.val + th.binds.val.length ⦄ := by
  unfold matching.Subst.lookup
  have hlen : (alloc.vec.Vec.len th.binds).val = th.binds.val.length := by simp
  step with lookup_loop_spec th.binds s v (alloc.vec.Vec.len th.binds)
    (le_of_eq hlen) (by omega) as ⟨o, s', ho, hs, ht⟩
  refine ⟨?_, hs, by omega⟩
  rw [ho, hlen, List.take_length]

@[step]
theorem bind_spec (th : matching.Subst) (v : U32) (t : store.TermId)
    (h : th.binds.val.length < Usize.max) :
    matching.Subst.bind th v t ⦃ th' => th'.binds.val = th.binds.val ++ [(v, t)] ⦄ := by
  unfold matching.Subst.bind
  step*

/-- The specification's substitution that a list of Rust bindings stands
for. The Rust list has the oldest binding first, the specification's the
newest. -/
def SubstRepr (nm : Nat → RwLog.Sym) (nodes : List store.Node) (bs : List (U32 × store.TermId))
    (θ : RwLog.PSubst) : Prop :=
  List.Forall₂ (fun b e => e.1 = b.1.val ∧ Repr nm nodes b.2.val e.2) bs.reverse θ

variable {nodes : List store.Node}

theorem SubstRepr.length {bs : List (U32 × store.TermId)} {θ : RwLog.PSubst}
    (h : SubstRepr nm nodes bs θ) : θ.length = bs.length := by
  simpa using h.length_eq.symm

theorem SubstRepr.bind {bs : List (U32 × store.TermId)} {θ : RwLog.PSubst}
    (h : SubstRepr nm nodes bs θ) (v : U32) {t : store.TermId} {tt : RwLog.Pat}
    (ht : Repr nm nodes t.val tt) : SubstRepr nm nodes (bs ++ [(v, t)]) ((v.val, tt) :: θ) := by
  unfold SubstRepr
  rw [List.reverse_append]
  exact .cons ⟨rfl, ht⟩ h

theorem forall₂_lookup {l : List (U32 × store.TermId)} {θ : RwLog.PSubst}
    (h : List.Forall₂ (fun b e => e.1 = b.1.val ∧ Repr nm nodes b.2.val e.2) l θ) (v : U32) :
    (l.lookup v = none → θ.lookup v.val = none) ∧
      ∀ u, l.lookup v = some u → ∃ t, θ.lookup v.val = some t ∧ Repr nm nodes u.val t := by
  induction h with
  | nil => simp
  | @cons b e l θ hbe _ ih =>
    obtain ⟨w, u⟩ := b
    obtain ⟨k, t⟩ := e
    obtain ⟨hk, hr⟩ := hbe
    dsimp only at hk hr
    subst hk
    rw [List.lookup_cons, List.lookup_cons]
    by_cases hv : v = w
    · subst hv; simp [hr]
    · have h1 : (v == w) = false := by rw [beq_eq_false_iff_ne]; exact hv
      have h2 : (v.val == w.val) = false := by
        rw [beq_eq_false_iff_ne]; exact fun e => hv ((UScalar.eq_equiv _ _).2 e)
      simp only [h1, h2]; exact ih

theorem SubstRepr.lookup {bs : List (U32 × store.TermId)} {θ : RwLog.PSubst}
    (h : SubstRepr nm nodes bs θ) (v : U32) :
    (lookupL bs v = none → θ.lookup v.val = none) ∧
      ∀ u, lookupL bs v = some u → ∃ t, θ.lookup v.val = some t ∧ Repr nm nodes u.val t :=
  forall₂_lookup h v

end RwLogVerified
