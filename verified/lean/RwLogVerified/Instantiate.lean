/-
# The Rust `instantiate` computes the specification's `Term.bind`, within a
stated number of ticks, and only appends to the store
-/
import RwLogVerified.Matching

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core

variable {nm : Nat → RwLog.Sym} {nodes : List store.Node}

theorem SubstRepr.append {bs : List (U32 × store.TermId)} {θ : RwLog.PSubst}
    (h : SubstRepr nm nodes bs θ) (more : List store.Node) :
    SubstRepr nm (nodes ++ more) bs θ :=
  List.Forall₂.imp (fun _ _ hbe => ⟨hbe.1, hbe.2.append more⟩) h

theorem instantiate_spec (s : store.Store) (th : matching.Subst) (t : store.TermId)
    {tt : RwLog.Pat} {θ : RwLog.PSubst}
    (ht : Repr nm s.nodes.val t.val tt) (hθ : SubstRepr nm s.nodes.val th.binds.val θ)
    (hroom : s.ticks.val + tt.size * (2 + θ.length) ≤ U64.max)
    (hspace : s.nodes.val.length + tt.size ≤ Usize.max) :
    matching.instantiate s th t ⦃ r s' =>
      (∃ more, s'.nodes.val = s.nodes.val ++ more ∧ more.length ≤ tt.size) ∧
      Repr nm s'.nodes.val r.val (tt.bind (RwLog.PSubst.apply θ)) ∧
      s'.ticks.val ≤ s.ticks.val + tt.size * (2 + θ.length) ⦄ := by
  induction hsize : tt.size using Nat.strong_induction_on generalizing s t tt with
  | _ k ih => ?_
  subst hsize
  unfold matching.instantiate
  have hlen := hθ.length
  have hsz := RwLog.Term.size_pos tt
  have hmul : tt.size * (2 + θ.length) ≥ 2 + θ.length := Nat.le_mul_of_pos_left _ hsz
  step with read_repr s t ht (by omega) as ⟨n, s1, hn, hs1, ht1⟩
  cases n <;> cases tt <;> simp only [NodeRepr] at hn
  case Var.var =>
    rename_i x v
    subst hn
    dsimp only
    simp only [RwLog.Term.size, Nat.one_mul] at hroom hspace ⊢
    step as ⟨o, s2, ho, hs2, ht2⟩
    obtain ⟨hnone, hsome⟩ := hθ.lookup x
    cases hlk : lookupL th.binds.val x with
    | none =>
      rw [hlk] at ho; subst ho
      dsimp only
      refine (WP.spec_ok _).2 ⟨⟨[], by simp [*], by simp⟩, ?_, by omega⟩
      simp only [RwLog.Term.bind, RwLog.PSubst.apply, hnone hlk, Option.getD_none]
      rw [hs2, hs1]; exact ht
    | some u =>
      rw [hlk] at ho; subst ho
      obtain ⟨tu, htu, hru⟩ := hsome u hlk
      dsimp only
      refine (WP.spec_ok _).2 ⟨⟨[], by simp [*], by simp⟩, ?_, by omega⟩
      simp only [RwLog.Term.bind, RwLog.PSubst.apply, htu, Option.getD_some]
      rw [hs2, hs1]; exact hru
  case Sym.sym =>
    rename_i f g
    subst hn
    dsimp only
    simp only [RwLog.Term.size, Nat.one_mul] at hroom hspace ⊢
    refine (WP.spec_ok _).2 ⟨⟨[], by simp [*], by simp⟩, ?_, by omega⟩
    simp only [RwLog.Term.bind]
    rw [hs1]; exact ht
  case App.app =>
    rename_i a b ta tb
    obtain ⟨hra, hrb⟩ := hn
    dsimp only
    simp only [RwLog.Term.size, Nat.add_mul, Nat.one_mul] at hroom hspace ih ⊢
    step with ih ta.size (by omega) s1 a (tt := ta) (by rw [hs1]; exact hra) (by rw [hs1]; exact hθ)
      (by omega) (by rw [hs1]; omega) rfl as ⟨a2, s2, more1, hm1, hml1, hr2, ht2⟩
    rw [hs1] at hm1
    step with ih tb.size (by omega) s2 b (tt := tb) (by rw [hm1]; exact hrb.append more1)
      (by rw [hm1]; exact hθ.append more1) (by omega) (by rw [hm1]; simp; omega) rfl
      as ⟨b2, s3, more2, hm2, hml2, hr3, ht3⟩
    have hr2' : Repr nm s3.nodes.val a2.val (ta.bind (RwLog.PSubst.apply θ)) := by
      rw [hm2]; exact hr2.append more2
    step with alloc_spec s3 (.App a2 b2) (by omega) (by rw [hm2, hm1]; simp; omega)
      ⟨hr2'.lt, hr3.lt⟩ as ⟨id, s4, hid, hs4, ht4⟩
    refine ⟨⟨more1 ++ more2 ++ [.App a2 b2], by simp [hs4, hm2, hm1], by simp; omega⟩, ?_, by omega⟩
    simp only [RwLog.Term.bind]
    rw [hs4]
    exact .app (by rw [hid]; simp) (hr2'.append _) (hr3.append _)

end RwLogVerified
