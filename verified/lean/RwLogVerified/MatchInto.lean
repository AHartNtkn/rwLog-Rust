/-
# The Rust `match_into` computes the specification's `matchInto`, within a
stated number of ticks
-/
import RwLogVerified.Matching

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core

variable {nm : Nat → RwLog.Sym} {nodes : List store.Node}

/-- The Rust result stands for the specification's result, and binds at most
`n` more variables than `θ`. -/
def MatchRes (nm : Nat → RwLog.Sym) (nodes : List store.Node) (θ : RwLog.PSubst) (n : Nat) :
    Option matching.Subst → Option RwLog.PSubst → Prop
  | none, none => True
  | some th', some θ' => SubstRepr nm nodes th'.binds.val θ' ∧ θ'.length ≤ θ.length + n
  | _, _ => False

theorem MatchRes.mono {θ θ₁ : RwLog.PSubst} {n n₁ : Nat} {r : Option matching.Subst}
    {m : Option RwLog.PSubst} (h : MatchRes nm nodes θ₁ n₁ r m)
    (hle : θ₁.length + n₁ ≤ θ.length + n) : MatchRes nm nodes θ n r m := by
  cases r <;> cases m <;> simp only [MatchRes] at h ⊢
  exact ⟨h.1, by omega⟩

theorem match_into_spec (hnm : Function.Injective nm) (s : store.Store) (p t : store.TermId)
    (th : matching.Subst) {tp tt : RwLog.Pat} {θ : RwLog.PSubst}
    (hp : Repr nm s.nodes.val p.val tp) (ht : Repr nm s.nodes.val t.val tt)
    (hθ : SubstRepr nm s.nodes.val th.binds.val θ)
    (L : Nat) (hL : θ.length + tp.size ≤ L) (hLmax : L ≤ Usize.max)
    (hroom : s.ticks.val + tp.size * (3 + L) + 3 * tt.size ≤ U64.max) :
    matching.match_into s p t th ⦃ r s' =>
      s'.nodes = s.nodes ∧
      s'.ticks.val ≤ s.ticks.val + tp.size * (3 + L) + 3 * tt.size ∧
      MatchRes nm s.nodes.val θ tp.size r (RwLog.matchInto tp tt θ) ⦄ := by
  induction hsize : tp.size using Nat.strong_induction_on generalizing s p t th tp tt θ with
  | _ k ih => ?_
  subst hsize
  unfold matching.match_into
  have hszt := RwLog.Term.size_pos tt
  have hszp := RwLog.Term.size_pos tp
  have hlen := hθ.length
  have hmul : tp.size * (3 + L) ≥ 3 + L := Nat.le_mul_of_pos_left _ hszp
  step with read_repr s p hp as ⟨n, s1, hn, hs1, ht1⟩
  cases n <;> cases tp <;> simp only [NodeRepr] at hn
  case Var.var =>
    rename_i x v
    subst hn
    dsimp only
    step as ⟨o, s2, ho, hs2, ht2⟩
    obtain ⟨hnone, hsome⟩ := hθ.lookup x
    cases hlk : lookupL th.binds.val x with
    | none =>
      rw [hlk] at ho; subst ho
      dsimp only
      step as ⟨th', hth'⟩
      simp only [RwLog.Term.size, Nat.one_mul] at hroom hL ⊢
      refine ⟨by simp [*], by omega, ?_⟩
      simp only [RwLog.matchInto, hnone hlk, MatchRes]
      exact ⟨hth' ▸ hθ.bind x ht, by simp⟩
    | some u =>
      rw [hlk] at ho; subst ho
      obtain ⟨tu, htu, hru⟩ := hsome u hlk
      dsimp only
      simp only [RwLog.Term.size, Nat.one_mul] at hroom hL ⊢
      step with term_eq_spec hnm s2 u t (ta := tu) (tb := tt) (by rw [hs2, hs1]; exact hru)
        (by rw [hs2, hs1]; exact ht) (by omega) as ⟨b, s3, hb, hs3, ht3⟩
      by_cases he : tu = tt
      · simp only [hb, he, decide_true, ↓reduceIte]
        refine (WP.spec_ok _).2 ?_
        refine ⟨by simp [*], by omega, ?_⟩
        simp only [RwLog.matchInto, htu, he, ↓reduceIte, MatchRes]
        exact ⟨hθ, by omega⟩
      · simp only [hb, he, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine (WP.spec_ok _).2 ?_
        refine ⟨by simp [*], by omega, ?_⟩
        simp only [RwLog.matchInto, htu, he, ↓reduceIte, MatchRes]
  case Sym.sym =>
    rename_i f g
    subst hn
    dsimp only
    simp only [RwLog.Term.size, Nat.one_mul] at hroom hL ⊢
    step with read_repr s1 t (hs1 ▸ ht) as ⟨n1, s2, hn1, hs2, ht2⟩
    rw [hs1] at hn1
    cases n1 <;> cases tt <;> simp only [NodeRepr] at hn1
    case Sym.sym =>
      rename_i f' g'
      subst hn1
      dsimp only
      step as ⟨b, s3, hb, hs3, ht3⟩
      by_cases he : f = f'
      · subst he
        simp only [hb, decide_true, ↓reduceIte]
        refine (WP.spec_ok _).2 ?_
        simp only [RwLog.Term.size] at hroom ⊢
        refine ⟨by simp [*], by omega, ?_⟩
        simp only [RwLog.matchInto, ↓reduceIte, MatchRes]
        exact ⟨hθ, by omega⟩
      · simp only [hb, he, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine (WP.spec_ok _).2 ?_
        simp only [RwLog.Term.size] at hroom ⊢
        refine ⟨by simp [*], by omega, ?_⟩
        have : nm f.val ≠ nm f'.val := fun e => he ((UScalar.eq_equiv _ _).2 (hnm e))
        simp only [RwLog.matchInto, this, ↓reduceIte, MatchRes]
    all_goals
      dsimp only
      refine (WP.spec_ok _).2 ?_
      simp only [RwLog.Term.size] at hroom ⊢
      refine ⟨by simp [*], by omega, ?_⟩
      simp only [RwLog.matchInto, MatchRes]
  case App.app =>
    rename_i p1 p2 tp1 tp2
    obtain ⟨hp1, hp2⟩ := hn
    dsimp only
    simp only [RwLog.Term.size, Nat.add_mul, Nat.one_mul] at hroom hL ih ⊢
    step with read_repr s1 t (hs1 ▸ ht) as ⟨n1, s2, hn1, hs2, ht2⟩
    rw [hs1] at hn1
    cases n1 <;> cases tt <;> simp only [NodeRepr] at hn1
    case App.app =>
      rename_i t1 t2 tt1 tt2
      obtain ⟨hr1, hr2⟩ := hn1
      dsimp only
      simp only [RwLog.Term.size] at hroom ⊢
      step with ih tp1.size (by omega) s2 p1 t1 th (tp := tp1) (tt := tt1) (θ := θ)
        (by rw [hs2, hs1]; exact hp1) (by rw [hs2, hs1]; exact hr1) (by rw [hs2, hs1]; exact hθ)
        (by omega) (by omega) rfl as ⟨o, s3, hs3, ht3, hres⟩
      rw [hs2, hs1] at hres
      cases hm : RwLog.matchInto tp1 tt1 θ with
      | none =>
        cases o <;> simp only [hm, MatchRes] at hres
        dsimp only
        refine (WP.spec_ok _).2 ?_
        refine ⟨by simp [*], by omega, ?_⟩
        simp only [RwLog.matchInto, hm, Option.bind_none, MatchRes]
      | some θ1 =>
        cases o <;> simp only [hm, MatchRes] at hres
        rename_i th1
        obtain ⟨hθ1, hl1⟩ := hres
        dsimp only
        step with ih tp2.size (by omega) s3 p2 t2 th1 (tp := tp2) (tt := tt2) (θ := θ1)
          (by rw [hs3, hs2, hs1]; exact hp2) (by rw [hs3, hs2, hs1]; exact hr2)
          (by rw [hs3, hs2, hs1]; exact hθ1) (by omega) (by omega) rfl as ⟨r, s4, hs4, ht4, hres2⟩
        rw [hs3, hs2, hs1] at hres2
        refine ⟨by simp [*], by omega, ?_⟩
        simp only [RwLog.matchInto, hm, Option.bind_some]
        exact hres2.mono (by omega)
    all_goals
      dsimp only
      refine (WP.spec_ok _).2 ?_
      simp only [RwLog.Term.size] at hroom ⊢
      refine ⟨by simp [*], by omega, ?_⟩
      simp only [RwLog.matchInto, MatchRes]

/-- Matching from the empty substitution. The cost is quadratic in the
pattern because a substitution is a list searched by charged comparisons;
the specification charges a match the sizes of the two terms
(`Trusted/Charged.lean`), which needs a substitution indexed by variable. -/
theorem match_into_empty_spec (hnm : Function.Injective nm) (s : store.Store) (p t : store.TermId)
    (th : matching.Subst) (hth : th.binds.val = []) {tp tt : RwLog.Pat}
    (hp : Repr nm s.nodes.val p.val tp) (ht : Repr nm s.nodes.val t.val tt)
    (hsize : tp.size ≤ Usize.max)
    (hroom : s.ticks.val + tp.size * (3 + tp.size) + 3 * tt.size ≤ U64.max) :
    matching.match_into s p t th ⦃ r s' =>
      s'.nodes = s.nodes ∧
      s'.ticks.val ≤ s.ticks.val + tp.size * (3 + tp.size) + 3 * tt.size ∧
      match r, RwLog.matchInto tp tt [] with
      | none, none => True
      | some th', some θ' => SubstRepr nm s.nodes.val th'.binds.val θ'
      | _, _ => False ⦄ := by
  have hθ : SubstRepr nm s.nodes.val th.binds.val [] := by rw [hth]; exact .nil
  step with match_into_spec hnm s p t th hp ht hθ tp.size (by simp) hsize hroom
    as ⟨r, s', hs, ht', hres⟩
  refine ⟨hs, ht', ?_⟩
  cases r <;> cases hm : RwLog.matchInto tp tt [] <;> simp only [hm, MatchRes] at hres ⊢
  exact hres.1

end RwLogVerified
