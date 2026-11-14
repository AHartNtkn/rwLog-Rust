/-
# The outermost free subterms of a pattern

`sorts::free_subterms` goes through the pattern of a store from the root and
asks of each subterm it reaches whether it is free (`sorts::free`). A free
subterm gets the next variable, and an entry that gives that variable the
sorts of the subterm; the arguments of a subterm that is not free are gone
through in turn. It keeps the list of the subterms it has asked about, so a
subterm that occurs many times is asked about once.
-/
import RwLogVerified.Free
import RwLogVerified.Among

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-- The free subterms found, newest first, each with its variable: the
variables count up from `N` in the order the subterms were found. -/
def fpairs (N : Nat) : List Pat → List (Pat × Nat)
  | [] => []
  | u :: Fl => (u, N + Fl.length) :: fpairs N Fl

theorem mem_fpairs {N : Nat} : ∀ {Fl : List Pat} {p : Pat × Nat},
    p ∈ fpairs N Fl → p.1 ∈ Fl ∧ N ≤ p.2 ∧ p.2 < N + Fl.length
  | [], _, h => by cases h
  | u :: Fl, p, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨List.mem_cons_self, by simp, by simp⟩
    · obtain ⟨h1, h2, h3⟩ := mem_fpairs h
      exact ⟨List.mem_cons_of_mem _ h1, h2, by simp only [List.length_cons]; omega⟩

/-- The list of the free subterms found with their variables, as a term. -/
def foundPat (z : Sym) (N : Nat) (Fl : List Pat) : Pat :=
  encList z ((fpairs N Fl).map fun p => .app p.1 (.var p.2))

/-- The entries of the variables of the free subterms found, before the
entries given. -/
noncomputable def foundEntries (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj))
    (N : Nat) (Fl : List Pat) : List (Nat × Sorts.Conj) :=
  ((fpairs N Fl).map fun p => (p.2, cloOf S U L p.1)) ++ L

/-- What holds of the subterms still to ask about, `T`, the subterms asked
about, `Sn`, and the free ones found, `Fl`. The ones found are the free ones
asked about, and the arguments of one asked about that is not a variable and
not free have been asked about or are still to ask about. -/
structure SGo (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj)) (XV : List Nat)
    (tp : Pat) (T Sn Fl : List Pat) : Prop where
  sub : ∀ x ∈ T ++ Sn, x ∈ tp.subs ∧ x.firstOrder = true
  nd : Sn.Nodup
  fnd : Fl.Nodup
  fl : Fl.length ≤ Sn.length
  found : ∀ u ∈ Fl, u ∈ Sn ∧ FreeAt S U L XV tp u
  free : ∀ u ∈ Sn, FreeAt S U L XV tp u → u ∈ Fl
  kids : ∀ u ∈ Sn, (∀ v, u ≠ .var v) → u ∉ Fl → ∀ a ∈ (unspine u []).2, a ∈ Sn ∨ a ∈ T
  root : tp ∈ Sn ∨ tp ∈ T

section go

variable {S : Sorts} {U : List Name} {L : List (Nat × Sorts.Conj)} {XV : List Nat} {tp : Pat}

/-- A subterm that has been asked about is dropped. -/
theorem SGo.skip {x : Pat} {T Sn Fl : List Pat} (h : SGo S U L XV tp (x :: T) Sn Fl)
    (hx : x ∈ Sn) : SGo S U L XV tp T Sn Fl := by
  refine ⟨fun y hy => h.sub y ?_, h.nd, h.fnd, h.fl, h.found, h.free, fun u hu hv hf a ha => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_cons] at hy ⊢; tauto
  · rcases h.kids u hu hv hf a ha with h1 | h1
    · exact .inl h1
    · rcases List.mem_cons.1 h1 with rfl | h1
      · exact .inl hx
      · exact .inr h1
  · rcases h.root with hr | hr
    · exact .inl hr
    · rcases List.mem_cons.1 hr with e | hr
      · exact .inl (e ▸ hx)
      · exact .inr hr

/-- A new subterm is asked about: it is found when it is free, and when it is
not, its arguments are put on the list. -/
theorem SGo.step {x : Pat} {T T' Sn Fl Fl' : List Pat} (h : SGo S U L XV tp (x :: T) Sn Fl)
    (hx : x ∉ Sn) (hT : ∀ y ∈ T', y ∈ T ∨ (y ∈ tp.subs ∧ y.firstOrder = true))
    (hT' : ∀ y ∈ T, y ∈ T')
    (hFl : (Fl' = Fl ∧ ¬ FreeAt S U L XV tp x) ∨ (Fl' = x :: Fl ∧ FreeAt S U L XV tp x))
    (hk : (∀ v, x ≠ .var v) → x ∉ Fl' → ∀ a ∈ (unspine x []).2, a ∈ T') :
    SGo S U L XV tp T' (x :: Sn) Fl' := by
  have hxs := h.sub x (by simp)
  have hxF : x ∉ Fl := fun hf => hx (h.found x hf).1
  have hsubF : ∀ u, u ∈ Fl → u ∈ Fl' := by
    intro u hu
    rcases hFl with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hu
    · exact List.mem_cons_of_mem _ hu
  refine ⟨fun y hy => ?_, List.nodup_cons.2 ⟨hx, h.nd⟩, ?_, ?_, fun u hu => ?_, fun u hu hf => ?_,
    fun u hu hv hf a ha => ?_, ?_⟩
  · rcases List.mem_append.1 hy with hy | hy
    · rcases hT y hy with hy | hy
      · exact h.sub y (by simp [hy])
      · exact hy
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hxs
      · exact h.sub y (by simp [hy])
  · rcases hFl with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact h.fnd
    · exact List.nodup_cons.2 ⟨hxF, h.fnd⟩
  · have := h.fl
    rcases hFl with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
  · rcases hFl with ⟨rfl, -⟩ | ⟨rfl, hfree⟩
    · obtain ⟨h1, h2⟩ := h.found u hu
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact ⟨List.mem_cons_self, hfree⟩
      · obtain ⟨h1, h2⟩ := h.found u hu
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
  · rcases List.mem_cons.1 hu with rfl | hu
    · rcases hFl with ⟨-, hn⟩ | ⟨rfl, -⟩
      · exact absurd hf hn
      · exact List.mem_cons_self
    · exact hsubF u (h.free u hu hf)
  · rcases List.mem_cons.1 hu with rfl | hu
    · exact .inr (hk hv hf a ha)
    · rcases h.kids u hu hv (fun hf' => hf (hsubF u hf')) a ha with h1 | h1
      · exact .inl (List.mem_cons_of_mem _ h1)
      · rcases List.mem_cons.1 h1 with rfl | h1
        · exact .inl List.mem_cons_self
        · exact .inr (hT' a h1)
  · rcases h.root with hr | hr
    · exact .inl (List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.1 hr with e | hr
      · exact .inl (e ▸ List.mem_cons_self)
      · exact .inr (hT' _ hr)

theorem SGo.seen_le {T Sn Fl : List Pat} (h : SGo S U L XV tp T Sn Fl) :
    Sn.length ≤ tp.subs.card := by
  classical
  rw [← List.toFinset_card_of_nodup h.nd]
  exact Finset.card_le_card fun x hx =>
    (h.sub x (List.mem_append_right _ (List.mem_toFinset.1 hx))).1

end go

theorem succCost_mono {a b : Nat} (h : a ≤ b) : succCost a ≤ succCost b := by
  unfold succCost
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have := Nat.log_mono_right (b := 2) (show a + 1 ≤ b + 1 by omega)
  omega

/-- The ticks asking about a new subterm may take, with the dropping of its
arguments. -/
noncomputable def sX (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj)) (r q : Nat)
    (XV : List Nat) (tp : Pat) (N W : Nat) (p : Pat) : Nat :=
  freeCost S U L r q XV tp p + 6 * nargs p + nargs p * fskip W + succCost (N + W) + 12

/-- The invariant of the loop of `free_subterms`. -/
def SubInv (nm : Option Nat → Sym) (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj))
    (XV : List Nat) (tp : Pat) (N : Nat) (X : Pat → Nat) (W : Nat) (s0 : store.Store) (Bd : Nat)
    (x : store.TermId × store.Store × store.TermId × store.TermId × store.TermId ×
      store.TermId) : Prop :=
  Inv x.2.1 ∧ Extends s0 x.2.1 ∧ ∃ T Sn Fl,
    Repr nm x.2.1.nodes.val x.1.val (encList (nm none) T) ∧
    Repr nm x.2.1.nodes.val x.2.2.1.val (encList (nm none) Sn) ∧
    Repr nm x.2.1.nodes.val x.2.2.2.1.val (foundPat (nm none) N Fl) ∧
    Repr nm x.2.1.nodes.val x.2.2.2.2.1.val (encVarEntries nm U (foundEntries S U L N Fl)) ∧
    VarAt x.2.1.nodes.val x.2.2.2.2.2.val (N + Fl.length) ∧
    SGo S U L XV tp T Sn Fl ∧
    x.2.1.ticks.val + T.length * fskip W + owedG tp.subs (· ∈ Sn) X + 1 ≤ Bd

/-- What the loop leaves. -/
def SubPost (nm : Option Nat → Sym) (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj))
    (XV : List Nat) (tp : Pat) (N : Nat) (s0 : store.Store) (Bd : Nat)
    (y : store.Store × store.TermId × store.TermId) : Prop :=
  Inv y.1 ∧ Extends s0 y.1 ∧ ∃ Sn Fl,
    Repr nm y.1.nodes.val y.2.1.val (foundPat (nm none) N Fl) ∧
    Repr nm y.1.nodes.val y.2.2.val (encVarEntries nm U (foundEntries S U L N Fl)) ∧
    SGo S U L XV tp [] Sn Fl ∧ y.1.ticks.val ≤ Bd

theorem free_subterms_body_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {r q : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (hUz : ∀ n ∈ U, n ≠ nm none)
    (L : List (Nat × Sorts.Conj)) (hL : ∀ v, Sub U (conjOf L v)) (XV : List Nat) {tp : Pat}
    (htfo : tp.firstOrder = true) (N W : Nat) (hW : tp.subs.card ≤ W) (s0 : store.Store)
    (Bd : Nat) (hB : 40 * Bd + 100 ≤ Usize.max) (decls names t xv es : store.TermId)
    (hd : Repr nm s0.nodes.val decls.val sp)
    (hU : Repr nm s0.nodes.val names.val (namesPat (nm none) U))
    (ht : Repr nm s0.nodes.val t.val tp)
    (hxv : Repr nm s0.nodes.val xv.val (encList (nm none) (XV.map Term.var)))
    (hes : Repr nm s0.nodes.val es.val (encVarEntries nm U L))
    (s : store.Store) (todo seen found es1 next : store.TermId)
    (h : SubInv nm S U L XV tp N (sX S U L r q XV tp N W) W s0 Bd
      (todo, s, seen, found, es1, next)) :
    sorts.free_subterms_loop.body decls names t xv es todo s seen found es1 next ⦃ r' =>
      match r' with
      | .done y => SubPost nm S U L XV tp N s0 Bd y
      | .cont x => SubInv nm S U L XV tp N (sX S U L r q XV tp N W) W s0 Bd x ∧
          s.ticks.val < x.2.1.ticks.val ⦄ := by
  unfold sorts.free_subterms_loop.body
  obtain ⟨hI, hE, T, Sn, Fl, rT, rS, rF, rE, hnx, hG, hc⟩ := h
  simp only at hI hE rT rS rF rE hnx hc
  have hsk : fskip W = 2 * W + 2 := rfl
  have hSlen : Sn.length ≤ W := Nat.le_trans hG.seen_le hW
  cases T with
  | nil =>
    step with uncons_repr s todo hI.toWf (p := Term.sym (nm none)) rT
      (by unfold Room; omega) as ⟨o, s1, hK0', hu0⟩
    have K1 : Kept s s1 1 := hK0'.kept hI
    have ht1 := K1.ticks
    subst hu0
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    simp only [WP.spec_ok]
    exact ⟨K1.inv, hE.trans hx1, Sn, Fl, by rw [K1.nodes]; exact rF, by rw [K1.nodes]; exact rE,
      hG, by simp only [List.length_nil] at hc; show s1.ticks.val ≤ Bd; omega⟩
  | cons x T' =>
    step with uncons_repr s todo hI.toWf
      (p := Term.app x (encList (nm none) T')) rT
      (by unfold Room; omega) as ⟨o, s1, hK0', hu0⟩
    have K1 : Kept s s1 1 := hK0'.kept hI
    have ht1 := K1.ticks
    obtain ⟨u, rest, rfl, ru, rrest⟩ := hu0
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hc
    obtain ⟨hxs, hxfo⟩ := hG.sub x (by simp)
    simp only
    step with among_spec hC.inj Sn s1 u seen (tn := x) K1.inv (by rw [K1.nodes]; exact ru)
      (by rw [K1.nodes]; exact rS) (by unfold Room; omega)
      as ⟨b, s2, hI2, hn2', htb2, ht2, hm2, hres⟩
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hn2', K1.nodes]
    have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
    by_cases hseen : x ∈ Sn
    · have hb : b = true := by rw [hres]; simpa using hseen
      subst hb
      simp only [↓reduceIte, WP.spec_ok]
      refine ⟨⟨hI2, hE.trans hx2, T', Sn, Fl, by rw [hn2]; exact rrest, by rw [hn2]; exact rS,
        by rw [hn2]; exact rF, by rw [hn2]; exact rE, by rw [hn2]; exact hnx, hG.skip hseen,
        by show s2.ticks.val + _ + _ + 1 ≤ Bd; omega⟩, by show s.ticks.val < s2.ticks.val; omega⟩
    · have hb : b = false := by rw [hres]; simpa using hseen
      subst hb
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hX := owedG_set (U := tp.subs) (fl := (· ∈ Sn)) (fl' := (· ∈ x :: Sn))
        (sX S U L r q XV tp N W) hxs hseen List.mem_cons_self
        (fun y hy => List.mem_cons_of_mem _ hy)
      have hXd : sX S U L r q XV tp N W x = freeCost S U L r q XV tp x + 6 * nargs x +
          nargs x * fskip W + succCost (N + W) + 12 := rfl
      step with alloc_spec s2 (.App u seen) hI2
        ⟨by rw [hn2]; exact ru.lt, by rw [hn2]; exact rS.lt⟩ (by unfold Room; omega)
        as ⟨seen1, s3, hI3, ht3, htb3, hx3, hid3⟩
      simp only [norm] at hid3
      have hx03 : Extends s s3 := hx2.trans hx3
      have rS1 : Repr nm s3.nodes.val seen1.val (encList (nm none) (x :: Sn)) :=
        .app hid3 (hx03.repr ru) (hx03.repr rS)
      step with is_var_w s3 u hI3.toWf (hx03.repr ru) (by unfold Room; omega)
        as ⟨b1, s4, hb1, hK4⟩
      have K4 : Kept s3 s4 1 := hK4.kept hI3
      have ht4 := K4.ticks
      have hx04 : Extends s s4 := hx03.trans (Extends.of_eq K4.nodes (by omega))
      have rS4 : Repr nm s4.nodes.val seen1.val (encList (nm none) (x :: Sn)) := by
        rw [K4.nodes]; exact rS1
      by_cases hv : ∃ v, x = .var v
      · have hb1' : b1 = true := hb1.2 hv
        subst hb1'
        obtain ⟨v, rfl⟩ := hv
        simp only [↓reduceIte, WP.spec_ok]
        refine ⟨⟨K4.inv, hE.trans hx04, T', _ :: Sn, Fl, hx04.repr rrest, rS4, hx04.repr rF,
          hx04.repr rE, hx04.varAt hnx,
          hG.step hseen (fun y hy => .inl hy) (fun y hy => hy)
            (.inl ⟨rfl, fun hf => hf.1 v rfl⟩) (fun hnv => absurd rfl (hnv v)),
          by show s4.ticks.val + _ + _ + 1 ≤ Bd; omega⟩,
          by show s.ticks.val < s4.ticks.val; omega⟩
      · have hb1' : b1 = false := by
          cases b1 with
          | false => rfl
          | true => exact absurd (hb1.1 rfl) hv
        subst hb1'
        have hnv : ∀ v, x ≠ .var v := fun v e => hv ⟨v, e⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        step with free_spec hC hr hq hUz L hL XV htfo hxfo s4 decls names t xv es u K4.inv
          ((hE.trans hx04).repr hd) ((hE.trans hx04).repr hU) ((hE.trans hx04).repr ht)
          ((hE.trans hx04).repr hxv) ((hE.trans hx04).repr hes) (hx04.repr ru)
          (by unfold Room; omega) as ⟨o1, s5, hI5, hx5, ht5, hpost⟩
        have hx05 : Extends s s5 := hx04.trans hx5
        have h45 := hx5.ticks_le
        cases o1 with
        | none =>
          have hlen : (unspine x []).2.length = nargs x := by
            simpa using unspine_length x []
          step with spine_spec s5 u hI5.toWf (hx05.repr ru) (by unfold Room; omega)
            as ⟨head, args, s6, hR6, _, rargs⟩
          have ht6 := hR6.ticks
          have hI6 : Inv s6 := ⟨hR6.wf, by rw [hR6.stk]; exact hI5.empty⟩
          have hx06 : Extends s s6 := hx05.trans hR6.ext
          have h56 := hR6.ext.ticks_le
          step with append_keep_spec (unspine x []).2 s6 args rest hI6 rargs (hx06.repr rrest)
            (by rw [hlen]; unfold Room; omega) as ⟨todo1, s7, hI7, hx7, rtodo, ht7, htb7⟩
          rw [hlen] at ht7
          have h67 := hx7.ticks_le
          have hx07 : Extends s s7 := hx06.trans hx7
          have hx47 : Extends s4 s7 := (hx5.trans hR6.ext).trans hx7
          refine ⟨⟨hI7, hE.trans hx07, (unspine x []).2 ++ T', x :: Sn, Fl, rtodo, hx47.repr rS4,
            hx07.repr rF, hx07.repr rE, hx07.varAt hnx,
            hG.step hseen ?_ (fun y hy => List.mem_append_right _ hy) (.inl ⟨rfl, hpost⟩)
              (fun _ _ a ha => List.mem_append_left _ ha), ?_⟩,
            by show s.ticks.val < s7.ticks.val; omega⟩
          · intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · rcases unspine_mem x [] y hy with h0 | ⟨h1, -, h3⟩
              · cases h0
              · exact .inr ⟨Term.subs_trans hxs h1, h3 hxfo⟩
            · exact .inl hy
          · show s7.ticks.val + _ + _ + 1 ≤ Bd
            simp only [List.length_append, hlen, Nat.add_mul]
            omega
        | some k =>
          obtain ⟨hfree, rk⟩ := hpost
          simp only
          have hnx5 : VarAt s5.nodes.val next.val (N + Fl.length) := hx05.varAt hnx
          step with alloc_spec s5 (.App u next) hI5 ⟨(hx05.repr ru).lt, hnx5.lt⟩
            (by unfold Room; omega) as ⟨p1, s6, hI6, ht6, htb6, hx6, hid6⟩
          simp only [norm] at hid6
          have hx06 : Extends s s6 := hx05.trans hx6
          have rp1 : Repr nm s6.nodes.val p1.val (.app x (.var (N + Fl.length))) :=
            .app hid6 (hx06.repr ru) (.var (hx6.varAt hnx5))
          step with alloc_spec s6 (.App p1 found) hI6 ⟨rp1.lt, (hx06.repr rF).lt⟩
            (by unfold Room; omega) as ⟨found1, s7, hI7, ht7, htb7, hx7, hid7⟩
          simp only [norm] at hid7
          have hx07 : Extends s s7 := hx06.trans hx7
          have rF1 : Repr nm s7.nodes.val found1.val (foundPat (nm none) N (x :: Fl)) :=
            .app hid7 (hx7.repr rp1) (hx07.repr rF)
          have hnx7 : VarAt s7.nodes.val next.val (N + Fl.length) := hx07.varAt hnx
          have rk7 : Repr nm s7.nodes.val k.val (cpat (nm none) U (cloOf S U L x)) :=
            (hx6.trans hx7).repr rk
          step with alloc_spec s7 (.App next k) hI7 ⟨hnx7.lt, rk7.lt⟩
            (by unfold Room; omega) as ⟨e, s8, hI8, ht8, htb8, hx8, hid8⟩
          simp only [norm] at hid8
          have hx08 : Extends s s8 := hx07.trans hx8
          have re : Repr nm s8.nodes.val e.val
              (varEntry nm U (N + Fl.length, cloOf S U L x)) :=
            .app hid8 (.var (hx8.varAt hnx7)) (hx8.repr rk7)
          step with alloc_spec s8 (.App e es1) hI8 ⟨re.lt, (hx08.repr rE).lt⟩
            (by unfold Room; omega) as ⟨es11, s9, hI9, ht9, htb9, hx9, hid9⟩
          simp only [norm] at hid9
          have hx09 : Extends s s9 := hx08.trans hx9
          have rE1 : Repr nm s9.nodes.val es11.val
              (encVarEntries nm U (foundEntries S U L N (x :: Fl))) :=
            .app hid9 (hx9.repr re) (hx09.repr rE)
          have hFl : Fl.length ≤ W := Nat.le_trans hG.fl hSlen
          have hsc := succCost_mono (a := N + Fl.length) (b := N + W) (by omega)
          step with var_succ_spec s9 next hI9 (hx09.varAt hnx) (by unfold Room; omega)
            as ⟨next1, s10, hI10, hx10, htb10, hnx10, ht10⟩
          have hx010 : Extends s s10 := hx09.trans hx10
          have hx410 : Extends s4 s10 :=
            ((((hx5.trans hx6).trans hx7).trans hx8).trans hx9).trans hx10
          have h910 := hx10.ticks_le
          refine ⟨⟨hI10, hE.trans hx010, T', x :: Sn, x :: Fl, hx010.repr rrest, hx410.repr rS4,
            ((hx8.trans hx9).trans hx10).repr rF1, hx10.repr rE1,
            by simpa [Nat.add_assoc] using hnx10,
            hG.step hseen (fun y hy => .inl hy) (fun y hy => hy) (.inr ⟨rfl, hfree⟩)
              (fun _ hn => absurd List.mem_cons_self hn), ?_⟩,
            by show s.ticks.val < s10.ticks.val; omega⟩
          show s10.ticks.val + _ + _ + 1 ≤ Bd
          omega

/-- The ticks `free_subterms` may take. -/
noncomputable def freeSubsCost (S : Sorts) (U : List Name) (L : List (Nat × Sorts.Conj))
    (r q : Nat) (XV : List Nat) (tp : Pat) (N : Nat) : Nat :=
  fskip tp.subs.card + tp.subs.sum (sX S U L r q XV tp N tp.subs.card) + 4

/-- `free_subterms` returns the free subterms it found, each with its
variable, and the entries with the sorts of those variables. -/
theorem free_subterms_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {r q : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (hUz : ∀ n ∈ U, n ≠ nm none)
    (L : List (Nat × Sorts.Conj)) (hL : ∀ v, Sub U (conjOf L v)) (XV : List Nat) {tp : Pat}
    (htfo : tp.firstOrder = true) (N : Nat) (s : store.Store)
    (decls names t xv es next0 : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (ht : Repr nm s.nodes.val t.val tp)
    (hxv : Repr nm s.nodes.val xv.val (encList (nm none) (XV.map Term.var)))
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (hnx : VarAt s.nodes.val next0.val N)
    (hroom : Room s (freeSubsCost S U L r q XV tp N)) :
    sorts.free_subterms s decls names t xv es next0 ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + freeSubsCost S U L r q XV tp N ∧
        ∃ Sn Fl, Repr nm s'.nodes.val res.1.val (foundPat (nm none) N Fl) ∧
          Repr nm s'.nodes.val res.2.val (encVarEntries nm U (foundEntries S U L N Fl)) ∧
          SGo S U L XV tp [] Sn Fl ⦄ := by
  unfold sorts.free_subterms sorts.free_subterms_loop
  have hroom' := hroom
  unfold Room at hroom'
  unfold freeSubsCost at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  have rnil1 : Repr nm s1.nodes.val nil.val (.sym (nm none)) := .nil hr1
  step with alloc_spec s1 (.App t nil) hI1 ⟨(hx1.repr ht).lt, rnil1.lt⟩
    (by unfold Room; omega) as ⟨todo, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr2
  have hx02 : Extends s s2 := hx1.trans hx2
  have rnil2 : Repr nm s2.nodes.val nil.val (.sym (nm none)) := hx2.repr rnil1
  let Bd := s.ticks.val + freeSubsCost S U L r q XV tp N
  have hsum := owedG_le_sum tp.subs (· ∈ ([] : List Pat)) (sX S U L r q XV tp N tp.subs.card)
  have hloop := loop.spec_decr_nat
    (fun x : store.TermId × store.Store × store.TermId × store.TermId × store.TermId ×
      store.TermId => Bd + 1 - x.2.1.ticks.val)
    (fun x => SubInv nm S U L XV tp N (sX S U L r q XV tp N tp.subs.card) tp.subs.card s2 Bd x)
    (fun y : store.Store × store.TermId × store.TermId => SubPost nm S U L XV tp N s2 Bd y)
    (fun x : store.TermId × store.Store × store.TermId × store.TermId × store.TermId ×
      store.TermId =>
      sorts.free_subterms_loop.body decls names t xv es x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2)
    (todo, s2, nil, nil, es, next0)
    (by
      rintro ⟨td, y, sn, fd, e1, nx⟩ hinv
      refine WP.spec_mono (free_subterms_body_spec hC hr hq hUz L hL XV htfo N tp.subs.card
        (Nat.le_refl _) s2 Bd (by unfold Bd freeSubsCost; omega) decls names t xv es
        (hx02.repr hd) (hx02.repr hU) (hx02.repr ht) (hx02.repr hxv) (hx02.repr hes) y td sn fd
        e1 nx hinv) ?_
      intro r' hr'
      cases r' with
      | done z => exact hr'
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr'
        refine ⟨h1, ?_⟩
        obtain ⟨-, -, T, Sn, Fl, -, -, -, -, -, -, hc⟩ := h1
        simp only at h2 hc ⊢
        omega)
    ⟨hI2, Extends.refl s2, [tp], [], [], .app hr2 (hx02.repr ht) rnil2, rnil2, rnil2,
      hx02.repr hes, hx02.varAt hnx, ⟨by
        intro x hx
        simp only [List.append_nil, List.mem_singleton] at hx
        subst hx
        exact ⟨Term.self_mem_subs _, htfo⟩, List.nodup_nil, List.nodup_nil, Nat.le_refl _,
        fun u hu => (by cases hu), fun u hu => (by cases hu), fun u hu => (by cases hu),
        .inr (by simp)⟩, by
      simp only [List.length_singleton, Nat.one_mul]
      unfold Bd freeSubsCost
      omega⟩
  step with hloop as ⟨s', fd, e1, hy⟩
  obtain ⟨hI', hx', Sn, Fl, rF, rE, hG, ht'⟩ := hy
  exact ⟨hI', hx02.trans hx', ht', Sn, Fl, rF, rE, hG⟩

end RwLogVerified
