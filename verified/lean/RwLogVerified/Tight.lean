/-
# `sorts::tighten` against the specification

The loop of `sorts::tighten` makes the rounds of `tightRun`
(`tighten_loop_spec`), each within `roundCost`. With `tightRun_total` and
`Sorts.Tightens`, what `sorts::tighten` returns denotes what it was given,
satisfies the invariant and has no variable whose values have one root, and
it returns nothing only for a store that denotes nothing (`tighten_sound`).
-/
import RwLogVerified.TightRun

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-- The nodes hold the state. -/
structure Holds (nm : Option Nat → RwLog.Sym) (U : List Name) (nodes : List store.Node)
    (st : TSt) (t x es next : store.TermId) : Prop where
  t : Repr nm nodes t.val st.T
  x : Repr nm nodes x.val (encX nm st.X)
  es : Repr nm nodes es.val (encVarEntries nm U st.L)
  next : VarAt nodes next.val st.N

theorem Holds.ext {U : List Name} {s s' : store.Store} {st : TSt} {t x es next : store.TermId}
    (h : Holds nm U s.nodes.val st t x es next) (hx : Extends s s') :
    Holds nm U s'.nodes.val st t x es next :=
  ⟨hx.repr h.t, hx.repr h.x, hx.repr h.es, hx.varAt h.next⟩

theorem altOf_length (S : Sorts) (c : Sorts.Conj) (f : Sym) (n : Nat) :
    (altOf S c f n).length = n := by simp [altOf]

theorem newEntries_length (S : Sorts) (st : TSt) (en : Nat × Sorts.Conj) (κ : Sym × Nat) :
    (newEntries S st en κ).length = κ.2 := by
  rw [newEntries, entsFrom_length, altOf_length]

/-- The ticks a replacement may take. -/
noncomputable def replaceCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u : Nat) (st : TSt) :
    Option (List (Nat × Sorts.Conj) × (Nat × Sorts.Conj) × (Sym × Nat) × List (Nat × Sorts.Conj)) →
      Nat
  | none => 0
  | some (_, en, κ, _) =>
    openCost nm st.N κ.2 st.T st.X +
      settleCost nm S u (newEntries S st en κ)
        (st.T.bind (Term.single en.1 (Sorts.expVar st.N κ.2 κ.1)))
        (st.X.map (Eqns.subst en.1 (Sorts.expVar st.N κ.2 κ.1))) + 2 * κ.2 + 1

/-- The ticks a round may take. -/
noncomputable def roundCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r : Nat) (st : TSt) :
    Nat :=
  anyAlwaysCost nm st.X + firstSoleCost nm S u r st.X st.L +
    replaceCost nm S u st (splitSole S st.X st.L)

/-- The ticks at most `k` rounds may take. -/
noncomputable def runCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r : Nat) :
    Nat → TSt → Nat
  | 0, _ => 0
  | k + 1, st =>
    match round S st with
    | .next st' true => roundCost nm S u r st + runCost nm S u r k st'
    | _ => roundCost nm S u r st

theorem tighten_loop_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat}
    {U : List Name} (hC : Ctx nm S sp U) {r : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (decls names : store.TermId) :
    ∀ (k : Nat) (st : TSt) (s : store.Store) (t x es next : store.TermId) (o : Option TSt),
    Inv s → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Holds nm U s.nodes.val st t x es next → (∀ p ∈ st.L, Sub U p.2) →
    tightRun S k st = some o → Room s (runCost nm S U.length r k st) →
    sorts.tighten_loop s decls names true t x es next true ⦃ res =>
      Inv res.1 ∧ Extends s res.1 ∧
        res.1.ticks.val ≤ s.ticks.val + runCost nm S U.length r k st ∧
        match o with
        | none => res.2.1 = false
        | some st' => res.2.1 = true ∧
            Holds nm U res.1.nodes.val st' res.2.2.1 res.2.2.2.1 res.2.2.2.2.1 res.2.2.2.2.2 ∧
            ∀ p ∈ st'.L, Sub U p.2 ⦄ := by
  intro k
  induction k with
  | zero => intro st s t x es next o _ _ _ _ _ hrun; cases hrun
  | succ k ih =>
    intro st s t x es next o hI hde hU hH hsub hrun hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.tighten_loop
    rw [loop]
    simp only [sorts.tighten_loop.body, ↓reduceIte]
    have hge : roundCost nm S U.length r st ≤ runCost nm S U.length r (k + 1) st := by
      simp only [runCost]
      split <;> omega
    have hrc : roundCost nm S U.length r st = anyAlwaysCost nm st.X +
        firstSoleCost nm S U.length r st.X st.L +
        replaceCost nm S U.length st (splitSole S st.X st.L) := rfl
    step with any_always_spec hnm s x hI hH.x (by unfold Room; omega) as ⟨r1, hI1, hx1, ht1, hb⟩
    obtain ⟨b, s1⟩ := r1
    simp only at hI1 hx1 ht1 hb
    cases b with
    | true =>
      have hround : round S st = .dead := by simp [round, ← hb]
      simp only [tightRun, hround, Option.some.injEq] at hrun
      subst hrun
      simp only [↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      exact ⟨hI1, hx1, by omega, trivial⟩
    | false =>
      have hany : st.X.any Sorts.always = false := hb.symm
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry]
      step with first_sole_spec hnm hC hr s1 decls names x es st.X st.L hI1 (hx1.repr hde)
        (hx1.repr hU) (hx1.repr hH.x) hsub (hx1.repr hH.es) (by unfold Room; omega)
        as ⟨r2, hI2, hx2, ht2, hF⟩
      obtain ⟨o1, s2⟩ := r2
      simp only at hI2 hx2 ht2 hF
      have hx02 := hx1.trans hx2
      cases o1 with
      | none =>
        have hq : splitSole S st.X st.L = none := splitSole_none hF
        have hround : round S st = .done := by simp [round, hany, hq]
        simp only [tightRun, hround, Option.some.injEq] at hrun
        subst hrun
        simp only [uncurry, bind_ok]
        rw [loop]
        simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
        exact ⟨hI2, hx02, by omega, trivial, hH.ext hx02, hsub⟩
      | some q =>
        obtain ⟨v, f, kids, others⟩ := q
        obtain ⟨pre, en, post, κ, hL, hpre, hs, hv, hf, hk, ho⟩ := hF
        have hq : splitSole S st.X st.L = some (pre, en, κ, post) := by
          rw [hL]; exact splitSole_some hs hpre
        have hround : round S st = .next (openSt S st pre post en κ)
            (settleOk S (newEntries S st en κ)) := by simp [round, hany, hq]
        rw [hq] at hrc
        simp only [replaceCost] at hrc
        have hlen := altOf_length S en.2 κ.1 κ.2
        simp only [uncurry]
        step with open_var_spec hnm (U := U) s2 v f kids next t x (xv := en.1) (N := st.N)
          (fs := κ.1) (cs := altOf S en.2 κ.1 κ.2) (T := st.T) (X := st.X) hI2 hv hf hk
          (hx02.varAt hH.next) (hx02.repr hH.t) (hx02.repr hH.x)
          (by rw [hlen]; unfold Room; omega) as ⟨r3, hI3, hx3, ht3, h31, h32, h33, h34⟩
        obtain ⟨⟨t2, x2, new, next2⟩, s3⟩ := r3
        rw [hlen] at ht3 h31 h32 h34
        simp only at hI3 hx3 ht3 h31 h32 h33 h34
        have hx03 := hx02.trans hx3
        have hsubnew : ∀ p ∈ newEntries S st en κ, Sub U p.2 := by
          intro p hp n hn
          obtain ⟨i, -, rfl⟩ := mem_newEntries.1 hp
          exact hC.names n (Sorts.kidC_subset_names hn)
        simp only [uncurry]
        step with settle_spec hnm hC (newEntries S st en κ)
          (st.T.bind (Term.single en.1 (Sorts.expVar st.N κ.2 κ.1)))
          (st.X.map (Eqns.subst en.1 (Sorts.expVar st.N κ.2 κ.1))) s3 decls names t2 x2 new hI3
          (hx03.repr hde) (hx03.repr hU) hsubnew h33 h31 h32 (by unfold Room; omega)
          as ⟨r4, hI4, hx4, ht4, h40, h41, h42, h43⟩
        obtain ⟨⟨ok3, t3, x3, kept⟩, s4⟩ := r4
        simp only at hI4 hx4 ht4 h40 h41 h42 h43
        have hx04 := hx03.trans hx4
        have hkl : (settleKept S (newEntries S st en κ)).length ≤ κ.2 := by
          rw [← newEntries_length S st en κ]; exact List.length_filter_le _ _
        simp only [uncurry]
        step with rev_onto_spec ((settleKept S (newEntries S st en κ)).map (varEntry nm U))
          ((pre ++ post).map (varEntry nm U)) s4 kept others hI4.toWf h43
          ((hx3.trans hx4).repr (by simpa [encVarEntries] using ho))
          (by simp only [List.length_map]; unfold Room; omega) as ⟨r5, hR, hr5⟩
        obtain ⟨es1, s5⟩ := r5
        simp only [List.length_map] at hR hr5
        have ht5 := hR.ticks
        have hI5 : Inv s5 := ⟨hR.wf, by rw [hR.stk]; exact hI4.empty⟩
        have hx05 := hx04.trans hR.ext
        have hH' : Holds nm U s5.nodes.val (openSt S st pre post en κ) t3 x3 es1 next2 :=
          ⟨hR.ext.repr h41, hR.ext.repr h42, by
            simpa [openSt, encVarEntries, List.map_append, List.map_reverse] using hr5,
            (hx4.trans hR.ext).varAt h34⟩
        have hsub' : ∀ p ∈ (openSt S st pre post en κ).L, Sub U p.2 := by
          intro p hp
          rcases List.mem_append.1 hp with hp | hp
          · exact hsubnew p (mem_settleKept.1 (List.mem_reverse.1 hp)).1
          · exact hsub p (pre_post_sub hL p hp)
        simp only [uncurry, bind_ok]
        cases ok3 with
        | false =>
          simp only [tightRun, hround, ← h40, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hrun
          subst hrun
          rw [loop]
          simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
          exact ⟨hI5, hx05, by omega, trivial⟩
        | true =>
          simp only [tightRun, hround, ← h40, ↓reduceIte] at hrun
          have hcost : runCost nm S U.length r (k + 1) st =
              roundCost nm S U.length r st +
                runCost nm S U.length r k (openSt S st pre post en κ) := by
            simp only [runCost, hround, ← h40]
          rw [hcost] at hroom'
          have IH := ih (openSt S st pre post en κ) s5 t3 x3 es1 next2 o hI5 (hx05.repr hde)
            (hx05.repr hU) hH' hsub' hrun (by unfold Room; omega)
          unfold sorts.tighten_loop at IH
          refine WP.spec_mono IH ?_
          rintro res ⟨hI', hx', ht', hres⟩
          exact ⟨hI', hx05.trans hx', by rw [hcost]; omega, hres⟩

/-! ## `sorts::tighten` -/

theorem tighten_loop_false (s : store.Store) (decls names t x es next : store.TermId) :
    sorts.tighten_loop s decls names false t x es next false = ok (s, false, t, x, es, next) := by
  unfold sorts.tighten_loop
  rw [loop]
  simp [sorts.tighten_loop.body]

/-- What `sorts::tighten` comes to with at most `k` rounds: nothing when more
are needed, and otherwise the state reached, or nothing when the store
denotes nothing. -/
def tightenRes (S : Sorts) (k : Nat) (st : TSt) : Option (Option TSt) :=
  if settleOk S st.L then tightRun S k (settleSt S st) else some none

/-- The ticks `sorts::tighten` may take with at most `k` rounds. -/
noncomputable def tightenCost (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r k : Nat)
    (st : TSt) : Nat :=
  settleCost nm S u st.L st.T st.X + runCost nm S u r k (settleSt S st)

/-- `tighten` replaces the variables with one value and then makes the rounds
of `tightRun`, within the charge of these rounds. -/
theorem tighten_spec (hnm : Function.Injective nm) {S : Sorts} {sp : Pat} {U : List Name}
    (hC : Ctx nm S sp U) {r : Nat} (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (s : store.Store) (decls names t x es next : store.TermId) (st : TSt) (k : Nat)
    (o : Option TSt) (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hH : Holds nm U s.nodes.val st t x es next) (hsub : ∀ p ∈ st.L, Sub U p.2)
    (hrun : tightenRes S k st = some o) (hroom : Room s (tightenCost nm S U.length r k st)) :
    sorts.tighten s decls names t x es next ⦃ res s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + tightenCost nm S U.length r k st ∧
        match o with
        | none => res = none
        | some st' => ∃ t' x' es' next', res = some (t', x', es', next') ∧
            Holds nm U s'.nodes.val st' t' x' es' next' ∧ ∀ p ∈ st'.L, Sub U p.2 ⦄ := by
  unfold sorts.tighten
  have hroom' := hroom
  unfold Room at hroom'
  simp only [tightenCost] at hroom'
  step with settle_spec hnm hC st.L st.T st.X s decls names t x es hI hde hU hsub hH.es hH.t hH.x
    (by unfold Room; omega) as ⟨ok0, t1, x1, es1, s1, hI1, hx1, ht1, h0, h1, h2, h3⟩
  cases ok0 with
  | false =>
    simp only [tightenRes, ← h0, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hrun
    subst hrun
    rw [tighten_loop_false]
    simp only [bind_ok, uncurry, Bool.false_eq_true, ↓reduceIte, WP.spec_ok, WP.uncurry']
    exact ⟨hI1, hx1, by simp only [tightenCost]; omega, trivial⟩
  | true =>
    simp only [tightenRes, ← h0, ↓reduceIte] at hrun
    have hH1 : Holds nm U s1.nodes.val (settleSt S st) t1 x1 es1 next :=
      ⟨h1, h2, h3, hx1.varAt hH.next⟩
    step with tighten_loop_spec hnm hC hr decls names k (settleSt S st) s1 t1 x1 es1 next o hI1
      (hx1.repr hde) (hx1.repr hU) hH1 (fun p hp => hsub p (mem_settleKept.1 hp).1) hrun
      (by unfold Room; omega) as ⟨s2, ok1, t', x', es', next', hI2, hx2, ht2, hres⟩
    cases o with
    | none =>
      simp only at hres
      subst hres
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨hI2, hx1.trans hx2, by simp only [tightenCost]; omega, rfl⟩
    | some st' =>
      obtain ⟨rfl, hH', hsub'⟩ := hres
      simp only [↓reduceIte, WP.spec_ok]
      exact ⟨hI2, hx1.trans hx2, by simp only [tightenCost]; omega, t', x', es', next', rfl, hH',
        hsub'⟩

/-- Among well-formed sorts, `sorts::tighten` ends. What it returns denotes
what it was given, satisfies the invariant of `Sorts.tighten`, and has no
variable whose values have one root; it returns nothing only when what it
was given denotes nothing. -/
theorem tighten_sound {S : Sorts} (hS : S.WellFormed) (st : TSt) (hok : st.OK)
    (hfin : st.abs.store.Fin st.N) (hfull : st.abs.store.Full) :
    ∃ k o, tightenRes S k st = some o ∧
      match o with
      | none => st.abs.store.Den S = ∅
      | some st' => st'.abs.store.Den S = st.abs.store.Den S ∧ Sorts.Inv S st'.abs ∧
          (∀ v ∈ st'.abs.t.vars,
            Sorts.sole S (st'.abs.conj v) (Sorts.gone st'.abs.x v) = none) ∧ st'.Good S := by
  obtain ⟨hden, hlen, hfin', hfull', -, hsubv, hnot⟩ :=
    Sorts.settle_spec S (st.L.map Prod.fst) st.abs
  have habs := settleSt_abs (S := S) hok
  have hok1 := settleSt_ok (S := S) hok
  have hkept : Sorts.Kept S (settleSt S st).abs := by
    rw [habs]
    refine ⟨by rw [hlen]; exact hfin' (by rw [TSt.abs_length]; exact hfin), hfull' hfull, ?_⟩
    intro v hv g
    by_cases hw : v ∈ st.L.map Prod.fst
    · exact hnot v hw hv g
    · rw [(hsubv v hv).2, hok.conj, conjOf_not fun e he e' => hw (List.mem_map.2 ⟨e, he, e'⟩),
        count_empty]
      intro e; cases e
  by_cases hflag : settleOk S st.L = true
  · have hG : (settleSt S st).Good S := by
      refine ⟨hok1, hkept, fun e he => ?_⟩
      obtain ⟨he1, he2⟩ := mem_settleKept.1 he
      have hnn := (List.all_eq_true.1 hflag) e he1
      cases hc : Sorts.count S e.2 with
      | none => rw [hc] at hnn; simp [noneB] at hnn
      | one g => rw [hc] at he2; simp [isOne] at he2
      | many => rfl
    obtain ⟨k, o, hrun, hT, hgood⟩ := tightRun_total hS _ _ rfl hG
    refine ⟨k, o, by simp [tightenRes, hflag, hrun], ?_⟩
    cases o with
    | none =>
      have := hT.none hkept rfl
      rw [habs, hden] at this
      exact this
    | some st' =>
      obtain ⟨h1, h2, h3⟩ := hT.some st'.abs rfl
      exact ⟨by rw [h1, habs, hden], h2, h3, hgood st' rfl⟩
  · refine ⟨0, none, by simp [tightenRes, hflag], ?_⟩
    have hex : ∃ e ∈ st.L, Sorts.count S e.2 = .none := by
      by_contra hne
      refine hflag (List.all_eq_true.2 fun e he => ?_)
      cases hc : Sorts.count S e.2 with
      | none => exact absurd ⟨e, he, hc⟩ hne
      | one g => rfl
      | many => rfl
    obtain ⟨e, he, hc⟩ := hex
    have hni : ¬ Sorts.Inv S (settleSt S st).abs :=
      not_inv_of_none hok1 (mem_settleKept.2 ⟨he, by rw [hc]; rfl⟩) hc
    have := Sorts.den_empty_of_not_inv hkept hni
    rw [habs, hden] at this
    exact this

end RwLogVerified
