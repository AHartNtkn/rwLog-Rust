/-
# Whether the members of a conjunction are the instances of a pattern

`sorts::fits` decides `Sorts.fitsIn`: whether every member of a conjunction
is an instance of a first-order pattern with its variables in the
conjunctions a list of entries gives them. It keeps a list of pairs of a
conjunction and a subterm still to ask about and a list of the pairs asked
about, so a pair is asked about once however often it is reached. A pair
with a variable asks whether the conjunction is within every sort of the
variable (`included`); a pair with a symbol asks for the one root of the
members of the conjunction (`sole_root`) and puts the pair of each argument
on the list.
-/
import RwLog.Sorts.Fits
import RwLogVerified.Among
import RwLogVerified.Clo
import RwLogVerified.Sole
import RwLogVerified.Compose

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-! ## The pairs asked about -/

/-- A pair of a conjunction and a subterm, as a term. -/
noncomputable def fpair (z : Sym) (U : List Name) (x : Sorts.Conj × Pat) : Pat :=
  .app (cpat z U x.1) x.2

theorem fpair_inj {z : Sym} {U : List Name} {x y : Sorts.Conj × Pat} (hx : Sub U x.1)
    (hy : Sub U y.1) (h : fpair z U x = fpair z U y) : x = y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [fpair, Term.app.injEq] at h
  have e : a = c := cpat_inj hx hy h.1
  rw [e, h.2]

/-- The pairs of the arguments of a pair with a symbol. -/
def fkids (S : Sorts) (K : Sorts.Conj) (f : Sym) (args : List Pat) : List (Sorts.Conj × Pat) :=
  (altOf S K f args.length).zip args

theorem unspine_mk {p : Pat} {f : Sym} {args : List Pat} (h : unspine p [] = (.sym f, args)) :
    p = Term.mk f args := by
  have := unspine_foldl p []
  rw [h] at this
  exact this

theorem fit_var {S : Sorts} (c : Nat → Sorts.Conj) (K : Sorts.Conj) (y : Nat) :
    Sorts.fitsIn S c K (.var y) = true ↔ ∀ m ∈ c y, Sorts.Incl S K m := by
  rw [Sorts.fitsIn_var, decide_eq_true_iff]

theorem fit_app {S : Sorts} (c : Nat → Sorts.Conj) (K : Sorts.Conj) {p : Pat} {f : Sym}
    {args : List Pat} (h : unspine p [] = (.sym f, args)) :
    Sorts.fitsIn S c K p = true ↔ Sorts.sole S K [] = some (f, args.length) ∧
      ∀ y ∈ fkids S K f args, Sorts.fitsIn S c y.1 y.2 = true := by
  rw [unspine_mk h, Sorts.fitsIn_mk, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro hall ⟨K', a⟩ hy
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hy
    simp only [fkids] at hi
    rw [List.getElem?_zip_eq_some] at hi
    obtain ⟨h1, h2⟩ := hi
    rw [altOf_getElem?] at h1
    split at h1
    · rename_i hlt
      simp only [Option.some.injEq] at h1
      subst h1
      have := hall ⟨i, hlt⟩ (List.mem_finRange _)
      have e : args[i] = a := by
        rw [List.getElem?_eq_getElem hlt] at h2
        exact Option.some.inj h2
      rw [← e]
      exact this
    · cases h1
  · intro hall i _
    refine hall (Sorts.kidC S K f args.length i, args[i]) ?_
    refine List.mem_iff_getElem?.2 ⟨i, ?_⟩
    simp only [fkids]
    rw [List.getElem?_zip_eq_some, altOf_getElem?]
    simp

theorem sole_kid {S : Sorts} {K : Sorts.Conj} {f : Sym} {n i : Nat}
    (h : Sorts.sole S K [] = some (f, n)) (hi : i < n) :
    Sorts.Kid S K (Sorts.kidC S K f n i) := by
  unfold Sorts.sole at h
  split at h
  · cases h
  · rename_i hr
    have : (f, n) ∈ Sorts.survivors S K [] := by
      rw [Sorts.only_eq_some.1 h]; exact Finset.mem_singleton_self _
    simp only [Sorts.survivors, List.filterMap_nil, List.toFinset_nil, Finset.union_empty,
      Finset.mem_filter] at this
    exact ⟨hr, (f, n), this.1, this.2.1.1, i, hi, rfl⟩

/-! ## Whether a conjunction is within every sort of another -/

/-- `all_included` answers whether every member of a conjunction is in every
sort of a list. -/
theorem all_included_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {q : Nat} (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (K : Sorts.Conj)
    (hK : Sub U K) :
    ∀ (ms : List Name) (s : store.Store) (decls names ki c : store.TermId), Inv s →
    Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val ki.val (cpat (nm none) U K) →
    Repr nm s.nodes.val c.val (namesPat (nm none) ms) → (∀ m ∈ ms, m ≠ nm none) →
    Room s (ms.length * (inclCost S U.length q + 1) + 1) →
    sorts.all_included_loop s decls names ki true c true ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + ms.length * (inclCost S U.length q + 1) + 1 ∧
        (b = true ↔ ∀ m ∈ ms, Sorts.Incl S K m) ⦄ := by
  intro ms
  induction ms with
  | nil =>
    intro s decls names ki c hI hd hU hk hc hz hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.all_included_loop
    rw [loop]
    simp only [sorts.all_included_loop.body, ↓reduceIte]
    step with uncons_repr s c hI.toWf (p := Term.sym (nm none)) hc (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok]
    rw [loop]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
      by simp⟩
  | cons m ms ih =>
    intro s decls names ki c hI hd hU hk hc hz hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    have hcost := outCost_mono S U.length (hq K m)
    unfold sorts.all_included_loop
    rw [loop]
    simp only [sorts.all_included_loop.body, ↓reduceIte]
    unfold namesPat at hc
    step with uncons_repr s c hI.toWf
      (p := Term.app (.sym m) (encList (nm none) (ms.map fun n => (.sym n : Pat)))) hc
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨mi, rest, rfl, rm, rrest⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
    step with included_spec hC K m hK (hz m List.mem_cons_self) s1 decls names ki mi K1.inv
      (hx1.repr hd) (hx1.repr hU) (hx1.repr hk) (hx1.repr rm)
      (by unfold Room inclCost at *; omega) as ⟨r1, hI2, hx2, ht2, hb⟩
    obtain ⟨b, s2⟩ := r1
    simp only at hI2 hx2 ht2 hb
    unfold inclCost at ht2 hroom' ⊢
    have hx02 : Extends s s2 := hx1.trans hx2
    by_cases hin : Sorts.Incl S K m
    · have hbt : b = true := hb.2 hin
      subst hbt
      simp only [↓reduceIte, uncurry, bind_ok]
      have IH := ih s2 decls names ki rest hI2 (hx02.repr hd) (hx02.repr hU) (hx02.repr hk)
        (hx02.repr rrest) (fun m' hm' => hz m' (List.mem_cons_of_mem _ hm'))
        (by unfold Room inclCost; omega)
      unfold sorts.all_included_loop at IH
      refine WP.spec_mono IH ?_
      rintro ⟨res, s'⟩ ⟨hI', hx', ht', hres'⟩
      unfold inclCost at ht'
      refine ⟨hI', hx02.trans hx', by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_⟩
      rw [hres']
      simp [hin]
    · have hbf : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd (hb.1 rfl) hin
      subst hbf
      simp only [Bool.false_eq_true, ↓reduceIte, uncurry, bind_ok]
      rw [loop]
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨hI2, hx02, by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      exact fun h => hin (h m List.mem_cons_self)

/-! ## The pairs of the arguments -/

/-- `pairs_onto` puts the pair of each member of a list with the member of
another at its place in front of a list of pairs. -/
theorem pairs_onto_gen_spec :
    ∀ (Ks args : List Pat) (s : store.Store) (kids ai out : store.TermId)
      (T : List Pat), Inv s → Ks.length = args.length →
    Repr nm s.nodes.val kids.val (encList (nm none) Ks) →
    Repr nm s.nodes.val ai.val (encList (nm none) args) →
    Repr nm s.nodes.val out.val (encList (nm none) T) →
    Room s (4 * Ks.length + 1) →
    sorts.pairs_onto_loop kids s out ai ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 4 * Ks.length + 1 ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) ((List.zipWith Term.app Ks args).reverse ++ T)) ⦄ := by
  intro Ks
  induction Ks with
  | nil =>
    intro args s kids ai out T hI hlen hk ha ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.pairs_onto_loop
    rw [loop]
    simp only [sorts.pairs_onto_loop.body]
    step with uncons_repr s kids hI.toWf (p := Term.sym (nm none)) hk (by unfold Room; omega)
      as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    subst hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    simp only [uncurry, bind_ok, WP.spec_ok]
    exact ⟨K1.inv, Extends.of_eq K1.nodes (by omega), by simp only [List.length_nil]; omega,
      by rw [K1.nodes]; simpa using ho⟩
  | cons K Ks ih =>
    intro args s kids ai out T hI hlen hk ha ho hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    cases args with
    | nil => simp at hlen
    | cons a args =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    unfold sorts.pairs_onto_loop
    rw [loop]
    simp only [sorts.pairs_onto_loop.body]
    step with uncons_repr s kids hI.toWf
      (p := Term.app K (encList (nm none) Ks)) hk
      (by unfold Room; omega) as ⟨r0, hK0, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK0
    obtain ⟨k, kt, rfl, rk, rkt⟩ := hu
    have K1 := hK0.kept hI
    have ht1 := K1.ticks
    step with uncons_repr s1 ai K1.inv.toWf (p := Term.app a (encList (nm none) args))
      (by rw [K1.nodes]; exact ha) (by unfold Room; omega) as ⟨r1, hK1, hu1⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu1
    simp only at hK1
    obtain ⟨a', at', rfl, ra, rat⟩ := hu1
    rw [K1.nodes] at ra rat
    have K2 := hK1.kept K1.inv
    have ht2 := K2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [K2.nodes, K1.nodes]
    have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
    step with alloc_spec s2 (.App k a') K2.inv ⟨(hx2.repr rk).lt, (hx2.repr ra).lt⟩
      (by unfold Room; omega) as ⟨r2, hI3, ht3, htb3, hx3, hid3⟩
    obtain ⟨p2, s3⟩ := r2
    simp only [norm] at hI3 ht3 htb3 hx3 hid3
    have hx03 : Extends s s3 := hx2.trans hx3
    have rp : Repr nm s3.nodes.val p2.val (.app K a) :=
      .app hid3 (hx03.repr rk) (hx03.repr ra)
    step with alloc_spec s3 (.App p2 out) hI3 ⟨rp.lt, (hx03.repr ho).lt⟩
      (by unfold Room; omega) as ⟨r3, hI4, ht4, htb4, hx4, hid4⟩
    obtain ⟨out1, s4⟩ := r3
    simp only [norm] at hI4 ht4 htb4 hx4 hid4
    have hx04 : Extends s s4 := hx03.trans hx4
    have ro : Repr nm s4.nodes.val out1.val
        (encList (nm none) (Term.app K a :: T)) :=
      .app hid4 (hx4.repr rp) (hx04.repr ho)
    simp only [uncurry, bind_ok]
    have IH := ih args s4 kt at' out1 (Term.app K a :: T) hI4 hlen (hx04.repr rkt) (hx04.repr rat) ro
      (by unfold Room; omega)
    unfold sorts.pairs_onto_loop at IH
    refine WP.spec_mono IH ?_
    rintro ⟨res, s'⟩ ⟨hI', hx', ht', hres'⟩
    refine ⟨hI', hx04.trans hx', by simp only [List.length_cons]; omega, ?_⟩
    simpa using hres'

/-- `pairs_onto` puts the pair of each conjunction with the argument at its
place in front of a list of pairs. -/
theorem pairs_onto_loop_spec {U : List Name} (Ks : List Sorts.Conj) (args : List Pat)
    (s : store.Store) (kids ai out : store.TermId) (T : List (Sorts.Conj × Pat)) (hI : Inv s)
    (hlen : Ks.length = args.length)
    (hk : Repr nm s.nodes.val kids.val (encList (nm none) (Ks.map (cpat (nm none) U))))
    (ha : Repr nm s.nodes.val ai.val (encList (nm none) args))
    (ho : Repr nm s.nodes.val out.val (encList (nm none) (T.map (fpair (nm none) U))))
    (hroom : Room s (4 * Ks.length + 1)) :
    sorts.pairs_onto_loop kids s out ai ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 4 * Ks.length + 1 ∧
        Repr nm s'.nodes.val r.val
          (encList (nm none) (((Ks.zip args).reverse ++ T).map (fpair (nm none) U))) ⦄ := by
  have e : (List.zipWith Term.app (Ks.map (cpat (nm none) U)) args).reverse ++
      T.map (fpair (nm none) U) = ((Ks.zip args).reverse ++ T).map (fpair (nm none) U) := by
    rw [List.map_append, List.map_reverse, List.zip_eq_zipWith, List.map_zipWith,
      List.zipWith_map_left]
    rfl
  rw [← e]
  simpa using pairs_onto_gen_spec (nm := nm) (Ks.map (cpat (nm none) U)) args s kids ai out
    (T.map (fpair (nm none) U)) hI (by simpa using hlen) hk ha ho (by simpa using hroom)

/-! ## The loop -/

theorem Extends.ticks_le {s s' : store.Store} (h : Extends s s') :
    s.ticks.val ≤ s'.ticks.val := by
  obtain ⟨m, -, h⟩ := h
  omega

/-- The pairs that may be asked about. -/
noncomputable def funiv (S : Sorts) (K0 : Sorts.Conj) (u0 : Pat) : Finset (Sorts.Conj × Pat) :=
  Sorts.reachSet S K0 ×ˢ u0.subs

theorem sub_of_reach {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {K0 K : Sorts.Conj} (hK0 : Sub U K0) (h : Sorts.Reach S K0 K) : Sub U K := by
  rcases h.eq_or_subset_names with rfl | h'
  · exact hK0
  · exact fun n hn => hC.names n (h' hn)

/-- What holds of the pairs still to ask about, `T`, and the pairs asked
about, `Sn`, while no answer has been no. Every pair is of a conjunction the
first one reaches and a subterm of the pattern, and fits when the first pair
does. A pair asked about with a variable fits; one with a symbol has that
one root, and the pairs of its arguments have been asked about or are still
to ask about. -/
structure FGo (S : Sorts) (c : Nat → Sorts.Conj) (K0 : Sorts.Conj) (u0 : Pat)
    (T Sn : List (Sorts.Conj × Pat)) : Prop where
  sub : ∀ x ∈ T ++ Sn, Sorts.Reach S K0 x.1 ∧ x.2 ∈ u0.subs ∧ x.2.firstOrder = true
  nd : Sn.Nodup
  need : ∀ x ∈ T ++ Sn, Sorts.fitsIn S c K0 u0 = true → Sorts.fitsIn S c x.1 x.2 = true
  done : ∀ x ∈ Sn, (∀ y, x.2 = .var y → Sorts.fitsIn S c x.1 x.2 = true) ∧
    ∀ f args, unspine x.2 [] = (.sym f, args) →
      Sorts.sole S x.1 [] = some (f, args.length) ∧ ∀ y ∈ fkids S x.1 f args, y ∈ Sn ∨ y ∈ T
  root : (K0, u0) ∈ Sn ∨ (K0, u0) ∈ T

/-- When nothing is left to ask about, the first pair fits. -/
theorem FGo.fits {S : Sorts} {c : Nat → Sorts.Conj} {K0 : Sorts.Conj} {u0 : Pat}
    {Sn : List (Sorts.Conj × Pat)} (h : FGo S c K0 u0 [] Sn) :
    Sorts.fitsIn S c K0 u0 = true := by
  have key : ∀ n, ∀ x ∈ Sn, x.2.size ≤ n → Sorts.fitsIn S c x.1 x.2 = true := by
    intro n
    induction n with
    | zero =>
      rintro ⟨K, p⟩ _ hs
      cases p <;> simp [Term.size] at hs
    | succ n ih =>
      intro x hx hs
      obtain ⟨hv, hk⟩ := h.done x hx
      by_cases hvar : ∃ y, x.2 = .var y
      · obtain ⟨y, hy⟩ := hvar
        exact hv y hy
      · have hfo := (h.sub x (by simp [hx])).2.2
        obtain ⟨f, hf⟩ := unspine_head x.2 [] hfo (fun v e => hvar ⟨v, e⟩)
        have hun : unspine x.2 [] = (.sym f, (unspine x.2 []).2) := Prod.ext hf rfl
        obtain ⟨hsole, hkids⟩ := hk f _ hun
        rw [fit_app c x.1 hun]
        refine ⟨hsole, fun y hy => ?_⟩
        rcases hkids y hy with hy' | hy'
        · refine ih y hy' ?_
          have hmem : y.2 ∈ (unspine x.2 []).2 := (List.of_mem_zip hy).2
          rcases unspine_mem x.2 [] y.2 hmem with h0 | ⟨-, h2, -⟩
          · cases h0
          · omega
        · cases hy'
  rcases h.root with hr | hr
  · exact key _ _ hr (Nat.le_refl _)
  · cases hr

/-- A pair found among the pairs asked about is dropped. -/
theorem FGo.skip {S : Sorts} {c : Nat → Sorts.Conj} {K0 : Sorts.Conj} {u0 : Pat}
    {x : Sorts.Conj × Pat} {T Sn : List (Sorts.Conj × Pat)} (h : FGo S c K0 u0 (x :: T) Sn)
    (hx : x ∈ Sn) : FGo S c K0 u0 T Sn := by
  refine ⟨fun y hy => h.sub y ?_, h.nd, fun y hy => h.need y ?_, fun y hy => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_cons] at hy ⊢; tauto
  · simp only [List.mem_append, List.mem_cons] at hy ⊢; tauto
  · obtain ⟨h1, h2⟩ := h.done y hy
    refine ⟨h1, fun f args hu => ?_⟩
    obtain ⟨h3, h4⟩ := h2 f args hu
    refine ⟨h3, fun z hz => ?_⟩
    rcases h4 z hz with hz' | hz'
    · exact .inl hz'
    · rcases List.mem_cons.1 hz' with rfl | hz'
      · exact .inl hx
      · exact .inr hz'
  · rcases h.root with hr | hr
    · exact .inl hr
    · rcases List.mem_cons.1 hr with e | hr
      · exact .inl (e ▸ hx)
      · exact .inr hr

/-- A new pair is asked about: it passes its own test, and the pairs of its
arguments are put on the list. -/
theorem FGo.step {S : Sorts} {c : Nat → Sorts.Conj} {K0 : Sorts.Conj} {u0 : Pat}
    {x : Sorts.Conj × Pat} {T T' Sn : List (Sorts.Conj × Pat)} (h : FGo S c K0 u0 (x :: T) Sn)
    (hx : x ∉ Sn)
    (hT : ∀ y ∈ T', y ∈ T ∨ ((Sorts.Reach S K0 y.1 ∧ y.2 ∈ u0.subs ∧ y.2.firstOrder = true) ∧
      (Sorts.fitsIn S c x.1 x.2 = true → Sorts.fitsIn S c y.1 y.2 = true)))
    (hT' : ∀ y ∈ T, y ∈ T')
    (hv : ∀ y, x.2 = .var y → Sorts.fitsIn S c x.1 x.2 = true)
    (hk : ∀ f args, unspine x.2 [] = (.sym f, args) →
      Sorts.sole S x.1 [] = some (f, args.length) ∧ ∀ y ∈ fkids S x.1 f args, y ∈ T') :
    FGo S c K0 u0 T' (x :: Sn) := by
  have hxs := h.sub x (by simp)
  have hxn := h.need x (by simp)
  refine ⟨fun y hy => ?_, List.nodup_cons.2 ⟨hx, h.nd⟩, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · rcases List.mem_append.1 hy with hy | hy
    · rcases hT y hy with hy | hy
      · exact h.sub y (by simp [hy])
      · exact hy.1
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hxs
      · exact h.sub y (by simp [hy])
  · intro h0
    rcases List.mem_append.1 hy with hy | hy
    · rcases hT y hy with hy | hy
      · exact h.need y (by simp [hy]) h0
      · exact hy.2 (hxn h0)
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hxn h0
      · exact h.need y (by simp [hy]) h0
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨hv, fun f args hu => ⟨(hk f args hu).1, fun z hz => .inr ((hk f args hu).2 z hz)⟩⟩
    · obtain ⟨h1, h2⟩ := h.done y hy
      refine ⟨h1, fun f args hu => ?_⟩
      obtain ⟨h3, h4⟩ := h2 f args hu
      refine ⟨h3, fun z hz => ?_⟩
      rcases h4 z hz with hz' | hz'
      · exact .inl (List.mem_cons_of_mem _ hz')
      · rcases List.mem_cons.1 hz' with rfl | hz'
        · exact .inl List.mem_cons_self
        · exact .inr (hT' z hz')
  · rcases h.root with hr | hr
    · exact .inl (List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.1 hr with e | hr
      · exact .inl (e ▸ List.mem_cons_self)
      · exact .inr (hT' _ hr)

open Classical in
/-- What the pairs not yet asked about may still cost. -/
noncomputable def owedF (Univ : Finset (Sorts.Conj × Pat)) (Sn : List (Sorts.Conj × Pat))
    (X : Pat → Nat) : Nat :=
  (Univ.filter (· ∉ Sn)).sum fun x => X x.2

theorem owedF_cons {Univ : Finset (Sorts.Conj × Pat)} {Sn : List (Sorts.Conj × Pat)}
    {X : Pat → Nat} {x : Sorts.Conj × Pat} (hx : x ∈ Univ) (hn : x ∉ Sn) :
    owedF Univ (x :: Sn) X + X x.2 = owedF Univ Sn X := by
  classical
  unfold owedF
  have e : Univ.filter (· ∉ x :: Sn) = (Univ.filter (· ∉ Sn)).erase x := by
    ext y
    simp only [Finset.mem_filter, List.mem_cons, not_or, Finset.mem_erase]
    tauto
  rw [e]
  exact Finset.sum_erase_add _ _ (Finset.mem_filter.2 ⟨hx, hn⟩)

theorem owedF_le (Univ : Finset (Sorts.Conj × Pat)) (Sn : List (Sorts.Conj × Pat))
    (X : Pat → Nat) : owedF Univ Sn X ≤ Univ.sum fun x => X x.2 := by
  classical
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem seen_length_le {Univ : Finset (Sorts.Conj × Pat)} {Sn : List (Sorts.Conj × Pat)}
    (hnd : Sn.Nodup) (hs : ∀ x ∈ Sn, x ∈ Univ) : Sn.length ≤ Univ.card := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card (fun x hx => hs x (List.mem_toFinset.1 hx))

/-- The ticks dropping a pair that has been asked about may take. -/
def fskip (W : Nat) : Nat := 2 * W + 2

/-- The ticks asking about a new pair may take, with the dropping of the
pairs of its arguments. -/
def fX (S : Sorts) (u r q W Ll : Nat) (p : Pat) : Nat :=
  3 * Ll + u * (inclCost S u q + 1) + soleAll S u r 0 + 8 * nargs p + nargs p * fskip W + 15

/-- The invariant of the loop of `fits`. -/
def FitInv (nm : Option Nat → Sym) (S : Sorts) (c : Nat → Sorts.Conj) (U : List Name)
    (K0 : Sorts.Conj) (u0 : Pat) (X : Pat → Nat) (W : Nat) (s0 : store.Store) (Bd : Nat)
    (x : store.Store × store.TermId × store.TermId × Bool × Bool) : Prop :=
  Inv x.1 ∧ Extends s0 x.1 ∧
    if x.2.2.2.2 = true then
      x.2.2.2.1 = true ∧ ∃ T Sn,
        Repr nm x.1.nodes.val x.2.1.val (encList (nm none) (T.map (fpair (nm none) U))) ∧
        Repr nm x.1.nodes.val x.2.2.1.val (encList (nm none) (Sn.map (fpair (nm none) U))) ∧
        FGo S c K0 u0 T Sn ∧
        x.1.ticks.val + T.length * fskip W + owedF (funiv S K0 u0) Sn X + 1 ≤ Bd
    else (x.2.2.2.1 = true ↔ Sorts.fitsIn S c K0 u0 = true) ∧ x.1.ticks.val ≤ Bd

/-- What the loop leaves. -/
def FitPost (S : Sorts) (c : Nat → Sorts.Conj) (K0 : Sorts.Conj) (u0 : Pat) (s0 : store.Store)
    (Bd : Nat) (y : Bool × store.Store) : Prop :=
  Inv y.2 ∧ Extends s0 y.2 ∧ (y.1 = true ↔ Sorts.fitsIn S c K0 u0 = true) ∧ y.2.ticks.val ≤ Bd

theorem fits_body_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (hUz : ∀ n ∈ U, n ≠ nm none)
    (L : List (Nat × Sorts.Conj)) (hL : ∀ v, Sub U (conjOf L v)) (K0 : Sorts.Conj)
    (hK0 : Sub U K0) (u0 : Pat) (W : Nat) (hW : (funiv S K0 u0).card ≤ W) (s0 : store.Store)
    (Bd : Nat) (hB : 40 * Bd + 100 ≤ Usize.max) (decls names es nil : store.TermId)
    (hd : Repr nm s0.nodes.val decls.val sp)
    (hU : Repr nm s0.nodes.val names.val (namesPat (nm none) U))
    (hes : Repr nm s0.nodes.val es.val (encVarEntries nm U L))
    (hnil : Repr nm s0.nodes.val nil.val (.sym (nm none)))
    (s : store.Store) (todo seen : store.TermId) (ok go : Bool)
    (h : FitInv nm S (conjOf L) U K0 u0 (fX S U.length r q W L.length) W s0 Bd
      (s, todo, seen, ok, go)) :
    sorts.fits_loop.body decls names es nil s todo seen ok go ⦃ r' =>
      match r' with
      | .done y => FitPost S (conjOf L) K0 u0 s0 Bd y
      | .cont x => FitInv nm S (conjOf L) U K0 u0 (fX S U.length r q W L.length) W s0 Bd x ∧
          s.ticks.val < x.1.ticks.val ⦄ := by
  unfold sorts.fits_loop.body
  obtain ⟨hI, hE, hrest⟩ := h
  cases go with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hrest ⊢
    simp only [WP.spec_ok]
    exact ⟨hI, hE, hrest.1, hrest.2⟩
  | true =>
    simp only [↓reduceIte] at hrest ⊢
    obtain ⟨rfl, T, Sn, rT, rS, hG, hc⟩ := hrest
    have hN : NodesOK s.nodes.val := hI.nodesOK
    have hsk : fskip W = 2 * W + 2 := rfl
    have hSnU : ∀ x ∈ Sn, x ∈ funiv S K0 u0 := fun x hx => by
      obtain ⟨h1, h2, -⟩ := hG.sub x (List.mem_append_right _ hx)
      exact Finset.mem_product.2 ⟨Sorts.mem_reachSet.2 h1, h2⟩
    have hSlen : Sn.length ≤ W := Nat.le_trans (seen_length_le hG.nd hSnU) hW
    cases T with
    | nil =>
      step with uncons_repr s todo hI.toWf (p := Term.sym (nm none)) rT
        (by unfold Room; omega) as ⟨o, s1, hK0', hu0⟩
      have K1 : Kept s s1 1 := hK0'.kept hI
      have ht1 := K1.ticks
      subst hu0
      have hx1 : Extends s s1 := Extends.of_eq K1.nodes (by omega)
      simp only [WP.spec_ok]
      refine ⟨⟨K1.inv, hE.trans hx1, ?_⟩,
        by show s.ticks.val < s1.ticks.val; omega⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨⟨fun _ => hG.fits, fun _ => by simp⟩, by simp only [List.length_nil] at hc; omega⟩
    | cons x T' =>
      step with uncons_repr s todo hI.toWf
        (p := Term.app (fpair (nm none) U x) (encList (nm none) (T'.map (fpair (nm none) U)))) rT
        (by unfold Room; omega) as ⟨o, s1, hK0', hu0⟩
      have K1 : Kept s s1 1 := hK0'.kept hI
      have ht1 := K1.ticks
      obtain ⟨pair, rest, rfl, rp, rrest⟩ := hu0
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hc
      obtain ⟨hxR, hxs, hxfo⟩ := hG.sub x (by simp)
      have hxU : Sub U x.1 := sub_of_reach hC hK0 hxR
      have hxUniv : x ∈ funiv S K0 u0 :=
        Finset.mem_product.2 ⟨Sorts.mem_reachSet.2 hxR, hxs⟩
      have hxneed := hG.need x (by simp)
      simp only
      step with among_spec hC.inj (Sn.map (fpair (nm none) U)) s1 pair seen
        (tn := fpair (nm none) U x) K1.inv (by rw [K1.nodes]; exact rp)
        (by rw [K1.nodes]; exact rS) (by simp only [List.length_map]; unfold Room; omega)
        as ⟨b, s2, hI2, hn2', htb2, ht2, hm2, hres⟩
      simp only [List.length_map] at ht2
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hn2', K1.nodes]
      have hx2 : Extends s s2 := Extends.of_eq hn2 (by omega)
      have hin : fpair (nm none) U x ∈ Sn.map (fpair (nm none) U) ↔ x ∈ Sn := by
        constructor
        · intro h
          obtain ⟨y, hy, e⟩ := List.mem_map.1 h
          have hyU : Sub U y.1 := sub_of_reach hC hK0 (hG.sub y (List.mem_append_right _ hy)).1
          rw [← fpair_inj hyU hxU e]
          exact hy
        · exact fun h => List.mem_map.2 ⟨x, h, rfl⟩
      by_cases hseen : x ∈ Sn
      · have hb : b = true := by rw [hres]; simpa using hin.2 hseen
        subst hb
        simp only [↓reduceIte, WP.spec_ok]
        refine ⟨⟨hI2, hE.trans hx2, ?_⟩, by show s.ticks.val < s2.ticks.val; omega⟩
        simp only [↓reduceIte, true_and]
        exact ⟨T', Sn, by rw [hn2]; exact rrest, by rw [hn2]; exact rS, hG.skip hseen, by omega⟩
      · have hb : b = false := by
          rw [hres]
          simpa using fun h => hseen (hin.1 h)
        subst hb
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hX := owedF_cons (X := fX S U.length r q W L.length) hxUniv hseen
        have hXd : fX S U.length r q W L.length x.2 = 3 * L.length +
            U.length * (inclCost S U.length q + 1) + soleAll S U.length r 0 + 8 * nargs x.2 +
            nargs x.2 * fskip W + 15 := rfl
        step with alloc_spec s2 (.App pair seen) hI2
          ⟨by rw [hn2]; exact rp.lt, by rw [hn2]; exact rS.lt⟩ (by unfold Room; omega)
          as ⟨seen1, s3, hI3, ht3, htb3, hx3, hid3⟩
        simp only [norm] at hid3
        have hx03 : Extends s s3 := hx2.trans hx3
        have rS1 : Repr nm s3.nodes.val seen1.val
            (encList (nm none) ((x :: Sn).map (fpair (nm none) U))) :=
          .app hid3 (hx03.repr rp) (hx03.repr rS)
        step with uncons_repr s3 pair hI3.toWf (p := Term.app (cpat (nm none) U x.1) x.2)
          (hx03.repr rp) (by unfold Room; omega) as ⟨o1, s4, hK4, hu4⟩
        have K4 : Kept s3 s4 1 := hK4.kept hI3
        have ht4 := K4.ticks
        obtain ⟨k, u, rfl, rk, ru⟩ := hu4
        simp only
        have hx04 : Extends s s4 := hx03.trans (Extends.of_eq K4.nodes (by omega))
        step with is_var_w s4 u K4.inv.toWf (by rw [K4.nodes]; exact ru) (by unfold Room; omega)
          as ⟨b1, s5, hb1, hK5⟩
        have K5 : Kept s4 s5 1 := hK5.kept K4.inv
        have ht5 := K5.ticks
        have hx05 : Extends s s5 := hx04.trans (Extends.of_eq K5.nodes (by omega))
        have rk5 : Repr nm s5.nodes.val k.val (cpat (nm none) U x.1) := by
          rw [K5.nodes, K4.nodes]; exact rk
        have ru5 : Repr nm s5.nodes.val u.val x.2 := by rw [K5.nodes, K4.nodes]; exact ru
        have rS5 : Repr nm s5.nodes.val seen1.val
            (encList (nm none) ((x :: Sn).map (fpair (nm none) U))) := by
          rw [K5.nodes, K4.nodes]; exact rS1
        by_cases hv : ∃ v, x.2 = .var v
        · have hb1' : b1 = true := hb1.2 hv
          subst hb1'
          obtain ⟨v, hxv⟩ := hv
          simp only [↓reduceIte]
          have hvar : VarAt s5.nodes.val u.val v := by
            rw [hxv] at ru5
            cases ru5 with
            | var h => exact h
          step with conj_at_spec s5 es u L K5.inv hvar ((hE.trans hx05).repr hes)
            (by unfold Room; omega) as ⟨c6, s6, hI6, hx6, ht6, rc6⟩
          have hx06 := hx05.trans hx6
          have h56 := hx6.ticks_le
          unfold cpat at rc6
          have hml : (conjList U (· ∈ conjOf L v)).length * (inclCost S U.length q + 1) ≤
              U.length * (inclCost S U.length q + 1) :=
            Nat.mul_le_mul_right _ (conjList_length_le _ _)
          step with all_included_loop_spec hC hq x.1 hxU (conjList U (· ∈ conjOf L v)) s6 decls
            names k c6 hI6 ((hE.trans hx06).repr hd) ((hE.trans hx06).repr hU) (hx6.repr rk5) rc6
            (fun m hm => hUz m (mem_conjList.1 hm).1) (by unfold Room; omega)
            as ⟨b2, s7, hI7, hx7, ht7, hb2⟩
          have h67 := hx7.ticks_le
          have hfit : Sorts.fitsIn S (conjOf L) x.1 x.2 = true ↔ b2 = true := by
            rw [hxv, fit_var, hb2]
            constructor
            · intro h m hm
              exact h m (mem_conjList.1 hm).2
            · intro h m hm
              exact h m (mem_conjList.2 ⟨hL v m hm, hm⟩)
          by_cases hb2t : b2 = true
          · subst hb2t
            simp only [↓reduceIte, WP.spec_ok]
            refine ⟨⟨hI7, hE.trans (hx06.trans hx7), ?_⟩,
              by show s.ticks.val < s7.ticks.val; omega⟩
            simp only [↓reduceIte, true_and]
            refine ⟨T', x :: Sn, (hx06.trans hx7).repr rrest, hx7.repr (hx6.repr rS5),
              hG.step hseen (fun y hy => .inl hy) (fun y hy => hy) (fun y _ => hfit.2 rfl)
                (fun f args hu => by
                  have h2 : (unspine x.2 []).1 = .sym f := congrArg Prod.fst hu
                  rw [hxv] at h2
                  simp [unspine] at h2), by omega⟩
          · have hb2f : b2 = false := by
              cases b2 with
              | false => rfl
              | true => exact absurd rfl hb2t
            subst hb2f
            simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
            refine ⟨⟨hI7, hE.trans (hx06.trans hx7), ?_⟩,
              by show s.ticks.val < s7.ticks.val; omega⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨⟨fun h => h.elim, fun h => ?_⟩, by omega⟩
            exact Bool.noConfusion (hfit.1 (hxneed h))
        · have hb1' : b1 = false := by
            cases b1 with
            | false => rfl
            | true => exact absurd (hb1.1 rfl) hv
          subst hb1'
          have hnv : ∀ v, x.2 ≠ .var v := fun v e => hv ⟨v, e⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          obtain ⟨f, hf⟩ := unspine_head x.2 [] hxfo hnv
          have hun : unspine x.2 [] = (.sym f, (unspine x.2 []).2) := Prod.ext hf rfl
          have hlen : (unspine x.2 []).2.length = nargs x.2 := by
            simpa using unspine_length x.2 []
          generalize hargs : (unspine x.2 []).2 = args at hun hlen
          rw [← hlen] at hXd
          step with spine_spec s5 u K5.inv.toWf ru5 (by unfold Room; omega)
            as ⟨head, argsI, s6, hR6, rhead, rargs⟩
          rw [hf] at rhead
          rw [hargs] at rargs
          rw [← hlen] at hR6
          have ht6 := hR6.ticks
          have hI6 : Inv s6 := ⟨hR6.wf, by rw [hR6.stk]; exact K5.inv.empty⟩
          have hx06 : Extends s s6 := hx05.trans hR6.ext
          have h56 := hR6.ext.ticks_le
          have rnil : Repr nm s6.nodes.val nil.val
              (encList (nm none) (([] : List GTerm).map GTerm.toPat)) :=
            (hE.trans hx06).repr hnil
          have hss : Sorts.sumSize [] = 0 := rfl
          step with sole_root_spec hC hr x.1 [] hxU s6 decls names k nil hI6
            ((hE.trans hx06).repr hd) ((hE.trans hx06).repr hU) (hR6.ext.repr rk5) rnil
            (by rw [hss]; unfold Room; omega) as ⟨o2, s7, hI7, hx7, ht7, hpost⟩
          rw [hss] at ht7
          have hx07 := hx06.trans hx7
          have h67 := hx7.ticks_le
          cases hsl : Sorts.sole S x.1 [] with
          | none =>
            rw [hsl] at hpost
            simp only at hpost
            subst hpost
            simp only [WP.spec_ok]
            refine ⟨⟨hI7, hE.trans hx07, ?_⟩, by show s.ticks.val < s7.ticks.val; omega⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨⟨fun h => (by simp at h), fun h => ?_⟩, by omega⟩
            have := ((fit_app (conjOf L) x.1 hun).1 (hxneed h)).1
            rw [hsl] at this
            cases this
          | some κ =>
            rw [hsl] at hpost
            obtain ⟨fi, kids, rfl, rfi, rkids⟩ := hpost
            simp only
            step with same_spec s7 fi head hI7 (by unfold Room; omega) as ⟨b2, s8, hb2, K8⟩
            have ht8 := K8.ticks
            have hx08 : Extends s s8 := hx07.trans (Extends.of_eq K8.nodes (by omega))
            have rhead7 : Repr nm s7.nodes.val head.val (.sym f) := hx7.repr rhead
            by_cases e : fi.val = head.val
            · have hb2' : b2 = true := by simp [hb2, e]
              subst hb2'
              have hκ1 : κ.1 = f := by
                rw [e] at rfi
                have := rfi.unique rhead7
                simpa using this
              simp only [↓reduceIte]
              step with same_len_spec args ((altOf S x.1 κ.1 κ.2).map (cpat (nm none) U)) s8
                argsI kids K8.inv.toWf (by rw [K8.nodes]; exact hx7.repr rargs)
                (by rw [K8.nodes]; exact rkids) (by unfold Room; omega)
                as ⟨r9, hsame, hR9⟩
              obtain ⟨same1, s9⟩ := r9
              simp only at hsame hR9
              have ht9 := hR9.ticks
              have hI9 : Inv s9 := ⟨hR9.wf, by rw [hR9.stk]; exact K8.inv.empty⟩
              have hx09 : Extends s s9 := hx08.trans hR9.ext
              have h89 := hR9.ext.ticks_le
              simp only [List.length_map, length_altOf] at hsame
              by_cases hl : args.length = κ.2
              · have hs1 : same1 = true := by simp [hsame, hl]
                subst hs1
                have hκ : κ = (f, args.length) := Prod.ext hκ1 hl.symm
                subst hκ
                simp only [bind_ok, uncurry, ↓reduceIte]
                step with pairs_onto_loop_spec (U := U) (altOf S x.1 f args.length) args s9 kids
                  argsI rest T' hI9 (length_altOf _ _ _ _)
                  (hR9.ext.repr (by rw [K8.nodes]; exact rkids))
                  (hR9.ext.repr (by rw [K8.nodes]; exact hx7.repr rargs)) (hx09.repr rrest)
                  (by rw [length_altOf]; unfold Room; omega)
                  as ⟨todo1, s10, hI10, hx10, ht10, rtodo⟩
                rw [length_altOf] at ht10
                have h910 := hx10.ticks_le
                refine ⟨⟨hI10, hE.trans (hx09.trans hx10), ?_⟩,
                  by show s.ticks.val < s10.ticks.val; omega⟩
                simp only [↓reduceIte, true_and]
                have hx510 : Extends s5 s10 :=
                  ((hR6.ext.trans hx7).trans (Extends.of_eq K8.nodes (by omega))).trans
                    (hR9.ext.trans hx10)
                refine ⟨(fkids S x.1 f args).reverse ++ T', x :: Sn, rtodo, hx510.repr rS5,
                  hG.step hseen ?_ (fun y hy => List.mem_append_right _ hy)
                    (fun y hy => absurd hy (hnv y)) ?_, ?_⟩
                · intro y hy
                  rcases List.mem_append.1 hy with hy | hy
                  · have hy' : y ∈ fkids S x.1 f args := List.mem_reverse.1 hy
                    refine .inr ⟨⟨?_, ?_, ?_⟩, fun h => ((fit_app (conjOf L) x.1 hun).1 h).2 y hy'⟩
                    · obtain ⟨i, hi, e'⟩ := List.mem_map.1 (List.of_mem_zip hy').1
                      rw [← e']
                      exact .step hxR (sole_kid hsl (List.mem_range.1 hi))
                    · have hmem : y.2 ∈ (unspine x.2 []).2 := by
                        rw [hargs]; exact (List.of_mem_zip hy').2
                      rcases unspine_mem x.2 [] y.2 hmem with h0 | ⟨h1, -, -⟩
                      · cases h0
                      · exact Term.subs_trans hxs h1
                    · have hmem : y.2 ∈ (unspine x.2 []).2 := by
                        rw [hargs]; exact (List.of_mem_zip hy').2
                      rcases unspine_mem x.2 [] y.2 hmem with h0 | ⟨-, -, h3⟩
                      · cases h0
                      · exact h3 hxfo
                  · exact .inl hy
                · intro f' args' hu'
                  rw [hun] at hu'
                  simp only [Prod.mk.injEq, Term.sym.injEq] at hu'
                  obtain ⟨rfl, rfl⟩ := hu'
                  exact ⟨hsl, fun y hy => List.mem_append_left _ (List.mem_reverse.2 hy)⟩
                · simp only [List.length_append, List.length_reverse, fkids, List.length_zip,
                    length_altOf, Nat.min_self, Nat.add_mul]
                  omega
              · have hs1 : same1 = false := by simp [hsame, hl]
                subst hs1
                simp only [bind_ok, uncurry, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
                refine ⟨⟨hI9, hE.trans hx09, ?_⟩, by show s.ticks.val < s9.ticks.val; omega⟩
                simp only [Bool.false_eq_true, ↓reduceIte]
                refine ⟨⟨fun h => (by simp at h), fun h => ?_⟩, by omega⟩
                have := ((fit_app (conjOf L) x.1 hun).1 (hxneed h)).1
                rw [hsl] at this
                simp only [Option.some.injEq] at this
                rw [this] at hl
                exact hl rfl
            · have hb2' : b2 = false := by simp [hb2, e]
              subst hb2'
              simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry, WP.spec_ok]
              refine ⟨⟨K8.inv, hE.trans hx08, ?_⟩, by show s.ticks.val < s8.ticks.val; omega⟩
              simp only [Bool.false_eq_true, ↓reduceIte]
              refine ⟨⟨fun h => (by simp at h), fun h => ?_⟩, by omega⟩
              have := ((fit_app (conjOf L) x.1 hun).1 (hxneed h)).1
              rw [hsl] at this
              simp only [Option.some.injEq] at this
              rw [this] at rfi
              exact e (Repr.inj hC.inj hI7.nodesOK rfi rhead7)

/-- The ticks `fits` may take. -/
noncomputable def fitsCost (S : Sorts) (u Ll r q : Nat) (u0 : Pat) : Nat :=
  fskip (r * u0.subs.card) +
    r * (u0.subs.sum fun p => fX S u r q (r * u0.subs.card) Ll p) + 4

/-- `fits` decides `Sorts.fitsIn`. -/
theorem fits_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) {r q : Nat}
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ r)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) (hUz : ∀ n ∈ U, n ≠ nm none)
    (L : List (Nat × Sorts.Conj)) (hL : ∀ v, Sub U (conjOf L v)) {K0 : Sorts.Conj}
    (hK0 : Sub U K0) {u0 : Pat} (hfo : u0.firstOrder = true) (s : store.Store)
    (decls names es k0 ui : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hes : Repr nm s.nodes.val es.val (encVarEntries nm U L))
    (hk : Repr nm s.nodes.val k0.val (cpat (nm none) U K0))
    (hu : Repr nm s.nodes.val ui.val u0)
    (hroom : Room s (fitsCost S U.length L.length r q u0)) :
    sorts.fits s decls names es k0 ui ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + fitsCost S U.length L.length r q u0 ∧
        (b = true ↔ Sorts.fitsIn S (conjOf L) K0 u0 = true) ⦄ := by
  unfold sorts.fits sorts.fits_loop
  have hroom' := hroom
  unfold Room at hroom'
  unfold fitsCost at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  step with alloc_spec s1 (.App k0 ui) hI1 ⟨(hx1.repr hk).lt, (hx1.repr hu).lt⟩
    (by unfold Room; omega) as ⟨first, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr2
  have hx02 : Extends s s2 := hx1.trans hx2
  have rnil2 : Repr nm s2.nodes.val nil.val (.sym (nm none)) := hx2.repr (.nil hr1)
  have rfirst : Repr nm s2.nodes.val first.val (fpair (nm none) U (K0, u0)) :=
    .app hr2 (hx02.repr hk) (hx02.repr hu)
  step with alloc_spec s2 (.App first nil) hI2 ⟨rfirst.lt, rnil2.lt⟩
    (by unfold Room; omega) as ⟨todo, s3, hI3, ht3, htb3, hx3, hr3⟩
  simp only [norm] at hr3
  have hx03 : Extends s s3 := hx02.trans hx3
  have rnil3 : Repr nm s3.nodes.val nil.val (.sym (nm none)) := hx3.repr rnil2
  let Bd := s.ticks.val + fitsCost S U.length L.length r q u0
  have hW : (funiv S K0 u0).card ≤ (r * u0.subs.card) := by
    unfold funiv
    rw [Finset.card_product]
    exact Nat.mul_le_mul_right _ (hr K0)
  have hsum : owedF (funiv S K0 u0) [] (fX S U.length r q (r * u0.subs.card) L.length) ≤ r * (u0.subs.sum fun p => (fX S U.length r q (r * u0.subs.card) L.length) p) := by
    refine Nat.le_trans (owedF_le _ _ _) ?_
    unfold funiv
    rw [Finset.sum_product]
    simp only [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (hr K0)
  have hloop := loop.spec_decr_nat
    (fun x : store.Store × store.TermId × store.TermId × Bool × Bool => Bd + 1 - x.1.ticks.val)
    (fun x => FitInv nm S (conjOf L) U K0 u0 (fX S U.length r q (r * u0.subs.card) L.length) (r * u0.subs.card) s3 Bd x)
    (fun y : Bool × store.Store => FitPost S (conjOf L) K0 u0 s3 Bd y)
    (fun x : store.Store × store.TermId × store.TermId × Bool × Bool =>
      sorts.fits_loop.body decls names es nil x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (s3, todo, nil, true, true)
    (by
      rintro ⟨y, td, sn, ok, go⟩ hinv
      refine WP.spec_mono (fits_body_spec hC hr hq hUz L hL K0 hK0 u0 (r * u0.subs.card) hW s3 Bd
        (by unfold Bd fitsCost; omega) decls names es nil (hx03.repr hd) (hx03.repr hU)
        (hx03.repr hes) rnil3 y td sn ok go hinv) ?_
      intro r' hr'
      cases r' with
      | done z => exact hr'
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr'
        refine ⟨h1, ?_⟩
        obtain ⟨-, -, h3⟩ := h1
        have : x'.1.ticks.val ≤ Bd := by
          split at h3
          · obtain ⟨-, T, Sn, -, -, -, hc⟩ := h3; omega
          · exact h3.2
        simp only at h2 ⊢
        omega)
    ⟨hI3, Extends.refl s3, by
      simp only [↓reduceIte, true_and]
      refine ⟨[(K0, u0)], [], .app hr3 (hx3.repr rfirst) rnil3, rnil3, ⟨?_, List.nodup_nil,
        ?_, ?_, .inr (by simp)⟩, ?_⟩
      · intro x hx
        simp only [List.append_nil, List.mem_singleton] at hx
        subst hx
        exact ⟨.refl, Term.self_mem_subs _, hfo⟩
      · intro x hx h
        simp only [List.append_nil, List.mem_singleton] at hx
        subst hx
        exact h
      · intro x hx; cases hx
      · simp only [List.length_singleton, Nat.one_mul]
        unfold Bd fitsCost
        omega⟩
  refine WP.spec_mono hloop ?_
  rintro ⟨b, s'⟩ ⟨hI', hx', hb, ht'⟩
  exact ⟨hI', hx03.trans hx', ht', hb⟩

end RwLogVerified
