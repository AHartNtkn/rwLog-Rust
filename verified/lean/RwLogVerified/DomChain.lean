/-
# The charges of the sorts domain, and the chain test

A machine may hold a representative in more than one way: with the mark or
without it, and with the exclusions of its store listed in any order
(`Form`, `HeldAs`). What an operation spends depends on how its arguments are
held. Its charge is the most it spends over the ways they may be held
(`most`), which are finitely many (`heldAs_finite`), so the charge is a
function of the representatives alone.

`dom::composable` composes a list of packed representatives from the left
(`packForm`), and says whether every composition relates something
(`Domain.composable` of `Sorts.dom`).
-/
import RwLogVerified.Dom
import RwLogVerified.SpanRep

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The ways a representative is held -/

/-- A way a machine holds a representative: a canonical store, a mark, and
a listing of the exclusions of the store. -/
structure Form where
  r : Sorts.Raw
  f : Bool
  Y : List Sorts.Binds

/-- The form is a way to hold the representative: its store is the folded
canonical store for its mark, and its listing has each exclusion once. -/
def HeldAs {S : Sorts} (ρ : Sorts.Rep S) (m : Form) : Prop :=
  Sorts.FoldOf S (ρ.orient m.f).1 m.r ∧ m.Y.Nodup ∧ m.Y.toFinset = m.r.x

theorem OrAt.heldAs {S : Sorts} {U : List Name} {nodes : List store.Node} {a : dom.Oriented}
    {ρ : Sorts.Rep S} {r : Sorts.Raw} {Y : List Sorts.Binds} (h : OrAt nm U nodes a ρ r Y) :
    HeldAs ρ ⟨r, a.flip, Y⟩ :=
  ⟨h.fold, h.rep.nd, h.rep.y⟩

/-- A representative is held in finitely many ways. -/
theorem heldAs_finite {S : Sorts} (ρ : Sorts.Rep S) : {m : Form | HeldAs ρ m}.Finite := by
  have hY : ∀ X : Finset Sorts.Binds,
      {Y : List Sorts.Binds | Y.Nodup ∧ Y.toFinset = X}.Finite := fun X =>
    (List.finite_toSet X.toList.permutations).subset fun Y hY =>
      List.mem_permutations.2 (List.perm_of_nodup_nodup_toFinset_eq hY.1 X.nodup_toList
        (by rw [hY.2, Finset.toList_toFinset]))
  have hr : ∀ f, {r | Sorts.FoldOf S (ρ.orient f).1 r}.Finite := fun f =>
    Set.Subsingleton.finite fun r hr r' hr' => Sorts.FoldOf.eq ρ.wf hr hr'
  refine ((Set.finite_univ (α := Bool)).biUnion fun f _ => (hr f).biUnion fun r _ =>
    (hY r.x).image (fun Y => (⟨r, f, Y⟩ : Form))).subset ?_
  rintro ⟨r, f, Y⟩ ⟨h1, h2, h3⟩
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨f, Set.mem_univ _, r, h1, Y, ⟨h2, h3⟩, rfl⟩

/-- The most a charge is over the ways a representative is held. -/
noncomputable def most {S : Sorts} (ρ : Sorts.Rep S) (c : Form → Nat) : Nat :=
  sSup (c '' {m | HeldAs ρ m})

theorem le_most {S : Sorts} {ρ : Sorts.Rep S} {m : Form} (h : HeldAs ρ m) (c : Form → Nat) :
    c m ≤ most ρ c :=
  le_csSup ((heldAs_finite ρ).image c).bddAbove ⟨m, h, rfl⟩

theorem le_most₂ {S : Sorts} {ρa ρb : Sorts.Rep S} {ma mb : Form} (ha : HeldAs ρa ma)
    (hb : HeldAs ρb mb) (c : Form → Form → Nat) :
    c ma mb ≤ most ρa fun ma => most ρb fun mb => c ma mb :=
  (le_most hb (c ma)).trans (le_most ha fun ma => most ρb (c ma))

/-! ## The charges -/

section Charges

variable (nm) (S : Sorts) (U : List Name) (rc q : Nat)

/-- The charge of `rep`. -/
noncomputable def repTicks (sp : Span) : Nat :=
  spanCost U.length sp + startCost nm S U.length (spanProbR sp) +
    normCharge nm S U rc q (spanProbR sp)

/-- What `compose` may spend on representatives held in two given ways. -/
noncomputable def composeAt (ma mb : Form) : Nat :=
  halvesCost nm U.length ma.r ma.Y mb.r mb.Y +
    startCost nm S U.length (composeProb U ma.r ma.f mb.r mb.f ma.Y mb.Y) +
    normCharge nm S U rc q (composeProb U ma.r ma.f mb.r mb.f ma.Y mb.Y)

/-- The charge of `compose`. -/
noncomputable def composeTicks (ρa ρb : Sorts.Rep S) : Nat :=
  most ρa fun ma => most ρb fun mb => composeAt nm S U rc q ma mb

/-- Every representative is held in some way: its store is normal, so it
has a folded canonical store, whose exclusions can be listed. -/
theorem heldAs_exists {S : Sorts} (ρ : Sorts.Rep S) : ∃ m, HeldAs ρ m := by
  have hn := (ρ.orient false).normal
  have hR : (ρ.orient false).1.Roomy S :=
    ⟨hn.toShaped, hn.sol_nonempty ρ.wf, fun _ hv => hn.infinite ρ.wf hv⟩
  exact ⟨⟨Sorts.foldRaw S (ρ.orient false).1, false, (Sorts.foldRaw S (ρ.orient false).1).x.toList⟩,
    Sorts.foldRaw_spec ρ.wf hR, Finset.nodup_toList _, Finset.toList_toFinset _⟩

/-- **A composition is charged a tick or more.** -/
theorem one_le_composeTicks (ρa ρb : Sorts.Rep S) : 1 ≤ composeTicks nm S U rc q ρa ρb := by
  obtain ⟨ma, ha⟩ := heldAs_exists ρa
  obtain ⟨mb, hb⟩ := heldAs_exists ρb
  have h := le_most₂ ha hb (composeAt nm S U rc q)
  have h8 : 8 ≤ composeAt nm S U rc q ma mb := by
    unfold composeAt halvesCost
    omega
  exact le_trans (by omega) h

/-- What `meet` may spend on representatives held in two given ways. -/
noncomputable def meetAt (ma mb : Form) : Nat :=
  halvesCost nm U.length ma.r ma.Y mb.r mb.Y + 2 +
    startCost nm S U.length (meetProb U ma.r ma.f mb.r mb.f ma.Y mb.Y) +
    normCharge nm S U rc q (meetProb U ma.r ma.f mb.r mb.f ma.Y mb.Y)

/-- The charge of `meet`. -/
noncomputable def meetTicks (ρa ρb : Sorts.Rep S) : Nat :=
  most ρa fun ma => most ρb fun mb => meetAt nm S U rc q ma mb

/-- The charge of `right`. -/
noncomputable def rightTicks (ρ : Sorts.Rep S) : Nat :=
  most ρ fun m => rightCost nm S U rc q m.r m.f m.Y

/-- The charge of `left`. -/
noncomputable def leftTicks (ρ : Sorts.Rep S) : Nat :=
  most ρ fun m => rightCost nm S U rc q m.r (!m.f) m.Y

/-- What `eq` may spend on representatives held in two given ways. -/
noncomputable def eqAt (ρb : Sorts.Rep S) (ma mb : Form) : Nat :=
  eqCost nm S U rc q ma.f mb.f ma.Y mb.r mb.Y (foldCard (ρb.orient ma.f))

/-- The charge of `eq`. -/
noncomputable def eqTicks (ρa ρb : Sorts.Rep S) : Nat :=
  most ρa fun ma => most ρb fun mb => eqAt nm S U rc q ρb ma mb

/-- What `covers` may spend on representatives held in two given ways. -/
noncomputable def coversAt (ρa ρb : Sorts.Rep S) (ma mb : Form) : Nat :=
  domCoversCost nm U rc q ρa ρb ma.r ma.f mb.r mb.f ma.Y mb.Y

/-- The charge of `covers`. -/
noncomputable def coversTicks (ρa ρb : Sorts.Rep S) : Nat :=
  most ρa fun ma => most ρb fun mb => coversAt nm S U rc q ρa ρb ma mb

/-- The ticks the loop of `composable` may spend, from the representative
composed so far and those that are left. -/
noncomputable def chainTicks : Sorts.Rep S → List (Sorts.Rep S) → Nat
  | _, [] => 1
  | acc, y :: ys => 5 + composeTicks nm S U rc q acc y +
    match acc.compose y with
    | some w => chainTicks w ys
    | none => 0

/-- The charge of `composable`. -/
noncomputable def composableTicks : List (Sorts.Rep S) → Nat
  | [] => 1
  | x :: rest => 5 + chainTicks nm S U rc q x rest

end Charges

/-! ## A representative as one node -/

/-- The mark as a term. -/
def markPat (z : Sym) : Bool → Pat
  | false => .sym z
  | true => .app (.sym z) (.sym z)

/-- A held representative as one term: its mark applied to its pattern, its
conjunctions and its exclusions. -/
noncomputable def packForm (nm : Option Nat → RwLog.Sym) (U : List Name) (m : Form) : Pat :=
  .app (.app (.app (markPat (nm none) m.f) m.r.t)
    (encList (nm none) (m.r.c.map (cpat (nm none) U))))
    (encLL nm (m.Y.map (vals m.r.c.length)))

theorem Repr.sym_none_inv (hnm : Function.Injective nm) {nodes : List store.Node} {i : Nat}
    (h : Repr nm nodes i (.sym (nm none))) : nodes[i]? = some .Nil := by
  generalize ht : Term.sym (nm none) = t at h
  cases h with
  | var _ => cases ht
  | sym _ => cases hnm (Term.sym.inj ht)
  | nil hn => exact hn
  | app _ _ _ => cases ht

/-- `mark` writes the mark as a node. -/
theorem dom_mark_spec (s : store.Store) (fl : Bool) (hI : Inv s) (hroom : Room s 2) :
    dom.mark s fl ⦃ m s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 2 ∧
        Repr nm s'.nodes.val m.val (markPat (nm none) fl) ⦄ := by
  unfold dom.mark
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s .Nil hI trivial (by unfold Room; omega)
    as ⟨nil, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  have rnil : Repr nm s1.nodes.val nil.val (.sym (nm none)) := .nil hr1
  cases fl
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨hI1, hx1, by omega, rnil⟩
  · simp only [↓reduceIte]
    refine WP.spec_mono (alloc_spec s1 (.App nil nil) hI1 ⟨rnil.lt, rnil.lt⟩
      (by unfold Room; omega)) ?_
    rintro ⟨m, s2⟩ ⟨hI2, ht2, htb2, hx2, hr2⟩
    simp only [norm] at hr2
    exact ⟨hI2, hx1.trans hx2, by omega, .app hr2 (hx2.repr rnil) (hx2.repr rnil)⟩

/-- `pack` writes a held representative as one node. -/
theorem dom_pack_spec {U : List Name} (s : store.Store) (a : dom.Oriented) {r : Sorts.Raw}
    {Y : List Sorts.Binds} (hI : Inv s) (ha : RepAt nm U s.nodes.val a.rep r Y)
    (hroom : Room s 5) :
    dom.pack s a ⦃ p s' =>
      Inv s' ∧ Extends s s' ∧ s'.ticks.val ≤ s.ticks.val + 5 ∧
        Repr nm s'.nodes.val p.val (packForm nm U ⟨r, a.flip, Y⟩) ⦄ := by
  unfold dom.pack
  have hroom' := hroom
  unfold Room at hroom'
  step with dom_mark_spec (nm := nm) s a.flip hI (by unfold Room; omega)
    as ⟨m, s1, hI1, hx1, ht1, rm⟩
  step with alloc_spec s1 (.App m a.rep.t) hI1 ⟨rm.lt, (hx1.repr ha.t).lt⟩
    (by unfold Room; omega) as ⟨h, s3, hI3, ht3, htb3, hx3, hr3⟩
  simp only [norm] at hr3
  have rh := Repr.app hr3 (hx3.repr rm) (hx3.repr (hx1.repr ha.t))
  have hx03 := hx1.trans hx3
  step with alloc_spec s3 (.App h a.rep.c) hI3 ⟨rh.lt, (hx03.repr ha.c).lt⟩
    (by unfold Room; omega) as ⟨g, s4, hI4, ht4, htb4, hx4, hr4⟩
  simp only [norm] at hr4
  have rg := Repr.app hr4 (hx4.repr rh) (hx4.repr (hx03.repr ha.c))
  have hx04 := hx03.trans hx4
  refine WP.spec_mono (alloc_spec s4 (.App g a.rep.x) hI4 ⟨rg.lt, (hx04.repr ha.x).lt⟩
    (by unfold Room; omega)) ?_
  rintro ⟨p, s5⟩ ⟨hI5, ht5, htb5, hx5, hr5⟩
  simp only [norm] at hr5
  exact ⟨hI5, hx04.trans hx5, by omega,
    .app hr5 (hx5.repr rg) (hx5.repr (hx04.repr ha.x))⟩

/-- `unpack` reads a held representative back from its node. -/
theorem dom_unpack_spec (hnm : Function.Injective nm) {U : List Name} (s : store.Store)
    (p : store.TermId) {m : Form} (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val (packForm nm U m)) (hroom : Room s 4) :
    dom.unpack s p ⦃ o s' =>
      Kept s s' 4 ∧ o.flip = m.f ∧ Repr nm s.nodes.val o.rep.t.val m.r.t ∧
        Repr nm s.nodes.val o.rep.c.val (encList (nm none) (m.r.c.map (cpat (nm none) U))) ∧
        Repr nm s.nodes.val o.rep.x.val (encLL nm (m.Y.map (vals m.r.c.length))) ⦄ := by
  unfold dom.unpack
  have hroom' := hroom
  unfold Room at hroom'
  unfold packForm at hp
  obtain ⟨g, x, hn0, hg, hx⟩ := Repr.app_inv hp
  obtain ⟨h, c, hn1, hh, hc⟩ := Repr.app_inv hg
  obtain ⟨mk, t, hn2, hmk, ht⟩ := Repr.app_inv hh
  step with read_spec s p hI hp.lt (by unfold Room; omega) as ⟨nd, s1, hnd, hK1⟩
  rw [hn0] at hnd
  cases hnd
  have ht1 := hK1.ticks
  simp only
  step with read_spec s1 g hK1.inv (by rw [hK1.nodes]; exact hg.lt) (by unfold Room; omega)
    as ⟨nd2, s2, hnd2, hK2⟩
  rw [hK1.nodes, hn1] at hnd2
  cases hnd2
  have ht2 := hK2.ticks
  simp only
  step with read_spec s2 h hK2.inv (by rw [hK2.nodes, hK1.nodes]; exact hh.lt)
    (by unfold Room; omega) as ⟨nd3, s3, hnd3, hK3⟩
  rw [hK2.nodes, hK1.nodes, hn2] at hnd3
  cases hnd3
  have ht3 := hK3.ticks
  simp only
  step with read_spec s3 mk hK3.inv (by rw [hK3.nodes, hK2.nodes, hK1.nodes]; exact hmk.lt)
    (by unfold Room; omega) as ⟨nd4, s4, hnd4, hK4⟩
  rw [hK3.nodes, hK2.nodes, hK1.nodes] at hnd4
  have hkept : Kept s s4 4 :=
    ⟨by rw [hK4.nodes, hK3.nodes, hK2.nodes, hK1.nodes],
      by rw [hK4.tbl, hK3.tbl, hK2.tbl, hK1.tbl],
      by rw [hK4.ticks, hK3.ticks, hK2.ticks, hK1.ticks], hK4.inv⟩
  cases hf : m.f
  · rw [hf] at hmk
    rw [Repr.sym_none_inv hnm hmk] at hnd4
    cases hnd4
    simp only [WP.spec_ok]
    exact ⟨hkept, rfl, ht, hc, hx⟩
  · rw [hf] at hmk
    obtain ⟨a, b, hn3, -, -⟩ := Repr.app_inv hmk
    rw [hn3] at hnd4
    cases hnd4
    simp only [WP.spec_ok]
    exact ⟨hkept, rfl, ht, hc, hx⟩

/-! ## The chain test -/

section Chain

variable {S : Sorts} {sp : Pat} {U : List Name} {rc q : Nat}

theorem foldl_rep_none (ys : List (Sorts.Rep S)) :
    ys.foldl (fun (a : Option (Sorts.Rep S)) t => a.bind (·.compose t)) none = none := by
  induction ys with
  | nil => rfl
  | cons y ys ih => exact ih

abbrev DChainState := store.Store × dom.Oriented × store.TermId × Bool × Bool

/-- The invariant of the loop. -/
def DChainInv (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (rc q : Nat)
    (s0 : store.Store) (B : Nat) (R : Bool) : DChainState → Prop
  | (s, acc, rest, ok, go) => Inv s ∧ Extends s0 s ∧
    if go then ok = true ∧ ∃ (ρ : Sorts.Rep S) (r : Sorts.Raw) (Y : List Sorts.Binds)
        (ps : List (Sorts.Rep S × Form)),
        OrAt nm U s.nodes.val acc ρ r Y ∧ (∀ p ∈ ps, HeldAs p.1 p.2) ∧
        Repr nm s.nodes.val rest.val
          (encList (nm none) (ps.map fun p => packForm nm U p.2)) ∧
        ((ps.map Prod.fst).foldl (fun (a : Option (Sorts.Rep S)) t => a.bind (·.compose t))
          (some ρ)).isSome = R ∧
        s.ticks.val + chainTicks nm S U rc q ρ (ps.map Prod.fst) ≤ B
    else s.ticks.val ≤ B ∧ ok = R

def dchainMeasure : DChainState → Nat
  | (_, _, rest, _, go) => 2 * rest.val + if go then 1 else 0

def DChainBody (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name) (rc q : Nat)
    (s0 : store.Store) (B : Nat) (R : Bool) (m : Nat) :
    ControlFlow DChainState (Bool × store.Store) → Prop
  | .done (ok, s) => Inv s ∧ Extends s0 s ∧ s.ticks.val ≤ B ∧ ok = R
  | .cont x => DChainInv nm S U rc q s0 B R x ∧ dchainMeasure x < m

theorem dom_composable_body_spec (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (s0 : store.Store) (decls names : store.TermId)
    (hde : Repr nm s0.nodes.val decls.val sp)
    (hU : Repr nm s0.nodes.val names.val (namesPat (nm none) U)) (B : Nat) (R : Bool)
    (hB : 40 * B + 100 ≤ Usize.max) (st : store.Store) (acc : dom.Oriented)
    (rest : store.TermId) (ok go : Bool)
    (h : DChainInv nm S U rc q s0 B R (st, acc, rest, ok, go)) :
    dom.composable_loop.body decls names st acc rest ok go ⦃ r =>
      DChainBody nm S U rc q s0 B R (dchainMeasure (st, acc, rest, ok, go)) r ⦄ := by
  unfold dom.composable_loop.body
  obtain ⟨hI, hE0, h⟩ := h
  cases go with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    step*
    exact ⟨hI, hE0, h.1, h.2⟩
  | true =>
    simp only [↓reduceIte] at h ⊢
    obtain ⟨hok, ρ, r, Y, ps, hacc, hps, hrest, hR, hc⟩ := h
    subst hok
    have h1le : 1 ≤ chainTicks nm S U rc q ρ (ps.map Prod.fst) := by
      cases ps <;> simp [chainTicks]; omega
    step with read_spec st rest hI hrest.lt (by unfold Room; omega) as ⟨nd, s1, hnd, hK1⟩
    have ht1 := hK1.ticks
    have hn1 := hK1.nodes
    have hstop : (∀ a b, nd ≠ .App a b) →
        DChainBody nm S U rc q s0 B R (dchainMeasure (st, acc, rest, true, true))
          (ControlFlow.cont (s1, acc, rest, true, false)) := by
      intro hna
      have hys := encList_of_not_app hrest hnd hna
      have hys' : ps = [] := List.map_eq_nil_iff.1 hys
      subst hys'
      refine ⟨⟨hK1.inv, hE0.trans (Extends.of_eq hn1 (by omega)), ?_⟩, by simp [dchainMeasure]⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, by rw [← hR]; rfl⟩
    cases nd with
    | V0 => step*
    | VL a => step*
    | VR a => step*
    | Sym g => step*
    | Nil => step*
    | App h2 t2 =>
      obtain ⟨t, ts, hmap, hh2, ht2⟩ := encList_of_app hrest hnd
      obtain ⟨⟨ρy, my⟩, ps', rfl, hy, hys'⟩ := List.map_eq_cons_iff.1 hmap
      subst hy hys'
      have hheld : HeldAs ρy my := hps _ List.mem_cons_self
      have hlt : t2.val < rest.val := by
        have := hI.shape.fits _ _ hnd
        simp only [Fits] at this
        exact this.2
      simp only [List.map_cons, chainTicks] at hc
      simp only
      step with dom_unpack_spec hnm (U := U) s1 h2 hK1.inv (by rw [hn1]; exact hh2)
        (by unfold Room; omega) as ⟨y', s2, hK2, hfl, hyt, hyc, hyx⟩
      have ht2' := hK2.ticks
      have hn2 : s2.nodes.val = st.nodes.val := by rw [hK2.nodes, hn1]
      have hx02 : Extends st s2 := Extends.of_eq hn2 (by omega)
      have hy' : OrAt nm U s2.nodes.val y' ρy my.r my.Y :=
        ⟨by rw [hfl]; exact hheld.1, ⟨by rw [hK2.nodes]; exact hyt, by rw [hK2.nodes]; exact hyc,
          hheld.2.1, hheld.2.2, by rw [hK2.nodes]; exact hyx⟩⟩
      have hacc2 := hacc.extends hx02
      have hle : composeAt nm S U rc q ⟨r, acc.flip, Y⟩ ⟨my.r, y'.flip, my.Y⟩ ≤
          composeTicks nm S U rc q ρ ρy :=
        le_most₂ hacc2.heldAs hy'.heldAs (composeAt nm S U rc q)
      simp only [composeAt] at hle
      step with dom_compose_spec hnm hz hC hN hUS hr hq ρ ρy Y my.Y s2 decls names acc y'
        hK2.inv ((hE0.trans hx02).repr hde) ((hE0.trans hx02).repr hU) hacc2 hy'
        (by unfold Room; omega) as ⟨o, s3, hI3, hx3, ht3, hpost⟩
      have hst3 : Extends st s3 := hx02.trans hx3
      cases o with
      | none =>
        simp only [OrPost] at hpost
        step*
        refine ⟨⟨hI3, hE0.trans hst3, ?_⟩, by simp [dchainMeasure]⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨by omega, ?_⟩
        rw [← hR]
        simp only [List.map_cons, List.foldl_cons, Option.bind_some, hpost, foldl_rep_none]
        rfl
      | some zz =>
        obtain ⟨ρ', r', Y', hρ', hzz⟩ := hpost.at
        rw [hρ'] at hc
        simp only at hc
        step*
        refine ⟨⟨hI3, hE0.trans hst3, ?_⟩, by simp only [dchainMeasure, ↓reduceIte]; omega⟩
        simp only [↓reduceIte, true_and]
        refine ⟨ρ', r', Y', ps', hzz, fun p hp => hps p (List.mem_cons_of_mem _ hp),
          hst3.repr ht2, ?_, by omega⟩
        rw [← hR]
        simp only [List.map_cons, List.foldl_cons, Option.bind_some, hρ']

/-- `composable` decides whether a chain of representatives composes
(`Domain.composable` of `Sorts.dom`), from the list of them packed as they
are held. -/
theorem dom_composable_spec (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q)
    (ps : List (Sorts.Rep S × Form)) (hps : ∀ p ∈ ps, HeldAs p.1 p.2)
    (s : store.Store) (decls names xs : store.TermId) (hI : Inv s)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hxs : Repr nm s.nodes.val xs.val (encList (nm none) (ps.map fun p => packForm nm U p.2)))
    (hroom : Room s (composableTicks nm S U rc q (ps.map Prod.fst))) :
    dom.composable s decls names xs ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ b = (Sorts.dom S).composable (ps.map Prod.fst) ∧
        s'.ticks.val ≤ s.ticks.val + composableTicks nm S U rc q (ps.map Prod.fst) ⦄ := by
  unfold dom.composable dom.composable_loop
  have hroom' := hroom
  unfold Room at hroom'
  have h1le : 1 ≤ composableTicks nm S U rc q (ps.map Prod.fst) := by
    cases ps <;> simp [composableTicks]; omega
  step with read_spec s xs hI hxs.lt (by unfold Room; omega) as ⟨nd, s1, hnd, hK1⟩
  have ht1 := hK1.ticks
  have hn1 := hK1.nodes
  have hstop : (∀ a b, nd ≠ .App a b) → Inv s1 ∧ Extends s s1 ∧
      true = (Sorts.dom S).composable (ps.map Prod.fst) ∧
      s1.ticks.val ≤ s.ticks.val + composableTicks nm S U rc q (ps.map Prod.fst) := by
    intro hna
    have hys := encList_of_not_app hxs hnd hna
    have hys' : ps = [] := List.map_eq_nil_iff.1 hys
    subst hys'
    exact ⟨hK1.inv, Extends.of_eq hn1 (by omega), rfl, by omega⟩
  cases nd with
  | V0 => step*; exact hstop (by simp)
  | VL a => step*; exact hstop (by simp)
  | VR a => step*; exact hstop (by simp)
  | Sym g => step*; exact hstop (by simp)
  | Nil => step*; exact hstop (by simp)
  | App h t =>
    obtain ⟨u, us, hmap, hh, ht⟩ := encList_of_app hxs hnd
    obtain ⟨⟨ρx, mx⟩, rest, rfl, hx, hrest⟩ := List.map_eq_cons_iff.1 hmap
    subst hx hrest
    have hheld : HeldAs ρx mx := hps _ List.mem_cons_self
    simp only [List.map_cons, composableTicks] at hroom' ⊢
    step with dom_unpack_spec hnm (U := U) s1 h hK1.inv (by rw [hn1]; exact hh)
      (by unfold Room; omega) as ⟨acc, s2, hK2, hfl, hat, hac, hax⟩
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hn1]
    have hx02 : Extends s s2 := Extends.of_eq hn2 (by omega)
    have hacc : OrAt nm U s2.nodes.val acc ρx mx.r mx.Y :=
      ⟨by rw [hfl]; exact hheld.1, ⟨by rw [hK2.nodes]; exact hat, by rw [hK2.nodes]; exact hac,
        hheld.2.1, hheld.2.2, by rw [hK2.nodes]; exact hax⟩⟩
    have hB : 40 * (s2.ticks.val + chainTicks nm S U rc q ρx (rest.map Prod.fst)) + 100 ≤
        Usize.max := by omega
    have hloop := loop.spec_decr_nat dchainMeasure
      (DChainInv nm S U rc q s2 (s2.ticks.val + chainTicks nm S U rc q ρx (rest.map Prod.fst))
        ((Sorts.dom S).composable (ρx :: rest.map Prod.fst)))
      (fun y : Bool × store.Store => Inv y.2 ∧ Extends s2 y.2 ∧
        y.2.ticks.val ≤ s2.ticks.val + chainTicks nm S U rc q ρx (rest.map Prod.fst) ∧
        y.1 = (Sorts.dom S).composable (ρx :: rest.map Prod.fst))
      (fun x : DChainState =>
        dom.composable_loop.body decls names x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (s2, acc, t, true, true)
      (by
        rintro ⟨st, acc', rest', ok', go'⟩ hinv
        refine WP.spec_mono (dom_composable_body_spec hnm hz hC hN hUS hr hq s2 decls names
          (hx02.repr hde) (hx02.repr hU) _ _ hB st acc' rest' ok' go' hinv) ?_
        intro r hr
        cases r with
        | done y => exact hr
        | cont x' => exact hr)
      ⟨hK2.inv, Extends.refl s2, by
        simp only [↓reduceIte, true_and]
        exact ⟨ρx, mx.r, mx.Y, rest, hacc, fun p hp => hps p (List.mem_cons_of_mem _ hp),
          by rw [hn2]; exact ht, rfl, Nat.le_refl _⟩⟩
    refine WP.spec_mono hloop ?_
    rintro ⟨b, s'⟩ ⟨h1, h2, h3, h4⟩
    exact ⟨h1, hx02.trans h2, h4, by simp only at h3 ⊢; omega⟩

end Chain

end RwLogVerified
