/-
# The chain test: the Rust `composable`

`composable_spec`: on a list of spans the store holds, `composable` says
whether the chain composes, as `Span.chain` does. It composes from the left
and stops at the first failure, so what it spends is the cost of the
compositions it makes (`composableCost`). That depends on the intermediate
spans, which the sizes of the spans in the list do not bound.
-/
import RwLogVerified.Compose
import RwLog.Trusted.Charged

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term

variable {nm : Option Nat → Sym}

/-- The ticks the loop of `composable` may spend, from the span composed so
far and the spans that are left. -/
def chainCost (z : Sym) : Span → List Span → Nat
  | _, [] => 1
  | acc, y :: ys => 3 + composeCost z acc y +
    match acc.compose y with
    | some w => chainCost z w ys
    | none => 0

/-- The ticks `composable` may spend. -/
def composableCost (z : Sym) : List Span → Nat
  | [] => 1
  | x :: rest => 3 + chainCost z x rest

theorem foldl_compose_none (ys : List Span) :
    ys.foldl (fun (a : Option Span) t => a.bind (·.compose t)) none = none := by
  induction ys with
  | nil => rfl
  | cons y ys ih => exact ih

abbrev ChainState := store.Store × span.Span × store.TermId × Bool × Bool

/-- The invariant of the loop. -/
def ChainInv (nm : Option Nat → Sym) (s0 : store.Store) (B : Nat) (R : Bool) : ChainState → Prop
  | (s, acc, rest, ok, go) => Inv s ∧ Extends s0 s ∧
    if go then ok = true ∧ ∃ sacc ys, SpanAt nm s.nodes.val acc sacc ∧
        Repr nm s.nodes.val rest.val (encList (nm none) (ys.map (packSpan (nm none)))) ∧
        (ys.foldl (fun (a : Option Span) t => a.bind (·.compose t)) (some sacc)).isSome = R ∧
        s.ticks.val + chainCost (nm none) sacc ys ≤ B
    else s.ticks.val ≤ B ∧ ok = R

def chainMeasure : ChainState → Nat
  | (_, _, rest, _, go) => 2 * rest.val + if go then 1 else 0

def ChainBody (nm : Option Nat → Sym) (s0 : store.Store) (B : Nat) (R : Bool) (m : Nat) :
    ControlFlow ChainState (Bool × store.Store) → Prop
  | .done (ok, s) => Inv s ∧ Extends s0 s ∧ s.ticks.val ≤ B ∧ ok = R
  | .cont x => ChainInv nm s0 B R x ∧ chainMeasure x < m

theorem composable_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (B : Nat) (R : Bool)
    (hB : 40 * B + 100 ≤ Usize.max) (st : store.Store) (acc : span.Span) (rest : store.TermId)
    (ok go : Bool) (h : ChainInv nm s0 B R (st, acc, rest, ok, go)) :
    span.composable_loop.body st acc rest ok go ⦃ r =>
      ChainBody nm s0 B R (chainMeasure (st, acc, rest, ok, go)) r ⦄ := by
  unfold span.composable_loop.body
  obtain ⟨hI, hE0, h⟩ := h
  cases go with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    step*
    exact ⟨hI, hE0, h.1, h.2⟩
  | true =>
    simp only [↓reduceIte] at h ⊢
    obtain ⟨hok, sacc, ys, hacc, hrest, hR, hc⟩ := h
    subst hok
    have h1le : 1 ≤ chainCost (nm none) sacc ys := by cases ys <;> simp [chainCost]; omega
    step with read_spec st rest hI hrest.lt (by unfold Room; omega) as ⟨nd, s1, hnd, hK1⟩
    have ht1 := hK1.ticks
    have hn1 := hK1.nodes
    have hstop : (∀ a b, nd ≠ .App a b) →
        ChainBody nm s0 B R (chainMeasure (st, acc, rest, true, true))
          (ControlFlow.cont (s1, acc, rest, true, false)) := by
      intro hna
      have hys := encList_of_not_app hrest hnd hna
      have hys' : ys = [] := List.map_eq_nil_iff.1 hys
      subst hys'
      refine ⟨⟨hK1.inv, hE0.trans (Extends.of_eq hn1), ?_⟩, by simp [chainMeasure]⟩
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
      obtain ⟨y, ys', rfl, hy, hys'⟩ := List.map_eq_cons_iff.1 hmap
      subst hy hys'
      have hlt : t2.val < rest.val := by
        have := hI.shape.fits _ _ hnd
        simp only [Fits] at this
        exact this.2
      simp only [chainCost] at hc
      simp only
      step with unpack_spec (nm := nm) s1 h2 hK1.inv (by rw [hn1]; exact hh2)
        (by unfold Room; omega) as ⟨y', s2, hI2, hn2, hl, hr, hcc, htk2⟩
      have hn2' : s2.nodes.val = st.nodes.val := by rw [hn2, hn1]
      have hy' : SpanAt nm s2.nodes.val y' y :=
        ⟨by rw [hn2]; exact hl, by rw [hn2]; exact hr, by rw [hn2]; exact hcc⟩
      step with compose_spec hnm s2 acc y' (sx := sacc) (sy := y) hI2
        (by rw [hn2']; exact hacc) hy' (by unfold Room; omega) as ⟨o, s3, hI3, hx3, ho, ht3⟩
      have hst3 : Extends st s3 := (Extends.of_eq hn2').trans hx3
      cases o with
      | none =>
        cases hcomp : sacc.compose y with
        | some w => rw [hcomp] at ho; exact ho.elim
        | none =>
          step*
          refine ⟨⟨hI3, hE0.trans hst3, ?_⟩, by simp [chainMeasure]⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨by omega, ?_⟩
          rw [← hR]
          simp only [List.foldl_cons, Option.bind_some, hcomp, foldl_compose_none]
          rfl
      | some zz =>
        cases hcomp : sacc.compose y with
        | none => rw [hcomp] at ho; exact ho.elim
        | some w =>
          rw [hcomp] at ho hc
          simp only at hc
          step*
          refine ⟨⟨hI3, hE0.trans hst3, ?_⟩, by simp only [chainMeasure, ↓reduceIte]; omega⟩
          simp only [↓reduceIte, true_and]
          refine ⟨w, ys', ho, hst3.repr ht2, ?_, by omega⟩
          rw [← hR]
          simp only [List.foldl_cons, Option.bind_some, hcomp]

theorem composable_spec (hnm : Function.Injective nm) (s : store.Store) (xs : store.TermId)
    {spans : List Span} (hI : Inv s)
    (hxs : Repr nm s.nodes.val xs.val (encList (nm none) (spans.map (packSpan (nm none)))))
    (hroom : Room s (composableCost (nm none) spans)) :
    span.composable s xs ⦃ b s' =>
      Inv s' ∧ Extends s s' ∧ b = (Span.chain spans).isSome ∧
        s'.ticks.val ≤ s.ticks.val + composableCost (nm none) spans ⦄ := by
  unfold span.composable span.composable_loop
  have hroom' := hroom
  unfold Room at hroom'
  have h1le : 1 ≤ composableCost (nm none) spans := by cases spans <;> simp [composableCost]; omega
  step with read_spec s xs hI hxs.lt (by unfold Room; omega) as ⟨nd, s1, hnd, hK1⟩
  have ht1 := hK1.ticks
  have hn1 := hK1.nodes
  have hstop : (∀ a b, nd ≠ .App a b) → Inv s1 ∧ Extends s s1 ∧
      true = (Span.chain spans).isSome ∧ s1.ticks.val ≤ s.ticks.val + composableCost (nm none) spans := by
    intro hna
    have hys := encList_of_not_app hxs hnd hna
    have hys' : spans = [] := List.map_eq_nil_iff.1 hys
    subst hys'
    exact ⟨hK1.inv, Extends.of_eq hn1, rfl, by omega⟩
  cases nd with
  | V0 => step*; exact hstop (by simp)
  | VL a => step*; exact hstop (by simp)
  | VR a => step*; exact hstop (by simp)
  | Sym g => step*; exact hstop (by simp)
  | Nil => step*; exact hstop (by simp)
  | App h t =>
    obtain ⟨u, us, hmap, hh, ht⟩ := encList_of_app hxs hnd
    obtain ⟨x, rest, rfl, hx, hrest⟩ := List.map_eq_cons_iff.1 hmap
    subst hx hrest
    simp only [composableCost] at hroom' ⊢
    step with unpack_spec (nm := nm) s1 h hK1.inv (by rw [hn1]; exact hh)
      (by unfold Room; omega) as ⟨acc, s2, hI2, hn2, hl, hr, hcc, htk2⟩
    have hn2' : s2.nodes.val = s.nodes.val := by rw [hn2, hn1]
    have hacc : SpanAt nm s2.nodes.val acc x :=
      ⟨by rw [hn2]; exact hl, by rw [hn2]; exact hr, by rw [hn2]; exact hcc⟩
    have hB : 40 * (s2.ticks.val + chainCost (nm none) x rest) + 100 ≤ Usize.max := by omega
    have hloop := loop.spec_decr_nat chainMeasure
      (ChainInv nm s2 (s2.ticks.val + chainCost (nm none) x rest) (Span.chain (x :: rest)).isSome)
      (fun y : Bool × store.Store => Inv y.2 ∧ Extends s2 y.2 ∧
        y.2.ticks.val ≤ s2.ticks.val + chainCost (nm none) x rest ∧
        y.1 = (Span.chain (x :: rest)).isSome)
      (fun x : ChainState => span.composable_loop.body x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (s2, acc, t, true, true)
      (by
        rintro ⟨st, acc', rest', ok', go'⟩ hinv
        refine WP.spec_mono (composable_body_spec hnm s2 _ _ hB st acc' rest' ok' go' hinv) ?_
        intro r hr
        cases r with
        | done y => exact hr
        | cont x' => exact hr)
      ⟨hI2, Extends.refl s2, by
        simp only [↓reduceIte, true_and]
        exact ⟨x, rest, hacc, by rw [hn2']; exact ht, rfl, Nat.le_refl _⟩⟩
    refine WP.spec_mono hloop ?_
    rintro ⟨b, s'⟩ ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (Extends.of_eq hn2').trans h2, h4, by simp only at h3 ⊢; omega⟩

end RwLogVerified
