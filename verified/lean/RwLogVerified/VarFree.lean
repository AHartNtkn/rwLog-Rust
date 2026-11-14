/-
# Whether a term has a variable: the Rust `var_free`

`var_free` asks of a term whether it has no variable; table `B` remembers
the answer for each node. `var_free_spec`: the answer is right, within
thirteen ticks for each distinct subterm that had no answer. `ground` clears
table `B` first (`ground_spec`, `RwLogVerified/Gone.lean`).
-/
import RwLogVerified.Lists

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term

variable {nm : Option Nat → Sym}

/-! ## Has a term no variable? -/

/-- The term has no variable. -/
def NoVar (t : Pat) : Prop := t.vars = []

instance (t : Pat) : Decidable (NoVar t) := by
  unfold NoVar; infer_instance

/-- Every entry of table `B` is the answer for its key. -/
def FreeOK (nm : Option Nat → Sym) (nodes : List store.Node) (B : Nat → Option Nat) : Prop :=
  ∀ k w, B k = some w → ∃ t, Repr nm nodes k t ∧ (w ≠ 0 ↔ NoVar t)

theorem FreeOK.set {nodes : List store.Node} {Bt : Nat → Option Nat} {k w : Nat} {t : Pat}
    (h : FreeOK nm nodes Bt) (hk : Repr nm nodes k t) (hw : w ≠ 0 ↔ NoVar t) :
    FreeOK nm nodes (Function.update Bt k (some w)) := by
  intro k' w' hk'
  by_cases e : k' = k
  · subst e
    simp only [Function.update_self, Option.some.injEq] at hk'
    subst hk'
    exact ⟨t, hk, hw⟩
  · rw [Function.update_of_ne e] at hk'
    exact h k' w' hk'

/-- What `var_free` leaves. -/
structure FreePost (nm : Option Nat → Sym) (s s' : store.Store) (t : Pat)
    (S : Finset Pat) (p : Nat) (b : Bool) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  res : b = decide (NoVar t)
  memo : FreeOK nm s'.nodes.val (tbl s' .B)
  tblA : tbl s' .A = tbl s .A
  grow : ∀ k, tbl s .B k ≠ none → tbl s' .B k ≠ none
  set : tbl s' .B p ≠ none
  cost : s'.ticks.val + 13 * (pending nm s'.nodes.val (tbl s' .B) S).card ≤
    s.ticks.val + 5 + 13 * (pending nm s.nodes.val (tbl s .B) S).card
  mono : s.ticks.val ≤ s'.ticks.val

theorem noVar_app {a b : Pat} : NoVar (.app a b) ↔ NoVar a ∧ NoVar b := by
  simp [NoVar, Term.vars]

/-- The invariant of the loop of `var_free`. -/
def AInv (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (S : Finset Pat)
    (B : Nat) (s : store.Store) : Prop :=
  Wf s ∧ s.nodes.val = s0.nodes.val ∧ tbl s .A = tbl s0 .A ∧
    FreeOK nm s0.nodes.val (tbl s .B) ∧
    RSt nm s0.nodes.val tp p (tbl s0 .B) (tbl s .B) (stk s) ∧
    ∃ U, Unb nm s0.nodes.val (tbl s .B) S (stk s) U ∧
      s.ticks.val + 1 + 2 * nV (stk s) + 5 * nB (stk s) + 13 * U.card ≤ B

def ADone (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (S : Finset Pat)
    (B : Nat) (s : store.Store) : Prop :=
  Wf s ∧ stk s = [] ∧ s.nodes.val = s0.nodes.val ∧ tbl s .A = tbl s0 .A ∧
    FreeOK nm s0.nodes.val (tbl s .B) ∧
    RSt nm s0.nodes.val tp p (tbl s0 .B) (tbl s .B) [] ∧
    s.ticks.val + 13 * (pending nm s0.nodes.val (tbl s .B) S).card ≤ B

def ABodyPost (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (p : Nat) (S : Finset Pat)
    (B : Nat) (t0 : Nat) : ControlFlow store.Store store.Store → Prop
  | .done s' => ADone nm s0 tp p S B s' ∧ t0 ≤ s'.ticks.val
  | .cont s' => AInv nm s0 tp p S B s' ∧ t0 < s'.ticks.val

theorem var_free_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (tp : Pat)
    (p : Nat) (S : Finset Pat) (B : Nat) (hB : 40 * B + 100 ≤ Usize.max)
    (hN : NodesOK s0.nodes.val) (hS : tp.subs ⊆ S)
    (s : store.Store) (h : AInv nm s0 tp p S B s) :
    term.var_free_loop.body s ⦃ r => ABodyPost nm s0 tp p S B s.ticks.val r ⦄ := by
  unfold term.var_free_loop.body
  obtain ⟨hW, hn, hTA, hAO, hSt, U, hU, hc⟩ := h
  step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
  cases hst : stk s with
  | nil =>
    rw [hst] at eo est hSt hU hc
    simp only [List.head?_nil, List.tail_nil] at eo est
    subst eo
    simp only [WP.spec_ok]
    have := hU.card_le
    simp only [nV_nil, nB_nil] at hc
    exact ⟨⟨hW1, est, by rw [e1, hn], by rw [e2, hTA], by rw [e2]; exact hAO,
      by rw [e2]; exact hSt, by rw [e2]; omega⟩, by omega⟩
  | cons fr st =>
    rw [hst] at eo est hSt hU hc
    simp only [List.head?_cons, List.tail_cons] at eo est
    subst eo
    obtain ⟨hfa, tq, htq, hq⟩ := hSt.frames fr List.mem_cons_self
    -- the answer for the node of the frame is written
    have hset : ∀ (s3 : store.Store) (m : Bool), Wf s3 → s3.nodes.val = s.nodes.val →
        tbl s3 = tbl s → stk s3 = st → tbl s .B (fkey fr) = none →
        ((if m = true then 1 else 0 : Nat) ≠ 0 ↔ NoVar tq) → s.ticks.val ≤ s3.ticks.val →
        s3.ticks.val + 2 + 2 * nV st + 5 * nB st + 13 * (U.erase tq).card ≤ B →
        (do
          let s5 ← store.Store.set_flag s3 store.Tbl.B (fid fr) m
          ok (ControlFlow.cont s5 : ControlFlow store.Store store.Store)) ⦃ r =>
          ABodyPost nm s0 tp p S B s.ticks.val r ⦄ := by
      intro s3 m hW3 hn3 htb3 hstk3 hnone hw hlt hcost
      step with set_flag_w s3 .B (fid fr) m hW3 (by rw [hn3, hn, fid_val]; exact hq.lt)
        (by unfold Room; omega) as ⟨s5, g1, g2, g3, g4, g5, g6⟩
      rw [htb3, fid_val] at g4
      refine ⟨⟨g3, by rw [g1, hn3, hn], by rw [g5 .A (by simp), htb3, hTA], ?_, ?_,
        U.erase tq, ?_, ?_⟩, by omega⟩
      · rw [g4]; exact hAO.set hq hw
      · rw [g4, g6, hstk3]; exact hSt.set hnone _
      · rw [g4, g6, hstk3]
        simpa using hU.set hq [] (if m = true then 1 else 0)
      · rw [g6, hstk3]; omega
    cases fr with
    | Visit q u =>
      have : q = u := by simp only [faux, fkey] at hfa; scalar_tac
      subst this
      simp only [fkey] at hq hset
      simp only [nV_visit, nB_visit] at hc
      simp only
      step with get_flag_w s1 .B q hW1 (by rw [e1, hn]; exact hq.lt) (by unfold Room; omega)
        as ⟨o1, s2, ho1, hK2⟩
      rw [e2] at ho1
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
      have hstk2 : stk s2 = st := by rw [hK2.stk, est]
      cases hBq : tbl s .B q.val with
      | some w =>
        rw [hBq] at ho1
        simp only [Option.map_some] at ho1
        subst ho1
        simp only [WP.spec_ok]
        refine ⟨⟨hK2.wf, by rw [hn2, hn], by rw [htb2, hTA], by rw [htb2]; exact hAO, ?_,
          U, ?_, ?_⟩, by omega⟩
        · rw [htb2, hstk2]; exact hSt.hit (by simp only [fkey]; rw [hBq]; simp)
        · rw [htb2, hstk2]; exact hU.pop_visit trivial
        · rw [hstk2]; omega
      | none =>
        rw [hBq] at ho1
        simp only [Option.map_none] at ho1
        subst ho1
        have htU : tq ∈ U := hU.mem_top hnm hN hSt.waits hq hBq (hS htq)
        have hU1 := card_erase_add_one htU
        simp only
        step with read_w s2 q hK2.wf (by rw [hn2, hn]; exact hq.lt) (by unfold Room; omega)
          as ⟨nd, s3, hnd, hK3⟩
        rw [hn2, hn] at hnd
        have ht3 := hK3.ticks
        have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
        have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
        have hstk3 : stk s3 = st := by rw [hK3.stk, hstk2]
        have hvar : ∀ v, tq = Term.var v →
            (do
              let s4 ← store.Store.set_flag s3 store.Tbl.B q false
              ok (ControlFlow.cont s4 : ControlFlow store.Store store.Store)) ⦃ r =>
              ABodyPost nm s0 tp p S B s.ticks.val r ⦄ := by
          intro v hv
          subst hv
          exact hset s3 false hK3.wf hn3 htb3 hstk3 hBq (by simp [NoVar, Term.vars]) (by omega)
            (by omega)
        have hatom : ∀ f, tq = Term.sym f →
            (do
              let s4 ← store.Store.set_flag s3 store.Tbl.B q true
              ok (ControlFlow.cont s4 : ControlFlow store.Store store.Store)) ⦃ r =>
              ABodyPost nm s0 tp p S B s.ticks.val r ⦄ := by
          intro f hf
          subst hf
          exact hset s3 true hK3.wf hn3 htb3 hstk3 hBq (by simp [NoVar, Term.vars]) (by omega)
            (by omega)
        cases nd with
        | V0 =>
          obtain ⟨v, hv, -⟩ := hq.of_var hnd trivial
          exact hvar v hv
        | VL a =>
          obtain ⟨v, hv, -⟩ := hq.of_var hnd trivial
          exact hvar v hv
        | VR a =>
          obtain ⟨v, hv, -⟩ := hq.of_var hnd trivial
          exact hvar v hv
        | Sym g => exact hatom _ (hq.of_sym hnd)
        | Nil => exact hatom _ (hq.of_nil hnd)
        | App a b =>
          simp only
          step with push_w s3 (.Build q q) hK3.wf (by unfold Room; omega)
            as ⟨s4, a1, a2, a3, hW4, a5⟩
          step with push_w s4 (.Visit b b) hW4 (by unfold Room; omega)
            as ⟨s5, b1, b2, b3, hW5, b5⟩
          step with push_w s5 (.Visit a a) hW5 (by unfold Room; omega)
            as ⟨s6, c1, c2, c3, hW6, c5⟩
          have htb6 : tbl s6 = tbl s := by rw [c2, b2, a2, htb3]
          have hstk6 : stk s6 = .Visit a a :: .Visit b b :: .Build q q :: st := by
            rw [c5, b5, a5, hstk3]
          refine ⟨⟨hW6, by rw [c1, b1, a1, hn3, hn], by rw [htb6, hTA], by rw [htb6]; exact hAO,
            ?_, U.erase tq, ?_, ?_⟩, by omega⟩
          · rw [htb6, hstk6]; exact hSt.expand hN hBq hnd
          · rw [htb6, hstk6]; exact hU.expand hq
          · rw [hstk6]
            simp only [nV_visit, nV_build, nB_visit, nB_build]
            omega
    | Build q u =>
      simp only [fkey] at hq hset
      simp only [nV_build, nB_build] at hc
      obtain ⟨a, b, hn0, hnone, hBa, hBb⟩ := hSt.top
      obtain ⟨ta, tb, e, ha, hb⟩ := hq.of_app hn0
      subst e
      have hEr := Finset.card_erase_le (s := U) (a := Term.app ta tb)
      simp only
      step with read_w s1 q hW1 (by rw [e1, hn]; exact hq.lt) (by unfold Room; omega)
        as ⟨nd, s2, hnd, hK2⟩
      rw [e1, hn, hn0] at hnd
      cases hnd
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
      simp only
      step with get_flag_w s2 .B a hK2.wf (by rw [hn2, hn]; exact ha.lt) (by unfold Room; omega)
        as ⟨o1, s3, ho1, hK3⟩
      rw [htb2] at ho1
      have ht3 := hK3.ticks
      have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
      have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
      cases hwa : tbl s .B a.val with
      | none => exact absurd hwa hBa
      | some wa =>
      rw [hwa] at ho1
      simp only [Option.map_some] at ho1
      subst ho1
      simp only [term.is_set, core.option.Option.unwrap_or_some, bind_ok]
      step with get_flag_w s3 .B b hK3.wf (by rw [hn3, hn]; exact hb.lt) (by unfold Room; omega)
        as ⟨o2, s4, ho2, hK4⟩
      rw [htb3] at ho2
      have ht4 := hK4.ticks
      have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
      have htb4 : tbl s4 = tbl s := by rw [hK4.tbl, htb3]
      have hstk4 : stk s4 = st := by rw [hK4.stk, hK3.stk, hK2.stk, est]
      cases hwb : tbl s .B b.val with
      | none => exact absurd hwb hBb
      | some wb =>
      rw [hwb] at ho2
      simp only [Option.map_some] at ho2
      subst ho2
      simp only [core.option.Option.unwrap_or_some]
      obtain ⟨ta', h1, hra⟩ := hAO _ _ hwa
      have := ha.unique h1
      subst this
      obtain ⟨tb', h2, hrb⟩ := hAO _ _ hwb
      have := hb.unique h2
      subst this
      by_cases ha0 : wa ≠ 0
      · simp only [decide_eq_true ha0, ↓reduceIte]
        refine hset s4 (decide (wb ≠ 0)) hK4.wf hn4 htb4 hstk4 hnone ?_ (by omega) (by omega)
        rw [noVar_app, ← hra, ← hrb]
        by_cases hb0 : wb ≠ 0 <;> simp [ha0, hb0]
      · simp only [decide_eq_false ha0, Bool.false_eq_true, ↓reduceIte]
        refine hset s4 false hK4.wf hn4 htb4 hstk4 hnone ?_ (by omega) (by omega)
        rw [noVar_app, ← hra]
        simp [ha0]

/-- `var_free` decides whether the term has no variable, and
leaves the answer for the node in table `B`. It spends five ticks, and
thirteen more for each term of `S` that had no answer and gets one. -/
theorem var_free_spec (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId)
    {tp : Pat} (S : Finset Pat) (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val tp)
    (hB : FreeOK nm s.nodes.val (tbl s .B)) (hS : tp.subs ⊆ S)
    (hroom : Room s (5 + 13 * (pending nm s.nodes.val (tbl s .B) S).card)) :
    term.var_free s p ⦃ b s' => FreePost nm s s' tp S p.val b ⦄ := by
  unfold term.var_free term.var_free_loop
  have hroom' := hroom
  unfold Room at hroom'
  step with push_w s (.Visit p p) hI.toWf (by unfold Room; omega) as ⟨s1, a1, a2, a3, hW1, a5⟩
  rw [hI.empty] at a5
  let B := s.ticks.val + 4 + 13 * (pending nm s.nodes.val (tbl s .B) S).card
  have hloop := loop.spec_decr_nat
    (fun x : store.Store => B + 1 - x.ticks.val)
    (fun x => AInv nm s tp p.val S B x ∧ s.ticks.val ≤ x.ticks.val)
    (fun x => ADone nm s tp p.val S B x ∧ s.ticks.val ≤ x.ticks.val)
    (fun x : store.Store => term.var_free_loop.body x) s1
    (by
      intro x hinv
      obtain ⟨hinv, hlow⟩ := hinv
      refine WP.spec_mono (var_free_body_spec hnm s tp p.val S B (by omega) hI.nodesOK hS
        x hinv) ?_
      intro r hr
      cases r with
      | done y => exact ⟨hr.1, Nat.le_trans hlow hr.2⟩
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr
        have hc := h1.2.2.2.2.2
        obtain ⟨U, -, hc⟩ := hc
        exact ⟨⟨h1, by omega⟩, by omega⟩)
    ⟨⟨hW1, a1, by rw [a2], by rw [a2]; exact hB,
      ⟨by rw [a2]; exact fun _ _ h => h, by
        rw [a5]
        intro f' hf'
        simp only [List.mem_singleton] at hf'
        subst hf'
        exact ⟨rfl, tp, Term.self_mem_subs tp, hp⟩, by
        rw [a5]
        intro q u hq
        simp at hq, by rw [a5]; exact Waits.single p p, by
        rw [a5]; exact Or.inr ⟨_, List.mem_singleton_self _, rfl⟩⟩,
      _, Unb.start _ _ _ _, by
        rw [a5, a2]
        simp only [nV_visit, nV_nil, nB_visit, nB_nil]
        omega⟩, by omega⟩
  step with hloop as ⟨s2, hD, hlow2⟩
  obtain ⟨hW2, hemp, hn2, hTA2, hAO2, hSt2, hc2⟩ := hD
  have hBp := hSt2.done
  step with get_flag_w s2 .B p hW2 (by rw [hn2]; exact hp.lt) (by unfold Room; omega)
    as ⟨o, s3, ho, hK3⟩
  have ht3 := hK3.ticks
  cases hw : tbl s2 .B p.val with
  | none => exact absurd hw hBp
  | some w =>
    rw [hw] at ho
    simp only [Option.map_some] at ho
    subst ho
    simp only [term.is_set, core.option.Option.unwrap_or_some, bind_ok, WP.spec_ok]
    obtain ⟨t', h1, hr⟩ := hAO2 _ _ hw
    have := hp.unique h1
    subst this
    refine ⟨⟨hK3.wf, by rw [hK3.stk]; exact hemp⟩, by rw [hK3.nodes, hn2], decide_eq_decide.2 hr,
      by rw [hK3.nodes, hn2, hK3.tbl]; exact hAO2, by rw [hK3.tbl, hTA2], ?_,
      by rw [hK3.tbl, hw]; simp, by rw [hK3.nodes, hn2, hK3.tbl]; omega, by omega⟩
    intro k hk
    rw [hK3.tbl]
    cases hk0 : tbl s .B k with
    | none => exact absurd hk0 hk
    | some v => rw [hSt2.keep k v hk0]; simp

theorem FreeOK.extends {s s' : store.Store} {B : Nat → Option Nat}
    (h : FreeOK nm s.nodes.val B) (he : Extends s s') : FreeOK nm s'.nodes.val B :=
  fun k w hk => by
    obtain ⟨t, hr, hw⟩ := h k w hk
    exact ⟨t, he.repr hr, hw⟩

end RwLogVerified
