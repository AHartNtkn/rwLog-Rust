/-
# The occurs check: the Rust `occurs` decides membership in `Term.vars`

`occurs s x p` says whether the variable at `x` occurs in the term at `p`.
Table `B` remembers the answer for each node visited, so a node is examined
once however often it occurs.

`occurs_spec`: the answer is `xv ∈ t.vars`, no node is added, table `A` is
untouched, and the cost is one tick plus five for each term that gets an
entry in `B`, counted as in `rebuild_spec`.
-/
import RwLogVerified.Rebuild

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-- Every entry of the table says whether the variable occurs in its key. -/
def FlagOK (nm : Option Nat → Sym) (nodes : List store.Node) (B : Nat → Option Nat) (xv : Nat) :
    Prop :=
  ∀ k v, B k = some v → ∃ t, Repr nm nodes k t ∧ (v ≠ 0 ↔ xv ∈ t.vars)

/-- What `occurs` leaves. -/
structure OccursPost (nm : Option Nat → Sym) (s s' : store.Store) (xv : Nat) (t : Pat)
    (S : Finset Pat) (b : Bool) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  res : b = decide (xv ∈ t.vars)
  memo : FlagOK nm s'.nodes.val (tbl s' .B) xv
  tblA : tbl s' .A = tbl s .A
  keep : ∀ k v, tbl s .B k = some v → tbl s' .B k = some v
  cost : s'.ticks.val + 5 * (pending nm s'.nodes.val (tbl s' .B) S).card ≤
    s.ticks.val + 1 + 5 * (pending nm s.nodes.val (tbl s .B) S).card

/-- The last step of a miss: the answer `b`, computed in `s3`, is written to
the table. -/
theorem occurs_finish (hnm : Function.Injective nm) {s s3 s' : store.Store} {xv : Nat}
    {t : Pat} {S : Finset Pat} {p : store.TermId} {b : Bool}
    (hI : Inv s) (hp : Repr nm s.nodes.val p.val t) (hnone : tbl s .B p.val = none) (htS : t ∈ S)
    (hn : s3.nodes.val = s.nodes.val) (hb : b = decide (xv ∈ t.vars))
    (hM : FlagOK nm s3.nodes.val (tbl s3 .B) xv) (hA : tbl s3 .A = tbl s .A)
    (hkeep : ∀ k v, tbl s .B k = some v → tbl s3 .B k = some v)
    (hc : s3.ticks.val + 5 * (pending nm s3.nodes.val (tbl s3 .B) (S.erase t)).card ≤
      s.ticks.val + 5 * (pending nm s.nodes.val (tbl s .B) (S.erase t)).card + 5)
    (g1 : s'.nodes.val = s3.nodes.val) (g2 : s'.ticks.val = s3.ticks.val + 1) (g3 : Inv s')
    (g4 : tbl s' .B = Function.update (tbl s3 .B) p.val (some (if b then 1 else 0)))
    (g5 : ∀ t', t' ≠ store.Tbl.B → tbl s' t' = tbl s3 t') :
    OccursPost nm s s' xv t S b := by
  have hp3 : Repr nm s3.nodes.val p.val t := by rw [hn]; exact hp
  refine ⟨g3, by rw [g1, hn], hb, ?_, ?_, ?_, ?_⟩
  · intro k v hk
    rw [g1]
    rw [g4] at hk
    by_cases e : k = p.val
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hk
      subst hk
      refine ⟨t, hp3, ?_⟩
      subst hb
      by_cases h : xv ∈ t.vars <;> simp [h]
    · rw [Function.update_of_ne e] at hk
      exact hM k v hk
  · rw [g5 .A (by simp), hA]
  · intro k v hk
    rw [g4]
    by_cases e : k = p.val
    · subst e; rw [hnone] at hk; cases hk
    · rw [Function.update_of_ne e]; exact hkeep k v hk
  · have hsub : pending nm s'.nodes.val (tbl s' .B) S ⊆
        pending nm s3.nodes.val (tbl s3 .B) (S.erase t) := by
      have := pending_after_set (nm := nm) (nodes := s3.nodes.val) (more := []) (A := tbl s3 .B)
        (A' := tbl s' .B) (S := S) (t := t) (p := p.val) (by simpa using hp3)
        (by rw [g4]; simp)
        (by
          intro k hk
          rw [g4]
          by_cases e : k = p.val
          · subst e; simp
          · rw [Function.update_of_ne e]; exact hk)
      simpa [g1] using this
    have h1 := Finset.card_le_card hsub
    have h2 := pending_erase_card (mem_pending_of_none hnm hI.nodesOK hp hnone htS)
    omega

theorem occurs_spec_aux (hnm : Function.Injective nm) (n : Nat) :
    ∀ (s : store.Store) (x p : store.TermId) (t : Pat) (xv : Nat) (S : Finset Pat),
      t.size ≤ n → Inv s → Repr nm s.nodes.val p.val t → VarAt s.nodes.val x.val xv →
      FlagOK nm s.nodes.val (tbl s .B) xv → t.subs ⊆ S →
      Room s (1 + 5 * (pending nm s.nodes.val (tbl s .B) S).card) →
      term.occurs s x p ⦃ b s' => OccursPost nm s s' xv t S b ⦄ := by
  induction n with
  | zero =>
    intro s x p t xv S hsz
    cases t <;> simp [Term.size] at hsz
  | succ n ih =>
    intro s x p t xv S hsz hI hp hx hM hS hroom
    unfold term.occurs
    step with get_flag_spec s .B p hI hp.lt (hroom.mono (by omega)) as ⟨o, s1, ho, hK1⟩
    cases hB : tbl s .B p.val with
    | some v =>
      rw [hB] at ho
      simp only [Option.map_some] at ho
      subst ho
      simp only
      step*
      obtain ⟨t', h1, h2⟩ := hM _ _ hB
      have := hp.unique h1
      subst this
      refine ⟨hK1.inv, hK1.nodes, ?_, ?_, by rw [hK1.tbl],
        fun k v hk => by rw [hK1.tbl]; exact hk, ?_⟩
      · exact decide_eq_decide.2 h2
      · rw [hK1.nodes, hK1.tbl]; exact hM
      · rw [hK1.nodes, hK1.tbl]; have := hK1.ticks; omega
    | none =>
      rw [hB] at ho
      simp only [Option.map_none] at ho
      subst ho
      have hnone := hB
      have htS : t ∈ S := hS (Term.self_mem_subs t)
      have hpend := mem_pending_of_none hnm hI.nodesOK hp hnone htS
      have hP := pending_erase_card hpend
      have hroom' := hroom
      unfold Room at hroom'
      have ht1 := hK1.ticks
      simp only
      have hp1 : p.val < s1.nodes.val.length := by rw [hK1.nodes]; exact hp.lt
      step with read_spec s1 p hK1.inv hp1 (by unfold Room; omega) as ⟨nd, s2, hnd, hK2⟩
      rw [hK1.nodes] at hnd
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK1.nodes]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK1.tbl]
      have hp2 : p.val < s2.nodes.val.length := by rw [hn2]; exact hp.lt
      have hleaf : ∀ v, t = Term.var v → VarAt s.nodes.val p.val v →
          (do
            let (s3, b) ← (do
              let (b1, s4) ← store.Store.same s2 p x
              ok (s4, b1))
            let s4 ← store.Store.set_flag s3 store.Tbl.B p b
            ok (b, s4)) ⦃ b s' => OccursPost nm s s' xv t S b ⦄ := by
        intro v hv hva
        subst hv
        step with same_spec s2 p x hK2.inv (by unfold Room; omega) as ⟨y, hb, hK4⟩
        obtain ⟨b1, s4⟩ := y
        simp only at hb hK4 ⊢
        have ht4 := hK4.ticks
        have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn2]
        have htb4 : tbl s4 = tbl s := by rw [hK4.tbl, htb2]
        step with set_flag_spec s4 .B p b1 hK4.inv (by rw [hn4]; exact hp.lt)
          (by unfold Room; omega) as ⟨s5, g1, g2, g3, g4, g5⟩
        refine occurs_finish hnm hI hp hnone htS hn4 ?_ (by rw [hn4, htb4]; exact hM)
          (by rw [htb4]) (fun k v hk => by rw [htb4]; exact hk) (by rw [hn4, htb4]; omega)
          g1 g2 g3 g4 g5
        rw [hb]
        simp only [Term.vars, List.mem_singleton]
        by_cases e : p.val = x.val
        · have : v = xv := by rw [e] at hva; exact hva.unique hx
          simp [e, this]
        · have : xv ≠ v := by
            rintro rfl
            exact e (hva.inj hI.nodesOK hx)
          simp [e, this]
      have hatom : (∀ y, y ∉ t.vars) →
          (do
            let (s3, b) ← (ok (s2, false) : Result (store.Store × Bool))
            let s4 ← store.Store.set_flag s3 store.Tbl.B p b
            ok (b, s4)) ⦃ b s' => OccursPost nm s s' xv t S b ⦄ := by
        intro hr
        step with set_flag_spec s2 .B p false hK2.inv hp2 (by unfold Room; omega)
          as ⟨s5, g1, g2, g3, g4, g5⟩
        refine occurs_finish hnm hI hp hnone htS hn2 (by simp [hr xv])
          (by rw [hn2, htb2]; exact hM) (by rw [htb2]) (fun k v hk => by rw [htb2]; exact hk)
          (by rw [hn2, htb2]; omega) g1 g2 g3 g4 g5
      cases nd with
      | V0 =>
        obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
        exact hleaf v hv hva
      | VL a =>
        obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
        exact hleaf v hv hva
      | VR a =>
        obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
        exact hleaf v hv hva
      | Sym g =>
        have := hp.of_sym hnd
        subst this
        exact hatom (by simp [Term.vars])
      | Nil =>
        have := hp.of_nil hnd
        subst this
        exact hatom (by simp [Term.vars])
      | App a c =>
        obtain ⟨ta, tb, e, ha, hc⟩ := hp.of_app hnd
        subst e
        simp only [Term.size] at hsz
        simp only
        have hSa := subs_left_erase hS
        have hSb := subs_right_erase hS
        step with ih s2 x a ta xv (S.erase (Term.app ta tb)) (by omega) hK2.inv
          (by rw [hn2]; exact ha) (by rw [hn2]; exact hx) (by rw [hn2, htb2]; exact hM) hSa
          (by rw [hn2, htb2]; unfold Room; omega) as ⟨y, hA⟩
        obtain ⟨b1, s4⟩ := y
        simp only at hA ⊢
        have hcA := hA.cost
        rw [hn2, htb2] at hcA
        have hn4 : s4.nodes.val = s.nodes.val := by rw [hA.nodes, hn2]
        cases b1 with
        | true =>
          simp only [uncurry_apply_pair, ↓reduceIte, bind_ok]
          step with set_flag_spec s4 .B p true hA.inv (by rw [hn4]; exact hp.lt)
            (by unfold Room; omega) as ⟨s5, g1, g2, g3, g4, g5⟩
          have hin : xv ∈ ta.vars := by simpa using hA.res.symm
          refine occurs_finish hnm hI hp hnone htS hn4 (by simp [Term.vars, hin]) hA.memo
            (by rw [hA.tblA, htb2]) (fun k v hk => hA.keep k v (by rw [htb2]; exact hk))
            (by omega) g1 g2 g3 g4 g5
        | false =>
          have hin : xv ∉ ta.vars := by simpa using hA.res.symm
          simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]
          step with ih s4 x c tb xv (S.erase (Term.app ta tb)) (by omega) hA.inv
            (by rw [hn4]; exact hc) (by rw [hn4]; exact hx) hA.memo hSb
            (by unfold Room; omega) as ⟨y, hBp⟩
          obtain ⟨b2, s5⟩ := y
          simp only at hBp ⊢
          have hcB := hBp.cost
          have hn5 : s5.nodes.val = s.nodes.val := by rw [hBp.nodes, hn4]
          step with set_flag_spec s5 .B p b2 hBp.inv (by rw [hn5]; exact hp.lt)
            (by unfold Room; omega) as ⟨s6, g1, g2, g3, g4, g5⟩
          refine occurs_finish hnm hI hp hnone htS hn5 (by rw [hBp.res]; simp [Term.vars, hin])
            hBp.memo (by rw [hBp.tblA, hA.tblA, htb2])
            (fun k v hk => hBp.keep k v (hA.keep k v (by rw [htb2]; exact hk)))
            (by omega) g1 g2 g3 g4 g5

/-- `occurs` decides whether a variable occurs in a term. It spends one tick,
and five more for each term of `S` that had no entry in `B` and gets one. -/
theorem occurs_spec (hnm : Function.Injective nm) (s : store.Store) (x p : store.TermId)
    {t : Pat} {xv : Nat} (S : Finset Pat) (hI : Inv s) (hp : Repr nm s.nodes.val p.val t)
    (hx : VarAt s.nodes.val x.val xv) (hM : FlagOK nm s.nodes.val (tbl s .B) xv)
    (hS : t.subs ⊆ S) (hroom : Room s (1 + 5 * (pending nm s.nodes.val (tbl s .B) S).card)) :
    term.occurs s x p ⦃ b s' => OccursPost nm s s' xv t S b ⦄ :=
  occurs_spec_aux hnm t.size s x p t xv S (Nat.le_refl _) hI hp hx hM hS hroom

end RwLogVerified
