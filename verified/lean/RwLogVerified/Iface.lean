/-
# The interfaces of a span: the Rust `right_bound` and `left_bound`

The interface at a side `p` of a span keeps the constraints whose variables
all occur in `p`. `mark` flags every subterm of `p` in table `A`,
`all_marked` asks of a constraint whether each of its variables is flagged
(table `B` remembers the answer for each node), and `keep` filters the list.

`right_bound_spec` and `left_bound_spec`: the results are the
specification's `bound s.rightIface` and `bound s.leftIface`, within
`ifaceCost` ticks: linear in the distinct subterms of the side and of the
constraints.
-/
import RwLogVerified.Cover

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term

variable {nm : Option Nat → Sym}

theorem var_mem_subs_iff {v : Nat} {t : Pat} : Term.var v ∈ t.subs ↔ v ∈ t.vars := by
  induction t with
  | var w => simp [Term.subs, Term.vars]
  | sym f => simp [Term.subs, Term.vars]
  | app a b iha ihb => simp [Term.subs, Term.vars, iha, ihb]

/-! ## Flagging the subterms of a term -/

/-- The nodes with an entry in the table are exactly the terms of `M`. -/
structure Marked (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat)
    (M : Finset Pat) : Prop where
  sound : ∀ k, A k ≠ none → ∃ t ∈ M, Repr nm nodes k t
  complete : ∀ t ∈ M, ∃ k, Repr nm nodes k t ∧ A k ≠ none

theorem Marked.iff (hnm : Function.Injective nm) {nodes : List store.Node} (hN : NodesOK nodes)
    {A : Nat → Option Nat} {M : Finset Pat} (h : Marked nm nodes A M) {k : Nat} {t : Pat}
    (hk : Repr nm nodes k t) : A k ≠ none ↔ t ∈ M := by
  constructor
  · intro hA
    obtain ⟨t', ht', hr⟩ := h.sound k hA
    rw [hk.unique hr]; exact ht'
  · intro ht
    obtain ⟨k', hr, hA⟩ := h.complete t ht
    rw [Repr.inj hnm hN hk hr]; exact hA

theorem Marked.extends {s s' : store.Store} {A : Nat → Option Nat} {M : Finset Pat}
    (h : Marked nm s.nodes.val A M) (he : Extends s s') : Marked nm s'.nodes.val A M :=
  ⟨fun k hk => by obtain ⟨t, ht, hr⟩ := h.sound k hk; exact ⟨t, ht, he.repr hr⟩,
   fun t ht => by obtain ⟨k, hr, hk⟩ := h.complete t ht; exact ⟨k, he.repr hr, hk⟩⟩

/-- What `mark` leaves. -/
structure MarkPost (nm : Option Nat → Sym) (s s' : store.Store) (M : Finset Pat) (tp : Pat)
    (S : Finset Pat) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  tblB : tbl s' .B = tbl s .B
  marked : Marked nm s'.nodes.val (tbl s' .A) (M ∪ tp.subs)
  grow : ∀ k, tbl s .A k ≠ none → tbl s' .A k ≠ none
  cost : s'.ticks.val + 4 * (pending nm s'.nodes.val (tbl s' .A) S).card ≤
    s.ticks.val + 1 + 4 * (pending nm s.nodes.val (tbl s .A) S).card

/-- The state after the parts of the node are flagged and before the node
is. -/
structure MarkMid (nm : Option Nat → Sym) (s s3 : store.Store) (M : Finset Pat) (tp : Pat)
    (S : Finset Pat) : Prop where
  inv : Inv s3
  nodes : s3.nodes.val = s.nodes.val
  tblB : tbl s3 .B = tbl s .B
  marked : ∃ M3, Marked nm s3.nodes.val (tbl s3 .A) M3 ∧ insert tp M3 = M ∪ tp.subs
  grow : ∀ k, tbl s .A k ≠ none → tbl s3 .A k ≠ none
  cost : s3.ticks.val + 4 * (pending nm s3.nodes.val (tbl s3 .A) (S.erase tp)).card ≤
    s.ticks.val + 4 + 4 * (pending nm s.nodes.val (tbl s .A) (S.erase tp)).card

theorem closed_union {M : Finset Pat} {t : Pat} (hM : ∀ u ∈ M, u.subs ⊆ M) :
    ∀ u ∈ M ∪ t.subs, u.subs ⊆ M ∪ t.subs := by
  intro u hu
  rcases Finset.mem_union.1 hu with h | h
  · exact (hM u h).trans Finset.subset_union_left
  · exact (Term.subs_trans h).trans Finset.subset_union_right

theorem mark_spec_aux (hnm : Function.Injective nm) (n : Nat) :
    ∀ (s : store.Store) (p : store.TermId) (tp : Pat) (M S : Finset Pat),
      tp.size ≤ n → Inv s → Repr nm s.nodes.val p.val tp →
      Marked nm s.nodes.val (tbl s .A) M → (∀ u ∈ M, u.subs ⊆ M) → tp.subs ⊆ S →
      Room s (1 + 4 * (pending nm s.nodes.val (tbl s .A) S).card) →
      cover.mark s p ⦃ s' => MarkPost nm s s' M tp S ⦄ := by
  induction n with
  | zero =>
    intro s p tp M S hsz
    cases tp <;> simp [Term.size] at hsz
  | succ n ih =>
    intro s p tp M S hsz hI hp hM hcl hS hroom
    unfold cover.mark
    have hroom' := hroom
    unfold Room at hroom'
    step with get_flag_spec s .A p hI hp.lt (by unfold Room; omega) as ⟨o, s1, ho, hK1⟩
    have ht1 := hK1.ticks
    have hn1 := hK1.nodes
    cases hA : tbl s .A p.val with
    | some v =>
      rw [hA] at ho
      simp only [Option.map_some] at ho
      subst ho
      simp only [WP.spec_ok]
      have hin : tp ∈ M := (hM.iff hnm hI.nodesOK hp).1 (by rw [hA]; simp)
      have hun : M ∪ tp.subs = M := Finset.union_eq_left.2 (hcl tp hin)
      refine ⟨hK1.inv, hn1, by rw [hK1.tbl], ?_, fun k hk => by rw [hK1.tbl]; exact hk, ?_⟩
      · rw [hun, hn1, hK1.tbl]; exact hM
      · rw [hn1, hK1.tbl]; omega
    | none =>
      rw [hA] at ho
      simp only [Option.map_none] at ho
      subst ho
      have htS : tp ∈ S := hS (Term.self_mem_subs tp)
      have hpend := mem_pending_of_none hnm hI.nodesOK hp hA htS
      have hP := pending_erase_card hpend
      simp only
      step with read_spec s1 p hK1.inv (by rw [hn1]; exact hp.lt) (by unfold Room; omega)
        as ⟨nd, s2, hnd, hK2⟩
      rw [hn1] at hnd
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hn1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK1.tbl]
      refine WP.spec_bind (Pₘ := fun s3 => MarkMid nm s s3 M tp S) ?_ ?_
      · have hleaf : tp.subs = {tp} → MarkMid nm s s2 M tp S := by
          intro hsub
          refine ⟨hK2.inv, hn2, by rw [htb2], ⟨M, by rw [hn2, htb2]; exact hM, ?_⟩,
            (fun k hk => by rw [htb2]; exact hk), by rw [hn2, htb2]; omega⟩
          rw [hsub]
          ext u
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
          tauto
        cases nd with
        | V0 =>
          obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
          simp only [WP.spec_ok]
          exact hleaf (by rw [hv]; rfl)
        | VL a =>
          obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
          simp only [WP.spec_ok]
          exact hleaf (by rw [hv]; rfl)
        | VR a =>
          obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
          simp only [WP.spec_ok]
          exact hleaf (by rw [hv]; rfl)
        | Sym g =>
          simp only [WP.spec_ok]
          exact hleaf (by rw [hp.of_sym hnd]; rfl)
        | Nil =>
          simp only [WP.spec_ok]
          exact hleaf (by rw [hp.of_nil hnd]; rfl)
        | App a b =>
          obtain ⟨ta, tb, e, ha, hb⟩ := hp.of_app hnd
          subst e
          simp only [Term.size] at hsz
          have hSa := subs_left_erase hS
          have hSb := subs_right_erase hS
          simp only
          step with ih s2 a ta M (S.erase (Term.app ta tb)) (by omega) hK2.inv
            (by rw [hn2]; exact ha) (by rw [hn2, htb2]; exact hM) hcl hSa
            (by rw [hn2, htb2]; unfold Room; omega) as ⟨s4, h4⟩
          have hc4 := h4.cost
          rw [hn2, htb2] at hc4
          have hn4 : s4.nodes.val = s.nodes.val := by rw [h4.nodes, hn2]
          refine WP.spec_mono (ih s4 b tb (M ∪ ta.subs) (S.erase (Term.app ta tb)) (by omega)
            h4.inv (by rw [hn4]; exact hb) h4.marked (closed_union hcl) hSb
            (by unfold Room; omega)) ?_
          intro s5 h5
          have hc5 := h5.cost
          refine ⟨h5.inv, by rw [h5.nodes, hn4], by rw [h5.tblB, h4.tblB, htb2],
            ⟨_, h5.marked, ?_⟩, (fun k hk => h5.grow k (h4.grow k (by rw [htb2]; exact hk))),
            by omega⟩
          ext u
          simp only [Term.subs, Finset.mem_insert, Finset.mem_union]
          tauto
      · intro s3 hmid
        obtain ⟨M3, hM3, hins⟩ := hmid.marked
        have hc := hmid.cost
        have hp3 : Repr nm s3.nodes.val p.val tp := by rw [hmid.nodes]; exact hp
        refine WP.spec_mono (set_flag_spec s3 .A p true hmid.inv hp3.lt (by unfold Room; omega)) ?_
        rintro s' ⟨g1, g2, g3, g4, g5⟩
        refine ⟨g3, by rw [g1, hmid.nodes], by rw [g5 .B (by simp), hmid.tblB], ?_, ?_, ?_⟩
        · rw [← hins, g1, g4]
          refine ⟨fun k hk => ?_, fun t ht => ?_⟩
          · by_cases e : k = p.val
            · subst e; exact ⟨tp, Finset.mem_insert_self _ _, hp3⟩
            · rw [Function.update_of_ne e] at hk
              obtain ⟨t, ht, hr⟩ := hM3.sound k hk
              exact ⟨t, Finset.mem_insert_of_mem ht, hr⟩
          · rcases Finset.mem_insert.1 ht with rfl | ht
            · exact ⟨p.val, hp3, by simp⟩
            · obtain ⟨k, hr, hk⟩ := hM3.complete t ht
              refine ⟨k, hr, ?_⟩
              by_cases e : k = p.val
              · subst e; simp
              · rw [Function.update_of_ne e]; exact hk
        · intro k hk
          rw [g4]
          by_cases e : k = p.val
          · subst e; simp
          · rw [Function.update_of_ne e]; exact hmid.grow k hk
        · have hsub : pending nm s'.nodes.val (tbl s' .A) S ⊆
              pending nm s3.nodes.val (tbl s3 .A) (S.erase tp) := by
            have := pending_after_set (nm := nm) (nodes := s3.nodes.val) (more := [])
              (A := tbl s3 .A) (A' := tbl s' .A) (S := S) (t := tp) (p := p.val)
              (by simpa using hp3) (by rw [g4]; simp)
              (by
                intro k hk
                rw [g4]
                by_cases e : k = p.val
                · subst e; simp
                · rw [Function.update_of_ne e]; exact hk)
            simpa [g1] using this
          have h1 := Finset.card_le_card hsub
          omega

/-- `mark` flags every subterm of the term. It spends one tick, and four more
for each term of `S` that had no entry and gets one. -/
theorem mark_spec (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId) {tp : Pat}
    {M : Finset Pat} (S : Finset Pat) (hI : Inv s) (hp : Repr nm s.nodes.val p.val tp)
    (hM : Marked nm s.nodes.val (tbl s .A) M) (hcl : ∀ u ∈ M, u.subs ⊆ M) (hS : tp.subs ⊆ S)
    (hroom : Room s (1 + 4 * (pending nm s.nodes.val (tbl s .A) S).card)) :
    cover.mark s p ⦃ s' => MarkPost nm s s' M tp S ⦄ :=
  mark_spec_aux hnm tp.size s p tp M S (Nat.le_refl _) hI hp hM hcl hS hroom

/-! ## Are all variables of a term flagged? -/

/-- Every variable of `t` is in `M`. -/
def AllIn (M : Finset Pat) (t : Pat) : Prop := ∀ v ∈ t.vars, Term.var v ∈ M

instance (M : Finset Pat) (t : Pat) : Decidable (AllIn M t) := by
  unfold AllIn; infer_instance

/-- Every entry of table `B` is the answer for its key. -/
def AllOK (nm : Option Nat → Sym) (nodes : List store.Node) (B : Nat → Option Nat)
    (M : Finset Pat) : Prop :=
  ∀ k w, B k = some w → ∃ t, Repr nm nodes k t ∧ (w ≠ 0 ↔ AllIn M t)

/-- What `all_marked` leaves. -/
structure AllPost (nm : Option Nat → Sym) (s s' : store.Store) (M : Finset Pat) (t : Pat)
    (S : Finset Pat) (b : Bool) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  res : b = decide (AllIn M t)
  memo : AllOK nm s'.nodes.val (tbl s' .B) M
  tblA : tbl s' .A = tbl s .A
  grow : ∀ k, tbl s .B k ≠ none → tbl s' .B k ≠ none
  cost : s'.ticks.val + 5 * (pending nm s'.nodes.val (tbl s' .B) S).card ≤
    s.ticks.val + 1 + 5 * (pending nm s.nodes.val (tbl s .B) S).card

structure AllMid (nm : Option Nat → Sym) (s s3 : store.Store) (M : Finset Pat) (t : Pat)
    (S : Finset Pat) (b : Bool) : Prop where
  inv : Inv s3
  nodes : s3.nodes.val = s.nodes.val
  res : b = decide (AllIn M t)
  memo : AllOK nm s3.nodes.val (tbl s3 .B) M
  tblA : tbl s3 .A = tbl s .A
  grow : ∀ k, tbl s .B k ≠ none → tbl s3 .B k ≠ none
  cost : s3.ticks.val + 5 * (pending nm s3.nodes.val (tbl s3 .B) (S.erase t)).card ≤
    s.ticks.val + 5 + 5 * (pending nm s.nodes.val (tbl s .B) (S.erase t)).card

theorem allIn_app {M : Finset Pat} {a b : Pat} : AllIn M (.app a b) ↔ AllIn M a ∧ AllIn M b := by
  simp only [AllIn, Term.vars, List.mem_append]
  constructor
  · exact fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨h1, h2⟩ v (hv | hv)
    · exact h1 v hv
    · exact h2 v hv

theorem all_marked_spec_aux (hnm : Function.Injective nm) (n : Nat) :
    ∀ (s : store.Store) (p : store.TermId) (tp : Pat) (M S : Finset Pat),
      tp.size ≤ n → Inv s → Repr nm s.nodes.val p.val tp →
      Marked nm s.nodes.val (tbl s .A) M → AllOK nm s.nodes.val (tbl s .B) M → tp.subs ⊆ S →
      Room s (1 + 5 * (pending nm s.nodes.val (tbl s .B) S).card) →
      cover.all_marked s p ⦃ b s' => AllPost nm s s' M tp S b ⦄ := by
  induction n with
  | zero =>
    intro s p tp M S hsz
    cases tp <;> simp [Term.size] at hsz
  | succ n ih =>
    intro s p tp M S hsz hI hp hM hB hS hroom
    unfold cover.all_marked
    have hroom' := hroom
    unfold Room at hroom'
    step with get_flag_spec s .B p hI hp.lt (by unfold Room; omega) as ⟨o, s1, ho, hK1⟩
    have ht1 := hK1.ticks
    have hn1 := hK1.nodes
    cases hBp : tbl s .B p.val with
    | some w =>
      rw [hBp] at ho
      simp only [Option.map_some] at ho
      subst ho
      simp only [WP.spec_ok]
      obtain ⟨t', h1, h2⟩ := hB _ _ hBp
      have := hp.unique h1
      subst this
      refine ⟨hK1.inv, hn1, decide_eq_decide.2 h2, by rw [hn1, hK1.tbl]; exact hB, by rw [hK1.tbl],
        (fun k hk => by rw [hK1.tbl]; exact hk), by rw [hn1, hK1.tbl]; omega⟩
    | none =>
      rw [hBp] at ho
      simp only [Option.map_none] at ho
      subst ho
      have htS : tp ∈ S := hS (Term.self_mem_subs tp)
      have hpend := mem_pending_of_none hnm hI.nodesOK hp hBp htS
      have hP := pending_erase_card hpend
      simp only
      step with read_spec s1 p hK1.inv (by rw [hn1]; exact hp.lt) (by unfold Room; omega)
        as ⟨nd, s2, hnd, hK2⟩
      rw [hn1] at hnd
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hn1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK1.tbl]
      refine WP.spec_bind (Pₘ := fun r => AllMid nm s r.1 M tp S r.2) ?_ ?_
      · have hvar : ∀ v, tp = Term.var v →
            (do
              let (o1, s4) ← store.Store.get_flag s2 store.Tbl.A p
              let b1 := core.option.Option.is_some o1
              ok (s4, b1)) ⦃ r => AllMid nm s r.1 M tp S r.2 ⦄ := by
          intro v hv
          subst hv
          step with get_flag_spec s2 .A p hK2.inv (by rw [hn2]; exact hp.lt)
            (by unfold Room; omega) as ⟨o1, s4, ho1, hK4⟩
          have ht4 := hK4.ticks
          have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn2]
          have htb4 : tbl s4 = tbl s := by rw [hK4.tbl, htb2]
          refine ⟨hK4.inv, hn4, ?_, by rw [hn4, htb4]; exact hB, by rw [htb4],
            (fun k hk => by rw [htb4]; exact hk), by rw [hn4, htb4]; omega⟩
          have hiff := hM.iff hnm hI.nodesOK hp
          have hall : AllIn M (Term.var v) ↔ Term.var v ∈ M := by simp [AllIn, Term.vars]
          rw [htb2] at ho1
          by_cases hin : Term.var v ∈ M
          · have hne := hiff.2 hin
            obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
            simp [ho1, hw, hall, hin]
          · have hnone : tbl s .A p.val = none := by
              by_contra h; exact hin (hiff.1 h)
            simp [ho1, hnone, hall, hin]
        have hatom : (∀ v, v ∉ tp.vars) → AllMid nm s s2 M tp S true := by
          intro hv
          refine ⟨hK2.inv, hn2, ?_, by rw [hn2, htb2]; exact hB, by rw [htb2],
            (fun k hk => by rw [htb2]; exact hk), by rw [hn2, htb2]; omega⟩
          have : AllIn M tp := fun v h => absurd h (hv v)
          simp [this]
        cases nd with
        | V0 =>
          obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
          exact hvar v hv
        | VL a =>
          obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
          exact hvar v hv
        | VR a =>
          obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
          exact hvar v hv
        | Sym g =>
          simp only [WP.spec_ok]
          exact hatom (by rw [hp.of_sym hnd]; simp [Term.vars])
        | Nil =>
          simp only [WP.spec_ok]
          exact hatom (by rw [hp.of_nil hnd]; simp [Term.vars])
        | App a c =>
          obtain ⟨ta, tb, e, ha, hc⟩ := hp.of_app hnd
          subst e
          simp only [Term.size] at hsz
          have hSa := subs_left_erase hS
          have hSb := subs_right_erase hS
          simp only
          step with ih s2 a ta M (S.erase (Term.app ta tb)) (by omega) hK2.inv
            (by rw [hn2]; exact ha) (by rw [hn2, htb2]; exact hM) (by rw [hn2, htb2]; exact hB) hSa
            (by rw [hn2, htb2]; unfold Room; omega) as ⟨b1, s4, h4⟩
          have hc4 := h4.cost
          rw [hn2, htb2] at hc4
          have hn4 : s4.nodes.val = s.nodes.val := by rw [h4.nodes, hn2]
          cases b1 with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
            have hna : ¬ AllIn M ta := by simpa using h4.res.symm
            refine ⟨h4.inv, hn4, ?_, h4.memo, by rw [h4.tblA, htb2],
              (fun k hk => h4.grow k (by rw [htb2]; exact hk)), by omega⟩
            simp [allIn_app, hna]
          | true =>
            simp only [↓reduceIte]
            have hya : AllIn M ta := by simpa using h4.res.symm
            step with ih s4 c tb M (S.erase (Term.app ta tb)) (by omega) h4.inv
              (by rw [hn4]; exact hc) (by rw [hn4, h4.tblA, htb2]; exact hM) h4.memo hSb
              (by unfold Room; omega) as ⟨b2, s5, h5⟩
            have hc5 := h5.cost
            refine ⟨h5.inv, by rw [h5.nodes, hn4], ?_, h5.memo, by rw [h5.tblA, h4.tblA, htb2],
              (fun k hk => h5.grow k (h4.grow k (by rw [htb2]; exact hk))), by omega⟩
            rw [h5.res]
            simp [allIn_app, hya]
      · rintro ⟨s3, b⟩ hmid
        have hmid : AllMid nm s s3 M tp S b := hmid
        have hc := hmid.cost
        have hp3 : Repr nm s3.nodes.val p.val tp := by rw [hmid.nodes]; exact hp
        step with set_flag_spec s3 .B p b hmid.inv hp3.lt (by unfold Room; omega)
          as ⟨s4, g1, g2, g3, g4, g5⟩
        refine ⟨g3, by rw [g1, hmid.nodes], hmid.res, ?_, by rw [g5 .A (by simp), hmid.tblA], ?_, ?_⟩
        · rw [g1, g4]
          intro k w hk
          by_cases e : k = p.val
          · subst e
            simp only [Function.update_self, Option.some.injEq] at hk
            subst hk
            refine ⟨tp, hp3, ?_⟩
            rw [hmid.res]
            by_cases h : AllIn M tp <;> simp [h]
          · rw [Function.update_of_ne e] at hk
            exact hmid.memo k w hk
        · intro k hk
          rw [g4]
          by_cases e : k = p.val
          · subst e; simp
          · rw [Function.update_of_ne e]; exact hmid.grow k hk
        · have hsub : pending nm s4.nodes.val (tbl s4 .B) S ⊆
              pending nm s3.nodes.val (tbl s3 .B) (S.erase tp) := by
            have := pending_after_set (nm := nm) (nodes := s3.nodes.val) (more := [])
              (A := tbl s3 .B) (A' := tbl s4 .B) (S := S) (t := tp) (p := p.val)
              (by simpa using hp3) (by rw [g4]; simp)
              (by
                intro k hk
                rw [g4]
                by_cases e : k = p.val
                · subst e; simp
                · rw [Function.update_of_ne e]; exact hk)
            simpa [g1] using this
          have h1 := Finset.card_le_card hsub
          omega

/-- `all_marked` answers whether every variable of the term is flagged. It
spends one tick, and five more for each term of `S` that had no answer and
gets one. -/
theorem all_marked_spec (hnm : Function.Injective nm) (s : store.Store) (p : store.TermId)
    {tp : Pat} {M : Finset Pat} (S : Finset Pat) (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val tp) (hM : Marked nm s.nodes.val (tbl s .A) M)
    (hB : AllOK nm s.nodes.val (tbl s .B) M) (hS : tp.subs ⊆ S)
    (hroom : Room s (1 + 5 * (pending nm s.nodes.val (tbl s .B) S).card)) :
    cover.all_marked s p ⦃ b s' => AllPost nm s s' M tp S b ⦄ :=
  all_marked_spec_aux hnm tp.size s p tp M S (Nat.le_refl _) hI hp hM hB hS hroom

theorem AllOK.extends {s s' : store.Store} {B : Nat → Option Nat} {M : Finset Pat}
    (h : AllOK nm s.nodes.val B M) (he : Extends s s') : AllOK nm s'.nodes.val B M :=
  fun k w hk => by
    obtain ⟨t, hr, hw⟩ := h k w hk
    exact ⟨t, he.repr hr, hw⟩

/-! ## Filtering the constraints -/

/-- What `keep` leaves. -/
structure KeepPost (nm : Option Nat → Sym) (s s' : store.Store) (M : Finset Pat) (cs : List Pat)
    (S : Finset Pat) (r : store.TermId) : Prop where
  inv : Inv s'
  ext : Extends s s'
  repr : Repr nm s'.nodes.val r.val (encList (nm none) (cs.filter fun a => decide (AllIn M a)))
  memo : AllOK nm s'.nodes.val (tbl s' .B) M
  tblA : tbl s' .A = tbl s .A
  cost : s'.ticks.val + 5 * (pending nm s'.nodes.val (tbl s' .B) S).card ≤
    s.ticks.val + 1 + 3 * cs.length + 5 * (pending nm s.nodes.val (tbl s .B) S).card

/-- `keep` returns the constraints whose variables are all flagged, in their
order. It spends one tick, three for each constraint, and five for each
term of `S` that had no answer and gets one. -/
theorem keep_spec (hnm : Function.Injective nm) (M S : Finset Pat) :
    ∀ (cs : List Pat) (s : store.Store) (c : store.TermId), Inv s →
      Repr nm s.nodes.val c.val (encList (nm none) cs) →
      Marked nm s.nodes.val (tbl s .A) M → AllOK nm s.nodes.val (tbl s .B) M →
      (∀ a ∈ cs, a.subs ⊆ S) →
      Room s (1 + 3 * cs.length + 5 * (pending nm s.nodes.val (tbl s .B) S).card) →
      cover.keep s c ⦃ r s' => KeepPost nm s s' M cs S r ⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro s c hI hc hM hB hS hroom
    unfold cover.keep
    step with read_spec s c hI hc.lt (by unfold Room at hroom ⊢; omega) as ⟨nd, s1, hnd, hK⟩
    have hfin : KeepPost nm s s1 M [] S c :=
      ⟨hK.inv, Extends.of_eq hK.nodes, by rw [hK.nodes]; exact hc,
        by rw [hK.nodes, hK.tbl]; exact hB, by rw [hK.tbl],
        by have := hK.ticks; rw [hK.nodes, hK.tbl]; simp only [List.length_nil]; omega⟩
    cases nd with
    | App h t =>
      obtain ⟨ta, tb, e', -, -⟩ := hc.of_app hnd
      cases e'
    | V0 => step*
    | VL _ => step*
    | VR _ => step*
    | Sym _ => step*
    | Nil => step*
  | cons a ts ih =>
    intro s c hI hc hM hB hS hroom
    unfold cover.keep
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    step with read_spec s c hI hc.lt (by unfold Room; omega) as ⟨nd, s1, hnd, hK⟩
    obtain ⟨h, t, hnode, hh, ht⟩ := Repr.app_inv (ta := a) (tb := encList (nm none) ts) hc
    rw [hnode] at hnd
    cases hnd
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    simp only
    step with ih s1 t hK.inv (by rw [hn1]; exact ht) (by rw [hn1, hK.tbl]; exact hM)
      (by rw [hn1, hK.tbl]; exact hB) (fun x hx => hS x (List.mem_cons_of_mem _ hx))
      (by rw [hn1, hK.tbl]; unfold Room; omega) as ⟨r, s2, h2⟩
    have hc2 := h2.cost
    rw [hn1, hK.tbl] at hc2
    have hx2 : Extends s s2 := (Extends.of_eq hn1).trans h2.ext
    have hM2 : Marked nm s2.nodes.val (tbl s2 .A) M := by
      rw [h2.tblA, hK.tbl]; exact hM.extends hx2
    step with all_marked_spec hnm s2 h S h2.inv (hx2.repr hh) hM2 h2.memo
      (hS a List.mem_cons_self) (by unfold Room; omega) as ⟨b, s3, h3⟩
    have hc3 := h3.cost
    have hx3 : Extends s s3 := hx2.trans (Extends.of_eq h3.nodes)
    have hr3 : Repr nm s3.nodes.val r.val
        (encList (nm none) (ts.filter fun a => decide (AllIn M a))) := by
      rw [h3.nodes]; exact h2.repr
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hna : ¬ AllIn M a := by simpa using h3.res.symm
      refine ⟨h3.inv, hx3, ?_, h3.memo, by rw [h3.tblA, h2.tblA, hK.tbl],
        by simp only [List.length_cons]; omega⟩
      have e : (a :: ts).filter (fun a => decide (AllIn M a)) =
          ts.filter (fun a => decide (AllIn M a)) := by simp [hna]
      rw [e]; exact hr3
    | true =>
      simp only [↓reduceIte]
      have hya : AllIn M a := by simpa using h3.res.symm
      step with alloc_spec s3 (.App h r) h3.inv ⟨(hx3.repr hh).lt, hr3.lt⟩ (by unfold Room; omega)
        as ⟨o, s4, hI4, ht4, htb4, m4, hm4, hr4⟩
      have hx4 : Extends s3 s4 := ⟨m4, hm4⟩
      simp only [norm] at hr4
      have hpm : pending nm s4.nodes.val (tbl s4 .B) S ⊆ pending nm s3.nodes.val (tbl s3 .B) S := by
        rw [hm4, htb4]; exact pending_mono (fun k hk => hk)
      have hcard := Finset.card_le_card hpm
      refine ⟨hI4, hx3.trans hx4, ?_, by rw [htb4]; exact h3.memo.extends hx4,
        by rw [htb4, h3.tblA, h2.tblA, hK.tbl], by simp only [List.length_cons]; omega⟩
      have e : (a :: ts).filter (fun a => decide (AllIn M a)) =
          a :: ts.filter (fun a => decide (AllIn M a)) := by simp [hya]
      rw [e]
      exact .app hr4 (hx4.repr (hx3.repr hh)) (hx4.repr hr3)

/-! ## The interface -/

theorem cover_is_var_spec (s : store.Store) (p : store.TermId) {tp : Pat} (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val tp) (hroom : Room s 1) :
    cover.is_var s p ⦃ b s' => (b = true ↔ ∃ v, tp = Term.var v) ∧ Kept s s' 1 ⦄ := by
  unfold cover.is_var
  step with read_spec s p hI hp.lt hroom as ⟨nd, s1, hnd, hK⟩
  cases nd with
  | V0 =>
    obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
    simp only [WP.spec_ok]
    exact ⟨by simp [hv], hK⟩
  | VL a =>
    obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
    simp only [WP.spec_ok]
    exact ⟨by simp [hv], hK⟩
  | VR a =>
    obtain ⟨v, hv, -⟩ := hp.of_var hnd trivial
    simp only [WP.spec_ok]
    exact ⟨by simp [hv], hK⟩
  | Sym g =>
    simp only [WP.spec_ok]
    exact ⟨by simp [hp.of_sym hnd], hK⟩
  | Nil =>
    simp only [WP.spec_ok]
    exact ⟨by simp [hp.of_nil hnd], hK⟩
  | App a b =>
    obtain ⟨ta, tb, e, -, -⟩ := hp.of_app hnd
    simp only [WP.spec_ok]
    exact ⟨by simp [e], hK⟩

theorem cover_is_nil_spec (hnm : Function.Injective nm) (s : store.Store) (c : store.TermId)
    {cs : List Pat} (hI : Inv s) (hc : Repr nm s.nodes.val c.val (encList (nm none) cs))
    (hroom : Room s 1) :
    cover.is_nil s c ⦃ b s' => (b = true ↔ cs = []) ∧ Kept s s' 1 ⦄ := by
  unfold cover.is_nil
  step with read_spec s c hI hc.lt hroom as ⟨nd, s1, hnd, hK⟩
  cases nd with
  | V0 =>
    obtain ⟨v, hv, -⟩ := hc.of_var hnd trivial
    have : cs ≠ [] := by rintro rfl; simp [encList] at hv
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | VL a =>
    obtain ⟨v, hv, -⟩ := hc.of_var hnd trivial
    have : cs ≠ [] := by rintro rfl; simp [encList] at hv
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | VR a =>
    obtain ⟨v, hv, -⟩ := hc.of_var hnd trivial
    have : cs ≠ [] := by rintro rfl; simp [encList] at hv
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | Sym g =>
    have e := hc.of_sym hnd
    have : cs ≠ [] := by
      rintro rfl
      simp only [encList, Term.sym.injEq] at e
      exact absurd (hnm e) (by simp)
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | Nil =>
    have : cs = [] := encList_of_not_app hc hnd (by simp)
    simp only [WP.spec_ok]
    exact ⟨by simp [this], hK⟩
  | App a b =>
    obtain ⟨t, ts, e, -, -⟩ := encList_of_app hc hnd
    simp only [WP.spec_ok]
    exact ⟨by simp [e], hK⟩

/-- The ticks an interface may spend: linear in the distinct subterms of the
side and of the constraints, and in the number of constraints. -/
def ifaceCost (tp : Pat) (cs : List Pat) : Nat :=
  6 + 4 * tp.subs.card + 3 * cs.length + 5 * (cs.toFinset.biUnion Term.subs).card

/-- `iface` returns the interface at the side `tp` of a span with
constraints `cs`, as a boundary, within `ifaceCost` ticks. -/
theorem iface_spec (hnm : Function.Injective nm) (s : store.Store) (p c : store.TermId)
    {tp : Pat} {cs : List Pat} (hI : Inv s) (hp : Repr nm s.nodes.val p.val tp)
    (hc : Repr nm s.nodes.val c.val (encList (nm none) cs)) (hroom : Room s (ifaceCost tp cs)) :
    cover.iface s p c ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
      OptSpanAt nm s'.nodes.val r
        (bound ⟨tp, tp, cs.filter fun a => a.vars.all (· ∈ tp.vars)⟩) ∧
      s'.ticks.val ≤ s.ticks.val + ifaceCost tp cs ⦄ := by
  unfold cover.iface
  have hroom' := hroom
  unfold Room ifaceCost at hroom'
  step with clear_spec s .A hI (by unfold Room; omega) as ⟨s1, hn1, ht1, hI1, hA1, ho1⟩
  have hM1 : Marked nm s1.nodes.val (tbl s1 .A) ∅ :=
    ⟨fun k hk => absurd (hA1 k) hk, fun t ht => by simp at ht⟩
  have hP1 := pending_card_le (nm := nm) s1.nodes.val (tbl s1 .A) tp.subs
  step with mark_spec hnm s1 p tp.subs hI1 (by rw [hn1]; exact hp) hM1 (by simp)
    (Finset.Subset.refl _) (by unfold Room; omega) as ⟨s2, h2⟩
  have hc2 := h2.cost
  have hn2 : s2.nodes.val = s.nodes.val := by rw [h2.nodes, hn1]
  step with clear_spec s2 .B h2.inv (by unfold Room; omega) as ⟨s3, hn3, ht3, hI3, hB3, ho3⟩
  have hn3' : s3.nodes.val = s.nodes.val := by rw [hn3, hn2]
  have hM3 : Marked nm s3.nodes.val (tbl s3 .A) tp.subs := by
    rw [hn3, ho3 .A (by simp)]; simpa using h2.marked
  have hB3' : AllOK nm s3.nodes.val (tbl s3 .B) tp.subs := fun k w hk => by
    rw [hB3 k] at hk; cases hk
  have hP3 := pending_card_le (nm := nm) s3.nodes.val (tbl s3 .B) (cs.toFinset.biUnion Term.subs)
  step with keep_spec hnm tp.subs (cs.toFinset.biUnion Term.subs) cs s3 c hI3
    (by rw [hn3']; exact hc) hM3 hB3'
    (fun a ha => Finset.subset_biUnion_of_mem Term.subs (List.mem_toFinset.2 ha))
    (by unfold Room; omega) as ⟨c2, s4, h4⟩
  have hc4 := h4.cost
  have hx4 : Extends s s4 := (Extends.of_eq hn3').trans h4.ext
  have hfilt : cs.filter (fun a => decide (AllIn tp.subs a)) =
      cs.filter (fun a => a.vars.all (· ∈ tp.vars)) := by
    apply List.filter_congr
    intro a _
    simp only [AllIn, var_mem_subs_iff]
    rw [Bool.eq_iff_iff]; simp [List.all_eq_true]
  have hrc := h4.repr
  rw [hfilt] at hrc
  step with cover_is_var_spec s4 p h4.inv (hx4.repr hp) (by unfold Room; omega) as ⟨b, s5, hb, hK5⟩
  have ht5 := hK5.ticks
  refine WP.spec_bind (Pₘ := fun r => Inv r.1 ∧ r.1.nodes.val = s4.nodes.val ∧
    r.1.ticks.val ≤ s5.ticks.val + 1 ∧
    (r.2 = true ↔ (∃ v, tp = Term.var v) ∧
      cs.filter (fun a => a.vars.all (· ∈ tp.vars)) = [])) ?_ ?_
  · cases b with
    | true =>
      simp only [↓reduceIte]
      step with cover_is_nil_spec hnm s5 c2 hK5.inv (by rw [hK5.nodes]; exact hrc)
        (by unfold Room; omega) as ⟨b1, s7, hb1, hK7⟩
      refine ⟨hK7.inv, by rw [hK7.nodes, hK5.nodes], by have := hK7.ticks; omega, ?_⟩
      exact ⟨fun h => ⟨hb.1 rfl, hb1.1 h⟩, fun h => hb1.2 h.2⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨hK5.inv, hK5.nodes, by omega, ?_⟩
      constructor
      · intro h; cases h
      · rintro ⟨hv, -⟩; exact absurd (hb.2 hv) (by simp)
  · rintro ⟨s6, tr⟩ hmid
    have hmid : Inv s6 ∧ s6.nodes.val = s4.nodes.val ∧ s6.ticks.val ≤ s5.ticks.val + 1 ∧
        (tr = true ↔ (∃ v, tp = Term.var v) ∧
          cs.filter (fun a => a.vars.all (· ∈ tp.vars)) = []) := hmid
    obtain ⟨hI6, hn6, ht6, htr⟩ := hmid
    have hx6 : Extends s s6 := hx4.trans (Extends.of_eq hn6)
    have hticks : s6.ticks.val ≤ s.ticks.val + ifaceCost tp cs := by unfold ifaceCost; omega
    cases tr with
    | true =>
      simp only [uncurry_apply_pair, ↓reduceIte, WP.spec_ok]
      obtain ⟨⟨v, hv⟩, hnil⟩ := htr.1 rfl
      refine ⟨hI6, hx6, ?_, hticks⟩
      rw [hnil]; subst hv; simp [bound, OptSpanAt]
    | false =>
      simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨hI6, hx6, ?_, hticks⟩
      have hbd : bound ⟨tp, tp, cs.filter fun a => a.vars.all (· ∈ tp.vars)⟩ =
          some ⟨tp, tp, cs.filter fun a => a.vars.all (· ∈ tp.vars)⟩ := by
        unfold bound
        split
        · next v h1 h2 => exact absurd (htr.2 ⟨⟨v, h1⟩, h2⟩) (by simp)
        · rfl
      rw [hbd]
      exact ⟨hx6.repr hp, hx6.repr hp, by rw [hn6]; exact hrc⟩

/-- `right_bound` returns the specification's right interface of the span,
as a boundary, within `ifaceCost` ticks. -/
theorem right_bound_spec (hnm : Function.Injective nm) (s : store.Store) (x : span.Span)
    {sx : Span} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sx)
    (hroom : Room s (ifaceCost sx.r sx.c)) :
    cover.right_bound s x ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ OptSpanAt nm s'.nodes.val r (bound sx.rightIface) ∧
      s'.ticks.val ≤ s.ticks.val + ifaceCost sx.r sx.c ⦄ := by
  unfold cover.right_bound
  exact iface_spec hnm s x.r x.c hI hx.r hx.c hroom

/-- `left_bound` returns the specification's left interface of the span, as
a boundary, within `ifaceCost` ticks. -/
theorem left_bound_spec (hnm : Function.Injective nm) (s : store.Store) (x : span.Span)
    {sx : Span} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sx)
    (hroom : Room s (ifaceCost sx.l sx.c)) :
    cover.left_bound s x ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ OptSpanAt nm s'.nodes.val r (bound sx.leftIface) ∧
      s'.ticks.val ≤ s.ticks.val + ifaceCost sx.l sx.c ⦄ := by
  unfold cover.left_bound
  exact iface_spec hnm s x.l x.c hI hx.l hx.c hroom

end RwLogVerified
