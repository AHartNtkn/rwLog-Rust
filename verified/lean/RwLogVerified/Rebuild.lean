/-
# Rebuilding a term: the Rust `rebuild` computes `Term.bind`

`rebuild s f p` copies the term at `p` with its variables replaced as `f`
says. Table `A` remembers what each node visited became, so a node is
rebuilt once however often it occurs.

`rebuild_spec`: the result stands for `t.bind σ`, where `σ` is the
substitution `f` stands for (`LeafOK`), and the cost is one tick plus five
for each term that gets a table entry. `pending S` is the set of members of
`S` without an entry; the statement holds for every set `S` that contains
the subterms of `t`, so a second call that shares the table pays only for
what the first did not visit.
-/
import RwLogVerified.Repr

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

/-- `s'` has the nodes of `s`, and maybe more. -/
def Extends (s s' : store.Store) : Prop := ∃ more, s'.nodes.val = s.nodes.val ++ more

theorem Extends.refl (s : store.Store) : Extends s s := ⟨[], by simp⟩

theorem Extends.trans {a b c : store.Store} (h₁ : Extends a b) (h₂ : Extends b c) : Extends a c := by
  obtain ⟨m₁, e₁⟩ := h₁
  obtain ⟨m₂, e₂⟩ := h₂
  exact ⟨m₁ ++ m₂, by rw [e₂, e₁, List.append_assoc]⟩

theorem Extends.of_eq {a b : store.Store} (h : b.nodes.val = a.nodes.val) : Extends a b :=
  ⟨[], by simp [h]⟩

theorem Extends.repr {s s' : store.Store} (h : Extends s s') {i : Nat} {t : Pat}
    (hr : Repr nm s.nodes.val i t) : Repr nm s'.nodes.val i t := by
  obtain ⟨m, e⟩ := h
  rw [e]; exact hr.append m

theorem Extends.varAt {s s' : store.Store} (h : Extends s s') {i n : Nat}
    (hr : VarAt s.nodes.val i n) : VarAt s'.nodes.val i n := by
  obtain ⟨m, e⟩ := h
  rw [e]; exact hr.append m

/-! ## The terms of a set that have no table entry yet -/

open Classical in
/-- The members of `S` that no identifier with an entry in `A` stands for. -/
noncomputable def pending (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat)
    (S : Finset Pat) : Finset Pat :=
  S.filter fun u => ¬ ∃ k, Repr nm nodes k u ∧ A k ≠ none

theorem mem_pending {nodes : List store.Node} {A : Nat → Option Nat} {S : Finset Pat} {u : Pat} :
    u ∈ pending nm nodes A S ↔ u ∈ S ∧ ¬ ∃ k, Repr nm nodes k u ∧ A k ≠ none := by
  simp [pending]

theorem pending_erase_card {nodes : List store.Node} {A : Nat → Option Nat} {S : Finset Pat}
    {t : Pat} (ht : t ∈ pending nm nodes A S) :
    (pending nm nodes A (S.erase t)).card + 1 = (pending nm nodes A S).card := by
  have e : pending nm nodes A (S.erase t) = (pending nm nodes A S).erase t := by
    ext u
    simp only [mem_pending, Finset.mem_erase]
    tauto
  rw [e, Finset.card_erase_of_mem ht]
  have := Finset.card_pos.2 ⟨t, ht⟩
  omega

/-- Giving the identifier of `t` an entry takes `t` out of the pending terms,
and later states have no more pending terms than earlier ones. -/
theorem pending_after_set {nodes more : List store.Node} {A A' : Nat → Option Nat}
    {S : Finset Pat} {t : Pat} {p : Nat} (hp : Repr nm (nodes ++ more) p t) (hA' : A' p ≠ none)
    (hA : ∀ k, A k ≠ none → A' k ≠ none) :
    pending nm (nodes ++ more) A' S ⊆ pending nm nodes A (S.erase t) := by
  intro u hu
  rw [mem_pending] at hu ⊢
  refine ⟨Finset.mem_erase.2 ⟨?_, hu.1⟩, ?_⟩
  · rintro rfl
    exact hu.2 ⟨p, hp, hA'⟩
  · rintro ⟨k, hk, hAk⟩
    exact hu.2 ⟨k, hk.append more, hA k hAk⟩

theorem pending_mono {nodes more : List store.Node} {A A' : Nat → Option Nat} {S : Finset Pat}
    (hA : ∀ k, A k ≠ none → A' k ≠ none) :
    pending nm (nodes ++ more) A' S ⊆ pending nm nodes A S := by
  intro u hu
  rw [mem_pending] at hu ⊢
  refine ⟨hu.1, ?_⟩
  rintro ⟨k, hk, hAk⟩
  exact hu.2 ⟨k, hk.append more, hA k hAk⟩

/-! ## What a leaf function and a table of rebuilt nodes stand for -/

/-- The substitution a leaf function stands for. -/
def LeafOK (nm : Option Nat → Sym) (nodes : List store.Node) (f : term.Leaf) (σ : Nat → Pat) :
    Prop :=
  match f with
  | .Left => σ = fun v => Term.var (2 * v)
  | .Right => σ = fun v => Term.var (2 * v + 1)
  | .Sub x u => ∃ xv tu, VarAt nodes x.val xv ∧ Repr nm nodes u.val tu ∧ σ = Term.single xv tu

theorem LeafOK.append {nodes : List store.Node} {f : term.Leaf} {σ : Nat → Pat}
    (h : LeafOK nm nodes f σ) (more : List store.Node) : LeafOK nm (nodes ++ more) f σ := by
  cases f with
  | Left => exact h
  | Right => exact h
  | Sub x u =>
    obtain ⟨xv, tu, hx, hu, e⟩ := h
    exact ⟨xv, tu, hx.append more, hu.append more, e⟩

theorem LeafOK.extends {s s' : store.Store} {f : term.Leaf} {σ : Nat → Pat}
    (h : LeafOK nm s.nodes.val f σ) (he : Extends s s') : LeafOK nm s'.nodes.val f σ := by
  obtain ⟨m, e⟩ := he
  rw [e]; exact h.append m

/-- Every entry of the table holds what its key became. -/
def MemoOK (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat)
    (σ : Nat → Pat) : Prop :=
  ∀ k v, A k = some v → ∃ t, Repr nm nodes k t ∧ Repr nm nodes v (t.bind σ)

theorem MemoOK.extends {s s' : store.Store} {A : Nat → Option Nat} {σ : Nat → Pat}
    (h : MemoOK nm s.nodes.val A σ) (he : Extends s s') : MemoOK nm s'.nodes.val A σ := by
  intro k v hk
  obtain ⟨t, h₁, h₂⟩ := h k v hk
  exact ⟨t, he.repr h₁, he.repr h₂⟩

theorem leaf_spec (s : store.Store) (f : term.Leaf) (p : store.TermId) {σ : Nat → Pat} {v : Nat}
    (hI : Inv s) (hv : VarAt s.nodes.val p.val v) (hf : LeafOK nm s.nodes.val f σ)
    (hroom : Room s 1) :
    term.leaf s f p ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ Repr nm s'.nodes.val r.val (σ v) ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 1 ⦄ := by
  unfold term.leaf
  cases f with
  | Left =>
    simp only [LeafOK] at hf
    subst hf
    step with alloc_spec s (.VL p) hI hv.node hroom as ⟨r, s', hI', ht, htbl, more, hmore, hr⟩
    have hext : Extends s s' := ⟨more, hmore⟩
    refine ⟨hI', hext, ?_, htbl, by omega⟩
    simp only [norm] at hr
    split at hr
    · rename_i h0
      have hv0 : v = 0 := by
        have h1 : VarAt s.nodes.val p.val 0 := by rw [h0]; exact .zero hI.root
        exact hv.unique h1
      subst hv0
      exact .var (.zero hr)
    · exact .var (.left hr (Extends.varAt hext hv))
  | Right =>
    simp only [LeafOK] at hf
    subst hf
    step with alloc_spec s (.VR p) hI hv.node hroom as ⟨r, s', hI', ht, htbl, more, hmore, hr⟩
    have hext : Extends s s' := ⟨more, hmore⟩
    refine ⟨hI', hext, ?_, htbl, by omega⟩
    simp only [norm] at hr
    exact .var (.right hr (Extends.varAt hext hv))
  | Sub x u =>
    obtain ⟨xv, tu, hx, hu, e⟩ := hf
    subst e
    step with same_spec s p x hI hroom as ⟨b, s1, hb, hK⟩
    have hext : Extends s s1 := Extends.of_eq hK.nodes
    split
    · rename_i hbt
      have hpx : p.val = x.val := by simpa [hb] using hbt
      have : v = xv := by rw [hpx] at hv; exact hv.unique hx
      subst this
      step*
      refine ⟨hK.inv, hext, ?_, hK.tbl, by have := hK.ticks; omega⟩
      simp only [Term.single, ↓reduceIte]
      exact hext.repr hu
    · rename_i hbf
      have hpx : p.val ≠ x.val := by simpa [hb] using hbf
      have hne : v ≠ xv := by
        rintro rfl
        exact hpx (hv.inj hI.nodesOK hx)
      step*
      refine ⟨hK.inv, hext, ?_, hK.tbl, by have := hK.ticks; omega⟩
      simp only [Term.single, hne, ↓reduceIte]
      exact .var (hext.varAt hv)

/-! ## Rebuilding -/

theorem mem_pending_of_none (hnm : Function.Injective nm) {nodes : List store.Node}
    (hN : NodesOK nodes) {A : Nat → Option Nat} {S : Finset Pat} {t : Pat} {p : Nat}
    (hp : Repr nm nodes p t) (hA : A p = none) (ht : t ∈ S) : t ∈ pending nm nodes A S := by
  rw [mem_pending]
  refine ⟨ht, ?_⟩
  rintro ⟨k, hk, hAk⟩
  rw [Repr.inj hnm hN hk hp] at hAk
  exact hAk hA

/-- What `rebuild` leaves: the result stands for `t.bind σ`, the table is
still right and only gained entries, table `B` is untouched, and the ticks
spent are one plus five for each term of `S` that got an entry. -/
structure RebuildPost (nm : Option Nat → Sym) (s s' : store.Store) (σ : Nat → Pat) (t : Pat)
    (S : Finset Pat) (r : store.TermId) : Prop where
  inv : Inv s'
  ext : Extends s s'
  repr : Repr nm s'.nodes.val r.val (t.bind σ)
  memo : MemoOK nm s'.nodes.val (tbl s' .A) σ
  tblB : tbl s' .B = tbl s .B
  keep : ∀ k v, tbl s .A k = some v → tbl s' .A k = some v
  cost : s'.ticks.val + 5 * (pending nm s'.nodes.val (tbl s' .A) S).card ≤
    s.ticks.val + 1 + 5 * (pending nm s.nodes.val (tbl s .A) S).card

/-- The last step of a miss: the result `r`, computed in `s3`, is written to
the table. -/
theorem rebuild_finish (hnm : Function.Injective nm) {s s3 s' : store.Store} {σ : Nat → Pat}
    {t : Pat} {S : Finset Pat} {p r : store.TermId}
    (hI : Inv s) (hp : Repr nm s.nodes.val p.val t) (hnone : tbl s .A p.val = none) (htS : t ∈ S)
    (hext : Extends s s3) (hr : Repr nm s3.nodes.val r.val (t.bind σ))
    (hM : MemoOK nm s3.nodes.val (tbl s3 .A) σ) (hB : tbl s3 .B = tbl s .B)
    (hkeep : ∀ k v, tbl s .A k = some v → tbl s3 .A k = some v)
    (hc : s3.ticks.val + 5 * (pending nm s3.nodes.val (tbl s3 .A) (S.erase t)).card ≤
      s.ticks.val + 5 * (pending nm s.nodes.val (tbl s .A) (S.erase t)).card + 5)
    (g1 : s'.nodes.val = s3.nodes.val) (g2 : s'.ticks.val = s3.ticks.val + 1) (g3 : Inv s')
    (g4 : tbl s' .A = Function.update (tbl s3 .A) p.val (some r.val))
    (g5 : ∀ t', t' ≠ store.Tbl.A → tbl s' t' = tbl s3 t') :
    RebuildPost nm s s' σ t S r := by
  have hp3 : Repr nm s3.nodes.val p.val t := hext.repr hp
  refine ⟨g3, hext.trans (Extends.of_eq g1), by rw [g1]; exact hr, ?_, ?_, ?_, ?_⟩
  · intro k v hk
    rw [g1]
    rw [g4] at hk
    by_cases e : k = p.val
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hk
      subst hk
      exact ⟨t, hp3, hr⟩
    · rw [Function.update_of_ne e] at hk
      exact hM k v hk
  · rw [g5 .B (by simp), hB]
  · intro k v hk
    rw [g4]
    by_cases e : k = p.val
    · subst e; rw [hnone] at hk; cases hk
    · rw [Function.update_of_ne e]; exact hkeep k v hk
  · have hsub : pending nm s'.nodes.val (tbl s' .A) S ⊆
        pending nm s3.nodes.val (tbl s3 .A) (S.erase t) := by
      have := pending_after_set (nm := nm) (nodes := s3.nodes.val) (more := []) (A := tbl s3 .A)
        (A' := tbl s' .A) (S := S) (t := t) (p := p.val) (by simpa using hp3)
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

theorem subs_left_erase {ta tb : Pat} {S : Finset Pat} (hS : (Term.app ta tb).subs ⊆ S) :
    ta.subs ⊆ S.erase (Term.app ta tb) := by
  intro u hu
  refine Finset.mem_erase.2 ⟨?_, hS (by simp [Term.subs, hu])⟩
  rintro rfl
  have := Term.size_le_of_mem_subs hu
  simp only [Term.size] at this
  omega

theorem subs_right_erase {ta tb : Pat} {S : Finset Pat} (hS : (Term.app ta tb).subs ⊆ S) :
    tb.subs ⊆ S.erase (Term.app ta tb) := by
  intro u hu
  refine Finset.mem_erase.2 ⟨?_, hS (by simp [Term.subs, hu])⟩
  rintro rfl
  have := Term.size_le_of_mem_subs hu
  simp only [Term.size] at this
  omega

theorem rebuild_spec_aux (hnm : Function.Injective nm) (n : Nat) :
    ∀ (s : store.Store) (f : term.Leaf) (p : store.TermId) (t : Pat) (σ : Nat → Pat)
      (S : Finset Pat), t.size ≤ n → Inv s → Repr nm s.nodes.val p.val t →
      LeafOK nm s.nodes.val f σ → MemoOK nm s.nodes.val (tbl s .A) σ → t.subs ⊆ S →
      Room s (1 + 5 * (pending nm s.nodes.val (tbl s .A) S).card) →
      term.rebuild s f p ⦃ r s' => RebuildPost nm s s' σ t S r ⦄ := by
  induction n with
  | zero =>
    intro s f p t σ S hsz
    cases t <;> simp [Term.size] at hsz
  | succ n ih =>
    intro s f p t σ S hsz hI hp hf hM hS hroom
    unfold term.rebuild
    step with get_spec s .A p hI hp.lt (hroom.mono (by omega)) as ⟨o, s1, ho, hK1⟩
    cases o with
    | some r =>
      simp only [Option.map_some] at ho
      simp only
      step*
      obtain ⟨t', h1, h2⟩ := hM _ _ ho.symm
      have := hp.unique h1
      subst this
      refine ⟨hK1.inv, Extends.of_eq hK1.nodes, by rw [hK1.nodes]; exact h2, ?_, by rw [hK1.tbl],
        fun k v hk => by rw [hK1.tbl]; exact hk, ?_⟩
      · rw [hK1.nodes, hK1.tbl]; exact hM
      · rw [hK1.nodes, hK1.tbl]; have := hK1.ticks; omega
    | none =>
      simp only [Option.map_none] at ho
      have hnone : tbl s .A p.val = none := ho.symm
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
      have hext2 : Extends s s2 := Extends.of_eq hn2
      have hleaf : ∀ v, t = Term.var v → VarAt s.nodes.val p.val v →
          (do
            let (s3, r) ← (do
              let (r1, s4) ← term.leaf s2 f p
              ok (s4, r1))
            let s4 ← store.Store.set s3 store.Tbl.A p r
            ok (r, s4)) ⦃ r s' => RebuildPost nm s s' σ t S r ⦄ := by
        intro v hv hva
        subst hv
        step with leaf_spec (nm := nm) s2 f p (σ := σ) (v := v) hK2.inv (by rw [hn2]; exact hva)
          (by rw [hn2]; exact hf) (by unfold Room; omega) as ⟨x, hI4, hext4, hr4, htbl4, ht4⟩
        obtain ⟨r1, s4⟩ := x
        simp only at hI4 hext4 hr4 htbl4 ht4 ⊢
        have hp4 : p.val < s4.nodes.val.length := (hext4.repr (hext2.repr hp)).lt
        step with set_spec s4 .A p r1 hI4 hp4 (by unfold Room; omega) as ⟨s5, g1, g2, g3, g4, g5⟩
        refine rebuild_finish hnm hI hp hnone htS (hext2.trans hext4) (by simpa using hr4) ?_
          (by rw [htbl4, htb2]) (fun k v hk => by rw [htbl4, htb2]; exact hk) ?_ g1 g2 g3 g4 g5
        · rw [htbl4, htb2]; exact hM.extends (hext2.trans hext4)
        · obtain ⟨more, hm⟩ := hext2.trans hext4
          have := Finset.card_le_card (pending_mono (nm := nm) (nodes := s.nodes.val) (more := more)
            (A := tbl s .A) (A' := tbl s .A) (S := S.erase (Term.var v)) (fun k hk => hk))
          rw [htbl4, htb2, hm]
          omega
      have hatom : Repr nm s.nodes.val p.val (t.bind σ) →
          (do
            let (s3, r) ← (ok (s2, p) : Result (store.Store × store.TermId))
            let s4 ← store.Store.set s3 store.Tbl.A p r
            ok (r, s4)) ⦃ r s' => RebuildPost nm s s' σ t S r ⦄ := by
        intro hr
        have hp2 : p.val < s2.nodes.val.length := by rw [hn2]; exact hp.lt
        step with set_spec s2 .A p p hK2.inv hp2 (by unfold Room; omega) as ⟨s5, g1, g2, g3, g4, g5⟩
        refine rebuild_finish hnm hI hp hnone htS hext2 (by rw [hn2]; exact hr) ?_
          (by rw [htb2]) (fun k v hk => by rw [htb2]; exact hk) ?_ g1 g2 g3 g4 g5
        · rw [htb2, hn2]; exact hM
        · rw [htb2, hn2]; omega
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
        exact hatom hp
      | Nil =>
        have := hp.of_nil hnd
        subst this
        exact hatom hp
      | App a b =>
        obtain ⟨ta, tb, e, ha, hb⟩ := hp.of_app hnd
        subst e
        simp only [Term.size] at hsz
        simp only
        have hSa := subs_left_erase hS
        have hSb := subs_right_erase hS
        step with ih s2 f a ta σ (S.erase (Term.app ta tb)) (by omega) hK2.inv
          (by rw [hn2]; exact ha) (by rw [hn2]; exact hf) (by rw [hn2, htb2]; exact hM) hSa
          (by rw [hn2, htb2]; unfold Room; omega) as ⟨x, hA⟩
        obtain ⟨ra, s4⟩ := x
        simp only at hA ⊢
        have hcA := hA.cost
        rw [hn2, htb2] at hcA
        have hext4 := hext2.trans hA.ext
        step with ih s4 f b tb σ (S.erase (Term.app ta tb)) (by omega) hA.inv
          (hext4.repr hb) (hf.extends hext4) hA.memo hSb
          (by unfold Room; omega) as ⟨x, hBp⟩
        obtain ⟨rb, s5⟩ := x
        simp only at hBp ⊢
        have hcB := hBp.cost
        have hext5 := hext4.trans hBp.ext
        step with alloc_spec s5 (.App ra rb) hBp.inv ⟨(hBp.ext.repr hA.repr).lt, hBp.repr.lt⟩
          (by unfold Room; omega) as ⟨x, hI6, ht6, htbl6, more, hmore, hr6⟩
        obtain ⟨r1, s6⟩ := x
        simp only at hI6 ht6 htbl6 hmore hr6 ⊢
        have hext6 : Extends s5 s6 := ⟨more, hmore⟩
        have hp6 : p.val < s6.nodes.val.length := ((hext5.trans hext6).repr hp).lt
        step with set_spec s6 .A p r1 hI6 hp6 (by unfold Room; omega) as ⟨s7, g1, g2, g3, g4, g5⟩
        refine rebuild_finish hnm hI hp hnone htS (hext5.trans hext6) ?_ ?_ ?_ ?_ ?_ g1 g2 g3 g4 g5
        · simp only [Term.bind_app]
          exact .app hr6 (hext6.repr (hBp.ext.repr hA.repr)) (hext6.repr hBp.repr)
        · rw [htbl6]; exact hBp.memo.extends hext6
        · rw [htbl6, hBp.tblB, hA.tblB, htb2]
        · intro k v hk
          rw [htbl6]
          exact hBp.keep k v (hA.keep k v (by rw [htb2]; exact hk))
        · obtain ⟨more, hm⟩ := hext6
          have := Finset.card_le_card (pending_mono (nm := nm) (nodes := s5.nodes.val) (more := more)
            (A := tbl s5 .A) (A' := tbl s5 .A) (S := S.erase (Term.app ta tb)) (fun k hk => hk))
          rw [htbl6, hm]
          omega

/-- `rebuild` computes `Term.bind`. It spends one tick, and five more for each
term of `S` that had no table entry and gets one. -/
theorem rebuild_spec (hnm : Function.Injective nm) (s : store.Store) (f : term.Leaf)
    (p : store.TermId) {t : Pat} {σ : Nat → Pat} (S : Finset Pat) (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val t) (hf : LeafOK nm s.nodes.val f σ)
    (hM : MemoOK nm s.nodes.val (tbl s .A) σ) (hS : t.subs ⊆ S)
    (hroom : Room s (1 + 5 * (pending nm s.nodes.val (tbl s .A) S).card)) :
    term.rebuild s f p ⦃ r s' => RebuildPost nm s s' σ t S r ⦄ :=
  rebuild_spec_aux hnm t.size s f p t σ S (Nat.le_refl _) hI hp hf hM hS hroom

end RwLogVerified
