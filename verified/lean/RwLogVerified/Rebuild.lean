/-
# Rebuilding a term: the Rust `rebuild` computes `Term.bind`

`rebuild s f p` copies the term at `p` with its variables replaced as `f`
says. Table `A` remembers what each node visited became, so a node is
rebuilt once however often it occurs.

`rebuild_spec`: the result stands for `t.bind σ`, where `σ` is the
substitution `f` stands for (`LeafOK`), and the cost is five ticks plus
fourteen for each term that gets a table entry. `pending S` is the set of
members of `S` without an entry; the statement holds for every set `S` that
contains the subterms of `t`, so a second call that shares the table pays
only for what the first did not visit.

The function is a loop over the stack of the store (`Walk.lean`). An
application is visited (six ticks), waits as a `Build` frame under a `Visit`
frame for each part (two ticks each, when the part is already done), and is
finished (six ticks): fourteen in all. `RSt` is what the loop keeps true of
the stack and the table, and `Unb` names the terms still to be paid for.
-/
import RwLogVerified.Walk

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → Sym}

theorem Extends.refl (s : store.Store) : Extends s s := ⟨[], by simp, by simp⟩

theorem Extends.trans {a b c : store.Store} (h₁ : Extends a b) (h₂ : Extends b c) : Extends a c := by
  obtain ⟨m₁, e₁, t₁⟩ := h₁
  obtain ⟨m₂, e₂, t₂⟩ := h₂
  exact ⟨m₁ ++ m₂, by rw [e₂, e₁, List.append_assoc], by simp only [List.length_append]; omega⟩

/-- A store with the same nodes, later. -/
theorem Extends.of_eq {a b : store.Store} (h : b.nodes.val = a.nodes.val)
    (ht : a.ticks.val ≤ b.ticks.val) : Extends a b :=
  ⟨[], by simp [h], by simpa using ht⟩

/-- The nodes added are at most the ticks spent. -/
theorem Extends.nodes_le {s s' : store.Store} (h : Extends s s') :
    s'.nodes.val.length + s.ticks.val ≤ s.nodes.val.length + s'.ticks.val := by
  obtain ⟨m, e, t⟩ := h
  rw [e, List.length_append]; omega

theorem Extends.repr {s s' : store.Store} (h : Extends s s') {i : Nat} {t : Pat}
    (hr : Repr nm s.nodes.val i t) : Repr nm s'.nodes.val i t := by
  obtain ⟨m, e, -⟩ := h
  rw [e]; exact hr.append m

theorem Extends.varAt {s s' : store.Store} (h : Extends s s') {i n : Nat}
    (hr : VarAt s.nodes.val i n) : VarAt s'.nodes.val i n := by
  obtain ⟨m, e, -⟩ := h
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

theorem pending_card_le (nodes : List store.Node) (A : Nat → Option Nat) (S : Finset Pat) :
    (pending nm nodes A S).card ≤ S.card := by
  apply Finset.card_le_card
  intro u hu
  exact (mem_pending.1 hu).1

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
  obtain ⟨m, e, -⟩ := he
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

theorem leaf_w (s : store.Store) (f : term.Leaf) (p : store.TermId) {σ : Nat → Pat} {v : Nat}
    (hI : Wf s) (hv : VarAt s.nodes.val p.val v) (hf : LeafOK nm s.nodes.val f σ)
    (hroom : Room s 1) :
    term.leaf s f p ⦃ r s' =>
      Wf s' ∧ Extends s s' ∧ Repr nm s'.nodes.val r.val (σ v) ∧ tbl s' = tbl s ∧
        s'.ticks.val ≤ s.ticks.val + 1 ∧ s.ticks.val ≤ s'.ticks.val ∧ stk s' = stk s ⦄ := by
  unfold term.leaf
  cases f with
  | Left =>
    simp only [LeafOK] at hf
    subst hf
    step with alloc_w s (.VL p) hI hv.node hroom as ⟨r, s', hI', ht, htbl, hext, hr, hstk⟩
    refine ⟨hI', hext, ?_, htbl, by omega, by omega, hstk⟩
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
    step with alloc_w s (.VR p) hI hv.node hroom as ⟨r, s', hI', ht, htbl, hext, hr, hstk⟩
    refine ⟨hI', hext, ?_, htbl, by omega, by omega, hstk⟩
    simp only [norm] at hr
    exact .var (.right hr (Extends.varAt hext hv))
  | Sub x u =>
    obtain ⟨xv, tu, hx, hu, e⟩ := hf
    subst e
    step with same_w s p x hI hroom as ⟨b, s1, hb, hK⟩
    have hext : Extends s s1 := Extends.of_eq hK.nodes (by have := hK.ticks; omega)
    split
    · rename_i hbt
      have hpx : p.val = x.val := by simpa [hb] using hbt
      have : v = xv := by rw [hpx] at hv; exact hv.unique hx
      subst this
      step*
      refine ⟨hK.wf, hext, ?_, hK.tbl, by have := hK.ticks; omega, by have := hK.ticks; omega,
        hK.stk⟩
      simp only [Term.single, ↓reduceIte]
      exact hext.repr hu
    · rename_i hbf
      have hpx : p.val ≠ x.val := by simpa [hb] using hbf
      have hne : v ≠ xv := by
        rintro rfl
        exact hpx (hv.inj hI.nodesOK hx)
      step*
      refine ⟨hK.wf, hext, ?_, hK.tbl, by have := hK.ticks; omega, by have := hK.ticks; omega,
        hK.stk⟩
      simp only [Term.single, hne, ↓reduceIte]
      exact .var (hext.varAt hv)

/-! ## The terms still to be paid for -/

theorem mem_pending_of_none (hnm : Function.Injective nm) {nodes : List store.Node}
    (hN : NodesOK nodes) {A : Nat → Option Nat} {S : Finset Pat} {t : Pat} {p : Nat}
    (hp : Repr nm nodes p t) (hA : A p = none) (ht : t ∈ S) : t ∈ pending nm nodes A S := by
  rw [mem_pending]
  refine ⟨ht, ?_⟩
  rintro ⟨k, hk, hAk⟩
  rw [Repr.inj hnm hN hk hp] at hAk
  exact hAk hA

/-- `U` holds every term of `S` that has no entry and whose node has no
`Build` frame on the stack. -/
def Unb (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat) (S : Finset Pat)
    (st : List store.Frame) (U : Finset Pat) : Prop :=
  ∀ t ∈ pending nm nodes A S, (∀ f ∈ st, IsVisit f ∨ ¬ Repr nm nodes (fkey f) t) → t ∈ U

theorem Unb.start (nodes : List store.Node) (A : Nat → Option Nat) (S : Finset Pat)
    (st : List store.Frame) : Unb nm nodes A S st (pending nm nodes A S) :=
  fun _ ht _ => ht

/-- With an empty stack, `U` holds every term without an entry. -/
theorem Unb.card_le {nodes : List store.Node} {A : Nat → Option Nat} {S U : Finset Pat}
    (h : Unb nm nodes A S [] U) : (pending nm nodes A S).card ≤ U.card :=
  Finset.card_le_card fun t ht => h t ht (by simp)

/-- A `Visit` frame is taken off. -/
theorem Unb.pop_visit {nodes : List store.Node} {A : Nat → Option Nat} {S U : Finset Pat}
    {f : store.Frame} {st : List store.Frame} (h : Unb nm nodes A S (f :: st) U)
    (hf : IsVisit f) : Unb nm nodes A S st U := by
  intro t ht hc
  refine h t ht fun f' hf' => ?_
  rcases List.mem_cons.1 hf' with rfl | hf'
  · exact Or.inl hf
  · exact hc f' hf'

/-- The node at the top is expanded: its term leaves `U`. -/
theorem Unb.expand {nodes : List store.Node} {A : Nat → Option Nat} {S U : Finset Pat}
    {q u u' : store.TermId} {f₁ f₂ : store.Frame} {st : List store.Frame} {t : Pat}
    (h : Unb nm nodes A S (.Visit q u :: st) U) (hq : Repr nm nodes q.val t) :
    Unb nm nodes A S (f₁ :: f₂ :: .Build q u' :: st) (U.erase t) := by
  intro t' ht' hc
  refine Finset.mem_erase.2 ⟨?_, h t' ht' fun f' hf' => ?_⟩
  · rintro rfl
    rcases hc (.Build q u') (by simp) with h | h
    · exact h
    · exact h hq
  · rcases List.mem_cons.1 hf' with rfl | hf'
    · exact Or.inl trivial
    · exact hc f' (by simp [hf'])

/-- The node of the top frame gets its entry, maybe after nodes were added:
its term leaves `U`. -/
theorem Unb.set {nodes : List store.Node} {A : Nat → Option Nat} {S U : Finset Pat}
    {f : store.Frame} {st : List store.Frame} {t : Pat} (h : Unb nm nodes A S (f :: st) U)
    (hq : Repr nm nodes (fkey f) t) (more : List store.Node) (r : Nat) :
    Unb nm (nodes ++ more) (Function.update A (fkey f) (some r)) S st (U.erase t) := by
  intro t' ht' hc
  have hsub := pending_after_set (nm := nm) (nodes := nodes) (more := more) (A := A)
    (A' := Function.update A (fkey f) (some r)) (S := S) (t := t) (p := fkey f) (hq.append more)
    (by simp)
    (by
      intro k hk
      by_cases e : k = fkey f
      · subst e; simp
      · rw [Function.update_of_ne e]; exact hk)
  have ht1 := hsub ht'
  rw [mem_pending, Finset.mem_erase] at ht1
  refine Finset.mem_erase.2 ⟨ht1.1.1, h t' (mem_pending.2 ⟨ht1.1.2, ht1.2⟩) fun f' hf' => ?_⟩
  rcases List.mem_cons.1 hf' with rfl | hf'
  · exact Or.inr fun hr => ht1.1.1 (hr.unique hq)
  · rcases hc f' hf' with h | h
    · exact Or.inl h
    · exact Or.inr fun hr => h (hr.append more)

/-- The term of a `Visit` frame at the top, when it has no entry, is in `U`. -/
theorem Unb.mem_top (hnm : Function.Injective nm) {nodes : List store.Node} (hN : NodesOK nodes)
    {A : Nat → Option Nat} {S U : Finset Pat} {q u : store.TermId} {st : List store.Frame}
    {t : Pat} {Kid : Nat × Nat → Nat × Nat → Prop} {done : Nat × Nat → Prop} {ent : Nat → Prop}
    (h : Unb nm nodes A S (.Visit q u :: st) U) (hw : Waits Kid done ent (.Visit q u :: st))
    (hq : Repr nm nodes q.val t) (hA : A q.val = none) (ht : t ∈ S) : t ∈ U := by
  refine h t (mem_pending_of_none hnm hN hq hA ht) fun f hf => ?_
  cases f with
  | Visit a b => exact Or.inl trivial
  | Build a b =>
    have hf' : store.Frame.Build a b ∈ st := by simpa using hf
    refine Or.inr fun hr => ?_
    have e : a.val = q.val := Repr.inj hnm hN hr hq
    have : a = q := by scalar_tac
    subst this
    exact hw.no_build b hf'

theorem card_erase_add_one {U : Finset Pat} {t : Pat} (h : t ∈ U) :
    (U.erase t).card + 1 = U.card := by
  rw [Finset.card_erase_of_mem h]
  have := Finset.card_pos.2 ⟨t, h⟩
  omega

/-! ## What the loop keeps true -/

/-- The parts an application node waits for. -/
def RKid (n0 : List store.Node) (g c : Nat × Nat) : Prop :=
  ∃ a b : store.TermId, n0[g.1]? = some (.App a b) ∧ (c = (a.val, a.val) ∨ c = (b.val, b.val))

/-- The state of a walk that fills a table: `n0` and `A0` are the nodes and
the table at the start, `tp` the term walked, `p` its node, and `M` says what
a right table is. -/
structure RSt (nm : Option Nat → Sym) (n0 : List store.Node) (tp : Pat) (p : Nat)
    (A0 : Nat → Option Nat) (A : Nat → Option Nat) (st : List store.Frame) : Prop where
  keep : ∀ k v, A0 k = some v → A k = some v
  frames : ∀ f ∈ st, faux f = fkey f ∧ ∃ t ∈ tp.subs, Repr nm n0 (fkey f) t
  builds : ∀ q u, store.Frame.Build q u ∈ st → ∃ a b : store.TermId,
    n0[q.val]? = some (.App a b)
  waits : Waits (RKid n0) (fun c => A c.1 ≠ none) (fun k => A k ≠ none) st
  root : A p ≠ none ∨ ∃ f ∈ st, fkey f = p

variable {n0 : List store.Node} {tp : Pat} {p : Nat} {A0 A : Nat → Option Nat}

/-- The node of the top frame has an entry already. -/
theorem RSt.hit {f : store.Frame} {st : List store.Frame}
    (h : RSt nm n0 tp p A0 A (f :: st)) (hA : A (fkey f) ≠ none) :
    RSt nm n0 tp p A0 A st := by
  refine ⟨h.keep, fun f' hf' => h.frames f' (List.mem_cons_of_mem _ hf'),
    fun q u hq => h.builds q u (List.mem_cons_of_mem _ hq),
    h.waits.pop (fun _ hg => hg) hA (fun _ hk => Or.inl hk), ?_⟩
  rcases h.root with h | ⟨f', hf', e⟩
  · exact Or.inl h
  · rcases List.mem_cons.1 hf' with rfl | hf'
    · exact Or.inl (e ▸ hA)
    · exact Or.inr ⟨f', hf', e⟩

/-- The node of the top frame gets its entry. -/
theorem RSt.set {f : store.Frame} {st : List store.Frame}
    (h : RSt nm n0 tp p A0 A (f :: st)) (hnone : A (fkey f) = none) (r : Nat) :
    RSt nm n0 tp p A0 (Function.update A (fkey f) (some r)) st := by
  refine ⟨?_, fun f' hf' => h.frames f' (List.mem_cons_of_mem _ hf'),
    fun q u hq => h.builds q u (List.mem_cons_of_mem _ hq), ?_, ?_⟩
  · intro k v hk
    by_cases e : k = fkey f
    · subst e
      rw [h.keep _ _ hk] at hnone
      cases hnone
    · rw [Function.update_of_ne e]; exact h.keep k v hk
  · refine h.waits.pop (fun g hg => ?_) (by simp [goal]) (fun k hk => ?_)
    · by_cases e : g.1 = fkey f
      · rw [e]; simp
      · rw [Function.update_of_ne e]; exact hg
    · by_cases e : k = fkey f
      · exact Or.inr e
      · rw [Function.update_of_ne e] at hk; exact Or.inl hk
  · rcases h.root with h | ⟨f', hf', e⟩
    · left
      by_cases e : p = fkey f
      · rw [e]; simp
      · rw [Function.update_of_ne e]; exact h
    · rcases List.mem_cons.1 hf' with rfl | hf'
      · left; rw [e]; simp
      · exact Or.inr ⟨f', hf', e⟩

/-- The application at the top is replaced by its `Build` frame under its
parts. -/
theorem RSt.expand (hN : NodesOK n0) {q a b : store.TermId} {st : List store.Frame}
    (h : RSt nm n0 tp p A0 A (.Visit q q :: st)) (hnone : A q.val = none)
    (hn : n0[q.val]? = some (.App a b)) :
    RSt nm n0 tp p A0 A (.Visit a a :: .Visit b b :: .Build q q :: st) := by
  obtain ⟨-, t, ht, hq⟩ := h.frames (.Visit q q) List.mem_cons_self
  obtain ⟨ta, tb, e, ha, hb⟩ := hq.of_app hn
  subst e
  have hfit := hN.fits _ _ hn
  simp only [Fits] at hfit
  have hsa : ta ∈ tp.subs := Term.subs_trans ht (by simp [Term.subs, Term.self_mem_subs])
  have hsb : tb ∈ tp.subs := Term.subs_trans ht (by simp [Term.subs, Term.self_mem_subs])
  refine ⟨h.keep, ?_, ?_, ?_, ?_⟩
  · intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | rfl | rfl | hf
    · exact ⟨rfl, ta, hsa, ha⟩
    · exact ⟨rfl, tb, hsb, hb⟩
    · exact ⟨rfl, _, ht, hq⟩
    · exact h.frames f (List.mem_cons_of_mem _ hf)
  · intro q' u' hq'
    simp only [List.mem_cons, reduceCtorEq, store.Frame.Build.injEq, false_or] at hq'
    rcases hq' with ⟨rfl, rfl⟩ | hq'
    · exact ⟨a, b, hn⟩
    · exact h.builds q' u' (List.mem_cons_of_mem _ hq')
  · refine h.waits.expand (by simpa using hnone) ?_ trivial trivial hfit.1 hfit.2
    rintro c ⟨a', b', hn', hc⟩
    simp only at hn'
    rw [hn] at hn'
    cases hn'
    exact hc
  · rcases h.root with h | ⟨f', hf', e⟩
    · exact Or.inl h
    · rcases List.mem_cons.1 hf' with rfl | hf'
      · exact Or.inr ⟨.Build q q, by simp, e⟩
      · exact Or.inr ⟨f', by simp [hf'], e⟩

/-- A `Build` frame at the top: its node is an application with no entry,
and its parts have theirs. -/
theorem RSt.top {q u : store.TermId} {st : List store.Frame}
    (h : RSt nm n0 tp p A0 A (.Build q u :: st)) :
    ∃ a b : store.TermId, n0[q.val]? = some (.App a b) ∧
      A q.val = none ∧ A a.val ≠ none ∧ A b.val ≠ none := by
  obtain ⟨a, b, hn⟩ := h.builds q u List.mem_cons_self
  obtain ⟨h1, h2⟩ := h.waits.top
  exact ⟨a, b, hn, by simpa using h1, h2 (a.val, a.val) ⟨a, b, hn, Or.inl rfl⟩,
    h2 (b.val, b.val) ⟨a, b, hn, Or.inr rfl⟩⟩

/-- With an empty stack, the node walked has its entry. -/
theorem RSt.done (h : RSt nm n0 tp p A0 A []) : A p ≠ none := by
  rcases h.root with h | ⟨f, hf, -⟩
  · exact h
  · simp at hf

theorem MemoOK.set {nodes : List store.Node} {σ : Nat → Pat} {k : Nat} {t : Pat}
    (h : MemoOK nm nodes A σ) (hk : Repr nm nodes k t) (more : List store.Node) {r : Nat}
    (hr : Repr nm (nodes ++ more) r (t.bind σ)) :
    MemoOK nm (nodes ++ more) (Function.update A k (some r)) σ := by
  intro k' v hk'
  by_cases e : k' = k
  · subst e
    simp only [Function.update_self, Option.some.injEq] at hk'
    subst hk'
    exact ⟨t, hk.append more, hr⟩
  · rw [Function.update_of_ne e] at hk'
    obtain ⟨t', h1, h2⟩ := h k' v hk'
    exact ⟨t', h1.append more, h2.append more⟩

/-! ## Rebuilding -/

/-- What `rebuild` leaves: the result stands for `t.bind σ`, the table is
still right and only gained entries, table `B` is untouched, and the ticks
spent are five plus fourteen for each term of `S` that got an entry. -/
structure RebuildPost (nm : Option Nat → Sym) (s s' : store.Store) (σ : Nat → Pat) (t : Pat)
    (S : Finset Pat) (r : store.TermId) : Prop where
  inv : Inv s'
  ext : Extends s s'
  repr : Repr nm s'.nodes.val r.val (t.bind σ)
  memo : MemoOK nm s'.nodes.val (tbl s' .A) σ
  tblB : tbl s' .B = tbl s .B
  keep : ∀ k v, tbl s .A k = some v → tbl s' .A k = some v
  cost : s'.ticks.val + 14 * (pending nm s'.nodes.val (tbl s' .A) S).card ≤
    s.ticks.val + 5 + 14 * (pending nm s.nodes.val (tbl s .A) S).card
  mono : s.ticks.val ≤ s'.ticks.val

/-- The invariant of the loop. `s0` is the store at the start and `B` the
tick count the loop stays under. -/
structure RInv (nm : Option Nat → Sym) (s0 : store.Store) (σ : Nat → Pat) (tp : Pat)
    (p : Nat) (S : Finset Pat) (B : Nat) (s : store.Store) : Prop where
  wf : Wf s
  ext : Extends s0 s
  memo : MemoOK nm s.nodes.val (tbl s .A) σ
  st : RSt nm s0.nodes.val tp p (tbl s0 .A) (tbl s .A) (stk s)
  tblB : tbl s .B = tbl s0 .B
  cost : ∃ U, Unb nm s.nodes.val (tbl s .A) S (stk s) U ∧
    s.ticks.val + 1 + 2 * nV (stk s) + 6 * nB (stk s) + 14 * U.card ≤ B

/-- What the loop leaves. -/
structure RDone (nm : Option Nat → Sym) (s0 : store.Store) (σ : Nat → Pat) (tp : Pat)
    (p : Nat) (S : Finset Pat) (B : Nat) (s : store.Store) : Prop where
  wf : Wf s
  empty : stk s = []
  ext : Extends s0 s
  memo : MemoOK nm s.nodes.val (tbl s .A) σ
  st : RSt nm s0.nodes.val tp p (tbl s0 .A) (tbl s .A) []
  tblB : tbl s .B = tbl s0 .B
  cost : s.ticks.val + 14 * (pending nm s.nodes.val (tbl s .A) S).card ≤ B

def RBodyPost (nm : Option Nat → Sym) (s0 : store.Store) (σ : Nat → Pat) (tp : Pat)
    (p : Nat) (S : Finset Pat) (B : Nat) (t0 : Nat) :
    ControlFlow store.Store store.Store → Prop
  | .done s' => RDone nm s0 σ tp p S B s' ∧ t0 ≤ s'.ticks.val
  | .cont s' => RInv nm s0 σ tp p S B s' ∧ t0 < s'.ticks.val

theorem rebuild_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (f : term.Leaf)
    (σ : Nat → Pat) (tp : Pat) (p : Nat) (S : Finset Pat) (B : Nat)
    (hB : 40 * B + 100 ≤ Usize.max) (hN0 : NodesOK s0.nodes.val)
    (hf : LeafOK nm s0.nodes.val f σ) (hS : tp.subs ⊆ S) (s : store.Store)
    (h : RInv nm s0 σ tp p S B s) :
    term.rebuild_loop.body f s ⦃ r => RBodyPost nm s0 σ tp p S B s.ticks.val r ⦄ := by
  unfold term.rebuild_loop.body
  obtain ⟨hW, hE, hM, hSt, hTB, U, hU, hc⟩ := h
  step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
  cases hst : stk s with
  | nil =>
    rw [hst] at eo est hSt hU hc
    simp only [List.head?_nil, List.tail_nil] at eo est
    subst eo
    simp only [WP.spec_ok]
    refine ⟨⟨hW1, est, hE.trans (Extends.of_eq e1 (by omega)), by rw [e1, e2]; exact hM,
      by rw [e2]; exact hSt, by rw [e2, hTB], ?_⟩, by omega⟩
    have := hU.card_le
    rw [e1, e2, e3]
    simp only [nV_nil, nB_nil] at hc
    omega
  | cons fr st =>
    rw [hst] at eo est hSt hU hc
    simp only [List.head?_cons, List.tail_cons] at eo est
    subst eo
    obtain ⟨hfa, tq, htq, hq0⟩ := hSt.frames fr List.mem_cons_self
    have hq : Repr nm s.nodes.val (fkey fr) tq := hE.repr hq0
    have hN : NodesOK s.nodes.val := hW.nodesOK
    have hE' := hE
    obtain ⟨more, hmore, -⟩ := hE'
    cases fr with
    | Visit q u =>
      have : q = u := by simp only [faux, fkey] at hfa; scalar_tac
      subst this
      simp only [fkey] at hq hq0
      simp only [nV_visit, nB_visit] at hc
      simp only
      step with get_w s1 .A q hW1 (by rw [e1]; exact hq.lt) (by unfold Room; omega)
        as ⟨o1, s2, ho1, hK2⟩
      rw [e2] at ho1
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
      have hstk2 : stk s2 = st := by rw [hK2.stk, est]
      cases o1 with
      | some r =>
        simp only [Option.map_some] at ho1
        simp only [WP.spec_ok]
        have hA : tbl s .A q.val ≠ none := by rw [← ho1]; simp
        refine ⟨⟨hK2.wf, hE.trans (Extends.of_eq hn2 (by omega)), by rw [hn2, htb2]; exact hM, ?_,
          by rw [htb2, hTB], U, ?_, ?_⟩, by omega⟩
        · rw [htb2, hstk2]
          exact hSt.hit hA
        · rw [hn2, htb2, hstk2]
          exact hU.pop_visit trivial
        · rw [hstk2]; omega
      | none =>
        simp only [Option.map_none] at ho1
        have hnone : tbl s .A q.val = none := ho1.symm
        have htU : tq ∈ U := hU.mem_top hnm hN hSt.waits hq hnone (hS htq)
        have hU1 := card_erase_add_one htU
        simp only
        step with read_w s2 q hK2.wf (by rw [hn2]; exact hq.lt) (by unfold Room; omega)
          as ⟨nd, s3, hnd, hK3⟩
        rw [hn2] at hnd
        have ht3 := hK3.ticks
        have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
        have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
        have hstk3 : stk s3 = st := by rw [hK3.stk, hstk2]
        have hnd0 : s0.nodes.val[q.val]? = some nd := by
          rw [hmore, List.getElem?_append_left hq0.lt] at hnd
          exact hnd
        -- a variable: the leaf function gives its entry
        have hleaf : ∀ v, tq = Term.var v → VarAt s.nodes.val q.val v →
            (do
              let (r, s4) ← term.leaf s3 f q
              let s5 ← store.Store.set s4 store.Tbl.A q r
              ok (ControlFlow.cont s5 : ControlFlow store.Store store.Store)) ⦃ r =>
              RBodyPost nm s0 σ tp p S B s.ticks.val r ⦄ := by
          intro v hv hva
          subst hv
          step with leaf_w (nm := nm) s3 f q (σ := σ) (v := v) hK3.wf (by rw [hn3]; exact hva)
            (by rw [hn3, hmore]; exact hf.append more) (by unfold Room; omega)
            as ⟨r1, s4, hW4, hext4, hr4, htbl4, ht4, hm4, hstk4⟩
          have hext4' := hext4
          obtain ⟨more4, hmore4, -⟩ := hext4'
          rw [hn3] at hmore4
          step with set_w s4 .A q r1 hW4 (by rw [hmore4]; simp; have := hq.lt; omega)
            (by unfold Room; omega) as ⟨s5, g1, g2, g3, g4, g5, g6⟩
          rw [htbl4, htb3] at g4
          refine ⟨⟨g3, hE.trans ((Extends.of_eq hn3 (by omega)).trans (hext4.trans (Extends.of_eq g1 (by omega)))), ?_, ?_, ?_,
            U.erase (Term.var v), ?_, ?_⟩, by omega⟩
          · rw [g1, g4, hmore4]
            exact hM.set hq more4 (by rw [← hmore4]; exact hr4)
          · rw [g4, g6, hstk4, hstk3]
            exact hSt.set hnone r1.val
          · rw [g5 .B (by simp), htbl4, htb3, hTB]
          · rw [g1, g4, g6, hstk4, hstk3, hmore4]
            exact hU.set hq more4 r1.val
          · rw [g6, hstk4, hstk3]; omega
        -- a symbol or the end of a list: it is its own entry
        have hatom : Repr nm s.nodes.val q.val (tq.bind σ) →
            (do
              let s4 ← store.Store.set s3 store.Tbl.A q q
              ok (ControlFlow.cont s4 : ControlFlow store.Store store.Store)) ⦃ r =>
              RBodyPost nm s0 σ tp p S B s.ticks.val r ⦄ := by
          intro hr
          step with set_w s3 .A q q hK3.wf (by rw [hn3]; exact hq.lt) (by unfold Room; omega)
            as ⟨s5, g1, g2, g3, g4, g5, g6⟩
          rw [htb3] at g4
          refine ⟨⟨g3, hE.trans ((Extends.of_eq hn3 (by omega)).trans (Extends.of_eq g1 (by omega))), ?_, ?_, ?_, U.erase tq, ?_, ?_⟩, by omega⟩
          · rw [g1, g4, hn3]
            have := hM.set hq [] (r := q.val) (by simpa using hr)
            simpa [fkey] using this
          · rw [g4, g6, hstk3]
            exact hSt.set hnone q.val
          · rw [g5 .B (by simp), htb3, hTB]
          · rw [g1, g4, g6, hstk3, hn3]
            have := hU.set (f := .Visit q q) hq [] q.val
            simpa [fkey] using this
          · rw [g6, hstk3]; omega
        cases nd with
        | V0 =>
          obtain ⟨v, hv, hva⟩ := hq.of_var hnd trivial
          exact hleaf v hv hva
        | VL a =>
          obtain ⟨v, hv, hva⟩ := hq.of_var hnd trivial
          exact hleaf v hv hva
        | VR a =>
          obtain ⟨v, hv, hva⟩ := hq.of_var hnd trivial
          exact hleaf v hv hva
        | Sym g =>
          have := hq.of_sym hnd
          subst this
          exact hatom hq
        | Nil =>
          have := hq.of_nil hnd
          subst this
          exact hatom hq
        | App a b =>
          simp only
          step with push_w s3 (.Build q q) hK3.wf (by unfold Room; omega)
            as ⟨s4, a1, a2, a3, hW4, a5⟩
          step with push_w s4 (.Visit b b) hW4 (by unfold Room; omega)
            as ⟨s5, b1, b2, b3, hW5, b5⟩
          step with push_w s5 (.Visit a a) hW5 (by unfold Room; omega)
            as ⟨s6, c1, c2, c3, hW6, c5⟩
          have hn6 : s6.nodes.val = s.nodes.val := by rw [c1, b1, a1, hn3]
          have htb6 : tbl s6 = tbl s := by rw [c2, b2, a2, htb3]
          have hstk6 : stk s6 = .Visit a a :: .Visit b b :: .Build q q :: st := by
            rw [c5, b5, a5, hstk3]
          refine ⟨⟨hW6, hE.trans (Extends.of_eq hn6 (by omega)), by rw [hn6, htb6]; exact hM, ?_,
            by rw [htb6, hTB], U.erase tq, ?_, ?_⟩, by omega⟩
          · rw [htb6, hstk6]
            exact hSt.expand hN0 hnone hnd0
          · rw [hn6, htb6, hstk6]
            exact hU.expand hq
          · rw [hstk6]
            simp only [nV_visit, nV_build, nB_visit, nB_build]
            omega
    | Build q u =>
      simp only [fkey] at hq hq0
      simp only [nV_build, nB_build] at hc
      obtain ⟨a, b, hn0, hnone, hAa, hAb⟩ := hSt.top
      obtain ⟨ta, tb, e, ha0, hb0⟩ := hq0.of_app hn0
      subst e
      have ha : Repr nm s.nodes.val a.val ta := by rw [hmore]; exact ha0.append more
      have hb : Repr nm s.nodes.val b.val tb := by rw [hmore]; exact hb0.append more
      have hnd' : s.nodes.val[q.val]? = some (.App a b) := by
        rw [hmore, List.getElem?_append_left hq0.lt]; exact hn0
      simp only
      step with read_w s1 q hW1 (by rw [e1]; exact hq.lt) (by unfold Room; omega)
        as ⟨nd, s2, hnd, hK2⟩
      rw [e1, hnd'] at hnd
      cases hnd
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
      simp only
      step with get_w s2 .A a hK2.wf (by rw [hn2]; exact ha.lt) (by unfold Room; omega)
        as ⟨o1, s3, ho1, hK3⟩
      rw [htb2] at ho1
      have ht3 := hK3.ticks
      have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
      have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
      cases o1 with
      | none => simp only [Option.map_none] at ho1; exact absurd ho1.symm hAa
      | some ra =>
        simp only [Option.map_some] at ho1
        simp only
        step with get_w s3 .A b hK3.wf (by rw [hn3]; exact hb.lt) (by unfold Room; omega)
          as ⟨o2, s4, ho2, hK4⟩
        rw [htb3] at ho2
        have ht4 := hK4.ticks
        have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
        have htb4 : tbl s4 = tbl s := by rw [hK4.tbl, htb3]
        have hstk4 : stk s4 = st := by rw [hK4.stk, hK3.stk, hK2.stk, est]
        cases o2 with
        | none => simp only [Option.map_none] at ho2; exact absurd ho2.symm hAb
        | some rb =>
          simp only [Option.map_some] at ho2
          simp only
          obtain ⟨ta', h1, hra⟩ := hM _ _ ho1.symm
          have := ha.unique h1
          subst this
          obtain ⟨tb', h2, hrb⟩ := hM _ _ ho2.symm
          have := hb.unique h2
          subst this
          step with alloc_w s4 (.App ra rb) hK4.wf (by rw [hn4]; exact ⟨hra.lt, hrb.lt⟩)
            (by unfold Room; omega) as ⟨r, s5, hW5, ht5, htbl5, hext5, hr5, hstk5⟩
          have hext5' := hext5
          obtain ⟨more5, hmore5, -⟩ := hext5'
          rw [hn4] at hmore5
          step with set_w s5 .A q r hW5 (by rw [hmore5]; simp; have := hq.lt; omega)
            (by unfold Room; omega) as ⟨s6, g1, g2, g3, g4, g5, g6⟩
          rw [htbl5, htb4] at g4
          have hr : Repr nm (s.nodes.val ++ more5) r.val ((Term.app ta tb).bind σ) := by
            simp only [Term.bind_app]
            rw [← hmore5]
            exact .app hr5 (by rw [hmore5]; exact hra.append more5)
              (by rw [hmore5]; exact hrb.append more5)
          refine ⟨⟨g3, hE.trans ((Extends.of_eq hn4 (by omega)).trans (hext5.trans (Extends.of_eq g1 (by omega)))), ?_, ?_, ?_,
            U.erase (Term.app ta tb), ?_, ?_⟩, by omega⟩
          · rw [g1, g4, hmore5]
            exact hM.set hq more5 hr
          · rw [g4, g6, hstk5, hstk4]
            exact hSt.set hnone r.val
          · rw [g5 .B (by simp), htbl5, htb4, hTB]
          · rw [g1, g4, g6, hstk5, hstk4, hmore5]
            exact hU.set (f := .Build q u) hq more5 r.val
          · rw [g6, hstk5, hstk4]
            have := Finset.card_erase_le (s := U) (a := Term.app ta tb)
            omega

/-- `rebuild` computes `Term.bind`. It spends five ticks, and fourteen more
for each term of `S` that had no table entry and gets one. -/
theorem rebuild_spec (hnm : Function.Injective nm) (s : store.Store) (f : term.Leaf)
    (p : store.TermId) {t : Pat} {σ : Nat → Pat} (S : Finset Pat) (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val t) (hf : LeafOK nm s.nodes.val f σ)
    (hM : MemoOK nm s.nodes.val (tbl s .A) σ) (hS : t.subs ⊆ S)
    (hroom : Room s (5 + 14 * (pending nm s.nodes.val (tbl s .A) S).card)) :
    term.rebuild s f p ⦃ r s' => RebuildPost nm s s' σ t S r ⦄ := by
  unfold term.rebuild term.rebuild_loop
  have hroom' := hroom
  unfold Room at hroom'
  step with push_w s (.Visit p p) hI.toWf (by unfold Room; omega) as ⟨s1, a1, a2, a3, hW1, a5⟩
  rw [hI.empty] at a5
  let B := s.ticks.val + 4 + 14 * (pending nm s.nodes.val (tbl s .A) S).card
  have hloop := loop.spec_decr_nat
    (fun x : store.Store => B + 1 - x.ticks.val)
    (fun x => RInv nm s σ t p.val S B x ∧ s.ticks.val ≤ x.ticks.val)
    (fun x => RDone nm s σ t p.val S B x ∧ s.ticks.val ≤ x.ticks.val)
    (fun x : store.Store => term.rebuild_loop.body f x) s1
    (by
      rintro x ⟨hinv, hx⟩
      refine WP.spec_mono (rebuild_body_spec hnm s f σ t p.val S B (by omega) hI.nodesOK hf hS
        x hinv) ?_
      intro r hr
      cases r with
      | done y => exact ⟨hr.1, by have := hr.2; omega⟩
      | cont x' =>
        obtain ⟨h1, h2⟩ := hr
        obtain ⟨U, -, hc⟩ := h1.cost
        exact ⟨⟨h1, by omega⟩, by omega⟩)
    ⟨⟨hW1, Extends.of_eq a1 (by omega), by rw [a1, a2]; exact hM,
      ⟨by rw [a2]; exact fun _ _ h => h, by
        rw [a5]
        intro f' hf'
        simp only [List.mem_singleton] at hf'
        subst hf'
        exact ⟨rfl, t, Term.self_mem_subs t, hp⟩, by
        rw [a5]
        intro q u hq
        simp at hq, by rw [a5]; exact Waits.single p p, by
        rw [a5]; exact Or.inr ⟨_, List.mem_singleton_self _, rfl⟩⟩,
      by rw [a2], _, Unb.start _ _ _ _, by
        rw [a5, a1, a2]
        simp only [nV_visit, nV_nil, nB_visit, nB_nil]
        omega⟩, by omega⟩
  step with hloop as ⟨s2, hD, hmono⟩
  obtain ⟨hW2, hemp, hE2, hM2, hSt2, hTB2, hc2⟩ := hD
  have hAp := hSt2.done
  have hp2 : Repr nm s2.nodes.val p.val t := hE2.repr hp
  step with get_w s2 .A p hW2 hp2.lt (by unfold Room; omega) as ⟨o, s3, ho, hK3⟩
  cases o with
  | none => simp only [Option.map_none] at ho; exact absurd ho.symm hAp
  | some r =>
    simp only [Option.map_some] at ho
    simp only [WP.spec_ok]
    obtain ⟨t', h1, hr⟩ := hM2 _ _ ho.symm
    have := hp2.unique h1
    subst this
    have ht3 := hK3.ticks
    refine ⟨⟨hK3.wf, by rw [hK3.stk]; exact hemp⟩, hE2.trans (Extends.of_eq hK3.nodes (by have := hK3.ticks; omega)),
      by rw [hK3.nodes]; exact hr, by rw [hK3.nodes, hK3.tbl]; exact hM2,
      by rw [hK3.tbl, hTB2], fun k v hk => by rw [hK3.tbl]; exact hSt2.keep k v hk, ?_, ?_⟩
    · rw [hK3.nodes, hK3.tbl]; omega
    · omega

end RwLogVerified
