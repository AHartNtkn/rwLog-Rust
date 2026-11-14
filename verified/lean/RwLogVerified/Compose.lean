/-
# Composition and conjunction: the Rust `compose` and `meet`

`compose_spec` and `meet_spec`: on spans the store holds, the Rust functions
return the specification's `Span.compose` and `Span.meet`, and spend at most
`composeCost` and `meetCost` ticks. Those are polynomials in the number of
distinct subterms of the two spans (`solveCost`), so a term that occurs many
times is paid for once.
-/
import RwLogVerified.Solve
import RwLogVerified.SpanSpec

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term
open RwLog.Eqns (solveOn)

variable {nm : Option Nat → Sym}

/-! ## Spans and lists in the store -/

/-- The Rust span `x` is the span `sp`. -/
structure SpanAt (nm : Option Nat → Sym) (nodes : List store.Node) (x : span.Span) (sp : Span) :
    Prop where
  l : Repr nm nodes x.l.val sp.l
  r : Repr nm nodes x.r.val sp.r
  c : Repr nm nodes x.c.val (encList (nm none) sp.c)

theorem SpanAt.extends {s s' : store.Store} {x : span.Span} {sp : Span}
    (h : SpanAt nm s.nodes.val x sp) (he : Extends s s') : SpanAt nm s'.nodes.val x sp :=
  ⟨he.repr h.l, he.repr h.r, he.repr h.c⟩

/-- An optional Rust span is the optional span. -/
def OptSpanAt (nm : Option Nat → Sym) (nodes : List store.Node) :
    Option span.Span → Option Span → Prop
  | none, none => True
  | some x, some sp => SpanAt nm nodes x sp
  | _, _ => False

theorem encList_of_not_app {nodes : List store.Node} {xs : List Pat} {i : Nat} {n : store.Node}
    (h : Repr nm nodes i (encList (nm none) xs)) (hn : nodes[i]? = some n)
    (hna : ∀ a b, n ≠ .App a b) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons t ts =>
    obtain ⟨a, b, h1, _, _⟩ := Repr.app_inv (ta := t) (tb := encList (nm none) ts) h
    rw [hn] at h1
    cases h1
    exact absurd rfl (hna a b)

theorem encList_of_app {nodes : List store.Node} {xs : List Pat} {i : Nat} {e rest : store.TermId}
    (h : Repr nm nodes i (encList (nm none) xs)) (hn : nodes[i]? = some (.App e rest)) :
    ∃ t ts, xs = t :: ts ∧ Repr nm nodes e.val t ∧ Repr nm nodes rest.val (encList (nm none) ts) := by
  cases xs with
  | nil =>
    obtain ⟨ta, tb, e', -, -⟩ := h.of_app hn
    cases e'
  | cons t ts =>
    obtain ⟨ta, tb, e', ha, hb⟩ := h.of_app hn
    simp only [encList, Term.app.injEq] at e'
    obtain ⟨rfl, rfl⟩ := e'
    exact ⟨_, _, rfl, ha, hb⟩

/-! ## Renaming a span -/

/-- The terms of a span: its two sides and its list of constraints. -/
def spanSubs (z : Sym) (sp : Span) : Finset Pat := sp.l.subs ∪ sp.r.subs ∪ (encList z sp.c).subs

/-- The ticks renaming a span may spend. -/
def renameCost (z : Sym) (sp : Span) : Nat := 16 + 14 * (spanSubs z sp).card

theorem rename_spec (hnm : Function.Injective nm) (s : store.Store) (f : term.Leaf)
    (x : span.Span) {sp : Span} {σ : Nat → Pat} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sp)
    (hf : LeafOK nm s.nodes.val f σ) (hroom : Room s (renameCost (nm none) sp)) :
    span.rename s f x ⦃ a s' =>
      Inv s' ∧ Extends s s' ∧ SpanAt nm s'.nodes.val a (subSpan sp σ) ∧
        s'.ticks.val ≤ s.ticks.val + renameCost (nm none) sp ⦄ := by
  unfold span.rename
  unfold renameCost at hroom ⊢
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_spec s .A hI (by unfold Room; omega) as ⟨s1, c1, c2, c3, c4, c5⟩
  have hx1 : Extends s s1 := Extends.of_eq c1 (by omega)
  have hpc := pending_card_le (nm := nm) s1.nodes.val (tbl s1 .A) (spanSubs (nm none) sp)
  step with rebuild_spec hnm s1 f x.l (t := sp.l) (σ := σ) (spanSubs (nm none) sp) c3
    (hx1.repr hx.l) (hf.extends hx1) (by intro k v hk; rw [c4] at hk; cases hk)
    (fun w hw => by simp [spanSubs, hw]) (by unfold Room; omega) as ⟨l, s2, h2⟩
  have hc2 := h2.cost
  have hx2 := hx1.trans h2.ext
  step with rebuild_spec hnm s2 f x.r (t := sp.r) (σ := σ) (spanSubs (nm none) sp) h2.inv
    (hx2.repr hx.r) (hf.extends hx2) h2.memo
    (fun w hw => by simp [spanSubs, hw]) (by unfold Room; omega) as ⟨r, s3, h3⟩
  have hc3 := h3.cost
  have hx3 := hx2.trans h3.ext
  step with rebuild_spec hnm s3 f x.c (t := encList (nm none) sp.c) (σ := σ)
    (spanSubs (nm none) sp) h3.inv (hx3.repr hx.c) (hf.extends hx3) h3.memo
    (fun w hw => by simp [spanSubs, hw]) (by unfold Room; omega) as ⟨c, s4, h4⟩
  have hc4 := h4.cost
  refine ⟨h4.inv, hx3.trans h4.ext, ⟨?_, ?_, ?_⟩, by omega⟩
  · exact h4.ext.repr (h3.ext.repr h2.repr)
  · exact h4.ext.repr h3.repr
  · have := h4.repr
    rw [encList_bind] at this
    exact this

/-! ## Appending lists -/

/-- The loop of `append` pushes the members of the list, the last on
top. -/
theorem append_push_spec (xs : List Pat) : ∀ (s : store.Store) (l : store.TermId),
    Wf s → Repr nm s.nodes.val l.val (encList (nm none) xs) → Room s (2 * xs.length + 1) →
    term.append_loop l s ⦃ s' =>
      Wf s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧
        s'.ticks.val = s.ticks.val + 2 * xs.length + 1 ∧
        ∃ fs, stk s' = fs ++ stk s ∧
          List.Forall₂ (fun f t => Repr nm s.nodes.val (fkey f) t) fs xs.reverse ⦄ := by
  unfold term.append_loop
  induction xs with
  | nil =>
    intro s l hW hl hroom
    rw [loop]
    simp only [term.append_loop.body]
    step with read_w s l hW hl.lt (by unfold Room at hroom ⊢; omega) as ⟨r0, hnd, hK⟩
    obtain ⟨nd, s1⟩ := r0
    simp only at hnd hK ⊢
    have hfin : Wf s1 ∧ s1.nodes.val = s.nodes.val ∧ tbl s1 = tbl s ∧
        s1.ticks.val = s.ticks.val + 2 * ([] : List Pat).length + 1 ∧
        ∃ fs, stk s1 = fs ++ stk s ∧
          List.Forall₂ (fun f t => Repr nm s.nodes.val (fkey f) t) fs ([] : List Pat).reverse :=
      ⟨hK.wf, hK.nodes, hK.tbl, by have := hK.ticks; simp; omega, [], by simp [hK.stk], by simp⟩
    cases nd with
    | App h t =>
      obtain ⟨ta, tb, e', -, -⟩ := hl.of_app hnd
      cases e'
    | V0 => step*
    | VL _ => step*
    | VR _ => step*
    | Sym _ => step*
    | Nil => step*
  | cons t ts ih =>
    intro s l hW hl hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    rw [loop]
    simp only [term.append_loop.body]
    step with read_w s l hW hl.lt (by unfold Room; omega) as ⟨r0, hnd, hK⟩
    obtain ⟨nd, s1⟩ := r0
    simp only at hnd hK ⊢
    obtain ⟨p, q, hnode, hp, hq⟩ := Repr.app_inv (ta := t) (tb := encList (nm none) ts) hl
    rw [hnode] at hnd
    cases hnd
    have ht1 := hK.ticks
    have hn1 := hK.nodes
    step with push_w s1 (.Visit p p) hK.wf (by unfold Room; omega) as ⟨s2, a1, a2, a3, hW2, a5⟩
    have hn2 : s2.nodes.val = s.nodes.val := by rw [a1, hn1]
    refine WP.spec_mono (ih s2 q hW2 (by rw [hn2]; exact hq) (by unfold Room; omega)) ?_
    rintro s3 ⟨hW3, b1, b2, b3, fs, b4, b5⟩
    refine ⟨hW3, by rw [b1, hn2], by rw [b2, a2, hK.tbl],
      by simp only [List.length_cons]; omega, fs ++ [.Visit p p], ?_, ?_⟩
    · rw [b4, a5, hK.stk]; simp
    · rw [List.reverse_cons]
      rw [hn2] at b5
      exact List.rel_append b5 (.cons hp .nil)

/-- `unstack` pops the nodes on the stack and puts each before the list built
so far. -/
theorem unstack_spec : ∀ (fs : List store.Frame) (ts acc : List Pat) (s : store.Store)
    (r : store.TermId), Wf s → stk s = fs →
    List.Forall₂ (fun f t => Repr nm s.nodes.val (fkey f) t) fs ts →
    Repr nm s.nodes.val r.val (encList (nm none) acc) → Room s (2 * fs.length + 1) →
    term.unstack_loop s r ⦃ r' s' =>
      Inv s' ∧ Extends s s' ∧ Repr nm s'.nodes.val r'.val (encList (nm none) (ts.reverse ++ acc)) ∧
        s'.ticks.val ≤ s.ticks.val + 2 * fs.length + 1 ∧ tbl s' = tbl s ⦄ := by
  unfold term.unstack_loop
  intro fs
  induction fs with
  | nil =>
    intro ts acc s r hW hstk hF hr hroom
    cases hF
    rw [loop]
    simp only [term.unstack_loop.body]
    step with pop_w s hW (by unfold Room at hroom ⊢; omega) as ⟨r0, p1, p2, p3, hW1, po, pst⟩
    obtain ⟨o, s1⟩ := r0
    simp only at p1 p2 p3 hW1 po pst ⊢
    rw [hstk] at po pst
    simp only [List.head?_nil] at po
    subst po
    step*
    exact ⟨⟨hW1, pst⟩, Extends.of_eq p1 (by omega), by rw [p1]; simpa using hr, by simp; omega, p2⟩
  | cons f fs ih =>
    intro ts acc s r hW hstk hF hr hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    cases hF with
    | cons hf hF' =>
    rename_i t ts'
    rw [loop]
    simp only [term.unstack_loop.body]
    step with pop_w s hW (by unfold Room; omega) as ⟨r0, p1, p2, p3, hW1, po, pst⟩
    obtain ⟨o, s1⟩ := r0
    simp only at p1 p2 p3 hW1 po pst ⊢
    rw [hstk] at po pst
    simp only [List.head?_cons] at po
    simp only [List.tail_cons] at pst
    subst po
    simp only [uncurry]
    rw [node_of_eq f]
    simp only [bind_ok]
    have hx1 : Extends s s1 := Extends.of_eq p1 (by omega)
    step with alloc_w s1 (.App (fid f) r) hW1
      ⟨by rw [fid_val]; exact (hx1.repr hf).lt, (hx1.repr hr).lt⟩ (by unfold Room; omega)
      as ⟨r0, hW2, ht2, htb2, hx2, hr1, hstk2⟩
    obtain ⟨r1, s2⟩ := r0
    simp only at hW2 ht2 htb2 hx2 hr1 hstk2 ⊢
    have hx : Extends s s2 := hx1.trans hx2
    simp only [norm] at hr1
    have hrep : Repr nm s2.nodes.val r1.val (encList (nm none) (t :: acc)) :=
      .app hr1 (by rw [fid_val]; exact hx.repr hf) (hx.repr hr)
    have IH := ih ts' (t :: acc) s2 r1 hW2 (by rw [hstk2, pst])
      (hF'.imp fun _ _ h => hx.repr h) hrep (by unfold Room; omega)
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r', s'⟩ ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, hx.trans h2, ?_, by simp only [List.length_cons]; omega, by rw [h5, htb2, p2]⟩
    simpa using h3

theorem append_spec (xs : List Pat) (s : store.Store) (a b : store.TermId) {ys : List Pat}
    (hI : Inv s) (ha : Repr nm s.nodes.val a.val (encList (nm none) xs))
    (hb : Repr nm s.nodes.val b.val (encList (nm none) ys)) (hroom : Room s (4 * xs.length + 2)) :
    term.append s a b ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ Repr nm s'.nodes.val r.val (encList (nm none) (xs ++ ys)) ∧
        s'.ticks.val ≤ s.ticks.val + 4 * xs.length + 2 ⦄ := by
  unfold term.append
  have hroom' := hroom
  unfold Room at hroom'
  step with append_push_spec (nm := nm) xs s a hI.toWf ha (by unfold Room; omega)
    as ⟨s1, hW1, hn1, htb1, ht1, fs, hstk1, hF⟩
  rw [hI.empty, List.append_nil] at hstk1
  have hlen : fs.length = xs.length := by simpa using hF.length_eq
  have hx1 : Extends s s1 := Extends.of_eq hn1 (by omega)
  step with unstack_spec (nm := nm) fs xs.reverse ys s1 b hW1 hstk1
    (hF.imp fun _ _ h => hx1.repr h) (hx1.repr hb) (by unfold Room; omega)
    as ⟨r, s2, h1, h2, h3, h4, _⟩
  refine ⟨h1, hx1.trans h2, by simpa using h3, by omega⟩

/-! ## Packing and unpacking -/

theorem pack_spec (s : store.Store) (l r c : store.TermId) {tl tr tc : Pat} (hI : Inv s)
    (hl : Repr nm s.nodes.val l.val tl) (hr : Repr nm s.nodes.val r.val tr)
    (hc : Repr nm s.nodes.val c.val tc) (hroom : Room s 2) :
    span.pack s l r c ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ Repr nm s'.nodes.val o.val (.app tl (.app tr tc)) ∧
        s'.ticks.val = s.ticks.val + 2 ⦄ := by
  unfold span.pack
  have hroom' := hroom
  unfold Room at hroom'
  step with alloc_spec s (.App r c) hI ⟨hr.lt, hc.lt⟩ (by unfold Room; omega)
    as ⟨rc, s1, hI1, ht1, htb1, hx1, hr1⟩
  simp only [norm] at hr1
  have hrc : Repr nm s1.nodes.val rc.val (.app tr tc) := .app hr1 (hx1.repr hr) (hx1.repr hc)
  step with alloc_spec s1 (.App l rc) hI1 ⟨(hx1.repr hl).lt, hrc.lt⟩ (by unfold Room; omega)
    as ⟨o, s2, hI2, ht2, htb2, hx2, hr2⟩
  simp only [norm] at hr2
  exact ⟨hI2, hx1.trans hx2, .app hr2 (hx2.repr (hx1.repr hl)) (hx2.repr hrc), by omega⟩

theorem unpack_spec (s : store.Store) (o : store.TermId) {tl tr tc : Pat} (hI : Inv s)
    (ho : Repr nm s.nodes.val o.val (.app tl (.app tr tc))) (hroom : Room s 2) :
    span.unpack s o ⦃ x s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ Repr nm s.nodes.val x.l.val tl ∧
        Repr nm s.nodes.val x.r.val tr ∧ Repr nm s.nodes.val x.c.val tc ∧
        s'.ticks.val = s.ticks.val + 2 ⦄ := by
  unfold span.unpack
  have hroom' := hroom
  unfold Room at hroom'
  obtain ⟨l, rc, hnode, hl, hrc⟩ := Repr.app_inv ho
  obtain ⟨r, c, hnode2, hr, hc⟩ := Repr.app_inv hrc
  step with read_spec s o hI ho.lt (by unfold Room; omega) as ⟨nd, s1, hnd, hK1⟩
  rw [hnode] at hnd
  cases hnd
  have ht1 := hK1.ticks
  simp only
  step with read_spec s1 rc hK1.inv (by rw [hK1.nodes]; exact hrc.lt) (by unfold Room; omega)
    as ⟨nd2, s2, hnd2, hK2⟩
  rw [hK1.nodes, hnode2] at hnd2
  cases hnd2
  have ht2 := hK2.ticks
  step*
  exact ⟨hK2.inv, by rw [hK2.nodes, hK1.nodes], hl, hr, hc, by omega⟩

/-! ## Solving and reading the answer -/

theorem finish_spec (hnm : Function.Injective nm) (s : store.Store) (eqs out : store.TermId)
    {E : Eqns Nat} {o : Pat} {R : Option Span} (hI : Inv s)
    (he : Repr nm s.nodes.val eqs.val (encEqs nm E)) (ho : Repr nm s.nodes.val out.val o)
    (hR : solveOn E o = R.map (packSpan (nm none))) (hroom : Room s (solveCost E o + 2)) :
    span.finish s eqs out ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ OptSpanAt nm s'.nodes.val r R ∧
        s'.ticks.val ≤ s.ticks.val + solveCost E o + 2 ⦄ := by
  unfold span.finish
  have hroom' := hroom
  unfold Room at hroom'
  step with solve_into_spec hnm s eqs out hI he ho (by unfold Room; omega)
    as ⟨ok, o', s1, hI1, hx1, ht1, hres⟩
  cases ok with
  | true =>
    simp only [SolveRes, ↓reduceIte] at hres
    obtain ⟨t', hrep, hsome, -⟩ := hres
    rw [hR] at hsome
    cases R with
    | none => cases hsome
    | some sp =>
      simp only [Option.map_some, Option.some.injEq] at hsome
      subst hsome
      simp only [↓reduceIte]
      step with unpack_spec (nm := nm) s1 o' hI1 hrep (by unfold Room; omega)
        as ⟨x, s2, hI2, hn2, hl, hr, hc, ht2⟩
      refine ⟨hI2, hx1.trans (Extends.of_eq hn2 (by omega)), ?_, by omega⟩
      simp only [OptSpanAt]
      exact ⟨by rw [hn2]; exact hl, by rw [hn2]; exact hr, by rw [hn2]; exact hc⟩
  | false =>
    simp only [SolveRes, Bool.false_eq_true, ↓reduceIte] at hres
    rw [hR] at hres
    cases R with
    | some sp => cases hres
    | none =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      step*
      exact ⟨hI1, hx1, trivial, by omega⟩

/-! ## Composition -/

/-- The equation `compose` solves. -/
def composeEqs (x y : Span) : Eqns Nat := [(x.r.bind lsub, y.l.bind rsub)]

/-- The store of the two spans, renamed apart. -/
def joinStore (x y : Span) : List Pat := x.c.map (Term.bind lsub) ++ y.c.map (Term.bind rsub)

/-- The term `compose` applies the solution to. -/
def composeOut (z : Sym) (x y : Span) : Pat :=
  .app (x.l.bind lsub) (.app (y.r.bind rsub) (encList z (joinStore x y)))

/-- The ticks `compose` may spend. -/
def composeCost (z : Sym) (x y : Span) : Nat :=
  renameCost z x + renameCost z y + (4 * x.c.length + 2) + 5 +
    (solveCost (composeEqs x y) (composeOut z x y) + 2)

theorem compose_spec (hnm : Function.Injective nm) (s : store.Store) (x y : span.Span)
    {sx sy : Span} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sx) (hy : SpanAt nm s.nodes.val y sy)
    (hroom : Room s (composeCost (nm none) sx sy)) :
    span.compose s x y ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ OptSpanAt nm s'.nodes.val r (sx.compose sy) ∧
        s'.ticks.val ≤ s.ticks.val + composeCost (nm none) sx sy ⦄ := by
  unfold span.compose
  have hroom' := hroom
  unfold Room composeCost at hroom'
  step with rename_spec hnm s term.Leaf.Left x (sp := sx) (σ := lsub) hI hx rfl
    (by unfold Room; omega) as ⟨a, s1, hI1, hx1, ha, ht1⟩
  step with rename_spec hnm s1 term.Leaf.Right y (sp := sy) (σ := rsub) hI1 (hy.extends hx1) rfl
    (by unfold Room; omega) as ⟨b, s2, hI2, hx2, hb, ht2⟩
  have hlen : (sx.c.map (Term.bind lsub)).length = sx.c.length := List.length_map _
  step with append_spec (nm := nm) (sx.c.map (Term.bind lsub)) s2 a.c b.c
    (ys := sy.c.map (Term.bind rsub)) hI2 (hx2.repr ha.c) hb.c (by unfold Room; omega)
    as ⟨c, s3, hI3, hx3, hc, ht3⟩
  step with pack_spec (nm := nm) s3 a.l b.r c hI3 (hx3.repr (hx2.repr ha.l)) (hx3.repr hb.r) hc
    (by unfold Room; omega) as ⟨out, s4, hI4, hx4, hout, ht4⟩
  step with alloc_spec s4 .Nil hI4 trivial (by unfold Room; omega)
    as ⟨nil, s5, hI5, ht5, htb5, hx5, hr5⟩
  simp only [norm] at hr5
  have h25 : Extends s2 s5 := hx3.trans (hx4.trans hx5)
  step with alloc_spec s5 (.App a.r b.l) hI5 ⟨(h25.repr (hx2.repr ha.r)).lt, (h25.repr hb.l).lt⟩
    (by unfold Room; omega) as ⟨e, s6, hI6, ht6, htb6, hx6, hr6⟩
  simp only [norm] at hr6
  have hre : Repr nm s6.nodes.val e.val (.app (sx.r.bind lsub) (sy.l.bind rsub)) :=
    .app hr6 (hx6.repr (h25.repr (hx2.repr ha.r))) (hx6.repr (h25.repr hb.l))
  have hrn : Repr nm s6.nodes.val nil.val (encEqs nm []) := hx6.repr (.nil hr5)
  step with alloc_spec s6 (.App e nil) hI6 ⟨hre.lt, hrn.lt⟩ (by unfold Room; omega)
    as ⟨eqs, s7, hI7, ht7, htb7, hx7, hr7⟩
  simp only [norm] at hr7
  have heqs : Repr nm s7.nodes.val eqs.val (encEqs nm (composeEqs sx sy)) :=
    .app hr7 (hx7.repr hre) (hx7.repr hrn)
  have hout7 : Repr nm s7.nodes.val out.val (composeOut (nm none) sx sy) :=
    hx7.repr (hx6.repr (hx5.repr hout))
  refine WP.spec_mono (finish_spec hnm s7 eqs out hI7 heqs hout7
    (compose_bridge (nm none) sx sy) (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4⟩
  refine ⟨h1, ?_, h3, by unfold composeCost; omega⟩
  exact hx1.trans (hx2.trans (hx3.trans (hx4.trans (hx5.trans (hx6.trans (hx7.trans h2))))))

/-! ## Conjunction -/

/-- The equations `meet` solves. -/
def meetEqs (x y : Span) : Eqns Nat :=
  [(x.l.bind lsub, y.l.bind rsub), (x.r.bind lsub, y.r.bind rsub)]

/-- The term `meet` applies the solution to. -/
def meetOut (z : Sym) (x y : Span) : Pat :=
  .app (x.l.bind lsub) (.app (x.r.bind lsub) (encList z (joinStore x y)))

/-- The ticks `meet` may spend. -/
def meetCost (z : Sym) (x y : Span) : Nat :=
  renameCost z x + renameCost z y + (4 * x.c.length + 2) + 7 +
    (solveCost (meetEqs x y) (meetOut z x y) + 2)

theorem meet_spec (hnm : Function.Injective nm) (s : store.Store) (x y : span.Span)
    {sx sy : Span} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sx) (hy : SpanAt nm s.nodes.val y sy)
    (hroom : Room s (meetCost (nm none) sx sy)) :
    span.meet s x y ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ OptSpanAt nm s'.nodes.val r (sx.meet sy) ∧
        s'.ticks.val ≤ s.ticks.val + meetCost (nm none) sx sy ⦄ := by
  unfold span.meet
  have hroom' := hroom
  unfold Room meetCost at hroom'
  step with rename_spec hnm s term.Leaf.Left x (sp := sx) (σ := lsub) hI hx rfl
    (by unfold Room; omega) as ⟨a, s1, hI1, hx1, ha, ht1⟩
  step with rename_spec hnm s1 term.Leaf.Right y (sp := sy) (σ := rsub) hI1 (hy.extends hx1) rfl
    (by unfold Room; omega) as ⟨b, s2, hI2, hx2, hb, ht2⟩
  have hlen : (sx.c.map (Term.bind lsub)).length = sx.c.length := List.length_map _
  step with append_spec (nm := nm) (sx.c.map (Term.bind lsub)) s2 a.c b.c
    (ys := sy.c.map (Term.bind rsub)) hI2 (hx2.repr ha.c) hb.c (by unfold Room; omega)
    as ⟨c, s3, hI3, hx3, hc, ht3⟩
  step with pack_spec (nm := nm) s3 a.l a.r c hI3 (hx3.repr (hx2.repr ha.l))
    (hx3.repr (hx2.repr ha.r)) hc (by unfold Room; omega) as ⟨out, s4, hI4, hx4, hout, ht4⟩
  step with alloc_spec s4 .Nil hI4 trivial (by unfold Room; omega)
    as ⟨nil, s5, hI5, ht5, htb5, hx5, hr5⟩
  simp only [norm] at hr5
  have h25 : Extends s2 s5 := hx3.trans (hx4.trans hx5)
  step with alloc_spec s5 (.App a.r b.r) hI5 ⟨(h25.repr (hx2.repr ha.r)).lt, (h25.repr hb.r).lt⟩
    (by unfold Room; omega) as ⟨e2, s6, hI6, ht6, htb6, hx6, hr6⟩
  simp only [norm] at hr6
  have h26 : Extends s2 s6 := h25.trans hx6
  have hre2 : Repr nm s6.nodes.val e2.val (.app (sx.r.bind lsub) (sy.r.bind rsub)) :=
    .app hr6 (h26.repr (hx2.repr ha.r)) (h26.repr hb.r)
  have hrn : Repr nm s6.nodes.val nil.val (encEqs nm []) := hx6.repr (.nil hr5)
  step with alloc_spec s6 (.App e2 nil) hI6 ⟨hre2.lt, hrn.lt⟩ (by unfold Room; omega)
    as ⟨r2, s7, hI7, ht7, htb7, hx7, hr7⟩
  simp only [norm] at hr7
  have h27 : Extends s2 s7 := h26.trans hx7
  have hrr2 : Repr nm s7.nodes.val r2.val (encEqs nm [(sx.r.bind lsub, sy.r.bind rsub)]) :=
    .app hr7 (hx7.repr hre2) (hx7.repr hrn)
  step with alloc_spec s7 (.App a.l b.l) hI7 ⟨(h27.repr (hx2.repr ha.l)).lt, (h27.repr hb.l).lt⟩
    (by unfold Room; omega) as ⟨e1, s8, hI8, ht8, htb8, hx8, hr8⟩
  simp only [norm] at hr8
  have h28 : Extends s2 s8 := h27.trans hx8
  have hre1 : Repr nm s8.nodes.val e1.val (.app (sx.l.bind lsub) (sy.l.bind rsub)) :=
    .app hr8 (h28.repr (hx2.repr ha.l)) (h28.repr hb.l)
  step with alloc_spec s8 (.App e1 r2) hI8 ⟨hre1.lt, (hx8.repr hrr2).lt⟩ (by unfold Room; omega)
    as ⟨eqs, s9, hI9, ht9, htb9, hx9, hr9⟩
  simp only [norm] at hr9
  have heqs : Repr nm s9.nodes.val eqs.val (encEqs nm (meetEqs sx sy)) :=
    .app hr9 (hx9.repr hre1) (hx9.repr (hx8.repr hrr2))
  have hout9 : Repr nm s9.nodes.val out.val (meetOut (nm none) sx sy) :=
    hx9.repr (hx8.repr (hx7.repr (hx6.repr (hx5.repr hout))))
  refine WP.spec_mono (finish_spec hnm s9 eqs out hI9 heqs hout9
    (meet_bridge (nm none) sx sy) (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4⟩
  refine ⟨h1, ?_, h3, by unfold meetCost; omega⟩
  exact hx1.trans (hx2.trans (hx3.trans (hx4.trans (hx5.trans (hx6.trans (hx7.trans
    (hx8.trans (hx9.trans h2))))))))

end RwLogVerified
