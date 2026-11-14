/-
# Spans and lists in the store

What it is for the store to hold a span and a list of terms, and the Rust
`unstack` and `append`: the list the stack holds in front of a list, and one
list followed by another, within four ticks for each member and two more.
-/
import RwLogVerified.Solve
import RwLogVerified.EncList

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

/-- `append` is the first list followed by the second; the tables are as
they were. -/
theorem append_keep_spec (xs : List Pat) (s : store.Store) (a b : store.TermId) {ys : List Pat}
    (hI : Inv s) (ha : Repr nm s.nodes.val a.val (encList (nm none) xs))
    (hb : Repr nm s.nodes.val b.val (encList (nm none) ys)) (hroom : Room s (4 * xs.length + 2)) :
    term.append s a b ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ Repr nm s'.nodes.val r.val (encList (nm none) (xs ++ ys)) ∧
        s'.ticks.val ≤ s.ticks.val + 4 * xs.length + 2 ∧ tbl s' = tbl s ⦄ := by
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
    as ⟨r, s2, h1, h2, h3, h4, h5⟩
  refine ⟨h1, hx1.trans h2, by simpa using h3, by omega, by rw [h5, htb1]⟩

theorem append_spec (xs : List Pat) (s : store.Store) (a b : store.TermId) {ys : List Pat}
    (hI : Inv s) (ha : Repr nm s.nodes.val a.val (encList (nm none) xs))
    (hb : Repr nm s.nodes.val b.val (encList (nm none) ys)) (hroom : Room s (4 * xs.length + 2)) :
    term.append s a b ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ Repr nm s'.nodes.val r.val (encList (nm none) (xs ++ ys)) ∧
        s'.ticks.val ≤ s.ticks.val + 4 * xs.length + 2 ⦄ := by
  refine WP.spec_mono (append_keep_spec xs s a b hI ha hb hroom) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4, -⟩
  exact ⟨h1, h2, h3, h4⟩

end RwLogVerified
