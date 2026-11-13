/-
# Matching, coverage without constraints, and equality

`mmatch_spec`: the Rust `mmatch` decides `matchInto`. Table `A` holds, for
each node of the pattern already matched, the term it matched; for a variable
that is its binding. A node of the pattern is matched once however often it
occurs, so the cost is six ticks plus twelve for each distinct subterm of the
pattern, whatever the size of the term it is matched against. `mmatch` is a
loop over the stack of the store: a `Visit` frame asks for a pattern to be
matched onto a term, and a `Build` frame writes the entry of an application
once both its parts are matched. `run` is what the frames on the stack still
ask for, and the loop keeps it equal to the answer of `matchInto`.

`covers_plain_spec`: for a covering span with no constraints, `covers_plain`
decides `Span.covers?`.

`span_eq_spec`: `span_eq` decides equality of spans in three ticks, because
equal terms are the same node.
-/
import RwLogVerified.Chain
import RwLogVerified.MatchSpec

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term RwLog.Matching

variable {nm : Option Nat → Sym}

/-! ## Matching -/

/-- Table `A` and the bindings `θ` of the specification say the same. -/
structure MatchOK (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat)
    (θ : PSubst) : Prop where
  /-- An entry is a pattern whose variables are bound, and what it is under
  the bindings. -/
  memo : ∀ k w, A k = some w → ∃ pk tw, Repr nm nodes k pk ∧ Repr nm nodes w tw ∧
    Bound θ pk ∧ pk.bind θ.apply = tw
  /-- A variable with no entry is unbound. -/
  free : ∀ k v, VarAt nodes k v → A k = none → θ.lookup v = none

/-- A node gets an entry that is right under the same bindings. -/
theorem MatchOK.set {nodes : List store.Node} {A : Nat → Option Nat} {θ : PSubst} {k w : Nat}
    {pk tw : Pat} (h : MatchOK nm nodes A θ) (hk : Repr nm nodes k pk) (hw : Repr nm nodes w tw)
    (hb : Bound θ pk) (hbind : pk.bind θ.apply = tw) :
    MatchOK nm nodes (Function.update A k (some w)) θ := by
  refine ⟨fun k' w' hk' => ?_, fun k' v hv hk' => ?_⟩
  · by_cases e : k' = k
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hk'
      subst hk'
      exact ⟨pk, tw, hk, hw, hb, hbind⟩
    · rw [Function.update_of_ne e] at hk'
      exact h.memo k' w' hk'
  · by_cases e : k' = k
    · subst e; simp at hk'
    · rw [Function.update_of_ne e] at hk'
      exact h.free k' v hv hk'

/-- The node of an unbound variable gets its entry, and the variable its
binding. -/
theorem MatchOK.bind_var {nodes : List store.Node} (hN : NodesOK nodes) {A : Nat → Option Nat}
    {θ : PSubst} {k w v : Nat} {tw : Pat} (h : MatchOK nm nodes A θ) (hk : VarAt nodes k v)
    (hw : Repr nm nodes w tw) (hnone : A k = none) :
    matchInto (Term.var v) tw θ = some ((v, tw) :: θ) ∧
      MatchOK nm nodes (Function.update A k (some w)) ((v, tw) :: θ) := by
  have hfree := h.free k v hk hnone
  have hmi : matchInto (Term.var v) tw θ = some ((v, tw) :: θ) := by simp [matchInto, hfree]
  obtain ⟨hext, hb, hbind⟩ := matchInto_ext _ _ _ _ hmi
  refine ⟨hmi, fun k' w' hk' => ?_, fun k' v' hv' hk' => ?_⟩
  · by_cases e : k' = k
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hk'
      subst hk'
      exact ⟨_, tw, .var hk, hw, hb, hbind⟩
    · rw [Function.update_of_ne e] at hk'
      obtain ⟨pk, tw', h1, h2, h3, h4⟩ := h.memo k' w' hk'
      obtain ⟨h3', h4'⟩ := bound_ext h3 hext
      exact ⟨pk, tw', h1, h2, h3', by rw [h4', h4]⟩
  · by_cases e : k' = k
    · subst e; simp at hk'
    · rw [Function.update_of_ne e] at hk'
      have hne : v' ≠ v := by
        rintro rfl
        exact e (hv'.inj hN hk)
      rw [lookup_cons_ne hne]
      exact h.free k' v' hv' hk'

/-- The parts a pair of applications waits for. -/
def MKid (nodes : List store.Node) (g c : Nat × Nat) : Prop :=
  ∃ q1 q2 u1 u2 : store.TermId, nodes[g.1]? = some (.App q1 q2) ∧
    nodes[g.2]? = some (.App u1 u2) ∧ (c = (q1.val, u1.val) ∨ c = (q2.val, u2.val))

/-- What the frames still ask for: a `Visit` frame matches its pattern onto
its term, and a `Build` frame asks for nothing. `xs` gives the pattern and
the term of each frame. -/
def run : List store.Frame → List (Pat × Pat) → PSubst → Option PSubst
  | .Visit _ _ :: st, x :: xs, θ => (matchInto x.1 x.2 θ).bind (run st xs)
  | .Build _ _ :: st, _ :: xs, θ => run st xs θ
  | _, _, θ => some θ

/-- The pattern and the term of a frame. -/
def FrameAt (nm : Option Nat → Sym) (nodes : List store.Node) (tp : Pat) (f : store.Frame)
    (x : Pat × Pat) : Prop :=
  x.1 ∈ tp.subs ∧ Repr nm nodes (fkey f) x.1 ∧ Repr nm nodes (faux f) x.2

/-- The state of a match that has not failed: `A0` is the table at the start,
`R` the answer of the specification, and `θ` the bindings so far. -/
structure MSt (nm : Option Nat → Sym) (nodes : List store.Node) (tp : Pat) (R : Option PSubst)
    (A0 A : Nat → Option Nat) (st : List store.Frame) (θ : PSubst) : Prop where
  ok : MatchOK nm nodes A θ
  grow : ∀ k, A0 k ≠ none → A k ≠ none
  frames : ∃ xs, List.Forall₂ (FrameAt nm nodes tp) st xs ∧ run st xs θ = R
  builds : ∀ q u, store.Frame.Build q u ∈ st → ∃ q1 q2 u1 u2 : store.TermId,
    nodes[q.val]? = some (.App q1 q2) ∧ nodes[u.val]? = some (.App u1 u2)
  waits : Waits (MKid nodes) (fun c => A c.1 = some c.2) (fun k => A k ≠ none) st

variable {nodes : List store.Node} {tp : Pat} {R : Option PSubst} {A0 A : Nat → Option Nat}

/-- The node of the top frame gets its entry, and the frames left ask for
`R` under the new bindings. -/
theorem MSt.set {f : store.Frame} {st : List store.Frame} {θ θ' : PSubst}
    (h : MSt nm nodes tp R A0 A (f :: st) θ) (hnone : A (fkey f) = none)
    (hok : MatchOK nm nodes (Function.update A (fkey f) (some (faux f))) θ')
    (hfr : ∃ xs, List.Forall₂ (FrameAt nm nodes tp) st xs ∧ run st xs θ' = R) :
    MSt nm nodes tp R A0 (Function.update A (fkey f) (some (faux f))) st θ' := by
  have hup : ∀ k, A k ≠ none → Function.update A (fkey f) (some (faux f)) k ≠ none := by
    intro k hk
    by_cases e : k = fkey f
    · subst e; simp
    · rw [Function.update_of_ne e]; exact hk
  refine ⟨hok, fun k hk => hup k (h.grow k hk), hfr,
    fun q u hq => h.builds q u (List.mem_cons_of_mem _ hq), ?_⟩
  refine h.waits.pop (fun c hc => ?_) (by simp [goal]) (fun k hk => ?_)
  · by_cases e : c.1 = fkey f
    · rw [e, hnone] at hc; cases hc
    · rw [Function.update_of_ne e]; exact hc
  · by_cases e : k = fkey f
    · exact Or.inr e
    · rw [Function.update_of_ne e] at hk; exact Or.inl hk

/-- The pattern of the top frame has an entry: the frame is satisfied when
the entry is its term, and the match fails when it is not. -/
theorem MSt.hit (hnm : Function.Injective nm) (hN : NodesOK nodes) {q u : store.TermId}
    {st : List store.Frame} {θ : PSubst} {w : Nat}
    (h : MSt nm nodes tp R A0 A (.Visit q u :: st) θ) (hA : A q.val = some w) :
    (w = u.val → MSt nm nodes tp R A0 A st θ) ∧ (w ≠ u.val → R = none) := by
  obtain ⟨xs, hF, hrun⟩ := h.frames
  cases hF with
  | cons hx hF' =>
  rename_i x xs'
  obtain ⟨-, hq, hu⟩ := hx
  simp only [fkey, faux] at hq hu
  obtain ⟨pk, tw, hk, hw, hbd, hbind⟩ := h.ok.memo _ _ hA
  have := hq.unique hk
  subst this
  have hmi := matchInto_bound x.1 x.2 θ hbd
  rw [hbind] at hmi
  simp only [run] at hrun
  constructor
  · intro e
    subst e
    have : tw = x.2 := hw.unique hu
    simp only [hmi, this, ↓reduceIte, Option.bind_some] at hrun
    refine ⟨h.ok, h.grow, ⟨xs', hF', hrun⟩, fun q' u' hq' => h.builds q' u' (List.mem_cons_of_mem _ hq'),
      h.waits.pop (fun _ hc => hc) (by simpa [goal, fkey, faux] using hA) (fun _ hk => Or.inl hk)⟩
  · intro e
    have : tw ≠ x.2 := fun e' => e (Repr.inj hnm hN hw (e' ▸ hu))
    simp only [hmi, this, ↓reduceIte, Option.bind_none] at hrun
    exact hrun.symm

/-- A variable at the top with no entry: it is bound to the term. -/
theorem MSt.var (hN : NodesOK nodes) {q u : store.TermId} {st : List store.Frame} {θ : PSubst}
    {v : Nat} (h : MSt nm nodes tp R A0 A (.Visit q u :: st) θ) (hnone : A q.val = none)
    (hv : VarAt nodes q.val v) :
    ∃ θ', MSt nm nodes tp R A0 (Function.update A q.val (some u.val)) st θ' := by
  obtain ⟨xs, hF, hrun⟩ := h.frames
  cases hF with
  | cons hx hF' =>
  rename_i x xs'
  obtain ⟨-, hq, hu⟩ := hx
  simp only [fkey, faux] at hq hu
  have e : x.1 = Term.var v := hq.unique (.var hv)
  obtain ⟨hmi, hok⟩ := h.ok.bind_var hN hv hu hnone
  simp only [run, e, hmi, Option.bind_some] at hrun
  exact ⟨_, h.set (f := .Visit q u) hnone hok ⟨xs', hF', hrun⟩⟩

/-- A symbol at the top with no entry: the frame is satisfied when the term
is the same node, and the match fails when it is not. -/
theorem MSt.atom (hnm : Function.Injective nm) (hN : NodesOK nodes) {q u : store.TermId}
    {st : List store.Frame} {θ : PSubst} {f : Sym}
    (h : MSt nm nodes tp R A0 A (.Visit q u :: st) θ) (hnone : A q.val = none)
    (hf : Repr nm nodes q.val (Term.sym f)) :
    (q.val = u.val → MSt nm nodes tp R A0 (Function.update A q.val (some u.val)) st θ) ∧
      (q.val ≠ u.val → R = none) := by
  obtain ⟨xs, hF, hrun⟩ := h.frames
  cases hF with
  | cons hx hF' =>
  rename_i x xs'
  obtain ⟨-, hq, hu⟩ := hx
  simp only [fkey, faux] at hq hu
  have e : x.1 = Term.sym f := hq.unique hf
  simp only [run, e] at hrun
  constructor
  · intro e'
    have ht : x.2 = Term.sym f := by rw [e'] at hf; exact hu.unique hf
    rw [ht] at hrun hu
    simp only [matchInto, ↓reduceIte, Option.bind_some] at hrun
    exact h.set (f := .Visit q u) hnone
      (h.ok.set hf hu (fun w hw => by simp [Term.vars] at hw) rfl) ⟨xs', hF', hrun⟩
  · intro e'
    have hne : x.2 ≠ Term.sym f := fun h' => e' (Repr.inj hnm hN hf (h' ▸ hu))
    have hmi : matchInto (Term.sym f) x.2 θ = none := by
      cases hx2 : x.2 with
      | var w => simp [matchInto]
      | app a b => simp [matchInto]
      | sym g =>
        have : f ≠ g := fun h' => hne (by rw [hx2, h'])
        simp [matchInto, this]
    rw [hmi] at hrun
    exact hrun.symm

/-- An application at the top with no entry, against an application: its
`Build` frame goes under frames for the two parts. -/
theorem MSt.expand (hN : NodesOK nodes) {q u q1 q2 u1 u2 : store.TermId}
    {st : List store.Frame} {θ : PSubst}
    (h : MSt nm nodes tp R A0 A (.Visit q u :: st) θ) (hnone : A q.val = none)
    (hq : nodes[q.val]? = some (.App q1 q2)) (hu : nodes[u.val]? = some (.App u1 u2)) :
    MSt nm nodes tp R A0 A (.Visit q1 u1 :: .Visit q2 u2 :: .Build q u :: st) θ := by
  obtain ⟨xs, hF, hrun⟩ := h.frames
  cases hF with
  | cons hx hF' =>
  rename_i x xs'
  obtain ⟨hs, hrq, hru⟩ := hx
  simp only [fkey, faux] at hrq hru
  obtain ⟨pa, pb, e1, ha, hb⟩ := hrq.of_app hq
  obtain ⟨ta, tb, e2, hta, htb⟩ := hru.of_app hu
  have hfit := hN.fits _ _ hq
  simp only [Fits] at hfit
  rw [e1] at hs
  refine ⟨h.ok, h.grow, ⟨(pa, ta) :: (pb, tb) :: x :: xs', ?_, ?_⟩, ?_, ?_⟩
  · exact .cons ⟨Term.subs_app_left hs, ha, hta⟩
      (.cons ⟨Term.subs_app_right hs, hb, htb⟩ (.cons ⟨by rw [e1]; exact hs, hrq, hru⟩ hF'))
  · simp only [run, e1, e2, matchInto] at hrun ⊢
    rw [← hrun, Option.bind_assoc]
  · intro q' u' hq'
    simp only [List.mem_cons, reduceCtorEq, store.Frame.Build.injEq, false_or] at hq'
    rcases hq' with ⟨rfl, rfl⟩ | hq'
    · exact ⟨q1, q2, u1, u2, hq, hu⟩
    · exact h.builds q' u' (List.mem_cons_of_mem _ hq')
  · refine h.waits.expand (by simpa using hnone) ?_ trivial trivial hfit.1 hfit.2
    rintro c ⟨a1, a2, b1, b2, hn1, hn2, hc⟩
    simp only at hn1 hn2
    rw [hq] at hn1
    rw [hu] at hn2
    cases hn1
    cases hn2
    exact hc

/-- An application at the top with no entry, against a term that is not an
application: the match fails. -/
theorem MSt.clash {q u q1 q2 : store.TermId} {st : List store.Frame} {θ : PSubst}
    {n : store.Node} (h : MSt nm nodes tp R A0 A (.Visit q u :: st) θ)
    (hq : nodes[q.val]? = some (.App q1 q2)) (hu : nodes[u.val]? = some n)
    (hn : ∀ a b, n ≠ .App a b) : R = none := by
  obtain ⟨xs, hF, hrun⟩ := h.frames
  cases hF with
  | cons hx hF' =>
  rename_i x xs'
  obtain ⟨-, hrq, hru⟩ := hx
  simp only [fkey, faux] at hrq hru
  obtain ⟨pa, pb, e1, -, -⟩ := hrq.of_app hq
  have hmi : matchInto (Term.app pa pb) x.2 θ = none := by
    cases hx2 : x.2 with
    | var w => simp [matchInto]
    | sym g => simp [matchInto]
    | app a b =>
      rw [hx2] at hru
      obtain ⟨a', b', hn', -, -⟩ := Repr.app_inv hru
      rw [hu] at hn'
      cases hn'
      exact absurd rfl (hn a' b')
  simp only [run, e1, hmi] at hrun
  exact hrun.symm

/-- A `Build` frame at the top: both parts are matched, so its node gets its
entry. -/
theorem MSt.build {q u : store.TermId} {st : List store.Frame} {θ : PSubst}
    (h : MSt nm nodes tp R A0 A (.Build q u :: st) θ) :
    A q.val = none ∧ MSt nm nodes tp R A0 (Function.update A q.val (some u.val)) st θ := by
  obtain ⟨xs, hF, hrun⟩ := h.frames
  cases hF with
  | cons hx hF' =>
  rename_i x xs'
  obtain ⟨-, hrq, hru⟩ := hx
  simp only [fkey, faux] at hrq hru
  obtain ⟨q1, q2, u1, u2, hq, hu⟩ := h.builds q u List.mem_cons_self
  obtain ⟨h1, h2⟩ := h.waits.top
  have hnone : A q.val = none := by simpa using h1
  obtain ⟨pa, pb, e1, ha, hb⟩ := hrq.of_app hq
  obtain ⟨ta, tb, e2, hta, htb⟩ := hru.of_app hu
  have m1 := h2 (q1.val, u1.val) ⟨q1, q2, u1, u2, hq, hu, Or.inl rfl⟩
  have m2 := h2 (q2.val, u2.val) ⟨q1, q2, u1, u2, hq, hu, Or.inr rfl⟩
  obtain ⟨pk1, tw1, k1, w1, b1, c1⟩ := h.ok.memo _ _ m1
  obtain ⟨pk2, tw2, k2, w2, b2, c2⟩ := h.ok.memo _ _ m2
  have := ha.unique k1
  subst this
  have := hb.unique k2
  subst this
  have := hta.unique w1
  subst this
  have := htb.unique w2
  subst this
  simp only [run] at hrun
  refine ⟨hnone, h.set (f := .Build q u) hnone (h.ok.set hrq hru ?_ ?_) ⟨xs', hF', hrun⟩⟩
  · rw [e1]
    intro v hv
    simp only [Term.vars, List.mem_append] at hv
    rcases hv with hv | hv
    · exact b1 v hv
    · exact b2 v hv
  · rw [e1, e2, Term.bind_app, c1, c2]

theorem MSt.top_frame {f : store.Frame} {st : List store.Frame} {θ : PSubst}
    (h : MSt nm nodes tp R A0 A (f :: st) θ) :
    ∃ pq tu, pq ∈ tp.subs ∧ Repr nm nodes (fkey f) pq ∧ Repr nm nodes (faux f) tu := by
  obtain ⟨xs, hF, -⟩ := h.frames
  cases hF with
  | cons hx _ => exact ⟨_, _, hx⟩

theorem MSt.done {θ : PSubst} (h : MSt nm nodes tp R A0 A [] θ) : R = some θ := by
  obtain ⟨xs, hF, hrun⟩ := h.frames
  cases hF
  simpa [run] using hrun.symm

/-- What `mmatch` leaves. -/
structure MatchPost (nm : Option Nat → Sym) (s s' : store.Store) (θ : PSubst) (tp tt : Pat)
    (S : Finset Pat) (b : Bool) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  tblB : tbl s' .B = tbl s .B
  res : b = (matchInto tp tt θ).isSome
  ok : b = true → ∃ θ', matchInto tp tt θ = some θ' ∧ MatchOK nm s'.nodes.val (tbl s' .A) θ'
  grow : ∀ k, tbl s .A k ≠ none → tbl s' .A k ≠ none
  cost : s'.ticks.val + 12 * (if b then (pending nm s'.nodes.val (tbl s' .A) S).card else 0) ≤
    s.ticks.val + 6 + 12 * (pending nm s.nodes.val (tbl s .A) S).card
  mono : s.ticks.val ≤ s'.ticks.val

/-- The invariant of the loop. `s0` is the store at the start, `R` the answer
of the specification and `B` the tick count the loop stays under. Once the
match has failed the stack is empty. -/
def MInv (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (R : Option PSubst)
    (S : Finset Pat) (B : Nat) : store.Store × Bool → Prop
  | (s, ok) => Wf s ∧ s.nodes.val = s0.nodes.val ∧ tbl s .B = tbl s0 .B ∧
    (∀ k, tbl s0 .A k ≠ none → tbl s .A k ≠ none) ∧
    if ok then ∃ θ U, MSt nm s0.nodes.val tp R (tbl s0 .A) (tbl s .A) (stk s) θ ∧
        Unb nm s0.nodes.val (tbl s .A) S (stk s) U ∧
        s.ticks.val + 3 * nV (stk s) + 2 * nB (stk s) + 12 * U.card + 2 ≤ B
    else stk s = [] ∧ R = none ∧ s.ticks.val + 1 ≤ B

def MDone (nm : Option Nat → Sym) (s0 : store.Store) (R : Option PSubst)
    (S : Finset Pat) (B : Nat) : Bool × store.Store → Prop
  | (b, s) => Wf s ∧ stk s = [] ∧ s.nodes.val = s0.nodes.val ∧ tbl s .B = tbl s0 .B ∧
    (∀ k, tbl s0 .A k ≠ none → tbl s .A k ≠ none) ∧ b = R.isSome ∧
    (b = true → ∃ θ', R = some θ' ∧ MatchOK nm s0.nodes.val (tbl s .A) θ') ∧
    s.ticks.val + 12 * (if b then (pending nm s0.nodes.val (tbl s .A) S).card else 0) ≤ B

def MBodyPost (nm : Option Nat → Sym) (s0 : store.Store) (tp : Pat) (R : Option PSubst)
    (S : Finset Pat) (B : Nat) (t0 : Nat) :
    ControlFlow (store.Store × Bool) (Bool × store.Store) → Prop
  | .done y => MDone nm s0 R S B y ∧ t0 ≤ y.2.ticks.val
  | .cont x => MInv nm s0 tp R S B x ∧ t0 < x.1.ticks.val

theorem mmatch_body_spec (hnm : Function.Injective nm) (s0 : store.Store) (tp : Pat)
    (R : Option PSubst) (S : Finset Pat) (B : Nat) (hB : 40 * B + 100 ≤ Usize.max)
    (hN : NodesOK s0.nodes.val) (hS : tp.subs ⊆ S) (s : store.Store) (ok : Bool)
    (h : MInv nm s0 tp R S B (s, ok)) :
    cover.mmatch_loop.body s ok ⦃ r => MBodyPost nm s0 tp R S B s.ticks.val r ⦄ := by
  unfold cover.mmatch_loop.body
  obtain ⟨hW, hn, hTB, hG, h⟩ := h
  have hlow : s.ticks.val + 1 ≤ B := by
    cases ok with
    | true => simp only [↓reduceIte] at h; obtain ⟨θ, U, -, -, hc⟩ := h; omega
    | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact h.2.2
  step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
  cases hst : stk s with
  | nil =>
    rw [hst] at eo est h
    simp only [List.head?_nil, List.tail_nil] at eo est
    subst eo
    simp only [WP.spec_ok]
    cases ok with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      refine ⟨⟨hW1, est, by rw [e1, hn], by rw [e2, hTB], by rw [e2]; exact hG,
        by rw [h.2.1]; rfl, fun hb => (by cases hb), ?_⟩, by simp only; omega⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨θ, U, hM, hU, hc⟩ := h
      have hR := hM.done
      refine ⟨⟨hW1, est, by rw [e1, hn], by rw [e2, hTB], by rw [e2]; exact hG,
        by rw [hR]; rfl, fun _ => ⟨θ, hR, by rw [e2]; exact hM.ok⟩, ?_⟩, by simp only; omega⟩
      have := hU.card_le
      simp only [nV_nil, nB_nil] at hc
      simp only [↓reduceIte]
      rw [e2]
      omega
  | cons fr st =>
    rw [hst] at eo est h
    simp only [List.head?_cons, List.tail_cons] at eo est
    subst eo
    cases ok with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases h.1
    | true =>
    simp only [↓reduceIte] at h
    obtain ⟨θ, U, hM, hU, hc⟩ := h
    obtain ⟨pq, tu, hpq, hq, hu⟩ := hM.top_frame
    -- the match fails: the stack is dropped
    have hfail : ∀ (s3 : store.Store), Wf s3 → s3.nodes.val = s.nodes.val → tbl s3 = tbl s →
        s3.ticks.val + 2 ≤ B → s.ticks.val < s3.ticks.val → R = none →
        (do
          let s4 ← store.Store.drop_stack s3
          ok (ControlFlow.cont (s4, false) :
            ControlFlow (store.Store × Bool) (Bool × store.Store))) ⦃ r =>
          MBodyPost nm s0 tp R S B s.ticks.val r ⦄ := by
      intro s3 hW3 hn3 htb3 ht3 hlt hR
      step with drop_stack_w s3 hW3 (by unfold Room; omega) as ⟨s4, d1, d2, d3, hW4, d5⟩
      refine ⟨⟨hW4, by rw [d1, hn3, hn], by rw [d2, htb3, hTB],
        by rw [d2, htb3]; exact hG, ?_⟩, by simp only; omega⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨d5, hR, by omega⟩
    cases fr with
    | Visit q u =>
      simp only [fkey, faux] at hq hu
      simp only [nV_visit, nB_visit] at hc
      simp only
      step with get_w s1 .A q hW1 (by rw [e1, hn]; exact hq.lt) (by unfold Room; omega)
        as ⟨o1, s2, ho1, hK2⟩
      rw [e2] at ho1
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, e1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, e2]
      have hstk2 : stk s2 = st := by rw [hK2.stk, est]
      -- the entry of the node is written
      have hset : ∀ (s3 : store.Store) (θ' : PSubst), Wf s3 → s3.nodes.val = s.nodes.val →
          tbl s3 = tbl s → stk s3 = st → s3.ticks.val ≤ s.ticks.val + 4 →
          s.ticks.val < s3.ticks.val →
          MSt nm s0.nodes.val tp R (tbl s0 .A)
            (Function.update (tbl s .A) q.val (some u.val)) st θ' →
          pq ∈ U →
          (do
            let s4 ← store.Store.set s3 store.Tbl.A q u
            ok (ControlFlow.cont (s4, true) :
              ControlFlow (store.Store × Bool) (Bool × store.Store))) ⦃ r =>
            MBodyPost nm s0 tp R S B s.ticks.val r ⦄ := by
        intro s3 θ' hW3 hn3 htb3 hstk3 ht3 hlt hM' htU
        have hU1 := card_erase_add_one htU
        step with set_w s3 .A q u hW3 (by rw [hn3, hn]; exact hq.lt) (by unfold Room; omega)
          as ⟨s4, g1, g2, g3, g4, g5, g6⟩
        rw [htb3] at g4
        refine ⟨⟨g3, by rw [g1, hn3, hn], by rw [g5 .B (by simp), htb3, hTB],
          by rw [g4]; exact hM'.grow, ?_⟩, by simp only; omega⟩
        simp only [↓reduceIte]
        rw [g4, g6, hstk3]
        refine ⟨θ', U.erase pq, hM', ?_, by omega⟩
        simpa [fkey] using hU.set (f := .Visit q u) hq [] u.val
      cases o1 with
      | some w =>
        simp only [Option.map_some] at ho1
        obtain ⟨hyes, hno⟩ := hM.hit hnm hN ho1.symm
        simp only
        step with same_w s2 w u hK2.wf (by unfold Room; omega) as ⟨b, s3, hb, hK3⟩
        have ht3 := hK3.ticks
        have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
        have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
        by_cases e : w.val = u.val
        · have : b = true := by simp [hb, e]
          subst this
          simp only [↓reduceIte, WP.spec_ok]
          refine ⟨⟨hK3.wf, by rw [hn3, hn], by rw [htb3, hTB], by rw [htb3]; exact hG, ?_⟩,
            by simp only; omega⟩
          simp only [↓reduceIte]
          rw [htb3, hK3.stk, hstk2]
          exact ⟨θ, U, hyes e, hU.pop_visit trivial, by omega⟩
        · have : b = false := by simp [hb, e]
          subst this
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hfail s3 hK3.wf hn3 htb3 (by omega) (by omega) (hno e)
      | none =>
        simp only [Option.map_none] at ho1
        have hnone : tbl s .A q.val = none := ho1.symm
        have htU : pq ∈ U := hU.mem_top hnm hN hM.waits hq hnone (hS hpq)
        have hU1 := card_erase_add_one htU
        simp only
        step with read_w s2 q hK2.wf (by rw [hn2, hn]; exact hq.lt) (by unfold Room; omega)
          as ⟨nd, s3, hnd, hK3⟩
        rw [hn2, hn] at hnd
        have ht3 := hK3.ticks
        have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
        have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, htb2]
        have hstk3 : stk s3 = st := by rw [hK3.stk, hstk2]
        have hvar : ∀ v, VarAt s0.nodes.val q.val v →
            (do
              let s4 ← store.Store.set s3 store.Tbl.A q u
              ok (ControlFlow.cont (s4, true) :
                ControlFlow (store.Store × Bool) (Bool × store.Store))) ⦃ r =>
              MBodyPost nm s0 tp R S B s.ticks.val r ⦄ := by
          intro v hva
          obtain ⟨θ', hM'⟩ := hM.var hN hnone hva
          exact hset s3 θ' hK3.wf hn3 htb3 hstk3 (by omega) (by omega) hM' htU
        have hatom : ∀ f, Repr nm s0.nodes.val q.val (Term.sym f) →
            (do
              let (b, s4) ← store.Store.same s3 q u
              if b then do
                let s5 ← store.Store.set s4 store.Tbl.A q u
                ok (ControlFlow.cont (s5, true) :
                  ControlFlow (store.Store × Bool) (Bool × store.Store))
              else do
                let s5 ← store.Store.drop_stack s4
                ok (ControlFlow.cont (s5, false))) ⦃ r =>
              MBodyPost nm s0 tp R S B s.ticks.val r ⦄ := by
          intro f hf
          obtain ⟨hyes, hno⟩ := hM.atom hnm hN hnone hf
          step with same_w s3 q u hK3.wf (by unfold Room; omega) as ⟨b, s4, hb, hK4⟩
          have ht4 := hK4.ticks
          have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
          have htb4 : tbl s4 = tbl s := by rw [hK4.tbl, htb3]
          by_cases e : q.val = u.val
          · have : b = true := by simp [hb, e]
            subst this
            simp only [↓reduceIte]
            exact hset s4 θ hK4.wf hn4 htb4 (by rw [hK4.stk, hstk3]) (by omega) (by omega)
              (hyes e) htU
          · have : b = false := by simp [hb, e]
            subst this
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact hfail s4 hK4.wf hn4 htb4 (by omega) (by omega) (hno e)
        cases nd with
        | V0 =>
          obtain ⟨v, -, hva⟩ := hq.of_var hnd trivial
          exact hvar v hva
        | VL a =>
          obtain ⟨v, -, hva⟩ := hq.of_var hnd trivial
          exact hvar v hva
        | VR a =>
          obtain ⟨v, -, hva⟩ := hq.of_var hnd trivial
          exact hvar v hva
        | Sym g => exact hatom _ (.sym hnd)
        | Nil => exact hatom _ (.nil hnd)
        | App q1 q2 =>
          simp only
          step with read_w s3 u hK3.wf (by rw [hn3, hn]; exact hu.lt) (by unfold Room; omega)
            as ⟨n1, s4, hnu, hK4⟩
          rw [hn3, hn] at hnu
          have ht4 := hK4.ticks
          have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn3]
          have htb4 : tbl s4 = tbl s := by rw [hK4.tbl, htb3]
          have hstk4 : stk s4 = st := by rw [hK4.stk, hstk3]
          have hclash : (∀ a b, n1 ≠ .App a b) →
              (do
                let s5 ← store.Store.drop_stack s4
                ok (ControlFlow.cont (s5, false) :
                  ControlFlow (store.Store × Bool) (Bool × store.Store))) ⦃ r =>
                MBodyPost nm s0 tp R S B s.ticks.val r ⦄ := fun hna =>
            hfail s4 hK4.wf hn4 htb4 (by omega) (by omega) (hM.clash hnd hnu hna)
          cases n1 with
          | V0 => exact hclash (by simp)
          | VL a => exact hclash (by simp)
          | VR a => exact hclash (by simp)
          | Sym g => exact hclash (by simp)
          | Nil => exact hclash (by simp)
          | App u1 u2 =>
            simp only
            step with push_w s4 (.Build q u) hK4.wf (by unfold Room; omega)
              as ⟨s5, b1, b2, b3, hW5, b5⟩
            step with push_w s5 (.Visit q2 u2) hW5 (by unfold Room; omega)
              as ⟨s6, c1, c2, c3, hW6, c5⟩
            step with push_w s6 (.Visit q1 u1) hW6 (by unfold Room; omega)
              as ⟨s7, d1, d2, d3, hW7, d5⟩
            have htb7 : tbl s7 = tbl s := by rw [d2, c2, b2, htb4]
            refine ⟨⟨hW7, by rw [d1, c1, b1, hn4, hn], by rw [htb7, hTB],
              by rw [htb7]; exact hG, ?_⟩, by simp only; omega⟩
            simp only [↓reduceIte]
            rw [htb7, d5, c5, b5, hstk4]
            refine ⟨θ, U.erase pq, hM.expand hN hnone hnd hnu, hU.expand hq, ?_⟩
            simp only [nV_visit, nB_visit, nV_build, nB_build]
            omega
    | Build q u =>
      simp only [fkey, faux] at hq hu
      simp only [nV_build, nB_build] at hc
      obtain ⟨hnone, hM'⟩ := hM.build
      simp only
      step with set_w s1 .A q u hW1 (by rw [e1, hn]; exact hq.lt) (by unfold Room; omega)
        as ⟨s4, g1, g2, g3, g4, g5, g6⟩
      rw [e2] at g4
      refine ⟨⟨g3, by rw [g1, e1, hn], by rw [g5 .B (by simp), e2, hTB],
        by rw [g4]; exact hM'.grow, ?_⟩, by simp only; omega⟩
      simp only [↓reduceIte]
      rw [g4, g6, est]
      refine ⟨θ, U.erase pq, hM', ?_, ?_⟩
      · simpa [fkey] using hU.set (f := .Build q u) hq [] u.val
      · have := Finset.card_erase_le (s := U) (a := pq)
        omega

/-- `mmatch` decides one-way matching. It spends six ticks, and twelve more
for each term of `S` that had no table entry and gets one. -/
theorem mmatch_spec (hnm : Function.Injective nm) (s : store.Store) (p t : store.TermId)
    {tp tt : Pat} {θ : PSubst} (S : Finset Pat) (hI : Inv s) (hp : Repr nm s.nodes.val p.val tp)
    (ht : Repr nm s.nodes.val t.val tt) (hM : MatchOK nm s.nodes.val (tbl s .A) θ)
    (hS : tp.subs ⊆ S) (hroom : Room s (6 + 12 * (pending nm s.nodes.val (tbl s .A) S).card)) :
    cover.mmatch s p t ⦃ b s' => MatchPost nm s s' θ tp tt S b ⦄ := by
  unfold cover.mmatch cover.mmatch_loop
  have hroom' := hroom
  unfold Room at hroom'
  step with push_w s (.Visit p t) hI.toWf (by unfold Room; omega) as ⟨s1, a1, a2, a3, hW1, a5⟩
  rw [hI.empty] at a5
  let B := s.ticks.val + 6 + 12 * (pending nm s.nodes.val (tbl s .A) S).card
  have hloop := loop.spec_decr_nat
    (fun y : store.Store × Bool => B + 1 - y.1.ticks.val)
    (fun y => MInv nm s tp (matchInto tp tt θ) S B y ∧ s.ticks.val ≤ y.1.ticks.val)
    (fun y : Bool × store.Store => MatchPost nm s y.2 θ tp tt S y.1)
    (fun y : store.Store × Bool => cover.mmatch_loop.body y.1 y.2) (s1, true)
    (by
      rintro ⟨y, ok⟩ ⟨hinv, hlow⟩
      simp only at hlow
      refine WP.spec_mono (mmatch_body_spec hnm s tp _ S B (by omega) hI.nodesOK hS y ok hinv) ?_
      intro r hr
      cases r with
      | done z =>
        obtain ⟨b, z⟩ := z
        obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9⟩ := hr
        simp only at h9
        refine ⟨⟨h1, h2⟩, h3, h4, h6, fun hb => ?_, h5, ?_, by simp only; omega⟩
        · obtain ⟨θ', e, hok⟩ := h7 hb
          exact ⟨θ', e, by rw [h3]; exact hok⟩
        · simp only
          rw [h3]
          exact h8
      | cont y' =>
        obtain ⟨h1, h2⟩ := hr
        obtain ⟨z, ok'⟩ := y'
        have hz : z.ticks.val + 1 ≤ B := by
          obtain ⟨-, -, -, -, h⟩ := h1
          cases ok' with
          | true => simp only [↓reduceIte] at h; obtain ⟨θ', U, -, -, hc⟩ := h; omega
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact h.2.2
        simp only at h2
        exact ⟨⟨h1, by simp only; omega⟩, by simp only; omega⟩)
    ⟨⟨hW1, a1, by rw [a2], by rw [a2]; exact fun _ h => h, by
      simp only [↓reduceIte]
      rw [a5, a2]
      refine ⟨θ, pending nm s.nodes.val (tbl s .A) S,
        ⟨hM, fun _ h => h, ⟨[(tp, tt)], .cons ⟨Term.self_mem_subs tp, hp, ht⟩ .nil, ?_⟩,
          fun q u hq => by simp at hq, Waits.single p t⟩, Unb.start _ _ _ _, ?_⟩
      · simp [run]
      · simp only [nV_visit, nV_nil, nB_visit, nB_nil]
        omega⟩, by simp only; omega⟩
  exact hloop

/-! ## Coverage by a span with no constraints -/

/-- The ticks `covers_plain` may spend: they depend on the covering span
only. -/
def coversPlainCost (a : Span) : Nat := 13 + 12 * (a.l.subs ∪ a.r.subs).card

theorem covers_plain_spec (hnm : Function.Injective nm) (s : store.Store) (a x : span.Span)
    {sa sx : Span} (hI : Inv s) (ha : SpanAt nm s.nodes.val a sa) (hx : SpanAt nm s.nodes.val x sx)
    (hc : sa.c = []) (hroom : Room s (coversPlainCost sa)) :
    cover.covers_plain s a x ⦃ b s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ b = sa.covers? sx ∧
        s'.ticks.val ≤ s.ticks.val + coversPlainCost sa ∧ s.ticks.val ≤ s'.ticks.val ⦄ := by
  unfold cover.covers_plain
  have hroom' := hroom
  unfold Room coversPlainCost at hroom'
  unfold coversPlainCost
  step with clear_spec s .A hI (by unfold Room; omega) as ⟨s1, c1, c2, c3, c4, c5⟩
  have hpc := pending_card_le (nm := nm) s1.nodes.val (tbl s1 .A) (sa.l.subs ∪ sa.r.subs)
  have hM0 : MatchOK nm s1.nodes.val (tbl s1 .A) [] :=
    ⟨(fun k w hk => by rw [c4] at hk; cases hk), fun _ _ _ _ => rfl⟩
  step with mmatch_spec hnm s1 a.l x.l (tp := sa.l) (tt := sx.l) (θ := [])
    (sa.l.subs ∪ sa.r.subs) c3 (by rw [c1]; exact ha.l) (by rw [c1]; exact hx.l) hM0
    Finset.subset_union_left (by unfold Room; omega) as ⟨b, s2, h2⟩
  have hc2 := h2.cost
  have hm2 := h2.mono
  have hn2 : s2.nodes.val = s.nodes.val := by rw [h2.nodes, c1]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hc2 ⊢
    have hm : matchInto sa.l sx.l [] = none := by
      have := h2.res
      cases h : matchInto sa.l sx.l [] with
      | none => rfl
      | some _ => rw [h] at this; cases this
    step*
    exact ⟨h2.inv, hn2, by simp [Span.covers?, hm], by omega, by omega⟩
  | true =>
    simp only [↓reduceIte] at hc2 ⊢
    obtain ⟨θ1, hm1, hM1⟩ := h2.ok rfl
    refine WP.spec_mono (mmatch_spec hnm s2 a.r x.r (tp := sa.r) (tt := sx.r) (θ := θ1)
      (sa.l.subs ∪ sa.r.subs) h2.inv (by rw [hn2]; exact ha.r) (by rw [hn2]; exact hx.r) hM1
      Finset.subset_union_right (by unfold Room; omega)) ?_
    rintro ⟨b2, s3⟩ h3
    have hc3 := h3.cost
    have hm3 := h3.mono
    refine ⟨h3.inv, by rw [h3.nodes, hn2], ?_, ?_, by omega⟩
    · rw [h3.res]
      simp only [Span.covers?, hm1, Option.bind_some, hc]
      cases matchInto sa.r sx.r θ1 <;> simp [matchAll]
    · have : s3.ticks.val ≤ s2.ticks.val + 6 +
          12 * (pending nm s2.nodes.val (tbl s2 .A) (sa.l.subs ∪ sa.r.subs)).card := by
        have h0 : 0 ≤ 12 * (if b2 = true then
          (pending nm s3.nodes.val (tbl s3 .A) (sa.l.subs ∪ sa.r.subs)).card else 0) := Nat.zero_le _
        omega
      omega

/-! ## Equality of spans -/

theorem spanAt_eq_iff (hnm : Function.Injective nm) {s : store.Store} (hI : Inv s)
    {x y : span.Span} {sx sy : Span} (hx : SpanAt nm s.nodes.val x sx)
    (hy : SpanAt nm s.nodes.val y sy) :
    sx = sy ↔ x.l.val = y.l.val ∧ x.r.val = y.r.val ∧ x.c.val = y.c.val := by
  constructor
  · rintro rfl
    exact ⟨Repr.inj hnm hI.nodesOK hx.l hy.l, Repr.inj hnm hI.nodesOK hx.r hy.r,
      Repr.inj hnm hI.nodesOK hx.c hy.c⟩
  · rintro ⟨h1, h2, h3⟩
    have e1 : sx.l = sy.l := by have := hx.l; rw [h1] at this; exact this.unique hy.l
    have e2 : sx.r = sy.r := by have := hx.r; rw [h2] at this; exact this.unique hy.r
    have e3 : sx.c = sy.c := by
      have := hx.c; rw [h3] at this; exact encList_inj _ (this.unique hy.c)
    cases sx; cases sy
    simp only at e1 e2 e3
    rw [e1, e2, e3]

theorem span_eq_spec (hnm : Function.Injective nm) (s : store.Store) (x y : span.Span)
    {sx sy : Span} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sx) (hy : SpanAt nm s.nodes.val y sy)
    (hroom : Room s 3) :
    cover.span_eq s x y ⦃ b s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧ b = decide (sx = sy) ∧
        s'.ticks.val ≤ s.ticks.val + 3 ∧ s.ticks.val ≤ s'.ticks.val ⦄ := by
  unfold cover.span_eq
  have hroom' := hroom
  unfold Room at hroom'
  have hiff := spanAt_eq_iff hnm hI hx hy
  step with same_spec s x.l y.l hI (by unfold Room; omega) as ⟨b, s1, hb, hK1⟩
  have ht1 := hK1.ticks
  by_cases e1 : x.l.val = y.l.val
  · have : b = true := by simp [hb, e1]
    subst this
    simp only [↓reduceIte]
    step with same_spec s1 x.r y.r hK1.inv (by unfold Room; omega) as ⟨b1, s2, hb1, hK2⟩
    have ht2 := hK2.ticks
    by_cases e2 : x.r.val = y.r.val
    · have : b1 = true := by simp [hb1, e2]
      subst this
      simp only [↓reduceIte]
      refine WP.spec_mono (same_spec s2 x.c y.c hK2.inv (by unfold Room; omega)) ?_
      rintro ⟨b2, s3⟩ ⟨hb2, hK3⟩
      have ht3 := hK3.ticks
      refine ⟨hK3.inv, by rw [hK3.nodes, hK2.nodes, hK1.nodes], by rw [hK3.tbl, hK2.tbl, hK1.tbl],
        ?_, by omega, by omega⟩
      rw [hb2]
      simp only [hiff, e1, e2, true_and]
    · have : b1 = false := by simp [hb1, e2]
      subst this
      simp only [Bool.false_eq_true, ↓reduceIte]
      step*
      refine ⟨hK2.inv, by rw [hK2.nodes, hK1.nodes], by rw [hK2.tbl, hK1.tbl], ?_, by omega, by omega⟩
      simp [hiff, e2]
  · have : b = false := by simp [hb, e1]
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte]
    step*
    refine ⟨hK1.inv, hK1.nodes, hK1.tbl, ?_, by omega, by omega⟩
    simp [hiff, e1]

end RwLogVerified
