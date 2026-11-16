/-
# Completeness of any run that serves every goal it opens

Every engine that works on the nodes of the normal form keeps, for goals
`lb ; node ; rb`, the representatives it has found for them, and finds more
by the rules of the derivation kernel (`Trusted/Kernel.lean`). Engines differ
in which goals they open, how they split a chain or a meet, and in what
order they work. This file has the one theorem of completeness they share.

A run is described by what it ever holds: `T t g` is the set of
representatives held for the goal `g` at time `t`, and `O` the set of goals
the run ever opens. Nothing is assumed of the order of the work, of how time
passes, or of tables growing: an answer may be dropped when another covers
it.

`Served D P O T g` says the run does not neglect the goal `g`: by one of the
strategies of its node, everything the strategy can make from the answers the
run ever holds is, at some time, covered by an answer held for `g`. The
strategies are those of the symmetric engine (`lean/SYMMETRIC_ENGINE.md`):

* a span node is composed with the boundaries;
* a call reads the answers of its body, and a union those of its members;
* a chain is split in two anywhere, and either the answers of the two sides
  are joined, or the answers of one side are pushed: the other side is
  opened between the interface of the answer and the boundary, and its
  answers are joined with the answer pushed; or the split has no answer by
  the interface check: every answer of one side ends inside one of finitely
  many interfaces, the other side is opened under each of them, and the run
  never holds an answer for any (`checkL`, `checkR`);
* a meet is split into a member and the meet of the others, and either the
  answers of both are conjoined, or the answers of one are pushed into the
  other, opened between the two interfaces of the answer;
* or the node is unfolded to its end, without any other goal: the run holds
  an answer for every ground relation the node derives (`whole`).

A strategy that pushes need not push every answer: it is enough to push, for
each answer, one that covers it. So an engine that keeps only the answers no
other covers is served.

`Saturated D P O T` says every goal the run opens is a goal of the normal form
between boundaries and is served. Then (`Saturated.covers`) for every goal the run
opens and every ground relation its node derives, the pairs of the relation
between the boundaries of the goal are covered by one answer the run holds
for the goal at some time. The proof is by induction on the depth of the
derivation and then on the node, so it does not matter that the run split
its chains and meets otherwise than the derivation did.

Two consequences. A saturated run that opens the query holds, for every span the
query derives, an answer that covers it (`Saturated.complete`). And two saturated
runs, whatever their schedules, strategies and splits, have the same answers
up to coverage on every goal both open, when the answers of the first are
valid (`Saturated.covers_valid`): no schedule finds what another misses.

Nothing here is about a machine.
-/
import RwLog.Kernel.Wrap
import RwLog.Kernel.NormalFormDepth
import RwLog.Kernel.NormalFormSplit
import RwLog.Kernel.NormalFormSpans

namespace RwLog

open Answer

namespace Saturation

variable {R : Type} [Answer R]

/-- A goal a run may open: its boundaries are boundaries, and its node is a
node of the normal form with first-order spans. -/
structure GoalOk (D : Domain R) (g : Goal R) : Prop where
  lb : IsBound D g.lb
  rb : IsBound D g.rb
  normal : Normal g.node
  fo : g.node.FO

/-- The pairs of `lb ; G ; rb`, for a ground relation `G` the node of the
goal derives. -/
def pairs (P : Program) (g : Goal R) (G : GRel) : PRel :=
  wrapAt P.sorts.interp g.lb (G.at P.sorts.interp) g.rb

/-- What a run holds: the representatives held for each goal at each
time. -/
abbrev Tables (R : Type) := Nat → Goal R → Set R

/-- The run holds the representative for the goal at some time. -/
def Held (T : Tables R) (g : Goal R) (a : R) : Prop := ∃ t, a ∈ T t g

/-- At some time the run holds for the goal a representative that relates
every pair of `X`. -/
def Ev (P : Program) (T : Tables R) (g : Goal R) (X : PRel) : Prop :=
  ∃ a, Held T g a ∧ X ⊆ den P.sorts.interp a

/-- What an operation returns, if anything, is covered for the goal at some
time. -/
def EvO (P : Program) (T : Tables R) (g : Goal R) (o : Option R) : Prop :=
  ∀ c, o = some c → Ev P T g (den P.sorts.interp c)

/-- The run pushes the answers of the goal `h`: for each answer it holds for
`h` it holds one that covers it and that it pushes, which is to open the
goal `next a'` and to cover for `g` what `op a'` makes of each answer of
that goal. -/
def Pushes (P : Program) (O : Set (Goal R)) (T : Tables R) (g h : Goal R)
    (next : R → Goal R) (op : R → R → Option R) : Prop :=
  h ∈ O ∧ ∀ a, Held T h a → ∃ a', Held T h a' ∧
    den P.sorts.interp a ⊆ den P.sorts.interp a' ∧ next a' ∈ O ∧
    ∀ b, Held T (next a') b → EvO P T g (op a' b)

/-- The run does not neglect the goal `g`: one strategy of its node is
carried out on everything the run ever holds. -/
inductive Served (D : Domain R) (P : Program) (O : Set (Goal R)) (T : Tables R) (g : Goal R) :
    Prop where
  /-- A span, composed with the boundaries. -/
  | span (s : Span) (hn : g.node = .span s) (h : EvO P T g (spanBoth D g.lb s g.rb))
  /-- A call reads the answers of its body. -/
  | call (b : Rel) (hb : Charged.bodyOf P g.node = some b) (ho : ⟨g.lb, b, g.rb⟩ ∈ O)
      (h : ∀ a, Held T ⟨g.lb, b, g.rb⟩ a → Ev P T g (den P.sorts.interp a))
  /-- A union reads the answers of its members. -/
  | union (xs : List Rel) (hv : g.node.view = .union xs)
      (h : ∀ x ∈ xs, (⟨g.lb, x, g.rb⟩ : Goal R) ∈ O ∧
        ∀ a, Held T ⟨g.lb, x, g.rb⟩ a → Ev P T g (den P.sorts.interp a))
  /-- A chain split at `i`, the answers of the two sides joined. -/
  | join (xs : List Rel) (i : Nat) (l r : Rel) (hv : g.node.view = .chain xs) (h0 : 0 < i)
      (hi : i < xs.length) (hl : g.node.interval 0 i = some l)
      (hr : g.node.interval i xs.length = some r) (ol : ⟨g.lb, l, none⟩ ∈ O)
      (or : ⟨none, r, g.rb⟩ ∈ O)
      (h : ∀ a b, Held T ⟨g.lb, l, none⟩ a → Held T ⟨none, r, g.rb⟩ b →
        EvO P T g (D.compose a b))
  /-- A chain split at `i`, the answers of the left side pushed into the
  right side. -/
  | pushL (xs : List Rel) (i : Nat) (l r : Rel) (hv : g.node.view = .chain xs) (h0 : 0 < i)
      (hi : i < xs.length) (hl : g.node.interval 0 i = some l)
      (hr : g.node.interval i xs.length = some r)
      (h : Pushes P O T g ⟨g.lb, l, none⟩ (fun a => ⟨D.rightBound a, r, g.rb⟩) D.compose)
  /-- A chain split at `i`, the answers of the right side pushed into the
  left side. -/
  | pushR (xs : List Rel) (i : Nat) (l r : Rel) (hv : g.node.view = .chain xs) (h0 : 0 < i)
      (hi : i < xs.length) (hl : g.node.interval 0 i = some l)
      (hr : g.node.interval i xs.length = some r)
      (h : Pushes P O T g ⟨none, r, g.rb⟩ (fun b => ⟨g.lb, l, D.leftBound b⟩)
        fun b a => D.compose a b)
  /-- A chain split at `i` that has no answer: every answer of the left side
  ends inside one of the interfaces `ps`, the right side is opened under each
  of them, and the run never holds an answer for any. -/
  | checkL (xs : List Rel) (i : Nat) (l r : Rel) (hv : g.node.view = .chain xs) (h0 : 0 < i)
      (hi : i < xs.length) (hl : g.node.interval 0 i = some l)
      (hr : g.node.interval i xs.length = some r) (ps : List R)
      (hedge : ∀ k, ∀ G ∈ GDn P k l, ∀ x m, (x, m) ∈ G.at P.sorts.interp →
        ∃ p ∈ ps, (m, m) ∈ bdenAt P.sorts.interp (some p))
      (h : ∀ p ∈ ps, (⟨some p, r, g.rb⟩ : Goal R) ∈ O ∧ ∀ a, ¬ Held T ⟨some p, r, g.rb⟩ a)
  /-- A chain split at `i` that has no answer: every answer of the right side
  begins inside one of the interfaces `ps`, the left side is opened under
  each of them, and the run never holds an answer for any. -/
  | checkR (xs : List Rel) (i : Nat) (l r : Rel) (hv : g.node.view = .chain xs) (h0 : 0 < i)
      (hi : i < xs.length) (hl : g.node.interval 0 i = some l)
      (hr : g.node.interval i xs.length = some r) (ps : List R)
      (hedge : ∀ k, ∀ G ∈ GDn P k r, ∀ m z, (m, z) ∈ G.at P.sorts.interp →
        ∃ p ∈ ps, (m, m) ∈ bdenAt P.sorts.interp (some p))
      (h : ∀ p ∈ ps, (⟨g.lb, l, some p⟩ : Goal R) ∈ O ∧ ∀ a, ¬ Held T ⟨g.lb, l, some p⟩ a)
  /-- A meet split into its `i`-th member and the others, the answers of
  both conjoined. -/
  | meet (xs : List Rel) (i : Nat) (x r : Rel) (hv : g.node.view = .meet xs)
      (hx : xs[i]? = some x) (hr : g.node.without i = some r) (ox : ⟨g.lb, x, g.rb⟩ ∈ O)
      (or : ⟨g.lb, r, g.rb⟩ ∈ O)
      (h : ∀ a b, Held T ⟨g.lb, x, g.rb⟩ a → Held T ⟨g.lb, r, g.rb⟩ b → EvO P T g (D.meet a b))
  /-- A meet split into its `i`-th member and the others, the answers of the
  member pushed into the others. -/
  | meetL (xs : List Rel) (i : Nat) (x r : Rel) (hv : g.node.view = .meet xs)
      (hx : xs[i]? = some x) (hr : g.node.without i = some r)
      (h : Pushes P O T g ⟨g.lb, x, g.rb⟩ (fun a => ⟨D.leftBound a, r, D.rightBound a⟩) D.meet)
  /-- A meet split into its `i`-th member and the others, the answers of the
  others pushed into the member. -/
  | meetR (xs : List Rel) (i : Nat) (x r : Rel) (hv : g.node.view = .meet xs)
      (hx : xs[i]? = some x) (hr : g.node.without i = some r)
      (h : Pushes P O T g ⟨g.lb, r, g.rb⟩ (fun b => ⟨D.leftBound b, x, D.rightBound b⟩) D.meet)
  /-- The node unfolded to its end: for every ground relation the node
  derives, the run holds an answer that relates its pairs between the
  boundaries. -/
  | whole (h : ∀ k, ∀ G ∈ GDn P k g.node, (pairs P g G).Nonempty → Ev P T g (pairs P g G))

/-- A saturated run: every goal it opens is a goal of the normal form between
boundaries, and is served. -/
structure Saturated (D : Domain R) (P : Program) (O : Set (Goal R)) (T : Tables R) : Prop where
  ok : ∀ g ∈ O, GoalOk D g
  served : ∀ g ∈ O, Served D P O T g

variable {D : Domain R} {P : Program} {O : Set (Goal R)} {T : Tables R}

theorem Ev.mono {g : Goal R} {X Y : PRel} (h : Ev P T g X) (hs : Y ⊆ X) : Ev P T g Y := by
  obtain ⟨a, ha, hX⟩ := h
  exact ⟨a, ha, hs.trans hX⟩

/-- Covered answers of another goal with the same pairs are covered. -/
theorem Ev.through {g h : Goal R} {X : PRel} (hX : Ev P T h X)
    (hh : ∀ a, Held T h a → Ev P T g (den P.sorts.interp a)) : Ev P T g X := by
  obtain ⟨a, ha, hXa⟩ := hX
  exact (hh a ha).mono hXa

section

variable (hL : D.Lawful P.sorts.interp)
include hL

/-- What composing two answers makes covers the compositions of what they
cover. -/
theorem compose_cov {g : Goal R} {a b : R} {X₁ X₂ : PRel}
    (h₁ : X₁ ⊆ den P.sorts.interp a) (h₂ : X₂ ⊆ den P.sorts.interp b)
    (hne : (X₁.comp X₂).Nonempty) (h : EvO P T g (D.compose a b)) : Ev P T g (X₁.comp X₂) := by
  have hsub : X₁.comp X₂ ⊆ (den P.sorts.interp a).comp (den P.sorts.interp b) :=
    fun _ ⟨m, ha, hb⟩ => ⟨m, h₁ ha, h₂ hb⟩
  cases hc : D.compose a b with
  | none =>
    obtain ⟨p, hp⟩ := hne
    exact absurd (hsub hp) (Set.eq_empty_iff_forall_notMem.1 (hL.compose_none _ _ hc) p)
  | some c => exact (h c hc).mono (by rw [hL.compose_some _ _ _ hc]; exact hsub)

/-- What conjoining two answers makes covers the pairs both cover. -/
theorem meet_cov {g : Goal R} {a b : R} {X₁ X₂ : PRel}
    (h₁ : X₁ ⊆ den P.sorts.interp a) (h₂ : X₂ ⊆ den P.sorts.interp b)
    (hne : (X₁ ∩ X₂).Nonempty) (h : EvO P T g (D.meet a b)) : Ev P T g (X₁ ∩ X₂) := by
  have hsub : X₁ ∩ X₂ ⊆ den P.sorts.interp a ∩ den P.sorts.interp b :=
    Set.inter_subset_inter h₁ h₂
  cases hc : D.meet a b with
  | none =>
    obtain ⟨p, hp⟩ := hne
    exact absurd (hsub hp) (Set.eq_empty_iff_forall_notMem.1 (hL.meet_none _ _ hc) p)
  | some c => exact (h c hc).mono (by rw [hL.meet_some _ _ _ hc]; exact hsub)

omit hL in
/-- The pairs of a chain between boundaries are the compositions of the
pairs of its two sides, the middle left open. -/
theorem pairs_comp (lb rb : Option R) (l r e : Rel) (G₁ G₂ : GRel) :
    pairs P ⟨lb, e, rb⟩ (G₁.comp G₂) =
      (pairs P ⟨lb, l, none⟩ G₁).comp (pairs P ⟨none, r, rb⟩ G₂) :=
  wrap_comp lb rb G₁ G₂

/-- A saturated run covers, for every goal it opens, the pairs of every ground
relation the node of the goal derives. -/
theorem Saturated.covers (hF : Saturated D P O T) (k : Nat) :
    ∀ (n : Nat) (g : Goal R), g ∈ O → g.node.size = n → ∀ G ∈ GDn P k g.node,
      (pairs P g G).Nonempty → Ev P T g (pairs P g G) := by
  induction k with
  | zero =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih => exact fun g hg hn G hG hne => step hL hF 0 (fun _ _ _ h hG _ _ => by
        rw [(gdn_bodyOf h 0).2] at hG; exact absurd hG (Set.notMem_empty _)) n ih g hg hn G hG hne
  | succ k ihk =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih => exact fun g hg hn G hG hne => step hL hF (k + 1) (fun _ _ G h hG ho hne => by
        rw [(gdn_bodyOf h k).1] at hG
        exact ihk _ _ ho rfl G hG hne) n ih g hg hn G hG hne
where
  /-- One node, given the nodes below it and the bodies of calls. -/
  step (hL : D.Lawful P.sorts.interp) (hF : Saturated D P O T) (k : Nat)
      (hcall : ∀ (g : Goal R) (b : Rel) (G : GRel), Charged.bodyOf P g.node = some b →
        G ∈ GDn P k g.node → (⟨g.lb, b, g.rb⟩ : Goal R) ∈ O →
        (pairs P ⟨g.lb, b, g.rb⟩ G).Nonempty → Ev P T ⟨g.lb, b, g.rb⟩ (pairs P ⟨g.lb, b, g.rb⟩ G))
      (n : Nat)
      (ih : ∀ m < n, ∀ (g : Goal R), g ∈ O → g.node.size = m → ∀ G ∈ GDn P k g.node,
        (pairs P g G).Nonempty → Ev P T g (pairs P g G))
      (g : Goal R) (hg : g ∈ O) (hn : g.node.size = n) (G : GRel) (hG : G ∈ GDn P k g.node)
      (hne : (pairs P g G).Nonempty) : Ev P T g (pairs P g G) := by
    have hok := hF.ok g hg
    cases hF.served g hg with
    | span s hs h =>
      rw [hs, (gdn_laws P k).span] at hG
      obtain rfl : G = s.den := hG
      have hfo : s.firstOrder = true := hok.fo s (by rw [hs]; simp [RelOf.spans])
      have hden := denO_spanBoth hL hfo g.lb g.rb
      cases hsb : spanBoth D g.lb s g.rb with
      | none =>
        rw [hsb, Domain.denO_none] at hden
        exact absurd hden.symm hne.ne_empty
      | some z =>
        rw [hsb, Domain.denO_some] at hden
        exact (h z hsb).mono (by rw [hden]; exact subset_rfl)
    | call b hb ho h => exact (hcall g b G hb hG ho hne).through h
    | union xs hv h =>
      have hparts := hok.normal.view_union_eq hv
      rw [← (gdn_laws P k).gd_unionParts, ← hparts] at hG
      obtain ⟨x, hx, hGx⟩ := Set.mem_iUnion₂.1 hG
      obtain ⟨ho, hh⟩ := h x hx
      exact (ih _ (by rw [← hn]; exact hok.normal.union_member_lt hv hx) _ ho rfl G hGx hne).through hh
    | join xs i l r hv h0 hi hl hr ol or h =>
      obtain ⟨hlen, l', r', hl', hr', -, hsl, hsr⟩ := hok.normal.chain_split hv h0 hi
      obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hl)
      obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
      rw [(gdn_laws P k).chain_split hl (hlen ▸ hr)] at hG
      obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
      have he : pairs P g (G₁.comp G₂) =
          (pairs P ⟨g.lb, l', none⟩ G₁).comp (pairs P ⟨none, r', g.rb⟩ G₂) :=
        pairs_comp g.lb g.rb l' r' g.node G₁ G₂
      rw [he] at hne ⊢
      obtain ⟨⟨p, q⟩, m, hpm, hmq⟩ := hne
      obtain ⟨a, ha, hXa⟩ := ih _ (hn ▸ hsl) _ ol rfl G₁ hG₁ ⟨_, hpm⟩
      obtain ⟨b, hb, hXb⟩ := ih _ (hn ▸ hsr) _ or rfl G₂ hG₂ ⟨_, hmq⟩
      exact compose_cov hL hXa hXb ⟨_, m, hpm, hmq⟩ (h a b ha hb)
    | pushL xs i l r hv h0 hi hl hr h =>
      obtain ⟨hlen, l', r', hl', hr', -, hsl, hsr⟩ := hok.normal.chain_split hv h0 hi
      obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hl)
      obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
      rw [(gdn_laws P k).chain_split hl (hlen ▸ hr)] at hG
      obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
      have he : pairs P g (G₁.comp G₂) =
          (pairs P ⟨g.lb, l', none⟩ G₁).comp (pairs P ⟨none, r', g.rb⟩ G₂) :=
        pairs_comp g.lb g.rb l' r' g.node G₁ G₂
      rw [he] at hne ⊢
      obtain ⟨ol, hp⟩ := h
      obtain ⟨⟨p, q⟩, m, hpm, hmq⟩ := hne
      obtain ⟨a, ha, hXa⟩ := ih _ (hn ▸ hsl) _ ol rfl G₁ hG₁ ⟨_, hpm⟩
      obtain ⟨a', -, haa, on, hb⟩ := hp a ha
      have hXa' := hXa.trans haa
      have hsub : (pairs P ⟨g.lb, l', none⟩ G₁).comp (pairs P ⟨none, r', g.rb⟩ G₂) ⊆
          (pairs P ⟨g.lb, l', none⟩ G₁).comp (pairs P ⟨D.rightBound a', r', g.rb⟩ G₂) := by
        rintro ⟨p, q⟩ ⟨m, hpm, hmq⟩
        refine ⟨m, hpm, ?_⟩
        obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 hmq
        obtain rfl : u = m := q₁
        exact mem_wrapAt.2 ⟨u, v, rightBound_at hL (hXa' hpm), q₂, q₃⟩
      obtain ⟨m', -, hmq'⟩ := hsub ⟨m, hpm, hmq⟩
      obtain ⟨b, hbh, hXb⟩ := ih _ (hn ▸ hsr) _ on rfl G₂ hG₂ ⟨_, hmq'⟩
      exact (compose_cov hL hXa' hXb ⟨_, hsub ⟨m, hpm, hmq⟩⟩ (hb b hbh)).mono hsub
    | pushR xs i l r hv h0 hi hl hr h =>
      obtain ⟨hlen, l', r', hl', hr', -, hsl, hsr⟩ := hok.normal.chain_split hv h0 hi
      obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hl)
      obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
      rw [(gdn_laws P k).chain_split hl (hlen ▸ hr)] at hG
      obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
      have he : pairs P g (G₁.comp G₂) =
          (pairs P ⟨g.lb, l', none⟩ G₁).comp (pairs P ⟨none, r', g.rb⟩ G₂) :=
        pairs_comp g.lb g.rb l' r' g.node G₁ G₂
      rw [he] at hne ⊢
      obtain ⟨or, hp⟩ := h
      obtain ⟨⟨p, q⟩, m, hpm, hmq⟩ := hne
      obtain ⟨b, hb, hXb⟩ := ih _ (hn ▸ hsr) _ or rfl G₂ hG₂ ⟨_, hmq⟩
      obtain ⟨b', -, hbb, on, ha⟩ := hp b hb
      have hXb' := hXb.trans hbb
      have hsub : (pairs P ⟨g.lb, l', none⟩ G₁).comp (pairs P ⟨none, r', g.rb⟩ G₂) ⊆
          (pairs P ⟨g.lb, l', D.leftBound b'⟩ G₁).comp (pairs P ⟨none, r', g.rb⟩ G₂) := by
        rintro ⟨p, q⟩ ⟨m, hpm, hmq⟩
        refine ⟨m, ?_, hmq⟩
        obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 hpm
        obtain rfl : m = v := q₃
        exact mem_wrapAt.2 ⟨u, m, q₁, q₂, leftBound_at hL (hXb' hmq)⟩
      obtain ⟨m', hpm', -⟩ := hsub ⟨m, hpm, hmq⟩
      obtain ⟨a, hah, hXa⟩ := ih _ (hn ▸ hsl) _ on rfl G₁ hG₁ ⟨_, hpm'⟩
      exact (compose_cov hL hXa hXb' ⟨_, hsub ⟨m, hpm, hmq⟩⟩ (ha a hah)).mono hsub
    | checkL xs i l r hv h0 hi hl hr ps hedge h =>
      obtain ⟨hlen, l', r', hl', hr', -, hsl, hsr⟩ := hok.normal.chain_split hv h0 hi
      obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hl)
      obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
      rw [(gdn_laws P k).chain_split hl (hlen ▸ hr)] at hG
      obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
      have he : pairs P g (G₁.comp G₂) =
          (pairs P ⟨g.lb, l', none⟩ G₁).comp (pairs P ⟨none, r', g.rb⟩ G₂) :=
        pairs_comp g.lb g.rb l' r' g.node G₁ G₂
      rw [he] at hne
      obtain ⟨⟨p, q⟩, m, hpm, hmq⟩ := hne
      obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 hpm
      obtain ⟨u', v', r₁, r₂, r₃⟩ := mem_wrapAt.1 hmq
      have e₁ : m = v := q₃
      have e₂ : u' = m := r₁
      obtain ⟨b, hb, hbm⟩ := hedge k G₁ hG₁ u v q₂
      obtain ⟨ho, hno⟩ := h b hb
      have hmq' : (m, q) ∈ pairs P ⟨some b, r', g.rb⟩ G₂ :=
        mem_wrapAt.2 ⟨m, v', by rw [e₁]; exact hbm, by rw [← e₂]; exact r₂, r₃⟩
      obtain ⟨c, hc, -⟩ := ih _ (hn ▸ hsr) _ ho rfl G₂ hG₂ ⟨_, hmq'⟩
      exact absurd hc (hno c)
    | checkR xs i l r hv h0 hi hl hr ps hedge h =>
      obtain ⟨hlen, l', r', hl', hr', -, hsl, hsr⟩ := hok.normal.chain_split hv h0 hi
      obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hl)
      obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
      rw [(gdn_laws P k).chain_split hl (hlen ▸ hr)] at hG
      obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
      have he : pairs P g (G₁.comp G₂) =
          (pairs P ⟨g.lb, l', none⟩ G₁).comp (pairs P ⟨none, r', g.rb⟩ G₂) :=
        pairs_comp g.lb g.rb l' r' g.node G₁ G₂
      rw [he] at hne
      obtain ⟨⟨p, q⟩, m, hpm, hmq⟩ := hne
      obtain ⟨u, v, q₁, q₂, q₃⟩ := mem_wrapAt.1 hpm
      obtain ⟨u', v', r₁, r₂, r₃⟩ := mem_wrapAt.1 hmq
      have e₁ : m = v := q₃
      have e₂ : u' = m := r₁
      obtain ⟨b, hb, hbm⟩ := hedge k G₂ hG₂ u' v' r₂
      obtain ⟨ho, hno⟩ := h b hb
      have hpm' : (p, m) ∈ pairs P ⟨g.lb, l', some b⟩ G₁ :=
        mem_wrapAt.2 ⟨u, m, q₁, by rw [e₁]; exact q₂, by rw [← e₂]; exact hbm⟩
      obtain ⟨c, hc, -⟩ := ih _ (hn ▸ hsl) _ ho rfl G₁ hG₁ ⟨_, hpm'⟩
      exact absurd hc (hno c)
    | meet xs i x r hv hx hr ox or h =>
      obtain ⟨hparts, x', r', hx', hr', -, -, hsx, hsr⟩ :=
        hok.normal.meet_split hv (i := i) (by
          rcases Nat.lt_or_ge i xs.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hx; cases hx)
      obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
      obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
      rw [(gdn_laws P k).meet_split (hparts ▸ hx) hr] at hG
      obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
      have he : pairs P g (G₁.meet G₂) = pairs P ⟨g.lb, x', g.rb⟩ G₁ ∩ pairs P ⟨g.lb, r', g.rb⟩ G₂ :=
        wrap_meet hL hok.lb hok.rb G₁ G₂
      rw [he] at hne ⊢
      obtain ⟨p, hp₁, hp₂⟩ := hne
      obtain ⟨a, ha, hXa⟩ := ih _ (hn ▸ hsx) _ ox rfl G₁ hG₁ ⟨_, hp₁⟩
      obtain ⟨b, hb, hXb⟩ := ih _ (hn ▸ hsr) _ or rfl G₂ hG₂ ⟨_, hp₂⟩
      exact meet_cov hL hXa hXb ⟨p, hp₁, hp₂⟩ (h a b ha hb)
    | meetL xs i x r hv hx hr h =>
      obtain ⟨hparts, x', r', hx', hr', -, -, hsx, hsr⟩ :=
        hok.normal.meet_split hv (i := i) (by
          rcases Nat.lt_or_ge i xs.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hx; cases hx)
      obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
      obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
      rw [(gdn_laws P k).meet_split (hparts ▸ hx) hr] at hG
      obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
      have he : pairs P g (G₁.meet G₂) = pairs P ⟨g.lb, x', g.rb⟩ G₁ ∩ pairs P ⟨g.lb, r', g.rb⟩ G₂ :=
        wrap_meet hL hok.lb hok.rb G₁ G₂
      rw [he] at hne ⊢
      obtain ⟨ox, hp⟩ := h
      obtain ⟨p, hp₁, hp₂⟩ := hne
      obtain ⟨a, ha, hXa⟩ := ih _ (hn ▸ hsx) _ ox rfl G₁ hG₁ ⟨_, hp₁⟩
      obtain ⟨a', -, haa, on, hb⟩ := hp a ha
      have hXa' := hXa.trans haa
      have hsub : pairs P ⟨g.lb, x', g.rb⟩ G₁ ∩ pairs P ⟨g.lb, r', g.rb⟩ G₂ ⊆
          pairs P ⟨g.lb, x', g.rb⟩ G₁ ∩ pairs P ⟨D.leftBound a', r', D.rightBound a'⟩ G₂ := by
        rintro ⟨u, v⟩ ⟨h₁, h₂⟩
        refine ⟨h₁, ?_⟩
        obtain ⟨-, hm, -⟩ := (mem_wrap hL hok.lb hok.rb).1 h₂
        exact mem_wrapAt.2 ⟨u, v, leftBound_at hL (hXa' h₁), hm, rightBound_at hL (hXa' h₁)⟩
      obtain ⟨b, hbh, hXb⟩ := ih _ (hn ▸ hsr) _ on rfl G₂ hG₂ ⟨p, (hsub ⟨hp₁, hp₂⟩).2⟩
      exact (meet_cov hL hXa' hXb ⟨p, hsub ⟨hp₁, hp₂⟩⟩ (hb b hbh)).mono hsub
    | meetR xs i x r hv hx hr h =>
      obtain ⟨hparts, x', r', hx', hr', -, -, hsx, hsr⟩ :=
        hok.normal.meet_split hv (i := i) (by
          rcases Nat.lt_or_ge i xs.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hx; cases hx)
      obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
      obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
      rw [(gdn_laws P k).meet_split (hparts ▸ hx) hr] at hG
      obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := hG
      have he : pairs P g (G₁.meet G₂) = pairs P ⟨g.lb, x', g.rb⟩ G₁ ∩ pairs P ⟨g.lb, r', g.rb⟩ G₂ :=
        wrap_meet hL hok.lb hok.rb G₁ G₂
      rw [he] at hne ⊢
      obtain ⟨or, hp⟩ := h
      obtain ⟨p, hp₁, hp₂⟩ := hne
      obtain ⟨b, hb, hXb⟩ := ih _ (hn ▸ hsr) _ or rfl G₂ hG₂ ⟨_, hp₂⟩
      obtain ⟨b', -, hbb, on, ha⟩ := hp b hb
      have hXb' := hXb.trans hbb
      have hsub : pairs P ⟨g.lb, x', g.rb⟩ G₁ ∩ pairs P ⟨g.lb, r', g.rb⟩ G₂ ⊆
          pairs P ⟨D.leftBound b', x', D.rightBound b'⟩ G₁ ∩ pairs P ⟨g.lb, r', g.rb⟩ G₂ := by
        rintro ⟨u, v⟩ ⟨h₁, h₂⟩
        refine ⟨?_, h₂⟩
        obtain ⟨-, hm, -⟩ := (mem_wrap hL hok.lb hok.rb).1 h₁
        exact mem_wrapAt.2 ⟨u, v, leftBound_at hL (hXb' h₂), hm, rightBound_at hL (hXb' h₂)⟩
      obtain ⟨a, hah, hXa⟩ := ih _ (hn ▸ hsx) _ on rfl G₁ hG₁ ⟨p, (hsub ⟨hp₁, hp₂⟩).1⟩
      have := meet_cov hL hXb' hXa ⟨p, (hsub ⟨hp₁, hp₂⟩).2, (hsub ⟨hp₁, hp₂⟩).1⟩ (ha a hah)
      exact this.mono (fun q hq => ⟨(hsub hq).2, (hsub hq).1⟩)
    | whole h => exact h k G hG hne

/-- A saturated run that opens the query holds, for every span the query
derives, an answer that relates every pair the span relates. -/
theorem Saturated.complete (hF : Saturated D P O T) {q : Rel} (hq : (⟨none, q.norm, none⟩ : Goal R) ∈ O)
    {s : Span} (hs : Derives P q s) (hne : (s.denAt P.sorts.interp).Nonempty) :
    ∃ a, Held T ⟨none, q.norm, none⟩ a ∧ s.denAt P.sorts.interp ⊆ den P.sorts.interp a := by
  obtain ⟨s', hs', he⟩ := derives_norm_iff.2 ⟨s, hs, rfl⟩
  obtain ⟨k, hk⟩ := mem_gd_iff.1 (derives_iff_derivesG.1 ⟨s', hs', he⟩).1
  have hp : pairs P (⟨none, q.norm, none⟩ : Goal R) s.den = s.denAt P.sorts.interp := by
    rw [Span.denAt_eq]; exact wrapAt_none _
  have := hF.covers hL k _ _ hq rfl s.den hk (by rw [hp]; exact hne)
  rwa [hp] at this

/-- A saturated run that opens the query holds, for every pair the query
relates, an answer that relates it. -/
theorem Saturated.covers_pair (hF : Saturated D P O T) {q : Rel}
    (hq : (⟨none, q.norm, none⟩ : Goal R) ∈ O) {p : GTerm × GTerm} (hp : p ∈ P.pairs q) :
    ∃ a, Held T ⟨none, q.norm, none⟩ a ∧ p ∈ den P.sorts.interp a := by
  obtain ⟨k, G, hG, hpG⟩ := pairs_gdn hp
  have hpp : pairs P (⟨none, q.norm, none⟩ : Goal R) G = G.at P.sorts.interp := wrapAt_none _
  obtain ⟨a, ha, hsub⟩ := hF.covers hL k _ _ hq rfl G hG (by rw [hpp]; exact ⟨p, hpG⟩)
  exact ⟨a, ha, hsub (by rw [hpp]; exact hpG)⟩

/-- No schedule finds what another misses: a valid answer of a goal, however
it was found, is covered by an answer a saturated run holds for the goal. -/
theorem Saturated.covers_valid (hF : Saturated D P O T) {g : Goal R} (hg : g ∈ O) {a : R}
    (ha : Valid D P g a) : Ev P T g (den P.sorts.interp a) := by
  obtain ⟨s, hs, he⟩ := ha.2 hL
  obtain ⟨k, hk⟩ := mem_gd_iff.1 (derives_iff_derivesG.1 ⟨s, hs, rfl⟩).1
  have := hF.covers hL k _ _ hg rfl s.den hk (by
    change (wrapAt _ _ _ _).Nonempty
    rw [← he]; exact hL.live a)
  exact this.mono (by rw [he]; exact subset_rfl)

end

end Saturation

end RwLog
