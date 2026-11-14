/-
# Two runs of the tabled machine, one the image of the other

The tabled machine on a node and on its image under the node map
(`nmap b t`, `Kernel/NormalFormMap.lean`: the converse when `b`, in the
mirrored program when `t`). A goal `⟨lb, n, rb⟩` of the first run corresponds
to the goal `gmap b t` of it in the second: the image of the node, between
the boundaries exchanged when `b`. A representative corresponds to its
converse when `b` (`smap b`).

This file has the two maps, what links the two programs and their unfolding
races (`Link`), and what one set of tables has of another (`Fwd`): a table
for the image of every goal that has one, complete when it is, with the image
of each of its answers. Two runs correspond when each has this of the other
(`Tied`); the map is its own inverse, so every statement is needed in one
direction only.
-/
import RwLog.Rungs.Tabled.Reading
import RwLog.Kernel.NormalFormMap

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R}

/-! ## The maps -/

/-- The goal of the second run a goal of the first corresponds to. -/
def gmap (b t : Bool) (g : GoalOf R Rel) : GoalOf R Rel :=
  ⟨if b then g.rb else g.lb, nmap b t g.node, if b then g.lb else g.rb⟩

/-- The representative of the second run a representative of the first
corresponds to. -/
def smap (b : Bool) (r : R) : R := if b then Answer.swap r else r

omit [Answer R] [DecidableEq R] in
theorem gmap_gmap {b t : Bool} {g : GoalOf R Rel} (h : Normal g.node) :
    gmap b t (gmap b t g) = g := by
  cases b <;> simp [gmap, h.nmap_nmap]

theorem spans_flip : ∀ e : Rel, e.flip.spans = e.spans
  | .zero | .span _ | .call _ => rfl
  | .or a b | .and a b | .seq a b => by
    simp only [RelOf.flip, RelOf.spans, spans_flip a, spans_flip b]
  | .conv a => by simp only [RelOf.flip, RelOf.spans, spans_flip a]

theorem fo_nmap {e : Rel} (h : e.FO) (b t : Bool) : (nmap b t e).FO := by
  refine RelOf.FO.normB (fun s hs => h s ?_) b
  cases t
  · exact hs
  · rw [tf_true, spans_flip] at hs; exact hs

omit [Answer R] [DecidableEq R] in
theorem GoalOk.gmap {g : GoalOf R Rel} (h : GoalOk D g) (b t : Bool) : GoalOk D (gmap b t g) := by
  cases b
  · exact ⟨h.lb, h.rb, normal_nmap _ _ _, fo_nmap h.fo _ _⟩
  · exact ⟨h.rb, h.lb, normal_nmap _ _ _, fo_nmap h.fo _ _⟩

section laws

variable {M : Interp} (hL : D.Lawful M)
include hL

omit [DecidableEq R] in
theorem smap_smap (b : Bool) (r : R) : smap b (smap b r) = r := by
  cases b
  · rfl
  · exact hL.swap_swap r

omit [DecidableEq R] in
theorem smap_inj {b : Bool} {r r' : R} (h : smap b r = smap b r') : r = r' := by
  rw [← smap_smap hL b r, ← smap_smap hL b r', h]

omit [DecidableEq R] in
theorem covers_smap (b : Bool) (x y : R) : D.covers (smap b x) (smap b y) = D.covers x y := by
  cases b
  · rfl
  · exact hL.covers_swap x y

omit [DecidableEq R] in
theorem leftBound_swap (x : R) : D.leftBound (Answer.swap x) = D.rightBound x := by
  unfold Domain.leftBound; rw [hL.swap_swap]

omit [DecidableEq R] in
/-- The representative of the image of a span between the image
boundaries. -/
theorem spanBoth_smap {s : Span} (hs : s.firstOrder = true) {lb rb : Option R}
    (hl : IsBound D lb) (hr : IsBound D rb) (b : Bool) :
    spanBoth D (if b then rb else lb) (if b then s.swap else s) (if b then lb else rb) =
      (spanBoth D lb s rb).map (smap b) := by
  cases b
  · show spanBoth D lb s rb = (spanBoth D lb s rb).map (smap false)
    cases spanBoth D lb s rb <;> rfl
  · refine hL.denO_inj ?_
    show Domain.denO M (spanBoth D rb s.swap lb) = Domain.denO M ((spanBoth D lb s rb).map swap)
    rw [denO_spanBoth hL (Span.firstOrder_swap s ▸ hs), Domain.denO_map_swap,
      denO_spanBoth hL hs, wrapAt_inv hL hl hr, swap_den, at_inv]

end laws

/-! ## The link between the two runs -/

/-- What links the first program and its unfolding race to the second: the
body a call reads in the second is the image of the body it reads in the
first, and the race of the second says of the image of a goal what the race
of the first says of the goal. -/
structure Link (D : Domain R) (P P' : Program) (b t : Bool)
    (U : GOracle R Rel (Ans D P) Cost) (U' : GOracle R Rel (Ans D P') Cost) : Prop where
  body : ∀ e, Normal e → Charged.bodyOf P' (nmap b t e) = (Charged.bodyOf P e).map (nmap b t)
  verdict : ∀ d g, GoalOk D g → (U' d (gmap b t g)).val.1 = (U d g).val.1
  ask : ∀ d g, GoalOk D g → ∀ a ∈ (U d g).val.2,
    ∃ a' ∈ (U' d (gmap b t g)).val.2, a'.span = smap b a.span

/-- The two programs and their races, each linked to the other, with what
the proofs about either need. -/
structure Twin (D : Domain R) (P P' : Program) (b t : Bool)
    (U : GOracle R Rel (Ans D P) Cost) (U' : GOracle R Rel (Ans D P') Cost) : Prop where
  law : D.Lawful P.sorts.interp
  law' : D.Lawful P'.sorts.interp
  fo : ProgFO P
  fo' : ProgFO P'
  uok : UOk D P U
  uok' : UOk D P' U'
  link : Link D P P' b t U U'
  link' : Link D P' P b t U' U

omit [DecidableEq R] in
theorem Twin.symm {P P' : Program} {b t : Bool} {U : GOracle R Rel (Ans D P) Cost}
    {U' : GOracle R Rel (Ans D P') Cost} (h : Twin D P P' b t U U') : Twin D P' P b t U' U :=
  ⟨h.law', h.law, h.fo', h.fo, h.uok', h.uok, h.link', h.link⟩

variable {P P' : Program}

/-- What the second tables have of the first: a table for the image of every
goal that has one, complete when it is, with the image of each answer. -/
structure Fwd (b t : Bool) (ts : List (TableOf R Rel (Ans D P)))
    (ts' : List (TableOf R Rel (Ans D P'))) : Prop where
  has : ∀ g i, idx ts g = some i → ∃ j, idx ts' (gmap b t g) = some j
  done : ∀ g, isDone ts g = true → isDone ts' (gmap b t g) = true
  ans : ∀ g, ∀ a ∈ ansOf ts g, ∃ a' ∈ ansOf ts' (gmap b t g), a'.span = smap b a.span

/-- The tables of the two runs correspond. -/
structure Tied (b t : Bool) (ts : List (TableOf R Rel (Ans D P)))
    (ts' : List (TableOf R Rel (Ans D P'))) : Prop where
  inv : Inv D P ts
  inv' : Inv D P' ts'
  nodup : GoalsNodup ts
  nodup' : GoalsNodup ts'
  fwd : Fwd b t ts ts'
  bwd : Fwd b t ts' ts

theorem Tied.symm {b t : Bool} {ts : List (TableOf R Rel (Ans D P))}
    {ts' : List (TableOf R Rel (Ans D P'))} (h : Tied b t ts ts') : Tied b t ts' ts :=
  ⟨h.inv', h.inv, h.nodup', h.nodup, h.bwd, h.fwd⟩

section tied

variable {b t : Bool} {U : GOracle R Rel (Ans D P) Cost} {U' : GOracle R Rel (Ans D P') Cost}
  {ts : List (TableOf R Rel (Ans D P))} {ts' : List (TableOf R Rel (Ans D P'))}
  (hW : Twin D P P' b t U U') (hT : Tied b t ts ts')
include hW hT

/-- An answer the second tables have for the image of a goal is the image of
an answer of the goal. -/
theorem ans_back {g : GoalOf R Rel} (hg : Normal g.node) {a' : Ans D P'}
    (ha : a' ∈ ansOf ts' (gmap b t g)) : ∃ a ∈ ansOf ts g, a'.span = smap b a.span := by
  obtain ⟨a, ha, e⟩ := hT.bwd.ans _ a' ha
  rw [gmap_gmap hg] at ha
  exact ⟨a, ha, by rw [e, smap_smap hW.law']⟩

omit hW in
theorem done_iff {g : GoalOf R Rel} (hg : Normal g.node) :
    isDone ts' (gmap b t g) = isDone ts g := by
  rw [Bool.eq_iff_iff]
  refine ⟨fun h => ?_, hT.fwd.done g⟩
  have := hT.bwd.done _ h
  rwa [gmap_gmap hg] at this

omit hW in
theorem idx_back {g : GoalOf R Rel} (hg : Normal g.node) {j : Nat}
    (h : idx ts' (gmap b t g) = some j) : ∃ i, idx ts g = some i := by
  have := hT.bwd.has _ j h
  rwa [gmap_gmap hg] at this

/-- The maximal answers of a goal and of its image correspond. -/
theorem maxima_fwd {g : GoalOf R Rel} (hg : Normal g.node) {x : Ans D P}
    (hx : x ∈ (ansOf ts g).maximaBy (covB D P)) :
    ∃ x' ∈ (ansOf ts' (gmap b t g)).maximaBy (covB D P'), x'.span = smap b x.span := by
  obtain ⟨c', hc', e⟩ := hT.fwd.ans g x (List.mem_maximaBy hx)
  obtain ⟨z, hz, hzc⟩ := maxima_of_max hW.law' hc' fun y' hy' hyc => by
    obtain ⟨y, hy, ey⟩ := ans_back hW hT hg hy'
    unfold covB at hyc ⊢
    rw [e, ey, covers_smap hW.law] at hyc ⊢
    exact maxima_max hx hy hyc
  exact ⟨z, hz, hzc.trans e⟩

end tied

end Tabled

end RwLog
