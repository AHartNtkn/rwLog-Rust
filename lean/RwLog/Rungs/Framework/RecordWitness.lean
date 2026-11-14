/-
# The record of wins: the admission rule has inhabitants

`Trusted/Cost.lean` admits a rung by `Admits`, over the record of the wins of
the rungs below it, and `Ladder` is a chain of such admissions. This file
shows that the statement can be met: a ladder of two rungs above a base, the
second admitted for an exponential gain over a record that holds the
polynomial win of the first.

The three engines are toys, made for this purpose only. None of them is a
machine for the language: they are not complete, and correctness is no part
of `Admits` (it is `Keeps`, `Trusted/Properties.lean`). What is shown is that
the clauses of `Admits` can hold together, with a record that is empty and
with one that is not.

`Admits` is at a kernel rung, and the rung here is a toy too: `sized` is the
domain of sorts where reading a span of the program is charged its size and
nothing else is charged. A span that is read has a representative
(`reads_of_mem`), and the reader emits that.

* `silent` never answers.
* `reader waste` reads its root node as a span. If the root is a span node it
  and the span is read, it emits the answer of its representative in its
  first step, after spending `waste t` further ticks, where `t` is what
  reading the span cost; otherwise it emits nothing. `slow` wastes `2 ^ (t + 1)` and `quick` wastes nothing.

The class is the queries that are one ground pair written out
(`RelOf.ofPairs [(a, c)]`) in the empty program. A member is its own targets
written out, so in a context it costs exactly its residue.

* `slow_admits`: `slow` is admitted above `silent`, over the empty record.
  Every bound on the old machine holds because `silent` never covers a pair.
* `quick_admits`: `quick` is admitted above `slow` by an exponential gain in
  time, over the record `[slowWin]`. The lower bound on `slow` in every
  context is real: whenever the normal form of a context around a pair is one
  span, that span has the size of the pair's (`norm_fill_pair`), so `slow`
  has wasted `2 ^ size` before it answers. `quick_keeps` is the clause this
  file is for: `quick` meets the bound `slow` was admitted with.
* `ladder`: the two admissions as a `Ladder`, with both wins on its record.

The facts about normal forms used on the way: when the normal form of a
union is one span, each side is that span or nothing (`normB_or_span`); the
normal form of a meet or a sequence is never one span (`normB_and_ne`,
`normB_seq_ne`); and the mirror image of an expression whose normal form is
one span has that span swapped as its normal form (`normB_dual`).
-/
import RwLog.Rungs.Framework.Admission
import RwLog.Rungs.Framework.Direction
import RwLog.Kernel.NormalFormStable
import RwLog.Rungs.Framework.Rules
import RwLog.Sorts.Dom

namespace RwLog
namespace Witness

/-- The engine that never answers and never stops. -/
def silent : Engine where
  State _ _ _ := Unit
  init _ := pure ()
  step _ := pure (.emit [] ())

/-- The engine that reads its root node as a span: if the root is a span node
it emits the answer of that span in its first step, after spending `waste t`
further ticks, where `t` is what reading the span cost. It never stops. -/
def reader (waste : Nat → Nat) : Engine where
  State _ N _ := Option N
  init n := pure (some n)
  step {S N A _} _ st :=
    match st with
    | none => pure (.emit [] none)
    | some n => do
      let r ← Kernel.metered (S := S) (DerivationKernel.leaf (S := S) (N := N) (A := A) none n none)
      match r.1 with
      | some a => do
        Kernel.tick (S := S) (waste r.2)
        pure (.emit [a] none)
      | none => pure (.emit [] none)

/-- The kernel rung the witnesses are read at: the domain of sorts, where
reading a span of the program is charged its size and no other operation is
charged. Like the engines it is a toy, made for this purpose only: its
charges are not derived on any machine. -/
@[reducible] def sized : KernelRung where
  Rep := Sorts.Rep
  dom := Sorts.dom
  kernel S := Kernel.ofOps (fun s => Charged.op ((Sorts.dom S).rep s) s.size s.size)
    (fun x y => pure ((Sorts.dom S).compose x y)) (fun x y => pure ((Sorts.dom S).meet x y))
    (fun xs => pure ((Sorts.dom S).composable xs)) (fun a s => pure ((Sorts.dom S).covers a s))
    (fun x y => pure (decide (x = y))) (fun s => pure ((Sorts.dom S).rightBound s))
    (fun s => pure ((Sorts.dom S).leftBound s))
  refines _ :=
    { monad := rfl, tick := rfl, race := fun _ _ _ => rfl, metered := fun _ _ => rfl, swap := rfl,
      rep := fun _ => rfl, compose := fun _ _ => rfl, meet := fun _ _ => rfl,
      composable := fun _ => rfl, covers := fun _ _ => rfl, eq := fun _ _ => rfl,
      rightBound := fun _ => rfl, leftBound := fun _ => rfl }
  lawful _ hS := Sorts.dom_lawful hS

/-- The reader as a machine with its cost. -/
abbrev rd (w : Nat → Nat) : CostedRuntime := (reader w).costed sized

/-- The derivation kernel the reader runs at. -/
abbrev dk (P : Program) :=
  DerivationKernel.over (sized.dom P.sorts) (sized.kernel P.sorts) (sized.refines P.sorts) P

variable (w : Nat → Nat)

theorem reader_start (P : Program) (q : Rel) :
    (rd w).start P q = ⟨P, q.norm, some q.norm⟩ := rfl

theorem reader_init_ticks (P : Program) (q : Rel) :
    ((rd w).init P q).ticks = (P.size + q.size) ^ 2 := rfl

theorem reader_step_none (P : Program) (root : Rel) :
    ((rd w).step ⟨P, root, none⟩) = pure (.emit [] ⟨P, root, none⟩) := rfl

/-- What a span that is read relates, and that it is first-order. -/
theorem rep_den {S : Sorts} {s : Span} {r : Sorts.Rep S} (h : (Sorts.dom S).rep s = some r) :
    r.1.rel S = s.denAt S.interp ∧ s.firstOrder = true := by
  rw [Sorts.dom_rep] at h
  split at h
  · exact ⟨Sorts.Rep.mk?_some h, ‹_›⟩
  · cases h

/-- A first-order span that relates a pair is read, when the sorts are well
formed. -/
theorem reads_of_mem {S : Sorts} (hS : S.WellFormed) {s : Span} (hfo : s.firstOrder = true)
    {x : GTerm × GTerm} (hx : x ∈ s.denAt S.interp) : ∃ r, (Sorts.dom S).rep s = some r := by
  cases hr : (Sorts.dom S).rep s with
  | some r => exact ⟨r, rfl⟩
  | none =>
    rw [(Sorts.dom_lawful hS).rep_none s hfo hr] at hx
    exact absurd hx (Set.notMem_empty x)

/-- The converse of a span that is read is read. -/
theorem reads_swap {S : Sorts} {s : Span} {r : Sorts.Rep S} (h : (Sorts.dom S).rep s = some r) :
    ∃ r', (Sorts.dom S).rep s.swap = some r' := by
  obtain ⟨hden, hfo⟩ := rep_den h
  obtain ⟨p, hp⟩ := (Sorts.dom_lawful r.2.1).live r
  have hp' : p ∈ s.denAt S.interp := hden ▸ hp
  exact reads_of_mem r.2.1 (by rw [Span.firstOrder_swap]; exact hfo)
    (x := (p.2, p.1)) (Span.mem_denAt_swap.2 hp')

theorem leaf_span {P : Program} {s : Span} {r : Sorts.Rep P.sorts}
    (h : (Sorts.dom P.sorts).rep s = some r) :
    ∃ hv, (@DerivationKernel.leaf _ _ _ _ (dk P) none (.span s) none).val =
      some ⟨⟨none, .span s, none⟩, r, hv⟩ := by
  have hb : IsBound (Sorts.dom P.sorts) none := fun _ e => by cases e
  have hsb : spanBoth (Sorts.dom P.sorts) none s none = some r := by
    unfold spanBoth; rw [h]; rfl
  exact ⟨Valid.leaf hb hb hsb, (Ans.leaf_val _ _).2 ⟨s, rfl, hb, hb, hsb, rfl⟩⟩

theorem leaf_span_none {P : Program} {s : Span} (h : (Sorts.dom P.sorts).rep s = none) :
    (@DerivationKernel.leaf _ _ _ _ (dk P) none (.span s) none).val = none := by
  cases hl : (@DerivationKernel.leaf _ _ _ _ (dk P) none (.span s) none).val with
  | none => rfl
  | some c =>
    obtain ⟨s', e, -, -, hs, -⟩ := (Ans.leaf_val _ _).1 hl
    cases e
    have h' : (sized.dom P.sorts).rep s = none := h
    unfold spanBoth at hs
    rw [h'] at hs
    cases hs

theorem leaf_not_span (P : Program) {n : Rel} (h : ∀ s, n ≠ .span s) :
    (@DerivationKernel.leaf _ _ _ _ (dk P) none n none).val = none := by
  cases n with
  | span s => exact absurd rfl (h s)
  | _ => rfl

/-- Reading a span node costs two ticks and the size of the span. -/
theorem leaf_ticks (P : Program) (s : Span) :
    (@DerivationKernel.leaf _ _ _ _ (dk P) none (.span s) none).ticks = 2 + s.size := by
  show (Ans.leaf _ P _ _ none (.span s) none).ticks = _
  have hb : IsBound (Sorts.dom P.sorts) none := fun _ e => by cases e
  unfold Ans.leaf
  simp only [Cost.bind_ticks, Cost.tick_ticks]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hb, hb⟩)]
  show 2 + (Ans.spanBothK _ none s none).ticks = _
  unfold Ans.spanBothK
  simp only [Cost.bind_ticks]
  show 2 + (s.size + _) = _
  split <;> rfl

theorem reader_step_span_val {P : Program} {s : Span} {r : Sorts.Rep P.sorts}
    (h : (Sorts.dom P.sorts).rep s = some r) :
    ((rd w).step ⟨P, .span s, some (.span s)⟩).val =
      .emit [⟨P.sorts, r⟩] ⟨P, .span s, none⟩ := by
  obtain ⟨hv, hl⟩ := leaf_span h
  simp [rd, Engine.costed, Engine.costedAt, reader, Engine.report, Kernel.metered, hl, Ans.rootSpan]

theorem reader_step_span_none {P : Program} {s : Span}
    (h : (Sorts.dom P.sorts).rep s = none) :
    ((rd w).step ⟨P, .span s, some (.span s)⟩).val = .emit [] ⟨P, .span s, none⟩ := by
  simp [rd, Engine.costed, Engine.costedAt, reader, Engine.report, Kernel.metered, leaf_span_none h]

theorem reader_step_other_val (P : Program) {n : Rel} (h : ∀ s, n ≠ .span s) :
    ((rd w).step ⟨P, n, some n⟩).val = .emit [] ⟨P, n, none⟩ := by
  simp [rd, Engine.costed, Engine.costedAt, reader, Engine.report, Kernel.metered, leaf_not_span P h]

theorem reader_step_span_ticks {P : Program} {s : Span} {r : Sorts.Rep P.sorts}
    (h : (Sorts.dom P.sorts).rep s = some r) :
    ((rd w).step ⟨P, .span s, some (.span s)⟩).ticks =
      2 + s.size + w (2 + s.size) + 1 := by
  obtain ⟨hv, hl⟩ := leaf_span h
  have ht := leaf_ticks P s
  simp [rd, Engine.costed, Engine.costedAt, reader, Engine.report, Kernel.metered, Cost.metered,
    Kernel.tick, hl, ht]
  omega


/-! ## Normal forms that are one span -/

theorem mkOr_eq_span {L : List Rel} {s : Span} (h : mkOr L = .span s) : L = [.span s] := by
  match L, h with
  | [], h => simp [mkOr] at h
  | [e], h => simpa [mkOr] using h
  | e :: e' :: es, h => simp [mkOr] at h

theorem mkOr_eq_zero {L : List Rel} (hL : ∀ x ∈ L, x ≠ .zero) (h : mkOr L = .zero) : L = [] := by
  match L, hL, h with
  | [], _, _ => rfl
  | [e], hL, h => exact absurd (by simpa [mkOr] using h) (hL e (List.mem_singleton_self e))
  | e :: e' :: es, _, h => simp [mkOr] at h

theorem eq_of_branches {s : Span} : ∀ {e : Rel}, Normal e →
    (∀ z ∈ orBranches e, z = .zero ∨ z = .span s) → e = .zero ∨ e = .span s
  | .or a b, h, hz => by
    obtain ⟨ha, ha0, _, hnb, hb0, hlt⟩ := normal_or.1 h
    rw [orBranches, orBranches_notOr ha] at hz
    have ha' : a = .span s := (hz a (by simp)).resolve_left ha0
    have hb' : b = .span s :=
      (eq_of_branches hnb fun z hz' => hz z (by simp [hz'])).resolve_left hb0
    subst ha' hb'
    exact absurd rfl (hlt _ (by simp [orBranches])).2
  | .zero, _, _ => Or.inl rfl
  | .span _, _, hz | .seq _ _, _, hz | .and _ _, _, hz | .conv _, _, hz | .call _, _, hz =>
    hz _ (by simp [orBranches])

theorem eq_zero_of_branches : ∀ {e : Rel}, Normal e → (∀ z ∈ orBranches e, z = .zero) →
    e = .zero
  | .or a b, h, hz => by
    obtain ⟨ha, ha0, _⟩ := normal_or.1 h
    rw [orBranches, orBranches_notOr ha] at hz
    exact absurd (hz a (by simp)) ha0
  | .zero, _, _ => rfl
  | .span _, _, hz | .seq _ _, _, hz | .and _ _, _, hz | .conv _, _, hz | .call _, _, hz =>
    hz _ (by simp [orBranches])

theorem normB_or (b : Bool) (x y : Rel) : normB b (.or x y) =
    mkOr (sortedBranches (orBranches (normB b x) ++ orBranches (normB b y))) := by
  cases b <;> rfl

theorem normB_conv (b : Bool) (x : Rel) : normB b (.conv x) = normB (!b) x := by
  cases b <;> rfl

/-- The normal form of a union is one span only when each side is that span
or nothing. -/
theorem normB_or_span {b : Bool} {x y : Rel} {s : Span} (h : normB b (.or x y) = .span s) :
    (normB b x = .zero ∨ normB b x = .span s) ∧ (normB b y = .zero ∨ normB b y = .span s) ∧
      (normB b x = .span s ∨ normB b y = .span s) := by
  rw [normB_or] at h
  have hL := mkOr_eq_span h
  have hz : ∀ z ∈ orBranches (normB b x) ++ orBranches (normB b y),
      z = .zero ∨ z = .span s := by
    intro z hz
    by_cases h0 : z = .zero
    · exact Or.inl h0
    · have hm := mem_sortedBranches.2 ⟨hz, h0⟩
      rw [hL] at hm
      exact Or.inr (List.mem_singleton.1 hm)
  have hx := eq_of_branches (normal_normB b x) fun z h => hz z (List.mem_append_left _ h)
  have hy := eq_of_branches (normal_normB b y) fun z h => hz z (List.mem_append_right _ h)
  refine ⟨hx, hy, ?_⟩
  have hs : (.span s : Rel) ∈ sortedBranches (orBranches (normB b x) ++ orBranches (normB b y)) := by
    rw [hL]; exact List.mem_singleton_self _
  have hs := (mem_sortedBranches.1 hs).1
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · rw [hx, hy] at hs; simp [orBranches] at hs
    · exact Or.inr hy
  · exact Or.inl hx

theorem normB_or_zero {b : Bool} {x y : Rel} (h : normB b (.or x y) = .zero) :
    normB b x = .zero ∧ normB b y = .zero := by
  rw [normB_or] at h
  have hL := mkOr_eq_zero (fun z hz => (mem_sortedBranches.1 hz).2) h
  have hz : ∀ z ∈ orBranches (normB b x) ++ orBranches (normB b y), z = .zero := by
    intro z hz
    by_contra h0
    have hm := mem_sortedBranches.2 ⟨hz, h0⟩
    rw [hL] at hm
    exact absurd hm List.not_mem_nil
  exact ⟨eq_zero_of_branches (normal_normB b x) fun z h => hz z (List.mem_append_left _ h),
    eq_zero_of_branches (normal_normB b y) fun z h => hz z (List.mem_append_right _ h)⟩

theorem normB_or_zero_of {b : Bool} {x y : Rel} (hx : normB b x = .zero) (hy : normB b y = .zero) :
    normB b (.or x y) = .zero := by
  rw [normB_or, hx, hy]; simp [orBranches, sortedBranches, mkOr]

theorem normB_or_of {b : Bool} {x y : Rel} {s : Span}
    (hx : normB b x = .zero ∨ normB b x = .span s) (hy : normB b y = .zero ∨ normB b y = .span s)
    (hxy : normB b x = .span s ∨ normB b y = .span s) : normB b (.or x y) = .span s := by
  have h1 : sortedBranches [(.span s : Rel)] = [.span s] :=
    sortedBranches_of_strict (List.pairwise_singleton _ _) (by simp)
  rw [normB_or, sortedBranches_eq (ys := [.span s]) ?_, h1]; rfl
  intro z hz
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rcases hxy with h | h
    · rw [hx] at h; cases h
    · rw [hy] at h; cases h
  all_goals rw [hx, hy]; simp [orBranches, hz]

theorem mkAnd_two : ∀ {L : List Rel}, 2 ≤ L.length → ∃ a c, mkAnd L = .and a c
  | a :: c :: r, _ => ⟨a, mkAnd (c :: r), rfl⟩
  | [], h | [_], h => by simp at h

theorem mkSeq_two : ∀ {L : List Rel}, 2 ≤ L.length → ∃ a c, mkSeq L = .seq a c
  | a :: c :: r, _ => ⟨a, mkSeq (c :: r), rfl⟩
  | [], h | [_], h => by simp at h

/-- The normal form of a meet is a meet. -/
theorem normB_and (b : Bool) (x y : Rel) : ∃ a c, normB b (.and x y) = .and a c := by
  have e : normB b (.and x y) =
      mkAnd (sortedParts (andParts (normB b x) ++ andParts (normB b y))) := by cases b <;> rfl
  rw [e]
  apply mkAnd_two
  rw [(sortedParts_perm _).length_eq, List.length_append]
  have := List.length_pos_of_ne_nil (andParts_ne_nil (normB b x))
  have := List.length_pos_of_ne_nil (andParts_ne_nil (normB b y))
  omega

/-- The normal form of a sequence is a chain. -/
theorem normB_seq (b : Bool) (x y : Rel) : ∃ a c, normB b (.seq x y) = .seq a c := by
  cases b
  · have e : normB false (.seq x y) = mkSeq (seqParts (normB false x) ++ seqParts (normB false y)) :=
      rfl
    rw [e]
    apply mkSeq_two
    rw [List.length_append]
    have := List.length_pos_of_ne_nil (seqParts_ne_nil (normB false x))
    have := List.length_pos_of_ne_nil (seqParts_ne_nil (normB false y))
    omega
  · have e : normB true (.seq x y) = mkSeq (seqParts (normB true y) ++ seqParts (normB true x)) :=
      rfl
    rw [e]
    apply mkSeq_two
    rw [List.length_append]
    have := List.length_pos_of_ne_nil (seqParts_ne_nil (normB true x))
    have := List.length_pos_of_ne_nil (seqParts_ne_nil (normB true y))
    omega

theorem normB_and_ne (b : Bool) (x y : Rel) :
    normB b (.and x y) ≠ .zero ∧ ∀ s, normB b (.and x y) ≠ .span s := by
  obtain ⟨a, c, h⟩ := normB_and b x y
  rw [h]
  exact ⟨fun h' => (by cases h'), fun s h' => (by cases h')⟩

theorem normB_seq_ne (b : Bool) (x y : Rel) :
    normB b (.seq x y) ≠ .zero ∧ ∀ s, normB b (.seq x y) ≠ .span s := by
  obtain ⟨a, c, h⟩ := normB_seq b x y
  rw [h]
  exact ⟨fun h' => (by cases h'), fun s h' => (by cases h')⟩

/-- An expression whose normal form is one span has a mirror image whose
normal form is that span swapped. -/
theorem normB_dual : ∀ (e : Rel) (b : Bool),
    (normB b e = .zero → normB b e.dual = .zero) ∧
      ∀ s, normB b e = .span s → normB b e.dual = .span s.swap
  | .zero, b => ⟨fun _ => by cases b <;> rfl, fun s h => by cases b <;> simp [normB] at h⟩
  | .span t, b => by
    cases b
    · exact ⟨fun h => by simp [normB] at h, fun s h => by
        simp only [normB, RelOf.span.injEq] at h; subst h; rfl⟩
    · exact ⟨fun h => by simp [normB] at h, fun s h => by
        simp only [normB, RelOf.span.injEq] at h; subst h; rfl⟩
  | .or x y, b => by
    obtain ⟨hx0, hxs⟩ := normB_dual x b
    obtain ⟨hy0, hys⟩ := normB_dual y b
    refine ⟨fun h => ?_, fun s h => ?_⟩
    · obtain ⟨h1, h2⟩ := normB_or_zero h
      exact normB_or_zero_of (hx0 h1) (hy0 h2)
    · obtain ⟨h1, h2, h3⟩ := normB_or_span h
      exact normB_or_of (h1.imp hx0 (hxs s)) (h2.imp hy0 (hys s)) (h3.imp (hxs s) (hys s))
  | .and x y, b =>
    ⟨fun h => absurd h (normB_and_ne b x y).1, fun s h => absurd h ((normB_and_ne b x y).2 s)⟩
  | .seq x y, b =>
    ⟨fun h => absurd h (normB_seq_ne b x y).1, fun s h => absurd h ((normB_seq_ne b x y).2 s)⟩
  | .conv x, b => by
    have := normB_dual x (!b)
    rw [normB_conv]
    exact this
  | .call n, b => ⟨fun h => by cases b <;> simp [normB] at h,
      fun s h => by cases b <;> simp [normB] at h⟩

/-- Around an expression whose normal form is a span of size `n` either way
round, the normal form of no context is nothing, and if it is one span that
span has size `n`. -/
theorem normB_fill {r : Rel} {n : Nat} (hr0 : ∀ b, normB b r ≠ .zero)
    (hrs : ∀ b s, normB b r = .span s → s.size = n) : ∀ (K : Ctx) (b : Bool),
    normB b (K.fill r) ≠ .zero ∧ ∀ s, normB b (K.fill r) = .span s → s.size = n
  | .hole, b => ⟨hr0 b, hrs b⟩
  | .orL K x, b =>
    ⟨fun h => (normB_fill hr0 hrs K b).1 (normB_or_zero h).1, fun s h =>
      (normB_or_span h).1.elim (fun h0 => absurd h0 (normB_fill hr0 hrs K b).1)
        ((normB_fill hr0 hrs K b).2 s)⟩
  | .orR x K, b =>
    ⟨fun h => (normB_fill hr0 hrs K b).1 (normB_or_zero h).2, fun s h =>
      (normB_or_span h).2.1.elim (fun h0 => absurd h0 (normB_fill hr0 hrs K b).1)
        ((normB_fill hr0 hrs K b).2 s)⟩
  | .andL K x, b =>
    ⟨(normB_and_ne b (K.fill r) x).1, fun s h => absurd h ((normB_and_ne b (K.fill r) x).2 s)⟩
  | .andR x K, b =>
    ⟨(normB_and_ne b x (K.fill r)).1, fun s h => absurd h ((normB_and_ne b x (K.fill r)).2 s)⟩
  | .seqL K x, b =>
    ⟨(normB_seq_ne b (K.fill r) x).1, fun s h => absurd h ((normB_seq_ne b (K.fill r) x).2 s)⟩
  | .seqR x K, b =>
    ⟨(normB_seq_ne b x (K.fill r)).1, fun s h => absurd h ((normB_seq_ne b x (K.fill r)).2 s)⟩
  | .conv K, b => by
    have := normB_fill hr0 hrs K (!b)
    rwa [← normB_conv] at this

/-- One pair written out: its normal form is its span, and the converse of
its normal form is that span swapped. -/
theorem normB_pair (b : Bool) (a c : GTerm) :
    normB b (.ofPairs [(a, c)]) =
      .span (if b then (⟨a.toPat, c.toPat, []⟩ : Span).swap else ⟨a.toPat, c.toPat, []⟩) := by
  cases b
  · exact normB_or_of (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  · exact normB_or_of (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)

theorem norm_pair (a c : GTerm) :
    (RelOf.ofPairs [(a, c)]).norm = .span ⟨a.toPat, c.toPat, []⟩ := normB_pair false a c

theorem size_pair (a c : GTerm) :
    (RelOf.ofPairs [(a, c)]).size = 2 + (⟨a.toPat, c.toPat, []⟩ : Span).size + 1 := by
  simp only [RelOf.ofPairs, RelOf.size]; omega

/-- Around one pair written out, a normal form that is one span has the size
of the pair's span. -/
theorem norm_fill_pair (a c : GTerm) (K : Ctx) {s : Span}
    (h : (K.fill (.ofPairs [(a, c)])).norm = .span s) :
    s.size = (⟨a.toPat, c.toPat, []⟩ : Span).size := by
  refine (normB_fill (r := .ofPairs [(a, c)]) (fun b => ?_) (fun b s' h' => ?_) K false).2 s h
  · rw [normB_pair]; simp
  · rw [normB_pair, RelOf.span.injEq] at h'
    subst h'
    cases b
    · rfl
    · exact Span.size_swap _


/-! ## What the reader does -/

theorem rd_run_none (P : Program) (root : Rel) :
    ∀ n, (rd w).runtime.run ⟨P, root, none⟩ n = ([], none)
  | 0 => rfl
  | n + 1 => by
    rw [(rd w).runtime.run_succ_emit (s := ⟨P, root, none⟩) (as := []) (s' := ⟨P, root, none⟩) rfl,
      rd_run_none P root n]
    rfl

theorem rd_spent_none (P : Program) (root : Rel) : ∀ n, (rd w).spent ⟨P, root, none⟩ n = 0
  | 0 => rfl
  | n + 1 => by
    rw [(rd w).spent_succ_emit (s := ⟨P, root, none⟩) (as := []) (s' := ⟨P, root, none⟩) rfl,
      rd_spent_none P root n]
    rfl

theorem rd_start_span {P : Program} {q : Rel} {s : Span} (h : q.norm = .span s) :
    (rd w).start P q = ⟨P, .span s, some (.span s)⟩ := by
  rw [reader_start, h]

/-- On a query whose normal form is a span that is read, the reader has
emitted its representative after its first step, and nothing else ever. -/
theorem rd_run_span {P : Program} {q : Rel} {s : Span} {r : Sorts.Rep P.sorts}
    (h : q.norm = .span s) (hr : (Sorts.dom P.sorts).rep s = some r) (n : Nat) :
    (rd w).runtime.run ((rd w).start P q) (n + 1) = ([⟨P.sorts, r⟩], none) := by
  rw [rd_start_span w h, (rd w).runtime.run_succ_emit (s := ⟨P, .span s, some (.span s)⟩)
    (reader_step_span_val w hr), rd_run_none]
  rfl

/-- What the reader has paid by then. -/
theorem rd_paid_span {P : Program} {q : Rel} {s : Span} {r : Sorts.Rep P.sorts}
    (h : q.norm = .span s) (hr : (Sorts.dom P.sorts).rep s = some r) (n : Nat) :
    (rd w).paid P q (n + 1) = (P.size + q.size) ^ 2 + (2 + s.size + w (2 + s.size) + 1) := by
  unfold CostedRuntime.paid
  rw [rd_start_span w h, (rd w).spent_succ_emit (reader_step_span_val w hr), rd_spent_none,
    reader_step_span_ticks w hr]
  rfl

/-- On any other query the reader emits nothing. -/
theorem rd_run_other {P : Program} {q : Rel}
    (h : ∀ s, q.norm = .span s → (Sorts.dom P.sorts).rep s = none) :
    ∀ n, (rd w).runtime.run ((rd w).start P q) n = ([], none)
  | 0 => rfl
  | n + 1 => by
    by_cases hq : ∃ s, q.norm = .span s
    · obtain ⟨s, hs⟩ := hq
      rw [rd_start_span w hs, (rd w).runtime.run_succ_emit (s := ⟨P, .span s, some (.span s)⟩)
        (reader_step_span_none w (h s hs)), rd_run_none]
      rfl
    · rw [reader_start, (rd w).runtime.run_succ_emit (s := ⟨P, q.norm, some q.norm⟩)
        (reader_step_other_val w P fun s hs => hq ⟨s, hs⟩), rd_run_none]
      rfl

/-- The normal form of the query is a span that is read, or the reader emits
nothing. -/
theorem rd_cases (P : Program) (q : Rel) :
    (∃ s r, q.norm = .span s ∧ (Sorts.dom P.sorts).rep s = some r) ∨
      ∀ n, (rd w).runtime.run ((rd w).start P q) n = ([], none) := by
  by_cases hq : ∃ s r, q.norm = .span s ∧ (Sorts.dom P.sorts).rep s = some r
  · exact .inl hq
  · refine .inr (rd_run_other w fun s hs => ?_)
    cases hr : (Sorts.dom P.sorts).rep s with
    | none => rfl
    | some r => exact absurd ⟨s, r, hs, hr⟩ hq

theorem rd_run_snd (P : Program) (q : Rel) (n : Nat) :
    ((rd w).runtime.run ((rd w).start P q) n).2 = none := by
  rcases rd_cases w P q with ⟨s, r, hs, hr⟩ | h
  · cases n with
    | zero => rfl
    | succ m => rw [rd_run_span w hs hr]
  · rw [h]

/-- The reader has covered a pair only when the normal form of the query is a
span that is read and relates it, and then it has taken a step. -/
theorem rd_covered {P : Program} {q : Rel} {M : Interp} {x : GTerm × GTerm} {n : Nat}
    (h : (rd w).Covered P q M x n) :
    ∃ s r m, q.norm = .span s ∧ (Sorts.dom P.sorts).rep s = some r ∧
      x ∈ s.denAt P.sorts.interp ∧ n = m + 1 := by
  obtain ⟨a, ha, hx⟩ := h
  replace ha : a ∈ ((rd w).runtime.run ((rd w).start P q) n).1 := ha
  rcases rd_cases w P q with ⟨s, r, hs, hr⟩ | h
  · cases n with
    | zero => exact absurd ha List.not_mem_nil
    | succ m =>
      rw [rd_run_span w hs hr] at ha
      obtain rfl := List.mem_singleton.1 ha
      exact ⟨s, r, m, hs, hr, (rep_den hr).1 ▸ hx, rfl⟩
  · rw [h] at ha
    exact absurd ha List.not_mem_nil

theorem rd_covers {P : Program} {q : Rel} {M : Interp} {x : GTerm × GTerm} {s : Span}
    {r : Sorts.Rep P.sorts} (h : q.norm = .span s) (hr : (Sorts.dom P.sorts).rep s = some r)
    (hx : x ∈ s.denAt P.sorts.interp) : (rd w).Covered P q M x 1 :=
  ⟨⟨P.sorts, r⟩, by
    show _ ∈ ((rd w).runtime.run ((rd w).start P q) 1).1
    rw [rd_run_span w h hr]; exact List.mem_singleton_self _, by
    show x ∈ r.1.rel P.sorts
    rw [(rep_den hr).1]; exact hx⟩

theorem rd_not_halts (P : Program) (q : Rel) (n : Nat) :
    ¬ (rd w).runtime.Halts ((rd w).start P q) n := by
  simp [Runtime.Halts, Runtime.final, rd_run_snd]

/-! ### With its answers swapped -/

theorem swapped_run (C : CostedRuntime) (init : Program → Rel → Cost C.State) :
    ∀ (n : Nat) (s : C.State), (C.swapped init).runtime.run s n =
      ((C.runtime.run s n).1.map Answer.swap, (C.runtime.run s n).2.map (List.map Answer.swap))
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done fin =>
      have hs' : (C.swapped init).runtime.step s = .done (fin.map Answer.swap) := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).runtime.run_succ_done hs',
        C.runtime.run_succ_done (show C.runtime.step s = .done fin from hs)]
      rfl
    | emit as s' =>
      have hs' : (C.swapped init).runtime.step s = .emit (as.map Answer.swap) s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).runtime.run_succ_emit hs',
        C.runtime.run_succ_emit (show C.runtime.step s = .emit as s' from hs),
        swapped_run C init n s']
      exact Prod.ext (List.map_append ..).symm rfl
    | progress k s' =>
      have hs' : (C.swapped init).runtime.step s = .progress k s' := by
        show (C.step s).val.swap = _; rw [hs]; rfl
      rw [(C.swapped init).runtime.run_succ_progress hs',
        C.runtime.run_succ_progress (show C.runtime.step s = .progress k s' from hs),
        swapped_run C init n s']

variable {init : Program → Rel → Cost (rd w).State} {P P' : Program} {q q' : Rel}

theorem rd_swapped_covered {M : Interp} {x : GTerm × GTerm} {n : Nat}
    (hi : (init P q).val = (rd w).start P' q') (h : ((rd w).swapped init).Covered P q M x n) :
    ∃ s r m, q'.norm = .span s ∧ (Sorts.dom P'.sorts).rep s = some r ∧
      x ∈ s.swap.denAt P'.sorts.interp ∧ n = m + 1 := by
  obtain ⟨a, ha, hx⟩ := h
  have ha' : a ∈ (((rd w).swapped init).runtime.run (init P q).val n).1 := ha
  rw [swapped_run, hi] at ha'
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha'
  obtain ⟨s, r, m, hs, hr, hx', hn⟩ := rd_covered w (M := M) (x := (x.2, x.1)) (n := n)
    ⟨a0, ha0, (Answer.den_swap M a0 ▸ hx : x ∈ (Answer.den M a0).inv)⟩
  exact ⟨s, r, m, hs, hr, Span.mem_denAt_swap.2 hx', hn⟩

theorem rd_swapped_covers {M : Interp} {x : GTerm × GTerm} {s : Span} {r : Sorts.Rep P'.sorts}
    (hi : (init P q).val = (rd w).start P' q') (h : q'.norm = .span s)
    (hr : (Sorts.dom P'.sorts).rep s = some r)
    (hx : x ∈ s.swap.denAt P'.sorts.interp) : ((rd w).swapped init).Covered P q M x 1 := by
  refine ⟨Answer.swap (⟨P'.sorts, r⟩ : (S : Sorts) × Sorts.Rep S), ?_, ?_⟩
  · have := swapped_run (rd w) init 1 (init P q).val
    rw [hi, rd_run_span w h hr] at this
    show _ ∈ (((rd w).swapped init).runtime.run (init P q).val 1).1
    rw [hi, this]
    exact List.mem_singleton_self _
  · have e := Answer.den_swap M (⟨P'.sorts, r⟩ : (S : Sorts) × Sorts.Rep S)
    have hm : x ∈ (Answer.den M (⟨P'.sorts, r⟩ : (S : Sorts) × Sorts.Rep S)).inv := by
      show (x.2, x.1) ∈ r.1.rel P'.sorts
      rw [(rep_den hr).1]; exact Span.mem_denAt_swap.1 hx
    exact e ▸ hm

theorem rd_swapped_not_halts (hi : (init P q).val = (rd w).start P' q') (n : Nat) :
    ¬ ((rd w).swapped init).runtime.Halts (((rd w).swapped init).start P q) n := by
  have h : (((rd w).swapped init).runtime.run (init P q).val n).2 = none := by
    rw [swapped_run, hi, rd_run_snd]; rfl
  show ¬ ((((rd w).swapped init).runtime.run (init P q).val n).2.isSome = true)
  rw [h]
  exact Bool.false_ne_true

/-! ## Simulations between machines that never stop -/

theorem simBy_of_covers {μ : Meter} {A B : CostedRuntime} {p : Nat → Nat → Nat}
    (hA : ∀ P q n, ¬ A.runtime.Halts (A.start P q) n)
    (h : ∀ P q n x, A.Covered P q P.sorts.interp x n →
      ∃ m, B.Covered P q P.sorts.interp x m ∧ μ B P q m ≤ p (μ A P q n) (P.size + q.size)) :
    SimulatesBy μ A B p :=
  fun P q _ n => ⟨fun x hx => h P q n x hx, fun hn => absurd hn (hA P q n)⟩

/-- The reader does not depend on the direction a query is written in: the
mirror image costs the same, and the converse is one node larger. -/
theorem rd_direction : DirectionFree (rd w) (DirBound.fn ⟨2, 1⟩) := by
  have hp : ∀ c n, c + 2 * n + 1 ≤ DirBound.fn ⟨2, 1⟩ c n := fun c n => by
    show c + 2 * n + 1 ≤ 2 * (c + n + 1) ^ 1
    rw [Nat.pow_one]; omega
  have sq : ∀ N : Nat, (N + 1) ^ 2 = N ^ 2 + 2 * N + 1 := fun N => by
    rw [Nat.pow_two, Nat.pow_two, Nat.add_mul, Nat.mul_add]; omega
  refine ⟨Simulates.mono ?_ hp, Simulates.mono ?_ hp, Simulates.mono ?_ hp, Simulates.mono ?_ hp⟩
  · refine simBy_of_covers (rd_not_halts w) fun P q n x hx => ?_
    obtain ⟨s, r, m, hs, hr, hx', rfl⟩ := rd_covered w hx
    obtain ⟨r', hr'⟩ := reads_swap hr
    have hd : q.dual.norm = .span s.swap := (normB_dual q false).2 s hs
    refine ⟨1, rd_swapped_covers w (init := fun P q => (rd w).init P.dual q.dual) (P' := P.dual)
      rfl hd hr' hx', ?_⟩
    show (rd w).mirror.paid P q 1 ≤ (rd w).paid P q (m + 1) + 2 * (P.size + q.size) + 1
    rw [CostedRuntime.mirror_paid, rd_paid_span w (P := P.dual) hd hr' 0, rd_paid_span w hs hr m,
      ProgramOf.size_dual, RelOf.size_dual, Span.size_swap]
    omega
  · refine simBy_of_covers
      (fun P q n => rd_swapped_not_halts w (init := fun P q => (rd w).init P.dual q.dual) rfl n)
      fun P q n x hx => ?_
    obtain ⟨s, r, m, hs, hr, hx', rfl⟩ :=
      rd_swapped_covered w (init := fun P q => (rd w).init P.dual q.dual) (P' := P.dual) rfl hx
    obtain ⟨r', hr'⟩ := reads_swap hr
    have hd : q.norm = .span s.swap := by
      have := (normB_dual q.dual false).2 s hs
      rwa [RelOf.dual_dual] at this
    refine ⟨1, rd_covers w (P := P) hd hr' hx', ?_⟩
    show (rd w).paid P q 1 ≤ (rd w).mirror.paid P q (m + 1) + 2 * (P.size + q.size) + 1
    rw [CostedRuntime.mirror_paid, rd_paid_span w (P := P) hd hr' 0,
      rd_paid_span w (P := P.dual) hs hr m, ProgramOf.size_dual, RelOf.size_dual, Span.size_swap]
    omega
  · refine simBy_of_covers (rd_not_halts w) fun P q n x hx => ?_
    obtain ⟨s, r, m, hs, hr, hx', rfl⟩ := rd_covered w hx
    obtain ⟨r', hr'⟩ := reads_swap hr
    have hc : (RelOf.conv q).norm = .span s.swap := by
      have := normB_normB true false q
      rw [show normB false q = .span s from hs] at this
      exact this.symm
    refine ⟨1, rd_swapped_covers w (init := fun P q => (rd w).init P (.conv q)) rfl hc hr' hx', ?_⟩
    show (rd w).conv.paid P q 1 ≤ (rd w).paid P q (m + 1) + 2 * (P.size + q.size) + 1
    rw [CostedRuntime.conv_paid, rd_paid_span w hc hr' 0, rd_paid_span w hs hr m, Span.size_swap]
    have := sq (P.size + q.size)
    have e : P.size + (RelOf.conv q).size = P.size + q.size + 1 := by
      simp only [RelOf.size]; omega
    rw [e]
    omega
  · refine simBy_of_covers
      (fun P q n => rd_swapped_not_halts w (init := fun P q => (rd w).init P (.conv q)) rfl n)
      fun P q n x hx => ?_
    obtain ⟨s, r, m, hs, hr, hx', rfl⟩ :=
      rd_swapped_covered w (init := fun P q => (rd w).init P (.conv q)) rfl hx
    obtain ⟨r', hr'⟩ := reads_swap hr
    have hc : q.norm = .span s.swap := by
      have := normB_normB true true q
      rw [show normB true q = .span s from hs] at this
      exact this.symm
    refine ⟨1, rd_covers w hc hr' hx', ?_⟩
    show (rd w).paid P q 1 ≤ (rd w).conv.paid P q (m + 1) + 2 * (P.size + q.size) + 1
    rw [CostedRuntime.conv_paid, rd_paid_span w hc hr' 0, rd_paid_span w hs hr m, Span.size_swap]
    have := sq (P.size + q.size)
    have e : P.size + (RelOf.conv q).size = P.size + q.size + 1 := by
      simp only [RelOf.size]; omega
    rw [e]
    omega

/-! ## What the silent engine does -/

theorem silent_run : ∀ (n : Nat) (s : (silent.costed sized).State),
    (silent.costed sized).runtime.run s n = ([], none)
  | 0, _ => rfl
  | n + 1, s => by
    rw [(silent.costed sized).runtime.run_succ_emit (s := s) (as := []) (s' := s) rfl, silent_run n s]
    rfl

theorem silent_not_covered {P : Program} {q : Rel} {M : Interp} {x : GTerm × GTerm} {n : Nat} :
    ¬ (silent.costed sized).Covered P q M x n := by
  rintro ⟨a, ha, _⟩
  replace ha : a ∈ ((silent.costed sized).runtime.run ((silent.costed sized).start P q) n).1 := ha
  rw [silent_run] at ha
  exact absurd ha List.not_mem_nil

theorem silent_not_halts (P : Program) (q : Rel) (n : Nat) :
    ¬ (silent.costed sized).runtime.Halts ((silent.costed sized).start P q) n := by
  simp [Runtime.Halts, Runtime.final, silent_run]

/-- Every machine simulates the silent one, in every resource and within any
bound. -/
theorem silent_simBy (μ : Meter) (B : CostedRuntime) (p : Nat → Nat → Nat) :
    SimulatesBy μ (silent.costed sized) B p :=
  simBy_of_covers silent_not_halts fun _ _ _ _ hx => absurd hx silent_not_covered


/-! ## The class: one pair written out, in the empty program -/

/-- The pair of a query that is one ground pair written out. -/
def pairTgt : Rel → List (GTerm × GTerm)
  | .or (.span s) .zero => [(s.l.bind fun _ => .sym "z", s.r.bind fun _ => .sym "z")]
  | _ => []

/-- The queries that are one ground pair written out, in the empty program,
with any rank. The target of a member is its pair. -/
def pairClass (rank : Program → Rel → Nat) : ProgClass where
  mem P q := decide (P.defs = [] ∧ P.sorts = [] ∧ pairTgt q ≠ [] ∧ q = .ofPairs (pairTgt q))
  rank := rank
  tgt _ q := pairTgt q

theorem pairTgt_ofPairs (a c : GTerm) : pairTgt (.ofPairs [(a, c)]) = [(a, c)] := by
  simp [RelOf.ofPairs, pairTgt, GTerm.toPat_bind]

variable {rank : Program → Rel → Nat}

theorem pairClass_mem {P : Program} {q : Rel} (h : (pairClass rank).mem P q) :
    P = ⟨[], []⟩ ∧ ∃ a c, q = .ofPairs [(a, c)] ∧ (pairClass rank).tgt P q = [(a, c)] := by
  simp only [pairClass, decide_eq_true_eq] at h
  obtain ⟨hd, hs, hne, hq⟩ := h
  obtain ⟨defs, sorts⟩ := P
  dsimp only at hd hs
  subst hd hs
  refine ⟨rfl, ?_⟩
  show ∃ a c, q = .ofPairs [(a, c)] ∧ pairTgt q = [(a, c)]
  unfold pairTgt at hne hq ⊢
  split at hne
  · exact ⟨_, _, hq, rfl⟩
  · exact absurd rfl hne

theorem pairClass_mem_pair (a c : GTerm) : (pairClass rank).mem ⟨[], []⟩ (.ofPairs [(a, c)]) := by
  simp [pairClass, pairTgt_ofPairs]

theorem toPat_firstOrder (g : GTerm) : g.toPat.firstOrder = true := by
  induction g with
  | var v => exact v.elim
  | sym f => rfl
  | app a b iha ihb =>
    cases a with
    | var v => exact v.elim
    | sym f =>
      simp only [GTerm.toPat, Term.rename, Term.bind, Term.firstOrder] at ihb ⊢
      simpa using ihb
    | app a₁ a₂ =>
      simp only [GTerm.toPat, Term.rename, Term.bind, Term.firstOrder] at iha ihb ⊢
      simp [iha, ihb]

/-- `s (s (… z))`, `n` deep, as a ground term. -/
def gtower : Nat → GTerm
  | 0 => .sym "z"
  | n + 1 => .app (.sym "s") (gtower n)

theorem le_gtower_size : ∀ n, n ≤ (gtower n).toPat.size
  | 0 => Nat.zero_le _
  | n + 1 => by
    have := le_gtower_size n
    simp only [gtower, GTerm.toPat, Term.rename, Term.bind, Term.size] at this ⊢
    omega

/-- The class is proper whenever the rank of a query is at least its size. -/
theorem pairClass_proper {size : Nat → Nat} (hr : ∀ P q, q.size ≤ rank P q)
    (hs : ∀ k, k ≤ size k) : (pairClass rank).Proper size where
  wf P r hm := by
    obtain ⟨rfl, a, c, rfl, _⟩ := pairClass_mem hm
    simpa [ProgramOf.WellFormed, RelOf.calls, RelOf.spans, RelOf.ofPairs, Span.firstOrder,
      toPat_firstOrder] using Sorts.wellFormed_nil
  size_le P r hm := by
    obtain ⟨rfl, _⟩ := pairClass_mem hm
    have h1 := hr ⟨[], []⟩ r
    have h2 := hs (rank ⟨[], []⟩ r)
    simp only [ProgramOf.size, Sorts.size, List.map_nil, List.sum_nil]
    show 0 + 0 + r.size ≤ size (rank ⟨[], []⟩ r)
    omega
  nonempty P r hm := by
    obtain ⟨_, a, c, _, ht⟩ := pairClass_mem hm
    rw [ht]; simp
  related P r hm x hx := by
    obtain ⟨rfl, a, c, rfl, ht⟩ := pairClass_mem hm
    rw [ht] at hx
    show x ∈ denoteAt _ _ (.ofPairs [(a, c)])
    rw [denoteAt_ofPairs]
    exact hx
  unbounded k := by
    refine ⟨⟨[], []⟩, .ofPairs [(gtower k, gtower k)], pairClass_mem_pair _ _, ?_⟩
    have h1 := hr ⟨[], []⟩ (.ofPairs [(gtower k, gtower k)])
    have h2 := le_gtower_size k
    rw [size_pair] at h1
    simp only [Span.size] at h1
    show k ≤ rank _ _
    omega

/-- A machine meets a bound on the class when it meets it on each pair alone:
a member is its targets written out, so in a context it costs its residue. -/
theorem pairClass_meets {M : CostedRuntime} {hi : Nat → Nat} {f : Nat → Nat → Nat → Nat}
    (halone : ∀ a c, M.CoversUsing Meter.time ⟨[], []⟩ (.ofPairs [(a, c)])
      (ProgramOf.sorts (S := Span) ⟨[], []⟩).interp (a, c)
      (hi (rank ⟨[], []⟩ (.ofPairs [(a, c)]))))
    (hf : ∀ k res n, res ≤ f k res n) : MeetsOn Meter.time M (pairClass rank) hi f where
  alone P r hm x hx := by
    obtain ⟨rfl, a, c, rfl, ht⟩ := pairClass_mem hm
    rw [ht] at hx
    obtain rfl := List.mem_singleton.1 hx
    exact halone _ _
  inContext P r hm K _ _ y _ res hres := by
    obtain ⟨rfl, a, c, rfl, ht⟩ := pairClass_mem hm
    rw [ht] at hres
    obtain ⟨n, hn, hc⟩ := hres
    exact ⟨n, hn, le_trans hc (hf _ _ _)⟩

/-- The span of a pair written out relates the pair. -/
theorem pair_mem (a c : GTerm) (M : Interp) :
    (a, c) ∈ (⟨a.toPat, c.toPat, []⟩ : Span).denAt M := by
  rw [Span.denAt_ground M (a, c)]; rfl

/-- In the empty program the span of a pair written out is read. -/
theorem pair_reads (a c : GTerm) :
    ∃ r, (Sorts.dom []).rep ⟨a.toPat, c.toPat, []⟩ = some r :=
  reads_of_mem Sorts.wellFormed_nil (by simp [Span.firstOrder, toPat_firstOrder])
    (pair_mem a c _)

/-- The reader covers a pair written out in its first step. -/
theorem rd_covers_pair (a c : GTerm) (M : Interp) :
    (rd w).Covered ⟨[], []⟩ (.ofPairs [(a, c)]) M (a, c) 1 := by
  obtain ⟨r, hr⟩ := pair_reads a c
  exact rd_covers w (P := ⟨[], []⟩) (norm_pair a c) hr (pair_mem a c _)

/-! ## Two rungs -/

/-- The slow reader: it spends `2 ^ (t + 1)` further ticks. -/
def slow : Engine := reader fun t => 2 ^ (t + 1)

/-- The quick reader: it spends nothing further. -/
def quick : Engine := reader fun _ => 0

/-- The class of the first win: the rank of a pair is what the slow reader
pays on it, and its size. -/
def slowClass : ProgClass := pairClass fun P q => (slow.costed sized).paid P q 1 + q.size

/-- The class of the second win: the rank of a pair is its size. -/
def quickClass : ProgClass := pairClass fun _ q => q.size

/-- The numerals of the first win: the slow reader uses at most `k + 1` on a
member of rank `k`. -/
def slowBounds : Bounds :=
  { simCoeff := 1, simDeg := 1, sizeCoeff := 1, sizeDeg := 1, hiCoeff := 1, hiDeg := 1, gain := 1,
    ctxCoeff := 1, ctxDeg := 0 }

/-- The numerals of the second win: the quick reader uses at most
`(k + 1) ^ 2` on a member of rank `k`. -/
def quickBounds : Bounds :=
  { simCoeff := 1, simDeg := 1, sizeCoeff := 1, sizeDeg := 1, hiCoeff := 1, hiDeg := 2, gain := 0,
    ctxCoeff := 1, ctxDeg := 1 }

/-- The first win, as it goes on the record. -/
def slowWin : Win := ⟨⟨.time, .polynomial⟩, slowClass, slowBounds⟩

/-- The second win. -/
def quickWin : Win := ⟨⟨.time, .exponential⟩, quickClass, quickBounds⟩

theorem mul_self_add_le (k : Nat) : k * k + k ≤ (k + 1) * (k + 1) := by
  rw [Nat.add_mul, Nat.mul_add]; omega

/-- The slow reader improves on the silent engine. -/
theorem slow_improves :
    Improves ⟨.time, .polynomial⟩ (silent.costed sized) (slow.costed sized) slowBounds slowClass where
  proper := pairClass_proper (fun _ _ => Nat.le_add_left _ _) fun k => by
    show k ≤ 1 * (k + 1) ^ 1
    rw [Nat.pow_one]; omega
  grows _ := Nat.one_pos
  simulates := silent_simBy _ _ _
  simulatesSpace _ := silent_simBy _ _ _
  separates :=
    { toMeetsOn := pairClass_meets
        (fun a c => ⟨1, rd_covers_pair _ a c _, by
          show (slow.costed sized).paid _ _ 1 ≤ 1 * ((slow.costed sized).paid _ _ 1 + _ + 1) ^ 1
          rw [Nat.pow_one]; omega⟩)
        (fun k res n => by
          show res ≤ 1 * (n + 1) ^ 0 * (slowBounds.hi k + res + 1)
          rw [Nat.pow_zero]; omega)
      below := fun _ _ _ _ _ _ _ _ _ h => absurd h silent_not_covered }

/-- The slow reader is admitted above the silent engine, over the empty
record. -/
theorem slow_admits :
    Admits sized ⟨.time, .polynomial⟩ ⟨Preprocessor.id, silent, false⟩ ⟨Preprocessor.id, slow, false⟩ slowBounds ⟨2, 1⟩
      (fun _ => 0) slowClass [] 0 :=
  Admits.of_id slow_improves (rd_direction _) fun _ h => absurd h List.not_mem_nil

/-- What the quick reader pays on a pair: at most what the slow one pays. -/
theorem quick_le_slow (a c : GTerm) :
    (quick.costed sized).paid ⟨[], []⟩ (.ofPairs [(a, c)]) 1 ≤
      (slow.costed sized).paid ⟨[], []⟩ (.ofPairs [(a, c)]) 1 := by
  obtain ⟨r, hr⟩ := pair_reads a c
  show (rd _).paid _ _ 1 ≤ (rd _).paid _ _ 1
  rw [rd_paid_span _ (P := ⟨[], []⟩) (norm_pair a c) hr 0,
    rd_paid_span _ (P := ⟨[], []⟩) (norm_pair a c) hr 0]
  refine Nat.add_le_add_left ?_ _
  generalize 2 ^ (2 + (⟨a.toPat, c.toPat, []⟩ : Span).size + 1) = e
  omega

/-- The quick reader keeps the win of the slow one, within the factor 1. -/
theorem quick_keeps : slowWin.KeptBy (quick.costed sized) 1 :=
  pairClass_meets
    (fun a c => ⟨1, rd_covers_pair _ a c _, by
      have := quick_le_slow a c
      show (quick.costed sized).paid _ _ 1 ≤ 1 * (1 * ((slow.costed sized).paid _ _ 1 + _ + 1) ^ 1)
      rw [Nat.pow_one]; omega⟩)
    (fun k res n => by
      show res ≤ 1 * (1 * (n + 1) ^ 0 * (slowBounds.hi k + res + 1))
      rw [Nat.pow_zero]; omega)

/-- The quick reader improves on the slow one by an exponential gain. -/
theorem quick_improves :
    Improves ⟨.time, .exponential⟩ (slow.costed sized) (quick.costed sized) quickBounds quickClass where
  proper := pairClass_proper (fun _ _ => Nat.le_refl _) fun k => by
    show k ≤ 1 * (k + 1) ^ 1
    rw [Nat.pow_one]; omega
  grows h := by cases h
  simulates := simBy_of_covers (rd_not_halts _) fun P q n x hx => by
    obtain ⟨s, r, m, hs, hr, hx', rfl⟩ := rd_covered _ hx
    refine ⟨1, rd_covers _ hs hr hx', ?_⟩
    show (rd _).paid P q 1 ≤ 1 * ((rd _).paid P q (m + 1) + (P.size + q.size) + 1) ^ 1
    rw [rd_paid_span _ hs hr 0, rd_paid_span _ hs hr m, Nat.pow_one]
    generalize 2 ^ (2 + s.size + 1) = e
    omega
  simulatesSpace h := absurd rfl h
  separates :=
    { toMeetsOn := pairClass_meets
        (fun a c => ⟨1, rd_covers_pair _ a c _, by
          obtain ⟨r, hr⟩ := pair_reads a c
          show (rd _).paid _ _ 1 ≤ 1 * ((RelOf.ofPairs [(a, c)]).size + 1) ^ 2
          rw [rd_paid_span _ (P := ⟨[], []⟩) (norm_pair a c) hr 0, size_pair,
            show ProgramOf.size (⟨[], []⟩ : Program) = 0 from rfl, Nat.zero_add, Nat.pow_two,
            Nat.pow_two, Nat.one_mul]
          generalize (⟨a.toPat, c.toPat, []⟩ : Span).size = t
          exact le_trans (Nat.add_le_add_left (by omega) _) (mul_self_add_le (2 + t + 1))⟩)
        (fun k res n => by
          show res ≤ 1 * (quickBounds.hi k + res + n + 1) ^ 1
          rw [Nat.pow_one]; omega)
      below := fun P r hm K _ _ y _ n h => by
        obtain ⟨rfl, a, c, rfl, _⟩ := pairClass_mem hm
        obtain ⟨s, r, m, hs, hr, _, rfl⟩ := rd_covered _ h
        have hsz := norm_fill_pair a c K.shape hs
        show 2 ^ (RelOf.ofPairs [(a, c)]).size ≤ (rd _).paid _ _ (m + 1)
        rw [rd_paid_span _ hs hr m, size_pair, ← hsz]
        generalize 2 ^ (2 + s.size + 1) = e
        omega }

/-- The quick reader is admitted above the slow one by an exponential gain,
over the record that holds the slow reader's polynomial win. -/
theorem quick_admits :
    Admits sized ⟨.time, .exponential⟩ ⟨Preprocessor.id, slow, false⟩ ⟨Preprocessor.id, quick, false⟩ quickBounds
      ⟨2, 1⟩ (fun _ => 0) quickClass [slowWin] 1 :=
  Admits.of_id quick_improves (rd_direction _) fun w hw => by
    obtain rfl := List.mem_singleton.1 hw
    exact quick_keeps

/-- A ladder of two rungs above the silent engine, with both wins on its
record. -/
theorem ladder :
    Ladder sized ⟨Preprocessor.id, silent, false⟩ ⟨Preprocessor.id, quick, false⟩ [quickWin, slowWin] :=
  .admit (.admit .base slow_admits) quick_admits

end Witness
end RwLog
