/-
# Classes and contexts: what the admission rule's definitions mean

`Trusted/Cost.lean` states admission on a class of inputs (`ProgClass`) and
inside contexts (`Context`). This file shows that those definitions say what
they are meant to say, and that each has an inhabitant.

* The targets written out relate exactly the targets (`denoteAt_ofPairs`),
  and the meaning of a context applied to the meaning of an expression is the
  meaning of the plugged expression (`Ctx.denAt_fill`). So the residue of a
  context is the cost of a query that relates the demanded pair.
* A hole occurs once, so the meaning of a context distributes over unions of
  what the hole holds (`Ctx.denAt_union`).
* The member alone is the context that is only a hole, and what it demands
  is the targets (`Context.demands_alone`). Beside any `b`, a target that `b`
  does not relate is demanded (`Context.demands_orL`), and one that `b`
  relates is not (`Context.not_demands_orL`). Under `Zero ; _` nothing is
  demanded (`Context.not_demands_zero_seq`).
* `|` with anything and `;` with a wrapper leave the hole open
  (`Ctx.open_orL`, `Ctx.open_wrap`); `;` with a test does not
  (`Ctx.not_open_test`).
* `ProgClass.points` is a proper class: the queries `@t` in the empty
  program.
* For time, the statements for any resource are the ones written with ticks
  (`coversUsing_time`, `exhaustsUsing_time`).
-/
import RwLog.Rungs.Framework.Latency

namespace RwLog

/-! ## Time -/

theorem CostedRuntime.coversUsing_time (C : CostedRuntime) (P : Program) (q : Rel) (M : Interp)
    (x : GTerm × GTerm) (c : Nat) :
    C.CoversUsing Meter.time P q M x c ↔ C.CoversWithin P q M x c := Iff.rfl

theorem CostedRuntime.exhaustsUsing_time (C : CostedRuntime) (P : Program) (q : Rel) (c : Nat) :
    C.ExhaustsUsing Meter.time P q c ↔ C.ExhaustsWithin P q c := Iff.rfl

/-! ## The targets written out -/

theorem GTerm.toPat_bind (t : GTerm) (σ : Nat → GTerm) : t.toPat.bind σ = t := by
  induction t with
  | var v => exact v.elim
  | sym f => rfl
  | app t u iht ihu =>
    simp only [GTerm.toPat, Term.rename, Term.bind_app] at iht ihu ⊢
    rw [iht, ihu]

/-- A ground span relates its two sides and nothing else. -/
theorem Span.denAt_ground (M : Interp) (x : GTerm × GTerm) :
    Span.denAt M ⟨x.1.toPat, x.2.toPat, []⟩ = {x} := by
  ext p
  simp only [Span.denAt, Set.mem_ofPred_eq, GTerm.toPat_bind, List.not_mem_nil, false_imp_iff,
    implies_true, and_true, Set.mem_singleton_iff]
  exact ⟨fun ⟨_, h1, h2⟩ => Prod.ext h1 h2, fun h => by rw [h]; exact ⟨fun _ => x.1, rfl, rfl⟩⟩

/-- The targets written out relate exactly the targets, in every model. -/
theorem denoteAt_ofPairs (M : Interp) (ρ : Name → PRel) (xs : List (GTerm × GTerm)) :
    denoteAt M ρ (.ofPairs xs) = {x | x ∈ xs} := by
  induction xs with
  | nil => ext p; simp [RelOf.ofPairs, denoteAt]
  | cons x xs ih =>
    ext p
    simp only [RelOf.ofPairs, denoteAt, ih, Span.denAt_ground, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons]

/-! ## The meaning of a context -/

namespace Ctx

/-- The meaning of a context applied to the meaning of an expression is the
meaning of the context with the expression in its hole. -/
theorem denAt_fill (M : Interp) (ρ : Name → PRel) (r : Rel) (K : Ctx) :
    K.denAt M ρ (denoteAt M ρ r) = denoteAt M ρ (K.fill r) := by
  induction K with
  | hole => rfl
  | orL K b ih | orR a K ih | andL K b ih | andR a K ih | seqL K b ih | seqR a K ih | conv K ih =>
    simp only [denAt, fill, denoteAt, ih]

/-- A hole occurs once: the meaning of a context distributes over a union of
what the hole holds, except for what the context relates by itself. -/
theorem denAt_union (M : Interp) (ρ : Name → PRel) (X Y : PRel) (K : Ctx) :
    K.denAt M ρ (X ∪ Y) = K.denAt M ρ X ∪ K.denAt M ρ Y := by
  induction K with
  | hole => rfl
  | orL K b ih | orR a K ih =>
    simp only [denAt, ih]; ext p; simp only [Set.mem_union]; tauto
  | andL K b ih | andR a K ih =>
    simp only [denAt, ih]; ext p; simp only [Set.mem_union, Set.mem_inter_iff]; tauto
  | seqL K b ih =>
    simp only [denAt, ih]; ext p
    simp only [PRel.comp, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, h | h, hb⟩
      · exact Or.inl ⟨m, h, hb⟩
      · exact Or.inr ⟨m, h, hb⟩
    · rintro (⟨m, h, hb⟩ | ⟨m, h, hb⟩)
      · exact ⟨m, Or.inl h, hb⟩
      · exact ⟨m, Or.inr h, hb⟩
  | seqR a K ih =>
    simp only [denAt, ih]; ext p
    simp only [PRel.comp, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, ha, h | h⟩
      · exact Or.inl ⟨m, ha, h⟩
      · exact Or.inr ⟨m, ha, h⟩
    · rintro (⟨m, ha, h⟩ | ⟨m, ha, h⟩)
      · exact ⟨m, ha, Or.inl h⟩
      · exact ⟨m, ha, Or.inr h⟩
  | conv K ih =>
    simp only [denAt, ih]; ext p; simp only [PRel.inv, Set.mem_union, Set.mem_ofPred_eq]

/-- More in the hole gives more. -/
theorem denAt_mono (M : Interp) (ρ : Name → PRel) {X Y : PRel} (h : X ⊆ Y) (K : Ctx) :
    K.denAt M ρ X ⊆ K.denAt M ρ Y := by
  have : Y = X ∪ Y := (Set.union_eq_self_of_subset_left h).symm
  rw [this, denAt_union]
  exact Set.subset_union_left

/-! ### Open holes -/

/-- `_ | b` leaves the hole open, whatever `b` is. -/
theorem open_orL (b : Rel) : (orL hole b).Open := trivial

/-- `_ ; ($x -> t)` leaves the hole open, whatever `t` is. -/
theorem open_wrap (v : Nat) (t : Pat) : (seqL hole (.span ⟨.var v, t, []⟩)).Open :=
  ⟨⟨v, rfl, fun _ h => by cases h⟩, trivial⟩

/-- `($x -> t)`'s converse on the other side leaves the hole open too. -/
theorem open_unwrap (v : Nat) (t : Pat) : (seqR (.span ⟨t, .var v, []⟩) hole).Open :=
  ⟨⟨v, rfl, fun _ h => by cases h⟩, trivial⟩

/-- `_ ; @c` does not: it asks for the answers that end in `c`. -/
theorem not_open_test (c : Sym) : ¬ (seqL hole (.span ⟨.sym c, .sym c, []⟩)).Open := by
  rintro ⟨⟨v, hv, _⟩, _⟩
  cases hv

/-- Nor does `&`. -/
theorem not_open_and (b : Rel) : ¬ (andL hole b).Open := id

end Ctx

/-! ## What a context demands -/

namespace Context

/-- The member alone: the context that is only a hole. -/
def alone : Context := ⟨.hole, []⟩

theorem alone_open : alone.Open := trivial

theorem alone_program (P : Program) : alone.program P = P := by
  simp [alone, program]

theorem alone_query (r : Rel) : alone.query r = r := rfl

/-- The member alone demands exactly the targets. -/
theorem demands_alone (P : Program) (r : Rel) (M : Interp) (X : PRel) (y : GTerm × GTerm) :
    alone.Demands P r M X y ↔ y ∈ X := by
  simp only [Demands, alone, Ctx.denAt, Set.mem_sdiff, not_and, not_not]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ => h⟩⟩

/-- Beside `b`, a target that `b` does not relate is demanded. -/
theorem demands_orL (defs : List (Name × Rel)) (b : Rel) (P : Program) (r : Rel) (M : Interp)
    (X : PRel) (y : GTerm × GTerm) (hy : y ∈ X)
    (hb : y ∉ (Context.program ⟨.orL .hole b, defs⟩ P).semAt M b) :
    Context.Demands ⟨.orL .hole b, defs⟩ P r M X y := by
  refine ⟨Or.inl hy, ?_⟩
  rintro (h | h)
  · exact h.2 hy
  · exact hb h

/-- Beside `b`, a pair that `b` relates is not demanded: the context has it
without the member. -/
theorem not_demands_orL (defs : List (Name × Rel)) (b : Rel) (P : Program) (r : Rel)
    (M : Interp) (X : PRel) (y : GTerm × GTerm)
    (hb : y ∈ (Context.program ⟨.orL .hole b, defs⟩ P).semAt M b) :
    ¬ Context.Demands ⟨.orL .hole b, defs⟩ P r M X y :=
  fun h => h.2 (Or.inr hb)

/-- Under `Zero ; _` nothing is demanded. -/
theorem not_demands_zero_seq (defs : List (Name × Rel)) (P : Program) (r : Rel) (M : Interp)
    (X : PRel) (y : GTerm × GTerm) :
    ¬ Context.Demands ⟨.seqR .zero .hole, defs⟩ P r M X y := by
  rintro ⟨⟨m, hm, _⟩, _⟩
  exact hm

/-- A demanded pair is related by the plugged query, when the member relates
the targets. -/
theorem Demands.related {K : Context} {P : Program} {r : Rel} {M : Interp} {X : PRel}
    {y : GTerm × GTerm} (h : K.Demands P r M X y) (hX : X ⊆ (K.program P).semAt M r) :
    y ∈ (K.program P).semAt M (K.query r) := by
  have := Ctx.denAt_mono M ((K.program P).meaningAt M) hX K.shape h.1
  rwa [ProgramOf.semAt, Ctx.denAt_fill] at this

/-- A demanded pair is related by the query whose hole holds the targets
written out, so the residue is the cost of covering a pair that query
relates. -/
theorem Demands.related_ofPairs {K : Context} {P : Program} {r : Rel} {M : Interp}
    {xs : List (GTerm × GTerm)} {y : GTerm × GTerm} (h : K.Demands P r M {x | x ∈ xs} y) :
    y ∈ (K.program P).semAt M (K.query (.ofPairs xs)) := by
  have := h.1
  rwa [← denoteAt_ofPairs M ((K.program P).meaningAt M), Ctx.denAt_fill] at this

end Context

/-! ## A proper class -/

/-- `s (s (… z))`, `n` deep. -/
def tower : Nat → Pat
  | 0 => .sym "z"
  | n + 1 => .app (.sym "s") (tower n)

theorem le_tower_size : ∀ n, n ≤ (tower n).size
  | 0 => Nat.zero_le _
  | n + 1 => by have := le_tower_size n; simp only [tower, Term.size]; omega

/-- The queries `@t` in the empty program. The rank of a member is its size,
and its target is the pair `(t, t)` with every variable of `t` set to `z`. -/
def ProgClass.points : ProgClass where
  mem P q := decide (P.defs = [] ∧ P.theory = []) &&
    match q with
    | .span s => decide (s.r = s.l ∧ s.c = [])
    | _ => false
  rank _ q := q.size
  tgt _ q :=
    match q with
    | .span s => [(s.l.bind fun _ => .sym "z", s.l.bind fun _ => .sym "z")]
    | _ => []

theorem ProgClass.points_mem {P : Program} {q : Rel} (h : ProgClass.points.mem P q) :
    P = ⟨[], []⟩ ∧ ∃ t, q = .span ⟨t, t, []⟩ := by
  simp only [points, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hd, ht⟩, hq⟩ := h
  refine ⟨by cases P; simp_all, ?_⟩
  cases q with
  | span s =>
    obtain ⟨l, r, c⟩ := s
    simp only [decide_eq_true_eq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact ⟨_, rfl⟩
  | _ => simp at hq

/-- `points` is a proper class, with members no larger than their rank. -/
theorem ProgClass.points_proper : ProgClass.points.Proper fun k => k where
  wf P r h := by
    obtain ⟨rfl, t, rfl⟩ := points_mem h
    simp [ProgramOf.WellFormed, RelOf.calls]
  size_le P r h := by
    obtain ⟨rfl, t, rfl⟩ := points_mem h
    simp [points, ProgramOf.size, Theory.size]
  model P r h := by
    obtain ⟨rfl, t, rfl⟩ := points_mem h
    exact ⟨∅, fun ρ hρ => by cases hρ⟩
  nonempty P r h := by
    obtain ⟨rfl, t, rfl⟩ := points_mem h
    simp [points]
  related P r h M _ x hx := by
    obtain ⟨rfl, t, rfl⟩ := points_mem h
    simp only [points, List.mem_singleton] at hx
    subst hx
    exact ⟨fun _ => .sym "z", rfl, rfl, by simp⟩
  unbounded k := by
    refine ⟨⟨[], []⟩, .span ⟨tower k, tower k, []⟩, by simp [points], ?_⟩
    have := le_tower_size k
    simp only [points, RelOf.size, Span.size]
    omega

end RwLog
