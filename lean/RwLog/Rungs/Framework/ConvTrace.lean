/-
# `ConvTrace` as stated is false for every engine

`Runtime.ConvTrace` (`Trusted/Properties.lean`) says the run on `conv q` is
the run on `q` with every answer swapped, as an equation between traces: the
answers of each step are the same list, in the same order.

An engine (`Trusted/Cost.lean`) is handed the root node of the normal form of
the query and nothing else of the query. The query

    (a -> b) | (b -> a)

and its converse have the same normal form: converse is pushed inward and
swaps each span, and the members of a union are a sorted set. So an engine
starts both in the same state, and `ConvTrace` asks that its trace on this
query is its own image under swapping every answer, in order. Then the first
answer it emits is its own converse, so it relates `(a, b)` exactly when it
relates `(b, a)`. A machine that is derivation-general emits only answers
that relate the pairs of one derivable span, here `a -> b` or `b -> a`, which
relate one of the two pairs and not the other; and a machine that is complete
pair by pair emits an answer.

So no engine has `ConvTrace` together with `DerivationGeneral` and
`PointComplete`, at any domain and any kernel, and `Runtime.Keeps` holds of
no engine (`Engine.not_keeps`). Nothing about the engine or the domain is
used but that the first state depends on the query through its normal form.

The run of an engine on a converse can be the mirror image of its run only up
to the order of the answers of a step, which is how `DualTrace` is stated
(`TraceEquiv`).
-/
import RwLog.Rungs.Framework.Derivation
import RwLog.Rungs.Framework.Runtime
import RwLog.SpanLayer.Sorts

namespace RwLog

namespace ConvTraceFalse

/-- `a -> b`. -/
def ab : Span := ⟨.sym "a", .sym "b", []⟩

/-- `(a -> b) | (b -> a)`. -/
def q : Rel := .or (.span ab) (.span ab.swap)

/-- The program with no definitions and no sorts. -/
def P : Program := ⟨[], []⟩

theorem wf : P.WellFormed q := by
  refine ⟨List.nodup_nil, ?_, Sorts.wellFormed_nil, ?_⟩
  · intro n hn; simp [q, P, RelOf.calls] at hn
  · intro s hs
    simp only [q, P, RelOf.spans, List.flatMap_nil, List.append_nil, List.mem_append,
      List.mem_singleton] at hs
    rcases hs with rfl | rfl <;> rfl

/-- The query and its converse have the same normal form. -/
theorem norm_conv : (RelOf.conv q).norm = q.norm := by
  show normB true (.or (.span ab) (.span ab.swap)) = normB false (.or (.span ab) (.span ab.swap))
  rw [normB_or_comm false]
  rfl

theorem ab_den (M : Interp) (p : GTerm × GTerm) : p ∈ ab.denAt M ↔ p = (.sym "a", .sym "b") := by
  constructor
  · rintro ⟨σ, h₁, h₂, -⟩; exact Prod.ext h₁ h₂
  · rintro rfl; exact ⟨fun _ => .sym "a", rfl, rfl, by simp [ab]⟩

theorem ba_den (M : Interp) (p : GTerm × GTerm) :
    p ∈ ab.swap.denAt M ↔ p = (.sym "b", .sym "a") := by
  constructor
  · rintro ⟨σ, h₁, h₂, -⟩; exact Prod.ext h₁ h₂
  · rintro rfl; exact ⟨fun _ => .sym "a", rfl, rfl, by simp [ab, Span.swap]⟩

/-- A derivable span of the query is one of the two. -/
theorem derives {s : Span} (h : Derives P q s) : s = ab ∨ s = ab.swap := by
  cases h with
  | orl h => cases h; exact .inl rfl
  | orr h => cases h; exact .inr rfl

end ConvTraceFalse

open ConvTraceFalse in
/-- A machine that starts `(a -> b) | (b -> a)` and its converse in the same
state does not have `ConvTrace` together with `DerivationGeneral` and
`PointComplete`. -/
theorem Runtime.not_convTrace_of_init (R : Runtime) (hinit : R.init P (.conv q) = R.init P q)
    (hG : R.DerivationGeneral) (hC : R.PointComplete) : ¬ R.ConvTrace := by
  intro hT
  have hab : ((.sym "a", .sym "b") : GTerm × GTerm) ∈ P.pairs q := by
    unfold ProgramOf.pairs
    rw [ProgramOf.semAt_eq]
    exact GRel.at_mono (Derives.den_subset (.orl (.span ab))) _
      ((Span.denAt_eq _ _ ▸ (ab_den _ _).2 rfl))
  obtain ⟨n, a, ha, -⟩ := hC P q wf _ hab
  -- the emitted answers are their own image under swapping
  have hE : R.emitted (R.init P q) n = (R.emitted (R.init P q) n).map Answer.swap := by
    have h := hT P q n
    rw [hinit] at h
    rw [R.emitted_eq_flatMap_trace]
    conv_lhs => rw [h]
    rw [List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun x _ => ?_
    cases x <;> rfl
  -- so the first one is its own converse
  obtain ⟨a₀, rest, hl⟩ : ∃ a₀ rest, R.emitted (R.init P q) n = a₀ :: rest := by
    cases hl : R.emitted (R.init P q) n with
    | nil => rw [hl] at ha; cases ha
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hswap : a₀ = Answer.swap a₀ := by
    rw [hl, List.map_cons] at hE
    exact (List.cons.inj hE).1
  obtain ⟨s, hs, hr⟩ := hG P q wf a₀ ⟨n, hl ▸ List.mem_cons_self⟩
  have hr' : Answer.den P.sorts.interp a₀ = s.denAt P.sorts.interp := hr
  have hinv : ∀ x y, (x, y) ∈ s.denAt P.sorts.interp → (y, x) ∈ s.denAt P.sorts.interp := by
    intro x y h
    rw [← hr'] at h ⊢
    rw [hswap, Answer.den_swap]
    exact h
  rcases derives hs with rfl | rfl
  · have := (ab_den _ _).1 (hinv _ _ ((ab_den _ _).2 rfl))
    simp at this
  · have := (ba_den _ _).1 (hinv _ _ ((ba_den _ _).2 rfl))
    simp at this

namespace Engine

variable (E : Engine) {R : Type} [Answer R] [DecidableEq R] (dom : Sorts → Domain R)
  (K : Sorts → Kernel R Cost) (hK : ∀ S, (K S).Refines (dom S))

/-- An engine starts two queries with the same normal form in the same
state. -/
theorem init_of_norm (P : Program) {q q' : Rel} (h : q.norm = q'.norm) :
    (E.costedAt dom K hK).runtime.init P q = (E.costedAt dom K hK).runtime.init P q' := by
  show ((E.costedAt dom K hK).init P q).val = ((E.costedAt dom K hK).init P q').val
  simp only [costedAt, Cost.bind_val, Charged.load, Charged.op_val, h]

/-- **No engine has `ConvTrace` as it is stated** together with
`DerivationGeneral` and `PointComplete`, at any domain and any kernel. -/
theorem not_convTrace (hG : (E.costedAt dom K hK).runtime.DerivationGeneral)
    (hC : (E.costedAt dom K hK).runtime.PointComplete) :
    ¬ (E.costedAt dom K hK).runtime.ConvTrace :=
  Runtime.not_convTrace_of_init _ (E.init_of_norm dom K hK _ ConvTraceFalse.norm_conv) hG hC

/-- **`Keeps` holds of no engine**, whatever the base. -/
theorem not_keeps (Base : Runtime) : ¬ (E.costedAt dom K hK).runtime.Keeps Base := fun h =>
  E.not_convTrace dom K hK h.derivationGeneral h.pointComplete h.convTrace

/-- Nor does `KeepsPointwise`, so no rung of an engine has `Rung.Keeps`. -/
theorem not_keepsPointwise (Base : Runtime) :
    ¬ (E.costedAt dom K hK).runtime.KeepsPointwise Base := fun h =>
  E.not_convTrace dom K hK h.derivationGeneral h.pointComplete h.convTrace

end Engine

end RwLog
