/-
# Fairness: what the bound means, and the wording that is false

`Trusted/Properties.lean` states the fairness bound `Fair`. This file has the
facts that show the statement says what it is meant to say, and the
counterexample to the wording it replaced.

* `Alternative.semAt_subset`: an alternative of a query relates only pairs
  the query relates, so the bound compares two runs that owe the same pair.
* `CostedRuntime.paid_le_steps`: what `n` steps cost is at most `n` times the
  dearest of them. With `Fair.flat` this is the bound in ticks: a pair an
  alternative covers within `n` ticks alone is covered within `c * n` steps,
  each costing at most what the dearest round so far cost
  (`Fair.flat_ticks`).
* `Runtime.FinalMaximal.maximal`: under `FinalMaximal` every reported answer
  is maximal among the emitted ones.

## The first wording

The first wording of the bound was: an answer is covered within a polynomial
of the size of its derivation and of the input. `FirstWording C coeff deg` is
that statement, with derivations of ground pairs (`GDerives`, the ground
semantics with the size of the derivation). `firstWording_false`: no machine
that emits spans, is sound and pays a tick for each answer it emits has it,
for any polynomial. The inputs are `bits k`, the query `bit ; … ; bit` with
`k + 1` factors and no program, where `bit` puts `o` or `i` on top of a term.
It has `2 ^ (k + 1)` answers, one for each word, each with a derivation of
size `3 * k + 2`, and no sound span relates the pairs of two words
(`no_shared_span`), so covering them takes `2 ^ (k + 1)` answers.
-/
import RwLog.SpanLayer.Sorts
import RwLog.Rungs.Framework.Latency
import RwLog.Trusted.Properties
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecificLimits.Normed

namespace RwLog

/-! ## Alternatives -/

theorem RelOf.semAt_of_mem_members (P : Program) (M : Interp) :
    ∀ (e : Rel) {m : Rel}, m ∈ e.members → P.semAt M m ⊆ P.semAt M e
  | .or a b, m, hm => by
    rcases List.mem_append.1 hm with h | h
    · exact (semAt_of_mem_members P M a h).trans Set.subset_union_left
    · exact (semAt_of_mem_members P M b h).trans Set.subset_union_right
  | .zero, m, hm => by rw [List.mem_singleton.1 hm]
  | .span _, m, hm => by rw [List.mem_singleton.1 hm]
  | .and _ _, m, hm => by rw [List.mem_singleton.1 hm]
  | .seq _ _, m, hm => by rw [List.mem_singleton.1 hm]
  | .conv _, m, hm => by rw [List.mem_singleton.1 hm]
  | .call _, m, hm => by rw [List.mem_singleton.1 hm]

/-- An alternative of a query relates only pairs the query relates. -/
theorem Alternative.semAt_subset {P : Program} {q q' : Rel} {f : Nat} (h : Alternative P q q' f)
    (M : Interp) : P.semAt M q' ⊆ P.semAt M q := by
  induction h with
  | same e => exact le_rfl
  | pick hm _ ih => exact ih.trans (RelOf.semAt_of_mem_members P M _ hm)
  | seq _ _ iha ihb => exact fun p ⟨m, h1, h2⟩ => ⟨m, iha h1, ihb h2⟩
  | and _ _ iha ihb => exact fun p ⟨h1, h2⟩ => ⟨iha h1, ihb h2⟩
  | conv _ ih => exact fun p hp => ih hp
  | @call n e' f _ ih =>
    refine ih.trans (le_of_eq ?_)
    exact (P.meaningAt_eq M n).symm

/-! ## The flat bound in ticks -/

namespace CostedRuntime

variable (C : CostedRuntime)

/-- The ticks of the dearest of the first `n` steps. -/
def dearest : C.State → Nat → Nat
  | _, 0 => 0
  | s, n + 1 =>
    max (C.step s).ticks (match (C.step s).val with
      | .emit _ s' => dearest s' n
      | .progress _ s' => dearest s' n
      | .done _ => 0)

/-- What `n` steps cost is at most `n` times the dearest of them. -/
theorem spent_le_steps : ∀ (n : Nat) (s : C.State), C.spent s n ≤ n * C.dearest s n
  | 0, _ => Nat.le_refl 0
  | n + 1, s => by
    have h1 : (C.step s).ticks ≤ C.dearest s (n + 1) := le_max_left _ _
    cases hs : (C.step s).val with
    | emit as s' =>
      have h2 : C.dearest s' n ≤ C.dearest s (n + 1) := by
        simp only [dearest, hs]; exact le_max_right _ _
      rw [C.spent_succ_emit hs]
      have := spent_le_steps n s'
      have := Nat.mul_le_mul_left n h2
      rw [Nat.succ_mul]; omega
    | progress k s' =>
      have h2 : C.dearest s' n ≤ C.dearest s (n + 1) := by
        simp only [dearest, hs]; exact le_max_right _ _
      rw [C.spent_succ_progress hs]
      have := spent_le_steps n s'
      have := Nat.mul_le_mul_left n h2
      rw [Nat.succ_mul]; omega
    | done fin =>
      rw [C.spent_succ_done hs, Nat.succ_mul]; omega

theorem paid_le_steps (P : Program) (q : Rel) (n : Nat) :
    C.paid P q n ≤ (C.init P q).ticks + n * C.dearest (C.start P q) n :=
  Nat.add_le_add_left (C.spent_le_steps n _) _

end CostedRuntime

/-- The flat bound in ticks: a pair an alternative covers within `n` ticks
when run alone is covered by the time the machine has paid for building its
first state and for `m ≤ c * n` steps, each at most the dearest of them. -/
theorem Fair.flat_ticks {C : CostedRuntime} {c : Nat} (h : Fair C c) {P : Program} {q q' : Rel}
    {f : Nat} (hwf : P.WellFormed q) (ha : Alternative P q q' f)
    {x : GTerm × GTerm} {n : Nat} (hx : C.Covered P q' P.sorts.interp x n) :
    ∃ m, m ≤ c * C.paid P q' n ∧
      C.CoversWithin P q P.sorts.interp x
        ((C.init P q).ticks + m * C.dearest (C.start P q) m) := by
  obtain ⟨m, hm, hc⟩ := h.flat P q q' f hwf ha x n hx
  exact ⟨m, hm, m, hc, C.paid_le_steps P q m⟩

/-! ## The final report -/

/-- Under `FinalMaximal` a reported answer is maximal among the emitted
ones: an emitted answer that covers it is covered by it. -/
theorem Runtime.FinalMaximal.maximal {R : Runtime} (h : R.FinalMaximal) {P : Program} {q : Rel}
    (hwf : P.WellFormed q) {n : Nat} {fin : List R.Ans} (hf : R.final (R.init P q) n = some fin)
    {a : R.Ans} (ha : a ∈ fin) {b : R.Ans} (hb : b ∈ R.emitted (R.init P q) n)
    (hba : Answer.Covers P.sorts.interp b a) : Answer.Covers P.sorts.interp a b := by
  obtain ⟨-, hcov, hpw⟩ := h P q hwf n fin hf
  obtain ⟨c, hc, hcb⟩ := hcov b hb
  have hca : Answer.Covers P.sorts.interp c a := Set.Subset.trans hba hcb
  by_cases hac : c = a
  · exact hac ▸ hcb
  · exfalso
    have : Std.Symm fun x y : R.Ans =>
        ¬ Answer.Covers P.sorts.interp x y ∧ ¬ Answer.Covers P.sorts.interp y x :=
      ⟨fun _ _ h => ⟨h.2, h.1⟩⟩
    exact (hpw.forall hc ha hac).1 hca

/-! ## The first wording of the fairness bound is false -/

/-- A derivation of a ground pair in an interpretation, with its size: the
ground semantics with every use of a rule counted. -/
inductive GDerives (P : Program) (M : Interp) : Nat → Rel → GTerm × GTerm → Prop
  | span {s : Span} {p : GTerm × GTerm} : p ∈ s.denAt M → GDerives P M 1 (.span s) p
  | orl {d : Nat} {a b : Rel} {p : GTerm × GTerm} : GDerives P M d a p →
      GDerives P M (d + 1) (.or a b) p
  | orr {d : Nat} {a b : Rel} {p : GTerm × GTerm} : GDerives P M d b p →
      GDerives P M (d + 1) (.or a b) p
  | seq {d₁ d₂ : Nat} {a b : Rel} {x m y : GTerm} : GDerives P M d₁ a (x, m) →
      GDerives P M d₂ b (m, y) → GDerives P M (d₁ + d₂ + 1) (.seq a b) (x, y)
  | and {d₁ d₂ : Nat} {a b : Rel} {p : GTerm × GTerm} : GDerives P M d₁ a p →
      GDerives P M d₂ b p → GDerives P M (d₁ + d₂ + 1) (.and a b) p
  | conv {d : Nat} {a : Rel} {x y : GTerm} : GDerives P M d a (x, y) →
      GDerives P M (d + 1) (.conv a) (y, x)
  | call {d : Nat} {n : Name} {p : GTerm × GTerm} : GDerives P M d (P.body n) p →
      GDerives P M (d + 1) (.call n) p

/-- A derived pair is a pair of the ground semantics. -/
theorem GDerives.semAt {P : Program} {M : Interp} {d : Nat} {e : Rel} {p : GTerm × GTerm}
    (h : GDerives P M d e p) : p ∈ P.semAt M e := by
  induction h with
  | span hp => exact hp
  | orl _ ih => exact Or.inl ih
  | orr _ ih => exact Or.inr ih
  | seq _ _ iha ihb => exact ⟨_, iha, ihb⟩
  | and _ _ iha ihb => exact ⟨iha, ihb⟩
  | conv _ ih => exact ih
  | @call d n p _ ih =>
    show p ∈ P.meaningAt M n
    rw [P.meaningAt_eq M n]; exact ih

/-- The first wording: every pair with a derivation of size `d` is covered
within `coeff * (d + size + 1) ^ deg` ticks. -/
def FirstWording (C : CostedRuntime) (coeff deg : Nat) : Prop :=
  ∀ P q, P.WellFormed q → ∀ d x, GDerives P P.sorts.interp d q x →
    C.CoversWithin P q P.sorts.interp x (coeff * (d + P.size + q.size + 1) ^ deg)

/-- The machine has paid a tick for each answer it has emitted. -/
def CostedRuntime.PaysPerAnswer (C : CostedRuntime) : Prop :=
  ∀ P q n, (C.runtime.emitted (C.start P q) n).length ≤ C.paid P q n

/-- A machine whose answers are spans. -/
def CostedRuntime.ofSpans (State : Type) (init : Program → Rel → Cost State)
    (step : State → Cost (StepOf Span State)) : CostedRuntime where
  Ans := Span
  State := State
  init := init
  step := step

namespace FirstWordingFalse

/-- The symbol a bit puts on top of a term. -/
def bitSym (b : Bool) : Sym := if b then "i" else "o"

theorem bitSym_inj {b b' : Bool} (h : bitSym b = bitSym b') : b = b' := by
  cases b <;> cases b' <;> simp [bitSym] at h ⊢

theorem bitSym_ne_z (b : Bool) : bitSym b ≠ "z" := by cases b <;> simp [bitSym]

/-- The word `w` on top of a term, first letter outermost. -/
def wrapO {V : Type} : List Bool → Term V → Term V
  | [], t => t
  | b :: w, t => .app (.sym (bitSym b)) (wrapO w t)

/-- The word `w` on top of a term, first letter innermost. -/
def wrapR {V : Type} : List Bool → Term V → Term V
  | [], t => t
  | b :: w, t => wrapR w (.app (.sym (bitSym b)) t)

theorem wrapO_append {V : Type} (u v : List Bool) (t : Term V) :
    wrapO (u ++ v) t = wrapO u (wrapO v t) := by
  induction u with
  | nil => rfl
  | cons b u ih => simp only [List.cons_append, wrapO, ih]

theorem wrapR_eq {V : Type} : ∀ (w : List Bool) (t : Term V), wrapR w t = wrapO w.reverse t
  | [], _ => rfl
  | b :: w, t => by
    rw [wrapR, wrapR_eq w, List.reverse_cons, wrapO_append]; rfl

/-- Put `o` or `i` on top of a term. -/
def bit : Rel :=
  .or (.span ⟨.var 0, .app (.sym "o") (.var 0), []⟩) (.span ⟨.var 0, .app (.sym "i") (.var 0), []⟩)

/-- `bit ; … ; bit`, with `k + 1` factors. -/
def bits : Nat → Rel
  | 0 => bit
  | k + 1 => .seq bit (bits k)

/-- The program with no definition and no sort. -/
def prog : Program := ⟨[], []⟩

/-- The ground term the targets start from. -/
def z : GTerm := .sym "z"

theorem bits_calls : ∀ k, (bits k).calls = []
  | 0 => rfl
  | k + 1 => by simp [bits, RelOf.calls, bits_calls k, bit]

theorem bits_spans : ∀ k, ∀ s ∈ (bits k).spans, s.firstOrder = true
  | 0 => by decide
  | k + 1 => by
    intro s hs
    simp only [bits, RelOf.spans, List.mem_append] at hs
    rcases hs with hs | hs
    · revert s; decide
    · exact bits_spans k s hs

theorem wellFormed (k : Nat) : prog.WellFormed (bits k) := by
  refine ⟨List.nodup_nil, ?_, Sorts.wellFormed_nil, ?_⟩
  · simp [bits_calls, prog]
  · simpa [prog] using bits_spans k

theorem bits_size : ∀ k, (bits k).size ≤ 12 * (k + 1)
  | 0 => by decide
  | k + 1 => by
    have := bits_size k
    have h0 : bit.size = 11 := by decide
    simp only [bits, RelOf.size, h0]; omega

theorem prog_size : prog.size = 0 := by decide

theorem mem_bit {M : Interp} {ρ : Name → PRel} {p : GTerm × GTerm} :
    p ∈ denoteAt M ρ bit ↔ ∃ b, p.2 = .app (.sym (bitSym b)) p.1 := by
  constructor
  · rintro (⟨σ, h1, h2, -⟩ | ⟨σ, h1, h2, -⟩)
    · exact ⟨false, by rw [h2, h1]; rfl⟩
    · exact ⟨true, by rw [h2, h1]; rfl⟩
  · rintro ⟨b, hb⟩
    cases b with
    | false => exact Or.inl ⟨fun _ => p.1, rfl, hb, by simp⟩
    | true => exact Or.inr ⟨fun _ => p.1, rfl, hb, by simp⟩

/-- A pair of `bits k` is a term and a word of `k + 1` letters on top of
it. -/
theorem mem_bits {M : Interp} {ρ : Name → PRel} : ∀ (k : Nat) {p : GTerm × GTerm},
    p ∈ denoteAt M ρ (bits k) → ∃ w : List Bool, w.length = k + 1 ∧ p.2 = wrapR w p.1
  | 0, p, h => by
    obtain ⟨b, hb⟩ := mem_bit.1 h
    exact ⟨[b], rfl, hb⟩
  | k + 1, p, ⟨m, h1, h2⟩ => by
    obtain ⟨b, hb⟩ := mem_bit.1 h1
    obtain ⟨w, hw, he⟩ := mem_bits k h2
    exact ⟨b :: w, by simp [hw], by rw [he]; simp only at hb; rw [hb]; rfl⟩

/-- Every word of `k + 1` letters on top of a term has a derivation of size
`3 * k + 2`. -/
theorem derives (M : Interp) : ∀ (k : Nat) (w : List Bool), w.length = k + 1 → ∀ x : GTerm,
    GDerives prog M (3 * k + 2) (bits k) (x, wrapR w x)
  | 0, [b], _, x => by
    cases b with
    | false => exact .orl (.span ⟨fun _ => x, rfl, rfl, by simp⟩)
    | true => exact .orr (.span ⟨fun _ => x, rfl, rfl, by simp⟩)
  | 0, [], h, _ => by simp at h
  | 0, _ :: _ :: _, h, _ => by simp at h
  | k + 1, [], h, _ => by simp at h
  | k + 1, b :: w, h, x => by
    have h1 : GDerives prog M 2 bit (x, .app (.sym (bitSym b)) x) := by
      cases b with
      | false => exact .orl (.span ⟨fun _ => x, rfl, rfl, by simp⟩)
      | true => exact .orr (.span ⟨fun _ => x, rfl, rfl, by simp⟩)
    have h2 := derives M k w (by simpa using h) (.app (.sym (bitSym b)) x)
    have := GDerives.seq h1 h2
    rw [show 3 * (k + 1) + 2 = 2 + (3 * k + 2) + 1 by omega]
    exact this

/-- Words of the same length on top of terms are equal only if the words
are. -/
theorem wrapO_inj {V : Type} : ∀ {w w' : List Bool} {t t' : Term V}, w.length = w'.length →
    wrapO w t = wrapO w' t' → w = w'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | b :: w, b' :: w', t, t', hl, h => by
    simp only [wrapO, Term.app.injEq, Term.sym.injEq] at h
    rw [bitSym_inj h.1, wrapO_inj (by simpa using hl) h.2]

/-- Put a ground term for a symbol. -/
def subSym (c : Sym) (g : GTerm) : GTerm → GTerm
  | .var e => nomatch e
  | .sym s => if s = c then g else .sym s
  | .app t u => .app (subSym c g t) (subSym c g u)

theorem subSym_fresh {c : Sym} {g : GTerm} : ∀ {t : GTerm}, c ∉ t.syms → subSym c g t = t
  | .var e, _ => nomatch e
  | .sym s, h => by
    have : s ≠ c := fun e => h (by simp [Term.syms, e])
    simp [subSym, this]
  | .app t u, h => by
    simp only [Term.syms, List.mem_append, not_or] at h
    simp only [subSym, subSym_fresh h.1, subSym_fresh h.2]

/-- An instance with a fresh symbol for one variable gives the instance back
when the value of the variable is put for the symbol. -/
theorem subSym_bind {c : Sym} {σ : Nat → GTerm} {v : Nat} : ∀ {t : Pat},
    c ∉ (t.bind σ).syms →
      subSym c (σ v) (t.bind (Function.update σ v (.sym c))) = t.bind σ
  | .var x, h => by
    by_cases hx : x = v
    · subst hx; simp [Term.bind, subSym]
    · simp only [Term.bind, Function.update_of_ne hx]
      exact subSym_fresh h
  | .sym s, h => by
    have : s ≠ c := fun e => h (by simp [Term.bind, Term.syms, e])
    simp [Term.bind, subSym, this]
  | .app t u, h => by
    simp only [Term.bind, Term.syms, List.mem_append, not_or] at h
    simp only [Term.bind, subSym, subSym_bind h.1, subSym_bind h.2]

/-- With no sort declared, the constraints that hold are the disequations of
different terms. -/
theorem holds_nil {g : GTerm} :
    Sorts.Holds [] g ↔ ∃ t u, g = .app (.app (.sym neSym) t) u ∧ t ≠ u := by
  constructor
  · intro h
    match g, h with
    | .app (.sym _) _, h => exact absurd h Sorts.not_mem_nil
    | .app (.app (.sym f) t) u, h => exact ⟨t, u, by rw [h.1], h.2⟩
  · rintro ⟨t, u, rfl, h⟩
    exact ⟨rfl, h⟩

/-- A letter, or a letter on top of a term. -/
def Lettered (d : GTerm) : Prop := ∃ b, d = .sym (bitSym b) ∨ ∃ t, d = .app (.sym (bitSym b)) t

theorem bitSym_ne_neSym (b : Bool) : bitSym b ≠ neSym := by cases b <;> decide

/-- A constraint that holds once a lettered term is put for a symbol held
before, with no sort declared. -/
theorem holds_of_subSym {c : Sym} {d g : GTerm} (hd : Lettered d)
    (h : Sorts.Holds [] (subSym c d g)) : Sorts.Holds [] g := by
  obtain ⟨b, hd⟩ := hd
  obtain ⟨t, u, e, hne⟩ := holds_nil.1 h
  have hsym : ∀ {x : GTerm} {f : Sym}, subSym c d x = .sym f → f ≠ bitSym b → x = .sym f := by
    intro x f hx hf
    match x, hx with
    | .sym s, hx =>
      simp only [subSym] at hx
      split at hx
      · rcases hd with rfl | ⟨_, rfl⟩
        · cases hx; exact absurd rfl hf
        · cases hx
      · exact hx
  match g, e with
  | .sym s, e =>
    simp only [subSym] at e
    split at e
    · rcases hd with rfl | ⟨_, rfl⟩ <;> cases e
    · cases e
  | .app (.sym s) g₂, e =>
    simp only [subSym, Term.app.injEq] at e
    split at e
    · rcases hd with rfl | ⟨_, rfl⟩
      · cases e.1
      · simp only [Term.app.injEq, Term.sym.injEq] at e
        exact absurd e.1.1 (bitSym_ne_neSym b)
    · cases e.1
  | .app (.app g₁ g₂) g₃, e =>
    simp only [subSym, Term.app.injEq] at e
    obtain ⟨⟨e₁, rfl⟩, rfl⟩ := e
    rw [hsym e₁ (bitSym_ne_neSym b).symm]
    exact ⟨rfl, fun e' => hne (by rw [e'])⟩

/-- A pattern with instances under two different words of the same length has
a variable, lettered in the first instance, such that the first instance with
a symbol that is no letter for that variable is under no word of that length:
where the two words first differ, the pattern has a variable. -/
theorem no_shared_pattern : ∀ (w w' : List Bool) (r : Pat) (σ σ' : Nat → GTerm) (t t' : GTerm),
    w.length = w'.length → w ≠ w' → r.bind σ = wrapO w t → r.bind σ' = wrapO w' t' →
    ∃ v, Lettered (σ v) ∧ ∀ c : Sym, (∀ b, c ≠ bitSym b) →
      ¬ ∃ (w'' : List Bool) (s : GTerm), w''.length = w.length ∧
        r.bind (Function.update σ v (.sym c)) = wrapO w'' s
  | [], [], _, _, _, _, _, _, hne, _, _ => absurd rfl hne
  | [], _ :: _, _, _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _, _, _ => by simp at hl
  | b :: w, b' :: w', r, σ, σ', t, t', hl, hne, h, h' => by
    cases r with
    | var v =>
      refine ⟨v, ⟨b, .inr ⟨_, h⟩⟩, ?_⟩
      rintro c - ⟨w'', s, hl'', he⟩
      cases w'' with
      | nil => simp at hl''
      | cons b'' w'' => simp [Term.bind, wrapO] at he
    | sym f => simp [Term.bind, wrapO] at h
    | app r₁ r₂ =>
      simp only [Term.bind, wrapO, Term.app.injEq] at h h'
      cases r₁ with
      | var v =>
        refine ⟨v, ⟨b, .inl h.1⟩, ?_⟩
        rintro c hc ⟨w'', s, hl'', he⟩
        cases w'' with
        | nil => simp at hl''
        | cons b'' w'' =>
          simp only [Term.bind, wrapO, Term.app.injEq, Function.update_self, Term.sym.injEq] at he
          exact hc b'' he.1
      | app _ _ => simp [Term.bind] at h
      | sym f =>
        simp only [Term.bind, Term.sym.injEq] at h h'
        have hb : b = b' := bitSym_inj (h.1.symm.trans h'.1)
        have hne' : w ≠ w' := fun hw => hne (by rw [hb, hw])
        obtain ⟨v, hv, hno⟩ := no_shared_pattern w w' r₂ σ σ' _ _ (by simpa using hl) hne' h.2 h'.2
        refine ⟨v, hv, ?_⟩
        rintro c hc ⟨w'', s, hl'', he⟩
        cases w'' with
        | nil => simp at hl''
        | cons b'' w'' =>
          simp only [Term.bind, wrapO, Term.app.injEq] at he
          exact hno c hc ⟨w'', s, by simpa using hl'', he.2⟩

/-- A span that relates only pairs of `bits k` does not relate `z` to two
different words on top of `z`. -/
theorem no_shared_span {k : Nat} {a : Span}
    (hs : a.denAt prog.sorts.interp ⊆ prog.semAt prog.sorts.interp (bits k)) {w w' : List Bool}
    (hw : w.length = k + 1) (hw' : w'.length = k + 1)
    (h : (z, wrapR w z) ∈ a.denAt prog.sorts.interp)
    (h' : (z, wrapR w' z) ∈ a.denAt prog.sorts.interp) :
    w = w' := by
  by_contra hne
  obtain ⟨σ, -, hr, hc⟩ := h
  obtain ⟨σ', -, hr', -⟩ := h'
  simp only at hr hr'
  rw [wrapR_eq] at hr hr'
  obtain ⟨v, hv, hno⟩ := no_shared_pattern w.reverse w'.reverse a.r σ σ' z z (by simp [hw, hw'])
    (fun h => hne (List.reverse_injective h)) hr.symm hr'.symm
  obtain ⟨c, hfresh⟩ := Infinite.exists_notMem_finset
    (a.c.flatMap (fun t => (t.bind σ).syms) ++ ["o", "i"]).toFinset
  simp only [List.mem_toFinset, List.mem_append, List.mem_flatMap, not_or, not_exists,
    not_and] at hfresh
  have hcb : ∀ b, c ≠ bitSym b := by
    intro b e
    cases b <;> simp [bitSym] at e <;> simp [e] at hfresh
  have hτ : (a.l.bind (Function.update σ v (.sym c)), a.r.bind (Function.update σ v (.sym c))) ∈
      a.denAt prog.sorts.interp :=
    ⟨_, rfl, rfl, fun t ht => holds_of_subSym (c := c) hv (by
      rw [subSym_bind (hfresh.1 t ht)]; exact hc t ht)⟩
  obtain ⟨w'', hw'', he⟩ := mem_bits k (hs hτ)
  simp only at he
  rw [wrapR_eq] at he
  exact hno c hcb ⟨w''.reverse, _, by simp [hw, hw''], he⟩

/-- An exponential outgrows every polynomial. -/
theorem exists_pow_lt (coeff deg : Nat) : ∃ k : Nat, coeff * (15 * (k + 1)) ^ deg < 2 ^ (k + 1) := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt deg (show (1 : ℝ) < 2 by norm_num)
  have hpos : (0 : ℝ) < 1 / ((coeff : ℝ) * 15 ^ deg + 1) := by positivity
  obtain ⟨n, hn⟩ := ((h.eventually (gt_mem_nhds hpos)).and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨hlt, hn1⟩ := hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨k, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hc : (0 : ℝ) < (coeff : ℝ) * 15 ^ deg + 1 := by positivity
  rw [div_lt_div_iff₀ h2 hc, one_mul] at hlt
  have : ((coeff * (15 * (k + 1)) ^ deg : Nat) : ℝ) < ((2 ^ (k + 1) : Nat) : ℝ) := by
    push_cast
    rw [mul_pow]
    have h3 : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ deg := by positivity
    push_cast at hlt
    nlinarith
  exact_mod_cast this

end FirstWordingFalse

open FirstWordingFalse in
/-- The first wording of the fairness bound is false for every machine that
emits spans, is sound, and pays a tick for each answer it emits, whatever the
polynomial. -/
theorem firstWording_false (State : Type) (init : Program → Rel → Cost State)
    (step : State → Cost (StepOf Span State))
    (hsound : (CostedRuntime.ofSpans State init step).runtime.Sound)
    (hpays : (CostedRuntime.ofSpans State init step).PaysPerAnswer) (coeff deg : Nat) :
    ¬ FirstWording (CostedRuntime.ofSpans State init step) coeff deg := by
  intro hfw
  set C := CostedRuntime.ofSpans State init step with hC
  obtain ⟨k, hk⟩ := exists_pow_lt coeff deg
  -- every word is covered within the bound
  have hcov : ∀ w : List.Vector Bool (k + 1),
      C.CoversWithin prog (bits k) prog.sorts.interp (z, wrapR w.1 z)
        (coeff * (3 * k + 2 + prog.size + (bits k).size + 1) ^ deg) := fun w =>
    hfw prog (bits k) (wellFormed k) _ _ (derives _ k w.1 w.2 z)
  choose n hn using hcov
  -- by the largest of those step counts every word is covered
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨List.Vector.replicate (k + 1) false,
    Finset.mem_univ _⟩ n
  set N := Finset.univ.sup n with hN
  have hall : ∀ w : List.Vector Bool (k + 1), C.Covered prog (bits k) prog.sorts.interp (z, wrapR w.1 z) N :=
    fun w => CostedRuntime.Covered.mono C (hn w).1 (Finset.le_sup (Finset.mem_univ w))
  have hpaid : C.paid prog (bits k) N ≤
      coeff * (3 * k + 2 + prog.size + (bits k).size + 1) ^ deg := hw₀ ▸ (hn w₀).2
  -- each word is covered by its own answer
  set L := C.runtime.emitted (C.start prog (bits k)) N with hL
  have hidx : ∀ w : List.Vector Bool (k + 1), ∃ i : Fin L.length,
      (z, wrapR w.1 z) ∈ (L.get i).denAt prog.sorts.interp := by
    intro w
    obtain ⟨a, ha, hx⟩ := hall w
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ⟨⟨i, hi⟩, hx⟩
  choose idx hidx using hidx
  have hinj : Function.Injective idx := by
    intro w w' h
    have hs : (L.get (idx w)).denAt prog.sorts.interp ⊆ prog.semAt prog.sorts.interp (bits k) :=
      hsound prog (bits k) (wellFormed k) N _ (List.get_mem L (idx w))
    exact Subtype.ext (no_shared_span hs w.2 w'.2 (hidx w) (h ▸ hidx w'))
  have hcard := Fintype.card_le_of_injective idx hinj
  rw [card_vector, Fintype.card_bool, Fintype.card_fin] at hcard
  -- so the machine has paid for `2 ^ (k + 1)` answers within a polynomial
  have hlen : L.length ≤ C.paid prog (bits k) N := hpays prog (bits k) N
  have hsize : 3 * k + 2 + prog.size + (bits k).size + 1 ≤ 15 * (k + 1) := by
    have := bits_size k
    rw [prog_size]; omega
  have := Nat.mul_le_mul_left coeff (Nat.pow_le_pow_left hsize deg)
  omega

end RwLog
