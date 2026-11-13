/-
# The charged tabled machine is R001

`Machine.lean` writes R001's round machine in the cost monad, leaving the
unfolding race to an oracle. Here each of its definitions is projected onto
the definition of `Base/Engine.lean` it was written from: forgetting the ticks
gives R001's function. The result is `Tabled.machine_runtime`: with any oracle
whose value is R001's unfolding race, the machine's runtime is `R001.runtime`,
as an equality of runtimes.

The one place where the two texts differ is completion. R001 asks whether the
unfolding is final for whichever table the fixpoint looks at; the charged
machine only has the oracle's verdicts for the tables that were not complete at
the start of the round. The fixpoint only ever looks at such tables
(`gfpFrom_congr`), so the two agree.
-/
import RwLog.Rungs.Framework.Cost
import RwLog.Lib.Gfp
import RwLog.Lib.List
import RwLog.Rungs.Tabled.Machine

namespace RwLog

open R001 Cost

/-- The oracle computes R001's unfolding race. -/
def Oracle.Exact (U : Oracle) : Prop :=
  ∀ P d g, (U P d g).val = (unfoldFinal P d g, unfoldAnswers P d g)

namespace Tabled

/-! ## Tables

`same_val` and `norm_val` hold by definition, but are proved by `simp` so that
they are not used as definitional rewrites: rewriting the condition of an `if`
definitionally leaves its decidability instance behind. -/

@[simp] theorem sameBound_val (a b : Option Span) : (sameBound a b).val = boundEq a b := by
  rcases a with _ | a <;> rcases b with _ | b <;>
    simp only [sameBound, boundEq, pure_val, bind_val, ite_val, Charged.covers]
  cases a.covers? b <;> simp

@[simp] theorem same_val (g h : Goal) : (same g h).val = g.same h := by
  simp only [same, GoalOf.same, bind_val, ite_val, pure_val, sameBound_val, Charged.eqRel]
  by_cases h1 : g.e = h.e <;> simp [h1]

/-- Comparing two keys without boundaries costs their sizes. -/
theorem same_ticks_none (a b : Rel) :
    (same ⟨none, a, none⟩ ⟨none, b, none⟩).ticks = a.size + b.size := by
  simp only [same, bind_ticks, ite_ticks, pure_ticks, sameBound, Charged.eqRel, pure_val]
  split <;> simp

theorem same_ticks_of_none {g h : Goal} (hg : g.lb = none ∧ g.rb = none)
    (hh : h.lb = none ∧ h.rb = none) : (same g h).ticks = goalSize g + goalSize h := by
  obtain ⟨gl, ge, gr⟩ := g
  obtain ⟨hl, he, hr⟩ := h
  obtain ⟨rfl, rfl⟩ := hg
  obtain ⟨rfl, rfl⟩ := hh
  rw [same_ticks_none]
  simp [goalSize]

theorem same_eq_of_none {g h : Goal} (hg : g.lb = none ∧ g.rb = none)
    (hh : h.lb = none ∧ h.rb = none) : same g h = ⟨g.same h, goalSize g + goalSize h⟩ := by
  have h1 := same_val g h
  have h2 := same_ticks_of_none hg hh
  cases hs : same g h with
  | mk v t =>
    rw [hs] at h1 h2
    cases h1; cases h2; rfl

/-- The search of the coverage tests on two boundaries. -/
def boundWork : Option Span → Option Span → Nat
  | some a, some b => Charged.coversWork a b + Charged.coversWork b a
  | _, _ => 0

theorem sameBound_ticks_le (a b : Option Span) :
    (sameBound a b).ticks ≤
      2 * ((a.toList ++ b.toList).map Span.size).sum + boundWork a b := by
  cases a <;> cases b <;>
    simp only [sameBound, boundWork, pure_ticks, bind_ticks, ite_ticks, Charged.covers,
      Option.toList, List.nil_append, List.map_nil, List.sum_nil, Nat.zero_le]
  split <;> simp <;> omega

/-- Comparing two keys costs at most twice their sizes and the search of the
coverage tests on their boundaries. -/
theorem same_ticks_le (g h : Goal) :
    (same g h).ticks ≤ 2 * (goalSize g + goalSize h) + boundWork g.lb h.lb + boundWork g.rb h.rb := by
  obtain ⟨gl, ge, gr⟩ := g
  obtain ⟨hl, he, hr⟩ := h
  have h1 := sameBound_ticks_le gl hl
  have h2 := sameBound_ticks_le gr hr
  have e : goalSize ⟨gl, ge, gr⟩ + goalSize ⟨hl, he, hr⟩ = ge.size + he.size +
      ((gl.toList ++ hl.toList).map Span.size).sum +
      ((gr.toList ++ hr.toList).map Span.size).sum := by
    cases gl <;> cases gr <;> cases hl <;> cases hr <;> simp [goalSize] <;> omega
  rw [e]
  simp only [same, bind_ticks, ite_ticks, pure_ticks, Charged.eqRel]
  split
  · split <;> omega
  · omega

@[simp] theorem norm_val (g : Goal) : (norm g).val = g.norm := by
  simp only [norm]

@[simp] theorem findTable_val (ts : Tables) (g : Goal) :
    (findTable ts g).val = R001.findTable ts g := by
  simp [findTable, R001.findTable]

theorem indexFrom_val (g : Goal) : ∀ (ts : Tables) (i : Nat),
    (indexFrom g i ts).val = (R001.indexOf ts g).map (· + i)
  | [], _ => rfl
  | t :: ts, i => by
    have ih := indexFrom_val g ts (i + 1)
    simp only [R001.indexOf] at ih
    simp only [indexFrom, bind_val, ite_val, pure_val, ih, same_val, R001.indexOf,
      List.findIdx?_cons]
    split
    · simp
    · cases List.findIdx? (fun t => t.goal.same g) ts
      · rfl
      · simp only [Option.map_some, Option.some.injEq]; omega

@[simp] theorem indexOf_val (ts : Tables) (g : Goal) :
    (indexOf ts g).val = R001.indexOf ts g := by
  simp [indexOf, indexFrom_val]

@[simp] theorem answersOf_val (ts : Tables) (g : Goal) :
    (answersOf ts g).val = R001.answersOf ts g := by
  simp only [answersOf, R001.answersOf, bind_val, norm_val, findTable_val, pure_val]
  cases R001.findTable ts g.norm.2 <;> rfl

@[simp] theorem doneOf_val (ts : Tables) (g : Goal) :
    (doneOf ts g).val = R001.doneOf ts g := by
  simp only [doneOf, R001.doneOf, bind_val, norm_val, findTable_val, pure_val]
  cases R001.findTable ts g.norm.2 <;> rfl

/-! ## Kernel steps -/

@[simp] theorem live_val (T : Theory) (s : Span) : (live T s).val = RwLog.live T s := rfl

@[simp] theorem composeLive_val (T : Theory) (x y : Span) :
    (composeLive T x y).val = RwLog.composeLive T x y := by
  simp only [composeLive, RwLog.composeLive, bind_val, Charged.compose]
  cases x.compose y <;> rfl

@[simp] theorem meetLive_val (T : Theory) (x y : Span) :
    (meetLive T x y).val = RwLog.meetLive T x y := by
  simp only [meetLive, RwLog.meetLive, bind_val, Charged.meet]
  cases x.meet y <;> rfl

@[simp] theorem spanAnswer_val (T : Theory) (lb : Option Span) (s : Span) (rb : Option Span) :
    (spanAnswer T lb s rb).val = R001.spanAnswer T lb s rb := by
  unfold spanAnswer R001.spanAnswer
  cases lb with
  | none => cases rb with
    | none => rfl
    | some r =>
      simp only [bind_val, pure_val, Charged.compose, Option.bind]
      cases s.compose r <;> rfl
  | some l =>
    simp only [bind_val, Charged.compose]
    cases l.compose s with
    | none => rfl
    | some s' => cases rb with
      | none => rfl
      | some r =>
        simp only [bind_val, Option.bind]
        cases s'.compose r <;> rfl

@[simp] theorem maxima_val (xs : List Span) : (maxima xs).val = RwLog.maxima xs := by
  simp [maxima, RwLog.maxima, Charged.covers]

@[simp] theorem fresh_val (old cands : List Span) : (fresh old cands).val = RwLog.fresh old cands := by
  simp [fresh, RwLog.fresh, Charged.covers]

/-! ## Pushed goals -/

@[simp] theorem seqPushL_val (g : Goal) (b : Rel) (x : Span) :
    (seqPushL g b x).val = R001.seqPushL g b x := rfl

@[simp] theorem seqPushR_val (g : Goal) (a : Rel) (y : Span) :
    (seqPushR g a y).val = R001.seqPushR g a y := rfl

@[simp] theorem andPush_val (e : Rel) (x : Span) : (andPush e x).val = R001.andPush e x := rfl

@[simp] theorem pushes_val (f : Span → Cost Goal) (xs : List Span) :
    (pushes f xs).val = xs.map fun x => (x, (f x).val) := by
  simp [pushes]

/-! ## Candidates and strategies -/

@[simp] theorem produceStrategies_val (P : Program) (ts : Tables) (g : Goal) :
    (produceStrategies P ts g).val = R001.produce.produceStrategies P ts g := by
  obtain ⟨lb, e, rb⟩ := g
  cases e with
  | seq a b | and a b =>
    simp only [produceStrategies, R001.produce.produceStrategies, bind_val, pure_val, ite_val,
      answersOf_val, doneOf_val, maxima_val, flatMapL_val, composeLive_val, meetLive_val]
    split <;> split <;> simp [*]
  | _ =>
    simp only [produceStrategies, R001.produce.produceStrategies, bind_val, pure_val,
      answersOf_val, flatMapL_val, spanAnswer_val]

@[simp] theorem produce_val (P : Program) (ts : Tables) (g : Goal) (u : Bool × List Span) :
    (produce P ts g u).val =
      (u.2 ++ (R001.produce.produceStrategies P ts g).1, (R001.produce.produceStrategies P ts g).2) := by
  simp only [produce, bind_val, pure_val, produceStrategies_val]

@[simp] theorem tableStrategies_val (P : Program) (ts : Tables) (g : Goal) :
    (tableStrategies P ts g).val = R001.strategies.tableStrategies P ts g := by
  obtain ⟨lb, e, rb⟩ := g
  cases e with
  | seq a b | and a b =>
    simp only [tableStrategies, R001.strategies.tableStrategies, bind_val, pure_val, ite_val,
      answersOf_val, doneOf_val, maxima_val]
    split <;> split <;> simp [*]
  | _ => simp only [tableStrategies, R001.strategies.tableStrategies, pure_val]

@[simp] theorem strategies_val (P : Program) (final : Bool) (ts : Tables) (g : Goal) :
    (strategies P final ts g).val =
      (if final then [[]] else []) ++ R001.strategies.tableStrategies P ts g := by
  simp only [strategies, bind_val, pure_val, tableStrategies_val]

/-! ## Completion -/

theorem gfpFrom_val (ok : List Nat → Nat → Cost Bool) : ∀ (n : Nat) (S : List Nat),
    (gfpFrom ok n S).val = RwLog.gfpFrom (fun S i => (ok S i).val) n S
  | 0, _ => rfl
  | n + 1, S => by
    simp only [gfpFrom, RwLog.gfpFrom, bind_val, filterL_val, ite_val, pure_val, gfpFrom_val ok n]

/-- The charged completion check is R001's, given the oracle's verdicts for
the tables that were not complete at the start of the round. -/
theorem completing_val (P : Program) (d : Nat) (finals : List Bool) (ts ts' : Tables)
    (h : ∀ i, i < ts.length → (ts.getD i ⟨⟨none, .zero, none⟩, [], false⟩).done = false →
      finals.getD i false = unfoldFinal P d (ts.getD i ⟨⟨none, .zero, none⟩, [], false⟩).goal) :
    (completing P finals ts ts').val = R001.completing P d ts ts' := by
  simp only [completing, R001.completing, gfpFrom_val]
  refine gfpFrom_congr
    (p := fun i => i < ts.length ∧ (ts.getD i ⟨⟨none, .zero, none⟩, [], false⟩).done = false)
    (fun S i hi => ?_) _ _ (fun i hi => ?_)
  · simp only [bind_val, strategies_val, anyL_val, allL_val, norm_val, indexOf_val, pure_val,
      h i hi.1 hi.2, R001.strategies]
    rfl
  · have hi' := List.mem_filter.1 hi
    refine ⟨List.mem_range.1 hi'.1, ?_⟩
    have := hi'.2
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    exact this.1

/-! ## One round -/

theorem ite_or {α : Type} (a b : Bool) (x y : α) :
    (if a = true then x else if b = true then x else y) = if (a || b) = true then x else y := by
  cases a <;> cases b <;> rfl

theorem round_val (U : Oracle) (hU : U.Exact) (st : State) : (round U st).val = R001.round st := by
  have hU' : ∀ P d g, (U P d g).val = (unfoldFinal P d g, unfoldAnswers P d g) := hU
  have hout : ∀ t : Table,
      (if t.done = true then (([], []) : List Span × List Goal) else
        ((if t.done = true then ((false, []) : Bool × List Span)
            else (unfoldFinal st.P st.depth t.goal, unfoldAnswers st.P st.depth t.goal)).2 ++
          (produce.produceStrategies st.P st.tables t.goal).1,
        (produce.produceStrategies st.P st.tables t.goal).2)) =
      if t.done = true then ([], []) else R001.produce st.P st.depth st.tables t.goal := by
    intro t; split <;> simp [*, R001.produce]
  simp only [round, R001.round, bind_val, mapL_val, foldL_val, anyL_val, ite_val,
    pure_val, produce_val, fresh_val, norm_val, same_val, hU', map_zip_map_self, hout, ite_or]
  rw [completing_val st.P st.depth]
  · rfl
  · intro i hi hd
    have hd' : (st.tables[i]).done = false := by
      simpa [List.getD_eq_getElem?_getD, hi] using hd
    simp [List.getD_eq_getElem?_getD, hi, hd']

theorem step_val (U : Oracle) (hU : U.Exact) (st : State) : (step U st).val = R001.step st := by
  simp only [step, R001.step, ite_val, pure_val, bind_val, round_val U hU]

/-- With an oracle that computes R001's unfolding race, the charged tabled
machine is R001: the same states, the same initial state, the same step. -/
theorem machine_runtime (U : Oracle) (hU : U.Exact) : (machine U).runtime = R001.runtime := by
  have hstep : (fun s => (step U s).val) = R001.step := funext (step_val U hU)
  show (⟨State, fun P q => StateOf.ofGoal P ⟨none, q, none⟩, fun s => (step U s).val⟩ : Runtime) = _
  rw [hstep]; rfl

/-- The tabled machine pays the size of the query to build its first state:
what it has paid is that and what its steps spent. -/
theorem paid_eq (U : Oracle) (P : Program) (q : Rel) (n : Nat) :
    (machine U).paid P q n = q.size + (machine U).spent ((machine U).start P q) n := by
  show goalSize ⟨none, q, none⟩ + 0 + _ = _
  simp [goalSize]

end Tabled

end RwLog
