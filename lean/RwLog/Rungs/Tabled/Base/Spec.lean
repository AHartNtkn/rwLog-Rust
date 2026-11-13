/-
# The tabled machine (R001): what is stated of it

The tabled machine is rung R001 of epoch 1, the proper baseline, and its
declarations keep the namespace `R001`. Each property is a `Prop` in
`R001.Obligation`, discharged by a theorem `R001.<name> : Obligation.<name>`
under `Proofs/`; `AxiomAudit.lean` lists them.

Master keeps the statements the shared libraries use, each with its proof:

* `Kernel`: coverage, interfaces, refutation and simplification as the
  machine relies on them, and boundary lifting.
* Tier 0 (P0.1 to P0.3) and P3.0: soundness, completeness up to refutation,
  honest exhaustion, derivation-general answers.
* Tables: sound, sound on completion, fair, and shared between goals that
  derive the same.
* Order and direction: `|` order and the converse, step for step and exactly.
* Constraints: more rules only remove answers (P2.3), and refuted spans never
  enter a table (P2.4).
* Answer quality: no answer covered by an earlier one (P3.1, P3.2).

R001's termination class (certificates), tabling termination, the fixed
modes of addition, empty and finite sides, the trace of the mirror image and
`R001.keeps` are stated and proved at the tag `epoch-1` (`lean/EPOCH1.md`),
not here.
-/
import RwLog.Rungs.Tabled.Base.Engine
import RwLog.Rungs.Naive.Engine
import RwLog.SpanLayer.Coverage
import RwLog.Rungs.Framework.Trace
import RwLog.Trusted.Properties

namespace RwLog

namespace R001

/-! ## Notions the statements use -/

/-- The run of the machine started on a single goal. -/
def GoalTerminates (P : Program) (g : Goal) : Prop :=
  ∃ n, (runtime.run (StateOf.ofGoal P g) n).2 = true

/-- The state after `n` steps (a finished state stays put). -/
def stateAfter (st : State) : Nat → State
  | 0 => st
  | n + 1 =>
    match step st with
    | .emit _ st' => stateAfter st' n
    | .done => st

/-- The goals a goal reads directly, whatever its strategy. -/
def directGoals (P : Program) (g : Goal) : List Goal :=
  match g.e with
  | .zero => []
  | .span _ => []
  | .or a b => orLeaves g a b
  | .call n => [callGoal P g n]
  | .conv a => [convGoal g a]
  | .seq a b => [seqLeft g a, seqRight g b]
  | .and a b => [andLeft g a, andRight g b]

/-- The answers the machine can derive for a goal: everything its strategies
compute from derivable answers of the goals they read, keeping only spans
the theory does not refute. Tables only ever hold such answers. -/
inductive GDerives (P : Program) : Goal → Span → Prop
  | unfold {g : Goal} {d : Nat} {x : Span} :
      x ∈ unfoldAnswers P d g → GDerives P g x
  | span {lb rb : Option Span} {s x : Span} :
      x ∈ spanAnswer P.theory lb s rb → GDerives P ⟨lb, .span s, rb⟩ x
  | or {g : Goal} {a b : Rel} {h : Goal} {x : Span} :
      g.e = .or a b → h ∈ orLeaves g a b → GDerives P h x → GDerives P g x
  | call {g : Goal} {n : Name} {x : Span} :
      g.e = .call n → GDerives P (callGoal P g n) x → GDerives P g x
  | conv {g : Goal} {a : Rel} {x : Span} :
      g.e = .conv a → GDerives P (convGoal g a) x → GDerives P g x.swap
  | seq {g : Goal} {a b : Rel} {x y z : Span} :
      g.e = .seq a b → GDerives P (seqLeft g a) x → GDerives P (seqRight g b) y →
      z ∈ composeLive P.theory x y → GDerives P g z
  | seqPushL {g : Goal} {a b : Rel} {x y z : Span} :
      g.e = .seq a b → GDerives P (seqLeft g a) x → GDerives P (seqPushL g b x) y →
      z ∈ composeLive P.theory x y → GDerives P g z
  | seqPushR {g : Goal} {a b : Rel} {x y z : Span} :
      g.e = .seq a b → GDerives P (seqRight g b) y → GDerives P (seqPushR g a y) x →
      z ∈ composeLive P.theory x y → GDerives P g z
  | and {g : Goal} {a b : Rel} {x y z : Span} :
      g.e = .and a b → GDerives P (andLeft g a) x → GDerives P (andRight g b) y →
      z ∈ meetLive P.theory x y → GDerives P g z
  | andPushL {g : Goal} {a b : Rel} {x y z : Span} :
      g.e = .and a b → GDerives P (andLeft g a) x → GDerives P (andPush b x) y →
      z ∈ meetLive P.theory x y → GDerives P g z
  | andPushR {g : Goal} {a b : Rel} {x y z : Span} :
      g.e = .and a b → GDerives P (andRight g b) y → GDerives P (andPush a y) x →
      z ∈ meetLive P.theory x y → GDerives P g z

/-- The goals the machine may ever create from a root: those read directly,
and those a push may run for any derivable answer of a finished side. -/
inductive Reach (P : Program) (root : Goal) : Goal → Prop
  | root : Reach P root root
  | direct {g d : Goal} : Reach P root g → d ∈ directGoals P g → Reach P root d
  | seqPushL {g : Goal} {a b : Rel} {x : Span} :
      Reach P root g → g.e = .seq a b → GDerives P (seqLeft g a) x → Reach P root (seqPushL g b x)
  | seqPushR {g : Goal} {a b : Rel} {y : Span} :
      Reach P root g → g.e = .seq a b → GDerives P (seqRight g b) y → Reach P root (seqPushR g a y)
  | andPushL {g : Goal} {a b : Rel} {x : Span} :
      Reach P root g → g.e = .and a b → GDerives P (andLeft g a) x → Reach P root (andPush b x)
  | andPushR {g : Goal} {a b : Rel} {y : Span} :
      Reach P root g → g.e = .and a b → GDerives P (andRight g b) y → Reach P root (andPush a y)

/-- A goal's boundaries are interfaces: each is diagonal (`l = r`) and its
store mentions only variables of `l`. The root goal `⟨none, q, none⟩` and
every pushed goal have this form. -/
def GoalOf.Interfaced (g : Goal) : Prop :=
  ∀ b ∈ g.lb.toList ++ g.rb.toList, b.l = b.r ∧ ∀ c ∈ b.c, ∀ v ∈ c.vars, v ∈ b.l.vars

/-! ## The obligations -/

namespace Obligation

/-! ### Kernel -/

/-- The coverage check decides `Span.Covers` (this uses that the signature
is infinite). -/
def covers_iff : Prop := ∀ a s : Span, a.covers? s = true ↔ a.Covers s

/-- Symbolic refutation is sound: no model of the theory contains any ground
instance of a refuted store. -/
def refutes_sound : Prop :=
  ∀ (T : Theory) (c : Store), (∀ ρ ∈ T, ρ.WellFormed) → T.refutes? c = true →
    ∀ (σ : Nat → GTerm) (M : Interp), T.Model M → ¬ ∀ x ∈ c, x.bind σ ∈ M

/-- Simplification is exact: a dropped span is dead, and a kept span relates
the same pairs as the original in every model of the theory. -/
def simplify_exact : Prop :=
  ∀ (T : Theory) (s : Span), (∀ ρ ∈ T, ρ.WellFormed) →
    (T.simplify s = none → s.Dead T) ∧ (∀ s', T.simplify s = some s' → s'.Refines T s)

/-- Simplification runs to the end: a simplified span has no refutation and
no forced equation left. So the instantiation budget is enough. -/
def simplify_stable : Prop :=
  ∀ (T : Theory) (s s' : Span), (∀ ρ ∈ T, ρ.WellFormed) → T.simplify s = some s' →
    T.refutes? s'.c = false ∧ T.bind? s'.c = none

/-- Showing an answer keeps its meaning: the shown answer relates the same
pairs as the answer in every model of the theory. -/
def present_exact : Prop :=
  ∀ (T : Theory) (s : Span), (∀ ρ ∈ T, ρ.WellFormed) → (T.present s).Refines T s

/-- Simplification keeps coverage and commutes with composition and
intersection, for every theory. The closure only adds atoms, so whatever it
derives from a store it derives from every instance of the store and every
larger store: if `f` covers `x` and `x` is not refuted, `f` is not refuted,
and the equations it forces hold in the simplified `x`. -/
def simplify_mono : Prop :=
  ∀ T : Theory, (∀ ρ ∈ T, ρ.WellFormed) →
    (∀ f x : Span, f.Covers x →
      T.simplify x = none ∨
        ∃ f' x', T.simplify f = some f' ∧ T.simplify x = some x' ∧ f'.Covers x') ∧
    (∀ s t : Span,
      Option.Rel Span.Equiv (((T.simplify t).bind s.compose).bind T.simplify)
        ((s.compose t).bind T.simplify) ∧
      Option.Rel Span.Equiv (((T.simplify s).bind (·.compose t)).bind T.simplify)
        ((s.compose t).bind T.simplify) ∧
      Option.Rel Span.Equiv (((T.simplify t).bind s.meet).bind T.simplify)
        ((s.meet t).bind T.simplify) ∧
      Option.Rel Span.Equiv (((T.simplify s).bind (·.meet t)).bind T.simplify)
        ((s.meet t).bind T.simplify))

/-- Interfaces are exact: `s ; s.rightIface = s` and `s.leftIface ; s = s`,
and a trivial interface is the identity. -/
def iface_exact : Prop :=
  ∀ s : Span, (s.den).comp s.rightIface.den = s.den ∧ (s.leftIface.den).comp s.den = s.den ∧
    (bound s.rightIface = none → s.rightIface.den = GRel.id) ∧
    (bound s.leftIface = none → s.leftIface.den = GRel.id)

/-- Equivalent answers have equivalent interfaces, so pushes from equivalent
answers reach the same table. -/
def iface_equiv : Prop :=
  ∀ x y : Span, x.Equiv y →
    boundEq (bound x.rightIface) (bound y.rightIface) = true ∧
    boundEq (bound x.leftIface) (bound y.leftIface) = true

/-- The mirrored program denotes the converse. -/
def denote_dual : Prop := ∀ (P : Program) (e : Rel), P.dual.sem e.dual = (P.sem e).inv

/-- Boundary lifting, the lemma most of the engine proofs share: what a
goal with interface boundaries (sub-identities, `l = r`) derives is, on
unrefuted instances and for spans that are not dead, the boundaries composed
with what the goal without boundaries derives. -/
def boundary_lifting : Prop :=
  ∀ (P : Program) (g : Goal), (∀ ρ ∈ P.theory, ρ.WellFormed) →
    (∀ b ∈ g.lb.toList ++ g.rb.toList, b.l = b.r) →
    (∀ y, GDerives P g y → ¬ y.Dead P.theory → ∃ y₀, GDerives P ⟨none, g.e, none⟩ y₀ ∧
      ∃ z ∈ spanAnswer P.theory g.lb y₀ g.rb, z.CoversLive P.theory y ∧ y.CoversLive P.theory z) ∧
    (∀ y₀, GDerives P ⟨none, g.e, none⟩ y₀ → ∀ z ∈ spanAnswer P.theory g.lb y₀ g.rb,
      ¬ z.Dead P.theory → ∃ y, GDerives P g y ∧ y.CoversLive P.theory z)

/-! ### Table invariants

Owned by the Tier 0 group and shared with the termination group: they hold
for every table of a run started from any goal. -/

/-- The tables after `n` rounds of the run started on `g`. -/
def tablesAt (P : Program) (g : Goal) (n : Nat) : Tables := (stateAfter (StateOf.ofGoal P g) n).tables

/-- Every answer of a table that is not dead is, up to the theory, a derivable
answer of its goal. (A dead answer the engine could not refute can be read
across a shared table into a goal whose derivations are all refuted.) -/
def table_sound : Prop :=
  ∀ P g, (∀ ρ ∈ P.theory, ρ.WellFormed) → g.Interfaced → ∀ n, ∀ t ∈ tablesAt P g n, ∀ a ∈ t.answers,
    a.Dead P.theory ∨ ∃ y, GDerives P t.goal y ∧ a.CoversLive P.theory y ∧ y.CoversLive P.theory a

/-- A complete table covers every derivable answer of its goal that is not
dead. -/
def completion_sound : Prop :=
  ∀ P g, (∀ ρ ∈ P.theory, ρ.WellFormed) → g.Interfaced → ∀ n, ∀ t ∈ tablesAt P g n, t.done = true →
    ∀ s, GDerives P t.goal s → s.Dead P.theory ∨ ∃ a ∈ t.answers, a.CoversLive P.theory s

/-- The tables after `m` rounds run unconditionally from `g`, whether or not
the root has completed. -/
def roundsAt (P : Program) (g : Goal) (m : Nat) : Tables :=
  ((fun st => (round st).1)^[m] (StateOf.ofGoal P g)).tables

/-- Every derivable answer of a table's goal that is not dead is eventually
covered by that table, if rounds keep running. A run stops once the root
completes, which can leave a table the root did not wait on unfinished: from
`call nat ; 0` the root completes by unfolding while the `call nat` table has
no answers. -/
def table_fair : Prop :=
  ∀ P g, (∀ ρ ∈ P.theory, ρ.WellFormed) → g.Interfaced → ∀ n, ∀ t ∈ tablesAt P g n,
    ∀ s, GDerives P t.goal s → s.Dead P.theory ∨
      ∃ m, ∃ t' ∈ roundsAt P g m, t'.goal = t.goal ∧ ∃ a ∈ t'.answers, a.CoversLive P.theory s

/-- Goals that share a table derive the same answers up to the theory, apart
from dead ones. -/
def gderives_same : Prop :=
  ∀ P (g h : Goal), (∀ ρ ∈ P.theory, ρ.WellFormed) → g.Interfaced → g.same h = true →
    ∀ y, GDerives P g y → y.Dead P.theory ∨
      ∃ y', GDerives P h y' ∧ y'.CoversLive P.theory y ∧ y.CoversLive P.theory y'

/-! ### Tier 0 and P3.0 -/

/-- P0.1: every emitted answer denotes only triples of the query. -/
def sound : Prop := runtime.Sound

/-- P0.2: every derivable span is covered by an emitted answer, unless every
instance of it is refuted. -/
def complete : Prop := runtime.Complete

/-- P0.3: on halting, the emitted answers are equivalent to the query. -/
def honest_exhaustion : Prop := runtime.HonestExhaustion

/-- P3.0: every emitted answer refines the span of one derivation: it is
that span, instantiated only by equations the theory forces, so it keeps every
unrefuted instance and no answer is less general than its derivation. -/
def derivation_general : Prop :=
  ∀ P q, P.WellFormed q → ∀ a ∈ runtime.Answers P q, ∃ s, Derives P q s ∧ a.Refines P.theory s

/-! ### Order and direction -/

/-- P1.1, exactly: swapping the branches of `|` does not change the run. -/
def or_comm_trace : Prop :=
  ∀ P (a b : Rel) n, runtime.trace (runtime.init P (.or a b)) n =
    runtime.trace (runtime.init P (.or b a)) n

/-- P1.1 for regrouping `|`, exactly: regrouping does not change the run. -/
def or_assoc : Prop :=
  ∀ P (a b c : Rel) n, runtime.trace (runtime.init P (.or (.or a b) c)) n =
    runtime.trace (runtime.init P (.or a (.or b c))) n

/-- P1.4 strong, for the converse: running `conv q` is running `q` with every
answer swapped, step for step and exactly. -/
def conv_trace : Prop :=
  ∀ P q n, runtime.trace (runtime.init P (.conv q)) n =
    (runtime.trace (runtime.init P q) n).map (·.map Span.swap)

/-! ### Constraints -/

/- P2.3 asked also that adding rules never turns a halting query into a
diverging one. A larger theory refutes more and forces more equations, and
both are monotone, but an instantiated answer can stop covering a later
candidate that the smaller theory's answer covered, so this is open
(`/mnt/project-files/r001/constraint-redesign-notes.md`). -/

/-- P2.3: adding rules only removes answers: in every model of the larger
theory, each answer under it relates only pairs that one answer under the
smaller theory relates, unless it relates nothing in any such model. (Every
model of the larger theory is a model of the smaller one.) -/
def theory_mono_answers : Prop :=
  ∀ P (T : Theory) q, P.WellFormed q → (∀ ρ ∈ T, ρ.WellFormed) → (∀ ρ ∈ P.theory, ρ ∈ T) →
    ∀ a ∈ runtime.Answers { P with theory := T } q,
      a.Dead T ∨ ∃ b ∈ runtime.Answers P q, b.CoversLive T a

/-- P2.4: refuted spans are cut at once. No table of any reachable state
holds an answer, or has a boundary, whose store the theory refutes, so no
work is ever done under a refuted span. -/
def prompt_pruning : Prop :=
  ∀ P q, P.WellFormed q → ∀ n, ∀ t ∈ (stateAfter (runtime.init P q) n).tables,
    (∀ a ∈ t.answers, P.theory.refutes? a.c = false) ∧
    (∀ b ∈ t.goal.lb.toList ++ t.goal.rb.toList, P.theory.refutes? b.c = false)

/-! ### Answer quality -/

/-- P3.1 and P3.2: no emitted answer is covered by an earlier one (so in
particular none is emitted twice, even up to renaming). -/
def no_subsumed : Prop :=
  ∀ P q, P.WellFormed q → ∀ n,
    (runtime.emitted (runtime.init P q) n).Pairwise fun a b => ¬ a.Covers b

end Obligation

end R001

end RwLog
