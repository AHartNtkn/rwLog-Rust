/-
# Rung R001: what must be proved

Every property the proper baseline must have is stated here as a `Prop`
named in the `R001.Obligation` namespace. Nothing in this file is proved: an
obligation is discharged by a theorem `R001.<name> : Obligation.<name>` in
another file, and `AxiomAudit.lean` lists the discharged ones. Stating them
as definitions keeps them checked by Lean (they must typecheck against the
frozen engine in `Engine.lean`) without adding `sorry` anywhere.

Grouping, with the property names of the execution-properties doc:

* `Kernel`: matching, coverage and refutation checks the engine relies on.
* Tier 0 (P0.1 to P0.3) and P3.0: soundness, completeness up to refutation,
  honest exhaustion, derivation-general answers.
* Termination: the exact termination class (`Cert`), tabling termination
  (P2.1), boundary pushing in fixed modes (addition), containment of rung
  zero's class, empty-side and finite-side termination (P1.2, P1.3).
* Order and direction: `|` order (P1.1, step for step), converse and mirrored
  program (P1.4 strong, step for step).
* Constraints: more refutation rules never break termination and only remove
  answers (P2.3), and refuted spans never enter a table (P2.4).
* Answer quality: no answer covered by an earlier one (P3.1, P3.2), finitely
  many answers on terminating queries (P3.3).

"Step for step" is up to the order of answers inside one step and up to
equivalent answers (`TraceEquiv`): a step emits a set of answers, and the
machine keeps one representative of each class of equivalent answers.
-/
import RwLog.Rungs.R001.Engine
import RwLog.Rungs.R000.Engine

namespace RwLog

namespace R001

/-! ## Notions the statements use -/

/-- The run of the machine started on a single goal. -/
def GoalTerminates (P : Program) (g : Goal) : Prop :=
  ∃ n, (runtime.run (State.ofGoal P g) n).2 = true

/-- The state after `n` steps (a finished state stays put). -/
def stateAfter (st : State) : Nat → State
  | 0 => st
  | n + 1 =>
    match step st with
    | .emit _ st' => stateAfter st' n
    | .done => st

/-- Two answer lists of one step agree up to order and equivalent answers. -/
def StepEquiv (xs ys : List Span) : Prop :=
  ∃ ys', ys'.Perm ys ∧ List.Forall₂ Span.Equiv xs ys'

/-- Two traces agree step for step, up to `StepEquiv`. -/
def TraceEquiv (t t' : List (List Span)) : Prop := List.Forall₂ StepEquiv t t'

/-- The goals a goal reads directly, whatever its strategy. -/
def directGoals (P : Program) (g : Goal) : List Goal :=
  match g.e with
  | .zero => []
  | .span _ => []
  | .or a b => [⟨g.lb, a, g.rb⟩, ⟨g.lb, b, g.rb⟩]
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
  | orl {g : Goal} {a b : Rel} {x : Span} :
      g.e = .or a b → GDerives P ⟨g.lb, a, g.rb⟩ x → GDerives P g x
  | orr {g : Goal} {a b : Rel} {x : Span} :
      g.e = .or a b → GDerives P ⟨g.lb, b, g.rb⟩ x → GDerives P g x
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

/-- `F` is a finite cover of the goal's derivable answers by derivable
answers, up to the theory. -/
def CoverBy (P : Program) (g : Goal) (F : List Span) : Prop :=
  (∀ f ∈ F, GDerives P g f) ∧
    ∀ s, GDerives P g s → s.Dead P.theory ∨ ∃ f ∈ F, f.CoversLive P.theory s

def FiniteCover (P : Program) (g : Goal) : Prop := ∃ F, CoverBy P g F

/-! ### Termination certificates

A certificate lists finitely many goals, each with a finite cover of its
answers and a rank. Each goal either unfolds to a call-free normal form (the
unfolding strategy) or picks one strategy whose goals are listed;
a push may only use a finished side of strictly lower rank, while the other
dependencies, which may be mutually recursive, need rank no higher. The
machine terminates exactly on the queries that have a certificate
(`Obligation.terminates_iff_cert`), so this is R001's termination class,
stated without reference to the machine's state. -/

structure CertEntry where
  goal : Goal
  cover : List Span
  rank : Nat

/-- The cover a certificate gives a goal (converses read through). -/
def certCover (C : List CertEntry) (g : Goal) : List Span :=
  let n := g.norm
  match C.find? (fun e => e.goal.same n.2) with
  | some e => orient n.1 e.cover
  | none => []

/-- The strategies of a goal, as in `strategies`, with each dependency marked
`true` when it must be finished first (strictly lower rank). -/
def certStrategies (P : Program) (C : List CertEntry) (g : Goal) : List (List (Goal × Bool)) :=
  match g.e with
  | .zero => [[]]
  | .span _ => [[]]
  | .or a b => [[(⟨g.lb, a, g.rb⟩, false), (⟨g.lb, b, g.rb⟩, false)]]
  | .call n => [[(callGoal P g n, false)]]
  | .conv a => [[(convGoal g a, false)]]
  | .seq a b =>
    let L := seqLeft g a
    let R := seqRight g b
    [[(L, false), (R, false)],
     (L, true) :: (maxima (certCover C L)).map fun x => (seqPushL g b x, false),
     (R, true) :: (maxima (certCover C R)).map fun y => (seqPushR g a y, false)]
  | .and a b =>
    let L := andLeft g a
    let R := andRight g b
    [[(L, false), (R, false)],
     (L, true) :: (maxima (certCover C L)).map fun x => (andPush b x, false),
     (R, true) :: (maxima (certCover C R)).map fun y => (andPush a y, false)]

def Cert.Valid (P : Program) (C : List CertEntry) (root : Goal) : Prop :=
  (∃ e ∈ C, e.goal.same root.norm.2 = true) ∧
  ∀ e ∈ C, CoverBy P e.goal e.cover ∧
    ((∃ d, unfoldFinal P d e.goal = true) ∨
      ∃ st ∈ certStrategies P C e.goal, ∀ d ∈ st, ∃ e' ∈ C, e'.goal.same d.1.norm.2 = true ∧
        (if d.2 then e'.rank < e.rank else e'.rank ≤ e.rank))

/-! ### The addition program, for the fixed-mode termination statement -/

namespace Examples

def num : Nat → Pat
  | 0 => .sym "z"
  | n + 1 => Term.mk "s" [num n]

/-- `rel add { (cons z $y) -> $y | [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)] }` -/
def add : Rel :=
  .or (.rw (Term.mk "cons" [.sym "z", .var 0]) (.var 0))
    (.seq (.rw (Term.mk "cons" [Term.mk "s" [.var 0], .var 1]) (Term.mk "cons" [.var 0, .var 1]))
      (.seq (.call "add") (.rw (.var 0) (Term.mk "s" [.var 0]))))

def addProg : Program := ⟨[("add", add)], []⟩

end Examples

/-! ## The obligations -/

namespace Obligation

/-! ### Kernel -/

/-- The coverage check decides `Span.Covers` (this uses that the signature
is infinite). -/
def covers_iff : Prop := ∀ a s : Span, a.covers? s = true ↔ a.Covers s

/-- Symbolic refutation is sound for every ground instance. -/
def refutes_sound : Prop :=
  ∀ (T : Theory) (c : Store), T.refutes? c = true → ∀ σ : Nat → GTerm, Refutes T (c.at σ)

/-- Symbolic refutation is monotone: in the theory, under instantiation, and
under adding constraints. -/
def refutes_mono : Prop :=
  ∀ (T T' : Theory) (c c' : Store) (θ : Nat → Pat),
    (∀ ρ ∈ T', ρ.WellFormed) → (∀ ρ ∈ T, ρ ∈ T') → (∀ a ∈ c, a.bind θ ∈ c') →
    T.refutes? c = true → T'.refutes? c' = true

/-- The firing budget is enough: a symbolic refutation that exists is found. -/
def refutes_complete_symbolic : Prop :=
  ∀ (T : Theory) (c : Store) (n : Nat), (∀ ρ ∈ T, ρ.WellFormed) →
    T.refutesWithin n c = true → T.refutes? c = true

/-- Simplification is exact: a dropped span is dead, and a kept span refines
the original, so up to the theory it loses only refuted instances. -/
def simplify_exact : Prop :=
  ∀ (T : Theory) (s : Span), (∀ ρ ∈ T, ρ.WellFormed) →
    (T.simplify s = none → s.Dead T) ∧ (∀ s', T.simplify s = some s' → s'.Refines T s)

/-- Simplification runs to the end: a simplified span has no symbolic
refutation, no symbolic firing that forces an equation however many firings
are taken, and no atom with a sole firing left. So the budgets are enough. -/
def simplify_stable : Prop :=
  ∀ (T : Theory) (s s' : Span) (n : Nat), (∀ ρ ∈ T, ρ.WellFormed) → T.simplify s = some s' →
    T.refutesWithin n s'.c = false ∧ T.bindWithin n s'.c = none ∧ T.drop? s'.c = none

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
def tablesAt (P : Program) (g : Goal) (n : Nat) : Tables := (stateAfter (State.ofGoal P g) n).tables

/-- Every answer of a table is, up to the theory, a derivable answer of its
goal. -/
def table_sound : Prop :=
  ∀ P g, (∀ ρ ∈ P.theory, ρ.WellFormed) → ∀ n, ∀ t ∈ tablesAt P g n, ∀ a ∈ t.answers,
    ∃ y, GDerives P t.goal y ∧ a.CoversLive P.theory y ∧ y.CoversLive P.theory a

/-- A complete table covers every derivable answer of its goal that is not
dead. -/
def completion_sound : Prop :=
  ∀ P g, (∀ ρ ∈ P.theory, ρ.WellFormed) → ∀ n, ∀ t ∈ tablesAt P g n, t.done = true →
    ∀ s, GDerives P t.goal s → s.Dead P.theory ∨ ∃ a ∈ t.answers, a.CoversLive P.theory s

/-- Every derivable answer of a table's goal that is not dead is eventually
covered by that table. -/
def table_fair : Prop :=
  ∀ P g, (∀ ρ ∈ P.theory, ρ.WellFormed) → ∀ n, ∀ t ∈ tablesAt P g n,
    ∀ s, GDerives P t.goal s → s.Dead P.theory ∨
      ∃ m, ∃ t' ∈ tablesAt P g m, t'.goal = t.goal ∧ ∃ a ∈ t'.answers, a.CoversLive P.theory s

/-- Goals that share a table derive the same answers up to the theory. -/
def gderives_same : Prop :=
  ∀ P (g h : Goal), (∀ ρ ∈ P.theory, ρ.WellFormed) → g.same h = true →
    ∀ y, GDerives P g y → ∃ y', GDerives P h y' ∧ y'.CoversLive P.theory y ∧ y.CoversLive P.theory y'

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

/-! ### Termination -/

/-- The termination class, exactly: the machine halts on a query iff the
query has a termination certificate. -/
def terminates_iff_cert : Prop :=
  ∀ P q, P.WellFormed q →
    (runtime.Terminates P q ↔ ∃ C, Cert.Valid P C ⟨none, q, none⟩)

/-- P2.1: if only finitely many goals can arise (up to equivalent
boundaries) and each has finitely many answers up to coverage, the machine
halts. -/
def tabling_termination : Prop :=
  ∀ P q, P.WellFormed q →
    (∃ Gs : List Goal, ∀ g, Reach P ⟨none, q, none⟩ g → ∃ h ∈ Gs, h.same g.norm.2 = true) →
    (∀ g, Reach P ⟨none, q, none⟩ g → FiniteCover P g) →
    runtime.Terminates P q

/-- R001 halts wherever rung zero does (`FinitelyNormalising` contains
`CallTreeFinite` and `RecursionFree`). -/
def terminates_finitelyNormalising : Prop := runtime.TerminatesOn R000.FinitelyNormalising

/-- Boundary pushing: addition halts in both fixed modes, forwards from a
ground pair and backwards from a ground sum. -/
def addition_fixed_modes : Prop :=
  ∀ n m k : Nat,
    runtime.Terminates Examples.addProg
      (.seq (.at_ (Term.mk "cons" [Examples.num n, Examples.num m])) (.call "add")) ∧
    runtime.Terminates Examples.addProg (.seq (.call "add") (.at_ (Examples.num k)))

/-- P1.2: a side that fails finitely makes `;` and `&` fail finitely, on
either side and whatever the other side does. -/
def empty_side : Prop :=
  ∀ P (a b : Rel), P.WellFormed (.seq a b) →
    runtime.Terminates P a → runtime.Answers P a = ∅ →
    runtime.Terminates P (.seq a b) ∧ runtime.Terminates P (.seq b a) ∧
    runtime.Terminates P (.and a b) ∧ runtime.Terminates P (.and b a)

/-- P1.3 for `;`, left side finite: if `a` halts and `b` halts under the
interface of each answer of `a`, then `a ; b` halts. -/
def finite_side_seq_left : Prop :=
  ∀ P (a b : Rel), P.WellFormed (.seq a b) → runtime.Terminates P a →
    (∀ x ∈ runtime.Answers P a, GoalTerminates P ⟨bound x.rightIface, b, none⟩) →
    runtime.Terminates P (.seq a b)

/-- P1.3 for `;`, right side finite (the mirror image). -/
def finite_side_seq_right : Prop :=
  ∀ P (a b : Rel), P.WellFormed (.seq a b) → runtime.Terminates P b →
    (∀ y ∈ runtime.Answers P b, GoalTerminates P ⟨none, a, bound y.leftIface⟩) →
    runtime.Terminates P (.seq a b)

/-- P1.3 for `&`: if `a` halts and `b` halts restricted to the input and
output shape of each answer of `a`, then `a & b` and `b & a` halt. -/
def finite_side_and : Prop :=
  ∀ P (a b : Rel), P.WellFormed (.and a b) → runtime.Terminates P a →
    (∀ x ∈ runtime.Answers P a, GoalTerminates P (andPush b x)) →
    runtime.Terminates P (.and a b) ∧ runtime.Terminates P (.and b a)

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

/-- P1.4 strong, for the mirrored program: running the mirror image of a
query in the mirrored program is the mirror image of the run, step for step. -/
def dual_trace : Prop :=
  ∀ P q n, TraceEquiv (runtime.trace (runtime.init P.dual q.dual) n)
    ((runtime.trace (runtime.init P q) n).map (·.map Span.swap))

/-! ### Constraints -/

/-- P2.3: adding refutation rules never turns a halting query into a
diverging one. -/
def theory_mono_terminates : Prop :=
  ∀ P (T : Theory) q, P.WellFormed q → (∀ ρ ∈ T, ρ.WellFormed) → (∀ ρ ∈ P.theory, ρ ∈ T) →
    runtime.Terminates P q → runtime.Terminates { P with theory := T } q

/-- P2.3: adding rules only removes answers: each answer under the larger
theory is covered, on its instances the larger theory cannot refute, by an
answer under the smaller one. (The larger theory may force more equations, so
its answers can be instances of the smaller theory's.) -/
def theory_mono_answers : Prop :=
  ∀ P (T : Theory) q, P.WellFormed q → (∀ ρ ∈ T, ρ.WellFormed) → (∀ ρ ∈ P.theory, ρ ∈ T) →
    ∀ a ∈ runtime.Answers { P with theory := T } q, ∃ b ∈ runtime.Answers P q, b.CoversLive T a

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

/-- P3.3 within the termination class: a halting query has finitely many
answers. -/
def finite_answers : Prop :=
  ∀ P q, P.WellFormed q → runtime.Terminates P q → (runtime.Answers P q).Finite

end Obligation

end R001

end RwLog
