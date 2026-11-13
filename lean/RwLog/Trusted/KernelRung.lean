/-
# Kernel rungs: kernels whose charges are derived

`Kernel.std` (`Trusted/Kernel.lean`) says what each operation on spans
*returns*. It is the specification kernel: its spans are trees, and what it
charges is a formula somebody wrote down.

A *kernel rung* is a kernel on the base machine (`Trusted/Base.lean`). Its
spans are pointers into the store (`MSpan`), its operations on terms are
programs written for every machine (`KernelProg`), and it comes with a proof
that each program returns what the specification kernel returns, read through
the store (`TermOps.Refines`). What an operation costs is then what its
program spends on the machine of the language. Nobody states it: a bound on it
is a theorem, and a kernel rung with a better representation of terms is
credited with exactly what it saves.

`Engine.costedOn K` is an engine run on the kernel rung `K`: the program is
loaded into the store, one tick a node, the engine runs at `K`'s kernel, and
each answer is read back through the store. Reading an answer back is not
charged: the answer the machine gives is the pointer.

## What is still postulated

The two operations that involve a constraint store in an essential way,
simplifying a span by a theory and a coverage test whose covering span has
constraints, are not programs yet. `Mach.simplifyInterim` and
`Mach.coversInterim` compute them on the terms read from the store and charge
what `Trusted/Charged.lean` charges. They are deleted when the constraint
operations are derived (roadmap ledger L39).
-/
import RwLog.Trusted.Base
import RwLog.Trusted.Cost

namespace RwLog

/-! ## Spans and expressions in a store -/

/-- A span whose terms are pointers. -/
structure MSpan (P : Type) where
  l : P
  r : P
  c : List P
  deriving DecidableEq, Repr

/-- Replace the spans of an expression. -/
def RelOf.mapSpan {S T : Type} (f : S → T) : RelOf S → RelOf T
  | .zero => .zero
  | .span s => .span (f s)
  | .or a b => .or (a.mapSpan f) (b.mapSpan f)
  | .and a b => .and (a.mapSpan f) (b.mapSpan f)
  | .seq a b => .seq (a.mapSpan f) (b.mapSpan f)
  | .conv a => .conv (a.mapSpan f)
  | .call n => .call n

/-- The spans of an expression. -/
def RelOf.spans {S : Type} : RelOf S → List S
  | .zero => []
  | .span s => [s]
  | .or a b => a.spans ++ b.spans
  | .and a b => a.spans ++ b.spans
  | .seq a b => a.spans ++ b.spans
  | .conv a => a.spans
  | .call _ => []

namespace MSpan

/-- The span a span of pointers stands for. -/
def read (h : Heap) (s : MSpan Nat) : Span := ⟨h.tm s.l, h.tm s.r, s.c.map h.tm⟩

/-- Every pointer of the span is in the store. -/
def In (h : Heap) (s : MSpan Nat) : Prop := s.l < h.size ∧ s.r < h.size ∧ ∀ p ∈ s.c, p < h.size

end MSpan

/-- The store `h'` is `h` with nodes added. -/
def Heap.le (h h' : Heap) : Prop := h.cells <+: h'.cells

/-- `m`, run from `h`, finishes; the store it leaves is `h` with nodes added,
and its result satisfies `R` there. -/
def Mach.Returns {α : Type} (m : Mach α) (h : Heap) (R : Heap → α → Prop) : Prop :=
  ∃ r, m h = some r ∧ h.le r.val.2 ∧ R r.val.2 r.val.1

/-! ## The operations on terms, as programs -/

/-- The operations of a kernel that only involve terms, for pointers `P` in a
monad `M`. `coversPlain` is the coverage test for a covering span without
constraints. -/
structure TermOps (P : Type) (M : Type → Type) where
  compose : MSpan P → MSpan P → M (Option (MSpan P))
  meet : MSpan P → MSpan P → M (Option (MSpan P))
  composable : List (MSpan P) → M Bool
  coversPlain : MSpan P → MSpan P → M Bool
  eq : MSpan P → MSpan P → M Bool
  eqRel : RelOf (MSpan P) → RelOf (MSpan P) → M Bool
  canon : RelOf (MSpan P) → M (RelOf (MSpan P))
  rightBound : MSpan P → M (Option (MSpan P))
  leftBound : MSpan P → M (Option (MSpan P))

/-- The operations on terms written for every machine. They can only spend
what the machine charges. -/
structure KernelProg where
  ops : {P V F : Type} → {M : Type → Type} → [Base P V F M] → TermOps P M

/-- A result that may be missing is the given span, read through the store. -/
def MSpan.ReadsO (h : Heap) (r : Option (MSpan Nat)) (v : Option Span) : Prop :=
  (∀ s ∈ r, s.In h) ∧ r.map (MSpan.read h) = v

/-- Each program returns what the specification kernel returns, on any spans
of any store. -/
structure TermOps.Refines (O : TermOps Nat Mach) : Prop where
  compose : ∀ h x y, MSpan.In h x → MSpan.In h y →
    (O.compose x y).Returns h fun h' r => MSpan.ReadsO h' r ((x.read h).compose (y.read h))
  meet : ∀ h x y, MSpan.In h x → MSpan.In h y →
    (O.meet x y).Returns h fun h' r => MSpan.ReadsO h' r ((x.read h).meet (y.read h))
  composable : ∀ h xs, (∀ x ∈ xs, MSpan.In h x) →
    (O.composable xs).Returns h fun _ r => r = (Span.chain (xs.map (MSpan.read h))).isSome
  coversPlain : ∀ h a s, MSpan.In h a → MSpan.In h s → a.c = [] →
    (O.coversPlain a s).Returns h fun _ r => r = (a.read h).covers? (s.read h)
  eq : ∀ h x y, MSpan.In h x → MSpan.In h y →
    (O.eq x y).Returns h fun _ r => r = decide (x.read h = y.read h)
  eqRel : ∀ h a b, (∀ x ∈ a.spans, MSpan.In h x) → (∀ x ∈ b.spans, MSpan.In h x) →
    (O.eqRel a b).Returns h fun _ r =>
      r = decide (a.mapSpan (MSpan.read h) = b.mapSpan (MSpan.read h))
  canon : ∀ h e, (∀ x ∈ e.spans, MSpan.In h x) →
    (O.canon e).Returns h fun h' r =>
      (∀ x ∈ r.spans, MSpan.In h' x) ∧
        r.mapSpan (MSpan.read h') = RwLog.canon (e.mapSpan (MSpan.read h))
  rightBound : ∀ h s, MSpan.In h s →
    (O.rightBound s).Returns h fun h' r => MSpan.ReadsO h' r (bound (s.read h).rightIface)
  leftBound : ∀ h s, MSpan.In h s →
    (O.leftBound s).Returns h fun h' r => MSpan.ReadsO h' r (bound (s.read h).leftIface)

/-! ## The operations that are still postulated -/

namespace Mach

/-- Write a term into the store, one node for each node of the term. -/
def put : Pat → Mach Nat
  | .var v => alloc (.var v)
  | .sym f => alloc (.sym f)
  | .app a b => do
    let x ← put a
    let y ← put b
    alloc (.app x y)

/-- Write a list of terms into the store. -/
def putAll : List Pat → Mach (List Nat)
  | [] => pure []
  | t :: ts => do
    let p ← put t
    let ps ← putAll ts
    pure (p :: ps)

/-- Write a span into the store. -/
def putSpan (s : Span) : Mach (MSpan Nat) := do
  let l ← put s.l
  let r ← put s.r
  let c ← putAll s.c
  pure ⟨l, r, c⟩

/-- Write the spans of an expression into the store. -/
def putRel : Rel → Mach (RelOf (MSpan Nat))
  | .zero => pure .zero
  | .span s => do
    let s' ← putSpan s
    pure (.span s')
  | .or a b => do
    let a' ← putRel a
    let b' ← putRel b
    pure (.or a' b')
  | .and a b => do
    let a' ← putRel a
    let b' ← putRel b
    pure (.and a' b')
  | .seq a b => do
    let a' ← putRel a
    let b' ← putRel b
    pure (.seq a' b')
  | .conv a => do
    let a' ← putRel a
    pure (.conv a')
  | .call n => pure (.call n)

/-- Write the definitions of a program into the store. -/
def putDefs : List (Name × Rel) → Mach (List (Name × RelOf (MSpan Nat)))
  | [] => pure []
  | d :: ds => do
    let e ← putRel d.2
    let es ← putDefs ds
    pure ((d.1, e) :: es)

/-- Write a program into the store. Its theory is not a term of the store. -/
def putProgram (P : Program) : Mach (ProgramOf (MSpan Nat)) := do
  let ds ← putDefs P.defs
  pure ⟨ds, P.theory⟩

/-- Run `m` and charge `n` ticks for it, whatever it spent. -/
def chargedAs {α : Type} (n : Nat) (m : Mach α) : Mach α := fun h =>
  (m h).map fun r => ⟨r.val, n⟩

/-- Interim (ledger L39): the coverage test of the specification kernel on
the spans read from the store, at the charge of `Charged.covers`. -/
def coversInterim (a s : MSpan Nat) : Mach Bool := fun h =>
  some ⟨((a.read h).covers? (s.read h), h), (Charged.covers (a.read h) (s.read h)).ticks⟩

/-- Interim (ledger L39): the simplification of the specification kernel on
the span read from the store, at the charge of `Charged.simplify`. The result
is written into the store within that charge. -/
def simplifyInterim (T : Theory) (s : MSpan Nat) : Mach (Option (MSpan Nat)) := fun h =>
  chargedAs (Charged.simplify T (s.read h)).ticks
    (match T.simplify (s.read h) with
      | none => pure none
      | some r => do
        let r' ← putSpan r
        pure (some r')) h

end Mach

/-! ## The kernel of a kernel rung -/

/-- The kernel made of the given operations on terms and the interim
constraint operations. A span is charged, where an engine charges itself for
handling one, by the pointers it holds. -/
@[reducible] def TermOps.kernel (O : TermOps Nat Mach) : Kernel (MSpan Nat) Mach where
  tick := Mach.tick
  race := Mach.race
  size s := 2 + s.c.length
  idSpan := ⟨0, 0, []⟩
  swap s := ⟨s.r, s.l, s.c⟩
  compose := O.compose
  meet := O.meet
  composable := O.composable
  covers a s := if a.c.isEmpty then O.coversPlain a s else Mach.coversInterim a s
  simplify := Mach.simplifyInterim
  eq := O.eq
  eqRel := O.eqRel
  canon := O.canon
  rightBound := O.rightBound
  leftBound := O.leftBound

/-- A kernel rung: programs for the operations on terms, and the proof that
they return what the specification kernel returns. -/
structure KernelRung where
  prog : KernelProg
  refines : (prog.ops (M := Mach)).Refines

/-- The kernel of a kernel rung, on the machine of the language. -/
@[reducible] def KernelRung.kernel (K : KernelRung) : Kernel (MSpan Nat) Mach :=
  (K.prog.ops (M := Mach)).kernel

/-! ## An engine on a kernel rung -/

/-- The engine `E` on the kernel rung `K`: a machine with its cost.

Its first state is built by writing the program and the query into the first
store and running the engine's `init`; the ticks of both are charged. A step
is the engine's step from the current store, and each answer is read back
through the store the step leaves. A state is `none` when a computation did
not finish: from there every step spends a tick and emits nothing, for
ever. -/
def Engine.costedOn (E : Engine) (K : KernelRung) : CostedRuntime where
  State := Option (E.State (MSpan Nat) × Heap)
  init P q :=
    letI := K.kernel
    match (do
        let P' ← Mach.putProgram P
        let q' ← Mach.putRel q
        E.init P' q' : Mach (E.State (MSpan Nat))) Heap.init with
    | some r => ⟨some r.val, r.ticks⟩
    | none => ⟨none, 1⟩
  step
    | none => ⟨.emit [] none, 1⟩
    | some (s, h) =>
      letI := K.kernel
      match (E.step s : Mach (StepOf (MSpan Nat) (E.State (MSpan Nat)))) h with
      | none => ⟨.emit [] none, 1⟩
      | some r =>
        match r.val.1 with
        | .done => ⟨.done, r.ticks⟩
        | .emit as s' => ⟨.emit (as.map (MSpan.read r.val.2)) (some (s', r.val.2)), r.ticks⟩

end RwLog
