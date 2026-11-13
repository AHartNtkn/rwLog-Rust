/-
# The kernel an engine is written against

An engine does not get to say what its work costs. It is written for an
arbitrary type `S` of spans and an arbitrary monad `M`, and all it is given
is a `Kernel S M`: the operations on spans, each returning in `M`. It cannot
look inside a span, build one, or compare two, except by calling an operation
of the kernel, and it cannot touch the ticks at all, except by spending more
(`tick`).

The language's kernel is the instance at `Span` and `Cost`: every operation
is the charged primitive of `Trusted/Charged.lean`. The cost of an engine is
what its instance at that kernel spends (`Engine.costed`,
`Trusted/Cost.lean`), so it is fixed by the engine's text and the trusted
charges, and by nothing the engine's author declares.

Walking over an expression, a list or a table is free: only what is done to
the spans found there is charged. An engine may still charge itself for it.
-/
import RwLog.Trusted.Charged

namespace RwLog

/-- The operations on spans, for a type `S` of spans, in a monad `M`. -/
class Kernel (S : Type) (M : outParam (Type → Type)) extends Monad M where
  /-- Spend ticks. -/
  tick : Nat → M Unit
  /-- Run two computations side by side until one finishes (`Cost.race`). -/
  race : {α : Type} → M α → M α → M α
  /-- The size of a span. -/
  size : S → Nat
  /-- The identity span `$x -> $x`. -/
  idSpan : S
  /-- The converse span. -/
  swap : S → S
  compose : S → S → M (Option S)
  meet : S → S → M (Option S)
  /-- Does the chain of spans compose? -/
  composable : List S → M Bool
  /-- Does the first span cover the second? -/
  covers : S → S → M Bool
  simplify : Theory → S → M (Option S)
  /-- Are the two spans the same, as written? -/
  eq : S → S → M Bool
  /-- Are the two expressions the same, as written? -/
  eqRel : RelOf S → RelOf S → M Bool
  /-- The canonical form of an expression. -/
  canon : RelOf S → M (RelOf S)
  /-- The right interface of a span, as a boundary. -/
  rightBound : S → M (Option S)
  /-- The left interface of a span, as a boundary. -/
  leftBound : S → M (Option S)

/-- The kernel of the language: spans, and every operation at its trusted
charge. -/
instance Kernel.std : Kernel Span Cost where
  tick := Cost.tick
  race := Cost.race
  size := Span.size
  idSpan := ⟨.var 0, .var 0, []⟩
  swap := Span.swap
  compose := Charged.compose
  meet := Charged.meet
  composable := Charged.composable
  covers := Charged.covers
  simplify := Charged.simplify
  eq := Charged.eq
  eqRel := Charged.eqRel
  canon := Charged.canon
  rightBound := Charged.rightBound
  leftBound := Charged.leftBound

end RwLog
