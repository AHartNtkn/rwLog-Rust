/-
# Kernel rungs

`Kernel.std` (`Trusted/Kernel.lean`) is the specification kernel: it says
what every operation on spans returns. What it charges is postulated.

A *kernel rung* is another kernel on the same spans, in the same monad of
charged computations, that returns what the specification kernel returns
(`Kernel.Refines`) and whose charges are theorems about a machine: each
charge is the number of ticks within which a program on the machine returns
the operation's result. The charges of a kernel rung are therefore its own,
and they may credit what the machine does well, such as sharing.

Refinement is stated operation by operation. It says nothing about the ticks,
so an engine may behave differently at two kernels where it reads the ticks
(`race`): what an engine returns at a kernel rung is proved from `Refines`,
and what it costs is proved from that rung's charges.

`Engine.costedAt` is an engine at a kernel; `Engine.costed` is the engine at
the specification kernel.
-/
import RwLog.Trusted.Cost

namespace RwLog

/-- The kernel returns what the specification kernel returns: it has the
monad of charged computations with its `tick` and `race`, the same size,
identity span and converse, and the value of every operation is the value of
the same operation of `Kernel.std`. -/
structure Kernel.Refines (K : Kernel Span Cost) : Prop where
  monad : K.toMonad = Kernel.std.toMonad
  tick : K.tick = Cost.tick
  race : ∀ (α : Type) (a b : Cost α), K.race a b = Cost.race a b
  size : K.size = Span.size
  idSpan : K.idSpan = ⟨.var 0, .var 0, []⟩
  swap : K.swap = Span.swap
  compose : ∀ x y, (K.compose x y).val = x.compose y
  meet : ∀ x y, (K.meet x y).val = x.meet y
  composable : ∀ xs, (K.composable xs).val = (Span.chain xs).isSome
  covers : ∀ a s, (K.covers a s).val = a.covers? s
  simplify : ∀ T s, (K.simplify T s).val = T.simplify s
  eq : ∀ x y, (K.eq x y).val = decide (x = y)
  eqRel : ∀ a b, (K.eqRel a b).val = decide (a = b)
  canon : ∀ e, (K.canon e).val = RwLog.canon e
  rightBound : ∀ s, (K.rightBound s).val = bound s.rightIface
  leftBound : ∀ s, (K.leftBound s).val = bound s.leftIface

/-- The specification kernel refines itself. -/
theorem Kernel.std_refines : Kernel.Refines Kernel.std where
  monad := rfl
  tick := rfl
  race _ _ _ := rfl
  size := rfl
  idSpan := rfl
  swap := rfl
  compose _ _ := rfl
  meet _ _ := rfl
  composable _ := rfl
  covers _ _ := rfl
  simplify _ _ := rfl
  eq _ _ := rfl
  eqRel _ _ := rfl
  canon _ := rfl
  rightBound _ := rfl
  leftBound _ := rfl

/-- The engine at a kernel on the spans of the language: a machine with the
cost that kernel charges. -/
def Engine.costedAt (E : Engine) (K : Kernel Span Cost) : CostedRuntime where
  State := E.State Span
  init := @Engine.init E Span Cost K
  step := @Engine.step E Span Cost K

/-- At the specification kernel this is `Engine.costed`. -/
theorem Engine.costedAt_std (E : Engine) : E.costedAt Kernel.std = E.costed := rfl

end RwLog
