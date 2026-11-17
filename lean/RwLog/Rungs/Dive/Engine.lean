/-
# The diving engine

An engine that keeps no tables. It reads the root node from the top and
makes one answer of it at a time, by a choice at every union on the way: an
answer of a span node is its leaf, of a call the answer of its body, of a
union the answer of the member chosen, of a chain the answers of its members
joined from left to right, and of a meet the answers of its members met. The
choices are the digits of a number, read at each union in the base of its
number of members, so the number 0 takes the first member everywhere and
every way through the unions is the reading of some number.

A step runs one such reading under a budget of ticks (`Kernel.within`), which
also bounds how deep the reading goes. The budgets are the powers of two;
under the budget `2 ^ n` the readings of the numbers `0` to `n` are run, one
at a step. So a reading that costs `c` ticks is run to its end within the
first steps whose budgets are below `2 * c`, whatever the other readings
would cost.

An answer made is emitted with its converse, which is an answer of the same
goal when the root is its own converse.

The engine never reports that it is done, and it is not complete: a reading
goes into a call that leads back to itself for as long as the budget
allows. It is sound because every engine is (`Engine.sound`): an answer can
only be made by the rules of the derivation kernel. It is an engine to put
beside a complete one (`Engine.beside`).
-/
import RwLog.Rungs.Framework.Holding

namespace RwLog

namespace Dive

/-- The state: the root node, the budget `2 ^ level` of the readings being
run, and the number of the next reading. -/
structure State (N : Type) where
  root : N
  level : Nat
  number : Nat

section

variable {S N A : Type} {M : Type → Type} [K : DerivationKernel S N A M]

/-- Join the answers of the members `xs` of a chain onto the answer `a` of
the members before them, each read by `ev` with what is left of the number.
Nothing if a member has no answer or two do not compose. -/
def joinL (ev : Nat → N → M (Option A × Nat)) (a : A) (k : Nat) : List N → M (Option A × Nat)
  | [] => pure (some a, k)
  | x :: xs => do
    let r ← ev k x
    match r.1 with
    | none => pure (none, r.2)
    | some b =>
      match ← K.join a b with
      | none => pure (none, r.2)
      | some c => joinL ev c r.2 xs

/-- Meet the answers of the members `xs` of a meet with the answer `a` of
the members before them. -/
def meetL (ev : Nat → N → M (Option A × Nat)) (a : A) (k : Nat) : List N → M (Option A × Nat)
  | [] => pure (some a, k)
  | x :: xs => do
    let r ← ev k x
    match r.1 with
    | none => pure (none, r.2)
    | some b =>
      match ← K.meetA a b with
      | none => pure (none, r.2)
      | some c => meetL ev c r.2 xs

/-- One reading of the node `n`, at most `d` nodes deep, by the choices of
the number `k`: an answer of the goal of `n` between no boundaries, if the
reading makes one, and what is left of the number. The answer of a chain or
a meet is checked to be an answer of the node itself (`inj` at a node that
is no union). -/
def read : Nat → Nat → N → M (Option A × Nat)
  | 0, k, _ => pure (none, k)
  | d + 1, k, n => do
    match ← K.view n with
    | .span _ => do
      let a ← K.leaf none n none
      pure (a, k)
    | .call _ _ =>
      match ← K.body n with
      | none => pure (none, k)
      | some b => do
        let r ← read d k b
        match r.1 with
        | none => pure (none, r.2)
        | some a => do
          let c ← K.unfold a n
          pure (c, r.2)
    | .union xs =>
      match xs[k % xs.length]? with
      | none => pure (none, k)
      | some x => do
        let r ← read d (k / xs.length) x
        match r.1 with
        | none => pure (none, r.2)
        | some a => do
          let c ← K.inj a n (k % xs.length)
          pure (c, r.2)
    | .chain xs =>
      match xs with
      | [] => pure (none, k)
      | x :: rest => do
        let r ← read d k x
        match r.1 with
        | none => pure (none, r.2)
        | some a => do
          let r' ← joinL (S := S) (read d) a r.2 rest
          match r'.1 with
          | none => pure (none, r'.2)
          | some c => do
            let c' ← K.inj c n 0
            pure (c', r'.2)
    | .meet xs =>
      match xs with
      | [] => pure (none, k)
      | x :: rest => do
        let r ← read d k x
        match r.1 with
        | none => pure (none, r.2)
        | some a => do
          let r' ← meetL (S := S) (read d) a r.2 rest
          match r'.1 with
          | none => pure (none, r'.2)
          | some c => do
            let c' ← K.inj c n 0
            pure (c', r'.2)

/-- The reading after this one: the next number under the same budget, or
the number 0 under twice the budget. -/
def State.next (s : State N) : State N :=
  if s.number < s.level then { s with number := s.number + 1 }
  else { s with level := s.level + 1, number := 0 }

/-- What a step shows of a reading run under the budget: the answer it made,
with its converse. -/
def finish (s : State N) : Option (Option A × Nat) → M (StepOf A (State N))
  | some (some a, _) => do
    let a' ← K.swapA a
    pure (.emit [a, a'] s.next)
  | _ => pure (.emit [] s.next)

/-- A step: one reading of the root under the budget, and its answer emitted
with its converse. -/
def step (s : State N) : M (StepOf A (State N)) := do
  let r ← K.within (2 ^ s.level) (read (S := S) (2 ^ s.level) s.number s.root)
  finish (S := S) s r

end

end Dive

attribute [local instance] Pack.node in
/-- The diving engine. Its state holds the root node and two numbers. -/
def dive : Engine where
  State _ N _ := Dive.State N
  init root := pure ⟨root, 0, 0⟩
  step {S N A M} _ s := Dive.step (S := S) (A := A) (M := M) s
  held s := Pack.pack (s.root, s.level, s.number)
  held_inj S N A := by
    intro a b e
    have h := Pack.inj e
    simp only [Prod.mk.injEq] at h
    cases a; cases b; simp_all

end RwLog
