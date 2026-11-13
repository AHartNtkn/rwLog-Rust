import Tests.R005Runs
import RwLog.Rungs.Directed.Reading

/-!
# Running the goal-directed tables

These checks run the goal-directed tabled machine (`Rungs/Directed`) beside
R004 and fail the build if what they compute changes. The machine is not a
rung: it is sound and not complete, and it never reports exhaustion.

Two families are measured.

* `free k`, the query `@a | (g ; @q) | w` with `g := gen k` and `w := w`. The
  unfolding is never final, so R004 answers from its tables, and its table for
  the free factor `g` asks the unfolding race for `2 ^ (k + 1)` spans in the
  round in which `a -> a` arrives. The goal-directed tables never open `g`
  without the boundary `@q`: they pay the same for every `k`, from either end.
* `digits d`, a query on which driving from the restricted end loses: `d`
  choices of a digit between two ground tests. Every choice the goal-directed
  tables push across opens a goal under a ground boundary, and they pay
  hundreds of times what R004 pays for `d = 3`. An evaluation order fixed by
  which end is restricted is not within a polynomial of R004.
-/

namespace RwLog.Tests

/-- The rounds taken and the ticks paid by the first round that emits an
answer, within `n` rounds. -/
def firstEmit (C : CostedRuntime) (s : C.State) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | n + 1, acc, r =>
    match (C.step s).val with
    | .done => none
    | .emit as s' =>
      if as.isEmpty then firstEmit C s' n (acc + (C.step s).ticks) (r + 1)
      else some (r + 1, acc + (C.step s).ticks)

def firstOf (C : CostedRuntime) (P : Program) (q : Rel) (n : Nat) : Option (Nat × Nat) :=
  firstEmit C (C.start P q) n ((C.init P q).ticks) 0

/-! ## A free factor beside an answer -/

def freeProg (k : Nat) : Program := ⟨[("g", R004.gen k), ("w", .call "w")], []⟩

def freeRel : Rel :=
  .or (.at_ (.sym "a")) (.or (.seq (.call "g") (.at_ (.sym "q"))) (.call "w"))

/-- The goal-directed tables emit `a -> a` in their third round and have paid
the same by then for every `k`, on the query and on its mirror image. -/
def directedFree (k : Nat) : Option (Nat × Nat) × Option (Nat × Nat) :=
  (firstOf Directed.machine (freeProg k) freeRel 5,
    firstOf Directed.machine (freeProg k).dual freeRel.dual 5)

#guard directedFree 0 == directedFree 2
#guard directedFree 2 == directedFree 6
#guard (directedFree 6).1 == (directedFree 6).2
#guard (directedFree 6).1.any fun r => r.1 == 3 && r.2 < 1000

-- What they emit is the answer.
#guard (Directed.machine.runtime.emitted (Directed.machine.start (freeProg 6) freeRel) 3).any
  fun a => a == ⟨.sym "a", .sym "a", []⟩

/-- R004 emits in its third round too, and has paid more than `4 ^ k` by
then, from either end. -/
def r004Free (k : Nat) : Bool :=
  (firstOf R004.costed (freeProg k) freeRel 5).any (fun r => r.1 == 3 && 4 ^ k < r.2) &&
    (firstOf R004.costed (freeProg k).dual freeRel.dual 5).any fun r => r.1 == 3 && 4 ^ k < r.2

#guard r004Free 2
#guard r004Free 4
#guard r004Free 6

/-! ## Driving from the restricted end loses -/

/-- `(t x_1 ... x_d)`. -/
def tuple (xs : List Pat) : Pat := xs.foldl .app (.sym "t")

/-- Set digit `j` of a tuple of `d` digits to `b`. -/
def setDigit (d j : Nat) (b : Sym) : Span :=
  ⟨tuple ((List.range d).map .var), tuple (((List.range d).map .var).set j (.sym b)), []⟩

/-- A branch with no answers whose table never completes: a number followed
by a test no number passes. -/
def noAnswer (d : Nat) : Rel :=
  .seq (.call "n") (.span ⟨.sym "bad", tuple ((List.range d).map .var), []⟩)

def digit (d j : Nat) : Rel :=
  .or (.span (setDigit d j "0")) (.or (.span (setDigit d j "1")) (noAnswer d))

def digitsFrom (d : Nat) : Nat → Rel
  | 0 => .at_ (tuple (List.replicate d (.sym "1")))
  | i + 1 => .seq (digit d (d - (i + 1))) (digitsFrom d i)

def digitsProg : Program :=
  ⟨[("n", .or (.span ⟨.var 0, .sym "z", []⟩)
      (.seq (.call "n") (.span ⟨.var 0, .app (.sym "s") (.var 0), []⟩)))], []⟩

/-- `@(t 0 ... 0) ; (digit_1 ; (... ; (digit_d ; @(t 1 ... 1))))`. -/
def digits (d : Nat) : Rel := .seq (.at_ (tuple (List.replicate d (.sym "0")))) (digitsFrom d d)

/-- R004 has answered within two rounds. The goal-directed tables need six
rounds for each digit, and pay more than 10 times as much for one digit, 50
times for two and 100 times for three. -/
def digitsRatio (d ratio : Nat) : Bool :=
  match firstOf R004.costed digitsProg (digits d) 3,
      firstOf Directed.machine digitsProg (digits d) (6 * d + 6) with
  | some r, some g => g.1 == 6 * d + 5 && ratio * r.2 < g.2
  | _, _ => false

#guard digitsRatio 1 10
#guard digitsRatio 2 50
#guard digitsRatio 3 100

end RwLog.Tests
