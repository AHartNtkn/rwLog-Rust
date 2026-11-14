/-
# Lower bounds on R005, stated

The next engine is admitted over R005 by a separation: a family of inputs on
which R005 pays exponentially more than it does. That needs a lower bound on
what R005 pays, and R005 is a mirrored machine, so the bound starts from
`Mirror.paid_ge_min` (`Rungs/Mirror/Bounds.lean`): R005 has paid at least the
cheaper of what the steps of R004 cost from the node of the query and from
its converse.

`LowerOn E P q x lo` is the form such a bound takes for a mirrored engine: at
any step at which the mirrored machine has covered `x`, each of the two runs
of `E` has cost at least `lo`. `LowerOn.paid` is the bound on the mirrored
machine it gives.

Two families are stated here and proved nowhere: proving them belongs to the
rung that is admitted over R005 (roadmap M6).

* `MidLower`: the chain restricted in the middle,
  `bit ; … ; bit ; ($x -> t_k) ; unbit ; … ; unbit` with `k` factors on each
  side. It has one answer, `$x -> z`. Neither end is restricted, so neither
  run of the mirror is the cheap one.
* `FreeLower`: `t | (g ; @q) | w` with `t` defined as `@a`, `g` as `gen k`
  and `w` as itself. The unfolding is never final, so the machine answers
  from its tables, and the table of the free factor `g` asks the unfolding
  race for all `2 ^ (k + 1)` spans of `gen k` in its fourth round, which is
  the round in which `a -> a` arrives through the call of `t`.

  In epoch 1 the family was `@a | (g ; @q) | w`, with the answer written in
  the query. On the machine as it is written now that answer arrives in the
  third round, a round before the table of `g` asks the race, and what the
  machine has paid by then does not grow with `k` beyond reading the input
  (`Tests/R005Runs.lean`: at `k = 12` each run has cost under 700 ticks). So
  the bound is false of the family as it was written, and the answer is put
  behind a call here.

Both are stated at the kernel of spans as they are written, which is the
kernel `Engine.costed` runs at. `Tests/R005Runs.lean` checks each of them on
small `k`.
-/
import RwLog.Rungs.R005.Engine
import RwLog.Rungs.Mirror.Bounds

namespace RwLog

/-- The steps of an engine at the kernel of spans as they are written, on a
program. -/
abbrev Engine.stepW (E : Engine) (P : Program) :=
  E.stepAt (R := fun _ => Span) (fun _ => Domain.written) (fun _ => Kernel.std)
    (fun _ => Kernel.std_refines) P

/-- The state an engine starts in on a node, at the kernel of spans as they
are written. -/
abbrev Engine.startW (E : Engine) (P : Program) (root : Rel) :=
  E.startAt (R := fun _ => Span) (fun _ => Domain.written) (fun _ => Kernel.std)
    (fun _ => Kernel.std_refines) P root

/-- At any step at which the mirrored machine has covered `x`, each of the
two runs of `E` has cost at least `lo`. -/
def Mirror.LowerOn (E : Engine) (P : Program) (q : Rel) (x : GTerm × GTerm) (lo : Nat) : Prop :=
  ∀ n, E.mirrored.costed.Covered P q P.sorts.interp x n →
    lo ≤ Mirror.cost (E.stepW P) (E.startW P q.norm) n ∧
    lo ≤ Mirror.cost (E.stepW P) (E.startW P q.norm.normConv) n

/-- A bound on the two runs is a bound on the mirrored machine. -/
theorem Mirror.LowerOn.paid {E : Engine} {P : Program} {q : Rel} {x : GTerm × GTerm} {lo : Nat}
    (h : Mirror.LowerOn E P q x lo) {n : Nat}
    (hx : E.mirrored.costed.Covered P q P.sorts.interp x n) :
    lo ≤ E.mirrored.costed.paid P q n :=
  Nat.le_trans (Nat.le_min.2 (h n hx))
    (Mirror.paid_ge_min E (fun _ => Domain.written) (fun _ => Kernel.std)
      (fun _ => Kernel.std_refines) P q n)

namespace R005

/-! ## The families -/

/-- `$x -> (f $x)`. -/
def wrap (f : Sym) : Span := ⟨.var 0, .app (.sym f) (.var 0), []⟩

/-- `(f $x) -> $x`. -/
def unwrap (f : Sym) : Span := ⟨.app (.sym f) (.var 0), .var 0, []⟩

/-- Put `0` or `1` on top of a term. -/
def bit : Rel := .or (.span (wrap "0")) (.span (wrap "1"))

/-- Take a `0` or a `1` off the top of a term. -/
def unbit : Rel := .or (.span (unwrap "0")) (.span (unwrap "1"))

/-- `k + 1` bits in a row: every term to its `2 ^ (k + 1)` wrappings. -/
def gen : Nat → Rel
  | 0 => bit
  | k + 1 => .seq bit (gen k)

/-- `z` under `k` wrappers. -/
def target : Nat → Pat
  | 0 => .sym "z"
  | k + 1 => .app (.sym "0") (target k)

/-- A chain, bracketed to the right. -/
def chain : List Rel → Rel
  | [] => .zero
  | [a] => a
  | a :: as => .seq a (chain as)

/-- `bit ; … ; bit ; ($x -> t_k) ; unbit ; … ; unbit`, `k` factors on each
side. -/
def mid (k : Nat) : Rel :=
  chain (List.replicate k bit ++ [.span ⟨.var 0, target k, []⟩] ++ List.replicate k unbit)

/-- `t` is `@a`, `g` is `gen k`, and `w` is itself. -/
def freeProg (k : Nat) : Program :=
  ⟨[("t", .at_ (.sym "a")), ("g", gen k), ("w", .call "w")], []⟩

/-- `t | (g ; @q) | w`. -/
def freeRel : Rel :=
  .or (.call "t") (.or (.seq (.call "g") (.at_ (.sym "q"))) (.call "w"))

/-- The family as epoch 1 wrote it, `@a | (g ; @q) | w`: the answer is in the
query. The bound is false of it. -/
def freeRelWritten : Rel :=
  .or (.at_ (.sym "a")) (.or (.seq (.call "g") (.at_ (.sym "q"))) (.call "w"))

/-! ## The bounds, stated -/

/-- On the chain restricted in the middle, R005 has paid at least `2 ^ k` by
any step at which it relates `z` to `z`. -/
def MidLower : Prop :=
  ∀ k, Mirror.LowerOn R004.engine ⟨[], []⟩ (mid k) (.sym "z", .sym "z") (2 ^ k)

/-- On the free factor beside an answer, R005 has paid at least `2 ^ k` by
any step at which it relates `a` to `a`. -/
def FreeLower : Prop :=
  ∀ k, Mirror.LowerOn R004.engine (freeProg k) freeRel (.sym "a", .sym "a") (2 ^ k)

/-- What `MidLower` says of R005. -/
theorem MidLower.paid (h : MidLower) (k : Nat) {n : Nat}
    (hx : R005.engine.costed.Covered ⟨[], []⟩ (mid k) (Sorts.interp []) (.sym "z", .sym "z") n) :
    2 ^ k ≤ R005.engine.costed.paid ⟨[], []⟩ (mid k) n :=
  (h k).paid hx

/-- What `FreeLower` says of R005. -/
theorem FreeLower.paid (h : FreeLower) (k : Nat) {n : Nat}
    (hx : R005.engine.costed.Covered (freeProg k) freeRel (Sorts.interp [])
      (.sym "a", .sym "a") n) :
    2 ^ k ≤ R005.engine.costed.paid (freeProg k) freeRel n :=
  (h k).paid hx

end R005

end RwLog
