/-
# The unfolding race, written against the kernel

The eager and the on-demand unfolding races of `Unfold.lean` (which says what
they do and why), written for an arbitrary type of spans and an arbitrary
monad: everything they do to a span is an operation of the kernel
(`Trusted/Kernel.lean`). `Unfold.lean` is this text read at the kernel of the
language, definition for definition (`Reading.lean` proves they are equal).
-/
import RwLog.Rungs.Tabled.Gen

namespace RwLog

namespace R002

namespace Gen

open Traverse

variable {Sp : Type} {M : Type → Type} [Kernel Sp M]

/-- The sequence of a list of factors; the identity for the empty list. -/
def toRel : List (RelOf Sp) → RelOf Sp
  | [] => .span Kernel.idSpan
  | [f] => f
  | f :: g :: fs => .seq f (toRel (g :: fs))

/-! ## Eagerly -/

namespace Eager

/-- Replace every call by the body of its definition; one tick per node. -/
def unfold (P : (ProgramOf Sp)) : (RelOf Sp) → M (RelOf Sp)
  | .zero => do Kernel.tick Sp 1; pure .zero
  | .span s => do Kernel.tick Sp 1; pure (.span s)
  | .or a b => do
    Kernel.tick Sp 1
    let a' ← unfold P a
    let b' ← unfold P b
    pure (.or a' b')
  | .and a b => do
    Kernel.tick Sp 1
    let a' ← unfold P a
    let b' ← unfold P b
    pure (.and a' b')
  | .seq a b => do
    Kernel.tick Sp 1
    let a' ← unfold P a
    let b' ← unfold P b
    pure (.seq a' b')
  | .conv a => do
    Kernel.tick Sp 1
    let a' ← unfold P a
    pure (.conv a')
  | .call n => do Kernel.tick Sp 1; pure (P.body n)

def unfoldN (P : (ProgramOf Sp)) : Nat → (RelOf Sp) → M (RelOf Sp)
  | 0, e => pure e
  | k + 1, e => do
    let e' ← unfold P e
    unfoldN P k e'

end Eager

/-- Join two chains, fusing the spans that meet. -/
def joinSeq (p q : List (RelOf Sp)) : M (Option (List (RelOf Sp))) :=
  match p.getLast?, q with
  | some (.span a), .span b :: q' => do
    let c ← Kernel.compose a b
    pure (c.map fun c => p.dropLast ++ .span c :: q')
  | _, _ => pure (some (p ++ q))

/-- Conjoin two products. -/
def mkAnd (p q : List (RelOf Sp)) : M (Option (List (RelOf Sp))) :=
  match p, q with
  | [.span a], [.span b] => do
    let c ← Kernel.meet a b
    pure (c.map fun c => [.span c])
  | _, _ => pure (some [.and (toRel p) (toRel q)])

/-- The span of a product that is a single span. -/
def single : List (RelOf Sp) → Option Sp
  | [.span s] => some s
  | _ => none

/-- The products that are a single span, as spans. A product of a normal form
that contains no call is a single span (`open_calls`), so when no product of
the unfolding contains a call these are all its answers. -/
def closed (N : List (List (RelOf Sp))) : List Sp := N.filterMap single

namespace Eager

/-- The normal form as a list of products; one tick per node, a span leaf
charged by its size. The products of the second factor of a sequence are
recomputed for each product of the first, as rung zero's `norm` does. -/
def norm : Bool → (RelOf Sp) → M (List (List (RelOf Sp)))
  | _, .zero => do Kernel.tick Sp 1; pure []
  | neg, .span s => do Kernel.tick Sp (1 + Kernel.size s); pure [[.span (if neg then Kernel.swap s else s)]]
  | neg, .or a b => do
    Kernel.tick Sp 1
    let xs ← norm neg a
    let ys ← norm neg b
    pure (xs ++ ys)
  | false, .seq a b => do
    Kernel.tick Sp 1
    let ps ← norm false a
    flatMapL (fun p => do
      let qs ← norm false b
      filterMapL (joinSeq p) qs) ps
  | true, .seq a b => do
    Kernel.tick Sp 1
    let ps ← norm true b
    flatMapL (fun p => do
      let qs ← norm true a
      filterMapL (joinSeq p) qs) ps
  | neg, .and a b => do
    Kernel.tick Sp 1
    let ps ← norm neg a
    flatMapL (fun p => do
      let qs ← norm neg b
      filterMapL (mkAnd p) qs) ps
  | neg, .conv a => do
    Kernel.tick Sp 1
    norm (!neg) a
  | neg, .call n => do Kernel.tick Sp 1; pure [[if neg then .conv (.call n) else .call n]]

end Eager

/-- R001's unfolding race: build the unfolding, normalize it, then look. -/
def eager : GOracle Sp M := fun P d g => do
  let e ← Eager.unfoldN P d g.rel
  let ps ← Eager.norm false e
  if ps.all fun p => (toRel p).calls.isEmpty then do
    let xs ← flatMapL (Tabled.Gen.live P.theory) (closed ps)
    pure (true, xs)
  else pure (false, [])

/-! ## On demand -/

/-- The first factor of a product, when it is a span. -/
def headSpan (p : List (RelOf Sp)) : Option Sp :=
  match p with
  | .span a :: _ => some a
  | _ => none

/-- The last factor of a product, when it is a span. -/
def lastSpan (p : List (RelOf Sp)) : Option Sp :=
  match p.getLast? with
  | some (.span a) => some a
  | _ => none

/-- The product can still be fused with the chain `L` on its left. An empty
chain is not tested. -/
def aliveL (L : List Sp) (p : List (RelOf Sp)) : M Bool :=
  match L, headSpan p with
  | _ :: _, some s => Kernel.composable (L ++ [s])
  | _, _ => pure true

/-- The product can still be fused with the chain `R` on its right. -/
def aliveR (p : List (RelOf Sp)) (R : List Sp) : M Bool :=
  match R, lastSpan p with
  | _ :: _, some s => Kernel.composable (s :: R)
  | _, _ => pure true

def alive (L : List Sp) (p : List (RelOf Sp)) (R : List Sp) : M Bool := do
  let a ← aliveL L p
  if a then aliveR p R else pure false

/-- The span every product of the expression starts with, when the expression
itself says so: `some (s, true)` when the expression is that span, and
`some (s, false)` when it is a sequence that starts with it. With `neg` the
converse of the expression is read. -/
def staticFirst : Bool → (RelOf Sp) → Option (Sp × Bool)
  | neg, .span s => some (if neg then Kernel.swap s else s, true)
  | false, .seq a _ => (staticFirst false a).map fun r => (r.1, false)
  | true, .seq _ b => (staticFirst true b).map fun r => (r.1, false)
  | neg, .conv a => staticFirst (!neg) a
  | _, _ => none

/-- The chain to the right of the first factor of a sequence whose second
factor is `e` and which itself has the chain `R` to its right. -/
def rightOf (neg : Bool) (e : (RelOf Sp)) (R : List Sp) : List Sp :=
  match staticFirst neg e with
  | some (t, true) => t :: R
  | some (t, false) => [t]
  | none => []

/-- The chain to the left of the second factor of a sequence, after the
product `p` of its first factor, which itself has the chain `L` to its left. -/
def leftAfter (L : List Sp) (p : List (RelOf Sp)) : List Sp :=
  match p with
  | [.span a] => L ++ [a]
  | _ => (lastSpan p).toList

/-- What the walk carries: stop, and the products handed to the top so far. -/
abbrev Walk (Sp : Type) := Bool × List (List (RelOf Sp))

/-- Walk the products of the normal form of `e` unfolded `d` times (of its
converse with `neg`), handing each one that is alive between the chains `L`
and `R` to `k`, in the normalizer's order, until `k` says stop. One tick per
node visited. -/
def walk (P : (ProgramOf Sp)) : (d : Nat) → Bool → (e : (RelOf Sp)) → List Sp → List Sp →
    (List (RelOf Sp) → List (List (RelOf Sp)) → M (Walk Sp)) → List (List (RelOf Sp)) → M (Walk Sp)
  | _, _, .zero, _, _, _, acc => do Kernel.tick Sp 1; pure (false, acc)
  | _, neg, .span s, L, R, k, acc => do
    Kernel.tick Sp 1
    let p := [(RelOf.span (if neg then Kernel.swap s else s) : (RelOf Sp))]
    let a ← alive L p R
    if a then k p acc else pure (false, acc)
  | d, neg, .or a b, L, R, k, acc => do
    Kernel.tick Sp 1
    let r ← walk P d neg a L R k acc
    if r.1 then pure r else walk P d neg b L R k r.2
  | d, false, .seq a b, L, R, k, acc => do
    Kernel.tick Sp 1
    walk P d false a L (rightOf false b R) (fun p acc =>
      walk P d false b (leftAfter L p) R (fun q acc => do
        let r ← joinSeq p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← aliveR r R
          if a then k r acc else pure (false, acc)) acc) acc
  | d, true, .seq a b, L, R, k, acc => do
    Kernel.tick Sp 1
    walk P d true b L (rightOf true a R) (fun p acc =>
      walk P d true a (leftAfter L p) R (fun q acc => do
        let r ← joinSeq p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← aliveR r R
          if a then k r acc else pure (false, acc)) acc) acc
  | d, neg, .and a b, L, R, k, acc => do
    Kernel.tick Sp 1
    walk P d neg a [] [] (fun p acc =>
      walk P d neg b [] [] (fun q acc => do
        let r ← mkAnd p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← alive L r R
          if a then k r acc else pure (false, acc)) acc) acc
  | d, neg, .conv a, L, R, k, acc => do
    Kernel.tick Sp 1
    walk P d (!neg) a L R k acc
  | 0, neg, .call n, _, _, k, acc => do
    Kernel.tick Sp 1
    k [if neg then .conv (.call n) else .call n] acc
  | d + 1, neg, .call n, L, R, k, acc => do
    Kernel.tick Sp 1
    walk P d neg (P.body n) L R k acc
termination_by d _ e => (d, sizeOf e)

/-- R002's unfolding race: walk the products on demand, stop at the first one
that reaches the top with a call left in it. -/
def onDemand : GOracle Sp M := fun P d g => do
  let r ← walk P d false g.rel [] []
    (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc))) []
  if r.1 then pure (false, [])
  else do
    let xs ← flatMapL (Tabled.Gen.live P.theory) (closed r.2)
    pure (true, xs)

end Gen

/-- R001 as an engine: the tabled machine with the eager race. -/
def baselineEngine : Engine := Tabled.Gen.engine Gen.eager

/-- R002 as an engine: the tabled machine with the race on demand. -/
def engine : Engine := Tabled.Gen.engine Gen.onDemand

end R002

end RwLog
