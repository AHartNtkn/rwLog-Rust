/-
# The unfolding race, eagerly and on demand

Every goal of the tabled machine races one strategy that reads no table:
unfold the calls of the goal `d` times, normalize the result into products as
rung zero does, and, if no product still contains a call, take the spans of
the products as all the answers of the goal. This is what lets the machine
halt wherever rung zero halts. The question asked each round is the same
whichever way it is computed: *is the unfolding to depth `d` final, and if
so what are its answers?*

## Eagerly (`eager`, R001's way)

Build the unfolded expression, normalize all of it, then look. The unfolded
expression of a definition with two calls, or with two recursive branches, has
at least `2 ^ d` nodes, and its normal form can have doubly exponentially many
products, all built before any of them is looked at.

## On demand (`onDemand`, R002's way)

Walk the products in the same order without building the unfolded expression
or the list of products, and:

* stop at the first product that survives to the top and still contains a
  call: the unfolding is not final, and nothing else matters;
* never go into a part of the expression that cannot survive. While walking,
  the spans that will be fused to the left of the current position are known
  (`L`), and so are the spans that stand to its right in the expression
  itself (`R`). A product whose first span does not compose with the chain
  `L`, or whose last span does not compose with the chain `R`, is dropped where
  it arises: the normalizer would build it and drop it later, when the fusion
  with its neighbour fails.

The walk hands the top exactly the products the normalizer lists, in the same
order, built by the same compositions in the same order, so the answer is the
same list of the same spans, not merely an equivalent one (obligation
`onDemand_exact`). Only the tests that prune are extra, and they are charged
as tests: no span is built for them.

A conjunction is a barrier for both chains: its product is fused with its
neighbours only when both sides are single spans, so nothing is pruned inside
it, and its result is tested when it is formed. A call left at depth zero is
a barrier too.
-/
import RwLog.Rungs.Tabled.Machine

namespace RwLog

namespace R002

open R000 Cost

/-! ## Eagerly -/

namespace Eager

/-- Replace every call by the body of its definition; one tick per node. -/
def unfold (P : Program) : Rel → Cost Rel
  | .zero => do tick 1; pure .zero
  | .span s => do tick 1; pure (.span s)
  | .or a b => do
    tick 1
    let a' ← unfold P a
    let b' ← unfold P b
    pure (.or a' b')
  | .and a b => do
    tick 1
    let a' ← unfold P a
    let b' ← unfold P b
    pure (.and a' b')
  | .seq a b => do
    tick 1
    let a' ← unfold P a
    let b' ← unfold P b
    pure (.seq a' b')
  | .conv a => do
    tick 1
    let a' ← unfold P a
    pure (.conv a')
  | .call n => do tick 1; pure (P.body n)

def unfoldN (P : Program) : Nat → Rel → Cost Rel
  | 0, e => pure e
  | k + 1, e => do
    let e' ← unfold P e
    unfoldN P k e'

end Eager

/-- Join two chains, fusing the spans that meet. -/
def joinSeq (p q : List Rel) : Cost (Option (List Rel)) :=
  match p.getLast?, q with
  | some (.span a), .span b :: q' => do
    let c ← Charged.compose a b
    pure (c.map fun c => p.dropLast ++ .span c :: q')
  | _, _ => pure (some (p ++ q))

/-- Conjoin two products. -/
def mkAnd (p q : List Rel) : Cost (Option (List Rel)) :=
  match p, q with
  | [.span a], [.span b] => do
    let c ← Charged.meet a b
    pure (c.map fun c => [.span c])
  | _, _ => pure (some [.and (toRel p) (toRel q)])

/-- The span of a product that is a single span. -/
def single : List Rel → Option Span
  | [.span s] => some s
  | _ => none

/-- The products that are a single span, as spans. A product of a normal form
that contains no call is a single span (`open_calls`), so when no product of
the unfolding contains a call these are all its answers. -/
def closed (N : List (List Rel)) : List Span := N.filterMap single

namespace Eager

/-- The normal form as a list of products; one tick per node, a span leaf
charged by its size. The products of the second factor of a sequence are
recomputed for each product of the first, as rung zero's `norm` does. -/
def norm : Bool → Rel → Cost (List (List Rel))
  | _, .zero => do tick 1; pure []
  | neg, .span s => do tick (1 + s.size); pure [[.span (if neg then s.swap else s)]]
  | neg, .or a b => do
    tick 1
    let xs ← norm neg a
    let ys ← norm neg b
    pure (xs ++ ys)
  | false, .seq a b => do
    tick 1
    let ps ← norm false a
    flatMapL (fun p => do
      let qs ← norm false b
      filterMapL (joinSeq p) qs) ps
  | true, .seq a b => do
    tick 1
    let ps ← norm true b
    flatMapL (fun p => do
      let qs ← norm true a
      filterMapL (joinSeq p) qs) ps
  | neg, .and a b => do
    tick 1
    let ps ← norm neg a
    flatMapL (fun p => do
      let qs ← norm neg b
      filterMapL (mkAnd p) qs) ps
  | neg, .conv a => do
    tick 1
    norm (!neg) a
  | neg, .call n => do tick 1; pure [[if neg then .conv (.call n) else .call n]]

end Eager

/-- R001's unfolding race: build the unfolding, normalize it, then look. -/
def eager : Oracle := fun P d g => do
  let e ← Eager.unfoldN P d g.rel
  let ps ← Eager.norm false e
  if ps.all fun p => (toRel p).calls.isEmpty then do
    let xs ← flatMapL (Tabled.live P.theory) (closed ps)
    pure (true, xs)
  else pure (false, [])

/-! ## On demand -/

/-- The first factor of a product, when it is a span. -/
def headSpan (p : List Rel) : Option Span :=
  match p with
  | .span a :: _ => some a
  | _ => none

/-- The last factor of a product, when it is a span. -/
def lastSpan (p : List Rel) : Option Span :=
  match p.getLast? with
  | some (.span a) => some a
  | _ => none

/-- The product can still be fused with the chain `L` on its left. An empty
chain is not tested. -/
def aliveL (L : List Span) (p : List Rel) : Cost Bool :=
  match L, headSpan p with
  | _ :: _, some s => Charged.composable (L ++ [s])
  | _, _ => pure true

/-- The product can still be fused with the chain `R` on its right. -/
def aliveR (p : List Rel) (R : List Span) : Cost Bool :=
  match R, lastSpan p with
  | _ :: _, some s => Charged.composable (s :: R)
  | _, _ => pure true

def alive (L : List Span) (p : List Rel) (R : List Span) : Cost Bool := do
  let a ← aliveL L p
  if a then aliveR p R else pure false

/-- The span every product of the expression starts with, when the expression
itself says so: `some (s, true)` when the expression is that span, and
`some (s, false)` when it is a sequence that starts with it. With `neg` the
converse of the expression is read. -/
def staticFirst : Bool → Rel → Option (Span × Bool)
  | neg, .span s => some (if neg then s.swap else s, true)
  | false, .seq a _ => (staticFirst false a).map fun r => (r.1, false)
  | true, .seq _ b => (staticFirst true b).map fun r => (r.1, false)
  | neg, .conv a => staticFirst (!neg) a
  | _, _ => none

/-- The chain to the right of the first factor of a sequence whose second
factor is `e` and which itself has the chain `R` to its right. -/
def rightOf (neg : Bool) (e : Rel) (R : List Span) : List Span :=
  match staticFirst neg e with
  | some (t, true) => t :: R
  | some (t, false) => [t]
  | none => []

/-- The chain to the left of the second factor of a sequence, after the
product `p` of its first factor, which itself has the chain `L` to its left. -/
def leftAfter (L : List Span) (p : List Rel) : List Span :=
  match p with
  | [.span a] => L ++ [a]
  | _ => (lastSpan p).toList

/-- What the walk carries: stop, and the products handed to the top so far. -/
abbrev Walk := Bool × List (List Rel)

/-- Walk the products of the normal form of `e` unfolded `d` times (of its
converse with `neg`), handing each one that is alive between the chains `L`
and `R` to `k`, in the normalizer's order, until `k` says stop. One tick per
node visited. -/
def walk (P : Program) : (d : Nat) → Bool → (e : Rel) → List Span → List Span →
    (List Rel → List (List Rel) → Cost Walk) → List (List Rel) → Cost Walk
  | _, _, .zero, _, _, _, acc => do tick 1; pure (false, acc)
  | _, neg, .span s, L, R, k, acc => do
    tick 1
    let p := [Rel.span (if neg then s.swap else s)]
    let a ← alive L p R
    if a then k p acc else pure (false, acc)
  | d, neg, .or a b, L, R, k, acc => do
    tick 1
    let r ← walk P d neg a L R k acc
    if r.1 then pure r else walk P d neg b L R k r.2
  | d, false, .seq a b, L, R, k, acc => do
    tick 1
    walk P d false a L (rightOf false b R) (fun p acc =>
      walk P d false b (leftAfter L p) R (fun q acc => do
        let r ← joinSeq p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← aliveR r R
          if a then k r acc else pure (false, acc)) acc) acc
  | d, true, .seq a b, L, R, k, acc => do
    tick 1
    walk P d true b L (rightOf true a R) (fun p acc =>
      walk P d true a (leftAfter L p) R (fun q acc => do
        let r ← joinSeq p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← aliveR r R
          if a then k r acc else pure (false, acc)) acc) acc
  | d, neg, .and a b, L, R, k, acc => do
    tick 1
    walk P d neg a [] [] (fun p acc =>
      walk P d neg b [] [] (fun q acc => do
        let r ← mkAnd p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← alive L r R
          if a then k r acc else pure (false, acc)) acc) acc
  | d, neg, .conv a, L, R, k, acc => do
    tick 1
    walk P d (!neg) a L R k acc
  | 0, neg, .call n, _, _, k, acc => do
    tick 1
    k [if neg then .conv (.call n) else .call n] acc
  | d + 1, neg, .call n, L, R, k, acc => do
    tick 1
    walk P d neg (P.body n) L R k acc
termination_by d _ e => (d, sizeOf e)

/-- R002's unfolding race: walk the products on demand, stop at the first one
that reaches the top with a call left in it. -/
def onDemand : Oracle := fun P d g => do
  let r ← walk P d false g.rel [] []
    (fun p acc => pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc))) []
  if r.1 then pure (false, [])
  else do
    let xs ← flatMapL (Tabled.live P.theory) (closed r.2)
    pure (true, xs)

end R002

end RwLog
