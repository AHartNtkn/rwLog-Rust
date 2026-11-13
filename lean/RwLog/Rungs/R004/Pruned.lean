/-
# The unfolding race, pruned from the right

R002's walk and R003's shared evaluation both go through the unfolded goal
from left to right. What stands to the left of a sub-expression is known when
it is reached, so a span that cannot follow it is dropped at once; what stands
to its right is known only where the expression itself says so (a span written
directly after it). A query that generates on the left and tests on the right,
`gen ; test`, is therefore answered by building everything `gen` produces and
discarding it at the end.

`pruned` answers the same question in two passes.

* **Right to left** (`walkR`). Go through the derivations of the unfolded goal
  with the second factor of every sequence first. For each derivation of the
  second factor, the spans it starts with are known (`front`), so a span of
  the first factor that does not compose with them is dropped where it stands,
  and nothing to its left is looked at for that derivation. Nothing is
  composed in this pass: a derivation is recorded as the expression it follows
  (`Path.pe`: the goal's unfolding with one branch of every choice taken) and
  the branches it took (`Path.key`).
* **Left to right** (`collect`). Each derivation that reaches the top is
  normalized as it stands. It is one product of the normal form, or none if a
  fusion fails. If the product still contains a call the unfolding is not
  final and the walk stops, as R002's does. Otherwise the product is kept
  under its key, and at the end the products are put in the normalizer's
  order, which is the order of their keys.

The first pass only drops derivations whose product would be dropped, and the
second builds each remaining product by the normalizer's own compositions in
the normalizer's order. So the answer is the same list of the same spans as
R001's unfolding race, not merely an equivalent one (obligation
`pruned_exact`); the repeats are removed at the end, as in R003.

The two passes can cost more than the walk: the second composes each
derivation from the left, and the spans built that way can be much larger
than what the first pass looked at. R004 therefore races `pruned` against
R003's unfolder (`Engine.lean`).

A conjunction and a call left at depth zero are barriers, as in the walk:
nothing is tested across them.
-/
import RwLog.Rungs.R003.Engine

namespace RwLog

namespace R004

open R000 Cost

/-- The branches a derivation takes: which side of each choice, and the two
halves at a sequence or a conjunction. -/
inductive Key where
  | leaf : Key
  | inl : Key → Key
  | inr : Key → Key
  | pair : Key → Key → Key
  deriving DecidableEq, Repr

namespace Key

/-- The order in which the normalizer lists products: the left branch of a
choice before the right one, and the first half of a pair before the
second. -/
def lt : Key → Key → Bool
  | .inl a, .inl b => lt a b
  | .inl _, .inr _ => true
  | .inr a, .inr b => lt a b
  | .pair a b, .pair c d => lt a c || (decide (a = c) && lt b d)
  | _, _ => false

def size : Key → Nat
  | .leaf => 1
  | .inl a => 1 + size a
  | .inr a => 1 + size a
  | .pair a b => 1 + size a + size b

end Key

/-- A derivation of the unfolded goal: the branches it takes, and the
expression that is left when they are taken. The expression is read left to
right as it stands: converses are already pushed to its spans and calls. -/
structure Path where
  key : Key
  pe : Rel
  deriving DecidableEq, Repr

/-- The spans a derivation starts with, followed by the chain `R` when the
derivation is nothing but spans. -/
def front : Rel → List Span → List Span
  | .span s, R => s :: R
  | .seq a b, R => front a (front b R)
  | _, _ => []

/-- Can the span be fused with the chain on its right? An empty chain is not
tested. -/
def fits (s : Span) (R : List Span) : Cost Bool :=
  match R with
  | [] => pure true
  | _ :: _ => Charged.composable (s :: R)

/-- Walk the derivations of `e` unfolded `d` times (of its converse with
`neg`) that can be followed by the chain `R`, the second factor of a sequence
first, handing each one to `k` until `k` says stop. One tick per node visited,
and a span is charged by its size. -/
def walkR {α : Type} (P : Program) : (d : Nat) → Bool → (e : Rel) → List Span →
    (Path → α → Cost (Bool × α)) → α → Cost (Bool × α)
  | _, _, .zero, _, _, acc => do tick 1; pure (false, acc)
  | _, neg, .span s, R, k, acc => do
    let s' := if neg then s.swap else s
    tick (1 + s'.size)
    let a ← fits s' R
    if a then k ⟨.leaf, .span s'⟩ acc else pure (false, acc)
  | d, neg, .or a b, R, k, acc => do
    tick 1
    let r ← walkR P d neg a R (fun x acc => k ⟨.inl x.key, x.pe⟩ acc) acc
    if r.1 then pure r else walkR P d neg b R (fun y acc => k ⟨.inr y.key, y.pe⟩ acc) r.2
  | d, false, .seq a b, R, k, acc => do
    tick 1
    walkR P d false b R (fun q acc =>
      walkR P d false a (front q.pe R) (fun p acc =>
        k ⟨.pair p.key q.key, .seq p.pe q.pe⟩ acc) acc) acc
  | d, true, .seq a b, R, k, acc => do
    tick 1
    walkR P d true a R (fun q acc =>
      walkR P d true b (front q.pe R) (fun p acc =>
        k ⟨.pair p.key q.key, .seq p.pe q.pe⟩ acc) acc) acc
  | d, neg, .and a b, _, k, acc => do
    tick 1
    walkR P d neg a [] (fun x acc =>
      walkR P d neg b [] (fun y acc =>
        k ⟨.pair x.key y.key, .and x.pe y.pe⟩ acc) acc) acc
  | d, neg, .conv a, R, k, acc => do
    tick 1
    walkR P d (!neg) a R k acc
  | 0, neg, .call n, _, k, acc => do
    tick 1
    k ⟨.leaf, if neg then .conv (.call n) else .call n⟩ acc
  | d + 1, neg, .call n, R, k, acc => do
    tick 1
    walkR P d neg (P.body n) R k acc
termination_by d _ e => (d, sizeOf e)

/-! ## The products, in the normalizer's order -/

/-- A product of the normal form, under the key of its derivation. -/
abbrev Found := Key × List Rel

/-- Normalize a derivation. Stop if its product still contains a call;
otherwise keep the product, if there is one. -/
def collect (x : Path) (acc : List Found) : Cost (Bool × List Found) := do
  let ps ← R002.Eager.norm false x.pe
  if ps.all fun p => (toRel p).calls.isEmpty then pure (false, ps.map (fun p => (x.key, p)) ++ acc)
  else pure (true, acc)

/-- Does `x` come before `y`? Charged by the sizes of the keys compared. -/
def before (x y : Found) : Cost Bool := do
  tick (x.1.size + y.1.size)
  pure (x.1.lt y.1)

/-- Put a product in its place in an ordered list. -/
def insert (x : Found) : List Found → Cost (List Found)
  | [] => pure [x]
  | y :: ys => do
    let b ← before x y
    if b then pure (x :: y :: ys) else do
      let r ← insert x ys
      pure (y :: r)

/-- The products in the normalizer's order. -/
def sort (xs : List Found) : Cost (List Found) := foldL (fun acc x => insert x acc) [] xs

/-! ## The race -/

/-- The unfolding race, pruned from the right: the derivations that survive
the walk from the right, each normalized from the left, in the normalizer's
order. -/
def pruned : Oracle := fun P d g => do
  let r ← walkR P d false g.rel [] collect []
  if r.1 then pure (false, [])
  else do
    let ys ← sort r.2
    let zs ← flatMapL (Tabled.live P.theory) (ys.flatMap fun y => derivs (toRel y.2))
    let ws ← foldL R003.addSpan [] zs
    pure (true, ws)

end R004

end RwLog
