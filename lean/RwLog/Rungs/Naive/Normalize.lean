/-
# Rung zero: unfolding and normalization

`unfold` replaces every call by the body of the called definition, once.
`norm` puts an expression into a list of *products* (chains of factors) with
no `or` left: it distributes `;` and `&` over `|`, pushes converse to the
leaves, fuses adjacent spans of a chain by matching, conjoins two single
spans, and drops a product as soon as a fusion has no match. It never
unfolds calls, so it always terminates.

`derivs` lists the spans an expression derives without unfolding any call.
-/
import RwLog.Rungs.Naive.Chain

namespace RwLog

namespace R000

variable (P : Program)

/-- Replace every call by the body of its definition. -/
def unfold : Rel → Rel
  | .zero => .zero
  | .span s => .span s
  | .or a b => .or (unfold a) (unfold b)
  | .and a b => .and (unfold a) (unfold b)
  | .seq a b => .seq (unfold a) (unfold b)
  | .conv a => .conv (unfold a)
  | .call n => P.body n

/-- Unfold `k` times. -/
def unfoldN (k : Nat) (e : Rel) : Rel := (unfold P)^[k] e

/-- Join two chains, fusing the spans that meet at the boundary. `none`
means the fusion has no match, so the product is empty. -/
def joinSeq (p q : List Rel) : Option (List Rel) :=
  match p.getLast?, q with
  | some (.span a), .span b :: q' => (a.compose b).map fun c => p.dropLast ++ .span c :: q'
  | _, _ => some (p ++ q)

/-- Conjoin two products; two single spans are met directly. -/
def mkAnd (p q : List Rel) : Option (List Rel) :=
  match p, q with
  | [.span a], [.span b] => (a.meet b).map fun c => [.span c]
  | _, _ => some [.and (toRel p) (toRel q)]

/-- Normal form as a list of products. With `neg = true` it normalizes the
converse of the expression. -/
def norm : Bool → Rel → List (List Rel)
  | _, .zero => []
  | neg, .span s => [[.span (if neg then s.swap else s)]]
  | neg, .or a b => norm neg a ++ norm neg b
  | false, .seq a b => (norm false a).flatMap fun p => (norm false b).filterMap (joinSeq p)
  | true, .seq a b => (norm true b).flatMap fun p => (norm true a).filterMap (joinSeq p)
  | neg, .and a b => (norm neg a).flatMap fun p => (norm neg b).filterMap (mkAnd p)
  | neg, .conv a => norm (!neg) a
  | neg, .call n => [[if neg then .conv (.call n) else .call n]]

/-- The spans an expression derives without unfolding any call. -/
def derivs : Rel → List Span
  | .zero => []
  | .span s => [s]
  | .or a b => derivs a ++ derivs b
  | .seq a b => (derivs a).flatMap fun s₁ => (derivs b).filterMap s₁.compose
  | .and a b => (derivs a).flatMap fun s₁ => (derivs b).filterMap s₁.meet
  | .conv a => (derivs a).map Span.swap
  | .call _ => []

/-- `e` or its converse. -/
def orient (neg : Bool) (e : Rel) : Rel := if neg then .conv e else e

def orientS (neg : Bool) (s : Span) : Span := if neg then s.swap else s

end R000

end RwLog
