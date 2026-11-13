/-
# The unfolding race pruned from the right, written against the kernel

The pruned race of `Pruned.lean` (which says what it does and why), written
for an arbitrary type of spans and an arbitrary monad: everything it does to a
span is an operation of the kernel (`Trusted/Kernel.lean`). `Pruned.lean` is
this text read at the kernel of the language (`Reading.lean` proves they are
equal).
-/
import RwLog.Rungs.R003.Gen
import RwLog.Rungs.R004.Pruned

namespace RwLog

namespace R004

namespace Gen

open R001 Traverse

variable {Sp : Type} {M : Type → Type} [Kernel Sp M]

/-- The spans a derivation starts with, followed by the chain `R` when the
derivation is nothing but spans. -/
def front : (RelOf Sp) → List Sp → List Sp
  | .span s, R => s :: R
  | .seq a b, R => front a (front b R)
  | _, _ => []

/-- Can the span be fused with the chain on its right? An empty chain is not
tested. -/
def fits (s : Sp) (R : List Sp) : M Bool :=
  match R with
  | [] => pure true
  | _ :: _ => Kernel.composable (s :: R)

/-- Walk the derivations of `e` unfolded `d` times (of its converse with
`neg`) that can be followed by the chain `R`, the second factor of a sequence
first, handing each one to `k` until `k` says stop. One tick per node visited,
and a span is charged by its size. -/
def walkR {α : Type} (P : (ProgramOf Sp)) : (d : Nat) → Bool → (e : (RelOf Sp)) → List Sp →
    ((PathOf Sp) → α → M (Bool × α)) → α → M (Bool × α)
  | _, _, .zero, _, _, acc => do Kernel.tick Sp 1; pure (false, acc)
  | _, neg, .span s, R, k, acc => do
    let s' := if neg then Kernel.swap s else s
    Kernel.tick Sp (1 + Kernel.size s')
    let a ← fits s' R
    if a then k ⟨.leaf, .span s'⟩ acc else pure (false, acc)
  | d, neg, .or a b, R, k, acc => do
    Kernel.tick Sp 1
    let r ← walkR P d neg a R (fun x acc => k ⟨.inl x.key, x.pe⟩ acc) acc
    if r.1 then pure r else walkR P d neg b R (fun y acc => k ⟨.inr y.key, y.pe⟩ acc) r.2
  | d, false, .seq a b, R, k, acc => do
    Kernel.tick Sp 1
    walkR P d false b R (fun q acc =>
      walkR P d false a (front q.pe R) (fun p acc =>
        k ⟨.pair p.key q.key, .seq p.pe q.pe⟩ acc) acc) acc
  | d, true, .seq a b, R, k, acc => do
    Kernel.tick Sp 1
    walkR P d true a R (fun q acc =>
      walkR P d true b (front q.pe R) (fun p acc =>
        k ⟨.pair p.key q.key, .seq p.pe q.pe⟩ acc) acc) acc
  | d, neg, .and a b, _, k, acc => do
    Kernel.tick Sp 1
    walkR P d neg a [] (fun x acc =>
      walkR P d neg b [] (fun y acc =>
        k ⟨.pair x.key y.key, .and x.pe y.pe⟩ acc) acc) acc
  | d, neg, .conv a, R, k, acc => do
    Kernel.tick Sp 1
    walkR P d (!neg) a R k acc
  | 0, neg, .call n, _, k, acc => do
    Kernel.tick Sp 1
    k ⟨.leaf, if neg then .conv (.call n) else .call n⟩ acc
  | d + 1, neg, .call n, R, k, acc => do
    Kernel.tick Sp 1
    walkR P d neg (P.body n) R k acc
termination_by d _ e => (d, sizeOf e)

/-! ## The products, in the normalizer's order -/

/-- A product of the normal form, under the key of its derivation. -/
abbrev Found (Sp : Type) := Key × List (RelOf Sp)

/-- Normalize a derivation. Stop if its product still contains a call;
otherwise keep the product, if there is one. -/
def collect (x : (PathOf Sp)) (acc : List (Found Sp)) : M (Bool × List (Found Sp)) := do
  let ps ← R002.Gen.Eager.norm false x.pe
  if ps.all fun p => (R002.Gen.toRel p).calls.isEmpty then pure (false, ps.map (fun p => (x.key, p)) ++ acc)
  else pure (true, acc)

/-- Does `x` come before `y`? Charged by the sizes of the keys compared. -/
def before (x y : (Found Sp)) : M Bool := do
  Kernel.tick Sp (x.1.size + y.1.size)
  pure (x.1.lt y.1)

/-- Put a product in its place in an ordered list. -/
def insert (x : (Found Sp)) : List (Found Sp) → M (List (Found Sp))
  | [] => pure [x]
  | y :: ys => do
    let b ← before x y
    if b then pure (x :: y :: ys) else do
      let r ← insert x ys
      pure (y :: r)

/-- The products in the normalizer's order. -/
def sort (xs : List (Found Sp)) : M (List (Found Sp)) := foldL (fun acc x => insert x acc) [] xs

/-! ## The race -/

/-- The unfolding race, pruned from the right: the derivations that survive
the walk from the right, each normalized from the left, in the normalizer's
order. -/
def pruned : GOracle Sp M := fun P d g => do
  let r ← walkR P d false g.rel [] collect []
  if r.1 then pure (false, [])
  else do
    let ys ← sort r.2
    let zs ← flatMapL (Tabled.Gen.live P.theory) (R002.Gen.closed (ys.map Prod.snd))
    let ws ← foldL R003.Gen.addSpan [] zs
    pure (true, ws)

/-- R004's unfolding race: R003's unfolder and the evaluation pruned from the
right, side by side. -/
def unfolder : GOracle Sp M := fun P d g => Kernel.race Sp (R003.Gen.unfolder P d g) (pruned P d g)

end Gen

/-- R004 as an engine: the tabled machine with R004's race. -/
def engine : Engine := Tabled.Gen.engine Gen.unfolder

end R004

end RwLog
