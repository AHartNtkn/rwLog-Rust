/-
# The unfolding race with shared work

R002's walk answers the unfolding race by going through the products of the
unfolded goal one at a time. When many derivations meet in the same place it
goes through what follows once for each of them: on a graph where two edges
leave every node and meet again, it follows every path, and there are `2 ^ k`
of those through `k` such nodes, although only `k` nodes are ever reached.

`shared` answers the same question by computing, for a sub-expression and
what stands to its left, the products that can still be fused with that left
side, once:

* a product without a call is a single span, and only one copy of a span is
  kept (the first);
* a product with a call matters only through what it leaves to its right, so
  that is all that is kept of it;
* what stands to the left of a sub-expression matters only through its right
  interface (`Span.rightIface`), so a sub-expression reached from two
  derivations that leave equivalent interfaces is evaluated once and the
  result is looked up the second time (`Memo`).

The spans are built by the same compositions as the normalizer's, in the same
order, so the answer is the walk's answer with the repeated spans removed
(obligation `shared_exact`). Removing repeats does not change what the tabled
machine does with the answer.

Unlike the walk, `shared` does not stop at the first product that still
contains a call: it finishes every sub-expression it starts. Where the walk
stops early `shared` can be far more expensive, so R003 runs the two side by
side (`Engine.lean`).

A conjunction is a barrier, as in the walk: its two sides are evaluated with
nothing to their left.
-/
import RwLog.Rungs.R002.Unfold

namespace RwLog

namespace R003

open R001 Cost

/-- The products of a sub-expression that can be fused with what stands to its
left: the spans of the ones without a call, in the normalizer's order and
without repeats, and, for each one with a call, what it leaves to its right
(`none`: no restriction). -/
structure SummaryOf (S : Type) where
  spans : List S
  opens : List (Option S)

abbrev Summary := SummaryOf Span

/-- What a summary was computed for: the expression (its converse with `neg`),
the unfolding depth, and the interface to its left. -/
structure KeyOf (S : Type) where
  neg : Bool
  e : RelOf S
  d : Nat
  ctx : Option S

abbrev Key := KeyOf Span

abbrev Memo := List (Key × Summary)

/-- Are two left interfaces equivalent? -/
def sameCtx : Option Span → Option Span → Cost Bool
  | none, none => pure true
  | some a, some b => do
    let x ← Charged.covers a b
    if x then Charged.covers b a else pure false
  | _, _ => pure false

/-- Compare two keys: one tick, the size of the expressions when the rest
agrees, and the comparison of the interfaces when the expressions agree. -/
def sameKey (k k' : Key) : Cost Bool := do
  tick 1
  if k.neg = k'.neg ∧ k.d = k'.d then do
    tick (k.e.size + k'.e.size)
    if k.e = k'.e then sameCtx k.ctx k'.ctx else pure false
  else pure false

def lookup (m : Memo) (k : Key) : Cost (Option Summary) := do
  let r ← findL (fun p => sameKey p.1 k) m
  pure (r.map Prod.snd)

/-- Can the span be fused with the interface to its left? -/
def alive (ctx : Option Span) (s : Span) : Cost Bool :=
  match ctx with
  | none => pure true
  | some c => Charged.composable [c, s]

/-- The interface left by the span `a` after the interface `ctx`. -/
def extend (ctx : Option Span) (a : Span) : Cost (Option Span) :=
  match ctx with
  | none => do
    tick a.size
    pure (bound a.rightIface)
  | some c => do
    let z ← Charged.compose c a
    match z with
    | some z => do
      tick z.size
      pure (bound z.rightIface)
    | none => pure none

/-- Add a span unless it is already there. -/
def addSpan (xs : List Span) (x : Span) : Cost (List Span) := do
  let b ← anyL (fun y => do tick (x.size + y.size); pure (decide (y = x))) xs
  pure (if b then xs else xs ++ [x])

def optSize : Option Span → Nat
  | none => 1
  | some s => s.size

/-- Add an interface unless it is already there. -/
def addOpen (xs : List (Option Span)) (x : Option Span) : Cost (List (Option Span)) := do
  let b ← anyL (fun y => do tick (optSize x + optSize y); pure (decide (y = x))) xs
  pure (if b then xs else xs ++ [x])

/-- Look the key up; compute and record the summary if it is not there. -/
def memo (k : Key) (m : Memo) (body : Memo → Cost (Summary × Memo)) : Cost (Summary × Memo) := do
  let hit ← lookup m k
  match hit with
  | some s => pure (s, m)
  | none => do
    let r ← body m
    pure (r.1, (k, r.1) :: r.2)

/-- What the evaluation of a sequence carries: the summary so far and the
memo. -/
abbrev Acc := List Span × List (Option Span) × Memo

/-- After the span `x` of the first factor: every product of the second
factor that can follow it. -/
def afterSpan (ctx : Option Span) (second : Option Span → Memo → Cost (Summary × Memo))
    (acc : Acc) (x : Span) : Cost Acc := do
  let c ← extend ctx x
  let r ← second c acc.2.2
  let zs ← filterMapL (fun y => Charged.compose x y) r.1.spans
  let spans ← foldL addSpan acc.1 zs
  let opens ← foldL addOpen acc.2.1 r.1.opens
  pure (spans, opens, r.2)

/-- After a product of the first factor that contains a call and leaves the
interface `c`: every product of the second factor that can follow it. All of
them still contain the call. -/
def afterOpen (second : Option Span → Memo → Cost (Summary × Memo))
    (acc : Acc) (c : Option Span) : Cost Acc := do
  let r ← second c acc.2.2
  let os ← mapL (extend c) r.1.spans
  let opens ← foldL addOpen acc.2.1 (os ++ r.1.opens)
  pure (acc.1, opens, r.2)

/-- The sequence of a factor already evaluated and a second one. -/
def seqSummary (ctx : Option Span) (first : Summary)
    (second : Option Span → Memo → Cost (Summary × Memo)) (m : Memo) : Cost (Summary × Memo) := do
  let a ← foldL (afterSpan ctx second) ([], [], m) first.spans
  let b ← foldL (afterOpen second) a first.opens
  pure (⟨b.1, b.2.1⟩, b.2.2)

/-- The conjunction of two factors evaluated with nothing to their left. -/
def andSummary (ctx : Option Span) (a b : Summary) : Cost Summary := do
  let zs ← flatMapL (fun x => filterMapL (fun y => Charged.meet x y) b.spans) a.spans
  let ws ← filterL (alive ctx) zs
  let spans ← foldL addSpan [] ws
  let some_ (s : Summary) : Bool := !s.spans.isEmpty || !s.opens.isEmpty
  let open_ := (!a.opens.isEmpty && some_ b) || (some_ a && !b.opens.isEmpty)
  pure ⟨spans, if open_ then [none] else []⟩

/-- The summary of `e` unfolded `d` times (of its converse with `neg`) after
the interface `ctx`. One tick per node evaluated. -/
def eval (P : Program) : (d : Nat) → Bool → (e : Rel) → Option Span → Memo →
    Cost (Summary × Memo)
  | _, _, .zero, _, m => do tick 1; pure (⟨[], []⟩, m)
  | _, neg, .span s, ctx, m => do
    tick 1
    let s' := if neg then s.swap else s
    let a ← alive ctx s'
    pure (⟨if a then [s'] else [], []⟩, m)
  | d, neg, .or a b, ctx, m => memo ⟨neg, .or a b, d, ctx⟩ m fun m => do
    tick 1
    let x ← eval P d neg a ctx m
    let y ← eval P d neg b ctx x.2
    let spans ← foldL addSpan x.1.spans y.1.spans
    let opens ← foldL addOpen x.1.opens y.1.opens
    pure (⟨spans, opens⟩, y.2)
  | d, false, .seq a b, ctx, m => memo ⟨false, .seq a b, d, ctx⟩ m fun m => do
    tick 1
    let x ← eval P d false a ctx m
    seqSummary ctx x.1 (fun c m => eval P d false b c m) x.2
  | d, true, .seq a b, ctx, m => memo ⟨true, .seq a b, d, ctx⟩ m fun m => do
    tick 1
    let x ← eval P d true b ctx m
    seqSummary ctx x.1 (fun c m => eval P d true a c m) x.2
  | d, neg, .and a b, ctx, m => memo ⟨neg, .and a b, d, ctx⟩ m fun m => do
    tick 1
    let x ← eval P d neg a none m
    let y ← eval P d neg b none x.2
    let s ← andSummary ctx x.1 y.1
    pure (s, y.2)
  | d, neg, .conv a, ctx, m => do
    tick 1
    eval P d (!neg) a ctx m
  | 0, _, .call _, _, m => do tick 1; pure (⟨[], [none]⟩, m)
  | d + 1, neg, .call n, ctx, m => memo ⟨neg, .call n, d + 1, ctx⟩ m fun m => do
    tick 1
    eval P d neg (P.body n) ctx m
termination_by d _ e => (d, sizeOf e)

/-- The unfolding race with shared work: final when no product still contains
a call, and then the spans of the products, without repeats. -/
def shared : Oracle := fun P d g => do
  let r ← eval P d false g.rel none []
  if r.1.opens.isEmpty then do
    let xs ← flatMapL (Tabled.live P.theory) r.1.spans
    let ys ← foldL addSpan [] xs
    pure (true, ys)
  else pure (false, [])

end R003

end RwLog
