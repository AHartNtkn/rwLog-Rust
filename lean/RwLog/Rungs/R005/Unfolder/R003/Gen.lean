/-
# The shared unfolding race, written against the kernel

The shared evaluation of `Shared.lean` (which says what it does and why),
written for an arbitrary type of spans and an arbitrary monad: everything it
does to a span is an operation of the kernel (`Trusted/Kernel.lean`).
`Shared.lean` is this text read at the kernel of the language
(`Reading.lean` proves they are equal).
-/
import RwLog.Rungs.R005.Unfolder.R002.Gen
import RwLog.Rungs.R005.Unfolder.R003.Shared

namespace RwLog

namespace R003

namespace Gen

open R001 Traverse

variable {Sp : Type} {M : Type → Type} [Kernel Sp M]

abbrev Memo (Sp : Type) := List ((KeyOf Sp) × (SummaryOf Sp))

/-- Are two left interfaces equivalent? -/
def sameCtx : Option Sp → Option Sp → M Bool
  | none, none => pure true
  | some a, some b => do
    let x ← Kernel.covers a b
    if x then Kernel.covers b a else pure false
  | _, _ => pure false

/-- Compare two keys: one tick, the size of the expressions when the rest
agrees, and the comparison of the interfaces when the expressions agree. -/
def sameKey (k k' : (KeyOf Sp)) : M Bool := do
  Kernel.tick Sp 1
  if k.neg = k'.neg ∧ k.d = k'.d then do
    let b ← Kernel.eqRel k.e k'.e
    if b then sameCtx k.ctx k'.ctx else pure false
  else pure false

def lookup (m : (Memo Sp)) (k : (KeyOf Sp)) : M (Option (SummaryOf Sp)) := do
  let r ← findL (fun p => sameKey p.1 k) m
  pure (r.map Prod.snd)

/-- Can the span be fused with the interface to its left? -/
def alive (ctx : Option Sp) (s : Sp) : M Bool :=
  match ctx with
  | none => pure true
  | some c => Kernel.composable [c, s]

/-- The interface left by the span `a` after the interface `ctx`. -/
def extend (ctx : Option Sp) (a : Sp) : M (Option Sp) :=
  match ctx with
  | none => Kernel.rightBound a
  | some c => do
    let z ← Kernel.compose c a
    match z with
    | some z => Kernel.rightBound z
    | none => pure none

/-- Add a span unless it is already there. -/
def addSpan (xs : List Sp) (x : Sp) : M (List Sp) := do
  let b ← anyL (fun y => Kernel.eq y x) xs
  pure (if b then xs else xs ++ [x])

/-- Are the two interfaces the same, as written? An absent interface counts
for one. -/
def eqOpt : Option Sp → Option Sp → M Bool
  | none, none => do Kernel.tick Sp 2; pure true
  | some a, some b => Kernel.eq a b
  | some a, none => do Kernel.tick Sp (Kernel.size a + 1); pure false
  | none, some b => do Kernel.tick Sp (1 + Kernel.size b); pure false

/-- Add an interface unless it is already there. -/
def addOpen (xs : List (Option Sp)) (x : Option Sp) : M (List (Option Sp)) := do
  let b ← anyL (fun y => eqOpt y x) xs
  pure (if b then xs else xs ++ [x])

/-- Look the key up; compute and record the summary if it is not there. -/
def memo (k : (KeyOf Sp)) (m : (Memo Sp)) (body : (Memo Sp) → M ((SummaryOf Sp) × (Memo Sp))) : M ((SummaryOf Sp) × (Memo Sp)) := do
  let hit ← lookup m k
  match hit with
  | some s => pure (s, m)
  | none => do
    let r ← body m
    pure (r.1, (k, r.1) :: r.2)

/-- What the evaluation of a sequence carries: the summary so far and the
memo. -/
abbrev Acc (Sp : Type) := List Sp × List (Option Sp) × (Memo Sp)

/-- After the span `x` of the first factor: every product of the second
factor that can follow it. -/
def afterSpan (ctx : Option Sp) (second : Option Sp → (Memo Sp) → M ((SummaryOf Sp) × (Memo Sp)))
    (acc : (Acc Sp)) (x : Sp) : M (Acc Sp) := do
  let c ← extend ctx x
  let r ← second c acc.2.2
  let zs ← filterMapL (fun y => Kernel.compose x y) r.1.spans
  let spans ← foldL addSpan acc.1 zs
  let opens ← foldL addOpen acc.2.1 r.1.opens
  pure (spans, opens, r.2)

/-- After a product of the first factor that contains a call and leaves the
interface `c`: every product of the second factor that can follow it. All of
them still contain the call. -/
def afterOpen (second : Option Sp → (Memo Sp) → M ((SummaryOf Sp) × (Memo Sp)))
    (acc : (Acc Sp)) (c : Option Sp) : M (Acc Sp) := do
  let r ← second c acc.2.2
  let os ← mapL (extend c) r.1.spans
  let opens ← foldL addOpen acc.2.1 (os ++ r.1.opens)
  pure (acc.1, opens, r.2)

/-- The sequence of a factor already evaluated and a second one. -/
def seqSummary (ctx : Option Sp) (first : (SummaryOf Sp))
    (second : Option Sp → (Memo Sp) → M ((SummaryOf Sp) × (Memo Sp))) (m : (Memo Sp)) : M ((SummaryOf Sp) × (Memo Sp)) := do
  let a ← foldL (afterSpan ctx second) ([], [], m) first.spans
  let b ← foldL (afterOpen second) a first.opens
  pure (⟨b.1, b.2.1⟩, b.2.2)

/-- The conjunction of two factors evaluated with nothing to their left. -/
def andSummary (ctx : Option Sp) (a b : (SummaryOf Sp)) : M (SummaryOf Sp) := do
  let zs ← flatMapL (fun x => filterMapL (fun y => Kernel.meet x y) b.spans) a.spans
  let ws ← filterL (alive ctx) zs
  let spans ← foldL addSpan [] ws
  let some_ (s : (SummaryOf Sp)) : Bool := !s.spans.isEmpty || !s.opens.isEmpty
  let open_ := (!a.opens.isEmpty && some_ b) || (some_ a && !b.opens.isEmpty)
  pure ⟨spans, if open_ then [none] else []⟩

/-- The summary of `e` unfolded `d` times (of its converse with `neg`) after
the interface `ctx`. One tick per node evaluated. -/
def eval (P : (ProgramOf Sp)) : (d : Nat) → Bool → (e : (RelOf Sp)) → Option Sp → (Memo Sp) →
    M ((SummaryOf Sp) × (Memo Sp))
  | _, _, .zero, _, m => do Kernel.tick Sp 1; pure (⟨[], []⟩, m)
  | _, neg, .span s, ctx, m => do
    Kernel.tick Sp 1
    let s' := if neg then Kernel.swap s else s
    let a ← alive ctx s'
    pure (⟨if a then [s'] else [], []⟩, m)
  | d, neg, .or a b, ctx, m => memo ⟨neg, .or a b, d, ctx⟩ m fun m => do
    Kernel.tick Sp 1
    let x ← eval P d neg a ctx m
    let y ← eval P d neg b ctx x.2
    let spans ← foldL addSpan x.1.spans y.1.spans
    let opens ← foldL addOpen x.1.opens y.1.opens
    pure (⟨spans, opens⟩, y.2)
  | d, false, .seq a b, ctx, m => memo ⟨false, .seq a b, d, ctx⟩ m fun m => do
    Kernel.tick Sp 1
    let x ← eval P d false a ctx m
    seqSummary ctx x.1 (fun c m => eval P d false b c m) x.2
  | d, true, .seq a b, ctx, m => memo ⟨true, .seq a b, d, ctx⟩ m fun m => do
    Kernel.tick Sp 1
    let x ← eval P d true b ctx m
    seqSummary ctx x.1 (fun c m => eval P d true a c m) x.2
  | d, neg, .and a b, ctx, m => memo ⟨neg, .and a b, d, ctx⟩ m fun m => do
    Kernel.tick Sp 1
    let x ← eval P d neg a none m
    let y ← eval P d neg b none x.2
    let s ← andSummary ctx x.1 y.1
    pure (s, y.2)
  | d, neg, .conv a, ctx, m => do
    Kernel.tick Sp 1
    eval P d (!neg) a ctx m
  | 0, _, .call _, _, m => do Kernel.tick Sp 1; pure (⟨[], [none]⟩, m)
  | d + 1, neg, .call n, ctx, m => memo ⟨neg, .call n, d + 1, ctx⟩ m fun m => do
    Kernel.tick Sp 1
    eval P d neg (P.body n) ctx m
termination_by d _ e => (d, sizeOf e)

/-- The unfolding race with shared work: final when no product still contains
a call, and then the spans of the products, without repeats. -/
def shared : GOracle Sp M := fun P d g => do
  let r ← eval P d false g.rel none []
  if r.1.opens.isEmpty then do
    let xs ← flatMapL (Tabled.Gen.live P.theory) r.1.spans
    let ys ← foldL addSpan [] xs
    pure (true, ys)
  else pure (false, [])

/-- R003's unfolding race: the walk and the shared evaluation, side by side. -/
def unfolder : GOracle Sp M := fun P d g => Kernel.race Sp (R002.Gen.onDemand P d g) (shared P d g)

end Gen

/-- R003 as an engine: the tabled machine with R003's race. -/
def engine : Engine := Tabled.Gen.engine Gen.unfolder

end R003

end RwLog
