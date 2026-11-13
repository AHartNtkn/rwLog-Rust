/-
# Running the kernel programs on the base machine

Each operation on terms is run as a program on the machine of the language
(`Prog.kernelProg`, `Kernel/Machine/Prog.lean`) and compared with what the
specification kernel returns, on every pair of a small family of spans. The
checks also record what some operations spend.
-/
import RwLog.Kernel.Machine.Prog
import RwLog.Trusted.Kernel

namespace RwLog.Tests.MachineKernel

def ops : TermOps Nat Mach := Prog.kernelProg.ops

/-- Write the spans into the first store, run `m` on them, and read the
result through the store it leaves; with the ticks `m` spent. -/
def runOn {α β : Type} (ss : List Span) (m : List (MSpan Nat) → Mach α)
    (read : Heap → α → β) : Option (β × Nat) :=
  let rec putAll : List Span → Mach (List (MSpan Nat))
    | [] => pure []
    | s :: ss => do
      let p ← Mach.putSpan s
      let ps ← putAll ss
      pure (p :: ps)
  match putAll ss Heap.init with
  | none => none
  | some r =>
    match m r.val.1 r.val.2 with
    | none => none
    | some r' => some (read r'.val.2 r'.val.1, r'.ticks)

def two {α : Type} (f : MSpan Nat → MSpan Nat → Mach α) (d : Mach α) : List (MSpan Nat) → Mach α
  | [x, y] => f x y
  | _ => d

def one {α : Type} (f : MSpan Nat → Mach α) (d : Mach α) : List (MSpan Nat) → Mach α
  | [x] => f x
  | _ => d

def v (n : Nat) : Pat := .var n
def c (f : String) : Pat := .sym f
def ap (a b : Pat) : Pat := .app a b

/-- Terms that share, clash, nest and repeat variables. -/
def terms : List Pat :=
  [v 0, v 1, c "a", c "b", ap (v 0) (v 0), ap (v 0) (v 1), ap (v 1) (v 0),
   ap (c "a") (v 0), ap (v 0) (c "a"), ap (ap (v 0) (v 1)) (v 0),
   ap (ap (v 0) (v 0)) (ap (v 0) (v 0)), ap (v 1) (ap (c "a") (v 1)),
   ap (ap (c "f") (v 2)) (ap (c "g") (v 0)), ap (ap (c "f") (ap (v 0) (v 1))) (ap (c "g") (v 2))]

def stores : List Store :=
  [[], [ap (c "p") (v 0)], [ap (c "p") (v 1), ap (c "q") (ap (v 0) (v 5))]]

/-- Spans over the terms: every pair of sides for the first few, with each
store. -/
def spans : List Span :=
  (terms.flatMap fun l => (terms.take 9).flatMap fun r => (stores.take 2).map fun s => ⟨l, r, s⟩) ++
  [⟨ap (v 0) (v 1), ap (v 1) (v 0), stores[2]!⟩, ⟨v 0, v 0, []⟩, ⟨v 3, v 3, [ap (c "p") (v 3)]⟩]

def pairs : List (Span × Span) :=
  let xs := spans
  (xs.zipIdx.flatMap fun (x, i) => (xs.zipIdx.filter fun (_, j) => (i * 7 + j * 3) % 11 == 0).map
    fun (y, _) => (x, y))

def readO (h : Heap) (r : Option (MSpan Nat)) : Option Span := r.map (MSpan.read h)

#guard 500 ≤ pairs.length

-- Composition and conjunction return the spans of the specification kernel.
#guard pairs.all fun (x, y) =>
  (runOn [x, y] (two ops.compose (pure none)) readO).map (·.1) == some (x.compose y)
#guard pairs.all fun (x, y) =>
  (runOn [x, y] (two ops.meet (pure none)) readO).map (·.1) == some (x.meet y)

-- Equality and coverage.
#guard pairs.all fun (x, y) =>
  (runOn [x, y] (two ops.eq (pure false)) fun _ b => b).map (·.1) == some (decide (x = y))
#guard spans.all fun x =>
  (runOn [x, x] (two ops.eq (pure false)) fun _ b => b).map (·.1) == some true
#guard pairs.all fun (x, y) =>
  let x' : Span := ⟨x.l, x.r, []⟩
  (runOn [x', y] (two ops.coversPlain (pure false)) fun _ b => b).map (·.1) == some (x'.covers? y)

-- Interfaces.
#guard spans.all fun x =>
  (runOn [x] (one ops.rightBound (pure none)) readO).map (·.1) == some (bound x.rightIface)
#guard spans.all fun x =>
  (runOn [x] (one ops.leftBound (pure none)) readO).map (·.1) == some (bound x.leftIface)

-- Chains.
#guard (pairs.take 200).all fun (x, y) =>
  (runOn [x, y, x.swap, y] ops.composable fun _ b => b).map (·.1) ==
    some (Span.chain [x, y, x.swap, y]).isSome
#guard (runOn [] ops.composable fun _ b => b).map (·.1) == some true

/-! ## Expressions -/

def runRel {β : Type} (es : List Rel) (m : List (RelOf (MSpan Nat)) → Mach β) : Option (β × Heap) :=
  let rec putAll : List Rel → Mach (List (RelOf (MSpan Nat)))
    | [] => pure []
    | s :: ss => do
      let p ← Mach.putRel s
      let ps ← putAll ss
      pure (p :: ps)
  match (do let ps ← putAll es; m ps : Mach β) Heap.init with
  | none => none
  | some r => some r.val

def rels : List Rel :=
  let s := spans.take 6 |>.map RelOf.span
  let base := s ++ [.zero, .call "f", .call "g"]
  base ++ (base.take 5).flatMap (fun a => (base.drop 3).flatMap fun b =>
    [.or a b, .or b a, .seq a b, .and a (.or b a), .conv (.or a (.or b a)),
     .or (.or a .zero) (.or b (.or a b))])

#guard rels.all fun e =>
  (runRel [e] fun
    | [x] => ops.canon x
    | _ => pure .zero).map (fun r => r.1.mapSpan (MSpan.read r.2)) == some (RwLog.canon e)

#guard (rels.take 40).all fun a => (rels.take 40).all fun b =>
  (runRel [a, b] fun
    | [x, y] => ops.eqRel x y
    | _ => pure false).map (·.1) == some (decide (a = b))

/-! ## Sharing is credited

`dbl` is `$0 -> ($0 $0)`. Composing `n` copies gives a span whose right side
is a full binary tree of `2 ^ n` leaves. The specification kernel charges the
tree; on the machine the chain test builds `n` nodes. -/

def dbl : Span := ⟨v 0, ap (v 0) (v 0), []⟩

def chainTicks (n : Nat) : Option Nat :=
  (runOn (List.replicate n dbl) ops.composable fun _ b => b).map (·.2)

#guard (Span.chain (List.replicate 10 dbl)).map (·.r.size) == some 2047
#guard ((List.range 7).map fun n => chainTicks (2 * n)).all Option.isSome
#guard (chainTicks 12).all fun t => t ≤ 20 * 12 * 12

end RwLog.Tests.MachineKernel
