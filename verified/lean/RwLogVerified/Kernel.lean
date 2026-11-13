/-
# The kernel rung of the Rust store

`rustKernel z` is a kernel on the spans of the language (`RwLog.Kernel`,
`lean/RwLog/Trusted/Kernel.lean`). It returns what the specification kernel
`Kernel.std` returns (`rustKernel_refines`), and the charge of each operation
on terms is the number of ticks within which the Rust function on the store
of `verified/rust/src/store.rs` returns that result:

| operation | Rust | theorem |
|---|---|---|
| `compose` | `span::compose` | `compose_realised` |
| `meet` | `span::meet` | `meet_realised` |
| `composable` | `span::composable` | `composable_realised` |
| `eq` | `cover::span_eq` | `eq_realised` |
| `covers`, covering span without constraints | `cover::covers_plain` | `covers_realised` |
| `rightBound` | `cover::right_bound` | `rightBound_realised` |
| `leftBound` | `cover::left_bound` | `leftBound_realised` |

`Realises` is what each of those theorems says: from any store that keeps
the invariant, holds the arguments and has room on its tick counter, the Rust
function does not panic, returns the operation's value, only adds nodes, and
advances the tick counter by at most the operation's charge.

`z` is the symbol the end of a list reads back as (`nm none` for the naming
`nm` of the theorems). The charges count distinct subterms, and a list of
constraints is a term that ends in `z`.

Not derived here, and charged as `Kernel.std` charges them: `simplify` and
`covers` when the covering span has constraints (their algorithms are
replaced first, roadmap L39). `swap` exchanges two fields and touches no
store. `tick`, `race` and `metered` are those of the cost monad.

Space. The store only grows and an allocation is a tick, so an operation
that may add nodes is charged its tick bound as the cells it holds
(`Charged.op v t t`). `span_eq` and `covers_plain` leave the store as it was
(their theorems say so) and hold nothing.

The operations on nodes and on answers of a `DerivationKernel` are not
derived on the store: `DerivationKernel.over (rustKernel z)` charges them as
`Trusted/Charged.lean` postulates (roadmap L45).
-/
import RwLog.Trusted.KernelRung
import RwLogVerified.Chain
import RwLogVerified.Iface

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term

/-- The kernel whose charges for the operations on terms are the tick bounds
proved of the Rust functions. -/
@[reducible] def rustKernel (z : Sym) : Kernel Span Cost where
  tick := Cost.tick
  race := Cost.race
  metered := Cost.metered
  swap := Span.swap
  compose x y := Charged.op (x.compose y) (composeCost z x y) (composeCost z x y)
  meet x y := Charged.op (x.meet y) (meetCost z x y) (meetCost z x y)
  composable xs := Charged.op (Span.chain xs).isSome (composableCost z xs) (composableCost z xs)
  covers a s := if a.c = [] then Charged.op (a.covers? s) (coversPlainCost a) 0 else Charged.covers a s
  simplify := Charged.simplify
  eq x y := Charged.op (decide (x = y)) 3 0
  rightBound s := Charged.op (bound s.rightIface) (ifaceCost s.r s.c) (ifaceCost s.r s.c)
  leftBound s := Charged.op (bound s.leftIface) (ifaceCost s.l s.c) (ifaceCost s.l s.c)

/-- The Rust kernel returns what the specification kernel returns. -/
theorem rustKernel_refines (z : Sym) : Kernel.Refines (rustKernel z) where
  monad := rfl
  tick := rfl
  race _ _ _ := rfl
  metered _ _ := rfl
  swap := rfl
  compose _ _ := rfl
  meet _ _ := rfl
  composable _ := rfl
  covers a s := by
    show (if a.c = [] then Charged.op (a.covers? s) (coversPlainCost a) 0 else Charged.covers a s).val
      = a.covers? s
    split <;> rfl
  simplify _ _ := rfl
  eq _ _ := rfl
  rightBound _ := rfl
  leftBound _ := rfl

/-- The Rust function `F` computes the charged operation `f`. `RA` says the
Rust argument stands for the specification's argument in a list of nodes, and
`RB` says the same of the results. -/
def Realises {A' A B' B : Type} (RA : List store.Node → A' → A → Prop)
    (RB : List store.Node → B' → B → Prop)
    (F : store.Store → A' → Result (B' × store.Store)) (f : A → Cost B) : Prop :=
  ∀ (s : store.Store) (a' : A') (a : A), Inv s → RA s.nodes.val a' a → Room s (f a).ticks →
    F s a' ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ RB s'.nodes.val r (f a).val ∧
        s'.ticks.val ≤ s.ticks.val + (f a).ticks ⦄

variable {nm : Option Nat → Sym}

/-- Two Rust spans stand for two spans. -/
def SpansAt (nm : Option Nat → Sym) (nodes : List store.Node) (p : span.Span × span.Span)
    (q : Span × Span) : Prop :=
  SpanAt nm nodes p.1 q.1 ∧ SpanAt nm nodes p.2 q.2

theorem compose_realised (hnm : Function.Injective nm) :
    Realises (SpansAt nm) (OptSpanAt nm) (fun s p => span.compose s p.1 p.2)
      (fun q => (rustKernel (nm none)).compose q.1 q.2) := by
  rintro s ⟨x, y⟩ ⟨sx, sy⟩ hI ⟨hx, hy⟩ hroom
  exact compose_spec hnm s x y hI hx hy hroom

theorem meet_realised (hnm : Function.Injective nm) :
    Realises (SpansAt nm) (OptSpanAt nm) (fun s p => span.meet s p.1 p.2)
      (fun q => (rustKernel (nm none)).meet q.1 q.2) := by
  rintro s ⟨x, y⟩ ⟨sx, sy⟩ hI ⟨hx, hy⟩ hroom
  exact meet_spec hnm s x y hI hx hy hroom

theorem composable_realised (hnm : Function.Injective nm) :
    Realises
      (fun nodes (xs : store.TermId) (spans : List Span) =>
        Repr nm nodes xs.val (encList (nm none) (spans.map (packSpan (nm none)))))
      (fun _ (b b' : Bool) => b = b') span.composable
      (fun spans => (rustKernel (nm none)).composable spans) := by
  intro s xs spans hI hxs hroom
  exact composable_spec hnm s xs hI hxs hroom

theorem eq_realised (hnm : Function.Injective nm) :
    Realises (SpansAt nm) (fun _ (b b' : Bool) => b = b') (fun s p => cover.span_eq s p.1 p.2)
      (fun q => (rustKernel (nm none)).eq q.1 q.2) := by
  rintro s ⟨x, y⟩ ⟨sx, sy⟩ hI ⟨hx, hy⟩ hroom
  refine WP.spec_mono (span_eq_spec hnm s x y hI hx hy hroom) ?_
  rintro ⟨b, s'⟩ ⟨h1, h2, -, h4, h5⟩
  exact ⟨h1, Extends.of_eq h2, h4, h5⟩

/-- Coverage, when the covering span has no constraints. -/
theorem covers_realised (hnm : Function.Injective nm) :
    Realises (fun nodes p (q : Span × Span) => SpansAt nm nodes p q ∧ q.1.c = [])
      (fun _ (b b' : Bool) => b = b') (fun s p => cover.covers_plain s p.1 p.2)
      (fun q => (rustKernel (nm none)).covers q.1 q.2) := by
  rintro s ⟨a, x⟩ ⟨sa, sx⟩ hI ⟨⟨ha, hx⟩, hc⟩ hroom
  have hc : sa.c = [] := hc
  have e : (rustKernel (nm none)).covers sa sx = Charged.op (sa.covers? sx) (coversPlainCost sa) 0 := by
    show (if sa.c = [] then _ else _) = _
    simp [hc]
  simp only [e] at hroom ⊢
  refine WP.spec_mono (covers_plain_spec hnm s a x hI ha hx hc hroom) ?_
  rintro ⟨b, s'⟩ ⟨h1, h2, h3, h4⟩
  exact ⟨h1, Extends.of_eq h2, h3, h4⟩

theorem rightBound_realised (hnm : Function.Injective nm) :
    Realises (SpanAt nm) (OptSpanAt nm) cover.right_bound
      (fun sx => (rustKernel (nm none)).rightBound sx) := by
  intro s x sx hI hx hroom
  exact right_bound_spec hnm s x hI hx hroom

theorem leftBound_realised (hnm : Function.Injective nm) :
    Realises (SpanAt nm) (OptSpanAt nm) cover.left_bound
      (fun sx => (rustKernel (nm none)).leftBound sx) := by
  intro s x sx hI hx hroom
  exact left_bound_spec hnm s x hI hx hroom

end RwLogVerified
