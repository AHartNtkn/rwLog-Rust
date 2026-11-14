/-
# A Rust function realises a charged operation

`Realises RA RB F f` says that the Rust function `F` on the store of
`verified/rust/src/store.rs` computes the charged operation `f` of a kernel
(`RwLog.Kernel`, `lean/RwLog/Trusted/Kernel.lean`): from any store that
keeps the invariant, holds the arguments and has room on its tick counter,
`F` does not panic, returns the operation's value, only adds nodes, and
advances the tick counter by at most the operation's charge.

The store only grows and an allocation is a tick, so a function that spends
`t` ticks adds at most `t` nodes (`Extends.grown`), and a kernel whose
operations hold what they are charged (`Charged.op v t t`) is realised in
space as well as in time.

The kernel whose operations are realised is the kernel of the sorts domain
(`RwLogVerified/SortsKernel.lean`). The operations on nodes and on answers of
a `DerivationKernel` are not derived on the store: they are charged as
`Trusted/Charged.lean` postulates (roadmap L45).
-/
import RwLog.Trusted.Cost
import RwLogVerified.Rebuild

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term

/-- The Rust function `F` computes the charged operation `f`. `RA` says the
Rust argument stands for the specification's argument in a list of nodes, and
`RB` says the same of the results. The function spends at most the ticks of
`f`, and adds at most as many nodes as `f` holds cells. -/
def Realises {A' A B' B : Type} (RA : List store.Node → A' → A → Prop)
    (RB : List store.Node → B' → B → Prop)
    (F : store.Store → A' → Result (B' × store.Store)) (f : A → Cost B) : Prop :=
  ∀ (s : store.Store) (a' : A') (a : A), Inv s → RA s.nodes.val a' a → Room s (f a).ticks →
    F s a' ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧ RB s'.nodes.val r (f a).val ∧
        s'.ticks.val ≤ s.ticks.val + (f a).ticks ∧
        s'.nodes.val.length ≤ s.nodes.val.length + (f a).held ⦄

/-- A store that grew by at most `n` ticks grew by at most `n` nodes. -/
theorem Extends.grown {s s' : store.Store} {n : Nat} (h : Extends s s')
    (ht : s'.ticks.val ≤ s.ticks.val + n) : s'.nodes.val.length ≤ s.nodes.val.length + n := by
  have := h.nodes_le
  omega

end RwLogVerified
