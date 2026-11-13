/-
# The Rust store, as translated by Aeneas: what each primitive does and costs

Each primitive of `verified/rust/src/store.rs` returns what it should, leaves
the nodes alone (or appends one), and advances the tick counter by exactly
one. The counter is a `u64`; every statement asks that it has room, and then
says the call does not fail.
-/
import Aeneas
import RwlogCore.Funs

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core

@[step]
theorem tick_spec (s : store.Store) (h : s.ticks.val < U64.max) :
    store.Store.tick s ⦃ s' => s'.nodes = s.nodes ∧ s'.ticks.val = s.ticks.val + 1 ⦄ := by
  unfold store.Store.tick
  step*

@[step]
theorem read_spec (s : store.Store) (i : store.TermId)
    (hi : i.val < s.nodes.length) (h : s.ticks.val < U64.max) :
    store.Store.read s i ⦃ n s' =>
      n = s.nodes.val[i.val] ∧ s'.nodes = s.nodes ∧ s'.ticks.val = s.ticks.val + 1 ⦄ := by
  unfold store.Store.read
  step*

@[step]
theorem word_eq_spec (s : store.Store) (a b : U32) (h : s.ticks.val < U64.max) :
    store.Store.word_eq s a b ⦃ r s' =>
      r = decide (a = b) ∧ s'.nodes = s.nodes ∧ s'.ticks.val = s.ticks.val + 1 ⦄ := by
  unfold store.Store.word_eq
  step*

@[step]
theorem same_spec (s : store.Store) (a b : store.TermId) (h : s.ticks.val < U64.max) :
    store.Store.same s a b ⦃ r s' =>
      r = decide (a = b) ∧ s'.nodes = s.nodes ∧ s'.ticks.val = s.ticks.val + 1 ⦄ := by
  unfold store.Store.same
  step*

/-- An application may only refer to nodes already in the store. -/
def store.Node.Older (len : Nat) : store.Node → Prop
  | .App a b => a.val < len ∧ b.val < len
  | _ => True

@[step]
theorem alloc_spec (s : store.Store) (n : store.Node) (h : s.ticks.val < U64.max)
    (hlen : s.nodes.val.length < Usize.max) (hn : store.Node.Older s.nodes.val.length n) :
    store.Store.alloc s n ⦃ id s' =>
      id.val = s.nodes.val.length ∧ s'.nodes.val = s.nodes.val ++ [n] ∧
        s'.ticks.val = s.ticks.val + 1 ⦄ := by
  unfold store.Store.alloc
  cases n <;> simp only [store.Node.Older] at hn <;> step*

end RwLogVerified
