/-
# What a store identifier stands for

`Repr nm nodes i t`: in the list of nodes, the identifier `i` is the pattern
`t` of the specification (`RwLog.Pat`). Variables are the Rust words read as
numbers; symbols are Rust words read through a naming `nm`, which the
theorems ask to be injective.

The relation is inductive, so a term that has a representation is finite, and
recursion on the Rust side terminates by induction on it. It is a function of
the identifier (`Repr.unique`).
-/
import Aeneas
import RwlogCore.Funs
import RwLog.Kernel.Match

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core

inductive Repr (nm : Nat → RwLog.Sym) (nodes : List store.Node) : Nat → RwLog.Pat → Prop
  | var {i : Nat} {x : U32} : nodes[i]? = some (.Var x) → Repr nm nodes i (.var x.val)
  | sym {i : Nat} {f : U32} : nodes[i]? = some (.Sym f) → Repr nm nodes i (.sym (nm f.val))
  | app {i : Nat} {a b : store.TermId} {ta tb : RwLog.Pat} :
      nodes[i]? = some (.App a b) → Repr nm nodes a.val ta → Repr nm nodes b.val tb →
      Repr nm nodes i (.app ta tb)

variable {nm : Nat → RwLog.Sym} {nodes : List store.Node}

theorem Repr.lt {i : Nat} {t : RwLog.Pat} (h : Repr nm nodes i t) : i < nodes.length := by
  cases h <;> rename_i h <;> exact (List.getElem?_eq_some_iff.1 h).1

theorem Repr.unique {i : Nat} {t u : RwLog.Pat} (h : Repr nm nodes i t) (h' : Repr nm nodes i u) :
    t = u := by
  induction h generalizing u with
  | var hx => cases h' <;> simp_all
  | sym hf => cases h' <;> simp_all
  | app hn _ _ iha ihb =>
    cases h' with
    | var hx => simp_all
    | sym hf => simp_all
    | app hn' ha' hb' =>
      rw [hn] at hn'; cases hn'
      rw [iha ha', ihb hb']

/-- Appending nodes keeps every representation. -/
theorem Repr.append {i : Nat} {t : RwLog.Pat} (h : Repr nm nodes i t) (more : List store.Node) :
    Repr nm (nodes ++ more) i t := by
  induction h with
  | var hx => exact .var (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]; exact hx)
  | sym hf => exact .sym (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hf).1]; exact hf)
  | app hn _ _ iha ihb =>
    exact .app (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hn).1]; exact hn) iha ihb

end RwLogVerified
