/-
# What a store identifier stands for

`Repr nm nodes i t`: in the list of nodes, the identifier `i` is the pattern
`t` of the specification (`RwLog.Pat`).

A variable node is a number in binary (`VarAt`): `V0` is `0`, `VL` doubles,
`VR` doubles and adds one. A symbol is a Rust word read through a naming
`nm`. The end of a list is read as a symbol too, the one `nm` gives to
`none`, so a list of the store is a term and everything proved about terms
applies to it. The theorems ask `nm` to be injective.

The relation is a function of the identifier (`Repr.unique`), survives adding
nodes (`Repr.append`), and in a store that satisfies the invariant two
identifiers of the same term are the same identifier (`Repr.inj`).
-/
import RwLogVerified.Store
import RwLog.Kernel.SolveFacts
import RwLog.Kernel.Subterms

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core

inductive VarAt (nodes : List store.Node) : Nat → Nat → Prop
  | zero {i : Nat} : nodes[i]? = some .V0 → VarAt nodes i 0
  | left {i : Nat} {a : store.TermId} {n : Nat} :
      nodes[i]? = some (.VL a) → VarAt nodes a.val n → VarAt nodes i (2 * n)
  | right {i : Nat} {a : store.TermId} {n : Nat} :
      nodes[i]? = some (.VR a) → VarAt nodes a.val n → VarAt nodes i (2 * n + 1)

inductive Repr (nm : Option Nat → RwLog.Sym) (nodes : List store.Node) : Nat → RwLog.Pat → Prop
  | var {i n : Nat} : VarAt nodes i n → Repr nm nodes i (.var n)
  | sym {i : Nat} {f : U32} : nodes[i]? = some (.Sym f) → Repr nm nodes i (.sym (nm (some f.val)))
  | nil {i : Nat} : nodes[i]? = some .Nil → Repr nm nodes i (.sym (nm none))
  | app {i : Nat} {a b : store.TermId} {ta tb : RwLog.Pat} :
      nodes[i]? = some (.App a b) → Repr nm nodes a.val ta → Repr nm nodes b.val tb →
      Repr nm nodes i (.app ta tb)

variable {nm : Option Nat → RwLog.Sym} {nodes : List store.Node}

theorem VarAt.node {i n : Nat} (h : VarAt nodes i n) : ∃ m, nodes[i]? = some m ∧ IsVarNode m := by
  cases h with
  | zero h => exact ⟨_, h, trivial⟩
  | left h _ => exact ⟨_, h, trivial⟩
  | right h _ => exact ⟨_, h, trivial⟩

theorem VarAt.lt {i n : Nat} (h : VarAt nodes i n) : i < nodes.length := by
  obtain ⟨m, hm, -⟩ := h.node
  exact (List.getElem?_eq_some_iff.1 hm).1

theorem Repr.lt {i : Nat} {t : RwLog.Pat} (h : Repr nm nodes i t) : i < nodes.length := by
  cases h with
  | var h => exact h.lt
  | sym h => exact (List.getElem?_eq_some_iff.1 h).1
  | nil h => exact (List.getElem?_eq_some_iff.1 h).1
  | app h _ _ => exact (List.getElem?_eq_some_iff.1 h).1

theorem VarAt.unique {i n m : Nat} (h : VarAt nodes i n) (h' : VarAt nodes i m) : n = m := by
  induction h generalizing m with
  | zero h => cases h' <;> simp_all
  | left h _ ih =>
    cases h' with
    | zero h' => simp_all
    | left h' ha' => rw [h] at h'; cases h'; rw [ih ha']
    | right h' ha' => simp_all
  | right h _ ih =>
    cases h' with
    | zero h' => simp_all
    | left h' ha' => simp_all
    | right h' ha' => rw [h] at h'; cases h'; rw [ih ha']

theorem Repr.unique {i : Nat} {t u : RwLog.Pat} (h : Repr nm nodes i t) (h' : Repr nm nodes i u) :
    t = u := by
  induction h generalizing u with
  | var hv =>
    cases h' with
    | var hv' => rw [hv.unique hv']
    | sym h' => obtain ⟨m, hm, hvn⟩ := hv.node; rw [h'] at hm; cases hm; exact hvn.elim
    | nil h' => obtain ⟨m, hm, hvn⟩ := hv.node; rw [h'] at hm; cases hm; exact hvn.elim
    | app h' _ _ => obtain ⟨m, hm, hvn⟩ := hv.node; rw [h'] at hm; cases hm; exact hvn.elim
  | sym h =>
    cases h' with
    | var hv' => obtain ⟨m, hm, hvn⟩ := hv'.node; rw [h] at hm; cases hm; exact hvn.elim
    | sym h' => rw [h] at h'; cases h'; rfl
    | nil h' => simp_all
    | app h' _ _ => simp_all
  | nil h =>
    cases h' with
    | var hv' => obtain ⟨m, hm, hvn⟩ := hv'.node; rw [h] at hm; cases hm; exact hvn.elim
    | sym h' => simp_all
    | nil h' => rfl
    | app h' _ _ => simp_all
  | app h _ _ iha ihb =>
    cases h' with
    | var hv' => obtain ⟨m, hm, hvn⟩ := hv'.node; rw [h] at hm; cases hm; exact hvn.elim
    | sym h' => simp_all
    | nil h' => simp_all
    | app h' ha' hb' => rw [h] at h'; cases h'; rw [iha ha', ihb hb']

theorem getElem?_append_of_some {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x)
    (more : List α) : (l ++ more)[i]? = some x := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h

/-- Adding nodes keeps what a variable node stands for. -/
theorem VarAt.append {i n : Nat} (h : VarAt nodes i n) (more : List store.Node) :
    VarAt (nodes ++ more) i n := by
  induction h with
  | zero h => exact .zero (getElem?_append_of_some h more)
  | left h _ ih => exact .left (getElem?_append_of_some h more) ih
  | right h _ ih => exact .right (getElem?_append_of_some h more) ih

/-- Adding nodes keeps every representation. -/
theorem Repr.append {i : Nat} {t : RwLog.Pat} (h : Repr nm nodes i t) (more : List store.Node) :
    Repr nm (nodes ++ more) i t := by
  induction h with
  | var hv => exact .var (hv.append more)
  | sym h => exact .sym (getElem?_append_of_some h more)
  | nil h => exact .nil (getElem?_append_of_some h more)
  | app h _ _ iha ihb => exact .app (getElem?_append_of_some h more) iha ihb

/-! ## Reading a node of a represented term -/

theorem Repr.of_app {i : Nat} {t : RwLog.Pat} {a b : store.TermId} (h : Repr nm nodes i t)
    (hn : nodes[i]? = some (.App a b)) :
    ∃ ta tb, t = .app ta tb ∧ Repr nm nodes a.val ta ∧ Repr nm nodes b.val tb := by
  cases h with
  | var hv => obtain ⟨m, hm, hvn⟩ := hv.node; rw [hn] at hm; cases hm; exact hvn.elim
  | sym h => simp_all
  | nil h => simp_all
  | app h ha hb => rw [hn] at h; cases h; exact ⟨_, _, rfl, ha, hb⟩

theorem Repr.of_var {i : Nat} {t : RwLog.Pat} {m : store.Node} (h : Repr nm nodes i t)
    (hn : nodes[i]? = some m) (hm : IsVarNode m) : ∃ v, t = .var v ∧ VarAt nodes i v := by
  cases h with
  | var hv => exact ⟨_, rfl, hv⟩
  | sym h => rw [hn] at h; cases h; exact hm.elim
  | nil h => rw [hn] at h; cases h; exact hm.elim
  | app h _ _ => rw [hn] at h; cases h; exact hm.elim

theorem Repr.of_sym {i : Nat} {t : RwLog.Pat} {f : U32} (h : Repr nm nodes i t)
    (hn : nodes[i]? = some (.Sym f)) : t = .sym (nm (some f.val)) :=
  h.unique (.sym hn)

theorem Repr.of_nil {i : Nat} {t : RwLog.Pat} (h : Repr nm nodes i t)
    (hn : nodes[i]? = some .Nil) : t = .sym (nm none) :=
  h.unique (.nil hn)

/-! ## One identifier for each term -/

/-- The part of the invariant that concerns nodes only. -/
structure NodesOK (nodes : List store.Node) : Prop where
  root : nodes[0]? = some .V0
  fits : ∀ i n, nodes[i]? = some n → Fits nodes i n
  nodup : nodes.Nodup

theorem Inv.nodesOK {s : store.Store} (h : Inv s) : NodesOK s.nodes.val :=
  ⟨h.root, h.shape.fits, h.shape.nodup⟩

theorem NodesOK.idx_inj (h : NodesOK nodes) {i j : Nat} {n : store.Node}
    (hi : nodes[i]? = some n) (hj : nodes[j]? = some n) : i = j := by
  obtain ⟨hi', ei⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hj', ej⟩ := List.getElem?_eq_some_iff.1 hj
  exact (List.Nodup.getElem_inj_iff h.nodup).1 (ei.trans ej.symm)

theorem VarAt.eq_zero (h : NodesOK nodes) {i n : Nat} (hv : VarAt nodes i n) (hn : n = 0) :
    i = 0 := by
  induction hv with
  | zero hi => exact h.idx_inj hi h.root
  | left hi ha ih =>
    have := ih (by omega)
    have hf := h.fits _ _ hi
    simp only [Fits] at hf
    exact absurd this hf.2.1
  | right _ _ _ => omega

theorem VarAt.inj' (h : NodesOK nodes) {i j n m : Nat} (hi : VarAt nodes i n)
    (hj : VarAt nodes j m) (e : n = m) : i = j := by
  induction hi generalizing j m with
  | zero hi =>
    have := hj.eq_zero h e.symm
    subst this
    exact h.idx_inj hi h.root
  | @left i a n hi ha ih =>
    cases hj with
    | zero hj' =>
      have h0 := (VarAt.left hi ha).eq_zero h e
      subst h0
      rw [h.root] at hi; cases hi
    | @left _ a' n' hj' ha' =>
      have e' := ih ha' (by omega)
      have : a = a' := by scalar_tac
      subst this
      exact h.idx_inj hi hj'
    | right hj' ha' => omega
  | @right i a n hi ha ih =>
    cases hj with
    | zero hj' => omega
    | left hj' ha' => omega
    | @right _ a' n' hj' ha' =>
      have e' := ih ha' (by omega)
      have : a = a' := by scalar_tac
      subst this
      exact h.idx_inj hi hj'

theorem VarAt.inj (h : NodesOK nodes) {i j n : Nat} (hi : VarAt nodes i n) (hj : VarAt nodes j n) :
    i = j := VarAt.inj' h hi hj rfl

/-- Two identifiers of the same term are the same identifier. -/
theorem Repr.inj (hnm : Function.Injective nm) (h : NodesOK nodes) {i j : Nat} {t : RwLog.Pat}
    (hi : Repr nm nodes i t) (hj : Repr nm nodes j t) : i = j := by
  induction hi generalizing j with
  | var hv =>
    cases hj with
    | var hv' => exact hv.inj h hv'
  | @sym i f hi =>
    generalize ht : RwLog.Term.sym (nm (some f.val)) = t at hj
    cases hj with
    | var _ => cases ht
    | @sym _ g hj' =>
      have := hnm (RwLog.Term.sym.inj ht)
      have : f = g := by simp at this; scalar_tac
      subst this
      exact h.idx_inj hi hj'
    | nil _ => exact absurd (hnm (RwLog.Term.sym.inj ht)) (by simp)
    | app _ _ _ => cases ht
  | @nil i hi =>
    generalize ht : RwLog.Term.sym (nm none) = t at hj
    cases hj with
    | var _ => cases ht
    | sym _ => exact absurd (hnm (RwLog.Term.sym.inj ht)) (by simp)
    | nil hj' => exact h.idx_inj hi hj'
    | app _ _ _ => cases ht
  | @app i a b ta tb hi _ _ iha ihb =>
    cases hj with
    | @app _ a' b' _ _ hj' ha' hb' =>
      have ea := iha ha'
      have eb := ihb hb'
      have : a = a' := by scalar_tac
      subst this
      have : b = b' := by scalar_tac
      subst this
      exact h.idx_inj hi hj'

end RwLogVerified
