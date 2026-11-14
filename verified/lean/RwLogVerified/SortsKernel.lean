/-
# The kernel rung of the sorts domain

`sortsKernel nm S U rc q` is a kernel on the representatives of the sorts
`S` (`Sorts.Rep S`, `lean/RwLog/Sorts/Rep.lean`). It returns what the domain
of the sorts returns (`sortsKernel_refines`, against `Sorts.dom S`), and the
charge of each operation is the number of ticks within which the Rust
function of `verified/rust/src/dom.rs` returns that result on the store:

| operation | Rust | theorem |
|---|---|---|
| `swap` | `dom::swap` | `swap_held` |
| `rep` | `dom::rep` | `sorts_rep_realised` |
| `compose` | `dom::compose` | `sorts_compose_realised` |
| `meet` | `dom::meet` | `sorts_meet_realised` |
| `composable` | `dom::composable` | `sorts_composable_realised` |
| `covers` | `dom::covers` | `sorts_covers_realised` |
| `eq` | `dom::eq` | `sorts_eq_realised` |
| `rightBound` | `dom::right` | `sorts_rightBound_realised` |
| `leftBound` | `dom::left` | `sorts_leftBound_realised` |

A machine holds a representative as a canonical store and a mark (`Held`):
the folded canonical store of the representative without the mark, and of
its converse with it. The converse changes the mark, touches no store and is
not charged (`swap_held`). What another operation spends depends on how its
arguments are held, with or without the mark and with the exclusions listed
in which order, so its charge is the most it spends over the finitely many
ways (`most`, `RwLogVerified/DomChain.lean`): a function of the
representatives alone.

`Realises` (`RwLogVerified/Realises.lean`) is what each theorem says: from any
store that keeps the invariant, holds the declarations, the names of the
sorts and the arguments, and has room on its tick counter, the Rust function
does not panic, returns the operation's value, only adds nodes, and advances
the tick counter by at most the operation's charge.

The parameters. `nm` names the symbols, one to one, with the end of a list
the empty symbol. `U` lists the names of the sorts of `S` as the store has
them (`Ctx`). `rc` and `q` bound the conjunctions and the goals reachable in
`S` (`Sorts.reachSet`, `Sorts.reachGSet`). No sort has a case for the pair
symbol (`Sorts.NoPair`).

Space. The store only grows and an allocation is a tick, so every operation
is charged its tick bound as the cells it holds.
-/
import RwLogVerified.Realises
import RwLogVerified.DomChain

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term

/-- The kernel of the sorts `S` whose charges are the tick bounds proved of
the Rust functions. -/
@[reducible] noncomputable def sortsKernel (nm : Option Nat → RwLog.Sym) (S : Sorts)
    (U : List Name) (rc q : Nat) : Kernel (Sorts.Rep S) Cost where
  tick := Cost.tick
  race := Cost.race
  metered := Cost.metered
  swap := Sorts.Rep.conv
  rep sp := Charged.op (Sorts.repOf S sp) (repTicks nm S U rc q sp) (repTicks nm S U rc q sp)
  compose x y :=
    Charged.op (x.compose y) (composeTicks nm S U rc q x y) (composeTicks nm S U rc q x y)
  meet x y := Charged.op (x.meet y) (meetTicks nm S U rc q x y) (meetTicks nm S U rc q x y)
  composable xs := Charged.op ((Sorts.dom S).composable xs) (composableTicks nm S U rc q xs)
    (composableTicks nm S U rc q xs)
  covers a b := Charged.op (decide (a.meet b = some b)) (coversTicks nm S U rc q a b)
    (coversTicks nm S U rc q a b)
  eq x y := Charged.op (decide (x = y)) (eqTicks nm S U rc q x y) (eqTicks nm S U rc q x y)
  rightBound x := Charged.op x.right (rightTicks nm S U rc q x) (rightTicks nm S U rc q x)
  leftBound x := Charged.op x.conv.right (leftTicks nm S U rc q x) (leftTicks nm S U rc q x)

/-- The kernel of the sorts returns what the domain of the sorts returns. -/
theorem sortsKernel_refines (nm : Option Nat → RwLog.Sym) (S : Sorts) (U : List Name)
    (rc q : Nat) : Kernel.Refines (Sorts.dom S) (sortsKernel nm S U rc q) where
  monad := rfl
  tick := rfl
  race _ _ _ := rfl
  metered _ _ := rfl
  swap := rfl
  rep _ := rfl
  compose _ _ := rfl
  meet _ _ := rfl
  composable _ := rfl
  covers _ _ := rfl
  eq _ _ := rfl
  rightBound _ := rfl
  leftBound _ := rfl

variable {nm : Option Nat → RwLog.Sym}

/-- A machine's value holds the representative: the store is the folded
canonical store for its mark, with some listing of the exclusions. -/
def Held {S : Sorts} (nm : Option Nat → RwLog.Sym) (U : List Name) (nodes : List store.Node)
    (a : dom.Oriented) (ρ : Sorts.Rep S) : Prop :=
  ∃ (r : Sorts.Raw) (Y : List Sorts.Binds), OrAt nm U nodes a ρ r Y

/-- What an operation returned holds what the specification returns, and is
nothing exactly when the specification has nothing. -/
def OptHeld {S : Sorts} (nm : Option Nat → RwLog.Sym) (U : List Name)
    (nodes : List store.Node) (res : Option dom.Oriented) (want : Option (Sorts.Rep S)) : Prop :=
  match res, want with
  | none, none => True
  | some o, some ρ => Held nm U nodes o ρ
  | _, _ => False

theorem OrPost.optHeld {S : Sorts} {U : List Name} {nodes : List store.Node}
    {want : Option (Sorts.Rep S)} {res : Option dom.Oriented} (h : OrPost nm U nodes want res) :
    OptHeld nm U nodes res want := by
  cases res with
  | none =>
    have e : want = none := h
    subst e
    trivial
  | some o =>
    obtain ⟨ρ', r', Y', rfl, hat⟩ := h.at
    exact ⟨r', Y', hat⟩

/-- The converse is the change of the mark, and spends nothing. -/
theorem swap_held {S : Sorts} {U : List Name} {nodes : List store.Node} {a : dom.Oriented}
    {ρ : Sorts.Rep S} (h : Held nm U nodes a ρ) :
    ∃ a', dom.swap a = ok a' ∧ Held nm U nodes a' ((sortsKernel nm S U 0 0).swap ρ) := by
  obtain ⟨r, Y, hat⟩ := h
  refine ⟨{ a with flip := !a.flip }, ?_, r, Y, hat.swap⟩
  unfold dom.swap
  simp only [decide_not, Bool.decide_eq_true]

/-- The declarations and the names of the sorts on the store. -/
def SortDeclsAt (nm : Option Nat → RwLog.Sym) (sp : Pat) (U : List Name) (nodes : List store.Node)
    (decls names : store.TermId) : Prop :=
  Repr nm nodes decls.val sp ∧ Repr nm nodes names.val (namesPat (nm none) U)

section Realised

variable {S : Sorts} {sp : Pat} {U : List Name} {rc q : Nat}

/-- Two machine values hold two representatives. -/
def HeldTwo (nm : Option Nat → RwLog.Sym) (sp : Pat) (U : List Name) (nodes : List store.Node)
    (p : store.TermId × store.TermId × dom.Oriented × dom.Oriented)
    (x : Sorts.Rep S × Sorts.Rep S) : Prop :=
  SortDeclsAt nm sp U nodes p.1 p.2.1 ∧ Held nm U nodes p.2.2.1 x.1 ∧ Held nm U nodes p.2.2.2 x.2

/-- A machine value holds a representative. -/
def HeldOne (nm : Option Nat → RwLog.Sym) (sp : Pat) (U : List Name) (nodes : List store.Node)
    (p : store.TermId × store.TermId × dom.Oriented) (x : Sorts.Rep S) : Prop :=
  SortDeclsAt nm sp U nodes p.1 p.2.1 ∧ Held nm U nodes p.2.2 x

theorem sorts_rep_realised (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hS : S.WellFormed) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) :
    Realises
      (fun nodes (p : store.TermId × store.TermId × U32 × span.Span) (x : Span) =>
        SortDeclsAt nm sp U nodes p.1 p.2.1 ∧ nm (some p.2.2.1.val) = neSym ∧
          SpanAt nm nodes p.2.2.2 x)
      (OptHeld nm U) (fun s p => dom.rep s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsKernel nm S U rc q).rep x) := by
  rintro s ⟨decls, names, ne, x⟩ sx hI ⟨⟨hde, hU⟩, hne, hx⟩ hroom
  refine WP.spec_mono (rep_spec hnm hz hC hS hUS hr hq sx ne hne s decls names x hI hde hU hx
    hroom) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4⟩
  have h3' : s'.ticks.val ≤ s.ticks.val + repTicks nm S U rc q sx := by
    unfold repTicks; omega
  exact ⟨h1, h2, h4.optHeld, h3', h2.grown h3'⟩

theorem sorts_compose_realised (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) :
    Realises (HeldTwo nm sp U) (OptHeld nm U)
      (fun s p => dom.compose s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsKernel nm S U rc q).compose x.1 x.2) := by
  rintro s ⟨decls, names, a, b⟩ ⟨ρa, ρb⟩ hI ⟨⟨hde, hU⟩, ⟨ra, Ya, ha⟩, rb, Yb, hb⟩ hroom
  have hle : composeAt nm S U rc q ⟨ra, a.flip, Ya⟩ ⟨rb, b.flip, Yb⟩ ≤
      composeTicks nm S U rc q ρa ρb := le_most₂ ha.heldAs hb.heldAs (composeAt nm S U rc q)
  simp only [composeAt] at hle
  have hroom' : Room s (composeTicks nm S U rc q ρa ρb) := hroom
  unfold Room at hroom'
  refine WP.spec_mono (dom_compose_spec hnm hz hC hN hUS hr hq ρa ρb Ya Yb s decls names a b hI
    hde hU ha hb (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4⟩
  have h3' : s'.ticks.val ≤ s.ticks.val + composeTicks nm S U rc q ρa ρb := by omega
  exact ⟨h1, h2, h4.optHeld, h3', h2.grown h3'⟩

theorem sorts_meet_realised (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) :
    Realises (HeldTwo nm sp U) (OptHeld nm U)
      (fun s p => dom.meet s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsKernel nm S U rc q).meet x.1 x.2) := by
  rintro s ⟨decls, names, a, b⟩ ⟨ρa, ρb⟩ hI ⟨⟨hde, hU⟩, ⟨ra, Ya, ha⟩, rb, Yb, hb⟩ hroom
  have hle : meetAt nm S U rc q ⟨ra, a.flip, Ya⟩ ⟨rb, b.flip, Yb⟩ ≤
      meetTicks nm S U rc q ρa ρb := le_most₂ ha.heldAs hb.heldAs (meetAt nm S U rc q)
  simp only [meetAt] at hle
  have hroom' : Room s (meetTicks nm S U rc q ρa ρb) := hroom
  unfold Room at hroom'
  refine WP.spec_mono (dom_meet_spec hnm hz hC hN hUS hr hq ρa ρb Ya Yb s decls names a b hI
    hde hU ha hb (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4⟩
  have h3' : s'.ticks.val ≤ s.ticks.val + meetTicks nm S U rc q ρa ρb := by omega
  exact ⟨h1, h2, h4.optHeld, h3', h2.grown h3'⟩

theorem sorts_covers_realised (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) :
    Realises (HeldTwo nm sp U) (fun _ (b b' : Bool) => b = b')
      (fun s p => dom.covers s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsKernel nm S U rc q).covers x.1 x.2) := by
  rintro s ⟨decls, names, a, b⟩ ⟨ρa, ρb⟩ hI ⟨⟨hde, hU⟩, ⟨ra, Ya, ha⟩, rb, Yb, hb⟩ hroom
  have hle : coversAt nm S U rc q ρa ρb ⟨ra, a.flip, Ya⟩ ⟨rb, b.flip, Yb⟩ ≤
      coversTicks nm S U rc q ρa ρb :=
    le_most₂ ha.heldAs hb.heldAs (coversAt nm S U rc q ρa ρb)
  simp only [coversAt] at hle
  have hroom' : Room s (coversTicks nm S U rc q ρa ρb) := hroom
  unfold Room at hroom'
  refine WP.spec_mono (dom_covers_spec hnm hz hC hN hUS hr hq ρa ρb Ya Yb s decls names a b hI
    hde hU ha hb (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4⟩
  have h3' : s'.ticks.val ≤ s.ticks.val + coversTicks nm S U rc q ρa ρb := by omega
  exact ⟨h1, h2, h4, h3', h2.grown h3'⟩

theorem sorts_eq_realised (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) :
    Realises (HeldTwo nm sp U) (fun _ (b b' : Bool) => b = b')
      (fun s p => dom.eq s p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun x => (sortsKernel nm S U rc q).eq x.1 x.2) := by
  rintro s ⟨decls, names, a, b⟩ ⟨ρa, ρb⟩ hI ⟨⟨hde, hU⟩, ⟨ra, Ya, ha⟩, rb, Yb, hb⟩ hroom
  have hle : eqAt nm S U rc q ρb ⟨ra, a.flip, Ya⟩ ⟨rb, b.flip, Yb⟩ ≤
      eqTicks nm S U rc q ρa ρb := le_most₂ ha.heldAs hb.heldAs (eqAt nm S U rc q ρb)
  simp only [eqAt] at hle
  have hroom' : Room s (eqTicks nm S U rc q ρa ρb) := hroom
  unfold Room at hroom'
  refine WP.spec_mono (eq_spec hnm hz hC hN hUS hr hq ρa ρb Ya Yb s decls names a b hI
    hde hU ha hb (by unfold Room; omega)) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4⟩
  have h3' : s'.ticks.val ≤ s.ticks.val + eqTicks nm S U rc q ρa ρb := by omega
  exact ⟨h1, h2, h4, h3', h2.grown h3'⟩

theorem sorts_rightBound_realised (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) :
    Realises (HeldOne nm sp U) (OptHeld nm U) (fun s p => dom.right s p.1 p.2.1 p.2.2)
      (fun x => (sortsKernel nm S U rc q).rightBound x) := by
  rintro s ⟨decls, names, a⟩ ρ hI ⟨⟨hde, hU⟩, r, Y, ha⟩ hroom
  have hle : rightCost nm S U rc q r a.flip Y ≤ rightTicks nm S U rc q ρ :=
    le_most ha.heldAs fun m => rightCost nm S U rc q m.r m.f m.Y
  have hroom' : Room s (rightTicks nm S U rc q ρ) := hroom
  unfold Room at hroom'
  refine WP.spec_mono (right_spec hnm hz hC hN hUS hr hq ρ Y s decls names a hI hde hU ha
    (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨h1, h2, h3, h4⟩
  have h3' : s'.ticks.val ≤ s.ticks.val + rightTicks nm S U rc q ρ := by omega
  exact ⟨h1, h2, h4.optHeld, h3', h2.grown h3'⟩

theorem sorts_leftBound_realised (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) :
    Realises (HeldOne nm sp U) (OptHeld nm U) (fun s p => dom.left s p.1 p.2.1 p.2.2)
      (fun x => (sortsKernel nm S U rc q).leftBound x) := by
  rintro s ⟨decls, names, a⟩ ρ hI ⟨⟨hde, hU⟩, r, Y, ha⟩ hroom
  have hle : rightCost nm S U rc q r (!a.flip) Y ≤ leftTicks nm S U rc q ρ :=
    le_most ha.heldAs fun m => rightCost nm S U rc q m.r (!m.f) m.Y
  have hroom' : Room s (leftTicks nm S U rc q ρ) := hroom
  unfold Room at hroom'
  refine WP.spec_mono (left_spec hnm hz hC hN hUS hr hq ρ Y s decls names a hI hde hU ha
    (by unfold Room; omega)) ?_
  rintro ⟨res, s'⟩ ⟨h1, h2, h3, h4⟩
  have h3' : s'.ticks.val ≤ s.ticks.val + leftTicks nm S U rc q ρ := by omega
  exact ⟨h1, h2, h4.optHeld, h3', h2.grown h3'⟩

/-- The chain test, on a list of representatives each packed as it is
held. -/
theorem sorts_composable_realised (hnm : Function.Injective nm) (hz : nm none = "")
    (hC : Ctx nm S sp U) (hN : Sorts.NoPair S) (hUS : ∀ n ∈ U, n ∈ Sorts.names S)
    (hr : ∀ d, (Sorts.reachSet S d).card ≤ rc)
    (hq : ∀ d m, (Sorts.reachGSet S (d, some m)).card ≤ q) :
    Realises
      (fun nodes (p : store.TermId × store.TermId × store.TermId) (xs : List (Sorts.Rep S)) =>
        SortDeclsAt nm sp U nodes p.1 p.2.1 ∧ ∃ ps : List (Sorts.Rep S × Form),
          ps.map Prod.fst = xs ∧ (∀ x ∈ ps, HeldAs x.1 x.2) ∧
          Repr nm nodes p.2.2.val (encList (nm none) (ps.map fun x => packForm nm U x.2)))
      (fun _ (b b' : Bool) => b = b') (fun s p => dom.composable s p.1 p.2.1 p.2.2)
      (fun xs => (sortsKernel nm S U rc q).composable xs) := by
  rintro s ⟨decls, names, xs⟩ _ hI ⟨⟨hde, hU⟩, ps, rfl, hps, hxs⟩ hroom
  refine WP.spec_mono (dom_composable_spec hnm hz hC hN hUS hr hq ps hps s decls names xs hI
    hde hU hxs hroom) ?_
  rintro ⟨r, s'⟩ ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4, h2.grown h4⟩

end Realised

end RwLogVerified
