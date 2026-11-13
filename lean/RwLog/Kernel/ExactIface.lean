/-
# Exact interfaces

`Domain.Lawful` (`Trusted/Domain.lean`) says of the right interface of a
representative that it is a boundary and relates to itself every right end
of a pair of the representative (`rightBound_mem`). It does not say that the
interface relates nothing else: an interface may be loose, and a
representative may have none.

`Domain.ExactIface D M` is the other half: every term the right interface of
a representative relates is a right end of one of its pairs, and when a
representative has no right interface every term is one. It is a hypothesis
stated here, outside the trusted statements (roadmap L58).

With both halves the set of terms a boundary relates (`bset`) is, for an
interface, the set of right ends (`bset_rightBound`) or of left ends
(`bset_leftBound`) of the representative, so restricting what follows a
representative to its interface loses nothing and keeps nothing dead.
-/
import RwLog.Kernel.DomainLaws
import RwLog.Kernel.Derivation

namespace RwLog

open Answer

namespace Domain

variable {R : Type} [Answer R]

/-- Interfaces are exact in `M`. -/
structure ExactIface (D : Domain R) (M : Interp) : Prop where
  /-- Every term the right interface relates is a right end of a pair. -/
  rightBound_end : ∀ a b : R, D.rightBound a = some b →
    ∀ p ∈ den M b, ∃ x, (x, p.1) ∈ den M a
  /-- With no right interface, every term is a right end of a pair. -/
  rightBound_none : ∀ a : R, D.rightBound a = none → ∀ z, ∃ x, (x, z) ∈ den M a

end Domain

section

variable {R : Type} [Answer R] {D : Domain R} {M : Interp}

/-- The right ends of the pairs of a relation. -/
def PRel.rends (X : PRel) : Set GTerm := {z | ∃ x, (x, z) ∈ X}

/-- The left ends of the pairs of a relation. -/
def PRel.lends (X : PRel) : Set GTerm := {x | ∃ z, (x, z) ∈ X}

theorem PRel.lends_inv (X : PRel) : X.inv.lends = X.rends := rfl

theorem PRel.rends_inv (X : PRel) : X.inv.rends = X.lends := rfl

/-- The terms a boundary lets through: all of them when there is none. -/
def bset (M : Interp) : Option R → Set GTerm
  | none => Set.univ
  | some b => {x | (x, x) ∈ den M b}

@[simp] theorem bset_none : bset M (none : Option R) = Set.univ := rfl

theorem mem_bset_some {b : R} {x : GTerm} : x ∈ bset M (some b) ↔ (x, x) ∈ den M b := Iff.rfl

/-- The pairs of a boundary are the terms it lets through, each with
itself. -/
theorem mem_bden (hL : D.Lawful M) {b : Option R} (hb : IsBound D b) {x y : GTerm} :
    (x, y) ∈ bdenAt M b ↔ y = x ∧ x ∈ bset M b := by
  cases b with
  | none => exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | some r =>
    constructor
    · intro h
      obtain rfl : y = x := hL.isBound_sub r (hb r rfl) _ h
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩; exact h

/-- A boundary lets some term through. -/
theorem bset_nonempty (hL : D.Lawful M) {b : Option R} (hb : IsBound D b) :
    (bset M b).Nonempty := by
  cases b with
  | none => exact ⟨.sym "", trivial⟩
  | some r =>
    obtain ⟨⟨x, y⟩, h⟩ := hL.live r
    obtain rfl : y = x := hL.isBound_sub r (hb r rfl) _ h
    exact ⟨y, h⟩

/-- The right interface lets through exactly the right ends. -/
theorem bset_rightBound (hL : D.Lawful M) (hE : D.ExactIface M) (a : R) :
    bset M (D.rightBound a) = (den M a).rends := by
  ext z
  cases h : D.rightBound a with
  | none => exact ⟨fun _ => hE.rightBound_none a h z, fun _ => trivial⟩
  | some b =>
    constructor
    · intro hz; exact hE.rightBound_end a b h _ hz
    · rintro ⟨x, hx⟩; exact hL.rightBound_mem a b h x z hx

/-- The left interface lets through exactly the left ends. -/
theorem bset_leftBound (hL : D.Lawful M) (hE : D.ExactIface M) (a : R) :
    bset M (D.leftBound a) = (den M a).lends := by
  unfold Domain.leftBound
  rw [bset_rightBound hL hE, Answer.den_swap, PRel.rends_inv]

end

end RwLog
