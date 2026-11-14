/-
# A representative as a machine holds it

The canonical store of the converse of a relation is not the canonical
store of the relation with its sides exchanged: the variables are numbered
from the left side. A machine therefore holds a representative as a
canonical store and a mark (`dom::Oriented`, `verified/rust/src/dom.rs`).
Without the mark the store is that of the representative; with the mark it
is that of its converse (`Rep.orient`), and the two sides are read the other
way round (`Raw.ends`). Read so, the store relates the pairs of the
representative whichever way it is marked (`Rep.fold_ends`), so the converse
changes the mark and nothing else (`Rep.orient_conv`).
-/
import RwLog.Sorts.FoldRep
import RwLog.Sorts.Dom
import RwLog.Kernel.DomainLaws

namespace RwLog
namespace Sorts

variable {S : Sorts}

/-- The pairs of two patterns under the solutions of a store. -/
def Raw.pairs (S : Sorts) (r : Raw) (u w : Pat) : PRel :=
  {p | ∃ σ ∈ r.store.Sol S, p.1 = u.bind σ ∧ p.2 = w.bind σ}

/-- The left side and the right side of a store as its mark says. -/
def Raw.ends (r : Raw) (f : Bool) : Pat × Pat :=
  (if f then r.sides.2 else r.sides.1, if f then r.sides.1 else r.sides.2)

theorem Raw.pairs_swap (r : Raw) (u w : Pat) : r.pairs S w u = (r.pairs S u w).inv := by
  ext p
  constructor
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨σ, hσ, e₂, e₁⟩
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨σ, hσ, e₂, e₁⟩

namespace Rep

theorem conv_rel (ρ : Rep S) : ρ.conv.1.rel S = (ρ.1.rel S).inv := Answer.den_swap S.interp ρ

/-- The converse of the converse is the representative. -/
theorem conv_conv (ρ : Rep S) : ρ.conv.conv = ρ :=
  ext_rel (by rw [conv_rel, conv_rel]; rfl)

/-- The representative whose canonical store a machine holds for `ρ` with
the mark `f`. -/
def orient (ρ : Rep S) (f : Bool) : Rep S := if f then ρ.conv else ρ

@[simp] theorem orient_false (ρ : Rep S) : ρ.orient false = ρ := rfl

@[simp] theorem orient_true (ρ : Rep S) : ρ.orient true = ρ.conv := rfl

/-- The store held for a representative is held for its converse with the
mark changed. -/
theorem orient_conv (ρ : Rep S) (f : Bool) : ρ.conv.orient (!f) = ρ.orient f := by
  cases f
  · exact ρ.conv_conv
  · rfl

theorem orient_orient (ρ : Rep S) (f g : Bool) : (ρ.orient g).orient (f != g) = ρ.orient f := by
  cases f <;> cases g
  · rfl
  · exact ρ.conv_conv
  · rfl
  · rfl

theorem orient_inj {ρ ρ' : Rep S} {f : Bool} (h : ρ.orient f = ρ'.orient f) : ρ = ρ' := by
  cases f
  · exact h
  · have := congrArg conv h
    simpa only [orient_true, conv_conv] using this

theorem orient_eq_iff {ρ ρ' : Rep S} {f : Bool} : ρ.orient f = ρ'.orient f ↔ ρ = ρ' :=
  ⟨orient_inj, fun h => by rw [h]⟩

/-- The folded canonical store held for a representative is a store over a
pair, and its two sides, read as the mark says, relate the pairs of the
representative. -/
theorem fold_ends (hN : NoPair S) (ρ : Rep S) (f : Bool) {r : Raw}
    (h : FoldOf S (ρ.orient f).1 r) :
    r.t = tpair r.sides.1 r.sides.2 ∧ r.pairs S (r.ends f).1 (r.ends f).2 = ρ.1.rel S := by
  obtain ⟨ht, -⟩ := (ρ.orient f).fold_sides hN h
  have hrel : r.pairs S r.sides.1 r.sides.2 = (ρ.orient f).1.rel S := by
    rw [← h.rel, Raw.rel_eq ht]; rfl
  refine ⟨ht, ?_⟩
  cases f
  · exact hrel
  · show r.pairs S r.sides.2 r.sides.1 = _
    rw [Raw.pairs_swap, hrel, orient_true, conv_rel]
    rfl

/-- The two sides of the converse are the same pattern exactly when those
of the representative are. -/
theorem conv_bound (ρ : Rep S) : ρ.conv.l = ρ.conv.r ↔ ρ.l = ρ.r := by
  have key : ∀ ρ : Rep S, ρ.l = ρ.r → ρ.conv = ρ := fun ρ h =>
    (dom_lawful ρ.wf).swap_of_isBound (b := ρ) (decide_eq_true h)
  constructor
  · intro h
    have e := key ρ.conv h
    rw [conv_conv] at e
    rw [← e] at h
    exact h
  · intro h
    rw [key ρ h]
    exact h

theorem orient_bound (ρ : Rep S) (f : Bool) : (ρ.orient f).l = (ρ.orient f).r ↔ ρ.l = ρ.r := by
  cases f
  · exact Iff.rfl
  · exact ρ.conv_bound

/-- The conjunction of the converses is the converse of the conjunction. -/
theorem meet_orient (a b : Rep S) (f : Bool) :
    (a.orient f).meet (b.orient f) = (a.meet b).map (·.orient f) := by
  cases f
  · simp
  · exact (dom_lawful a.wf).meet_swap a b

/-- One store held covers another exactly when the representatives do. -/
theorem covers_orient (a b : Rep S) (f : Bool) :
    (a.orient f).meet (b.orient f) = some (b.orient f) ↔ a.meet b = some b := by
  rw [meet_orient]
  cases a.meet b with
  | none => simp
  | some m => simp [orient_eq_iff]

end Rep

end Sorts
end RwLog
