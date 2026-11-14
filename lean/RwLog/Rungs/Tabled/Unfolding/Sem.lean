/-
# What the unfolding of a goal to a depth stands for

The unfolding race reads a node to a depth (`Rungs/Tabled/Unfold.lean`). A
derivation of the node is *read whole* at depth `d` (`GR P d`) when every
node on it is read: reading a node costs one level, for its members and for
the body of a call alike. A derivation that is read whole is a closed product
of the unfolding; one that is not runs into a node that was not read and is
an open product.

This file has `GR`, what a node derives by the kind of node it reads as
(`gd_of_span`, `gd_of_body`, `gd_of_union`, `gd_of_chain`, `gd_of_meet`), and
what an open product says of a pair: its first stretch relates the left term
to something (`admL`), its last stretch relates something to the right term
(`admR`).
-/
import RwLog.Rungs.Tabled.Invariant

namespace RwLog

namespace Tabled

namespace Unfold

open Answer

/-! ## What a node derives, by the kind of node -/

theorem view_chain_eq {e : Rel} {xs : List Rel} (h : e.view = .chain xs) : xs = seqParts e := by
  cases e with
  | seq a b => simpa [RelOf.view] using h.symm
  | conv a => cases a <;> simp [RelOf.view] at h
  | _ => simp [RelOf.view] at h

theorem view_meet_eq {e : Rel} {xs : List Rel} (h : e.view = .meet xs) : xs = andParts e := by
  cases e with
  | and a b => simpa [RelOf.view] using h.symm
  | conv a => cases a <;> simp [RelOf.view] at h
  | _ => simp [RelOf.view] at h

variable (P : Program)

theorem gd_of_chain {e : Rel} {xs : List Rel} (h : e.view = .chain xs) :
    GD P e = RwLog.seqAll (xs.map (GD P)) := by
  rw [view_chain_eq h]; exact ((gd_laws P).gd_seqParts e).symm

theorem gd_of_meet {e : Rel} {xs : List Rel} (h : e.view = .meet xs) :
    GD P e = RwLog.andAll (xs.map (GD P)) := by
  rw [view_meet_eq h]; exact ((gd_laws P).gd_andParts e).symm

theorem gd_of_union {e : Rel} {xs : List Rel} (hn : Normal e) (h : e.view = .union xs) {G : GRel} :
    G ∈ GD P e ↔ ∃ x ∈ xs, G ∈ GD P x := by
  rw [← gd_unionParts, ← hn.view_union_eq h]
  simp

theorem gd_of_body {e b : Rel} (hb : Charged.bodyOf P e = some b) : GD P e = GD P b := by
  ext G
  rw [mem_gd_iff, mem_gd_iff]
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => rw [(gdn_bodyOf hb 0).2] at hk; cases hk
    | succ k => rw [(gdn_bodyOf hb k).1] at hk; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [(gdn_bodyOf hb k).1]; exact hk⟩

/-! ## Derivations read whole -/

/-- The derivations of a node on which every node is read at depth `d`. -/
def GR : Nat → Rel → Set GRel
  | 0, _ => ∅
  | d + 1, e =>
    match e.view.forget with
    | .span _ => GD P e
    | .call _ _ =>
      match Charged.bodyOf P e with
      | some b => GR d b
      | none => ∅
    | .union xs => {G | ∃ x ∈ xs, G ∈ GR d x}
    | .chain xs => RwLog.seqAll (xs.map (GR d))
    | .meet xs => RwLog.andAll (xs.map (GR d))

@[simp] theorem gr_zero (e : Rel) : GR P 0 e = ∅ := rfl

theorem gr_span {d : Nat} {e : Rel} (h : e.view.forget = .span ()) : GR P (d + 1) e = GD P e := by
  simp only [GR, h]

theorem gr_call {d : Nat} {e b : Rel} {n : Name} {f : Bool} (h : e.view.forget = .call n f)
    (hb : Charged.bodyOf P e = some b) : GR P (d + 1) e = GR P d b := by
  simp only [GR, h, hb]

theorem gr_union {d : Nat} {e : Rel} {xs : List Rel} (h : e.view.forget = .union xs) :
    GR P (d + 1) e = {G | ∃ x ∈ xs, G ∈ GR P d x} := by
  simp only [GR, h]

theorem gr_chain {d : Nat} {e : Rel} {xs : List Rel} (h : e.view.forget = .chain xs) :
    GR P (d + 1) e = RwLog.seqAll (xs.map (GR P d)) := by
  simp only [GR, h]

theorem gr_meet {d : Nat} {e : Rel} {xs : List Rel} (h : e.view.forget = .meet xs) :
    GR P (d + 1) e = RwLog.andAll (xs.map (GR P d)) := by
  simp only [GR, h]

/-! ## The ends of an open product -/

variable {R : Type} [Answer R]

/-- The first stretch of an open product relates the term to something. -/
def admL (M : Interp) (l : Option R) (x : GTerm) : Prop := ∀ r, l = some r → ∃ u, (x, u) ∈ den M r

/-- The last stretch of an open product relates something to the term. -/
def admR (M : Interp) (r : Option R) (z : GTerm) : Prop := ∀ s, r = some s → ∃ v, (v, z) ∈ den M s

theorem admL_none (M : Interp) (x : GTerm) : admL M (none : Option R) x := fun _ h => by cases h

theorem admR_none (M : Interp) (z : GTerm) : admR M (none : Option R) z := fun _ h => by cases h

/-- A boundary is a first stretch for the pairs between it. -/
theorem admL_bound {M : Interp} {lb rb : Option R} {X : PRel} {x z : GTerm}
    (h : (x, z) ∈ wrapAt M lb X rb) : admL M lb x := by
  rintro r rfl
  obtain ⟨u, v, h₁, -, -⟩ := mem_wrapAt.1 h
  exact ⟨u, h₁⟩

theorem admR_bound {M : Interp} {lb rb : Option R} {X : PRel} {x z : GTerm}
    (h : (x, z) ∈ wrapAt M lb X rb) : admR M rb z := by
  rintro r rfl
  obtain ⟨u, v, -, -, h₃⟩ := mem_wrapAt.1 h
  exact ⟨v, h₃⟩

end Unfold

end Tabled

end RwLog
