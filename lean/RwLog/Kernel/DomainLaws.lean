/-
# The algebra of a lawful constraint domain

`Domain.Lawful` (`Trusted/Domain.lean`) says that a representative is never
empty, that two representatives relating the same pairs are the same value,
and that each operation returns the representative of what it names. Every
algebraic law follows, as an equation between representatives.

The result of an operation is read as a set of pairs, nothing being the empty
set (`Domain.denO`). Two results that are the same set are equal
(`Lawful.denO_inj`), and the set of each operation is the operation on sets
(`denO_rep`, for a first-order span, `denO_compose`, `denO_meet`). So a law of relations is a law of
the domain:

* the converse is an involution (`swap_swap`) and commutes with every
  operation (`rep_swap`, `compose_swap`, `meet_swap`, `covers_swap`), and a
  boundary is its own converse (`swap_of_isBound`);
* composition is associative (`compose_assoc`);
* conjunction is commutative, associative and idempotent (`meet_comm`,
  `meet_assoc`, `meet_self`);
* coverage is a partial order (`covers_refl`, `covers_trans`,
  `covers_antisymm`).
-/
import RwLog.Trusted.Domain
import RwLog.SpanLayer.Sorts

namespace RwLog

namespace PRel

theorem comp_assoc (X Y Z : PRel) : (X.comp Y).comp Z = X.comp (Y.comp Z) := by
  ext p
  constructor
  · rintro ⟨m, ⟨n, h₁, h₂⟩, h₃⟩; exact ⟨n, h₁, m, h₂, h₃⟩
  · rintro ⟨n, h₁, m, h₂, h₃⟩; exact ⟨m, ⟨n, h₁, h₂⟩, h₃⟩

theorem inv_comp (X Y : PRel) : (X.comp Y).inv = Y.inv.comp X.inv := by
  ext p
  constructor
  · rintro ⟨m, h₁, h₂⟩; exact ⟨m, h₂, h₁⟩
  · rintro ⟨m, h₁, h₂⟩; exact ⟨m, h₂, h₁⟩

theorem inv_inter (X Y : PRel) : (X ∩ Y).inv = X.inv ∩ Y.inv := rfl

theorem inv_empty : (∅ : PRel).inv = ∅ := rfl

theorem empty_comp (X : PRel) : (∅ : PRel).comp X = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ => h

theorem comp_empty (X : PRel) : X.comp ∅ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, _, h⟩ => h

end PRel

namespace Domain

variable {R : Type} [Answer R]

/-- The pairs of the result of an operation: none when there is no
representative. -/
def denO (M : Interp) : Option R → PRel
  | none => ∅
  | some r => Answer.den M r

@[simp] theorem denO_none (M : Interp) : denO M (none : Option R) = ∅ := rfl

@[simp] theorem denO_some (M : Interp) (r : R) : denO M (some r) = Answer.den M r := rfl

theorem denO_map_swap (M : Interp) (x : Option R) :
    denO M (x.map Answer.swap) = (denO M x).inv := by
  cases x with
  | none => rfl
  | some r => exact Answer.den_swap M r

namespace Lawful

variable {D : Domain R} {M : Interp} (L : D.Lawful M)
include L

/-- Results that relate the same pairs are the same result. -/
theorem denO_inj {x y : Option R} (h : denO M x = denO M y) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b => exact absurd h.symm (L.live b).ne_empty
  | some a =>
    cases y with
    | none => exact absurd h (L.live a).ne_empty
    | some b => rw [L.canon a b h]

theorem denO_rep {s : Span} (hs : s.firstOrder = true) : denO M (D.rep s) = s.denAt M := by
  cases h : D.rep s with
  | none => exact (L.rep_none s hs h).symm
  | some r => exact L.rep_some s r h

theorem denO_compose (a b : R) :
    denO M (D.compose a b) = (Answer.den M a).comp (Answer.den M b) := by
  cases h : D.compose a b with
  | none => exact (L.compose_none a b h).symm
  | some c => exact L.compose_some a b c h

theorem denO_meet (a b : R) : denO M (D.meet a b) = Answer.den M a ∩ Answer.den M b := by
  cases h : D.meet a b with
  | none => exact (L.meet_none a b h).symm
  | some c => exact L.meet_some a b c h

theorem denO_bind_compose_right (x : Option R) (c : R) :
    denO M (x.bind (D.compose · c)) = (denO M x).comp (Answer.den M c) := by
  cases x with
  | none => exact (PRel.empty_comp _).symm
  | some a => exact L.denO_compose a c

theorem denO_bind_compose_left (a : R) (x : Option R) :
    denO M (x.bind (D.compose a ·)) = (Answer.den M a).comp (denO M x) := by
  cases x with
  | none => exact (PRel.comp_empty _).symm
  | some b => exact L.denO_compose a b

theorem denO_bind_meet_right (x : Option R) (c : R) :
    denO M (x.bind (D.meet · c)) = denO M x ∩ Answer.den M c := by
  cases x with
  | none => exact (Set.empty_inter _).symm
  | some a => exact L.denO_meet a c

theorem denO_bind_meet_left (a : R) (x : Option R) :
    denO M (x.bind (D.meet a ·)) = Answer.den M a ∩ denO M x := by
  cases x with
  | none => exact (Set.inter_empty _).symm
  | some b => exact L.denO_meet a b

/-! ## The converse -/

/-- The converse is an involution. -/
theorem swap_swap (r : R) : Answer.swap (Answer.swap r) = r :=
  L.canon _ _ (by rw [Answer.den_swap, Answer.den_swap]; rfl)

/-- The representative of a first-order span with its sides exchanged is the
converse of its representative. -/
theorem rep_swap {s : Span} (hs : s.firstOrder = true) :
    D.rep s.swap = (D.rep s).map Answer.swap :=
  L.denO_inj (by
    rw [L.denO_rep (Span.firstOrder_swap s ▸ hs), denO_map_swap, L.denO_rep hs]
    exact Answer.den_swap M s)

/-- The converse of a composition is the composition of the converses, in
the other order. -/
theorem compose_swap (a b : R) :
    D.compose (Answer.swap b) (Answer.swap a) = (D.compose a b).map Answer.swap :=
  L.denO_inj (by
    rw [L.denO_compose, denO_map_swap, L.denO_compose, Answer.den_swap, Answer.den_swap,
      PRel.inv_comp])

/-- The converse of a conjunction is the conjunction of the converses. -/
theorem meet_swap (a b : R) :
    D.meet (Answer.swap a) (Answer.swap b) = (D.meet a b).map Answer.swap :=
  L.denO_inj (by
    rw [L.denO_meet, denO_map_swap, L.denO_meet, Answer.den_swap, Answer.den_swap,
      PRel.inv_inter])

/-- A boundary is its own converse. -/
theorem swap_of_isBound {b : R} (h : D.isBound b = true) : Answer.swap b = b := by
  refine L.canon _ _ ?_
  rw [Answer.den_swap]
  ext ⟨x, y⟩
  constructor
  · intro hp
    have e : x = y := L.isBound_sub b h (y, x) hp
    subst e; exact hp
  · intro hp
    have e : y = x := L.isBound_sub b h (x, y) hp
    subst e; exact hp

/-- Coverage of the converses is coverage. -/
theorem covers_swap (a b : R) : D.covers (Answer.swap a) (Answer.swap b) = D.covers a b := by
  rw [Bool.eq_iff_iff, L.covers_iff, L.covers_iff, Answer.den_swap, Answer.den_swap]
  exact ⟨fun h p hp => h (a := (p.2, p.1)) hp, fun h p hp => h (a := (p.2, p.1)) hp⟩

/-! ## Composition and conjunction -/

/-- Composition is associative. -/
theorem compose_assoc (a b c : R) :
    (D.compose a b).bind (D.compose · c) = (D.compose b c).bind (D.compose a ·) :=
  L.denO_inj (by
    rw [L.denO_bind_compose_right, L.denO_bind_compose_left, L.denO_compose, L.denO_compose,
      PRel.comp_assoc])

/-- Conjunction is commutative. -/
theorem meet_comm (a b : R) : D.meet a b = D.meet b a :=
  L.denO_inj (by rw [L.denO_meet, L.denO_meet, Set.inter_comm])

/-- Conjunction is associative. -/
theorem meet_assoc (a b c : R) :
    (D.meet a b).bind (D.meet · c) = (D.meet b c).bind (D.meet a ·) :=
  L.denO_inj (by
    rw [L.denO_bind_meet_right, L.denO_bind_meet_left, L.denO_meet, L.denO_meet,
      Set.inter_assoc])

/-- Conjunction is idempotent. -/
theorem meet_self (a : R) : D.meet a a = some a :=
  L.denO_inj (by rw [L.denO_meet, Set.inter_self]; rfl)

/-! ## Coverage -/

theorem covers_refl (a : R) : D.covers a a = true := (L.covers_iff a a).2 subset_rfl

theorem covers_trans {a b c : R} (h₁ : D.covers a b = true) (h₂ : D.covers b c = true) :
    D.covers a c = true :=
  (L.covers_iff a c).2 (Set.Subset.trans ((L.covers_iff b c).1 h₂) ((L.covers_iff a b).1 h₁))

/-- Representatives that cover each other are the same value. -/
theorem covers_antisymm {a b : R} (h₁ : D.covers a b = true) (h₂ : D.covers b a = true) :
    a = b :=
  L.canon a b (Set.Subset.antisymm ((L.covers_iff b a).1 h₂) ((L.covers_iff a b).1 h₁))

end Lawful

end Domain

end RwLog
