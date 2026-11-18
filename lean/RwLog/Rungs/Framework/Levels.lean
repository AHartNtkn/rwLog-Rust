/-
# Levels: what the definition says

`Trusted/Levels.lean` grades the pairs of a relation by the weight of a
derivation. Here:

* a derivation weighs at least 1, so level 0 is empty (`LevelAt.pos`,
  `level_zero`);
* the levels grow (`LevelAt.mono`, `level_mono`);
* a level holds only pairs the relation relates (`level_subset_pairs`), and
  every pair the relation relates is in some level (`exists_level`): the
  levels together are the relation (`pairs_eq_iUnion_level`);
* weight does not depend on the direction an expression is written in: the
  levels of a converse are the levels swapped (`levelAt_conv`), and so are
  the levels of the mirror image in the mirrored program (`levelAt_dual`);
* a run that has covered a level has covered every lower one
  (`CostedRuntime.Covered.anti`), and a run that is done, of a machine that
  exhausts honestly, has covered every level (`CostedRuntime.Covered.of_halts`).
-/
import RwLog.Trusted.Levels
import RwLog.SpanLayer.Dual
import RwLog.Rungs.Framework.Direction

namespace RwLog

variable {P : Program} {M : Interp}

/-- A derivation weighs at least 1. -/
theorem LevelAt.pos {c : Nat} {e : Rel} {p : GTerm × GTerm} (h : LevelAt P M c e p) : 1 ≤ c := by
  induction h with
  | span h _ => exact h
  | orl _ ih => exact ih
  | orr _ ih => exact ih
  | seq _ _ hs ih _ => omega
  | and _ _ hs ih _ => omega
  | conv _ ih => exact ih
  | call _ _ => omega

/-- A pair of a level is a pair of every higher level. -/
theorem LevelAt.mono {c : Nat} {e : Rel} {p : GTerm × GTerm} (h : LevelAt P M c e p) :
    ∀ {c' : Nat}, c ≤ c' → LevelAt P M c' e p := by
  induction h with
  | span h1 hp => intro c' hc; exact .span (h1.trans hc) hp
  | orl _ ih => intro c' hc; exact .orl (ih hc)
  | orr _ ih => intro c' hc; exact .orr (ih hc)
  | seq ha hb hs _ _ => intro c' hc; exact .seq ha hb (hs.trans hc)
  | and ha hb hs _ _ => intro c' hc; exact .and ha hb (hs.trans hc)
  | conv _ ih => intro c' hc; exact .conv (ih hc)
  | call _ ih =>
    intro c' hc
    obtain ⟨k, rfl⟩ : ∃ k, c' = k + 1 := ⟨c' - 1, by omega⟩
    exact .call (ih (by omega))

/-- A pair of a level is a pair of the relation. -/
theorem LevelAt.sem {c : Nat} {e : Rel} {p : GTerm × GTerm} (h : LevelAt P M c e p) :
    p ∈ P.semAt M e := by
  induction h with
  | span _ hp => exact hp
  | orl _ ih => exact Or.inl ih
  | orr _ ih => exact Or.inr ih
  | seq _ _ _ iha ihb => exact ⟨_, iha, ihb⟩
  | and _ _ _ iha ihb => exact ⟨iha, ihb⟩
  | conv _ ih => exact ih
  | @call c n p _ ih =>
    show p ∈ P.meaningAt M n
    rw [P.meaningAt_eq]; exact ih

/-- A pair an expression relates, when every name means the pairs of its
levels, is in a level of the expression. -/
theorem exists_levelAt_of_denote :
    ∀ (e : Rel) (p : GTerm × GTerm),
      p ∈ denoteAt M (fun n => {p | ∃ c, LevelAt P M c (.call n) p}) e → ∃ c, LevelAt P M c e p
  | .zero, _, h => h.elim
  | .span _, _, h => ⟨1, .span le_rfl h⟩
  | .or a b, p, h => by
    rcases h with h | h
    · obtain ⟨c, hc⟩ := exists_levelAt_of_denote a p h; exact ⟨c, .orl hc⟩
    · obtain ⟨c, hc⟩ := exists_levelAt_of_denote b p h; exact ⟨c, .orr hc⟩
  | .and a b, p, h => by
    obtain ⟨ca, ha⟩ := exists_levelAt_of_denote a p h.1
    obtain ⟨cb, hb⟩ := exists_levelAt_of_denote b p h.2
    exact ⟨ca + cb, .and ha hb le_rfl⟩
  | .seq a b, (x, z), h => by
    obtain ⟨m, h1, h2⟩ := h
    obtain ⟨ca, ha⟩ := exists_levelAt_of_denote a _ h1
    obtain ⟨cb, hb⟩ := exists_levelAt_of_denote b _ h2
    exact ⟨ca + cb, .seq ha hb le_rfl⟩
  | .conv a, p, h => by
    obtain ⟨c, hc⟩ := exists_levelAt_of_denote a (p.2, p.1) h
    exact ⟨c, .conv hc⟩
  | .call _, _, h => h

/-- **Every pair of the relation is in some level.** -/
theorem exists_levelAt {e : Rel} {p : GTerm × GTerm} (h : p ∈ P.semAt M e) :
    ∃ c, LevelAt P M c e p := by
  let ρ' : Name → PRel := fun n => {p | ∃ c, LevelAt P M c (.call n) p}
  have hpre : P.stepAt M ρ' ≤ ρ' := by
    intro n p hp
    obtain ⟨c, hc⟩ := exists_levelAt_of_denote (P.body n) p hp
    exact ⟨c + 1, .call hc⟩
  have hle : P.meaningAt M ≤ ρ' := OrderHom.lfp_le _ hpre
  exact exists_levelAt_of_denote e p (denoteAt_mono M hle e h)

namespace ProgramOf

/-- Level 0 is empty. -/
theorem level_zero (P : Program) (e : Rel) : P.level 0 e = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => absurd (LevelAt.pos h) (by omega)

/-- The levels grow. -/
theorem level_mono (P : Program) (e : Rel) {c c' : Nat} (h : c ≤ c') :
    P.level c e ⊆ P.level c' e := fun _ hp => LevelAt.mono hp h

/-- A level holds only pairs the relation relates. -/
theorem level_subset_pairs (P : Program) (c : Nat) (e : Rel) : P.level c e ⊆ P.pairs e :=
  fun _ hp => LevelAt.sem hp

/-- Every pair the relation relates is in some level. -/
theorem exists_level (P : Program) {e : Rel} {p : GTerm × GTerm} (h : p ∈ P.pairs e) :
    ∃ c, p ∈ P.level c e := exists_levelAt h

/-- **The levels together are the relation.** -/
theorem pairs_eq_iUnion_level (P : Program) (e : Rel) : P.pairs e = ⋃ c, P.level c e := by
  ext p
  rw [Set.mem_iUnion]
  exact ⟨P.exists_level, fun ⟨c, h⟩ => P.level_subset_pairs c e h⟩

/-- The levels of a converse are the levels swapped. -/
theorem levelAt_conv (P : Program) (M : Interp) (c : Nat) (e : Rel) :
    P.levelAt M c (.conv e) = (P.levelAt M c e).inv := by
  ext p
  constructor
  · intro h; cases h with | conv h => exact h
  · intro h; exact .conv h

end ProgramOf

/-- A derivation in the mirrored program is a derivation of the swapped
pair, of the same weight. -/
theorem LevelAt.of_dual {c : Nat} {e' : Rel} {p : GTerm × GTerm} (h : LevelAt P.dual M c e' p) :
    ∀ {e : Rel}, e' = e.dual → LevelAt P M c e (p.2, p.1) := by
  induction h with
  | @span c s p h1 hp =>
    intro e he
    cases e <;> simp only [RelOf.dual] at he <;> try cases he
    exact .span h1 (Span.mem_denAt_swap.1 hp)
  | orl _ ih =>
    intro e he
    cases e <;> simp only [RelOf.dual] at he <;> try cases he
    exact .orl (ih rfl)
  | orr _ ih =>
    intro e he
    cases e <;> simp only [RelOf.dual] at he <;> try cases he
    exact .orr (ih rfl)
  | seq _ _ hs iha ihb =>
    intro e he
    cases e <;> simp only [RelOf.dual] at he <;> try cases he
    exact .seq (ihb rfl) (iha rfl) (by omega)
  | and _ _ hs iha ihb =>
    intro e he
    cases e <;> simp only [RelOf.dual] at he <;> try cases he
    exact .and (iha rfl) (ihb rfl) hs
  | conv _ ih =>
    intro e he
    cases e <;> simp only [RelOf.dual] at he <;> try cases he
    exact .conv (ih rfl)
  | @call c n p _ ih =>
    intro e he
    cases e <;> simp only [RelOf.dual] at he <;> try cases he
    exact .call (ih (P.dual_body n))

/-- **Weight does not depend on direction.** The levels of the mirror image
in the mirrored program are the levels swapped. -/
theorem ProgramOf.levelAt_dual (P : Program) (M : Interp) (c : Nat) (e : Rel) :
    P.dual.levelAt M c e.dual = (P.levelAt M c e).inv := by
  ext p
  constructor
  · intro h; exact LevelAt.of_dual h rfl
  · intro h
    have h' : LevelAt P.dual.dual M c e.dual.dual (p.2, p.1) := by
      rw [P.dual_dual, e.dual_dual]; exact h
    exact LevelAt.of_dual (P := P.dual) h' rfl

namespace CostedRuntime

variable (C : CostedRuntime)

/-- A run that has covered a level has covered every lower one. -/
theorem Covered.anti {P : Program} {q : Rel} {c c' n : Nat} (h : C.Covered P q c n)
    (hc : c' ≤ c) : C.Covered P q c' n := fun p hp => h p (P.level_mono q hc hp)

/-- A run that is done, of a machine that exhausts honestly, has covered
every level. -/
theorem Covered.of_halts (hh : C.runtime.HonestExhaustion) {P : Program} {q : Rel}
    (wf : P.WellFormed q) {n : Nat} (hn : C.runtime.Halts (C.start P q) n) (c : Nat) :
    C.Covered P q c n := fun p hp => by
  have hp' : p ∈ P.pairs q := P.level_subset_pairs c q hp
  rw [hh P q wf n hn] at hp'
  obtain ⟨a, ha, hpa⟩ := Set.mem_iUnion₂.1 hp'
  exact ⟨a, ha, hpa⟩

end CostedRuntime

end RwLog
