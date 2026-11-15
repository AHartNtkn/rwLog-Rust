/-
# What the mirrored program and the program in normal form derive

The ground relations an expression derives (`GD`,
`Kernel/NormalFormCorrect.lean`) in two other programs:

* in the mirrored program the mirror image of an expression derives the
  converses (`gd_dual`);
* in the program with every body in its normal form an expression derives
  the same (`gd_normed`).

With `gd_norm` and `gd_normConv` this says what each of the inputs an input
stands with derives (`orient`, `Trusted/Cost.lean`).
-/
import RwLog.Kernel.NormalFormCorrect
import RwLog.SpanLayer.Dual
import RwLog.Rungs.Framework.Direction

namespace RwLog

/-! ## The mirrored program -/

theorem DerivesG.dual {P : Program} {e : Rel} {G : GRel} (h : DerivesG P e G) :
    DerivesG P.dual e.dual G.inv := by
  induction h with
  | span s => rw [← swap_den]; exact .span s.swap
  | orl _ ih => exact .orl ih
  | orr _ ih => exact .orr ih
  | seq _ _ ih₁ ih₂ => rw [GRel.inv_comp]; exact .seq ih₂ ih₁
  | and _ _ ih₁ ih₂ => rw [GRel.inv_meet]; exact .and ih₁ ih₂
  | conv _ ih => exact .conv ih
  | call _ ih => exact .call (by rw [ProgramOf.dual_body]; exact ih)

/-- **In the mirrored program the mirror image of an expression derives the
converses of what the expression derives.** -/
theorem gd_dual (P : Program) (e : Rel) : GD P.dual e.dual = GRel.inv '' GD P e := by
  ext G
  constructor
  · intro h
    refine ⟨G.inv, ?_, GRel.inv_inv G⟩
    have := DerivesG.dual h
    rw [ProgramOf.dual_dual, RelOf.dual_dual] at this
    exact this
  · rintro ⟨G', h, rfl⟩
    exact DerivesG.dual h

/-! ## The program in normal form -/

theorem lookup_normed (n : Name) : ∀ defs : List (Name × Rel),
    (defs.map fun d => (d.1, d.2.norm)).lookup n = (defs.lookup n).map RelOf.norm
  | [] => rfl
  | (k, e) :: defs => by
    simp only [List.map_cons, List.lookup_cons]
    cases n == k
    · exact lookup_normed n defs
    · rfl

theorem ProgramOf.normed_body (P : Program) (n : Name) :
    P.normed.body n = (P.body n).norm := by
  unfold ProgramOf.body ProgramOf.normed
  simp only
  rw [lookup_normed]
  cases P.defs.lookup n <;> rfl

/-- **The program with every body in its normal form derives what the
program derives.** -/
theorem gd_normed (P : Program) (e : Rel) : GD P.normed e = GD P e := by
  ext G
  constructor
  · intro h
    induction h with
    | span s => exact .span s
    | orl _ ih => exact .orl ih
    | orr _ ih => exact .orr ih
    | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
    | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
    | conv _ ih => exact .conv ih
    | call _ ih =>
      rw [ProgramOf.normed_body] at ih
      have : _ ∈ GD P (P.body _).norm := ih
      rw [gd_norm] at this
      exact .call this
  · intro h
    induction h with
    | span s => exact .span s
    | orl _ ih => exact .orl ih
    | orr _ ih => exact .orr ih
    | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
    | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
    | conv _ ih => exact .conv ih
    | call _ ih =>
      refine .call ?_
      rw [ProgramOf.normed_body]
      have : _ ∈ GD P.normed (P.body _) := ih
      rw [← gd_norm] at this
      exact this

end RwLog
