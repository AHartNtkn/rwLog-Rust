/-
# The mirrored program denotes the converse

`Program.sem_dual`: `P.dual.sem e.dual = (P.sem e).inv`, by induction on
expressions and by conjugating the least fixpoint with the converse.
-/
import RwLog.Kernel.Span
import RwLog.SpanLayer.Algebra

namespace RwLog

/-- Pointwise converse of the meaning of every name. -/
def invAll (ρ : Name → GRel) : Name → GRel := fun n => (ρ n).inv

theorem invAll_invAll (ρ : Name → GRel) : invAll (invAll ρ) = ρ := rfl

theorem invAll_mono {ρ ρ' : Name → GRel} (h : ρ ≤ ρ') : invAll ρ ≤ invAll ρ' :=
  fun n _ hx => h n hx

theorem denote_dual_inv (ρ : Name → GRel) : ∀ e : Rel, denote (invAll ρ) e.dual = (denote ρ e).inv
  | .zero => by ext; simp [denote, Rel.dual, GRel.inv]
  | .span s => swap_den s
  | .or a b => by
    simp only [Rel.dual, denote, denote_dual_inv ρ a, denote_dual_inv ρ b]; rfl
  | .and a b => by simp only [Rel.dual, denote, denote_dual_inv ρ a, denote_dual_inv ρ b]; rfl
  | .seq a b => by
    simp only [Rel.dual, denote, denote_dual_inv ρ a, denote_dual_inv ρ b, GRel.inv_comp]
  | .conv a => by simp only [Rel.dual, denote, denote_dual_inv ρ a]
  | .call n => rfl

theorem lookup_dual (n : Name) : ∀ defs : List (Name × Rel),
    (defs.map fun d => (d.1, d.2.dual)).lookup n = (defs.lookup n).map Rel.dual
  | [] => rfl
  | (k, e) :: defs => by
    simp only [List.map_cons, List.lookup_cons]
    cases n == k
    · exact lookup_dual n defs
    · rfl

theorem Program.dual_body (P : Program) (n : Name) : P.dual.body n = (P.body n).dual := by
  unfold Program.body Program.dual
  simp only
  rw [lookup_dual]
  cases P.defs.lookup n <;> rfl

theorem Program.dual_step (P : Program) (ρ : Name → GRel) :
    P.dual.step ρ = invAll (P.step (invAll ρ)) := by
  funext n
  show denote ρ (P.dual.body n) = (denote (invAll ρ) (P.body n)).inv
  rw [Program.dual_body, ← denote_dual_inv, invAll_invAll]

theorem Program.dual_meaning (P : Program) : P.dual.meaning = invAll P.meaning := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    rw [Program.dual_step, invAll_invAll]
    exact le_of_eq (congrArg invAll (OrderHom.map_lfp P.step))
  · have : P.meaning ≤ invAll P.dual.meaning := by
      apply OrderHom.lfp_le
      have h := OrderHom.map_lfp P.dual.step
      rw [Program.dual_step] at h
      have h' := congrArg invAll h
      rw [invAll_invAll] at h'
      exact le_of_eq h'
    exact invAll_mono this

theorem Program.sem_dual (P : Program) (e : Rel) : P.dual.sem e.dual = (P.sem e).inv := by
  show denote P.dual.meaning e.dual = _
  rw [Program.dual_meaning, denote_dual_inv]
  rfl

end RwLog
