/-
# The mirrored engine at the kernel of the language

Each definition of `Gen.lean`, taken at the kernel of the language, is the
definition of `Machine.lean` with the same name. So the mirrored engine is,
at that kernel, the machine the proofs are about (`mirrored_costed`).
-/
import RwLog.Rungs.Mirror.Machine
import RwLog.Rungs.Framework.TraverseStd

namespace RwLog

namespace Mirror

open Cost

theorem dualRel_std : ∀ e : Rel, Gen.dualRel e = e.dual
  | .zero => rfl
  | .span _ => rfl
  | .or a b => by simp only [Gen.dualRel, RelOf.dual, dualRel_std a, dualRel_std b]
  | .and a b => by simp only [Gen.dualRel, RelOf.dual, dualRel_std a, dualRel_std b]
  | .seq a b => by simp only [Gen.dualRel, RelOf.dual, dualRel_std a, dualRel_std b]
  | .conv a => by simp only [Gen.dualRel, RelOf.dual, dualRel_std a]
  | .call _ => rfl

theorem dualProg_std (P : Program) : Gen.dualProg P = P.dual := by
  simp only [Gen.dualProg, ProgramOf.dual, dualRel_std]

theorem orient_std (f : Bool) (as : List Span) : Gen.orient f as = orient f as := rfl

theorem level_std {σ : Type} (f : Bool) (x y : σ) (r r' : Step σ ⊕ Step σ) :
    Gen.level f x y r r' = level f x y r r' := by
  rcases r with (_ | _) | (_ | _) <;> rcases r' with (_ | _) | (_ | _) <;> rfl

theorem go_std (C : CostedRuntime) : ∀ (g : Nat) (f : Bool) (x y : C.State),
    Gen.go (M := Cost) C.step g f x y = go C g f x y
  | 0, f, x, y => by
    rw [Gen.go, go]
    simp only [level_std]
    rfl
  | g + 1, f, x, y => by
    rw [Gen.go, go]
    simp only [go_std C g]
    same_text

/-- The mirrored engine, at the kernel of the language, is the mirrored
machine of the engine at that kernel. -/
theorem mirrored_costed (E : Engine) : E.mirrored.costed = machine E.costed := by
  have hstep : (fun st : StOf (E.State Span) =>
      Gen.go (M := Cost) (fun s => E.step s) st.gap st.fwd st.lead st.lag) =
      fun st => go E.costed st.gap st.fwd st.lead st.lag :=
    funext fun st => go_std E.costed st.gap st.fwd st.lead st.lag
  show (⟨StOf (E.State Span), _, _⟩ : CostedRuntime) = ⟨StOf (E.State Span), _, _⟩
  simp only [Engine.mirrored, Engine.costed, dualProg_std, dualRel_std, hstep]

end Mirror

end RwLog
