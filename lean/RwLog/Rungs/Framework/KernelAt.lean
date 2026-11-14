/-
# A kernel that returns what a domain returns, in the monad of `Cost`

`Kernel.Refines D K` says that the monad of `K` is the monad of charged
computations, with its `tick`, `race` and `metered`. To read an engine at
such a kernel, it is enough to read it at a kernel where these are the ones
of `Cost` by definition: `Kernel.Refines.elim`.
-/
import RwLog.Trusted.KernelRung

namespace RwLog

variable {R : Type} [Answer R] [DecidableEq R]

/-- The kernel in the monad of `Cost` with the given operations on
representatives. -/
@[reducible] def Kernel.ofOps (rep : Span → Cost (Option R)) (compose meet : R → R → Cost (Option R))
    (composable : List R → Cost Bool) (covers eq : R → R → Cost Bool)
    (rightBound leftBound : R → Cost (Option R)) : Kernel R Cost where
  tick := Cost.tick
  race := Cost.race
  metered := Cost.metered
  swap := Answer.swap
  rep := rep
  compose := compose
  meet := meet
  composable := composable
  covers := covers
  eq := eq
  rightBound := rightBound
  leftBound := leftBound

/-- A statement about every kernel that returns what a domain returns holds
if it holds of those in the monad of `Cost`. -/
theorem Kernel.Refines.elim {D : Domain R}
    {motive : (K : Kernel R Cost) → K.Refines D → Prop}
    (h : ∀ rep compose meet composable covers eq rightBound leftBound
      (hK : (Kernel.ofOps rep compose meet composable covers eq rightBound leftBound).Refines D),
      motive _ hK) : ∀ (K : Kernel R Cost) (hK : K.Refines D), motive K hK := by
  intro K hK
  cases K with
  | mk tick race metered swap rep compose meet composable covers eq rb lb =>
    rename_i m
    have h₁ : m = Kernel.std.toMonad := hK.monad
    have h₂ := hK.tick
    have h₃ : @race = @Cost.race := by funext α a b; exact hK.race α a b
    have h₄ : @metered = @Cost.metered := by funext α a; exact hK.metered α a
    have h₅ := hK.swap
    simp only at h₁ h₂ h₅
    subst h₁ h₂ h₃ h₄ h₅
    exact h rep compose meet composable covers eq rb lb hK

/-- Read the goal at a kernel in the monad of `Cost`. -/
macro "at_cost " K:ident hK:ident : tactic =>
  `(tactic| induction $K:term, $hK:term using Kernel.Refines.elim with
    | h _ _ _ _ _ _ _ _ $hK:ident => ?_)

end RwLog

namespace RwLog

variable {R : Type} [Answer R] [DecidableEq R]

/-- The kernel that returns what a domain returns and charges nothing: every
operation is the operation of the domain. It is for what a run shows, never
for what it costs. -/
@[reducible] def Kernel.uncharged (D : Domain R) : Kernel R Cost :=
  Kernel.ofOps (fun s => pure (D.rep s)) (fun x y => pure (D.compose x y))
    (fun x y => pure (D.meet x y)) (fun xs => pure (D.composable xs))
    (fun a s => pure (D.covers a s)) (fun x y => pure (decide (x = y)))
    (fun s => pure (D.rightBound s)) (fun s => pure (D.leftBound s))

theorem Kernel.uncharged_refines (D : Domain R) : (Kernel.uncharged D).Refines D where
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

end RwLog
