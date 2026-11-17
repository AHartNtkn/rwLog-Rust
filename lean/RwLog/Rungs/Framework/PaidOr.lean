/-
# Paid, or kept: lower bounds on what a computation spends

A lower bound on a costed machine is proved along its text, with a property
of the state that the machine keeps until it has paid. `PaidOr B m Q` says of
a computation `m`: it spends `B` ticks or more, or what it returns has `Q`.
It goes through `>>=` and through a fold, so a machine keeps `Q`, or has paid
`B`, when each of its parts does.
-/
import RwLog.Rungs.Framework.Cost
import RwLog.Rungs.Framework.TraverseStd

namespace RwLog

namespace Cost

variable {α β : Type} {B : Nat}

/-- The computation spends `B` ticks or more, or what it returns has `Q`. -/
def PaidOr (B : Nat) (m : Cost α) (Q : α → Prop) : Prop := B ≤ m.ticks ∨ Q m.val

theorem PaidOr.of_val {m : Cost α} {Q : α → Prop} (h : Q m.val) : PaidOr B m Q := .inr h

theorem PaidOr.of_ticks {m : Cost α} {Q : α → Prop} (h : B ≤ m.ticks) : PaidOr B m Q := .inl h

theorem PaidOr.mono {m : Cost α} {Q Q' : α → Prop} (h : PaidOr B m Q) (hq : Q m.val → Q' m.val) :
    PaidOr B m Q' := h.imp id hq

/-- What a part has spent, the whole has spent. -/
theorem PaidOr.bind {m : Cost α} {f : α → Cost β} {Q : α → Prop} {Q' : β → Prop}
    (h1 : PaidOr B m Q) (h2 : Q m.val → PaidOr B (f m.val) Q') : PaidOr B (m >>= f) Q' := by
  rcases h1 with h | h
  · exact .inl (by rw [bind_ticks]; omega)
  · rcases h2 h with h' | h'
    · exact .inl (by rw [bind_ticks]; omega)
    · exact .inr h'

/-- The same, with what the first part returns taken apart. -/
theorem PaidOr.bind' {m : Cost α} {f : α → Cost β} {Q : α → Prop} {Q' : β → Prop}
    (h1 : PaidOr B m Q) (h2 : ∀ a, Q a → PaidOr B (f a) Q') : PaidOr B (m >>= f) Q' :=
  h1.bind (h2 m.val)

/-- A part that is run first has spent what the whole has. -/
theorem le_bind_ticks {m : Cost α} {f : α → Cost β} (h : B ≤ m.ticks) : B ≤ (m >>= f).ticks := by
  rw [bind_ticks]; omega

theorem PaidOr.metered {m : Cost α} {Q : α × Nat → Prop}
    (h : PaidOr B m fun a => Q (a, m.ticks)) : PaidOr B (Cost.metered m) Q := h

/-- A fold has paid, or keeps what each of its steps keeps. -/
theorem PaidOr.foldL (I : β → Prop) (f : β → α → Cost β) :
    ∀ (xs : List α), (∀ b x, x ∈ xs → I b → PaidOr B (f b x) I) → ∀ b, I b →
      PaidOr B (Cost.foldL f b xs) I
  | [], _, _, hb => .inr hb
  | x :: xs, hf, b, hb =>
    PaidOr.bind (hf b x List.mem_cons_self hb) fun h =>
      PaidOr.foldL I f xs (fun b y hy => hf b y (List.mem_cons_of_mem _ hy)) _ h

end Cost

namespace Traverse

open Cost

variable {α β : Type} {B : Nat}

/-- A fold has paid, or keeps what each of its steps keeps. -/
theorem paidOr_foldL (I : β → Prop) (f : β → α → Cost β) (xs : List α)
    (h : ∀ b x, x ∈ xs → I b → PaidOr B (f b x) I) (b : β) (hb : I b) :
    PaidOr B (Traverse.foldL f b xs) I := by
  rw [foldL_std]
  exact PaidOr.foldL I f xs h b hb

end Traverse

end RwLog
