/-
# Every engine is sound, and no less general than a derivation

An engine (`Trusted/Cost.lean`) emits answers of the derivation kernel, and
the kernel makes an answer only by a rule that keeps it valid
(`Kernel/Derivation.lean`). So two of the properties every rung keeps hold of
every engine, at every kernel rung, by the theorems of this file and with no
proof about the engine:

* `Engine.sound`: `Runtime.Sound`;
* `Engine.derivationGeneral`: `Runtime.DerivationGeneral`.

Both are about the query as it is written, not about its normal form.
-/
import RwLog.Trusted.KernelRung
import RwLog.Trusted.Properties

namespace RwLog

/-- The value of a bind, when the value of the continuation is known. -/
theorem bind_val_of {α β : Type} (m : Cost α) (f : α → Cost β) (g : α → β)
    (h : ∀ x, (f x).val = g x) : (m >>= f).val = g m.val := h _

/-- An answer emitted within `n + 1` steps is emitted by the first step or
within `n` steps of the state after it. -/
theorem mem_emitted_succ (R : Runtime) {s : R.State} {n : Nat} {a : Span}
    (h : a ∈ R.emitted s (n + 1)) :
    ∃ as s', R.step s = .emit as s' ∧ (a ∈ as ∨ a ∈ R.emitted s' n) := by
  unfold Runtime.emitted Runtime.run at h
  cases hs : R.step s with
  | emit as s' =>
    rw [hs] at h
    exact ⟨as, s', rfl, List.mem_append.1 h⟩
  | done => rw [hs] at h; simp at h

namespace Engine

variable (E : Engine) (K : Kernel Span Cost) (hK : K.Refines)

/-- What a step of the machine does, read off the engine's step. -/
theorem costedAt_step_val (s : E.StateAt) :
    ((E.costedAt K hK).step s).val =
      match (@Engine.step E Span Rel (Ans s.P) Cost (DerivationKernel.over K hK s.P) s.st).val with
      | .emit as st' => .emit (as.filterMap (Ans.rootSpan s.root)) ⟨s.P, s.root, st'⟩
      | .done => .done :=
  bind_val_of (@Engine.step E Span Rel (Ans s.P) Cost (DerivationKernel.over K hK s.P) s.st)
    (E.report s.P s.root)
    (fun r => match r with
      | .emit as st' => .emit (as.filterMap (Ans.rootSpan s.root)) ⟨s.P, s.root, st'⟩
      | .done => .done)
    fun r => by cases r <;> rfl

/-- Every span the machine emits is a valid answer of the root goal of the
state it was started in. -/
theorem emitted_valid : ∀ (n : Nat) (s : E.StateAt),
    ∀ a ∈ (E.costedAt K hK).runtime.emitted s n, Valid s.P ⟨none, s.root, none⟩ a
  | 0, _, a, h => by simp [Runtime.emitted, Runtime.run] at h
  | n + 1, s, a, h => by
    obtain ⟨as, s', hstep, h⟩ := mem_emitted_succ _ h
    have hs : (E.costedAt K hK).runtime.step s = ((E.costedAt K hK).step s).val := rfl
    rw [hs, costedAt_step_val] at hstep
    cases hr : (@Engine.step E Span Rel (Ans s.P) Cost (DerivationKernel.over K hK s.P) s.st).val with
    | done => rw [hr] at hstep; cases hstep
    | emit bs st' =>
      rw [hr] at hstep
      cases hstep
      rcases h with h | h
      · obtain ⟨ans, -, hans⟩ := List.mem_filterMap.1 h
        unfold Ans.rootSpan at hans
        split at hans
        · next hg =>
          cases hans
          exact hg ▸ ans.valid
        · cases hans
      · exact emitted_valid n ⟨s.P, s.root, st'⟩ a h

/-- The first state is for the program it was given and the normal form of
the query. -/
theorem start_P (P : Program) (q : Rel) : ((E.costedAt K hK).start P q).P = P := rfl

theorem start_root (P : Program) (q : Rel) : ((E.costedAt K hK).start P q).root = q.norm := rfl

theorem valid_of_emitted {P : Program} {q : Rel} {n : Nat} {a : Span}
    (h : a ∈ (E.costedAt K hK).runtime.emitted ((E.costedAt K hK).runtime.init P q) n) :
    Valid P ⟨none, q.norm, none⟩ a :=
  emitted_valid E K hK n _ a h

/-- **Every engine is sound**, at every kernel that returns what the
specification kernel returns. -/
theorem sound : (E.costedAt K hK).runtime.Sound := fun _ _ hwf _ _ ha M hM =>
  (valid_of_emitted E K hK ha).sound hwf.2.2 M hM

/-- **No answer of an engine is less general than its derivation**, at every
kernel that returns what the specification kernel returns. -/
theorem derivationGeneral : (E.costedAt K hK).runtime.DerivationGeneral :=
  fun _ _ hwf _ ⟨_, ha⟩ => (valid_of_emitted E K hK ha).general hwf.2.2

end Engine

end RwLog
