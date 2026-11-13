/-
# Every engine is sound, and no less general than a derivation

An engine (`Trusted/Cost.lean`) emits answers of the derivation kernel, and
the kernel makes an answer only by a rule that keeps it valid
(`Kernel/Derivation.lean`). So two of the properties every rung keeps hold of
every engine, at every kernel of a constraint domain that is lawful at the
sorts of a well-formed program, by the theorems of this file and with no
proof about the engine:

* `Engine.sound`: `Runtime.Sound`;
* `Engine.derivationGeneral`: `Runtime.DerivationGeneral`.

Both are about the query as it is written, not about its normal form. The
domain of spans as written (`Domain.written`) looks at no store and has no
canonical form, so it is not lawful and these theorems say nothing of
`Engine.costed`.
-/
import RwLog.Trusted.KernelRung
import RwLog.Trusted.Properties

namespace RwLog

/-- The value of a bind, when the value of the continuation is known. -/
theorem bind_val_of {α β : Type} (m : Cost α) (f : α → Cost β) (g : α → β)
    (h : ∀ x, (f x).val = g x) : (m >>= f).val = g m.val := h _

/-- An answer emitted within `n + 1` steps is emitted by the first step or
within `n` steps of the state after it. -/
theorem mem_emitted_succ (R : Runtime) {s : R.State} {n : Nat} {a : R.Ans}
    (h : a ∈ R.emitted s (n + 1)) :
    (∃ as s', R.step s = .emit as s' ∧ (a ∈ as ∨ a ∈ R.emitted s' n)) ∨
      ∃ k s', R.step s = .progress k s' ∧ a ∈ R.emitted s' n := by
  unfold Runtime.emitted Runtime.run at h
  cases hs : R.step s with
  | emit as s' =>
    rw [hs] at h
    exact .inl ⟨as, s', rfl, List.mem_append.1 h⟩
  | progress k s' =>
    rw [hs] at h
    exact .inr ⟨k, s', rfl, h⟩
  | done _ => rw [hs] at h; simp at h

namespace Engine

variable (E : Engine) {R : Type} [Answer R] [DecidableEq R] (dom : Sorts → Domain R)
  (K : Sorts → Kernel R Cost) (hK : ∀ S, (K S).Refines (dom S))

/-- What a step of the machine does, read off the engine's step. -/
theorem costedAt_step_val (s : E.StateAt dom) :
    ((E.costedAt dom K hK).step s).val =
      match (@Engine.step E R Rel (Ans (dom s.P.sorts) s.P) Cost
        (DerivationKernel.over (dom s.P.sorts) (K s.P.sorts) (hK s.P.sorts) s.P) s.st).val with
      | .emit as st' => .emit (as.filterMap (Ans.rootSpan (R := R) s.root)) ⟨s.P, s.root, st'⟩
      | .progress k st' => .progress k ⟨s.P, s.root, st'⟩
      | .done final => .done (final.filterMap (Ans.rootSpan (R := R) s.root)) :=
  bind_val_of (@Engine.step E R Rel (Ans (dom s.P.sorts) s.P) Cost
        (DerivationKernel.over (dom s.P.sorts) (K s.P.sorts) (hK s.P.sorts) s.P) s.st)
    (E.report dom s.P s.root)
    (fun r => match r with
      | .emit as st' => .emit (as.filterMap (Ans.rootSpan (R := R) s.root)) ⟨s.P, s.root, st'⟩
      | .progress k st' => .progress k ⟨s.P, s.root, st'⟩
      | .done final => .done (final.filterMap (Ans.rootSpan (R := R) s.root)))
    fun r => by cases r <;> rfl

/-- Every span the machine emits is a valid answer of the root goal of the
state it was started in. -/
theorem emitted_valid : ∀ (n : Nat) (s : E.StateAt dom),
    ∀ a ∈ (E.costedAt dom K hK).runtime.emitted s n, Valid (dom s.P.sorts) s.P ⟨none, s.root, none⟩ a
  | 0, _, a, h => by simp [Runtime.emitted, Runtime.run] at h
  | n + 1, s, a, h => by
    have hs : (E.costedAt dom K hK).runtime.step s = ((E.costedAt dom K hK).step s).val := rfl
    rcases mem_emitted_succ _ h with ⟨as, s', hstep, h⟩ | ⟨k, s', hstep, h⟩
    · rw [hs, costedAt_step_val] at hstep
      cases hr : (@Engine.step E R Rel (Ans (dom s.P.sorts) s.P) Cost
        (DerivationKernel.over (dom s.P.sorts) (K s.P.sorts) (hK s.P.sorts) s.P) s.st).val with
      | done _ => rw [hr] at hstep; cases hstep
      | progress _ _ => rw [hr] at hstep; cases hstep
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
    · rw [hs, costedAt_step_val] at hstep
      cases hr : (@Engine.step E R Rel (Ans (dom s.P.sorts) s.P) Cost
        (DerivationKernel.over (dom s.P.sorts) (K s.P.sorts) (hK s.P.sorts) s.P) s.st).val with
      | done _ => rw [hr] at hstep; cases hstep
      | emit _ _ => rw [hr] at hstep; cases hstep
      | progress _ st' =>
        rw [hr] at hstep
        cases hstep
        exact emitted_valid n ⟨s.P, s.root, st'⟩ a h

/-- The first state is for the program it was given and the normal form of
the query. -/
theorem start_P (P : Program) (q : Rel) : ((E.costedAt dom K hK).start P q).P = P := rfl

theorem start_root (P : Program) (q : Rel) : ((E.costedAt dom K hK).start P q).root = q.norm := rfl

theorem valid_of_emitted {P : Program} {q : Rel} {n : Nat} {a : R}
    (h : a ∈ (E.costedAt dom K hK).runtime.emitted ((E.costedAt dom K hK).runtime.init P q) n) :
    Valid (dom P.sorts) P ⟨none, q.norm, none⟩ a :=
  emitted_valid E dom K hK n _ a h

/-- **Every engine is sound**, at every kernel that returns what a domain
returns that is lawful at well-formed sorts. -/
theorem sound (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp) :
    (E.costedAt dom K hK).runtime.Sound := fun P _ hwf _ _ ha =>
  (valid_of_emitted E dom K hK ha).sound (hD P.sorts hwf.2.2.1)

/-- **No answer of an engine is less general than its derivation**, at every
kernel that returns what a domain returns that is lawful at well-formed
sorts. -/
theorem derivationGeneral (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp) :
    (E.costedAt dom K hK).runtime.DerivationGeneral :=
  fun P _ hwf _ ⟨_, ha⟩ => (valid_of_emitted E dom K hK ha).general (hD P.sorts hwf.2.2.1)

end Engine

end RwLog
