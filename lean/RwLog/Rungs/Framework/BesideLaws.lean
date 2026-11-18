/-
# The machine of two engines side by side

The machine of an engine (`Engine.costedAt`) read off the runs of the
engine's step, and with that what the machine of a pair of engines
(`Engine.beside`) keeps of the machines of its two engines: it emits
everything the first emits, reports that it is done exactly when the first
does, and has emitted everything the second emits in its first `n` steps by
the time it has spent a fixed multiple of what those steps cost.
-/
import RwLog.Rungs.Framework.BesideRun
import RwLog.Rungs.Framework.Runtime
import RwLog.Rungs.Framework.Cost

namespace RwLog

namespace Engine

open Beside

variable (E F : Engine) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
  (cells : ∀ S, R S → Nat)

/-- The engine's step at the derivation kernel of a program. -/
def stepAt (P : Program) (st : E.State (R P.sorts) Rel (Ans (dom P.sorts) P)) :
    Cost (StepOf (Ans (dom P.sorts) P) (E.State (R P.sorts) Rel (Ans (dom P.sorts) P))) :=
  @Engine.step E (R P.sorts) Rel (Ans (dom P.sorts) P) Cost
    (DerivationKernel.over (dom P.sorts) (K P.sorts) (hK P.sorts) P) st

/-- What the machine shows of answers of the engine: those of the root goal,
as representatives with the sorts of the program. -/
def shownAt (P : Program) (root : Rel) (as : List (Ans (dom P.sorts) P)) :
    List ((S : Sorts) × R S) :=
  (as.filterMap (Ans.rootSpan root)).map (Sigma.mk P.sorts)

theorem shownAt_append (P : Program) (root : Rel) (as bs : List (Ans (dom P.sorts) P)) :
    shownAt dom P root (as ++ bs) = shownAt dom P root as ++ shownAt dom P root bs := by
  simp [shownAt]

theorem shownAt_mono {P : Program} {root : Rel} {as bs : List (Ans (dom P.sorts) P)}
    (h : ∀ a ∈ as, a ∈ bs) : ∀ a ∈ shownAt dom P root as, a ∈ shownAt dom P root bs := by
  intro a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
  obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.1 hr
  exact List.mem_map.2 ⟨r, List.mem_filterMap.2 ⟨x, h x hx, hxr⟩, rfl⟩

/-- What a step of the machine does, read off the engine's step. -/
theorem machine_step (s : E.StateAt dom) :
    ((E.costedAt dom K hK cells).step s).val =
      match (E.stepAt dom K hK s.P s.st).val with
      | .emit as st' => .emit (shownAt dom s.P s.root as) ⟨s.P, s.root, st'⟩
      | .done fin => .done (shownAt dom s.P s.root fin) :=
  costedAt_step_val E dom K hK s

/-- What a step of the machine costs: the engine's step, and a tick for each
answer it shows. -/
theorem machine_ticks (s : E.StateAt dom) :
    ((E.costedAt dom K hK cells).step s).ticks =
      (E.stepAt dom K hK s.P s.st).ticks + shown (E.stepAt dom K hK s.P s.st).val := by
  show (E.stepAt dom K hK s.P s.st >>= E.report dom s.P s.root).ticks = _
  rw [Cost.bind_ticks]
  cases (E.stepAt dom K hK s.P s.st).val <;> simp [Engine.report, shown]

/-- The answers the machine emits are those the engine's steps emit, as the
machine shows them. -/
theorem machine_emitted : ∀ (n : Nat) (s : E.StateAt dom),
    (E.costedAt dom K hK cells).runtime.emitted s n =
      shownAt dom s.P s.root (emits (E.stepAt dom K hK s.P) s.st n)
  | 0, _ => rfl
  | n + 1, s => by
    have hv := machine_step E dom K hK cells s
    cases hr : (E.stepAt dom K hK s.P s.st).val with
    | emit as st' =>
      rw [hr] at hv
      have hs : (E.costedAt dom K hK cells).runtime.step s =
          .emit (shownAt dom s.P s.root as) ⟨s.P, s.root, st'⟩ := hv
      have hn : next (E.stepAt dom K hK s.P s.st).val = some st' := by rw [hr]; rfl
      have ih := machine_emitted n ⟨s.P, s.root, st'⟩
      rw [emits_succ_some _ hn, hr, shownAt_append, ← ih]
      simp only [Runtime.emitted, Runtime.run_succ_emit _ hs]
      rfl
    | done fin =>
      rw [hr] at hv
      have hs : (E.costedAt dom K hK cells).runtime.step s = .done (shownAt dom s.P s.root fin) := hv
      have hn : next (E.stepAt dom K hK s.P s.st).val = none := by rw [hr]; rfl
      simp only [Runtime.emitted, Runtime.run_succ_done _ hs, emits, hn, outs_of_next_none hn]
      rfl

/-- The machine has reported that it is done when a step of the engine
has. -/
theorem machine_halts : ∀ (n : Nat) (s : E.StateAt dom),
    (E.costedAt dom K hK cells).runtime.Halts s n ↔
      after (E.stepAt dom K hK s.P) s.st n = none
  | 0, s => by
    simp only [after, reduceCtorEq, iff_false]
    exact Runtime.halts_zero _ s
  | n + 1, s => by
    have hv := machine_step E dom K hK cells s
    cases hr : (E.stepAt dom K hK s.P s.st).val with
    | emit as st' =>
      rw [hr] at hv
      have hs : (E.costedAt dom K hK cells).runtime.step s =
          .emit (shownAt dom s.P s.root as) ⟨s.P, s.root, st'⟩ := hv
      have hn : next (E.stepAt dom K hK s.P s.st).val = some st' := by rw [hr]; rfl
      rw [Runtime.halts_succ_emit _ hs, after_succ_some _ hn]
      exact machine_halts n ⟨s.P, s.root, st'⟩
    | done fin =>
      rw [hr] at hv
      have hs : (E.costedAt dom K hK cells).runtime.step s = .done (shownAt dom s.P s.root fin) := hv
      have hn : next (E.stepAt dom K hK s.P s.st).val = none := by rw [hr]; rfl
      rw [after_succ_none _ hn]
      exact iff_of_true (Runtime.halts_succ_done _ hs n) rfl

/-- What the machine spends is what the engine's steps cost, with a tick for
each answer shown. -/
theorem machine_spent : ∀ (n : Nat) (s : E.StateAt dom),
    (E.costedAt dom K hK cells).spent s n = cost (E.stepAt dom K hK s.P) s.st n
  | 0, _ => rfl
  | n + 1, s => by
    have hv := machine_step E dom K hK cells s
    have ht := machine_ticks E dom K hK cells s
    cases hr : (E.stepAt dom K hK s.P s.st).val with
    | emit as st' =>
      rw [hr] at hv
      have hs : (E.costedAt dom K hK cells).runtime.step s =
          .emit (shownAt dom s.P s.root as) ⟨s.P, s.root, st'⟩ := hv
      have hn : next (E.stepAt dom K hK s.P s.st).val = some st' := by rw [hr]; rfl
      rw [CostedRuntime.spent_succ_emit _ hs, cost_succ_some _ hn, ht,
        machine_spent n ⟨s.P, s.root, st'⟩]
    | done fin =>
      rw [hr] at hv
      have hs : (E.costedAt dom K hK cells).runtime.step s = .done (shownAt dom s.P s.root fin) := hv
      have hn : next (E.stepAt dom K hK s.P s.st).val = none := by rw [hr]; rfl
      rw [CostedRuntime.spent_succ_done _ hs, cost_succ_none _ hn, ht]

/-! ## The pair -/

/-- The step of the pair at the derivation kernel of a program is the step
of the pair of the two engines' steps there. -/
theorem beside_stepAt (P : Program) :
    (E.beside F).stepAt dom K hK P = stepC (E.stepAt dom K hK P) (F.stepAt dom K hK P) :=
  funext fun s => step_eq (dom P.sorts) (K P.sorts) (hK P.sorts) P _ _ s


/-- The state of the first engine in a state of the pair. -/
def fstAt (s : (E.beside F).StateAt dom) : E.StateAt dom := ⟨s.P, s.root, s.st.fst⟩

/-- **The machine of the pair emits everything the machine of its first
engine emits, and reports that it is done if that machine does.** -/
theorem beside_fst (s : (E.beside F).StateAt dom) (n : Nat) : ∃ m,
    (∀ a ∈ (E.costedAt dom K hK cells).runtime.emitted (fstAt E F dom s) n,
        a ∈ ((E.beside F).costedAt dom K hK cells).runtime.emitted s m) ∧
      ((E.costedAt dom K hK cells).runtime.Halts (fstAt E F dom s) n →
        ((E.beside F).costedAt dom K hK cells).runtime.Halts s m) := by
  obtain ⟨m, h1, h2⟩ := fst_run (E.stepAt dom K hK s.P) (F.stepAt dom K hK s.P) n s.st
  refine ⟨m, fun a ha => ?_, fun h => ?_⟩
  · rw [machine_emitted] at ha ⊢
    rw [beside_stepAt]
    exact shownAt_mono dom h1 a ha
  · rw [machine_halts] at h ⊢
    rw [beside_stepAt]
    exact h2 h

/-- **The machine of the pair reports that it is done only when the machine
of its first engine does**, and by then it has emitted everything that
machine emitted. -/
theorem beside_done (s : (E.beside F).StateAt dom) (m : Nat)
    (h : ((E.beside F).costedAt dom K hK cells).runtime.Halts s m) : ∃ n,
    (E.costedAt dom K hK cells).runtime.Halts (fstAt E F dom s) n ∧
      ∀ a ∈ (E.costedAt dom K hK cells).runtime.emitted (fstAt E F dom s) n,
        a ∈ ((E.beside F).costedAt dom K hK cells).runtime.emitted s m := by
  rw [machine_halts, beside_stepAt] at h
  obtain ⟨n, h1, h2⟩ := halt_fst _ _ m s.st h
  refine ⟨n, (machine_halts E dom K hK cells n (fstAt E F dom s)).2 h1, fun a ha => ?_⟩
  rw [machine_emitted] at ha ⊢
  rw [beside_stepAt]
  exact shownAt_mono dom h2 a ha

/-- **What the machine of the pair has spent when its second engine has
taken `n` steps**: at most twenty times what it had charged that engine and
three times what the machine of that engine spends in `n` steps, and a fixed
number of ticks for each step. By then it has emitted everything that
machine emits in `n` steps, or has reported that it is done. What the first
engine costs is not in the bound. -/
theorem beside_snd (s : (E.beside F).StateAt dom) (y : F.State (R s.P.sorts) Rel (Ans (dom s.P.sorts) s.P))
    (hy : s.st.snd = some y) (hI : Inv s.st) (n : Nat) : ∃ m,
    ((E.beside F).costedAt dom K hK cells).spent s m + pot s.st ≤
        20 * (s.st.paidSnd + 3 * (F.costedAt dom K hK cells).spent ⟨s.P, s.root, y⟩ n + n) + 16 ∧
      (((E.beside F).costedAt dom K hK cells).runtime.Halts s m ∨
        ∀ a ∈ (F.costedAt dom K hK cells).runtime.emitted ⟨s.P, s.root, y⟩ n,
          a ∈ ((E.beside F).costedAt dom K hK cells).runtime.emitted s m) := by
  obtain ⟨m, h1, h2⟩ :=
    snd_run (E.stepAt dom K hK s.P) (F.stepAt dom K hK s.P) n s.st y hy hI
  refine ⟨m, ?_, h2.imp (fun h => ?_) fun h a ha => ?_⟩
  · rw [machine_spent, machine_spent, beside_stepAt]
    exact h1
  · rw [machine_halts, beside_stepAt]
    exact h
  · rw [machine_emitted] at ha ⊢
    rw [beside_stepAt]
    exact shownAt_mono dom h a ha

/-- The pair starts from the first state of each engine, with nothing
charged. -/
theorem beside_start (P : Program) (q : Rel) :
    ((E.beside F).costedAt dom K hK cells).start P q =
      ⟨P, q.norm, ⟨((E.costedAt dom K hK cells).start P q).st,
        some ((F.costedAt dom K hK cells).start P q).st, 0, 0, 0, 0⟩⟩ := by
  simp only [CostedRuntime.start, Engine.costedAt, Engine.beside, init_eq, Cost.bind_val,
    Cost.pure_val]
  rfl

/-- Building the first state of the pair costs no more than building the
first state of each engine. -/
theorem beside_init_ticks (P : Program) (q : Rel) :
    (((E.beside F).costedAt dom K hK cells).init P q).ticks ≤
      ((E.costedAt dom K hK cells).init P q).ticks + ((F.costedAt dom K hK cells).init P q).ticks := by
  simp only [Engine.costedAt, Engine.beside, init_eq, Cost.bind_ticks, Cost.bind_val,
    Cost.pure_ticks]
  omega

theorem beside_start_fst (P : Program) (q : Rel) :
    fstAt E F dom (((E.beside F).costedAt dom K hK cells).start P q) =
      (E.costedAt dom K hK cells).start P q := by
  rw [beside_start]; rfl

/-! ## The laws of the pair -/

/-- **The pair is complete if its first engine is.** -/
theorem beside_complete (hc : (E.costedAt dom K hK cells).runtime.Complete) :
    ((E.beside F).costedAt dom K hK cells).runtime.Complete := fun P q hwf s hd =>
  (hc P q hwf s hd).imp id fun ⟨n, a, ha, hcov⟩ => by
    obtain ⟨m, h1, -⟩ :=
      beside_fst E F dom K hK cells (((E.beside F).costedAt dom K hK cells).start P q) n
    rw [beside_start_fst] at h1
    exact ⟨m, a, h1 a ha, hcov⟩

/-- **The pair reports that it is done exactly when its first engine
does.** -/
theorem beside_terminates (P : Program) (q : Rel) :
    ((E.beside F).costedAt dom K hK cells).runtime.Terminates P q ↔
      (E.costedAt dom K hK cells).runtime.Terminates P q := by
  constructor
  · rintro ⟨m, h⟩
    obtain ⟨n, h1, -⟩ := beside_done E F dom K hK cells
      (((E.beside F).costedAt dom K hK cells).start P q) m h
    rw [beside_start_fst] at h1
    exact ⟨n, h1⟩
  · rintro ⟨n, h⟩
    obtain ⟨m, -, h1⟩ :=
      beside_fst E F dom K hK cells (((E.beside F).costedAt dom K hK cells).start P q) n
    rw [beside_start_fst] at h1
    exact ⟨m, h1 h⟩

/-- **The pair is honest when it reports that it is done, if its first
engine is.** It is done only when the first engine is, and by then it has
emitted everything that engine emitted. -/
theorem beside_honest (hs : ((E.beside F).costedAt dom K hK cells).runtime.Sound)
    (hh : (E.costedAt dom K hK cells).runtime.HonestExhaustion) :
    ((E.beside F).costedAt dom K hK cells).runtime.HonestExhaustion := fun P q hwf m hm => by
  obtain ⟨n, h1, h2⟩ := beside_done E F dom K hK cells
    (((E.beside F).costedAt dom K hK cells).start P q) m hm
  rw [beside_start_fst] at h1 h2
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rw [hh P q hwf n h1]
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2 ⟨a, h2 a ha, hxa⟩
  · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 hx
    exact hs P q hwf m a ha hxa

/-- **What the pair has paid when its second engine has taken `n` steps**:
what building the first state of each engine costs, sixty times what the
machine of the second engine spends in `n` steps, and a fixed number of
ticks for each step. By then it has emitted everything that machine emits in
`n` steps, or has reported that it is done. What the steps of the first
engine cost is not in the bound. -/
theorem beside_paid (P : Program) (q : Rel) (n : Nat) : ∃ m,
    ((E.beside F).costedAt dom K hK cells).paid P q m ≤
        ((E.costedAt dom K hK cells).init P q).ticks +
          ((F.costedAt dom K hK cells).init P q).ticks +
          60 * (F.costedAt dom K hK cells).spent ((F.costedAt dom K hK cells).start P q) n +
          20 * n + 16 ∧
      (((E.beside F).costedAt dom K hK cells).runtime.Halts
          (((E.beside F).costedAt dom K hK cells).start P q) m ∨
        ∀ a ∈ (F.costedAt dom K hK cells).runtime.emitted
            ((F.costedAt dom K hK cells).start P q) n,
          a ∈ ((E.beside F).costedAt dom K hK cells).runtime.emitted
            (((E.beside F).costedAt dom K hK cells).start P q) m) := by
  have hi := beside_init_ticks E F dom K hK cells P q
  have e := beside_start E F dom K hK cells P q
  obtain ⟨m, h1, h2⟩ := beside_snd E F dom K hK cells
    ⟨P, q.norm, ⟨((E.costedAt dom K hK cells).start P q).st,
      some ((F.costedAt dom K hK cells).start P q).st, 0, 0, 0, 0⟩⟩
    ((F.costedAt dom K hK cells).start P q).st rfl ⟨Nat.le_refl _, Nat.zero_le _⟩ n
  have h3 : (F.costedAt dom K hK cells).spent
      ⟨P, q.norm, ((F.costedAt dom K hK cells).start P q).st⟩ n =
      (F.costedAt dom K hK cells).spent ((F.costedAt dom K hK cells).start P q) n := rfl
  have hp : ((E.beside F).costedAt dom K hK cells).paid P q m =
      (((E.beside F).costedAt dom K hK cells).init P q).ticks +
        ((E.beside F).costedAt dom K hK cells).spent
          (((E.beside F).costedAt dom K hK cells).start P q) m := rfl
  refine ⟨m, ?_, ?_⟩
  · rw [hp, e]
    simp only [pot] at h1
    omega
  · rw [e]
    exact h2

end Engine

end RwLog
