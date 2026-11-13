/-
# What a run of the hedge is made of

A step of `Hedge.machine A B` is a step of `A`, or a step of `B`
(`step_cases`). So a state the hedge reaches holds a state `A` reaches and a
state `B` reaches (`Track`), and of what it has emitted by then:

* every answer is an answer `A` emitted or an answer `B` emitted
  (`emitted_origin`);
* every answer `A` emitted is covered by one (`halts_first` states this for
  a run that halts, where it is needed for honest exhaustion);
* none is covered by an earlier one, if that holds of `A` (`noSubsumed`).

The hedge halts only by a step of `A` that reports it is done.
-/
import RwLog.Rungs.Hedge.Steps
import RwLog.Rungs.Framework.Reach
import RwLog.Rungs.Tabled.Base.Proofs.Tier0.Inv

namespace RwLog

open Cost

namespace Hedge

variable {A B : CostedRuntime}

/-- The plain answers among those of a step of `B`. -/
def plains (bs : List Span) : List Span := bs.filter fun x => (plain x).val

/-- A step of the hedge: `A` is done; or a step of `A`; or `B` is done, which
is noted; or a step of `B`. -/
theorem step_cases (st : State A.State B.State) :
    ((A.step st.a).val = .done ∧ (step A B st).val = .done) ∨
    (∃ as a', (A.step st.a).val = .emit as a' ∧
      (step A B st).val = .emit (outA st as) (stA st as a')) ∨
    (st.live = true ∧ (B.step st.b).val = .done ∧
      (step A B st).val = .emit [] { st with live := false }) ∨
    (st.live = true ∧ ∃ bs b', (B.step st.b).val = .emit bs b' ∧
      (step A B st).val = .emit (outB st (plains bs)) (stB st (plains bs) b')) := by
  have viaA : (step A B st).val = (afterA A B st (A.step st.a).val).val →
      ((A.step st.a).val = .done ∧ (step A B st).val = .done) ∨
      (∃ as a', (A.step st.a).val = .emit as a' ∧
        (step A B st).val = .emit (outA st as) (stA st as a')) := by
    intro hv
    cases ha : (A.step st.a).val with
    | done => rw [ha] at hv; exact .inl ⟨rfl, hv⟩
    | emit as a' =>
      rw [ha, (afterA_emit st as a').1] at hv
      exact .inr ⟨as, a', rfl, hv⟩
  by_cases hl : st.live = true
  · rcases step_live hl with ⟨hv, -⟩ | ⟨hv, -⟩
    · rcases viaA hv with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · right; right
      cases hb : (B.step st.b).val with
      | done =>
        have : resB st = none := by unfold resB; rw [hb]
        rw [this, (afterB_none st).1] at hv
        exact .inl ⟨hl, rfl, hv⟩
      | emit bs b' =>
        have : resB st = some (plains bs, b') := by unfold resB; rw [hb]; rfl
        rw [this, (afterB_some st _ b').1] at hv
        exact .inr ⟨hl, bs, b', rfl, hv⟩
  · have hl' : st.live = false := by simpa using hl
    rcases viaA (step_dead hl').1 with h | h
    · exact .inl h
    · exact .inr (.inl h)

/-- What a state the hedge reaches holds, for the states `a0` and `b0` the
two machines started in. -/
structure Track (a0 : A.State) (b0 : B.State) (st : State A.State B.State) : Prop where
  inv : Inv A B st
  ex : ∃ ea nA eb nB, A.runtime.Reach a0 ea nA st.a ∧ B.runtime.Reach b0 eb nB st.b ∧
    (∀ x ∈ st.seen, x ∈ st.seenB ∨ x ∈ ea) ∧ (∀ x ∈ st.seenB, x ∈ eb) ∧
    (∀ x ∈ ea, ∃ y ∈ st.seen, y.Covers x) ∧
    ((∀ n, (A.runtime.emitted a0 n).Pairwise fun a b => ¬ a.Covers b) →
      st.seen.Pairwise fun a b => a.covers? b = false)

/-- Every state the hedge reaches holds what `Track` says, and what it has
emitted is what it has seen. -/
theorem track {a0 : A.State} {b0 : B.State} {es : List Span} {m : Nat}
    {st st0 : (machine A B).runtime.State}
    (h0 : st0 = (⟨a0, b0, true, true, 0, [], []⟩ : State A.State B.State))
    (r : (machine A B).runtime.Reach st0 es m st) :
    (st : State A.State B.State).seen = es ∧ Track a0 b0 st := by
  induction r with
  | refl =>
    subst h0
    exact ⟨rfl, Inv.mk (fun t ht => nomatch ht) (fun t ht => nomatch ht) (Nat.le_refl _),
      [], 0, [], 0, .refl, .refl, (fun x hx => nomatch hx), (fun x hx => nomatch hx),
      (fun x hx => nomatch hx), fun _ => List.Pairwise.nil⟩
  | @step es n s' s'' as _ hstep ih =>
    obtain ⟨hseen, hinv, ea, nA, eb, nB, rA, rB, hor, hsb, hcov, hpw⟩ := ih
    have hstep' : (step A B s').val = .emit as s'' := hstep
    rcases step_cases s' with ⟨-, hv⟩ | ⟨as₀, a', ha, hv⟩ | ⟨-, -, hv⟩ | ⟨-, bs, b', hb, hv⟩
    · rw [hv] at hstep'; cases hstep'
    · rw [hv] at hstep'
      obtain ⟨rfl, rfl⟩ := StepOf.emit.inj hstep'
      have ha' : A.runtime.step s'.a = .emit as₀ a' := ha
      refine ⟨by rw [← hseen]; rfl, inv_stA hinv as₀ a', ea ++ as₀, nA + 1, eb, nB,
        rA.step ha', rB, ?_, hsb, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · rcases hor x h with h' | h'
          · exact .inl h'
          · exact .inr (List.mem_append_left _ h')
        · exact .inr (List.mem_append_right _ (List.mem_filter.1 h).1)
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · obtain ⟨y, hy, hyx⟩ := hcov x h
          exact ⟨y, List.mem_append_left _ hy, hyx⟩
        · by_cases hc : (s'.seenB.any fun t => t.covers? x) = true
          · obtain ⟨t, ht, htx⟩ := List.any_eq_true.1 hc
            exact ⟨t, List.mem_append_left _ (hinv.sub t ht), (covers?_iff t x).1 htx⟩
          · exact ⟨x, List.mem_append_right _ (List.mem_filter.2 ⟨h, by simpa using hc⟩),
              Span.Covers.refl x⟩
      · intro hA
        have hall := hA (nA + 1)
        rw [(rA.step ha').emitted, List.pairwise_append] at hall
        obtain ⟨-, hpas, hcross⟩ := hall
        show (s'.seen ++ outA s' as₀).Pairwise _
        rw [List.pairwise_append]
        refine ⟨hpw hA, ?_, ?_⟩
        · refine (hpas.sublist List.filter_sublist).imp fun {a b} hab => ?_
          cases hc : a.covers? b with
          | false => rfl
          | true => exact absurd ((covers?_iff a b).1 hc) hab
        · intro a ha₁ b hb₁
          obtain ⟨hb₂, hb₃⟩ := List.mem_filter.1 hb₁
          rcases hor a ha₁ with h | h
          · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
              Bool.not_eq_true] at hb₃
            exact hb₃ a h
          · cases hc : a.covers? b with
            | false => rfl
            | true => exact absurd ((covers?_iff a b).1 hc) (hcross a h b hb₂)
    · rw [hv] at hstep'
      obtain ⟨rfl, rfl⟩ := StepOf.emit.inj hstep'
      exact ⟨by rw [← hseen]; simp, ⟨hinv.plain, hinv.sub, hinv.le⟩, ea, nA, eb, nB, rA, rB,
        hor, hsb, hcov, hpw⟩
    · rw [hv] at hstep'
      obtain ⟨rfl, rfl⟩ := StepOf.emit.inj hstep'
      have hb' : B.runtime.step s'.b = .emit bs b' := hb
      have hpl : ∀ t ∈ plains bs, t.c = [] := fun t ht =>
        plain_sound (by simpa using (List.mem_filter.1 ht).2)
      refine ⟨by rw [← hseen]; rfl, inv_stB hinv hpl b', ea, nA, eb ++ bs, nB + 1, rA,
        rB.step hb', ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · rcases hor x h with h' | h'
          · exact .inl (List.mem_append_left _ h')
          · exact .inr h'
        · exact .inl (List.mem_append_right _ h)
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact List.mem_append_left _ (hsb x h)
        · exact List.mem_append_right _ (List.mem_filter.1 ((fresh_sublist _ _).subset h)).1
      · intro x hx
        obtain ⟨y, hy, hyx⟩ := hcov x hx
        exact ⟨y, List.mem_append_left _ hy, hyx⟩
      · intro hA
        exact R001.Tier0.pw_fresh (hpw hA)

/-- What a run of the hedge from the start has emitted, and where it is. -/
theorem run_track (P : Program) (q : Rel) (m : Nat) :
    ∃ k st, (machine A B).runtime.Reach ((machine A B).start P q)
        ((machine A B).runtime.emitted ((machine A B).start P q) m) k st ∧
      st.seen = (machine A B).runtime.emitted ((machine A B).start P q) m ∧
      Track (A.start P q) (B.start P q) st ∧
      ((machine A B).runtime.Halts ((machine A B).start P q) m → (A.step st.a).val = .done) := by
  have hst : (machine A B).start P q = ⟨A.start P q, B.start P q, true, true, 0, [], []⟩ := rfl
  rcases Runtime.run_cases (R := (machine A B).runtime) m ((machine A B).start P q) with ⟨st, r, hn⟩ | ⟨k, st, -, r, hd, -⟩
  · obtain ⟨h1, h2⟩ := track hst r
    exact ⟨m, st, r, h1, h2, fun hh => absurd hh hn⟩
  · obtain ⟨h1, h2⟩ := track hst r
    refine ⟨k, st, r, h1, h2, fun _ => ?_⟩
    have hd' : (step A B st).val = .done := hd
    rcases step_cases st with ⟨h, -⟩ | ⟨_, _, -, hv⟩ | ⟨-, -, hv⟩ | ⟨-, _, _, -, hv⟩
    · exact h
    · rw [hv] at hd'; cases hd'
    · rw [hv] at hd'; cases hd'
    · rw [hv] at hd'; cases hd'

/-- Every answer the hedge emits is an answer of `A` or an answer of `B`. -/
theorem emitted_origin (P : Program) (q : Rel) (m : Nat) :
    ∀ x ∈ (machine A B).runtime.emitted ((machine A B).start P q) m,
      (∃ n, x ∈ A.runtime.emitted (A.start P q) n) ∨
        (∃ n, x ∈ B.runtime.emitted (B.start P q) n) := by
  intro x hx
  obtain ⟨k, st, -, hseen, ⟨-, ea, nA, eb, nB, rA, rB, hor, hsb, -, -⟩, -⟩ :=
    run_track (A := A) (B := B) P q m
  rw [← hseen] at hx
  rcases hor x hx with h | h
  · exact .inr ⟨nB, by rw [rB.emitted]; exact hsb x h⟩
  · exact .inl ⟨nA, by rw [rA.emitted]; exact h⟩

/-- When the hedge halts, `A` has halted, and every answer of `A` is covered
by an answer the hedge emitted. -/
theorem halts_first (P : Program) (q : Rel) (m : Nat)
    (h : (machine A B).runtime.Halts ((machine A B).start P q) m) :
    ∃ n, A.runtime.Halts (A.start P q) n ∧ ∀ x ∈ A.runtime.emitted (A.start P q) n,
      ∃ y ∈ (machine A B).runtime.emitted ((machine A B).start P q) m, y.Covers x := by
  obtain ⟨k, st, -, hseen, ⟨-, ea, nA, eb, nB, rA, -, -, -, hcov, -⟩, hd⟩ :=
    run_track (A := A) (B := B) P q m
  obtain ⟨hh, he⟩ := rA.halts (hd h)
  refine ⟨nA + 1, hh, fun x hx => ?_⟩
  rw [he] at hx
  rw [← hseen]
  exact hcov x hx

/-- No answer of the hedge is covered by an earlier one, if that holds of
`A`. -/
theorem noSubsumed (P : Program) (q : Rel)
    (hA : ∀ n, (A.runtime.emitted (A.start P q) n).Pairwise fun a b => ¬ a.Covers b) (m : Nat) :
    ((machine A B).runtime.emitted ((machine A B).start P q) m).Pairwise
      fun a b => ¬ a.Covers b := by
  obtain ⟨k, st, -, hseen, ⟨-, ea, nA, eb, nB, -, -, -, -, -, hpw⟩, -⟩ :=
    run_track (A := A) (B := B) P q m
  rw [← hseen]
  refine (hpw hA).imp fun {a b} hab hc => ?_
  rw [(covers?_iff a b).2 hc] at hab
  cases hab

end Hedge

end RwLog
