/-
# The mirrored machine keeps what the machine it mirrors keeps

For a machine `C` with every property of `Runtime.Keeps`, whose runs on
`conv q` and on `q` cost the same step for step (`ConvBisim`), and whose
first states for `a | b` and `b | a`, and for the two groupings of three
branches, are the same, the mirrored machine has every property of
`Runtime.Keeps` (`keeps`).

* It emits, step for step, what `C` emits up to order and equivalence
  (`Mirror.trace_start`), so it runs like `C` (`sameRun`) and everything
  stated on answers carries over.
* Each step of it emits what one step of one of the two runs emits
  (`step_from`), and costs at least what that step costs. So no answer of a
  step is covered by an earlier one of the same step, and across steps this
  carries over from `C`.
* On the converse and on the mirror image it goes through related states
  (`Mirror.convBisim`, `Mirror.dualBisim`).
-/
import RwLog.Rungs.Mirror.Direction
import RwLog.Rungs.Framework.Transfer

namespace RwLog

theorem ProgramOf.WellFormed.of_calls {P : Program} {q q' : Rel} (h : P.WellFormed q)
    (hc : ∀ n ∈ q'.calls, n ∈ q.calls) : P.WellFormed q' := by
  refine ⟨h.1, fun n hn => h.2.1 n ?_, h.2.2⟩
  rcases List.mem_append.1 hn with hn | hn
  · exact List.mem_append_left _ (hc n hn)
  · exact List.mem_append_right _ hn

theorem List.Forall₂.exists_right {α β : Type} {E : α → β → Prop} :
    ∀ {L : List α} {L' : List β}, List.Forall₂ E L L' → ∀ {a : α}, a ∈ L → ∃ b ∈ L', E a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hab t, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, e⟩ := List.Forall₂.exists_right t h
      exact ⟨b, List.mem_cons_of_mem _ hb, e⟩

/-- A relation that holds between the entries of a list, in order, holds
between the corresponding entries of a list related to it entry by entry. -/
theorem List.Forall₂.pairwise {α β : Type} {E : α → β → Prop} {S : α → α → Prop}
    {S' : β → β → Prop} (hE : ∀ a a' b b', E a a' → E b b' → S' a' b' → S a b) :
    ∀ {L : List α} {L' : List β}, List.Forall₂ E L L' → L'.Pairwise S' → L.Pairwise S
  | _, _, .nil, _ => List.Pairwise.nil
  | _, _, .cons hab t, hp => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hp
    refine List.pairwise_cons.2 ⟨fun b hb => ?_, List.Forall₂.pairwise hE t h2⟩
    obtain ⟨b', hb', e⟩ := List.Forall₂.exists_right t hb
    exact hE _ _ _ _ hab e (h1 b' hb')

namespace Mirror

open Cost RwLog.Runtime

variable {C : CostedRuntime}

/-! ## The same run -/

/-- The mirrored machine runs like the machine it mirrors. -/
theorem sameRun (hdual : C.runtime.DualTrace) : SameRun (machine C).runtime C.runtime where
  emitted P q hP n := by
    have h1 := (machine C).runtime.emitted_eq_flatten_trace n ((machine C).start P q)
    have h2 := C.runtime.emitted_eq_flatten_trace n (C.start P q)
    exact h1 ▸ h2 ▸ TraceEquiv.flatten (trace_start hdual hP n)
  halts P q hP n := by
    have h1 := (machine C).runtime.halts_iff_trace_length n ((machine C).start P q)
    have h2 := C.runtime.halts_iff_trace_length n (C.start P q)
    have h3 := (trace_start hdual hP n).length_eq
    exact h1.trans ((by rw [h3] : _ ↔ _).trans h2.symm)

/-! ## What one step emits -/

theorem win_le {x y : C.State} (h : wins x y = true) : (C.step x).ticks ≤ raced x y := by
  have hwin := winner_le_raceCost (C.step x).ticks (C.step y).ticks
  have : firstWins (C.step x).ticks (C.step y).ticks = true := h
  rwa [this] at hwin

theorem lose_le {x y : C.State} (h : wins x y = false) : (C.step y).ticks ≤ raced x y := by
  have hwin := winner_le_raceCost (C.step x).ticks (C.step y).ticks
  have : firstWins (C.step x).ticks (C.step y).ticks = false := h
  rwa [this] at hwin

/-- What a step of the mirrored machine emits is what one step of one of the
two runs emits, as answers to the query or swapped, and the step costs at
least what that step costs. `Q` is any property of the states of `C` that its
steps keep. -/
def From (C : CostedRuntime) (Q : C.State → Prop) (bs : List Span) (t : Nat) : Prop :=
  ∃ f z as z', Q z ∧ (C.step z).val = .emit as z' ∧ bs = orient f as ∧ (C.step z).ticks ≤ t

theorem go_from (Q : C.State → Prop)
    (hQ : ∀ z as z', Q z → (C.step z).val = .emit as z' → Q z') :
    ∀ (g : Nat) (f : Bool) (x y : C.State), Q x → Q y → ∀ bs s',
      (go C g f x y).val = .emit bs s' →
      Q s'.lead ∧ Q s'.lag ∧ From C Q bs (go C g f x y).ticks
  | 0, f, x, y, qx, qy, bs, s', h => by
    have alone : wins x y = true → wins y x = false →
        Q s'.lead ∧ Q s'.lag ∧ From C Q bs (go C 0 f x y).ticks := by
      intro h1 h2
      cases hx : (C.step x).val with
      | emit as x' =>
        rw [go_alone_emit f h1 h2 hx] at h ⊢
        cases h
        exact ⟨hQ x as x' qx hx, qy, f, x, as, x', qx, hx, rfl,
          by have := win_le h1; show _ ≤ 1 + raced x y + raced y x; omega⟩
      | done => rw [go_alone_done f h1 h2 hx] at h; cases h
    have over : wins x y = false → wins y x = true →
        Q s'.lead ∧ Q s'.lag ∧ From C Q bs (go C 0 f x y).ticks := by
      intro h1 h2
      cases hy : (C.step y).val with
      | emit as y' =>
        rw [go_overtake f h1 h2 hy] at h ⊢
        cases h
        exact ⟨hQ y as y' qy hy, qx, !f, y, as, y', qy, hy, rfl,
          by have := win_le h2; show _ ≤ 1 + raced x y + raced y x; omega⟩
      | done => rw [go_overtake_done f h1 h2 hy] at h; cases h
    have both : wins x y = wins y x →
        Q s'.lead ∧ Q s'.lag ∧ From C Q bs (go C 0 f x y).ticks := by
      intro hw
      cases hx : (C.step x).val with
      | emit as x' =>
        cases hy : (C.step y).val with
        | emit cs y' =>
          rw [go_both_emit f hw hx hy] at h ⊢
          cases h
          refine ⟨hQ x as x' qx hx, hQ y cs y' qy hy, f, x, as, x', qx, hx, rfl, ?_⟩
          show _ ≤ 1 + raced x y + raced y x
          cases h1 : wins x y
          · have := lose_le (hw ▸ h1 : wins y x = false); omega
          · have := win_le h1; omega
        | done => rw [go_both_done f hw (.inr hy)] at h; cases h
      | done => rw [go_both_done f hw (.inl hx)] at h; cases h
    cases h1 : wins x y <;> cases h2 : wins y x
    · exact both (by rw [h1, h2])
    · exact over h1 h2
    · exact alone h1 h2
    · exact both (by rw [h1, h2])
  | g + 1, f, x, y, qx, qy, bs, s', h => by
    by_cases hw : wins x y = true
    · cases hx : (C.step x).val with
      | emit as x' =>
        rw [go_lead_emit g f hw hx] at h ⊢
        cases h
        exact ⟨hQ x as x' qx hx, qy, f, x, as, x', qx, hx, rfl,
          by have := win_le hw; show _ ≤ 1 + raced x y; omega⟩
      | done => rw [go_lead_done g f hw hx] at h; cases h
    · have hw : wins x y = false := by simpa using hw
      cases hy : (C.step y).val with
      | done => rw [go_lag_done g f hw hy] at h; cases h
      | emit cs y' =>
        rw [go_catch g f hw hy] at h ⊢
        obtain ⟨h1, h2, f', z, as, z', qz, hz, e, ht⟩ :=
          go_from Q hQ g f x y' qx (hQ y cs y' qy hy) bs s' h
        exact ⟨h1, h2, f', z, as, z', qz, hz, e,
          by show _ ≤ 1 + raced x y + (go C g f x y').ticks; omega⟩

/-- A step of the mirrored machine from two runs with `Q`: the runs still
have `Q`, and what it emits is what one step of one of them emits, at no less
than its cost. -/
theorem step_from (Q : C.State → Prop)
    (hQ : ∀ z as z', Q z → (C.step z).val = .emit as z' → Q z')
    (s : StOf C.State) (qx : Q s.lead) (qy : Q s.lag) (bs : List Span) (s' : StOf C.State)
    (h : ((machine C).step s).val = .emit bs s') :
    Q s'.lead ∧ Q s'.lag ∧ From C Q bs ((machine C).step s).ticks :=
  go_from Q hQ s.gap s.fwd s.lead s.lag qx qy bs s' h

/-- Every step of a run of the mirrored machine emits what one step of one
of the two runs emits. -/
theorem trace_from (Q : C.State → Prop)
    (hQ : ∀ z as z', Q z → (C.step z).val = .emit as z' → Q z') :
    ∀ (n : Nat) (s : StOf C.State), Q s.lead → Q s.lag →
      ∀ ch ∈ (machine C).runtime.trace s n,
        ∃ f z as z', Q z ∧ (C.step z).val = .emit as z' ∧ ch = orient f as
  | 0, _, _, _, ch, h => absurd h List.not_mem_nil
  | n + 1, s, qx, qy, ch, h => by
    cases hs : ((machine C).step s).val with
    | done =>
      rw [(machine C).runtime.trace_succ_done (show (machine C).runtime.step s = .done from hs)] at h
      exact absurd h List.not_mem_nil
    | emit bs s' =>
      rw [(machine C).runtime.trace_succ_emit
        (show (machine C).runtime.step s = .emit bs s' from hs)] at h
      obtain ⟨h1, h2, f, z, as, z', qz, hz, e, -⟩ := step_from Q hQ s qx qy bs s' hs
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨f, z, as, z', qz, hz, e⟩
      · exact trace_from Q hQ n s' h1 h2 ch h

/-! ## No answer is covered by an earlier one -/

/-- `a` does not cover `b`. -/
abbrev NC (a b : Span) : Prop := ¬ a.Covers b

/-- No step from here on emits an answer covered by an earlier one of the
same step. -/
def Clean (C : CostedRuntime) (z : C.State) : Prop :=
  ∀ m, ∀ ch ∈ C.runtime.trace z m, ch.Pairwise NC

theorem Clean.next {z z' : C.State} {as : List Span} (h : Clean C z)
    (hz : (C.step z).val = .emit as z') : Clean C z' := fun m ch hch =>
  h (m + 1) ch (by
    rw [C.runtime.trace_succ_emit (show C.runtime.step z = .emit as z' from hz)]
    exact List.mem_cons_of_mem _ hch)

theorem Clean.step {z z' : C.State} {as : List Span} (h : Clean C z)
    (hz : (C.step z).val = .emit as z') : as.Pairwise NC :=
  h 1 as (by
    rw [C.runtime.trace_succ_emit (show C.runtime.step z = .emit as z' from hz)]
    exact List.mem_cons_self)

theorem clean_start (hns : C.runtime.NoSubsumed) {P : Program} {q : Rel} (hP : P.WellFormed q) :
    Clean C (C.start P q) := fun m => by
  have h := hns P q hP m
  have e := C.runtime.emitted_eq_flatten_trace m (C.start P q)
  exact (List.pairwise_flatten.1 (e ▸ h)).1

theorem orient_pairwise (f : Bool) {as : List Span} (h : as.Pairwise NC) :
    (orient f as).Pairwise NC := by
  cases f
  · exact List.Pairwise.map _ (fun a b hab hc => hab (Span.Covers.of_swap hc)) h
  · exact h

theorem noSubsumed (hdual : C.runtime.DualTrace) (hns : C.runtime.NoSubsumed) :
    (machine C).runtime.NoSubsumed := by
  intro P q hP n
  have e := (machine C).runtime.emitted_eq_flatten_trace n ((machine C).start P q)
  refine e ▸ List.pairwise_flatten.2 ⟨fun ch hch => ?_, ?_⟩
  · obtain ⟨f, z, as, z', qz, hz, rfl⟩ :=
      trace_from (Clean C) (fun z as z' h hz => h.next hz) n ((machine C).start P q)
        (clean_start hns hP) (clean_start hns hP.dual) ch hch
    exact orient_pairwise f (qz.step hz)
  · have h := hns P q hP n
    have e' := C.runtime.emitted_eq_flatten_trace n (C.start P q)
    refine List.Forall₂.pairwise ?_ (trace_start hdual hP n) (List.pairwise_flatten.1 (e' ▸ h)).2
    intro l1 l1' l2 l2' e1 e2 hS a ha b hb hab
    obtain ⟨a', ha', ea⟩ := e1.mem ha
    obtain ⟨b', hb', eb⟩ := e2.mem hb
    exact hS a' ha' b' hb' ((ea.2.trans hab).trans eb.1)

/-! ## On the converse and on the mirror image -/

theorem eq_of_swaps : ∀ {t t' : List (List Span)}, List.Forall₂ Swaps t t' →
    t = t'.map (·.map Span.swap)
  | _, _, .nil => rfl
  | _, _, .cons hab h => by rw [List.map_cons, ← eq_of_swaps h, hab]

theorem traceEquiv_of_swapEquiv : ∀ {t t' : List (List Span)}, List.Forall₂ SwapEquiv t t' →
    TraceEquiv t' (t.map (·.map Span.swap))
  | _, _, .nil => List.Forall₂.nil
  | _, _, .cons hab h => by
    refine List.Forall₂.cons ?_ (traceEquiv_of_swapEquiv h)
    have := (StepEquiv.map_swap hab).symm
    rwa [map_swap_swap] at this

theorem convTrace {rel : C.State → C.State → Prop} (hconv : ConvBisim C rel) :
    (machine C).runtime.ConvTrace := fun P q n =>
  eq_of_swaps ((convBisim hconv).toCostBisim.trace n _ _ ((convBisim hconv).start P q))

theorem dualTrace (hdual : C.runtime.DualTrace) : (machine C).runtime.DualTrace := by
  intro P q n hT
  have hs : Dual ((machine C).start P q) ((machine C).start P.dual q.dual) := by
    refine .inr ⟨rfl, ?_, fun n => hdual P q n hT⟩
    show (machine C).start P.dual q.dual = _
    rw [start_eq, ProgramOf.dual_dual, RelOf.dual_dual]
    rfl
  exact traceEquiv_of_swapEquiv ((dualBisim hdual).toCostBisim.trace n _ _ hs)

/-! ## Everything -/

/-- The mirrored machine keeps every property the machine it mirrors
keeps. -/
theorem keeps {Base : Runtime} {rel : C.State → C.State → Prop}
    (hk : C.runtime.Keeps Base) (hconv : ConvBisim C rel)
    (hor : ∀ P a b, C.start P (.or a b) = C.start P (.or b a))
    (hassoc : ∀ P a b c, C.start P (.or (.or a b) c) = C.start P (.or a (.or b c))) :
    (machine C).runtime.Keeps Base := by
  have hs := sameRun hk.dualTrace
  have hterm : ∀ P q, P.WellFormed q → C.runtime.Terminates P q →
      (machine C).runtime.Terminates P q :=
    fun P q hP ⟨n, hn⟩ => ⟨n, (hs.halts P q hP n).2 hn⟩
  have hterm' : ∀ P q, P.WellFormed q → (machine C).runtime.Terminates P q →
      C.runtime.Terminates P q :=
    fun P q hP ⟨n, hn⟩ => ⟨n, (hs.halts P q hP n).1 hn⟩
  refine
    { sound := hs.sound hk.sound
      complete := hs.complete hk.complete
      pointComplete := (hs.complete hk.complete).pointwise
      honest := hs.honest ⟨hk.sound, hk.complete, hk.honest⟩
      derivationGeneral := hs.derivationGeneral hk.derivationGeneral
      terminates := fun P q hP hb => hterm P q hP (hk.terminates P q hP hb)
      orComm := fun P a b n => ?_
      orAssoc := fun P a b c n => ?_
      emptySide := fun P a b hP ht he => ?_
      convTrace := convTrace hconv
      dualTrace := dualTrace hk.dualTrace
      theoryMono := fun P T q hP hT hsub a ha => ?_
      noSubsumed := noSubsumed hk.dualTrace hk.noSubsumed }
  · have : (machine C).start P (.or a b) = (machine C).start P (.or b a) := by
      rw [start_eq, start_eq, hor P a b]
      show StOf.mk _ (C.start P.dual (.or a.dual b.dual)) _ _ = _
      rw [hor P.dual a.dual b.dual]; rfl
    exact congrArg (fun s => (machine C).runtime.trace s n) this
  · have : (machine C).start P (.or (.or a b) c) = (machine C).start P (.or a (.or b c)) := by
      rw [start_eq, start_eq, hassoc P a b c]
      show StOf.mk _ (C.start P.dual (.or (.or a.dual b.dual) c.dual)) _ _ = _
      rw [hassoc P.dual a.dual b.dual c.dual]; rfl
    exact congrArg (fun s => (machine C).runtime.trace s n) this
  · have hPa : P.WellFormed a := hP.of_calls fun n hn => List.mem_append_left _ hn
    have he' : C.runtime.Answers P a = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x ⟨n, hx⟩ => ?_
      obtain ⟨x', hx', -⟩ := hs.symm.answer hPa hx
      exact Set.eq_empty_iff_forall_notMem.1 he x' ⟨n, hx'⟩
    obtain ⟨h1, h2, h3, h4⟩ := hk.emptySide P a b hP (hterm' P a hPa ht) he'
    refine ⟨hterm _ _ hP h1, hterm _ _ (hP.of_calls fun n hn => ?_) h2,
      hterm _ _ (hP.of_calls fun n hn => hn) h3, hterm _ _ (hP.of_calls fun n hn => ?_) h4⟩
    · exact List.mem_append.2 (List.mem_append.1 hn).symm
    · exact List.mem_append.2 (List.mem_append.1 hn).symm
  · have hPT : ProgramOf.WellFormed { P with theory := T } q := ⟨hP.1, hP.2.1, hT⟩
    obtain ⟨n, ha⟩ := ha
    obtain ⟨a0, ha0, e⟩ := hs.answer hPT ha
    rcases hk.theoryMono P T q hP hT hsub a0 ⟨n, ha0⟩ with hd | ⟨b0, ⟨m, hb0⟩, hc⟩
    · exact .inl fun M hM => by rw [e.refines T M hM]; exact hd M hM
    · obtain ⟨b, hb, eb⟩ := hs.symm.answer hP hb0
      exact .inr ⟨b, ⟨m, hb⟩, fun M hM =>
        (e.2.at_subset M).trans ((hc M hM).trans (eb.2.at_subset M))⟩

end Mirror

end RwLog
