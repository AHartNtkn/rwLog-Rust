/-
# Two runs of the hedge that go the same way

Which machine the hedge follows at a step depends only on what the next steps
of the two machines cost. So if two runs of `A` cost the same step for step
and emit related answers, and likewise two runs of `B`, the two runs of the
hedge take the same turns and emit related answers (`step_sim`).

How the answers are related is a parameter (`Rels`): the same up to the
converse for the run on `conv q`, the same up to order and equivalence for
the run on the mirror image. `B`'s answers have to be related closely enough
that the plain ones correspond and cost the same to tell.
-/
import RwLog.Rungs.Hedge.Runs
import RwLog.Rungs.Hedge.Second
import RwLog.Rungs.Framework.Trace

namespace RwLog

open Cost

namespace Hedge

/-- How the answers of two runs are related: the answers of a step of `A`
(`EA`), of a step of `B` (`EB`), of a step of the hedge (`E`), everything
emitted so far (`S`), and what of it came from `B` (`SB`). -/
structure Rels where
  EA : List Span → List Span → Prop
  EB : List Span → List Span → Prop
  E : List Span → List Span → Prop
  S : List Span → List Span → Prop
  SB : List Span → List Span → Prop
  plainTicks : ∀ {bs bs'}, EB bs bs' → (filterL plain bs').ticks = (filterL plain bs).ticks
  plains : ∀ {bs bs'}, EB bs bs' → EB (plains bs) (plains bs')
  outA : ∀ {as as' sb sb'}, EA as as' → SB sb sb' →
    E (as.filter fun x => !sb.any fun t => t.covers? x)
      (as'.filter fun x => !sb'.any fun t => t.covers? x)
  outB : ∀ {ps ps' s s'}, EB ps ps' → S s s' → E (fresh s ps) (fresh s' ps')
  appS : ∀ {s s' o o'}, S s s' → E o o' → S (s ++ o) (s' ++ o')
  appSB : ∀ {s s' o o'}, SB s s' → E o o' → SB (s ++ o) (s' ++ o')
  nil : E [] []

/-- Two steps cost the same and correspond. -/
def CRel {σ : Type} (E : List Span → List Span → Prop) (Sim : σ → σ → Prop)
    (x x' : Cost (Step σ)) : Prop :=
  x'.ticks = x.ticks ∧ Step.Rel E Sim x.val x'.val

variable {A B : CostedRuntime}

/-- Two states of the hedge correspond. -/
def SimH (r : Rels) (SimA : A.State → A.State → Prop) (SimB : B.State → B.State → Prop)
    (st st' : State A.State B.State) : Prop :=
  SimA st.a st'.a ∧ SimB st.b st'.b ∧ st'.live = st.live ∧ st'.last = st.last ∧
    st'.streak = st.streak ∧ r.S st.seen st'.seen ∧ r.SB st.seenB st'.seenB

variable {r : Rels} {SimA : A.State → A.State → Prop} {SimB : B.State → B.State → Prop}

theorem afterA_sim {st st' : State A.State B.State} (h : SimH r SimA SimB st st')
    {x x' : Step A.State} (hx : Step.Rel r.EA SimA x x') :
    Step.Rel r.E (SimH r SimA SimB) (afterA A B st x).val (afterA A B st' x').val := by
  obtain ⟨ha, hb, hl, hla, hs, hS, hSB⟩ := h
  cases x with
  | done =>
    cases x' with
    | done => exact trivial
    | emit as' a' => exact hx.elim
  | emit as a₁ =>
    cases x' with
    | done => exact hx.elim
    | emit as' a₁' =>
      rw [(afterA_emit st as a₁).1, (afterA_emit st' as' a₁').1]
      have hE := r.outA hx.1 hSB
      exact ⟨hE, hx.2, hb, hl, rfl, by simp only [stA, hla, hs], r.appS hS hE, hSB⟩

theorem afterB_sim {st st' : State A.State B.State} (h : SimH r SimA SimB st st')
    (hx : Step.Rel r.EB SimB (B.step st.b).val (B.step st'.b).val) :
    Step.Rel r.E (SimH r SimA SimB) (afterB A B st (resB st)).val
      (afterB A B st' (resB st')).val := by
  obtain ⟨ha, hb, hl, hla, hs, hS, hSB⟩ := h
  unfold resB
  cases h1 : (B.step st.b).val with
  | done =>
    cases h2 : (B.step st'.b).val with
    | done => exact ⟨r.nil, ha, hb, rfl, hla, hs, hS, hSB⟩
    | emit bs' b' => rw [h1, h2] at hx; exact hx.elim
  | emit bs b₁ =>
    cases h2 : (B.step st'.b).val with
    | done => rw [h1, h2] at hx; exact hx.elim
    | emit bs' b₁' =>
      rw [h1, h2] at hx
      show Step.Rel r.E (SimH r SimA SimB) (afterB A B st (some (plains bs, b₁))).val
        (afterB A B st' (some (plains bs', b₁'))).val
      rw [(afterB_some st _ b₁).1, (afterB_some st' _ b₁').1]
      have hE := r.outB (r.plains hx.1) hS
      exact ⟨hE, ha, hx.2, hl, rfl, by simp only [stB, hla, hs], r.appS hS hE, r.appSB hSB hE⟩

/-- Corresponding states of the hedge take corresponding steps, when the two
machines do and their steps cost the same. -/
theorem step_sim (hA : ∀ a a', SimA a a' → CRel r.EA SimA (A.step a) (A.step a'))
    (hB : ∀ b b', SimB b b' → CRel r.EB SimB (B.step b) (B.step b'))
    {st st' : State A.State B.State} (h : SimH r SimA SimB st st') :
    Step.Rel r.E (SimH r SimA SimB) (step A B st).val (step A B st').val := by
  obtain ⟨hAt, hAv⟩ := hA _ _ h.1
  obtain ⟨hBt, hBv⟩ := hB _ _ h.2.1
  by_cases hl : st.live = true
  · have hl' : st'.live = true := h.2.2.1.trans hl
    have hpa : padA A B st' = padA A B st := by simp only [padA, h.2.2.2.1, h.2.2.2.2.1]
    have hpb : padB A B st' = padB A B st := by simp only [padB, h.2.2.2.1, h.2.2.2.2.1]
    have hcb : costB B st'.b = costB B st.b := by
      unfold costB
      rw [hBt]
      cases h1 : (B.step st.b).val with
      | done =>
        cases h2 : (B.step st'.b).val with
        | done => rfl
        | emit bs' b' => rw [h1, h2] at hBv; exact hBv.elim
      | emit bs b₁ =>
        cases h2 : (B.step st'.b).val with
        | done => rw [h1, h2] at hBv; exact hBv.elim
        | emit bs' b₁' =>
          rw [h1, h2] at hBv
          simp only [r.plainTicks hBv.1]
    obtain ⟨-, hw⟩ := race_sim (sideA A B st) (sideB A B st) (sideA A B st') (sideB A B st')
      (by rw [sideA_ticks, sideA_ticks, hpa, hAt]) (by rw [sideB_ticks, sideB_ticks, hpb, hcb])
    have e : ∀ s : State A.State B.State, s.live = true →
        (step A B s).val = Sum.elim (fun x => (afterA A B s x).val)
          (fun x => (afterB A B s x).val) (race (sideA A B s) (sideB A B s)).val := by
      intro s hs
      simp only [step, hs, ite_true, bind_val]
      cases (race (sideA A B s) (sideB A B s)).val <;> rfl
    rw [e st hl, e st' hl']
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, sideA_val, sideA_val]
      exact afterA_sim h hAv
    · rw [h1, h2, sideB_val, sideB_val]
      exact afterB_sim h hBv
  · have hl0 : st.live = false := by simpa using hl
    have hl' : st'.live = false := h.2.2.1.trans hl0
    rw [(step_dead hl0).1, (step_dead hl').1]
    exact afterA_sim h hAv

/-- Corresponding runs of the hedge have corresponding traces. -/
theorem trace_sim (hA : ∀ a a', SimA a a' → CRel r.EA SimA (A.step a) (A.step a'))
    (hB : ∀ b b', SimB b b' → CRel r.EB SimB (B.step b) (B.step b'))
    {st st' : State A.State B.State} (h : SimH r SimA SimB st st') (n : Nat) :
    List.Forall₂ r.E ((machine A B).runtime.trace st n) ((machine A B).runtime.trace st' n) :=
  Runtime.trace_of_sim (R := (machine A B).runtime) (R' := (machine A B).runtime)
    (Sim := SimH r SimA SimB) (fun _ _ hs => step_sim hA hB hs) n st st' h

end Hedge

end RwLog
