/-
# Answers that owe nothing to a definition

`Light D P h a`: the answer `a` relates nothing, or it is an answer of its
goal in the program where `h` derives nothing. Every rule of the kernel keeps
that, but unfolding an answer of the body of `h` that relates a pair onto a
call of `h`
(`rules_light`). When the body of `h` needs a name that the unfolding race
never reads whole (`Unfold.Tags`), the answers of a final unfolding have it
too (`light_raced`). So a request keeps it (`prov_light`): a run holds
answers that owe nothing to `h` until a table holds an answer of the body of
`h`.
-/
import RwLog.Rungs.Symmetric.Provenance
import RwLog.Rungs.Framework.Unfolding.Never

namespace RwLog

namespace Symmetric

open Goals Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The answer relates nothing, or it is an answer of its goal in the program
where `h` derives nothing. -/
def Light (D : Domain R) (P : Program) (h : Name) (a : Ans D P) : Prop :=
  den P.sorts.interp a.span = ∅ ∨ Valid D (P.withBody h .zero) a.goal a.span

/-- The answer is an answer of the body of `h`, or of its converse, and it
relates a pair. -/
def OnBody (P : Program) (h : Name) (a : Ans D P) : Prop :=
  (Charged.bodyOf P (.call h) = some a.goal.node ∨
    Charged.bodyOf P (.conv (.call h)) = some a.goal.node) ∧
  (den P.sorts.interp a.span).Nonempty

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D) {h : Name}

include hL in
theorem light_join {x y c : Ans D P} (hx : Light D P h x) (hy : Light D P h y)
    (e : (Ans.join D P K hK x y).val = some c) : Light D P h c := by
  obtain ⟨hok, hc, hg⟩ := (Ans.join_val K hK).1 e
  have hden := hL.compose_some _ _ _ hc
  rcases hx with hx | hx
  · exact .inl (by rw [hden, hx]; ext p; simp [PRel.comp])
  rcases hy with hy | hy
  · exact .inl (by rw [hden, hy]; ext p; simp [PRel.comp])
  refine .inr ?_
  rw [hg]
  exact Valid.join (x := x.goal.node) (y := y.goal.node) hx hy hok hc

include hL in
theorem light_meet {x y c : Ans D P} (hx : Light D P h x) (hy : Light D P h y)
    (e : (Ans.meetA D P K hK x y).val = some c) : Light D P h c := by
  obtain ⟨hok, hc, hg⟩ := (Ans.meetA_val K hK).1 e
  have hden := hL.meet_some _ _ _ hc
  rcases hx with hx | hx
  · exact .inl (by rw [hden, hx]; simp)
  rcases hy with hy | hy
  · exact .inl (by rw [hden, hy]; simp)
  refine .inr ?_
  rw [hg]
  exact Valid.meet (x := x.goal.node) (y := y.goal.node) hx hy hok hc

include hL in
/-- The rules of the kernel keep `Light`, but that an answer of the body of
`h` need not have it once it is unfolded. -/
theorem rules_light : Rules K hK (Light D P h) (OnBody P h) := by
  refine ⟨fun {lb rb n c} e => ?_, fun {k x y c} hx hy e => ?_, fun {k left x y c} hx hy e => ?_,
    fun {a c n} ha e => ?_, fun {a c u i} ha e => ?_, fun a ha => ?_⟩
  · obtain ⟨s, -, hl, hr, hsb, hg⟩ := (Ans.leaf_val K hK).1 e
    refine .inr ?_
    rw [hg]
    exact Valid.leaf hl hr hsb
  · cases k with
    | seq => exact light_join hL K hK hx hy e
    | and => exact light_meet hL K hK hx hy e
  · cases k with
    | seq =>
      cases left with
      | true => exact light_join hL K hK hx hy e
      | false => exact light_join hL K hK hy hx e
    | and => exact light_meet hL K hK hx hy e
  · obtain ⟨hb, hs, hg⟩ := Ans.unfold_val.1 e
    rcases ha with ha | ha
    · exact .inr (.inl (by rw [hs]; exact ha))
    by_cases hne : (den P.sorts.interp a.span).Nonempty
    swap
    · exact .inr (.inl (by rw [hs]; exact Set.not_nonempty_iff_eq_empty.1 hne))
    by_cases hon : Charged.bodyOf P (.call h) = some a.goal.node ∨
        Charged.bodyOf P (.conv (.call h)) = some a.goal.node
    · exact .inl ⟨hon, hne⟩
    refine .inr (.inr ?_)
    rw [hg, hs]
    unfold Charged.bodyOf at hb
    split at hb
    · next m =>
      have hm : m ≠ h := fun e => hon (.inl (by subst e; exact hb))
      have e' : a.goal = ⟨a.goal.lb, ((P.withBody h .zero).body m).norm, a.goal.rb⟩ := by
        rw [ProgramOf.withBody_ne _ _ hm, Option.some.inj hb]
      rw [e'] at ha
      exact Valid.unfold ha
    · next m =>
      have hm : m ≠ h := fun e => hon (.inr (by subst e; exact hb))
      have e' : a.goal = ⟨a.goal.lb, ((P.withBody h .zero).body m).normConv, a.goal.rb⟩ := by
        rw [ProgramOf.withBody_ne _ _ hm, Option.some.inj hb]
      rw [e'] at ha
      exact Valid.unfoldConv ha
    · cases hb
  · obtain ⟨hi, hs, hg⟩ := Ans.inj_val.1 e
    rcases ha with ha | ha
    · exact .inl (by rw [hs]; exact ha)
    refine .inr ?_
    rw [hg, hs]
    exact Valid.inj (x := a.goal.node) ha (List.mem_of_getElem? hi)
  · have e : (Ans.swapA D P a).val =
        ⟨⟨a.goal.rb, a.goal.node.normConv, a.goal.lb⟩, Answer.swap a.span, a.valid.swap⟩ := rfl
    rw [e]
    rcases ha with ha | ha
    · exact .inl (by
        show den P.sorts.interp (Answer.swap a.span) = ∅
        rw [Answer.den_swap, ha]; rfl)
    · exact .inr (Valid.swap (x := a.goal.node) ha)

variable {c : Name} {ξ : Nat → Span} {τ : Nat → GTerm}

include hL in
/-- The answers of a final unfolding owe nothing to `h`, when the body of `h`
needs a name the race never reads whole. -/
theorem light_raced (hP : ProgFO P) (hT : Unfold.Tags P c ξ τ)
    (hneed : ∀ s, ¬ Derives (P.withBody c .zero) (P.body h) s) (n : Nat) (g : GoalOf R Rel)
    (hg : GoalOk D g)
    (hfin : (Unfold.raced (K := DerivationKernel.over D K hK P) n g).val.1 = true) :
    ∀ a ∈ (Unfold.raced (K := DerivationKernel.over D K hK P) n g).val.2, Light D P h a := by
  intro a ha
  by_cases hne : (den P.sorts.interp a.span).Nonempty
  · have hgoal := (good_raced D P K hK hL hP).goal n g hg a ha
    have hv := Unfold.light_of_final (whole_raced K hK hL hP) hT hL hg hfin (hgoal ▸ a.valid) hne
    refine .inr ?_
    rw [hgoal]
    obtain ⟨hw, hd⟩ := hv
    exact ⟨hw, fun hL' => by
      obtain ⟨s, hs, e⟩ := hd hL'
      exact ⟨s, Derives.withBody_zero hneed hs, e⟩⟩
  · exact .inl (Set.not_nonempty_iff_eq_empty.1 hne)

include hL in
/-- **A request keeps it:** a table holds an answer of the body of `h`, or
every answer held owes nothing to `h`. -/
theorem prov_light {rd : EdgeReader} (hP : ProgFO P) (hT : Unfold.Tags P c ξ τ)
    (hneed : ∀ s, ¬ Derives (P.withBody c .zero) (P.body h) s)
    {st : StateOf R Rel (Ans D P)}
    (hst : Prov (Light D P h) (OnBody P h) (fun g => ¬ GoalOk D g) st) :
    Prov (Light D P h) (OnBody P h) (fun g => ¬ GoalOk D g)
      (request @rd (K := DerivationKernel.over D K hK P)
        (Unfold.raced (K := DerivationKernel.over D K hK P)) st).val.1 :=
  prov_request (rules_light hL K hK) _
    (fun n g hg hfin a ha =>
      .inl (light_raced hL K hK hP hT hneed n g (not_not.1 hg) hfin a ha)) hst

end Symmetric

end RwLog
