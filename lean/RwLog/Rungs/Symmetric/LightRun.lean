/-
# A run that covers a pair that needs `h` holds an answer of the body of `h`

Rung 1's machine is run on one orientation of its input. `h` is a name whose
body, in the program run, needs a name the unfolding race never reads whole
(`Unfold.Tags`).

* Every state of the run holds only answers that owe nothing to `h`, or one
  of its tables holds an answer of the body of `h` (`prov_stateAt`,
  `body_or_light`).
* An answer of the root goal that owes nothing to `h` relates only pairs the
  query relates in the program where `h` derives nothing
  (`Light.root_sub`).
* So a run that has covered a pair the query does not relate where `h`
  derives nothing has a table that holds an answer of the body of `h`
  (`covered_body`), and that is so of a pair that needs pairs of a call of
  `h` in a context (`covered_body_ctx`).
-/
import RwLog.Rungs.Symmetric.Correct
import RwLog.Rungs.Symmetric.Light
import RwLog.Rungs.Framework.Zeroed

namespace RwLog

namespace Symmetric

open Answer

section kernel

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {K : Kernel R Cost}
variable {rd : EdgeReader} {hK : K.Refines D} {P : Program} {root : Rel}
variable {h c : Name} {ξ : Nat → Span} {τ : Nat → GTerm}

/-- A table of the state holds an answer of the body of `h`. -/
def HoldsBody (P : Program) (h : Name) (st : StateOf R Rel (Ans D P)) : Prop :=
  ∃ (i : Nat) (t : Table R Rel (Ans D P)), st.tables[i]? = some t ∧ ∃ a ∈ t.answers, OnBody P h a

/-- Every state of a run holds only answers that owe nothing to `h`, unless a
table holds an answer of the body of `h`. -/
theorem prov_stateAt (hL : D.Lawful P.sorts.interp) (hP : ProgFO P)
    (hT : Unfold.Tags P c ξ τ) (hneed : ∀ s, ¬ Derives (P.withBody c .zero) (P.body h) s) :
    ∀ r, Prov (Light D P h) (OnBody P h) (fun g => ¬ GoalOk D g)
      (stateAt (rd := @rd) K hK P root (Unfold.raced (K := DerivationKernel.over D K hK P)) r)
  | 0 => prov_init root
  | r + 1 => prov_light hL K hK hP hT hneed (prov_stateAt hL hP hT hneed r)

/-- A state of a run: a table holds an answer of the body of `h`, or every
answer of the root table owes nothing to `h`. -/
theorem body_or_light {st : StateOf R Rel (Ans D P)} (hG : Good (rd := @rd) st)
    (hp : Prov (Light D P h) (OnBody P h) (fun g => ¬ GoalOk D g) st) :
    HoldsBody P h st ∨ ∀ a ∈ st.answers 0, Light D P h a := by
  rcases hp with ⟨i, t, ht, hbad | hon⟩ | hlit
  · have hg : goalAt st i = some t.goal := by simp [goalAt, ht]
    have hgood := hG.base.good i t.goal hg
    exact absurd ⟨hgood.1, hgood.2.1, (hG.inv.core i t ht).1, hgood.2.2⟩ hbad
  · exact .inl ⟨i, t, ht, hon⟩
  · refine .inr fun a ha => ?_
    unfold StateOf.answers at ha
    cases ht : st.tables[0]? with
    | none => rw [ht] at ha; cases ha
    | some t => rw [ht] at ha; exact hlit.ans 0 t ht a ha

omit [DecidableEq R] in
/-- An answer of the root goal that owes nothing to `h` relates only pairs
the root relates in the program where `h` derives nothing. -/
theorem Light.root_sub (hL : D.Lawful P.sorts.interp) {a : Ans D P} (ha : Light D P h a)
    (hn : Normal root) (hg : a.goal = ⟨none, root, none⟩) :
    den P.sorts.interp a.span ⊆ (P.withBody h .zero).pairs root := by
  rcases ha with ha | ha
  · rw [ha]
    exact Set.empty_subset _
  · rw [hg, ← hn.norm_eq] at ha
    exact ha.sound hL

end kernel

section run

variable (rd : EdgeReader) {R : Sorts → Type} [∀ S, Answer (R S)] [∀ S, DecidableEq (R S)]
  (dom : ∀ S, Domain (R S)) (K : ∀ S, Kernel (R S) Cost) (hK : ∀ S, (K S).Refines (dom S))
variable (hD : ∀ S : Sorts, S.WellFormed → (dom S).Lawful S.interp) (hRd : GoodReader @rd)
variable {h c : Name} {ξ : Nat → Span} {τ : Nat → GTerm}

include hD hRd in
/-- **A run that has covered a pair the query does not relate where `h`
derives nothing holds an answer of the body of `h`.** The run is of the
machine on one orientation of its input, with the raced unfolding and any
reading of edges; the state is one of the first `n + 1` of the run. -/
theorem covered_body {P : Program} {q : Rel} (wf : P.WellFormed q)
    (hT : Unfold.Tags (orient P q).P c ξ τ)
    (hneed : ∀ s, ¬ Derives ((orient P q).P.withBody c .zero) ((orient P q).P.body h) s)
    {y : GTerm × GTerm} (hy : y ∉ (P.withBody h .zero).pairs q) {n : Nat}
    (hc : ((engine Unfold.raced @rd).costedAt dom K hK).oriented.Covered P q P.sorts.interp y n) :
    ∃ r ≤ n, HoldsBody (orient P q).P h
      (sAt Unfold.raced @rd dom K hK (orient P q).P (orient P q).root r) := by
  have wf' := wf_orient wf
  have hn := normal_orient_root P q
  have hL := hD _ wf'.2.2.1
  have hI := isRun_of_wf (U := Unfold.raced) (rd := @rd) (dom := dom) (K := K) (hK := hK) hD
    good_raced hRd wf'
  rw [hn.norm_eq] at hI
  obtain ⟨a', ha', hya⟩ := hc
  have he := CostedRuntime.oriented_init_emitted
    ((engine Unfold.raced @rd).costedAt dom K hK) P q n
  have ha'' : a' ∈ (((engine Unfold.raced @rd).costedAt dom K hK).runtime.emitted
      (((engine Unfold.raced @rd).costedAt dom K hK).runtime.init (orient P q).P
        (orient P q).root) n).map (Answer.as (orient P q).swap) := he ▸ ha'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha''
  have hinit := init_eq Unfold.raced @rd dom K hK (orient P q).P (orient P q).root
  rw [hn.norm_eq] at hinit
  have hb' : b ∈ (Rt Unfold.raced @rd dom K hK).emitted
      (stAt Unfold.raced @rd dom K hK (orient P q).P (orient P q).root 0) n := hinit ▸ hb
  obtain ⟨j, hj, a, ha, rfl⟩ : ∃ j ≤ n, ∃ a ∈
      (sAt Unfold.raced @rd dom K hK (orient P q).P (orient P q).root j).answers 0,
      b = sp Unfold.raced @rd dom K hK (orient P q).P a := by
    rcases run_cases hI n with ⟨-, hr⟩ | ⟨j, hj, -, hr⟩
    · have e : (Rt Unfold.raced @rd dom K hK).emitted
          (stAt Unfold.raced @rd dom K hK (orient P q).P (orient P q).root 0) n = _ :=
        congrArg Prod.fst hr
      rw [e] at hb'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb'
      exact ⟨n, Nat.le_refl n, a, ha, rfl⟩
    · have e : (Rt Unfold.raced @rd dom K hK).emitted
          (stAt Unfold.raced @rd dom K hK (orient P q).P (orient P q).root 0) n = _ :=
        congrArg Prod.fst hr
      rw [e] at hb'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb'
      exact ⟨j, Nat.le_of_lt hj, a, ha, rfl⟩
  refine ⟨j, hj, ?_⟩
  rcases body_or_light (hI.good j)
    (prov_stateAt hL (progFO_orient wf) hT hneed j) with hbody | hlight
  · exact hbody
  · exfalso
    have hsub := (hlight a ha).root_sub hL hn (rootAns_goal hI ha)
    rw [orient_pairs_zero] at hsub
    have key : ∀ b : Bool,
        y ∈ den P.sorts.interp (Answer.as b (sp Unfold.raced @rd dom K hK (orient P q).P a)) →
          y ∈ den (orient P q).P.sorts.interp (Answer.as b a.span) := fun b hb => by
      cases b <;> exact hb
    exact hy (Answer.as_sub (orient P q).P.sorts.interp (orient P q).swap hsub
      (key _ hya))

include hD hRd in
/-- **In a context**: a run on the context's query that has covered a pair
that needs pairs of a call of `h` holds an answer of the body of `h`. -/
theorem covered_body_ctx {P : Program} (Kc : Context)
    (wf : (Kc.program P).WellFormed (Kc.query (.call h)))
    (hT : Unfold.Tags (orient (Kc.program P) (Kc.query (.call h))).P c ξ τ)
    (hneed : ∀ s, ¬ Derives ((orient (Kc.program P) (Kc.query (.call h))).P.withBody c .zero)
      ((orient (Kc.program P) (Kc.query (.call h))).P.body h) s)
    {X : PRel} {y : GTerm × GTerm} (hd : Kc.Demands P (.call h) P.sorts.interp X y) {n : Nat}
    (hc : ((engine Unfold.raced @rd).costedAt dom K hK).oriented.Covered (Kc.program P)
      (Kc.query (.call h)) P.sorts.interp y n) :
    ∃ r ≤ n, HoldsBody (orient (Kc.program P) (Kc.query (.call h))).P h
      (sAt Unfold.raced @rd dom K hK (orient (Kc.program P) (Kc.query (.call h))).P
        (orient (Kc.program P) (Kc.query (.call h))).root r) :=
  covered_body @rd dom K hK hD hRd wf hT hneed (not_demands_zero P h Kc hd) hc

end run

end Symmetric

end RwLog
