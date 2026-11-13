/-
# Rung R001: combining certificates

Certificates for several goals can be put together, and a goal whose push
strategy reads certified goals can be added on top.

An entry is good (`GoodE`) when its cover holds derivable answers and covers
everything its goal derives; this does not depend on the list the entry sits
in, and every entry of a valid certificate is good. Good entries with equal
goals have covers that cover each other, so the pushes a strategy runs from
one cover are, up to equivalent boundaries, the pushes it runs from another
(`maxima_transfer`). So a strategy that is listed in a part of a list is
listed in the whole list (`strat_transfer`), and the closure condition of a
certificate follows from goodness alone (`valid_of_pre`).
-/
import RwLog.Rungs.R001.Proofs.CertOfHalt

namespace RwLog

namespace R001

namespace Combine

open Tier0 Exact CertHalts CertOfHalt

variable {P : Program}

/-- An entry whose cover holds derivable answers of its goal and covers
everything the goal derives. -/
def GoodE (P : Program) (e : CertEntry) : Prop :=
  GoodG e.goal ∧ (∀ f ∈ e.cover, GDerives P e.goal f) ∧
    ∀ s, Derives P e.goal.e s → XC P.theory e.cover (GDen e.goal s.den)

theorem _root_.RwLog.R001.CertOfHalt.Listed.mono {C₁ C : List CertEntry} {ρ : Nat} {d : Goal} {fl : Bool}
    (h : Listed C₁ ρ d fl) (hsub : ∀ e ∈ C₁, e ∈ C) : Listed C ρ d fl := by
  obtain ⟨e', he', h1, h2⟩ := h
  exact ⟨e', hsub e' he', h1, h2⟩

theorem _root_.RwLog.R001.CertOfHalt.Listed.weaken {C : List CertEntry} {ρ ρ' : Nat} {d : Goal} {fl : Bool}
    (h : Listed C ρ d fl) (hρ : ρ ≤ ρ') : Listed C ρ' d fl := by
  obtain ⟨e', he', h1, h2⟩ := h
  refine ⟨e', he', h1, ?_⟩
  cases fl
  · simp only [Bool.false_eq_true, ite_false] at h2 ⊢; omega
  · simp only [ite_true] at h2 ⊢; omega

/-- The cover a list gives a listed goal is the cover of a listed entry. -/
theorem certCover_spec {C : List CertEntry} {L : Goal}
    (h : ∃ e ∈ C, e.goal.same L.norm.2 = true) :
    ∃ e ∈ C, e.goal.same L.norm.2 = true ∧ certCover C L = orient L.norm.1 e.cover := by
  obtain ⟨e', he', hs'⟩ := h
  cases hf : C.find? (fun e => e.goal.same L.norm.2) with
  | none => exact absurd hs' (by simpa using List.find?_eq_none.1 hf e' he')
  | some e =>
    exact ⟨e, List.mem_of_find?_eq_some hf,
      List.find?_some (p := fun e : CertEntry => e.goal.same L.norm.2) hf, by simp [certCover, hf]⟩

section Laws

variable (hL : SimpLaws P.theory)
include hL

theorem goodE_of_valid {C : List CertEntry} {D : Nat} {root : Goal} (hC : Cert.Valid P C D root)
    {e : CertEntry} (he : e ∈ C) : GoodE P e :=
  ⟨goodG_of_interfaced (hC.2 e he).1, (hC.2 e he).2.1, fun s hs => by
    obtain ⟨w, hw⟩ := dw_of_derives hs
    exact cert_xc hL hC _ e he w s hw le_rfl⟩

/-- Good entries with equal goals have covers that cover each other. -/
theorem good_mutual {e₁ e₂ : CertEntry} (h₁ : GoodE P e₁) (h₂ : GoodE P e₂)
    (hs : e₁.goal.same e₂.goal = true) : ∀ f ∈ e₁.cover, ∃ f' ∈ e₂.cover, f'.Covers f := by
  intro f hf
  obtain ⟨s, hd, hsub⟩ := gderives_sub hL (h₁.2.1 f hf) h₁.1
  rw [same_e hs] at hd
  rw [same_gden hs h₁.1 h₂.1] at hsub
  exact (h₂.2.2 s hd).cover hsub

/-- The tables of good entries satisfy the table invariant. -/
theorem xinv_certTables {C : List CertEntry} (h : ∀ e ∈ C, GoodE P e) : XInv P (certTables C) where
  good := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
    exact (h e he).1
  sub := by
    intro t ht a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
    exact gderives_sub hL ((h e he).2.1 a ha) (h e he).1
  comp := by
    intro t ht _ s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
    exact (h e he).2.2 s hs

/-- Two lists of good entries give a listed goal covers with equivalent
maxima. -/
theorem maxima_transfer {C₁ C : List CertEntry} (h₁ : ∀ e ∈ C₁, GoodE P e)
    (h : ∀ e ∈ C, GoodE P e) {L : Goal} (hl₁ : ∃ e ∈ C₁, e.goal.same L.norm.2 = true)
    (hl : ∃ e ∈ C, e.goal.same L.norm.2 = true) :
    ∀ x ∈ maxima (certCover C L), ∃ x₁ ∈ maxima (certCover C₁ L), x.Equiv x₁ := by
  obtain ⟨e₁, he₁, hs₁, hc₁⟩ := certCover_spec hl₁
  obtain ⟨e, he, hs, hc⟩ := certCover_spec hl
  rw [hc₁, hc]
  have hss : e.goal.same e₁.goal = true := Goal.same_trans hs (Goal.same_symm hs₁)
  intro x hx
  exact maxima_equiv (orient_cover (good_mutual hL (h e he) (h₁ e₁ he₁) hss))
    (orient_cover (good_mutual hL (h₁ e₁ he₁) (h e he) (Goal.same_symm hss))) hx

/-- A strategy listed in a part of a list of good entries is listed in the
whole list. -/
theorem strat_transfer {C₁ C : List CertEntry} (hsub : ∀ e ∈ C₁, e ∈ C)
    (hg : ∀ e ∈ C, GoodE P e) {ρ : Nat} {g : Goal} {st₁ : List (Goal × Bool)}
    (hst : st₁ ∈ certStrategies P C₁ g) (hall : ∀ d ∈ st₁, Listed C₁ ρ d.1 d.2) :
    ∃ st ∈ certStrategies P C g, ∀ d ∈ st, Listed C ρ d.1 d.2 := by
  have push : ∀ (L : Goal) (push : Span → Goal),
      (∀ x x' : Span, x.Equiv x' → (push x).same (push x') = true) →
      (∀ d ∈ (L, true) :: (maxima (certCover C₁ L)).map (fun x => (push x, false)),
        Listed C₁ ρ d.1 d.2) →
      ∀ d ∈ (L, true) :: (maxima (certCover C L)).map (fun x => (push x, false)),
        Listed C ρ d.1 d.2 := by
    intro L push hp h d hd
    have hLl := h (L, true) List.mem_cons_self
    rcases List.mem_cons.1 hd with rfl | hd
    · exact hLl.mono hsub
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      have hl₁ : ∃ e ∈ C₁, e.goal.same L.norm.2 = true :=
        let ⟨e', he', hs', _⟩ := hLl; ⟨e', he', hs'⟩
      obtain ⟨x₁, hx₁, hxe⟩ := maxima_transfer hL (fun e he => hg e (hsub e he)) hg hl₁
        (let ⟨e', he', hs'⟩ := hl₁; ⟨e', hsub e' he', hs'⟩) x hx
      exact ((h (push x₁, false) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x₁, hx₁, rfl⟩))).mono
        hsub).same (hp x₁ x hxe.symm)
  obtain ⟨lb, ex, rb⟩ := g
  cases ex with
  | zero => exact ⟨st₁, hst, fun d hd => (hall d hd).mono hsub⟩
  | span _ => exact ⟨st₁, hst, fun d hd => (hall d hd).mono hsub⟩
  | or _ _ => exact ⟨st₁, hst, fun d hd => (hall d hd).mono hsub⟩
  | call _ => exact ⟨st₁, hst, fun d hd => (hall d hd).mono hsub⟩
  | conv _ => exact ⟨st₁, hst, fun d hd => (hall d hd).mono hsub⟩
  | seq a b =>
    simp only [certStrategies, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl
    · exact ⟨[(seqLeft ⟨lb, .seq a b, rb⟩ a, false), (seqRight ⟨lb, .seq a b, rb⟩ b, false)],
        by simp [certStrategies], fun d hd => (hall d hd).mono hsub⟩
    · exact ⟨(seqLeft ⟨lb, .seq a b, rb⟩ a, true) ::
          (maxima (certCover C (seqLeft ⟨lb, .seq a b, rb⟩ a))).map fun x =>
            (seqPushL ⟨lb, .seq a b, rb⟩ b x, false), by simp [certStrategies],
        push _ (seqPushL ⟨lb, .seq a b, rb⟩ b)
          (fun x x' hxe => same_mk b (iface_equiv x x' hxe).1 (boundEq_refl rb)) hall⟩
    · exact ⟨(seqRight ⟨lb, .seq a b, rb⟩ b, true) ::
          (maxima (certCover C (seqRight ⟨lb, .seq a b, rb⟩ b))).map fun y =>
            (seqPushR ⟨lb, .seq a b, rb⟩ a y, false), by simp [certStrategies],
        push _ (seqPushR ⟨lb, .seq a b, rb⟩ a)
          (fun x x' hxe => same_mk a (boundEq_refl lb) (iface_equiv x x' hxe).2) hall⟩
  | and a b =>
    simp only [certStrategies, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl
    · exact ⟨[(andLeft ⟨lb, .and a b, rb⟩ a, false), (andRight ⟨lb, .and a b, rb⟩ b, false)],
        by simp [certStrategies], fun d hd => (hall d hd).mono hsub⟩
    · exact ⟨(andLeft ⟨lb, .and a b, rb⟩ a, true) ::
          (maxima (certCover C (andLeft ⟨lb, .and a b, rb⟩ a))).map fun x => (andPush b x, false),
        by simp [certStrategies],
        push _ (andPush b)
          (fun x x' hxe => same_mk b (iface_equiv x x' hxe).2 (iface_equiv x x' hxe).1) hall⟩
    · exact ⟨(andRight ⟨lb, .and a b, rb⟩ b, true) ::
          (maxima (certCover C (andRight ⟨lb, .and a b, rb⟩ b))).map fun y => (andPush a y, false),
        by simp [certStrategies],
        push _ (andPush a)
          (fun x x' hxe => same_mk a (iface_equiv x x' hxe).2 (iface_equiv x x' hxe).1) hall⟩

end Laws

/-! ## Certificates without a root -/

/-- A list of good entries, each with a listed strategy: a certificate but
for naming a root. -/
def Pre (P : Program) (C : List CertEntry) (D : Nat) : Prop :=
  (∀ e ∈ C, GoodE P e) ∧ ∀ e ∈ C, unfoldFinal P D e.goal = true ∨
    ∃ st ∈ certStrategies P C e.goal, ∀ d ∈ st, Listed C e.rank d.1 d.2

theorem pre_nil (P : Program) (D : Nat) : Pre P [] D :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem pre_mono {C : List CertEntry} {D D' : Nat} (h : Pre P C D) (hD : D ≤ D') : Pre P C D' :=
  ⟨h.1, fun e he => (h.2 e he).imp (fun hu => Unf.unfoldFinal_mono P hu _ hD) id⟩

section Laws

variable (hL : SimpLaws P.theory)
include hL

theorem pre_of_valid {C : List CertEntry} {D : Nat} {root : Goal} (hC : Cert.Valid P C D root) :
    Pre P C D :=
  ⟨fun _ he => goodE_of_valid hL hC he, fun e he => (hC.2 e he).2.2.2⟩

theorem pre_append {C₁ C₂ : List CertEntry} {D : Nat} (h₁ : Pre P C₁ D) (h₂ : Pre P C₂ D) :
    Pre P (C₁ ++ C₂) D := by
  have hg : ∀ e ∈ C₁ ++ C₂, GoodE P e := fun e he =>
    (List.mem_append.1 he).elim (h₁.1 e) (h₂.1 e)
  refine ⟨hg, fun e he => ?_⟩
  rcases List.mem_append.1 he with he | he
  · exact (h₁.2 e he).imp id fun ⟨_, hst, hall⟩ =>
      strat_transfer hL (fun _ => List.mem_append_left _) hg hst hall
  · exact (h₂.2 e he).imp id fun ⟨_, hst, hall⟩ =>
      strat_transfer hL (fun _ => List.mem_append_right _) hg hst hall

/-- A rootless certificate that lists a goal's key is a certificate for the
goal. -/
theorem valid_of_pre {C : List CertEntry} {D : Nat} (h : Pre P C D) {root : Goal}
    (hr : ∃ e ∈ C, e.goal.same root.norm.2 = true) : Cert.Valid P C D root := by
  have hI := xinv_certTables hL h.1
  refine ⟨hr, fun e he => ⟨interfaced_of_goodG (h.1 e he).1, (h.1 e he).2.1, fun x hx => ?_,
    h.2 e he⟩⟩
  obtain ⟨s, hder, hsub⟩ := cands_sub hL (ansSub_of hL hI.good hI.sub) (h.1 e he).1 hx
  exact ((h.1 e he).2.2 s hder).cover hsub

end Laws

/-! ## Adding a goal that pushes -/

theorem rank_le_sum : ∀ {C : List CertEntry} {e : CertEntry}, e ∈ C →
    e.rank ≤ (C.map CertEntry.rank).sum
  | a :: C, e, he => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 he with rfl | he
    · omega
    · have := rank_le_sum he; omega

section Laws

variable (hL : SimpLaws P.theory)
include hL

/-- A goal with a push strategy whose side and pushes are listed can be added
to a rootless certificate. -/
theorem pre_push {C' : List CertEntry} {D : Nat} (h : Pre P C' D) {G L : Goal} (hG : GoodG G)
    (push : Span → Goal)
    (hstrat : ∀ C, ((L, true) :: (maxima (certCover C L)).map fun x => (push x, false)) ∈
      certStrategies P C G)
    (hpush : ∀ x x' : Span, x.Equiv x' → (push x).same (push x') = true)
    (hxc : ∀ ts : Tables, XInv P ts → doneOf ts L = true →
      (∀ x ∈ maxima (answersOf ts L), doneOf ts (push x) = true) →
      ∀ s, Derives P G.e s → XC P.theory (produce P D ts G).1 (GDen G s.den))
    (hLl : ∃ e ∈ C', e.goal.same L.norm.2 = true)
    (hpl : ∀ x ∈ maxima (certCover C' L), ∃ e ∈ C', e.goal.same (push x).norm.2 = true) :
    ∃ F ρ, Pre P (C' ++ [⟨G, F, ρ⟩]) D := by
  have hI := xinv_certTables hL h.1
  have hXC := hxc (certTables C') hI (doneOf_certTables hLl) fun x hx =>
    doneOf_certTables (hpl x (by rwa [answersOf_certTables] at hx))
  obtain ⟨F, hF1, hF2⟩ := cover_exists hL hG (produce P D (certTables C') G).1 fun a ha =>
    cands_sub hL (ansSub_of hL hI.good hI.sub) hG ha
  refine ⟨F, (C'.map CertEntry.rank).sum + 1, ?_⟩
  have hgG : GoodE P ⟨G, F, (C'.map CertEntry.rank).sum + 1⟩ :=
    ⟨hG, hF1, fun s hs => (hXC s hs).covers hF2⟩
  have hg : ∀ e ∈ C' ++ [⟨G, F, (C'.map CertEntry.rank).sum + 1⟩], GoodE P e := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact h.1 e he
    · cases List.mem_singleton.1 he; exact hgG
  refine ⟨hg, fun e he => ?_⟩
  rcases List.mem_append.1 he with he | he
  · exact (h.2 e he).imp id fun ⟨_, hst, hall⟩ =>
      strat_transfer hL (fun _ => List.mem_append_left _) hg hst hall
  · cases List.mem_singleton.1 he
    refine .inr ⟨_, hstrat _, fun d hd => ?_⟩
    obtain ⟨eL, heL, hsL⟩ := hLl
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨eL, List.mem_append_left _ heL, hsL, by
        have := rank_le_sum heL
        simp only [ite_true]; omega⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      obtain ⟨x₁, hx₁, hxe⟩ := maxima_transfer hL h.1 hg ⟨eL, heL, hsL⟩
        ⟨eL, List.mem_append_left _ heL, hsL⟩ x hx
      obtain ⟨e', he', hs'⟩ := hpl x₁ hx₁
      have hl : Listed (C' ++ [⟨G, F, (C'.map CertEntry.rank).sum + 1⟩])
          ((C'.map CertEntry.rank).sum + 1) (push x₁) false :=
        ⟨e', List.mem_append_left _ he', hs', by
          have := rank_le_sum he'
          simp only [Bool.false_eq_true, ite_false]; omega⟩
      exact hl.same (hpush x₁ x hxe.symm)

/-- Certificates for finitely many pushes, put together. -/
theorem pre_family (push : Span → Goal) : ∀ l : List Span,
    (∀ x ∈ l, ∃ C D, Cert.Valid P C D (push x)) →
    ∃ C D, Pre P C D ∧ ∀ x ∈ l, ∃ e ∈ C, e.goal.same (push x).norm.2 = true
  | [], _ => ⟨[], 0, pre_nil P 0, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, h => by
    obtain ⟨C₁, D₁, hC₁⟩ := h x List.mem_cons_self
    obtain ⟨C₂, D₂, hp, hl⟩ := pre_family push l fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨C₁ ++ C₂, max D₁ D₂, pre_append hL (pre_mono (pre_of_valid hL hC₁) (le_max_left _ _))
      (pre_mono hp (le_max_right _ _)), fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · obtain ⟨e, he, hs⟩ := hC₁.1
      exact ⟨e, List.mem_append_left _ he, hs⟩
    · obtain ⟨e, he, hs⟩ := hl y hy
      exact ⟨e, List.mem_append_right _ he, hs⟩

/-- A goal with a push strategy has a certificate when its side has one and
the push from every maximal answer of the side's cover has one. -/
theorem push_cert {G L : Goal} (hG : GoodG G) (push : Span → Goal)
    (hstrat : ∀ C, ((L, true) :: (maxima (certCover C L)).map fun x => (push x, false)) ∈
      certStrategies P C G)
    (hpush : ∀ x x' : Span, x.Equiv x' → (push x).same (push x') = true)
    (hxc : ∀ (D : Nat) (ts : Tables), XInv P ts → doneOf ts L = true →
      (∀ x ∈ maxima (answersOf ts L), doneOf ts (push x) = true) →
      ∀ s, Derives P G.e s → XC P.theory (produce P D ts G).1 (GDen G s.den))
    {CL : List CertEntry} {DL : Nat} (hCL : Cert.Valid P CL DL L)
    (hx : ∀ x ∈ maxima (certCover CL L), ∃ C D, Cert.Valid P C D (push x)) :
    ∃ C D, ∀ root : Goal, G.same root.norm.2 = true → Cert.Valid P C D root := by
  obtain ⟨Cf, Df, hpf, hlf⟩ := pre_family hL push _ hx
  have hpL := pre_of_valid hL hCL
  have hpre : Pre P (CL ++ Cf) (max DL Df) :=
    pre_append hL (pre_mono hpL (le_max_left _ _)) (pre_mono hpf (le_max_right _ _))
  have hLl : ∃ e ∈ CL ++ Cf, e.goal.same L.norm.2 = true :=
    let ⟨e, he, hs⟩ := hCL.1; ⟨e, List.mem_append_left _ he, hs⟩
  have hpl : ∀ x ∈ maxima (certCover (CL ++ Cf) L),
      ∃ e ∈ CL ++ Cf, e.goal.same (push x).norm.2 = true := by
    intro x hx'
    obtain ⟨x₁, hx₁, hxe⟩ := maxima_transfer hL hpL.1 hpre.1 hCL.1 hLl x hx'
    obtain ⟨e, he, hs⟩ := hlf x₁ hx₁
    exact ⟨e, List.mem_append_right _ he,
      Goal.same_trans hs (Symmetry.norm_same (hpush x₁ x hxe.symm)).2⟩
  obtain ⟨F, ρ, hfin⟩ := pre_push hL hpre hG push hstrat hpush (hxc _) hLl hpl
  exact ⟨_, _, fun root hr => valid_of_pre hL hfin
    ⟨⟨G, F, ρ⟩, List.mem_append_right _ (List.mem_singleton_self _), hr⟩⟩

end Laws

/-! ## A certificate's root cover and the answers of the run -/

/-- Every maximal answer of the cover a certificate gives a query is
equivalent to an answer the machine emits. -/
theorem cover_answers (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {q : Rel} {C : List CertEntry}
    {D : Nat} (hC : Cert.Valid P C D ⟨none, q, none⟩) :
    ∀ x ∈ maxima (certCover C ⟨none, q, none⟩), ∃ x' ∈ runtime.Answers P q, x.Equiv x' := by
  have hL := simpLaws_of_wf hwf
  have hroot := goodG_root q
  obtain ⟨n, hn⟩ := (goalTerminates_iff P _).1 (halts_of_cert hwf hroot hC)
  obtain ⟨k, h2⟩ : ∃ k, stateAfter (State.ofGoal P ⟨none, q, none⟩) n =
      iter (State.ofGoal P ⟨none, q, none⟩) k := by
    rcases stateAfter_cases (State.ofGoal P ⟨none, q, none⟩) n with ⟨k, -, -, h⟩ | ⟨-, h⟩
    · exact ⟨k, h⟩
    · exact ⟨n, h⟩
  rw [h2] at hn
  have hne0 : (State.ofGoal P ⟨none, q, none⟩).tables ≠ [] := by simp [State.ofGoal]
  have hne := iter_ne_nil hne0 k
  have h0lt : 0 < (iter (State.ofGoal P ⟨none, q, none⟩) k).tables.length :=
    List.length_pos_iff.2 hne
  have hd0 : (iter (State.ofGoal P ⟨none, q, none⟩) k).tables[0].done = true := by
    simpa [State.finished, List.head?_eq_getElem?, List.getElem?_eq_getElem h0lt] using hn
  obtain ⟨e, he, hs, hcc⟩ := certCover_spec hC.1
  have hm : indexOf (iter (State.ofGoal P ⟨none, q, none⟩) k).tables e.goal = some 0 :=
    indexOf_iter _ (Nat.zero_le k) (show indexOf (State.ofGoal P ⟨none, q, none⟩).tables e.goal = some 0 by
      simp [State.ofGoal, indexOf, Goal.same_symm hs])
  have hIk := xinv_iter (st := State.ofGoal P ⟨none, q, none⟩) hL (xinv_ofGoal hroot) k
  intro x hx
  rw [hcc] at hx
  obtain ⟨y, hy, hxy⟩ := maxima_equiv
    (orient_cover (matched_cov_done hL hC hIk he hm h0lt hd0))
    (orient_cover (matched_cov hL hC hIk he hm h0lt)) hx
  refine ⟨y, ⟨n, ?_⟩, hxy⟩
  show y ∈ (runtime.run (State.ofGoal P ⟨none, q, none⟩) n).1
  rw [(run_root n _ hne0).1, h2]
  have hra : rootAns (iter (State.ofGoal P ⟨none, q, none⟩) k) =
      (iter (State.ofGoal P ⟨none, q, none⟩) k).tables[0].answers := by
    simp [rootAns, List.head?_eq_getElem?, List.getElem?_eq_getElem h0lt]
  rw [hra]
  simpa [rootAns, State.ofGoal] using maxima_sub hy

/-! ## The four push strategies -/

theorem norm_canon (lb rb : Option Span) (e : Rel) :
    (⟨lb, canon e, rb⟩ : Goal).norm = (⟨lb, e, rb⟩ : Goal).norm := by
  simp [Goal.norm, Symmetry.canon_idem]

theorem certCover_norm (C : List CertEntry) {g h : Goal} (e : g.norm = h.norm) :
    certCover C g = certCover C h := by
  simp [certCover, e]

/-- A certificate only depends on the root's table key. -/
theorem valid_root {C : List CertEntry} {D : Nat} {r r' : Goal} (h : Cert.Valid P C D r)
    (hs : r.norm.2.same r'.norm.2 = true) : Cert.Valid P C D r' :=
  ⟨let ⟨e, he, h1⟩ := h.1; ⟨e, he, Goal.same_trans h1 hs⟩, h.2⟩

theorem valid_root_eq {C : List CertEntry} {D : Nat} {r r' : Goal} (h : Cert.Valid P C D r)
    (hs : r.norm = r'.norm) : Cert.Valid P C D r' :=
  valid_root h (by rw [hs]; exact Goal.same_refl _)

theorem norm_seq_root (lb rb : Option Span) (a b : Rel) :
    (⟨lb, .seq a b, rb⟩ : Goal).norm.2 = ⟨lb, .seq (canon a) (canon b), rb⟩ := by
  simp only [Goal.norm, canon]
  rw [strip_nc _ (by simp)]

theorem norm_and_root (a b : Rel) :
    (⟨none, .and a b, none⟩ : Goal).norm.2 = ⟨none, .and (canon a) (canon b), none⟩ := by
  simp only [Goal.norm, canon]
  rw [strip_nc _ (by simp)]

section Laws

variable (hL : SimpLaws P.theory)
include hL

/-- `lb ; (a ; b) ; rb` has a certificate when `lb ; a` has one and `b ; rb`
has one under the interface of each maximal answer of that cover. -/
theorem seqL_cert {lb rb : Option Span} {a b : Rel} (hg : GoodG ⟨lb, .seq a b, rb⟩)
    {CL : List CertEntry} {DL : Nat} (hCL : Cert.Valid P CL DL ⟨lb, a, none⟩)
    (hx : ∀ x ∈ maxima (certCover CL ⟨lb, a, none⟩),
      ∃ C D, Cert.Valid P C D ⟨bound x.rightIface, b, rb⟩) :
    ∃ C D, Cert.Valid P C D ⟨lb, .seq a b, rb⟩ := by
  have hG : GoodG ⟨lb, .seq (canon a) (canon b), rb⟩ := hg
  have hgL : GoodG ⟨lb, canon a, none⟩ := ⟨hg.1, trivial⟩
  obtain ⟨C, D, h⟩ := push_cert hL (G := ⟨lb, .seq (canon a) (canon b), rb⟩)
    (L := ⟨lb, canon a, none⟩) hG (seqPushL ⟨lb, .seq (canon a) (canon b), rb⟩ (canon b))
    (fun C => by simp [certStrategies, seqLeft])
    (fun x x' hxe => same_mk _ (iface_equiv x x' hxe).1 (boundEq_refl rb))
    (fun D ts hI hd hp s hs => by
      obtain ⟨w, hw⟩ := dw_of_derives hs
      cases hw with
      | seq hw₁ hw₂ hc =>
        rw [compose_some hc]
        exact xc_seq_pushL hL hd (xc_done hL hI hgL hd hw₁.derives) fun x hx =>
          xc_done hL hI (goodG_pushL hG _ x) (hp x hx) hw₂.derives)
    (valid_root_eq hCL (norm_canon _ _ _).symm)
    (fun x hx' => by
      rw [certCover_norm CL (norm_canon lb none a)] at hx'
      obtain ⟨C, D, hC⟩ := hx x hx'
      exact ⟨C, D, valid_root_eq hC (norm_canon _ _ _).symm⟩)
  exact ⟨C, D, h _ (by rw [norm_seq_root]; exact Goal.same_refl _)⟩

/-- The mirror image: `lb ; (a ; b) ; rb` has a certificate when `b ; rb` has
one and `lb ; a` has one under the interface of each maximal answer of that
cover. -/
theorem seqR_cert {lb rb : Option Span} {a b : Rel} (hg : GoodG ⟨lb, .seq a b, rb⟩)
    {CL : List CertEntry} {DL : Nat} (hCL : Cert.Valid P CL DL ⟨none, b, rb⟩)
    (hx : ∀ y ∈ maxima (certCover CL ⟨none, b, rb⟩),
      ∃ C D, Cert.Valid P C D ⟨lb, a, bound y.leftIface⟩) :
    ∃ C D, Cert.Valid P C D ⟨lb, .seq a b, rb⟩ := by
  have hG : GoodG ⟨lb, .seq (canon a) (canon b), rb⟩ := hg
  have hgR : GoodG ⟨none, canon b, rb⟩ := ⟨trivial, hg.2⟩
  obtain ⟨C, D, h⟩ := push_cert hL (G := ⟨lb, .seq (canon a) (canon b), rb⟩)
    (L := ⟨none, canon b, rb⟩) hG (seqPushR ⟨lb, .seq (canon a) (canon b), rb⟩ (canon a))
    (fun C => by simp [certStrategies, seqRight])
    (fun x x' hxe => same_mk _ (boundEq_refl lb) (iface_equiv x x' hxe).2)
    (fun D ts hI hd hp s hs => by
      obtain ⟨w, hw⟩ := dw_of_derives hs
      cases hw with
      | seq hw₁ hw₂ hc =>
        rw [compose_some hc]
        exact xc_seq_pushR hL hd (xc_done hL hI hgR hd hw₂.derives) fun y hy =>
          xc_done hL hI (goodG_pushR hG _ y) (hp y hy) hw₁.derives)
    (valid_root_eq hCL (norm_canon _ _ _).symm)
    (fun y hy' => by
      rw [certCover_norm CL (norm_canon none rb b)] at hy'
      obtain ⟨C, D, hC⟩ := hx y hy'
      exact ⟨C, D, valid_root_eq hC (norm_canon _ _ _).symm⟩)
  exact ⟨C, D, h _ (by rw [norm_seq_root]; exact Goal.same_refl _)⟩

/-- `a & b` has a certificate when `a` has one and `b` has one restricted to
each maximal answer of `a`'s cover. -/
theorem andL_cert {a b : Rel} {CL : List CertEntry} {DL : Nat}
    (hCL : Cert.Valid P CL DL ⟨none, a, none⟩)
    (hx : ∀ x ∈ maxima (certCover CL ⟨none, a, none⟩), ∃ C D, Cert.Valid P C D (andPush b x)) :
    ∃ C D, Cert.Valid P C D ⟨none, .and a b, none⟩ := by
  have hG : GoodG ⟨none, .and (canon a) (canon b), none⟩ := goodG_root _
  obtain ⟨C, D, h⟩ := push_cert hL (G := ⟨none, .and (canon a) (canon b), none⟩)
    (L := ⟨none, canon a, none⟩) hG (andPush (canon b))
    (fun C => by simp [certStrategies, andLeft])
    (fun x x' hxe => same_mk _ (iface_equiv x x' hxe).2 (iface_equiv x x' hxe).1)
    (fun D ts hI hd hp s hs => by
      obtain ⟨w, hw⟩ := dw_of_derives hs
      cases hw with
      | and hw₁ hw₂ hc =>
        rw [meet_some hc]
        exact xc_and_pushL hL (goodG_root .zero) hd (xc_done hL hI (goodG_root _) hd hw₁.derives)
          fun x hx => xc_done hL hI (goodG_andPush _ x) (hp x hx) hw₂.derives)
    (valid_root_eq hCL (norm_canon _ _ _).symm)
    (fun x hx' => by
      rw [certCover_norm CL (norm_canon none none a)] at hx'
      obtain ⟨C, D, hC⟩ := hx x hx'
      exact ⟨C, D, valid_root_eq hC (norm_canon _ _ _).symm⟩)
  exact ⟨C, D, h _ (by rw [norm_and_root]; exact Goal.same_refl _)⟩

/-- The mirror image: `b & a` has a certificate when `a` has one and `b` has
one restricted to each maximal answer of `a`'s cover. -/
theorem andR_cert {a b : Rel} {CL : List CertEntry} {DL : Nat}
    (hCL : Cert.Valid P CL DL ⟨none, a, none⟩)
    (hx : ∀ x ∈ maxima (certCover CL ⟨none, a, none⟩), ∃ C D, Cert.Valid P C D (andPush b x)) :
    ∃ C D, Cert.Valid P C D ⟨none, .and b a, none⟩ := by
  have hG : GoodG ⟨none, .and (canon b) (canon a), none⟩ := goodG_root _
  obtain ⟨C, D, h⟩ := push_cert hL (G := ⟨none, .and (canon b) (canon a), none⟩)
    (L := ⟨none, canon a, none⟩) hG (andPush (canon b))
    (fun C => by simp [certStrategies, andRight])
    (fun x x' hxe => same_mk _ (iface_equiv x x' hxe).2 (iface_equiv x x' hxe).1)
    (fun D ts hI hd hp s hs => by
      obtain ⟨w, hw⟩ := dw_of_derives hs
      cases hw with
      | and hw₁ hw₂ hc =>
        rw [meet_some hc]
        exact xc_and_pushR hL (goodG_root .zero) hd (xc_done hL hI (goodG_root _) hd hw₂.derives)
          fun y hy => xc_done hL hI (goodG_andPush _ y) (hp y hy) hw₁.derives)
    (valid_root_eq hCL (norm_canon _ _ _).symm)
    (fun x hx' => by
      rw [certCover_norm CL (norm_canon none none a)] at hx'
      obtain ⟨C, D, hC⟩ := hx x hx'
      exact ⟨C, D, valid_root_eq hC (norm_canon _ _ _).symm⟩)
  exact ⟨C, D, h _ (by rw [norm_and_root]; exact Goal.same_refl _)⟩

end Laws

/-- Certificates for the pushes from a cover's maximal answers, from halting
on the pushes from the emitted answers. -/
theorem certs_of_answers (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {a : Rel} {CL : List CertEntry}
    {DL : Nat} (hCL : Cert.Valid P CL DL ⟨none, a, none⟩) (push : Span → Goal)
    (hpush : ∀ x x' : Span, x.Equiv x' → (push x).same (push x') = true)
    (hgood : ∀ x, GoodG (push x))
    (h : ∀ x ∈ runtime.Answers P a, GoalTerminates P (push x)) :
    ∀ x ∈ maxima (certCover CL ⟨none, a, none⟩), ∃ C D, Cert.Valid P C D (push x) := by
  intro x hx
  obtain ⟨x', hx', hxe⟩ := cover_answers hwf hCL x hx
  obtain ⟨C, D, hC⟩ := cert_of_halts hwf (hgood x') (h x' hx')
  exact ⟨C, D, valid_root hC (Symmetry.norm_same (hpush x' x hxe.symm)).2⟩

end Combine

end R001

end RwLog
