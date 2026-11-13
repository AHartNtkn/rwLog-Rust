/-
# Rung R001: a halting run yields a certificate

When the root completes, the complete tables are a certificate. Each lists its
goal, derivable answers covering the table's answers (`coverOf`), and the
round in which it completed as its rank (`rk`). A table completed through a
strategy whose goals had tables that were complete or completed in the same
round, so their ranks are no higher, and a side a push waited on was complete
before, so its rank is lower. The covers are closed because a complete table
covers everything its goal derives.
-/
import RwLog.Rungs.R001.Proofs.CertHalts

namespace RwLog

namespace R001

namespace CertOfHalt

open Tier0 Exact CertHalts

/-! ## When a table completes -/

/-- Table `i` is complete after `k` rounds. -/
def doneAt (st : State) (k i : Nat) : Bool := ((iter st k).tables.getD i noTable).done

theorem doneAt_lt {st : State} {k i : Nat} (h : doneAt st k i = true) :
    i < (iter st k).tables.length := by
  by_contra hn
  simp [doneAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h

theorem doneAt_eq {st : State} {k i : Nat} (hi : i < (iter st k).tables.length) :
    doneAt st k i = (iter st k).tables[i].done := by
  simp [doneAt, List.getD_eq_getElem?_getD, hi]

theorem doneAt_mono {st : State} {k k' i : Nat} (hk : k ≤ k') (h : doneAt st k i = true) :
    doneAt st k' i = true := by
  have hi := doneAt_lt h
  obtain ⟨hi', hext⟩ := iter_ext_le st hk i hi
  rw [doneAt_eq hi']
  exact hext.2.2 (by rwa [doneAt_eq hi] at h)

open Classical in
/-- The round after which table `i` is complete. -/
noncomputable def rk (st : State) (i : Nat) : Nat :=
  if h : ∃ k, doneAt st k i = true then Nat.find h else 0

theorem rk_le {st : State} {k i : Nat} (h : doneAt st k i = true) : rk st i ≤ k := by
  have hex : ∃ k, doneAt st k i = true := ⟨k, h⟩
  unfold rk
  simp only [hex, ↓reduceDIte]
  exact Nat.find_min' hex h

theorem lt_rk {st : State} {k k' i : Nat} (h : doneAt st k i = false)
    (h' : doneAt st k' i = true) : k < rk st i := by
  have hex : ∃ k, doneAt st k i = true := ⟨k', h'⟩
  by_contra hn
  have hs : doneAt st (rk st i) i = true := by
    unfold rk
    simp only [hex, ↓reduceDIte]
    exact Nat.find_spec hex
  rw [doneAt_mono (Nat.le_of_not_gt hn) hs] at h
  cases h

/-- A table complete after `K` rounds completed in one of them. -/
theorem first_compl {st : State} {i : Nat} (h0 : doneAt st 0 i = false) :
    ∀ K, doneAt st K i = true → ∃ k < K, doneAt st k i = false ∧ i ∈ compl (iter st k)
  | 0, h => by rw [h0] at h; cases h
  | K + 1, h => by
    cases hK : doneAt st K i with
    | true =>
      obtain ⟨k, hk, r⟩ := first_compl h0 K hK
      exact ⟨k, by omega, r⟩
    | false =>
      refine ⟨K, Nat.lt_succ_self _, hK, ?_⟩
      have hi' := doneAt_lt h
      by_cases hi : i < (iter st K).tables.length
      · obtain ⟨_, he⟩ := iter_getElem_succ st K i hi
        rw [doneAt_eq hi', he, after_done, ← doneAt_eq hi, hK] at h
        simpa using h
      · exfalso
        obtain ⟨t, ht, htd⟩ : ∃ t, (iter st (K + 1)).tables[i]? = some t ∧ t.done = true :=
          ⟨_, List.getElem?_eq_getElem hi', by rwa [doneAt_eq hi'] at h⟩
        rw [show (iter st (K + 1)).tables = _ from round_tables (iter st K),
          List.getElem?_append_right (by simpa using Nat.le_of_not_lt hi), List.getElem?_map] at ht
        cases hg : (newGoalsOf (iter st K))[i - (List.mapIdx (after (iter st K)) (iter st K).tables).length]? with
        | none => rw [hg] at ht; cases ht
        | some g => rw [hg] at ht; cases ht; cases htd

/-! ## Covers -/

section Cover

variable {P : Program} (hL : SimpLaws P.theory)
include hL

theorem cover_exists {g : Goal} (hg : GoodG g) : ∀ l : List Span,
    (∀ a ∈ l, ∃ s, Derives P g.e s ∧ Under P.theory (GDen g s.den) a) →
    ∃ F : List Span, (∀ f ∈ F, GDerives P g f) ∧ ∀ a ∈ l, ∃ f ∈ F, f.Covers a
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, h => by
    obtain ⟨F, hF1, hF2⟩ := cover_exists hg l fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨s, hs, hsub⟩ := h a List.mem_cons_self
    obtain ⟨y, hy, hya⟩ := realise_sub hL hg hs hsub
    refine ⟨y :: F, fun f hf => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hf with rfl | hf
      · exact hy
      · exact hF1 f hf
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨y, List.mem_cons_self, hya⟩
      · obtain ⟨f, hf, hfx⟩ := hF2 x hx
        exact ⟨f, List.mem_cons_of_mem _ hf, hfx⟩

omit hL in
open Classical in
/-- Derivable answers covering a table's answers. -/
noncomputable def coverOf (P : Program) (t : Table) : List Span :=
  if h : ∃ F : List Span, (∀ f ∈ F, GDerives P t.goal f) ∧ ∀ a ∈ t.answers, ∃ f ∈ F, f.Covers a
  then Classical.choose h else []

theorem coverOf_spec {ts : Tables} (hI : XInv P ts) {t : Table} (ht : t ∈ ts) :
    (∀ f ∈ coverOf P t, GDerives P t.goal f) ∧ ∀ a ∈ t.answers, ∃ f ∈ coverOf P t, f.Covers a := by
  have hex := cover_exists hL (hI.good t ht) t.answers (hI.sub t ht)
  unfold coverOf
  simp only [hex, ↓reduceDIte]
  exact Classical.choose_spec hex

omit hL in
/-- A complete table covers the answers of any table with an equal goal. -/
theorem done_mutual {ts ts' : Tables} (hI : XInv P ts) (hI' : XInv P ts') {t t' : Table}
    (ht : t ∈ ts) (ht' : t' ∈ ts') (hd : t.done = true) (hs : t.goal.same t'.goal = true) :
    ∀ a' ∈ t'.answers, ∃ a ∈ t.answers, a.Covers a' := by
  intro a' ha'
  obtain ⟨s, hder, hsub⟩ := hI'.sub t' ht' a' ha'
  rw [← same_e hs] at hder
  rw [← same_gden hs (hI.good t ht) (hI'.good t' ht')] at hsub
  exact (hI.comp t ht hd s hder).cover hsub

/-- A complete table covers its cover. -/
theorem coverOf_back {ts : Tables} (hI : XInv P ts) {t : Table} (ht : t ∈ ts) (hd : t.done = true) :
    ∀ f ∈ coverOf P t, ∃ a ∈ t.answers, a.Covers f := by
  intro f hf
  obtain ⟨s, hder, hsub⟩ := gderives_sub hL ((coverOf_spec hL hI ht).1 f hf) (hI.good t ht)
  exact (hI.comp t ht hd s hder).cover hsub

end Cover

/-! ## The machine's strategy is one the certificate allows -/

/-- `d` is listed in `C`, with rank below `ρ` if `fl` and at most `ρ`
otherwise. -/
def Listed (C : List CertEntry) (ρ : Nat) (d : Goal) (fl : Bool) : Prop :=
  ∃ e' ∈ C, e'.goal.same d.norm.2 = true ∧ (if fl then e'.rank < ρ else e'.rank ≤ ρ)

theorem Listed.same {C : List CertEntry} {ρ : Nat} {d d' : Goal} {fl : Bool}
    (h : Listed C ρ d fl) (hs : d.same d' = true) : Listed C ρ d' fl := by
  obtain ⟨e', he', h1, h2⟩ := h
  exact ⟨e', he', Goal.same_trans h1 (Symmetry.norm_same hs).2, h2⟩

theorem strat_cert {P : Program} {C : List CertEntry} (ts : Tables) (ρ : Nat) (g : Goal)
    (M : Goal → Prop) (hf : ∀ d, M d → Listed C ρ d false)
    (ht : ∀ d, M d → doneOf ts d = true → Listed C ρ d true)
    (hmax : ∀ L, doneOf ts L = true → ∀ x ∈ maxima (certCover C L),
      ∃ x' ∈ maxima (answersOf ts L), x.Equiv x')
    {deps : List Goal} (hdeps : deps ∈ strategies.tableStrategies P ts g)
    (hall : ∀ d ∈ deps, M d) :
    ∃ st ∈ certStrategies P C g, ∀ d ∈ st, Listed C ρ d.1 d.2 := by
  obtain ⟨lb, ex, rb⟩ := g
  cases ex with
  | zero => exact ⟨[], by simp [certStrategies], by simp⟩
  | span _ => exact ⟨[], by simp [certStrategies], by simp⟩
  | or a b =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    refine ⟨(orLeaves ⟨lb, .or a b, rb⟩ a b).map fun h => (h, false), by simp [certStrategies], ?_⟩
    rintro ⟨d, fl⟩ hd
    obtain ⟨h, hh, heq⟩ := List.mem_map.1 hd
    cases heq
    exact hf _ (hall _ hh)
  | call n =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    refine ⟨[(callGoal P ⟨lb, .call n, rb⟩ n, false)], by simp [certStrategies], ?_⟩
    rintro ⟨d, fl⟩ hd
    cases List.mem_singleton.1 hd
    exact hf _ (hall _ (List.mem_singleton_self _))
  | conv a =>
    simp only [strategies.tableStrategies, List.mem_singleton] at hdeps
    subst hdeps
    refine ⟨[(convGoal ⟨lb, .conv a, rb⟩ a, false)], by simp [certStrategies], ?_⟩
    rintro ⟨d, fl⟩ hd
    cases List.mem_singleton.1 hd
    exact hf _ (hall _ (List.mem_singleton_self _))
  | seq a b =>
    simp only [strategies.tableStrategies, List.mem_append, List.mem_singleton] at hdeps
    rcases hdeps with (rfl | hd) | hd
    · refine ⟨[(seqLeft ⟨lb, .seq a b, rb⟩ a, false), (seqRight ⟨lb, .seq a b, rb⟩ b, false)],
        by simp [certStrategies], ?_⟩
      rintro ⟨d, fl⟩ hd
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hd
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hf _ (hall _ (by simp))
      · exact hf _ (hall _ (by simp))
    · by_cases hdn : doneOf ts (seqLeft ⟨lb, .seq a b, rb⟩ a) = true
      · simp only [hdn, ite_true, List.mem_singleton] at hd
        subst hd
        refine ⟨(seqLeft ⟨lb, .seq a b, rb⟩ a, true) ::
          (maxima (certCover C (seqLeft ⟨lb, .seq a b, rb⟩ a))).map fun x =>
            (seqPushL ⟨lb, .seq a b, rb⟩ b x, false), by simp [certStrategies], ?_⟩
        rintro ⟨d, fl⟩ hd
        rcases List.mem_cons.1 hd with heq | hd
        · cases heq
          exact ht _ (hall _ List.mem_cons_self) hdn
        · obtain ⟨x, hx, heq⟩ := List.mem_map.1 hd
          cases heq
          obtain ⟨x', hx', hxe⟩ := hmax _ hdn x hx
          exact (hf _ (hall _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x', hx', rfl⟩)))).same
            (same_mk b (iface_equiv x' x hxe.symm).1 (boundEq_refl rb))
      · simp [hdn] at hd
    · by_cases hdn : doneOf ts (seqRight ⟨lb, .seq a b, rb⟩ b) = true
      · simp only [hdn, ite_true, List.mem_singleton] at hd
        subst hd
        refine ⟨(seqRight ⟨lb, .seq a b, rb⟩ b, true) ::
          (maxima (certCover C (seqRight ⟨lb, .seq a b, rb⟩ b))).map fun y =>
            (seqPushR ⟨lb, .seq a b, rb⟩ a y, false), by simp [certStrategies], ?_⟩
        rintro ⟨d, fl⟩ hd
        rcases List.mem_cons.1 hd with heq | hd
        · cases heq
          exact ht _ (hall _ List.mem_cons_self) hdn
        · obtain ⟨x, hx, heq⟩ := List.mem_map.1 hd
          cases heq
          obtain ⟨x', hx', hxe⟩ := hmax _ hdn x hx
          exact (hf _ (hall _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x', hx', rfl⟩)))).same
            (same_mk a (boundEq_refl lb) (iface_equiv x' x hxe.symm).2)
      · simp [hdn] at hd
  | and a b =>
    simp only [strategies.tableStrategies, List.mem_append, List.mem_singleton] at hdeps
    rcases hdeps with (rfl | hd) | hd
    · refine ⟨[(andLeft ⟨lb, .and a b, rb⟩ a, false), (andRight ⟨lb, .and a b, rb⟩ b, false)],
        by simp [certStrategies], ?_⟩
      rintro ⟨d, fl⟩ hd
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hd
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hf _ (hall _ (by simp))
      · exact hf _ (hall _ (by simp))
    · by_cases hdn : doneOf ts (andLeft ⟨lb, .and a b, rb⟩ a) = true
      · simp only [hdn, ite_true, List.mem_singleton] at hd
        subst hd
        refine ⟨(andLeft ⟨lb, .and a b, rb⟩ a, true) ::
          (maxima (certCover C (andLeft ⟨lb, .and a b, rb⟩ a))).map fun x =>
            (andPush b x, false), by simp [certStrategies], ?_⟩
        rintro ⟨d, fl⟩ hd
        rcases List.mem_cons.1 hd with heq | hd
        · cases heq
          exact ht _ (hall _ List.mem_cons_self) hdn
        · obtain ⟨x, hx, heq⟩ := List.mem_map.1 hd
          cases heq
          obtain ⟨x', hx', hxe⟩ := hmax _ hdn x hx
          exact (hf _ (hall _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x', hx', rfl⟩)))).same
            (same_mk b (iface_equiv x' x hxe.symm).2 (iface_equiv x' x hxe.symm).1)
      · simp [hdn] at hd
    · by_cases hdn : doneOf ts (andRight ⟨lb, .and a b, rb⟩ b) = true
      · simp only [hdn, ite_true, List.mem_singleton] at hd
        subst hd
        refine ⟨(andRight ⟨lb, .and a b, rb⟩ b, true) ::
          (maxima (certCover C (andRight ⟨lb, .and a b, rb⟩ b))).map fun y =>
            (andPush a y, false), by simp [certStrategies], ?_⟩
        rintro ⟨d, fl⟩ hd
        rcases List.mem_cons.1 hd with heq | hd
        · cases heq
          exact ht _ (hall _ List.mem_cons_self) hdn
        · obtain ⟨x, hx, heq⟩ := List.mem_map.1 hd
          cases heq
          obtain ⟨x', hx', hxe⟩ := hmax _ hdn x hx
          exact (hf _ (hall _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x', hx', rfl⟩)))).same
            (same_mk a (iface_equiv x' x hxe.symm).2 (iface_equiv x' x hxe.symm).1)
      · simp [hdn] at hd

/-! ## The certificate of a run -/

/-- The complete tables after `K` rounds, as certificate entries. -/
noncomputable def certOf (st : State) (K : Nat) : List CertEntry :=
  (List.range (iter st K).tables.length).filterMap fun i =>
    if ((iter st K).tables.getD i noTable).done then
      some ⟨((iter st K).tables.getD i noTable).goal,
        coverOf st.P ((iter st K).tables.getD i noTable), rk st i⟩
    else none

theorem mem_certOf {st : State} {K : Nat} {e : CertEntry} :
    e ∈ certOf st K ↔ ∃ i, ∃ hi : i < (iter st K).tables.length,
      (iter st K).tables[i].done = true ∧
      e = ⟨(iter st K).tables[i].goal, coverOf st.P (iter st K).tables[i], rk st i⟩ := by
  simp only [certOf, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
    split at h
    · rename_i hd
      exact ⟨i, hi, hd, (Option.some.inj h).symm⟩
    · cases h
  · rintro ⟨i, hi, hd, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hd]

theorem interfaced_of_goodG {g : Goal} (h : GoodG g) : g.Interfaced := by
  obtain ⟨lb, e, rb⟩ := g
  obtain ⟨h1, h2⟩ := h
  intro b hb
  cases lb with
  | none =>
    cases rb with
    | none => simp at hb
    | some r =>
      obtain rfl : b = r := by simpa using hb
      exact h2
  | some l =>
    cases rb with
    | none =>
      obtain rfl : b = l := by simpa using hb
      exact h1
    | some r =>
      have : b = l ∨ b = r := by simpa using hb
      rcases this with rfl | rfl
      · exact h1
      · exact h2

theorem compl_done {st : State} {k j : Nat} (h : j ∈ compl (iter st k)) :
    doneAt st (k + 1) j = true := by
  obtain ⟨hj, -⟩ := mem_compl h
  obtain ⟨hj', he⟩ := iter_getElem_succ st k j hj
  rw [doneAt_eq hj', he, after_done]
  simp [h]

/-- The complete tables of a run are a certificate, apart from listing the
root. -/
theorem cert_valid {st : State} (hL : SimpLaws st.P.theory) (hI : XInv st.P st.tables)
    (h0 : ∀ i, doneAt st 0 i = false) (K : Nat) :
    ∀ e ∈ certOf st K, e.goal.Interfaced ∧ (∀ f ∈ e.cover, GDerives st.P e.goal f) ∧
      (∀ x ∈ (produce st.P (st.depth + K) (certTables (certOf st K)) e.goal).1,
        ∃ f ∈ e.cover, f.Covers x) ∧
      (unfoldFinal st.P (st.depth + K) e.goal = true ∨
        ∃ s ∈ certStrategies st.P (certOf st K) e.goal, ∀ d ∈ s, ∃ e' ∈ certOf st K,
          e'.goal.same d.1.norm.2 = true ∧
            (if d.2 then e'.rank < e.rank else e'.rank ≤ e.rank)) := by
  intro e he
  obtain ⟨i, hi, hd, rfl⟩ := mem_certOf.1 he
  have hIK := xinv_iter hL hI K
  have hti := List.getElem_mem hi
  have hdK : doneAt st K i = true := by rw [doneAt_eq hi]; exact hd
  refine ⟨interfaced_of_goodG (hIK.good _ hti), (coverOf_spec hL hIK hti).1, ?_, ?_⟩
  · intro x hx
    have hA : AnsSub st.P (certTables (certOf st K)) := by
      refine ansSub_of hL ?_ ?_
      · intro t ht
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 ht
        obtain ⟨j, hj, -, rfl⟩ := mem_certOf.1 he'
        exact hIK.good (iter st K).tables[j] (List.getElem_mem hj)
      · intro t ht a ha
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 ht
        obtain ⟨j, hj, -, rfl⟩ := mem_certOf.1 he'
        exact gderives_sub hL ((coverOf_spec hL hIK (List.getElem_mem hj)).1 a ha)
          (hIK.good (iter st K).tables[j] (List.getElem_mem hj))
    obtain ⟨s, hder, hsub⟩ := cands_sub hL hA (hIK.good _ hti) hx
    obtain ⟨a, ha, hax⟩ := (hIK.comp _ hti hd s hder).cover hsub
    obtain ⟨f, hf, hfa⟩ := (coverOf_spec hL hIK hti).2 a ha
    exact ⟨f, hf, hfa.trans hax⟩
  · obtain ⟨k, hkK, hk0, hc⟩ := first_compl (h0 i) K hdK
    obtain ⟨hik, -, -, deps, hdeps, hall⟩ := mem_compl hc
    obtain ⟨_, hext⟩ := iter_ext_le st (Nat.le_of_lt hkK) i hik
    rw [iter_P, iter_depth, ← hext.1] at hdeps
    have hIk := xinv_iter hL hI k
    have hri : k < rk st i := lt_rk hk0 hdK
    -- a goal whose table is complete after `k'` rounds is listed with rank at most `k'`
    have entry : ∀ (d : Goal) (j k' : Nat), indexOf (iter st k).tables d.norm.2 = some j →
        doneAt st k' j = true → k' ≤ K →
        ∃ e' ∈ certOf st K, e'.goal.same d.norm.2 = true ∧ e'.rank ≤ k' := by
      intro d j k' hj hdj hk'
      obtain ⟨hjk, -, hsame⟩ := indexOf_find hj
      have hdjK := doneAt_mono hk' hdj
      have hjK := doneAt_lt hdjK
      obtain ⟨_, hextj⟩ := iter_ext_le st (Nat.le_of_lt hkK) j hjk
      refine ⟨_, mem_certOf.2 ⟨j, hjK, by rwa [← doneAt_eq hjK], rfl⟩, ?_, rk_le hdj⟩
      show (iter st K).tables[j].goal.same d.norm.2 = true
      rw [hextj.1]; exact hsame
    simp only [strategies, List.mem_append] at hdeps
    rcases hdeps with hu | hts
    · left
      split at hu
      · rename_i hfin
        exact Unf.unfoldFinal_mono st.P hfin _ (by omega)
      · cases hu
    · right
      refine strat_cert (iter st k).tables (rk st i) _
        (fun d => ∃ j, indexOf (iter st k).tables d.norm.2 = some j ∧
          (doneAt st k j = true ∨ j ∈ compl (iter st k))) ?_ ?_ ?_ hts ?_
      · rintro d ⟨j, hj, hdc⟩
        have hdj : doneAt st (k + 1) j = true := by
          rcases hdc with h | h
          · exact doneAt_mono (Nat.le_succ k) h
          · exact compl_done h
        obtain ⟨e', he', h1, h2⟩ := entry d j (k + 1) hj hdj (by omega)
        exact ⟨e', he', h1, by simp only [Bool.false_eq_true, ite_false]; omega⟩
      · rintro d ⟨j, hj, -⟩ hdn
        obtain ⟨hjk, -, -⟩ := indexOf_find hj
        rw [doneOf_of_index hj hjk, ← doneAt_eq hjk] at hdn
        obtain ⟨e', he', h1, h2⟩ := entry d j k hj hdn (Nat.le_of_lt hkK)
        exact ⟨e', he', h1, by simp only [ite_true]; omega⟩
      · intro L hdn x hx
        unfold doneOf at hdn
        cases hft : findTable (iter st k).tables L.norm.2 with
        | none => rw [hft] at hdn; cases hdn
        | some t =>
          rw [hft] at hdn
          simp only at hdn
          obtain ⟨j, hj, hjk, rfl⟩ := find_indexOf hft
          obtain ⟨_, -, hsame⟩ := indexOf_find hj
          have htj := List.getElem_mem hjk
          cases hf : (certOf st K).find? (fun e => e.goal.same L.norm.2) with
          | none =>
            have : certCover (certOf st K) L = [] := by simp [certCover, hf]
            rw [this] at hx
            cases hx
          | some e'' =>
            have he'' := List.mem_of_find?_eq_some hf
            have hs'' : e''.goal.same L.norm.2 = true :=
              List.find?_some (p := fun e : CertEntry => e.goal.same L.norm.2) hf
            obtain ⟨j', hj', hd', rfl⟩ := mem_certOf.1 he''
            have htj' := List.getElem_mem hj'
            have hss : (iter st k).tables[j].goal.same (iter st K).tables[j'].goal = true :=
              Goal.same_trans hsame (Goal.same_symm hs'')
            have hcc : certCover (certOf st K) L =
                orient L.norm.1 (coverOf st.P (iter st K).tables[j']) := by
              simp [certCover, hf]
            rw [hcc] at hx
            rw [answersOf_of_index hj hjk]
            refine maxima_equiv (orient_cover fun f hf' => ?_) (orient_cover fun a ha => ?_) hx
            · obtain ⟨a'', ha'', h1⟩ := coverOf_back hL hIK htj' hd' f hf'
              obtain ⟨a, ha, h2⟩ := done_mutual hIk hIK htj htj' hdn hss a'' ha''
              exact ⟨a, ha, h2.trans h1⟩
            · obtain ⟨a'', ha'', h1⟩ := done_mutual hIK hIk htj' htj hd' (Goal.same_symm hss) a ha
              obtain ⟨f, hf', h2⟩ := (coverOf_spec hL hIK htj').2 a'' ha''
              exact ⟨f, hf', h2.trans h1⟩
      · intro d hd
        obtain ⟨j, hj, hjk, -, hdc⟩ := hall d hd
        exact ⟨j, hj, by rw [doneAt_eq hjk]; exact hdc⟩

/-- A goal the machine halts on has a valid certificate. -/
theorem cert_of_halts {P : Program} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {root : Goal}
    (hroot : GoodG root) (h : GoalTerminates P root) : ∃ C D, Cert.Valid P C D root := by
  have hL := simpLaws_of_wf hwf
  rw [goalTerminates_iff, halts_iff_iter] at h
  obtain ⟨K, hK⟩ := h
  have hne := iter_ne_nil (st := State.ofGoal P root) (by simp [State.ofGoal]) K
  have h0lt : 0 < (iter (State.ofGoal P root) K).tables.length := List.length_pos_iff.2 hne
  have hd0 : (iter (State.ofGoal P root) K).tables[0].done = true := by
    simpa [State.finished, List.head?_eq_getElem?, List.getElem?_eq_getElem h0lt] using hK
  have h0 : ∀ i, doneAt (State.ofGoal P root) 0 i = false := by
    intro i
    cases i <;> simp [doneAt, iter, State.ofGoal]
  obtain ⟨_, hext⟩ := iter_ext_le (State.ofGoal P root) (Nat.zero_le K) 0
    (by simp [iter, State.ofGoal])
  refine ⟨certOf (State.ofGoal P root) K, K, ⟨_, mem_certOf.2 ⟨0, h0lt, hd0, rfl⟩, ?_⟩, ?_⟩
  · show (iter (State.ofGoal P root) K).tables[0].goal.same root.norm.2 = true
    rw [hext.1]
    exact Goal.same_refl _
  · have := cert_valid (st := State.ofGoal P root) hL (xinv_ofGoal hroot) h0 K
    simpa [State.ofGoal] using this

end CertOfHalt

end R001

end RwLog
