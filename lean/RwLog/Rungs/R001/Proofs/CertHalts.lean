/-
# Rung R001: a certified query halts

A valid certificate bounds the run. Every table whose goal the certificate
lists holds only answers the listed cover covers (`matched_cov`); the table
comes to cover each member of the cover (`cover_eventually`), and from then
on gains nothing (`no_gain`). Once that has happened to every listed table
that ever exists, the tables listed with rank below `r` complete, by induction
on `r`: the tables of rank `r` that are still open form a set closed under
the completion test, because each has the strategy the certificate names for
it, and that strategy's goals are listed with rank at most `r`, or below `r`
for the side a push waits on (`closed_complete`).
-/
import RwLog.Rungs.R001.Proofs.TerminationBasics
import RwLog.Rungs.R001.Proofs.Exact.Derives
import RwLog.Rungs.R001.Proofs.Exact.Fair
import RwLog.Rungs.R001.Proofs.Unfolding

namespace RwLog

namespace R001

namespace CertHalts

open Tier0 Exact

/-! ## Lists -/

/-- Finitely many things that each hold from some round on hold together
from some round on. -/
theorem ev_all {α : Type} (p : α → Nat → Prop) : ∀ l : List α,
    (∀ x ∈ l, ∃ K, ∀ k ≥ K, p x k) → ∃ K, ∀ x ∈ l, ∀ k ≥ K, p x k
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, h => by
    obtain ⟨K₁, h₁⟩ := h a List.mem_cons_self
    obtain ⟨K₂, h₂⟩ := ev_all p l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨max K₁ K₂, fun x hx k hk => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h₁ k (le_trans (le_max_left _ _) hk)
    · exact h₂ x hx k (le_trans (le_max_right _ _) hk)

/-- A maximum covers whatever covers it. -/
theorem maxima_top {xs : List Span} {y z : Span} (hy : y ∈ maxima xs) (hz : z ∈ xs)
    (h : z.Covers y) : y.Covers z := by
  obtain ⟨-, -, h3, -⟩ := fold_spec (topOf xs) []
  rcases h3 y hy with h' | h'
  · simp at h'
  · have := (List.mem_filter.1 h').2
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.and_eq_true,
      not_and, Bool.not_eq_false] at this
    exact covers?_sound (this z hz (covers?_complete h))

/-- Lists that cover each other have equivalent maxima. -/
theorem maxima_equiv {xs ys : List Span} (h1 : ∀ x ∈ xs, ∃ y ∈ ys, y.Covers x)
    (h2 : ∀ y ∈ ys, ∃ x ∈ xs, x.Covers y) {x : Span} (hx : x ∈ maxima xs) :
    ∃ y ∈ maxima ys, x.Equiv y := by
  obtain ⟨f, hf, hfx⟩ := h1 x (maxima_sub hx)
  obtain ⟨m, hm, hmf⟩ := maxima_cover hf
  obtain ⟨a, ha, ham⟩ := h2 m (maxima_sub hm)
  have hax : a.Covers x := ham.trans (hmf.trans hfx)
  exact ⟨m, hm, (maxima_top hx ha hax).trans ham, hmf.trans hfx⟩

theorem orient_cover {f : Bool} {xs ys : List Span} (h : ∀ x ∈ xs, ∃ y ∈ ys, y.Covers x) :
    ∀ x ∈ orient f xs, ∃ y ∈ orient f ys, y.Covers x := by
  cases f
  · simpa [orient] using h
  · intro x hx
    simp only [orient, ite_true, List.mem_map] at hx ⊢
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y, hy, hyx⟩ := h x₀ hx₀
    exact ⟨_, ⟨y, hy, rfl⟩, covers_swap hyx⟩

/-! ## Table positions of equal keys -/

theorem indexOf_same (ts : Tables) {g h : Goal} (hs : g.same h = true) :
    indexOf ts g = indexOf ts h := by
  unfold indexOf
  congr 1
  funext t
  cases h1 : t.goal.same g with
  | true => exact (Goal.same_trans h1 hs).symm
  | false =>
    cases h2 : t.goal.same h with
    | false => rfl
    | true => rw [Goal.same_trans h2 (Goal.same_symm hs)] at h1; cases h1

theorem iter_depth (st : State) : ∀ k, (iter st k).depth = st.depth + k
  | 0 => rfl
  | k + 1 => by show (iter st k).depth + 1 = _; rw [iter_depth st k]; rfl

theorem doneOf_of_index {ts : Tables} {g : Goal} {j : Nat} (h : indexOf ts g.norm.2 = some j)
    (hj : j < ts.length) : doneOf ts g = ts[j].done := by
  obtain ⟨_, hf, -⟩ := indexOf_find h
  simp [doneOf, hf]

theorem answersOf_of_index {ts : Tables} {g : Goal} {j : Nat} (h : indexOf ts g.norm.2 = some j)
    (hj : j < ts.length) : answersOf ts g = orient g.norm.1 ts[j].answers := by
  obtain ⟨_, hf, -⟩ := indexOf_find h
  simp [answersOf, hf]

/-! ## Listed tables hold what the certificate lists -/

section Matched

variable {P : Program} (hL : SimpLaws P.theory) {C : List CertEntry} {D : Nat} {root : Goal}
  (hC : Cert.Valid P C D root)
include hL hC

/-- Every answer of a listed table is covered by the listed cover. -/
theorem matched_cov {ts : Tables} (hI : XInv P ts) {e : CertEntry} (he : e ∈ C) {j : Nat}
    (hm : indexOf ts e.goal = some j) (hj : j < ts.length) :
    ∀ a ∈ ts[j].answers, ∃ f ∈ e.cover, f.Covers a := by
  intro a ha
  obtain ⟨_, -, hs⟩ := indexOf_find hm
  have ht := List.getElem_mem hj
  obtain ⟨s, hd, hsub⟩ := hI.sub _ ht a ha
  have hge := goodG_of_interfaced (hC.2 e he).1
  rw [same_e hs] at hd
  rw [same_gden hs (hI.good _ ht) hge] at hsub
  exact cert_cover_sub hL hC he hd hsub

/-- A complete listed table covers the listed cover. -/
theorem matched_cov_done {ts : Tables} (hI : XInv P ts) {e : CertEntry} (he : e ∈ C) {j : Nat}
    (hm : indexOf ts e.goal = some j) (hj : j < ts.length) (hd : ts[j].done = true) :
    ∀ f ∈ e.cover, ∃ a ∈ ts[j].answers, a.Covers f := by
  intro f hf
  obtain ⟨_, -, hs⟩ := indexOf_find hm
  have ht := List.getElem_mem hj
  have hge := goodG_of_interfaced (hC.2 e he).1
  obtain ⟨s, hd', hsub⟩ := gderives_sub hL ((hC.2 e he).2.1 f hf) hge
  rw [← same_e hs] at hd'
  rw [← same_gden hs (hI.good _ ht) hge] at hsub
  exact (hI.comp _ ht hd s hd').cover hsub

/-- A listed table that covers the listed cover gains nothing. -/
theorem no_gain {s : State} (hP : s.P = P) (hI : XInv P s.tables) {e : CertEntry} (he : e ∈ C)
    {j : Nat} (hm : indexOf s.tables e.goal = some j) (hj : j < s.tables.length)
    (hcov : ∀ f ∈ e.cover, ∃ a ∈ s.tables[j].answers, a.Covers f) :
    (upd s s.tables[j]).answers.length = s.tables[j].answers.length := by
  subst hP
  have hnil : fresh s.tables[j].answers (outOf s s.tables[j]).1 = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := fresh_sub hy
    cases hdn : s.tables[j].done with
    | true => rw [outOf_done hdn] at hy1; simp at hy1
    | false =>
      rw [outOf_not_done hdn] at hy1
      obtain ⟨_, -, hs⟩ := indexOf_find hm
      have ht := List.getElem_mem hj
      have hge := goodG_of_interfaced (hC.2 e he).1
      obtain ⟨s', hd, hsub⟩ := cands_sub hL (ansSub_of hL hI.good hI.sub) (hI.good _ ht) hy1
      rw [same_e hs] at hd
      rw [same_gden hs (hI.good _ ht) hge] at hsub
      obtain ⟨f, hf, hfy⟩ := cert_cover_sub hL hC he hd hsub
      obtain ⟨a, ha, haf⟩ := hcov f hf
      have := hy2 a ha
      rw [covers?_complete (haf.trans hfy)] at this
      cases this
  simp [upd, hnil]

end Matched

/-! ## The certificate's strategy passes the completion test -/

/-- The completion test of one dependency against a candidate set `X`. -/
def depOK (s : State) (X : List Nat) (g : Goal) : Bool :=
  match indexOf s.tables g.norm.2 with
  | none => false
  | some j => !gainedAt s.tables (s.tables.map (upd s)) j &&
      ((s.tables.getD j noTable).done || X.contains j)

theorem same_mk {lb lb' rb rb' : Option Span} (e : Rel) (hl : boundEq lb lb' = true)
    (hr : boundEq rb rb' = true) : (⟨lb, e, rb⟩ : Goal).same ⟨lb', e, rb'⟩ = true :=
  Goal.same_iff.2 ⟨rfl, hl, hr⟩

/-- A table whose goal equals a listed goal has, among its strategies, the
one the certificate names, provided the goals it reads pass the test when
they are listed with rank at most `ρ`, and are complete and agree with the
listed cover when listed with rank below `ρ`. -/
theorem strat_ok {P : Program} {C : List CertEntry} (s : State) (hP : s.P = P) (X : List Nat)
    (ρ : Nat) {tg eg : Goal} (hs : tg.same eg = true)
    (hdep : ∀ g ∈ (produce s.P s.depth s.tables tg).2, ∀ ge : Goal, g.same ge = true →
      (∃ e' ∈ C, e'.goal.same ge.norm.2 = true ∧ e'.rank ≤ ρ) → depOK s X g = true)
    (hdone : ∀ g ∈ (produce s.P s.depth s.tables tg).2, ∀ ge : Goal, g.same ge = true →
      (∃ e' ∈ C, e'.goal.same ge.norm.2 = true ∧ e'.rank < ρ) → doneOf s.tables g = true ∧
        ∀ x' ∈ maxima (answersOf s.tables g), ∃ x ∈ maxima (certCover C ge), x'.Equiv x)
    (hst : ∃ st ∈ certStrategies P C eg, ∀ d ∈ st, ∃ e' ∈ C, e'.goal.same d.1.norm.2 = true ∧
        (if d.2 then e'.rank < ρ else e'.rank ≤ ρ)) :
    (strategies.tableStrategies s.P s.tables tg).any (fun deps => deps.all (depOK s X)) = true := by
  subst hP
  obtain ⟨lb, ex, rb⟩ := tg
  obtain ⟨lb', ex', rb'⟩ := eg
  obtain ⟨he, hl, hr⟩ := Goal.same_iff.1 hs
  simp only at he hl hr
  subst he
  obtain ⟨st, hst, hall⟩ := hst
  have dep : ∀ (g ge : Goal) (fl : Bool), g ∈ (produce s.P s.depth s.tables ⟨lb, ex, rb⟩).2 →
      g.same ge = true → (ge, fl) ∈ st → depOK s X g = true := by
    intro g ge fl hg hsg hm
    obtain ⟨e', he', h1, h2⟩ := hall _ hm
    refine hdep g hg ge hsg ⟨e', he', h1, ?_⟩
    cases fl
    · simpa using h2
    · exact Nat.le_of_lt (by simpa using h2)
  have dn : ∀ (g ge : Goal), g ∈ (produce s.P s.depth s.tables ⟨lb, ex, rb⟩).2 →
      g.same ge = true → (ge, true) ∈ st → doneOf s.tables g = true ∧
        ∀ x' ∈ maxima (answersOf s.tables g), ∃ x ∈ maxima (certCover C ge), x'.Equiv x := by
    intro g ge hg hsg hm
    obtain ⟨e', he', h1, h2⟩ := hall _ hm
    exact hdone g hg ge hsg ⟨e', he', h1, by simpa using h2⟩
  cases ex with
  | zero => simp [strategies.tableStrategies]
  | span _ => simp [strategies.tableStrategies]
  | or a b =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    simp only [strategies.tableStrategies, List.any_cons, List.any_nil, Bool.or_false,
      List.all_eq_true]
    intro g hg
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg
    exact dep _ ⟨lb', c, rb'⟩ false hg (same_mk c hl hr)
      (List.mem_map.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, rfl⟩)
  | call n =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    simp only [strategies.tableStrategies, List.any_cons, List.any_nil, Bool.or_false,
      List.all_cons, List.all_nil, Bool.and_true]
    exact dep _ (callGoal s.P ⟨lb', .call n, rb'⟩ n) false (by simp [produce, produce.produceStrategies])
      (same_mk _ hl hr) (by simp)
  | conv a =>
    simp only [certStrategies, List.mem_singleton] at hst
    subst hst
    simp only [strategies.tableStrategies, List.any_cons, List.any_nil, Bool.or_false,
      List.all_cons, List.all_nil, Bool.and_true]
    exact dep _ (convGoal ⟨lb', .conv a, rb'⟩ a) false (by simp [produce, produce.produceStrategies])
      (same_mk _ (by rwa [boundEq_swap]) (by rwa [boundEq_swap])) (by simp)
  | seq a b =>
    have hL' : seqLeft ⟨lb, .seq a b, rb⟩ a ∈ (produce s.P s.depth s.tables ⟨lb, .seq a b, rb⟩).2 := by
      simp [produce, produce.produceStrategies]
    have hR' : seqRight ⟨lb, .seq a b, rb⟩ b ∈ (produce s.P s.depth s.tables ⟨lb, .seq a b, rb⟩).2 := by
      simp [produce, produce.produceStrategies]
    have sL : (seqLeft ⟨lb, .seq a b, rb⟩ a).same (seqLeft ⟨lb', .seq a b, rb'⟩ a) = true :=
      same_mk _ hl rfl
    have sR : (seqRight ⟨lb, .seq a b, rb⟩ b).same (seqRight ⟨lb', .seq a b, rb'⟩ b) = true :=
      same_mk _ rfl hr
    simp only [certStrategies, List.mem_cons, List.not_mem_nil, or_false] at hst
    simp only [strategies.tableStrategies]
    rcases hst with rfl | rfl | rfl
    · refine List.any_eq_true.2 ⟨_, List.mem_append_left _ (List.mem_append_left _
        (List.mem_singleton_self _)), ?_⟩
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      exact ⟨dep _ _ false hL' sL (by simp), dep _ _ false hR' sR (by simp)⟩
    · obtain ⟨hdn, hcorr⟩ := dn _ _ hL' sL (by simp)
      refine List.any_eq_true.2 ⟨_, List.mem_append_left _ (List.mem_append_right _
        (by simp only [hdn, ↓reduceIte]; exact List.mem_singleton_self _)), ?_⟩
      simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true]
      refine ⟨dep _ _ true hL' sL (by simp), fun g hg => ?_⟩
      obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hg
      obtain ⟨x, hx, hxe⟩ := hcorr x' hx'
      refine dep _ (seqPushL ⟨lb', .seq a b, rb'⟩ b x) false ?_
        (same_mk _ (iface_equiv _ _ hxe).1 hr) ?_
      · simp only [produce, produce.produceStrategies, hdn, ite_true, List.map_map,
          List.mem_append, List.mem_map]
        exact .inl (.inr ⟨x', hx', rfl⟩)
      · simp only [List.mem_cons, List.mem_map]
        exact .inr ⟨x, hx, rfl⟩
    · obtain ⟨hdn, hcorr⟩ := dn _ _ hR' sR (by simp)
      refine List.any_eq_true.2 ⟨_, List.mem_append_right _
        (by simp only [hdn, ↓reduceIte]; exact List.mem_singleton_self _), ?_⟩
      simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true]
      refine ⟨dep _ _ true hR' sR (by simp), fun g hg => ?_⟩
      obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hg
      obtain ⟨x, hx, hxe⟩ := hcorr x' hx'
      refine dep _ (seqPushR ⟨lb', .seq a b, rb'⟩ a x) false ?_
        (same_mk _ hl (iface_equiv _ _ hxe).2) ?_
      · simp only [produce, produce.produceStrategies, hdn, ite_true, List.map_map,
          List.mem_append, List.mem_map]
        exact .inr ⟨x', hx', rfl⟩
      · simp only [List.mem_cons, List.mem_map]
        exact .inr ⟨x, hx, rfl⟩
  | and a b =>
    have hL' : andLeft ⟨lb, .and a b, rb⟩ a ∈ (produce s.P s.depth s.tables ⟨lb, .and a b, rb⟩).2 := by
      simp [produce, produce.produceStrategies]
    have hR' : andRight ⟨lb, .and a b, rb⟩ b ∈ (produce s.P s.depth s.tables ⟨lb, .and a b, rb⟩).2 := by
      simp [produce, produce.produceStrategies]
    have sL : (andLeft ⟨lb, .and a b, rb⟩ a).same (andLeft ⟨lb', .and a b, rb'⟩ a) = true :=
      same_mk _ hl hr
    have sR : (andRight ⟨lb, .and a b, rb⟩ b).same (andRight ⟨lb', .and a b, rb'⟩ b) = true :=
      same_mk _ hl hr
    simp only [certStrategies, List.mem_cons, List.not_mem_nil, or_false] at hst
    simp only [strategies.tableStrategies]
    rcases hst with rfl | rfl | rfl
    · refine List.any_eq_true.2 ⟨_, List.mem_append_left _ (List.mem_append_left _
        (List.mem_singleton_self _)), ?_⟩
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      exact ⟨dep _ _ false hL' sL (by simp), dep _ _ false hR' sR (by simp)⟩
    · obtain ⟨hdn, hcorr⟩ := dn _ _ hL' sL (by simp)
      refine List.any_eq_true.2 ⟨_, List.mem_append_left _ (List.mem_append_right _
        (by simp only [hdn, ↓reduceIte]; exact List.mem_singleton_self _)), ?_⟩
      simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true]
      refine ⟨dep _ _ true hL' sL (by simp), fun g hg => ?_⟩
      obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hg
      obtain ⟨x, hx, hxe⟩ := hcorr x' hx'
      refine dep _ (andPush b x) false ?_
        (same_mk _ (iface_equiv _ _ hxe).2 (iface_equiv _ _ hxe).1) ?_
      · simp only [produce, produce.produceStrategies, hdn, ite_true, List.map_map,
          List.mem_append, List.mem_map]
        exact .inl (.inr ⟨x', hx', rfl⟩)
      · simp only [List.mem_cons, List.mem_map]
        exact .inr ⟨x, hx, rfl⟩
    · obtain ⟨hdn, hcorr⟩ := dn _ _ hR' sR (by simp)
      refine List.any_eq_true.2 ⟨_, List.mem_append_right _
        (by simp only [hdn, ↓reduceIte]; exact List.mem_singleton_self _), ?_⟩
      simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true]
      refine ⟨dep _ _ true hR' sR (by simp), fun g hg => ?_⟩
      obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hg
      obtain ⟨x, hx, hxe⟩ := hcorr x' hx'
      refine dep _ (andPush a x) false ?_
        (same_mk _ (iface_equiv _ _ hxe).2 (iface_equiv _ _ hxe).1) ?_
      · simp only [produce, produce.produceStrategies, hdn, ite_true, List.map_map,
          List.mem_append, List.mem_map]
        exact .inr ⟨x', hx', rfl⟩
      · simp only [List.mem_cons, List.mem_map]
        exact .inr ⟨x, hx, rfl⟩

/-! ## The open listed tables complete together -/

/-- The open tables listed with rank at most `r`. -/
def openAt (C : List CertEntry) (ts : Tables) (r : Nat) : List Nat :=
  (List.range ts.length).filter fun j =>
    !(ts.getD j noTable).done &&
      C.any fun e => decide (e.rank ≤ r) && decide (indexOf ts e.goal = some j)

theorem mem_openAt {C : List CertEntry} {ts : Tables} {r j : Nat} :
    j ∈ openAt C ts r ↔ ∃ hj : j < ts.length, ts[j].done = false ∧
      ∃ e ∈ C, e.rank ≤ r ∧ indexOf ts e.goal = some j := by
  simp only [openAt, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hj, hd, h⟩
    exact ⟨hj, by simpa [List.getD_eq_getElem?_getD, hj] using hd, h⟩
  · rintro ⟨hj, hd, h⟩
    exact ⟨hj, by simpa [List.getD_eq_getElem?_getD, hj] using hd, h⟩

theorem gained_false {s : State} {j : Nat} (hj : j < s.tables.length)
    (h : (upd s s.tables[j]).answers.length = s.tables[j].answers.length) :
    gainedAt s.tables (s.tables.map (upd s)) j = false := by
  simp [gainedAt, List.getD_eq_getElem?_getD, hj, h]

/-- A goal an open table reads has a table, and a listed one has it already
if no listed goal gets its table this round. -/
theorem dep_index {C : List CertEntry} {s : State}
    (hex : ∀ e ∈ C, (∃ j, indexOf (round s).1.tables e.goal = some j) →
      ∃ j, indexOf s.tables e.goal = some j)
    {i : Nat} (hi : i < s.tables.length) (hnd : s.tables[i].done = false) {g : Goal}
    (hg : g ∈ (produce s.P s.depth s.tables s.tables[i].goal).2) {e' : CertEntry} (he' : e' ∈ C)
    (hs : e'.goal.same g.norm.2 = true) :
    ∃ j, ∃ _ : j < s.tables.length,
      indexOf s.tables g.norm.2 = some j ∧ indexOf s.tables e'.goal = some j := by
  have hr : g.norm.2 ∈ reqsOf s := by
    simp only [reqsOf, List.mem_map, List.mem_flatMap]
    exact ⟨g, ⟨_, ⟨_, List.getElem_mem hi, rfl⟩, by rwa [outOf_not_done hnd]⟩, rfl⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (reqs_found hr)
  obtain ⟨j', hj', -⟩ := find_indexOf ht
  obtain ⟨j, hj⟩ := hex e' he' ⟨j', by rw [indexOf_same _ hs]; exact hj'⟩
  obtain ⟨hlt, -, -⟩ := indexOf_find hj
  exact ⟨j, hlt, by rw [← indexOf_same _ hs]; exact hj, hj⟩

section Closed

variable {P : Program} (hL : SimpLaws P.theory) {C : List CertEntry} {D : Nat} {root : Goal}
  (hC : Cert.Valid P C D root)
include hL hC

/-- In a state past the certificate's depth where no listed goal is still to
get its table, the listed tables of rank below `r` are complete and no listed
table gains an answer, every open table listed with rank at most `r`
completes. -/
theorem closed_complete {s : State} (hP : s.P = P) (hI : XInv P s.tables) (r : Nat)
    (hD : D ≤ s.depth)
    (hex : ∀ e ∈ C, (∃ j, indexOf (round s).1.tables e.goal = some j) →
      ∃ j, indexOf s.tables e.goal = some j)
    (hlow : ∀ e ∈ C, e.rank < r → ∀ j (hj : j < s.tables.length),
      indexOf s.tables e.goal = some j → s.tables[j].done = true)
    (hng : ∀ e ∈ C, ∀ j (hj : j < s.tables.length), indexOf s.tables e.goal = some j →
      (upd s s.tables[j]).answers.length = s.tables[j].answers.length) :
    ∀ i ∈ openAt C s.tables r, i ∈ compl s := by
  subst hP
  refine completing_closed s.P s.depth s.tables (s.tables.map (upd s)) _ ?_ ?_ ?_ ?_
  · intro i hi; exact (mem_openAt.1 hi).1
  · intro i hi
    obtain ⟨hj, hd, -⟩ := mem_openAt.1 hi
    simpa [List.getD_eq_getElem?_getD, hj] using hd
  · intro i hi
    obtain ⟨hj, -, e, he, -, hm⟩ := mem_openAt.1 hi
    exact gained_false hj (hng e he i hj hm)
  · intro i hi
    obtain ⟨hj, hd, e, he, her, hm⟩ := mem_openAt.1 hi
    obtain ⟨_, -, hs⟩ := indexOf_find hm
    have hgi : (s.tables.getD i noTable).goal = s.tables[i].goal := by
      simp [List.getD_eq_getElem?_getD, hj]
    show (strategies s.P s.depth s.tables (s.tables.getD i noTable).goal).any
      (fun deps => deps.all (depOK s (openAt C s.tables r))) = true
    rw [hgi]
    have hdep : ∀ g ∈ (produce s.P s.depth s.tables s.tables[i].goal).2, ∀ ge : Goal,
        g.same ge = true → (∃ e' ∈ C, e'.goal.same ge.norm.2 = true ∧ e'.rank ≤ r) →
        depOK s (openAt C s.tables r) g = true := by
      rintro g hg ge hsg ⟨e', he', h1, h2⟩
      have hs' : e'.goal.same g.norm.2 = true :=
        Goal.same_trans h1 (Goal.same_symm (Symmetry.norm_same hsg).2)
      obtain ⟨j, hlt, hj1, hj2⟩ := dep_index hex hj hd hg he' hs'
      simp only [depOK, hj1]
      rw [gained_false hlt (hng e' he' j hlt hj2)]
      cases hdj : s.tables[j].done with
      | true => simp [List.getD_eq_getElem?_getD, hlt, hdj]
      | false =>
        have : j ∈ openAt C s.tables r := mem_openAt.2 ⟨hlt, hdj, e', he', h2, hj2⟩
        simp [this]
    have hdone : ∀ g ∈ (produce s.P s.depth s.tables s.tables[i].goal).2, ∀ ge : Goal,
        g.same ge = true → (∃ e' ∈ C, e'.goal.same ge.norm.2 = true ∧ e'.rank < r) →
        doneOf s.tables g = true ∧
          ∀ x' ∈ maxima (answersOf s.tables g), ∃ x ∈ maxima (certCover C ge), x'.Equiv x := by
      rintro g hg ge hsg ⟨e', he', h1, h2⟩
      have hn := Symmetry.norm_same hsg
      have hs' : e'.goal.same g.norm.2 = true := Goal.same_trans h1 (Goal.same_symm hn.2)
      obtain ⟨j, hlt, hj1, hj2⟩ := dep_index hex hj hd hg he' hs'
      have hdj := hlow e' he' h2 j hlt hj2
      refine ⟨by rw [doneOf_of_index hj1 hlt]; exact hdj, ?_⟩
      cases hf : C.find? (fun e => e.goal.same ge.norm.2) with
      | none => exact absurd h1 (by simpa using List.find?_eq_none.1 hf e' he')
      | some e'' =>
        have he'' := List.mem_of_find?_eq_some hf
        have hs'' : e''.goal.same ge.norm.2 = true :=
          List.find?_some (p := fun e : CertEntry => e.goal.same ge.norm.2) hf
        have hj3 : indexOf s.tables e''.goal = some j := by
          rw [indexOf_same _ (Goal.same_trans hs'' (Goal.same_symm hn.2))]; exact hj1
        have hcc : certCover C ge = orient ge.norm.1 e''.cover := by simp [certCover, hf]
        rw [hcc, answersOf_of_index hj1 hlt, hn.1]
        intro x' hx'
        exact maxima_equiv (orient_cover (matched_cov hL hC hI he'' hj3 hlt))
          (orient_cover (matched_cov_done hL hC hI he'' hj3 hlt hdj)) hx'
    rcases (hC.2 e he).2.2.2 with hu | hst
    · have : unfoldFinal s.P s.depth s.tables[i].goal = true := by
        rw [Unf.unfoldFinal_same s.P hs]; exact Unf.unfoldFinal_mono s.P hu _ hD
      simp [strategies, this]
    · simp only [strategies, List.any_append, Bool.or_eq_true]
      right
      refine strat_ok s rfl _ r hs hdep hdone ?_
      obtain ⟨st, h1, h2⟩ := hst
      refine ⟨st, h1, fun d hd => ?_⟩
      obtain ⟨e', he', h3, h4⟩ := h2 d hd
      refine ⟨e', he', h3, ?_⟩
      split <;> rename_i h <;> simp only [h, ite_true, Bool.false_eq_true, ite_false] at h4 <;> omega

end Closed

/-! ## The run -/

/-- A run halts exactly when some unconditional round leaves the root
complete. -/
theorem halts_iff_iter (st : State) :
    (∃ k, (stateAfter st k).finished = true) ↔ ∃ k, (iter st k).finished = true := by
  constructor
  · rintro ⟨n, hn⟩
    rcases stateAfter_cases st n with ⟨k, -, -, h2⟩ | ⟨-, h2⟩
    · exact ⟨k, by rw [← h2]; exact hn⟩
    · exact ⟨n, by rw [← h2]; exact hn⟩
  · rintro ⟨k, hk⟩
    rcases stateAfter_cases st k with ⟨k', -, h1, h2⟩ | ⟨-, h2⟩
    · exact ⟨k, by rw [h2]; exact h1⟩
    · exact ⟨k, by rw [h2]; exact hk⟩

/-- From some round on, every listed goal that ever gets a table has it. -/
theorem listed_early (st : State) (C : List CertEntry) :
    ∃ K, ∀ e ∈ C, ∀ k ≥ K, (∃ k' j, indexOf (iter st k').tables e.goal = some j) →
      ∃ j, indexOf (iter st k).tables e.goal = some j := by
  refine ev_all (fun (e : CertEntry) k => (∃ k' j, indexOf (iter st k').tables e.goal = some j) →
      ∃ j, indexOf (iter st k).tables e.goal = some j) C fun e _ => ?_
  by_cases h : ∃ k' j, indexOf (iter st k').tables e.goal = some j
  · obtain ⟨k', j, hj⟩ := h
    exact ⟨k', fun k hk _ => ⟨j, indexOf_iter st hk hj⟩⟩
  · exact ⟨0, fun k _ h' => absurd h' h⟩

section Run

variable {P : Program} (hL : SimpLaws P.theory) {C : List CertEntry} {D : Nat} {root : Goal}
  (hC : Cert.Valid P C D root)
include hL hC

/-- From some round on, every listed table covers the listed cover. -/
theorem listed_stable {st : State} (hP : st.P = P) (hI : XInv P st.tables) :
    ∃ K, ∀ e ∈ C, ∀ k ≥ K, ∀ j, indexOf (iter st k).tables e.goal = some j →
      ∀ f ∈ e.cover, ∃ hj : j < (iter st k).tables.length,
        ∃ a ∈ (iter st k).tables[j].answers, a.Covers f := by
  subst hP
  refine ev_all (fun (e : CertEntry) k => ∀ j, indexOf (iter st k).tables e.goal = some j →
      ∀ f ∈ e.cover, ∃ hj : j < (iter st k).tables.length,
        ∃ a ∈ (iter st k).tables[j].answers, a.Covers f) C fun e he => ?_
  by_cases h : ∃ k' j, indexOf (iter st k').tables e.goal = some j
  · obtain ⟨k', j', hj'⟩ := h
    obtain ⟨hlt, -, hs⟩ := indexOf_find hj'
    have hge := goodG_of_interfaced (hC.2 e he).1
    have hgt := (xinv_iter hL hI k').good _ (List.getElem_mem hlt)
    obtain ⟨K₁, hK₁⟩ := ev_all (fun (f : Span) k => ∃ hj : j' < (iter st k).tables.length,
        ∃ a ∈ (iter st k).tables[j'].answers, a.Covers f) e.cover (by
      intro f hf
      obtain ⟨s, hd, hsub⟩ := gderives_sub hL ((hC.2 e he).2.1 f hf) hge
      rw [← same_e hs] at hd
      rw [← same_gden hs hgt hge] at hsub
      obtain ⟨w, hw⟩ := dw_of_derives hd
      obtain ⟨k₀, hk₀⟩ := fair_x hL hI _ k' j' hlt w s hw le_rfl
      refine ⟨k₀, fun k hk => ?_⟩
      obtain ⟨hi', hxc⟩ := hk₀ k hk
      exact ⟨hi', hxc.cover hsub⟩)
    refine ⟨max k' K₁, fun k hk j hj f hf => ?_⟩
    have := indexOf_iter st (le_trans (le_max_left _ _) hk) hj'
    rw [hj] at this
    cases this
    exact hK₁ f hf k (le_trans (le_max_right _ _) hk)
  · exact ⟨0, fun k _ j hj => absurd ⟨k, j, hj⟩ h⟩

/-- The listed tables of rank below `r` are complete from some round on. -/
theorem ranks_complete {st : State} (hP : st.P = P) (hI : XInv P st.tables) :
    ∀ r, ∃ K, ∀ k ≥ K, ∀ e ∈ C, e.rank < r → ∀ j,
      indexOf (iter st k).tables e.goal = some j →
      ∃ hj : j < (iter st k).tables.length, (iter st k).tables[j].done = true
  | 0 => ⟨0, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | r + 1 => by
    obtain ⟨Kr, hKr⟩ := ranks_complete hP hI r
    obtain ⟨K₀, hK₀⟩ := listed_early st C
    obtain ⟨Kd, hKd⟩ := listed_stable hL hC hP hI
    subst hP
    let K := max (max Kr K₀) (max Kd D)
    have h1 : Kr ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
    have h2 : K₀ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
    have h3 : Kd ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
    have h4 : D ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨K + 1, fun k hk e he her j hm => ?_⟩
    obtain ⟨j₀, hj₀⟩ := hK₀ e he K h2 ⟨k, j, hm⟩
    have := indexOf_iter st (show K ≤ k by omega) hj₀
    rw [hm] at this
    cases this
    obtain ⟨hlt, -, -⟩ := indexOf_find hj₀
    obtain ⟨hlt', hafter⟩ := iter_getElem_succ st K j hlt
    have hdone : (iter st (K + 1)).tables[j].done = true := by
      rw [hafter, after_done]
      cases hdj : (iter st K).tables[j].done with
      | true => rfl
      | false =>
        have hopen : j ∈ openAt C (iter st K).tables r :=
          mem_openAt.2 ⟨hlt, hdj, e, he, by omega, hj₀⟩
        have := closed_complete hL hC (s := iter st K) (iter_P st K) (xinv_iter hL hI K) r
          (by rw [iter_depth]; omega)
          (fun e' he' ⟨j', hj'⟩ => hK₀ e' he' K h2 ⟨K + 1, j', hj'⟩)
          (fun e' he' hr' j' _ hm' => (hKr K h1 e' he' hr' j' hm').2)
          (fun e' he' j' hj' hm' => no_gain hL hC (iter_P st K) (xinv_iter hL hI K) he' hm' hj'
            (fun f hf => (hKd e' he' K h3 j' hm' f hf).2))
          j hopen
        simp [this]
    obtain ⟨hk', hext⟩ := iter_ext_le st (show K + 1 ≤ k by omega) j hlt'
    exact ⟨hk', hext.2.2 hdone⟩

end Run

/-- A goal with a valid certificate halts. -/
theorem halts_of_cert {P : Program} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) {C : List CertEntry}
    {D : Nat} {root : Goal} (hroot : GoodG root) (hC : Cert.Valid P C D root) :
    GoalTerminates P root := by
  have hL := simpLaws_of_wf hwf
  rw [goalTerminates_iff, halts_iff_iter]
  obtain ⟨e, he, hs⟩ := hC.1
  have hm0 : indexOf (State.ofGoal P root).tables e.goal = some 0 := by
    simp [State.ofGoal, indexOf, Goal.same_symm hs]
  obtain ⟨K, hK⟩ := ranks_complete hL hC (st := State.ofGoal P root) rfl (xinv_ofGoal hroot)
    (e.rank + 1)
  obtain ⟨hj, hd⟩ := hK K le_rfl e he (Nat.lt_succ_self _) 0 (indexOf_iter _ (Nat.zero_le K) hm0)
  refine ⟨K, ?_⟩
  simp [State.finished, List.head?_eq_getElem?, List.getElem?_eq_getElem hj, hd]

end CertHalts

end R001

end RwLog
