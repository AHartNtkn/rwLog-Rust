/-
# A goal whose unfolding is final completes

For the symmetric engine with an exact unfolding race that meets its
specification. If the unfolding of a goal to some depth is final, every run
of requests that does not neglect the goal completes it (`final_completes`).

The engine asks the race for chain goals only. For a goal of another kind the
verdict of its unfolding is made of the verdicts of the goals its own
strategies read (`Unfolding/Model.lean`, `SE`), one depth lower:

* a span completes by its strategy;
* a call is final when its body is, and a union when every member is: the
  strategy that copies them has nothing left to do;
* a chain has its race, asked at every depth (`IsRun.race_done`);
* a meet is final when every member is, and then the join of one member with
  the others has nothing left to do; or when the unfolding of one member has
  no product, and then that member relates nothing and completes, which
  completes the meet (`IsRun.done_of_side`).

Each step is a certificate of one reason over goals that complete
(`completes_step`, by `Cert.completes`). The answers of a goal whose
unfolding is final are those the race gives (`raceAns`).
-/
import RwLog.Rungs.Symmetric.EmptySide
import RwLog.Rungs.Framework.Unfolding.RacesExact

namespace RwLog

namespace Symmetric

open Answer Saturation Goals Unfold

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  {U : GOracle R Rel (Ans D P) Cost}

section

variable (hL : D.Lawful P.sorts.interp)

include hL

omit [DecidableEq R] in
/-- The answers of a final verdict are answers of the goal and cover every
answer of the goal. -/
theorem raceAns (hU : UOk D P U) {g : GoalOf R Rel} (hg : GoalOk D g) {d : Nat}
    (hf : (U d g).val.1 = true) :
    (∀ a ∈ (U d g).val.2, a.goal = toGoal g) ∧
      ∀ y : Ans D P, y.goal = toGoal g → ∃ f ∈ (U d g).val.2, covB D P f y = true := by
  refine ⟨hU.goal d g hg, fun y hy => ?_⟩
  obtain ⟨k, G, hG, e⟩ := ans_gdn hL hy
  have hne : (pairsOf P g G).Nonempty := by
    rw [← e]
    exact hL.live y.span
  obtain ⟨f, hf', hsub⟩ := hU.final d g hg hf k G hG hne
  exact ⟨f, hf', (covB_iff hL f y).2 (by rw [e]; exact hsub)⟩

/-- **One reason over goals that complete.** A goal whose unfolding is final
completes if it has a reason to (`Why`) among goals that complete and whose
unfoldings are final, whatever their order and their answers. -/
theorem completes_step (hU : UOk D P U) {g : GoalOf R Rel} (hg : GoalOk D g) {d : Nat}
    (hf : (U d g).val.1 = true) (subs : List (GoalOf R Rel))
    (hsubs : ∀ s ∈ subs, Completes U s ∧ GoalOk D s ∧ ∃ d, (U d s).val.1 = true)
    (hw : ∀ (ρ : GoalOf R Rel → Nat) (A : GoalOf R Rel → List (Ans D P)),
      (∀ s, ρ s ≤ ρ g) → Why (fun g' => g' = g ∨ g' ∈ subs) ρ A g) : Completes U g := by
  classical
  let ρ : GoalOf R Rel → Nat := fun s => if s = g then 1 else 0
  let A : GoalOf R Rel → List (Ans D P) := fun s =>
    if h : ∃ d, (U d s).val.1 = true then (U (Classical.choose h) s).val.2 else []
  have hρ : ∀ s, ρ s ≤ ρ g := fun s => by
    show (if s = g then 1 else 0) ≤ (if g = g then 1 else 0)
    simp only [↓reduceIte]
    split <;> omega
  have ok : ∀ s, (s = g ∨ s ∈ subs) → GoalOk D s ∧ ∃ d, (U d s).val.1 = true := by
    rintro s (rfl | hs)
    · exact ⟨hg, d, hf⟩
    · exact (hsubs s hs).2
  have hA : ∀ s, (s = g ∨ s ∈ subs) → (∀ a ∈ A s, a.goal = toGoal s) ∧
      ∀ y : Ans D P, y.goal = toGoal s → ∃ f ∈ A s, covB D P f y = true := by
    intro s hs
    obtain ⟨hok, h⟩ := ok s hs
    have e : A s = (U (Classical.choose h) s).val.2 := by
      show (if h : ∃ d, (U d s).val.1 = true then (U (Classical.choose h) s).val.2 else []) = _
      simp only [h, ↓reduceDIte]
    rw [e]
    exact raceAns hL hU hok (Classical.choose_spec h)
  have hC : Cert U (fun g' => g' = g ∨ g' ∈ subs) ρ A := by
    refine ⟨⟨g :: subs, fun s hs => by simpa using hs⟩, fun s hs => (hA s hs).1,
      fun s hs => (hA s hs).2, fun s hs => ?_⟩
    by_cases e : s = g
    · subst e
      exact .inr (hw ρ A hρ)
    · exact .inl (hsubs s (hs.resolve_left e)).1
  exact hC.completes hL (.inl rfl)

end

local notation "𝕄" => P.sorts.interp

omit [DecidableEq R] in
/-- A goal whose unfolding is final and has no product relates nothing. -/
theorem void_of_empty (hU : UOk D P U) (hE : UEx D P U) {g : GoalOf R Rel} (hg : GoalOk D g)
    {d : Nat} (hf : (U d g).val.1 = true)
    (he : SE P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb) = ∅) : Void P g := by
  intro k G hG
  by_contra hne
  obtain ⟨a, ha, -⟩ := hU.final d g hg hf k G hG (Set.nonempty_iff_ne_empty.2 hne)
  have := (hE.closed d g hg hf (den 𝕄 a.span)).1 ⟨a, ha, rfl⟩
  unfold closedPart at this
  rw [he] at this
  exact this

omit [DecidableEq R] in
/-- The unfolding of a meet all of whose members have a final unfolding is
final, one depth further. -/
theorem meet_verdict (hE : UEx D P U) {lb rb : Option R} {xs : List Rel} (h2 : 2 ≤ xs.length)
    (hna : ∀ x ∈ xs, NotAnd x) (hgok : GoalOk D (⟨lb, mkAnd xs, rb⟩ : GoalOf R Rel)) {d : Nat}
    (hall : ∀ x ∈ xs, Final P 𝕄 d (bset 𝕄 lb) x (bset 𝕄 rb)) :
    (U (d + 1) ⟨lb, mkAnd xs, rb⟩).val.1 = true := by
  refine (hE.final (d + 1) _ hgok).2 ?_
  have hv : (mkAnd xs).view.forget = .meet xs := by rw [view_mkAnd h2 hna]; rfl
  show ¬ HasOpn (SE P 𝕄 (d + 1) _ (mkAnd xs) _)
  rw [se_meet hv]
  rintro ⟨A', B', h | ⟨-, -, S, hS, hop⟩⟩
  · obtain ⟨X, -, e⟩ := h
    cases e
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hS
    exact hall x hx hop

/-- A meet all of whose members complete and have a final unfolding
completes: the join of one member with the others has nothing left to do. -/
theorem meet_completes (hL : D.Lawful P.sorts.interp) (hU : UOk D P U) (hE : UEx D P U)
    {lb rb : Option R} (hlb : IsBound D lb) (hrb : IsBound D rb) {d : Nat} :
    ∀ (n : Nat) (xs : List Rel), xs.length = n + 2 → xs.Pairwise RelLE →
      (∀ x ∈ xs, Normal x ∧ NotAnd x) → (∀ x ∈ xs, x.FO) →
      (∀ x ∈ xs, Completes U (⟨lb, x, rb⟩ : GoalOf R Rel) ∧ (U d ⟨lb, x, rb⟩).val.1 = true) →
      Completes U (⟨lb, mkAnd xs, rb⟩ : GoalOf R Rel) ∧
        GoalOk D (⟨lb, mkAnd xs, rb⟩ : GoalOf R Rel) ∧
        ∃ d', (U d' ⟨lb, mkAnd xs, rb⟩).val.1 = true := by
  have tail : ∀ xs : List Rel, 2 ≤ xs.length → xs.Pairwise RelLE →
      (∀ x ∈ xs, Normal x ∧ NotAnd x) → (∀ x ∈ xs, x.FO) →
      (∀ x ∈ xs, Completes U (⟨lb, x, rb⟩ : GoalOf R Rel) ∧ (U d ⟨lb, x, rb⟩).val.1 = true) →
      (Completes U (⟨lb, mkAnd (xs.eraseIdx 0), rb⟩ : GoalOf R Rel) ∧
        GoalOk D (⟨lb, mkAnd (xs.eraseIdx 0), rb⟩ : GoalOf R Rel) ∧
        ∃ d', (U d' ⟨lb, mkAnd (xs.eraseIdx 0), rb⟩).val.1 = true) →
      Completes U (⟨lb, mkAnd xs, rb⟩ : GoalOf R Rel) ∧
        GoalOk D (⟨lb, mkAnd xs, rb⟩ : GoalOf R Rel) ∧
        ∃ d', (U d' ⟨lb, mkAnd xs, rb⟩).val.1 = true := by
    intro xs h2 hs hN hfo hall hrest
    have hgok : GoalOk D (⟨lb, mkAnd xs, rb⟩ : GoalOf R Rel) :=
      ⟨hlb, hrb, normal_mkAnd (List.ne_nil_of_length_pos (by omega)) hN hs, fun s hs' => by
        obtain ⟨x, hx, h⟩ := (spans_mkAnd xs s).1 hs'
        exact hfo x hx s h⟩
    have mok : ∀ x ∈ xs, GoalOk D (⟨lb, x, rb⟩ : GoalOf R Rel) := fun x hx =>
      ⟨hlb, hrb, (hN x hx).1, hfo x hx⟩
    have hfin := meet_verdict hE h2 (fun x hx => (hN x hx).2) hgok
      (fun x hx => (hE.final d _ (mok x hx)).1 (hall x hx).2)
    have h0 : 0 < xs.length := by omega
    have hsp : SplitAt (⟨lb, mkAnd xs, rb⟩ : GoalOf R Rel) .and ⟨lb, xs[0], rb⟩
        ⟨lb, mkAnd (xs.eraseIdx 0), rb⟩ :=
      splitAt_mkAnd (fun x hx => (hN x hx).2) h2 h0 (by
        unfold andSplits
        split
        · simp
        · exact List.mem_range.2 h0)
    refine ⟨completes_step hL hU hgok hfin
      [⟨lb, xs[0], rb⟩, ⟨lb, mkAnd (xs.eraseIdx 0), rb⟩] (fun s hs => ?_)
      (fun ρ A hρ => .join .and _ _ hsp ⟨.inr (by simp), hρ _⟩ ⟨.inr (by simp), hρ _⟩),
      hgok, _, hfin⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨(hall _ (List.getElem_mem h0)).1, mok _ (List.getElem_mem h0), d,
        (hall _ (List.getElem_mem h0)).2⟩
    · exact hrest
  intro n
  induction n with
  | zero =>
    intro xs hlen hs hN hfo hall
    refine tail xs (by omega) hs hN hfo hall ?_
    match xs, hlen with
    | [a, b], _ =>
      have hb : b ∈ [a, b] := by simp
      exact ⟨(hall b hb).1, ⟨hlb, hrb, (hN b hb).1, hfo b hb⟩, d, (hall b hb).2⟩
  | succ n ih =>
    intro xs hlen hs hN hfo hall
    refine tail xs (by omega) hs hN hfo hall ?_
    have hsub : ∀ x ∈ xs.eraseIdx 0, x ∈ xs := fun x hx => List.mem_of_mem_eraseIdx hx
    exact ih (xs.eraseIdx 0) (by rw [List.length_eraseIdx]; split <;> omega)
      (hs.sublist (List.eraseIdx_sublist xs 0)) (fun x hx => hN x (hsub x hx))
      (fun x hx => hfo x (hsub x hx)) (fun x hx => hall x (hsub x hx))

/-- **A goal whose unfolding is final completes**, in every run of requests
that does not neglect it. -/
theorem final_completes (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
    (hE : UEx D P U) : ∀ (d : Nat) (g : GoalOf R Rel), GoalOk D g → (U d g).val.1 = true →
      Completes U g := by
  intro d
  induction d with
  | zero =>
    intro g hg hf
    exact absurd ⟨_, _, rfl⟩ ((hE.final 0 g hg).1 hf)
  | succ d ih =>
    intro g hg hf
    have hF := (hE.final (d + 1) g hg).1 hf
    obtain ⟨lb, e, rb⟩ := g
    have hlb : IsBound D lb := hg.lb
    have hrb : IsBound D rb := hg.rb
    have hn : Normal e := hg.normal
    have hfo : e.FO := hg.fo
    change Final P 𝕄 (d + 1) (bset 𝕄 lb) e (bset 𝕄 rb) at hF
    cases hv : e.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      exact completes_step hL hU hg hf [] (by simp) (fun ρ A _ => .span ⟨s, rfl⟩)
    | call n f =>
      obtain ⟨b, hb⟩ := forget_call (P := P) hv
      have hgb : GoalOk D (⟨lb, b, rb⟩ : GoalOf R Rel) :=
        ⟨hlb, hrb, normal_bodyOf hb, bodyOf_fo hP hb⟩
      have hFb : Final P 𝕄 d (bset 𝕄 lb) b (bset 𝕄 rb) := by
        unfold Final at hF ⊢
        rw [se_call hv hb] at hF
        exact hF
      have hfb := (hE.final d _ hgb).2 hFb
      refine completes_step hL hU hg hf [⟨lb, b, rb⟩] (fun s hs => ?_)
        (fun ρ A hρ => .copy true (fun _ => ⟨b, hb⟩) (fun h => by cases h) (fun x hx => ?_))
      · obtain rfl := List.mem_singleton.1 hs
        exact ⟨ih _ hgb hfb, hgb, d, hfb⟩
      · have hx' : x ∈ (Charged.bodyOf P e).toList := hx
        rw [hb] at hx'
        obtain rfl : x = b := by simpa using hx'
        exact ⟨.inr (List.mem_singleton.2 rfl), hρ _⟩
    | union xs =>
      have hvu := forget_union hv
      have hparts : xs = e.unionParts := hn.view_union_eq hvu
      have mok : ∀ x ∈ xs, GoalOk D (⟨lb, x, rb⟩ : GoalOf R Rel) := fun x hx =>
        ⟨hlb, hrb, hn.view_members (by rw [hvu]; exact hx),
          hfo.view_members (by rw [hvu]; exact hx)⟩
      have hfx : ∀ x ∈ xs, (U d ⟨lb, x, rb⟩).val.1 = true := fun x hx =>
        (hE.final d _ (mok x hx)).2 (fun ⟨A', B', h⟩ => hF ⟨A', B', by
          rw [se_union hv]
          exact ⟨x, hx, h⟩⟩)
      refine completes_step hL hU hg hf (xs.map fun x => ⟨lb, x, rb⟩) (fun s hs => ?_)
        (fun ρ A hρ => .copy false (fun h => by cases h) (fun _ => ⟨xs, hvu⟩) (fun x hx => ?_))
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
        exact ⟨ih _ (mok x hx) (hfx x hx), mok x hx, d, hfx x hx⟩
      · have hx' : x ∈ e.unionParts := hx
        rw [← hparts] at hx'
        exact ⟨.inr (List.mem_map.2 ⟨x, hx', rfl⟩), hρ _⟩
    | chain xs =>
      have hh : hasRace (⟨lb, e, rb⟩ : GoalOf R Rel) = true := by
        unfold hasRace
        simp only [hv]
      intro τ hτ _ r' k hk ho
      rcases ho with hev | hlive
      · exact hev
      · exact hτ.race_done hk hlive hh hf
    | meet xs =>
      have hvm := forget_meet hv
      obtain ⟨h2, hmem, hsort, rfl⟩ := hn.view_meet hvm
      have hfx : ∀ x ∈ xs, x.FO := fun x hx s hs => hfo s ((spans_mkAnd xs s).2 ⟨x, hx, hs⟩)
      have mok : ∀ x ∈ xs, GoalOk D (⟨lb, x, rb⟩ : GoalOf R Rel) := fun x hx =>
        ⟨hlb, hrb, (hmem x hx).1, hfx x hx⟩
      unfold Final at hF
      rw [se_meet hv] at hF
      by_cases hall : ∀ x ∈ xs, Final P 𝕄 d (bset 𝕄 lb) x (bset 𝕄 rb)
      · have hv' : ∀ x ∈ xs, (U d ⟨lb, x, rb⟩).val.1 = true := fun x hx =>
          (hE.final d _ (mok x hx)).2 (hall x hx)
        exact (meet_completes hL hU hE hlb hrb (xs.length - 2) xs (by omega) hsort hmem hfx
          (fun x hx => ⟨ih _ (mok x hx) (hv' x hx), hv' x hx⟩)).1
      · -- a member has an open product, so the unfolding of some member has no product
        have hex : ∃ x ∈ xs, SE P 𝕄 d (bset 𝕄 lb) x (bset 𝕄 rb) = ∅ := by
          by_contra hno
          simp only [not_forall] at hall
          obtain ⟨x, hx, hop⟩ := hall
          refine hF ⟨_, _, .inr ⟨rfl, fun S hS => ?_, _, List.mem_map_of_mem hx,
            not_not.1 hop⟩⟩
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hS
          exact Set.nonempty_iff_ne_empty.2 fun h => hno ⟨y, hy, h⟩
        obtain ⟨x, hx, hemp⟩ := hex
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        have hfi : (U d ⟨lb, xs[i], rb⟩).val.1 = true :=
          (hE.final d _ (mok _ hx)).2 (by
            unfold Final
            rw [hemp]
            rintro ⟨_, _, h⟩
            exact h)
        have hvoid : Void P (⟨lb, xs[i], rb⟩ : GoalOf R Rel) :=
          void_of_empty hU hE (mok _ hx) hfi hemp
        have hcomp := ih _ (mok _ hx) hfi
        have hna : ∀ x ∈ xs, NotAnd x := fun x hx => (hmem x hx).2
        intro τ hτ hN r' k hk ho
        by_cases hsplit : i ∈ andSplits xs.length
        · exact hτ.done_of_side hL hk ho (splitAt_mkAnd hna h2 hi hsplit) true rfl hvoid
            (fun r'' j hj ho' => hcomp τ hτ hN r'' j hj ho')
        · have h2' : xs.length = 2 ∧ i = 1 := by
            unfold andSplits at hsplit
            split at hsplit
            · simp only [List.mem_singleton] at hsplit
              omega
            · exact absurd (List.mem_range.2 hi) hsplit
          obtain ⟨hl2, rfl⟩ := h2'
          have h0 : 0 < xs.length := by omega
          have he : mkAnd (xs.eraseIdx 0) = xs[1] := by
            match xs, hl2, hi with
            | [a, b], _, _ => rfl
          exact hτ.done_of_side hL hk ho
            (splitAt_mkAnd hna h2 h0 (by unfold andSplits; simp [hl2])) false
            (by simp only [Bool.false_eq_true, ↓reduceIte, he]) hvoid (fun r'' j hj ho' => hcomp τ hτ hN r'' j hj ho')

end Symmetric

end RwLog
