/-
# A run of requests is fair

A table that has a round in infinitely many requests is served
(`IsRun.served_live`). One of its groups works in infinitely many requests
(`Requests.line`), and that group has a span, a call, a union or a join, or
is all interface checks:

* a span has run after the group worked once;
* a call or a union reads every answer of every table it reads: the number
  of answers below a position that it has not read falls whenever the group
  works while one is left;
* a join combines every pair: the rank of its cursor falls whenever the
  group works while the pair is not combined;
* of a group of checks, one check is never dead. The depth edges are read
  to doubles while it has not read its side, so it reads it; it is offered,
  or it would be dead; and none of the goals it opened ever has an answer.

The tables such a strategy reads need no round in infinitely many requests,
so they are not neglected either. Of the members of a union one has a round
when the group works, the one fed least, and every member still needs no
round in infinitely many requests (`Requests.union_settled`).

With `IsRun.served_done`, a run of requests is fair (`IsRun.fair`), and it
opens the root (`IsRun.root_opened`).
-/
import RwLog.Rungs.Symmetric.Served

namespace RwLog

namespace Symmetric

open Answer Saturation

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
  {U : GOracle R Rel (Ans D P) Cost}

variable {σ : Nat → StateOf R Rel (Ans D P)}

/-- The group has a span. -/
theorem IsRun.live_span (h : IsRun U σ) {ra k m : Nat} {g : GoalOf R Rel}
    {L : Nat → List (Strat Rel (Ans D P))} {ran0 : Bool} (hk : goalAt (σ ra) k = some g)
    (hL : Line (readNeed P) σ k ra L) (h0 : (L ra)[m]? = some (.span ran0)) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  obtain ⟨r, -, hr, hst⟩ := hL.step m ra
  obtain ⟨s, hs, ran, rfl⟩ := hL.along (fun _ s => ∃ ran, s = Strat.span ran) h0 ⟨ran0, rfl⟩
    (fun r s s' _ _ _ hq hadv => by
      obtain ⟨ran, rfl⟩ := hq
      cases hadv
      exact ⟨_, rfl⟩) hr
  obtain ⟨s', hs', hstep⟩ := hst _ hs
  cases hstep
  exact h.served_span hk (hL.mem (r + 1) (by omega) _ (List.mem_of_getElem? hs'))

/-- The group has a call or a union. -/
theorem IsRun.live_copy (h : IsRun U σ) {ra k m : Nat} {g : GoalOf R Rel}
    {L : Nat → List (Strat Rel (Ans D P))} {c : Bool} {subs0 : List (Nat × Nat)}
    (hk : goalAt (σ ra) k = some g) (hL : Line (readNeed P) σ k ra L)
    (h0 : (L ra)[m]? = some (.copy c subs0)) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  have al : ∀ r, ra ≤ r → ∃ s, (L r)[m]? = some s ∧
      ∃ subs, s = Strat.copy c subs ∧ Pointwise SubAdv subs0 subs := fun r hr =>
    hL.along (fun _ s => ∃ subs, s = Strat.copy c subs ∧ Pointwise SubAdv subs0 subs) h0
      ⟨subs0, rfl, Pointwise.refl (fun p => ⟨rfl, Nat.le_refl _⟩) _⟩
      (fun r s s' _ _ _ hq hadv => by
        obtain ⟨subs, rfl, hp⟩ := hq
        cases hadv with
        | copy hp' => exact ⟨_, rfl, Pointwise.comp (r₁ := SubAdv) (r₂ := SubAdv) (r₃ := SubAdv)
            (fun _ _ _ h1 h2 => SubAdv.trans h1 h2) hp hp'⟩) hr
  have hs0 : IsStrat σ k ra (.copy c subs0) :=
    hL.mem ra (Nat.le_refl _) _ (List.mem_of_getElem? h0)
  refine h.served_copy hk hs0 fun m' j pos0 hm => ?_
  have hp := h.prog hk hs0
  dsimp only [Prog] at hp
  obtain ⟨-, -, -, h3⟩ := hp
  obtain ⟨_, -, hgj, -⟩ := h3 m' j pos0 hm
  have ent : ∀ r, ra ≤ r → ∃ (subs : List (Nat × Nat)) (pos : Nat),
      (L r)[m]? = some (.copy c subs) ∧ subs[m']? = some (j, pos) := fun r hr => by
    obtain ⟨_, hs, subs, rfl, hp⟩ := al r hr
    obtain ⟨p, hp1, hp2⟩ := hp.get hm
    refine ⟨subs, p.2, hs, ?_⟩
    rw [hp1]
    exact congrArg some (Prod.ext hp2.1 rfl)
  refine ⟨h.opened_of_settled hgj fun r' => ?_, fun n r1 hn => ?_⟩
  · cases c with
    | true =>
      obtain ⟨r, hr', hr, hfed, -⟩ := hL.worked r'
      obtain ⟨subs, pos, hs, hm'⟩ := ent (r + 1) (by omega)
      exact ⟨r, hr', hfed _ (List.mem_of_getElem? hs) (j, pos) (List.mem_of_getElem? hm')⟩
    | false =>
      refine h.req.union_settled hL (m := m) (M := subs0.map Prod.fst) (fun r hr => ?_)
        (List.mem_map.2 ⟨(j, pos0), List.mem_of_getElem? hm, rfl⟩) r'
      obtain ⟨_, hs, subs, rfl, hp⟩ := al r hr
      exact ⟨subs, hs, map_fst_of_subAdv hp⟩
  · by_contra hcon
    simp only [not_exists, not_and, Nat.not_lt] at hcon
    let f : Nat → Nat := fun r =>
      match (L r)[m]? with
      | some (.copy _ subs) => behind (n + 1) subs
      | _ => 0
    refine no_descent (· < ·) Nat.lt_wfRel.wf (fun _ _ _ h1 h2 => Nat.lt_trans h1 h2) f
      (max ra r1) (fun r hr => ?_) (fun r' => ?_)
    · obtain ⟨_, hs, subs, rfl, -⟩ := al r (by omega)
      obtain ⟨s', hs', hadv⟩ := (hL.adv r (by omega)).get hs
      cases hadv with
      | copy hp' =>
        have := behind_le (n + 1) hp'
        simp only [f, hs, hs']
        omega
    · obtain ⟨r, hr', hr, hst⟩ := hL.step m (max r' (max ra r1))
      obtain ⟨subs, pos, hs, hm'⟩ := ent r hr
      obtain ⟨s', hs', hstep⟩ := hst _ hs
      cases hstep with
      | copy hp' hlt =>
        refine ⟨r, by omega, ?_⟩
        simp only [f, hs, hs']
        refine hlt (n + 1) m' j pos hm' ?_ ?_
        · have := hcon r subs pos (hL.mem r hr _ (List.mem_of_getElem? hs)) hm'
          omega
        · have := (h.stable (show r1 ≤ r by omega)).len_le j
          omega

/-- The group has a join. -/
theorem IsRun.live_join (h : IsRun U σ) {ra k m : Nat} {g : GoalOf R Rel}
    {L : Nat → List (Strat Rel (Ans D P))} {kd : Kind} {a b : Nat} {c0 : Cursor}
    (hk : goalAt (σ ra) k = some g) (hL : Line (readNeed P) σ k ra L)
    (h0 : (L ra)[m]? = some (.join kd a b c0)) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  have al : ∀ r, ra ≤ r → ∃ c, (L r)[m]? = some (.join kd a b c) := fun r hr => by
    obtain ⟨_, hs, c, rfl⟩ := hL.along (fun _ s => ∃ c, s = Strat.join kd a b c) h0 ⟨c0, rfl⟩
      (fun r s s' _ _ _ hq hadv => by
        obtain ⟨c, rfl⟩ := hq
        cases hadv
        exact ⟨_, rfl⟩) hr
    exact ⟨c, hs⟩
  have hs0 : IsStrat σ k ra (.join kd a b c0) :=
    hL.mem ra (Nat.le_refl _) _ (List.mem_of_getElem? h0)
  have hp := h.prog hk hs0
  dsimp only [Prog] at hp
  obtain ⟨La, Rb, -, hga, hgb, -, -⟩ := hp
  have fed : ∀ r', ∃ r, r' ≤ r ∧ Settled (σ (r + 1)) a ∧ Settled (σ (r + 1)) b := fun r' => by
    obtain ⟨r, hr', hr, hfed, -⟩ := hL.worked r'
    obtain ⟨c, hs⟩ := al (r + 1) (by omega)
    exact ⟨r, hr', hfed _ (List.mem_of_getElem? hs)⟩
  refine h.served_join hk hs0
    (h.opened_of_settled hga fun r' => (fed r').imp fun _ hr => ⟨hr.1, hr.2.1⟩)
    (h.opened_of_settled hgb fun r' => (fed r').imp fun _ hr => ⟨hr.1, hr.2.2⟩)
    fun p q r1 hp hq => ?_
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hno : ∀ r c, ra ≤ r → (L r)[m]? = some (.join kd a b c) → ¬ c.Before p q :=
    fun r c hr hs => hcon r c (hL.mem r hr _ (List.mem_of_getElem? hs))
  -- once the join has worked after `r1`, it has filed the two answers
  obtain ⟨rf, hrf', hrf, hstf⟩ := hL.step m (max ra r1)
  obtain ⟨cf, hsf⟩ := al rf hrf
  obtain ⟨sf', hsf', hstepf⟩ := hstf _ hsf
  have filed : ∀ r c, rf + 1 ≤ r → (L r)[m]? = some (.join kd a b c) →
      p < c.pa.length ∧ q < c.pb.length := by
    have base : ∀ d c, (L (rf + 1 + d))[m]? = some (.join kd a b c) →
        p < c.pa.length ∧ q < c.pb.length := by
      intro d
      induction d with
      | zero =>
        intro c hs
        rw [Nat.add_zero, hsf'] at hs
        cases hs
        cases hstepf with
        | join _ _ _ g5 _ =>
          have hpa := (h.stable (show r1 ≤ rf by omega)).len_le a
          have hqb := (h.stable (show r1 ≤ rf by omega)).len_le b
          exact ⟨by omega, by omega⟩
      | succ d ih =>
        intro c hs
        obtain ⟨c1, hs1⟩ := al (rf + 1 + d) (by omega)
        obtain ⟨s', hs', hadv⟩ := (hL.adv (rf + 1 + d) (by omega)).get hs1
        rw [show rf + 1 + (d + 1) = rf + 1 + d + 1 from rfl, hs'] at hs
        cases hs
        cases hadv with
        | join _ _ g3 =>
          have := ih c1 hs1
          exact ⟨by omega, by omega⟩
    intro r c hr hs
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
    exact base d c hs
  let f : Nat → List Nat := fun r =>
    match (L r)[m]? with
    | some (.join _ _ _ c) => c.rank p q
    | _ => []
  refine no_descent RankLt rankLt_wf (fun _ _ _ h1 h2 => RankLt.trans h1 h2) f
    (rf + 1) (fun r hr => ?_) (fun r' => ?_)
  · obtain ⟨c, hs⟩ := al r (by omega)
    obtain ⟨s', hs', hadv⟩ := (hL.adv r (by omega)).get hs
    obtain ⟨fa, fb⟩ := filed r c hr hs
    cases hadv with
    | join h1 h2 =>
      simp only [f, hs, hs']
      rcases h2 p q fa fb with hb | he | hlt
      · exact absurd hb (hno (r + 1) _ (by omega) hs')
      · exact .inl he
      · exact .inr hlt
  · obtain ⟨r, hr', hr, hst⟩ := hL.step m (max r' (rf + 1))
    obtain ⟨c, hs⟩ := al r hr
    obtain ⟨s', hs', hstep⟩ := hst _ hs
    obtain ⟨fa, fb⟩ := filed r c (by omega) hs
    cases hstep with
    | join h1 h2 =>
      refine ⟨r, by omega, ?_⟩
      simp only [f, hs, hs']
      rcases h2 p q fa fb with hb | hlt
      · exact absurd hb (hno (r + 1) _ (by omega) hs')
      · exact hlt

/-- The group is all interface checks. -/
theorem IsRun.live_check (h : IsRun U σ) {ra k : Nat} {g : GoalOf R Rel}
    {L : Nat → List (Strat Rel (Ans D P))} (hk : goalAt (σ ra) k = some g)
    (hL : Line (readNeed P) σ k ra L) (hall : ∀ s ∈ L ra, s.isCheck = true) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  -- one check is not dead in infinitely many requests
  obtain ⟨m, hm, hlive⟩ := infinitely_often_fin (L ra).length
    (fun r m => ra ≤ r ∧ ∃ s, (L r)[m]? = some s ∧ s.dead (σ r) = false) (fun r' => by
      obtain ⟨r, hr', hr, -, s, hs, hdead⟩ := hL.worked r'
      obtain ⟨m, hm⟩ := List.getElem?_of_mem hs
      exact ⟨r, hr', m, by rw [← hL.length hr]; exact (List.getElem?_eq_some_iff.1 hm).1, hr,
        s, hm, hdead⟩)
  have h0 : (L ra)[m]? = some (L ra)[m] := List.getElem?_eq_getElem hm
  generalize (L ra)[m] = s0 at h0
  have hc0 := hall s0 (List.mem_of_getElem? h0)
  cases s0 with
  | span _ => cases hc0
  | copy _ _ => cases hc0
  | join _ _ _ _ => cases hc0
  | push _ _ _ _ _ _ _ _ _ => cases hc0
  | check left side other c0 =>
  have al : ∀ r, ra ≤ r → ∃ c, (L r)[m]? = some (.check left side other c) := fun r hr => by
    obtain ⟨_, hs, c, rfl⟩ := hL.along (fun _ s => ∃ c, s = Strat.check left side other c) h0
      ⟨c0, rfl⟩ (fun r s s' _ _ _ hq hadv => by
        obtain ⟨c, rfl⟩ := hq
        cases hadv
        exact ⟨_, rfl⟩) hr
    exact ⟨c, hs⟩
  -- so it is never dead
  have dead_on : ∀ r s, ra ≤ r → (L r)[m]? = some s → s.dead (σ r) = true →
      ∀ d, ∃ s', (L (r + d))[m]? = some s' ∧ s'.dead (σ (r + d)) = true := by
    intro r s hr hs hd d
    induction d with
    | zero => exact ⟨s, hs, hd⟩
    | succ d ih =>
      obtain ⟨s1, hs1, hd1⟩ := ih
      obtain ⟨s2, hs2, hadv⟩ := (hL.adv (r + d) (by omega)).get hs1
      exact ⟨s2, hs2, dead_adv hadv (h.stable (Nat.le_succ _)).answers hd1⟩
  have alive : ∀ r s, ra ≤ r → (L r)[m]? = some s → s.dead (σ r) = false := by
    intro r s hr hs
    by_contra hd
    obtain ⟨r2, hr2, -, s2, hs2, hd2⟩ := hlive r
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr2
    obtain ⟨s3, hs3, hd3⟩ := dead_on r s hr hs (by simpa using hd) d
    rw [hs2] at hs3
    cases hs3
    rw [hd2] at hd3
    cases hd3
  -- it reads its side
  have read : ∃ r1 c1, ra ≤ r1 ∧ (L r1)[m]? = some (.check left side other c1) ∧
      c1 ≠ .reading := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have rd : ∀ r, ra ≤ r → (L r)[m]? = some (.check left side other .reading) := fun r hr => by
      obtain ⟨c, hs⟩ := al r hr
      rw [hcon r c hr hs] at hs
      exact hs
    refine no_descent (· < ·) Nat.lt_wfRel.wf (fun _ _ _ h1 h2 => Nat.lt_trans h1 h2)
      (fun r => readNeed P side - (σ r).depth) ra (fun r _ => ?_) (fun r' => ?_)
    · have := (h.req.req r).depth
      omega
    · obtain ⟨r, hr', hr, hst⟩ := hL.step m r'
      obtain ⟨s', hs', hstep⟩ := hst _ (rd r hr)
      rw [rd (r + 1) (by omega)] at hs'
      cases hs'
      cases hstep with
      | check _ h2 =>
        refine ⟨r, hr', ?_⟩
        have h1 := h.req.depth_le (Nat.zero_le r)
        have h3 := h.depth
        rcases h2 rfl with hne | ⟨hd, hlt⟩
        · exact absurd rfl hne
        · omega
  obtain ⟨r1, c1, hr1, hs1, hne⟩ := read
  -- and is the same from then on
  have const : ∀ r, r1 ≤ r → (L r)[m]? = some (.check left side other c1) := by
    intro r hr
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
    induction d with
    | zero => exact hs1
    | succ d ih =>
      have hs := ih (by omega)
      obtain ⟨s', hs', hadv⟩ := (hL.adv (r1 + d) (by omega)).get hs
      cases hadv with
      | check hc =>
        rcases hc with hc | hc
        · exact absurd hc hne
        · rw [hc] at hs'
          exact hs'
  cases c1 with
  | reading => exact absurd rfl hne
  | off => exact absurd (alive r1 _ hr1 hs1) (by simp [Strat.dead])
  | opened subs =>
    have empty : ∀ j ∈ subs, ∀ r, (σ r).answers j = [] := by
      intro j hj r
      have hd : (subs.any fun j => !((σ (max r r1)).answers j).isEmpty) = false :=
        alive (max r r1) _ (by omega) (const _ (Nat.le_max_right _ _))
      have hd' := List.any_eq_false.1 hd j hj
      have he : (σ (max r r1)).answers j = [] := by
        cases hx : (σ (max r r1)).answers j with
        | nil => rfl
        | cons _ _ => rw [hx] at hd'; simp at hd'
      have := (h.stable (Nat.le_max_left r r1)).answers j
      rw [he] at this
      exact List.prefix_nil.1 this
    refine h.served_check (h.goal_le hr1 hk)
      (hL.mem r1 hr1 _ (List.mem_of_getElem? hs1)) fun j hj =>
      ⟨fun r' h' hgj => h.opened_of_settled hgj fun r' => ?_, empty j hj⟩
    obtain ⟨r, hr', hr, hfed, -⟩ := hL.worked (max r' r1)
    have hs := const (r + 1) (by omega)
    exact ⟨r, by omega, hfed _ (List.mem_of_getElem? hs) (fun j' hj' => empty j' hj' _) j hj⟩

/-- **A table that has rounds for ever is served.** -/
theorem IsRun.served_live (h : IsRun U σ) {r0 k : Nat} {g : GoalOf R Rel}
    (hk : goalAt (σ r0) k = some g) (hl : Live σ k) :
    Served D P (opened σ) (held σ) (toGoal g) := by
  obtain ⟨ra, L, hL⟩ := h.req.line k hl
  have hka : goalAt (σ ra) k = some g := by
    obtain ⟨r, hr, t, ht, -⟩ := hl ra
    obtain ⟨t0, ht0, -⟩ : ∃ t0, (σ ra).tables[k]? = some t0 ∧ True := by
      obtain ⟨gr, hgr⟩ : ∃ s, s ∈ L ra := by
        rcases hL.shape with ⟨s, hs, -⟩ | hall
        · exact ⟨s, hs⟩
        · obtain ⟨r, -, hr, -, s, hs, -⟩ := hL.worked ra
          have := hL.length hr
          cases hx : L ra with
          | nil => rw [hx] at this; rw [List.length_eq_zero_iff.1 this] at hs; cases hs
          | cons s' _ => exact ⟨s', List.mem_cons_self⟩
      obtain ⟨t0, -, -, ht0, -⟩ := hL.mem ra (Nat.le_refl _) _ hgr
      exact ⟨t0, ht0, trivial⟩
    exact h.goal_at hk ht0
  rcases hL.shape with ⟨s, hs, hlead⟩ | hall
  · obtain ⟨m, hm⟩ := List.getElem?_of_mem hs
    cases s with
    | span _ => exact h.live_span hka hL hm
    | copy _ _ => exact h.live_copy hka hL hm
    | join _ _ _ _ => exact h.live_join hka hL hm
    | push _ _ _ _ _ _ _ _ _ => cases hlead
    | check _ _ _ _ => cases hlead
  · exact h.live_check hka hL hall

/-- **A run of requests is fair.** -/
theorem IsRun.fair (hL : D.Lawful P.sorts.interp) (h : IsRun U σ) :
    Saturation.Fair D P (opened σ) (held σ) where
  ok := by
    rintro _ ⟨k, r, g, hk, rfl, -⟩
    have hg := (h.good r).base.good k g hk
    exact ⟨hg.1, hg.2.1, h.normal hk, hg.2.2⟩
  served := by
    rintro _ ⟨k, r, g, hk, rfl, ho | ho⟩
    · exact h.served_done hL hk ho
    · exact h.served_live hk ho

/-- The run does not neglect the root. -/
theorem IsRun.root_opened (h : IsRun U σ) {g : GoalOf R Rel} (h0 : goalAt (σ 0) 0 = some g) :
    toGoal g ∈ opened σ :=
  h.mem_opened h0
    (h.opened_of_settled h0 fun r' => ⟨r', Nat.le_refl _, (h.req.req r').root⟩)

end Symmetric

end RwLog
