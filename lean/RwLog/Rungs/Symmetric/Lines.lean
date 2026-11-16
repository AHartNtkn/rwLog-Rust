/-
# Every group of a table that has rounds for ever works for ever

A run is a sequence of states, each a request after the one before
(`Requests`). Of a table that has a round in infinitely many requests
(`HadRound`): the list of its groups stops shrinking, and then every one of
its groups works in infinitely many requests (`Requests.lines`). `Line` is a
group through time: its strategies, each later than itself before (`SAdv`),
each of them working again and again (`SStep`), the tables they read fed
again and again (`Fed`), and never all dead; and the group has a span, a call, a
union or a join, or is all interface checks.

That every group has its turn is the balance (`Balanced`, `Turns.lean`): in
a round a group worked, or it stands as it stood while a group below it
rose. A group that never works again keeps its level, and what the groups
hold below that level then grows in every round and cannot grow for ever.
When a group works, each of its strategies has worked or owes less than it
did (`OStep`), and it owes the same when the group does not work. What a
strategy owes cannot fall for ever, so it works again.

Nothing here is about a kernel.
-/
import RwLog.Lib.Sequences
import RwLog.Rungs.Symmetric.Turns

namespace RwLog

namespace Symmetric

variable {S N A : Type} {need : N → Nat} {Rc : RaceSem S N A}

/-- A run by requests from a state where no table has groups yet. -/
structure Requests (need : N → Nat) (Rc : RaceSem S N A) (σ : Nat → StateOf S N A) : Prop where
  req : ∀ r, Req need Rc (σ r) (σ (r + 1))
  start : ∀ (k : Nat) (t : Table S N A), (σ 0).tables[k]? = some t → t.groups = none

/-- The table at `k` had its round in the request after the state `r`. -/
def HadRound (σ : Nat → StateOf S N A) (r k : Nat) : Prop :=
  ∃ t, (σ (r + 1)).tables[k]? = some t ∧ t.stamp = (σ (r + 1)).round

variable {σ : Nat → StateOf S N A}

theorem Requests.stable (h : Requests need Rc σ) {r r' : Nat} (hr : r ≤ r') :
    Stable (σ r) (σ r') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => exact Stable.refl _
  | succ d ih => exact (ih (by omega)).trans (h.req (r + d)).stable

theorem Requests.depth_le (h : Requests need Rc σ) {r r' : Nat} (hr : r ≤ r') :
    (σ r).depth ≤ (σ r').depth := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (ih (by omega)) (h.req (r + d)).depth

theorem Requests.round (h : Requests need Rc σ) (r : Nat) : (σ r).round = (σ 0).round + r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [(h.req r).round, ih]; omega

/-- The groups of every table are shaped, throughout. -/
theorem Requests.shaped (h : Requests need Rc σ) : ∀ (r k : Nat) (t : Table S N A)
    (gs : List (Group N A)), (σ r).tables[k]? = some t → t.groups = some gs → Shaped gs
  | 0, k, t, gs, ht, hg => by rw [h.start k t ht] at hg; cases hg
  | r + 1, k, t', gs, ht', hg => by
    cases ht : (σ r).tables[k]? with
    | none => rw [((h.req r).born k t' ht' ht).2] at hg; cases hg
    | some t =>
      by_cases hs : t'.stamp = (σ (r + 1)).round
      · obtain ⟨gs', e, hsh⟩ := ((h.req r).turn k t t' ht ht' hs).shaped
          fun gs0 h0 => Requests.shaped h r k t gs0 ht h0
        rw [hg] at e
        cases e
        exact hsh
      · rw [(h.req r).groups k t t' ht ht' (.inr hs)] at hg
        exact Requests.shaped h r k t gs ht hg

/-- A group of a table through time, from the state `r0` on: `L r` is its
strategies in the state `r`. -/
structure Line (need : N → Nat) (σ : Nat → StateOf S N A) (k r0 : Nat)
    (L : Nat → List (Strat N A)) : Prop where
  mem : ∀ r, r0 ≤ r → ∀ s ∈ L r, ∃ (t : Table S N A) (gs : List (Group N A)) (gr : Group N A),
    (σ r).tables[k]? = some t ∧ t.groups = some gs ∧ gr ∈ gs ∧ s ∈ gr.strats
  adv : ∀ r, r0 ≤ r → Pointwise (SAdv) (L r) (L (r + 1))
  shape : (∃ s ∈ L r0, s.lead = true) ∨ ∀ s ∈ L r0, s.isCheck = true
  worked : ∀ r', ∃ r, r' ≤ r ∧ r0 ≤ r ∧
    (∀ s ∈ L (r + 1), Fed (σ r) (σ (r + 1)) s) ∧ ∃ s ∈ L r, s.dead (σ r) = false
  stepped : ∀ m, m < (L r0).length → ∀ r', ∃ r, r' ≤ r ∧ r0 ≤ r ∧ ∃ s s',
    (L r)[m]? = some s ∧ (L (r + 1))[m]? = some s' ∧
    SStep need (σ r).len (σ r).isDone (σ r).depth (σ (r + 1)).depth s s'

theorem Line.length {k r0 : Nat} {L : Nat → List (Strat N A)} (hL : Line need σ k r0 L)
    {r : Nat} (hr : r0 ≤ r) : (L r).length = (L r0).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => rfl
  | succ d ih => exact ((hL.adv (r0 + d) (by omega)).1).symm.trans (ih (by omega))

/-- The strategy at each place of the group works again and again. -/
theorem Line.step {k r0 : Nat} {L : Nat → List (Strat N A)} (hL : Line need σ k r0 L)
    (m r' : Nat) : ∃ r, r' ≤ r ∧ r0 ≤ r ∧ ∀ s, (L r)[m]? = some s → ∃ s',
      (L (r + 1))[m]? = some s' ∧
      SStep need (σ r).len (σ r).isDone (σ r).depth (σ (r + 1)).depth s s' := by
  by_cases hm : m < (L r0).length
  · obtain ⟨r, hr', hr, s, s', hs, hs', hstp⟩ := hL.stepped m hm r'
    refine ⟨r, hr', hr, fun s1 hs1 => ?_⟩
    rw [hs] at hs1
    cases hs1
    exact ⟨s', hs', hstp⟩
  · refine ⟨max r' r0, Nat.le_max_left _ _, Nat.le_max_right _ _, fun s hs => ?_⟩
    have := (List.getElem?_eq_some_iff.1 hs).1
    rw [hL.length (Nat.le_max_right _ _)] at this
    exact absurd this hm

/-- What holds of the strategy at one place of the group at the start and
is kept by a strategy moving on holds of it throughout. -/
theorem Line.along {k r0 : Nat} {L : Nat → List (Strat N A)} (hL : Line need σ k r0 L)
    (Q : Nat → Strat N A → Prop) {m : Nat} {s0 : Strat N A} (h0 : (L r0)[m]? = some s0)
    (hQ : Q r0 s0)
    (hstep : ∀ r s s', r0 ≤ r → (L r)[m]? = some s → (L (r + 1))[m]? = some s' → Q r s →
      SAdv s s' → Q (r + 1) s') {r : Nat} (hr : r0 ≤ r) :
    ∃ s, (L r)[m]? = some s ∧ Q r s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => exact ⟨s0, h0, hQ⟩
  | succ d ih =>
    obtain ⟨s, hs, hq⟩ := ih (by omega)
    obtain ⟨s', hs', hadv⟩ := (hL.adv (r0 + d) (by omega)).get hs
    exact ⟨s', hs', hstep (r0 + d) s s' (by omega) hs hs' hq hadv⟩

/-- What one request does to the groups `G` of a table that has groups:
there are no more of them after, and if there are as many, each is itself
later; they are the same if the table had no round, and if it had one, none
of them was all dead and the round was balanced. -/
theorem Requests.step (h : Requests need Rc σ) (k r : Nat) {t t' : Table S N A}
    {G G' : List (Group N A)} (ht : (σ r).tables[k]? = some t) (hg : t.groups = some G)
    (ht' : (σ (r + 1)).tables[k]? = some t') (hg' : t'.groups = some G') :
    G'.length ≤ G.length ∧ (G'.length = G.length →
      Pointwise (GrAdv) G G' ∧ (¬ HadRound σ r k → G' = G) ∧
      (HadRound σ r k → ∀ (m : Nat) (gr0 gr1 : Group N A), G[m]? = some gr0 →
        G'[m]? = some gr1 → (∃ s ∈ gr0.strats, s.dead (σ r) = false) ∧
          Balanced need (σ r) (σ (r + 1)) G G' gr0 gr1)) := by
  by_cases hs : t'.stamp = (σ (r + 1)).round
  · obtain ⟨gs0, gs1, p, h1, -, h3, h4, -, h6⟩ := (h.req r).turn k t t' ht ht' hs
    obtain rfl : G = gs0 := h1 G hg
    have e' : G' = gs1.filter p := by rw [hg'] at h3; exact h3
    subst e'
    have hlen : (gs1.filter p).length ≤ G.length := by
      rw [h4.1]; exact List.length_filter_le _ _
    refine ⟨hlen, fun hl => ?_⟩
    have hf : gs1.filter p = gs1 :=
      (List.filter_sublist).eq_of_length (by rw [hl, h4.1])
    have hall : ∀ gr ∈ gs1, p gr = true := List.filter_eq_self.1 hf
    rw [hf]
    exact ⟨h4.imp fun _ _ hr => hr.1, fun hno => absurd ⟨t', ht', hs⟩ hno,
      fun _ m gr0 gr1 e0 e1 => ⟨(h4.2 m gr0 gr1 e0 e1).2.1 (hall gr1 (List.mem_of_getElem? e1)),
        h6 m gr0 gr1 e0 e1⟩⟩
  · have e := (h.req r).groups k t t' ht ht' (.inr hs)
    rw [hg, hg'] at e
    cases e
    refine ⟨Nat.le_refl _, fun _ => ⟨Pointwise.refl (fun gr =>
      Pointwise.refl SAdv.refl gr.strats) _, fun _ => rfl, ?_⟩⟩
    rintro ⟨u, hu, hsu⟩
    rw [ht'] at hu
    cases hu
    exact absurd hsu hs

/-- **Every group of a table that has rounds for ever works for ever.** From
some state on the table keeps its groups, and each of them is a line: a
group that did not work in a round stands as it stood while a lower one
rose, and the groups below a level can rise only so often before they have
all passed it. -/
theorem Requests.lines (h : Requests need Rc σ) (k : Nat)
    (hinf : ∀ r', ∃ r, r' ≤ r ∧ HadRound σ r k) :
    ∃ r0, 0 < (groupsAt (σ r0) k).length ∧ ∀ m, m < (groupsAt (σ r0) k).length →
      Line need σ k r0 fun r => (((groupsAt (σ r) k)[m]?).map (·.strats)).getD [] := by
  -- the table is there from some state on
  obtain ⟨r1, -, t1, ht1, -⟩ := hinf 0
  have hex : ∀ r, r1 + 1 ≤ r → ∃ t, (σ r).tables[k]? = some t := fun r hr => by
    obtain ⟨t, ht, -⟩ := h.stable hr k t1 ht1
    exact ⟨t, ht⟩
  -- and has groups from its next round on
  obtain ⟨r2, hr2, t2', ht2', hs2⟩ := hinf (r1 + 1)
  have hgr : ∀ r, r2 + 1 ≤ r → ∃ t, (σ r).tables[k]? = some t ∧
      t.groups = some (groupsAt (σ r) k) := by
    intro r hr
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
    have key : ∀ (r : Nat) (t : Table S N A) (gs : List (Group N A)),
        (σ r).tables[k]? = some t → t.groups = some gs → gs = groupsAt (σ r) k := by
      intro r t gs ht hg
      simp only [groupsAt, ht, hg, Option.getD_some]
    induction d with
    | zero =>
      obtain ⟨t2, ht2⟩ := hex r2 hr2
      obtain ⟨gs', e, -⟩ := ((h.req r2).turn k t2 t2' ht2 ht2' hs2).shaped
        fun gs0 h0 => h.shaped r2 k t2 gs0 ht2 h0
      exact ⟨t2', ht2', by rw [e, key _ _ _ ht2' e]⟩
    | succ d ih =>
      obtain ⟨t, ht, hg⟩ := ih (by omega)
      obtain ⟨t', ht'⟩ := hex (r2 + 1 + d + 1) (by omega)
      refine ⟨t', ht', ?_⟩
      by_cases hs : t'.stamp = (σ (r2 + 1 + d + 1)).round
      · obtain ⟨gs', e, -⟩ := ((h.req (r2 + 1 + d)).turn k t t' ht ht' hs).shaped
          fun gs0 h0 => h.shaped _ k t gs0 ht h0
        exact e.trans (congrArg some (key _ _ _ ht' e))
      · have e := (h.req (r2 + 1 + d)).groups k t t' ht ht' (.inr hs)
        rw [hg] at e
        exact e.trans (congrArg some (key _ _ _ ht' e))
  have hstep : ∀ r, r2 + 1 ≤ r →
      (groupsAt (σ (r + 1)) k).length ≤ (groupsAt (σ r) k).length ∧
      ((groupsAt (σ (r + 1)) k).length = (groupsAt (σ r) k).length →
        Pointwise (GrAdv) (groupsAt (σ r) k) (groupsAt (σ (r + 1)) k) ∧
        (¬ HadRound σ r k → groupsAt (σ (r + 1)) k = groupsAt (σ r) k) ∧
        (HadRound σ r k → ∀ (m : Nat) (gr0 gr1 : Group N A),
          (groupsAt (σ r) k)[m]? = some gr0 → (groupsAt (σ (r + 1)) k)[m]? = some gr1 →
          (∃ s ∈ gr0.strats, s.dead (σ r) = false) ∧
            Balanced need (σ r) (σ (r + 1)) (groupsAt (σ r) k) (groupsAt (σ (r + 1)) k)
              gr0 gr1)) := fun r hr => by
    obtain ⟨t, ht, hg⟩ := hgr r hr
    obtain ⟨t', ht', hg'⟩ := hgr (r + 1) (by omega)
    exact h.step k r ht hg ht' hg'
  -- the number of its groups stops falling
  obtain ⟨r0, hr0, hconst⟩ := eventually_const (fun r => (groupsAt (σ r) k).length) (r2 + 1)
    fun r hr => (hstep r hr).1
  have hlen : ∀ r, r0 ≤ r → (groupsAt (σ (r + 1)) k).length = (groupsAt (σ r) k).length :=
    fun r hr => by
      have h1 := hconst r hr
      have h2 := hconst (r + 1) (by omega)
      rw [h1, h2]
  have hst : ∀ r, r0 ≤ r →
      Pointwise (GrAdv) (groupsAt (σ r) k) (groupsAt (σ (r + 1)) k) ∧
      (¬ HadRound σ r k → groupsAt (σ (r + 1)) k = groupsAt (σ r) k) ∧
      (HadRound σ r k → ∀ (m : Nat) (gr0 gr1 : Group N A),
        (groupsAt (σ r) k)[m]? = some gr0 → (groupsAt (σ (r + 1)) k)[m]? = some gr1 →
        (∃ s ∈ gr0.strats, s.dead (σ r) = false) ∧
          Balanced need (σ r) (σ (r + 1)) (groupsAt (σ r) k) (groupsAt (σ (r + 1)) k)
            gr0 gr1) := fun r hr => (hstep r (by omega)).2 (hlen r hr)
  -- no level falls
  have hmono : ∀ r, r0 ≤ r → ∀ (m : Nat) (gr0 gr1 : Group N A),
      (groupsAt (σ r) k)[m]? = some gr0 → (groupsAt (σ (r + 1)) k)[m]? = some gr1 →
      gr0.level ≤ gr1.level := by
    intro r hr m gr0 gr1 e0 e1
    by_cases hround : HadRound σ r k
    · exact ((hst r hr).2.2 hround m gr0 gr1 e0 e1).2.1
    · rw [(hst r hr).2.1 hround, e0] at e1
      cases e1
      exact Nat.le_refl _
  have hpos : 0 < (groupsAt (σ r0) k).length := by
    obtain ⟨t, ht, hg⟩ := hgr r0 hr0
    obtain ⟨⟨gr, hgr', -⟩, -⟩ := h.shaped r0 k t _ ht hg
    exact List.length_pos_of_mem hgr'
  refine ⟨r0, hpos, fun m hm => ?_⟩
  have hat : ∀ r, r0 ≤ r → ∃ gr, (groupsAt (σ r) k)[m]? = some gr := fun r hr => by
    have := hconst r hr
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  -- the group at `m` works for ever
  have hwork : ∀ r', ∃ r, r' ≤ r ∧ r0 ≤ r ∧ HadRound σ r k ∧ ∃ (gr0 gr1 : Group N A),
      (groupsAt (σ r) k)[m]? = some gr0 ∧ (groupsAt (σ (r + 1)) k)[m]? = some gr1 ∧
      Tried need (σ r) (σ (r + 1)) gr0 gr1 := by
    intro r'
    by_contra hno
    have hno' : ∀ r, r' ≤ r → r0 ≤ r → HadRound σ r k → ∀ (gr0 gr1 : Group N A),
        (groupsAt (σ r) k)[m]? = some gr0 → (groupsAt (σ (r + 1)) k)[m]? = some gr1 →
        ¬ Tried need (σ r) (σ (r + 1)) gr0 gr1 :=
      fun r h1 h2 h3 gr0 gr1 e0 e1 ht => hno ⟨r, h1, h2, h3, gr0, gr1, e0, e1, ht⟩
    -- its level stays
    have hlev : ∀ r, max r' r0 ≤ r → ∀ (gr gr1 : Group N A),
        (groupsAt (σ (max r' r0)) k)[m]? = some gr → (groupsAt (σ r) k)[m]? = some gr1 →
        gr1.level = gr.level := by
      intro r hr
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
      induction d with
      | zero =>
        intro gr gr1 e e1
        rw [Nat.add_zero, e] at e1
        cases e1
        rfl
      | succ d ih =>
        intro gr gr1 e e1
        obtain ⟨gr0, e0⟩ := hat (max r' r0 + d) (by omega)
        have h0 := ih (by omega) gr gr0 e e0
        by_cases hround : HadRound σ (max r' r0 + d) k
        · obtain ⟨-, -, ht | ⟨heq, -⟩⟩ :=
            (hst (max r' r0 + d) (by omega)).2.2 hround m gr0 gr1 e0 e1
          · exact absurd ht (hno' _ (by omega) (by omega) hround gr0 gr1 e0 e1)
          · omega
        · have e1' : (groupsAt (σ (max r' r0 + d + 1)) k)[m]? = some gr1 := e1
          rw [(hst (max r' r0 + d) (by omega)).2.1 hround, e0] at e1'
          cases e1'
          exact h0
    obtain ⟨grm, em⟩ := hat (max r' r0) (by omega)
    -- so what the groups have below it only grows, and grows in every round
    have hsum_le : ∀ r, max r' r0 ≤ r →
        ((groupsAt (σ r) k).map fun gr => min gr.level grm.level).sum ≤
          ((groupsAt (σ (r + 1)) k).map fun gr => min gr.level grm.level).sum := by
      intro r hr
      refine sum_le_sum_of_getElem (by simp [hlen r (by omega)]) fun i a b ha hb => ?_
      rw [List.getElem?_map] at ha hb
      cases e0 : (groupsAt (σ r) k)[i]? with
      | none => rw [e0] at ha; cases ha
      | some gr0 =>
        cases e1 : (groupsAt (σ (r + 1)) k)[i]? with
        | none => rw [e1] at hb; cases hb
        | some gr1 =>
          rw [e0] at ha
          rw [e1] at hb
          cases ha
          cases hb
          have := hmono r (by omega) i gr0 gr1 e0 e1
          show min gr0.level grm.level ≤ min gr1.level grm.level
          omega
    have hsum_lt : ∀ r, max r' r0 ≤ r → HadRound σ r k →
        ((groupsAt (σ r) k).map fun gr => min gr.level grm.level).sum <
          ((groupsAt (σ (r + 1)) k).map fun gr => min gr.level grm.level).sum := by
      intro r hr hround
      obtain ⟨gr0, e0⟩ := hat r (by omega)
      obtain ⟨gr1, e1⟩ := hat (r + 1) (by omega)
      have hl0 := hlev r hr grm gr0 em e0
      obtain ⟨-, -, ht | ⟨-, -, k', gr0', gr1', e0', e1', hlt, hrise⟩⟩ :=
        (hst r (by omega)).2.2 hround m gr0 gr1 e0 e1
      · exact absurd ht (hno' r (by omega) (by omega) hround gr0 gr1 e0 e1)
      · refine sum_lt_sum_of_getElem (by simp [hlen r (by omega)]) (fun i a b ha hb => ?_)
          ⟨k', min gr0'.level grm.level, min gr1'.level grm.level, by simp [e0'], by simp [e1'],
            by omega⟩
        rw [List.getElem?_map] at ha hb
        cases e0 : (groupsAt (σ r) k)[i]? with
        | none => rw [e0] at ha; cases ha
        | some gr0 =>
          cases e1 : (groupsAt (σ (r + 1)) k)[i]? with
          | none => rw [e1] at hb; cases hb
          | some gr1 =>
            rw [e0] at ha
            rw [e1] at hb
            cases ha
            cases hb
            have := hmono r (by omega) i gr0 gr1 e0 e1
            show min gr0.level grm.level ≤ min gr1.level grm.level
            omega
    have hbound : ∀ r, r0 ≤ r →
        ((groupsAt (σ r) k).map fun gr => min gr.level grm.level).sum ≤
          (groupsAt (σ r0) k).length * grm.level := fun r hr => by
      rw [← hconst r hr]
      exact sum_map_le_mul fun x _ => Nat.min_le_right _ _
    obtain ⟨r3, hr3, hflat⟩ := eventually_const
      (fun r => (groupsAt (σ r0) k).length * grm.level -
        ((groupsAt (σ r) k).map fun gr => min gr.level grm.level).sum) (max r' r0)
      fun r hr => by
        have := hsum_le r hr
        omega
    obtain ⟨r, hr, hround⟩ := hinf r3
    have h1 := hflat r hr
    have h2 := hflat (r + 1) (by omega)
    have h3 := hsum_lt r (by omega) hround
    have h4 := hbound (r + 1) (by omega)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr s hs
    obtain ⟨gr, hgr'⟩ := hat r hr
    obtain ⟨t, ht, hg⟩ := hgr r (by omega)
    simp only [hgr', Option.map_some, Option.getD_some] at hs
    exact ⟨t, _, gr, ht, hg, List.mem_of_getElem? hgr', hs⟩
  · intro r hr
    obtain ⟨gr, e⟩ := hat r hr
    obtain ⟨gr', e'⟩ := hat (r + 1) (by omega)
    simp only [e, e', Option.map_some, Option.getD_some]
    exact (hst r hr).1.2 m gr gr' e e'
  · obtain ⟨gr, e⟩ := hat r0 (Nat.le_refl _)
    obtain ⟨t, ht, hg⟩ := hgr r0 hr0
    simp only [e, Option.map_some, Option.getD_some]
    exact (h.shaped r0 k t _ ht hg).2 gr (List.mem_of_getElem? e)
  · intro r'
    obtain ⟨r, hr, hr0', hround, gr0, gr1, e0, e1, -, hfed⟩ := hwork r'
    refine ⟨r, hr, hr0', ?_, ?_⟩
    · simp only [e1, Option.map_some, Option.getD_some]
      exact hfed
    · simp only [e0, Option.map_some, Option.getD_some]
      exact ((hst r hr0').2.2 hround m gr0 gr1 e0 e1).1
  · -- a strategy that never worked again would owe less and less for ever
    intro q hq r'
    obtain ⟨grs, es⟩ := hat r0 (Nat.le_refl _)
    simp only [es, Option.map_some, Option.getD_some] at hq
    have hlenq : ∀ r, r0 ≤ r → ∀ gr : Group N A, (groupsAt (σ r) k)[m]? = some gr →
        gr.strats.length = grs.strats.length := by
      intro r hr
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
      induction d with
      | zero =>
        intro gr e
        rw [Nat.add_zero, es] at e
        cases e
        rfl
      | succ d ih =>
        intro gr e
        obtain ⟨gr0, e0⟩ := hat (r0 + d) (by omega)
        exact ((hst (r0 + d) (by omega)).1.2 m gr0 gr e0 e).1.symm.trans (ih (by omega) gr0 e0)
    by_contra hno
    have hno' : ∀ r, r' ≤ r → r0 ≤ r → ∀ (gr0 gr1 : Group N A) (s s' : Strat N A),
        (groupsAt (σ r) k)[m]? = some gr0 → (groupsAt (σ (r + 1)) k)[m]? = some gr1 →
        gr0.strats[q]? = some s → gr1.strats[q]? = some s' →
        ¬ SStep need (σ r).len (σ r).isDone (σ r).depth (σ (r + 1)).depth s s' :=
      fun r h1 h2 gr0 gr1 s s' e0 e1 hs hs' hstp => hno ⟨r, h1, h2, s, s', by
        simp only [e0, Option.map_some, Option.getD_some]
        exact hs, by
        simp only [e1, Option.map_some, Option.getD_some]
        exact hs', hstp⟩
    have hdown : ∀ r, max r' r0 ≤ r → ∀ (gr0 gr1 : Group N A),
        (groupsAt (σ r) k)[m]? = some gr0 → (groupsAt (σ (r + 1)) k)[m]? = some gr1 →
        gr1.owed.getD q 0 ≤ gr0.owed.getD q 0 ∧
          (Tried need (σ r) (σ (r + 1)) gr0 gr1 → gr1.owed.getD q 0 < gr0.owed.getD q 0) := by
      intro r hr gr0 gr1 e0 e1
      have hq0 : q < gr0.strats.length := by rw [hlenq r (by omega) gr0 e0]; exact hq
      have hq1 : q < gr1.strats.length := by rw [hlenq (r + 1) (by omega) gr1 e1]; exact hq
      have htr : Tried need (σ r) (σ (r + 1)) gr0 gr1 →
          gr1.owed.getD q 0 < gr0.owed.getD q 0 := fun ht =>
        (ht.1.2 q _ _ (List.getElem?_eq_getElem hq0) (List.getElem?_eq_getElem hq1)).resolve_left
          (hno' r (by omega) (by omega) gr0 gr1 _ _ e0 e1 (List.getElem?_eq_getElem hq0)
            (List.getElem?_eq_getElem hq1))
      refine ⟨?_, htr⟩
      by_cases hround : HadRound σ r k
      · obtain ⟨-, -, ht | ⟨-, ho, -⟩⟩ := (hst r (by omega)).2.2 hround m gr0 gr1 e0 e1
        · exact Nat.le_of_lt (htr ht)
        · rw [ho]
      · rw [(hst r (by omega)).2.1 hround, e0] at e1
        cases e1
        exact Nat.le_refl _
    obtain ⟨r3, hr3, hflat⟩ := eventually_const
      (fun r => (((groupsAt (σ r) k)[m]?).map fun gr => gr.owed.getD q 0).getD 0) (max r' r0)
      fun r hr => by
        obtain ⟨gr0, e0⟩ := hat r (by omega)
        obtain ⟨gr1, e1⟩ := hat (r + 1) (by omega)
        simp only [e0, e1, Option.map_some, Option.getD_some]
        exact (hdown r hr gr0 gr1 e0 e1).1
    obtain ⟨r, hr, -, -, gr0, gr1, e0, e1, htr⟩ := hwork r3
    have h1 := hflat r hr
    have h2 := hflat (r + 1) (by omega)
    simp only [e0, e1, Option.map_some, Option.getD_some] at h1 h2
    have := (hdown r (by omega) gr0 gr1 e0 e1).2 htr
    omega

/-- **A table that has rounds for ever has a group that works for ever.** -/
theorem Requests.line (h : Requests need Rc σ) (k : Nat)
    (hinf : ∀ r', ∃ r, r' ≤ r ∧ HadRound σ r k) : ∃ r0 L, Line need σ k r0 L := by
  obtain ⟨r0, hpos, hl⟩ := h.lines k hinf
  exact ⟨r0, _, hl 0 hpos⟩

/-- **A table that has rounds for ever and a race with a final verdict at
some depth completes.** The race begins at depth zero in the first round of
the table and is asked again whenever the table has had as many rounds as
the race has spent and needs for its next ask. An ask it can pay for moves
it one depth further. An ask it cannot pay for it gives up, and it is then
allowed more than it gave up before and less than the ask costs, which
cannot happen for ever at one depth. So it is asked at the depth of the
final verdict. -/
theorem Requests.race_done (h : Requests need Rc σ) (k : Nat)
    (hinf : ∀ r', ∃ r, r' ≤ r ∧ HadRound σ r k) {g : GoalOf S N} {n : Nat}
    (hg : ∀ (r : Nat) (t : Table S N A), (σ r).tables[k]? = some t → t.goal = g)
    (hh : Rc.has g = true) (hf : Rc.final g n) :
    ∃ (r : Nat) (t : Table S N A), (σ r).tables[k]? = some t ∧ t.done = true := by
  by_contra hnd
  have hnd' : ∀ (r : Nat) (t : Table S N A), (σ r).tables[k]? = some t → t.done = false :=
    fun r t ht => by
      cases hd : t.done with
      | false => rfl
      | true => exact absurd ⟨r, t, ht, hd⟩ hnd
  -- a table with groups has a race that stands no deeper than the final verdict
  have inv : ∀ (r : Nat) (t : Table S N A), (σ r).tables[k]? = some t →
      t.groups = none ∨ ∃ rc, t.race = some rc ∧ rc.depth ≤ n := by
    intro r
    induction r with
    | zero => exact fun t ht => .inl (h.start k t ht)
    | succ r ih =>
      intro t' ht'
      cases ht : (σ r).tables[k]? with
      | none => exact .inl ((h.req r).born k t' ht' ht).2
      | some t =>
        by_cases hs : t'.stamp = (σ (r + 1)).round
        · obtain ⟨-, ha⟩ := (h.req r).asked k t t' ht ht' hs
          rw [hg r t ht, hh] at ha
          cases hgr : t.groups with
          | none =>
            rcases ha ⟨0, 0, 0⟩ (by simp [hgr]) with h1 | h1 | ⟨c, h1, h2⟩ | ⟨l, h1, -⟩
            · exact .inr ⟨_, h1.1, Nat.zero_le _⟩
            · rw [hnd' _ t' ht'] at h1; cases h1
            · refine .inr ⟨_, h1, ?_⟩
              rcases Nat.eq_zero_or_pos n with h0 | h0
              · subst h0; exact absurd hf h2
              · exact h0
            · exact .inr ⟨_, h1, Nat.zero_le _⟩
          | some gs =>
            obtain ⟨rc, hrc, hle⟩ := (ih t ht).resolve_left (by rw [hgr]; exact fun e => by cases e)
            rcases ha rc (by simp [hgr, hrc]) with h1 | h1 | ⟨c, h1, h2⟩ | ⟨l, h1, -⟩
            · exact .inr ⟨_, h1.1, hle⟩
            · rw [hnd' _ t' ht'] at h1; cases h1
            · refine .inr ⟨_, h1, ?_⟩
              rcases Nat.lt_or_eq_of_le hle with hlt | he
              · exact hlt
              · rw [he] at h2; exact absurd hf h2
            · exact .inr ⟨_, h1, hle⟩
        · rw [(h.req r).groups k t t' ht ht' (.inr hs), ((h.req r).race k t t' ht ht' (.inr hs)).1]
          exact ih t ht
  -- from some state on the table has groups
  obtain ⟨r0, hpos, hl⟩ := h.lines k hinf
  have hL := hl 0 hpos
  have hgr : ∀ r, r0 ≤ r → ∃ (t : Table S N A) (gs : List (Group N A)),
      (σ r).tables[k]? = some t ∧ t.groups = some gs := by
    intro r hr
    obtain ⟨r1, -, hr1, -, s1, hs1, -⟩ := hL.worked 0
    have hlen : 0 < ((((groupsAt (σ r) k)[0]?).map (·.strats)).getD []).length := by
      rw [hL.length hr, ← hL.length hr1]
      exact List.length_pos_of_mem hs1
    obtain ⟨s, hs⟩ := List.exists_mem_of_length_pos hlen
    obtain ⟨t, gs, -, ht, hgs, -⟩ := hL.mem r hr s hs
    exact ⟨t, gs, ht, hgs⟩
  -- the race is asked again, and cannot stand deeper for ever
  have main : ∀ d e m r (t : Table S N A) (rc : Race), r0 ≤ r → (σ r).tables[k]? = some t →
      t.race = some rc → rc.depth ≤ n → n - rc.depth ≤ d → Rc.cost g rc.depth - rc.gaveUp ≤ e →
      rc.spent + max 1 (2 * rc.gaveUp) - t.rounds ≤ m → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ihd =>
      intro e
      induction e using Nat.strong_induction_on with
      | _ e ihe =>
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ihm =>
        intro r t rc hr ht hrc hle hd he hm
        -- the next round of the table
        classical
        let r2 := Nat.find (hinf r)
        obtain ⟨hr2, t', ht', hs'⟩ := Nat.find_spec (hinf r)
        have keep : ∀ j, r ≤ j → j ≤ r2 → ∃ tj, (σ j).tables[k]? = some tj ∧
            tj.race = t.race ∧ tj.rounds = t.rounds := by
          intro j hj
          obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hj
          induction e with
          | zero => exact fun _ => ⟨t, ht, rfl, rfl⟩
          | succ e ihe =>
            intro hj2
            obtain ⟨tj, htj, e1, e2⟩ := ihe (by omega) (by omega)
            obtain ⟨tj', htj', -⟩ := (h.req (r + e)).stable k tj htj
            have hno : ¬ (r ≤ r + e ∧ HadRound σ (r + e) k) :=
              Nat.find_min (hinf r) (show r + e < r2 by omega)
            have hs : tj'.stamp ≠ (σ (r + e + 1)).round := fun hs =>
              hno ⟨Nat.le_add_right _ _, tj', htj', hs⟩
            obtain ⟨f1, f2⟩ := (h.req (r + e)).race k tj tj' htj htj' (.inr hs)
            exact ⟨tj', htj', f1.trans e1, f2.trans e2⟩
        obtain ⟨t2, ht2, e1, e2⟩ := keep r2 hr2 (Nat.le_refl _)
        obtain ⟨t2', gs2, ht2', hgs2⟩ := hgr r2 (by omega)
        rw [ht2] at ht2'
        cases ht2'
        obtain ⟨hrd, ha⟩ := (h.req r2).asked k t2 t' ht2 ht' hs'
        rcases ha rc (by simp [hgs2, e1, hrc]) with h1 | h1 | ⟨c, h1, h2⟩ | ⟨l, h1, h2, h3⟩
        · exact ihm (rc.spent + max 1 (2 * rc.gaveUp) - t'.rounds) (by omega) (r2 + 1) t' rc
            (by omega) ht' h1.1 hle hd he (Nat.le_refl _)
        · rw [hnd' _ t' ht'] at h1; cases h1
        · rw [hg r2 t2 ht2] at h2
          have hlt : rc.depth < n := by
            rcases Nat.lt_or_eq_of_le hle with hlt | he
            · exact hlt
            · rw [he] at h2; exact absurd hf h2
          exact ihd (n - (rc.depth + 1)) (by omega) _ _ (r2 + 1) t' _ (by omega) ht' h1 hlt
            (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        · rw [hg r2 t2 ht2] at h3
          exact ihe (Rc.cost g rc.depth - l) (by omega) _ (r2 + 1) t' _ (by omega) ht' h1 hle hd
            (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨t, gs, ht, hgs⟩ := hgr r0 (Nat.le_refl _)
  rcases inv r0 t ht with hn | ⟨rc, hrc, hle⟩
  · rw [hgs] at hn; cases hn
  · exact main _ _ _ r0 t rc (Nat.le_refl _) ht hrc hle (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _)

/-! ## The members of a union

A union gives a round to one member at a time, the one that has been fed
least of those that still need one. A member that needs a round is passed
over only for one that has been fed no more than it has, and that member is
then fed more. So the members that have been fed no more than it cannot be
fed for ever while it waits: it has its round again and again. -/

/-- What the tables given have been fed, each counted up to `B + 1`. -/
def fedSum (st : StateOf S N A) (B : Nat) (M : List Nat) : Nat :=
  (M.map fun q => min (st.fedAt q) (B + 1)).sum

theorem fedSum_le (st : StateOf S N A) (B : Nat) : ∀ M : List Nat,
    fedSum st B M ≤ M.length * (B + 1)
  | [] => by simp [fedSum]
  | q :: M => by
    have := fedSum_le st B M
    simp only [fedSum, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at this ⊢
    omega

theorem fedSum_mono {st st' : StateOf S N A} (h : ∀ q, st.fedAt q ≤ st'.fedAt q) (B : Nat) :
    ∀ M : List Nat, fedSum st B M ≤ fedSum st' B M
  | [] => Nat.le_refl _
  | q :: M => by
    have := fedSum_mono h B M
    have := h q
    simp only [fedSum, List.map_cons, List.sum_cons] at *
    omega

theorem fedSum_lt {st st' : StateOf S N A} (h : ∀ q, st.fedAt q ≤ st'.fedAt q) {B : Nat} :
    ∀ {M : List Nat} {q : Nat}, q ∈ M → st.fedAt q < st'.fedAt q → st.fedAt q ≤ B →
      fedSum st B M < fedSum st' B M
  | x :: M, q, hq, h1, h2 => by
    have hm := fedSum_mono h B M
    have hx := h x
    rcases List.mem_cons.1 hq with rfl | hq
    · simp only [fedSum, List.map_cons, List.sum_cons] at *
      omega
    · have := fedSum_lt h hq h1 h2
      simp only [fedSum, List.map_cons, List.sum_cons] at *
      omega

theorem map_fst_of_subAdv {a b : List (Nat × Nat)} (h : Pointwise SubAdv a b) :
    b.map Prod.fst = a.map Prod.fst := by
  apply List.ext_getElem?
  intro n
  simp only [List.getElem?_map]
  cases ha : a[n]? with
  | none =>
    have : b[n]? = none := by
      rw [List.getElem?_eq_none_iff] at ha ⊢
      rw [← h.1]
      exact ha
    rw [this]
  | some x =>
    obtain ⟨y, hy, e⟩ := h.get ha
    rw [hy]
    simp [e.1]

/-- **A member of a union whose group works for ever needs no round again
and again.** -/
theorem Requests.union_settled (h : Requests need Rc σ) {k ra m : Nat}
    {L : Nat → List (Strat N A)} (hL : Line need σ k ra L) {M : List Nat}
    (al : ∀ r, ra ≤ r → ∃ subs, (L r)[m]? = some (.copy false subs) ∧ subs.map Prod.fst = M)
    {j : Nat} (hj : j ∈ M) (r' : Nat) : ∃ r, r' ≤ r ∧ Settled (σ (r + 1)) j := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have fedmono : ∀ r q, (σ r).fedAt q ≤ (σ (r + 1)).fedAt q := fun r q => ((h.req r).fed q).1
  have const : ∀ r, max r' ra ≤ r → (σ (r + 1)).fedAt j = (σ r).fedAt j := fun r hr => by
    have hf := (h.req r).fed j
    by_contra hne
    exact hcon r (by omega) (hf.2 (by omega))
  have hB : ∀ d, (σ (max r' ra + d)).fedAt j = (σ (max r' ra)).fedAt j := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih => rw [← Nat.add_assoc, const _ (by omega), ih]
  generalize hBd : (σ (max r' ra)).fedAt j = B at hB
  refine no_descent (· < ·) Nat.lt_wfRel.wf (fun _ _ _ h1 h2 => Nat.lt_trans h1 h2)
    (fun r => M.length * (B + 1) - fedSum (σ r) B M) (max r' ra) (fun r hr => ?_) (fun r0 => ?_)
  · have h1 := fedSum_mono (fedmono r) B M
    have h2 := fedSum_le (σ (r + 1)) B M
    show _ - _ = _ - _ ∨ _ - _ < _ - _
    omega
  · obtain ⟨r, hr0, hr, hfed, -⟩ := hL.worked (max r0 (max r' ra))
    obtain ⟨subs, hs, hmap⟩ := al (r + 1) (by omega)
    have hF := hfed _ (List.mem_of_getElem? hs)
    obtain ⟨p, hp, hpj⟩ : ∃ p ∈ subs, p.1 = j := by
      rw [← hmap] at hj
      obtain ⟨p, hp, e⟩ := List.mem_map.1 hj
      exact ⟨p, hp, e⟩
    rcases hF p hp with hs' | ⟨q, hq, e1, e2⟩
    · exact absurd (hpj ▸ hs') (hcon r (by omega))
    · refine ⟨r, by omega, ?_⟩
      have hqM : q.1 ∈ M := by
        rw [← hmap]
        exact List.mem_map.2 ⟨q, hq, rfl⟩
      have hBr : (σ (r + 1)).fedAt j = B := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show max r' ra ≤ r + 1 by omega)
        rw [hd]
        exact hB d
      rw [hpj, hBr] at e2
      have h1 := fedSum_lt (fedmono r) hqM e1 e2
      have h2 := fedSum_le (σ (r + 1)) B M
      show _ - _ < _ - _
      omega

end Symmetric

end RwLog
