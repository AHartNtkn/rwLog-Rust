/-
# Every group of a table that has rounds for ever works for ever

A run is a sequence of states, each a request after the one before
(`Requests`). Of a table that has a round in infinitely many requests
(`HadRound`): the list of its groups stops shrinking, and then every one of
its groups works in infinitely many requests (`Requests.lines`). `Line` is a
group through time: its strategies, each later than itself before (`SAdv`),
all of them worked again and again (`SStep`) with the tables they read
settled, and never all dead; and the group has a span, a call, a union or a
join, or is all interface checks.

That every group works is the balance (`Balanced`, `Turns.lean`): in a round
a group worked, or it stands as it stood while a group below it rose. A
group that never works again keeps its level, and what the groups hold
below that level then grows in every round and cannot grow for ever.

Nothing here is about a kernel.
-/
import RwLog.Lib.Sequences
import RwLog.Rungs.Symmetric.Turns

namespace RwLog

namespace Symmetric

variable {S N A : Type} {need : N → Nat}

/-- A run by requests from a state where no table has groups yet. -/
structure Requests (need : N → Nat) (σ : Nat → StateOf S N A) : Prop where
  req : ∀ r, Req need (σ r) (σ (r + 1))
  start : ∀ (k : Nat) (t : Table S N A), (σ 0).tables[k]? = some t → t.groups = none

/-- The table at `k` had its round in the request after the state `r`. -/
def HadRound (σ : Nat → StateOf S N A) (r k : Nat) : Prop :=
  ∃ t, (σ (r + 1)).tables[k]? = some t ∧ t.stamp = (σ (r + 1)).round

variable {σ : Nat → StateOf S N A}

theorem Requests.stable (h : Requests need σ) {r r' : Nat} (hr : r ≤ r') :
    Stable (σ r) (σ r') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => exact Stable.refl _
  | succ d ih => exact (ih (by omega)).trans (h.req (r + d)).stable

theorem Requests.depth_le (h : Requests need σ) {r r' : Nat} (hr : r ≤ r') :
    (σ r).depth ≤ (σ r').depth := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (ih (by omega)) (h.req (r + d)).depth

theorem Requests.round (h : Requests need σ) (r : Nat) : (σ r).round = (σ 0).round + r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [(h.req r).round, ih]; omega

/-- The groups of every table are shaped, throughout. -/
theorem Requests.shaped (h : Requests need σ) : ∀ (r k : Nat) (t : Table S N A)
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
  adv : ∀ r, r0 ≤ r → Pointwise (SAdv (σ r).len) (L r) (L (r + 1))
  shape : (∃ s ∈ L r0, s.lead = true) ∨ ∀ s ∈ L r0, s.isCheck = true
  worked : ∀ r', ∃ r, r' ≤ r ∧ r0 ≤ r ∧
    Pointwise (SStep need (σ r).len (σ r).depth (σ (r + 1)).depth) (L r) (L (r + 1)) ∧
    (∀ s ∈ L (r + 1), SFed (σ (r + 1)) s) ∧ ∃ s ∈ L r, s.dead (σ r) = false

theorem Line.length {k r0 : Nat} {L : Nat → List (Strat N A)} (hL : Line need σ k r0 L)
    {r : Nat} (hr : r0 ≤ r) : (L r).length = (L r0).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => rfl
  | succ d ih => exact ((hL.adv (r0 + d) (by omega)).1).symm.trans (ih (by omega))

/-- What holds of the strategy at one place of the group at the start and
is kept by a strategy moving on holds of it throughout. -/
theorem Line.along {k r0 : Nat} {L : Nat → List (Strat N A)} (hL : Line need σ k r0 L)
    (Q : Nat → Strat N A → Prop) {m : Nat} {s0 : Strat N A} (h0 : (L r0)[m]? = some s0)
    (hQ : Q r0 s0)
    (hstep : ∀ r s s', r0 ≤ r → (L r)[m]? = some s → (L (r + 1))[m]? = some s' → Q r s →
      SAdv (σ r).len s s' → Q (r + 1) s') {r : Nat} (hr : r0 ≤ r) :
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
theorem Requests.step (h : Requests need σ) (k r : Nat) {t t' : Table S N A}
    {G G' : List (Group N A)} (ht : (σ r).tables[k]? = some t) (hg : t.groups = some G)
    (ht' : (σ (r + 1)).tables[k]? = some t') (hg' : t'.groups = some G') :
    G'.length ≤ G.length ∧ (G'.length = G.length →
      Pointwise (GrAdv (σ r).len) G G' ∧ (¬ HadRound σ r k → G' = G) ∧
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
      Pointwise.refl (SAdv.refl _) gr.strats) _, fun _ => rfl, ?_⟩⟩
    rintro ⟨u, hu, hsu⟩
    rw [ht'] at hu
    cases hu
    exact absurd hsu hs

/-- **Every group of a table that has rounds for ever works for ever.** From
some state on the table keeps its groups, and each of them is a line: a
group that did not work in a round stands as it stood while a lower one
rose, and the groups below a level can rise only so often before they have
all passed it. -/
theorem Requests.lines (h : Requests need σ) (k : Nat)
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
        Pointwise (GrAdv (σ r).len) (groupsAt (σ r) k) (groupsAt (σ (r + 1)) k) ∧
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
      Pointwise (GrAdv (σ r).len) (groupsAt (σ r) k) (groupsAt (σ (r + 1)) k) ∧
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
      obtain ⟨-, -, ht | ⟨-, k', gr0', gr1', e0', e1', hlt, hrise⟩⟩ :=
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
  refine ⟨?_, ?_, ?_, ?_⟩
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
    obtain ⟨r, hr, hr0', hround, gr0, gr1, e0, e1, hstp, hfed⟩ := hwork r'
    refine ⟨r, hr, hr0', ?_, ?_, ?_⟩
    · simp only [e0, e1, Option.map_some, Option.getD_some]
      exact hstp
    · simp only [e1, Option.map_some, Option.getD_some]
      exact hfed
    · simp only [e0, Option.map_some, Option.getD_some]
      exact ((hst r hr0').2.2 hround m gr0 gr1 e0 e1).1

/-- **A table that has rounds for ever has a group that works for ever.** -/
theorem Requests.line (h : Requests need σ) (k : Nat)
    (hinf : ∀ r', ∃ r, r' ≤ r ∧ HadRound σ r k) : ∃ r0 L, Line need σ k r0 L := by
  obtain ⟨r0, hpos, hl⟩ := h.lines k hinf
  exact ⟨r0, _, hl 0 hpos⟩

end Symmetric

end RwLog
