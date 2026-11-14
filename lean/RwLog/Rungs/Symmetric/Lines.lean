/-
# A table that has rounds for ever has a group that works for ever

A run is a sequence of states, each a request after the one before
(`Requests`). Of a table that has a round in infinitely many requests
(`HadRound`): the list of its groups stops shrinking, and then one of its
groups works in infinitely many requests. `Line` is that group through
time: its strategies, each later than itself before (`SAdv`), all of them
worked again and again (`SStep`) with the tables they read settled, and
never all dead; and the group has a span, a call, a union or a join, or is
all interface checks.

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

/-- What one request does to the groups `G` of a table that has groups:
there are no more of them after, and if there are as many, each is itself
later, and if the table had its round one of them worked. -/
theorem Requests.step (h : Requests need σ) (k r : Nat) {t t' : Table S N A}
    {G G' : List (Group N A)} (ht : (σ r).tables[k]? = some t) (hg : t.groups = some G)
    (ht' : (σ (r + 1)).tables[k]? = some t') (hg' : t'.groups = some G') :
    G'.length ≤ G.length ∧ (G'.length = G.length →
      Pointwise (GrAdv (σ r).len) G G' ∧ (HadRound σ r k → ∃ (m : Nat) (gr0 gr1 : Group N A),
        G[m]? = some gr0 ∧ G'[m]? = some gr1 ∧
        GrStep need (σ r).len (σ r).depth (σ (r + 1)).depth gr0 gr1 ∧
        (∀ s ∈ gr1.strats, SFed (σ (r + 1)) s) ∧ ∃ s ∈ gr0.strats, s.dead (σ r) = false)) := by
  by_cases hs : t'.stamp = (σ (r + 1)).round
  · obtain ⟨gs0, gs1, p, h1, -, h3, h4, h5⟩ := (h.req r).turn k t t' ht ht' hs
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
    refine ⟨h4.imp fun _ _ hr => hr.1, fun _ => ?_⟩
    rcases h5 with h5 | ⟨m, gr0, gr1, e0, e1, hst, hfed⟩
    · obtain ⟨⟨gr, hgr, -⟩, -⟩ := h.shaped r k t G ht hg
      rw [h5] at hgr
      cases hgr
    · exact ⟨m, gr0, gr1, e0, e1, hst, hfed,
        (h4.2 m gr0 gr1 e0 e1).2.1 (hall gr1 (List.mem_of_getElem? e1))⟩
  · have e := (h.req r).groups k t t' ht ht' (.inr hs)
    rw [hg, hg'] at e
    cases e
    refine ⟨Nat.le_refl _, fun _ => ⟨Pointwise.refl (fun gr =>
      Pointwise.refl (SAdv.refl _) gr.strats) _, ?_⟩⟩
    rintro ⟨u, hu, hsu⟩
    rw [ht'] at hu
    cases hu
    exact absurd hsu hs

/-- **A table that has rounds for ever has a group that works for ever.** -/
theorem Requests.line (h : Requests need σ) (k : Nat)
    (hinf : ∀ r', ∃ r, r' ≤ r ∧ HadRound σ r k) : ∃ r0 L, Line need σ k r0 L := by
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
        (HadRound σ r k → ∃ (m : Nat) (gr0 gr1 : Group N A),
          (groupsAt (σ r) k)[m]? = some gr0 ∧ (groupsAt (σ (r + 1)) k)[m]? = some gr1 ∧
          GrStep need (σ r).len (σ r).depth (σ (r + 1)).depth gr0 gr1 ∧
          (∀ s ∈ gr1.strats, SFed (σ (r + 1)) s) ∧
          ∃ s ∈ gr0.strats, s.dead (σ r) = false)) := fun r hr => by
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
  -- one of them works for ever
  obtain ⟨m, hm, hwork⟩ := infinitely_often_fin (groupsAt (σ r0) k).length
    (fun r m => r0 ≤ r ∧ ∃ (gr0 gr1 : Group N A),
      (groupsAt (σ r) k)[m]? = some gr0 ∧ (groupsAt (σ (r + 1)) k)[m]? = some gr1 ∧
      GrStep need (σ r).len (σ r).depth (σ (r + 1)).depth gr0 gr1 ∧
      (∀ s ∈ gr1.strats, SFed (σ (r + 1)) s) ∧ ∃ s ∈ gr0.strats, s.dead (σ r) = false)
    (fun r' => by
      obtain ⟨r, hr, hround⟩ := hinf (max r' r0)
      have hr0' : r0 ≤ r := by omega
      obtain ⟨m, gr0, gr1, e0, e1, rest⟩ :=
        ((hstep r (by omega)).2 (hlen r hr0')).2 hround
      refine ⟨r, by omega, m, ?_, hr0', gr0, gr1, e0, e1, rest⟩
      have := (List.getElem?_eq_some_iff.1 e0).1
      have := hconst r hr0'
      omega)
  have hat : ∀ r, r0 ≤ r → ∃ gr, (groupsAt (σ r) k)[m]? = some gr := fun r hr => by
    have := hconst r hr
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  refine ⟨r0, fun r => (((groupsAt (σ r) k)[m]?).map (·.strats)).getD [], ?_, ?_, ?_, ?_⟩
  · intro r hr s hs
    obtain ⟨gr, hgr'⟩ := hat r hr
    obtain ⟨t, ht, hg⟩ := hgr r (by omega)
    simp only [hgr', Option.map_some, Option.getD_some] at hs
    exact ⟨t, _, gr, ht, hg, List.mem_of_getElem? hgr', hs⟩
  · intro r hr
    obtain ⟨gr, e⟩ := hat r hr
    obtain ⟨gr', e'⟩ := hat (r + 1) (by omega)
    simp only [e, e', Option.map_some, Option.getD_some]
    exact ((hstep r (by omega)).2 (hlen r hr)).1.2 m gr gr' e e'
  · obtain ⟨gr, e⟩ := hat r0 (Nat.le_refl _)
    obtain ⟨t, ht, hg⟩ := hgr r0 hr0
    simp only [e, Option.map_some, Option.getD_some]
    exact (h.shaped r0 k t _ ht hg).2 gr (List.mem_of_getElem? e)
  · intro r'
    obtain ⟨r, hr, hr0', gr0, gr1, e0, e1, hst, hfed, hdead⟩ := hwork r'
    refine ⟨r, hr, hr0', ?_, ?_, ?_⟩
    · simp only [e0, e1, Option.map_some, Option.getD_some]
      exact hst
    · simp only [e1, Option.map_some, Option.getD_some]
      exact hfed
    · simp only [e0, Option.map_some, Option.getD_some]
      exact hdead

end Symmetric

end RwLog
