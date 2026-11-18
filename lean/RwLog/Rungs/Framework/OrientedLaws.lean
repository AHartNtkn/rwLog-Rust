/-
# A machine run on one orientation has the laws

`CostedRuntime.oriented` runs a machine on the input `orient` chooses and
shows the run the other way round if the choice says so. The input chosen
means what the input means, or its converse when the run is swapped
(`orient_pairs`, `orient_derives`), and it is well formed (`wf_orient`). So
a machine that is sound, complete and honest when done on every well-formed
input is so run on one orientation (`CostedRuntime.oriented_sound`,
`oriented_complete`, `oriented_honest`, `oriented_laws`).
-/
import RwLog.Rungs.Framework.OrientedSem
import RwLog.Rungs.Framework.Runtime
import RwLog.Rungs.Framework.Tier0
import RwLog.Rungs.Framework.Finishing
import RwLog.SpanLayer.Bridge

namespace RwLog

/-! ## The other way round, or as it is -/

/-- A relation the other way round, or as it is. -/
def PRel.as (b : Bool) (X : PRel) : PRel := if b then X.inv else X

/-- An answer the other way round, or as it is. -/
def Answer.as {A : Type} [Answer A] (b : Bool) (a : A) : A := if b then Answer.swap a else a

theorem Answer.den_as {A : Type} [Answer A] (M : Interp) (b : Bool) (a : A) :
    Answer.den M (Answer.as b a) = (Answer.den M a).as b := by
  cases b
  · rfl
  · exact Answer.den_swap M a

theorem PRel.as_as (b : Bool) (X : PRel) : (X.as b).as b = X := by
  cases b <;> rfl

theorem PRel.as_subset {b : Bool} {X Y : PRel} : X.as b ⊆ Y.as b ↔ X ⊆ Y := by
  cases b
  · exact Iff.rfl
  · exact ⟨fun h p hp => h (a := (p.2, p.1)) hp, fun h p hp => h hp⟩

theorem PRel.as_eq_empty {b : Bool} {X : PRel} : X.as b = ∅ ↔ X = ∅ := by
  cases b
  · exact Iff.rfl
  · constructor
    · intro h
      ext p
      exact ⟨fun hp => (Set.eq_empty_iff_forall_notMem.1 h (p.2, p.1) hp).elim, fun hp => hp.elim⟩
    · rintro rfl; rfl

section as

variable {A : Type} [Answer A] (M : Interp) (b : Bool)

theorem Answer.as_sub {a : A} {X : PRel} (h : Answer.den M a ⊆ X.as b) :
    Answer.den M (Answer.as b a) ⊆ X := by
  rw [Answer.den_as]
  exact PRel.as_subset.1 (by rw [PRel.as_as]; exact h)

theorem Answer.sub_as {a : A} {Y : PRel} (h : Y.as b ⊆ Answer.den M a) :
    Y ⊆ Answer.den M (Answer.as b a) := by
  rw [Answer.den_as]
  exact PRel.as_subset.1 (by rw [PRel.as_as]; exact h)

theorem Answer.den_as_eq {a : A} {Y : PRel} (h : Answer.den M a = Y.as b) :
    Answer.den M (Answer.as b a) = Y := by
  rw [Answer.den_as, h, PRel.as_as]

theorem Answer.as_sub_as {x y : A}
    (h : Answer.den M (Answer.as b y) ⊆ Answer.den M (Answer.as b x)) :
    Answer.den M y ⊆ Answer.den M x := by
  rw [Answer.den_as, Answer.den_as] at h
  exact PRel.as_subset.1 h

theorem Answer.iUnion_as {l : List A} {X : PRel} (h : X.as b = ⋃ a ∈ l, Answer.den M a) :
    X = ⋃ a ∈ l.map (Answer.as b), Answer.den M a := by
  have hX : X = PRel.as b (⋃ a ∈ l, Answer.den M a) := by rw [← h, PRel.as_as]
  rw [hX]
  ext p
  constructor
  · intro hp
    have : ∃ a ∈ l, p ∈ (Answer.den M a).as b := by
      cases b
      · obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 hp
        exact ⟨a, ha, h⟩
      · obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (show (p.2, p.1) ∈ ⋃ a ∈ l, Answer.den M a from hp)
        exact ⟨a, ha, h⟩
    obtain ⟨a, ha, hpa⟩ := this
    exact Set.mem_iUnion₂.2 ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, by rw [Answer.den_as]; exact hpa⟩
  · intro hp
    obtain ⟨_, hm, hpa⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
    rw [Answer.den_as] at hpa
    cases b
    · show p ∈ ⋃ a ∈ l, Answer.den M a
      exact Set.mem_iUnion₂.2 ⟨a, ha, hpa⟩
    · show (p.2, p.1) ∈ ⋃ a ∈ l, Answer.den M a
      exact Set.mem_iUnion₂.2 ⟨a, ha, hpa⟩

end as

/-! ## What the input chosen means -/

theorem mem_pairs_iff (P : Program) (q : Rel) (p : GTerm × GTerm) :
    p ∈ P.pairs q ↔ ∃ G ∈ GD P q, p ∈ G.at P.sorts.interp := by
  unfold ProgramOf.pairs
  rw [ProgramOf.semAt_eq, sem_eq_sUnion_gd]
  constructor
  · rintro ⟨S, ⟨G, hG, h⟩, hM⟩; exact ⟨G, hG, S, h, hM⟩
  · rintro ⟨G, hG, S, h, hM⟩; exact ⟨S, ⟨G, hG, h⟩, hM⟩

/-- **The input chosen to run relates the pairs the input relates**, the other
way round when what the run shows is to be swapped. -/
theorem orient_pairs (P : Program) (q : Rel) :
    (orient P q).P.pairs (orient P q).root = (P.pairs q).as (orient P q).swap := by
  ext p
  rw [mem_pairs_iff, orient_gd, orient_sorts]
  cases hb : (orient P q).swap
  · simp only [Bool.false_eq_true, ↓reduceIte, PRel.as]
    exact (mem_pairs_iff P q p).symm
  · simp only [↓reduceIte, PRel.as]
    show _ ↔ (p.2, p.1) ∈ P.pairs q
    rw [mem_pairs_iff]
    constructor
    · rintro ⟨_, ⟨G, hG, rfl⟩, h⟩
      exact ⟨G, hG, by rw [at_inv] at h; exact h⟩
    · rintro ⟨G, hG, h⟩
      exact ⟨G.inv, ⟨G, hG, rfl⟩, by rw [at_inv]; exact h⟩

/-- Two spans one of which denotes the other's ground relation, the other way
round or as it is, relate the same pairs that way. -/
theorem Span.den_as {s s' : Span} {b : Bool} (h : s'.den = if b then s.den.inv else s.den)
    (M : Interp) : (Answer.den M s' : PRel) = (Answer.den M s : PRel).as b := by
  show s'.denAt M = (s.denAt M).as b
  rw [Span.denAt_eq, Span.denAt_eq, h]
  cases b
  · rfl
  · exact at_inv _ _

/-- A span the input derives is, the other way round or as it is, a span the
input chosen derives. -/
theorem orient_derives {P : Program} {q : Rel} {s : Span} (h : Derives P q s) :
    ∃ s', Derives (orient P q).P (orient P q).root s' ∧
      s'.den = if (orient P q).swap then s.den.inv else s.den := by
  refine derives_iff_derivesG.2 ⟨?_, ?_⟩
  · show _ ∈ GD _ _
    rw [orient_gd]
    cases (orient P q).swap
    · exact h.derivesG
    · exact ⟨_, h.derivesG, rfl⟩
  · cases (orient P q).swap
    · exact s.den_nonempty
    · exact GRel.inv_nonempty.2 s.den_nonempty

/-- A span the input chosen derives is, the other way round or as it is, a
span the input derives. -/
theorem orient_derives_back {P : Program} {q : Rel} {s' : Span}
    (h : Derives (orient P q).P (orient P q).root s') :
    ∃ s, Derives P q s ∧ s'.den = if (orient P q).swap then s.den.inv else s.den := by
  have hg : s'.den ∈ GD (orient P q).P (orient P q).root := h.derivesG
  rw [orient_gd] at hg
  cases hb : (orient P q).swap
  · rw [hb] at hg
    obtain ⟨s, hs, e⟩ := derives_iff_derivesG.2 ⟨hg, s'.den_nonempty⟩
    exact ⟨s, hs, e.symm⟩
  · rw [hb] at hg
    obtain ⟨G, hG, e⟩ := hg
    have hn : G.Nonempty := GRel.inv_nonempty.1 (e ▸ s'.den_nonempty)
    obtain ⟨s, hs, rfl⟩ := derives_iff_derivesG.2 ⟨hG, hn⟩
    exact ⟨s, hs, e.symm⟩

/-! ## What the run shows -/

section shown

variable {A : Type} [Answer A]

theorem emits_shownAs (b : Bool) (t : List (Shown A)) :
    (t.map (Shown.shownAs b)).flatMap Shown.emits = (t.flatMap Shown.emits).map (Answer.as b) := by
  rw [List.flatMap_map, List.map_flatMap]
  congr 1
  funext x
  have h0 : (Answer.as false : A → A) = id := rfl
  have h1 : (Answer.as true : A → A) = Answer.swap := rfl
  cases b <;> cases x <;> simp [Shown.shownAs, Shown.swap, Shown.emits, h0, h1]

theorem final_shownAs (b : Bool) (t : List (Shown A)) :
    (∃ fin, (t.map (Shown.shownAs b)).getLast? = some (.final fin)) ↔
      ∃ fin, t.getLast? = some (.final fin) := by
  rw [List.getLast?_map]
  cases t.getLast? with
  | none => simp
  | some x => cases b <;> cases x <;> simp [Shown.shownAs, Shown.swap]

end shown

namespace CostedRuntime

variable (C : CostedRuntime)

theorem oriented_emitted (b : Bool) (n : Nat) (s : C.State) :
    C.oriented.runtime.emitted (b, s) n = (C.runtime.emitted s n).map (Answer.as b) :=
  (C.oriented.runtime.emitted_eq_flatMap_trace n (b, s)).trans
    ((congrArg (fun t => t.flatMap Shown.emits) (C.oriented_trace b n s)).trans
      ((emits_shownAs b _).trans
        (congrArg (List.map (Answer.as b)) (C.runtime.emitted_eq_flatMap_trace n s).symm)))

theorem oriented_halts (b : Bool) (n : Nat) (s : C.State) :
    C.oriented.runtime.Halts (b, s) n ↔ C.runtime.Halts s n :=
  (C.oriented.runtime.halts_iff_trace (s := (b, s)) (n := n)).trans
    ((iff_of_eq (congrArg (fun t => ∃ fin, t.getLast? = some (Shown.final fin))
      (C.oriented_trace b n s))).trans
      ((final_shownAs b _).trans (C.runtime.halts_iff_trace (s := s) (n := n)).symm))

/-! ## The laws on every input -/

theorem oriented_init_emitted (P : Program) (q : Rel) (n : Nat) :
    C.oriented.runtime.emitted (C.oriented.runtime.init P q) n =
      (C.runtime.emitted (C.runtime.init (orient P q).P (orient P q).root) n).map
        (Answer.as (orient P q).swap) :=
  C.oriented_emitted _ n _

theorem oriented_init_halts (P : Program) (q : Rel) (n : Nat) :
    C.oriented.runtime.Halts (C.oriented.runtime.init P q) n ↔
      C.runtime.Halts (C.runtime.init (orient P q).P (orient P q).root) n :=
  C.oriented_halts _ n _

variable {C}

theorem oriented_sound (h : C.runtime.Sound) : C.oriented.runtime.Sound := by
  intro P q wf n a ha
  rw [C.oriented_init_emitted] at ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  have := h _ _ (wf_orient wf) n a' ha'
  rw [orient_pairs, orient_sorts] at this
  exact Answer.as_sub _ _ this

theorem oriented_complete (h : C.runtime.Complete) : C.oriented.runtime.Complete := by
  intro P q wf s hs
  obtain ⟨s', hs', e⟩ := orient_derives hs
  have hden := Span.den_as e P.sorts.interp
  rcases h _ _ (wf_orient wf) s' hs' with hd | ⟨n, a', ha', hc⟩
  · left
    rw [orient_sorts] at hd
    exact PRel.as_eq_empty.1 (hden.symm.trans hd)
  · right
    refine ⟨n, Answer.as (orient P q).swap a', ?_, ?_⟩
    · rw [C.oriented_init_emitted]
      exact List.mem_map.2 ⟨a', ha', rfl⟩
    · rw [orient_sorts] at hc
      have hc' : (Answer.den P.sorts.interp s : PRel).as (orient P q).swap ⊆
          Answer.den P.sorts.interp a' := fun p hp => hc ((Set.ext_iff.1 hden p).2 hp)
      exact Answer.sub_as _ _ hc'

theorem oriented_honest (h : C.runtime.HonestExhaustion) :
    C.oriented.runtime.HonestExhaustion := by
  intro P q wf n hn
  have := h _ _ (wf_orient wf) n ((C.oriented_init_halts P q n).1 hn)
  rw [orient_pairs, orient_sorts] at this
  rw [C.oriented_init_emitted]
  exact Answer.iUnion_as _ _ this

/-- A machine that reports no level reports none run on one orientation. -/
theorem oriented_silent (h : C.runtime.Silent) : C.oriented.runtime.Silent := by
  intro P q wf n x hx k
  have hx' : x ∈ (C.runtime.trace (C.runtime.init (orient P q).P (orient P q).root) n).map
      (Shown.shownAs (orient P q).swap) :=
    (C.oriented_trace (orient P q).swap n _) ▸ hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx'
  have hy' := h _ _ (wf_orient wf) n y hy
  cases y with
  | answers as => exact fun e => by cases hb : (orient P q).swap <;> rw [hb] at e <;> cases e
  | level j => exact absurd rfl (hy' j)
  | final as => exact fun e => by cases hb : (orient P q).swap <;> rw [hb] at e <;> cases e

/-- **A machine that has the laws has them run on one orientation.** -/
theorem oriented_laws (hs : C.runtime.Sound) (hc : C.runtime.Complete)
    (hh : C.runtime.HonestExhaustion) : C.oriented.runtime.Laws :=
  ⟨oriented_sound hs, (oriented_complete hc).pointwise, oriented_honest hh⟩

end CostedRuntime

end RwLog
