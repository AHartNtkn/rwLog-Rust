/-
# What a machine run on one orientation keeps

`CostedRuntime.oriented` runs a machine on the input `orient` chooses and
shows the run the other way round if the choice says so. The input chosen
means what the input means, or its converse when the run is swapped
(`orient_pairs`, `orient_derives`), and it is well formed (`wf_orient`). So
what the machine has on every well-formed input, the machine run on one
orientation has (`CostedRuntime.oriented_keeps`). Two things are asked of the
machine that the list of `Keeps` does not name: that it halts on an input
exactly when it halts on the input chosen for it (`CostedRuntime.SameHalt`),
and that a side that halts and relates nothing makes `;` and `&` halt
(`Runtime.VoidSide`), since the machine may emit an answer on an input and
none on the input chosen.
-/
import RwLog.Rungs.Framework.OrientedSem
import RwLog.Rungs.Framework.Runtime
import RwLog.Rungs.Framework.Tier0
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

theorem Answer.mem_as_of {l : List A} {X : PRel} {n : Nat}
    (h : ∀ p ∈ X.as b, p.1.size ≤ n → p.2.size ≤ n → ∃ a ∈ l, p ∈ Answer.den M a) :
    ∀ p ∈ X, p.1.size ≤ n → p.2.size ≤ n → ∃ a ∈ l.map (Answer.as b), p ∈ Answer.den M a := by
  intro p hp h1 h2
  cases b
  · obtain ⟨a, ha, hpa⟩ := h p hp h1 h2
    exact ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, hpa⟩
  · obtain ⟨a, ha, hpa⟩ := h (p.2, p.1) (show ((p.2, p.1).2, (p.2, p.1).1) ∈ X from hp) h2 h1
    refine ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩
    rw [Answer.den_as]
    exact hpa

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

theorem level_shownAs (b : Bool) (t : List (Shown A)) (k n : Nat) :
    (t.map (Shown.shownAs b))[k]? = some (.level n) ↔ t[k]? = some (.level n) := by
  rw [List.getElem?_map]
  cases t[k]? with
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

theorem oriented_certifies (b : Bool) (k n : Nat) (s : C.State) :
    C.oriented.runtime.Certifies (b, s) k n ↔ C.runtime.Certifies s k n :=
  (iff_of_eq (congrArg (fun t => t[k]? = some (Shown.level n))
    (C.oriented_trace b (k + 1) s))).trans (level_shownAs b _ k n)

/-! ## Two writings of one input choose the same input -/

end CostedRuntime

theorem norm_conv_eq (q : Rel) : (RelOf.conv q).norm = normB true q := by
  rw [RelOf.norm, normB]; rfl

/-- Two queries with the same normal forms, and whose mirror images have the
same normal forms, choose the same input. -/
theorem orient_of_normB (P : Program) {q q' : Rel} (h : ∀ b, normB b q = normB b q')
    (hd : ∀ b, normB b q.dual = normB b q'.dual) : orient P q = orient P q' := by
  have e1 : q.norm = q'.norm := h false
  have e2 : (RelOf.conv q).norm = (RelOf.conv q').norm := by
    rw [norm_conv_eq, norm_conv_eq]; exact h true
  have e3 : q.dual.norm = q'.dual.norm := hd false
  have e4 : (RelOf.conv q.dual).norm = (RelOf.conv q'.dual).norm := by
    rw [norm_conv_eq, norm_conv_eq]; exact hd true
  unfold orient
  rw [e1, e2, e3, e4]

namespace CostedRuntime

variable (C : CostedRuntime)

theorem oriented_init_of_orient {P : Program} {q q' : Rel} (h : orient P q = orient P q') :
    C.oriented.runtime.init P q = C.oriented.runtime.init P q' := by
  show C.oriented.start P q = C.oriented.start P q'
  rw [oriented_start, oriented_start, h]

/-- Swapping the branches of `|` does not change the run of a machine run on
one orientation. -/
theorem oriented_orComm : C.oriented.runtime.OrComm := fun P a b n => by
  rw [C.oriented_init_of_orient (orient_of_normB P (fun w => normB_or_comm w a b)
    (fun w => normB_or_comm w a.dual b.dual))]

/-- Regrouping `|` does not change the run of a machine run on one
orientation. -/
theorem oriented_orAssoc : C.oriented.runtime.OrAssoc := fun P a b c n => by
  rw [C.oriented_init_of_orient (orient_of_normB P (fun w => normB_or_assoc w a b c)
    (fun w => normB_or_assoc w a.dual b.dual c.dual))]

/-! ## What is kept on every input -/

theorem oriented_init_emitted (P : Program) (q : Rel) (n : Nat) :
    C.oriented.runtime.emitted (C.oriented.runtime.init P q) n =
      (C.runtime.emitted (C.runtime.init (orient P q).P (orient P q).root) n).map
        (Answer.as (orient P q).swap) :=
  C.oriented_emitted _ n _

theorem oriented_init_halts (P : Program) (q : Rel) (n : Nat) :
    C.oriented.runtime.Halts (C.oriented.runtime.init P q) n ↔
      C.runtime.Halts (C.runtime.init (orient P q).P (orient P q).root) n :=
  C.oriented_halts _ n _

theorem oriented_init_certifies (P : Program) (q : Rel) (k n : Nat) :
    C.oriented.runtime.Certifies (C.oriented.runtime.init P q) k n ↔
      C.runtime.Certifies (C.runtime.init (orient P q).P (orient P q).root) k n :=
  C.oriented_certifies _ k n _

/-- A machine run on one orientation halts on an input exactly when the
machine halts on the input chosen. -/
theorem oriented_terminates (P : Program) (q : Rel) :
    C.oriented.runtime.Terminates P q ↔
      C.runtime.Terminates (orient P q).P (orient P q).root :=
  exists_congr fun n => C.oriented_init_halts P q n

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

theorem oriented_derivationGeneral (h : C.runtime.DerivationGeneral) :
    C.oriented.runtime.DerivationGeneral := by
  intro P q wf a ⟨n, ha⟩
  rw [C.oriented_init_emitted] at ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  obtain ⟨s', hs', hr⟩ := h _ _ (wf_orient wf) a' ⟨n, ha'⟩
  obtain ⟨s, hs, e⟩ := orient_derives_back hs'
  refine ⟨s, hs, ?_⟩
  rw [orient_sorts] at hr
  exact Answer.den_as_eq _ _ (Eq.trans hr (Span.den_as e P.sorts.interp))

theorem oriented_honest (h : C.runtime.HonestExhaustion) :
    C.oriented.runtime.HonestExhaustion := by
  intro P q wf n hn
  have := h _ _ (wf_orient wf) n ((C.oriented_init_halts P q n).1 hn)
  rw [orient_pairs, orient_sorts] at this
  rw [C.oriented_init_emitted]
  exact Answer.iUnion_as _ _ this

theorem oriented_honestProgress (h : C.runtime.HonestProgress) :
    C.oriented.runtime.HonestProgress := by
  intro P q wf k n hc
  have := h _ _ (wf_orient wf) k n ((C.oriented_init_certifies P q k n).1 hc)
  rw [orient_pairs, orient_sorts] at this
  rw [C.oriented_init_emitted]
  exact Answer.mem_as_of _ _ this

/-! ## Halting -/

variable (C) in
/-- The machine halts on a well-formed input exactly when it halts on the
input chosen for it. -/
def SameHalt : Prop :=
  ∀ P q, P.WellFormed q →
    (C.runtime.Terminates P q ↔ C.runtime.Terminates (orient P q).P (orient P q).root)

theorem oriented_terminatesWhere {Base : Runtime} (hS : C.SameHalt)
    (h : C.runtime.TerminatesWhere Base) : C.oriented.runtime.TerminatesWhere Base :=
  fun P q wf hb => (C.oriented_terminates P q).2 ((hS P q wf).1 (h P q wf hb))

end CostedRuntime

/-- A side that halts and relates nothing makes `;` and `&` halt, on either
side. This asks less of the side than `EmptySide`, which asks that the run
emit no answer. -/
def Runtime.VoidSide (R : Runtime) : Prop :=
  ∀ P (a b : Rel), P.WellFormed (.seq a b) →
    R.Terminates P a → P.pairs a = ∅ →
    R.Terminates P (.seq a b) ∧ R.Terminates P (.seq b a) ∧
    R.Terminates P (.and a b) ∧ R.Terminates P (.and b a)

namespace CostedRuntime

variable {C : CostedRuntime}

theorem oriented_emptySide (hS : C.SameHalt) (hh : C.runtime.HonestExhaustion)
    (hV : C.runtime.VoidSide) : C.oriented.runtime.EmptySide := by
  intro P a b wf ht he
  have wfa : P.WellFormed a := wf.seq_left
  obtain ⟨n, hn⟩ := ht
  have hp : P.pairs a = ∅ := by
    rw [oriented_honest hh P a wfa n hn]
    refine Set.eq_empty_of_forall_notMem fun p hp => ?_
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 hp
    have : x ∈ C.oriented.runtime.Answers P a := ⟨n, hx⟩
    rw [he] at this
    exact this
  have hta : C.runtime.Terminates P a :=
    (hS P a wfa).2 ((C.oriented_terminates P a).1 ⟨n, hn⟩)
  obtain ⟨h1, h2, h3, h4⟩ := hV P a b wf hta hp
  exact ⟨(C.oriented_terminates P _).2 ((hS P _ wf).1 h1),
    (C.oriented_terminates P _).2 ((hS P _ wf.seq_swap).1 h2),
    (C.oriented_terminates P _).2 ((hS P _ wf.and_of_seq).1 h3),
    (C.oriented_terminates P _).2 ((hS P _ wf.seq_swap.and_of_seq).1 h4)⟩

/-- **A machine run on one orientation keeps every property**, if on every
well-formed input the machine is sound, complete, honest and no less general
than a derivation, emits no answer an earlier one covers and halts where the
base halts; it halts on an input exactly when it halts on the input chosen
for it; a side that halts and relates nothing makes `;` and `&` halt; and
the machine run on one orientation has the two mirror properties. The mirror
properties are not asked of the machine itself. -/
theorem oriented_keeps {Base : Runtime} (hsound : C.runtime.Sound)
    (hcomplete : C.runtime.Complete) (hhonest : C.runtime.HonestExhaustion)
    (hprogress : C.runtime.HonestProgress) (hgeneral : C.runtime.DerivationGeneral)
    (hterm : C.runtime.TerminatesWhere Base) (hS : C.SameHalt)
    (hV : C.runtime.VoidSide) (hc : C.oriented.runtime.ConvTrace)
    (hd : C.oriented.runtime.DualTrace) : C.oriented.runtime.Keeps Base where
  sound := oriented_sound hsound
  pointComplete := (oriented_complete hcomplete).pointwise
  honest := oriented_honest hhonest
  honestProgress := oriented_honestProgress hprogress
  derivationGeneral := oriented_derivationGeneral hgeneral
  terminates := oriented_terminatesWhere hS hterm
  orComm := C.oriented_orComm
  orAssoc := C.oriented_orAssoc
  emptySide := oriented_emptySide hS hhonest hV
  convTrace := hc
  dualTrace := hd
  complete := oriented_complete hcomplete

end CostedRuntime

end RwLog
