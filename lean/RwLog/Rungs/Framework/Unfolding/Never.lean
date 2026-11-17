/-
# A name the unfolding race never finishes

The unfolding race answers for a goal only when it has read every derivation
of the goal whole (`Whole`). Some names are never read whole: `c := id | c ; id`
derives the identity at every depth, so at every depth a derivation of it runs
into a node that was not read. An answer of a final unfolding therefore owes
nothing to such a name: it is an answer of the goal in the program where the
name derives nothing (`light_of_final`).

The derivations of `c` cannot be told apart by what they relate, so "not read
whole" cannot be said of one of them. It is said of a derivation of a larger
program instead. `Tags P c ξ τ`: for every `j` the span `ξ j` relates what
every derivation of `c` relates, carries the constraint `τ j` on its store,
and added to the body of `c` it derives nothing the body did not derive
already. The program with `ξ j` added (`ext`) derives the same from a call as
from its body in `P`, so the race reads its derivations whole too
(`olaws_ext`). A derivation through `c` gives one of that program for every
`j`, with `τ j` on the store of all it relates (`pump`); the constraints are
all different, a store is finite, and only finitely many relations are read
whole at a depth (`gr_finite`), so one of them was not read whole.
-/
import RwLog.Rungs.Framework.Unfolding.Races
import Mathlib.Data.Set.Finite.Lattice

namespace RwLog

open Goals Answer

/-- The program with the body of one name replaced. -/
def ProgramOf.withBody (P : Program) (c : Name) (b : Rel) : Program :=
  { P with defs := (c, b) :: P.defs }

@[simp] theorem ProgramOf.withBody_self (P : Program) (c : Name) (b : Rel) :
    (P.withBody c b).body c = b := by
  simp [ProgramOf.body, ProgramOf.withBody]

theorem ProgramOf.withBody_ne (P : Program) {c n : Name} (b : Rel) (h : n ≠ c) :
    (P.withBody c b).body n = P.body n := by
  simp [ProgramOf.body, ProgramOf.withBody, List.lookup_cons, beq_eq_false_iff_ne.2 h]

/-- A program derives what another does, when it derives from its own bodies
what it derives from the other's. -/
theorem DerivesG.mono {P P' : Program}
    (h : ∀ n G, DerivesG P' (P.body n) G → DerivesG P' (P'.body n) G) {e : Rel} {G : GRel}
    (hd : DerivesG P e G) : DerivesG P' e G := by
  induction hd with
  | span s => exact .span s
  | orl _ ih => exact .orl ih
  | orr _ ih => exact .orr ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | conv _ ih => exact .conv ih
  | call _ ih => exact .call (h _ _ ih)

/-- A derivation in the program where `c` derives nothing is one in the
program where `h` derives nothing, when the body of `h` needs `c`. -/
theorem Derives.withBody_zero {P : Program} {c h : Name}
    (hneed : ∀ s, ¬ Derives (P.withBody c .zero) (P.body h) s) {e : Rel} {s : Span}
    (hd : Derives (P.withBody c .zero) e s) : Derives (P.withBody h .zero) e s := by
  induction hd with
  | span s => exact .span s
  | orl _ ih => exact .orl ih
  | orr _ ih => exact .orr ih
  | seq _ _ hc ih₁ ih₂ => exact .seq ih₁ ih₂ hc
  | and _ _ hc ih₁ ih₂ => exact .and ih₁ ih₂ hc
  | conv _ ih => exact .conv ih
  | @call n s hb ih =>
    by_cases hc : n = c
    · subst hc
      rw [ProgramOf.withBody_self] at ih
      cases ih
    · rw [ProgramOf.withBody_ne _ _ hc] at hb ih
      by_cases hh : n = h
      · subst hh
        exact absurd hb (hneed s)
      · refine .call ?_
        rw [ProgramOf.withBody_ne _ _ hh]
        exact ih

namespace Unfold

/-! ## Finitely many relations are read whole -/

theorem seqAll_finite : ∀ L : List (Set GRel), (∀ X ∈ L, X.Finite) → (RwLog.seqAll L).Finite
  | [], _ => Set.finite_singleton _
  | X :: L, h => by
    show (Set.image2 GRel.comp X (RwLog.seqAll L)).Finite
    rw [← Set.iUnion_image_left]
    exact Set.Finite.biUnion (h X (by simp)) fun a _ =>
      Set.Finite.image _ (seqAll_finite L fun Y hY => h Y (by simp [hY]))

theorem andAll_finite : ∀ L : List (Set GRel), (∀ X ∈ L, X.Finite) → (RwLog.andAll L).Finite
  | [], _ => Set.finite_singleton _
  | X :: L, h => by
    show (Set.image2 GRel.meet X (RwLog.andAll L)).Finite
    rw [← Set.iUnion_image_left]
    exact Set.Finite.biUnion (h X (by simp)) fun a _ =>
      Set.Finite.image _ (andAll_finite L fun Y hY => h Y (by simp [hY]))

/-- The derivations of a node read whole at a depth are finitely many
relations. -/
theorem gr_finite (P : Program) : ∀ (d : Nat) (e : Rel), (GR P d e).Finite
  | 0, e => by simp
  | d + 1, e => by
    cases hv : e.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      rw [gr_span P hv, (gd_laws P).span]
      exact Set.finite_singleton _
    | call m f =>
      cases hb : Charged.bodyOf P e with
      | none =>
        have e' : GR P (d + 1) e = ∅ := by simp only [GR, hv, hb]
        rw [e']
        exact Set.finite_empty
      | some b =>
        rw [gr_call P hv hb]
        exact gr_finite P d b
    | union xs =>
      rw [gr_union P hv]
      exact Set.Finite.subset
        (Set.Finite.biUnion (List.finite_toSet xs) fun x _ => gr_finite P d x)
        fun G ⟨x, hx, hG⟩ => Set.mem_biUnion (show x ∈ {x | x ∈ xs} from hx) hG
    | chain xs =>
      rw [gr_chain P hv]
      exact seqAll_finite _ fun X hX => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hX
        exact gr_finite P d x
    | meet xs =>
      rw [gr_meet P hv]
      exact andAll_finite _ fun X hX => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hX
        exact gr_finite P d x

/-! ## Tags -/

/-- For every `j` a span that stands for every derivation of `c`, marked with
a constraint of its own. -/
structure Tags (P : Program) (c : Name) (ξ : Nat → Span) (τ : Nat → GTerm) : Prop where
  /-- The constraints are all different. -/
  inj : Function.Injective τ
  /-- Everything the span relates carries its constraint. -/
  tag : ∀ j, ∀ x ∈ (ξ j).den, τ j ∈ x.2.2
  /-- Added to the body of `c`, the span derives nothing new. -/
  absorb : ∀ j, (ξ j).den ∈ GD (P.withBody c (.or (P.body c) (.span (ξ j)))) (P.body c)
  /-- The span relates what every derivation of `c` relates. -/
  cover : ∀ j, ∀ G ∈ GD P (.call c), G.at P.sorts.interp ⊆ (ξ j).den.at P.sorts.interp

/-- The program with the `j`-th span added to the body of `c`. -/
def ext (P : Program) (c : Name) (ξ : Nat → Span) (j : Nat) : Program :=
  P.withBody c (.or (P.body c) (.span (ξ j)))

variable {P : Program} {c : Name} {ξ : Nat → Span} {τ : Nat → GTerm}

/-- The larger program derives what the program does. -/
theorem derivesG_ext (j : Nat) {e : Rel} {G : GRel} (h : DerivesG P e G) :
    DerivesG (ext P c ξ j) e G := by
  refine DerivesG.mono (fun n G hG => ?_) h
  by_cases hn : n = c
  · subst hn
    rw [ext, ProgramOf.withBody_self]
    exact .orl hG
  · rw [ext, ProgramOf.withBody_ne _ _ hn]
    exact hG

/-- The larger program derives the same from a call as from its body in the
program: the evaluations of an unfolding read its derivations as they read
those of the program. -/
theorem olaws_ext (hT : Tags P c ξ τ) (j : Nat) : OLaws P (GD (ext P c ξ j)) := by
  have key : ∀ m, GD (ext P c ξ j) (.call m) = GD (ext P c ξ j) (P.body m) := by
    intro m
    rw [gd_call]
    by_cases hm : m = c
    · subst hm
      rw [ext, ProgramOf.withBody_self, gd_or, gd_span]
      exact Set.union_eq_left.2 (Set.singleton_subset_iff.2 (hT.absorb j))
    · rw [ext, ProgramOf.withBody_ne _ _ hm]
  refine ⟨(gd_laws _).span, fun {e b} hb => ?_, fun hn h => gd_of_union _ hn h,
    fun h => gd_of_chain _ h, fun h => gd_of_meet _ h⟩
  unfold Charged.bodyOf at hb
  split at hb
  · cases hb
    rw [gd_norm, key]
  · cases hb
    rw [gd_normConv, gd_conv, key]
  · cases hb

/-- A derivation does not go through `c`, or for every `j` the larger program
has one that relates as much and carries the `j`-th constraint on all it
relates. -/
theorem pump (hT : Tags P c ξ τ) {e : Rel} {G : GRel} (h : DerivesG P e G) :
    DerivesG (P.withBody c .zero) e G ∨ ∀ j, ∃ G', DerivesG (ext P c ξ j) e G' ∧
      (∀ x ∈ G', τ j ∈ x.2.2) ∧ G.at P.sorts.interp ⊆ G'.at P.sorts.interp := by
  induction h with
  | span s => exact .inl (.span s)
  | orl _ ih =>
    exact ih.imp .orl fun h j => by
      obtain ⟨G', h₁, h₂, h₃⟩ := h j
      exact ⟨G', .orl h₁, h₂, h₃⟩
  | orr _ ih =>
    exact ih.imp .orr fun h j => by
      obtain ⟨G', h₁, h₂, h₃⟩ := h j
      exact ⟨G', .orr h₁, h₂, h₃⟩
  | @seq a b A B ha hb iha ihb =>
    rcases iha with la | ra
    · rcases ihb with lb | rb
      · exact .inl (.seq la lb)
      · refine .inr fun j => ?_
        obtain ⟨B', h₁, h₂, h₃⟩ := rb j
        refine ⟨A.comp B', .seq (derivesG_ext j ha) h₁, ?_, ?_⟩
        · rintro x ⟨m, S₁, S₂, -, hx, e⟩
          rw [e]
          exact Finset.mem_union_right _ (h₂ _ hx)
        · rw [at_comp, at_comp]
          rintro p ⟨m, hp₁, hp₂⟩
          exact ⟨m, hp₁, h₃ hp₂⟩
    · refine .inr fun j => ?_
      obtain ⟨A', h₁, h₂, h₃⟩ := ra j
      refine ⟨A'.comp B, .seq h₁ (derivesG_ext j hb), ?_, ?_⟩
      · rintro x ⟨m, S₁, S₂, hx, -, e⟩
        rw [e]
        exact Finset.mem_union_left _ (h₂ _ hx)
      · rw [at_comp, at_comp]
        rintro p ⟨m, hp₁, hp₂⟩
        exact ⟨m, h₃ hp₁, hp₂⟩
  | @and a b A B ha hb iha ihb =>
    rcases iha with la | ra
    · rcases ihb with lb | rb
      · exact .inl (.and la lb)
      · refine .inr fun j => ?_
        obtain ⟨B', h₁, h₂, h₃⟩ := rb j
        refine ⟨A.meet B', .and (derivesG_ext j ha) h₁, ?_, ?_⟩
        · rintro x ⟨S₁, S₂, -, hx, e⟩
          rw [e]
          exact Finset.mem_union_right _ (h₂ _ hx)
        · rw [at_meet, at_meet]
          exact Set.inter_subset_inter_right _ h₃
    · refine .inr fun j => ?_
      obtain ⟨A', h₁, h₂, h₃⟩ := ra j
      refine ⟨A'.meet B, .and h₁ (derivesG_ext j hb), ?_, ?_⟩
      · rintro x ⟨S₁, S₂, hx, -, e⟩
        rw [e]
        exact Finset.mem_union_left _ (h₂ _ hx)
      · rw [at_meet, at_meet]
        exact Set.inter_subset_inter_left _ h₃
  | conv _ ih =>
    refine ih.imp .conv fun h j => ?_
    obtain ⟨G', h₁, h₂, h₃⟩ := h j
    refine ⟨G'.inv, .conv h₁, fun x hx => h₂ (x.2.1, x.1, x.2.2) hx, ?_⟩
    rw [at_inv, at_inv]
    exact fun p hp => h₃ hp
  | @call n G hb ih =>
    by_cases hn : n = c
    · subst hn
      refine .inr fun j => ⟨(ξ j).den, .call ?_, hT.tag j, hT.cover j G (.call hb)⟩
      rw [ext, ProgramOf.withBody_self]
      exact .orr (.span _)
    · refine ih.imp (fun h => .call ?_) fun h j => ?_
      · rw [ProgramOf.withBody_ne _ _ hn]
        exact h
      · obtain ⟨G', h₁, h₂, h₃⟩ := h j
        refine ⟨G', .call ?_, h₂, h₃⟩
        rw [ext, ProgramOf.withBody_ne _ _ hn]
        exact h₁

/-! ## What a final unfolding answers -/

variable {R : Type} [Answer R] {D : Domain R}

/-- An answer of a final unfolding that relates a pair is an answer of the
goal in the program where `c` derives nothing. -/
theorem light_of_final {U : GOracle R Rel (Ans D P) Cost} (hW : Whole D P U)
    (hT : Tags P c ξ τ) (hL : D.Lawful P.sorts.interp) {n : Nat} {g : GoalOf R Rel}
    (hg : GoalOk D g) (hfin : (U n g).val.1 = true) {a : R} (hv : Valid D P (toGoal g) a)
    (hne : (den P.sorts.interp a).Nonempty) : Valid D (P.withBody c .zero) (toGoal g) a := by
  obtain ⟨s, hs, hden⟩ := hv.2 hL
  rcases pump hT hs.derivesG with h0 | hj
  · obtain ⟨s', hs', e⟩ := h0.derives s.den_nonempty
    exact ⟨hv.1, fun _ => ⟨s', hs', by rw [e]; exact hden⟩⟩
  · exfalso
    choose G' hG' htag hsub using hj
    have hpairs : ∀ j, (pairsOf P g (G' j)).Nonempty := fun j =>
      (hden ▸ hne).mono (wrap_mono (hsub j))
    have hin : ∀ j, G' j ∈ GR P n g.node := fun j =>
      hW _ (olaws_ext hT j) n g hg hfin _ (hG' j) (hpairs j)
    have hne' : ∀ j, (G' j).Nonempty := fun j => by
      obtain ⟨p, S, hS, -⟩ := wrapAt_mid_nonempty (hpairs j)
      exact ⟨_, hS⟩
    classical
    let pick : GRel → Set GTerm := fun G => if h : G.Nonempty then ↑h.some.2.2 else ∅
    have hfinite : (⋃ G ∈ GR P n g.node, pick G).Finite :=
      Set.Finite.biUnion (gr_finite P n g.node) fun G _ => by
        simp only [pick]
        split
        · exact Finset.finite_toSet _
        · exact Set.finite_empty
    obtain ⟨t, ⟨j, rfl⟩, hnot⟩ :=
      ((Set.infinite_range_of_injective hT.inj).sdiff hfinite).nonempty
    refine hnot (Set.mem_biUnion (hin j) ?_)
    simp only [pick, dite_eq_left (hne' j)]
    exact htag j _ (hne' j).some_mem

end Unfold

end RwLog
