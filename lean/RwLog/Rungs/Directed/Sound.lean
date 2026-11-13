/-
# The goal-directed machine is sound

Every answer of every table of `Directed.machine` stands, up to the theory,
for one derivation of the table's goal (`GInv`, kept by a round), so every
answer the machine emits stands for one derivation of the query
(`emitted_ref`). Soundness and derivation-general answers follow for any
machine that emits only such answers (`Rungs/Framework/Tier0.lean`).

The candidates of a sequence are read as R001's are (`cands_ref` there), with
the pushes made for the answers a sub-goal has so far instead of for the
answers of a complete one; that a sub-goal is complete is not used by R001's
argument either.
-/
import RwLog.Rungs.Directed.Machine
import RwLog.Rungs.Tabled.Exact
import RwLog.Rungs.Framework.TraverseStd
import RwLog.Rungs.R001.Proofs.Tier0

namespace RwLog

open R001 R001.Tier0 Cost

namespace Directed

variable {P : Program}

/-- The invariant of the tables: boundaries are interfaces, and every answer
stands for one derivation of its table's goal. -/
structure GInv (P : Program) (ts : Tables) : Prop where
  good : ∀ t ∈ ts, GoodG t.goal
  ref : ∀ t ∈ ts, ∀ a ∈ t.answers, ∃ s, Derives P t.goal.e s ∧ Ref P.theory a (GDen t.goal s.den)

theorem ansRef_of {ts : Tables} (hI : GInv P ts) : AnsRef P ts := by
  intro d hd a ha
  obtain ⟨t, hf, a₀, ha₀, rfl⟩ := answersOf_mem ha
  obtain ⟨ht, hs⟩ := findTable_spec hf
  obtain ⟨s, hds, hr⟩ := hI.ref t ht a₀ ha₀
  rw [same_e hs] at hds
  obtain ⟨hd', heq⟩ := norm_back d hds
  refine ⟨oS d.norm.1 s, hd', ?_⟩
  rw [heq, ← same_gden hs (hI.good t ht) (goodG_norm hd)]
  exact ref_oS _ hr

/-! ## The candidates of a sequence, as lists -/

/-- The pushes of a sequence restricted on the left. -/
def pushL (ts : Tables) (g : Goal) (a b : Rel) : List (Span × Goal) :=
  if g.lb.isSome || isSpan a then
    (maxima (answersOf ts (seqLeft g a))).map fun x => (x, seqPushL g b x)
  else []

/-- The pushes of a sequence restricted on the right. -/
def pushR (ts : Tables) (g : Goal) (a b : Rel) : List (Span × Goal) :=
  if g.rb.isSome || isSpan b then
    (maxima (answersOf ts (seqRight g b))).map fun y => (y, seqPushR g a y)
  else []

theorem seqCandidates_val (P : Program) (ts : Tables) (g : Goal) (a b : Rel) :
    (seqCandidates P ts g a b).val =
      if (g.lb.isSome || isSpan a) || (g.rb.isSome || isSpan b) then
        ((pushL ts g a b).flatMap (fun p =>
            (answersOf ts p.2).flatMap fun y => composeLive P.theory p.1 y) ++
          (pushR ts g a b).flatMap (fun p =>
            (answersOf ts p.2).flatMap fun x => composeLive P.theory x p.1),
         (if g.lb.isSome || isSpan a then [seqLeft g a] else []) ++
          (if g.rb.isSome || isSpan b then [seqRight g b] else []) ++
          (pushL ts g a b).map Prod.snd ++ (pushR ts g a b).map Prod.snd)
      else
        ((answersOf ts (seqLeft g a)).flatMap (fun x =>
            (answersOf ts (seqRight g b)).flatMap fun y => composeLive P.theory x y),
         [seqLeft g a, seqRight g b]) := by
  unfold seqCandidates pushL pushR
  cases hl : (g.lb.isSome || isSpan a) <;> cases hr : (g.rb.isSome || isSpan b) <;>
    simp [Tabled.answersOf_val, Tabled.maxima_val, Tabled.composeLive_val]

theorem candidates_val (P : Program) (ts : Tables) (g : Goal) :
    (candidates P ts g).val = match g.e with
      | .seq a b => (seqCandidates P ts g a b).val
      | _ => produce.produceStrategies P ts g := by
  obtain ⟨lb, e, rb⟩ := g
  cases e <;> simp only [candidates, Tabled.produceStrategies_val]

/-! ## Candidates stand for derivations -/

section

variable (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
include hwf

theorem cands_ref {ts : Tables} (hA : AnsRef P ts) {h : Goal} (hg : GoodG h) {c : Span}
    (hc : c ∈ (candidates P ts h).val.1) : ∃ s, Derives P h.e s ∧ Ref P.theory c (GDen h s.den) := by
  obtain ⟨lb, e, rb⟩ := h
  rw [candidates_val] at hc
  have other : c ∈ (produce.produceStrategies P ts ⟨lb, e, rb⟩).1 →
      ∃ s, Derives P e s ∧ Ref P.theory c (GDen ⟨lb, e, rb⟩ s.den) := fun hc' =>
    Tier0.cands_ref hwf (dd := 0) hA hg (by
      simp only [produce, List.mem_append]; exact .inr hc')
  cases e with
  | seq a b =>
    have hL : GoodG (seqLeft ⟨lb, .seq a b, rb⟩ a) := ⟨hg.1, trivial⟩
    have hR : GoodG (seqRight ⟨lb, .seq a b, rb⟩ b) := ⟨trivial, hg.2⟩
    simp only [seqCandidates_val] at hc
    split at hc
    · simp only [List.mem_append, List.mem_flatMap] at hc
      rcases hc with ⟨p, hp, y, hy, hc⟩ | ⟨p, hp, x, hx, hc⟩
      · unfold pushL at hp
        split at hp
        · simp only [List.mem_map] at hp
          obtain ⟨x, hx, rfl⟩ := hp
          obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hL x (maxima_sub hx)
          obtain ⟨s₂, hs₂, hr₂⟩ := hA _ (goodG_pushL hg b x) y hy
          have hr := composeLive_ref hwf (Ref.self x) hr₂ hc
          simp only [seqPushL] at hr
          rw [gden_pushL] at hr
          have hr' := hr.trans (Backed.comp hr₁.1 (Backed.refl _)) (hr₁.2.comp (LCov.refl _))
          rw [seqLeft, gden_seqL lb rb a (.seq a b)] at hr'
          obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty (hr'.nonempty))
          exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr'⟩
        · simp at hp
      · unfold pushR at hp
        split at hp
        · simp only [List.mem_map] at hp
          obtain ⟨y, hy, rfl⟩ := hp
          obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hR y (maxima_sub hy)
          obtain ⟨s₁, hs₁, hr₁⟩ := hA _ (goodG_pushR hg a y) x hx
          have hr := composeLive_ref hwf hr₁ (Ref.self y) hc
          simp only [seqPushR] at hr
          rw [gden_pushR] at hr
          have hr' := hr.trans (Backed.comp (Backed.refl _) hr₂.1) ((LCov.refl _).comp hr₂.2)
          rw [seqRight, gden_seqR lb rb b (.seq a b)] at hr'
          obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty (hr'.nonempty))
          exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr'⟩
        · simp at hp
    · simp only [List.mem_flatMap] at hc
      obtain ⟨x, hx, y, hy, hc⟩ := hc
      obtain ⟨s₁, hs₁, hr₁⟩ := hA _ hL x hx
      obtain ⟨s₂, hs₂, hr₂⟩ := hA _ hR y hy
      have hr := composeLive_ref hwf hr₁ hr₂ hc
      rw [seqLeft, seqRight, gden_seq lb rb a b (.seq a b)] at hr
      obtain ⟨s, hs, hsd⟩ := compose_isSome (gden_nonempty (hr.nonempty))
      exact ⟨s, .seq hs₁ hs₂ hs, by rw [hsd]; exact hr⟩
  | zero => exact other hc
  | span s => exact other hc
  | or a b => exact other hc
  | and a b => exact other hc
  | conv a => exact other hc
  | call n => exact other hc

end

/-- The goals a table asks for have interface boundaries. -/
theorem deps_good {ts : Tables} {g d : Goal} (hg : GoodG g)
    (hd : d ∈ (candidates P ts g).val.2) : GoodG d := by
  obtain ⟨lb, e, rb⟩ := g
  rw [candidates_val] at hd
  have other : d ∈ (produce.produceStrategies P ts ⟨lb, e, rb⟩).2 → GoodG d := fun hd' =>
    Tier0.deps_good (P := P) (dd := 0) (ts := ts) hg (by simpa only [produce] using hd')
  cases e with
  | seq a b =>
    simp only [seqCandidates_val] at hd
    split at hd
    · simp only [List.mem_append, List.mem_map] at hd
      rcases hd with ((hd | hd) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
      · split at hd
        · rw [List.mem_singleton] at hd; subst hd; exact ⟨hg.1, trivial⟩
        · simp at hd
      · split at hd
        · rw [List.mem_singleton] at hd; subst hd; exact ⟨trivial, hg.2⟩
        · simp at hd
      · unfold pushL at hp
        split at hp
        · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
          exact goodG_pushL hg b x
        · simp at hp
      · unfold pushR at hp
        split at hp
        · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
          exact goodG_pushR hg a y
        · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨hg.1, trivial⟩
      · exact ⟨trivial, hg.2⟩
  | zero => exact other hd
  | span s => exact other hd
  | or a b => exact other hd
  | and a b => exact other hd
  | conv a => exact other hd
  | call n => exact other hd

/-! ## A round -/

/-- What each table computes in a round. -/
def outs (st : State) : List (List Span × List Goal) :=
  st.tables.map fun t => (candidates st.P st.tables t.goal).val

/-- The tables after their answers were added. -/
def grown (st : State) : Tables :=
  (st.tables.zip (outs st)).map fun p => { p.1 with answers := p.1.answers ++ fresh p.1.answers p.2.1 }

theorem foldl_sub {α : Type} (f : List α → α → List α)
    (hf : ∀ acc g, f acc g = acc ∨ f acc g = acc ++ [g]) :
    ∀ (l acc : List α) {x : α}, x ∈ l.foldl f acc → x ∈ acc ∨ x ∈ l
  | [], _, _, h => .inl h
  | y :: l, acc, x, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_sub f hf l _ h with h | h
    · rcases hf acc y with e | e
      · rw [e] at h; exact .inl h
      · rw [e] at h
        rcases List.mem_append.1 h with h | h
        · exact .inl h
        · exact .inr (by simp_all)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- A round keeps the program and the orientation of the root, grows each
table by fresh candidates, adds empty tables for goals that were asked for,
and emits what the root gained. -/
theorem round_spec (st : State) :
    (round st).val.1.P = st.P ∧ (round st).val.1.rootFlip = st.rootFlip ∧
    (∃ new : List Goal, (∀ g ∈ new, ∃ d ∈ (outs st).flatMap Prod.snd, g = d.norm.2) ∧
      (round st).val.1.tables = grown st ++ new.map fun g => ⟨g, [], false⟩) ∧
    (round st).val.2 = orient st.rootFlip (match st.tables.head?, (grown st).head? with
      | some t, some t' => t'.answers.drop t.answers.length
      | _, _ => []) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold round grown outs
    simp only [bind_val, pure_val, mapL_val, foldL_val, Tabled.fresh_val, Tabled.norm_val]
    refine ⟨_, fun g hg => ?_, rfl⟩
    rcases foldl_sub _ (fun acc g => by
      split
      · exact .inl rfl
      · simp only [bind_val, pure_val]
        split
        · exact .inl rfl
        · exact .inr rfl) _ _ hg with h | h
    · cases h
    · simp only [List.mem_map] at h
      obtain ⟨d, hd, rfl⟩ := h
      exact ⟨d, hd, rfl⟩
  · simp only [round, bind_val, pure_val, mapL_val, Tabled.fresh_val, grown, outs]
    same_text

/-- The invariant is kept by a round. -/
theorem ginv_round {st : State} (hwf : ∀ ρ ∈ st.P.theory, ρ.WellFormed)
    (hI : GInv st.P st.tables) : GInv st.P (round st).val.1.tables := by
  obtain ⟨-, -, ⟨new, hnew, htab⟩, -⟩ := round_spec st
  have hA := ansRef_of hI
  have hgrown : ∀ t' ∈ grown st, ∃ t ∈ st.tables, t'.goal = t.goal ∧
      ∀ a ∈ t'.answers, a ∈ t.answers ∨ a ∈ (candidates st.P st.tables t.goal).val.1 := by
    intro t' ht'
    simp only [grown, outs, List.mem_map] at ht'
    obtain ⟨p, hp, rfl⟩ := ht'
    have hp1 := (List.of_mem_zip hp).1
    have hp2 : p.2 = (candidates st.P st.tables p.1.goal).val := by
      have := List.of_mem_zip hp
      rw [List.zip_map_right] at hp
      simp only [List.mem_map] at hp
      obtain ⟨⟨t, t₂⟩, htt, rfl⟩ := hp
      have : t = t₂ := by
        have := List.mem_iff_getElem.1 htt
        obtain ⟨i, hi, e⟩ := this
        simp only [List.getElem_zip, Prod.mk.injEq] at e
        exact e.1.symm.trans e.2
      subst this
      rfl
    refine ⟨p.1, hp1, rfl, fun a ha => ?_⟩
    rcases List.mem_append.1 ha with h | h
    · exact .inl h
    · exact .inr (by rw [← hp2]; exact (fresh_sub h).1)
  rw [htab]
  constructor
  · intro t ht
    rcases List.mem_append.1 ht with h | h
    · obtain ⟨t₀, ht₀, e, -⟩ := hgrown t h
      rw [e]; exact hI.good t₀ ht₀
    · simp only [List.mem_map] at h
      obtain ⟨g, hg, rfl⟩ := h
      obtain ⟨d, hd, rfl⟩ := hnew g hg
      simp only [outs, List.mem_flatMap, List.mem_map] at hd
      obtain ⟨_, ⟨t₀, ht₀, rfl⟩, hd⟩ := hd
      exact goodG_norm (deps_good (hI.good t₀ ht₀) hd)
  · intro t ht a ha
    rcases List.mem_append.1 ht with h | h
    · obtain ⟨t₀, ht₀, e, hans⟩ := hgrown t h
      rw [e]
      rcases hans a ha with h' | h'
      · exact hI.ref t₀ ht₀ a h'
      · exact cands_ref hwf hA (hI.good t₀ ht₀) h'
    · simp only [List.mem_map] at h
      obtain ⟨g, -, rfl⟩ := h
      cases ha

/-! ## A run -/

/-- The invariant of a reachable state of the run on `q`: the first table is
the query's, and the tables satisfy `GInv`. -/
structure SInv (P : Program) (q : Rel) (st : State) : Prop where
  prog : st.P = P
  flip : st.rootFlip = (GoalOf.norm ⟨none, q, none⟩).1
  root : ∃ t rest, st.tables = t :: rest ∧ t.goal = (GoalOf.norm ⟨none, q, none⟩).2
  inv : GInv P st.tables

theorem sinv_start (P : Program) (q : Rel) : SInv P q (machine.start P q) := by
  have e : machine.start P q =
      ⟨P, [⟨(GoalOf.norm ⟨none, q, none⟩).2, [], false⟩], (GoalOf.norm ⟨none, q, none⟩).1, 0⟩ := rfl
  rw [e]
  refine ⟨rfl, rfl, ⟨_, _, rfl, rfl⟩, ?_, ?_⟩
  · intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact goodG_norm (goodG_root q)
  · intro t ht a ha
    rw [List.mem_singleton] at ht
    subst ht
    cases ha

/-- A round keeps the invariant, and what it emits are answers of the query's
table, oriented. -/
theorem sinv_round {q : Rel} {st : State} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
    (h : SInv P q st) :
    SInv P q (round st).val.1 ∧
      ∀ a ∈ (round st).val.2, ∃ t rest, (round st).val.1.tables = t :: rest ∧
        ∃ a₀ ∈ t.answers, a = oS (GoalOf.norm ⟨none, q, none⟩).1 a₀ := by
  obtain ⟨hP, hF, ⟨new, -, htab⟩, hemit⟩ := round_spec st
  obtain ⟨t, rest, ht, htg⟩ := h.root
  have hI := ginv_round (st := st) (by rw [h.prog]; exact hwf) (by rw [h.prog]; exact h.inv)
  rw [h.prog] at hI
  have hgr : ∃ rest', grown st = (⟨t.goal, t.answers ++
      fresh t.answers (candidates st.P st.tables t.goal).val.1, t.done⟩ : Table) :: rest' := by
    simp only [grown, outs, ht, List.map_cons, List.zip_cons_cons]
    exact ⟨_, rfl⟩
  obtain ⟨rest', hgr⟩ := hgr
  refine ⟨⟨hP.trans h.prog, hF.trans h.flip,
    ⟨⟨t.goal, t.answers ++ fresh t.answers (candidates st.P st.tables t.goal).val.1, t.done⟩, _,
      by rw [htab, hgr]; rfl, htg⟩, hI⟩, ?_⟩
  intro a ha
  rw [hemit, ht, hgr, orient_eq] at ha
  simp only [List.head?_cons, List.mem_map] at ha
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  refine ⟨_, _, by rw [htab, hgr]; rfl, a₀, ?_, by rw [h.flip]⟩
  simp only [List.drop_left'] at ha₀
  exact List.mem_append_right _ (by simpa using ha₀)

/-- Every answer the machine emits stands for one derivation of the query. -/
theorem emitted_ref_from {q : Rel} (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed) :
    ∀ (n : Nat) (st : State), SInv P q st → ∀ a ∈ machine.runtime.emitted st n,
      ∃ s, Derives P q s ∧ Ref P.theory a s.den
  | 0, _, _, _, ha => nomatch ha
  | n + 1, st, h, a, ha => by
    have hs : machine.runtime.step st = .emit (round st).val.2 (round st).val.1 := rfl
    obtain ⟨h', hem⟩ := sinv_round hwf h
    unfold Runtime.emitted at ha
    rw [machine.runtime.run_succ_emit hs] at ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨t, rest, ht, a₀, ha₀, rfl⟩ := hem a ha
      obtain ⟨t', rest', ht', htg⟩ := h'.root
      rw [ht] at ht'
      obtain ⟨rfl, -⟩ := List.cons.inj ht'
      obtain ⟨s, hs, hr⟩ := h'.inv.ref t (by rw [ht]; exact List.mem_cons_self) a₀ ha₀
      rw [htg] at hs hr
      obtain ⟨hd, heq⟩ := norm_back ⟨none, q, none⟩ hs
      refine ⟨_, hd, ?_⟩
      have := ref_oS (GoalOf.norm ⟨none, q, none⟩).1 hr
      rwa [← heq, gden_root] at this
    · exact emitted_ref_from hwf n _ h' a ha

/-- Every answer the goal-directed machine emits stands for one derivation of
the query. -/
theorem emitted_ref (P : Program) (q : Rel) (hP : P.WellFormed q) (n : Nat) :
    ∀ a ∈ machine.runtime.emitted (machine.runtime.init P q) n,
      ∃ s, Derives P q s ∧ Ref P.theory a s.den :=
  emitted_ref_from hP.2.2 n _ (sinv_start P q)

end Directed

end RwLog
