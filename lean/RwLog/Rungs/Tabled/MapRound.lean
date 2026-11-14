/-
# A round keeps two runs in correspondence

If the tables of two runs of the tabled machine correspond
(`Rungs/Tabled/MapGoal.lean`), they correspond after a round (`tied_next`):
the answers that enter the table of the image of a goal are the images of the
answers that enter the table of the goal (`gain_fwd`), the goals that get a
table in the second run are the images of those that get one in the first
(`newGoals_fwd`), and the tables that complete are those of the images of
the goals whose tables complete (`closing_fwd`).
-/
import RwLog.Rungs.Tabled.MapNode

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P P' : Program}
  (K : Kernel R Cost) (hK : K.Refines D)

variable {b t : Bool} {U : GOracle R Rel (Ans D P) Cost} {U' : GOracle R Rel (Ans D P') Cost}
  {ts : List (TableOf R Rel (Ans D P))} {ts' : List (TableOf R Rel (Ans D P'))}
  (hW : Twin D P P' b t U U') (hT : Tied b t ts ts') (depth : Nat)
include hW hT

/-! ## What a table computes -/

theorem prod_cand_fwd {g : GoalOf R Rel} (hg : GoalOk D g) {c : Ans D P}
    (hc : c ∈ (prodG K hK U ts depth g).1) :
    ∃ c' ∈ (prodG K hK U' ts' depth (gmap b t g)).1, c'.span = smap b c.span := by
  rcases (mem_prodG_fst K hK U ts depth g c).1 hc with h | h
  · obtain ⟨c', hc', e⟩ := hW.link.ask depth g hg c h
    exact ⟨c', (mem_prodG_fst K hK U' ts' depth _ c').2 (.inl hc'), e⟩
  · obtain ⟨c', hc', e⟩ := cand_fwd K hK hW hT hg h
    exact ⟨c', (mem_prodG_fst K hK U' ts' depth _ c').2 (.inr hc'), e⟩

theorem prod_strat_fwd {g : GoalOf R Rel} (hg : GoalOk D g) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (prodG K hK U ts depth g).2) :
    ∃ strat' ∈ (prodG K hK U' ts' depth (gmap b t g)).2, Img (gmap b t) strat strat' := by
  rcases (mem_prodG_snd K hK U ts depth g strat).1 hs with ⟨hu, rfl⟩ | h
  · exact ⟨[], (mem_prodG_snd K hK U' ts' depth _ _).2
      (.inl ⟨by rw [hW.link.verdict depth g hg]; exact hu, rfl⟩), by simp [Img]⟩
  · obtain ⟨s', hs', e⟩ := strat_fwd K hK hW hT hg h
    exact ⟨s', (mem_prodG_snd K hK U' ts' depth _ _).2 (.inr hs'), e⟩

omit hW depth in
/-- The table of a goal and the table of its image. -/
theorem pair_tab {g : GoalOf R Rel} {i : Nat} (hi : idx ts g = some i) :
    ∃ (hil : i < ts.length) (j : Nat) (hjl : j < ts'.length),
      idx ts' (gmap b t g) = some j ∧ ts[i].goal = g ∧ ts'[j].goal = gmap b t g ∧
        ts'[j].done = ts[i].done ∧ GoalOk D g := by
  obtain ⟨hil, hgi, -⟩ := idx_some.1 hi
  obtain ⟨j, hj⟩ := hT.fwd.has g i hi
  obtain ⟨hjl, hgj, -⟩ := idx_some.1 hj
  have hg : GoalOk D g := hgi ▸ (hT.inv.ok _ (List.getElem_mem hil)).1
  obtain ⟨_, e₁⟩ := isDone_of_idx hi
  obtain ⟨_, e₂⟩ := isDone_of_idx hj
  exact ⟨hil, j, hjl, hj, hgi, hgj, by rw [← e₁, ← e₂]; exact done_iff hT hg.normal, hg⟩

/-! ## The answers that enter a table -/

theorem gain_fwd {g : GoalOf R Rel} {i j : Nat} (hi : idx ts g = some i)
    (hj : idx ts' (gmap b t g) = some j) (hil : i < ts.length) (hjl : j < ts'.length)
    {a : Ans D P} (ha : a ∈ gainOf K hK U ts depth ts[i]) :
    ∃ a' ∈ gainOf K hK U' ts' depth ts'[j], a'.span = smap b a.span := by
  obtain ⟨_, j₀, _, hj₀, hgi, hgj₀, hd₀, hg⟩ := pair_tab hT hi
  obtain rfl : j₀ = j := Option.some.inj (hj₀.symm.trans hj)
  have hdi : ts[i].done = false := by
    cases h : ts[i].done with
    | false => rfl
    | true => rw [gain_done K hK U ts depth h] at ha; cases ha
  have hdj : ts'[j₀].done = false := hd₀.trans hdi
  obtain ⟨_, old⟩ := ansOf_of_idx hi
  obtain ⟨_, old'⟩ := ansOf_of_idx hj
  unfold gainOf at ha ⊢
  rw [outOf_live K hK U ts depth hdi, hgi] at ha
  rw [outOf_live K hK U' ts' depth hdj, hgj₀]
  obtain ⟨hc, hco⟩ := mem_fresh K hK ha
  obtain ⟨c', hc', e⟩ := prod_cand_fwd K hK hW hT depth hg hc
  obtain ⟨a', ha', ea⟩ := fresh_of_max (K := K) (hK := hK) hW.law' hc' (old := ts'[j₀].answers)
    (fun t' ht' => by
      rw [← old'] at ht'
      obtain ⟨t₀, ht₀, e₀⟩ := ans_back hW hT hg.normal ht'
      have := hco t₀ (old ▸ ht₀)
      unfold covB at this ⊢
      rw [e₀, e, covers_smap hW.law]; exact this)
    (fun c₂' hc₂' hco₂ hcov => by
      obtain ⟨c₂, hc₂, e₂⟩ := prod_cand_fwd K hK hW.symm hT.symm depth (hg.gmap b t) hc₂'
      rw [gmap_gmap hg.normal] at hc₂
      have e₂' : c₂'.span = smap b c₂.span := by rw [e₂, smap_smap hW.law']
      have hco₂' : ∀ t₀ ∈ ts[i].answers, covB D P t₀ c₂ = false := by
        intro t₀ ht₀
        obtain ⟨t₀', ht₀', e₀⟩ := hT.fwd.ans g t₀ (old ▸ ht₀)
        have := hco₂ t₀' (old' ▸ ht₀')
        unfold covB at this ⊢
        rw [e₀, e₂', covers_smap hW.law] at this; exact this
      have hcov' : covB D P c₂ a = true := by
        unfold covB at hcov ⊢
        rw [e₂', e, covers_smap hW.law] at hcov; exact hcov
      have := fresh_max ha hc₂ hco₂' hcov'
      unfold covB at this ⊢
      rw [e, e₂', covers_smap hW.law]; exact this)
  exact ⟨a', ha', ea.trans e⟩

/-! ## The goals that get a table -/

theorem newGoals_fwd {g : GoalOf R Rel} (h : g ∈ newGoals K hK U ts depth) :
    gmap b t g ∈ newGoals K hK U' ts' depth := by
  obtain ⟨t₀, ht₀, strat, hs, hgs, hnone⟩ := (mem_newGoals K hK U ts depth g).1 h
  have hgok : GoalOk D g := out_ok hW.law hW.fo K hK depth hT.inv.ok ht₀ hs hgs
  obtain ⟨i, hil, hi, rfl⟩ := idx_of_mem hT.nodup ht₀
  obtain ⟨_, j, hjl, hj, -, hgj, hd, hg⟩ := pair_tab hT hi
  have hdi : ts[i].done = false := by
    cases h : ts[i].done with
    | false => rfl
    | true => rw [outOf_done K hK U ts depth h] at hs; cases hs
  rw [outOf_live K hK U ts depth hdi] at hs
  obtain ⟨s', hs', e⟩ := prod_strat_fwd K hK hW hT depth hg hs
  refine (mem_newGoals K hK U' ts' depth _).2 ⟨ts'[j], List.getElem_mem hjl, s', ?_, e.1 g hgs, ?_⟩
  · rw [outOf_live K hK U' ts' depth (hd.trans hdi), hgj]; exact hs'
  · cases hn : idx ts' (gmap b t g) with
    | none => rfl
    | some k =>
      obtain ⟨i', hi'⟩ := idx_back hT hgok.normal hn
      rw [hnone] at hi'; cases hi'

/-! ## The tables that complete -/

theorem closing_fwd {i j : Nat} (hi : i ∈ closing K hK U ts depth) (hil : i < ts.length)
    (hj : idx ts' (gmap b t ts[i].goal) = some j) : j ∈ closing K hK U' ts' depth := by
  let S : List Nat := (closing K hK U ts depth).filterMap fun i =>
    (ts[i]?).bind fun t₀ => idx ts' (gmap b t t₀.goal)
  have hmem : ∀ j, j ∈ S ↔ ∃ i ∈ closing K hK U ts depth, ∃ hil : i < ts.length,
      idx ts' (gmap b t ts[i].goal) = some j := by
    intro j
    simp only [S, List.mem_filterMap]
    constructor
    · rintro ⟨i, hi, h⟩
      cases hti : ts[i]? with
      | none => rw [hti] at h; cases h
      | some t₀ =>
        obtain ⟨hil, rfl⟩ := List.getElem?_eq_some_iff.1 hti
        rw [hti] at h
        exact ⟨i, hi, hil, h⟩
    · rintro ⟨i, hi, hil, h⟩
      exact ⟨i, hi, by rw [List.getElem?_eq_getElem hil]; exact h⟩
  refine closing_of_closed S (fun j hjS => ?_) j ((hmem j).2 ⟨i, hi, hil, hj⟩)
  obtain ⟨i, hi, hil, hj⟩ := (hmem j).1 hjS
  obtain ⟨_, hdi, hgain, strat, hs, hdeps⟩ := mem_closing K hK U ts depth hi
  have hidx := idx_getElem hT.nodup hil
  obtain ⟨_, j₀, hjl, hj₀, -, hgj, hd, hg⟩ := pair_tab hT hidx
  obtain rfl : j₀ = j := Option.some.inj (hj₀.symm.trans hj)
  refine ⟨hjl, hd.trans hdi, ?_, ?_⟩
  · refine List.eq_nil_iff_forall_not_mem.2 fun a' ha' => ?_
    have hback : idx ts (gmap b t (gmap b t ts[i].goal)) = some i := by
      rw [gmap_gmap hg.normal]; exact hidx
    obtain ⟨a, ha, -⟩ := gain_fwd K hK hW.symm hT.symm depth hj hback hjl hil ha'
    rw [hgain] at ha; cases ha
  · rw [outOf_live K hK U ts depth hdi] at hs
    obtain ⟨s', hs', e⟩ := prod_strat_fwd K hK hW hT depth hg hs
    refine ⟨s', by rw [outOf_live K hK U' ts' depth (hd.trans hdi), hgj]; exact hs',
      fun d' hd' => ?_⟩
    obtain ⟨d, hd, rfl⟩ := e.2 d' hd'
    obtain ⟨k, hk, hc⟩ := hdeps d hd
    obtain ⟨hkl, k', hkl', hk', hgk, -, hdk, -⟩ := pair_tab hT hk
    refine ⟨k', hk', hc.imp (fun ⟨_, h⟩ => ⟨hkl', hdk.trans h⟩) fun h => ?_⟩
    exact (hmem k').2 ⟨k, h, hkl, by rw [hgk]; exact hk'⟩

/-! ## The round -/

theorem fwd_next :
    Fwd b t (nextTables K hK U ts depth) (nextTables K hK U' ts' depth) := by
  have hnew : ∀ g, idx ts g = none → g ∈ newGoals K hK U ts depth →
      idx ts' (gmap b t g) = none ∧ gmap b t g ∈ newGoals K hK U' ts' depth := by
    intro g _ hg
    have := newGoals_fwd K hK hW hT depth hg
    obtain ⟨-, -, -, -, -, hn⟩ := (mem_newGoals K hK U' ts' depth _).1 this
    exact ⟨hn, this⟩
  refine ⟨fun g j h => ?_, fun g h => ?_, fun g a ha => ?_⟩
  · rcases idx_next_cases h with ⟨i, hi⟩ | ⟨hn, hg⟩
    · obtain ⟨j', hj'⟩ := hT.fwd.has g i hi
      exact ⟨j', next_idx hj'⟩
    · obtain ⟨hn', hg'⟩ := hnew g hn hg
      exact (idx_next_new hn' hg').1
  · obtain ⟨j, hj⟩ := idx_of_done h
    rcases idx_next_cases hj with ⟨i, hi⟩ | ⟨hn, hg⟩
    · obtain ⟨hil, -, hd⟩ := ansOf_next (K := K) (hK := hK) (U := U) (depth := depth) hi
      obtain ⟨_, j', hjl, hj', hgi, -, hdj, -⟩ := pair_tab hT hi
      obtain ⟨_, -, hd'⟩ := ansOf_next (K := K) (hK := hK) (U := U') (depth := depth) hj'
      rw [hd] at h
      rw [hd']
      rcases Bool.or_eq_true_iff.1 h with h | h
      · rw [hdj, h]; rfl
      · have := closing_fwd K hK hW hT depth (List.contains_iff_mem.1 h) hil
          (by rw [hgi]; exact hj')
        rw [List.contains_iff_mem.2 this, Bool.or_true]
    · rw [(idx_next_new hn hg).2.2] at h; cases h
  · obtain ⟨j, hj⟩ := idx_of_ans ha
    rcases idx_next_cases hj with ⟨i, hi⟩ | ⟨hn, hg⟩
    · obtain ⟨hil, hans, -⟩ := ansOf_next (K := K) (hK := hK) (U := U) (depth := depth) hi
      obtain ⟨_, j', hjl, hj', -, -, -, -⟩ := pair_tab hT hi
      obtain ⟨_, hans', -⟩ := ansOf_next (K := K) (hK := hK) (U := U') (depth := depth) hj'
      rw [hans] at ha
      rw [hans']
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨_, old⟩ := ansOf_of_idx hi
        obtain ⟨_, old'⟩ := ansOf_of_idx hj'
        obtain ⟨a', ha', e⟩ := hT.fwd.ans g a (old ▸ ha)
        exact ⟨a', List.mem_append_left _ (old' ▸ ha'), e⟩
      · obtain ⟨a', ha', e⟩ := gain_fwd K hK hW hT depth hi hj' hil hjl ha
        exact ⟨a', List.mem_append_right _ ha', e⟩
    · rw [(idx_next_new hn hg).2.1] at ha; cases ha

/-- A round keeps the correspondence. -/
theorem tied_next : Tied b t (nextTables K hK U ts depth) (nextTables K hK U' ts' depth) :=
  ⟨inv_next hW.law hW.fo K hK hW.uok depth hT.inv,
    inv_next hW.law' hW.fo' K hK hW.uok' depth hT.inv',
    nodup_next hT.nodup, nodup_next hT.nodup',
    fwd_next K hK hW hT depth, fwd_next K hK hW.symm hT.symm depth⟩

end Tabled

end RwLog
