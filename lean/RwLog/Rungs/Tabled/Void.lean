/-
# A side that relates nothing completes the goal it was split from

A goal is *void* when no derivation of its node relates a pair between its
boundaries (`Void`). A complete table with no answer has a void goal
(`void_of_done`), a void goal never has an answer (`void_no_ans`), and a
chain or a meet one side of a split of which is void is void
(`SeqSplit.void_left` and the three beside it).

A void goal one of whose strategies has only complete goals completes in the
round (`done_of_strat`). When a side of a split is complete with no answer,
the strategy that pushes its answers has that side alone, so a void goal
with a table completes once a void side of one of its splits does
(`done_of_side`).

`chain_ladder`: in a run from a chain, if the goal of the first members
completes whenever it has a table and is void, the root completes. The run
splits the chain before its last member again and again until it reaches
that goal, and the goals complete back up. `meet_ladder` is the same for a
meet and any of its members: the run takes the other members away one at a
time.
-/
import RwLog.Kernel.NormalFormMap
import RwLog.Rungs.Tabled.Host

namespace RwLog

namespace Tabled

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- No derivation of the node of the goal relates a pair between its
boundaries. -/
def Void (P : Program) (g : GoalOf R Rel) : Prop :=
  ∀ k G, G ∈ GDn P k g.node → pairsOf P g G = ∅

theorem comp_empty_left (Y : PRel) : PRel.comp ∅ Y = ∅ :=
  Set.eq_empty_of_forall_notMem fun ⟨_, _⟩ ⟨_, h, _⟩ => h

theorem comp_empty_right (X : PRel) : PRel.comp X ∅ = ∅ :=
  Set.eq_empty_of_forall_notMem fun ⟨_, _⟩ ⟨_, _, h⟩ => h

section split

variable {g : GoalOf R Rel} {w : Kind × GoalOf R Rel × GoalOf R Rel}

omit [DecidableEq R] in
theorem SeqSplit.void_left (h : SeqSplit D P g w) (hv : Void P w.2.1) : Void P g := by
  intro k G hG
  rw [h.gdn k] at hG
  obtain ⟨G₁, hG₁, G₂, -, rfl⟩ := hG
  have := hv k G₁ hG₁
  unfold pairsOf at this ⊢
  rw [h.llb, h.lrb] at this
  rw [wrap_comp, this, comp_empty_left]

omit [DecidableEq R] in
theorem SeqSplit.void_right (h : SeqSplit D P g w) (hv : Void P w.2.2) : Void P g := by
  intro k G hG
  rw [h.gdn k] at hG
  obtain ⟨G₁, -, G₂, hG₂, rfl⟩ := hG
  have := hv k G₂ hG₂
  unfold pairsOf at this ⊢
  rw [h.rlb, h.rrb] at this
  rw [wrap_comp, this, comp_empty_right]

omit [DecidableEq R] in
theorem AndSplit.void_left (hL : D.Lawful P.sorts.interp) (hg : GoalOk D g)
    (h : AndSplit D P g w) (hv : Void P w.2.1) : Void P g := by
  intro k G hG
  rw [h.gdn k] at hG
  obtain ⟨G₁, hG₁, G₂, -, rfl⟩ := hG
  have := hv k G₁ hG₁
  unfold pairsOf at this ⊢
  rw [h.llb, h.lrb] at this
  rw [wrap_meet hL hg.lb hg.rb, this, Set.empty_inter]

omit [DecidableEq R] in
theorem AndSplit.void_right (hL : D.Lawful P.sorts.interp) (hg : GoalOk D g)
    (h : AndSplit D P g w) (hv : Void P w.2.2) : Void P g := by
  intro k G hG
  rw [h.gdn k] at hG
  obtain ⟨G₁, -, G₂, hG₂, rfl⟩ := hG
  have := hv k G₂ hG₂
  unfold pairsOf at this ⊢
  rw [h.rlb, h.rrb] at this
  rw [wrap_meet hL hg.lb hg.rb, this, Set.inter_empty]

end split

section tables

variable (hL : D.Lawful P.sorts.interp) {ts : List (TableOf R Rel (Ans D P))} {g : GoalOf R Rel}
include hL

omit [DecidableEq R] in
/-- A void goal has no answer. -/
theorem void_no_ans (hv : Void P g) (a : Ans D P) : a.goal ≠ toGoal g := by
  intro ha
  obtain ⟨k, G, hG, e⟩ := ans_gdn hL ha
  have := hL.live a.span
  rw [e, hv k G hG] at this
  exact Set.not_nonempty_empty this

/-- A void goal has no answer in any table. -/
theorem void_ansOf (hT : TablesOk D ts) (hv : Void P g) : ansOf ts g = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun a ha => void_no_ans hL hv a (ansOf_goal hT ha)

omit hL in
/-- A complete table with no answer has a void goal. -/
theorem void_of_done (hI : Inv D P ts) (hd : isDone ts g = true) (he : ansOf ts g = []) :
    Void P g := by
  intro k G hG
  by_contra hne
  obtain ⟨i, hi⟩ := idx_of_done hd
  obtain ⟨hil, hg, -⟩ := idx_some.1 hi
  obtain ⟨_, ea⟩ := ansOf_of_idx hi
  obtain ⟨_, ed⟩ := isDone_of_idx hi
  obtain ⟨b, hb, -⟩ := hI.full _ (List.getElem_mem hil) (by rw [← ed]; exact hd) k G
    (by rw [hg]; exact hG) (by rw [hg]; exact Set.nonempty_iff_ne_empty.2 hne)
  rw [← ea, he] at hb
  cases hb

variable (K : Kernel R Cost) (hK : K.Refines D)

/-- When the left side of a split is complete and void, the split has a
strategy with that side alone. -/
theorem side_left (hT : TablesOk D ts) {w : Kind × GoalOf R Rel × GoalOf R Rel}
    (hd : isDone ts w.2.1 = true) (hv : Void P w.2.1) :
    ∃ strat ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.2,
      ∀ d ∈ strat, isDone ts d = true := by
  refine ⟨_, (mem_way_strats K hK _ g w _).2 (.inr (.inl ⟨hd, rfl⟩)), fun d hdm => ?_⟩
  rcases List.mem_cons.1 hdm with rfl | hdm
  · exact hd
  · obtain ⟨x, hx, -⟩ := List.mem_map.1 hdm
    have := List.mem_maximaBy hx
    rw [void_ansOf hL hT hv] at this
    cases this

theorem side_right (hT : TablesOk D ts) {w : Kind × GoalOf R Rel × GoalOf R Rel}
    (hd : isDone ts w.2.2 = true) (hv : Void P w.2.2) :
    ∃ strat ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.2,
      ∀ d ∈ strat, isDone ts d = true := by
  refine ⟨_, (mem_way_strats K hK _ g w _).2 (.inr (.inr ⟨hd, rfl⟩)), fun d hdm => ?_⟩
  rcases List.mem_cons.1 hdm with rfl | hdm
  · exact hd
  · obtain ⟨x, hx, -⟩ := List.mem_map.1 hdm
    have := List.mem_maximaBy hx
    rw [void_ansOf hL hT hv] at this
    cases this

end tables

/-! ## In a run -/

section run

variable {K : Kernel R Cost} {hK : K.Refines D} {U : GOracle R Rel (Ans D P) Cost} {root : Rel}
  (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
  (hroot : GoalOk D (⟨none, root, none⟩ : GoalOf R Rel))

include hL hP hU hroot in
/-- A void goal one of whose strategies has only complete goals completes in
the round. -/
theorem done_of_strat {r : Nat} {g : GoalOf R Rel} (hv : Void P g) {i : Nat}
    (hi : idx (tablesAt K hK U root r) g = some i) {strat : List (GoalOf R Rel)}
    (hs : strat ∈ (produceTables (K := DerivationKernel.over D K hK P)
      (tablesAt K hK U root r) g).val.2)
    (hd : ∀ d ∈ strat, isDone (tablesAt K hK U root r) d = true) :
    isDone (tablesAt K hK U root (r + 1)) g = true := by
  rcases Bool.eq_false_or_eq_true (isDone (tablesAt K hK U root r) g) with hdd | hdd
  · exact done_mono (Nat.le_succ r) hdd
  · have hI := inv_at hL hP hU hroot (K := K) (hK := hK) r
    exact done_of_closed (K := K) (hK := hK) (U := U) (ts := tablesAt K hK U root r) (depth := r)
      (fun x => x = g)
      (fun x hx => by
        subst hx
        exact ⟨⟨i, hi⟩, hdd,
          gain_nil_of_covered hU hI.ok hi hdd fun c hc => (void_no_ans hL hv c hc).elim,
          strat, (mem_prodG_snd K hK U _ r x strat).2 (.inr hs),
          fun d hdm => ⟨idx_of_done (hd d hdm), .inl (hd d hdm)⟩⟩)
      g rfl

include hL hP hU hroot in
/-- A void goal with a table completes once a void side of one of its splits
does. -/
theorem done_of_side {g : GoalOf R Rel} (hv : Void P g)
    {w : Kind × GoalOf R Rel × GoalOf R Rel}
    (hw : ∀ ts : List (TableOf R Rel (Ans D P)), ∀ s,
      s ∈ (way (K := DerivationKernel.over D K hK P) ts g w).val.2 →
      s ∈ (produceTables (K := DerivationKernel.over D K hK P) ts g).val.2)
    {side : GoalOf R Rel} (hside : side = w.2.1 ∨ side = w.2.2) (hsv : Void P side)
    (hsd : (∃ r i, idx (tablesAt K hK U root r) side = some i) →
      ∃ r, isDone (tablesAt K hK U root r) side = true)
    (hh : ∃ r i, idx (tablesAt K hK U root r) g = some i) :
    ∃ r, isDone (tablesAt K hK U root r) g = true := by
  obtain ⟨r₀, i, hi⟩ := hh
  rcases Bool.eq_false_or_eq_true (isDone (tablesAt K hK U root r₀) g) with hdd | hdd
  · exact ⟨r₀, hdd⟩
  · have h₀ : [w.2.1, w.2.2] ∈ (prodG K hK U (tablesAt K hK U root r₀) r₀ g).2 :=
      (mem_prodG_snd K hK U _ r₀ g _).2 (.inr (hw _ _ ((mem_way_strats K hK _ g w _).2 (.inl rfl))))
    have hask := asked hi hdd h₀ (d := side) (by rcases hside with rfl | rfl <;> simp)
    obtain ⟨r₁, hr₁⟩ := hsd ⟨r₀ + 1, hask⟩
    have hd := done_mono (Nat.le_max_right r₀ r₁) hr₁
    have hi' := idx_mono (Nat.le_max_left r₀ r₁) hi
    have hI := inv_at hL hP hU hroot (K := K) (hK := hK) (max r₀ r₁)
    have key : ∃ strat ∈ (way (K := DerivationKernel.over D K hK P)
        (tablesAt K hK U root (max r₀ r₁)) g w).val.2,
        ∀ d ∈ strat, isDone (tablesAt K hK U root (max r₀ r₁)) d = true := by
      rcases hside with rfl | rfl
      · exact side_left hL K hK hI.ok hd hsv
      · exact side_right hL K hK hI.ok hd hsv
    obtain ⟨strat, hs, hall⟩ := key
    exact ⟨max r₀ r₁ + 1, done_of_strat hL hP hU hroot hv hi' (hw _ _ hs) hall⟩

end run

/-! ## Down a chain and back -/

theorem view_mkSeq : ∀ {ys : List Rel}, 2 ≤ ys.length → (∀ x ∈ ys, NotSeq x) →
    (mkSeq ys).view = .chain ys
  | y :: y' :: t, _, hn => by
    show NodeView.chain (seqParts (mkSeq (y :: y' :: t))) = _
    rw [seqParts_mkSeq (by simp) hn]

theorem view_mkAnd : ∀ {ys : List Rel}, 2 ≤ ys.length → (∀ x ∈ ys, NotAnd x) →
    (mkAnd ys).view = .meet ys
  | y :: y' :: t, _, hn => by
    show NodeView.meet (andParts (mkAnd (y :: y' :: t))) = _
    rw [andParts_mkAnd (by simp) hn]

theorem mkAnd_eraseIdx_one : ∀ {ys : List Rel} {l : Rel}, ys.length = 2 → ys[0]? = some l →
    mkAnd (ys.eraseIdx 1) = l
  | [y, y'], l, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl

section ladder

variable {K : Kernel R Cost} {hK : K.Refines D} {U : GOracle R Rel (Ans D P) Cost} {root : Rel}
  (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (hU : UOk D P U)
  (hroot : GoalOk D (⟨none, root, none⟩ : GoalOf R Rel))

/-- The goal of a node with no boundary. -/
abbrev bare (e : Rel) : GoalOf R Rel := ⟨none, e, none⟩

include hL hP hU hroot in
/-- If the goal of the first `p` members of a chain is void and completes
whenever it has a table, so does the goal of every longer prefix. -/
theorem chain_ladder {xs : List Rel} (hx : ∀ x ∈ xs, NotSeq x) {p : Nat} (hp : 0 < p)
    (hbv : Void P (bare (mkSeq (xs.take p)) : GoalOf R Rel))
    (hbd : (∃ r i, idx (tablesAt K hK U root r) (bare (mkSeq (xs.take p))) = some i) →
      ∃ r, isDone (tablesAt K hK U root r) (bare (mkSeq (xs.take p))) = true) :
    ∀ d j, j = p + d → j ≤ xs.length →
      GoalOk D (bare (mkSeq (xs.take j)) : GoalOf R Rel) →
      Void P (bare (mkSeq (xs.take j)) : GoalOf R Rel) ∧
        ((∃ r i, idx (tablesAt K hK U root r) (bare (mkSeq (xs.take j))) = some i) →
          ∃ r, isDone (tablesAt K hK U root r) (bare (mkSeq (xs.take j))) = true) := by
  intro d
  induction d with
  | zero =>
    intro j hj _ _
    obtain rfl : j = p := by omega
    exact ⟨hbv, hbd⟩
  | succ d ih =>
    intro j hj hjl hg
    have hlen : (xs.take j).length = j := by rw [List.length_take]; omega
    have hys : ∀ x ∈ xs.take j, NotSeq x := fun x h => hx x (List.mem_of_mem_take h)
    have hne : xs.take j ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    have hv : (mkSeq (xs.take j)).view = .chain (xs.take j) := view_mkSeq (by omega) hys
    have hvf : (bare (mkSeq (xs.take j)) : GoalOf R Rel).node.view.forget = .chain (xs.take j) := by
      show (mkSeq (xs.take j)).view.forget = _
      rw [hv]; rfl
    obtain ⟨-, l, r, hl, hr, -⟩ := hg.normal.chain_split hv (i := j - 1) (by omega) (by omega)
    have hl' : (mkSeq (xs.take j)).interval 0 (j - 1) = some (mkSeq (xs.take (j - 1))) := by
      unfold RelOf.interval
      simp only [RelOf.chainParts]
      rw [seqParts_mkSeq hne hys, ite_of_pos ⟨by omega, by omega⟩, List.drop_zero, List.take_take,
        Nat.min_eq_left (by omega)]
    obtain rfl : l = mkSeq (xs.take (j - 1)) := Option.some.inj (hl.symm.trans hl')
    have hw : ((Kind.seq, bare (mkSeq (xs.take (j - 1))), bare r) :
        Kind × GoalOf R Rel × GoalOf R Rel) ∈
        (splitsOf (K := DerivationKernel.over D K hK P) (bare (mkSeq (xs.take j)))
          (.chain (xs.take j))).val :=
      (mem_splitsOf_chain K hK _ _ _).2 ⟨j - 1, by
        rw [hlen]; unfold seqSplits; split
        · simp only [List.mem_singleton]; omega
        · simp, _, r, hl, hr, rfl⟩
    have hS := seqSplit_of_mem K hK hg hvf hw
    obtain ⟨hvoid, hdone⟩ := ih (j - 1) (by omega) (by omega) hS.lok
    refine ⟨hS.void_left hvoid, done_of_side hL hP hU hroot (hS.void_left hvoid)
      (w := (Kind.seq, bare (mkSeq (xs.take (j - 1))), bare r))
      (fun ts s hs => ?_) (.inl rfl) hvoid hdone⟩
    rw [produceTables_chain K hK ts _ hvf]
    exact List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw, rfl⟩, hs⟩

include hL hP hU hroot in
/-- If the goal of the members of a chain from the `q`-th on is void and
completes whenever it has a table, so does the goal of every longer
suffix. -/
theorem chain_ladder_right {xs : List Rel} (hx : ∀ x ∈ xs, NotSeq x) {q : Nat}
    (hq : q < xs.length)
    (hbv : Void P (bare (mkSeq (xs.drop q)) : GoalOf R Rel))
    (hbd : (∃ r i, idx (tablesAt K hK U root r) (bare (mkSeq (xs.drop q))) = some i) →
      ∃ r, isDone (tablesAt K hK U root r) (bare (mkSeq (xs.drop q))) = true) :
    ∀ d j, j + d = q →
      GoalOk D (bare (mkSeq (xs.drop j)) : GoalOf R Rel) →
      Void P (bare (mkSeq (xs.drop j)) : GoalOf R Rel) ∧
        ((∃ r i, idx (tablesAt K hK U root r) (bare (mkSeq (xs.drop j))) = some i) →
          ∃ r, isDone (tablesAt K hK U root r) (bare (mkSeq (xs.drop j))) = true) := by
  intro d
  induction d with
  | zero =>
    intro j hj _
    obtain rfl : j = q := by omega
    exact ⟨hbv, hbd⟩
  | succ d ih =>
    intro j hj hg
    have hlen : (xs.drop j).length = xs.length - j := List.length_drop
    have hys : ∀ x ∈ xs.drop j, NotSeq x := fun x h => hx x (List.mem_of_mem_drop h)
    have hne : xs.drop j ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    have hv : (mkSeq (xs.drop j)).view = .chain (xs.drop j) := view_mkSeq (by omega) hys
    have hvf : (bare (mkSeq (xs.drop j)) : GoalOf R Rel).node.view.forget = .chain (xs.drop j) := by
      show (mkSeq (xs.drop j)).view.forget = _
      rw [hv]; rfl
    obtain ⟨-, l, r, hl, hr, -⟩ := hg.normal.chain_split hv (i := 1) (by omega) (by omega)
    have hr' : (mkSeq (xs.drop j)).interval 1 (xs.drop j).length =
        some (mkSeq (xs.drop (j + 1))) := by
      unfold RelOf.interval
      simp only [RelOf.chainParts]
      rw [seqParts_mkSeq hne hys, ite_of_pos ⟨by omega, Nat.le_refl _⟩, List.take_length,
        List.drop_drop]
    obtain rfl : r = mkSeq (xs.drop (j + 1)) := Option.some.inj (hr.symm.trans hr')
    have hw : ((Kind.seq, bare l, bare (mkSeq (xs.drop (j + 1)))) :
        Kind × GoalOf R Rel × GoalOf R Rel) ∈
        (splitsOf (K := DerivationKernel.over D K hK P) (bare (mkSeq (xs.drop j)))
          (.chain (xs.drop j))).val :=
      (mem_splitsOf_chain K hK _ _ _).2 ⟨1, by unfold seqSplits; split <;> simp, l, _, hl, hr, rfl⟩
    have hS := seqSplit_of_mem K hK hg hvf hw
    obtain ⟨hvoid, hdone⟩ := ih (j + 1) (by omega) hS.rok
    refine ⟨hS.void_right hvoid, done_of_side hL hP hU hroot (hS.void_right hvoid)
      (w := (Kind.seq, bare l, bare (mkSeq (xs.drop (j + 1)))))
      (fun ts s hs => ?_) (.inr rfl) hvoid hdone⟩
    rw [produceTables_chain K hK ts _ hvf]
    exact List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw, rfl⟩, hs⟩

include hL hP hU hroot in
/-- If the goal of the meet of some members is void and completes whenever
it has a table, so does the goal of the meet of those and any others. -/
theorem meet_ladder {A : List Rel} (hA : A ≠ []) (hAs : A.Pairwise RelLE)
    (hbv : Void P (bare (mkAnd A) : GoalOf R Rel))
    (hbd : (∃ r i, idx (tablesAt K hK U root r) (bare (mkAnd A)) = some i) →
      ∃ r, isDone (tablesAt K hK U root r) (bare (mkAnd A)) = true) :
    ∀ (n : Nat) (ys C : List Rel), C.length = n → ys.Pairwise RelLE → ys.Perm (A ++ C) →
      (∀ x ∈ ys, NotAnd x) → GoalOk D (bare (mkAnd ys) : GoalOf R Rel) →
      Void P (bare (mkAnd ys) : GoalOf R Rel) ∧
        ((∃ r i, idx (tablesAt K hK U root r) (bare (mkAnd ys)) = some i) →
          ∃ r, isDone (tablesAt K hK U root r) (bare (mkAnd ys)) = true) := by
  intro n
  induction n with
  | zero =>
    intro ys C hC hs hperm _ _
    obtain rfl : C = [] := List.length_eq_zero_iff.1 hC
    rw [List.append_nil] at hperm
    obtain rfl : ys = A := eq_of_perm_of_sorted hperm hs hAs
    exact ⟨hbv, hbd⟩
  | succ n ih =>
    intro ys C hC hs hperm hna hg
    obtain ⟨c, C', rfl⟩ : ∃ c C', C = c :: C' := by
      cases C with
      | nil => simp at hC
      | cons c C' => exact ⟨c, C', rfl⟩
    have hC' : C'.length = n := by simpa using hC
    have hApos := List.length_pos_iff.2 hA
    have hlen : ys.length = A.length + (C'.length + 1) := by
      rw [hperm.length_eq]; simp
    obtain ⟨i, hi, hci⟩ := List.getElem_of_mem (hperm.mem_iff.2 (by simp) : c ∈ ys)
    have hv : (mkAnd ys).view = .meet ys := view_mkAnd (by omega) hna
    have hvf : (bare (mkAnd ys) : GoalOf R Rel).node.view.forget = .meet ys := by
      show (mkAnd ys).view.forget = _
      rw [hv]; rfl
    -- the meet without the member
    have hs' : (ys.eraseIdx i).Pairwise RelLE := hs.sublist (List.eraseIdx_sublist ys i)
    have hna' : ∀ x ∈ ys.eraseIdx i, NotAnd x := fun x h => hna x (List.mem_of_mem_eraseIdx h)
    have hperm' : (ys.eraseIdx i).Perm (A ++ C') := by
      have h₁ : (ys[i] :: ys.eraseIdx i).Perm ys := List.getElem_cons_eraseIdx_perm hi
      have h₂ : ys.Perm (ys[i] :: (A ++ C')) := by
        rw [hci]; exact hperm.trans List.perm_middle
      exact (h₁.trans h₂).cons_inv
    have hprod : ∀ w : Kind × GoalOf R Rel × GoalOf R Rel,
        w ∈ (splitsOf (K := DerivationKernel.over D K hK P) (bare (mkAnd ys)) (.meet ys)).val →
        ∀ ts : List (TableOf R Rel (Ans D P)), ∀ s,
          s ∈ (way (K := DerivationKernel.over D K hK P) ts (bare (mkAnd ys)) w).val.2 →
          s ∈ (produceTables (K := DerivationKernel.over D K hK P) ts (bare (mkAnd ys))).val.2 := by
      intro w hw ts s hs
      rw [produceTables_meet K hK ts _ hvf]
      exact List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, hw, rfl⟩, hs⟩
    have hwo : ∀ k, k < ys.length → (mkAnd ys).without k = some (mkAnd (ys.eraseIdx k)) := by
      intro k hk
      unfold RelOf.without
      simp only [RelOf.meetParts]
      rw [andParts_mkAnd (List.ne_nil_of_length_pos (by omega)) hna, ite_of_pos ⟨hk, by omega⟩]
    by_cases hsplit : i ∈ andSplits ys.length
    · have hw : ((Kind.and, bare ys[i], bare (mkAnd (ys.eraseIdx i))) :
          Kind × GoalOf R Rel × GoalOf R Rel) ∈
          (splitsOf (K := DerivationKernel.over D K hK P) (bare (mkAnd ys)) (.meet ys)).val :=
        (mem_splitsOf_meet K hK _ _ _).2 ⟨i, hsplit, _, _, List.getElem?_eq_getElem hi, hwo i hi, rfl⟩
      have hS := andSplit_of_mem K hK hg hvf hw
      obtain ⟨hvoid, hdone⟩ := ih (ys.eraseIdx i) C' hC' hs' hperm' hna' hS.rok
      exact ⟨hS.void_right hL hg hvoid, done_of_side hL hP hU hroot (hS.void_right hL hg hvoid)
        (hprod _ hw) (.inr rfl) hvoid hdone⟩
    · have h2 : ys.length = 2 ∧ i = 1 := by
        unfold andSplits at hsplit
        split at hsplit
        · simp only [List.mem_singleton] at hsplit; omega
        · exact absurd (List.mem_range.2 hi) hsplit
      obtain ⟨hl2, rfl⟩ := h2
      have h0 : 0 < ys.length := by omega
      have he : mkAnd (ys.eraseIdx 1) = ys[0] :=
        mkAnd_eraseIdx_one hl2 (List.getElem?_eq_getElem h0)
      have hw : ((Kind.and, bare ys[0], bare (mkAnd (ys.eraseIdx 0))) :
          Kind × GoalOf R Rel × GoalOf R Rel) ∈
          (splitsOf (K := DerivationKernel.over D K hK P) (bare (mkAnd ys)) (.meet ys)).val :=
        (mem_splitsOf_meet K hK _ _ _).2 ⟨0, by unfold andSplits; split <;> simp; omega, _, _,
          List.getElem?_eq_getElem h0, hwo 0 h0, rfl⟩
      have hS := andSplit_of_mem K hK hg hvf hw
      have hlok : GoalOk D (bare (mkAnd (ys.eraseIdx 1)) : GoalOf R Rel) := by
        rw [he]; exact hS.lok
      obtain ⟨hvoid, hdone⟩ := ih (ys.eraseIdx 1) C' hC' hs' hperm' hna' hlok
      rw [he] at hvoid hdone
      exact ⟨hS.void_left hL hg hvoid, done_of_side hL hP hU hroot (hS.void_left hL hg hvoid)
        (hprod _ hw) (.inl rfl) hvoid hdone⟩

end ladder

end Tabled

end RwLog
