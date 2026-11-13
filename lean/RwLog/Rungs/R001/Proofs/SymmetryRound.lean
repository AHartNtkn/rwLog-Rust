/-
# Rung R001, Symmetry: rounds of a run and of its mirror

One round of the run and one round of the mirrored run keep the tables in
correspondence (`StRel`): corresponding tables gain corresponding answers
(`produce_mirror`, `fresh_stepEquiv`, `fresh_map_swap`), complete in the same
round (the completing set is the greatest closed subset of the candidates,
and closed sets correspond through mirrored strategies), and the requested
goals open corresponding new tables. The root emits corresponding answers.
By induction over the trace, `dual_trace` follows.
-/
import RwLog.Rungs.R001.Proofs.SymmetryProduce

namespace RwLog

namespace R001

namespace Symmetry

/-! ## The round, restated -/

/-- The candidates a table computes in a round. -/
def candsOf (P : Program) (d : Nat) (ts : Tables) (t : Table) : List Span :=
  if t.done then [] else (produce P d ts t.goal).1

/-- The goals a table requests in a round. -/
def reqsOfT (P : Program) (d : Nat) (ts : Tables) (t : Table) : List Goal :=
  if t.done then [] else (produce P d ts t.goal).2

/-- A table after this round's answers were added. -/
def upd (P : Program) (d : Nat) (ts : Tables) (t : Table) : Table :=
  { t with answers := t.answers ++ fresh t.answers (candsOf P d ts t) }

/-- The keys requested in a round. -/
def reqsOf (P : Program) (d : Nat) (ts : Tables) : List Goal :=
  (ts.flatMap (reqsOfT P d ts)).map fun g => g.norm.2

/-- The new keys of a round: requested keys without a table, once each. -/
def newOf (ts : Tables) (reqs : List Goal) : List Goal :=
  reqs.foldl
    (fun acc g => if ts.any (fun t => t.goal.same g) || acc.any (fun h => h.same g) then acc else acc ++ [g]) []

theorem round_eq (st : State) :
    round st =
      (⟨st.P,
        ((st.tables.map (upd st.P st.depth st.tables)).mapIdx fun i t =>
            if (completing st.P st.depth st.tables (st.tables.map (upd st.P st.depth st.tables))).contains i
            then { t with done := true } else t) ++
          (newOf st.tables (reqsOf st.P st.depth st.tables)).map fun g => ⟨g, [], false⟩,
        st.rootFlip, st.depth + 1⟩,
       orient st.rootFlip (match st.tables.head?, (st.tables.map (upd st.P st.depth st.tables)).head? with
        | some t, some t' => t'.answers.drop t.answers.length
        | _, _ => [])) := by
  have h1 : ((st.tables.zip (st.tables.map fun t =>
      if t.done then (([] : List Span), ([] : List Goal)) else produce st.P st.depth st.tables t.goal)).map
        fun p => { p.1 with answers := p.1.answers ++ fresh p.1.answers p.2.1 }) =
      st.tables.map (upd st.P st.depth st.tables) := by
    rw [map_zip_map_self]
    congr 1; funext t
    simp only [upd, candsOf]
    split <;> rfl
  have h2 : ((st.tables.map fun t =>
      if t.done then (([] : List Span), ([] : List Goal)) else produce st.P st.depth st.tables t.goal).flatMap
        Prod.snd).map (fun g => g.norm.2) = reqsOf st.P st.depth st.tables := by
    simp only [reqsOf, List.flatMap_map]
    congr 2; funext t
    unfold reqsOfT
    split <;> rfl
  unfold round
  simp only [h1, h2]
  rfl

/-! ## New keys -/

section NewKeys

variable (ts : Tables)

def addKey (acc : List Goal) (g : Goal) : List Goal :=
  if ts.any (fun t => t.goal.same g) || acc.any (fun h => h.same g) then acc else acc ++ [g]

theorem newOf_eq (reqs : List Goal) : newOf ts reqs = reqs.foldl (addKey ts) [] := rfl

theorem foldl_addKey : ∀ (reqs acc : List Goal),
    (∀ g ∈ reqs.foldl (addKey ts) acc, g ∈ acc ∨ (g ∈ reqs ∧ ∀ t ∈ ts, t.goal.same g = false)) ∧
    (∀ r ∈ reqs, (∃ t ∈ ts, t.goal.same r = true) ∨ ∃ g ∈ reqs.foldl (addKey ts) acc, g.same r = true) ∧
    (∀ g ∈ acc, g ∈ reqs.foldl (addKey ts) acc) ∧
    (acc.Pairwise (fun g h => g.same h = false) →
      (reqs.foldl (addKey ts) acc).Pairwise (fun g h => g.same h = false))
  | [], acc => by simp
  | r :: reqs, acc => by
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := foldl_addKey reqs (addKey ts acc r)
    simp only [List.foldl_cons]
    unfold addKey at ih₁ ih₂ ih₃ ih₄ ⊢
    by_cases hc : (ts.any (fun t => t.goal.same r) || acc.any (fun h => h.same r)) = true
    · simp only [hc, ite_true] at ih₁ ih₂ ih₃ ih₄ ⊢
      refine ⟨fun g hg => ?_, fun x hx => ?_, ih₃, ih₄⟩
      · rcases ih₁ g hg with h | ⟨h, h'⟩
        · exact .inl h
        · exact .inr ⟨List.mem_cons_of_mem _ h, h'⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · simp only [Bool.or_eq_true, List.any_eq_true] at hc
          rcases hc with ⟨t, ht, e⟩ | ⟨h, hh, e⟩
          · exact .inl ⟨t, ht, e⟩
          · exact .inr ⟨h, ih₃ h hh, e⟩
        · exact ih₂ x hx
    · simp only [hc, Bool.false_eq_true, ite_false] at ih₁ ih₂ ih₃ ih₄ ⊢
      simp only [Bool.or_eq_true, List.any_eq_true, not_or, not_exists, not_and] at hc
      refine ⟨fun g hg => ?_, fun x hx => ?_, fun g hg => ih₃ g (List.mem_append_left _ hg), fun hp => ?_⟩
      · rcases ih₁ g hg with h | ⟨h, h'⟩
        · rcases List.mem_append.1 h with h | h
          · exact .inl h
          · rw [List.mem_singleton.1 h]
            exact .inr ⟨List.mem_cons_self .., fun t ht => by simpa using hc.1 t ht⟩
        · exact .inr ⟨List.mem_cons_of_mem _ h, h'⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact .inr ⟨x, ih₃ x (by simp), GoalOf.same_refl x⟩
        · exact ih₂ x hx
      · apply ih₄
        rw [List.pairwise_append]
        refine ⟨hp, List.pairwise_singleton _ _, fun g hg h hh => ?_⟩
        rw [List.mem_singleton.1 hh]
        simpa using hc.2 g hg

theorem mem_newOf {reqs : List Goal} {g : Goal} (h : g ∈ newOf ts reqs) :
    g ∈ reqs ∧ ∀ t ∈ ts, t.goal.same g = false := by
  rw [newOf_eq] at h
  rcases (foldl_addKey ts reqs []).1 g h with h | h
  · cases h
  · exact h

theorem newOf_cover {reqs : List Goal} {r : Goal} (h : r ∈ reqs) :
    (∃ t ∈ ts, t.goal.same r = true) ∨ ∃ g ∈ newOf ts reqs, g.same r = true := by
  rw [newOf_eq]; exact (foldl_addKey ts reqs []).2.1 r h

theorem newOf_pairwise (reqs : List Goal) :
    (newOf ts reqs).Pairwise (fun g h => g.same h = false) := by
  rw [newOf_eq]; exact (foldl_addKey ts reqs []).2.2.2 List.Pairwise.nil

end NewKeys

/-! ## The completing set is the greatest closed set -/

theorem filter_length_eq {α : Type} {p : α → Bool} : ∀ {l : List α},
    (l.filter p).length = l.length → ∀ x ∈ l, p x = true
  | [], _, x, hx => by cases hx
  | y :: l, h, x, hx => by
    by_cases hy : p y = true
    · rw [List.filter_cons_of_pos hy, List.length_cons, List.length_cons] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hy
      · exact filter_length_eq (by omega) x hx
    · rw [List.filter_cons_of_neg hy, List.length_cons] at h
      have := List.length_filter_le p l
      omega

theorem mem_gfpFrom {ok : List Nat → Nat → Bool}
    (mono : ∀ X Y i, (∀ k ∈ X, k ∈ Y) → ok X i = true → ok Y i = true) :
    ∀ (n : Nat) (S : List Nat), S.length ≤ n → ∀ i,
      (i ∈ gfpFrom ok n S ↔ ∃ X : List Nat, (∀ x ∈ X, x ∈ S ∧ ok X x = true) ∧ i ∈ X)
  | 0, S, hS, i => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hS)]
    simp only [gfpFrom, List.not_mem_nil, false_iff, not_exists, not_and]
    intro X hX hi
    exact (hX i hi).1
  | n + 1, S, hS, i => by
    simp only [gfpFrom]
    split
    · rename_i heq
      have hall := filter_length_eq heq
      constructor
      · intro hi; exact ⟨S, fun x hx => ⟨hx, hall x hx⟩, hi⟩
      · rintro ⟨X, hX, hi⟩; exact (hX i hi).1
    · rename_i hne
      have hlt : (S.filter (ok S)).length ≤ n := by
        have := List.length_filter_le (ok S) S
        omega
      rw [mem_gfpFrom mono n _ hlt i]
      constructor
      · rintro ⟨X, hX, hi⟩
        exact ⟨X, fun x hx => ⟨(List.mem_filter.1 (hX x hx).1).1, (hX x hx).2⟩, hi⟩
      · rintro ⟨X, hX, hi⟩
        refine ⟨X, fun x hx => ⟨List.mem_filter.2 ⟨(hX x hx).1, ?_⟩, (hX x hx).2⟩, hi⟩
        exact mono X S x (fun k hk => (hX k hk).1) (hX x hx).2

/-! ## Positions of corresponding tables -/

theorem indexOf_some {ts : Tables} {K : Goal} {k : Nat} (h : indexOf ts K = some k) :
    ∃ hk : k < ts.length, findTable ts K = some ts[k] := by
  unfold indexOf at h
  obtain ⟨hk, hp, hfirst⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  refine ⟨hk, ?_⟩
  unfold findTable
  exact List.find?_eq_some_iff_getElem.2 ⟨hp, k, hk, rfl, fun j hj => by simpa using hfirst j hj⟩

theorem indexOf_of_findTable {ts : Tables} {K : Goal} {t : Table} (h : findTable ts K = some t) :
    ∃ k, ∃ hk : k < ts.length, indexOf ts K = some k ∧ ts[k] = t := by
  unfold findTable at h
  obtain ⟨hp, k, hk, rfl, hfirst⟩ := List.find?_eq_some_iff_getElem.1 h
  refine ⟨k, hk, ?_, rfl⟩
  unfold indexOf
  exact List.findIdx?_eq_some_iff_getElem.2 ⟨hk, hp, fun j hj => by simpa using hfirst j hj⟩

theorem indexOf_none {ts : Tables} {K : Goal} (h : findTable ts K = none) : indexOf ts K = none := by
  unfold findTable at h
  unfold indexOf
  rw [List.findIdx?_eq_none_iff]
  intro t ht
  simpa using List.find?_eq_none.1 h t ht

/-- Position `i` of the run's tables and position `j` of the mirror's hold
corresponding tables. -/
def IR (tsA tsB : Tables) (i j : Nat) : Prop :=
  ∃ (hi : i < tsA.length) (hj : j < tsB.length), TabRel tsA[i] tsB[j]

theorem idx_fwd {tsA tsB : Tables} (R : TabsRel tsA tsB) {i : Nat} (hi : i < tsA.length) :
    ∃ j, IR tsA tsB i j := by
  obtain ⟨tB, htB, hr⟩ := R.fwd tsA[i] (List.getElem_mem hi)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 htB
  exact ⟨j, hi, hj, hr⟩

theorem idx_bwd {tsA tsB : Tables} (R : TabsRel tsA tsB) {j : Nat} (hj : j < tsB.length) :
    ∃ i, IR tsA tsB i j := by
  obtain ⟨tA, htA, hr⟩ := R.bwd tsB[j] (List.getElem_mem hj)
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 htA
  exact ⟨i, hi, hj, hr⟩

/-- Mirrored goals find corresponding positions, or none. -/
theorem indexOf_mirror {tsA tsB : Tables} (R : TabsRel tsA tsB) {g h : Goal} (hm : Mirror g h) :
    (∀ j, indexOf tsA g.norm.2 = some j → ∃ k, indexOf tsB h.norm.2 = some k ∧ IR tsA tsB j k) ∧
      (∀ k, indexOf tsB h.norm.2 = some k → ∃ j, indexOf tsA g.norm.2 = some j ∧ IR tsA tsB j k) := by
  rcases findTable_mirror R (isKey_norm g) hm.2 with ⟨tA, tB, hA, hB, hr⟩ | ⟨hA, hB⟩
  · obtain ⟨j, hj, hiA, rfl⟩ := indexOf_of_findTable hA
    obtain ⟨k, hk, hiB, rfl⟩ := indexOf_of_findTable hB
    refine ⟨fun j' hj' => ?_, fun k' hk' => ?_⟩
    · rw [hiA] at hj'; cases hj'; exact ⟨k, hiB, hj, hk, hr⟩
    · rw [hiB] at hk'; cases hk'; exact ⟨j, hiA, hj, hk, hr⟩
  · refine ⟨fun j hj => ?_, fun k hk => ?_⟩
    · rw [indexOf_none hA] at hj; cases hj
    · rw [indexOf_none hB] at hk; cases hk

/-! ## Tables gain corresponding answers -/

section Upd

variable {P : Program} (hK : Obligation.SimplifyRespectsEquiv P.theory) {tsA tsB : Tables}
  (R : TabsRel tsA tsB) (d : Nat)

include hK R

theorem cands_mirror {tA tB : Table} (hA : tA ∈ tsA) (hr : TabRel tA tB) :
    ClassEq (candsOf P.dual d tsB tB) ((candsOf P d tsA tA).map Span.swap) := by
  unfold candsOf
  rw [hr.2.2]
  split
  · exact ClassEq.refl _
  · exact (produce_mirror hK R (R.keyA tA hA) hr.1 d).1

theorem fresh_mirror {tA tB : Table} (hA : tA ∈ tsA) (hr : TabRel tA tB) :
    StepEquiv (fresh tB.answers (candsOf P.dual d tsB tB))
      ((fresh tA.answers (candsOf P d tsA tA)).map Span.swap) := by
  rw [← fresh_map_swap]
  exact fresh_stepEquiv (ClassEq.of_stepEquiv hr.2.1) (cands_mirror hK R d hA hr)

theorem upd_rel {tA tB : Table} (hA : tA ∈ tsA) (hr : TabRel tA tB) :
    TabRel (upd P d tsA tA) (upd P.dual d tsB tB) := by
  refine ⟨hr.1, ?_, hr.2.2⟩
  simp only [upd, List.map_append]
  exact hr.2.1.append (fresh_mirror hK R d hA hr)

end Upd

/-! ## Completion corresponds -/

def gainedC (ts ts' : Tables) (j : Nat) : Bool :=
  decide ((ts'.getD j dflt).answers.length ≠ (ts.getD j dflt).answers.length)

def isDoneC (ts : Tables) (j : Nat) : Bool := (ts.getD j dflt).done

def S0C (ts ts' : Tables) : List Nat :=
  (List.range ts.length).filter fun i => !isDoneC ts i && !gainedC ts ts' i

def okC (P : Program) (d : Nat) (ts ts' : Tables) (S : List Nat) (i : Nat) : Bool :=
  (strategies P d ts (ts.getD i dflt).goal).any fun deps =>
    deps.all fun g =>
      match indexOf ts g.norm.2 with
      | none => false
      | some j => !gainedC ts ts' j && (isDoneC ts j || S.contains j)

theorem completing_eq (P : Program) (d : Nat) (ts ts' : Tables) :
    completing P d ts ts' = gfpFrom (okC P d ts ts') (S0C ts ts').length (S0C ts ts') := rfl

theorem okC_mono (P : Program) (d : Nat) (ts ts' : Tables) :
    ∀ X Y i, (∀ k ∈ X, k ∈ Y) → okC P d ts ts' X i = true → okC P d ts ts' Y i = true := by
  intro X Y i hXY h
  simp only [okC, List.any_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨deps, hd, hall⟩ := h
  refine ⟨deps, hd, fun g hg => ?_⟩
  have := hall g hg
  cases hj : indexOf ts g.norm.2 with
  | none => simp [hj] at this
  | some j =>
    simp only [hj, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true,
      List.contains_iff_mem] at this ⊢
    exact ⟨this.1, this.2.imp_right (hXY j)⟩

theorem mem_completing (P : Program) (d : Nat) (ts ts' : Tables) (i : Nat) :
    i ∈ completing P d ts ts' ↔
      ∃ X : List Nat, (∀ x ∈ X, x ∈ S0C ts ts' ∧ okC P d ts ts' X x = true) ∧ i ∈ X := by
  rw [completing_eq]
  exact mem_gfpFrom (okC_mono P d ts ts') _ _ le_rfl i

/-- A closed set of one run gives a closed set of the other through a
relation of positions. -/
theorem closed_transfer {okA okB : List Nat → Nat → Bool} {SA SB : List Nat} {n : Nat}
    (Q : Nat → Nat → Prop) (hn : ∀ i j, Q i j → j < n) (hS : ∀ i j, Q i j → i ∈ SA → j ∈ SB)
    (hok : ∀ X X' i j, Q i j → (∀ x ∈ X, ∀ y, Q x y → y ∈ X') → okA X i = true → okB X' j = true)
    {X : List Nat} (hX : ∀ x ∈ X, x ∈ SA ∧ okA X x = true) {i j : Nat} (hi : i ∈ X) (hq : Q i j) :
    ∃ X' : List Nat, (∀ x ∈ X', x ∈ SB ∧ okB X' x = true) ∧ j ∈ X' := by
  classical
  let X' := (List.range n).filter fun y => decide (∃ x ∈ X, Q x y)
  have hmem : ∀ y, y ∈ X' ↔ ∃ x ∈ X, Q x y := by
    intro y
    simp only [X', List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · rintro ⟨x, hx, q⟩; exact ⟨hn x y q, x, hx, q⟩
  refine ⟨X', fun y hy => ?_, (hmem j).2 ⟨i, hi, hq⟩⟩
  obtain ⟨x, hx, q⟩ := (hmem y).1 hy
  exact ⟨hS x y q (hX x hx).1,
    hok X X' x y q (fun x' hx' y' q' => (hmem y').2 ⟨x', hx', q'⟩) (hX x hx).2⟩

theorem getD_lt {ts : Tables} {i : Nat} (hi : i < ts.length) (t : Table) : ts.getD i t = ts[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

section Completing

variable {P : Program} (hK : Obligation.SimplifyRespectsEquiv P.theory) {tsA tsB : Tables}
  (R : TabsRel tsA tsB) (d : Nat)

theorem gainedC_upd {P : Program} {d : Nat} {ts : Tables} {i : Nat} (hi : i < ts.length) :
    gainedC ts (ts.map (upd P d ts)) i = decide ((fresh ts[i].answers (candsOf P d ts ts[i])).length ≠ 0) := by
  simp only [gainedC, getD_lt hi,
    getD_lt (by simpa using hi : i < (ts.map (upd P d ts)).length),
    List.getElem_map, upd, List.length_append]
  congr 1
  apply propext
  omega

theorem isDoneC_lt {ts : Tables} {i : Nat} (hi : i < ts.length) : isDoneC ts i = ts[i].done := by
  simp only [isDoneC, getD_lt hi]

include hK R in
theorem IR.gained {i j : Nat} (h : IR tsA tsB i j) :
    gainedC tsB (tsB.map (upd P.dual d tsB)) j = gainedC tsA (tsA.map (upd P d tsA)) i := by
  obtain ⟨hi, hj, hr⟩ := h
  rw [gainedC_upd hi, gainedC_upd hj, (fresh_mirror hK R d (List.getElem_mem hi) hr).length,
    List.length_map]

theorem IR.done {i j : Nat} (h : IR tsA tsB i j) : isDoneC tsB j = isDoneC tsA i := by
  obtain ⟨hi, hj, hr⟩ := h
  rw [isDoneC_lt hi, isDoneC_lt hj, hr.2.2]

include hK R in
theorem IR.S0 {i j : Nat} (h : IR tsA tsB i j) :
    (j ∈ S0C tsB (tsB.map (upd P.dual d tsB)) ↔ i ∈ S0C tsA (tsA.map (upd P d tsA))) := by
  simp only [S0C, List.mem_filter, List.mem_range, IR.done h, IR.gained hK R d h, h.1, h.2.1, true_and]

include hK R in
theorem ok_fwd {X X' : List Nat} {i j : Nat} (h : IR tsA tsB i j)
    (hX : ∀ x ∈ X, ∀ y, IR tsA tsB x y → y ∈ X')
    (ok : okC P d tsA (tsA.map (upd P d tsA)) X i = true) :
    okC P.dual d tsB (tsB.map (upd P.dual d tsB)) X' j = true := by
  obtain ⟨hi, hj, hr⟩ := h
  simp only [okC, getD_lt hi, getD_lt hj, List.any_eq_true,
    List.all_eq_true] at ok ⊢
  obtain ⟨deps, hd, hall⟩ := ok
  obtain ⟨deps', hd', hm⟩ :=
    (produce_mirror hK R (R.keyA _ (List.getElem_mem hi)) hr.1 d).2.2.1 deps hd
  refine ⟨deps', hd', fun g' hg' => ?_⟩
  obtain ⟨g, hg, hmg⟩ := hm.2 g' hg'
  have := hall g hg
  cases hk : indexOf tsA g.norm.2 with
  | none => simp [hk] at this
  | some k =>
    obtain ⟨k', hk', ir⟩ := (indexOf_mirror R hmg).1 k hk
    simp only [hk, hk', ir.done, ir.gained hK R d, Bool.and_eq_true, Bool.or_eq_true,
      List.contains_iff_mem] at this ⊢
    exact ⟨this.1, this.2.imp_right fun hx => hX k hx k' ir⟩

include hK R in
theorem ok_bwd {Y Y' : List Nat} {i j : Nat} (h : IR tsA tsB i j)
    (hY : ∀ y ∈ Y, ∀ x, IR tsA tsB x y → x ∈ Y')
    (ok : okC P.dual d tsB (tsB.map (upd P.dual d tsB)) Y j = true) :
    okC P d tsA (tsA.map (upd P d tsA)) Y' i = true := by
  obtain ⟨hi, hj, hr⟩ := h
  simp only [okC, getD_lt hi, getD_lt hj, List.any_eq_true,
    List.all_eq_true] at ok ⊢
  obtain ⟨deps', hd', hall⟩ := ok
  obtain ⟨deps, hd, hm⟩ :=
    (produce_mirror hK R (R.keyA _ (List.getElem_mem hi)) hr.1 d).2.2.2 deps' hd'
  refine ⟨deps, hd, fun g hg => ?_⟩
  obtain ⟨g', hg', hmg⟩ := hm.1 g hg
  have := hall g' hg'
  cases hk' : indexOf tsB g'.norm.2 with
  | none => simp [hk'] at this
  | some k' =>
    obtain ⟨k, hk, ir⟩ := (indexOf_mirror R hmg).2 k' hk'
    simp only [hk, hk', ← ir.done, ← ir.gained hK R d, Bool.and_eq_true, Bool.or_eq_true,
      List.contains_iff_mem] at this ⊢
    exact ⟨this.1, this.2.imp_right fun hy => hY k' hy k ir⟩

include hK R in
/-- Corresponding tables complete in the same round. -/
theorem completing_mirror {i j : Nat} (h : IR tsA tsB i j) :
    j ∈ completing P.dual d tsB (tsB.map (upd P.dual d tsB)) ↔
      i ∈ completing P d tsA (tsA.map (upd P d tsA)) := by
  rw [mem_completing, mem_completing]
  constructor
  · rintro ⟨Y, hY, hj⟩
    exact closed_transfer (fun j i => IR tsA tsB i j) (fun _ _ q => q.1)
      (fun _ _ q hy => (q.S0 hK R d).1 hy)
      (fun _ _ _ _ q hYY ok => ok_bwd hK R d q hYY ok) hY hj h
  · rintro ⟨X, hX, hi⟩
    exact closed_transfer (IR tsA tsB) (fun _ _ q => q.2.1)
      (fun _ _ q hx => (q.S0 hK R d).2 hx)
      (fun _ _ _ _ q hXX ok => ok_fwd hK R d q hXX ok) hX hi h

end Completing

/-! ## Requested keys correspond -/

section Reqs

variable {P : Program} (hK : Obligation.SimplifyRespectsEquiv P.theory) {tsA tsB : Tables}
  (R : TabsRel tsA tsB) (d : Nat)

theorem isKey_reqs {P : Program} {d : Nat} {ts : Tables} {g : Goal} (h : g ∈ reqsOf P d ts) :
    IsKey g := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.1 h
  exact isKey_norm r

include hK R

theorem reqs_fwd {g : Goal} (h : g ∈ reqsOf P d tsA) :
    ∃ g' ∈ reqsOf P.dual d tsB, g'.same (KD g) = true := by
  simp only [reqsOf, List.mem_map, List.mem_flatMap] at h
  obtain ⟨r, ⟨tA, htA, hr⟩, rfl⟩ := h
  obtain ⟨tB, htB, hT⟩ := R.fwd tA htA
  unfold reqsOfT at hr
  split at hr
  · cases hr
  · rename_i hd
    obtain ⟨k, hk, m⟩ := (produce_mirror hK R (R.keyA tA htA) hT.1 d).2.1.1 r hr
    refine ⟨k.norm.2, ?_, m.2⟩
    simp only [reqsOf, List.mem_map, List.mem_flatMap]
    refine ⟨k, ⟨tB, htB, ?_⟩, rfl⟩
    unfold reqsOfT
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hT.2.2]; exact hd))]
    exact hk

theorem reqs_bwd {g' : Goal} (h : g' ∈ reqsOf P.dual d tsB) :
    ∃ g ∈ reqsOf P d tsA, g'.same (KD g) = true := by
  simp only [reqsOf, List.mem_map, List.mem_flatMap] at h
  obtain ⟨k, ⟨tB, htB, hk⟩, rfl⟩ := h
  obtain ⟨tA, htA, hT⟩ := R.bwd tB htB
  unfold reqsOfT at hk
  split at hk
  · cases hk
  · rename_i hd
    obtain ⟨r, hr, m⟩ := (produce_mirror hK R (R.keyA tA htA) hT.1 d).2.1.2 k hk
    refine ⟨r.norm.2, ?_, m.2⟩
    simp only [reqsOf, List.mem_map, List.mem_flatMap]
    refine ⟨r, ⟨tA, htA, ?_⟩, rfl⟩
    unfold reqsOfT
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [← hT.2.2]; exact hd))]
    exact hr

theorem new_fwd {g : Goal} (h : g ∈ newOf tsA (reqsOf P d tsA)) :
    ∃ g' ∈ newOf tsB (reqsOf P.dual d tsB), g'.same (KD g) = true := by
  obtain ⟨hg, hfresh⟩ := mem_newOf tsA h
  obtain ⟨g₁, hg₁, hs⟩ := reqs_fwd hK R d hg
  rcases newOf_cover tsB hg₁ with ⟨t, ht, e⟩ | ⟨g', hg', e⟩
  · exfalso
    obtain ⟨tA, htA, hT⟩ := R.bwd t ht
    have : tA.goal.same g = true :=
      same_of_KD_same (R.keyA tA htA) (isKey_reqs hg)
        (GoalOf.same_trans (GoalOf.same_symm hT.1) (GoalOf.same_trans e hs))
    rw [hfresh tA htA] at this; cases this
  · exact ⟨g', hg', GoalOf.same_trans e hs⟩

theorem new_bwd {g' : Goal} (h : g' ∈ newOf tsB (reqsOf P.dual d tsB)) :
    ∃ g ∈ newOf tsA (reqsOf P d tsA), g'.same (KD g) = true := by
  obtain ⟨hg', hfresh⟩ := mem_newOf tsB h
  obtain ⟨g₁, hg₁, hs⟩ := reqs_bwd hK R d hg'
  rcases newOf_cover tsA hg₁ with ⟨t, ht, e⟩ | ⟨g, hg, e⟩
  · exfalso
    obtain ⟨tB, htB, hT⟩ := R.fwd t ht
    have : tB.goal.same g' = true :=
      GoalOf.same_trans hT.1 (GoalOf.same_trans (KD_same e) (GoalOf.same_symm hs))
    rw [hfresh tB htB] at this; cases this
  · exact ⟨g, hg, GoalOf.same_trans hs (GoalOf.same_symm (KD_same e))⟩

end Reqs

/-! ## The tables after a round correspond -/

/-- New tables for new keys. -/
def mkT (g : Goal) : Table := ⟨g, [], false⟩

theorem mem_mkT {gs : List Goal} {t : Table} (h : t ∈ gs.map mkT) : ∃ g ∈ gs, t = mkT g := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h
  exact ⟨g, hg, rfl⟩

theorem mem_goals {ts ts' : Tables} (hg : ts'.map TableOf.goal = ts.map TableOf.goal) {t : Table}
    (ht : t ∈ ts') : ∃ t₀ ∈ ts, t₀.goal = t.goal := by
  have : t.goal ∈ ts.map TableOf.goal := hg ▸ List.mem_map_of_mem ht
  exact List.mem_map.1 this

/-- Old tables updated position by position, and new tables for keys that
correspond, give corresponding tables. -/
theorem tabsRel_extend {tsA tsB ts2A ts2B : Tables} (R : TabsRel tsA tsB)
    (hgA : ts2A.map TableOf.goal = tsA.map TableOf.goal) (hgB : ts2B.map TableOf.goal = tsB.map TableOf.goal)
    (hT : ∀ i j (hi : i < ts2A.length) (hj : j < ts2B.length), IR tsA tsB i j → TabRel ts2A[i] ts2B[j])
    {nA nB : List Goal} (kA : ∀ g ∈ nA, IsKey g) (kB : ∀ g ∈ nB, IsKey g)
    (pA : nA.Pairwise fun g h => g.same h = false) (pB : nB.Pairwise fun g h => g.same h = false)
    (fA : ∀ g ∈ nA, ∀ t ∈ tsA, t.goal.same g = false) (fB : ∀ g ∈ nB, ∀ t ∈ tsB, t.goal.same g = false)
    (nf : ∀ g ∈ nA, ∃ g' ∈ nB, g'.same (KD g) = true) (nb : ∀ g' ∈ nB, ∃ g ∈ nA, g'.same (KD g) = true) :
    TabsRel (ts2A ++ nA.map mkT) (ts2B ++ nB.map mkT) := by
  have hlA : ts2A.length = tsA.length := by simpa using congrArg List.length hgA
  have hlB : ts2B.length = tsB.length := by simpa using congrArg List.length hgB
  have keys : ∀ {ts ts2 : Tables} {ns : List Goal}, (∀ t ∈ ts, IsKey t.goal) →
      ts2.map TableOf.goal = ts.map TableOf.goal → (∀ g ∈ ns, IsKey g) →
      ∀ t ∈ ts2 ++ ns.map mkT, IsKey t.goal := by
    intro ts ts2 ns k hg kn t ht
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨t₀, ht₀, e⟩ := mem_goals hg ht
      exact e ▸ k t₀ ht₀
    · obtain ⟨g, hg, rfl⟩ := mem_mkT ht
      exact kn g hg
  have nd : ∀ {ts ts2 : Tables} {ns : List Goal}, (ts.Pairwise fun t t' => t.goal.same t'.goal = false) →
      ts2.map TableOf.goal = ts.map TableOf.goal → (ns.Pairwise fun g h => g.same h = false) →
      (∀ g ∈ ns, ∀ t ∈ ts, t.goal.same g = false) →
      (ts2 ++ ns.map mkT).Pairwise fun t t' => t.goal.same t'.goal = false := by
    intro ts ts2 ns n hg pn fn
    rw [List.pairwise_append]
    refine ⟨?_, ?_, fun t ht t' ht' => ?_⟩
    · have h1 : (ts.map TableOf.goal).Pairwise (fun g h : Goal => g.same h = false) :=
        List.pairwise_map.2 n
      rw [← hg] at h1
      exact List.pairwise_map.1 h1
    · rw [List.pairwise_map]; exact pn
    · obtain ⟨t₀, ht₀, e⟩ := mem_goals hg ht
      obtain ⟨g, hg', rfl⟩ := mem_mkT ht'
      rw [← e]; exact fn g hg' t₀ ht₀
  refine ⟨keys R.keyA hgA kA, keys R.keyB hgB kB, nd R.ndA hgA pA fA, nd R.ndB hgB pB fB, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
      obtain ⟨j, hj⟩ := idx_fwd R (hlA ▸ hi)
      exact ⟨ts2B[j]'(hlB ▸ hj.2.1), List.mem_append_left _ (List.getElem_mem _),
        hT i j hi _ hj⟩
    · obtain ⟨g, hg, rfl⟩ := mem_mkT ht
      obtain ⟨g', hg', e⟩ := nf g hg
      exact ⟨mkT g', List.mem_append_right _ (List.mem_map_of_mem hg'), e, StepEquiv.refl _, rfl⟩
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ht
      obtain ⟨i, hi⟩ := idx_bwd R (hlB ▸ hj)
      exact ⟨ts2A[i]'(hlA ▸ hi.1), List.mem_append_left _ (List.getElem_mem _),
        hT i j _ hj hi⟩
    · obtain ⟨g', hg', rfl⟩ := mem_mkT ht
      obtain ⟨g, hg, e⟩ := nb g' hg'
      exact ⟨mkT g, List.mem_append_right _ (List.mem_map_of_mem hg), e, StepEquiv.refl _, rfl⟩

/-- Mark the completing tables done. -/
def mark (S : List Nat) (ts : Tables) : Tables :=
  ts.mapIdx fun i t => if S.contains i then { t with done := true } else t

theorem mark_goals (S : List Nat) (P : Program) (d : Nat) (ts : Tables) :
    (mark S (ts.map (upd P d ts))).map TableOf.goal = ts.map TableOf.goal := by
  apply List.ext_getElem (by simp [mark])
  intro i h₁ h₂
  simp only [mark, List.getElem_map, List.getElem_mapIdx]
  split <;> rfl

/-! ## One round -/

/-- The answers the root gains in a round. -/
def rootNewOf (P : Program) (d : Nat) : Tables → List Span
  | [] => []
  | t :: ts => fresh t.answers (candsOf P d (t :: ts) t)

theorem round_eq' (st : State) :
    round st =
      (⟨st.P,
        mark (completing st.P st.depth st.tables (st.tables.map (upd st.P st.depth st.tables)))
            (st.tables.map (upd st.P st.depth st.tables)) ++
          (newOf st.tables (reqsOf st.P st.depth st.tables)).map mkT,
        st.rootFlip, st.depth + 1⟩,
       orient st.rootFlip (rootNewOf st.P st.depth st.tables)) := by
  rw [round_eq]
  obtain ⟨P, ts, f, d⟩ := st
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [List.head?_cons, List.map_cons, upd, rootNewOf, List.drop_left]
    rfl

/-- The states of a run and of its mirror correspond. -/
structure StRel (P : Program) (stA stB : State) : Prop where
  progA : stA.P = P
  progB : stB.P = P.dual
  tabs : TabsRel stA.tables stB.tables
  head : Option.Rel TabRel stA.tables.head? stB.tables.head?
  flip : stB.rootFlip = stA.rootFlip
  depth : stB.depth = stA.depth

theorem StRel.finished {P : Program} {stA stB : State} (h : StRel P stA stB) :
    stB.finished = stA.finished := by
  have hh := h.head
  unfold StateOf.finished
  revert hh
  cases stA.tables.head? <;> cases stB.tables.head? <;> intro hh
  · rfl
  · cases hh
  · cases hh
  · cases hh with
    | some r => exact r.2.2

theorem orient_stepEquiv {xs ys : List Span} (f : Bool) (h : StepEquiv ys (xs.map Span.swap)) :
    StepEquiv (orient f ys) ((orient f xs).map Span.swap) := by
  rw [← orient_map_swap]
  cases f
  · exact h
  · exact h.map_swap

theorem round_rel {P : Program} (hK : Obligation.SimplifyRespectsEquiv P.theory) {stA stB : State}
    (h : StRel P stA stB) :
    StRel P (round stA).1 (round stB).1 ∧ StepEquiv (round stB).2 ((round stA).2.map Span.swap) := by
  obtain ⟨PA, tsA, fA, dA⟩ := stA
  obtain ⟨PB, tsB, fB, dB⟩ := stB
  obtain ⟨hPA, hPB, R, hh, hf, hd⟩ := h
  simp only at hPA hPB hf hd R hh
  subst hPA hPB
  subst fB
  subst dB
  rw [round_eq', round_eq']
  simp only
  -- corresponding positions keep corresponding tables
  have hT : ∀ i j (hi : i < (mark (completing PA dA tsA (tsA.map (upd PA dA tsA)))
        (tsA.map (upd PA dA tsA))).length)
      (hj : j < (mark (completing PA.dual dA tsB (tsB.map (upd PA.dual dA tsB)))
        (tsB.map (upd PA.dual dA tsB))).length), IR tsA tsB i j →
      TabRel (mark (completing PA dA tsA (tsA.map (upd PA dA tsA))) (tsA.map (upd PA dA tsA)))[i]
        (mark (completing PA.dual dA tsB (tsB.map (upd PA.dual dA tsB)))
          (tsB.map (upd PA.dual dA tsB)))[j] := by
    intro i j _ _ ir
    obtain ⟨hi', hj', hr⟩ := ir
    have u := upd_rel hK R dA (List.getElem_mem hi') hr
    have c := completing_mirror hK R dA ⟨hi', hj', hr⟩
    simp only [mark, List.getElem_mapIdx, List.getElem_map, List.contains_iff_mem]
    by_cases hc : i ∈ completing PA dA tsA (tsA.map (upd PA dA tsA))
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true (c.2 hc))]
      exact ⟨u.1, u.2.1, rfl⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false (fun h => hc (c.1 h)))]
      exact u
  refine ⟨⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · exact tabsRel_extend R (mark_goals _ _ _ _) (mark_goals _ _ _ _) hT
      (fun g hg => isKey_reqs (mem_newOf tsA hg).1) (fun g hg => isKey_reqs (mem_newOf tsB hg).1)
      (newOf_pairwise tsA _) (newOf_pairwise tsB _)
      (fun g hg => (mem_newOf tsA hg).2) (fun g hg => (mem_newOf tsB hg).2)
      (fun g hg => new_fwd hK R dA hg) (fun g hg => new_bwd hK R dA hg)
  · cases tsA with
    | nil =>
      cases tsB with
      | nil => exact Option.Rel.none
      | cons b tsB => cases hh
    | cons a tsA =>
      cases tsB with
      | nil => cases hh
      | cons b tsB =>
        have := hT 0 0 (by simp [mark]) (by simp [mark])
          ⟨by simp, by simp, by cases hh with | some r => exact r⟩
        simpa [mark] using Option.Rel.some this
  · apply orient_stepEquiv
    cases tsA with
    | nil =>
      cases tsB with
      | nil => exact StepEquiv.refl _
      | cons b tsB => cases hh
    | cons a tsA =>
      cases tsB with
      | nil => cases hh
      | cons b tsB =>
        cases hh with
        | some r => exact fresh_mirror hK R dA (List.mem_cons_self ..) r

/-! ## The trace -/

theorem trace_rel {P : Program} (hK : Obligation.SimplifyRespectsEquiv P.theory)
    (n : Nat) (stA stB : State) (h : StRel P stA stB) :
    TraceEquiv (runtime.trace stB n) ((runtime.trace stA n).map (·.map Span.swap)) := by
  rw [TraceEquiv, List.forall₂_map_right_iff]
  refine Runtime.trace_of_sim (R := runtime) (R' := runtime) (Sim := fun b a => StRel P a b)
    (E := fun bs as => StepEquiv bs (as.map Span.swap)) (fun sB sA h => ?_) n stB stA h
  show Step.Rel _ _ (step sB) (step sA)
  unfold step
  rw [h.finished]
  cases sA.finished
  · exact ⟨(round_rel hK h).2, (round_rel hK h).1⟩
  · exact trivial

theorem init_rel (P : Program) (q : Rel) :
    StRel P (runtime.init P q) (runtime.init P.dual q.dual) := by
  have m := mirror_dual (⟨none, q, none⟩ : Goal)
  refine ⟨rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, m.1, rfl⟩
  · intro t ht; rw [List.mem_singleton.1 ht]; exact isKey_norm _
  · intro t ht; rw [List.mem_singleton.1 ht]; exact isKey_norm _
  · exact List.pairwise_singleton _ _
  · exact List.pairwise_singleton _ _
  · intro t ht; rw [List.mem_singleton.1 ht]
    exact ⟨_, List.mem_singleton_self _, m.2, StepEquiv.refl _, rfl⟩
  · intro t ht; rw [List.mem_singleton.1 ht]
    exact ⟨_, List.mem_singleton_self _, m.2, StepEquiv.refl _, rfl⟩
  · exact Option.Rel.some ⟨m.2, StepEquiv.refl _, rfl⟩

/-- **P1.4 strong, for the mirrored program**, for a theory whose
simplification respects equivalent spans. -/
theorem dual_trace_of_respects (P : Program) (q : Rel) (n : Nat)
    (hK : Obligation.SimplifyRespectsEquiv P.theory) :
    TraceEquiv (runtime.trace (runtime.init P.dual q.dual) n)
      ((runtime.trace (runtime.init P q) n).map (·.map Span.swap)) :=
  trace_rel hK n _ _ (init_rel P q)

end Symmetry

/-- **P1.4 strong, for the mirrored program.** Simplification keeps coverage
(`simpLaws_of_wf`), so it respects equivalent spans, which is all the mirrored
run needs. -/
theorem dual_trace : Obligation.dual_trace :=
  fun P q n hwf => Symmetry.dual_trace_of_respects P q n fun _ _ h => (simpLaws_of_wf hwf).respects h


end R001

end RwLog
