/-
# The tabled machine ignores repeated answers of the oracle

An oracle may hand a table the same span more than once. The table takes the
candidates that no old answer covers and keeps one maximal span of each
equivalence class (`fresh`), and a span covers itself, so a second copy of a
span never changes what the table gains. Hence two oracles that agree up to
repeats of earlier spans drive the machine through the same states
(`step_val_of_skips`), and the one with fewer repeats pays no more for
everything that happens after the oracle has answered (`rest_skips`).

* `Thins seen l' l`: `l'` is `l` with some members left out, each of which is
  in `seen` or occurs earlier in `l`. `l.eraseDups` is such a list.
* `Oracle.SkipsRepeats U V`: `U` gives `V`'s verdict, and `V`'s answers with
  some repeats left out.
* `Oracle.ExactModRepeats U`: `U` gives R001's verdict, and R001's answers
  with or without the repeats. The machine with such an oracle is
  `R001.runtime` (`machine_runtime_modRepeats`).
* `spent_le_of_skips`: if moreover one call of `U` costs at most `c` times
  the same call of `V`, then the machine with `U` has spent at most `c` times
  what the machine with `V` has, after any number of steps.
-/
import RwLog.Rungs.Tabled.Exact
import RwLog.Kernel.Covers

namespace RwLog

open R001 Cost

/-! ## Leaving out repeats -/

/-- `l'` is `l` with some members left out, each of which is in `seen` or
occurs earlier in `l`. -/
inductive Thins {α : Type} : List α → List α → List α → Prop
  | nil (seen : List α) : Thins seen [] []
  | keep {seen l' l : List α} (x : α) : Thins (x :: seen) l' l → Thins seen (x :: l') (x :: l)
  | drop {seen l' l : List α} (x : α) : x ∈ seen → Thins seen l' l → Thins seen l' (x :: l)

namespace Thins

variable {α : Type}

theorem refl : ∀ (l seen : List α), Thins seen l l
  | [], seen => .nil seen
  | x :: l, seen => .keep x (refl l (x :: seen))

theorem append {seen l' l : List α} (h : Thins seen l' l) (r : List α) :
    Thins seen (l' ++ r) (l ++ r) := by
  induction h with
  | nil seen => exact refl r seen
  | keep x _ ih => exact .keep x ih
  | drop x hx _ ih => exact .drop x hx ih

theorem filter (p : α → Bool) {seen l' l : List α} (h : Thins seen l' l) :
    Thins (seen.filter p) (l'.filter p) (l.filter p) := by
  induction h with
  | nil seen => exact .nil _
  | keep x _ ih =>
    cases hp : p x
    · simpa only [List.filter_cons, hp, Bool.false_eq_true, ite_false] using ih
    · simp only [List.filter_cons, hp, ite_true] at ih ⊢
      exact .keep x ih
  | drop x hx _ ih =>
    cases hp : p x
    · simpa only [List.filter_cons, hp, Bool.false_eq_true, ite_false] using ih
    · rw [List.filter_cons_of_pos hp]
      exact .drop x (List.mem_filter.2 ⟨hx, hp⟩) ih

theorem mem_of_mem {seen l' l : List α} (h : Thins seen l' l) : ∀ x ∈ l', x ∈ l := by
  induction h with
  | nil seen => exact fun _ hx => hx
  | keep y _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih x hx)
  | drop y _ _ ih => exact fun x hx => List.mem_cons_of_mem _ (ih x hx)

theorem mem_or {seen l' l : List α} (h : Thins seen l' l) : ∀ x ∈ l, x ∈ l' ∨ x ∈ seen := by
  induction h with
  | nil seen => exact fun _ hx => .inl hx
  | keep y _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact .inl List.mem_cons_self
    · rcases ih x hx with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl List.mem_cons_self
        · exact .inr h
  | drop y hy _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact .inr hy
    · exact ih x hx

/-- With nothing seen beforehand, the two lists have the same members. -/
theorem any_eq (p : α → Bool) {l' l : List α} (h : Thins [] l' l) : l'.any p = l.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, h.mem_of_mem x hx, hp⟩
  · rintro ⟨x, hx, hp⟩
    rcases h.mem_or x hx with hx' | hx'
    · exact ⟨x, hx', hp⟩
    · cases hx'

theorem sum_le (w : α → Nat) {seen l' l : List α} (h : Thins seen l' l) :
    (l'.map w).sum ≤ (l.map w).sum := by
  induction h with
  | nil seen => exact Nat.le_refl _
  | keep x _ ih => simp only [List.map_cons, List.sum_cons]; omega
  | drop x _ _ ih => simp only [List.map_cons, List.sum_cons]; omega

theorem eraseDups_filter [DecidableEq α] : ∀ (l seen : List α),
    Thins seen ((l.filter fun x => !seen.contains x).eraseDups) l
  | [], seen => .nil seen
  | y :: t, seen => by
    by_cases hy : y ∈ seen
    · have : (!seen.contains y) = false := by simp [hy]
      rw [List.filter_cons, this]
      exact .drop y hy (eraseDups_filter t seen)
    · have : (!seen.contains y) = true := by simp [hy]
      rw [List.filter_cons, this]
      simp only [ite_true, List.eraseDups_cons, List.filter_filter]
      refine .keep y ?_
      have e : (t.filter fun a => (!a == y) && !seen.contains a) =
          t.filter fun x => !(y :: seen).contains x :=
        List.filter_congr fun a _ => by
          by_cases ha : a = y <;> simp [ha]
      rw [e]
      exact eraseDups_filter t (y :: seen)

/-- A list without its repeats. -/
theorem eraseDups [DecidableEq α] (l : List α) : Thins [] l.eraseDups l := by
  simpa using eraseDups_filter l []

/-- A search that stops at the first hit pays no more on the thinner list,
when nothing that was left out is a hit. -/
theorem anyL_ticks {f : α → Cost Bool} {seen l' l : List α} (h : Thins seen l' l)
    (hs : ∀ z ∈ seen, (f z).val = false) : (anyL f l').ticks ≤ (anyL f l).ticks := by
  induction h with
  | nil seen => exact Nat.le_refl _
  | keep x _ ih =>
    simp only [anyL, bind_ticks]
    cases hx : (f x).val
    · simp only [Bool.false_eq_true, ite_false]
      refine Nat.add_le_add_left (ih fun z hz => ?_) _
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hx
      · exact hs z hz
    · simp
  | drop x hx _ ih =>
    have := ih hs
    simp only [anyL, bind_ticks, hs x hx, Bool.false_eq_true, ite_false]
    omega

end Thins

/-- `U` gives `V`'s verdict, and `V`'s answers with some repeats of earlier
answers left out. -/
def Oracle.SkipsRepeats (U V : Oracle) : Prop :=
  ∀ P d g, (U P d g).val.1 = (V P d g).val.1 ∧ Thins [] (U P d g).val.2 (V P d g).val.2

/-- `U` gives R001's verdict, and R001's answers with or without the
repeats. -/
def Oracle.ExactModRepeats (U : Oracle) : Prop :=
  ∀ P d g, (U P d g).val.1 = unfoldFinal P d g ∧
    ((U P d g).val.2 = unfoldAnswers P d g ∨ (U P d g).val.2 = (unfoldAnswers P d g).eraseDups)

theorem Oracle.ExactModRepeats.skips {U V : Oracle} (hU : U.ExactModRepeats) (hV : V.Exact) :
    U.SkipsRepeats V := by
  intro P d g
  rw [hV P d g]
  refine ⟨(hU P d g).1, ?_⟩
  rcases (hU P d g).2 with h | h <;> rw [h]
  · exact Thins.refl _ _
  · exact Thins.eraseDups _

namespace Tabled

/-! ## What a table gains from thinner candidates -/

/-- Is `x` not strictly covered by a member of `xs`? -/
def undominated (xs : List Span) (x : Span) : Cost Bool := do
  let b ← anyL (fun y => do
    let c ← Charged.covers y x
    if c then do
      let c' ← Charged.covers x y
      pure !c'
    else pure false) xs
  pure !b

/-- Add `x` to the spans kept so far unless one of them covers it. -/
def keepStep (acc : List Span) (x : Span) : Cost (List Span) := do
  let b ← anyL (fun y => Charged.covers y x) acc
  pure (if b then acc else acc ++ [x])

theorem maxima_eq (xs : List Span) :
    maxima xs = (filterL (undominated xs) xs >>= foldL keepStep []) := rfl

/-- Is `c` not covered by an old answer? -/
def notOld (old : List Span) (c : Span) : Cost Bool := do
  let b ← anyL (fun t => Charged.covers t c) old
  pure !b

theorem fresh_eq (old cands : List Span) :
    fresh old cands = (filterL (notOld old) cands >>= maxima) := rfl

theorem keepStep_val (acc : List Span) (x : Span) :
    (keepStep acc x).val = if acc.any (fun y => y.covers? x) then acc else acc ++ [x] := by
  simp only [keepStep, bind_val, pure_val, anyL_val, Charged.covers]

/-- A span that is covered by one already kept changes nothing, so the thinner
list keeps the same spans. -/
theorem foldL_keepStep {seen l' l : List Span} (h : Thins seen l' l) :
    ∀ acc : List Span, (∀ z ∈ seen, acc.any (fun y => y.covers? z) = true) →
      (foldL keepStep acc l').val = (foldL keepStep acc l).val ∧
        (foldL keepStep acc l').ticks ≤ (foldL keepStep acc l).ticks := by
  induction h with
  | nil seen => exact fun _ _ => ⟨rfl, Nat.le_refl _⟩
  | keep x _ ih =>
    intro acc hacc
    simp only [foldL, bind_val, bind_ticks]
    have := ih (keepStep acc x).val fun z hz => by
      rw [keepStep_val]
      rcases List.mem_cons.1 hz with rfl | hz
      · split
        · assumption
        · simp [covers?_refl]
      · split
        · exact hacc z hz
        · simp [hacc z hz]
    exact ⟨this.1, Nat.add_le_add_left this.2 _⟩
  | drop x hx _ ih =>
    intro acc hacc
    have hv : (keepStep acc x).val = acc := by rw [keepStep_val, hacc x hx]; rfl
    have := ih acc hacc
    simp only [foldL, bind_val, bind_ticks, hv]
    exact ⟨this.1, by omega⟩

theorem maxima_thins {xs' xs : List Span} (h : Thins [] xs' xs) :
    (maxima xs').val = (maxima xs).val ∧ (maxima xs').ticks ≤ (maxima xs).ticks := by
  have hq : (fun x => (undominated xs' x).val) = fun x => (undominated xs x).val := by
    funext x
    simp only [undominated, bind_val, pure_val, anyL_val]
    rw [h.any_eq]
  have htop : Thins [] (xs'.filter fun x => (undominated xs' x).val)
      (xs.filter fun x => (undominated xs x).val) := by
    rw [hq]
    exact h.filter _
  have hf := foldL_keepStep htop [] (fun _ hz => by cases hz)
  have ht : (xs'.map fun x => (undominated xs' x).ticks).sum ≤
      (xs.map fun x => (undominated xs x).ticks).sum := by
    refine Nat.le_trans (sum_map_le fun x _ => ?_) (h.sum_le _)
    simp only [undominated, bind_ticks, pure_ticks, Nat.add_zero]
    exact h.anyL_ticks (fun _ hz => by cases hz)
  simp only [maxima_eq, bind_val, bind_ticks, filterL_val, filterL_ticks]
  exact ⟨hf.1, Nat.add_le_add ht hf.2⟩

/-- A table gains the same answers from the thinner candidates, and pays no
more. -/
theorem fresh_thins (old : List Span) {cs' cs : List Span} (h : Thins [] cs' cs) :
    (fresh old cs').val = (fresh old cs).val ∧ (fresh old cs').ticks ≤ (fresh old cs).ticks := by
  have hm := maxima_thins (h.filter fun c => (notOld old c).val)
  simp only [fresh_eq, bind_val, bind_ticks, filterL_val, filterL_ticks]
  exact ⟨hm.1, Nat.add_le_add (h.sum_le _) hm.2⟩

/-! ## A round, after the oracle -/

/-- The candidates of each table, given what the oracle said. -/
def candidates (st : State) (us : List (Bool × List Span)) : Cost (List (List Span × List Goal)) :=
  mapL (fun p => if p.1.done then pure ([], []) else produce st.P st.tables p.1.goal p.2)
    (st.tables.zip us)

/-- Each table takes its fresh candidates. -/
def grow (st : State) (outs : List (List Span × List Goal)) : Cost Tables :=
  mapL (fun p => do
    let f ← fresh p.1.answers p.2.1
    pure { p.1 with answers := p.1.answers ++ f }) (st.tables.zip outs)

/-- The end of a round: tables for the goals that were asked for, and
completion. -/
def close (st : State) (finals : List Bool) (needed : List Goal) (ts1 : Tables) :
    Cost (State × List Span) := do
  let ts := st.tables
  let reqs ← mapL (fun g => do
    let k ← norm g
    pure k.2) needed
  let newGoals ← foldL (fun acc g => do
    let b ← anyL (fun t => same t.goal g) ts
    if b then pure acc else do
      let b' ← anyL (fun h => same h g) acc
      pure (if b' then acc else acc ++ [g])) [] reqs
  let S ← completing st.P finals ts ts1
  let ts2 : Tables := ts1.mapIdx fun i t => if S.contains i then { t with done := true } else t
  let ts3 : Tables := ts2 ++ newGoals.map fun g => ⟨g, [], false⟩
  let rootNew := match ts.head?, ts1.head? with
    | some t, some t' => t'.answers.drop t.answers.length
    | _, _ => []
  pure (⟨st.P, ts3, st.rootFlip, st.depth + 1⟩, orient st.rootFlip rootNew)

/-- What a round does with the oracle's answers. -/
def rest (st : State) (us : List (Bool × List Span)) : Cost (State × List Span) := do
  let outs ← candidates st us
  let ts1 ← grow st outs
  close st (us.map Prod.fst) (outs.flatMap Prod.snd) ts1

/-- `round_split`, with the remainder named. -/
theorem round_eq (U : Oracle) (st : State) :
    round U st = (do
      tick 1
      let us ← mapL (ask U st) st.tables
      rest st us) := rfl

/-- The candidates of one table. -/
def cand (st : State) (u : Table → Bool × List Span) (t : Table) : Cost (List Span × List Goal) :=
  if t.done then pure ([], []) else produce st.P st.tables t.goal (u t)

theorem candidates_val (st : State) (u : Table → Bool × List Span) :
    (candidates st (st.tables.map u)).val = st.tables.map fun t => (cand st u t).val := by
  simp only [candidates, mapL_val, map_zip_map_self, cand]

theorem candidates_ticks (st : State) (u : Table → Bool × List Span) :
    (candidates st (st.tables.map u)).ticks = (st.tables.map fun t => (cand st u t).ticks).sum := by
  simp only [candidates, mapL_ticks, map_zip_map_self, cand]

theorem grow_val (st : State) (o : Table → List Span × List Goal) :
    (grow st (st.tables.map o)).val =
      st.tables.map fun t => { t with answers := t.answers ++ (fresh t.answers (o t).1).val } := by
  simp only [grow, mapL_val, map_zip_map_self, bind_val, pure_val]

theorem grow_ticks (st : State) (o : Table → List Span × List Goal) :
    (grow st (st.tables.map o)).ticks =
      (st.tables.map fun t => (fresh t.answers (o t).1).ticks).sum := by
  simp only [grow, mapL_ticks, map_zip_map_self, bind_ticks, pure_ticks, Nat.add_zero]

/-- What the oracle said goes in front of a table's candidates and nowhere
else, and reading it costs nothing. -/
theorem cand_skips (st : State) {u' u : Table → Bool × List Span} (t : Table)
    (h : Thins [] (u' t).2 (u t).2) :
    (cand st u' t).val.2 = (cand st u t).val.2 ∧
      Thins [] (cand st u' t).val.1 (cand st u t).val.1 ∧
      (cand st u' t).ticks = (cand st u t).ticks := by
  unfold cand
  cases t.done
  · simp only [Bool.false_eq_true, ite_false, produce, bind_val, bind_ticks, pure_val, pure_ticks]
    exact ⟨trivial, h.append _, trivial⟩
  · exact ⟨rfl, Thins.refl _ _, rfl⟩

/-- With thinner answers from the oracle, the rest of the round ends in the
same state with the same emissions, and costs no more. -/
theorem rest_skips (st : State) {u' u : Table → Bool × List Span}
    (h : ∀ t, (u' t).1 = (u t).1 ∧ Thins [] (u' t).2 (u t).2) :
    (rest st (st.tables.map u')).val = (rest st (st.tables.map u)).val ∧
      (rest st (st.tables.map u')).ticks ≤ (rest st (st.tables.map u)).ticks := by
  have hc := fun t => cand_skips st t (h t).2
  have e1 : (st.tables.map u').map Prod.fst = (st.tables.map u).map Prod.fst := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun t _ => (h t).1
  have e2 : (candidates st (st.tables.map u')).val.flatMap Prod.snd =
      (candidates st (st.tables.map u)).val.flatMap Prod.snd := by
    rw [candidates_val, candidates_val, List.flatMap_map, List.flatMap_map]
    exact List.flatMap_congr fun t _ => (hc t).1
  have e3 : (grow st (candidates st (st.tables.map u')).val).val =
      (grow st (candidates st (st.tables.map u)).val).val := by
    rw [candidates_val, candidates_val, grow_val, grow_val]
    exact List.map_congr_left fun t _ => by rw [(fresh_thins t.answers (hc t).2.1).1]
  have t1 : (candidates st (st.tables.map u')).ticks = (candidates st (st.tables.map u)).ticks := by
    rw [candidates_ticks, candidates_ticks]
    exact congrArg List.sum (List.map_congr_left fun t _ => (hc t).2.2)
  have t2 : (grow st (candidates st (st.tables.map u')).val).ticks ≤
      (grow st (candidates st (st.tables.map u)).val).ticks := by
    rw [candidates_val, candidates_val, grow_ticks, grow_ticks]
    exact sum_map_le fun t _ => (fresh_thins t.answers (hc t).2.1).2
  simp only [rest, bind_val, bind_ticks, e1, e2, e3, t1]
  exact ⟨trivial, by omega⟩

/-! ## Two oracles that agree up to repeats -/

theorem ask_skips {U V : Oracle} (h : U.SkipsRepeats V) (st : State) (t : Table) :
    (ask U st t).val.1 = (ask V st t).val.1 ∧ Thins [] (ask U st t).val.2 (ask V st t).val.2 := by
  unfold ask
  cases t.done
  · exact h st.P st.depth t.goal
  · exact ⟨rfl, Thins.refl _ _⟩

theorem round_val_of_skips {U V : Oracle} (h : U.SkipsRepeats V) (st : State) :
    (round U st).val = (round V st).val := by
  simp only [round_eq, bind_val, mapL_val]
  exact (rest_skips st (ask_skips h st)).1

theorem step_val_of_skips {U V : Oracle} (h : U.SkipsRepeats V) (st : State) :
    (step U st).val = (step V st).val := by
  simp only [step, ite_val, pure_val, bind_val, round_val_of_skips h]

theorem sum_map_le_mul {α : Type} {f g : α → Nat} (c : Nat) {xs : List α}
    (h : ∀ x ∈ xs, f x ≤ c * g x) : (xs.map f).sum ≤ c * (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons y xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A round with the oracle that skips repeats costs at most `c` times the
round with the other, when each of its calls does. -/
theorem round_ticks_of_skips {U V : Oracle} (h : U.SkipsRepeats V) {c : Nat} (hc : 1 ≤ c)
    (ht : ∀ P d g, (U P d g).ticks ≤ c * (V P d g).ticks) (st : State) :
    (round U st).ticks ≤ c * (round V st).ticks := by
  have ha : (mapL (ask U st) st.tables).ticks ≤ c * (mapL (ask V st) st.tables).ticks := by
    rw [mapL_ticks, mapL_ticks]
    refine sum_map_le_mul c fun t _ => ?_
    unfold ask
    cases t.done
    · simp only [Bool.false_eq_true, ite_false, bind_ticks, tick_ticks, Nat.mul_add]
      exact Nat.add_le_add (Nat.le_mul_of_pos_left _ hc) (ht _ _ _)
    · exact Nat.zero_le _
  have hr := (rest_skips st (ask_skips h st)).2
  have hr' := Nat.le_mul_of_pos_left
    (rest st (st.tables.map fun t => (ask V st t).val)).ticks hc
  simp only [round_eq, bind_ticks, tick_ticks, mapL_val, Nat.mul_add]
  omega

theorem step_ticks_of_skips {U V : Oracle} (h : U.SkipsRepeats V) {c : Nat} (hc : 1 ≤ c)
    (ht : ∀ P d g, (U P d g).ticks ≤ c * (V P d g).ticks) (st : State) :
    (step U st).ticks ≤ c * (step V st).ticks := by
  unfold step
  simp only [ite_ticks, pure_ticks, bind_ticks, Nat.add_zero]
  split
  · exact Nat.zero_le _
  · exact round_ticks_of_skips h hc ht st

/-- The machines of two oracles that agree up to repeats are the same
runtime. -/
theorem machine_runtime_of_skips {U V : Oracle} (h : U.SkipsRepeats V) :
    (machine U).runtime = (machine V).runtime := by
  simp only [CostedRuntime.runtime, machine, step_val_of_skips h]

/-- With an oracle that computes R001's unfolding race up to repeated
answers, the charged tabled machine is R001. -/
theorem machine_runtime_modRepeats (U : Oracle) (hU : U.ExactModRepeats) :
    (machine U).runtime = R001.runtime := by
  have hV : Oracle.Exact fun P d g => pure (unfoldFinal P d g, unfoldAnswers P d g) :=
    fun _ _ _ => rfl
  rw [machine_runtime_of_skips (hU.skips hV)]
  exact machine_runtime _ hV

/-- After any number of steps, the machine whose oracle skips repeats has
spent at most `c` times what the other has, when each call of its oracle costs
at most `c` times the same call of the other. -/
theorem spent_le_of_skips {U V : Oracle} (h : U.SkipsRepeats V) {c : Nat} (hc : 1 ≤ c)
    (ht : ∀ P d g, (U P d g).ticks ≤ c * (V P d g).ticks) :
    ∀ (n : Nat) (st : State), (machine U).spent st n ≤ c * (machine V).spent st n
  | 0, _ => Nat.zero_le _
  | n + 1, st => by
    have hs : ((machine U).step st).ticks ≤ c * ((machine V).step st).ticks :=
      step_ticks_of_skips h hc ht st
    have hv : ((machine U).step st).val = ((machine V).step st).val := step_val_of_skips h st
    cases hV : ((machine V).step st).val with
    | done =>
      rw [(machine U).spent_succ_done (hv.trans hV), (machine V).spent_succ_done hV]
      exact hs
    | emit as st' =>
      rw [(machine U).spent_succ_emit (hv.trans hV), (machine V).spent_succ_emit hV, Nat.mul_add]
      exact Nat.add_le_add hs (spent_le_of_skips h hc ht n st')

end Tabled

end RwLog
