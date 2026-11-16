/-
# Reading an edge is right about the program

`readEdge` reads from the program the interfaces the answers of a node can
show at one end. Here: what it returns is right (`readEdge_sound`). Every answer of a
node of the normal form with first-order spans ends (begins) with one of the
runs `runs` returns (`runs_ok`), so inside the interface of one of them.
-/
import RwLog.Rungs.Symmetric.Progress
import RwLog.Rungs.Framework.GoalsVal
import RwLog.SpanLayer.Modulo

namespace RwLog

namespace Symmetric

open Traverse Answer

/-! ## Folds -/

/-- A fold of steps that only add holds what it started with and what each
step adds whatever it is given. -/
theorem foldl_grow {α β : Type} (g : List β → α → List β) (hsub : ∀ acc x, acc ⊆ g acc x) :
    ∀ (xs : List α) (acc : List β), acc ⊆ xs.foldl g acc ∧
      ∀ x ∈ xs, ∀ b, (∀ acc', b ∈ g acc' x) → b ∈ xs.foldl g acc
  | [], acc => ⟨fun _ h => h, fun _ h => by cases h⟩
  | y :: ys, acc => by
    obtain ⟨h1, h2⟩ := foldl_grow g hsub ys (g acc y)
    refine ⟨fun b hb => h1 (hsub acc y hb), fun x hx b hb => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1 (hb acc)
    · exact h2 x hx b hb

/-- A fold that stops at nothing: if it returns something it started with
something, and what holds of the start and the members passed, and is kept
by each step, holds of what it returns. -/
theorem foldl_option_inv {α β : Type} (g : Option β → α → Option β) (I : List α → β → Prop)
    (xs : List α) (hnone : ∀ x, g none x = none)
    (hstep : ∀ done b x b', x ∈ xs → g (some b) x = some b' → I done b → I (done ++ [x]) b') :
    ∀ (ys : List α), (∀ y ∈ ys, y ∈ xs) → ∀ (done : List α) (acc : Option β) (b' : β),
      ys.foldl g acc = some b' → ∃ b0, acc = some b0 ∧ (I done b0 → I (done ++ ys) b')
  | [], _, done, acc, b', h => ⟨b', h, fun h => by rwa [List.append_nil]⟩
  | y :: ys, hys, done, acc, b', h => by
    obtain ⟨b1, h1, h2⟩ := foldl_option_inv g I xs hnone hstep ys
      (fun z hz => hys z (List.mem_cons_of_mem _ hz)) (done ++ [y]) (g acc y) b' h
    cases acc with
    | none => rw [hnone] at h1; cases h1
    | some b0 =>
      refine ⟨b0, rfl, fun h0 => ?_⟩
      have := h2 (hstep done b0 y b1 (hys y List.mem_cons_self) h1 h0)
      rwa [List.append_assoc] at this

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## What a run says of an answer -/

/-- What a run says of a pair an answer relates: a whole run relates the
pair, and a run that is not whole relates some pair with the same right
(`last`) or left end. A run with no span says nothing, and is not whole. -/
def RunAt (M : Interp) (last : Bool) (r : Run R) (x z : GTerm) : Prop :=
  match r with
  | (none, w) => w = false
  | (some s, true) => (x, z) ∈ den M s
  | (some s, false) => if last then ∃ y, (y, z) ∈ den M s else ∃ y, (x, y) ∈ den M s

/-- Every pair of every relation of the set is what one of the runs says. -/
def RunsOk (M : Interp) (last : Bool) (rs : List (Run R)) (S : Set GRel) : Prop :=
  ∀ G ∈ S, ∀ x z, (x, z) ∈ G.at M → ∃ r ∈ rs, RunAt M last r x z

omit [DecidableEq R] in
theorem RunsOk.mono {M : Interp} {last : Bool} {rs rs' : List (Run R)} {S : Set GRel}
    (h : RunsOk M last rs S) (hs : rs ⊆ rs') : RunsOk M last rs' S := fun G hG x z hx => by
  obtain ⟨r, hr, h'⟩ := h G hG x z hx
  exact ⟨r, hs hr, h'⟩

omit [DecidableEq R] in
/-- What a run that is not whole says depends on one end of the pair
only. -/
theorem RunAt.edge {M : Interp} {last : Bool} {r : Run R} {x z : GTerm} (h : RunAt M last r x z)
    (hr : r.2 = false) (x' z' : GTerm) :
    RunAt M last r (if last then x' else x) (if last then z else z') := by
  obtain ⟨o, w⟩ := r
  simp only at hr
  subst hr
  cases o with
  | none => exact h
  | some s =>
    cases last
    · exact h
    · exact h

/-- The relations of a chain continued by one member inwards: before the
runs read so far (`last`), or after. -/
def stepSet (last : Bool) (S T : Set GRel) : Set GRel :=
  if last then Set.image2 GRel.comp T S else Set.image2 GRel.comp S T

omit [DecidableEq R] in
/-- Runs none of which is whole say of a longer chain what they say of the
edge. -/
theorem RunsOk.edge {M : Interp} {last : Bool} {rs : List (Run R)} {S : Set GRel}
    (h : RunsOk M last rs S) (hr : ∀ r ∈ rs, r.2 = false) (T : Set GRel) :
    RunsOk M last rs (stepSet last S T) := by
  intro G hG x z hx
  cases last
  · obtain ⟨A, hA, B, hB, rfl⟩ := hG
    rw [at_comp] at hx
    obtain ⟨m, h1, h2⟩ := hx
    obtain ⟨r, hr', hrun⟩ := h A hA x m h1
    exact ⟨r, hr', hrun.edge (hr r hr') x z⟩
  · obtain ⟨A, hA, B, hB, rfl⟩ := hG
    rw [at_comp] at hx
    obtain ⟨m, h1, h2⟩ := hx
    obtain ⟨r, hr', hrun⟩ := h B hB m z h2
    exact ⟨r, hr', hrun.edge (hr r hr') x z⟩

omit [DecidableEq R] in
/-- **The runs of a chain continued by one member**: a run that is not whole
stays, and a whole one composed with each run of the member is a run of the
longer chain. -/
theorem RunsOk.step {M : Interp} (hL : D.Lawful M) {last : Bool} {rs ys rs' : List (Run R)}
    {S T : Set GRel} (h : RunsOk M last rs S) (hy : RunsOk M last ys T)
    (ha : ∀ r ∈ rs, r.2 = false → r ∈ rs')
    (hb : ∀ s, (some s, true) ∈ rs → ∀ q ∈ ys,
      match q.1 with
      | none => (some s, false) ∈ rs'
      | some t => ∀ c, (if last then D.compose t s else D.compose s t) = some c →
          (some c, q.2) ∈ rs') :
    RunsOk M last rs' (stepSet last S T) := by
  intro G hG x z hx
  cases last
  · obtain ⟨A, hA, B, hB, rfl⟩ := hG
    rw [at_comp] at hx
    obtain ⟨m, h1, h2⟩ := hx
    obtain ⟨r, hr, hrun⟩ := h A hA x m h1
    obtain ⟨q, hq, hqrun⟩ := hy B hB m z h2
    obtain ⟨o, w⟩ := r
    cases w with
    | false => exact ⟨_, ha _ hr rfl, hrun.edge rfl x z⟩
    | true =>
      cases o with
      | none => cases hrun
      | some s =>
        have hxs : (x, m) ∈ den M s := hrun
        have hq' := hb s hr q hq
        obtain ⟨qo, qw⟩ := q
        cases qo with
        | none => exact ⟨_, hq', ⟨m, hxs⟩⟩
        | some t =>
          simp only [Bool.false_eq_true, ite_false] at hq'
          have ht : ∃ z', (m, z') ∈ den M t := by
            cases qw
            · exact hqrun
            · exact ⟨z, hqrun⟩
          obtain ⟨z', hz'⟩ := ht
          cases hc : D.compose s t with
          | none =>
            have := hL.compose_none s t hc
            exact absurd (show (x, z') ∈ (den M s).comp (den M t) from ⟨m, hxs, hz'⟩)
              (by rw [this]; exact fun h => h)
          | some c =>
            refine ⟨_, hq' c hc, ?_⟩
            have hden := hL.compose_some s t c hc
            cases qw
            · exact ⟨z', by rw [hden]; exact ⟨m, hxs, hz'⟩⟩
            · show (x, z) ∈ den M c
              rw [hden]
              exact ⟨m, hxs, hqrun⟩
  · obtain ⟨B, hB, A, hA, rfl⟩ := hG
    rw [at_comp] at hx
    obtain ⟨m, h1, h2⟩ := hx
    obtain ⟨r, hr, hrun⟩ := h A hA m z h2
    obtain ⟨q, hq, hqrun⟩ := hy B hB x m h1
    obtain ⟨o, w⟩ := r
    cases w with
    | false => exact ⟨_, ha _ hr rfl, hrun.edge rfl x z⟩
    | true =>
      cases o with
      | none => cases hrun
      | some s =>
        have hxs : (m, z) ∈ den M s := hrun
        have hq' := hb s hr q hq
        obtain ⟨qo, qw⟩ := q
        cases qo with
        | none => exact ⟨_, hq', ⟨m, hxs⟩⟩
        | some t =>
          simp only [ite_true] at hq'
          have ht : ∃ x', (x', m) ∈ den M t := by
            cases qw
            · exact hqrun
            · exact ⟨x, hqrun⟩
          obtain ⟨x', hx'⟩ := ht
          cases hc : D.compose t s with
          | none =>
            have := hL.compose_none t s hc
            exact absurd (show (x', z) ∈ (den M t).comp (den M s) from ⟨m, hx', hxs⟩)
              (by rw [this]; exact fun h => h)
          | some c =>
            refine ⟨_, hq' c hc, ?_⟩
            have hden := hL.compose_some t s c hc
            cases qw
            · exact ⟨x', by rw [hden]; exact ⟨m, hx', hxs⟩⟩
            · show (x, z) ∈ den M c
              rw [hden]
              exact ⟨m, hqrun, hxs⟩

omit [Answer R] [DecidableEq R] in
/-- What the runs of a chain continued by one member hold, from what each
step of the fold adds. -/
theorem extend_key (D : Domain R) (last : Bool) (rs ys : List (Run R))
    (g : List (Run R) → Run R → List (Run R)) (hsub : ∀ acc r, acc ⊆ g acc r)
    (hmem : ∀ s q, q ∈ ys → ∀ acc,
      match q.1 with
      | none => (some s, false) ∈ g acc (some s, true)
      | some t => ∀ c, (if last then D.compose t s else D.compose s t) = some c →
          (some c, q.2) ∈ g acc (some s, true)) :
    (∀ r ∈ rs, r.2 = false → r ∈ rs.foldl g (rs.filter fun r => !r.2)) ∧
      ∀ s, (some s, true) ∈ rs → ∀ q ∈ ys,
        match q.1 with
        | none => (some s, false) ∈ rs.foldl g (rs.filter fun r => !r.2)
        | some t => ∀ c, (if last then D.compose t s else D.compose s t) = some c →
            (some c, q.2) ∈ rs.foldl g (rs.filter fun r => !r.2) := by
  obtain ⟨h1, h2⟩ := foldl_grow g hsub rs (rs.filter fun r => !r.2)
  refine ⟨fun r hr hw => h1 (List.mem_filter.2 ⟨hr, by simp [hw]⟩), fun s hs q hq => ?_⟩
  obtain ⟨qo, qw⟩ := q
  cases qo with
  | none => exact h2 _ hs _ fun acc => hmem s _ hq acc
  | some t => exact fun c hc => h2 _ hs _ fun acc => hmem s _ hq acc c hc

omit [DecidableEq R] in
/-- One more interface, unless it is there. -/
theorem bounds_add (D : Domain R) (last : Bool) {done : List (Run R)} {b : List R} {x p : R}
    {w : Bool} (flag : Bool) (hflag : flag = true → p ∈ b)
    (hb : (if last then D.rightBound x else D.leftBound x) = some p)
    (hI : (∀ r ∈ done, ∃ x p, r.1 = some x ∧
        (if last then D.rightBound x else D.leftBound x) = some p ∧ p ∈ b) ∧
      ∀ q ∈ b, ∃ x, (if last then D.rightBound x else D.leftBound x) = some q) :
    (∀ r ∈ done ++ [(some x, w)], ∃ y q, r.1 = some y ∧
        (if last then D.rightBound y else D.leftBound y) = some q ∧
        q ∈ (if flag then b else b ++ [p])) ∧
      ∀ q ∈ (if flag then b else b ++ [p]), ∃ x,
        (if last then D.rightBound x else D.leftBound x) = some q := by
  cases flag with
  | true =>
    have hp := hflag rfl
    refine ⟨fun r hr => ?_, hI.2⟩
    rcases List.mem_append.1 hr with hr | hr
    · exact hI.1 r hr
    · obtain rfl := List.mem_singleton.1 hr
      exact ⟨x, p, rfl, hb, hp⟩
  | false =>
    refine ⟨fun r hr => ?_, fun q hq => ?_⟩
    · rcases List.mem_append.1 hr with hr | hr
      · obtain ⟨y, q, h1, h2, h3⟩ := hI.1 r hr
        exact ⟨y, q, h1, h2, List.mem_append_left _ h3⟩
      · obtain rfl := List.mem_singleton.1 hr
        exact ⟨x, p, rfl, hb, by simp⟩
    · rcases List.mem_append.1 hq with hq | hq
      · exact hI.2 q hq
      · obtain rfl := List.mem_singleton.1 hq
        exact ⟨x, hb⟩

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

theorem addRun_spec (acc : List (Run R)) (r : Run R) :
    acc ⊆ (addRun (K := DerivationKernel.over D K hK P) acc r).val ∧
      r ∈ (addRun (K := DerivationKernel.over D K hK P) acc r).val := by
  have hsb := fun a b => Goals.sameBound_val (P := P) K hK a b
  at_cost K hK
  simp only [addRun, Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val]
  split
  · next hb =>
    refine ⟨fun _ h => h, ?_⟩
    obtain ⟨q, hq, hqr⟩ := List.any_eq_true.1 hb
    split at hqr
    · next e =>
      rw [hsb] at hqr
      have e1 : q.1 = r.1 := by simpa using hqr
      have : q = r := Prod.ext e1 e
      exact this ▸ hq
    · cases hqr
  · exact ⟨List.subset_append_left _ _, by simp⟩

theorem extendRuns_spec (last : Bool) (rs ys : List (Run R)) :
    (∀ r ∈ rs, r.2 = false →
        r ∈ (extendRuns (K := DerivationKernel.over D K hK P) last rs ys).val) ∧
      ∀ s, (some s, true) ∈ rs → ∀ q ∈ ys,
        match q.1 with
        | none => (some s, false) ∈
            (extendRuns (K := DerivationKernel.over D K hK P) last rs ys).val
        | some t => ∀ c, (if last then D.compose t s else D.compose s t) = some c →
            (some c, q.2) ∈ (extendRuns (K := DerivationKernel.over D K hK P) last rs ys).val := by
  have hadd := fun acc r => addRun_spec (K := K) (hK := hK) (P := P) acc r
  at_cost K hK
  simp only [extendRuns, foldL_std, Cost.foldL_val]
  refine extend_key D last rs ys _ (fun acc r => ?_) (fun s q hq acc => ?_)
  · split
    · rw [Cost.foldL_val]
      refine (foldl_grow _ (fun acc q => ?_) ys acc).1
      split
      · exact (hadd _ _).1
      · split <;>
        · simp only [Cost.bind_val]
          split
          · exact fun _ h => h
          · exact (hadd _ _).1
    · exact fun _ h => h
  · simp only [Cost.foldL_val]
    obtain ⟨qo, qw⟩ := q
    cases qo with
    | none =>
      refine (foldl_grow _ (fun acc q => ?_) ys acc).2 _ hq _ (fun acc' => (hadd _ _).2)
      split
      · exact (hadd _ _).1
      · split <;>
        · simp only [Cost.bind_val]
          split
          · exact fun _ h => h
          · exact (hadd _ _).1
    | some t =>
      intro c hc
      refine (foldl_grow _ (fun acc q => ?_) ys acc).2 _ hq _ (fun acc' => ?_)
      · split
        · exact (hadd _ _).1
        · split <;>
          · simp only [Cost.bind_val]
            split
            · exact fun _ h => h
            · exact (hadd _ _).1
      · cases last
        · simp only [Bool.false_eq_true, ite_false, Cost.bind_val] at hc ⊢
          rw [hK.compose, hc]
          exact (hadd _ _).2
        · simp only [ite_true, Cost.bind_val] at hc ⊢
          rw [hK.compose, hc]
          exact (hadd _ _).2

/-- The relations of the members of a chain read so far, given in the order
read. -/
def chainSet (P : Program) (last : Bool) (k : Nat) (done : List Rel) : Set GRel :=
  seqAll ((if last then done.reverse else done).map (GDn P k))

theorem chainSet_single (last : Bool) (k : Nat) (e : Rel) :
    chainSet P last k [e] = GDn P k e := by
  cases last <;> exact image2_comp_id _

theorem chainSet_snoc (last : Bool) (k : Nat) (done : List Rel) (x : Rel) :
    chainSet P last k (done ++ [x]) = stepSet last (chainSet P last k done) (GDn P k x) := by
  cases last
  · show seqAll (List.map (GDn P k) (done ++ [x])) =
      Set.image2 GRel.comp (seqAll (done.map (GDn P k))) (GDn P k x)
    rw [List.map_append, seqAll_append]
    congr 1
    exact image2_comp_id _
  · show seqAll (List.map (GDn P k) (done ++ [x]).reverse) =
      Set.image2 GRel.comp (GDn P k x) (seqAll (done.reverse.map (GDn P k)))
    rw [List.reverse_append]
    rfl

theorem runs_ok (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) (last : Bool) :
    ∀ (d : Nat) (seen : List Rel) (n : Rel) (rs : List (Run R)), Normal n → n.FO →
      (runs (K := DerivationKernel.over D K hK P) last d seen n).val = some rs →
      ∀ k, RunsOk P.sorts.interp last rs (GDn P k n) := by
  have hadd := fun acc r => addRun_spec (K := K) (hK := hK) (P := P) acc r
  have hext := fun rs ys => extendRuns_spec (K := K) (hK := hK) (P := P) last rs ys
  have hleaf := fun (s : Span) (c : Ans D P) =>
    Ans.leaf_val (P := P) K hK (lb := none) (rb := none) (n := .span s) (c := c)
  have hleafok := fun (s : Span) (z : R) hz =>
    Ans.leaf_ok (P := P) K hK (s := s) (z := z) (isBound_none D) (isBound_none D) hz
  at_cost K hK
  intro d
  induction d with
  | zero =>
    intro seen n rs _ _ h
    simp only [runs, Cost.pure_val] at h
    cases h
  | succ d ih =>
    intro seen n rs hn hfo h k
    simp only [runs, Cost.bind_val] at h
    split at h
    · next hv =>
      obtain ⟨s, rfl⟩ := forget_span hv
      simp only [Cost.bind_val, Cost.pure_val, over_leaf, over_span] at h
      rw [← Option.some.inj h]
      intro G hG x z hx
      rw [(gdn_laws P k).span] at hG
      obtain rfl := Set.mem_singleton_iff.1 hG
      split
      · next a ha =>
        obtain ⟨s1, e, -, -, hsb, -⟩ := (hleaf s a).1 ha
        cases e
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        show (x, z) ∈ den P.sorts.interp a.span
        rw [spanBoth_den hL hsb, wrapAt_none]
        exact hx
      · next ha =>
        cases hr : D.rep s with
        | some r =>
          obtain ⟨c, hc, -⟩ := hleafok s r (by simp [spanBoth, hr])
          rw [ha] at hc
          cases hc
        | none =>
          have := hL.rep_none s (hfo s (by simp [RelOf.spans])) hr
          rw [← Span.denAt_eq, this] at hx
          exact absurd hx (Set.notMem_empty _)
    · simp only [Cost.pure_val] at h
      cases h
      exact fun G hG x z hx => ⟨(none, false), List.mem_singleton_self _, rfl⟩
    · next xs hv =>
      have hvu := forget_union hv
      have hxs := hn.view_union_eq hvu
      simp only [foldL_std, Cost.foldL_val] at h
      have key := foldl_option_inv _ (fun (done : List Rel) (b : List (Run R)) =>
        ∀ x ∈ done, ∀ k, RunsOk P.sorts.interp last b (GDn P k x)) xs ?_ ?_ xs (fun _ h => h)
        [] _ rs h
      · obtain ⟨b0, hb0, hI⟩ := key
        have hall := hI (fun x hx => by cases hx)
        intro G hG x z hxz
        rw [← (gdn_laws P k).gd_unionParts n, ← hxs] at hG
        simp only [Set.mem_iUnion, exists_prop] at hG
        obtain ⟨m, hm, hG⟩ := hG
        exact hall m (by simpa using hm) k G hG x z hxz
      · exact fun x => rfl
      · intro done b x b' hx hg hI
        simp only [Cost.bind_val] at hg
        split at hg
        · cases hg
        · next r hr =>
          simp only [Cost.bind_val, Cost.pure_val, Cost.foldL_val, Option.some.injEq] at hg
          subst hg
          obtain ⟨h1, h2⟩ := foldl_grow
            (fun acc r => (addRun (K := DerivationKernel.over D _ hK P) acc r).val)
            (fun acc r => (hadd acc r).1) r b
          intro y hy k'
          rcases List.mem_append.1 hy with hy | hy
          · exact (hI y hy k').mono h1
          · obtain rfl := List.mem_singleton.1 hy
            have hmem : y ∈ n.view.members := by rw [hvu]; exact hx
            exact (ih seen y r (hn.view_members hmem) (hfo.view_members hmem) hr k').mono
              fun q hq => h2 q hq q fun acc' => (hadd acc' q).2
    · next f fl hv =>
      simp only [Cost.bind_val, anyL_std] at h
      split at h
      · simp only [Cost.pure_val] at h
        cases h
        exact fun G hG x z hx => ⟨(none, false), List.mem_singleton_self _, rfl⟩
      · simp only [Cost.bind_val, over_body] at h
        split at h
        · next hb =>
          obtain ⟨b, hb'⟩ := forget_call (P := P) hv
          rw [show Charged.bodyOf P n = none from hb] at hb'
          cases hb'
        · next bd hb =>
          have hb' : Charged.bodyOf P n = some bd := hb
          have hbd := ih _ bd rs (normal_bodyOf hb') (bodyOf_fo hP hb') h
          cases k with
          | zero =>
            intro G hG
            rw [(gdn_bodyOf hb' 0).2] at hG
            cases hG
          | succ k =>
            rw [(gdn_bodyOf hb' k).1]
            exact hbd k
    · next xs hv =>
      have hvc := forget_chain hv
      obtain ⟨h2, hmem, hmk⟩ := hn.view_chain hvc
      have hne : xs ≠ [] := by intro e; rw [e] at h2; simp at h2
      have hparts : seqParts n = xs := by
        rw [← hmk]; exact seqParts_mkSeq hne fun x hx => (hmem x hx).2
      split at h
      · simp only [Cost.pure_val] at h
        cases h
        exact fun G hG x z hx => ⟨(none, false), List.mem_singleton_self _, rfl⟩
      · next e rest heq =>
        simp only [Cost.bind_val, foldL_std, Cost.foldL_val] at h
        have hsub : ∀ y ∈ e :: rest, y ∈ xs := by
          intro y hy
          rw [← heq] at hy
          cases last <;> simpa using hy
        have key := foldl_option_inv _ (fun (done : List Rel) (b : List (Run R)) =>
          ∀ k, RunsOk P.sorts.interp last b (chainSet P last k done)) rest ?_ ?_ rest
          (fun _ h => h) [e] _ rs h
        · obtain ⟨b0, hb0, hI⟩ := key
          have he : e ∈ n.view.members := by rw [hvc]; exact hsub e (by simp)
          have h0 := ih seen e b0 (hn.view_members he) (hfo.view_members he) hb0
          have hfin := hI (fun k => by rw [chainSet_single]; exact h0 k) k
          have hc : chainSet P last k ([e] ++ rest) = GDn P k n := by
            rw [← (gdn_laws P k).gd_seqParts n, hparts]
            show seqAll ((if last then (e :: rest).reverse else e :: rest).map _) = _
            rw [← heq]
            cases last <;> simp
          rwa [hc] at hfin
        · exact fun x => rfl
        · intro done b x b' hx hg hI k'
          rw [chainSet_snoc]
          simp only at hg
          split at hg
          · simp only [Cost.bind_val] at hg
            split at hg
            · cases hg
            · next ys hys =>
              simp only [Cost.pure_val, Cost.bind_val, Option.some.injEq] at hg
              subst hg
              have hxm : x ∈ n.view.members := by
                rw [hvc]; exact hsub x (List.mem_cons_of_mem _ hx)
              exact (hI k').step hL
                (ih seen x ys (hn.view_members hxm) (hfo.view_members hxm) hys k')
                (hext b ys).1 (hext b ys).2
          · next hany =>
            simp only [Cost.pure_val, Option.some.injEq] at hg
            subst hg
            refine (hI k').edge (fun r hr => ?_) _
            cases hr2 : r.2 with
            | false => rfl
            | true => exact absurd (List.any_eq_true.2 ⟨r, hr, hr2⟩) hany

/-- A reading made a reading of every node is right about the program if
the reading is. -/
theorem offered_sound {rd : Bool → Nat → Rel → Cost (Option (Option (List R)))}
    (h : ∀ (last : Bool) (d : Nat) (n : Rel) (ps : List R),
      (rd last d n).val = some (some ps) → EdgeOk D P n last ps) :
    ∀ (last : Bool) (d : Nat) (n : Rel) (ps : List R),
      (offered (K := DerivationKernel.over D K hK P) rd last d n).val = some (some ps) →
        EdgeOk D P n last ps := by
  intro last d n ps
  at_cost K hK
  intro h'
  simp only [offered, Cost.bind_val] at h'
  split at h'
  · cases h'
  · cases h'
  · exact h last d n ps h'

/-- **The interfaces of the runs are right about the program**: they are
boundaries, and every answer of a node of the normal form with first-order
spans ends (begins) inside one of them. -/
theorem readRuns_sound (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) :
    ∀ (last : Bool) (d : Nat) (n : Rel) (ps : List R),
      (readRuns (K := DerivationKernel.over D K hK P) last d n).val = some (some ps) →
        EdgeOk D P n last ps := by
  intro last d n ps h
  have hruns := fun rs => runs_ok (K := K) (hK := hK) hL hP last d [] n rs
  at_cost K hK
  simp only [readRuns, Cost.bind_val] at h
  · split at h
    · cases h
    · next rs hrs =>
      simp only [Cost.bind_val, Cost.pure_val, foldL_std, Cost.foldL_val, Option.some.injEq] at h
      have key := foldl_option_inv _ (fun (done : List (Run R)) (ps : List R) =>
        (∀ r ∈ done, ∃ x p, r.1 = some x ∧
          (if last then D.rightBound x else D.leftBound x) = some p ∧ p ∈ ps) ∧
        ∀ q ∈ ps, ∃ x, (if last then D.rightBound x else D.leftBound x) = some q) rs ?_ ?_ rs
        (fun _ h => h) [] _ ps h
      · obtain ⟨b0, hb0, hI⟩ := key
        cases hb0
        obtain ⟨h1, h2⟩ := hI ⟨(fun r hr => by cases hr), fun q hq => by cases hq⟩
        refine ⟨fun p hp => ?_, fun hn hfo k G hG x z hx => ?_⟩
        · obtain ⟨y, hy⟩ := h2 p hp
          cases last
          · exact hL.rightBound_isBound _ p hy
          · exact hL.rightBound_isBound _ p hy
        · obtain ⟨r, hr, hrun⟩ := hruns rs hn hfo hrs k G hG x z hx
          obtain ⟨s, p, e, hb, hp⟩ := h1 r (by simpa using hr)
          obtain ⟨o, w⟩ := r
          simp only at e
          subst e
          refine ⟨p, hp, ?_⟩
          cases last
          · simp only [Bool.false_eq_true, ite_false] at hb ⊢
            rw [← hb]
            cases w
            · obtain ⟨y, hy⟩ := hrun
              exact leftBound_at hL hy
            · exact leftBound_at hL hrun
          · simp only [ite_true] at hb ⊢
            rw [← hb]
            cases w
            · obtain ⟨y, hy⟩ := hrun
              exact rightBound_at hL hy
            · exact rightBound_at hL hrun
      · intro x
        cases x.1 <;> rfl
      · intro done b r b' hr hg hI
        obtain ⟨o, w⟩ := r
        cases o with
        | none => cases hg
        | some x =>
          have hflag : ∀ p,
              (b.any fun q => ((DerivationKernel.over D _ hK P).eq q p).val) = true → p ∈ b := by
            intro p hp
            obtain ⟨q, hq, hqp⟩ := List.any_eq_true.1 hp
            rw [show ((DerivationKernel.over D _ hK P).eq q p).val = decide (q = p) from
              hK.eq q p] at hqp
            exact (of_decide_eq_true hqp) ▸ hq
          cases last
          · simp only [Bool.false_eq_true, ite_false, Cost.bind_val] at hg
            cases hp : D.leftBound x with
            | none => rw [show _ = D.leftBound x from hK.leftBound x, hp] at hg; cases hg
            | some p =>
              rw [show _ = D.leftBound x from hK.leftBound x, hp] at hg
              simp only [Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val,
                Option.some.injEq] at hg
              subst hg
              exact bounds_add D false _ (hflag p) hp hI
          · simp only [ite_true, Cost.bind_val] at hg
            cases hp : D.rightBound x with
            | none => rw [show _ = D.rightBound x from hK.rightBound x, hp] at hg; cases hg
            | some p =>
              rw [show _ = D.rightBound x from hK.rightBound x, hp] at hg
              simp only [Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val,
                Option.some.injEq] at hg
              subst hg
              exact bounds_add D true _ (hflag p) hp hI

/-- **Reading an edge is right about the program.** -/
theorem readEdge_sound (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) :
    ∀ (last : Bool) (d : Nat) (n : Rel) (ps : List R),
      (readEdge (K := DerivationKernel.over D K hK P) last d n).val = some (some ps) →
        EdgeOk D P n last ps :=
  offered_sound (readRuns_sound hL hP)

end kernel

end Symmetric

end RwLog
