/-
# The rounds of `sorts::tighten`, without the store

A store as `sorts::tighten` holds it is a pattern, a list of exclusions, a
list of entries (a variable with the conjunction of its sorts) and the next
unused variable (`TSt`). It stands for the `CStore` in which a variable
below the next one has the conjunction of its entry, or none (`TSt.abs`).

A round (`round`) is what the loop of `sorts::tighten` does once. Its runs
(`run`, with the number of rounds allowed) are replacements in the sense of
`Sorts.Tightens`, and among well-formed sorts some number of rounds is
enough (`tightRun_total`).
-/
import RwLogVerified.Tighten

namespace RwLogVerified

open RwLog

/-! ## The conjunction an entry list gives a variable -/

/-- The conjunction of the first entry of the variable, or none. -/
def conjOf (L : List (Nat × Sorts.Conj)) (u : Nat) : Sorts.Conj := (L.lookup u).getD ∅

theorem conjOf_nil (u : Nat) : conjOf [] u = ∅ := rfl

theorem conjOf_cons (e : Nat × Sorts.Conj) (L : List (Nat × Sorts.Conj)) (u : Nat) :
    conjOf (e :: L) u = if u = e.1 then e.2 else conjOf L u := by
  obtain ⟨k, b⟩ := e
  unfold conjOf
  rw [List.lookup_cons]
  by_cases h : u = k
  · subst h; simp
  · have : (u == k) = false := by simpa using h
    simp [this, h]

theorem conjOf_not {L : List (Nat × Sorts.Conj)} {u : Nat} (h : ∀ e ∈ L, e.1 ≠ u) :
    conjOf L u = ∅ := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [conjOf_cons, ite_neg' (fun e' => h e (by simp) e'.symm)]
    exact ih fun e' he' => h e' (List.mem_cons_of_mem _ he')

theorem conjOf_mem {L : List (Nat × Sorts.Conj)} {u : Nat} {c : Sorts.Conj}
    (hnd : (L.map Prod.fst).Nodup) (h : (u, c) ∈ L) : conjOf L u = c := by
  induction L with
  | nil => cases h
  | cons e L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [conjOf_cons]
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have hne : u ≠ e.1 := by
        intro e'
        exact hnd.1 (e' ▸ List.mem_map.2 ⟨(u, c), h, rfl⟩)
      rw [ite_neg' hne]
      exact ih hnd.2 h

/-- With distinct variables, two entries of one variable are one entry. -/
theorem entry_unique {L : List (Nat × Sorts.Conj)} (hnd : (L.map Prod.fst).Nodup)
    {e e' : Nat × Sorts.Conj} (he : e ∈ L) (he' : e' ∈ L) (h : e.1 = e'.1) : e = e' := by
  have h1 := conjOf_mem hnd (u := e.1) (c := e.2) he
  have h2 := conjOf_mem hnd (u := e'.1) (c := e'.2) he'
  rw [h] at h1
  exact Prod.ext h (h1.symm.trans h2)

/-! ## The store a state stands for -/

/-- A store as `sorts::tighten` holds it. -/
structure TSt where
  T : Pat
  X : List (Eqns Nat)
  L : List (Nat × Sorts.Conj)
  N : Nat

/-- The conjunctions of the variables below `N`. -/
def cOf (L : List (Nat × Sorts.Conj)) (N : Nat) : List Sorts.Conj := (List.range N).map (conjOf L)

/-- The store of the specification a state stands for. -/
def TSt.abs (st : TSt) : Sorts.CStore := ⟨st.T, cOf st.L st.N, st.X⟩

/-- The entries are of distinct variables, below the next one. -/
structure TSt.OK (st : TSt) : Prop where
  nodup : (st.L.map Prod.fst).Nodup
  lt : ∀ e ∈ st.L, e.1 < st.N

theorem conj_cOf (L : List (Nat × Sorts.Conj)) (N u : Nat) :
    (cOf L N).getD u ∅ = if u < N then conjOf L u else ∅ := by
  unfold cOf
  rw [List.getD_eq_getElem?_getD]
  by_cases h : u < N
  · simp [h]
  · simp [h]

theorem TSt.abs_conj (st : TSt) (u : Nat) :
    st.abs.conj u = if u < st.N then conjOf st.L u else ∅ := conj_cOf st.L st.N u

theorem TSt.OK.conj {st : TSt} (h : st.OK) (u : Nat) : st.abs.conj u = conjOf st.L u := by
  rw [st.abs_conj]
  by_cases hu : u < st.N
  · rw [ite_pos' hu]
  · rw [ite_neg' hu]
    exact (conjOf_not fun e he e' => hu (by rw [← e']; exact h.lt e he)).symm

theorem TSt.abs_length (st : TSt) : st.abs.c.length = st.N := by simp [TSt.abs, cOf]

theorem cstore_ext {a b : Sorts.CStore} (ht : a.t = b.t) (hx : a.x = b.x)
    (hl : a.c.length = b.c.length) (hc : ∀ u, a.conj u = b.conj u) : a = b := by
  obtain ⟨at', ac, ax⟩ := a
  obtain ⟨bt, bc, bx⟩ := b
  simp only at ht hx hl
  subst ht hx
  congr 1
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have := hc i
  simpa [Sorts.CStore.conj, List.getD_eq_getElem?_getD, h1, h2] using this

/-! ## Settling the variables of entries -/

/-- Settling the variables of entries that say what the store says of them. -/
theorem settle_entries (S : Sorts) (s : Sorts.CStore) (E : List (Nat × Sorts.Conj))
    (hnd : (E.map Prod.fst).Nodup) (hE : ∀ e ∈ E, s.conj e.1 = e.2) :
    (Sorts.CStore.settle S s (E.map Prod.fst)).t = (settleT S E (s.t, s.x)).1 ∧
    (Sorts.CStore.settle S s (E.map Prod.fst)).x = (settleT S E (s.t, s.x)).2 ∧
    ∀ u, (Sorts.CStore.settle S s (E.map Prod.fst)).conj u =
      if (∃ e ∈ E, e.1 = u ∧ isOne (Sorts.count S e.2) = true) then ∅ else s.conj u := by
  obtain ⟨h1, h2, h3⟩ := settle_link S (E.map Prod.fst) s hnd
  have hmap : ((E.map Prod.fst).map fun w => (w, s.conj w)) = E := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id E]
    exact List.map_congr_left fun e he => by
      show (e.1, s.conj e.1) = e
      rw [hE e he]
  rw [hmap] at h1 h2
  refine ⟨h1, h2, fun u => ?_⟩
  rw [h3 u]
  by_cases hu : ∃ e ∈ E, e.1 = u ∧ isOne (Sorts.count S e.2) = true
  · obtain ⟨e, he, rfl, ho⟩ := hu
    rw [ite_pos' ⟨List.mem_map.2 ⟨e, he, rfl⟩, by rw [hE e he]; exact ho⟩,
      ite_pos' ⟨e, he, rfl, ho⟩]
  · rw [ite_neg' hu, ite_neg']
    rintro ⟨hm, ho⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    exact hu ⟨e, he, rfl, by rw [← hE e he]; exact ho⟩

theorem mem_settleKept {S : Sorts} {E : List (Nat × Sorts.Conj)} {e : Nat × Sorts.Conj} :
    e ∈ settleKept S E ↔ e ∈ E ∧ isOne (Sorts.count S e.2) = false := by
  simp [settleKept]

theorem settleKept_nodup {S : Sorts} {E : List (Nat × Sorts.Conj)}
    (hnd : (E.map Prod.fst).Nodup) : ((settleKept S E).map Prod.fst).Nodup :=
  hnd.sublist (List.filter_sublist.map _)

/-- The conjunction the entries that are left give a variable. -/
theorem conjOf_settleKept {S : Sorts} {E : List (Nat × Sorts.Conj)}
    (hnd : (E.map Prod.fst).Nodup) (u : Nat) :
    conjOf (settleKept S E) u =
      if (∃ e ∈ E, e.1 = u ∧ isOne (Sorts.count S e.2) = true) then ∅ else conjOf E u := by
  by_cases hu : ∃ c, (u, c) ∈ E
  · obtain ⟨c, hc⟩ := hu
    by_cases ho : isOne (Sorts.count S c) = true
    · rw [ite_pos' ⟨(u, c), hc, rfl, ho⟩]
      refine conjOf_not fun e he e' => ?_
      obtain ⟨he1, he2⟩ := mem_settleKept.1 he
      have := entry_unique hnd he1 hc e'
      subst this
      rw [ho] at he2
      cases he2
    · rw [ite_neg', conjOf_mem hnd hc]
      · exact conjOf_mem (settleKept_nodup hnd) (mem_settleKept.2 ⟨hc, by simpa using ho⟩)
      · rintro ⟨e, he, e', ho'⟩
        have := entry_unique hnd he hc e'
        subst this
        exact ho ho'
  · have hno : ∀ e ∈ E, e.1 ≠ u := fun e he e' => hu ⟨e.2, by rw [← e']; exact he⟩
    rw [ite_neg' (fun ⟨e, he, e', _⟩ => hno e he e'), conjOf_not hno]
    exact conjOf_not fun e he => hno e (mem_settleKept.1 he).1

/-- The state after the first replacement of the variables with one value. -/
def settleSt (S : Sorts) (st : TSt) : TSt :=
  ⟨(settleT S st.L (st.T, st.X)).1, (settleT S st.L (st.T, st.X)).2, settleKept S st.L, st.N⟩

theorem settleSt_ok {S : Sorts} {st : TSt} (h : st.OK) : (settleSt S st).OK :=
  ⟨settleKept_nodup h.nodup, fun e he => h.lt e (mem_settleKept.1 he).1⟩

theorem settleSt_abs {S : Sorts} {st : TSt} (h : st.OK) :
    (settleSt S st).abs = Sorts.CStore.settle S st.abs (st.L.map Prod.fst) := by
  obtain ⟨h1, h2, h3⟩ := settle_entries S st.abs st.L h.nodup fun e he => by
    rw [h.conj]; exact conjOf_mem h.nodup he
  refine cstore_ext h1.symm h2.symm ?_ fun u => ?_
  · rw [(Sorts.settle_spec S _ _).2.1, TSt.abs_length, TSt.abs_length]; rfl
  · rw [h3 u, (settleSt_ok h).conj, h.conj]
    exact conjOf_settleKept h.nodup u

/-! ## A round -/

/-- The first entry whose variable has values with one root: the entries
before it, the entry, the root, and the entries after it. -/
def splitSole (S : Sorts) (X : List (Eqns Nat)) :
    List (Nat × Sorts.Conj) →
      Option (List (Nat × Sorts.Conj) × (Nat × Sorts.Conj) × (Sym × Nat) × List (Nat × Sorts.Conj))
  | [] => none
  | e :: L =>
    match Sorts.sole S e.2 (Sorts.gone X e.1) with
    | some κ => some ([], e, κ, L)
    | none => (splitSole S X L).map fun q => (e :: q.1, q.2)

theorem splitSole_none {S : Sorts} {X : List (Eqns Nat)} :
    ∀ {L : List (Nat × Sorts.Conj)},
      (∀ e ∈ L, Sorts.sole S e.2 (Sorts.gone X e.1) = none) → splitSole S X L = none
  | [], _ => rfl
  | e :: L, h => by
    simp only [splitSole, h e (by simp), Option.map_eq_none_iff]
    exact splitSole_none fun e' he' => h e' (List.mem_cons_of_mem _ he')

theorem splitSole_some {S : Sorts} {X : List (Eqns Nat)} {en : Nat × Sorts.Conj}
    {κ : Sym × Nat} {post : List (Nat × Sorts.Conj)}
    (hs : Sorts.sole S en.2 (Sorts.gone X en.1) = some κ) :
    ∀ {pre : List (Nat × Sorts.Conj)},
      (∀ e ∈ pre, Sorts.sole S e.2 (Sorts.gone X e.1) = none) →
      splitSole S X (pre ++ en :: post) = some (pre, en, κ, post)
  | [], _ => by simp only [List.nil_append, splitSole, hs]
  | e :: pre, h => by
    simp only [List.cons_append, splitSole, h e (by simp),
      splitSole_some hs fun e' he' => h e' (List.mem_cons_of_mem _ he'), Option.map_some]

theorem splitSole_spec {S : Sorts} {X : List (Eqns Nat)} :
    ∀ (L : List (Nat × Sorts.Conj)),
      match splitSole S X L with
      | none => ∀ e ∈ L, Sorts.sole S e.2 (Sorts.gone X e.1) = none
      | some (pre, en, κ, post) => L = pre ++ en :: post ∧
          (∀ e ∈ pre, Sorts.sole S e.2 (Sorts.gone X e.1) = none) ∧
          Sorts.sole S en.2 (Sorts.gone X en.1) = some κ
  | [] => by simp [splitSole]
  | e :: L => by
    have ih := splitSole_spec (S := S) (X := X) L
    cases hs : Sorts.sole S e.2 (Sorts.gone X e.1) with
    | some κ => simp [splitSole, hs]
    | none =>
      cases hq : splitSole S X L with
      | none =>
        rw [hq] at ih
        simp only [splitSole, hs, hq, Option.map_none]
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · exact hs
        · exact ih e' he'
      | some q =>
        obtain ⟨pre, en, κ, post⟩ := q
        rw [hq] at ih
        simp only [splitSole, hs, hq, Option.map_some]
        obtain ⟨h1, h2, h3⟩ := ih
        refine ⟨by rw [h1]; rfl, ?_, h3⟩
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · exact hs
        · exact h2 e' he'

/-- The entries of the new variables of a replacement. -/
def newEntries (S : Sorts) (st : TSt) (en : Nat × Sorts.Conj) (κ : Sym × Nat) :
    List (Nat × Sorts.Conj) :=
  entsFrom st.N (altOf S en.2 κ.1 κ.2)

/-- The state after the replacement of the variable of the entry `en`, which
stands between `pre` and `post`, by the root `κ`. -/
def openSt (S : Sorts) (st : TSt) (pre post : List (Nat × Sorts.Conj)) (en : Nat × Sorts.Conj)
    (κ : Sym × Nat) : TSt :=
  ⟨(settleT S (newEntries S st en κ)
      (st.T.bind (Term.single en.1 (Sorts.expVar st.N κ.2 κ.1)),
        st.X.map (Eqns.subst en.1 (Sorts.expVar st.N κ.2 κ.1)))).1,
    (settleT S (newEntries S st en κ)
      (st.T.bind (Term.single en.1 (Sorts.expVar st.N κ.2 κ.1)),
        st.X.map (Eqns.subst en.1 (Sorts.expVar st.N κ.2 κ.1)))).2,
    (settleKept S (newEntries S st en κ)).reverse ++ (pre ++ post), st.N + κ.2⟩

/-- What a round comes to. -/
inductive Round where
  /-- An exclusion always holds. -/
  | dead
  /-- No variable has values with one root. -/
  | done
  /-- A variable was replaced; the flag says whether every new entry has a
  member. -/
  | next (st : TSt) (ok : Bool)

/-- One round of the loop of `sorts::tighten`. -/
def round (S : Sorts) (st : TSt) : Round :=
  if st.X.any Sorts.always then .dead
  else
    match splitSole S st.X st.L with
    | none => .done
    | some (pre, en, κ, post) =>
      .next (openSt S st pre post en κ) (settleOk S (newEntries S st en κ))

/-- The state after at most `k` rounds: nothing when more are needed, and
otherwise the state reached, or nothing when the store denotes nothing. -/
def tightRun (S : Sorts) : Nat → TSt → Option (Option TSt)
  | 0, _ => none
  | k + 1, st =>
    match round S st with
    | .dead => some none
    | .done => some (some st)
    | .next st' ok => if ok then tightRun S k st' else some none

/-! ## A replacement is `stepAt` -/

theorem entsFrom_map_range (g : Nat → Sorts.Conj) :
    ∀ (n N : Nat), entsFrom N ((List.range n).map g) = (List.range n).map fun i => (N + i, g i) := by
  intro n
  induction n generalizing g with
  | zero => intro N; rfl
  | succ n ih =>
    intro N
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, entsFrom]
    rw [ih]
    simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

theorem newEntries_eq (S : Sorts) (st : TSt) (en : Nat × Sorts.Conj) (κ : Sym × Nat) :
    newEntries S st en κ =
      (List.range κ.2).map fun i => (st.N + i, Sorts.kidC S en.2 κ.1 κ.2 i) :=
  entsFrom_map_range _ _ _

theorem newEntries_keys (S : Sorts) (st : TSt) (en : Nat × Sorts.Conj) (κ : Sym × Nat) :
    (newEntries S st en κ).map Prod.fst = (List.range κ.2).map (st.N + ·) := by
  rw [newEntries_eq, List.map_map]; rfl

theorem mem_newEntries {S : Sorts} {st : TSt} {en : Nat × Sorts.Conj} {κ : Sym × Nat}
    {e : Nat × Sorts.Conj} :
    e ∈ newEntries S st en κ ↔ ∃ i, i < κ.2 ∧ e = (st.N + i, Sorts.kidC S en.2 κ.1 κ.2 i) := by
  rw [newEntries_eq]
  simp only [List.mem_map, List.mem_range]
  exact ⟨fun ⟨i, hi, e'⟩ => ⟨i, hi, e'.symm⟩, fun ⟨i, hi, e'⟩ => ⟨i, hi, e'.symm⟩⟩

theorem newEntries_nodup (S : Sorts) (st : TSt) (en : Nat × Sorts.Conj) (κ : Sym × Nat) :
    ((newEntries S st en κ).map Prod.fst).Nodup := by
  rw [newEntries_keys]
  exact List.nodup_range.map fun a b h => by simpa using h

section step

variable {S : Sorts} {st : TSt} {pre post : List (Nat × Sorts.Conj)} {en : Nat × Sorts.Conj}
  {κ : Sym × Nat}

theorem pre_post_no_key (h : st.OK) (hL : st.L = pre ++ en :: post) :
    ∀ e ∈ pre ++ post, e.1 ≠ en.1 := by
  have hnd := h.nodup
  rw [hL, List.map_append, List.map_cons, List.nodup_middle, List.nodup_cons] at hnd
  intro e he e'
  refine hnd.1 ?_
  rw [← List.map_append, ← e']
  exact List.mem_map.2 ⟨e, he, rfl⟩

theorem pre_post_sub (hL : st.L = pre ++ en :: post) : ∀ e ∈ pre ++ post, e ∈ st.L := by
  intro e he
  rw [hL]
  rcases List.mem_append.1 he with he | he
  · exact List.mem_append_left _ he
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ he)

theorem pre_post_nodup (h : st.OK) (hL : st.L = pre ++ en :: post) :
    ((pre ++ post).map Prod.fst).Nodup := by
  have hnd := h.nodup
  rw [hL, List.map_append, List.map_cons, List.nodup_middle, List.nodup_cons] at hnd
  rw [List.map_append]
  exact hnd.2

theorem openSt_ok (h : st.OK) (hL : st.L = pre ++ en :: post) : (openSt S st pre post en κ).OK := by
  have hnewlt : ∀ e ∈ settleKept S (newEntries S st en κ), st.N ≤ e.1 ∧ e.1 < st.N + κ.2 := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := mem_newEntries.1 (mem_settleKept.1 he).1
    exact ⟨Nat.le_add_right _ _, by simpa using hi⟩
  constructor
  · show (((settleKept S (newEntries S st en κ)).reverse ++ (pre ++ post)).map Prod.fst).Nodup
    rw [List.map_append, List.map_reverse]
    refine List.Nodup.append (List.nodup_reverse.2 (settleKept_nodup (newEntries_nodup S st en κ)))
      (pre_post_nodup h hL) ?_
    intro a ha hb
    rw [List.mem_reverse] at ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    obtain ⟨e', he', e''⟩ := List.mem_map.1 hb
    have := h.lt e' (pre_post_sub hL e' he')
    have := (hnewlt e he).1
    omega
  · intro e he
    show e.1 < st.N + κ.2
    rcases List.mem_append.1 he with he | he
    · exact (hnewlt e (List.mem_reverse.1 he)).2
    · have := h.lt e (pre_post_sub hL e he)
      omega

/-- A round that replaces a variable is `stepAt` at that variable. -/
theorem openSt_abs (h : st.OK) (hL : st.L = pre ++ en :: post) :
    (openSt S st pre post en κ).abs = Sorts.stepAt S st.abs en.1 κ := by
  have hen : en ∈ st.L := by rw [hL]; simp
  have hv : en.1 < st.abs.c.length := by rw [TSt.abs_length]; exact h.lt en hen
  have hvN : en.1 < st.N := h.lt en hen
  have hcv : st.abs.conj en.1 = en.2 := by rw [h.conj]; exact conjOf_mem h.nodup hen
  -- the sorts after the replacement
  have hexp : ∀ u, (st.abs.exp S en.1 κ.1 κ.2).conj u =
      if u = en.1 then ∅ else if st.N ≤ u ∧ u < st.N + κ.2
        then Sorts.kidC S en.2 κ.1 κ.2 (u - st.N) else conjOf st.L u := by
    intro u
    have := congrArg (fun s : Sorts.Store => s.c u) (st.abs.exp_store (S := S) hv κ.1 κ.2)
    simp only [Sorts.expStore, Sorts.CStore.store, TSt.abs_length] at this
    rw [hcv, h.conj] at this
    exact this
  have hE : ∀ e ∈ newEntries S st en κ, (st.abs.exp S en.1 κ.1 κ.2).conj e.1 = e.2 := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := mem_newEntries.1 he
    rw [hexp, ite_neg' (by omega), ite_pos' ⟨by omega, by omega⟩]
    simp
  obtain ⟨h1, h2, h3⟩ := settle_entries S (st.abs.exp S en.1 κ.1 κ.2) (newEntries S st en κ)
    (newEntries_nodup S st en κ) hE
  have ht : (st.abs.exp S en.1 κ.1 κ.2).t =
      st.T.bind (Term.single en.1 (Sorts.expVar st.N κ.2 κ.1)) := by
    show st.T.bind (Term.single en.1 (Sorts.expVar st.abs.c.length κ.2 κ.1)) = _
    rw [TSt.abs_length]
  have hx : (st.abs.exp S en.1 κ.1 κ.2).x =
      st.X.map (Eqns.subst en.1 (Sorts.expVar st.N κ.2 κ.1)) := by
    show st.X.map (Eqns.subst en.1 (Sorts.expVar st.abs.c.length κ.2 κ.1)) = _
    rw [TSt.abs_length]
  rw [ht, hx] at h1 h2
  have hws : (newEntries S st en κ).map Prod.fst =
      (List.range κ.2).map (st.abs.c.length + ·) := by
    rw [newEntries_keys, TSt.abs_length]
  unfold Sorts.stepAt
  rw [← hws]
  refine cstore_ext (show (openSt S st pre post en κ).abs.t = _ from h1.symm)
    (show (openSt S st pre post en κ).abs.x = _ from h2.symm) ?_ fun u => ?_
  · rw [(Sorts.settle_spec S _ _).2.1, Sorts.CStore.exp_length, TSt.abs_length, TSt.abs_length]
    rfl
  · rw [h3 u, (openSt_ok h hL).conj, hexp]
    show conjOf ((settleKept S (newEntries S st en κ)).reverse ++ (pre ++ post)) u = _
    have hok := (openSt_ok (S := S) (κ := κ) h hL).nodup
    change (((settleKept S (newEntries S st en κ)).reverse ++ (pre ++ post)).map Prod.fst).Nodup
      at hok
    have hnok : ∀ e ∈ pre ++ post, ¬ (st.N ≤ e.1) := fun e he hge => by
      have := h.lt e (pre_post_sub hL e he); omega
    have hnew : ∀ e ∈ newEntries S st en κ, st.N ≤ e.1 ∧ e.1 < st.N + κ.2 := by
      intro e he
      obtain ⟨i, hi, rfl⟩ := mem_newEntries.1 he
      exact ⟨Nat.le_add_right _ _, by simpa using hi⟩
    by_cases hnewu : st.N ≤ u ∧ u < st.N + κ.2
    · -- a new variable
      have hmem : (u, Sorts.kidC S en.2 κ.1 κ.2 (u - st.N)) ∈ newEntries S st en κ :=
        mem_newEntries.2 ⟨u - st.N, by omega, by congr 1; omega⟩
      by_cases ho : isOne (Sorts.count S (Sorts.kidC S en.2 κ.1 κ.2 (u - st.N))) = true
      · rw [ite_pos' ⟨_, hmem, rfl, ho⟩]
        refine conjOf_not fun e he e' => ?_
        rcases List.mem_append.1 he with he | he
        · obtain ⟨he1, he2⟩ := mem_settleKept.1 (List.mem_reverse.1 he)
          have := entry_unique (newEntries_nodup S st en κ) he1 hmem e'
          subst this
          rw [ho] at he2
          cases he2
        · exact hnok e he (e' ▸ hnewu.1)
      · rw [ite_neg', ite_neg' (by omega), ite_pos' hnewu]
        · exact conjOf_mem hok (List.mem_append_left _ (List.mem_reverse.2
            (mem_settleKept.2 ⟨hmem, by simpa using ho⟩)))
        · rintro ⟨e, he, e', ho'⟩
          have := entry_unique (newEntries_nodup S st en κ) he hmem e'
          subst this
          exact ho ho'
    · rw [ite_neg' (fun ⟨e, he, e', _⟩ => hnewu (e' ▸ hnew e he)), ite_neg' hnewu]
      by_cases huv : u = en.1
      · rw [ite_pos' huv]
        refine conjOf_not fun e he e' => ?_
        rcases List.mem_append.1 he with he | he
        · exact hnewu (e' ▸ hnew e (mem_settleKept.1 (List.mem_reverse.1 he)).1)
        · exact pre_post_no_key h hL e he (e'.trans huv)
      · rw [ite_neg' huv]
        by_cases hu : ∃ c, (u, c) ∈ st.L
        · obtain ⟨c, hc⟩ := hu
          rw [conjOf_mem h.nodup hc]
          refine conjOf_mem hok (List.mem_append_right _ ?_)
          rw [hL] at hc
          rcases List.mem_append.1 hc with hc | hc
          · exact List.mem_append_left _ hc
          · rcases List.mem_cons.1 hc with hc | hc
            · exact absurd (congrArg Prod.fst hc) huv
            · exact List.mem_append_right _ hc
        · have hno : ∀ e ∈ st.L, e.1 ≠ u := fun e he e' => hu ⟨e.2, by rw [← e']; exact he⟩
          rw [conjOf_not hno]
          refine conjOf_not fun e he e' => ?_
          rcases List.mem_append.1 he with he | he
          · exact hnewu (e' ▸ hnew e (mem_settleKept.1 (List.mem_reverse.1 he)).1)
          · exact hno e (pre_post_sub hL e he) e'

end step

/-! ## Runs are replacements in the sense of the specification -/

theorem count_empty (S : Sorts) : Sorts.count S ∅ = .many :=
  Sorts.count_many.2 ⟨.sym "a", .sym "b", by simp, fun n hn => by simp at hn, fun n hn => by simp at hn⟩

theorem sole_empty (S : Sorts) (G : List GTerm) : Sorts.sole S ∅ G = none := by
  simp [Sorts.sole, Sorts.RestOK]

/-- What the loop of `sorts::tighten` keeps: the entries are of distinct
variables below the next one, the store is one `Sorts.tighten` goes on from,
and every entry has more than one member. -/
structure TSt.Good (S : Sorts) (st : TSt) : Prop where
  ok : st.OK
  kept : Sorts.Kept S st.abs
  many : ∀ e ∈ st.L, Sorts.count S e.2 = .many

theorem TSt.Good.conj_many {S : Sorts} {st : TSt} (h : st.Good S) (u : Nat) :
    Sorts.count S (st.abs.conj u) = .many := by
  rw [h.ok.conj]
  by_cases hu : ∃ c, (u, c) ∈ st.L
  · obtain ⟨c, hc⟩ := hu
    rw [conjOf_mem h.ok.nodup hc]
    exact h.many _ hc
  · rw [conjOf_not fun e he e' => hu ⟨e.2, by rw [← e']; exact he⟩]
    exact count_empty S

/-- A state with an entry that has no member does not satisfy the
invariant. -/
theorem not_inv_of_none {S : Sorts} {st : TSt} (hok : st.OK) {e : Nat × Sorts.Conj}
    (he : e ∈ st.L) (hc : Sorts.count S e.2 = .none) : ¬ Sorts.Inv S st.abs := by
  intro hI
  have hcj : st.abs.conj e.1 = e.2 := by rw [hok.conj]; exact conjOf_mem hok.nodup he
  by_cases hv : e.1 ∈ st.abs.t.vars
  · have := hI.many e.1 hv
    rw [hcj, hc] at this
    cases this
  · have := hI.cs e.1 (by rw [TSt.abs_length]; exact hok.lt e he) hv
    rw [hcj] at this
    rw [this, count_empty] at hc
    cases hc

/-- Among well-formed sorts, some number of rounds is enough, and what they
come to is reached by replacements in the sense of the specification. -/
theorem tightRun_total {S : Sorts} (hS : S.WellFormed) :
    ∀ (m : Nat) (st : TSt), Sorts.room S st.abs = m → st.Good S →
      ∃ k o, tightRun S k st = some o ∧ Sorts.Tightens S st.abs (o.map TSt.abs) ∧
        ∀ st', o = some st' → st'.Good S := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro st hm hG
    by_cases hany : st.X.any Sorts.always = true
    · refine ⟨1, none, by simp [tightRun, round, hany], ?_, by intro st' e; cases e⟩
      refine .dead fun hI => ?_
      obtain ⟨E, hE, hE'⟩ := List.any_eq_true.1 hany
      have := hI.open_ E hE
      rw [hE'] at this
      cases this
    · have hopen : ∀ E ∈ st.abs.x, Sorts.always E = false := by
        intro E hE
        by_contra h
        exact hany (List.any_eq_true.2 ⟨E, hE, by simpa using h⟩)
      have hI : Sorts.Inv S st.abs := hG.kept.inv (fun v _ => hG.conj_many v) hopen
      have hsp := splitSole_spec (S := S) (X := st.X) st.L
      cases hq : splitSole S st.X st.L with
      | none =>
        rw [hq] at hsp
        refine ⟨1, some st, by simp [tightRun, round, hany, hq], ?_, by intro st' e; cases e; exact hG⟩
        refine .done hI fun v _ => ?_
        rw [hG.ok.conj]
        by_cases hu : ∃ c, (v, c) ∈ st.L
        · obtain ⟨c, hc⟩ := hu
          rw [conjOf_mem hG.ok.nodup hc]
          exact hsp (v, c) hc
        · rw [conjOf_not fun e he e' => hu ⟨e.2, by rw [← e']; exact he⟩]
          exact sole_empty S _
      | some q =>
        obtain ⟨pre, en, κ, post⟩ := q
        rw [hq] at hsp
        obtain ⟨hL, -, hsole⟩ := hsp
        have hen : en ∈ st.L := by rw [hL]; simp
        have hcj : st.abs.conj en.1 = en.2 := by
          rw [hG.ok.conj]; exact conjOf_mem hG.ok.nodup hen
        have hsole' : Sorts.sole S (st.abs.conj en.1) (Sorts.gone st.abs.x en.1) = some κ := by
          rw [hcj]; exact hsole
        have hv : en.1 ∈ st.abs.t.vars := by
          by_contra hv
          have := hI.cs en.1 (by rw [TSt.abs_length]; exact hG.ok.lt en hen) hv
          rw [this, sole_empty] at hsole'
          cases hsole'
        have habs := openSt_abs (S := S) (κ := κ) hG.ok hL
        have hok' := openSt_ok (S := S) (κ := κ) hG.ok hL
        obtain ⟨-, -, hkept⟩ := Sorts.stepAt_spec hI hv hsole'
        rw [← habs] at hkept
        by_cases hflag : settleOk S (newEntries S st en κ) = true
        · -- every new entry has a member
          have hG' : (openSt S st pre post en κ).Good S := by
            refine ⟨hok', hkept, ?_⟩
            intro e he
            rcases List.mem_append.1 he with he | he
            · obtain ⟨he1, he2⟩ := mem_settleKept.1 (List.mem_reverse.1 he)
              have hnn := (List.all_eq_true.1 hflag) e he1
              cases hc : Sorts.count S e.2 with
              | none => rw [hc] at hnn; simp [noneB] at hnn
              | one g => rw [hc] at he2; simp [isOne] at he2
              | many => rfl
            · exact hG.many e (pre_post_sub hL e he)
          have hlt : Sorts.room S (openSt S st pre post en κ).abs < m := by
            rw [habs, ← hm]; exact Sorts.room_lt_at hS hI hv hsole'
          obtain ⟨k, o, hrun, hT, hgood⟩ := ih _ hlt _ rfl hG'
          refine ⟨k + 1, o, by simp [tightRun, round, hany, hq, hflag, hrun], ?_, hgood⟩
          rw [habs] at hT
          exact .step hI hv hsole' hT
        · refine ⟨1, none, by simp [tightRun, round, hany, hq, hflag], ?_, by intro st' e; cases e⟩
          refine .step hI hv hsole' (.dead ?_)
          rw [← habs]
          have hex : ∃ e ∈ newEntries S st en κ, Sorts.count S e.2 = .none := by
            by_contra hne
            refine hflag (List.all_eq_true.2 fun e he => ?_)
            cases hc : Sorts.count S e.2 with
            | none => exact absurd ⟨e, he, hc⟩ hne
            | one g => rfl
            | many => rfl
          obtain ⟨e, he, hc⟩ := hex
          exact not_inv_of_none hok' (List.mem_append_left _ (List.mem_reverse.2
            (mem_settleKept.2 ⟨he, by rw [hc]; rfl⟩))) hc

end RwLogVerified
