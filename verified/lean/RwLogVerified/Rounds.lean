/-
# The number of rounds of `sorts::tighten`

A round replaces a variable of the pattern by a term that has a variable the
pattern did not have. Such a replacement sends distinct subterms of the
pattern to distinct subterms, and the new variable is one more, so each
round adds a distinct subterm to the pattern (`subs_card_lt_of_fresh`). The
rounds made are then fewer than the distinct subterms of the pattern they
end with.
-/
import RwLogVerified.Tight

namespace RwLogVerified

open RwLog

/-! ## A replacement by a term with a new variable -/

/-- An instance that has a variable the term did not have contains what the
variable replaced was replaced by. -/
theorem height_le_of_fresh {v y : Nat} {R : Pat} :
    ∀ {t : Pat}, y ∉ t.vars → y ∈ (t.bind (Term.single v R)).vars →
      R.height ≤ (t.bind (Term.single v R)).height
  | .var u, hy, h => by
    by_cases hu : u = v
    · subst hu; simp [Term.single]
    · simp only [Term.bind_var, Term.single, hu, ↓reduceIte] at h
      exact absurd h hy
  | .sym f, _, h => by simp [Term.vars] at h
  | .app a b, hy, h => by
    simp only [Term.vars, List.mem_append, not_or] at hy
    simp only [Term.bind_app, Term.vars, List.mem_append] at h
    simp only [Term.bind_app, Term.height]
    rcases h with h | h
    · have := height_le_of_fresh hy.1 h; omega
    · have := height_le_of_fresh hy.2 h; omega

/-- No term but the variable itself is sent to what the variable is replaced
by, when that has a variable the term does not have. -/
theorem eq_var_of_bind_eq {v y : Nat} {R : Pat} (hR : y ∈ R.vars) :
    ∀ {t : Pat}, y ∉ t.vars → t.bind (Term.single v R) = R → t = .var v
  | .var u, _, h => by
    by_cases hu : u = v
    · rw [hu]
    · simp only [Term.bind_var, Term.single, hu, ↓reduceIte] at h
      rw [← h] at hR
      simp only [Term.vars, List.mem_singleton] at hR
      rename_i hy
      exact absurd (by rw [hR]; simp [Term.vars]) hy
  | .sym f, _, h => by
    simp only [Term.bind_sym] at h
    rw [← h] at hR
    simp [Term.vars] at hR
  | .app a b, hy, h => by
    exfalso
    simp only [Term.vars, List.mem_append, not_or] at hy
    simp only [Term.bind_app] at h
    have hh := congrArg Term.height h
    simp only [Term.height] at hh
    have hR' : y ∈ ((a.bind (Term.single v R)).app (b.bind (Term.single v R))).vars := by
      rw [h]; exact hR
    simp only [Term.vars, List.mem_append] at hR'
    rcases hR' with hR' | hR'
    · have := height_le_of_fresh hy.1 hR'; omega
    · have := height_le_of_fresh hy.2 hR'; omega

/-- Replacing a variable by a term with a variable that two terms do not
have sends them to different terms, unless they are the same. -/
theorem bind_single_inj {v y : Nat} {R : Pat} (hR : y ∈ R.vars) :
    ∀ {a b : Pat}, y ∉ a.vars → y ∉ b.vars →
      a.bind (Term.single v R) = b.bind (Term.single v R) → a = b
  | .var u, b, ha, hb, h => by
    by_cases hu : u = v
    · subst hu
      have e : (Term.var u : Pat).bind (Term.single u R) = R := by simp [Term.single]
      rw [e] at h
      exact (eq_var_of_bind_eq hR hb h.symm).symm
    · have e : (Term.var u : Pat).bind (Term.single v R) = .var u := by simp [Term.single, hu]
      rw [e] at h
      cases b with
      | var w =>
        by_cases hw : w = v
        · subst hw
          simp only [Term.bind_var, Term.single, ↓reduceIte] at h
          rw [← h] at hR
          simp only [Term.vars, List.mem_singleton] at hR
          exact absurd (by rw [hR]; simp [Term.vars]) ha
        · simpa [Term.single, hw] using h
      | sym f => cases h
      | app c d => cases h
  | .sym f, b, _, hb, h => by
    cases b with
    | var w =>
      by_cases hw : w = v
      · subst hw
        simp only [Term.bind_sym, Term.bind_var, Term.single, ↓reduceIte] at h
        rw [← h] at hR
        simp [Term.vars] at hR
      · simp [Term.single, hw] at h
    | sym g => simpa using h
    | app c d => cases h
  | .app a1 a2, b, ha, hb, h => by
    cases b with
    | var w =>
      by_cases hw : w = v
      · subst hw
        have e : (Term.var w : Pat).bind (Term.single w R) = R := by simp [Term.single]
        rw [e] at h
        exact eq_var_of_bind_eq hR ha h
      · simp [Term.single, hw] at h
    | sym g => cases h
    | app b1 b2 =>
      simp only [Term.vars, List.mem_append, not_or] at ha hb
      simp only [Term.bind_app, Term.app.injEq] at h
      rw [bind_single_inj hR ha.1 hb.1 h.1, bind_single_inj hR ha.2 hb.2 h.2]

/-- Replacing a variable of a term by a term that is not a variable and has
a variable the term does not have gives a term with more distinct
subterms. -/
theorem subs_card_lt_of_fresh {v y : Nat} {R T : Pat} (hv : v ∈ T.vars) (hy : y ∉ T.vars)
    (hR : y ∈ R.vars) (hRn : ∀ w, R ≠ .var w) :
    T.subs.card < (T.bind (Term.single v R)).subs.card := by
  have hfresh : ∀ u ∈ T.subs, y ∉ u.vars := fun u hu h =>
    hy (var_mem_subs_iff.1 (Term.subs_trans hu (var_mem_subs_iff.2 h)))
  have hinj : Set.InjOn (Term.bind (Term.single v R)) (T.subs : Set Pat) := fun a ha b hb h =>
    bind_single_inj hR (hfresh a ha) (hfresh b hb) h
  have hsub : insert (Term.var y) (T.subs.image (Term.bind (Term.single v R))) ⊆
      (T.bind (Term.single v R)).subs := by
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · have hRm : R ∈ (T.bind (Term.single v R)).subs := by
        have := mem_subs_bind (Term.single v R) (var_mem_subs_iff.2 hv)
        simpa [Term.single] using this
      exact Term.subs_trans hRm (var_mem_subs_iff.2 hR)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
      exact mem_subs_bind _ ha
  have hnot : Term.var y ∉ T.subs.image (Term.bind (Term.single v R)) := by
    intro h
    obtain ⟨a, ha, e⟩ := Finset.mem_image.1 h
    cases a with
    | var w =>
      by_cases hw : w = v
      · subst hw
        simp only [Term.bind_var, Term.single, ↓reduceIte] at e
        exact hRn y e
      · simp only [Term.bind_var, Term.single, hw, ↓reduceIte, Term.var.injEq] at e
        subst e
        exact hy (var_mem_subs_iff.1 ha)
    | sym f => cases e
    | app c d => cases e
  calc T.subs.card = (T.subs.image (Term.bind (Term.single v R))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ < (insert (Term.var y) (T.subs.image (Term.bind (Term.single v R)))).card := by
        rw [Finset.card_insert_of_notMem hnot]; omega
    _ ≤ _ := Finset.card_le_card hsub

/-! ## A variable with many values has an argument with many values -/

/-- When the values of a conjunction with more than one member have one
root, and every argument of that root has a value, some argument has more
than one. -/
theorem exists_many_kid {S : Sorts} (hS : S.WellFormed) {c : Sorts.Conj} {G : List GTerm}
    {f : Sym} {n : Nat} (hsole : Sorts.sole S c G = some (f, n))
    (hmany : Sorts.count S c = .many)
    (hok : ∀ i < n, Sorts.count S (Sorts.kidC S c f n i) ≠ .none) :
    ∃ i < n, Sorts.count S (Sorts.kidC S c f n i) = .many := by
  by_contra hno
  have hone : ∀ i, ∃ g, i < n → Sorts.count S (Sorts.kidC S c f n i) = .one g := by
    intro i
    by_cases hi : i < n
    · cases hc : Sorts.count S (Sorts.kidC S c f n i) with
      | none => exact absurd hc (hok i hi)
      | one g => exact ⟨g, fun _ => rfl⟩
      | many => exact absurd ⟨i, hi, hc⟩ hno
    · exact ⟨.sym "", fun h => absurd h hi⟩
  choose g hg using hone
  have hsub : {t | Sorts.MemC S c t} ⊆
      (↑(insert (Term.mk f ((List.range n).map g)) G.toFinset) : Set GTerm) := by
    intro t ht
    by_cases hG : t ∈ G
    · simp [hG]
    · have hk := Sorts.sole_sound hsole ht hG
      obtain ⟨f', ts, rfl, -⟩ := Sorts.exists_mk t
      simp only [Term.key, Term.spine_mk, Option.map_some, Option.some.injEq, Prod.mk.injEq]
        at hk
      obtain ⟨rfl, rfl⟩ := hk
      have hkid := (Sorts.memC_mk.1 ht).2
      have e : ts = (List.range ts.length).map g := by
        refine List.ext_getElem (by simp) fun i h1 h2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        exact (Sorts.count_one.1 (hg i h1)).2 _ (hkid i h1)
      rw [← e]
      simp
  exact Sorts.count_many_infinite hS hmany ((Finset.finite_toSet _).subset hsub)

/-! ## What a round does to the pattern -/

theorem mem_vars_bind_single_of_ne {y w : Nat} {u : Pat} :
    ∀ {t : Pat}, y ∈ t.vars → w ≠ y → y ∈ (t.bind (Term.single w u)).vars
  | .var x, h, hw => by
    simp only [Term.vars, List.mem_singleton] at h
    subst h
    simp [Term.single, Ne.symm hw, Term.vars]
  | .sym f, h, _ => by simp [Term.vars] at h
  | .app a b, h, hw => by
    simp only [Term.vars, List.mem_append] at h
    simp only [Term.bind_app, Term.vars, List.mem_append]
    exact h.imp (fun h => mem_vars_bind_single_of_ne h hw)
      (fun h => mem_vars_bind_single_of_ne h hw)

/-- Replacing the variables of entries with one value in an instance of a
term that has none of them replaces them in what the instance put in. -/
theorem settleT_fst_single (S : Sorts) {T : Pat} {v : Nat} :
    ∀ (L : List (Nat × Sorts.Conj)) (R0 : Pat) (X : List (Eqns Nat)),
      (∀ e ∈ L, e.1 ∉ T.vars) →
      (settleT S L (T.bind (Term.single v R0), X)).1 =
        T.bind (Term.single v (settleT S L (R0, [])).1)
  | [], _, _, _ => rfl
  | p :: L, R0, X, h => by
    have hL : ∀ e ∈ L, e.1 ∉ T.vars := fun e he => h e (List.mem_cons_of_mem _ he)
    cases hc : Sorts.count S p.2 with
    | one g =>
      have e1 : (T.bind (Term.single v R0)).bind (Term.single p.1 (GTerm.toPat g)) =
          T.bind (Term.single v (R0.bind (Term.single p.1 (GTerm.toPat g)))) := by
        rw [Term.bind_bind]
        refine Term.bind_congr fun u hu => ?_
        by_cases huv : u = v
        · simp [Term.single, huv]
        · have hup : u ≠ p.1 := fun e => h p List.mem_cons_self (e ▸ hu)
          simp [Term.single, huv, hup]
      simp only [settleT, hc, e1, List.map_nil]
      exact settleT_fst_single S L _ _ hL
    | none => simp only [settleT, hc]; exact settleT_fst_single S L _ _ hL
    | many => simp only [settleT, hc]; exact settleT_fst_single S L _ _ hL

/-- A variable none of whose entries has one value stays. -/
theorem settleT_keeps_var (S : Sorts) {y : Nat} :
    ∀ (L : List (Nat × Sorts.Conj)) (R0 : Pat) (X : List (Eqns Nat)), y ∈ R0.vars →
      (∀ e ∈ L, e.1 = y → ∀ g, Sorts.count S e.2 ≠ .one g) →
      y ∈ (settleT S L (R0, X)).1.vars
  | [], _, _, hy, _ => hy
  | p :: L, R0, X, hy, h => by
    have hL : ∀ e ∈ L, e.1 = y → ∀ g, Sorts.count S e.2 ≠ .one g :=
      fun e he => h e (List.mem_cons_of_mem _ he)
    cases hc : Sorts.count S p.2 with
    | one g =>
      have hp : p.1 ≠ y := fun e => h p List.mem_cons_self e g hc
      simp only [settleT, hc]
      exact settleT_keeps_var S L _ _ (mem_vars_bind_single_of_ne hy hp) hL
    | none => simp only [settleT, hc]; exact settleT_keeps_var S L _ _ hy hL
    | many => simp only [settleT, hc]; exact settleT_keeps_var S L _ _ hy hL

/-- An application stays one. -/
theorem settleT_app (S : Sorts) :
    ∀ (L : List (Nat × Sorts.Conj)) (a b : Pat) (X : List (Eqns Nat)),
      ∃ a' b', (settleT S L (Term.app a b, X)).1 = .app a' b'
  | [], a, b, _ => ⟨a, b, rfl⟩
  | p :: L, a, b, X => by
    cases hc : Sorts.count S p.2 with
    | one g => simp only [settleT, hc, Term.bind_app]; exact settleT_app S L _ _ _
    | none => simp only [settleT, hc]; exact settleT_app S L _ _ _
    | many => simp only [settleT, hc]; exact settleT_app S L _ _ _

theorem expVar_succ_app (N n : Nat) (f : Sym) : ∃ a b, Sorts.expVar N (n + 1) f = .app a b := by
  rw [Sorts.expVar, List.range_succ, List.map_append, Term.mk, List.foldl_append]
  exact ⟨_, _, rfl⟩

/-- A round that replaces a variable gives a pattern with more distinct
subterms. -/
theorem round_subs_lt {S : Sorts} (hS : S.WellFormed) {st st' : TSt} (hG : st.Good S)
    (h : round S st = .next st' true) : st.T.subs.card < st'.T.subs.card := by
  obtain ⟨pre, en, κ, post, hL, hsole, rfl, hflag, -, hv⟩ := round_next hG h
  obtain ⟨f, n⟩ := κ
  have hen : en ∈ st.L := by rw [hL]; simp
  have hfresh : ∀ w ∈ st.T.vars, w < st.N := fun w hw => by
    have := hG.kept.fin.tv w hw
    rwa [TSt.abs_length] at this
  have hok : ∀ i < n, Sorts.count S (Sorts.kidC S en.2 f n i) ≠ .none := by
    intro i hi hc
    have := (List.all_eq_true.1 hflag.symm) (st.N + i, Sorts.kidC S en.2 f n i)
      (mem_newEntries.2 ⟨i, hi, rfl⟩)
    simp [hc, noneB] at this
  obtain ⟨i, hi, hmi⟩ := exists_many_kid hS hsole (hG.many en hen) hok
  have hNE : ∀ e ∈ newEntries S st en (f, n), e.1 ∉ st.T.vars := by
    intro e he hin
    obtain ⟨j, -, rfl⟩ := mem_newEntries.1 he
    have := hfresh _ hin
    simp only at this
    omega
  have eT : (openSt S st pre post en (f, n)).T = st.T.bind (Term.single en.1
      (settleT S (newEntries S st en (f, n)) (Sorts.expVar st.N n f, [])).1) :=
    settleT_fst_single S _ _ _ hNE
  rw [eT]
  refine subs_card_lt_of_fresh (y := st.N + i) hv
    (fun hin => by have := hfresh _ hin; omega)
    (settleT_keeps_var S _ _ _ (Sorts.mem_expVar_vars.2 ⟨by omega, by omega⟩) ?_) ?_
  · intro e he hey g hc
    obtain ⟨j, -, rfl⟩ := mem_newEntries.1 he
    have hj : j = i := by simp only at hey; omega
    subst hj
    rw [hmi] at hc
    cases hc
  · intro w hw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨a, b, hab⟩ := expVar_succ_app st.N m f
    obtain ⟨a', b', hab'⟩ := settleT_app S (newEntries S st en (f, m + 1)) a b []
    rw [hab, hab'] at hw
    cases hw

/-! ## The rounds of a run -/

/-- A round on a state that satisfies the invariant does not stop for an
exclusion that always holds. -/
theorem round_ne_dead {S : Sorts} {st : TSt} (hI : Sorts.Inv S st.abs) : round S st ≠ .dead := by
  have hany : ¬ st.X.any Sorts.always = true := by
    intro hany
    obtain ⟨E, hE, hE'⟩ := List.any_eq_true.1 hany
    have := hI.open_ E hE
    rw [hE'] at this
    cases this
  unfold round
  simp only [hany, Bool.false_eq_true, ↓reduceIte]
  cases splitSole S st.X st.L with
  | none => simp
  | some q => simp

/-- A round that replaces a variable gives every new entry a member, and a
state that satisfies the invariant. -/
theorem round_next_inv {S : Sorts} (hS : S.WellFormed) {st st' : TSt} {ok : Bool}
    (hG : st.Good S) (h : round S st = .next st' ok) : ok = true ∧ Sorts.Inv S st'.abs := by
  obtain ⟨pre, en, κ, post, hL, hsole, rfl, hflag, hI, hv⟩ := round_next hG h
  have hen : en ∈ st.L := by rw [hL]; simp
  have hsole' : Sorts.sole S (st.abs.conj en.1) (Sorts.gone st.abs.x en.1) = some κ := by
    rw [hG.ok.conj, conjOf_mem hG.ok.nodup hen]; exact hsole
  obtain ⟨hden, -, hkept⟩ := Sorts.stepAt_spec hI hv hsole'
  have habs := openSt_abs (S := S) (κ := κ) hG.ok hL
  have hok' := openSt_ok (S := S) (κ := κ) hG.ok hL
  rw [← habs] at hkept hden
  have hI' : Sorts.Inv S (openSt S st pre post en κ).abs := by
    by_contra hn
    have he := Sorts.den_empty_of_not_inv hkept hn
    rw [hden] at he
    obtain ⟨g, hg⟩ := hI.nonempty hS
    rw [he] at hg
    exact hg
  refine ⟨?_, hI'⟩
  rw [hflag]
  by_contra hf
  have hex : ∃ e ∈ newEntries S st en κ, Sorts.count S e.2 = .none := by
    by_contra hne
    refine hf (List.all_eq_true.2 fun e he => ?_)
    cases hc : Sorts.count S e.2 with
    | none => exact absurd ⟨e, he, hc⟩ hne
    | one g => rfl
    | many => rfl
  obtain ⟨e, he, hc⟩ := hex
  exact not_inv_of_none hok' (List.mem_append_left _ (List.mem_reverse.2
    (mem_settleKept.2 ⟨he, by rw [hc]; rfl⟩))) hc hI'

/-- From a state that satisfies the invariant the rounds do not come to
nothing. -/
theorem tightRun_ne_none {S : Sorts} (hS : S.WellFormed) :
    ∀ (k : Nat) (st : TSt), st.Good S → Sorts.Inv S st.abs → tightRun S k st ≠ some none
  | 0, _, _, _ => by simp [tightRun]
  | k + 1, st, hG, hI => by
    cases hr : round S st with
    | dead => exact absurd hr (round_ne_dead hI)
    | done => simp [tightRun, hr]
    | next st1 ok =>
      obtain ⟨rfl, hI1⟩ := round_next_inv hS hG hr
      simp only [tightRun, hr, ↓reduceIte]
      exact tightRun_ne_none hS k st1 (round_good hG hr) hI1

/-- The rounds come to nothing only in the first one, for an exclusion that
always holds. -/
theorem round_dead_of_none {S : Sorts} (hS : S.WellFormed) {k : Nat} {st : TSt}
    (hG : st.Good S) (h : tightRun S k st = some none) : round S st = .dead := by
  cases k with
  | zero => simp [tightRun] at h
  | succ k =>
    cases hr : round S st with
    | dead => rfl
    | done => simp [tightRun, hr] at h
    | next st1 ok =>
      obtain ⟨rfl, hI1⟩ := round_next_inv hS hG hr
      simp only [tightRun, hr, ↓reduceIte] at h
      exact absurd h (tightRun_ne_none hS k st1 (round_good hG hr) hI1)

/-- Once the rounds allowed are enough, allowing more changes neither what
the run comes to nor what it spends. -/
theorem tightRun_add (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r : Nat) :
    ∀ {k : Nat} {st : TSt} {o : Option TSt}, tightRun S k st = some o → ∀ j,
      tightRun S (k + j) st = some o ∧ runCost nm S u r (k + j) st = runCost nm S u r k st
  | 0, _, _, h, _ => by simp [tightRun] at h
  | k + 1, st, o, h, j => by
    rw [Nat.add_right_comm]
    cases hr : round S st with
    | dead => simpa [tightRun, runCost, hr] using h
    | done => simpa [tightRun, runCost, hr] using h
    | next st1 ok =>
      cases ok with
      | true =>
        simp only [tightRun, hr, ↓reduceIte] at h
        obtain ⟨h1, h2⟩ := tightRun_add nm S u r h j
        simp [tightRun, runCost, hr, h1, h2]
      | false => simpa [tightRun, runCost, hr] using h

/-- The states the rounds of a run are made on. -/
def runStates (S : Sorts) : Nat → TSt → List TSt
  | 0, _ => []
  | k + 1, st =>
    match round S st with
    | .next st' true => st :: runStates S k st'
    | _ => [st]

/-- The charge of a run is the charge of its rounds. -/
theorem runCost_eq_sum (nm : Option Nat → RwLog.Sym) (S : Sorts) (u r : Nat) :
    ∀ (k : Nat) (st : TSt),
      runCost nm S u r k st = ((runStates S k st).map (roundCost nm S u r)).sum
  | 0, _ => rfl
  | k + 1, st => by
    cases hr : round S st with
    | dead => simp [runCost, runStates, hr]
    | done => simp [runCost, runStates, hr]
    | next st1 ok =>
      cases ok with
      | true => simp [runCost, runStates, hr, runCost_eq_sum nm S u r k st1]
      | false => simp [runCost, runStates, hr]

/-- The rounds of a run that comes to a state are made on states the rounds
go on from, whose patterns have no more distinct subterms than the pattern
it comes to, and there are no more of them than the distinct subterms the
run adds to the pattern, and one. -/
theorem runStates_bound {S : Sorts} (hS : S.WellFormed) :
    ∀ (k : Nat) (st st' : TSt), st.Good S → tightRun S k st = some (some st') →
      (∀ s ∈ runStates S k st, s.Good S ∧ s.T.subs.card ≤ st'.T.subs.card) ∧
        (runStates S k st).length + st.T.subs.card ≤ st'.T.subs.card + 1 ∧
        st.T.subs.card ≤ st'.T.subs.card ∧ st'.Good S
  | 0, _, _, _, h => by simp [tightRun] at h
  | k + 1, st, st', hG, h => by
    cases hr : round S st with
    | dead => simp [tightRun, hr] at h
    | done =>
      simp only [tightRun, hr, Option.some.injEq] at h
      subst h
      simp only [runStates, hr, List.mem_singleton, forall_eq, List.length_singleton]
      exact ⟨⟨hG, Nat.le_refl _⟩, by omega, Nat.le_refl _, hG⟩
    | next st1 ok =>
      cases ok with
      | false => simp [tightRun, hr] at h
      | true =>
        simp only [tightRun, hr, ↓reduceIte] at h
        obtain ⟨h1, h2, hle, hG'⟩ := runStates_bound hS k st1 st' (round_good hG hr) h
        have hlt := round_subs_lt hS hG hr
        refine ⟨?_, ?_, by omega, hG'⟩
        · intro s hs
          simp only [runStates, hr, List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact ⟨hG, by omega⟩
          · exact h1 s hs
        · simp only [runStates, hr, List.length_cons]
          omega

end RwLogVerified
