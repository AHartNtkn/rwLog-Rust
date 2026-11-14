/-
# Whether a conjunction of sorts has a member, on the store

`sorts::live` goes through the conjunctions a conjunction reaches
(`Sorts.Reach`), keeps for each the symbol and the argument conjunctions of
every root it has a case for and accepts, and then marks in rounds the
conjunctions that have a member (`flag_live_spec`). `live_spec` says it answers whether the conjunction is in
`Sorts.live`, and what it spends in terms of the number of conjunctions
reached.

Table `B` flags a conjunction reached: with yes when it is known to have a
member. `FlagsB` says which.
-/
import RwLogVerified.Conj
import RwLog.Sorts.Reach

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## Conjunctions and their flags -/

/-- A conjunction as the store has it. -/
noncomputable def cpat (z : Sym) (U : List Name) (c : Sorts.Conj) : Pat :=
  namesPat z (conjList U (· ∈ c))

/-- Every sort of the conjunction is a name of the list. -/
def Sub (U : List Name) (c : Sorts.Conj) : Prop := ∀ n ∈ c, n ∈ U

theorem namesPat_inj (z : Sym) : ∀ {xs ys : List Name}, namesPat z xs = namesPat z ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [namesPat, encList] at h
  | _ :: _, [], h => by simp [namesPat, encList] at h
  | x :: xs, y :: ys, h => by
    simp only [namesPat, List.map_cons, encList, Term.app.injEq, Term.sym.injEq] at h
    rw [h.1, namesPat_inj z (xs := xs) (ys := ys) h.2]

theorem cpat_inj {z : Sym} {U : List Name} {c d : Sorts.Conj} (hc : Sub U c) (hd : Sub U d)
    (h : cpat z U c = cpat z U d) : c = d := by
  have := namesPat_inj z h
  rw [← toFinset_conjList hc, ← toFinset_conjList hd, this]

/-- The flag of a node in table `B`. -/
def flagB (s : store.Store) (i : Nat) : Option Bool := (tbl s .B i).map fun v => decide (v ≠ 0)

/-- Table `B` flags the conjunctions as `m` says. -/
structure FlagsB (nm : Option Nat → RwLog.Sym) (s : store.Store) (U : List Name)
    (m : Sorts.Conj → Option Bool) : Prop where
  has : ∀ c, m c ≠ none → Sub U c ∧ ∃ i, Repr nm s.nodes.val i (cpat (nm none) U c) ∧
    flagB s i = m c
  back : ∀ i, flagB s i ≠ none → ∃ c, Sub U c ∧ Repr nm s.nodes.val i (cpat (nm none) U c) ∧
    m c = flagB s i

theorem FlagsB.get (hnm : Function.Injective nm) {s : store.Store} {U : List Name}
    {m : Sorts.Conj → Option Bool} (h : FlagsB nm s U m) (hW : Wf s) {k : Nat} {c : Sorts.Conj}
    (hc : Sub U c) (hk : Repr nm s.nodes.val k (cpat (nm none) U c)) : flagB s k = m c := by
  by_cases hm : m c = none
  · rw [hm]
    by_contra hne
    obtain ⟨d, hd, rd, e⟩ := h.back k hne
    have := cpat_inj hc hd (hk.unique rd)
    subst this
    exact hne (e ▸ hm)
  · obtain ⟨-, i, ri, e⟩ := h.has c hm
    rw [← Repr.inj hnm hW.nodesOK ri hk]; exact e

theorem FlagsB.mono {s s' : store.Store} {U : List Name} {m : Sorts.Conj → Option Bool}
    (h : FlagsB nm s U m) (hx : Extends s s') (ht : tbl s' .B = tbl s .B) : FlagsB nm s' U m := by
  have hf : ∀ i, flagB s' i = flagB s i := fun i => by simp only [flagB, ht]
  constructor
  · intro c hc
    obtain ⟨hs, i, ri, e⟩ := h.has c hc
    exact ⟨hs, i, hx.repr ri, by rw [hf]; exact e⟩
  · intro i hi
    rw [hf] at hi
    obtain ⟨c, hs, ri, e⟩ := h.back i hi
    exact ⟨c, hs, hx.repr ri, by rw [hf]; exact e⟩

theorem FlagsB.set (hnm : Function.Injective nm) {s s' : store.Store} {U : List Name}
    {m : Sorts.Conj → Option Bool} (h : FlagsB nm s U m) (hW : Wf s) {k : Nat} {c : Sorts.Conj}
    {b : Bool} (hc : Sub U c) (hk : Repr nm s.nodes.val k (cpat (nm none) U c))
    (hn : s'.nodes.val = s.nodes.val)
    (ht : tbl s' .B = Function.update (tbl s .B) k (some (if b then 1 else 0))) :
    FlagsB nm s' U (Function.update m c (some b)) := by
  have hfk : flagB s' k = some b := by
    simp only [flagB, ht, Function.update_self, Option.map_some]; cases b <;> simp
  have hf : ∀ i, i ≠ k → flagB s' i = flagB s i := fun i hi => by
    simp only [flagB, ht, Function.update_of_ne hi]
  constructor
  · intro d hd
    by_cases hdc : d = c
    · subst hdc
      exact ⟨hc, k, by rw [hn]; exact hk, by rw [hfk, Function.update_self]⟩
    · rw [Function.update_of_ne hdc] at hd ⊢
      obtain ⟨hs, i, ri, e⟩ := h.has d hd
      have hik : i ≠ k := by
        rintro rfl
        exact hdc (cpat_inj hs hc (ri.unique hk))
      exact ⟨hs, i, by rw [hn]; exact ri, by rw [hf i hik]; exact e⟩
  · intro i hi
    by_cases hik : i = k
    · subst hik
      exact ⟨c, hc, by rw [hn]; exact hk, by rw [hfk, Function.update_self]⟩
    · rw [hf i hik] at hi ⊢
      obtain ⟨d, hs, ri, e⟩ := h.back i hi
      have hdc : d ≠ c := by
        rintro rfl
        exact hik (Repr.inj hnm hW.nodesOK ri hk)
      exact ⟨d, hs, by rw [hn]; exact ri, by rw [Function.update_of_ne hdc]; exact e⟩

/-- A list of conjunctions as the store has it. -/
noncomputable def altPat (z : Sym) (U : List Name) (a : List Sorts.Conj) : Pat :=
  encList z (a.map (cpat z U))

/-- A function ran that may have written the tables: the invariant, the
nodes there were, the stack, and at most `n` ticks spent. -/
structure RanB (s s' : store.Store) (n : Nat) : Prop where
  wf : Wf s'
  ext : Extends s s'
  stk : stk s' = stk s
  ticks : s'.ticks.val ≤ s.ticks.val + n

theorem Ran.ranB {s s' : store.Store} {n : Nat} (h : Ran s s' n) : RanB s s' n :=
  ⟨h.wf, h.ext, h.stk, h.ticks⟩

theorem RanB.refl {s : store.Store} (h : Wf s) : RanB s s 0 :=
  ⟨h, Extends.refl s, rfl, Nat.le_refl _⟩

theorem RanB.trans {a b c : store.Store} {n m : Nat} (h₁ : RanB a b n) (h₂ : RanB b c m) :
    RanB a c (n + m) :=
  ⟨h₂.wf, h₁.ext.trans h₂.ext, by rw [h₂.stk, h₁.stk], by
    have := h₁.ticks; have := h₂.ticks; omega⟩

theorem RanB.mono {s s' : store.Store} {n m : Nat} (h : RanB s s' n) (hnm : n ≤ m) : RanB s s' m :=
  ⟨h.wf, h.ext, h.stk, by have := h.ticks; omega⟩

/-! ## Is every conjunction of a list flagged with yes -/

theorem all_live_done (s : store.Store) (kids : store.TermId) (ok1 : Bool) :
    sorts.all_live_loop s kids ok1 false ⦃ r => r = (ok1, s) ⦄ := by
  unfold sorts.all_live_loop
  rw [loop]
  simp only [sorts.all_live_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem all_live_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Sorts.Conj → Option Bool} :
    ∀ (a : List Sorts.Conj) (s : store.Store) (kids : store.TermId), Wf s → FlagsB nm s U m →
    (∀ c ∈ a, Sub U c) → Repr nm s.nodes.val kids.val (altPat (nm none) U a) →
    Room s (2 * a.length + 1) →
    sorts.all_live_loop s kids true true ⦃ r =>
      Ran s r.2 (2 * a.length + 1) ∧ (r.1 = true ↔ ∀ c ∈ a, m c = some true) ⦄ := by
  intro a
  induction a with
  | nil =>
    intro s kids hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.all_live_loop
    rw [loop]
    simp only [sorts.all_live_loop.body, ↓reduceIte]
    step with uncons_repr s kids hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := all_live_done s1 kids true
    unfold sorts.all_live_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by omega), by simp⟩
  | cons x a ih =>
    intro s kids hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.all_live_loop
    rw [loop]
    simp only [sorts.all_live_loop.body, ↓reduceIte]
    step with uncons_repr s kids hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with get_flag_w s1 .B k hK.wf (by rw [hK.nodes]; exact rk.lt) (by unfold Room; omega)
      as ⟨r1, hfl, hK2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hfl hK2
    have ht2 := hK2.ticks
    have hmx : o1 = m x := by
      rw [hfl]
      have := hF.get hnm hW (hs x List.mem_cons_self) rk
      simp only [flagB] at this
      rw [hK.tbl]; exact this
    have R2 : Ran s s2 2 := (hK.ran.trans hK2.ran)
    have stop : m x ≠ some true →
        sorts.all_live_loop s2 kids false false ⦃ r =>
          Ran s r.2 (2 * (x :: a).length + 1) ∧ (r.1 = true ↔ ∀ c ∈ x :: a, m c = some true) ⦄ := by
      intro hne
      refine WP.spec_mono (all_live_done s2 kids false) ?_
      rintro r rfl
      exact ⟨R2.mono (by simp only [List.length_cons]; omega),
        by simpa using fun h => absurd h hne⟩
    cases o1 with
    | none =>
      simp only [uncurry, bind_ok]
      have := stop (by rw [← hmx]; simp)
      unfold sorts.all_live_loop at this
      exact this
    | some b =>
      cases b with
      | false =>
        simp only [uncurry, bind_ok, Bool.false_eq_true, ↓reduceIte]
        have := stop (by rw [← hmx]; simp)
        unfold sorts.all_live_loop at this
        exact this
      | true =>
        simp only [uncurry, bind_ok, ↓reduceIte]
        have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
        have IH := ih s2 t hK2.wf (hF.mono R2.ext (by rw [R2.tbl]))
          (fun c hc => hs c (List.mem_cons_of_mem _ hc)) (by rw [hn2]; exact rt)
          (by unfold Room; omega)
        unfold sorts.all_live_loop at IH
        refine WP.spec_mono IH ?_
        rintro r ⟨hR, hr⟩
        refine ⟨(R2.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
        rw [hr]
        simp only [List.mem_cons, forall_eq_or_imp, ← hmx, true_and]

theorem all_live_spec' (hnm : Function.Injective nm) {U : List Name}
    {m : Sorts.Conj → Option Bool} (a : List Sorts.Conj) (s : store.Store) (kids : store.TermId)
    (hW : Wf s) (hF : FlagsB nm s U m) (hs : ∀ c ∈ a, Sub U c)
    (hk : Repr nm s.nodes.val kids.val (altPat (nm none) U a)) (hroom : Room s (2 * a.length + 1)) :
    sorts.all_live s kids ⦃ r =>
      Ran s r.2 (2 * a.length + 1) ∧ (r.1 = true ↔ ∀ c ∈ a, m c = some true) ⦄ :=
  all_live_spec hnm a s kids hW hF hs hk hroom

/-! ## Is some alternative all flagged with yes -/

/-- An alternative of a conjunction: a root symbol with the conjunctions of
its arguments. -/
abbrev Alt := Sym × List Sorts.Conj

/-- An alternative as the store has it. -/
noncomputable def kaltPat (z : Sym) (U : List Name) (a : Alt) : Pat :=
  .app (.sym a.1) (altPat z U a.2)

/-- The alternatives of a conjunction as the store has them. -/
noncomputable def altsPat (z : Sym) (U : List Name) (alts' : List Alt) : Pat :=
  encList z (alts'.map (kaltPat z U))

theorem alt_live_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Sorts.Conj → Option Bool} (a : Alt) (s : store.Store) (ai : store.TermId)
    (hW : Wf s) (hF : FlagsB nm s U m) (hs : ∀ c ∈ a.2, Sub U c)
    (hk : Repr nm s.nodes.val ai.val (kaltPat (nm none) U a)) (hroom : Room s (2 * a.2.length + 2)) :
    sorts.alt_live s ai ⦃ r =>
      Ran s r.2 (2 * a.2.length + 2) ∧ (r.1 = true ↔ ∀ c ∈ a.2, m c = some true) ⦄ := by
  have hroom' := hroom
  unfold Room at hroom'
  unfold sorts.alt_live
  step with uncons_repr s ai hW hk (by unfold Room; omega) as ⟨o, s1, hK, hu⟩
  obtain ⟨f, kids, rfl, -, rk⟩ := hu
  have ht1 := hK.ticks
  step with all_live_spec' hnm a.2 s1 kids hK.wf (hF.mono hK.ran.ext (by rw [hK.tbl])) hs
    (by rw [hK.nodes]; exact rk) (by unfold Room; omega) as ⟨r1, hR2, hb⟩
  exact ⟨(hK.ran.trans hR2).mono (by omega), hb⟩

/-- The ticks looking for an alternative may spend. -/
def anyCost : List Alt → Nat
  | [] => 1
  | a :: alts' => 2 * a.2.length + 3 + anyCost alts'

theorem any_alt_done (s : store.Store) (alts : store.TermId) (found : Bool) :
    sorts.any_alt_loop s alts found false ⦃ r => r = (found, s) ⦄ := by
  unfold sorts.any_alt_loop
  rw [loop]
  simp only [sorts.any_alt_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem any_alt_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Sorts.Conj → Option Bool} :
    ∀ (alts' : List Alt) (s : store.Store) (alts : store.TermId), Wf s →
    FlagsB nm s U m → (∀ a ∈ alts', ∀ c ∈ a.2, Sub U c) →
    Repr nm s.nodes.val alts.val (altsPat (nm none) U alts') → Room s (anyCost alts') →
    sorts.any_alt_loop s alts false true ⦃ r =>
      Ran s r.2 (anyCost alts') ∧ (r.1 = true ↔ ∃ a ∈ alts', ∀ c ∈ a.2, m c = some true) ⦄ := by
  intro alts'
  induction alts' with
  | nil =>
    intro s alts hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [anyCost] at hroom'
    unfold sorts.any_alt_loop
    rw [loop]
    simp only [sorts.any_alt_loop.body, ↓reduceIte]
    step with uncons_repr s alts hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altsPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := any_alt_done s1 alts false
    unfold sorts.any_alt_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by simp only [anyCost]; omega), by simp⟩
  | cons x alts' ih =>
    intro s alts hW hF hs hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [anyCost] at hroom'
    unfold sorts.any_alt_loop
    rw [loop]
    simp only [sorts.any_alt_loop.body, ↓reduceIte]
    step with uncons_repr s alts hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altsPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with alt_live_spec hnm x s1 k hK.wf (hF.mono hK.ran.ext (by rw [hK.tbl]))
      (hs x List.mem_cons_self) (by rw [hK.nodes]; exact rk) (by unfold Room; omega)
      as ⟨r1, hR2, hb⟩
    obtain ⟨b, s2⟩ := r1
    simp only at hR2 hb
    have ht2 := hR2.ticks
    have R2 : Ran s s2 (2 * x.2.length + 3) := (hK.ran.trans hR2).mono (by omega)
    cases b with
    | true =>
      have hdn := any_alt_done s2 alts true
      unfold sorts.any_alt_loop at hdn
      simp only [uncurry, ↓reduceIte, bind_ok]
      refine WP.spec_mono hdn ?_
      rintro r rfl
      exact ⟨R2.mono (by simp only [anyCost]; omega), by
        simpa using Or.inl (hb.1 rfl)⟩
    | false =>
      have IH := ih s2 t hR2.wf (hF.mono R2.ext (by rw [R2.tbl]))
        (fun a ha => hs a (List.mem_cons_of_mem _ ha)) (R2.ext.repr rt) (by unfold Room; omega)
      unfold sorts.any_alt_loop at IH
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R2.trans hR).mono (by simp only [anyCost]; omega), ?_⟩
      rw [hr]
      have hx : ¬ ∀ c ∈ x.2, m c = some true := fun h => by simpa using hb.2 h
      simp only [List.mem_cons, exists_eq_or_imp, hx, false_or]

theorem any_alt_spec' (hnm : Function.Injective nm) {U : List Name}
    {m : Sorts.Conj → Option Bool} (alts' : List Alt) (s : store.Store)
    (alts : store.TermId) (hW : Wf s) (hF : FlagsB nm s U m) (hs : ∀ a ∈ alts', ∀ c ∈ a.2, Sub U c)
    (hk : Repr nm s.nodes.val alts.val (altsPat (nm none) U alts')) (hroom : Room s (anyCost alts')) :
    sorts.any_alt s alts ⦃ r =>
      Ran s r.2 (anyCost alts') ∧ (r.1 = true ↔ ∃ a ∈ alts', ∀ c ∈ a.2, m c = some true) ⦄ :=
  any_alt_spec hnm alts' s alts hW hF hs hk hroom

/-! ## One round -/

/-- A conjunction with its alternatives. -/
abbrev Entry := Sorts.Conj × List Alt

noncomputable def entryPat (z : Sym) (U : List Name) (e : Entry) : Pat :=
  .app (cpat z U e.1) (altsPat z U e.2)

/-- The conjunctions reached with their alternatives, as the store has them. -/
noncomputable def graphPat (z : Sym) (U : List Name) (G : List Entry) : Pat :=
  encList z (G.map (entryPat z U))

/-- The ticks one round may spend. -/
def passCost : List Entry → Nat
  | [] => 1
  | e :: G => anyCost e.2 + 4 + passCost G

/-- Every conjunction flagged with yes has a member. -/
def Sound (S : Sorts) (m : Sorts.Conj → Option Bool) : Prop :=
  ∀ c, m c = some true → ∃ t, Sorts.MemC S c t

/-- Flags only change from no to yes. -/
def Le (m m' : Sorts.Conj → Option Bool) : Prop :=
  ∀ c, m' c = m c ∨ (m c = some false ∧ m' c = some true)

theorem Le.refl (m : Sorts.Conj → Option Bool) : Le m m := fun _ => Or.inl rfl

theorem Le.trans {a b c : Sorts.Conj → Option Bool} (h₁ : Le a b) (h₂ : Le b c) : Le a c := by
  intro x
  rcases h₂ x with e | ⟨e₁, e₂⟩
  · rw [e]; exact h₁ x
  · rcases h₁ x with e | ⟨e₃, -⟩
    · exact Or.inr ⟨by rw [← e]; exact e₁, e₂⟩
    · exact Or.inr ⟨e₃, e₂⟩

theorem Le.set {m : Sorts.Conj → Option Bool} {d : Sorts.Conj} (h : m d = some false) :
    Le m (Function.update m d (some true)) := by
  intro x
  by_cases hx : x = d
  · subst hx; exact Or.inr ⟨h, by simp⟩
  · exact Or.inl (Function.update_of_ne hx _ _)

/-- The alternatives kept for a conjunction are over the names, and a member
of each argument conjunction of one gives the conjunction a member. -/
def EntryOK (S : Sorts) (U : List Name) (e : Entry) : Prop :=
  Sub U e.1 ∧ ∀ a ∈ e.2, (∀ c ∈ a.2, Sub U c) ∧
    ((∀ c ∈ a.2, ∃ t, Sorts.MemC S c t) → ∃ t, Sorts.MemC S e.1 t)

/-- No alternative of a conjunction flagged with no is all flagged with yes. -/
def Stable (m : Sorts.Conj → Option Bool) (G : List Entry) : Prop :=
  ∀ e ∈ G, m e.1 = some false → ¬ ∃ a ∈ e.2, ∀ c ∈ a.2, m c = some true

theorem pass_loop_spec (hnm : Function.Injective nm) (S : Sorts) {U : List Name} :
    ∀ (G : List Entry) (s : store.Store) (graph : store.TermId) (ch : Bool)
      (m : Sorts.Conj → Option Bool), Wf s → FlagsB nm s U m → Sound S m →
    (∀ e ∈ G, EntryOK S U e) → (∀ e ∈ G, m e.1 ≠ none) →
    Repr nm s.nodes.val graph.val (graphPat (nm none) U G) → Room s (passCost G) →
    sorts.pass_loop graph s ch ⦃ r => ∃ m',
      RanB s r.2 (passCost G) ∧ FlagsB nm r.2 U m' ∧ Sound S m' ∧
        Le m m' ∧ (ch = true → r.1 = true) ∧ (r.1 = false → m' = m ∧ Stable m G) ∧
        (r.1 = true → ch = true ∨ ∃ e ∈ G, m e.1 = some false ∧ m' e.1 = some true) ⦄ := by
  intro G
  induction G with
  | nil =>
    intro s graph ch m hW hF hSd hG hdom hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [passCost] at hroom'
    unfold sorts.pass_loop
    rw [loop]
    simp only [sorts.pass_loop.body]
    step with uncons_repr s graph hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [graphPat] at hu
    simp only at hK
    subst hu
    have hfin : ∃ m', RanB s s1 (passCost []) ∧ FlagsB nm s1 U m' ∧
        Sound S m' ∧ Le m m' ∧ (ch = true → ch = true) ∧ (ch = false → m' = m ∧ Stable m []) ∧
        (ch = true → ch = true ∨ ∃ e ∈ ([] : List Entry), m e.1 = some false ∧ m' e.1 = some true) :=
      ⟨m, hK.ran.ranB, hF.mono hK.ran.ext (by rw [hK.tbl]), hSd, Le.refl m, id,
        fun _ => ⟨rfl, fun e he => by cases he⟩, fun h => Or.inl h⟩
    step*
  | cons e G ih =>
    intro s graph ch m hW hF hSd hG hdom hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [passCost] at hroom'
    obtain ⟨hsub, hal⟩ := hG e List.mem_cons_self
    have hGt : ∀ e' ∈ G, EntryOK S U e' := fun e' he' => hG e' (List.mem_cons_of_mem _ he')
    unfold sorts.pass_loop
    rw [loop]
    simp only [sorts.pass_loop.body]
    step with uncons_repr s graph hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [graphPat] at hu
    simp only at hK
    obtain ⟨en, t, rfl, ren, rt⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 en hK.wf (by rw [hK.nodes]; exact ren) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [entryPat] at hu2
    simp only at hK2
    obtain ⟨d, alts, rfl, rd, ralts⟩ := hu2
    rw [hK.nodes] at rd ralts
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
    step with get_flag_w s2 .B d hK2.wf (by rw [hn2]; exact rd.lt) (by unfold Room; omega)
      as ⟨r2, hfl, hK3⟩
    obtain ⟨o2, s3⟩ := r2
    simp only at hfl hK3
    have ht3 := hK3.ticks
    have hn3 : s3.nodes.val = s.nodes.val := by rw [hK3.nodes, hn2]
    have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, hK2.tbl, hK.tbl]
    have hx3 : Extends s s3 := Extends.of_eq hn3 (by omega)
    have hst3 : stk s3 = stk s := by rw [hK3.stk, hK2.stk, hK.stk]
    have hmd : o2 = m e.1 := by
      rw [hfl]
      have := hF.get hnm hW hsub rd
      simp only [flagB] at this
      rw [hK2.tbl, hK.tbl]; exact this
    have hF3 : FlagsB nm s3 U m := hF.mono hx3 (by rw [htb3])
    -- the rest of the round, from a store with the same nodes
    have rest : ∀ (s' : store.Store) (ch' : Bool) (m₁ : Sorts.Conj → Option Bool) (k : Nat),
        RanB s s' k → k ≤ anyCost e.2 + 4 → FlagsB nm s' U m₁ → Sound S m₁ → Le m m₁ →
        (ch = true → ch' = true) →
        (ch' = false → m₁ = m ∧ (m e.1 = some false → ¬ ∃ a ∈ e.2, ∀ c ∈ a.2, m c = some true)) →
        (ch' = true → ch = true ∨ (m e.1 = some false ∧ m₁ e.1 = some true)) →
        loop (fun x => match x with
          | (graph1, s1, changed1) => sorts.pass_loop.body graph1 s1 changed1) (t, s', ch') ⦃ r =>
          ∃ m', RanB s r.2 (passCost (e :: G)) ∧
            FlagsB nm r.2 U m' ∧ Sound S m' ∧ Le m m' ∧ (ch = true → r.1 = true) ∧
            (r.1 = false → m' = m ∧ Stable m (e :: G)) ∧
            (r.1 = true → ch = true ∨ ∃ e' ∈ e :: G, m e'.1 = some false ∧ m' e'.1 = some true) ⦄ := by
      intro s' ch' m₁ k R0 hk hF' hS' hLe hch hst hflip
      have htk' := R0.ticks
      have hdom' : ∀ e' ∈ G, m₁ e'.1 ≠ none := by
        intro e' he' h0
        have := hdom e' (List.mem_cons_of_mem _ he')
        rcases hLe e'.1 with h | ⟨-, h⟩
        · exact this (h ▸ h0)
        · rw [h] at h0; cases h0
      have IH := ih s' t ch' m₁ R0.wf hF' hS' hGt hdom' (R0.ext.repr rt)
        (by unfold Room; omega)
      unfold sorts.pass_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨m', hR, hFm, hSm, hLm, hc, hs, hf⟩
      refine ⟨m', (R0.trans hR).mono (by simp only [passCost]; omega), hFm, hSm,
        hLe.trans hLm, fun h => hc (hch h), ?_, ?_⟩
      · intro hr
        obtain ⟨e₁, hstG⟩ := hs hr
        have hch' : ch' = false := by
          cases hc' : ch' with
          | false => rfl
          | true => rw [hc hc'] at hr; cases hr
        obtain ⟨e₂, hste⟩ := hst hch'
        subst e₂
        refine ⟨e₁, ?_⟩
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · exact hste
        · exact hstG e' he'
      · intro hr
        rcases hf hr with hc' | ⟨e', he', h₁, h₂⟩
        · rcases hflip hc' with h | ⟨h₁, h₂⟩
          · exact Or.inl h
          · refine Or.inr ⟨e, List.mem_cons_self, h₁, ?_⟩
            rcases hLm e.1 with h | ⟨-, h⟩
            · rw [h]; exact h₂
            · exact h
        · rcases hLe e'.1 with h | ⟨h₃, -⟩
          · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', by rw [← h]; exact h₁, h₂⟩
          · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h₃, h₂⟩
    cases o2 with
    | none => exact absurd hmd.symm (hdom e List.mem_cons_self)
    | some b =>
      cases b with
      | true =>
        simp only [uncurry, ↓reduceIte, bind_ok]
        exact rest s3 ch m 3 ⟨hK3.wf, hx3, hst3, by omega⟩ (by omega) hF3 hSd (Le.refl m) id
          (fun _ => ⟨rfl, fun h => by rw [← hmd] at h; cases h⟩) (fun h => Or.inl h)
      | false =>
        simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
        step with any_alt_spec' hnm e.2 s3 alts hK3.wf hF3 (fun a ha => (hal a ha).1)
          (by rw [hn3]; exact ralts) (by unfold Room; omega) as ⟨r4, hR4, hb⟩
        obtain ⟨b, s4⟩ := r4
        simp only at hR4 hb
        have ht4 := hR4.ticks
        have R4 : RanB s s4 (anyCost e.2 + 3) :=
          ⟨hR4.wf, hx3.trans hR4.ext, by rw [hR4.stk, hst3], by omega⟩
        have hF4 : FlagsB nm s4 U m := hF3.mono hR4.ext (by rw [hR4.tbl])
        have hmf : m e.1 = some false := hmd.symm
        cases b with
        | false =>
          simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
          exact rest s4 ch m _ R4 (by omega) hF4 hSd (Le.refl m) id
            (fun _ => ⟨rfl, fun _ h => by simpa using hb.2 h⟩) (fun h => Or.inl h)
        | true =>
          simp only [uncurry, ↓reduceIte]
          step with set_flag_w s4 .B d true hR4.wf (R4.ext.repr rd).lt (by unfold Room; omega)
            as ⟨s5, hn5, ht5, hW5, htb5, htbo5, hst5⟩
          have R5 : RanB s s5 (anyCost e.2 + 4) :=
            ⟨hW5, R4.ext.trans (Extends.of_eq hn5 (by omega)), by rw [hst5, R4.stk], by omega⟩
          have hF5 := hF4.set hnm hR4.wf (b := true) hsub (R4.ext.repr rd) hn5
            (by simpa using htb5)
          obtain ⟨a, ha, hall⟩ := hb.1 rfl
          have hS5 : Sound S (Function.update m e.1 (some true)) := by
            intro c hc
            by_cases hce : c = e.1
            · subst hce
              exact (hal a ha).2 fun c hc => hSd c (hall c hc)
            · rw [Function.update_of_ne hce] at hc; exact hSd c hc
          exact rest s5 true _ _ R5 (by omega) hF5 hS5 (Le.set hmf) (fun _ => rfl)
            (fun h => by cases h) (fun _ => Or.inr ⟨hmf, by simp⟩)

/-! ## Rounds until nothing changes -/

theorem pass_spec (hnm : Function.Injective nm) (S : Sorts) {U : List Name} (G : List Entry)
    (s : store.Store) (graph : store.TermId) (m : Sorts.Conj → Option Bool) (hW : Wf s)
    (hF : FlagsB nm s U m) (hSd : Sound S m) (hG : ∀ e ∈ G, EntryOK S U e)
    (hdom : ∀ e ∈ G, m e.1 ≠ none) (hg : Repr nm s.nodes.val graph.val (graphPat (nm none) U G))
    (hroom : Room s (passCost G)) :
    sorts.pass s graph ⦃ r => ∃ m',
      RanB s r.2 (passCost G) ∧ FlagsB nm r.2 U m' ∧ Sound S m' ∧ Le m m' ∧
        (r.1 = false → m' = m ∧ Stable m G) ∧
        (r.1 = true → ∃ e ∈ G, m e.1 = some false ∧ m' e.1 = some true) ⦄ := by
  refine WP.spec_mono (pass_loop_spec hnm S G s graph false m hW hF hSd hG hdom hg hroom) ?_
  rintro r ⟨m', hR, hFm, hSm, hLm, -, hs, hf⟩
  exact ⟨m', hR, hFm, hSm, hLm, hs, fun h => (hf h).resolve_left (by simp)⟩

/-- The conjunctions of the graph flagged with no. -/
noncomputable def falses (G : List Entry) (m : Sorts.Conj → Option Bool) : Nat :=
  ((G.map Prod.fst).toFinset.filter fun c => m c = some false).card

theorem falses_lt {G : List Entry} {m m' : Sorts.Conj → Option Bool} (hLe : Le m m') {e : Entry}
    (he : e ∈ G) (h₁ : m e.1 = some false) (h₂ : m' e.1 = some true) :
    falses G m' < falses G m := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨e.1, ?_, ?_⟩
    · simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map]
      exact ⟨⟨e, he, rfl⟩, h₁⟩
    · simp [h₂]
  · intro c hc
    simp only [Finset.mem_filter] at hc ⊢
    refine ⟨hc.1, ?_⟩
    rcases hLe c with h | ⟨h, h'⟩
    · rw [← h]; exact hc.2
    · exact h

theorem falses_le (G : List Entry) (m : Sorts.Conj → Option Bool) : falses G m ≤ G.length := by
  unfold falses
  refine (Finset.card_filter_le _ _).trans ?_
  exact (List.toFinset_card_le _).trans (by simp)

theorem live_loop_done (s : store.Store) (graph : store.TermId) :
    sorts.flag_live_loop s graph false ⦃ r => r = s ⦄ := by
  unfold sorts.flag_live_loop
  rw [loop]
  simp only [sorts.flag_live_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem live_loop_spec (hnm : Function.Injective nm) (S : Sorts) {U : List Name} (G : List Entry)
    (graph : store.TermId) (hG : ∀ e ∈ G, EntryOK S U e) :
    ∀ (n : Nat) (s : store.Store) (m : Sorts.Conj → Option Bool), falses G m < n → Wf s →
    FlagsB nm s U m → Sound S m → (∀ e ∈ G, m e.1 ≠ none) →
    Repr nm s.nodes.val graph.val (graphPat (nm none) U G) → Room s (n * passCost G) →
    sorts.flag_live_loop s graph true ⦃ s' => ∃ m',
      RanB s s' (n * passCost G) ∧ FlagsB nm s' U m' ∧ Sound S m' ∧ Le m m' ∧ Stable m' G ⦄ := by
  intro n
  induction n with
  | zero => intro s m h; cases h
  | succ n ih =>
    intro s m hlt hW hF hSd hdom hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    rw [Nat.add_mul, Nat.one_mul] at hroom'
    unfold sorts.flag_live_loop
    rw [loop]
    simp only [sorts.flag_live_loop.body, ↓reduceIte]
    step with pass_spec hnm S G s graph m hW hF hSd hG hdom hg (by unfold Room; omega)
      as ⟨r1, m₁, hR, hF₁, hS₁, hLe, hs, hf⟩
    obtain ⟨go1, s1⟩ := r1
    simp only at hR hF₁ hs hf
    have ht1 := hR.ticks
    cases go1 with
    | false =>
      obtain ⟨rfl, hst⟩ := hs rfl
      have hdn := live_loop_done s1 graph
      unfold sorts.flag_live_loop at hdn
      simp only [uncurry, bind_ok]
      refine WP.spec_mono hdn ?_
      rintro r rfl
      exact ⟨m₁, hR.mono (by rw [Nat.add_mul, Nat.one_mul]; omega), hF₁, hS₁, hLe, hst⟩
    | true =>
      obtain ⟨e, he, h₁, h₂⟩ := hf rfl
      have hlt' : falses G m₁ < n := by
        have := falses_lt hLe he h₁ h₂; omega
      have hdom' : ∀ e' ∈ G, m₁ e'.1 ≠ none := by
        intro e' he' h0
        rcases hLe e'.1 with h | ⟨-, h⟩
        · exact hdom e' he' (h ▸ h0)
        · rw [h] at h0; cases h0
      have IH := ih s1 m₁ hlt' hR.wf hF₁ hS₁ hdom' (hR.ext.repr hg) (by unfold Room; omega)
      unfold sorts.flag_live_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro r ⟨m', hR', hF', hS', hLe', hst⟩
      exact ⟨m', (hR.trans hR').mono (by rw [Nat.add_mul, Nat.one_mul]; omega), hF', hS', hLe.trans hLe', hst⟩

/-! ## Has every sort of a conjunction a rest -/

theorem rest_ok_done (s : store.Store) (decls c : store.TermId) (ok1 : Bool) :
    sorts.rest_ok_loop s decls c ok1 false ⦃ r => r = (ok1, s) ⦄ := by
  unfold sorts.rest_ok_loop
  rw [loop]
  simp only [sorts.rest_ok_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

/-- Has the sort a rest. -/
def HasRest (S : Sorts) (n : Name) : Prop := ((S.lookup n).bind (·.rest)).isSome = true

theorem rest_ok_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) :
    ∀ (cs : List Name) (s : store.Store) (decls c : store.TermId), Wf s →
    Repr nm s.nodes.val decls.val sp → Repr nm s.nodes.val c.val (namesPat (nm none) cs) →
    Room s (cs.length * (3 * S.length + 4) + 1) →
    sorts.rest_ok_loop s decls c true true ⦃ r =>
      Ran s r.2 (cs.length * (3 * S.length + 4) + 1) ∧ (r.1 = true ↔ ∀ n ∈ cs, HasRest S n) ⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro s decls c hW hd hc hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.rest_ok_loop
    rw [loop]
    simp only [sorts.rest_ok_loop.body, ↓reduceIte]
    step with uncons_repr s c hW hc (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := rest_ok_done s1 decls c true
    unfold sorts.rest_ok_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by omega), by simp⟩
  | cons x cs ih =>
    intro s decls c hW hd hc hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    unfold sorts.rest_ok_loop
    rw [loop]
    simp only [sorts.rest_ok_loop.body, ↓reduceIte]
    step with uncons_repr s c hW hc (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    obtain ⟨n, t, rfl, rn, rt⟩ := hu
    have ht1 := hK.ticks
    have hx1 := hK.ran.ext
    step with lookup_spec hnm S hS s1 decls n hK.wf (hx1.repr hd) (hx1.repr rn)
      (by unfold Room; omega) as ⟨r1, hR2, hl⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hR2 hl
    have ht2 := hR2.ticks
    have R2 := hK.ran.trans hR2
    have stop : ¬ HasRest S x → ∀ s3 : store.Store, Ran s s3 (3 * S.length + 4) →
        sorts.rest_ok_loop s3 decls c false false ⦃ r =>
          Ran s r.2 ((x :: cs).length * (3 * S.length + 4) + 1) ∧
            (r.1 = true ↔ ∀ n ∈ x :: cs, HasRest S n) ⦄ := by
      intro hne s3 R3
      refine WP.spec_mono (rest_ok_done s3 decls c false) ?_
      rintro r rfl
      exact ⟨R3.mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega),
        by simpa using fun h => absurd h hne⟩
    cases hlk : S.lookup x with
    | none =>
      rw [hlk] at hl
      subst hl
      simp only [uncurry, bind_ok]
      have := stop (by simp [HasRest, hlk]) s2 (R2.mono (by omega))
      unfold sorts.rest_ok_loop at this
      exact this
    | some d =>
      rw [hlk] at hl
      obtain ⟨cc, r, rp, rfl, -, rr, hrest⟩ := hl
      step with is_nil_w s2 r hR2.wf (hR2.ext.repr rr).lt (by unfold Room; omega) as ⟨r3, hb, hK3⟩
      obtain ⟨b, s3⟩ := r3
      simp only at hb hK3
      have ht3 := hK3.ticks
      have R3 : Ran s s3 (3 * S.length + 4) := (R2.trans hK3.ran).mono (by omega)
      have hbr : b = true ↔ d.rest = none := by
        rw [hb]
        have rr2 := hR2.ext.repr rr
        cases hr : d.rest with
        | none =>
          rw [hr] at hrest
          simp only [RestAt] at hrest
          subst hrest
          rcases rr2.sym_node with h | ⟨f, -, e⟩
          · simp [h.1]
          · cases hnm e
        | some rv =>
          rw [hr] at hrest
          obtain ⟨xs, -, rfl⟩ := hrest
          obtain ⟨a, b', h, -, -⟩ := Repr.app_inv rr2
          simp [h]
      cases b with
      | true =>
        simp only [uncurry, ↓reduceIte, bind_ok]
        have := stop (by simp [HasRest, hlk, hbr.1 rfl]) s3 R3
        unfold sorts.rest_ok_loop at this
        exact this
      | false =>
        simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
        have hx : HasRest S x := by
          have : d.rest ≠ none := fun h => by simpa using hbr.2 h
          simp only [HasRest, hlk, Option.bind_some]
          exact Option.isSome_iff_ne_none.2 this
        have IH := ih s3 decls t hK3.wf (R3.ext.repr hd) (R3.ext.repr rt) (by unfold Room; omega)
        unfold sorts.rest_ok_loop at IH
        refine WP.spec_mono IH ?_
        rintro r ⟨hR, hr⟩
        refine ⟨(R3.trans hR).mono
          (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega), ?_⟩
        rw [hr]
        simp only [List.mem_cons, forall_eq_or_imp, hx, true_and]

/-- `rest_ok` on a conjunction: has every sort of it a rest. -/
theorem rest_ok_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) {U : List Name} (c : Sorts.Conj) (hc : Sub U c)
    (s : store.Store) (decls ci : store.TermId) (hW : Wf s)
    (hd : Repr nm s.nodes.val decls.val sp) (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c))
    (hroom : Room s (U.length * (3 * S.length + 4) + 1)) :
    sorts.rest_ok s decls ci ⦃ r =>
      Ran s r.2 (U.length * (3 * S.length + 4) + 1) ∧ (r.1 = true ↔ Sorts.RestOK S c) ⦄ := by
  have hlen := length_conjList_le U (· ∈ c)
  have hmul := Nat.mul_le_mul_right (3 * S.length + 4) hlen
  refine WP.spec_mono (rest_ok_loop_spec hnm S hS _ s decls ci hW hd hci
    (by unfold Room at hroom ⊢; omega)) ?_
  rintro r ⟨hR, hr⟩
  refine ⟨hR.mono (by omega), ?_⟩
  rw [hr]
  simp only [mem_conjList, Sorts.RestOK, HasRest]
  exact ⟨fun h n hn => h n ⟨hc n hn, hn⟩, fun h n hn => h n hn.2⟩

/-! ## Conjunctions still to go through -/

/-- From `m` and `T` to `m'` and `T'`: conjunctions not flagged, all with
`P`, were flagged with no and put in front. -/
def Enq (P : Sorts.Conj → Prop) (m m' : Sorts.Conj → Option Bool) (T T' : List Sorts.Conj) :
    Prop :=
  ∃ new : List Sorts.Conj, T' = new ++ T ∧ new.Nodup ∧ (∀ c ∈ new, m c = none ∧ P c) ∧
    ∀ c, m' c = if c ∈ new then some false else m c

theorem Enq.refl (P : Sorts.Conj → Prop) (m : Sorts.Conj → Option Bool) (T : List Sorts.Conj) :
    Enq P m m T T :=
  ⟨[], rfl, List.nodup_nil, fun _ h => (by cases h), fun _ => (by simp)⟩

theorem Enq.trans {P : Sorts.Conj → Prop} {a b c : Sorts.Conj → Option Bool}
    {T₁ T₂ T₃ : List Sorts.Conj} (h₁ : Enq P a b T₁ T₂) (h₂ : Enq P b c T₂ T₃) :
    Enq P a c T₁ T₃ := by
  obtain ⟨n₁, rfl, nd₁, hn₁, hb⟩ := h₁
  obtain ⟨n₂, rfl, nd₂, hn₂, hc⟩ := h₂
  have hdis : ∀ x ∈ n₂, x ∉ n₁ := by
    intro x hx hx'
    have := (hn₂ x hx).1
    rw [hb] at this
    simp [hx'] at this
  refine ⟨n₂ ++ n₁, by simp, List.nodup_append.2 ⟨nd₂, nd₁, fun x hx y hy e => hdis x hx (e ▸ hy)⟩,
    ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · have := hn₂ x hx
      rw [hb] at this
      simpa [hdis x hx] using this
    · exact hn₁ x hx
  · intro x
    rw [hc, hb]
    by_cases h2 : x ∈ n₂
    · simp [h2]
    · by_cases h1 : x ∈ n₁ <;> simp [h1, h2]

theorem Enq.mono {P Q : Sorts.Conj → Prop} {m m' : Sorts.Conj → Option Bool}
    {T T' : List Sorts.Conj} (h : Enq P m m' T T') (hPQ : ∀ c, P c → Q c) : Enq Q m m' T T' := by
  obtain ⟨n, e, nd, hn, hm⟩ := h
  exact ⟨n, e, nd, fun c hc => ⟨(hn c hc).1, hPQ c (hn c hc).2⟩, hm⟩

theorem Enq.keeps {P : Sorts.Conj → Prop} {m m' : Sorts.Conj → Option Bool}
    {T T' : List Sorts.Conj} (h : Enq P m m' T T') {c : Sorts.Conj} (hc : m c ≠ none) :
    m' c = m c := by
  obtain ⟨n, -, -, hn, hm⟩ := h
  rw [hm]
  split
  · rename_i hin; exact absurd (hn c hin).1 hc
  · rfl

theorem Enq.flagged {P : Sorts.Conj → Prop} {m m' : Sorts.Conj → Option Bool}
    {T T' : List Sorts.Conj} (h : Enq P m m' T T') {c : Sorts.Conj} (hc : m c ≠ none) :
    m' c ≠ none := by rw [h.keeps hc]; exact hc

theorem Enq.one {P : Sorts.Conj → Prop} {m : Sorts.Conj → Option Bool} (T : List Sorts.Conj)
    {x : Sorts.Conj} (hx : m x = none) (hP : P x) :
    Enq P m (Function.update m x (some false)) T (x :: T) := by
  refine ⟨[x], rfl, List.nodup_singleton x, fun c hc => ?_, fun c => ?_⟩
  · rw [List.mem_singleton.1 hc]; exact ⟨hx, hP⟩
  · by_cases h : c = x
    · subst h; simp
    · simp [h]

theorem enqueue_loop_spec (hnm : Function.Injective nm) {U : List Name}
    {P : Sorts.Conj → Prop} :
    ∀ (a : List Sorts.Conj) (s : store.Store) (kids todo : store.TermId) (T : List Sorts.Conj)
      (m : Sorts.Conj → Option Bool), Wf s → FlagsB nm s U m → (∀ c ∈ a, Sub U c ∧ P c) →
    Repr nm s.nodes.val kids.val (altPat (nm none) U a) →
    Repr nm s.nodes.val todo.val (altPat (nm none) U T) → Room s (4 * a.length + 1) →
    sorts.enqueue_loop kids s todo ⦃ r => ∃ m' T',
      RanB s r.2 (4 * a.length + 1) ∧ FlagsB nm r.2 U m' ∧
        Repr nm r.2.nodes.val r.1.val (altPat (nm none) U T') ∧ Enq P m m' T T' ∧
        ∀ c ∈ a, m' c ≠ none ⦄ := by
  intro a
  induction a with
  | nil =>
    intro s kids todo T m hW hF hs hk htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.enqueue_loop
    rw [loop]
    simp only [sorts.enqueue_loop.body]
    step with uncons_repr s kids hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altPat] at hu
    simp only at hK
    subst hu
    have hfin : ∃ m' T', RanB s s1 (4 * ([] : List Sorts.Conj).length + 1) ∧ FlagsB nm s1 U m' ∧
        Repr nm s1.nodes.val todo.val (altPat (nm none) U T') ∧ Enq P m m' T T' ∧
        ∀ c ∈ ([] : List Sorts.Conj), m' c ≠ none :=
      ⟨m, T, hK.ran.ranB, hF.mono hK.ran.ext (by rw [hK.tbl]), by rw [hK.nodes]; exact htd,
        Enq.refl P m T, fun _ h => by cases h⟩
    step*
  | cons x a ih =>
    intro s kids todo T m hW hF hs hk htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    have hsa : ∀ c ∈ a, Sub U c ∧ P c := fun c hc => hs c (List.mem_cons_of_mem _ hc)
    unfold sorts.enqueue_loop
    rw [loop]
    simp only [sorts.enqueue_loop.body]
    step with uncons_repr s kids hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with get_flag_w s1 .B k hK.wf (by rw [hK.nodes]; exact rk.lt) (by unfold Room; omega)
      as ⟨r1, hfl, hK2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hfl hK2
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
    have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK.tbl]
    have R2 : Ran s s2 2 := hK.ran.trans hK2.ran
    have hmx : o1 = m x := by
      rw [hfl]
      have := hF.get hnm hW (hs x List.mem_cons_self).1 rk
      simp only [flagB] at this
      rw [hK.tbl]; exact this
    have hF2 : FlagsB nm s2 U m := hF.mono R2.ext (by rw [htb2])
    -- the rest of the list
    have rest : ∀ (s' : store.Store) (todo' : store.TermId) (m₁ : Sorts.Conj → Option Bool)
        (T₁ : List Sorts.Conj), RanB s s' 4 → FlagsB nm s' U m₁ →
        Repr nm s'.nodes.val todo'.val (altPat (nm none) U T₁) → Enq P m m₁ T T₁ → m₁ x ≠ none →
        loop (fun x => match x with
          | (kids1, s1, todo1) => sorts.enqueue_loop.body kids1 s1 todo1) (t, s', todo') ⦃ r =>
          ∃ m' T', RanB s r.2 (4 * (x :: a).length + 1) ∧ FlagsB nm r.2 U m' ∧
            Repr nm r.2.nodes.val r.1.val (altPat (nm none) U T') ∧ Enq P m m' T T' ∧
            ∀ c ∈ x :: a, m' c ≠ none ⦄ := by
      intro s' todo' m₁ T₁ R0 hF' htd' hE hx
      have := R0.ticks
      have IH := ih s' t todo' T₁ m₁ R0.wf hF' hsa (R0.ext.repr rt) htd' (by unfold Room; omega)
      unfold sorts.enqueue_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨m', T', hR, hFm, hrt, hE', hall⟩
      refine ⟨m', T', (R0.trans hR).mono (by simp only [List.length_cons]; omega), hFm, hrt,
        hE.trans hE', ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hE'.flagged hx
      · exact hall c hc
    cases o1 with
    | some b =>
      simp only [uncurry, bind_ok]
      exact rest s2 todo m T (R2.ranB.mono (by omega)) hF2 (by rw [hn2]; exact htd) (Enq.refl P m T)
        (by rw [← hmx]; simp)
    | none =>
      simp only [uncurry]
      step with set_flag_w s2 .B k false hK2.wf (by rw [hn2]; exact rk.lt) (by unfold Room; omega)
        as ⟨s3, hn3, ht3, hW3, htb3, htbo3, hst3⟩
      have hn3' : s3.nodes.val = s.nodes.val := by rw [hn3, hn2]
      step with alloc_w s3 (.App k todo) hW3 ⟨by rw [hn3']; exact rk.lt, by rw [hn3']; exact htd.lt⟩
        (by unfold Room; omega) as ⟨r4, hW4, ht4, htb4, hx4, hid, hst4⟩
      obtain ⟨todo1, s4⟩ := r4
      simp only at hW4 ht4 htb4 hx4 hid hst4 ⊢
      have hx3 : Extends s s3 := Extends.of_eq hn3' (by omega)
      have R4 : RanB s s4 4 :=
        ⟨hW4, hx3.trans hx4, by rw [hst4, hst3, R2.stk], by omega⟩
      have hF3 := hF2.set hnm hK2.wf (b := false) (hs x List.mem_cons_self).1
        (by rw [hn2]; exact rk) hn3 (by simpa using htb3)
      have htd1 : Repr nm s4.nodes.val todo1.val (altPat (nm none) U (x :: T)) := by
        simp only [altPat, List.map_cons, encList]
        exact .app hid (R4.ext.repr rk) (R4.ext.repr htd)
      simp only [uncurry, bind_ok]
      exact rest s4 todo1 _ (x :: T) R4 (hF3.mono hx4 (by rw [htb4])) htd1
        (Enq.one T hmx.symm (hs x List.mem_cons_self).2) (by simp)

theorem enqueue_spec (hnm : Function.Injective nm) {U : List Name} {P : Sorts.Conj → Prop}
    (a : List Sorts.Conj) (s : store.Store) (kids todo : store.TermId) (T : List Sorts.Conj)
    (m : Sorts.Conj → Option Bool) (hW : Wf s) (hF : FlagsB nm s U m)
    (hs : ∀ c ∈ a, Sub U c ∧ P c) (hk : Repr nm s.nodes.val kids.val (altPat (nm none) U a))
    (htd : Repr nm s.nodes.val todo.val (altPat (nm none) U T)) (hroom : Room s (4 * a.length + 1)) :
    sorts.enqueue s todo kids ⦃ r => ∃ m' T',
      RanB s r.2 (4 * a.length + 1) ∧ FlagsB nm r.2 U m' ∧
        Repr nm r.2.nodes.val r.1.val (altPat (nm none) U T') ∧ Enq P m m' T T' ∧
        ∀ c ∈ a, m' c ≠ none ⦄ :=
  enqueue_loop_spec hnm a s kids todo T m hW hF hs hk htd hroom

/-! ## The alternatives of a conjunction -/

/-- What stays the same while conjunctions are gone through: the sorts in the
store, a list with every name, and no name is the end of a list. -/
structure Ctx (nm : Option Nat → RwLog.Sym) (S : Sorts) (sp : Pat) (U : List Name) : Prop where
  inj : Function.Injective nm
  sorts : SortsAt (nm none) S sp
  names : ∀ n ∈ Sorts.names S, n ∈ U
  nz : ∀ n ∈ Sorts.names S, n ≠ nm none

theorem step_kid_names {S : Sorts} {n : Name} {f : Sym} {k : Nat} {ks : List (Option Name)}
    (h : Sorts.step S n f k = some ks) {m : Name} (hm : some m ∈ ks) : m ∈ Sorts.names S := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
  exact Sorts.kidC_subset_names (c := {n}) (f := f) (k := k) (i := i)
    (Sorts.mem_kidC.2 ⟨n, by simp, ks, h, hi⟩)

theorem RanB.inv {s s' : store.Store} {n : Nat} (h : RanB s s' n) (hI : Inv s) : Inv s' :=
  ⟨h.wf, by rw [h.stk]; exact hI.empty⟩

/-- The argument conjunctions of a root of a conjunction. -/
def altOf (S : Sorts) (d : Sorts.Conj) (f : Sym) (k : Nat) : List Sorts.Conj :=
  (List.range k).map (Sorts.kidC S d f k)

/-- The alternatives the cases of a list give a conjunction. -/
def caseAlts (S : Sorts) (d : Sorts.Conj) : List (Sym × List (Option Name)) → List Alt
  | [] => []
  | c :: cs =>
    (if Sorts.Accepts S d c.1 c.2.length then [(c.1, altOf S d c.1 c.2.length)] else []) ++ caseAlts S d cs

/-- The ticks going through the cases of a list may spend. -/
def casesWork (S : Sorts) (u : Nat) : List (Sym × List (Option Name)) → Nat
  | [] => 1
  | c :: cs => stepConjCost S u u c.2.length + 4 * c.2.length + 5 + casesWork S u cs

theorem altOf_sub {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U) (d : Sorts.Conj)
    (f : Sym) (k : Nat) : ∀ c ∈ altOf S d f k, Sub U c := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact fun n hn => hC.names n (Sorts.kidC_subset_names hn)

theorem expand_cases_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (hd : Sub U d) (hnr : ¬ Sorts.RestOK S d) :
    ∀ (cs : List (Sym × List (Option Name))) (s : store.Store)
      (cases decls names ci alts todo : store.TermId) (acc : List Alt)
      (T : List Sorts.Conj) (m : Sorts.Conj → Option Bool), Inv s → FlagsB nm s U m →
    (∀ c ∈ cs, (c.1, c.2.length) ∈ Sorts.caseKeys S d) →
    Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val ci.val (cpat (nm none) U d) →
    Repr nm s.nodes.val cases.val
      (encList (nm none) ((cs.map (caseEnt (nm none))).map (entPat (nm none)))) →
    Repr nm s.nodes.val alts.val (altsPat (nm none) U acc) →
    Repr nm s.nodes.val todo.val (altPat (nm none) U T) → Room s (casesWork S U.length cs) →
    sorts.expand_cases_loop cases s decls names ci alts todo ⦃ r => ∃ m' T',
      RanB s r.1 (casesWork S U.length cs) ∧ FlagsB nm r.1 U m' ∧
        Repr nm r.1.nodes.val r.2.1.val (altsPat (nm none) U ((caseAlts S d cs).reverse ++ acc)) ∧
        Repr nm r.1.nodes.val r.2.2.val (altPat (nm none) U T') ∧ Enq (Sorts.Kid S d) m m' T T' ∧
        ∀ a ∈ caseAlts S d cs, ∀ c ∈ a.2, m' c ≠ none ⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro s cases decls names ci alts todo acc T m hI hF hkeys hde hU hci hcs hal htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [casesWork] at hroom'
    unfold sorts.expand_cases_loop
    rw [loop]
    simp only [sorts.expand_cases_loop.body]
    step with uncons_repr s cases hI.toWf hcs (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    subst hu
    have hfin : ∃ m' T', RanB s s1 (casesWork S U.length []) ∧ FlagsB nm s1 U m' ∧
        Repr nm s1.nodes.val alts.val
          (altsPat (nm none) U ((caseAlts S d []).reverse ++ acc)) ∧
        Repr nm s1.nodes.val todo.val (altPat (nm none) U T') ∧ Enq (Sorts.Kid S d) m m' T T' ∧
        ∀ a ∈ caseAlts S d [], ∀ c ∈ a.2, m' c ≠ none :=
      ⟨m, T, hK.ran.ranB.mono (by simp [casesWork]), hF.mono hK.ran.ext (by rw [hK.tbl]),
        by rw [hK.nodes]; simpa [caseAlts] using hal, by rw [hK.nodes]; exact htd,
        Enq.refl _ m T, fun _ h => (by simp [caseAlts] at h)⟩
    step*
  | cons x cs ih =>
    intro s cases decls names ci alts todo acc T m hI hF hkeys hde hU hci hcs hal htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [casesWork] at hroom'
    have hW := hI.toWf
    unfold sorts.expand_cases_loop
    rw [loop]
    simp only [sorts.expand_cases_loop.body]
    step with uncons_repr s cases hW hcs (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu
    simp only at hK
    obtain ⟨cn, t, rfl, rcn, rt⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 cn hK.wf (by rw [hK.nodes]; exact rcn) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [entPat, caseEnt] at hu2
    simp only at hK2
    obtain ⟨f, ks, rfl, rf, rks⟩ := hu2
    rw [hK.nodes] at rf rks
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
    have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK.tbl]
    have R2 : Ran s s2 2 := hK.ran.trans hK2.ran
    have hI2 : Inv s2 := R2.ranB.inv hI
    have hlen : (x.2.map (kidPat (nm none))).length = x.2.length := List.length_map _
    step with step_conj_conj_spec hC.inj S hC.sorts (f := x.1) (ag := x.2.map (kidPat (nm none)))
      U d s2 decls names ci f ks hI2 (by rw [hn2]; exact hde) (by rw [hn2]; exact hU) hd
      (by rw [hn2]; exact hci) (by rw [hn2]; exact rf) (by rw [hn2]; exact rks)
      (fun n _ ks' hs m' hm' => hC.nz m' (step_kid_names hs hm'))
      (by rw [hlen]; unfold Room; omega) as ⟨r3, hI3, hx3, htb3, ht3, hres⟩
    obtain ⟨o2, s3⟩ := r3
    simp only at hI3 hx3 htb3 ht3 hres
    rw [hlen] at ht3 hres
    have R3 : RanB s s3 (stepConjCost S U.length U.length x.2.length + 2) :=
      ⟨hI3.toWf, R2.ext.trans hx3, by rw [hI3.empty, hI.empty], by have := R2.ticks; omega⟩
    have hF3 : FlagsB nm s3 U m := (hF.mono R2.ext (by rw [htb2])).mono hx3 htb3
    have hkeys' : ∀ c ∈ cs, (c.1, c.2.length) ∈ Sorts.caseKeys S d :=
      fun c hc => hkeys c (List.mem_cons_of_mem _ hc)
    -- the rest of the cases
    have rest : ∀ (s' : store.Store) (alts' todo' : store.TermId) (acc' : List Alt)
        (m₁ : Sorts.Conj → Option Bool) (T₁ : List Sorts.Conj),
        RanB s s' (stepConjCost S U.length U.length x.2.length + 4 * x.2.length + 5) →
        Inv s' → FlagsB nm s' U m₁ →
        Repr nm s'.nodes.val alts'.val (altsPat (nm none) U acc') →
        Repr nm s'.nodes.val todo'.val (altPat (nm none) U T₁) → Enq (Sorts.Kid S d) m m₁ T T₁ →
        ((caseAlts S d cs).reverse ++ acc' = (caseAlts S d (x :: cs)).reverse ++ acc) →
        (∀ a ∈ caseAlts S d (x :: cs), a ∈ caseAlts S d cs ∨ ∀ c ∈ a.2, m₁ c ≠ none) →
        loop (fun x => match x with
          | (cases1, s1, alts1, todo1) =>
            sorts.expand_cases_loop.body decls names ci cases1 s1 alts1 todo1)
          (t, s', alts', todo') ⦃ r => ∃ m' T',
          RanB s r.1 (casesWork S U.length (x :: cs)) ∧ FlagsB nm r.1 U m' ∧
            Repr nm r.1.nodes.val r.2.1.val
              (altsPat (nm none) U ((caseAlts S d (x :: cs)).reverse ++ acc)) ∧
            Repr nm r.1.nodes.val r.2.2.val (altPat (nm none) U T') ∧
            Enq (Sorts.Kid S d) m m' T T' ∧
            ∀ a ∈ caseAlts S d (x :: cs), ∀ c ∈ a.2, m' c ≠ none ⦄ := by
      intro s' alts' todo' acc' m₁ T₁ R0 hI' hF' hal' htd' hE hacc hfl
      have := R0.ticks
      have IH := ih s' t decls names ci alts' todo' acc' T₁ m₁ hI' hF' hkeys' (R0.ext.repr hde)
        (R0.ext.repr hU) (R0.ext.repr hci) (R0.ext.repr rt) hal' htd' (by unfold Room; omega)
      unfold sorts.expand_cases_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨m', T', hR, hFm, hra, hrt, hE', hall⟩
      refine ⟨m', T', (R0.trans hR).mono (by simp only [casesWork]; omega), hFm,
        by rw [← hacc]; exact hra, hrt, hE.trans hE', ?_⟩
      intro a ha c hc
      rcases hfl a ha with h | h
      · exact hall a h c hc
      · exact hE'.flagged (h c hc)
    by_cases hacc : Sorts.Accepts S d x.1 x.2.length
    · simp only [hacc, ↓reduceIte] at hres
      obtain ⟨r, kids, rfl, hkl, rkids, hk⟩ := hres
      have hkids : kids = (altOf S d x.1 x.2.length).map (cpat (nm none) U) := by
        apply List.ext_getElem
        · simp [altOf, hkl]
        · intro i h₁ h₂
          obtain ⟨k', rk', ck'⟩ := hk i h₁
          simp only [altOf, List.getElem_map, List.getElem_range]
          exact rk'.unique ck'
      simp only [uncurry]
      have rkids' : Repr nm s3.nodes.val r.val
          (altPat (nm none) U (altOf S d x.1 x.2.length)) := by
        have := rkids
        rw [hkids] at this
        exact this
      step with alloc_w s3 (.App f r) hI3.toWf ⟨(R3.ext.repr rf).lt, rkids.lt⟩
        (by unfold Room; omega) as ⟨r4', hW4', ht4', htb4', hx4', hid', hst4'⟩
      obtain ⟨alt, s4'⟩ := r4'
      simp only at hW4' ht4' htb4' hx4' hid' hst4' ⊢
      have R4' : RanB s s4' (stepConjCost S U.length U.length x.2.length + 3) :=
        ⟨hW4', R3.ext.trans hx4', by rw [hst4', R3.stk], by have := R3.ticks; omega⟩
      have ralt : Repr nm s4'.nodes.val alt.val
          (kaltPat (nm none) U (x.1, altOf S d x.1 x.2.length)) :=
        .app hid' (R4'.ext.repr rf) (hx4'.repr rkids')
      step with alloc_w s4' (.App alt alts) hW4' ⟨ralt.lt, (R4'.ext.repr hal).lt⟩
        (by unfold Room; omega) as ⟨r4, hW4, ht4, htb4, hx40, hid, hst4⟩
      obtain ⟨alts1, s4⟩ := r4
      simp only at hW4 ht4 htb4 hx40 hid hst4 ⊢
      have hx4 : Extends s3 s4 := hx4'.trans hx40
      have htb4 : tbl s4 = tbl s3 := by rw [htb4, htb4']
      have R4 : RanB s s4 (stepConjCost S U.length U.length x.2.length + 4) :=
        ⟨hW4, R3.ext.trans hx4, by rw [hst4, hst4', R3.stk], by have := R3.ticks; omega⟩
      have ral1 : Repr nm s4.nodes.val alts1.val
          (altsPat (nm none) U ((x.1, altOf S d x.1 x.2.length) :: acc)) := by
        simp only [altsPat, List.map_cons, encList]
        exact .app hid (hx40.repr ralt) (R4.ext.repr hal)
      have hkid : ∀ c ∈ altOf S d x.1 x.2.length, Sub U c ∧ Sorts.Kid S d c := by
        intro c hc
        refine ⟨altOf_sub hC d _ _ c hc, ?_⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
        exact ⟨hnr, (x.1, x.2.length), hkeys x List.mem_cons_self, hacc, i, List.mem_range.1 hi, rfl⟩
      have hlen2 : (altOf S d x.1 x.2.length).length = x.2.length := by simp [altOf]
      step with enqueue_spec hC.inj (altOf S d x.1 x.2.length) s4 r todo T m hW4
        (hF3.mono hx4 (by rw [htb4])) hkid
        (by have := hx4.repr rkids; rw [hkids] at this; exact this) (R4.ext.repr htd)
        (by rw [hlen2]; unfold Room; omega) as ⟨r5, m₁, T₁, hR5, hF5, rtd5, hE5, hall5⟩
      obtain ⟨todo1, s5⟩ := r5
      simp only at hR5 hF5 rtd5
      rw [hlen2] at hR5
      have R5 := (R4.trans hR5).mono
        (m := stepConjCost S U.length U.length x.2.length + 4 * x.2.length + 5) (by omega)
      simp only [uncurry, bind_ok]
      exact rest s5 alts1 todo1 _ m₁ T₁ R5 (R5.inv hI) hF5 (hR5.ext.repr ral1) rtd5 hE5
        (by simp [caseAlts, hacc])
        (fun a ha => by
          simp only [caseAlts, hacc, ↓reduceIte, List.singleton_append, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact Or.inr hall5
          · exact Or.inl ha)
    · simp only [hacc, ↓reduceIte] at hres
      subst hres
      simp only [uncurry, bind_ok]
      exact rest s3 alts todo acc m T (R3.mono (by omega)) hI3 hF3 (R3.ext.repr hal)
        (R3.ext.repr htd) (Enq.refl _ m T) (by simp [caseAlts, hacc])
        (fun a ha => by
          simp only [caseAlts, hacc, ↓reduceIte, List.nil_append] at ha
          exact Or.inl ha)

theorem expand_cases_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (hd : Sub U d) (hnr : ¬ Sorts.RestOK S d)
    (cs : List (Sym × List (Option Name))) (s : store.Store)
    (cases decls names ci alts todo : store.TermId) (acc : List Alt)
    (T : List Sorts.Conj) (m : Sorts.Conj → Option Bool) (hI : Inv s) (hF : FlagsB nm s U m)
    (hkeys : ∀ c ∈ cs, (c.1, c.2.length) ∈ Sorts.caseKeys S d)
    (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (hcs : Repr nm s.nodes.val cases.val
      (encList (nm none) ((cs.map (caseEnt (nm none))).map (entPat (nm none)))))
    (hal : Repr nm s.nodes.val alts.val (altsPat (nm none) U acc))
    (htd : Repr nm s.nodes.val todo.val (altPat (nm none) U T))
    (hroom : Room s (casesWork S U.length cs)) :
    sorts.expand_cases s decls names ci cases alts todo ⦃ r => ∃ m' T',
      RanB s r.2 (casesWork S U.length cs) ∧ FlagsB nm r.2 U m' ∧
        Repr nm r.2.nodes.val r.1.1.val (altsPat (nm none) U ((caseAlts S d cs).reverse ++ acc)) ∧
        Repr nm r.2.nodes.val r.1.2.val (altPat (nm none) U T') ∧ Enq (Sorts.Kid S d) m m' T T' ∧
        ∀ a ∈ caseAlts S d cs, ∀ c ∈ a.2, m' c ≠ none ⦄ := by
  unfold sorts.expand_cases
  step with expand_cases_loop_spec hC d hd hnr cs s cases decls names ci alts todo acc T m hI hF
    hkeys hde hU hci hcs hal htd hroom as ⟨s1, alts1, todo1, m', T', h1, h2, h3, h4, h5, h6⟩
  exact ⟨m', T', h1, h2, h3, h4, h5, h6⟩

/-- The alternatives the sorts of a list give a conjunction. -/
def nameAlts (S : Sorts) (d : Sorts.Conj) : List Name → List Alt
  | [] => []
  | n :: ns =>
    (match S.lookup n with
      | some dd => caseAlts S d dd.cases
      | none => []) ++ nameAlts S d ns

/-- The ticks going through the cases of every declaration may spend. -/
def sortsWork (S : Sorts) (u : Nat) : Nat := (S.map fun p => casesWork S u p.2.cases).sum

theorem casesWork_le {S : Sorts} {n : Name} {dd : SortDef} (h : S.lookup n = some dd) (u : Nat) :
    casesWork S u dd.cases ≤ sortsWork S u := by
  have hm := Sorts.mem_of_lookup h
  exact List.le_sum_of_mem (List.mem_map.2 ⟨(n, dd), hm, rfl⟩)

theorem expand_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (hd : Sub U d) (hnr : ¬ Sorts.RestOK S d) :
    ∀ (ns : List Name) (s : store.Store) (nsi decls names ci alts todo : store.TermId)
      (acc : List Alt) (T : List Sorts.Conj) (m : Sorts.Conj → Option Bool),
    Inv s → FlagsB nm s U m → (∀ n ∈ ns, n ∈ d) →
    Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val ci.val (cpat (nm none) U d) →
    Repr nm s.nodes.val nsi.val (namesPat (nm none) ns) →
    Repr nm s.nodes.val alts.val (altsPat (nm none) U acc) →
    Repr nm s.nodes.val todo.val (altPat (nm none) U T) →
    Room s (ns.length * (3 * S.length + 3 + sortsWork S U.length) + 1) →
    sorts.expand_loop nsi s decls names ci alts todo ⦃ r => ∃ m' T',
      RanB s r.1 (ns.length * (3 * S.length + 3 + sortsWork S U.length) + 1) ∧
        FlagsB nm r.1 U m' ∧
        Repr nm r.1.nodes.val r.2.1.val (altsPat (nm none) U ((nameAlts S d ns).reverse ++ acc)) ∧
        Repr nm r.1.nodes.val r.2.2.val (altPat (nm none) U T') ∧ Enq (Sorts.Kid S d) m m' T T' ∧
        ∀ a ∈ nameAlts S d ns, ∀ c ∈ a.2, m' c ≠ none ⦄ := by
  intro ns
  induction ns with
  | nil =>
    intro s nsi decls names ci alts todo acc T m hI hF hmem hde hU hci hns hal htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    unfold sorts.expand_loop
    rw [loop]
    simp only [sorts.expand_loop.body]
    step with uncons_repr s nsi hI.toWf hns (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    subst hu
    have hfin : ∃ m' T', RanB s s1
          (([] : List Name).length * (3 * S.length + 3 + sortsWork S U.length) + 1) ∧
        FlagsB nm s1 U m' ∧
        Repr nm s1.nodes.val alts.val (altsPat (nm none) U ((nameAlts S d []).reverse ++ acc)) ∧
        Repr nm s1.nodes.val todo.val (altPat (nm none) U T') ∧ Enq (Sorts.Kid S d) m m' T T' ∧
        ∀ a ∈ nameAlts S d [], ∀ c ∈ a.2, m' c ≠ none :=
      ⟨m, T, hK.ran.ranB.mono (by simp), hF.mono hK.ran.ext (by rw [hK.tbl]),
        by rw [hK.nodes]; simpa [nameAlts] using hal, by rw [hK.nodes]; exact htd,
        Enq.refl _ m T, fun _ h => (by simp [nameAlts] at h)⟩
    step*
  | cons x ns ih =>
    intro s nsi decls names ci alts todo acc T m hI hF hmem hde hU hci hns hal htd hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hroom'
    have hW := hI.toWf
    unfold sorts.expand_loop
    rw [loop]
    simp only [sorts.expand_loop.body]
    step with uncons_repr s nsi hW hns (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [namesPat] at hu
    simp only at hK
    obtain ⟨n, t, rfl, rn, rt⟩ := hu
    have ht1 := hK.ticks
    have hx1 := hK.ran.ext
    step with lookup_spec hC.inj S hC.sorts s1 decls n hK.wf (hx1.repr hde) (hx1.repr rn)
      (by unfold Room; omega) as ⟨r1, hR2, hl⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hR2 hl
    have ht2 := hR2.ticks
    have R2 : Ran s s2 (3 * S.length + 3) := (hK.ran.trans hR2).mono (by omega)
    have hF2 : FlagsB nm s2 U m := hF.mono R2.ext (by rw [R2.tbl])
    have hmem' : ∀ n ∈ ns, n ∈ d := fun n hn => hmem n (List.mem_cons_of_mem _ hn)
    have rest : ∀ (s' : store.Store) (alts' todo' : store.TermId) (acc' : List Alt)
        (m₁ : Sorts.Conj → Option Bool) (T₁ : List Sorts.Conj),
        RanB s s' (3 * S.length + 3 + sortsWork S U.length) → FlagsB nm s' U m₁ →
        Repr nm s'.nodes.val alts'.val (altsPat (nm none) U acc') →
        Repr nm s'.nodes.val todo'.val (altPat (nm none) U T₁) → Enq (Sorts.Kid S d) m m₁ T T₁ →
        ((nameAlts S d ns).reverse ++ acc' = (nameAlts S d (x :: ns)).reverse ++ acc) →
        (∀ a ∈ nameAlts S d (x :: ns), a ∈ nameAlts S d ns ∨ ∀ c ∈ a.2, m₁ c ≠ none) →
        loop (fun x => match x with
          | (ns1, s1, alts1, todo1) => sorts.expand_loop.body decls names ci ns1 s1 alts1 todo1)
          (t, s', alts', todo') ⦃ r => ∃ m' T',
          RanB s r.1 ((x :: ns).length * (3 * S.length + 3 + sortsWork S U.length) + 1) ∧
            FlagsB nm r.1 U m' ∧
            Repr nm r.1.nodes.val r.2.1.val
              (altsPat (nm none) U ((nameAlts S d (x :: ns)).reverse ++ acc)) ∧
            Repr nm r.1.nodes.val r.2.2.val (altPat (nm none) U T') ∧
            Enq (Sorts.Kid S d) m m' T T' ∧
            ∀ a ∈ nameAlts S d (x :: ns), ∀ c ∈ a.2, m' c ≠ none ⦄ := by
      intro s' alts' todo' acc' m₁ T₁ R0 hF' hal' htd' hE hacc hfl
      have := R0.ticks
      have IH := ih s' t decls names ci alts' todo' acc' T₁ m₁ (R0.inv hI) hF' hmem'
        (R0.ext.repr hde) (R0.ext.repr hU) (R0.ext.repr hci) (R0.ext.repr rt) hal' htd'
        (by unfold Room; omega)
      unfold sorts.expand_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨m', T', hR, hFm, hra, hrt, hE', hall⟩
      refine ⟨m', T', (R0.trans hR).mono
        (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega), hFm,
        by rw [← hacc]; exact hra, hrt, hE.trans hE', ?_⟩
      intro a ha c hc
      rcases hfl a ha with h | h
      · exact hall a h c hc
      · exact hE'.flagged (h c hc)
    cases hlk : S.lookup x with
    | none =>
      rw [hlk] at hl
      subst hl
      simp only [uncurry, bind_ok]
      exact rest s2 alts todo acc m T (R2.ranB.mono (by omega)) hF2 (R2.ext.repr hal)
        (R2.ext.repr htd) (Enq.refl _ m T) (by simp [nameAlts, hlk])
        (fun a ha => by
          simp only [nameAlts, hlk, List.nil_append] at ha
          exact Or.inl ha)
    | some dd =>
      rw [hlk] at hl
      obtain ⟨cc, r, rp, rfl, rcc, -, -⟩ := hl
      have hcw := casesWork_le hlk U.length
      have hkeys : ∀ c ∈ dd.cases, (c.1, c.2.length) ∈ Sorts.caseKeys S d := by
        intro c hc
        simp only [Sorts.caseKeys, Finset.mem_biUnion]
        exact ⟨x, hmem x List.mem_cons_self, by
          simp only [hlk, List.mem_toFinset, List.mem_map]; exact ⟨c, hc, rfl⟩⟩
      simp only [uncurry]
      step with expand_cases_spec hC d hd hnr dd.cases s2 cc decls names ci alts todo acc T m
        (R2.ranB.inv hI) hF2 hkeys (R2.ext.repr hde) (R2.ext.repr hU) (R2.ext.repr hci)
        (hR2.ext.repr rcc) (R2.ext.repr hal) (R2.ext.repr htd) (by unfold Room; omega)
        as ⟨r3, m₁, T₁, hR3, hF3, ral3, rtd3, hE3, hall3⟩
      obtain ⟨⟨a3, td3⟩, s3⟩ := r3
      simp only at hR3 hF3 ral3 rtd3
      have := R2.ticks
      have := hR3.ticks
      simp only [uncurry, bind_ok]
      exact rest s3 a3 td3 _ m₁ T₁ ((R2.ranB.trans hR3).mono (by omega)) hF3 ral3 rtd3 hE3
        (by simp [nameAlts, hlk])
        (fun a ha => by
          simp only [nameAlts, hlk, List.mem_append] at ha
          rcases ha with ha | ha
          · exact Or.inr (hall3 a ha)
          · exact Or.inl ha)

theorem mem_caseAlts {S : Sorts} {d : Sorts.Conj} {a : Alt} :
    ∀ {cs : List (Sym × List (Option Name))}, a ∈ caseAlts S d cs ↔
      ∃ c ∈ cs, Sorts.Accepts S d c.1 c.2.length ∧ a = (c.1, altOf S d c.1 c.2.length)
  | [] => by simp [caseAlts]
  | x :: cs => by
    simp only [caseAlts, List.mem_append, mem_caseAlts (cs := cs), List.mem_cons, exists_eq_or_imp]
    by_cases h : Sorts.Accepts S d x.1 x.2.length <;> simp [h]

theorem mem_nameAlts {S : Sorts} {d : Sorts.Conj} {a : Alt} :
    ∀ {ns : List Name}, a ∈ nameAlts S d ns ↔
      ∃ n ∈ ns, ∃ dd, S.lookup n = some dd ∧ a ∈ caseAlts S d dd.cases
  | [] => by simp [nameAlts]
  | x :: ns => by
    simp only [nameAlts, List.mem_append, mem_nameAlts (ns := ns), List.mem_cons, exists_eq_or_imp]
    cases h : S.lookup x <;> simp

/-- The alternatives of a conjunction: for each root one of its sorts has a
case for and all accept, the conjunctions of the arguments. -/
noncomputable def dAlts (S : Sorts) (U : List Name) (d : Sorts.Conj) : List Alt :=
  (nameAlts S d (conjList U (· ∈ d))).reverse

theorem mem_dAlts {S : Sorts} {U : List Name} {d : Sorts.Conj} (hd : Sub U d)
    {a : Alt} : a ∈ dAlts S U d ↔
      ∃ key ∈ Sorts.caseKeys S d, Sorts.Accepts S d key.1 key.2 ∧ a = (key.1, altOf S d key.1 key.2) := by
  simp only [dAlts, List.mem_reverse, mem_nameAlts, mem_caseAlts, mem_conjList, Sorts.caseKeys,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨n, ⟨-, hn⟩, dd, hl, c, hc, hacc, rfl⟩
    have hk : (c.1, c.2.length) ∈ (match S.lookup n with
        | some d => (d.cases.map fun cs : Sym × List (Option Name) => (cs.1, cs.2.length)).toFinset
        | none => (∅ : Finset (Sym × Nat))) := by
      simp only [hl, List.mem_toFinset, List.mem_map]
      exact ⟨c, hc, rfl⟩
    exact ⟨(c.1, c.2.length), ⟨n, hn, hk⟩, hacc, rfl⟩
  · rintro ⟨key, ⟨n, hn, hk⟩, hacc, rfl⟩
    cases hl : S.lookup n with
    | none => simp [hl] at hk
    | some dd =>
      simp only [hl, List.mem_toFinset, List.mem_map] at hk
      obtain ⟨c, hc, rfl⟩ := hk
      exact ⟨n, ⟨hd n hn, hn⟩, dd, hl, c, hc, hacc, rfl⟩

/-- The ticks finding the alternatives of a conjunction may spend. -/
def expandCost (S : Sorts) (u : Nat) : Nat := u * (3 * S.length + 3 + sortsWork S u) + 2

theorem expand_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (d : Sorts.Conj) (hd : Sub U d) (hnr : ¬ Sorts.RestOK S d) (s : store.Store)
    (decls names ci todo : store.TermId) (T : List Sorts.Conj) (m : Sorts.Conj → Option Bool)
    (hI : Inv s) (hF : FlagsB nm s U m) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U d))
    (htd : Repr nm s.nodes.val todo.val (altPat (nm none) U T))
    (hroom : Room s (expandCost S U.length)) :
    sorts.expand s decls names ci todo ⦃ r => ∃ m' T',
      RanB s r.2 (expandCost S U.length) ∧ FlagsB nm r.2 U m' ∧
        Repr nm r.2.nodes.val r.1.1.val (altsPat (nm none) U (dAlts S U d)) ∧
        Repr nm r.2.nodes.val r.1.2.val (altPat (nm none) U T') ∧ Enq (Sorts.Kid S d) m m' T T' ∧
        ∀ a ∈ dAlts S U d, ∀ c ∈ a.2, m' c ≠ none ⦄ := by
  unfold sorts.expand
  have hroom' := hroom
  unfold Room at hroom'
  simp only [expandCost] at hroom'
  have hlen := length_conjList_le U (· ∈ d)
  have hmul := Nat.mul_le_mul_right (3 * S.length + 3 + sortsWork S U.length) hlen
  step with alloc_w s .Nil hI.toWf trivial (by unfold Room; omega)
    as ⟨alts, s1, hW1, ht1, htb1, hx1, hid, hst1⟩
  have R1 : RanB s s1 1 := ⟨hW1, hx1, hst1, by omega⟩
  step with expand_loop_spec hC d hd hnr (conjList U (· ∈ d)) s1 ci decls names ci alts todo [] T m
    (R1.inv hI) (hF.mono hx1 (by rw [htb1])) (fun n hn => (mem_conjList.1 hn).2) (hx1.repr hde)
    (hx1.repr hU) (hx1.repr hci) (hx1.repr hci) (.nil hid) (hx1.repr htd)
    (by unfold Room; omega) as ⟨s2, alts1, todo1, m', T', hR, hFm, hra, hrt, hE, hall⟩
  refine ⟨m', T', (R1.trans hR).mono (by simp only [expandCost]; omega), hFm,
    by simpa [dAlts] using hra, hrt, hE, ?_⟩
  intro a ha
  exact hall a (by simpa [dAlts] using ha)

/-! ## The conjunctions a conjunction reaches -/

/-- What holds while the conjunctions `c₀` reaches are gone through: `T` are
still to do, `Dn` are done, and `G` holds those done that have a sort without
a rest, with their alternatives. -/
structure WalkInv (S : Sorts) (U : List Name) (c₀ : Sorts.Conj) (T : List Sorts.Conj)
    (G : List Entry) (Dn : List Sorts.Conj) (m : Sorts.Conj → Option Bool) : Prop where
  nodup : (T ++ Dn).Nodup
  dom : ∀ c, m c ≠ none ↔ c ∈ T ∨ c ∈ Dn
  root : m c₀ ≠ none
  reach : ∀ c, m c ≠ none → Sorts.Reach S c₀ c
  sound : Sound S m
  done : ∀ c ∈ Dn, (Sorts.RestOK S c ∧ m c = some true) ∨
    (¬ Sorts.RestOK S c ∧ (c, dAlts S U c) ∈ G ∧ ∀ a ∈ dAlts S U c, ∀ k ∈ a.2, m k ≠ none)
  graph : ∀ e ∈ G, e.1 ∈ Dn ∧ e.2 = dAlts S U e.1
  glen : G.length ≤ Dn.length
  norest : ∀ e ∈ G, ¬ Sorts.RestOK S e.1

theorem WalkInv.rest {S : Sorts} {U : List Name} {c₀ d : Sorts.Conj} {T : List Sorts.Conj}
    {G : List Entry} {Dn : List Sorts.Conj} {m : Sorts.Conj → Option Bool}
    (h : WalkInv S U c₀ (d :: T) G Dn m) (hr : Sorts.RestOK S d) :
    WalkInv S U c₀ T G (d :: Dn) (Function.update m d (some true)) := by
  have hmd : m d ≠ none := (h.dom d).2 (Or.inl List.mem_cons_self)
  have hne : ∀ c, Function.update m d (some true) c ≠ none ↔ m c ≠ none := by
    intro c
    by_cases hc : c = d
    · subst hc; simp [hmd]
    · rw [Function.update_of_ne hc]
  have hnd : (T ++ d :: Dn).Nodup :=
    (List.perm_middle.nodup_iff).2 (by simpa using h.nodup)
  have hdn : d ∉ Dn := by
    have := h.nodup
    simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at this
    exact this.1.2
  refine ⟨hnd, fun c => ?_, (hne c₀).2 h.root, fun c hc => h.reach c ((hne c).1 hc), ?_, ?_, ?_,
    by simp only [List.length_cons]; have := h.glen; omega, h.norest⟩
  · rw [hne, h.dom]
    simp only [List.mem_cons]
    tauto
  · intro c hc
    by_cases hcd : c = d
    · subst hcd; exact Sorts.restOK_memC hr
    · rw [Function.update_of_ne hcd] at hc; exact h.sound c hc
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Or.inl ⟨hr, by simp⟩
    · have hcd : c ≠ d := fun e => hdn (e ▸ hc)
      rcases h.done c hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩
      · exact Or.inl ⟨h₁, by rw [Function.update_of_ne hcd]; exact h₂⟩
      · exact Or.inr ⟨h₁, h₂, fun a ha k hk => (hne k).2 (h₃ a ha k hk)⟩
  · intro e he
    exact ⟨List.mem_cons_of_mem _ (h.graph e he).1, (h.graph e he).2⟩

theorem WalkInv.expand {S : Sorts} {U : List Name} {c₀ d : Sorts.Conj} {T T' : List Sorts.Conj}
    {G : List Entry} {Dn : List Sorts.Conj} {m m' : Sorts.Conj → Option Bool}
    (h : WalkInv S U c₀ (d :: T) G Dn m) (hr : ¬ Sorts.RestOK S d)
    (hE : Enq (Sorts.Kid S d) m m' T T') (hall : ∀ a ∈ dAlts S U d, ∀ c ∈ a.2, m' c ≠ none) :
    WalkInv S U c₀ T' ((d, dAlts S U d) :: G) (d :: Dn) m' := by
  have hkeep : ∀ c, m c ≠ none → m' c = m c := fun c hc => hE.keeps hc
  obtain ⟨new, rfl, nd, hnew, hm'⟩ := hE
  have hmd : m d ≠ none := (h.dom d).2 (Or.inl List.mem_cons_self)
  have hne : ∀ c, m' c ≠ none ↔ c ∈ new ∨ m c ≠ none := by
    intro c
    rw [hm']
    by_cases hc : c ∈ new <;> simp [hc]
  have hold := h.nodup
  simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at hold
  have hnd : ((new ++ T) ++ d :: Dn).Nodup := by
    rw [List.append_assoc]
    refine List.nodup_append.2 ⟨nd, (List.perm_middle.nodup_iff).2 (by simpa using h.nodup), ?_⟩
    intro x hx y hy e
    subst e
    have h0 := (hnew x hx).1
    have : m x ≠ none := (h.dom x).2 (by
      simp only [List.mem_append, List.mem_cons] at hy ⊢
      tauto)
    exact this h0
  refine ⟨hnd, fun c => ?_, (hne c₀).2 (Or.inr h.root), ?_, ?_, ?_, ?_,
    by simp only [List.length_cons]; have := h.glen; omega, fun e he => ?_⟩
  rotate_right
  · rcases List.mem_cons.1 he with rfl | he
    · exact hr
    · exact h.norest e he
  · rw [hne, h.dom]
    simp only [List.mem_append, List.mem_cons]
    tauto
  · intro c hc
    rcases (hne c).1 hc with hc | hc
    · exact (h.reach d hmd).step (hnew c hc).2
    · exact h.reach c hc
  · intro c hc
    rw [hm'] at hc
    by_cases hcn : c ∈ new
    · simp [hcn] at hc
    · simp only [hcn, ↓reduceIte] at hc; exact h.sound c hc
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Or.inr ⟨hr, List.mem_cons_self, hall⟩
    · rcases h.done c hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩
      · exact Or.inl ⟨h₁, by rw [hkeep c (by rw [h₂]; simp)]; exact h₂⟩
      · exact Or.inr ⟨h₁, List.mem_cons_of_mem _ h₂,
          fun a ha k hk => (hne k).2 (Or.inr (h₃ a ha k hk))⟩
  · intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨List.mem_cons_self, rfl⟩
    · exact ⟨List.mem_cons_of_mem _ (h.graph e he).1, (h.graph e he).2⟩

theorem WalkInv.lt_card {S : Sorts} {U : List Name} {c₀ d : Sorts.Conj} {T : List Sorts.Conj}
    {G : List Entry} {Dn : List Sorts.Conj} {m : Sorts.Conj → Option Bool}
    (h : WalkInv S U c₀ (d :: T) G Dn m) : Dn.length < (Sorts.reachSet S c₀).card := by
  have hnd : (d :: Dn).Nodup := by
    have := h.nodup
    simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at this
    exact List.nodup_cons.2 ⟨this.1.2, (List.nodup_append.1 this.2).2.1⟩
  have hsub : (d :: Dn).toFinset ⊆ Sorts.reachSet S c₀ := by
    intro c hc
    rw [List.mem_toFinset] at hc
    refine Sorts.mem_reachSet.2 (h.reach c ((h.dom c).2 ?_))
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Or.inl List.mem_cons_self
    · exact Or.inr hc
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  simpa using this

theorem WalkInv.len_le {S : Sorts} {U : List Name} {c₀ : Sorts.Conj} {T : List Sorts.Conj}
    {G : List Entry} {Dn : List Sorts.Conj} {m : Sorts.Conj → Option Bool}
    (h : WalkInv S U c₀ T G Dn m) : Dn.length ≤ (Sorts.reachSet S c₀).card := by
  have hnd : Dn.Nodup := (List.nodup_append.1 h.nodup).2.1
  have hsub : Dn.toFinset ⊆ Sorts.reachSet S c₀ := by
    intro c hc
    rw [List.mem_toFinset] at hc
    exact Sorts.mem_reachSet.2 (h.reach c ((h.dom c).2 (Or.inr hc)))
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd] at this

theorem WalkInv.entryOK {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    {c₀ : Sorts.Conj} {T : List Sorts.Conj} {G : List Entry} {Dn : List Sorts.Conj}
    {m : Sorts.Conj → Option Bool} (h : WalkInv S U c₀ T G Dn m) (hsub : ∀ c ∈ Dn, Sub U c) :
    ∀ e ∈ G, EntryOK S U e := by
  intro e he
  obtain ⟨hd, hal⟩ := h.graph e he
  refine ⟨hsub _ hd, fun a ha => ?_⟩
  rw [hal, mem_dAlts (hsub _ hd)] at ha
  obtain ⟨key, hkey, hacc, rfl⟩ := ha
  refine ⟨altOf_sub hC _ _ _, fun hm => ?_⟩
  exact Sorts.memC_of_grows (Or.inr ⟨key, hkey, hacc, fun i hi =>
    hm _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)⟩)

/-- When nothing is still to do, every conjunction reached is done. -/
theorem WalkInv.reached {S : Sorts} {U : List Name} {c₀ : Sorts.Conj} {G : List Entry}
    {Dn : List Sorts.Conj} {m : Sorts.Conj → Option Bool} (h : WalkInv S U c₀ [] G Dn m)
    (hsub : ∀ c ∈ Dn, Sub U c) {c : Sorts.Conj} (hc : Sorts.Reach S c₀ c) : c ∈ Dn := by
  have hin : ∀ c, m c ≠ none → c ∈ Dn := fun c hc => by
    rcases (h.dom c).1 hc with h | h
    · cases h
    · exact h
  induction hc with
  | refl => exact hin c₀ h.root
  | @step d e _ hk ih =>
    obtain ⟨hnr, key, hkey, hacc, i, hi, rfl⟩ := hk
    rcases h.done d ih with ⟨h₁, -⟩ | ⟨-, -, h₃⟩
    · exact absurd h₁ hnr
    · exact hin _ (h₃ (key.1, altOf S d key.1 key.2)
        ((mem_dAlts (hsub d ih)).2 ⟨key, hkey, hacc, rfl⟩) _
        (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))

/-- When no round changes a flag, the flag of the conjunction says whether it
has a member. -/
theorem WalkInv.live_iff {S : Sorts} {U : List Name} {c₀ : Sorts.Conj} {G : List Entry}
    {Dn : List Sorts.Conj} {m m' : Sorts.Conj → Option Bool} (h : WalkInv S U c₀ [] G Dn m)
    (hsub : ∀ c ∈ Dn, Sub U c) (hLe : Le m m') (hS : Sound S m') (hst : Stable m' G)
    {c : Sorts.Conj} (hc₀ : Sorts.Reach S c₀ c) : m' c = some true ↔ c ∈ Sorts.live S := by
  have hall : ∀ c, Sorts.Reach S c₀ c → c ∈ Dn := fun c hc => h.reached hsub hc
  rw [Sorts.mem_live_iff]
  refine ⟨hS c, Sorts.live_of_stable (R := Sorts.Reach S c₀) (L := fun c => m' c = some true)
    (fun _ _ h k => h.step k) ?_ c hc₀⟩
  intro c hc hg
  have hcd := hall c hc
  rcases h.done c hcd with ⟨-, h₂⟩ | ⟨hnr, hG, -⟩
  · rcases hLe c with e | ⟨-, e⟩
    · rw [e]; exact h₂
    · exact e
  · rcases hg with hr | ⟨key, hkey, hacc, hk⟩
    · exact absurd hr hnr
    · by_contra hne
      have hmc : m c ≠ none := (h.dom c).2 (Or.inr hcd)
      have hfalse : m' c = some false := by
        rcases hLe c with e | ⟨-, e⟩
        · rw [e] at hne ⊢
          cases hv : m c with
          | none => exact absurd hv hmc
          | some b => cases b with
            | false => rfl
            | true => exact absurd hv hne
        · exact absurd e hne
      refine hst _ hG hfalse ⟨(key.1, altOf S c key.1 key.2),
        (mem_dAlts (hsub c hcd)).2 ⟨key, hkey, hacc, rfl⟩, fun k hk' => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk'
      exact hk i (List.mem_range.1 hi)

/-- The ticks going through one conjunction may spend. -/
def nodeCost (S : Sorts) (u : Nat) : Nat := u * (3 * S.length + 4) + expandCost S u + 4

theorem reach_loop_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (c₀ : Sorts.Conj) (decls names : store.TermId) :
    ∀ (n : Nat) (s : store.Store) (todo graph : store.TermId) (T : List Sorts.Conj)
      (G : List Entry) (Dn : List Sorts.Conj) (m : Sorts.Conj → Option Bool),
    (Sorts.reachSet S c₀).card ≤ Dn.length + n → Inv s → FlagsB nm s U m →
    WalkInv S U c₀ T G Dn m → Repr nm s.nodes.val decls.val sp →
    Repr nm s.nodes.val names.val (namesPat (nm none) U) →
    Repr nm s.nodes.val todo.val (altPat (nm none) U T) →
    Repr nm s.nodes.val graph.val (graphPat (nm none) U G) →
    Room s (n * nodeCost S U.length + 1) →
    sorts.reach_loop todo s decls names graph ⦃ r => ∃ m' G' Dn',
      RanB s r.2 (n * nodeCost S U.length + 1) ∧ FlagsB nm r.2 U m' ∧
        Repr nm r.2.nodes.val r.1.val (graphPat (nm none) U G') ∧ WalkInv S U c₀ [] G' Dn' m' ⦄ := by
  intro n
  induction n with
  | zero =>
    intro s todo graph T G Dn m hcard hI hF hInv hde hU htd hg hroom
    cases T with
    | cons d T => have := hInv.lt_card; omega
    | nil =>
      have hroom' := hroom
      unfold Room at hroom'
      unfold sorts.reach_loop
      rw [loop]
      simp only [sorts.reach_loop.body]
      step with uncons_repr s todo hI.toWf htd (by unfold Room; omega) as ⟨r0, hK, hu⟩
      obtain ⟨o, s1⟩ := r0
      simp only [altPat] at hu
      simp only at hK
      subst hu
      have hfin : ∃ m' G' Dn', RanB s s1 (0 * nodeCost S U.length + 1) ∧ FlagsB nm s1 U m' ∧
          Repr nm s1.nodes.val graph.val (graphPat (nm none) U G') ∧
          WalkInv S U c₀ [] G' Dn' m' :=
        ⟨m, G, Dn, hK.ran.ranB.mono (by omega), hF.mono hK.ran.ext (by rw [hK.tbl]),
          by rw [hK.nodes]; exact hg, hInv⟩
      step*
  | succ n ih =>
    intro s todo graph T G Dn m hcard hI hF hInv hde hU htd hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [Nat.add_mul, Nat.one_mul, nodeCost] at hroom'
    have hW := hI.toWf
    unfold sorts.reach_loop
    rw [loop]
    simp only [sorts.reach_loop.body]
    step with uncons_repr s todo hW htd (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altPat] at hu
    simp only at hK
    cases T with
    | nil =>
      subst hu
      have hfin : ∃ m' G' Dn', RanB s s1 ((n + 1) * nodeCost S U.length + 1) ∧
          FlagsB nm s1 U m' ∧ Repr nm s1.nodes.val graph.val (graphPat (nm none) U G') ∧
          WalkInv S U c₀ [] G' Dn' m' :=
        ⟨m, G, Dn, hK.ran.ranB.mono (by omega), hF.mono hK.ran.ext (by rw [hK.tbl]),
          by rw [hK.nodes]; exact hg, hInv⟩
      step*
    | cons d T =>
      obtain ⟨di, t, rfl, rd, rt⟩ := hu
      have ht1 := hK.ticks
      have hx1 := hK.ran.ext
      have hmd : m d ≠ none := (hInv.dom d).2 (Or.inl List.mem_cons_self)
      have hsub : Sub U d := (hF.has d hmd).1
      have hF1 : FlagsB nm s1 U m := hF.mono hx1 (by rw [hK.tbl])
      step with rest_ok_spec hC.inj S hC.sorts d hsub s1 decls di hK.wf (hx1.repr hde)
        (hx1.repr rd) (by unfold Room; omega) as ⟨r1, hR2, hb⟩
      obtain ⟨b, s2⟩ := r1
      simp only at hR2 hb
      have ht2 := hR2.ticks
      have R2 : Ran s s2 (U.length * (3 * S.length + 4) + 2) := (hK.ran.trans hR2).mono (by omega)
      have hF2 : FlagsB nm s2 U m := hF.mono R2.ext (by rw [R2.tbl])
      have rest : ∀ (s' : store.Store) (todo' graph' : store.TermId) (T' : List Sorts.Conj)
          (G' : List Entry) (m₁ : Sorts.Conj → Option Bool),
          RanB s s' (nodeCost S U.length) → FlagsB nm s' U m₁ →
          WalkInv S U c₀ T' G' (d :: Dn) m₁ →
          Repr nm s'.nodes.val todo'.val (altPat (nm none) U T') →
          Repr nm s'.nodes.val graph'.val (graphPat (nm none) U G') →
          loop (fun x => match x with
            | (todo1, s1, graph1) => sorts.reach_loop.body decls names todo1 s1 graph1)
            (todo', s', graph') ⦃ r => ∃ m' G' Dn',
            RanB s r.2 ((n + 1) * nodeCost S U.length + 1) ∧ FlagsB nm r.2 U m' ∧
              Repr nm r.2.nodes.val r.1.val (graphPat (nm none) U G') ∧
              WalkInv S U c₀ [] G' Dn' m' ⦄ := by
        intro s' todo' graph' T' G' m₁ R0 hF' hInv' htd' hg'
        have := R0.ticks
        simp only [nodeCost] at this
        have IH := ih s' todo' graph' T' G' (d :: Dn) m₁
          (by simp only [List.length_cons]; omega) (R0.inv hI) hF' hInv' (R0.ext.repr hde)
          (R0.ext.repr hU) htd' hg' (by unfold Room; simp only [nodeCost]; omega)
        unfold sorts.reach_loop at IH
        refine WP.spec_mono IH ?_
        rintro r ⟨m', G'', Dn', hR, hFm, hrg, hInv''⟩
        exact ⟨m', G'', Dn', (R0.trans hR).mono (by simp only [Nat.add_mul, Nat.one_mul]; omega),
          hFm, hrg, hInv''⟩
      cases b with
      | true =>
        have hr : Sorts.RestOK S d := hb.1 rfl
        simp only [uncurry, ↓reduceIte]
        step with set_flag_w s2 .B di true hR2.wf (R2.ext.repr rd).lt (by unfold Room; omega)
          as ⟨s3, hn3, ht3, hW3, htb3, htbo3, hst3⟩
        have hx3 : Extends s2 s3 := Extends.of_eq hn3 (by omega)
        have R3 : RanB s s3 (nodeCost S U.length) :=
          ⟨hW3, R2.ext.trans hx3, by rw [hst3, R2.stk], by
            have := R2.ticks; simp only [nodeCost]; omega⟩
        have hF3 := hF2.set hC.inj hR2.wf (b := true) hsub (R2.ext.repr rd) hn3
          (by simpa using htb3)
        exact rest s3 t graph T G _ R3 hF3 (hInv.rest hr) (R3.ext.repr rt) (R3.ext.repr hg)
      | false =>
        have hnr : ¬ Sorts.RestOK S d := fun h => by simpa using hb.2 h
        simp only [uncurry, Bool.false_eq_true, ↓reduceIte]
        step with expand_spec hC d hsub hnr s2 decls names di t T m (R2.ranB.inv hI) hF2
          (R2.ext.repr hde) (R2.ext.repr hU) (R2.ext.repr rd) (R2.ext.repr rt)
          (by unfold Room; omega) as ⟨r3, m₁, T₁, hR3, hF3, ral, rtd, hE, hall⟩
        obtain ⟨⟨alts, td⟩, s3⟩ := r3
        simp only at hR3 hF3 ral rtd
        have ht3 := hR3.ticks
        have R3 := R2.ranB.trans hR3
        step with alloc_w s3 (.App di alts) hR3.wf ⟨(R3.ext.repr rd).lt, ral.lt⟩
          (by unfold Room; omega) as ⟨r4, hW4, ht4, htb4, hx4, hid4, hst4⟩
        obtain ⟨entry, s4⟩ := r4
        simp only at hW4 ht4 htb4 hx4 hid4 hst4 ⊢
        have rentry : Repr nm s4.nodes.val entry.val (entryPat (nm none) U (d, dAlts S U d)) :=
          .app hid4 (hx4.repr (R3.ext.repr rd)) (hx4.repr ral)
        step with alloc_w s4 (.App entry graph) hW4 ⟨rentry.lt, (hx4.repr (R3.ext.repr hg)).lt⟩
          (by unfold Room; omega) as ⟨r5, hW5, ht5, htb5, hx5, hid5, hst5⟩
        obtain ⟨graph1, s5⟩ := r5
        simp only at hW5 ht5 htb5 hx5 hid5 hst5 ⊢
        have R5 : RanB s s5 (nodeCost S U.length) :=
          ⟨hW5, (R3.ext.trans hx4).trans hx5, by rw [hst5, hst4, R3.stk], by
            have := R2.ticks; simp only [nodeCost]; omega⟩
        have rg1 : Repr nm s5.nodes.val graph1.val
            (graphPat (nm none) U ((d, dAlts S U d) :: G)) := by
          simp only [graphPat, List.map_cons, encList]
          exact .app hid5 (hx5.repr rentry) (R5.ext.repr hg)
        simp only [uncurry, bind_ok]
        exact rest s5 td graph1 T₁ _ m₁ R5 ((hF3.mono hx4 (by rw [htb4])).mono hx5 (by rw [htb5]))
          (hInv.expand hnr hE hall) (hx5.repr (hx4.repr rtd)) rg1

theorem reach_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (c₀ : Sorts.Conj) (hc : Sub U c₀) (s : store.Store) (decls names ci : store.TermId)
    (hI : Inv s) (hF : FlagsB nm s U fun _ => none) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c₀))
    (hroom : Room s ((Sorts.reachSet S c₀).card * nodeCost S U.length + 4)) :
    sorts.reach s decls names ci ⦃ r => ∃ m G Dn,
      RanB s r.2 ((Sorts.reachSet S c₀).card * nodeCost S U.length + 4) ∧ FlagsB nm r.2 U m ∧
        Repr nm r.2.nodes.val r.1.val (graphPat (nm none) U G) ∧ WalkInv S U c₀ [] G Dn m ⦄ := by
  unfold sorts.reach
  have hroom' := hroom
  unfold Room at hroom'
  have hW := hI.toWf
  step with alloc_w s .Nil hW trivial (by unfold Room; omega)
    as ⟨nil, s1, hW1, ht1, htb1, hx1, hid1, hst1⟩
  step with set_flag_w s1 .B ci false hW1 (hx1.repr hci).lt (by unfold Room; omega)
    as ⟨s2, hn2, ht2, hW2, htb2, htbo2, hst2⟩
  have hx2 : Extends s s2 := hx1.trans (Extends.of_eq hn2 (by omega))
  have rnil : Repr nm s2.nodes.val nil.val (.sym (nm none)) := by rw [hn2]; exact .nil hid1
  step with alloc_w s2 (.App ci nil) hW2 ⟨(hx2.repr hci).lt, rnil.lt⟩ (by unfold Room; omega)
    as ⟨todo, s3, hW3, ht3, htb3, hx3, hid3, hst3⟩
  have R3 : RanB s s3 3 := ⟨hW3, hx2.trans hx3, by rw [hst3, hst2, hst1], by omega⟩
  have hF2 := (hF.mono hx1 (by rw [htb1])).set hC.inj hW1 (b := false) hc (hx1.repr hci) hn2
    (by simpa using htb2)
  have hInv : WalkInv S U c₀ [c₀] [] [] (Function.update (fun _ => none) c₀ (some false)) := by
    have hne : ∀ c, Function.update (fun _ : Sorts.Conj => (none : Option Bool)) c₀ (some false) c
        ≠ none ↔ c = c₀ := by
      intro c
      by_cases h : c = c₀
      · subst h; simp
      · simp [h]
    refine ⟨by simp, fun c => by rw [hne]; simp, (hne c₀).2 rfl, fun c h => ?_, fun c h => ?_,
      fun c h => (by cases h), fun e h => (by cases h), Nat.le_refl _, fun e h => (by cases h)⟩
    · rw [(hne c).1 h]; exact .refl
    · by_cases hcc : c = c₀
      · subst hcc; simp at h
      · simp [hcc] at h
  have rtodo : Repr nm s3.nodes.val todo.val (altPat (nm none) U [c₀]) := by
    simp only [altPat, List.map_cons, List.map_nil, encList]
    exact .app hid3 (hx3.repr (hx2.repr hci)) (hx3.repr rnil)
  have rgraph : Repr nm s3.nodes.val nil.val (graphPat (nm none) U []) := hx3.repr rnil
  refine WP.spec_mono (reach_loop_spec hC c₀ decls names (Sorts.reachSet S c₀).card s3 todo nil
    [c₀] [] [] _ (by simp) (R3.inv hI) (hF2.mono hx3 (by rw [htb3])) hInv (R3.ext.repr hde) (R3.ext.repr hU)
    rtodo rgraph (by unfold Room; omega)) ?_
  rintro r ⟨m', G', Dn', hR, hFm, hrg, hInv'⟩
  exact ⟨m', G', Dn', (R3.trans hR).mono (by omega), hFm, hrg, hInv'⟩

/-! ## What the rounds may spend -/

theorem anyCost_eq : ∀ l : List Alt,
    anyCost l = (l.map fun a => 2 * a.2.length + 3).sum + 1
  | [] => rfl
  | a :: l => by simp only [anyCost, anyCost_eq l, List.map_cons, List.sum_cons]; omega

/-- The ticks looking through the alternatives of the cases of every
declaration may spend. -/
def altW (S : Sorts) : Nat :=
  (S.map fun p => (p.2.cases.map fun c => 2 * c.2.length + 3).sum).sum

theorem sum_caseAlts_le (S : Sorts) (d : Sorts.Conj) : ∀ cs : List (Sym × List (Option Name)),
    ((caseAlts S d cs).map fun a => 2 * a.2.length + 3).sum ≤
      (cs.map fun c => 2 * c.2.length + 3).sum
  | [] => by simp [caseAlts]
  | x :: cs => by
    have ih := sum_caseAlts_le S d cs
    by_cases h : Sorts.Accepts S d x.1 x.2.length
    · simp only [caseAlts, h, ↓reduceIte, List.singleton_append, List.map_cons, List.sum_cons,
        altOf, List.length_map, List.length_range]
      omega
    · simp only [caseAlts, h, ↓reduceIte, List.nil_append, List.map_cons, List.sum_cons]
      omega

theorem sum_nameAlts_le (S : Sorts) (d : Sorts.Conj) : ∀ ns : List Name,
    ((nameAlts S d ns).map fun a => 2 * a.2.length + 3).sum ≤ ns.length * altW S
  | [] => by simp [nameAlts]
  | x :: ns => by
    have ih := sum_nameAlts_le S d ns
    simp only [nameAlts, List.map_append, List.sum_append, List.length_cons, Nat.add_mul,
      Nat.one_mul]
    have : ((match S.lookup x with
        | some dd => caseAlts S d dd.cases
        | none => []).map fun a : Alt => 2 * a.2.length + 3).sum ≤ altW S := by
      cases hl : S.lookup x with
      | none => simp
      | some dd =>
        refine (sum_caseAlts_le S d dd.cases).trans ?_
        exact List.le_sum_of_mem (List.mem_map.2 ⟨(x, dd), Sorts.mem_of_lookup hl, rfl⟩)
    omega

theorem anyCost_dAlts_le (S : Sorts) (U : List Name) (d : Sorts.Conj) :
    anyCost (dAlts S U d) ≤ U.length * altW S + 1 := by
  rw [anyCost_eq, dAlts, List.map_reverse, List.sum_reverse]
  have h₁ := sum_nameAlts_le S d (conjList U (· ∈ d))
  have h₂ := Nat.mul_le_mul_right (altW S) (length_conjList_le U (· ∈ d))
  omega

theorem passCost_le {B : Nat} : ∀ G : List Entry, (∀ e ∈ G, anyCost e.2 ≤ B) →
    passCost G ≤ G.length * (B + 4) + 1
  | [], _ => by simp [passCost]
  | e :: G, h => by
    have ih := passCost_le G fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have := h e List.mem_cons_self
    simp only [passCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The ticks flagging the conjunctions a conjunction reaches may spend, when
it reaches `r` of them, with `u` names. -/
def flagCost (S : Sorts) (u r : Nat) : Nat :=
  r * nodeCost S u + (r + 1) * (r * (u * altW S + 5) + 1) + 5

/-- `flag_live` gives the conjunctions the conjunction reaches that have a
sort without a rest, each with its alternatives, and leaves table `B` flagging
with yes exactly the conjunctions reached that have a member
(`WalkInv.live_iff`). -/
theorem flag_live_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (c₀ : Sorts.Conj) (hc : Sub U c₀) (s : store.Store) (decls names ci : store.TermId)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c₀))
    (hroom : Room s (flagCost S U.length (Sorts.reachSet S c₀).card)) :
    sorts.flag_live s decls names ci ⦃ r => ∃ m m' G Dn,
      RanB s r.2 (flagCost S U.length (Sorts.reachSet S c₀).card) ∧ FlagsB nm r.2 U m' ∧
        Repr nm r.2.nodes.val r.1.val (graphPat (nm none) U G) ∧ WalkInv S U c₀ [] G Dn m ∧
        (∀ c ∈ Dn, Sub U c) ∧ Le m m' ∧ Sound S m' ∧ Stable m' G ∧
        passCost G ≤ (Sorts.reachSet S c₀).card * (U.length * altW S + 5) + 1 ⦄ := by
  unfold sorts.flag_live
  have hroom' := hroom
  unfold Room at hroom'
  simp only [flagCost] at hroom'
  have hW := hI.toWf
  step with clear_w s .B hW (by unfold Room; omega) as ⟨s1, hn1, ht1, hW1, hcl, hoth, hst1⟩
  have hx1 : Extends s s1 := Extends.of_eq hn1 (by omega)
  have R1 : RanB s s1 1 := ⟨hW1, hx1, hst1, by omega⟩
  have hF1 : FlagsB nm s1 U fun _ => none :=
    ⟨fun c h => absurd rfl h, fun i h => absurd (by simp [flagB, hcl]) h⟩
  step with reach_spec hC c₀ hc s1 decls names ci (R1.inv hI) hF1 (hx1.repr hde) (hx1.repr hU)
    (hx1.repr hci) (by unfold Room; omega) as ⟨graph, s2, m, G, Dn, hR2, hF2, rg, hInv⟩
  have ht2 := hR2.ticks
  have R2 := R1.trans hR2
  have hsub : ∀ c ∈ Dn, Sub U c := fun c hcd => (hF2.has c ((hInv.dom c).2 (Or.inr hcd))).1
  have hG := hInv.entryOK hC hsub
  have hdom : ∀ e ∈ G, m e.1 ≠ none := fun e he => (hInv.dom e.1).2 (Or.inr (hInv.graph e he).1)
  have hGl : G.length ≤ (Sorts.reachSet S c₀).card := hInv.glen.trans hInv.len_le
  have hpc : passCost G ≤ (Sorts.reachSet S c₀).card * (U.length * altW S + 5) + 1 := by
    have h₁ := passCost_le (B := U.length * altW S + 1) G fun e he => by
      rw [(hInv.graph e he).2]; exact anyCost_dAlts_le S U e.1
    have h₂ := Nat.mul_le_mul_right (U.length * altW S + 1 + 4) hGl
    have e : U.length * altW S + 1 + 4 = U.length * altW S + 5 := by omega
    rw [e] at h₁ h₂
    omega
  have hfl : falses G m + 1 ≤ (Sorts.reachSet S c₀).card + 1 := by
    have := falses_le G m; omega
  have hloop : (falses G m + 1) * passCost G ≤
      ((Sorts.reachSet S c₀).card + 1) *
        ((Sorts.reachSet S c₀).card * (U.length * altW S + 5) + 1) :=
    Nat.mul_le_mul hfl hpc
  step with live_loop_spec hC.inj S G graph hG (falses G m + 1) s2 m (Nat.lt_succ_self _) hR2.wf
    hF2 hInv.sound hdom rg (by unfold Room; omega) as ⟨s3, m', hR3, hF3, hS3, hLe, hst⟩
  have ht3 := hR3.ticks
  have R3 := R2.trans hR3
  exact ⟨m, m', G, Dn, R3.mono (by simp only [flagCost]; omega), hF3, hR3.ext.repr rg, hInv,
    hsub, hLe, hS3, hst, hpc⟩

/-- The ticks deciding whether a conjunction that reaches `r` conjunctions
has a member may spend, with `u` names. -/
def liveCost (S : Sorts) (u r : Nat) : Nat := flagCost S u r + 1

/-- `live` answers whether the conjunction has a member (`Sorts.live`). It
spends a number of ticks that is polynomial in the size of the sorts and in
the number of conjunctions the conjunction reaches. -/
theorem live_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (c₀ : Sorts.Conj) (hc : Sub U c₀) (s : store.Store) (decls names ci : store.TermId)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c₀))
    (hroom : Room s (liveCost S U.length (Sorts.reachSet S c₀).card)) :
    sorts.live s decls names ci ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + liveCost S U.length (Sorts.reachSet S c₀).card ∧
        (r = true ↔ c₀ ∈ Sorts.live S) ⦄ := by
  unfold sorts.live
  have hroom' := hroom
  unfold Room at hroom'
  simp only [liveCost] at hroom'
  step with flag_live_spec hC c₀ hc s decls names ci hI hde hU hci (by unfold Room; omega)
    as ⟨graph, s3, m, m', G, Dn, R3, hF3, rg, hInv, hsub, hLe, hS3, hst, hpc⟩
  have ht3 := R3.ticks
  have rci := R3.ext.repr hci
  step with get_flag_w s3 .B ci R3.wf rci.lt (by unfold Room; omega) as ⟨o, s4, hfl4, hK4⟩
  have ht4 := hK4.ticks
  have hfin : Inv s4 ∧ Extends s s4 ∧
      s4.ticks.val ≤ s.ticks.val + liveCost S U.length (Sorts.reachSet S c₀).card :=
    ⟨⟨hK4.wf, by rw [hK4.stk, R3.stk]; exact hI.empty⟩, R3.ext.trans hK4.ran.ext, by
      simp only [liveCost]; omega⟩
  have ho : o = m' c₀ := by
    rw [hfl4]
    have := hF3.get hC.inj R3.wf hc rci
    simpa only [flagB] using this
  have hiff := hInv.live_iff hsub hLe hS3 hst .refl
  rw [← ho] at hiff
  cases o with
  | none => simp only [WP.spec_ok]; exact ⟨hfin.1, hfin.2.1, hfin.2.2, by simpa using hiff⟩
  | some b =>
    cases b with
    | true => simp only [↓reduceIte, WP.spec_ok]; exact ⟨hfin.1, hfin.2.1, hfin.2.2, by simpa using hiff⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨hfin.1, hfin.2.1, hfin.2.2, by simpa using hiff⟩

end RwLogVerified
