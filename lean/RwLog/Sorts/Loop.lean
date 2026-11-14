/-
# Bringing a store to a tight one

`tighten` replaces, as long as there is one, a variable whose values have one
root by that root applied to new variables, and each new variable whose sorts
have one member by that member. The store it returns denotes what the store
it was given does (`tighten_den`), satisfies `Inv`, and has no variable whose
values have one root (`tighten_sole`). It returns nothing only for a store
that denotes nothing (`tighten_none`).

Each replacement adds a symbol to the pattern, and a pattern has no more
symbols than a term it denotes. The recursion is on the room that leaves
(`room`), which is not computed.
-/
import RwLog.Sorts.Tighten

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

namespace CStore

/-- The store with the variable `v` replaced by `f` applied to `n` new
variables. -/
def exp (S : Sorts) (s : CStore) (v : Nat) (f : Sym) (n : Nat) : CStore :=
  ⟨s.t.bind (Term.single v (expVar s.c.length n f)),
    s.c.set v ∅ ++ (List.range n).map (kidC S (s.conj v) f n),
    s.x.map (Eqns.subst v (expVar s.c.length n f))⟩

theorem exp_store (s : CStore) {v : Nat} (hv : v < s.c.length) (f : Sym) (n : Nat) :
    (s.exp S v f n).store = expStore S s.store s.c.length v f n := by
  show Store.mk _ _ _ = Store.mk _ _ _
  congr 1
  funext w
  show (s.c.set v ∅ ++ (List.range n).map (kidC S (s.conj v) f n)).getD w ∅ = _
  show _ = if w = v then ∅ else if s.c.length ≤ w ∧ w < s.c.length + n
    then kidC S (s.conj v) f n (w - s.c.length) else s.conj w
  rw [List.getD_eq_getElem?_getD]
  by_cases hwv : w = v
  · subst hwv
    simp [List.getElem?_append_left, hv]
  · rw [ite_eq_right hwv]
    by_cases hw : w < s.c.length
    · rw [List.getElem?_append_left (by simpa using hw), List.getElem?_set_ne (Ne.symm hwv),
        ite_eq_right (by omega)]
      simp [conj, List.getD_eq_getElem?_getD]
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hw)]
      simp only [List.length_set]
      by_cases hr : w < s.c.length + n
      · rw [ite_eq_left ⟨Nat.le_of_not_lt hw, hr⟩]
        have : w - s.c.length < n := by omega
        simp [this]
      · rw [ite_eq_right (by omega), s.conj_of_ge (Nat.le_of_not_lt hw)]
        have : n ≤ w - s.c.length := by omega
        simp [this]

theorem exp_length (s : CStore) (v : Nat) (f : Sym) (n : Nat) :
    (s.exp S v f n).c.length = s.c.length + n := by simp [exp]

/-- The store with the variable `v` replaced by the ground term `g`. -/
def set (s : CStore) (v : Nat) (g : GTerm) : CStore :=
  ⟨s.t.bind (Term.single v (GTerm.toPat g)), s.c.set v ∅,
    s.x.map (Eqns.subst v (GTerm.toPat g))⟩

theorem set_store (s : CStore) (v : Nat) (g : GTerm) : (s.set v g).store = setStore s.store v g := by
  show Store.mk _ _ _ = Store.mk _ _ _
  congr 1
  funext w
  show (s.c.set v ∅).getD w ∅ = if w = v then ∅ else s.conj w
  rw [List.getD_eq_getElem?_getD]
  by_cases hwv : w = v
  · subst hwv
    by_cases hw : w < s.c.length
    · simp [hw]
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hw)]; simp
  · rw [ite_eq_right hwv, List.getElem?_set_ne (Ne.symm hwv)]
    simp [conj, List.getD_eq_getElem?_getD]

theorem set_length (s : CStore) (v : Nat) (g : GTerm) : (s.set v g).c.length = s.c.length := by
  simp [set]

/-- Replace each listed variable whose sorts have one member by that member. -/
def settle (S : Sorts) (s : CStore) : List Nat → CStore
  | [] => s
  | w :: ws =>
    match count S (s.conj w) with
    | .one g => settle S (s.set w g) ws
    | _ => settle S s ws

end CStore

open CStore

/-- What `tighten` keeps between replacements: the store is first-order, every
variable it mentions occurs in its pattern, and no variable of the pattern
has sorts with one member. -/
structure Kept (S : Sorts) (s : CStore) : Prop where
  fin : s.store.Fin s.c.length
  full : s.store.Full
  notOne : ∀ v ∈ s.t.vars, ∀ g, count S (s.conj v) ≠ .one g

theorem Inv.kept {s : CStore} (h : Inv S s) : Kept S s :=
  ⟨h.fin, h.full, fun v hv g e => by rw [h.many v hv] at e; cases e⟩

theorem settle_spec (S : Sorts) : ∀ (ws : List Nat) (s : CStore),
    (settle S s ws).store.Den S = s.store.Den S ∧
    (settle S s ws).c.length = s.c.length ∧
    (s.store.Fin s.c.length → (settle S s ws).store.Fin s.c.length) ∧
    (s.store.Full → (settle S s ws).store.Full) ∧
    s.t.syms.length ≤ (settle S s ws).t.syms.length ∧
    (∀ w ∈ (settle S s ws).t.vars, w ∈ s.t.vars ∧ (settle S s ws).conj w = s.conj w) ∧
    ∀ w ∈ ws, w ∈ (settle S s ws).t.vars → ∀ g, count S ((settle S s ws).conj w) ≠ .one g
  | [], s => ⟨rfl, rfl, id, id, Nat.le_refl _, fun w hw => ⟨hw, rfl⟩, by simp⟩
  | w :: ws, s => by
    cases hc : count S (s.conj w) with
    | one g =>
      have e : settle S s (w :: ws) = settle S (s.set w g) ws := by simp only [settle, hc]
      rw [e]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := settle_spec S ws (s.set w g)
      have hden : (s.set w g).store.Den S = s.store.Den S := by
        rw [set_store]
        exact setStore_den (count_one.1 hc).1 (count_one.1 hc).2
      have hnot : w ∉ (s.set w g).t.vars := by
        have := setStore_not_mem (s := s.store) (v := w) (g := g)
        rwa [← set_store] at this
      have hvars : ∀ u ∈ (s.set w g).t.vars, u ∈ s.t.vars ∧ u ≠ w := by
        intro u hu
        rcases Term.vars_bind_single u hu with h | h
        · exact h
        · rw [toPat_vars] at h; cases h
      have hconj : ∀ u, u ≠ w → (s.set w g).conj u = s.conj u := by
        intro u hu
        have := congrArg (fun st : Store => st.c u) (s.set_store w g)
        simpa [setStore, hu, CStore.store] using this
      rw [set_length] at h2 h3
      refine ⟨h1.trans hden, h2, fun hf => h3 (by rw [set_store]; exact setStore_fin hf),
        fun hf => h4 (by rw [set_store]; exact setStore_full hf),
        Nat.le_trans (Term.syms_length_bind_le _ _) h5, ?_, ?_⟩
      · intro u hu
        obtain ⟨hu1, hu2⟩ := h6 u hu
        exact ⟨(hvars u hu1).1, hu2.trans (hconj u (hvars u hu1).2)⟩
      · intro u hu hin
        rcases List.mem_cons.1 hu with rfl | hu
        · exact absurd (h6 u hin).1 hnot
        · exact h7 u hu hin
    | none =>
      have e : settle S s (w :: ws) = settle S s ws := by simp only [settle, hc]
      rw [e]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := settle_spec S ws s
      refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
      intro u hu hin
      rcases List.mem_cons.1 hu with rfl | hu
      · rw [(h6 u hin).2, hc]; intro g e; cases e
      · exact h7 u hu hin
    | many =>
      have e : settle S s (w :: ws) = settle S s ws := by simp only [settle, hc]
      rw [e]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := settle_spec S ws s
      refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
      intro u hu hin
      rcases List.mem_cons.1 hu with rfl | hu
      · rw [(h6 u hin).2, hc]; intro g e; cases e
      · exact h7 u hu hin

/-- One replacement: the first variable whose values have one root. -/
def step? (S : Sorts) (s : CStore) : Option CStore :=
  (s.t.vars.findSome? fun v => (sole S (s.conj v) (gone s.x v)).map fun key => (v, key)).map
    fun r => settle S (s.exp S r.1 r.2.1 r.2.2) ((List.range r.2.2).map (s.c.length + ·))

theorem step?_none {s : CStore} (h : step? S s = none) :
    ∀ v ∈ s.t.vars, sole S (s.conj v) (gone s.x v) = none := by
  simp only [step?, Option.map_eq_none_iff, List.findSome?_eq_none_iff] at h
  exact h

theorem step?_some {s s' : CStore} (hI : Inv S s) (h : step? S s = some s') :
    s'.store.Den S = s.store.Den S ∧ s.t.syms.length < s'.t.syms.length ∧ Kept S s' := by
  simp only [step?, Option.map_eq_some_iff] at h
  obtain ⟨⟨v, f, n⟩, hfind, rfl⟩ := h
  obtain ⟨v', hv', hsome⟩ := List.exists_of_findSome?_eq_some hfind
  have hsole : sole S (s.conj v) (gone s.x v) = some (f, n) ∧ v' = v := by
    cases hsl : sole S (s.conj v') (gone s.x v') with
    | none => rw [hsl] at hsome; cases hsome
    | some key =>
      rw [hsl] at hsome
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact ⟨hsl, rfl⟩
  obtain ⟨hsole, rfl⟩ := hsole
  have hvN := hI.tv v' hv'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := settle_spec S
    ((List.range n).map (s.c.length + ·)) (s.exp S v' f n)
  have hes := s.exp_store (S := S) hvN f n
  have hsole' : sole S (s.store.c v') (gone s.store.x v') = some (f, n) := hsole
  rw [exp_length] at h2 h3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, hes]; exact expStore_den hI.fin hvN hsole'
  · exact Nat.lt_of_lt_of_le
      (Term.syms_length_bind_single_lt (Term.syms_mk_pos _ _) hv') h5
  · rw [h2]; exact h3 (by rw [hes]; exact expStore_fin hI.fin hv')
  · exact h4 (by rw [hes]; exact expStore_full hI.full hv')
  · intro u hu g
    obtain ⟨hu1, hu2⟩ := h6 u hu
    rcases Term.vars_bind_single u hu1 with ⟨hut, huv⟩ | hnew
    · rw [hu2]
      have : (s.exp S v' f n).conj u = s.conj u := by
        have := congrArg (fun st : Store => st.c u) hes
        have hlt := hI.tv u hut
        simpa [expStore, huv, CStore.store, Nat.not_le.2 hlt] using this
      rw [this, hI.many u hut]; intro e; cases e
    · obtain ⟨hlo, hhi⟩ := mem_expVar_vars.1 hnew
      refine h7 u (List.mem_map.2 ⟨u - s.c.length, List.mem_range.2 (by omega), by omega⟩) hu g

/-- A term the set holds, when it holds one. -/
noncomputable def witness (D : Set GTerm) : GTerm :=
  open Classical in if h : D.Nonempty then Classical.choose h else .sym ""

theorem witness_mem {D : Set GTerm} (h : D.Nonempty) : witness D ∈ D := by
  unfold witness; simp only [h, ↓reduceDIte]; exact Classical.choose_spec h

/-- The symbols a term the store denotes has more than the pattern. -/
noncomputable def room (S : Sorts) (s : CStore) : Nat :=
  (witness (s.store.Den S)).syms.length - s.t.syms.length

theorem room_lt (hS : S.WellFormed) {s s' : CStore} (hI : Inv S s) (h : step? S s = some s') :
    room S s' < room S s := by
  obtain ⟨hden, hsyms, -⟩ := step?_some hI h
  unfold room
  rw [hden]
  have hm : witness (s.store.Den S) ∈ s'.store.Den S := by
    rw [hden]; exact witness_mem (hI.nonempty hS)
  obtain ⟨σ, -, hσ⟩ := hm
  have : s'.t.syms.length ≤ (witness (s.store.Den S)).syms.length := by
    rw [hσ]; exact Term.syms_length_bind_le σ s'.t
  omega

/-- Replace variables until none has values with one root. -/
def tighten (S : Sorts) (hS : S.WellFormed) (s : CStore) : Option CStore :=
  if _h : Inv S s then
    match _hs : step? S s with
    | some s' => tighten S hS s'
    | none => some s
  else none
termination_by room S s
decreasing_by exact room_lt hS ‹_› ‹_›

theorem tighten_some (hS : S.WellFormed) : ∀ (k : Nat) (s s' : CStore), room S s = k →
    tighten S hS s = some s' →
    s'.store.Den S = s.store.Den S ∧ Inv S s' ∧
      ∀ v ∈ s'.t.vars, sole S (s'.conj v) (gone s'.x v) = none := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s s' hk h
    rw [tighten] at h
    split at h
    · rename_i hI
      split at h
      · rename_i s₁ hs
        obtain ⟨h1, h2, h3⟩ := ih _ (hk ▸ room_lt hS hI hs) s₁ s' rfl h
        exact ⟨h1.trans (step?_some hI hs).1, h2, h3⟩
      · rename_i hs
        cases h
        exact ⟨rfl, hI, step?_none hs⟩
    · cases h

/-- Equations that always hold are satisfied by every substitution. -/
theorem always_unifies {E : Eqns Nat} (h : always E = true) (σ : Nat → GTerm) :
    Eqns.Unifies σ E := by
  unfold always at h
  split at h
  · rename_i θ hθ
    rw [List.all_eq_true] at h
    obtain ⟨hu, -⟩ := solve_some hθ
    intro p hp
    have e : ∀ q : Pat, (∀ w ∈ q.vars, w ∈ E.vars) → q.bind θ = q := by
      intro q hq
      conv_rhs => rw [← Term.bind_var_id q]
      apply Term.bind_congr
      intro w hw
      simpa using h w (hq w hw)
    have hin : ∀ w, w ∈ p.1.vars ++ p.2.vars → w ∈ E.vars := fun w hw =>
      List.mem_flatMap.2 ⟨p, hp, hw⟩
    have := hu p hp
    rw [e p.1 fun w hw => hin w (List.mem_append_left _ hw),
      e p.2 fun w hw => hin w (List.mem_append_right _ hw)] at this
    rw [this]
  · cases h

/-- A store that fails the invariant, with what `tighten` keeps, denotes
nothing. -/
theorem den_empty_of_not_inv {s : CStore} (hP : Kept S s) (hI : ¬ Inv S s) :
    s.store.Den S = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun g ⟨σ, hσ, _⟩ => hI ?_
  refine ⟨hP.fin.fo, hP.fin.tv, hP.fin.xfo, ?_, fun v _ hv => hP.full.cs v hv, ?_, ?_⟩
  · intro E hE v hv
    obtain ⟨p, hp, hv⟩ := List.mem_flatMap.1 hv
    exact hP.full.xs E hE p hp v hv
  · intro v hv
    cases hc : count S (s.conj v) with
    | none => exact absurd ⟨_, hσ.1 v⟩ (count_none.1 hc)
    | one g => exact absurd hc (hP.notOne v hv g)
    | many => rfl
  · intro E hE
    by_contra h
    rw [Bool.not_eq_false] at h
    exact hσ.2 E hE (always_unifies h σ)

theorem tighten_none (hS : S.WellFormed) : ∀ (k : Nat) (s : CStore), room S s = k → Kept S s →
    tighten S hS s = none → s.store.Den S = ∅ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hk hP h
    rw [tighten] at h
    split at h
    · rename_i hI
      split at h
      · rename_i s₁ hs
        obtain ⟨hden, -, hP₁⟩ := step?_some hI hs
        rw [← hden]
        exact ih _ (hk ▸ room_lt hS hI hs) s₁ rfl hP₁ h
      · cases h
    · rename_i hI
      exact den_empty_of_not_inv hP hI

end Sorts
end RwLog
