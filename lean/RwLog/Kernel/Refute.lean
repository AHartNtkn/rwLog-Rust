/-
# Refuting and instantiating a non-ground span by its theory

A rule `H₁, …, Hₙ <=> B` means that, in every model of the theory, the heads
all hold exactly when the body holds. The engine reads it forwards only, as a
propagation: when the heads match members of a span's store (one-way, the
store's variables are rigid), the body instantiated by the match holds too. In
every ground instance, the models containing the store are exactly the models
containing the store together with those body atoms, so adding them changes no
meaning. Nothing is ever removed, so what the theory derives from a store it
also derives from every instance of the store and from every larger store:
refutation and forced equations are monotone, for every theory. Two matched
heads may land on one member; that is an instance of the rule's axiom and
needs no special case.

A body's equations, instantiated by the match, are solved over the store's
variables. So a symbolic firing has three outcomes:

* `refuted`: the body is `fail`, or its equations have no common instance, so
  no model contains any ground instance of the store;
* `add bs`: the equations hold syntactically, and the atoms `bs` hold too;
* `bind θ`: the equations have a most general unifier `θ` that is not the
  identity. A ground instance that `θ` does not cover makes the body false, so
  no model contains it, and instantiating the whole span by `θ` keeps exactly
  the instances some model can contain. Equations never enter the store.

Only bounded rules propagate (`TRule.bounded`, a check on the rule itself):
once a bounded rule's equations hold, each body atom is one of its heads or
smaller than one under every substitution. So every atom the closure adds is
smaller than a member of the store, over the store's variables and the
symbols of the store and the theory, and the closure is finite. A rule that is
not bounded is never used. Leaving it unused never changes a meaning, because
every firing preserves it; it can only leave a refutation unfound.

* `Theory.saturate T c` adds the atoms of every firing of a bounded rule until
  none is new.
* `Theory.refutes? T c`: some firing on the saturated store refutes it
  (obligation `Kernel.refutes_sound`).
* `Theory.bind? T c`: the first equation instantiation a firing on the
  saturated store forces.
* `Theory.simplify T s` drops `s` when it is refuted and instantiates it by
  every forced equation. It keeps the store as written: the atoms the closure
  derives are implied by it, so they are recomputed, never stored. A span's
  store is therefore compared syntactically (`Span.covers?`), and coverage is
  kept by simplification for every theory (obligation `simplify_mono`).

A non-identity most general unifier eliminates at least one variable of the
store, and no firing adds one (every variable of a rule's body occurs in its
heads), so a span is instantiated at most as many times as its store has
variables (obligation `Kernel.simplify_stable`).
-/
import RwLog.Kernel.TermFacts
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace RwLog

/-- The result of one symbolic firing. -/
inductive Firing where
  | refuted
  | add (bs : Store)
  | bind (θ : Nat → Pat)

/-- Solve the equations of a firing whose body atoms are `bs`. -/
def firingOfEqs (eqs : List (Pat × Pat)) (bs : Store) : Firing :=
  if eqs.all fun e => e.1 = e.2 then .add bs
  else match solve eqs with
    | none => .refuted
    | some θ => .bind θ

/-- The atoms a firing adds. -/
def Firing.added : Firing → Store
  | .add bs => bs
  | _ => []

/-- `u` is smaller than `t` under every substitution: it is smaller, and no
variable occurs more often in `u` than in `t`. -/
def Pat.smaller (u t : Pat) : Bool :=
  decide (u.size < t.size) && u.vars.all fun v => decide (u.vars.count v ≤ t.vars.count v)

/-- A rule is bounded when, once its equations hold (under their most general
unifier `μ`), each atom of its body is one of its heads or smaller than one.
This is a property of the rule, so on every store and every instance of it
the atoms a firing adds are members already or smaller than a member. A rule
whose equations have no unifier only refutes. -/
def TRule.bounded (ρ : TRule) : Bool :=
  match ρ.body with
  | .fail => true
  | .conj eqs cs =>
    match solve eqs with
    | none => true
    | some μ =>
      let H := ρ.heads.map (Term.bind μ)
      (cs.map (Term.bind μ)).all fun b => H.contains b || H.any (Pat.smaller b)

/-- All symbolic firings of one rule on a store, one for each match of its
heads. -/
def TRule.firings (ρ : TRule) (c : Store) : List Firing :=
  (matchAll ρ.heads c []).map fun r =>
    match ρ.body with
    | .fail => .refuted
    | .conj eqs cs =>
      firingOfEqs (eqs.map fun e => (e.1.bind r.1.apply, e.2.bind r.1.apply))
        (cs.map (Term.bind r.1.apply))

/-- The firings of the bounded rules of a theory on a store. -/
def Theory.firings (T : Theory) (c : Store) : List Firing :=
  T.flatMap fun ρ => if ρ.bounded then ρ.firings c else []

/-! ### The closure terminates

Every atom a round adds is smaller than a member of the store and is built
from the store's variables and from symbols of the store and of the bodies of
bounded rules. Such atoms form a finite set that adding them does not change,
so each round that adds an atom leaves less room. -/

/-- The symbols a bounded rule's body can bring in: those of its body atoms
under the most general unifier of its equations. -/
def TRule.bodySyms (ρ : TRule) : List Sym :=
  match ρ.body with
  | .fail => []
  | .conj eqs cs =>
    match solve eqs with
    | none => []
    | some μ => (cs.map (Term.bind μ)).flatMap Term.syms

/-- The symbols the closure of `c` can use. -/
def Theory.symsOf (T : Theory) (c : Store) : Finset Sym :=
  (c.flatMap Term.syms).toFinset ∪ (T.flatMap TRule.bodySyms).toFinset

/-- The variables of a store. -/
def Store.varSet (c : Store) : Finset Nat := (c.flatMap Term.vars).toFinset

/-- The size of the store's largest member. -/
def Store.maxSize (c : Store) : Nat := c.foldr (fun a n => max a.size n) 0

/-- The atoms of size at most `m` over the symbols `S` and the variables `V`. -/
def Pat.Within (S : Finset Sym) (V : Finset Nat) (m : Nat) (t : Pat) : Prop :=
  (∀ f ∈ t.syms, f ∈ S) ∧ (∀ v ∈ t.vars, v ∈ V) ∧ t.size ≤ m

theorem Pat.within_finite (S : Finset Sym) (V : Finset Nat) :
    ∀ m, {t : Pat | t.Within S V m}.Finite
  | 0 => Set.finite_empty.subset fun t ht => by
      have := Term.size_pos t; have := ht.2.2; omega
  | m + 1 => by
    refine ((((Finset.finite_toSet S).image Term.sym).union
      ((Finset.finite_toSet V).image Term.var)).union
      ((Pat.within_finite S V m).image2 Term.app (Pat.within_finite S V m))).subset ?_
    rintro (v | f | ⟨t, u⟩) ⟨hs, hv, hz⟩
    · exact Or.inl (Or.inr ⟨v, hv v (by simp [Term.vars]), rfl⟩)
    · exact Or.inl (Or.inl ⟨f, hs f (by simp [Term.syms]), rfl⟩)
    · simp only [Term.size] at hz
      have := Term.size_pos t; have := Term.size_pos u
      refine Or.inr ⟨t, ⟨fun f hf => hs f (by simp [Term.syms, hf]),
        fun v hv' => hv v (by simp [Term.vars, hv']), by omega⟩, u,
        ⟨fun f hf => hs f (by simp [Term.syms, hf]),
        fun v hv' => hv v (by simp [Term.vars, hv']), by omega⟩, rfl⟩

/-- How much room the closure of `c` has left. -/
noncomputable def Theory.room (T : Theory) (c : Store) : Nat :=
  ((Pat.within_finite (T.symsOf c) c.varSet c.maxSize).toFinset \ c.toFinset).card

theorem Term.size_bind {V W : Type} (σ : V → Term W) :
    ∀ t : Term V, (t.bind σ).size = t.size + (t.vars.map fun v => (σ v).size - 1).sum
  | .var v => by
    have := Term.size_pos (σ v)
    simp only [Term.bind_var, Term.size, Term.vars, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  | .sym f => by simp [Term.size, Term.vars]
  | .app t u => by
    simp only [Term.bind_app, Term.size, Term.vars, List.map_append, List.sum_append,
      Term.size_bind σ t, Term.size_bind σ u]
    omega

theorem Pat.smaller_vars {u t : Pat} (h : u.smaller t = true) :
    (u.vars : Multiset Nat) ≤ t.vars := by
  rw [Multiset.le_iff_count]
  intro v
  simp only [Multiset.coe_count]
  by_cases hv : v ∈ u.vars
  · simp only [Pat.smaller, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact h.2 v hv
  · rw [List.count_eq_zero.2 hv]; exact Nat.zero_le _

theorem Pat.smaller_size {u t : Pat} (h : u.smaller t = true) (σ : Nat → Pat) :
    (u.bind σ).size < (t.bind σ).size := by
  have h1 : u.size < t.size := by
    simp only [Pat.smaller, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  obtain ⟨D, hD⟩ := Multiset.le_iff_exists_add.1 (Pat.smaller_vars h)
  have h2 := congrArg (fun m : Multiset Nat => (m.map fun v => (σ v).size - 1).sum) hD
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_coe, Multiset.sum_coe] at h2
  rw [Term.size_bind, Term.size_bind]
  omega

theorem Pat.smaller_mem_vars {u t : Pat} (h : u.smaller t = true) {v : Nat} (hv : v ∈ u.vars) :
    v ∈ t.vars := by
  have := Multiset.count_le_of_le v (Pat.smaller_vars h)
  simp only [Multiset.coe_count] at this
  exact List.count_pos_iff.1 (lt_of_lt_of_le (List.count_pos_iff.2 hv) this)

theorem Store.le_maxSize {c : Store} {a : Pat} (h : a ∈ c) : a.size ≤ c.maxSize := by
  induction c with
  | nil => cases h
  | cons b c ih =>
    simp only [Store.maxSize, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem Store.maxSize_le {c : Store} {m : Nat} (h : ∀ a ∈ c, a.size ≤ m) : c.maxSize ≤ m := by
  induction c with
  | nil => exact Nat.zero_le _
  | cons b c ih =>
    simp only [Store.maxSize, List.foldr_cons] at ih ⊢
    exact max_le (h b (by simp)) (ih fun a ha => h a (by simp [ha]))

/-- The atoms one round adds: those some firing derives that the store lacks. -/
def Theory.newAtoms (T : Theory) (c : Store) : Store :=
  (((T.firings c).flatMap Firing.added).eraseDups).filter fun a => !c.contains a

/-- An atom a round adds is new, smaller than a member, and built from the
store's variables and the symbols the closure can use. -/
theorem Theory.newAtoms_spec {T : Theory} {c : Store} {x : Pat} (hx : x ∈ T.newAtoms c) :
    x ∉ c ∧ (∃ y ∈ c, x.size < y.size) ∧ (∀ f ∈ x.syms, f ∈ T.symsOf c) ∧
      ∀ v ∈ x.vars, v ∈ c.varSet := by
  simp only [Theory.newAtoms, List.mem_filter, List.mem_eraseDups, List.mem_flatMap,
    Bool.not_eq_true'] at hx
  obtain ⟨⟨f, hf, hxf⟩, hxc⟩ := hx
  replace hxc : x ∉ c := fun h => by rw [List.contains_iff_mem.2 h] at hxc; cases hxc
  refine ⟨hxc, ?_⟩
  simp only [Theory.firings, List.mem_flatMap] at hf
  obtain ⟨ρ, hρ, hf⟩ := hf
  split_ifs at hf with hbd
  swap
  · cases hf
  simp only [TRule.firings, List.mem_map] at hf
  obtain ⟨r, hr, rfl⟩ := hf
  obtain ⟨-, -, hrc, hrh⟩ := Matching.matchAll_sound _ _ _ _ hr
  have hheads : ∀ h ∈ ρ.heads, h.bind r.1.apply ∈ c := fun h hh =>
    hrc _ (by rw [← hrh r.1 (Matching.Ext.refl _)]; exact List.mem_map_of_mem hh)
  cases hb : ρ.body with
  | fail => rw [hb] at hxf; simp [Firing.added] at hxf
  | conj eqs cs =>
    rw [hb] at hxf
    dsimp only at hxf
    unfold firingOfEqs at hxf
    split_ifs at hxf with hall
    swap
    · cases hs : solve (eqs.map fun e => (e.1.bind r.1.apply, e.2.bind r.1.apply)) <;>
        rw [hs] at hxf <;> simp [Firing.added] at hxf
    simp only [Firing.added, List.mem_map] at hxf
    obtain ⟨b, hbcs, rfl⟩ := hxf
    have hU : Eqns.Unifies r.1.apply eqs := by
      intro e he
      simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at hall
      exact hall e he
    unfold TRule.bounded at hbd
    rw [hb] at hbd
    dsimp only at hbd
    cases hs : solve eqs with
    | none => exact absurd hU (solve_none hs _)
    | some μ =>
      rw [hs] at hbd
      have hfac : ∀ t : Pat, t.bind r.1.apply = (t.bind μ).bind r.1.apply := fun t => by
        rw [Term.bind_bind]
        exact Term.bind_congr fun v _ => ((solve_some hs).2 _ hU v).symm
      simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] at hbd
      rcases hbd b hbcs with ⟨h, hh, heq⟩ | ⟨_, ⟨h, hh, rfl⟩, hsm⟩
      · refine absurd ?_ hxc
        rw [hfac b, ← heq, ← hfac h]
        exact hheads h hh
      · have hmem := hheads h hh
        rw [hfac] at hmem ⊢
        refine ⟨⟨_, hmem, Pat.smaller_size hsm _⟩, fun f hf => ?_, fun v hv => ?_⟩
        · rcases Term.syms_bind_sub hf with hf | ⟨w, hw, hf⟩
          · refine Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_flatMap.2 ⟨ρ, hρ, ?_⟩))
            simp only [TRule.bodySyms, hb, hs, List.mem_flatMap, List.mem_map]
            exact ⟨_, ⟨b, hbcs, rfl⟩, hf⟩
          · exact Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_flatMap.2
              ⟨_, hmem, Term.syms_var_sub (Pat.smaller_mem_vars hsm hw) hf⟩))
        · obtain ⟨w, hw, hv⟩ := Term.vars_bind_mem hv
          exact List.mem_toFinset.2 (List.mem_flatMap.2
            ⟨_, hmem, Term.vars_sub_bind (Pat.smaller_mem_vars hsm hw) v hv⟩)

theorem Theory.room_lt {T : Theory} {c : Store} (h : T.newAtoms c ≠ []) :
    T.room (c ++ T.newAtoms c) < T.room c := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  have spec := fun y (hy : y ∈ T.newAtoms c) => Theory.newAtoms_spec hy
  have hS : T.symsOf (c ++ T.newAtoms c) = T.symsOf c := by
    apply le_antisymm
    · intro f hf
      simp only [Theory.symsOf, Finset.mem_union, List.mem_toFinset, List.mem_flatMap,
        List.mem_append] at hf
      rcases hf with ⟨a, ha | ha, hfa⟩ | hf
      · exact Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_flatMap.2 ⟨a, ha, hfa⟩))
      · exact (spec a ha).2.2.1 f hfa
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_flatMap.2 hf))
    · intro f hf
      simp only [Theory.symsOf, Finset.mem_union, List.mem_toFinset, List.mem_flatMap,
        List.mem_append] at hf ⊢
      rcases hf with ⟨a, ha, hfa⟩ | hf
      · exact Or.inl ⟨a, Or.inl ha, hfa⟩
      · exact Or.inr hf
  have hV : (c ++ T.newAtoms c).varSet = c.varSet := by
    apply le_antisymm
    · intro v hv
      simp only [Store.varSet, List.mem_toFinset, List.mem_flatMap, List.mem_append] at hv
      rcases hv with ⟨a, ha | ha, hva⟩
      · exact List.mem_toFinset.2 (List.mem_flatMap.2 ⟨a, ha, hva⟩)
      · exact (spec a ha).2.2.2 v hva
    · intro v hv
      simp only [Store.varSet, List.mem_toFinset, List.mem_flatMap, List.mem_append] at hv ⊢
      obtain ⟨a, ha, hva⟩ := hv
      exact ⟨a, Or.inl ha, hva⟩
  have hM : (c ++ T.newAtoms c).maxSize = c.maxSize := by
    apply le_antisymm
    · apply Store.maxSize_le
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact Store.le_maxSize ha
      · obtain ⟨y, hy, hlt⟩ := (spec a ha).2.1
        exact le_trans hlt.le (Store.le_maxSize hy)
    · exact Store.maxSize_le fun a ha => Store.le_maxSize (List.mem_append_left _ ha)
  unfold Theory.room
  simp only [hS, hV, hM]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨x, ?_, ?_⟩
  · intro y hy
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_append] at hy ⊢
    exact ⟨hy.1, fun h => hy.2 (Or.inl h)⟩
  · simp only [Finset.mem_sdiff, List.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    obtain ⟨hxc, ⟨y, hy, hlt⟩, hs, hv⟩ := spec x hx
    exact ⟨⟨hs, hv, le_trans hlt.le (Store.le_maxSize hy)⟩, hxc⟩
  · simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_append, not_and, not_not]
    exact fun _ => Or.inr hx

/-- The closure of a store under the bounded rules of the theory: add what the
firings derive until a round adds nothing new. -/
def Theory.saturate (T : Theory) (c : Store) : Store :=
  if _ : T.newAtoms c = [] then c else T.saturate (c ++ T.newAtoms c)
termination_by T.room c
decreasing_by exact Theory.room_lt ‹_›

/-- The closure contains the store. -/
theorem Theory.sub_saturate (T : Theory) (c : Store) : ∀ x ∈ c, x ∈ T.saturate c := by
  intro x hx
  rw [Theory.saturate]
  split
  · exact hx
  · exact Theory.sub_saturate T _ x (List.mem_append_left _ hx)
termination_by T.room c
decreasing_by exact Theory.room_lt ‹_›

/-- The closure is closed: no firing on it derives an atom it lacks. -/
theorem Theory.saturate_closed (T : Theory) (c : Store) : T.newAtoms (T.saturate c) = [] := by
  rw [Theory.saturate]
  split
  · assumption
  · exact Theory.saturate_closed T _
termination_by T.room c
decreasing_by exact Theory.room_lt ‹_›

/-- Some firing on the closure refutes the store. -/
def Theory.refutes? (T : Theory) (c : Store) : Bool :=
  (T.firings (T.saturate c)).any fun
    | .refuted => true
    | _ => false

/-- The first equation instantiation a firing on the closure forces. -/
def Theory.bind? (T : Theory) (c : Store) : Option (Nat → Pat) :=
  (T.firings (T.saturate c)).findSome? fun
    | .bind θ => some θ
    | _ => none

/-- Instantiate a span. Atoms that become equal are kept once: a ground store
is a set, so this does not change the span's ground triples. -/
def Span.inst (s : Span) (θ : Nat → Pat) : Span :=
  ⟨s.l.bind θ, s.r.bind θ, (s.c.map (Term.bind θ)).eraseDups⟩

/-- The distinct variables of a store. -/
def Store.varCount (c : Store) : Nat := (c.flatMap Term.vars).eraseDups.length

/-- Simplify with a budget of `n` instantiations: `none` when the span is
refuted. -/
def Theory.simplifyWithin (T : Theory) : Nat → Span → Option Span
  | n, s =>
    if T.refutes? s.c then none
    else match n, T.bind? s.c with
      | n + 1, some θ => T.simplifyWithin n (s.inst θ)
      | _, _ => some ⟨s.l, s.r, s.c.eraseDups⟩

/-- Simplify a span by its theory: drop it when the theory refutes it, and
instantiate it by every equation the theory forces. A store is a set, so each
atom is kept once.

The budget is a bound, not tuning: an instantiation removes a variable of the
store and a firing never adds one, so there are at most as many instantiations
as the store has variables (obligation `Kernel.simplify_stable`). -/
def Theory.simplify (T : Theory) (s : Span) : Option Span :=
  T.simplifyWithin s.c.varCount s

/-! ## Showing an answer

Tables keep stores as written. An answer is shown with its store rewritten:
a firing replaces the matched heads by the rule's body, which keeps the models
of every ground instance, so the shown answer relates the same pairs in every
model (obligation `Kernel.present_exact`). Only firings whose equations already
hold rewrite (a simplified span has no other), only decreasing rules are used,
and a firing is taken only when it lowers `storeWeight`, so rewriting
terminates for every theory. Which normal form is shown can depend on the
order of the store when the theory is not confluent; every one of them means
the same. -/

/-- Replace the matched members `ms` of the store `c` by the atoms `bs`. A
store is a set, so copies are kept once. -/
def Store.replace (c ms bs : Store) : Store :=
  (c.filter (fun a => !ms.contains a) ++ bs).eraseDups

/-- A rule decreases when, once its equations hold (under their most general
unifier `μ`), its body is smaller than its heads in the multiset extension of
`Pat.smaller`: after cancelling the atoms it writes back, some head is left and
every other body atom is smaller than a head that is left. -/
def TRule.decreasing (ρ : TRule) : Bool :=
  match ρ.body with
  | .fail => false
  | .conj eqs cs =>
    match solve eqs with
    | none => false
    | some μ =>
      let H := ρ.heads.map (Term.bind μ)
      let B := cs.map (Term.bind μ)
      let H' := H.diff B
      !H'.isEmpty && (B.diff H).all fun b => H'.any fun h => Pat.smaller b h

/-- The stores one rule rewrites a store to, one for each match of its heads
under which its equations hold. -/
def TRule.rewrites (ρ : TRule) (c : Store) : List Store :=
  match ρ.body with
  | .fail => []
  | .conj eqs cs =>
    (matchAll ρ.heads c []).filterMap fun r =>
      if eqs.all fun e => e.1.bind r.1.apply = e.2.bind r.1.apply then
        some (c.replace r.2 (cs.map (Term.bind r.1.apply)))
      else none

/-- The largest number of atoms a rule body adds, plus one. -/
def Theory.base (T : Theory) : Nat :=
  1 + T.foldl (fun m ρ => max m ρ.body.atoms.length) 0

/-- The measure a rewrite must lower to be taken: each atom of size `n` weighs
`base ^ n`, so trading an atom for fewer than `base` strictly smaller ones
lowers it. -/
def Theory.storeWeight (T : Theory) (c : Store) : Nat := (c.map fun a => T.base ^ a.size).sum

/-- The first weight-lowering rewrite of the store by a decreasing rule. -/
def Theory.step? (T : Theory) (c : Store) :
    Option {c' : Store // T.storeWeight c' < T.storeWeight c} :=
  T.findSome? fun ρ =>
    if ρ.decreasing then
      (ρ.rewrites c).findSome? fun c' =>
        if h : T.storeWeight c' < T.storeWeight c then some ⟨c', h⟩ else none
    else none

/-- Rewrite until no weight-lowering rewrite is left. -/
def Theory.normalize (T : Theory) (c : Store) : Store :=
  match T.step? c with
  | none => c
  | some c' => T.normalize c'.1
termination_by T.storeWeight c
decreasing_by exact c'.2

/-- The answer as shown: its store rewritten by the theory. -/
def Theory.present (T : Theory) (s : Span) : Span := ⟨s.l, s.r, T.normalize s.c⟩

end RwLog
