/-
# The normal store of a problem, as a function

`Prob.norm S hS P` is the normal store that denotes what the first-order
problem `P` denotes (`Prob.norm_some`); there is none exactly when `P`
denotes nothing (`Prob.norm_none`). A normal store is determined by what it
denotes (`Raw.Normal.eq`), so this is the only one (`Prob.norm_unique`).

The steps:

1. `Prob.start` solves the equations and applies the solution, brings the
   sorts of patterns down to sorts of variables, and pairs the pattern with
   a tuple of all the variables, so that every variable occurs in it.
2. `CStore.settle` replaces each variable whose sorts have one member.
3. `tighten` replaces variables whose values have one root until none is
   left, and stops when the store denotes nothing.
4. `ofTight` numbers the variables in the order they first occur, gives
   each the sorts that hold of all its values, and puts the exclusions in
   normal form (`assembled`).
5. `Raw.cut` keeps the first part of the pattern.
-/
import RwLog.Sorts.Tightened
import RwLog.Sorts.Hidden
import RwLog.Sorts.Reduce

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-! ## From a tight store -/

/-- The normal store of a tight store that satisfies `Inv`. -/
def ofTight (S : Sorts) (s : CStore) : Raw :=
  assembled S (s.t.rename fun v => (firsts s.t.vars).idxOf v)
    ((firsts s.t.vars).map fun v =>
      (names S).filter fun n => inclBut S (s.conj v) n (gone s.x v))
    (s.x.map (Eqns.ren fun v => (firsts s.t.vars).idxOf v))

theorem ofTight_normal (hS : S.WellFormed) {s : CStore} (hI : Inv S s)
    (hsole : ∀ v ∈ s.t.vars, sole S (s.conj v) (gone s.x v) = none) :
    (ofTight S s).Normal S ∧ (ofTight S s).store.Den S = s.store.Den S := by
  obtain ⟨hocc, h₁, h₂⟩ := renum_spec s.t.vars
  let ρ : Nat → Nat := fun v => (firsts s.t.vars).idxOf v
  let ρ' : Nat → Nat := fun w => (firsts s.t.vars).getD w 0
  have hinv : ∀ v ∈ s.store.t.vars, ρ' (ρ v) = v := fun v hv => (h₁ v hv).2
  have hfull := hI.full
  have hfin₃ : (s.store.ren ρ ρ').Fin (firsts s.t.vars).length :=
    ren_fin hI.fin hfull fun v hv => (h₁ v hv).1
  have ht₃ : (s.store.ren ρ ρ').Tight S :=
    ren_tight hfull hinv (tight_of_sole hS hI hsole)
  have hden₃ : (s.store.ren ρ ρ').Den S = s.store.Den S := ren_den hfull hinv
  have hocc₃ : FirstOcc (s.store.ren ρ ρ').t.vars := by
    show FirstOcc (s.t.rename ρ).vars
    rw [Term.vars_rename]; exact hocc
  have hv₃ : ∀ w, w ∈ (s.store.ren ρ ρ').t.vars ↔ w < (firsts s.t.vars).length := by
    intro w
    show w ∈ (s.t.rename ρ).vars ↔ _
    rw [Term.vars_rename]
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      exact (h₁ v hv).1
    · intro hw
      obtain ⟨hm, e⟩ := h₂ w hw
      rw [← e]; exact List.mem_map_of_mem hm
  obtain ⟨σ, hσ⟩ := hI.sol hS
  have hcL : ∀ w n,
      n ∈ ((firsts s.t.vars).map fun v =>
        (names S).filter fun n => inclBut S (s.conj v) n (gone s.x v)).getD w ∅ ↔
      w < (firsts s.t.vars).length ∧ n ∈ names S ∧
        ∀ σ ∈ (s.store.ren ρ ρ').Sol S, mem S n (σ w) = true := by
    intro w n
    by_cases hw : w < (firsts s.t.vars).length
    · have e : ((firsts s.t.vars).map fun v =>
          (names S).filter fun n => inclBut S (s.conj v) n (gone s.x v)).getD w ∅ =
          (names S).filter fun n => inclBut S (s.conj (ρ' w)) n (gone s.x (ρ' w)) := by
        simp [List.getD_eq_getElem?_getD, hw, ρ']
      rw [e, Finset.mem_filter, hI.inclBut_iff hS]
      constructor
      · rintro ⟨hn, h⟩
        refine ⟨hw, hn, fun σ' hσ' => ?_⟩
        have := h _ (ren_bwd hfull hinv hσ').1
        have e' : ρ (ρ' w) = w := (h₂ w hw).2
        simpa only [comp_apply, e'] using this
      · rintro ⟨-, hn, h⟩
        exact ⟨hn, fun σ hσ => h _ (ren_fwd hfull hinv hσ).1⟩
    · simp [List.getD_eq_getElem?_getD, hw]
  obtain ⟨hN, hsol⟩ := assembled_normal hS hfin₃ ht₃ hocc₃ hv₃
    ⟨_, (ren_fwd hfull hinv hσ).1⟩ (by simp) hcL
  refine ⟨hN, ?_⟩
  rw [← hden₃]
  show {g | ∃ σ ∈ (ofTight S s).store.Sol S, g = _} = {g | ∃ σ ∈ Store.Sol S _, g = _}
  rw [show (ofTight S s).store.Sol S = _ from hsol]
  rfl

/-! ## From a problem to a store -/

/-- The store of a problem: its equations solved, its sorts on variables,
and its pattern paired with a tuple of all the variables. Nothing when the
equations have no solution or a sort rejects its pattern. -/
def Prob.start (S : Sorts) (P : Prob) : Option CStore :=
  (solve P.e).bind fun θ =>
    (pushAll S (P.a.map fun a => (a.1, a.2.bind θ))).map fun As =>
      ⟨tpair (P.t.bind θ)
          (tup (bound ((P.t.bind θ).vars ++ As.map Prod.fst ++
            (P.x.map fun E => E.map fun p => (p.1.bind θ, p.2.bind θ)).flatMap Eqns.vars))),
        (List.range (bound ((P.t.bind θ).vars ++ As.map Prod.fst ++
            (P.x.map fun E => E.map fun p => (p.1.bind θ, p.2.bind θ)).flatMap Eqns.vars))).map
          fun v => ((As.filter fun a => a.1 = v).map Prod.snd).toFinset,
        P.x.map fun E => E.map fun p => (p.1.bind θ, p.2.bind θ)⟩

theorem Prob.start_none {P : Prob} (hP : P.FO) (h : P.start S = none) : P.Den S = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨σ, hσ, -⟩
  unfold Prob.start at h
  cases hsolve : solve P.e with
  | none => exact solve_none hsolve σ hσ.1
  | some θ =>
    rw [hsolve] at h
    simp only [Option.bind_some, Option.map_eq_none_iff] at h
    have hθfo := solve_fo P.e hP.e θ hsolve
    refine pushAll_none (S := S) (L := P.a.map fun a => (a.1, a.2.bind θ)) ?_ h σ ?_
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      exact Term.fo_bind (hP.a a' ha') fun v _ => hθfo v
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      show mem S a'.1 ((a'.2.bind θ).bind σ) = true
      rw [Term.bind_bind, show (fun v => (θ v).bind σ) = σ from
        funext ((solve_some hsolve).2 σ hσ.1)]
      exact hσ.2.1 a' ha'

/-- The store of a problem has all its variables in its pattern, denotes
pairs, and the first parts of the pairs are what the problem denotes. -/
theorem Prob.start_some {P : Prob} {s : CStore} (hP : P.FO) (h : P.start S = some s) :
    s.store.Fin s.c.length ∧ s.store.Full ∧
      (∀ g ∈ s.store.Den S, ∃ x y, g = tpair x y) ∧
      P.Den S = {x | ∃ y, tpair x y ∈ s.store.Den S} := by
  unfold Prob.start at h
  cases hsolve : solve P.e with
  | none => rw [hsolve] at h; cases h
  | some θ =>
    rw [hsolve] at h
    simp only [Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨As, hpush, rfl⟩ := h
    obtain ⟨hθu, hθm⟩ := solve_some hsolve
    have hθfo := solve_fo P.e hP.e θ hsolve
    have fix : ∀ σ : Nat → GTerm, Eqns.Unifies σ P.e → (fun v => (θ v).bind σ) = σ :=
      fun σ hσ => funext (hθm σ hσ)
    have bb : ∀ (q : Pat) (τ : Nat → GTerm), (q.bind θ).bind τ = q.bind fun v => (θ v).bind τ :=
      fun q τ => Term.bind_bind _ _ _
    have uni : ∀ τ : Nat → GTerm, Eqns.Unifies (fun v => (θ v).bind τ) P.e := by
      intro τ p hp
      rw [← bb, ← bb, hθu p hp]
    have hL : ∀ τ : Nat → GTerm,
        (∀ a ∈ P.a.map fun a => (a.1, a.2.bind θ), mem S a.1 (a.2.bind τ) = true) ↔
        ∀ a ∈ P.a, mem S a.1 (a.2.bind fun v => (θ v).bind τ) = true := by
      intro τ
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, bb]
    have hAs := pushAll_some (S := S) (L := P.a.map fun a => (a.1, a.2.bind θ)) (As := As)
      (by
        intro a ha
        obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
        exact Term.fo_bind (hP.a a' ha') fun v _ => hθfo v) hpush
    generalize hx' : (P.x.map fun E => E.map fun p => (p.1.bind θ, p.2.bind θ)) = x' at *
    generalize hN : bound ((P.t.bind θ).vars ++ As.map Prod.fst ++ x'.flatMap Eqns.vars) = N
    have hx : ∀ (τ : Nat → GTerm) (E : Eqns Nat),
        Eqns.Unifies τ (E.map fun p => (p.1.bind θ, p.2.bind θ)) ↔
          Eqns.Unifies (fun v => (θ v).bind τ) E := by
      intro τ E
      simp only [Eqns.Unifies, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, bb]
    have hconj : ∀ (v : Nat) (n : Name),
        n ∈ ((List.range N).map fun v =>
          ((As.filter fun a => a.1 = v).map Prod.snd).toFinset).getD v ∅ ↔ (v, n) ∈ As := by
      intro v n
      rw [getD_map_range]
      constructor
      · intro hn
        split at hn
        · simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hn
          obtain ⟨a, ⟨ha, hav⟩, rfl⟩ := hn
          simp only [decide_eq_true_eq] at hav
          rw [← hav]; exact ha
        · simp at hn
      · intro ha
        have hv : v < N := by
          rw [← hN]
          exact lt_bound (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map_of_mem (f := Prod.fst) ha)))
        simp only [hv, ↓reduceIte, List.mem_toFinset, List.mem_map, List.mem_filter]
        exact ⟨(v, n), ⟨ha, by simp⟩, rfl⟩
    have hc : ∀ τ : Nat → GTerm,
        (∀ v, MemC S (((List.range N).map fun v =>
          ((As.filter fun a => a.1 = v).map Prod.snd).toFinset).getD v ∅) (τ v)) ↔
          Atoms.Holds S As τ := by
      intro τ
      constructor
      · intro h a ha
        exact h a.1 a.2 ((hconj a.1 a.2).2 ha)
      · intro h v n hn
        exact h (v, n) ((hconj v n).1 hn)
    have hlen : ((List.range N).map fun v =>
        ((As.filter fun a => a.1 = v).map Prod.snd).toFinset).length = N := by simp
    have hvar : ∀ v, v < N → v ∈ (tpair (P.t.bind θ) (tup N)).vars := fun v hv => by
      rw [tpair_vars]; exact List.mem_append_right _ (mem_tup_vars.2 hv)
    have hxv : ∀ E ∈ x', ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, v < N := by
      intro E hE p hp v hv
      rw [← hN]
      exact lt_bound (List.mem_append_right _
        (List.mem_flatMap.2 ⟨E, hE, List.mem_flatMap.2 ⟨p, hp, hv⟩⟩))
    have hcv : ∀ v, N ≤ v → ((List.range N).map fun v =>
        ((As.filter fun a => a.1 = v).map Prod.snd).toFinset).getD v ∅ = ∅ := by
      intro v hv
      rw [getD_map_range]
      simp [Nat.not_lt.2 hv]
    have key₁ : ∀ τ ∈ (CStore.mk (tpair (P.t.bind θ) (tup N)) ((List.range N).map fun v =>
        ((As.filter fun a => a.1 = v).map Prod.snd).toFinset) x').store.Sol S,
        (fun v => (θ v).bind τ) ∈ P.Sol S := by
      intro τ hτ
      refine ⟨uni τ, (hL τ).1 ((hAs τ).2 ((hc τ).1 hτ.1)), fun E hE hu => ?_⟩
      refine hτ.2 (E.map fun p => (p.1.bind θ, p.2.bind θ)) ?_ ((hx τ E).2 hu)
      rw [← hx']; exact List.mem_map_of_mem hE
    have key₂ : ∀ σ ∈ P.Sol S,
        σ ∈ (CStore.mk (tpair (P.t.bind θ) (tup N)) ((List.range N).map fun v =>
          ((As.filter fun a => a.1 = v).map Prod.snd).toFinset) x').store.Sol S := by
      intro σ hσ
      have e := fix σ hσ.1
      refine ⟨(hc σ).2 ((hAs σ).1 ((hL σ).2 (by rw [e]; exact hσ.2.1))), fun E' hE' hu => ?_⟩
      rw [← hx'] at hE'
      obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
      rw [hx, e] at hu
      exact hσ.2.2 E hE hu
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hlen]
      refine ⟨?_, ?_, hcv, ?_, hxv⟩
      · show (tpair (P.t.bind θ) (tup N)).firstOrder = true
        rw [tpair_fo, Term.fo_bind hP.t fun v _ => hθfo v, tup_fo]; rfl
      · intro v hv
        change v ∈ (tpair (P.t.bind θ) (tup N)).vars at hv
        rw [tpair_vars, List.mem_append, mem_tup_vars] at hv
        rcases hv with hv | hv
        · rw [← hN]
          exact lt_bound (List.mem_append_left _ (List.mem_append_left _ hv))
        · exact hv
      · intro E' hE' q hq
        rw [← hx'] at hE'
        obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        exact ⟨Term.fo_bind (hP.x E hE p hp).1 fun v _ => hθfo v,
          Term.fo_bind (hP.x E hE p hp).2 fun v _ => hθfo v⟩
    · exact ⟨fun v hv => hcv v (by by_contra hlt; exact hv (hvar v (by omega))),
        fun E hE p hp v hv => hvar v (hxv E hE p hp v hv)⟩
    · rintro g ⟨τ, -, rfl⟩
      exact ⟨_, _, tpair_bind τ _ _⟩
    · ext g
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        refine ⟨(tup N).bind σ, σ, key₂ σ hσ, ?_⟩
        show _ = (tpair (P.t.bind θ) (tup N)).bind σ
        rw [tpair_bind, bb, fix σ hσ.1]
      · rintro ⟨y, τ, hτ, e⟩
        have e' : tpair g y = tpair ((P.t.bind θ).bind τ) ((tup N).bind τ) :=
          e.trans (tpair_bind τ _ _)
        exact ⟨_, key₁ τ hτ, by rw [(tpair_inj e').1, bb]⟩

/-- The variables of a problem once its equations are solved by `θ`. -/
def Prob.occ (P : Prob) (θ : Nat → Pat) : List Nat :=
  (P.t.bind θ).vars ++ (P.a.flatMap fun a => (a.2.bind θ).vars) ++
    P.x.flatMap fun E => E.flatMap fun p => (p.1.bind θ).vars ++ (p.2.bind θ).vars

/-- A solution of the equations of a problem, read after the equations are
solved and the variables that are left renamed one to one: a substitution
that gives each part of the problem, solved and renamed, the value the
solution gives it. -/
theorem Prob.begin_back {P : Prob} {θ : Nat → Pat} (hsolve : solve P.e = some θ)
    {ρ : Nat → Nat} (hinj : ∀ v ∈ P.occ θ, ∀ w ∈ P.occ θ, ρ v = ρ w → v = w)
    {σ : Nat → GTerm} (hσ : Eqns.Unifies σ P.e) :
    ∃ τ : Nat → GTerm, ∀ q : Pat, (∀ v ∈ (q.bind θ).vars, v ∈ P.occ θ) →
      ((q.bind θ).rename ρ).bind τ = q.bind σ := by
  classical
  let τ : Nat → GTerm := fun w =>
    if h : ∃ v, v ∈ P.occ θ ∧ ρ v = w then σ h.choose else σ w
  have hτ : ∀ v ∈ P.occ θ, τ (ρ v) = σ v := by
    intro v hv
    have h : ∃ u, u ∈ P.occ θ ∧ ρ u = ρ v := ⟨v, hv, rfl⟩
    show (if h : ∃ u, u ∈ P.occ θ ∧ ρ u = ρ v then σ h.choose else σ (ρ v)) = σ v
    rw [dite_eq_left_of_eq_true (eq_true h), hinj _ h.choose_spec.1 v hv h.choose_spec.2]
  refine ⟨τ, fun q hq => ?_⟩
  have rb : ((q.bind θ).rename ρ).bind τ = (q.bind θ).bind (τ ∘ ρ) := Term.bind_bind _ _ _
  rw [rb, Term.bind_congr (σ := τ ∘ ρ) (τ := σ) fun v hv => hτ v (hq v hv), Term.bind_bind,
    show (fun v => (θ v).bind σ) = σ from funext ((solve_some hsolve).2 σ hσ)]

/-- Any store built from a problem as follows denotes pairs whose first
parts are what the problem denotes: solve the equations, rename the
variables that are left one to one below `n`, pair the pattern with the
tuple of the first `n` variables, and give the variables sorts that hold
exactly when the sorts of the problem do. -/
theorem Prob.begin_spec {P : Prob} (hP : P.FO) {θ : Nat → Pat} (hsolve : solve P.e = some θ)
    {ρ : Nat → Nat} {n : Nat}
    (hinj : ∀ v ∈ P.occ θ, ∀ w ∈ P.occ θ, ρ v = ρ w → v = w)
    (hn : ∀ v ∈ P.occ θ, ρ v < n) {s : Store}
    (ht : s.t = tpair ((P.t.bind θ).rename ρ) (tup n))
    (hx : s.x = P.x.map fun E => E.map fun p =>
      ((p.1.bind θ).rename ρ, (p.2.bind θ).rename ρ))
    (hc : ∀ τ : Nat → GTerm, τ ∈ s.Pos S ↔
      ∀ a ∈ P.a, mem S a.1 (((a.2.bind θ).rename ρ).bind τ) = true)
    (hcv : ∀ v, n ≤ v → s.c v = ∅) :
    s.Fin n ∧ s.Full ∧ (∀ g ∈ s.Den S, ∃ x y, g = tpair x y) ∧
      P.Den S = {x | ∃ y, tpair x y ∈ s.Den S} := by
  obtain ⟨hθu, hθm⟩ := solve_some hsolve
  have hθfo := solve_fo P.e hP.e θ hsolve
  have fix : ∀ σ : Nat → GTerm, Eqns.Unifies σ P.e → (fun v => (θ v).bind σ) = σ :=
    fun σ hσ => funext (hθm σ hσ)
  have bb : ∀ (q : Pat) (τ : Nat → GTerm), (q.bind θ).bind τ = q.bind fun v => (θ v).bind τ :=
    fun q τ => Term.bind_bind _ _ _
  have uni : ∀ τ : Nat → GTerm, Eqns.Unifies (fun v => (θ v).bind τ) P.e := by
    intro τ p hp
    rw [← bb, ← bb, hθu p hp]
  have rfo : ∀ q : Pat, q.firstOrder = true → ((q.bind θ).rename ρ).firstOrder = true :=
    fun q hq => Term.fo_bind (Term.fo_bind hq fun v _ => hθfo v) fun _ _ => rfl
  have ot : ∀ v ∈ (P.t.bind θ).vars, v ∈ P.occ θ := fun v hv =>
    List.mem_append_left _ (List.mem_append_left _ hv)
  have oa : ∀ a ∈ P.a, ∀ v ∈ (a.2.bind θ).vars, v ∈ P.occ θ := fun a ha v hv =>
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, hv⟩))
  have ox : ∀ E ∈ P.x, ∀ p ∈ E, ∀ v ∈ (p.1.bind θ).vars ++ (p.2.bind θ).vars, v ∈ P.occ θ :=
    fun E hE p hp v hv =>
      List.mem_append_right _ (List.mem_flatMap.2 ⟨E, hE, List.mem_flatMap.2 ⟨p, hp, hv⟩⟩)
  have hvar : ∀ v, v < n → v ∈ s.t.vars := fun v hv => by
    rw [ht, tpair_vars]; exact List.mem_append_right _ (mem_tup_vars.2 hv)
  have hxv : ∀ E ∈ s.x, ∀ p ∈ E, ∀ v ∈ p.1.vars ++ p.2.vars, v < n := by
    intro E' hE' q hq v hv
    rw [hx] at hE'
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    simp only [Term.vars_rename, ← List.map_append] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    exact hn w (ox E hE p hp w hw)
  have rb : ∀ (τ : Nat → GTerm) (q : Pat), (q.rename ρ).bind τ = q.bind (τ ∘ ρ) :=
    fun τ q => Term.bind_bind _ _ _
  -- A substitution after the renaming, read before it.
  have back : ∀ (τ : Nat → GTerm) (q : Pat),
      ((q.bind θ).rename ρ).bind τ = q.bind fun v => (θ v).bind (τ ∘ ρ) :=
    fun τ q => by rw [rb, bb]
  refine ⟨⟨?_, ?_, hcv, ?_, hxv⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [ht, tpair_fo, rfo _ hP.t, tup_fo]; rfl
  · intro v hv
    rw [ht, tpair_vars, List.mem_append, mem_tup_vars, Term.vars_rename] at hv
    rcases hv with hv | hv
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      exact hn w (ot w hw)
    · exact hv
  · intro E' hE' q hq
    rw [hx] at hE'
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨rfo _ (hP.x E hE p hp).1, rfo _ (hP.x E hE p hp).2⟩
  · exact fun v hv => hcv v (by by_contra hlt; exact hv (hvar v (by omega)))
  · exact fun E hE p hp v hv => hvar v (hxv E hE p hp v hv)
  · rintro g ⟨τ, -, rfl⟩
    rw [ht]
    exact ⟨_, _, tpair_bind τ _ _⟩
  · ext g
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨τ, fwd⟩ := Prob.begin_back hsolve hinj hσ.1
      have hsol : τ ∈ s.Sol S := by
        refine ⟨(hc τ).2 fun a ha => ?_, fun E' hE' hu => ?_⟩
        · rw [fwd _ (oa a ha)]; exact hσ.2.1 a ha
        · rw [hx] at hE'
          obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
          refine hσ.2.2 E hE fun p hp => ?_
          have := hu _ (List.mem_map_of_mem (f := fun p : Pat × Pat =>
            ((p.1.bind θ).rename ρ, (p.2.bind θ).rename ρ)) hp)
          simp only at this
          rw [fwd _ fun v hv => ox E hE p hp v (List.mem_append_left _ hv),
            fwd _ fun v hv => ox E hE p hp v (List.mem_append_right _ hv)] at this
          exact this
      refine ⟨(tup n).bind τ, τ, hsol, ?_⟩
      rw [ht, tpair_bind, fwd _ ot]
    · rintro ⟨y, τ, hτ, e⟩
      have e' : tpair g y = tpair (((P.t.bind θ).rename ρ).bind τ) ((tup n).bind τ) := by
        rw [e, ht]; exact tpair_bind τ _ _
      refine ⟨fun v => (θ v).bind (τ ∘ ρ), ⟨uni _, fun a ha => ?_, fun E hE hu => ?_⟩, ?_⟩
      · rw [← back]; exact (hc τ).1 hτ.1 a ha
      · refine hτ.2 _ (by rw [hx]; exact List.mem_map_of_mem hE) fun q hq => ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        show ((p.1.bind θ).rename ρ).bind τ = ((p.2.bind θ).rename ρ).bind τ
        rw [back, back]; exact hu p hp
      · rw [(tpair_inj e').1, back]

/-! ## The normal store -/

/-- The first part of a pair of patterns. -/
def left : Pat → Pat
  | .app (.app _ a) _ => a
  | t => t

/-- The normal store of a problem; nothing when it denotes nothing. -/
def Prob.norm (S : Sorts) (hS : S.WellFormed) (P : Prob) : Option Raw :=
  (P.start S).bind fun s =>
    (tighten S hS (s.settle S (List.range s.c.length))).map fun s' =>
      (ofTight S s').cut (left (ofTight S s').t) (width (left (ofTight S s').t))

theorem Prob.norm_none (hS : S.WellFormed) {P : Prob} (hP : P.FO)
    (h : P.norm S hS = none) : P.Den S = ∅ := by
  unfold Prob.norm at h
  cases hs : P.start S with
  | none => exact Prob.start_none hP hs
  | some s =>
    rw [hs] at h
    simp only [Option.bind_some, Option.map_eq_none_iff] at h
    obtain ⟨hfin, hfull, -, hfst⟩ := Prob.start_some hP hs
    obtain ⟨hden, hlen, hfin', hfull', -, hsub, hnot⟩ :=
      settle_spec S (List.range s.c.length) s
    have hkept : Kept S (s.settle S (List.range s.c.length)) :=
      ⟨by rw [hlen]; exact hfin' hfin, hfull' hfull, fun v hv =>
        hnot v (List.mem_range.2 (hfin.tv v (hsub v hv).1)) hv⟩
    have := tighten_none hS _ _ rfl hkept h
    rw [hfst, ← hden, this]
    simp

theorem Prob.norm_some (hS : S.WellFormed) {P : Prob} {r : Raw} (hP : P.FO)
    (h : P.norm S hS = some r) : r.Normal S ∧ r.store.Den S = P.Den S := by
  unfold Prob.norm at h
  cases hs : P.start S with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    simp only [Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨s', ht, rfl⟩ := h
    obtain ⟨-, -, hpairs, hfst⟩ := Prob.start_some hP hs
    obtain ⟨hden, -⟩ := settle_spec S (List.range s.c.length) s
    obtain ⟨hden', hI, hsole⟩ := tighten_some hS _ _ _ rfl ht
    obtain ⟨hN, hdenN⟩ := ofTight_normal hS hI hsole
    have hD : (ofTight S s').store.Den S = s.store.Den S := by rw [hdenN, hden', hden]
    obtain ⟨a, b, hab⟩ := shape_pair hN (hN.sol_nonempty hS) (by rw [hD]; exact hpairs)
    have hl : left (ofTight S s').t = a := by rw [hab]; rfl
    rw [hl]
    obtain ⟨hN', hden''⟩ := hN.proj hS hab
    refine ⟨hN', ?_⟩
    ext g
    rw [hden'', hfst, ← hD]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨b.bind σ, σ, hσ, by show _ = (ofTight S s').t.bind σ; rw [hab, tpair_bind]⟩
    · rintro ⟨y, σ, hσ, e⟩
      have e' : tpair g y = tpair (a.bind σ) (b.bind σ) := by
        rw [e]; show (ofTight S s').t.bind σ = _; rw [hab, tpair_bind]
      exact ⟨σ, hσ, (tpair_inj e').1⟩

/-- The normal store of a problem is the only normal store that denotes what
the problem does. -/
theorem Prob.norm_unique (hS : S.WellFormed) {P : Prob} {r : Raw} (hP : P.FO)
    (hr : r.Normal S) (hden : r.store.Den S = P.Den S) : P.norm S hS = some r := by
  cases h : P.norm S hS with
  | none =>
    have := Prob.norm_none hS hP h
    obtain ⟨σ, hσ⟩ := hr.sol_nonempty hS
    have hm : r.t.bind σ ∈ r.store.Den S := ⟨σ, hσ, rfl⟩
    rw [hden, this] at hm
    exact absurd hm (Set.notMem_empty _)
  | some r' =>
    obtain ⟨hr', hden'⟩ := Prob.norm_some hS hP h
    rw [Raw.Normal.eq hS hr' hr (hden'.trans hden.symm)]

/-- A problem that denotes nothing has no normal store. -/
theorem Prob.norm_of_empty (hS : S.WellFormed) {P : Prob} (hP : P.FO) (h : P.Den S = ∅) :
    P.norm S hS = none := by
  cases hn : P.norm S hS with
  | none => rfl
  | some r =>
    obtain ⟨hr, hden⟩ := Prob.norm_some hS hP hn
    obtain ⟨σ, hσ⟩ := hr.sol_nonempty hS
    have hm : r.t.bind σ ∈ r.store.Den S := ⟨σ, hσ, rfl⟩
    rw [hden, h] at hm
    exact absurd hm (Set.notMem_empty _)

/-- Problems that denote the same have the same normal store. -/
theorem Prob.norm_congr (hS : S.WellFormed) {P P' : Prob} (hP : P.FO) (hP' : P'.FO)
    (h : P.Den S = P'.Den S) : P.norm S hS = P'.norm S hS := by
  cases hn : P.norm S hS with
  | none => exact (Prob.norm_of_empty hS hP' (by rw [← h]; exact Prob.norm_none hS hP hn)).symm
  | some r =>
    obtain ⟨hr, hden⟩ := Prob.norm_some hS hP hn
    exact (Prob.norm_unique hS hP' hr (hden.trans h)).symm

/-- The normal store of a problem, read off any tight store that denotes
pairs whose first parts are what the problem denotes: the pattern of its
normal store is a pair, and the first part of it, with its variables and
exclusions, is the normal store of the problem. -/
theorem Prob.norm_of_tight (hS : S.WellFormed) {P : Prob} (hP : P.FO) {s : CStore}
    (hpairs : ∀ g ∈ s.store.Den S, ∃ x y, g = tpair x y)
    (hfst : P.Den S = {x | ∃ y, tpair x y ∈ s.store.Den S}) (hI : Inv S s)
    (hsole : ∀ v ∈ s.t.vars, sole S (s.conj v) (gone s.x v) = none) :
    ∃ a b, (ofTight S s).t = tpair a b ∧
      P.norm S hS = some ((ofTight S s).cut a (width a)) := by
  obtain ⟨hN, hD⟩ := ofTight_normal hS hI hsole
  obtain ⟨a, b, hab⟩ := shape_pair hN (hN.sol_nonempty hS) (by rw [hD]; exact hpairs)
  refine ⟨a, b, hab, ?_⟩
  obtain ⟨hN', hden''⟩ := hN.proj hS hab
  refine Prob.norm_unique hS hP hN' ?_
  ext g
  rw [hden'', hfst, ← hD]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨b.bind σ, σ, hσ, by show _ = (ofTight S s).t.bind σ; rw [hab, tpair_bind]⟩
  · rintro ⟨y, σ, hσ, e⟩
    have e' : tpair g y = tpair (a.bind σ) (b.bind σ) := by
      rw [e]; show (ofTight S s).t.bind σ = _; rw [hab, tpair_bind]
    exact ⟨σ, hσ, (tpair_inj e').1⟩

/-- A first-order problem with a solution has a normal store that denotes the
same terms. -/
theorem Prob.normal (hS : S.WellFormed) {P : Prob} (hP : P.FO)
    (hne : (P.Den S).Nonempty) : ∃ r : Raw, r.Normal S ∧ r.store.Den S = P.Den S := by
  cases h : P.norm S hS with
  | none => rw [Prob.norm_none hS hP h] at hne; exact absurd hne Set.not_nonempty_empty
  | some r => exact ⟨r, Prob.norm_some hS hP h⟩

end Sorts
end RwLog
