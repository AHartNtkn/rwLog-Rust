/-
# Numbering the variables of a store

The variables of a normal store are numbered in the order they first occur
in its pattern. A store all of whose variables occur in its pattern can be
renamed to that numbering (`firsts`, `renum_spec`, `Store.ren`) without
changing what it denotes (`ren_den`).
-/
import RwLog.Sorts.Tight
import RwLog.Lib.Firsts
import RwLog.Sorts.Normal
import RwLog.Kernel.SolveFacts
import RwLog.Kernel.Span

namespace RwLog
namespace Sorts

open Function

theorem firstOcc_iff {L : List Nat} : FirstOcc L ↔
    ∀ (i m v : Nat), L[i]? = some v → m < v → ∃ j, j < i ∧ L[j]? = some m := by
  constructor
  · intro H i m v hv hm
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hv
    obtain ⟨j, hj, e⟩ := H i h m hm
    exact ⟨j, hj, List.getElem?_eq_some_iff.2 ⟨by omega, e⟩⟩
  · intro H i h m hm
    obtain ⟨j, hj, e⟩ := H i m L[i] (List.getElem?_eq_getElem h) hm
    obtain ⟨_, e'⟩ := List.getElem?_eq_some_iff.1 e
    exact ⟨j, hj, e'⟩

/-- The members of a list, each replaced by its place among the members in
the order they first occur, are numbered in the order they first occur. -/
theorem firstOcc_map_firsts {α : Type} [DecidableEq α] (L : List α) :
    FirstOcc (L.map fun v => (firsts L).idxOf v) := by
  obtain ⟨-, -, hF⟩ := firsts_spec L
  rw [firstOcc_iff]
  intro i m v' hv' hm
  rw [List.getElem?_map, Option.map_eq_some_iff] at hv'
  obtain ⟨v, hv, rfl⟩ := hv'
  obtain ⟨j, hj, u, hu, e⟩ := hF i m v hv hm
  exact ⟨j, hj, by rw [List.getElem?_map, hu]; simp [e]⟩

/-- Numbering the members of a list in the order they first occur, with its
inverse. -/
theorem renum_spec (L : List Nat) : FirstOcc (L.map fun v => (firsts L).idxOf v) ∧
    (∀ v ∈ L, (firsts L).idxOf v < (firsts L).length ∧
      (firsts L).getD ((firsts L).idxOf v) 0 = v) ∧
    ∀ w, w < (firsts L).length →
      (firsts L).getD w 0 ∈ L ∧ (firsts L).idxOf ((firsts L).getD w 0) = w := by
  obtain ⟨hnd, hmem, -⟩ := firsts_spec L
  refine ⟨firstOcc_map_firsts L, ?_, ?_⟩
  all_goals generalize firsts L = F at hnd hmem ⊢
  · intro v hv
    have hvF : v ∈ F := (hmem v).2 hv
    have hlt : F.idxOf v < F.length := List.idxOf_lt_length_iff.2 hvF
    refine ⟨hlt, ?_⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  · intro w hw
    have e : F.getD w 0 = F[w] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]
    show F.getD w 0 ∈ L ∧ F.idxOf (F.getD w 0) = w
    rw [e]
    exact ⟨(hmem _).1 (List.getElem_mem hw), hnd.idxOf_getElem w hw⟩

/-- A store with its variables renamed by `ρ`; `ρ'` undoes `ρ` on the
variables of the pattern. -/
def Store.ren (s : Store) (ρ ρ' : Nat → Nat) : Store :=
  ⟨s.t.rename ρ, fun w => if w ∈ s.t.vars.map ρ then s.c (ρ' w) else ∅, s.x.map (Eqns.ren ρ)⟩

theorem memC_empty (S : Sorts) (g : GTerm) : MemC S ∅ g := fun n hn => by simp at hn

theorem unifies_ren {ρ : Nat → Nat} {σ : Nat → GTerm} {E : Eqns Nat} :
    Eqns.Unifies σ (Eqns.ren ρ E) ↔ Eqns.Unifies (σ ∘ ρ) E := by
  constructor
  · intro h p hp
    have := h (p.1.rename ρ, p.2.rename ρ) (List.mem_map.2 ⟨p, hp, rfl⟩)
    simpa only [rename_bind] using this
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    simpa only [rename_bind] using h p hp

section ren

variable {S : Sorts} {s : Store} {ρ ρ' : Nat → Nat}

theorem ren_fwd (hfull : s.Full) (hinv : ∀ v ∈ s.t.vars, ρ' (ρ v) = v) {σ : Nat → GTerm}
    (hσ : σ ∈ s.Sol S) :
    σ ∘ ρ' ∈ (s.ren ρ ρ').Sol S ∧ (s.ren ρ ρ').t.bind (σ ∘ ρ') = s.t.bind σ := by
  have hb : ∀ q : Pat, (∀ v ∈ q.vars, v ∈ s.t.vars) → q.bind ((σ ∘ ρ') ∘ ρ) = q.bind σ :=
    fun q hq => Term.bind_congr fun v hv => by simp [hinv v (hq v hv)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro w
    show MemC S (if w ∈ s.t.vars.map ρ then s.c (ρ' w) else ∅) (σ (ρ' w))
    split
    · exact hσ.1 (ρ' w)
    · exact memC_empty S _
  · intro E' hE' hu
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    rw [unifies_ren] at hu
    refine hσ.2 E hE fun p hp => ?_
    have := hu p hp
    rwa [hb p.1 fun v hv => hfull.xs E hE p hp v (List.mem_append_left _ hv),
      hb p.2 fun v hv => hfull.xs E hE p hp v (List.mem_append_right _ hv)] at this
  · show (s.t.rename ρ).bind (σ ∘ ρ') = s.t.bind σ
    rw [rename_bind]; exact hb s.t fun v hv => hv

theorem ren_bwd (hfull : s.Full) (hinv : ∀ v ∈ s.t.vars, ρ' (ρ v) = v) {σ : Nat → GTerm}
    (hσ : σ ∈ (s.ren ρ ρ').Sol S) :
    σ ∘ ρ ∈ s.Sol S ∧ s.t.bind (σ ∘ ρ) = (s.ren ρ ρ').t.bind σ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v
    by_cases hv : v ∈ s.t.vars
    · have := hσ.1 (ρ v)
      have hm : ρ v ∈ s.t.vars.map ρ := List.mem_map_of_mem hv
      simp only [Store.ren, hm, ite_true, hinv v hv] at this
      exact this
    · show MemC S (s.c v) _
      rw [hfull.cs v hv]; exact memC_empty S _
  · intro E hE hu
    exact hσ.2 (Eqns.ren ρ E) (List.mem_map_of_mem hE) (unifies_ren.2 hu)
  · show s.t.bind (σ ∘ ρ) = (s.t.rename ρ).bind σ
    rw [rename_bind]

theorem ren_den (hfull : s.Full) (hinv : ∀ v ∈ s.t.vars, ρ' (ρ v) = v) :
    (s.ren ρ ρ').Den S = s.Den S := by
  ext g
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨h, e⟩ := ren_bwd hfull hinv hσ
    exact ⟨_, h, e.symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨h, e⟩ := ren_fwd hfull hinv hσ
    exact ⟨_, h, e.symm⟩

theorem ren_tight (hfull : s.Full) (hinv : ∀ v ∈ s.t.vars, ρ' (ρ v) = v) (ht : s.Tight S) :
    (s.ren ρ ρ').Tight S := by
  intro w hw
  have hw' : w ∈ s.t.vars.map ρ := by rwa [← Term.vars_rename]
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw'
  obtain ⟨σ, hσ, σ', hσ', hne⟩ := ht v hv
  refine ⟨_, (ren_fwd hfull hinv hσ).1, _, (ren_fwd hfull hinv hσ').1, ?_⟩
  simpa only [comp_apply, hinv v hv] using hne

theorem ren_full (hfull : s.Full) : (s.ren ρ ρ').Full := by
  constructor
  · intro w hw
    have hw' : w ∉ s.t.vars.map ρ := by rwa [← Term.vars_rename]
    simp only [Store.ren, hw', ite_false]
  · intro E' hE' q hq w hw
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    show w ∈ (s.t.rename ρ).vars
    rw [Term.vars_rename]
    simp only [Term.vars_rename, ← List.map_append] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact List.mem_map_of_mem (hfull.xs E hE p hp v hv)

theorem rename_fo {t : Pat} (h : t.firstOrder = true) (ρ : Nat → Nat) :
    (t.rename ρ).firstOrder = true :=
  Term.fo_bind h fun _ _ => rfl

theorem ren_fin {N k : Nat} (hfin : s.Fin N) (hfull : s.Full) (hk : ∀ v ∈ s.t.vars, ρ v < k) :
    (s.ren ρ ρ').Fin k := by
  have hvars : ∀ w ∈ (s.ren ρ ρ').t.vars, w < k := by
    intro w hw
    have hw' : w ∈ s.t.vars.map ρ := by rwa [← Term.vars_rename]
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw'
    exact hk v hv
  refine ⟨rename_fo hfin.fo ρ, hvars, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ∉ s.t.vars.map ρ := by
      intro hm
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hm
      exact absurd (hk v hv) (by omega)
    simp only [Store.ren, hw', ite_false]
  · intro E' hE' q hq
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hE'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨rename_fo (hfin.xfo E hE p hp).1 ρ, rename_fo (hfin.xfo E hE p hp).2 ρ⟩
  · intro E' hE' q hq w hw
    exact hvars w ((ren_full hfull).xs E' hE' q hq w hw)

end ren

end Sorts
end RwLog
