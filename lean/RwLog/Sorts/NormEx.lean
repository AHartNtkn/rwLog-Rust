/-
# The normal form of an exclusion, as a function

`normEx S r E` is the normal exclusion that removes, among the substitutions
in the sorts of the raw store `r`, the ones that satisfy the equations `E`
(`normEx_some`); there is none when no substitution in the sorts satisfies
them (`normEx_none`).

The equations are solved and the solution is oriented (`Orient.lean`). The
sorts of each bound variable are then pushed onto its value, which gives
sorts for the free variables (`ups`). What the exclusion removes is laid
out by the free variables, each taken freely in its sorts (`ex_ups`,
`mem_ex_of_ups`). So the exclusion removes nothing when a sort rejects a
value outright or a free variable has no value; a free variable with one
value is bound to it; and the free variables that are left take two values.
-/
import RwLog.Sorts.Orient
import RwLog.Sorts.Count
import RwLog.Sorts.UniqueExcl

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts} {r : Raw} {θ : Binds}

/-- The sorts the values of the variables put on the variables in them. -/
def pushed (S : Sorts) (r : Raw) (θ : Binds) : Finset (Nat × Name) :=
  (Finset.range r.c.length).biUnion fun v => (r.conj v).biUnion fun n =>
    match push S n (PSubst.apply θ v) with
    | some as => as.toFinset
    | none => ∅

/-- A sort of a variable rejects its value whatever the variables are. -/
def dead (S : Sorts) (r : Raw) (θ : Binds) : Prop :=
  ∃ v ∈ Finset.range r.c.length, ∃ n ∈ r.conj v, push S n (PSubst.apply θ v) = none

instance (S : Sorts) (r : Raw) (θ : Binds) : Decidable (dead S r θ) := by
  unfold dead; infer_instance

/-- The sorts put on one variable. -/
def ups (S : Sorts) (r : Raw) (θ : Binds) (y : Nat) : Conj :=
  ((pushed S r θ).filter fun a => a.1 = y).image Prod.snd

theorem mem_ups {y : Nat} {n : Name} : n ∈ ups S r θ y ↔ (y, n) ∈ pushed S r θ := by
  simp only [ups, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, rfl⟩, rfl⟩; exact ha
  · intro h; exact ⟨(y, n), ⟨h, rfl⟩, rfl⟩

theorem mem_pushed {a : Nat × Name} : a ∈ pushed S r θ ↔
    ∃ v, v < r.c.length ∧ ∃ n ∈ r.conj v, ∃ as, push S n (PSubst.apply θ v) = some as ∧ a ∈ as := by
  simp only [pushed, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨v, hv, n, hn, h⟩
    cases hp : push S n (PSubst.apply θ v) with
    | none => rw [hp] at h; simp at h
    | some as => rw [hp] at h; exact ⟨v, hv, n, hn, as, hp, by simpa using h⟩
  · rintro ⟨v, hv, n, hn, as, hp, ha⟩
    exact ⟨v, hv, n, hn, by rw [hp]; simpa using ha⟩

/-- What the exclusion removes has every variable in the sorts put on
it. -/
theorem ex_ups (hθ : Pre r.c.length θ) {σ : Nat → GTerm} (hσ : σ ∈ r.Ex S θ) :
    ¬ dead S r θ ∧ ∀ y, MemC S (ups S r θ y) (σ y) := by
  have hF := unifies_eqnsOf hθ.sorted
  have hall : ∀ v, ∀ n ∈ r.conj v, mem S n ((PSubst.apply θ v).bind σ) = true := by
    intro v n hn
    rw [← (hF σ).1 hσ.2 v]; exact hσ.1 v n hn
  constructor
  · rintro ⟨v, -, n, hn, hp⟩
    have := push_none (hθ.apply_fo v) hp σ
    rw [hall v n hn] at this; cases this
  · intro y n hn
    obtain ⟨v, -, m, hm, as, hp, ha⟩ := mem_pushed.1 (mem_ups.1 hn)
    exact (push_some (hθ.apply_fo v) hp σ).1 (hall v m hm) (y, n) ha

/-- Values of the variables in the sorts put on them give something the
exclusion removes. -/
theorem mem_ex_of_ups (hθ : Pre r.c.length θ) (hd : ¬ dead S r θ) {τ : Nat → GTerm}
    (hτ : ∀ y, MemC S (ups S r θ y) (τ y)) :
    (fun v => (PSubst.apply θ v).bind τ) ∈ r.Ex S θ := by
  have hF := unifies_eqnsOf hθ.sorted
  refine ⟨fun v n hn => ?_, (hF _).2 fun v => ?_⟩
  · have hv : v < r.c.length := by
      by_contra h
      rw [show r.store.c v = r.conj v from rfl, Raw.Normal.conj_of_ge r (by omega)] at hn
      simp at hn
    show mem S n ((PSubst.apply θ v).bind τ) = true
    cases hp : push S n (PSubst.apply θ v) with
    | none => exact absurd ⟨v, Finset.mem_range.2 hv, n, hn, hp⟩ hd
    | some as =>
      refine (push_some (hθ.apply_fo v) hp τ).2 fun a ha => ?_
      exact hτ a.1 a.2 (mem_ups.2 (mem_pushed.2 ⟨v, hv, n, hn, as, hp, ha⟩))
  · exact (Pre.bind_apply_of_free (hθ.apply_free v) τ).symm

/-! ## Binding the variables with one value -/

/-- The free variables with one value, each with its value. -/
def ones (S : Sorts) (r : Raw) (θ : Binds) : List (Nat × GTerm) :=
  (List.range r.c.length).filterMap fun y =>
    if (θ.lookup y).isNone then
      match count S (ups S r θ y) with
      | .one g => some (y, g)
      | _ => none
    else none

theorem lookup_isNone {y : Nat} : (θ.lookup y).isNone = true ↔ ∀ b ∈ θ, b.1 ≠ y := by
  constructor
  · intro h b hb e
    cases hl : θ.lookup y with
    | some p => rw [hl] at h; cases h
    | none =>
      rw [List.lookup_eq_none_iff] at hl
      exact absurd (by simpa using e.symm) (by simpa using hl b hb)
  · intro h
    cases hl : θ.lookup y with
    | some p => exact absurd rfl (h _ (mem_of_lookup hl))
    | none => rfl

theorem mem_ones {b : Nat × GTerm} : b ∈ ones S r θ ↔
    b.1 < r.c.length ∧ (∀ c ∈ θ, c.1 ≠ b.1) ∧ count S (ups S r θ b.1) = .one b.2 := by
  simp only [ones, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨y, hy, h⟩
    by_cases hl : (θ.lookup y).isNone = true
    · simp only [hl, ↓reduceIte] at h
      cases hc : count S (ups S r θ y) with
      | one g =>
        rw [hc] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨hy, lookup_isNone.1 hl, hc⟩
      | none => rw [hc] at h; cases h
      | many => rw [hc] at h; cases h
    · simp [hl] at h
  · rintro ⟨hk, hfree, hc⟩
    refine ⟨b.1, hk, ?_⟩
    simp only [lookup_isNone.2 hfree, ↓reduceIte, hc]

theorem sorted_ones (S : Sorts) (r : Raw) (θ : Binds) :
    (ones S r θ).Pairwise fun a b => a.1 < b.1 := by
  refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
  intro v w hvw b hb b' hb'
  have e : ∀ {u : Nat} {c : Nat × GTerm},
      c ∈ (if (θ.lookup u).isNone then
        match count S (ups S r θ u) with
        | .one g => some (u, g)
        | _ => none
      else none) → c.1 = u := by
    intro u c hc
    by_cases hl : (θ.lookup u).isNone = true
    · simp only [hl, ↓reduceIte] at hc
      cases hcnt : count S (ups S r θ u) with
      | one g =>
        rw [hcnt] at hc
        simp only [Option.mem_def, Option.some.injEq] at hc
        rw [← hc]
      | none => rw [hcnt] at hc; cases hc
      | many => rw [hcnt] at hc; cases hc
    · simp [hl] at hc
  rw [e hb, e hb']
  exact hvw

/-- Adding bindings of free variables to the one value each takes in what the
exclusion removes keeps what it removes. -/
theorem fold_ext (k : Nat) (hk : k = r.c.length) : ∀ (L : List (Nat × GTerm)) (θ : Binds),
    Pre k θ → (L.Pairwise fun a b => a.1 < b.1) →
    (∀ b ∈ L, b.1 < k ∧ (∀ c ∈ θ, c.1 ≠ b.1) ∧ ∀ σ ∈ r.Ex S θ, σ b.1 = b.2) →
    Pre k (L.foldl (fun θ' b => ext k θ' b.1 (Term.lift b.2)) θ) ∧
      r.Ex S (L.foldl (fun θ' b => ext k θ' b.1 (Term.lift b.2)) θ) = r.Ex S θ ∧
      ∀ y, (∀ c ∈ L.foldl (fun θ' b => ext k θ' b.1 (Term.lift b.2)) θ, c.1 ≠ y) ↔
        (∀ c ∈ θ, c.1 ≠ y) ∧ ∀ b ∈ L, b.1 ≠ y
  | [], θ, hθ, _, _ => ⟨hθ, rfl, fun y => by simp⟩
  | b :: L, θ, hθ, hs, hL => by
    obtain ⟨hbk, hfree, hval⟩ := hL b List.mem_cons_self
    rw [List.pairwise_cons] at hs
    have hpre : Pre k (ext k θ b.1 (Term.lift b.2)) :=
      pre_ext hθ hbk hfree (Term.lift_fo _) (by simp [Term.lift_vars]) (by
        intro y hy
        have := Term.lift_vars b.2
        rw [hy] at this
        simp [Term.vars] at this)
    have hEx : r.Ex S (ext k θ b.1 (Term.lift b.2)) = r.Ex S θ := by
      ext σ
      constructor
      · rintro ⟨hp, hu⟩
        exact ⟨hp, ((unifies_ext hθ hbk hfree σ).1 hu).1⟩
      · rintro ⟨hp, hu⟩
        refine ⟨hp, (unifies_ext hθ hbk hfree σ).2 ⟨hu, ?_⟩⟩
        rw [Term.lift_bind]
        exact hval σ ⟨hp, hu⟩
    have hm := @mem_ext k θ b.1 (Term.lift b.2) hθ hbk hfree
    have hfr : ∀ y, (∀ c ∈ ext k θ b.1 (Term.lift b.2), c.1 ≠ y) ↔
        (∀ c ∈ θ, c.1 ≠ y) ∧ b.1 ≠ y := by
      intro y
      constructor
      · intro h
        refine ⟨fun c hc => ?_, h _ (hm.2 (Or.inl rfl))⟩
        exact h (c.1, c.2.bind (Term.single b.1 (Term.lift b.2))) (hm.2 (Or.inr ⟨c.2, hc, rfl⟩))
      · rintro ⟨h₁, h₂⟩ c hc
        rcases hm.1 hc with rfl | ⟨q, hq, -⟩
        · exact h₂
        · exact h₁ (c.1, q) hq
    obtain ⟨h₁, h₂, h₃⟩ := fold_ext k hk L (ext k θ b.1 (Term.lift b.2)) hpre hs.2 (by
      intro b' hb'
      obtain ⟨hb'k, hfree', hval'⟩ := hL b' (List.mem_cons_of_mem _ hb')
      refine ⟨hb'k, (hfr b'.1).2 ⟨hfree', Nat.ne_of_lt (hs.1 b' hb')⟩, ?_⟩
      rw [hEx]; exact hval')
    refine ⟨h₁, h₂.trans hEx, fun y => ?_⟩
    simp only [List.foldl_cons]
    rw [h₃ y, hfr y]
    constructor
    · rintro ⟨⟨h, hb⟩, hrest⟩
      refine ⟨h, fun b' hb' => ?_⟩
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact hb
      · exact hrest b' hb'
    · rintro ⟨h, hall⟩
      exact ⟨⟨h, hall b List.mem_cons_self⟩, fun b' hb' => hall b' (List.mem_cons_of_mem _ hb')⟩

/-- The conjunction has no member. -/
def noMember (S : Sorts) (c : Conj) : Bool :=
  match count S c with
  | .none => true
  | _ => false

theorem noMember_iff {c : Conj} : noMember S c = true ↔ ¬ ∃ t, MemC S c t := by
  rw [← count_none]
  unfold noMember
  cases count S c <;> simp

/-- A solved exclusion with its one-valued free variables bound; nothing
when it removes nothing. -/
def close (S : Sorts) (r : Raw) (θ : Binds) : Option Binds :=
  if dead S r θ ∨ ∃ a ∈ pushed S r θ, noMember S (ups S r θ a.1) = true then none
  else some ((ones S r θ).foldl (fun θ' b => ext r.c.length θ' b.1 (Term.lift b.2)) θ)

theorem close_none (hθ : Pre r.c.length θ) (h : close S r θ = none) : r.Ex S θ = ∅ := by
  unfold close at h
  split at h
  · rename_i hc
    ext σ
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hσ
    obtain ⟨hd, hm⟩ := ex_ups hθ hσ
    rcases hc with hc | ⟨a, -, ha⟩
    · exact hd hc
    · exact noMember_iff.1 ha ⟨_, hm a.1⟩
  · cases h

/-- The result is in normal form but for being non-empty, and removes what
the solved exclusion did. -/
theorem close_some {θ' : Binds} (hθ : Pre r.c.length θ) (h : close S r θ = some θ') :
    Pre r.c.length θ' ∧ r.Ex S θ' = r.Ex S θ ∧ (r.Ex S θ').Nonempty ∧
      ∀ y, y < r.c.length → (∀ b ∈ θ', b.1 ≠ y) →
        ∃ σ ∈ r.Ex S θ', ∃ σ' ∈ r.Ex S θ', σ y ≠ σ' y := by
  unfold close at h
  split at h
  · cases h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    push Not at hc
    obtain ⟨hd, hne⟩ := hc
    have hmemb : ∀ y, ∃ t, MemC S (ups S r θ y) t := by
      intro y
      by_cases hy : ∃ n, (y, n) ∈ pushed S r θ
      · obtain ⟨n, hn⟩ := hy
        by_contra hno
        exact hne (y, n) hn (noMember_iff.2 hno)
      · refine ⟨.sym "", fun n hn => ?_⟩
        exact absurd ⟨n, mem_ups.1 hn⟩ hy
    choose τ hτ using hmemb
    obtain ⟨h₁, h₂, h₃⟩ := fold_ext (S := S) (r := r) r.c.length rfl (ones S r θ) θ hθ
      (sorted_ones S r θ) (by
        intro b hb
        obtain ⟨hk, hfree, hcnt⟩ := mem_ones.1 hb
        exact ⟨hk, hfree, fun σ hσ => (count_one.1 hcnt).2 _ ((ex_ups hθ hσ).2 b.1)⟩)
    refine ⟨h₁, h₂, ?_, ?_⟩
    · rw [h₂]; exact ⟨_, mem_ex_of_ups hθ hd hτ⟩
    · intro y hy hfree
      obtain ⟨hfreeθ, hnot⟩ := (h₃ y).1 hfree
      have hmany : count S (ups S r θ y) = .many := by
        cases hcnt : count S (ups S r θ y) with
        | none => exact absurd ⟨_, hτ y⟩ (count_none.1 hcnt)
        | one g => exact absurd rfl (hnot (y, g) (mem_ones.2 ⟨hy, hfreeθ, hcnt⟩))
        | many => rfl
      obtain ⟨t₁, t₂, hne', hm₁, hm₂⟩ := count_many.1 hmany
      have hupd : ∀ t, MemC S (ups S r θ y) t → ∀ z, MemC S (ups S r θ z) (update τ y t z) := by
        intro t ht z
        by_cases e : z = y
        · subst e; simpa using ht
        · simpa [update, e] using hτ z
      rw [h₂]
      refine ⟨_, mem_ex_of_ups hθ hd (hupd t₁ hm₁), _, mem_ex_of_ups hθ hd (hupd t₂ hm₂), ?_⟩
      show (PSubst.apply θ y).bind (update τ y t₁) ≠ (PSubst.apply θ y).bind (update τ y t₂)
      rw [apply_of_not_mem hfreeθ]
      simpa [Term.bind] using hne'

/-! ## The normal form -/

/-- The normal exclusion that removes the substitutions in the sorts that
satisfy the equations; nothing when there are none. -/
def normEx (S : Sorts) (r : Raw) (E : Eqns Nat) : Option Binds :=
  (solve E).bind fun μ => close S r (bindsOf r.c.length (orient r.c.length μ))

theorem normEx_none {E : Eqns Nat} (hE : E.FO) (hEv : ∀ v ∈ E.vars, v < r.c.length)
    (h : normEx S r E = none) : ∀ σ ∈ r.store.Pos S, ¬ Eqns.Unifies σ E := by
  intro σ hσ hu
  unfold normEx at h
  cases hs : solve E with
  | none => exact solve_none hs σ hu
  | some μ =>
    rw [hs] at h
    have := close_none (pre_solved hs hE hEv) h
    have hin : σ ∈ r.Ex S (bindsOf r.c.length (orient r.c.length μ)) :=
      ⟨hσ, (unifies_solved hs hE hEv σ).2 hu⟩
    rw [this] at hin
    exact hin

theorem normEx_some {E : Eqns Nat} {θ : Binds} (hE : E.FO)
    (hEv : ∀ v ∈ E.vars, v < r.c.length) (h : normEx S r E = some θ) :
    Pre r.c.length θ ∧ r.Ex S θ = {σ | σ ∈ r.store.Pos S ∧ Eqns.Unifies σ E} ∧
      (r.Ex S θ).Nonempty ∧
      ∀ y, y < r.c.length → (∀ b ∈ θ, b.1 ≠ y) →
        ∃ σ ∈ r.Ex S θ, ∃ σ' ∈ r.Ex S θ, σ y ≠ σ' y := by
  unfold normEx at h
  cases hs : solve E with
  | none => rw [hs] at h; cases h
  | some μ =>
    rw [hs] at h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := close_some (pre_solved hs hE hEv) h
    refine ⟨h₁, ?_, h₃, h₄⟩
    rw [h₂]
    ext σ
    exact ⟨fun hσ => ⟨hσ.1, (unifies_solved hs hE hEv σ).1 hσ.2⟩,
      fun hσ => ⟨hσ.1, (unifies_solved hs hE hEv σ).2 hσ.2⟩⟩

end Sorts
end RwLog
