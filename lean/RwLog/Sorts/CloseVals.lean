/-
# Closing a solved exclusion from any atoms that say what the pushed sorts say

`close` reads the sorts of the free variables off the atoms `push` returns.
What it returns depends only on what these atoms say of the values of the
free variables: any list of atoms that holds of the same values gives the
same answer (`close_some_of_atoms`, `close_none_of_atoms`), and there is
none when a sort rejects every instance of a value (`close_none_of_reject`).
The values of the variables after closing are their values before with each
free variable that has one value replaced by it (`oneSub`).
-/
import RwLog.Sorts.NormEx
import RwLog.Kernel.Subterms

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts} {r : Raw} {θ : Binds} {k : Nat}

/-! ## The sorts atoms put on a variable -/

/-- The sorts the atoms put on a variable. -/
def upsOf (A : Atoms) (y : Nat) : Conj := ((A.filter fun a => a.1 = y).map Prod.snd).toFinset

theorem mem_upsOf {A : Atoms} {y : Nat} {n : Name} : n ∈ upsOf A y ↔ (y, n) ∈ A := by
  simp only [upsOf, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, rfl⟩, rfl⟩; exact ha
  · intro h; exact ⟨(y, n), ⟨h, rfl⟩, rfl⟩

theorem holds_iff_upsOf {A : Atoms} {τ : Nat → GTerm} :
    Atoms.Holds S A τ ↔ ∀ y, MemC S (upsOf A y) (τ y) := by
  constructor
  · intro h y n hn; exact h (y, n) (mem_upsOf.1 hn)
  · intro h a ha; exact h a.1 a.2 (mem_upsOf.2 ha)

/-- The values of the variables are in the sorts of the variables. -/
def InSorts (S : Sorts) (r : Raw) (θ : Binds) (τ : Nat → GTerm) : Prop :=
  ∀ v, v < r.c.length → ∀ n ∈ r.conj v, mem S n ((PSubst.apply θ v).bind τ) = true

theorem inSorts_iff_ups (hθ : Pre r.c.length θ) (hd : ¬ dead S r θ) (τ : Nat → GTerm) :
    InSorts S r θ τ ↔ ∀ y, MemC S (ups S r θ y) (τ y) := by
  constructor
  · intro h y n hn
    obtain ⟨v, hv, m, hm, as, hp, ha⟩ := mem_pushed.1 (mem_ups.1 hn)
    exact (push_some (hθ.apply_fo v) hp τ).1 (h v hv m hm) (y, n) ha
  · intro h v hv n hn
    cases hp : push S n (PSubst.apply θ v) with
    | none => exact absurd ⟨v, Finset.mem_range.2 hv, n, hn, hp⟩ hd
    | some as =>
      refine (push_some (hθ.apply_fo v) hp τ).2 fun a ha => ?_
      exact h a.1 a.2 (mem_ups.2 (mem_pushed.2 ⟨v, hv, n, hn, as, hp, ha⟩))

theorem not_inSorts_of_dead (hθ : Pre r.c.length θ) (hd : dead S r θ) (τ : Nat → GTerm) :
    ¬ InSorts S r θ τ := by
  obtain ⟨v, hv, n, hn, hp⟩ := hd
  intro h
  have := push_none (hθ.apply_fo v) hp τ
  rw [h v (Finset.mem_range.1 hv) n hn] at this
  cases this

/-! ## Sorts that allow the same values -/

/-- Two families of conjunctions that allow the same values of all the
variables together have the same members at each variable, when they allow
any. -/
theorem memC_congr_of_prod {C D : Nat → Conj}
    (h : ∀ τ : Nat → GTerm, (∀ y, MemC S (C y) (τ y)) ↔ ∀ y, MemC S (D y) (τ y))
    {τ₀ : Nat → GTerm} (h₀ : ∀ y, MemC S (C y) (τ₀ y)) (y : Nat) (t : GTerm) :
    MemC S (C y) t ↔ MemC S (D y) t := by
  have h₁ := (h τ₀).1 h₀
  constructor
  · intro ht
    have := (h (update τ₀ y t)).1 (fun z => by
      by_cases e : z = y
      · subst e; simpa using ht
      · simpa [update, e] using h₀ z) y
    simpa using this
  · intro ht
    have := (h (update τ₀ y t)).2 (fun z => by
      by_cases e : z = y
      · subst e; simpa using ht
      · simpa [update, e] using h₁ z) y
    simpa using this

/-- How many members a conjunction has depends on its members only. -/
theorem count_congr {c d : Conj} (h : ∀ t, MemC S c t ↔ MemC S d t) : count S c = count S d := by
  cases hc : count S c with
  | none => exact (count_none.2 fun ⟨t, ht⟩ => count_none.1 hc ⟨t, (h t).2 ht⟩).symm
  | one g =>
    obtain ⟨h1, h2⟩ := count_one.1 hc
    exact (count_one.2 ⟨(h g).1 h1, fun u hu => h2 u ((h u).2 hu)⟩).symm
  | many =>
    obtain ⟨t1, t2, hne, h1, h2⟩ := count_many.1 hc
    exact (count_many.2 ⟨t1, t2, hne, (h _).1 h1, (h _).1 h2⟩).symm

/-! ## The values after closing -/

/-- A free variable with one value in its sorts becomes that value; any
other variable stays. -/
def oneSub (S : Sorts) (k : Nat) (ν : Nat → Pat) (C : Nat → Conj) (y : Nat) : Pat :=
  if y < k ∧ ν y = .var y then
    match count S (C y) with
    | .one g => Term.lift g
    | _ => .var y
  else .var y

theorem oneSub_congr {ν : Nat → Pat} {C D : Nat → Conj}
    (h : ∀ y, count S (C y) = count S (D y)) : oneSub S k ν C = oneSub S k ν D := by
  funext y
  simp only [oneSub, h y]

theorem lift_bind_pat (g : GTerm) (σ : Nat → Pat) : (Term.lift g).bind σ = Term.lift g := by
  conv_rhs => rw [← Term.bind_var_id (Term.lift g)]
  refine Term.bind_congr fun v hv => ?_
  rw [Term.lift_vars] at hv
  cases hv

/-- The value of a variable after one more variable is bound. -/
theorem apply_ext {x : Nat} {p : Pat} (hθ : Pre k θ) (hx : x < k) (hfree : ∀ b ∈ θ, b.1 ≠ x)
    (v : Nat) : PSubst.apply (ext k θ x p) v = (PSubst.apply θ v).bind (Term.single x p) := by
  have hm := @mem_ext k θ x p hθ hx hfree
  by_cases hvx : v = x
  · subst hvx
    rw [apply_of_not_mem hfree]
    have := apply_of_mem (sorted_ext (k := k) (θ := θ) (x := v) (p := p)) (b := (v, p))
      (hm.2 (Or.inl rfl))
    simpa [Term.bind, Term.single] using this
  · rcases apply_cases θ v with e | hin
    · have hno : ∀ b ∈ θ, b.1 ≠ v := by
        intro b hb hbv
        have hb2 : b.2 = .var b.1 := by rw [← apply_of_mem hθ.sorted hb, hbv, e]
        have := hθ.later b hb b.1 hb2
        omega
      rw [e]
      have : ∀ b ∈ ext k θ x p, b.1 ≠ v := by
        intro b hb hbv
        rcases hm.1 hb with rfl | ⟨q, hq, -⟩
        · exact hvx hbv.symm
        · exact hno _ hq hbv
      rw [apply_of_not_mem this]
      simp [Term.bind, Term.single, hvx]
    · have := apply_of_mem (sorted_ext (k := k) (θ := θ) (x := x) (p := p))
        (b := (v, (PSubst.apply θ v).bind (Term.single x p))) (hm.2 (Or.inr ⟨_, hin, rfl⟩))
      simpa using this

/-- The values after the variables of a list are bound each to a ground
term. -/
theorem apply_foldl_ext : ∀ (L : List (Nat × GTerm)) (θ : Binds), Pre k θ →
    (L.Pairwise fun a b => a.1 < b.1) → (∀ b ∈ L, b.1 < k ∧ ∀ c ∈ θ, c.1 ≠ b.1) → ∀ v,
    PSubst.apply (L.foldl (fun θ' b => ext k θ' b.1 (Term.lift b.2)) θ) v =
      (PSubst.apply θ v).bind fun y =>
        match L.lookup y with
        | some g => Term.lift g
        | none => .var y
  | [], θ, _, _, _, v => by
    simp only [List.foldl_nil, List.lookup_nil]
    exact (Term.bind_var_id _).symm
  | b :: L, θ, hθ, hs, hL, v => by
    obtain ⟨hbk, hfree⟩ := hL b List.mem_cons_self
    rw [List.pairwise_cons] at hs
    have hpre : Pre k (ext k θ b.1 (Term.lift b.2)) :=
      pre_ext hθ hbk hfree (Term.lift_fo _) (by simp [Term.lift_vars]) (by
        intro y hy
        have := Term.lift_vars b.2
        rw [hy] at this
        simp [Term.vars] at this)
    have hm := @mem_ext k θ b.1 (Term.lift b.2) hθ hbk hfree
    have hL' : ∀ b' ∈ L, b'.1 < k ∧ ∀ c ∈ ext k θ b.1 (Term.lift b.2), c.1 ≠ b'.1 := by
      intro b' hb'
      refine ⟨(hL b' (List.mem_cons_of_mem _ hb')).1, fun c hc hcb => ?_⟩
      rcases hm.1 hc with rfl | ⟨q, hq, -⟩
      · exact absurd hcb (Nat.ne_of_lt (hs.1 b' hb'))
      · exact (hL b' (List.mem_cons_of_mem _ hb')).2 _ hq hcb
    simp only [List.foldl_cons]
    rw [apply_foldl_ext L _ hpre hs.2 hL' v, apply_ext hθ hbk hfree v, Term.bind_bind]
    refine Term.bind_congr fun y _ => ?_
    by_cases hy : y = b.1
    · subst hy
      simp [Term.single, lift_bind_pat, List.lookup]
    · have hy' : (y == b.1) = false := by simpa using hy
      simp [Term.single, hy, List.lookup, hy']

theorem free_of_apply (hθ : Pre k θ) {y : Nat} (h : PSubst.apply θ y = .var y) :
    ∀ c ∈ θ, c.1 ≠ y := by
  intro c hc hcy
  have hc2 : c.2 = .var c.1 := by rw [← apply_of_mem hθ.sorted hc, hcy, h]
  have := hθ.later c hc c.1 hc2
  omega

theorem lookup_sorted {β : Type} : ∀ {L : List (Nat × β)}, (L.Pairwise fun a b => a.1 < b.1) →
    ∀ b ∈ L, L.lookup b.1 = some b.2
  | [], _, b, hb => by simp at hb
  | a :: L, h, b, hb => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · simp [List.lookup]
    · have hne : (b.1 == a.1) = false := by
        have := h.1 b hb
        simpa using Nat.ne_of_gt this
      simp only [List.lookup, hne]
      exact lookup_sorted h.2 b hb

theorem oneSub_one {ν : Nat → Pat} {C : Nat → Conj} {y : Nat} {g : GTerm} (hy : y < k)
    (hν : ν y = .var y) (hc : count S (C y) = .one g) : oneSub S k ν C y = Term.lift g := by
  simp only [oneSub, hy, hν, and_self, ↓reduceIte, hc]

theorem oneSub_not {ν : Nat → Pat} {C : Nat → Conj} {y : Nat} (h : ¬ (y < k ∧ ν y = .var y)) :
    oneSub S k ν C y = .var y := by
  simp only [oneSub, h, ↓reduceIte]

theorem oneSub_none {ν : Nat → Pat} {C : Nat → Conj} {y : Nat}
    (hc : ∀ g, count S (C y) ≠ .one g) : oneSub S k ν C y = .var y := by
  unfold oneSub
  split
  · cases h : count S (C y) with
    | none => rfl
    | many => rfl
    | one g => exact absurd h (hc g)
  · rfl

/-- The substitution `close` applies. -/
theorem ones_lookup (hθ : Pre r.c.length θ) (y : Nat) :
    (match (ones S r θ).lookup y with
      | some g => Term.lift g
      | none => .var y) = oneSub S r.c.length (PSubst.apply θ) (ups S r θ) y := by
  cases hl : (ones S r θ).lookup y with
  | some g =>
    obtain ⟨hy, hfree, hc⟩ := mem_ones.1 (mem_of_lookup hl)
    exact (oneSub_one hy (apply_of_not_mem hfree) hc).symm
  | none =>
    by_cases hcond : y < r.c.length ∧ PSubst.apply θ y = .var y
    · refine (oneSub_none fun g hc => ?_).symm
      have := lookup_sorted (sorted_ones S r θ) (y, g)
        (mem_ones.2 ⟨hcond.1, free_of_apply hθ hcond.2, hc⟩)
      rw [hl] at this
      cases this
    · exact (oneSub_not hcond).symm

/-! ## Closing from other atoms -/

/-- Nothing is excluded when a sort of a variable rejects every instance of
its value. -/
theorem close_none_of_reject (hθ : Pre r.c.length θ) {v : Nat} {n : Name} (hn : n ∈ r.conj v)
    (h : ∀ τ : Nat → GTerm, mem S n ((PSubst.apply θ v).bind τ) = false) :
    close S r θ = none := by
  cases hc : close S r θ with
  | none => rfl
  | some θ' =>
    obtain ⟨-, hEx, ⟨σ, hσ⟩, -⟩ := close_some hθ hc
    rw [hEx] at hσ
    have hF := unifies_eqnsOf hθ.sorted
    have := hσ.1 v n hn
    rw [(hF σ).1 hσ.2 v, h σ] at this
    cases this

/-- Nothing is excluded when atoms that hold exactly of the values in the
sorts leave a variable no value. -/
theorem close_none_of_atoms (hθ : Pre r.c.length θ) {A : Atoms}
    (hA : ∀ τ : Nat → GTerm, Atoms.Holds S A τ ↔ InSorts S r θ τ) {y : Nat}
    (hy : count S (upsOf A y) = .none) : close S r θ = none := by
  by_cases hd : dead S r θ
  · unfold close
    split
    · rfl
    · rename_i hc; exact absurd (Or.inl hd) hc
  · have hno : ¬ ∃ τ : Nat → GTerm, ∀ z, MemC S (ups S r θ z) (τ z) := by
      rintro ⟨τ, hτ⟩
      have := holds_iff_upsOf.1 ((hA τ).2 ((inSorts_iff_ups hθ hd τ).2 hτ)) y
      exact count_none.1 hy ⟨_, this⟩
    have hz : ∃ z, ¬ ∃ t, MemC S (ups S r θ z) t := by
      by_contra hall
      push Not at hall
      choose τ hτ using hall
      exact hno ⟨τ, hτ⟩
    obtain ⟨z, hz⟩ := hz
    have hn : ∃ n, n ∈ ups S r θ z := by
      by_contra hnone
      push Not at hnone
      exact hz ⟨.sym "", fun n hn => absurd hn (hnone n)⟩
    obtain ⟨n, hn⟩ := hn
    unfold close
    split
    · rfl
    · rename_i hc; exact absurd (Or.inr ⟨(z, n), mem_ups.1 hn, noMember_iff.2 hz⟩) hc

/-- When atoms that hold exactly of the values in the sorts leave every
variable a value, the exclusion is closed by binding each free variable
they leave one value. -/
theorem close_some_of_atoms (hθ : Pre r.c.length θ) {A : Atoms}
    (hA : ∀ τ : Nat → GTerm, Atoms.Holds S A τ ↔ InSorts S r θ τ)
    (hAk : ∀ a ∈ A, a.1 < r.c.length)
    (hall : ∀ y, y < r.c.length → count S (upsOf A y) ≠ .none) :
    ∃ θ', close S r θ = some θ' ∧ ∀ v, PSubst.apply θ' v =
      (PSubst.apply θ v).bind (oneSub S r.c.length (PSubst.apply θ) (upsOf A)) := by
  have hmem : ∀ y, ∃ t, MemC S (upsOf A y) t := by
    intro y
    by_cases hy : y < r.c.length
    · by_contra hno
      exact hall y hy (count_none.2 hno)
    · refine ⟨.sym "", fun n hn => ?_⟩
      exact absurd (hAk _ (mem_upsOf.1 hn)) hy
  choose τ₀ hτ₀ using hmem
  have hin : InSorts S r θ τ₀ := (hA τ₀).1 (holds_iff_upsOf.2 hτ₀)
  have hd : ¬ dead S r θ := fun hd => not_inSorts_of_dead hθ hd τ₀ hin
  have hiff : ∀ τ : Nat → GTerm,
      (∀ y, MemC S (upsOf A y) (τ y)) ↔ ∀ y, MemC S (ups S r θ y) (τ y) :=
    fun τ => (holds_iff_upsOf.symm.trans (hA τ)).trans (inSorts_iff_ups hθ hd τ)
  have hcong := memC_congr_of_prod hiff hτ₀
  have hcount : ∀ y, count S (upsOf A y) = count S (ups S r θ y) :=
    fun y => count_congr (hcong y)
  have hne : ¬ (dead S r θ ∨ ∃ a ∈ pushed S r θ, noMember S (ups S r θ a.1) = true) := by
    rintro (h | ⟨a, -, ha⟩)
    · exact hd h
    · exact noMember_iff.1 ha ⟨_, (hcong a.1 _).1 (hτ₀ a.1)⟩
  have hcl : close S r θ = some ((ones S r θ).foldl
      (fun θ' b => ext r.c.length θ' b.1 (Term.lift b.2)) θ) := by
    unfold close
    split
    · rename_i hc; exact absurd hc hne
    · rfl
  refine ⟨_, hcl, fun v => ?_⟩
  rw [apply_foldl_ext (ones S r θ) θ hθ (sorted_ones S r θ) (fun b hb =>
    ⟨(mem_ones.1 hb).1, (mem_ones.1 hb).2.1⟩) v, oneSub_congr hcount]
  exact Term.bind_congr fun y _ => ones_lookup hθ y

/-! ## The size of the values bound -/

/-- The number of subterms of the one member of a conjunction that has
one. -/
noncomputable def soleSize (S : Sorts) (d : Conj) : Nat :=
  match count S d with
  | .one g => (Term.lift g).subs.card
  | _ => 0

/-- A bound on the number of subterms of a value `close` binds a variable
to, over the conjunctions of the names of a list. -/
noncomputable def soleMax (S : Sorts) (U : List Name) : Nat :=
  1 + U.toFinset.powerset.sup (soleSize S)

theorem oneSub_subs_le {U : List Name} {ν : Nat → Pat} {C : Nat → Conj}
    (hC : ∀ y, ∀ n ∈ C y, n ∈ U) (y : Nat) : (oneSub S k ν C y).subs.card ≤ soleMax S U := by
  by_cases h : y < k ∧ ν y = .var y
  · cases hc : count S (C y) with
    | none =>
      rw [oneSub_none fun g hg => by rw [hc] at hg; cases hg]
      simp [soleMax, Term.subs]
    | many =>
      rw [oneSub_none fun g hg => by rw [hc] at hg; cases hg]
      simp [soleMax, Term.subs]
    | one g =>
      rw [oneSub_one h.1 h.2 hc]
      have hmem : C y ∈ U.toFinset.powerset :=
        Finset.mem_powerset.2 fun n hn => List.mem_toFinset.2 (hC y n hn)
      have := Finset.le_sup (f := soleSize S) hmem
      have e : soleSize S (C y) = (Term.lift g).subs.card := by simp only [soleSize, hc]
      unfold soleMax
      omega
  · rw [oneSub_not h]
    simp [soleMax, Term.subs]

end Sorts
end RwLog
