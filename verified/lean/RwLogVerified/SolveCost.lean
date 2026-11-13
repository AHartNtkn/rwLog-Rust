/-
# What solving a list of equations costs

The Rust `solve_into` keeps its equations as a list in the store. `encEqs` is
that list as a term, so the facts about terms apply to it.

`solveCost E o` bounds the ticks `solve_into` spends on the equations `E`
with the output term `o`. It is a polynomial in three numbers:

* `dcount E o`, the number of distinct subterms of the equations and of `o`;
* the length of `E`;
* `Eqns.lead E`, which is at most `dcount E o`.

The lemmas here say how the bound moves with each step of the loop: dropping
an equation between a term and itself and splitting an equation between two
applications each pay nine ticks, and eliminating a variable pays for a pass
over everything.
-/
import RwLog.Kernel.SolveFacts
import RwLog.Kernel.Subterms

namespace RwLogVerified

open RwLog RwLog.Term

variable {nm : Option Nat → Sym}

/-- A list of equations as a term. -/
def encEqs (nm : Option Nat → Sym) : Eqns Nat → Pat
  | [] => .sym (nm none)
  | p :: E => .app (.app p.1 p.2) (encEqs nm E)

theorem enc_subst (x : Nat) (u : Pat) (E : Eqns Nat) :
    (encEqs nm E).bind (single x u) = encEqs nm (Eqns.subst x u E) := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    show _ = encEqs nm ((p.1.bind (single x u), p.2.bind (single x u)) :: Eqns.subst x u E)
    simp only [encEqs, Term.bind_app, ih]

/-- The nodes of the list itself: each suffix and each pair. -/
def spine (nm : Option Nat → Sym) : Eqns Nat → Finset Pat
  | [] => {.sym (nm none)}
  | p :: E => insert (encEqs nm (p :: E)) (insert (.app p.1 p.2) (spine nm E))

theorem card_spine_le (E : Eqns Nat) : (spine nm E).card ≤ 2 * E.length + 1 := by
  induction E with
  | nil => simp [spine]
  | cons p E ih =>
    simp only [spine, List.length_cons]
    have h1 := Finset.card_insert_le (encEqs nm (p :: E)) (insert (Term.app p.1 p.2) (spine nm E))
    have h2 := Finset.card_insert_le (Term.app p.1 p.2) (spine nm E)
    omega

theorem subs_enc_subset (E : Eqns Nat) : (encEqs nm E).subs ⊆ Eqns.subs E ∪ spine nm E := by
  induction E with
  | nil => simp [encEqs, spine, Term.subs]
  | cons p E ih =>
    intro w hw
    simp only [encEqs, Term.subs, Finset.mem_insert, Finset.mem_union] at hw
    simp only [Eqns.subs, spine, encEqs, Finset.mem_union, Finset.mem_insert]
    rcases hw with h | (h | h | h) | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · rcases Finset.mem_union.1 (ih h) with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr (Or.inr (Or.inr h'))

/-- The number of distinct subterms of the equations and of the output. -/
def dcount (E : Eqns Nat) (o : Pat) : Nat := (Eqns.subs E ∪ o.subs).card

theorem card_subs_enc_le (E : Eqns Nat) (o : Pat) :
    ((encEqs nm E).subs ∪ o.subs).card ≤ dcount E o + 2 * E.length + 1 := by
  have hsub : (encEqs nm E).subs ∪ o.subs ⊆ (Eqns.subs E ∪ o.subs) ∪ spine nm E := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · rcases Finset.mem_union.1 (subs_enc_subset E h) with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h')
      · exact Finset.mem_union_right _ h'
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Eqns.subs E ∪ o.subs) (spine nm E)
  have h3 := card_spine_le (nm := nm) E
  unfold dcount
  omega

/-! ## The bound -/

/-- The bound as a function of the length `L`, the number `K` of splits that
can still happen, and the number `D` of distinct subterms. -/
def phi (L K D : Nat) : Nat := 1 + 9 * (L + 2 * K) + (D + 1) * (10 + 10 * D + 10 * (L + K))

theorem phi_step {L K D L' K' D' : Nat} (hN : L' + 2 * K' + 1 ≤ L + 2 * K) (hLK : L' + K' ≤ L + K)
    (hD : D' ≤ D) : phi L' K' D' + 9 ≤ phi L K D := by
  unfold phi
  have h := Nat.mul_le_mul (show D' + 1 ≤ D + 1 by omega)
    (show 10 + 10 * D' + 10 * (L' + K') ≤ 10 + 10 * D + 10 * (L + K) by omega)
  generalize (D' + 1) * (10 + 10 * D' + 10 * (L' + K')) = A at h
  generalize (D + 1) * (10 + 10 * D + 10 * (L + K)) = B at h
  omega

theorem phi_elim {L K D L' K' D' : Nat} (hL : L' + 1 = L) (hK : K' ≤ K) (hD : D' + 1 ≤ D) :
    phi L' K' D' + (10 + 10 * D + 10 * L) ≤ phi L K D := by
  unfold phi
  have h := Nat.mul_le_mul (show D' + 1 ≤ D by omega)
    (show 10 + 10 * D' + 10 * (L' + K') ≤ 10 + 10 * D + 10 * (L + K) by omega)
  have e : (D + 1) * (10 + 10 * D + 10 * (L + K)) =
      D * (10 + 10 * D + 10 * (L + K)) + (10 + 10 * D + 10 * (L + K)) := by rw [Nat.add_mul, Nat.one_mul]
  rw [e]
  generalize (D' + 1) * (10 + 10 * D' + 10 * (L' + K')) = A at h
  generalize D * (10 + 10 * D + 10 * (L + K)) = B at h
  omega

theorem phi_ge (L K D : Nat) : 10 + 10 * D + 10 * L ≤ phi L K D := by
  unfold phi
  have e : (D + 1) * (10 + 10 * D + 10 * (L + K)) =
      D * (10 + 10 * D + 10 * (L + K)) + (10 + 10 * D + 10 * (L + K)) := by rw [Nat.add_mul, Nat.one_mul]
  rw [e]
  omega

/-- A bound on the ticks `solve_into` spends. -/
def solveCost (E : Eqns Nat) (o : Pat) : Nat :=
  phi E.length (Eqns.lead E + dcount E o * dcount E o) (dcount E o)

theorem solveCost_ge (E : Eqns Nat) (o : Pat) :
    10 + 10 * dcount E o + 10 * E.length ≤ solveCost E o := phi_ge _ _ _

theorem dcount_tail (t u : Pat) (E : Eqns Nat) (o : Pat) : dcount E o ≤ dcount ((t, u) :: E) o :=
  Finset.card_le_card (Finset.union_subset_union_left (Eqns.subs_tail_subset t u E))

theorem dcount_split (a b c d : Pat) (E : Eqns Nat) (o : Pat) :
    dcount ((a, c) :: (b, d) :: E) o ≤ dcount ((Term.app a b, Term.app c d) :: E) o :=
  Finset.card_le_card (Finset.union_subset_union_left (Eqns.subs_split_subset a b c d E))

theorem solveCost_skip (t : Pat) (E : Eqns Nat) (o : Pat) :
    solveCost E o + 9 ≤ solveCost ((t, t) :: E) o := by
  unfold solveCost
  have hD := dcount_tail t t E o
  have hDD := Nat.mul_le_mul hD hD
  rw [Eqns.lead_skip]
  apply phi_step
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega
  · exact hD

theorem solveCost_split {a b c d : Pat} (E : Eqns Nat) (o : Pat) (h : Term.app a b ≠ Term.app c d) :
    solveCost ((a, c) :: (b, d) :: E) o + 9 ≤ solveCost ((Term.app a b, Term.app c d) :: E) o := by
  unfold solveCost
  have hD := dcount_split a b c d E o
  have hDD := Nat.mul_le_mul hD hD
  have hl := Eqns.lead_split E h
  apply phi_step
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega
  · exact hD

/-- Eliminating a variable leaves fewer distinct subterms. -/
theorem dcount_elim {x : Nat} {u t u' : Pat} (E : Eqns Nat) (o : Pat) (hx : x ∉ u.vars)
    (h : (t = Term.var x ∧ u' = u) ∨ (u' = Term.var x ∧ t = u)) :
    dcount (Eqns.subst x u E) (o.bind (single x u)) < dcount ((t, u') :: E) o := by
  have e : Eqns.subs (Eqns.subst x u E) ∪ (o.bind (single x u)).subs =
      Eqns.subs (Eqns.subst x u ((o, o) :: E)) := by
    show _ = Eqns.subs ((o.bind (single x u), o.bind (single x u)) :: Eqns.subst x u E)
    ext w
    simp only [Eqns.subs_cons, Finset.mem_union]
    tauto
  unfold dcount
  rw [e]
  apply Eqns.card_subs_subst_lt hx
  · intro w hw
    simp only [Eqns.subs_cons, Finset.mem_union] at hw ⊢
    tauto
  · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [Term.subs]
  · intro w hw
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [hw]

theorem solveCost_elim {x : Nat} {u t u' : Pat} (E : Eqns Nat) (o : Pat) (hx : x ∉ u.vars)
    (h : (t = Term.var x ∧ u' = u) ∨ (u' = Term.var x ∧ t = u)) :
    solveCost (Eqns.subst x u E) (o.bind (single x u)) +
        (10 + 10 * dcount ((t, u') :: E) o + 10 * ((t, u') :: E).length) ≤
      solveCost ((t, u') :: E) o := by
  unfold solveCost
  have hD := dcount_elim E o hx h
  have hl : Eqns.lead (Eqns.subst x u E) ≤ dcount (Eqns.subst x u E) (o.bind (single x u)) :=
    (Eqns.lead_le _).trans (Finset.card_le_card Finset.subset_union_left)
  have hm := Nat.mul_le_mul (Nat.le_of_lt hD) (Nat.succ_le_of_lt hD)
  have e : dcount (Eqns.subst x u E) (o.bind (single x u)) *
      (dcount (Eqns.subst x u E) (o.bind (single x u))).succ =
      dcount (Eqns.subst x u E) (o.bind (single x u)) +
        dcount (Eqns.subst x u E) (o.bind (single x u)) *
          dcount (Eqns.subst x u E) (o.bind (single x u)) := by
    rw [Nat.mul_succ]; omega
  rw [e] at hm
  apply phi_elim
  · simp [Eqns.subst]
  · omega
  · omega

end RwLogVerified
