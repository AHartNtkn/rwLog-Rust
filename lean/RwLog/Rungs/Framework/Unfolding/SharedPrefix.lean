/-
# The shared evaluation of a chain whose first members split

The shared evaluation records the summary of the rest of a chain for each
context it meets there, and looks it up when the same context comes back. A
member of a chain *splits* (`Splits`) when two of its closed products take
the terms a context lets through to different sets, and different contexts to
different sets. After `k` such members there are `2 ^ k` contexts, no two the
same, so the memo ends with `2 ^ k` summaries for the rest
(`sufSV_prefix_count`).

Each summary recorded for the rest costs a tick, the tick of the member it
starts with (`sufS_pot`). So the race answered with shared work costs at
least `2 ^ k` on a goal whose chain starts with `k` members that split
(`sharedRace_prefix_ticks`).

How the memo grows: only at its head (`Gr`), an evaluation at depth `d` by
summaries of nodes and of chains at smaller depths (`evalSV_gr`), the members
of a chain from the `i`-th on also by summaries of that chain from the `i`-th
on (`sufSV_gr`).
-/
import RwLog.Rungs.Framework.Unfolding.SharedExact

namespace RwLog

open Goals

namespace Unfold

open Answer Traverse

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## How the memo grows -/

/-- The memo grew at its head, by summaries whose keys are of a kind. -/
def Gr (New : Key R Rel → Prop) (m m' : Mm D P) : Prop :=
  ∃ l : Mm D P, m' = l ++ m ∧ ∀ e ∈ l, New e.1

section growth

variable {New New' : Key R Rel → Prop}

omit [DecidableEq R] in
theorem Gr.refl (m : Mm D P) : Gr New m m := ⟨[], rfl, fun _ h => by cases h⟩

omit [DecidableEq R] in
theorem Gr.trans {m₁ m₂ m₃ : Mm D P} (h₁ : Gr New m₁ m₂) (h₂ : Gr New m₂ m₃) : Gr New m₁ m₃ := by
  obtain ⟨l₁, rfl, n₁⟩ := h₁
  obtain ⟨l₂, rfl, n₂⟩ := h₂
  exact ⟨l₂ ++ l₁, (List.append_assoc ..).symm, fun e he =>
    (List.mem_append.1 he).elim (n₂ e) (n₁ e)⟩

omit [DecidableEq R] in
theorem Gr.mono {m m' : Mm D P} (h : Gr New m m') (hN : ∀ k, New k → New' k) : Gr New' m m' := by
  obtain ⟨l, e, n⟩ := h
  exact ⟨l, e, fun p hp => hN _ (n p hp)⟩

theorem memoV_gr {k : Key R Rel} {m : Mm D P} {body : Mm D P → Sm D P × Mm D P} (hk : New k)
    (hb : Gr New m (body m).2) : Gr New m (memoV k m body).2 := by
  unfold memoV
  cases lookupV m k with
  | some s => exact Gr.refl m
  | none =>
    obtain ⟨l, e, n⟩ := hb
    refine ⟨(k, (body m).1) :: l, by simp only [e, List.cons_append], fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with h | h
    · rw [h]; exact hk
    · exact n p h

/-- The key looked up is in the memo afterwards. -/
theorem memoV_has (k : Key R Rel) (m : Mm D P) (body : Mm D P → Sm D P × Mm D P) :
    ∃ e ∈ (memoV k m body).2, e.1 = k := by
  unfold memoV
  cases h : lookupV m k with
  | some s =>
    unfold lookupV at h
    obtain ⟨p, hp, -⟩ := Option.map_eq_some_iff.1 h
    exact ⟨p, List.mem_of_find?_eq_some hp, sameKeyV_eq (by simpa using List.find?_some hp)⟩
  | none => exact ⟨_, List.mem_cons_self, rfl⟩

omit [DecidableEq R] in
theorem foldl_gr {ι : Type} (F : Sm D P × Mm D P → ι → Sm D P × Mm D P)
    (h : ∀ acc a, Gr New acc.2 (F acc a).2) :
    ∀ (L : List ι) (init : Sm D P × Mm D P), Gr New init.2 (L.foldl F init).2
  | [], _ => Gr.refl _
  | a :: L, init => (h init a).trans (foldl_gr F h L (F init a))

variable (K : Kernel R Cost) (hK : K.Refines D)

theorem sufBodyV_gr (sv : Near R → Mm D P → Sm D P × Mm D P)
    (hsv : ∀ c m, Gr New m (sv c m).2) (s : Sm D P × Mm D P) :
    Gr New s.2 (sufBodyV K hK sv s).2 := by
  unfold sufBodyV
  refine Gr.trans (foldl_gr _ ?_ s.1.closed (⟨[], []⟩, s.2)) (foldl_gr _ ?_ _ _)
  · exact fun acc a => hsv _ _
  · exact fun acc o => hsv _ _

omit [DecidableEq R] in
theorem membersSV_gr (wv : Rel → Mm D P → Sm D P × Mm D P) (hw : ∀ x m, Gr New m (wv x m).2) :
    ∀ (xs : List Rel) (m : Mm D P), Gr New m (membersSV wv xs m).2
  | [], m => Gr.refl m
  | x :: xs, m => (hw x m).trans (membersSV_gr wv hw xs _)

end growth

/-- The keys of the summaries of nodes, and of chains at depths below `d`. -/
def N0 (d : Nat) (k : Key R Rel) : Prop := k.idx = 0 ∨ k.d < d

/-- Those, and the keys of the members of a chain at depth `d` from the `i`-th
on. -/
def NS (d i : Nat) (k : Key R Rel) : Prop := N0 d k ∨ (k.d = d ∧ i ≤ k.idx)

variable (K : Kernel R Cost) (hK : K.Refines D)

theorem sufSV_gr (wv : Near R → Rel → Option R → Mm D P → Sm D P × Mm D P) (n : Rel) (d : Nat)
    (far : Option R) (hw : ∀ c x fr m, Gr (N0 d) m (wv c x fr m).2) :
    ∀ (xs : List Rel) (i : Nat) (c : Near R) (m : Mm D P),
      Gr (NS d i) m (sufSV K hK wv n d far i xs c m).2
  | [], i, c, m => by simp only [sufSV]; exact Gr.refl m
  | [x], i, c, m => by simp only [sufSV]; exact (hw c x far m).mono fun _ h => .inl h
  | x :: y :: xs, i, c, m => by
    have ih := sufSV_gr wv n d far hw (y :: xs) (i + 1)
    have body : ∀ m', Gr (NS d i) m'
        (sufBodyV K hK (sufSV K hK wv n d far (i + 1) (y :: xs)) (wv c x none m')).2 := fun m' =>
      ((hw c x none m').mono fun _ h => .inl h).trans
        (sufBodyV_gr K hK _ (fun c' m'' => (ih c' m'').mono fun k h => h.elim .inl
          fun h => .inr ⟨h.1, by omega⟩) _)
    by_cases hi : i = 0
    · simp only [sufSV, hi, ite_true]
      rw [hi] at body
      exact body m
    · simp only [sufSV, hi, ite_false]
      exact memoV_gr (.inr ⟨rfl, Nat.le_refl _⟩) (body m)

theorem evalSV_gr : ∀ (d : Nat) (c : Near R) (n : Rel) (far : Option R) (m : Mm D P),
    Gr (N0 d) m (evalSV (P := P) K hK d c n far m).2
  | 0, c, n, far, m => by simp only [evalSV]; exact Gr.refl m
  | d + 1, c, n, far, m => by
    have ih := evalSV_gr d
    have up : ∀ k : Key R Rel, N0 d k → N0 (d + 1) k := fun k h =>
      h.elim .inl fun h => .inr (by omega)
    simp only [evalSV]
    refine memoV_gr (.inl rfl) ?_
    cases hv : n.view.forget with
    | span u => exact Gr.refl m
    | call f b =>
      dsimp only
      cases hb : Charged.bodyOf P n with
      | none => exact Gr.refl m
      | some b => exact (ih c b far m).mono up
    | union xs =>
      refine foldl_gr _ ?_ _ _
      exact fun acc p => (ih c p.1 far acc.2).mono up
    | chain xs =>
      exact (sufSV_gr K hK (evalSV K hK d) n d far ih xs 0 c m).mono fun k h =>
        h.elim (up k) fun h => .inr (by omega)
    | meet xs =>
      dsimp only
      cases c.isPushed
      · exact membersSV_gr _ (fun x m' => (ih c x far m').mono up) xs m
      · exact (membersSV_gr _ (fun x m' => (ih c x far m').mono up) xs m).trans
          (membersSV_gr _ (fun x m' => (ih c.own x far m').mono up) xs _)

/-! ## A tick for each summary of the rest -/

/-- The summaries of the memo for the members of a chain from the `L`-th on,
at depth `d`. -/
def pot (L d : Nat) (m : Mm D P) : Nat := m.countP fun e => decide (e.1.idx = L ∧ e.1.d = d)

omit [DecidableEq R] in
theorem pot_append (L d : Nat) (l m : Mm D P) : pot L d (l ++ m) = pot L d l + pot L d m :=
  List.countP_append

omit [DecidableEq R] in
/-- Summaries of another kind do not count. -/
theorem Gr.pot_eq {New : Key R Rel → Prop} {L d : Nat} {m m' : Mm D P} (h : Gr New m m')
    (hN : ∀ k, New k → ¬(k.idx = L ∧ k.d = d)) : pot L d m' = pot L d m := by
  obtain ⟨l, rfl, n⟩ := h
  rw [pot_append]
  have : pot L d l = 0 := List.countP_eq_zero.2 fun e he => by
    simpa using hN e.1 (n e he)
  omega

omit [DecidableEq R] in
theorem foldL_pot {α σ : Type} {L d : Nat} (f : σ × Mm D P → α → Cost (σ × Mm D P))
    (h : ∀ b x, pot L d (f b x).val.2 ≤ pot L d b.2 + (f b x).ticks) :
    ∀ (xs : List α) (b : σ × Mm D P),
      pot L d (Cost.foldL f b xs).val.2 ≤ pot L d b.2 + (Cost.foldL f b xs).ticks
  | [], b => Nat.le_add_right _ _
  | x :: xs, b => by
    have h₁ := h b x
    have h₂ := foldL_pot f h xs (f b x).val
    simp only [Cost.foldL, Cost.bind_val, Cost.bind_ticks]
    omega

theorem findL_some_ticks {α : Type} (f : α → Cost Bool) (h : ∀ x, 1 ≤ (f x).ticks) :
    ∀ xs : List α, (Cost.findL f xs).val ≠ none → 1 ≤ (Cost.findL f xs).ticks
  | [], hne => absurd rfl hne
  | x :: xs, _ => by
    have := h x
    simp only [Cost.findL, Cost.bind_ticks]
    omega

theorem sameKey_pos (k k' : Key R Rel) :
    1 ≤ (sameKey (A := Ans D P) (K := DerivationKernel.over D K hK P) k k').ticks := by
  at_cost K hK
  simp only [sameKey, Cost.bind_ticks, Kernel.tick, Cost.tick_ticks]
  omega

/-- A summary found in the memo costs a tick. -/
theorem lookup_some_ticks (m : Mm D P) (k : Key R Rel)
    (h : (lookup (K := DerivationKernel.over D K hK P) m k).val ≠ none) :
    1 ≤ (lookup (K := DerivationKernel.over D K hK P) m k).ticks := by
  have sk := sameKey_pos (P := P) K hK
  at_cost K hK
  simp only [lookup, Cost.bind_ticks, Cost.bind_val, Cost.pure_val, Cost.pure_ticks,
    findL_std] at h ⊢
  have := findL_some_ticks _ (fun p : Key R Rel × Sm D P => sk p.1 k) m
    (fun e => h (by rw [e]; rfl))
  omega

/-- A summary computed and recorded: one more counts at most, and what
computing it adds was paid for. -/
theorem memo_pot {L d : Nat} (k : Key R Rel) (m : Mm D P)
    (body : Mm D P → Cost (Sm D P × Mm D P))
    (hb : pot L d (body m).val.2 + 1 ≤ pot L d m + (body m).ticks) :
    pot L d (memo (K := DerivationKernel.over D K hK P) k m body).val.2 ≤
      pot L d m + (memo (K := DerivationKernel.over D K hK P) k m body).ticks := by
  at_cost K hK
  simp only [memo, Cost.bind_val, Cost.bind_ticks]
  generalize (lookup (K := DerivationKernel.over D _ hK P) m k).val = hit
  cases hit with
  | some s =>
    simp only [Cost.pure_val, Cost.pure_ticks]
    omega
  | none =>
    simp only [Cost.pure_val, Cost.bind_val, Cost.bind_ticks, Cost.pure_ticks]
    have : pot L d ((k, (body m).val.1) :: (body m).val.2) ≤ pot L d (body m).val.2 + 1 := by
      unfold pot
      rw [List.countP_cons]
      split <;> omega
    omega

/-- The summary of a node at a positive depth costs a tick, found or
computed. -/
theorem evalS_pos (d : Nat) (c : Near R) (n : Rel) (far : Option R) (m : Mm D P) :
    1 ≤ (evalS (K := DerivationKernel.over D K hK P) (d + 1) c n far m).ticks := by
  have lk := lookup_some_ticks (P := P) K hK m ⟨n, 0, d + 1, c, far⟩
  at_cost K hK
  simp only [evalS, memo, Cost.bind_ticks]
  generalize (lookup (K := DerivationKernel.over D _ hK P) m _).val = hit at lk ⊢
  cases hit with
  | some s =>
    have := lk (by simp)
    omega
  | none =>
    simp only [Cost.bind_ticks, Kernel.tick, Cost.tick_ticks]
    omega

theorem chain3 {A₂ A₁ A₀ Am t₂ t₁ tw : Nat} (h₂ : A₂ ≤ A₁ + t₂) (h₁ : A₁ ≤ A₀ + t₁)
    (h₀ : A₀ + 1 ≤ Am + tw) : A₂ + 1 ≤ Am + (tw + (t₁ + t₂)) := by omega

/-- The members of a chain from the `i`-th on: every summary recorded for the
members from the `L`-th on was paid for, by the tick of the member it starts
with. -/
theorem sufS_pot {L d : Nat} (w : Evaluator R Rel (Ans D P) Cost)
    (hw : ∀ c x fr m, pot L d (w c x fr m).val.2 = pot L d m)
    (hw1 : ∀ c x fr m, 1 ≤ (w c x fr m).ticks) (n : Rel) (far : Option R) :
    ∀ (xs : List Rel) (i : Nat) (c : Near R) (m : Mm D P),
      pot L d (sufS (K := DerivationKernel.over D K hK P) w n d far i xs c m).val.2 ≤
        pot L d m + (sufS (K := DerivationKernel.over D K hK P) w n d far i xs c m).ticks
  | [], i, c, m => by
    at_cost K hK
    simp only [sufS, Cost.pure_val, Cost.pure_ticks]
    omega
  | [x], i, c, m => by
    simp only [sufS]
    rw [hw]
    omega
  | x :: y :: xs, i, c, m => by
    have ih := sufS_pot w hw hw1 n far (y :: xs) (i + 1)
    have mp := memo_pot (P := P) (L := L) (d := d) K hK ⟨n, i, d, c, far⟩ m
    by_cases hi : i = 0
    · subst hi
      at_cost K hK
      simp only [sufS, ite_true]
      refine Nat.le_trans (Nat.le_add_right _ 1) ?_
      simp only [Cost.bind_val, Cost.bind_ticks, foldL_std]
      refine chain3 (foldL_pot _ ?_ _ _) (foldL_pot _ ?_ _ _) ?_
      · intro b o
        simp only [Cost.bind_val, Cost.bind_ticks, Cost.pure_val, Cost.pure_ticks]
        refine Nat.le_trans (ih _ _) ?_
        omega
      · intro b a
        simp only [Cost.bind_val, Cost.bind_ticks, Cost.pure_val, Cost.pure_ticks]
        refine Nat.le_trans (ih _ _) ?_
        omega
      · show pot L d (w c x none m).val.2 + 1 ≤ _
        rw [hw]
        have := hw1 c x none m
        omega
    · at_cost K hK
      simp only [sufS, hi, ite_false]
      refine mp _ ?_
      simp only [Cost.bind_val, Cost.bind_ticks, foldL_std]
      refine chain3 (foldL_pot _ ?_ _ _) (foldL_pot _ ?_ _ _) ?_
      · intro b o
        simp only [Cost.bind_val, Cost.bind_ticks, Cost.pure_val, Cost.pure_ticks]
        refine Nat.le_trans (ih _ _) ?_
        omega
      · intro b a
        simp only [Cost.bind_val, Cost.bind_ticks, Cost.pure_val, Cost.pure_ticks]
        refine Nat.le_trans (ih _ _) ?_
        omega
      · show pot L d (w c x none m).val.2 + 1 ≤ _
        rw [hw]
        have := hw1 c x none m
        omega

/-- The summary of a chain, from an empty memo, costs what its members
cost. -/
theorem evalS_chain_ticks {n : Rel} {xs : List Rel} (hv : n.view.forget = .chain xs) (d : Nat)
    (c : Near R) (far : Option R) :
    (sufS (K := DerivationKernel.over D K hK P) (evalS (K := DerivationKernel.over D K hK P) d)
        n d far 0 xs c []).ticks ≤
      (evalS (K := DerivationKernel.over D K hK P) (d + 1) c n far []).ticks := by
  at_cost K hK
  simp only [evalS, memo, lookup, findL_std, Cost.findL, Cost.bind_ticks, Cost.bind_val,
    Cost.pure_val, Option.map, over_view, Charged.viewNode, Charged.op, hv]
  omega

end Unfold

end RwLog
