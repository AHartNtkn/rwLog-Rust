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

/-! ## Members that split -/

/-- Two closed products of a member that take the terms a context lets
through to different sets, and different contexts to different sets. -/
structure Splits (P : Program) (M : Interp) (d : Nat) (x : Rel) (Y : Bool → PRel) : Prop where
  mem : ∀ f, SP.closed (Y f) ∈ SED P M false d Set.univ x Set.univ
  live : ∀ f (X : Set GTerm), X.Nonempty → (postS X (Y f)).Nonempty
  inj : ∀ f g (X X' : Set GTerm), X.Nonempty → X'.Nonempty →
    postS X (Y f) = postS X' (Y g) → f = g ∧ X = X'

/-- The contexts after the members `Bs`, from one context: one for each
choice of a product at each member. -/
def reachL (W : Rel → Bool → PRel) : List Rel → Set GTerm → List (Set GTerm)
  | [], X => [X]
  | b :: Bs, X => reachL W Bs (postS X (W b false)) ++ reachL W Bs (postS X (W b true))

section reach

variable {M : Interp} {d : Nat} {W : Rel → Bool → PRel}

theorem reachL_length : ∀ (Bs : List Rel) (X : Set GTerm),
    (reachL W Bs X).length = 2 ^ Bs.length
  | [], _ => rfl
  | b :: Bs, X => by
    simp only [reachL, List.length_append, reachL_length Bs, List.length_cons, Nat.pow_succ]
    omega

theorem reachL_cons {b : Rel} {Bs : List Rel} {X Z : Set GTerm} :
    Z ∈ reachL W (b :: Bs) X ↔ ∃ f, Z ∈ reachL W Bs (postS X (W b f)) := by
  simp only [reachL, List.mem_append]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨f, h⟩
    cases f
    · exact .inl h
    · exact .inr h

/-- Different contexts are followed by different contexts. -/
theorem reachL_inj : ∀ (Bs : List Rel), (∀ b ∈ Bs, Splits P M d b (W b)) →
    ∀ (X X' Z : Set GTerm), X.Nonempty → X'.Nonempty → Z ∈ reachL W Bs X →
      Z ∈ reachL W Bs X' → X = X'
  | [], _, X, X', Z, _, _, h, h' => by
    simp only [reachL, List.mem_singleton] at h h'
    rw [← h, h']
  | b :: Bs, H, X, X', Z, hX, hX', h, h' => by
    obtain ⟨f, hf⟩ := reachL_cons.1 h
    obtain ⟨g, hg⟩ := reachL_cons.1 h'
    have hb := H b List.mem_cons_self
    have := reachL_inj Bs (fun z hz => H z (List.mem_cons_of_mem _ hz)) _ _ Z (hb.live f X hX)
      (hb.live g X' hX') hf hg
    exact (hb.inj f g X X' hX hX' this).2

theorem reachL_nodup : ∀ (Bs : List Rel), (∀ b ∈ Bs, Splits P M d b (W b)) →
    ∀ X : Set GTerm, X.Nonempty → (reachL W Bs X).Nodup
  | [], _, X, _ => by simp [reachL]
  | b :: Bs, H, X, hX => by
    have hb := H b List.mem_cons_self
    have H' : ∀ z ∈ Bs, Splits P M d z (W z) := fun z hz => H z (List.mem_cons_of_mem _ hz)
    simp only [reachL]
    refine List.nodup_append.2 ⟨reachL_nodup Bs H' _ (hb.live false X hX),
      reachL_nodup Bs H' _ (hb.live true X hX), ?_⟩
    rintro Z h Z' h' rfl
    have := reachL_inj Bs H' _ _ Z (hb.live false X hX) (hb.live true X hX) h h'
    exact Bool.noConfusion (hb.inj false true X X hX hX this).1

end reach

/-! ## The summaries of the rest that the memo ends with -/

section count

variable (hL : D.Lawful P.sorts.interp)

local notation "𝕄" => P.sorts.interp

/-- The memo has a summary for the members from the `L`-th on after a context
that lets `Z` through. -/
def HasL (L d : Nat) (m : Mm D P) (Z : Set GTerm) : Prop :=
  ∃ e ∈ m, e.1.idx = L ∧ e.1.d = d ∧ bset 𝕄 e.1.near.bound = Z

omit [DecidableEq R] in
theorem HasL.mono {L d : Nat} {m : Mm D P} {Z : Set GTerm} (l : Mm D P) (h : HasL L d m Z) :
    HasL L d (l ++ m) Z := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, List.mem_append_right _ he, h⟩

omit [DecidableEq R] in
/-- Summaries after different contexts are different summaries. -/
theorem pot_ge {L d : Nat} {m : Mm D P} {l : List (Set GTerm)} (hn : l.Nodup)
    (h : ∀ Z ∈ l, HasL L d m Z) : l.length ≤ pot L d m := by
  have sub : l ⊆ (m.filter fun e => decide (e.1.idx = L ∧ e.1.d = d)).map
      fun e => bset 𝕄 e.1.near.bound := by
    intro Z hZ
    obtain ⟨e, he, h₁, h₂, rfl⟩ := h Z hZ
    exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp [h₁, h₂]⟩, rfl⟩
  have := (List.subperm_of_subset hn sub).length_le
  rwa [List.length_map, ← List.countP_eq_length_filter] at this

/-- Wherever the memo has a summary for the members of the chain from one of
the first on, it has one for the rest after every context that follows. -/
def InvL (W : Rel → Bool → PRel) (BsAll : List Rel) (d : Nat) (m : Mm D P) : Prop :=
  ∀ e ∈ m, e.1.d = d → 0 < e.1.idx → e.1.idx ≤ BsAll.length →
    ∀ Z ∈ reachL W (BsAll.drop e.1.idx) (bset 𝕄 e.1.near.bound), HasL BsAll.length d m Z

omit [DecidableEq R] in
theorem InvL.ext {W : Rel → Bool → PRel} {BsAll : List Rel} {d : Nat} {m : Mm D P}
    (h : InvL W BsAll d m) (l : Mm D P)
    (hl : ∀ e ∈ l, e.1.d = d → 0 < e.1.idx → e.1.idx ≤ BsAll.length →
      ∀ Z ∈ reachL W (BsAll.drop e.1.idx) (bset 𝕄 e.1.near.bound),
        HasL BsAll.length d (l ++ m) Z) :
    InvL W BsAll d (l ++ m) := by
  intro e he h₁ h₂ h₃ Z hZ
  rcases List.mem_append.1 he with he | he
  · exact hl e he h₁ h₂ h₃ Z hZ
  · exact (h e he h₁ h₂ h₃ Z hZ).mono l

omit [DecidableEq R] in
/-- A fold that threads the memo: what each step keeps is kept, and what a
step leaves in the memo stays. -/
theorem foldl_track {ι : Type} (F : Sm D P × Mm D P → ι → Sm D P × Mm D P) (J : Mm D P → Prop)
    (Post : ι → Mm D P → Prop) (hmono : ∀ a m l, Post a m → Post a (l ++ m)) :
    ∀ (L : List ι) (init : Sm D P × Mm D P),
      (∀ a ∈ L, ∀ acc, J acc.2 →
        J (F acc a).2 ∧ (∃ l, (F acc a).2 = l ++ acc.2) ∧ Post a (F acc a).2) →
      J init.2 →
      J (L.foldl F init).2 ∧ (∃ l, (L.foldl F init).2 = l ++ init.2) ∧
        ∀ a ∈ L, Post a (L.foldl F init).2
  | [], init, _, hJ => ⟨hJ, ⟨[], rfl⟩, fun _ h => by cases h⟩
  | a :: L, init, hs, hJ => by
    obtain ⟨hJ₁, ⟨l₁, e₁⟩, hP₁⟩ := hs a List.mem_cons_self init hJ
    obtain ⟨hJ₂, ⟨l₂, e₂⟩, hP₂⟩ := foldl_track F J Post hmono L (F init a)
      (fun b hb => hs b (List.mem_cons_of_mem _ hb)) hJ₁
    refine ⟨hJ₂, ⟨l₂ ++ l₁, ?_⟩, fun b hb => ?_⟩
    · simp only [List.foldl_cons]
      rw [e₂, e₁, List.append_assoc]
    · simp only [List.foldl_cons]
      rcases List.mem_cons.1 hb with rfl | hb
      · rw [e₂]
        exact hmono _ _ _ hP₁
      · exact hP₂ b hb

variable (K : Kernel R Cost) (hK : K.Refines D)

/-- The first member's summary followed by the summary of the rest: the same
for the memo. -/
theorem sufBodyV_track (sv : Near R → Mm D P → Sm D P × Mm D P) (s : Sm D P × Mm D P)
    (J : Mm D P → Prop) (Post : Ans D P → Mm D P → Prop)
    (hmono : ∀ a m l, Post a m → Post a (l ++ m))
    (h₁ : ∀ a ∈ s.1.closed, ∀ m, J m → J (sv ⟨D.rightBound a.span, true⟩ m).2 ∧
      (∃ l, (sv ⟨D.rightBound a.span, true⟩ m).2 = l ++ m) ∧
      Post a (sv ⟨D.rightBound a.span, true⟩ m).2)
    (h₂ : ∀ o ∈ s.1.opens, ∀ m, J m → J (sv ⟨o, o.isSome⟩ m).2 ∧
      ∃ l, (sv ⟨o, o.isSome⟩ m).2 = l ++ m)
    (hJ : J s.2) :
    J (sufBodyV K hK sv s).2 ∧ (∃ l, (sufBodyV K hK sv s).2 = l ++ s.2) ∧
      ∀ a ∈ s.1.closed, Post a (sufBodyV K hK sv s).2 := by
  unfold sufBodyV
  generalize hr₁ : List.foldl _ ((⟨[], []⟩ : Sm D P), s.2) s.1.closed = r₁
  have T₁ : J r₁.2 ∧ (∃ l, r₁.2 = l ++ s.2) ∧ ∀ a ∈ s.1.closed, Post a r₁.2 := by
    rw [← hr₁]
    exact foldl_track _ J Post hmono _ _ (fun a ha acc hacc => h₁ a ha acc.2 hacc) hJ
  obtain ⟨J₁, ⟨l₁, e₁⟩, P₁⟩ := T₁
  generalize hr₂ : List.foldl _ r₁ s.1.opens = r₂
  have T₂ : J r₂.2 ∧ (∃ l, r₂.2 = l ++ r₁.2) ∧ ∀ o ∈ s.1.opens, True := by
    rw [← hr₂]
    exact foldl_track _ J (fun _ _ => True) (fun _ _ _ h => h) _ _
      (fun o ho acc hacc => ⟨(h₂ o ho acc.2 hacc).1, (h₂ o ho acc.2 hacc).2, trivial⟩) J₁
  obtain ⟨J₂, ⟨l₂, e₂⟩, -⟩ := T₂
  refine ⟨J₂, ⟨l₂ ++ l₁, by rw [e₂, e₁, List.append_assoc]⟩, fun a ha => ?_⟩
  rw [e₂]
  exact hmono _ _ _ (P₁ a ha)

include hL in
omit [DecidableEq R] in
/-- A closed product of a member is among the answers of its summary; the
answer leaves the context the product takes the context to. -/
theorem closed_after {c : Near R} {x : Rel} {d : Nat} {s : Sm D P} {Y : PRel}
    (hs : SemS 𝕄 s = WT P 𝕄 false d c x none) (hc : c.pushed = true ∨ c.bound = none)
    (hY : SP.closed Y ∈ SED P 𝕄 false d Set.univ x Set.univ)
    (hne : (postS (bset 𝕄 c.bound) Y).Nonempty) :
    ∃ a ∈ s.closed, bset 𝕄 (D.rightBound a.span) = postS (bset 𝕄 c.bound) Y := by
  have hW : SP.closed (restrD false (bset 𝕄 c.bound) Y) ∈ WS P 𝕄 false d c x none := by
    rcases hc with hp | hb
    · unfold WS
      rw [ite_eq_left_of_eq_true _ _ (eq_true hp)]
      obtain ⟨z, m, hm, hmz⟩ := hne
      exact ⟨_, hY, .closed ⟨(m, z), hmz, hm, trivial⟩⟩
    · rw [ws_none hL hb (isBound_none D), hb]
      have : restrD false (bset 𝕄 (none : Option R)) Y = Y := by
        ext ⟨u, v⟩
        exact ⟨fun h => h.1, fun h => ⟨h, trivial, trivial⟩⟩
      rw [this]
      exact hY
  have hm : SI.closed (restrD false (bset 𝕄 c.bound) Y) ∈ SemS 𝕄 s := by
    rw [hs]
    exact ⟨_, hW, rfl⟩
  obtain ⟨a, ha, e⟩ := sems_closed_iff.1 hm
  refine ⟨a, ha, ?_⟩
  rw [bset_rightBound hL, e]
  exact farEnds_restrD false _ _

theorem lookupV_some {m : Mm D P} {k : Key R Rel} {s : Sm D P} (h : lookupV m k = some s) :
    ∃ p ∈ m, p.1 = k := by
  unfold lookupV at h
  obtain ⟨p, hp, -⟩ := Option.map_eq_some_iff.1 h
  exact ⟨p, List.mem_of_find?_eq_some hp, sameKeyV_eq (by simpa using List.find?_some hp)⟩

include hL in
/-- The members of a chain from the `i`-th on, the first of which split: the
memo ends with a summary of the rest after every context that follows the
context they are evaluated after. -/
theorem sufSV_split (hP : ProgFO P) {n : Rel} {d : Nat} {far : Option R} (hfar : IsBound D far)
    (hn : Normal n) (hfo : n.FO) {BsAll : List Rel} {y : Rel} {ys : List Rel} (hys : ys ≠ [])
    (hBs : BsAll ≠ []) (hv : n.view.forget = .chain (BsAll ++ y :: ys)) (W : Rel → Bool → PRel)
    (HB : ∀ b ∈ BsAll, Splits P 𝕄 d b (W b)) :
    ∀ (Bs : List Rel) (i : Nat) (c : Near R) (m : Mm D P), BsAll.drop i = Bs →
      i + Bs.length = BsAll.length → IsBound D c.bound → (c.pushed = true ∨ c.bound = none) →
      MemoOk m ∧ MemoEx m ∧ InvL (P := P) W BsAll d m →
      (MemoOk (sufSV K hK (evalSV K hK d) n d far i (Bs ++ y :: ys) c m).2 ∧
          MemoEx (sufSV K hK (evalSV K hK d) n d far i (Bs ++ y :: ys) c m).2 ∧
          InvL (P := P) W BsAll d (sufSV K hK (evalSV K hK d) n d far i (Bs ++ y :: ys) c m).2) ∧
        (∃ l, (sufSV K hK (evalSV K hK d) n d far i (Bs ++ y :: ys) c m).2 = l ++ m) ∧
        ∀ Z ∈ reachL W Bs (bset 𝕄 c.bound),
          HasL (P := P) BsAll.length d
            (sufSV K hK (evalSV K hK d) n d far i (Bs ++ y :: ys) c m).2 Z := by
  have hvc := forget_chain hv
  obtain ⟨-, hmem, -⟩ := hn.view_chain hvc
  have HW : MembersS (P := P) (evalSV K hK d) d (BsAll ++ y :: ys) :=
    fun x hx c' fr m₂ hm₂ hc' hfr => evalS_ok hL K hK hP d c' x fr m₂ hm₂ hc' hfr (hmem x hx).1
      (hfo.view_members (by rw [hvc]; exact hx))
  have HX : MembersEx (P := P) (evalSV K hK d) d (BsAll ++ y :: ys) :=
    fun x hx c' fr m₂ hm₂ hmx₂ hc' hfr => evalS_ex hL K hK hP d c' x fr m₂ hm₂ hmx₂ hc' hfr
      (hmem x hx).1 (hfo.view_members (by rw [hvc]; exact hx))
  have hns : ∀ x ∈ BsAll ++ y :: ys, NotSeq x := fun x hx => (hmem x hx).2
  have hpos : 0 < BsAll.length := List.length_pos_of_ne_nil hBs
  -- what the lemmas about the summary say of the members from the `i`-th on
  have whole : ∀ (xs : List Rel) (i : Nat) (c : Near R) (m : Mm D P), xs ≠ [] →
      (BsAll ++ y :: ys).drop i = xs → IsBound D c.bound → MemoOk m → MemoEx m →
      MemoOk (sufSV K hK (evalSV K hK d) n d far i xs c m).2 ∧
        MemoEx (sufSV K hK (evalSV K hK d) n d far i xs c m).2 := by
    intro xs i c m hne hdrop hc hm hmx
    have sub : ∀ x ∈ xs, x ∈ BsAll ++ y :: ys := fun x hx =>
      List.mem_of_mem_drop (hdrop ▸ hx)
    exact ⟨(suf_ok hL K hK (evalSV K hK d) hfar hn hfo hv xs i c m hne hdrop
        (fun x hx => HW x (sub x hx)) (fun x hx => hns x (sub x hx)) hm hc).2,
      (suf_ex hL K hK (evalSV K hK d) hfar hn hfo hv xs i c m hne hdrop
        (fun x hx => HW x (sub x hx)) (fun x hx => HX x (sub x hx))
        (fun x hx => hns x (sub x hx)) hm hmx hc).2⟩
  intro Bs
  induction Bs with
  | nil =>
    intro i c m hd hlen hc _ ⟨hm, hmx, hinv⟩
    obtain ⟨y', ys', rfl⟩ := List.exists_cons_of_ne_nil hys
    have hi : i = BsAll.length := by simpa using hlen
    have hi0 : i ≠ 0 := by omega
    have hdrop : (BsAll ++ y :: y' :: ys').drop i = y :: y' :: ys' := by
      rw [List.drop_append_of_le_length (by omega), hd]
      rfl
    simp only [List.nil_append]
    obtain ⟨ok, ex⟩ := whole _ i c m (by simp) hdrop hc hm hmx
    obtain ⟨l, el, nl⟩ := sufSV_gr K hK (evalSV K hK d) n d far (evalSV_gr K hK d)
      (y :: y' :: ys') i c m
    have has : ∃ e ∈ (sufSV K hK (evalSV K hK d) n d far i (y :: y' :: ys') c m).2,
        e.1 = ⟨n, i, d, c, far⟩ := by
      simp only [sufSV, hi0, ite_false]
      exact memoV_has _ _ _
    refine ⟨⟨ok, ex, ?_⟩, ⟨l, el⟩, ?_⟩
    · rw [el]
      refine hinv.ext l fun e he hde h0 hle Z hZ => ?_
      have hidx : e.1.idx = BsAll.length := by
        rcases nl e he with (h | h) | h
        · omega
        · omega
        · omega
      rw [hidx, List.drop_length] at hZ
      simp only [reachL, List.mem_singleton] at hZ
      exact ⟨e, List.mem_append_left _ he, hidx, hde, hZ.symm⟩
    · intro Z hZ
      simp only [reachL, List.mem_singleton] at hZ
      obtain ⟨e, he, hk⟩ := has
      exact ⟨e, he, by rw [hk]; exact hi, by rw [hk], by rw [hk]; exact hZ.symm⟩
  | cons b Bs' ih =>
    intro i c m hd hlen hc hpc ⟨hm, hmx, hinv⟩
    have hlen' : i + 1 + Bs'.length = BsAll.length := by
      simp only [List.length_cons] at hlen
      omega
    have hd' : BsAll.drop (i + 1) = Bs' := by
      rw [← List.tail_drop, hd]
      rfl
    have hbm : b ∈ BsAll := List.mem_of_mem_drop (hd ▸ List.mem_cons_self)
    have hb := HB b hbm
    have hbx : b ∈ BsAll ++ y :: ys := List.mem_append_left _ hbm
    have hdrop : (BsAll ++ y :: ys).drop i = b :: (Bs' ++ y :: ys) := by
      rw [List.drop_append_of_le_length (by omega), hd]
      rfl
    obtain ⟨ok, ex⟩ := whole _ i c m (by simp) hdrop hc hm hmx
    obtain ⟨z, zs, hz⟩ : ∃ z zs, Bs' ++ y :: ys = z :: zs := by
      cases Bs' <;> exact ⟨_, _, rfl⟩
    simp only [List.cons_append, hz] at ih ok ex ⊢
    -- the first member, then the rest after each of its products
    obtain ⟨ok_s, mok_s⟩ := evalS_ok hL K hK hP d c b none m hm hc (isBound_none D)
      (hmem b hbx).1 (hfo.view_members (by rw [hvc]; exact hbx))
    obtain ⟨ex_s, mex_s⟩ := evalS_ex hL K hK hP d c b none m hm hmx hc (isBound_none D)
      (hmem b hbx).1 (hfo.view_members (by rw [hvc]; exact hbx))
    obtain ⟨l₀, e₀, n₀⟩ := evalSV_gr (P := P) K hK d c b none m
    have inv_s : InvL (P := P) W BsAll d (evalSV K hK d c b none m).2 := by
      rw [e₀]
      refine hinv.ext l₀ fun e he hde h0 _ => ?_
      rcases n₀ e he with h | h <;> omega
    obtain ⟨JB, ⟨lB, eB⟩, PB⟩ := sufBodyV_track K hK
      (sufSV K hK (evalSV K hK d) n d far (i + 1) (z :: zs)) (evalSV K hK d c b none m)
      (fun m => MemoOk m ∧ MemoEx m ∧ InvL (P := P) W BsAll d m)
      (fun a m => ∀ Z ∈ reachL W Bs' (bset 𝕄 (D.rightBound a.span)),
        HasL (P := P) BsAll.length d m Z)
      (fun a m l h Z hZ => (h Z hZ).mono l)
      (fun a _ m₂ hm₂ => ih (i + 1) ⟨D.rightBound a.span, true⟩ m₂ hd' hlen'
        (isBound_right hL _) (.inl rfl) hm₂)
      (fun o ho m₂ hm₂ => by
        have := ih (i + 1) ⟨o, o.isSome⟩ m₂ hd' hlen' (ok_s.bound o ho)
          (by cases o
              · exact .inr rfl
              · exact .inl rfl) hm₂
        exact ⟨this.1, this.2.1⟩)
      ⟨mok_s, mex_s, inv_s⟩
    have reach : ∀ Z ∈ reachL W (b :: Bs') (bset 𝕄 c.bound),
        HasL (P := P) BsAll.length d
          (sufBodyV K hK (sufSV K hK (evalSV K hK d) n d far (i + 1) (z :: zs))
            (evalSV K hK d c b none m)).2 Z := by
      intro Z hZ
      obtain ⟨f, hf⟩ := reachL_cons.1 hZ
      obtain ⟨a, ha, ea⟩ := closed_after hL ex_s hpc (hb.mem f)
        (hb.live f _ (bset_nonempty hL hc))
      exact PB a ha Z (by rw [ea]; exact hf)
    by_cases hi0 : i = 0
    · simp only [sufSV, hi0, ite_true]
      rw [hi0] at JB eB reach
      exact ⟨JB, ⟨lB ++ l₀, by rw [eB, e₀, List.append_assoc]⟩, reach⟩
    · simp only [sufSV, hi0, ite_false] at ok ex ⊢
      unfold memoV at ok ex ⊢
      cases hlk : lookupV m ⟨n, i, d, c, far⟩ with
      | some s' =>
        refine ⟨⟨hm, hmx, hinv⟩, ⟨[], rfl⟩, ?_⟩
        obtain ⟨p, hp, hpk⟩ := lookupV_some hlk
        have := hinv p hp
        rw [hpk] at this
        have := this rfl (by show 0 < i; omega) (by show i ≤ BsAll.length; omega)
        rw [show BsAll.drop i = b :: Bs' from hd] at this
        exact this
      | none =>
        simp only [hlk] at ok ex
        have inv' : InvL (P := P) W BsAll d
            ((⟨n, i, d, c, far⟩,
              (sufBodyV K hK (sufSV K hK (evalSV K hK d) n d far (i + 1) (z :: zs))
                (evalSV K hK d c b none m)).1) ::
              (sufBodyV K hK (sufSV K hK (evalSV K hK d) n d far (i + 1) (z :: zs))
                (evalSV K hK d c b none m)).2) := by
          refine JB.2.2.ext [_] fun e he _ _ _ Z hZ => ?_
          obtain rfl := List.mem_singleton.1 he
          rw [show BsAll.drop i = b :: Bs' from hd] at hZ
          exact (reach Z hZ).mono [_]
        exact ⟨⟨ok, ex, inv'⟩, ⟨_ :: (lB ++ l₀), by rw [eB, e₀, List.cons_append, List.append_assoc]⟩,
          fun Z hZ => (reach Z hZ).mono [_]⟩

include hL in
/-- The members of a chain the first `k` of which split: the memo ends with
`2 ^ k` summaries of the rest. -/
theorem sufSV_prefix_count (hP : ProgFO P) {n : Rel} {d : Nat} {far : Option R}
    (hfar : IsBound D far) (hn : Normal n) (hfo : n.FO) {Bs : List Rel} {y : Rel} {ys : List Rel}
    (hys : ys ≠ []) (hBs : Bs ≠ []) (hv : n.view.forget = .chain (Bs ++ y :: ys))
    (W : Rel → Bool → PRel) (HB : ∀ b ∈ Bs, Splits P 𝕄 d b (W b)) (c : Near R)
    (hc : c.bound = none) :
    2 ^ Bs.length ≤
      pot Bs.length d (sufSV K hK (evalSV (P := P) K hK d) n d far 0 (Bs ++ y :: ys) c []).2 := by
  have hcb : IsBound D c.bound := by rw [hc]; exact isBound_none D
  obtain ⟨-, -, hreach⟩ := sufSV_split hL K hK hP hfar hn hfo hys hBs hv W HB Bs 0 c []
    (List.drop_zero ..) (Nat.zero_add _) hcb (.inr hc)
    ⟨fun p hp => (by cases hp), fun p hp => (by cases hp), fun p hp => (by cases hp)⟩
  have := pot_ge (P := P) (reachL_nodup Bs HB _ (bset_nonempty hL hcb)) hreach
  rwa [reachL_length] at this

include hL in
/-- The race answered with shared work costs `2 ^ k` on a goal whose chain
starts with `k` members that split. -/
theorem sharedRace_prefix_ticks (hP : ProgFO P) (d : Nat) (g : GoalOf R Rel) (hg : GoalOk D g)
    {Bs : List Rel} {y : Rel} {ys : List Rel} (hys : ys ≠ []) (hBs : Bs ≠ [])
    (hv : g.node.view.forget = .chain (Bs ++ y :: ys)) (W : Rel → Bool → PRel)
    (HB : ∀ b ∈ Bs, Splits P 𝕄 (d + 1) b (W b)) (hnear : g.lb = none) :
    2 ^ Bs.length ≤ (sharedRace (K := DerivationKernel.over D K hK P) (d + 2) g).ticks := by
  show 2 ^ Bs.length ≤ (sharedRace (K := DerivationKernel.over D K hK P) (d + 1 + 1) g).ticks
  have hpos : 0 < Bs.length := List.length_pos_of_ne_nil hBs
  have h₁ := sufSV_prefix_count hL K hK hP hg.rb hg.normal hg.fo hys hBs hv W HB ⟨g.lb, false⟩
    hnear
  have h₂ := sufS_pot (P := P) (L := Bs.length) (d := d + 1) K hK
    (evalS (K := DerivationKernel.over D K hK P) (d + 1))
    (fun c x fr m => by
      rw [evalS_val]
      refine (evalSV_gr K hK (d + 1) c x fr m).pot_eq fun k hk hcount => ?_
      rcases hk with h | h <;> omega)
    (fun c x fr m => evalS_pos K hK d c x fr m) g.node g.rb (Bs ++ y :: ys) 0 ⟨g.lb, false⟩ []
  rw [sufS_val K hK _ _ (evalS_val K hK (d + 1))] at h₂
  have h₃ := evalS_chain_ticks (P := P) K hK hv (d + 1) ⟨g.lb, false⟩ g.rb
  have h₄ : (evalS (K := DerivationKernel.over D K hK P) (d + 1 + 1) ⟨g.lb, false⟩ g.node g.rb
      []).ticks ≤ (sharedRace (K := DerivationKernel.over D K hK P) (d + 1 + 1) g).ticks := by
    at_cost K hK
    simp only [sharedRace, Cost.bind_ticks]
    omega
  have h₀ : pot Bs.length (d + 1) ([] : Mm D P) = 0 := rfl
  omega

end count

end Unfold

end RwLog
