/-
# The separating family: R002's walk

The walk of `cRel j` goes through every one of its `2 ^ (j + 1)` products:
none of them is ruled out by the spans around it, and none contains a call, so
the walk never stops early. Each product costs more the deeper it lies,
because the chain to its left is tested again at every choice.
-/
import RwLog.Rungs.R003.Proofs.Separation.Family
import RwLog.Rungs.R002.Proofs.Same

namespace RwLog

namespace R003

namespace Sep

open Cost R000 R001 R002

/-- Every product is a single span. -/
def Prods (acc : List (List Rel)) : Prop := ∀ p ∈ acc, ∃ s : Span, p = [.span s]

theorem prods_nil : Prods [] := fun _ h => by simp at h

/-- What the walk of `cRel j` needs of the continuation it hands its products
to: it never stops, adds at most `m` products, each a single span, and
spends at least `c`. -/
def Cont (K : List Rel → List (List Rel) → Cost Walk) (m c : Nat) : Prop :=
  ∀ s, Good s → ∀ acc, Prods acc →
    (K [.span s] acc).val.1 = false ∧ Prods (K [.span s] acc).val.2 ∧
      (K [.span s] acc).val.2.length ≤ acc.length + m ∧ c ≤ (K [.span s] acc).ticks

theorem alive_good {L : List Span} {s : Span} (hL : ∀ t ∈ L, Good t) (hs : Good s) :
    (R002.alive L [.span s] []).val = true ∧
      (if L = [] then 0 else 2 * (L.length + 1)) ≤ (R002.alive L [.span s] []).ticks := by
  cases L with
  | nil => simp [R002.alive, aliveL, aliveR]
  | cons a L =>
    have hg : ∀ t ∈ a :: L ++ [s], Good t := by
      intro t ht
      rcases List.mem_append.1 ht with h | h
      · exact hL t h
      · rw [List.mem_singleton.1 h]; exact hs
    have hc := chain_good hg
    have hsum := sum_size_good hg
    simp only [List.cons_append] at hc hsum
    refine ⟨?_, ?_⟩
    · simp [R002.alive, aliveL, aliveR, headSpan, Charged.composable, hc]
    · simp only [R002.alive, aliveL, aliveR, headSpan, Charged.composable, bind_ticks, hc,
        List.cons_append, hsum]
      simp

/-- The walk of one span. -/
theorem walk_span (d : Nat) {s : Span} (hs : Good s) {L : List Span} (hL : ∀ t ∈ L, Good t)
    {K : List Rel → List (List Rel) → Cost Walk} {m c : Nat} (hK : Cont K m c)
    {acc : List (List Rel)} (hacc : Prods acc) :
    (walk P0 d false (.span s) L [] K acc).val.1 = false ∧
      Prods (walk P0 d false (.span s) L [] K acc).val.2 ∧
      (walk P0 d false (.span s) L [] K acc).val.2.length ≤ acc.length + m ∧
      1 + (if L = [] then 0 else 2 * (L.length + 1)) + c ≤
        (walk P0 d false (.span s) L [] K acc).ticks := by
  obtain ⟨ha, hat⟩ := alive_good hL hs
  obtain ⟨h1, h2, h3, h4⟩ := hK s hs acc hacc
  rw [walk]
  simp only [Bool.false_eq_true, ↓reduceIte, bind_val, bind_ticks, tick_ticks, ha, h1]
  refine ⟨trivial, h2, h3, ?_⟩
  omega

/-- The walk of a choice hands both spans on. -/
theorem walk_tw (d : Nat) {L : List Span} (hL : ∀ t ∈ L, Good t)
    {K : List Rel → List (List Rel) → Cost Walk} {m c : Nat} (hK : Cont K m c)
    {acc : List (List Rel)} (hacc : Prods acc) :
    (walk P0 d false tw L [] K acc).val.1 = false ∧
      Prods (walk P0 d false tw L [] K acc).val.2 ∧
      (walk P0 d false tw L [] K acc).val.2.length ≤ acc.length + 2 * m ∧
      4 * L.length + 3 + 2 * c ≤ (walk P0 d false tw L [] K acc).ticks := by
  obtain ⟨a1, a2, a3, a4⟩ := walk_span d good_xz hL hK hacc
  obtain ⟨b1, b2, b3, b4⟩ := walk_span d good_zz hL hK a2
  rw [walk]
  simp only [bind_val, bind_ticks, tick_ticks, a1, Bool.false_eq_true, ↓reduceIte]
  refine ⟨b1, b2, by omega, ?_⟩
  by_cases hl : L = []
  · subst hl; simp at a4 b4 ⊢; omega
  · simp only [hl, ↓reduceIte] at a4 b4; omega

theorem staticFirst_cRel : ∀ j, staticFirst false (cRel j) = none
  | 0 => rfl
  | j + 1 => by simp [cRel, staticFirst]

/-- Joining two of the spans composes them: six ticks, and the first one
comes back. -/
theorem joinSeq_good {a b : Span} (ha : Good a) (hb : Good b) :
    R002.joinSeq [.span a] [.span b] = ⟨some [.span a], 6⟩ := by
  have hc := compose_good ha hb
  refine Cost.ext ?_ ?_
  · simp [R002.joinSeq, Charged.compose, hc]
  · simp [R002.joinSeq, Charged.compose, hc, Charged.outSize, size_good ha, size_good hb]

/-- The continuation of the first factor of a sequence: join, and hand on. -/
theorem cont_join {K : List Rel → List (List Rel) → Cost Walk} {m c : Nat} (hK : Cont K m c)
    {x : Span} (hx : Good x) :
    Cont (fun q acc => do
      let r ← R002.joinSeq [.span x] q
      match r with
      | none => pure (false, acc)
      | some r => do
        let a ← aliveR r []
        if a then K r acc else pure (false, acc)) m (c + 6) := by
  intro b hb acc hacc
  obtain ⟨h1, h2, h3, h4⟩ := hK x hx acc hacc
  simp only [joinSeq_good hx hb, aliveR, bind_val, bind_ticks, pure_val, pure_ticks, ↓reduceIte]
  exact ⟨h1, h2, h3, by omega⟩

/-- The walk of `cRel j` between a chain of the two spans and nothing: it does
not stop, hands on `2 ^ (j + 1)` products, and spends at least
`2 ^ j (4 (n + j) + 3 + 2 c + 12 j)`, where `n` is the length of the chain. -/
theorem walk_cRel (d : Nat) : ∀ (j : Nat) {L : List Span}, (∀ t ∈ L, Good t) →
    ∀ {K : List Rel → List (List Rel) → Cost Walk} {m c : Nat}, Cont K m c →
    ∀ {acc : List (List Rel)}, Prods acc →
    (walk P0 d false (cRel j) L [] K acc).val.1 = false ∧
      Prods (walk P0 d false (cRel j) L [] K acc).val.2 ∧
      (walk P0 d false (cRel j) L [] K acc).val.2.length ≤ acc.length + 2 ^ (j + 1) * m ∧
      2 ^ j * (4 * (L.length + j) + 3 + 2 * c + 12 * j) ≤
        (walk P0 d false (cRel j) L [] K acc).ticks
  | 0, L, hL, K, m, c, hK, acc, hacc => by
    obtain ⟨h1, h2, h3, h4⟩ := walk_tw d hL hK hacc
    exact ⟨h1, h2, by simpa [cRel] using h3, by simpa [cRel] using h4⟩
  | j + 1, L, hL, K, m, c, hK, acc, hacc => by
    have hin : Cont (fun p acc =>
        walk P0 d false (cRel j) (leftAfter L p) [] (fun q acc => do
          let r ← R002.joinSeq p q
          match r with
          | none => pure (false, acc)
          | some r => do
            let a ← aliveR r []
            if a then K r acc else pure (false, acc)) acc)
        (2 ^ (j + 1) * m) (2 ^ j * (4 * (L.length + 1 + j) + 3 + 2 * (c + 6) + 12 * j)) := by
      intro a ha acc hacc
      have hL' : ∀ t ∈ L ++ [a], Good t := by
        intro t ht
        rcases List.mem_append.1 ht with h | h
        · exact hL t h
        · rw [List.mem_singleton.1 h]; exact ha
      have := walk_cRel d j hL' (cont_join hK ha) hacc
      simpa [leftAfter] using this
    obtain ⟨h1, h2, h3, h4⟩ := walk_tw d hL hin hacc
    rw [cRel, walk]
    simp only [rightOf, staticFirst_cRel, bind_val, bind_ticks, tick_ticks]
    have e1 : acc.length + 2 * (2 ^ (j + 1) * m) = acc.length + 2 ^ (j + 1 + 1) * m := by ring
    have e2 : 2 ^ (j + 1) * (4 * (L.length + (j + 1)) + 3 + 2 * c + 12 * (j + 1)) ≤
        1 + (4 * L.length + 3 +
          2 * (2 ^ j * (4 * (L.length + 1 + j) + 3 + 2 * (c + 6) + 12 * j))) := by
      have : 2 ^ (j + 1) * (4 * (L.length + (j + 1)) + 3 + 2 * c + 12 * (j + 1)) =
          2 * (2 ^ j * (4 * (L.length + 1 + j) + 3 + 2 * (c + 6) + 12 * j)) := by ring
      omega
    exact ⟨h1, h2, le_trans h3 (le_of_eq e1), le_trans e2 (Nat.add_le_add_left h4 1)⟩

/-! ## The race on demand -/

theorem cont_top : Cont (fun p acc =>
    pure (if (toRel p).calls.isEmpty then (false, acc ++ [p]) else (true, acc))) 1 0 := by
  intro s _ acc hacc
  simp only [toRel, RelOf.calls, List.isEmpty_nil, ↓reduceIte, pure_val, pure_ticks,
    List.length_append, List.length_singleton, le_refl, and_true, true_and]
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact hacc p h
  · exact ⟨s, List.mem_singleton.1 h⟩

theorem length_live (T : Theory) (s : Span) : (Tabled.live T s).val.length ≤ 1 := by
  simp only [Tabled.live, bind_val, pure_val]
  cases (Charged.simplify T s).val <;> simp

theorem length_flatMap_live (T : Theory) : ∀ xs : List Span,
    (xs.flatMap fun x => (Tabled.live T x).val).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
    have := length_live T x
    have := length_flatMap_live T xs
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem length_derivs_prods : ∀ {acc : List (List Rel)}, Prods acc →
    (closed acc).length = acc.length
  | [], _ => rfl
  | p :: acc, h => by
    obtain ⟨s, rfl⟩ := h p (by simp)
    have ih := length_derivs_prods (acc := acc) fun q hq => h q (by simp [hq])
    simp only [closed, List.filterMap_cons, single, List.length_cons] at ih ⊢
    rw [ih]

/-- The walk on `cRel j` finds the unfolding final, returns at most
`2 ^ (j + 1)` answers, and spends at least `2 ^ j (16 j + 3)`. -/
theorem onDemand_gC (d j : Nat) :
    (onDemand P0 d (gC j)).val.1 = true ∧ (onDemand P0 d (gC j)).val.2.length ≤ 2 ^ (j + 1) ∧
      2 ^ j * (16 * j + 3) ≤ (onDemand P0 d (gC j)).ticks := by
  obtain ⟨h1, h2, h3, h4⟩ := walk_cRel d j (L := []) (by simp) cont_top prods_nil
  have hrel : (gC j).rel = cRel j := rfl
  simp only [onDemand, hrel, bind_val, bind_ticks, h1, Bool.false_eq_true,
    ↓reduceIte, pure_val, flatMapL_val]
  refine ⟨trivial, ?_, ?_⟩
  · refine le_trans (length_flatMap_live _ _) ?_
    rw [length_derivs_prods h2]
    simpa using h3
  · simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h4
    have e : 2 ^ j * (16 * j + 3) = 2 ^ j * (4 * j + 3 + 12 * j) := by ring
    omega

end Sep

end R003

end RwLog
