/-
# What the on-demand walk costs

The walk of `Unfold.lean` visits the nodes the eager normalizer visits and
builds the products it builds, so it is charged for the same compositions.
What it pays beyond that are its tests, and the calls it steps through. This
file bounds both against the eager normalizer's own ticks.

The statement is by continuation (`Spec`): if the continuation `k` spends at
most `κ p` on each product `p` it is handed, the walk of an expression whose
eager normalization costs `c` spends at most

    Phi D S c (|L| + |R|) + Σ over the products p alive between L and R of
      (κ p + c * rch R p)

where `|L|`, `|R|` are the sizes of the two chains, `S` bounds every span
written in the program and the goal, and `D` is three more than the depth.
`Phi D S c z = c (z + D) + c² (S + 1)`.

Where the three kinds of extra work go:

* a test where a span is born (a leaf, a conjunction, a fusion) costs at most
  the size of the two chains and of the span, and the eager normalizer pays
  for the span there too, so it is `c (z + D)`;
* the chains grow on the way down: the left one by a product of the first
  factor, which the eager normalizer paid for, the right one by a span written
  in the expression, which is at most `S`; that is the `c² (S + 1)`;
* a test of a joined product whose last span is that of its second part
  repeats a test that passed. It is not paid here but carried on the product
  (`c * rch R p`) up to the sequence that put the span at the head of `R`
  there. That the test passed says the product composes with that span, so the
  eager normalizer composes them and pays for the span, once for each product
  carrying the charge.

A potential `G` on what the continuation has collected is carried through, so
that the top can charge the answers of the collected products.
-/
import RwLog.Rungs.R002.Proofs.OnDemand
import RwLog.Rungs.Framework.Cost
import RwLog.Kernel.Size
import RwLog.Lib.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RwLog

namespace R002

open Cost

/-! ## Sizes -/

/-- The size of a chain. -/
def sz (L : List Span) : Nat := (L.map Span.size).sum

@[simp] theorem sz_nil : sz [] = 0 := rfl
@[simp] theorem sz_cons (s : Span) (L : List Span) : sz (s :: L) = s.size + sz L := rfl
theorem sz_append (L L' : List Span) : sz (L ++ L') = sz L + sz L' := by
  simp only [sz, List.map_append, List.sum_append]

/-- The size of the last span of a product, if it ends with one. -/
def lsz (p : List Rel) : Nat :=
  match lastSpan p with
  | some s => s.size
  | none => 0

/-- What a repeated test of the product against the right chain reads of the
chain. A product that is a single span is never tested twice. -/
def rch (R : List Span) (p : List Rel) : Nat :=
  if 2 ≤ p.length ∧ (lastSpan p).isSome = true then sz R else 0

theorem rch_nil (p : List Rel) : rch [] p = 0 := by
  unfold rch; split <;> rfl

theorem rch_le (R : List Span) (p : List Rel) : rch R p ≤ sz R := by
  unfold rch; split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem lsz_of_lastSpan {p : List Rel} {s : Span} (h : lastSpan p = some s) : lsz p = s.size := by
  unfold lsz; rw [h]

theorem aliveR_ticks_le (r : List Rel) (R : List Span) :
    (aliveR r R).ticks ≤ lsz r + if (lastSpan r).isSome = true then sz R else 0 := by
  unfold aliveR lsz
  cases R with
  | nil => simp
  | cons x R =>
    cases lastSpan r with
    | none => simp
    | some s =>
      simp only [Charged.composable, List.map_cons, List.sum_cons, Option.isSome_some, ite_true,
        sz_cons]
      exact Nat.le_refl _

theorem aliveR_congr {r q : List Rel} (h : lastSpan r = lastSpan q) (R : List Span) :
    aliveR r R = aliveR q R := by
  unfold aliveR; rw [h]

theorem aliveL_congr {r q : List Rel} (h : headSpan r = headSpan q) (L : List Span) :
    aliveL L r = aliveL L q := by
  unfold aliveL; rw [h]

theorem alive_ticks_span (L R : List Span) (s : Span) :
    (alive L [.span s] R).ticks ≤ sz L + sz R + 2 * s.size := by
  have hR : (aliveR [.span s] R).ticks ≤ s.size + sz R := by
    have := aliveR_ticks_le [.span s] R
    rwa [show lsz [.span s] = s.size from rfl, show lastSpan [.span s] = some s from rfl,
      Option.isSome_some, ite_eq_left rfl] at this
  have hL : (aliveL L [.span s]).ticks ≤ sz L + s.size := by
    unfold aliveL
    cases L with
    | nil => simp
    | cons x L =>
      simp only [headSpan, Charged.composable]
      rw [← sz, sz_append]
      exact Nat.le_refl _
  unfold alive
  simp only [bind_ticks, ite_ticks, pure_ticks]
  split <;> omega

theorem sz_leftAfter (L : List Span) (p : List Rel) : sz (leftAfter L p) ≤ sz L + lsz p := by
  unfold leftAfter
  split
  · rw [sz_append]; exact Nat.le_refl _
  · unfold lsz
    cases lastSpan p with
    | none => exact Nat.zero_le _
    | some s => simp [sz]

/-! ## What a join costs -/

theorem joinSeq_ticks_cases {p q r : List Rel} (h : R000.joinSeq p q = some r) :
    (∃ a b q' c, p.getLast? = some (.span a) ∧ q = .span b :: q' ∧ a.compose b = some c ∧
      r = p.dropLast ++ .span c :: q' ∧ (R002.joinSeq p q).ticks = a.size + b.size + c.size) ∨
    r = p ++ q := by
  rcases R000.joinSeq_cases h with ⟨a, b, q', c, hl, rfl, hc, rfl⟩ | rfl
  · refine .inl ⟨a, b, q', c, hl, rfl, hc, rfl, ?_⟩
    unfold R002.joinSeq
    rw [hl]
    simp only [bind_ticks, Charged.compose, hc, Charged.outSize, pure_ticks, Nat.add_zero]
  · exact .inr rfl

theorem mkAnd_ticks_cases {p q r : List Rel} (h : R000.mkAnd p q = some r) :
    (∃ c, r = [.span c] ∧ c.size ≤ (R002.mkAnd p q).ticks) ∨ ∃ x y, r = [.and x y] := by
  unfold R000.mkAnd at h
  split at h
  · rename_i a b
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    refine .inl ⟨c, rfl, ?_⟩
    simp only [R002.mkAnd, bind_ticks, Charged.meet, hc, Charged.outSize, pure_ticks]
    omega
  · cases h
    exact .inr ⟨_, _, rfl⟩

/-! ## The bound, by continuation -/

/-- A continuation of the walk. -/
abbrev Kont := List Rel → List (List Rel) → Cost Walk

/-- A walk, as a function of its two chains, its continuation and what has
been collected. -/
abbrev Walker := List Span → List Span → Kont → List (List Rel) → Cost Walk

def Phi (D S x z : Nat) : Nat := x * (z + D) + x * x * (S + 1)

theorem Phi_mono {D D' S x x' z z' : Nat} (hD : D ≤ D') (hx : x ≤ x') (hz : z ≤ z') :
    Phi D S x z ≤ Phi D' S x' z' := by
  unfold Phi
  exact Nat.add_le_add (Nat.mul_le_mul hx (Nat.add_le_add hz hD))
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul hx hx))

/-- A product the walk can hand on: not empty, and alive between the chains. -/
def Ok (L R : List Span) (p : List Rel) : Prop := p ≠ [] ∧ keep L R p = true

instance (L R : List Span) (p : List Rel) : Decidable (Ok L R p) := by
  unfold Ok; infer_instance

structure Spec (D S : Nat) (w : Walker) (N : List (List Rel)) (c : Nat) : Prop where
  ne : ∀ p ∈ N, p ≠ []
  ls : (N.map lsz).sum ≤ c
  pos : 1 ≤ c
  bound : ∀ (L R : List Span) (k : Kont) (acc : List (List Rel)) (G : List (List Rel) → Nat)
    (κ : List Rel → Nat),
    (∀ p acc, Ok L R p → (k p acc).ticks + G (k p acc).val.2 ≤ κ p + G acc) →
    (w L R k acc).ticks + G (w L R k acc).val.2 ≤
      Phi D S c (sz L + sz R) + (N.map fun p => if Ok L R p then κ p + c * rch R p else 0).sum +
        G acc

theorem Spec.zero (D S : Nat) :
    Spec D S (fun _ _ _ acc => do tick 1; pure (false, acc)) [] 1 where
  ne := by simp
  ls := by simp
  pos := Nat.le_refl _
  bound := by
    intro L R k acc G κ _
    simp only [bind_ticks, tick_ticks, pure_ticks, bind_val, pure_val, Phi, List.map_nil,
      List.sum_nil]
    omega

theorem Spec.leaf (D S : Nat) (hD : 2 ≤ D) (s : Span) (c : Nat) (hc : c = 1 + s.size) :
    Spec D S (fun L R k acc => do
      tick 1
      let a ← alive L [.span s] R
      if a then k [.span s] acc else pure (false, acc)) [[.span s]] c where
  ne := by simp
  ls := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [show lsz [.span s] = s.size from rfl]
    omega
  pos := by omega
  bound := by
    intro L R k acc G κ hk
    have ht := alive_ticks_span L R s
    have hP : 1 + (sz L + sz R + 2 * s.size) ≤ Phi D S c (sz L + sz R) := by
      subst hc
      unfold Phi
      nlinarith [Nat.zero_le ((1 + s.size) * (1 + s.size) * (S + 1)),
        Nat.zero_le (s.size * (sz L + sz R)), Nat.mul_le_mul_left s.size hD]
    simp only [bind_ticks, tick_ticks, bind_val, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ite_ticks, ite_val, pure_ticks, pure_val]
    by_cases ha : (alive L [.span s] R).val = true
    · have hok : Ok L R [.span s] := ⟨by simp, ha⟩
      have := hk _ acc hok
      rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left hok]
      omega
    · have hok : ¬ Ok L R [.span s] := fun h => ha h.2
      rw [ite_eq_right ha, ite_eq_right ha, ite_eq_right hok]
      dsimp only
      omega

theorem sum_ok_mono {L R : List Span} {κ : List Rel → Nat} {c c' : Nat} (h : c ≤ c')
    (N : List (List Rel)) :
    (N.map fun p => if Ok L R p then κ p + c * rch R p else 0).sum ≤
      (N.map fun p => if Ok L R p then κ p + c' * rch R p else 0).sum :=
  sum_map_le fun p _ => by
    split
    · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
    · exact Nat.le_refl _

theorem Spec.or {D S : Nat} {wa wb : Walker} {Na Nb : List (List Rel)} {ca cb : Nat}
    (ha : Spec D S wa Na ca) (hb : Spec D S wb Nb cb) :
    Spec D S (fun L R k acc => do
      tick 1
      let r ← wa L R k acc
      if r.1 then pure r else wb L R k r.2) (Na ++ Nb) (1 + ca + cb) where
  ne := fun p hp => (List.mem_append.mp hp).elim (ha.ne p) (hb.ne p)
  ls := by
    rw [List.map_append, List.sum_append]
    have := ha.ls
    have := hb.ls
    omega
  pos := by omega
  bound := by
    intro L R k acc G κ hk
    have h1 := ha.bound L R k acc G κ hk
    have h2 := hb.bound L R k (wa L R k acc).val.2 G κ hk
    have m1 := sum_ok_mono (L := L) (R := R) (κ := κ) (show ca ≤ 1 + ca + cb by omega) Na
    have m2 := sum_ok_mono (L := L) (R := R) (κ := κ) (show cb ≤ 1 + ca + cb by omega) Nb
    have hP : 1 + Phi D S ca (sz L + sz R) + Phi D S cb (sz L + sz R) ≤
        Phi D S (1 + ca + cb) (sz L + sz R) := by
      unfold Phi
      nlinarith [Nat.zero_le (ca * cb * (S + 1)), Nat.zero_le ((ca + cb) * (S + 1)),
        Nat.zero_le (sz L + sz R + D), Nat.zero_le S]
    simp only [bind_ticks, tick_ticks, bind_val, ite_ticks, ite_val, pure_ticks, pure_val,
      List.map_append, List.sum_append]
    split <;> omega

theorem Phi_step {D D' S c c' : Nat} (hD : D ≤ D') (hc : c ≤ c') (hlt : D + c < D' + c')
    (hpos : 1 ≤ c) (z : Nat) : 1 + Phi D S c z ≤ Phi D' S c' z := by
  rcases Nat.lt_or_ge c c' with h | h
  · refine Nat.le_trans ?_ (Phi_mono hD (show c + 1 ≤ c' from h) (Nat.le_refl z))
    unfold Phi
    nlinarith [Nat.zero_le (c * S), Nat.zero_le (z + D), Nat.zero_le S]
  · have hcc : c' = c := Nat.le_antisymm h hc
    subst hcc
    refine Nat.le_trans ?_ (Phi_mono (show D + 1 ≤ D' by omega) (Nat.le_refl c') (Nat.le_refl z))
    unfold Phi
    nlinarith

/-- One more tick before a walk, paid by one more unit of depth or of cost. -/
theorem Spec.step {D D' S : Nat} {w : Walker} {N : List (List Rel)} {c c' : Nat}
    (h : Spec D S w N c) (hD : D ≤ D') (hc : c ≤ c') (hlt : D + c < D' + c') :
    Spec D' S (fun L R k acc => do tick 1; w L R k acc) N c' where
  ne := h.ne
  ls := h.ls.trans hc
  pos := h.pos.trans hc
  bound := by
    intro L R k acc G κ hk
    have h1 := h.bound L R k acc G κ hk
    have m1 := sum_ok_mono (L := L) (R := R) (κ := κ) hc N
    have hP := Phi_step (S := S) hD hc hlt h.pos (sz L + sz R)
    simp only [bind_ticks, tick_ticks, bind_val]
    omega

theorem lastSpan_atom {x : Rel} (hx : ∀ s, x ≠ .span s) : lastSpan [x] = none := by
  cases h : lastSpan [x] with
  | none => rfl
  | some s =>
    have := lastSpan_eq_some h
    simp only [List.getLast?_singleton, Option.some.injEq] at this
    exact absurd this (hx s)

theorem headSpan_atom {x : Rel} (hx : ∀ s, x ≠ .span s) : headSpan [x] = none := by
  cases h : headSpan [x] with
  | none => rfl
  | some s =>
    obtain ⟨q', hq⟩ := headSpan_eq_some h
    simp only [List.cons.injEq] at hq
    exact absurd hq.1 (hx s)

theorem Ok_atom (L R : List Span) {x : Rel} (hx : ∀ s, x ≠ .span s) : Ok L R [x] :=
  ⟨by simp, keep_iff.mpr ⟨fun _ s hs => by simp [headSpan_atom hx] at hs,
    fun _ s hs => by simp [lastSpan_atom hx] at hs⟩⟩

/-- A factor that is not a span, handed on as it is. -/
theorem Spec.atom (D S : Nat) (x : Rel) (hx : ∀ s, x ≠ .span s) :
    Spec D S (fun _ _ k acc => do tick 1; k [x] acc) [[x]] 1 where
  ne := by simp
  ls := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, lsz, lastSpan_atom hx]
    omega
  pos := Nat.le_refl _
  bound := by
    intro L R k acc G κ hk
    have h1 := hk [x] acc (Ok_atom L R hx)
    have hP : 1 ≤ Phi D S 1 (sz L + sz R) := by
      unfold Phi
      omega
    simp only [bind_ticks, tick_ticks, bind_val, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ite_eq_left (Ok_atom L R hx)]
    omega

/-! ## Conjunction -/

theorem alive_ticks_atom (L R : List Span) {x : Rel} (hx : ∀ s, x ≠ .span s) :
    (alive L [x] R).ticks = 0 := by
  unfold alive aliveL aliveR
  rw [headSpan_atom hx, lastSpan_atom hx]
  cases L <;> cases R <;> rfl

theorem sum_quad_le {α : Type} (K M : Nat) (y : α → Nat) (xs : List α) :
    (xs.map fun p => y p * K + y p * y p * M).sum ≤
      (xs.map y).sum * K + (xs.map y).sum * (xs.map y).sum * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    nlinarith [Nat.zero_le (y x * (xs.map y).sum * M)]

theorem and_pair {L R : List Span} (k : Kont) (G : List (List Rel) → Nat) (κ : List Rel → Nat)
    (hk : ∀ p acc, Ok L R p → (k p acc).ticks + G (k p acc).val.2 ≤ κ p + G acc)
    (p q : List Rel) (acc : List (List Rel)) :
    ((do
      let r ← R002.mkAnd p q
      match r with
      | none => pure (false, acc)
      | some r => do
        let a ← alive L r R
        if a then k r acc else pure (false, acc)) : Cost Walk).ticks +
      G ((do
        let r ← R002.mkAnd p q
        match r with
        | none => pure (false, acc)
        | some r => do
          let a ← alive L r R
          if a then k r acc else pure (false, acc)) : Cost Walk).val.2 ≤
      (R002.mkAnd p q).ticks * (sz L + sz R + 3) +
        (R000.mkAnd p q).elim 0 (fun r => if Ok L R r then κ r else 0) + G acc := by
  simp only [bind_ticks, bind_val, mkAnd_val]
  have hJ : (R002.mkAnd p q).ticks ≤ (R002.mkAnd p q).ticks * (sz L + sz R + 3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  cases hj : R000.mkAnd p q with
  | none =>
    simp only [pure_ticks, pure_val, Option.elim_none]
    omega
  | some r =>
    simp only [bind_ticks, bind_val, ite_ticks, ite_val, pure_ticks, pure_val, Option.elim_some]
    have hal : (alive L r R).ticks + (R002.mkAnd p q).ticks ≤
        (R002.mkAnd p q).ticks * (sz L + sz R + 3) := by
      rcases mkAnd_ticks_cases hj with ⟨c, rfl, hc⟩ | ⟨x, y, rfl⟩
      · have := alive_ticks_span L R c
        have := Span.size_pos c
        nlinarith [Nat.zero_le ((R002.mkAnd p q).ticks * (sz L + sz R))]
      · rw [alive_ticks_atom L R (fun s h => by cases h)]
        omega
    by_cases ha : (alive L r R).val = true
    · have hok : Ok L R r := ⟨R000.mkAnd_ne_nil hj, ha⟩
      have := hk r acc hok
      rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left hok]
      omega
    · have hok : ¬ Ok L R r := fun h => ha h.2
      rw [ite_eq_right ha, ite_eq_right ha, ite_eq_right hok]
      dsimp only
      omega

theorem Spec.and {D S : Nat} {wa wb : Walker} {Na Nb : List (List Rel)} {ca cb : Nat}
    (hD : 3 ≤ D) (ha : Spec D S wa Na ca) (hb : Spec D S wb Nb cb) :
    Spec D S (fun L R k acc => do
      tick 1
      wa [] [] (fun p acc =>
        wb [] [] (fun q acc => do
          let r ← R002.mkAnd p q
          match r with
          | none => pure (false, acc)
          | some r => do
            let a ← alive L r R
            if a then k r acc else pure (false, acc)) acc) acc)
      (Na.flatMap fun p => Nb.filterMap (R000.mkAnd p))
      (1 + ca + (Na.map fun p => cb + (Nb.map fun q => (R002.mkAnd p q).ticks).sum).sum) where
  ne := by
    intro r hr
    simp only [List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨p, -, q, -, hj⟩ := hr
    exact R000.mkAnd_ne_nil hj
  ls := by
    rw [sum_flatMap_map]
    refine Nat.le_trans (sum_map_le (g := fun p => cb + (Nb.map fun q => (R002.mkAnd p q).ticks).sum)
      fun p _ => ?_) (by omega)
    rw [sum_filterMap_map]
    refine Nat.le_trans (sum_map_le (g := fun q => (R002.mkAnd p q).ticks) fun q _ => ?_)
      (Nat.le_add_left _ _)
    cases hj : R000.mkAnd p q with
    | none => exact Nat.zero_le _
    | some r =>
      rcases mkAnd_ticks_cases hj with ⟨c, rfl, hc⟩ | ⟨x, y, rfl⟩
      · exact hc
      · exact Nat.zero_le _
  pos := by omega
  bound := by
    intro L R k acc G κ hk
    have hb' : ∀ p acc, Ok [] [] p →
        (wb [] [] (fun q acc => do
          let r ← R002.mkAnd p q
          match r with
          | none => pure (false, acc)
          | some r => do
            let a ← alive L r R
            if a then k r acc else pure (false, acc)) acc).ticks +
          G (wb [] [] (fun q acc => do
            let r ← R002.mkAnd p q
            match r with
            | none => pure (false, acc)
            | some r => do
              let a ← alive L r R
              if a then k r acc else pure (false, acc)) acc).val.2 ≤
        (Phi D S cb 0 + (Nb.map fun q => (R002.mkAnd p q).ticks * (sz L + sz R + 3) +
          (R000.mkAnd p q).elim 0 (fun r => if Ok L R r then κ r else 0)).sum) + G acc := by
      intro p acc _
      refine Nat.le_trans (hb.bound [] [] _ acc G _ fun q acc _ => and_pair k G κ hk p q acc) ?_
      refine Nat.add_le_add_right (Nat.add_le_add_left (sum_map_le fun q _ => ?_) _) _
      split
      · rw [rch_nil]; omega
      · exact Nat.zero_le _
    have h1 := ha.bound [] [] _ acc G _ hb'
    have h2 : (Na.map fun p => if Ok [] [] p then
          (Phi D S cb 0 + (Nb.map fun q => (R002.mkAnd p q).ticks * (sz L + sz R + 3) +
            (R000.mkAnd p q).elim 0 (fun r => if Ok L R r then κ r else 0)).sum) + ca * rch [] p
          else 0).sum ≤
        (Na.map fun p => (Phi D S cb 0 +
            (Nb.map fun q => (R002.mkAnd p q).ticks).sum * (sz L + sz R + 3)) +
          (Nb.map fun q => (R000.mkAnd p q).elim 0 (fun r => if Ok L R r then κ r else 0)).sum).sum := by
      refine sum_map_le fun p _ => ?_
      rw [sum_map_add', sum_map_mul_right']
      split
      · rw [rch_nil]; omega
      · exact Nat.zero_le _
    rw [sum_map_add'] at h2
    have h3 : (Na.map fun p => (Nb.map fun q =>
          (R000.mkAnd p q).elim 0 (fun r => if Ok L R r then κ r else 0)).sum).sum ≤
        ((Na.flatMap fun p => Nb.filterMap (R000.mkAnd p)).map fun r =>
          if Ok L R r then κ r + (1 + ca + (Na.map fun p => cb +
            (Nb.map fun q => (R002.mkAnd p q).ticks).sum).sum) * rch R r else 0).sum := by
      rw [sum_flatMap_map]
      refine sum_map_le fun p _ => ?_
      rw [sum_filterMap_map]
      refine sum_map_le fun q _ => ?_
      cases R000.mkAnd p q with
      | none => exact Nat.le_refl _
      | some r =>
        simp only [Option.elim_some]
        split
        · exact Nat.le_add_right _ _
        · exact Nat.le_refl _
    have h4 : (Na.map fun p => Phi D S cb 0 +
          (Nb.map fun q => (R002.mkAnd p q).ticks).sum * (sz L + sz R + 3)).sum ≤
        (Na.map fun p => cb + (Nb.map fun q => (R002.mkAnd p q).ticks).sum).sum *
            (sz L + sz R + D) +
          (Na.map fun p => cb + (Nb.map fun q => (R002.mkAnd p q).ticks).sum).sum *
            (Na.map fun p => cb + (Nb.map fun q => (R002.mkAnd p q).ticks).sum).sum * (S + 1) := by
      refine Nat.le_trans (sum_map_le fun p _ => ?_) (sum_quad_le _ _ _ _)
      unfold Phi
      generalize (Nb.map fun q => (R002.mkAnd p q).ticks).sum = J
      nlinarith [Nat.zero_le (cb * (sz L + sz R)), Nat.zero_le (cb * J * (S + 1)),
        Nat.zero_le (J * J * (S + 1)), Nat.mul_le_mul_left J hD]
    generalize (Na.map fun p => cb + (Nb.map fun q => (R002.mkAnd p q).ticks).sum).sum = Y at *
    have h5 : 1 + Phi D S ca 0 + (Y * (sz L + sz R + D) + Y * Y * (S + 1)) ≤
        Phi D S (1 + ca + Y) (sz L + sz R) := by
      unfold Phi
      nlinarith [Nat.zero_le (ca * (sz L + sz R)), Nat.zero_le (ca * Y * (S + 1)),
        Nat.zero_le ((ca + Y) * (S + 1)), Nat.zero_le S, Nat.zero_le (sz L + sz R)]
    simp only [bind_ticks, tick_ticks, bind_val]
    rw [Nat.add_assoc]
    refine Nat.le_trans (Nat.add_le_add_left h1 1) ?_
    simp only [sz_nil, Nat.add_zero]
    omega

/-! ## Sequence -/

/-- A second part alive after the first composes with the last span of the
first. -/
theorem compose_of_AL {L : List Span} {p q' : List Rel} {a b : Span}
    (hl : p.getLast? = some (.span a)) (h : AL (leftAfter L p) (.span b :: q')) :
    ∃ c, a.compose b = some c := by
  have hLa : ∃ L', leftAfter L p = L' ++ [a] := by
    by_cases hp : p = [.span a]
    · subst hp; exact ⟨L, rfl⟩
    · refine ⟨[], ?_⟩
      rw [leftAfter_other, lastSpan_of_getLast? hl]
      · rfl
      · rintro a' rfl
        simp only [List.getLast?_singleton, Option.some.injEq, RelOf.span.injEq] at hl
        exact hp (by rw [hl])
  obtain ⟨L', hL'⟩ := hLa
  have := h (by rw [hL']; simp) b rfl
  rw [hL', chain_concat, GRel.comp_assoc] at this
  obtain ⟨c, hc, -⟩ := compose_isSome (GRel.comp_nonempty_right this)
  exact ⟨c, hc⟩

/-- The last span of a joined product: either it was made by fusing the single
span of the second part, and the join paid for it, or it is the last span of
the second part and the product has at least two factors. -/
theorem join_last_cases {p q r : List Rel} (h : R000.joinSeq p q = some r) (hp : p ≠ [])
    (hq : q ≠ []) :
    (∃ c, lastSpan r = some c ∧ c.size ≤ (R002.joinSeq p q).ticks ∧
      1 ≤ (R002.joinSeq p q).ticks ∧ q.length = 1) ∨
    (lastSpan r = lastSpan q ∧ 2 ≤ r.length) := by
  rcases joinSeq_ticks_cases h with ⟨a, b, q', c, hl, rfl, hc, rfl, hJ⟩ | rfl
  · cases q' with
    | nil =>
      refine .inl ⟨c, lastSpan_of_getLast? (by simp), by omega, ?_, rfl⟩
      have := Span.size_pos a
      omega
    | cons y q'' =>
      refine .inr ⟨?_, by simp only [List.length_append, List.length_cons]; omega⟩
      rw [lastSpan_append (List.cons_ne_nil _ _)]
      exact (lastSpan_append (p := [RelOf.span c]) (List.cons_ne_nil y q'')).trans
        (lastSpan_append (p := [RelOf.span b]) (List.cons_ne_nil y q'')).symm
  · refine .inr ⟨lastSpan_append hq, ?_⟩
    have := List.length_pos_of_ne_nil hp
    have := List.length_pos_of_ne_nil hq
    rw [List.length_append]
    omega

theorem rch_of_len {R : List Span} {r : List Rel} (h : 2 ≤ r.length) :
    rch R r = if (lastSpan r).isSome = true then sz R else 0 := by
  unfold rch
  simp only [h, true_and]

theorem lsz_congr {r q : List Rel} (h : lastSpan r = lastSpan q) : lsz r = lsz q := by
  unfold lsz; rw [h]

/-- What one join costs the walk, against what it costs the eager normalizer
(`(R002.joinSeq p q).ticks`), with the charge the second part carried. -/
theorem seq_pair {L R : List Span} {p q : List Rel} (κ : List Rel → Nat) (cb : Nat)
    (hp : p ≠ []) (hLp : AL L p) (hq : Ok (leftAfter L p) R q) :
    (R002.joinSeq p q).ticks +
        (R000.joinSeq p q).elim 0
          (fun r => (aliveR r R).ticks + if (aliveR r R).val = true then κ r else 0) +
        cb * rch R q ≤
      (sz R + 3) * (R002.joinSeq p q).ticks + lsz q +
        (R000.joinSeq p q).elim 0 fun r => if Ok L R r then κ r + (cb + 1) * rch R r else 0 := by
  obtain ⟨hqne, hkq⟩ := hq
  obtain ⟨hALq, hARq⟩ := keep_iff.mp hkq
  have hJ : (R002.joinSeq p q).ticks ≤ (sz R + 3) * (R002.joinSeq p q).ticks :=
    Nat.le_mul_of_pos_left _ (by omega)
  cases hj : R000.joinSeq p q with
  | none =>
    simp only [Option.elim_none]
    have hr : rch R q = 0 := by
      unfold R000.joinSeq at hj
      split at hj
      · rename_i a b q' hl
        obtain ⟨c, hc⟩ := compose_of_AL hl hALq
        rw [hc] at hj
        cases hj
      · cases hj
    rw [hr]
    omega
  | some r =>
    simp only [Option.elim_some]
    have hrne := R000.joinSeq_ne_nil hj hp
    have hALr := AL_join hj hp hLp hALq
    have ht := aliveR_ticks_le r R
    rcases join_last_cases hj hp hqne with ⟨c, hc, hcJ, hJ1, hlen⟩ | ⟨hlast, hlen⟩
    · have hr : rch R q = 0 := by
        unfold rch
        rw [ite_eq_right]
        omega
      rw [lsz_of_lastSpan hc, hc, Option.isSome_some, ite_eq_left rfl] at ht
      have hRJ : sz R ≤ sz R * (R002.joinSeq p q).ticks := Nat.le_mul_of_pos_right _ hJ1
      have hexp : (sz R + 3) * (R002.joinSeq p q).ticks =
          sz R * (R002.joinSeq p q).ticks + 3 * (R002.joinSeq p q).ticks := Nat.add_mul _ _ _
      by_cases ha : (aliveR r R).val = true
      · have hok : Ok L R r := ⟨hrne, keep_iff.mpr ⟨hALr, (aliveR_iff _ _).mp ha⟩⟩
        rw [ite_eq_left ha, ite_eq_left hok, hr]
        omega
      · rw [ite_eq_right ha, hr]
        omega
    · have ha : (aliveR r R).val = true := by
        rw [aliveR_congr hlast]
        exact (aliveR_iff _ _).mpr hARq
      have hok : Ok L R r := ⟨hrne, keep_iff.mpr ⟨hALr, (aliveR_iff _ _).mp ha⟩⟩
      rw [ite_eq_left ha, ite_eq_left hok, rch_of_len hlen]
      rw [lsz_congr hlast, hlast] at ht
      have hq' : rch R q ≤ if (lastSpan q).isSome = true then sz R else 0 := by
        unfold rch
        split
        · rename_i h
          rw [ite_eq_left h.2]
        · exact Nat.zero_le _
      rw [hlast]
      generalize (if (lastSpan q).isSome = true then sz R else 0) = x at *
      have := Nat.mul_le_mul_left cb hq'
      have : (cb + 1) * x = cb * x + x := Nat.succ_mul _ _
      omega

/-- The chain to the right of the first factor of a sequence, from what the
second factor is known to start with. -/
def rightBy (sf : Option (Span × Bool)) (R : List Span) : List Span :=
  match sf with
  | some (t, true) => t :: R
  | some (t, false) => [t]
  | none => []

theorem rightOf_eq (neg : Bool) (e : Rel) (R : List Span) :
    rightOf neg e R = rightBy (staticFirst neg e) R := rfl

/-- The charge a product of the first factor carries for the chain to its
right is paid by the second factor, or carried on by the product they make. -/
theorem seq_transfer {L R : List Span} {p : List Rel} {Nb : List (List Rel)} {S cb : Nat}
    (ca : Nat) (sf : Option (Span × Bool))
    (hsf : ∀ t fl, sf = some (t, fl) →
      t.size ≤ S ∧ t.size + 1 ≤ cb ∧ (fl = true → Nb = [[.span t]]))
    (hp : Ok L (rightBy sf R) p) :
    ca * rch (rightBy sf R) p ≤ ca * cb +
      (Nb.map fun q => (R000.joinSeq p q).elim 0 fun r =>
        if Ok L R r then ca * rch R r else 0).sum := by
  match sf, hsf, hp with
  | none, _, _ =>
    rw [show rightBy none R = [] from rfl, rch_nil]
    omega
  | some (t, false), hsf, _ =>
    have h1 := (hsf t false rfl).2.1
    have h2 := rch_le (rightBy (some (t, false)) R) p
    rw [show rightBy (some (t, false)) R = [t] from rfl, sz_cons, sz_nil] at h2
    refine Nat.le_trans (Nat.mul_le_mul_left ca (show rch [t] p ≤ cb by omega)) (Nat.le_add_right _ _)
  | some (t, true), hsf, hp =>
    obtain ⟨-, h1, h3⟩ := hsf t true rfl
    rw [h3 rfl]
    rw [show rightBy (some (t, true)) R = t :: R from rfl] at hp ⊢
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hc : 2 ≤ p.length ∧ (lastSpan p).isSome = true
    · obtain ⟨hlen, hsome⟩ := hc
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hpne, hkp⟩ := hp
      obtain ⟨hALp, hARp⟩ := keep_iff.mp hkp
      have hne := hARp (List.cons_ne_nil _ _) s hs
      rw [List.map_cons, GRel.chain_cons, ← GRel.comp_assoc] at hne
      obtain ⟨c, hc, hden⟩ := compose_isSome (GRel.comp_nonempty_left hne)
      have hj : R000.joinSeq p [.span t] = some (p.dropLast ++ [.span c]) := by
        rw [joinSeq_fused (lastSpan_eq_some hs), hc]
        rfl
      have hlast : lastSpan (p.dropLast ++ [.span c]) = some c :=
        lastSpan_of_getLast? (by simp)
      have hok : Ok L R (p.dropLast ++ [.span c]) := by
        refine ⟨by simp, keep_iff.mpr ⟨?_, ?_⟩⟩
        · rcases joinSeq_head hj hpne with ⟨a, b, q', c', rfl, -, -, -⟩ | hh
          · simp at hlen
          · intro hL s' hs'
            exact hALp hL s' (hh ▸ hs')
        · intro hR s' hs'
          rw [hlast] at hs'
          cases hs'
          rw [hden]
          exact hne
      have hrl : rch R (p.dropLast ++ [.span c]) = sz R := by
        rw [rch_of_len (by simp; omega), hlast]
        rfl
      rw [hj, Option.elim_some, ite_eq_left hok, hrl, rch_of_len hlen, hsome, ite_eq_left rfl,
        sz_cons, Nat.mul_add]
      have := Nat.mul_le_mul_left ca (show t.size ≤ cb by omega)
      omega
    · have : rch (t :: R) p = 0 := by
        unfold rch
        rw [ite_eq_right hc]
      rw [this]
      omega

/-- The continuation the walk gives the second factor of a sequence. -/
def joinK (k : Kont) (R : List Span) (p : List Rel) : Kont := fun q acc => do
  let r ← R002.joinSeq p q
  match r with
  | none => pure (false, acc)
  | some r => do
    let a ← aliveR r R
    if a then k r acc else pure (false, acc)

theorem joinK_bound {L R : List Span} (k : Kont) (G : List (List Rel) → Nat) (κ : List Rel → Nat)
    (hk : ∀ p acc, Ok L R p → (k p acc).ticks + G (k p acc).val.2 ≤ κ p + G acc)
    {p : List Rel} (hp : p ≠ []) (hLp : AL L p) (q : List Rel) (acc : List (List Rel))
    (hq : Ok (leftAfter L p) R q) :
    (joinK k R p q acc).ticks + G (joinK k R p q acc).val.2 ≤
      (R002.joinSeq p q).ticks + (R000.joinSeq p q).elim 0
        (fun r => (aliveR r R).ticks + if (aliveR r R).val = true then κ r else 0) + G acc := by
  unfold joinK
  simp only [bind_ticks, bind_val, joinSeq_val]
  cases hj : R000.joinSeq p q with
  | none =>
    simp only [pure_ticks, pure_val, Option.elim_none]
    omega
  | some r =>
    simp only [bind_ticks, bind_val, ite_ticks, ite_val, pure_ticks, pure_val, Option.elim_some]
    by_cases ha : (aliveR r R).val = true
    · have hok : Ok L R r := ⟨R000.joinSeq_ne_nil hj hp,
        keep_iff.mpr ⟨AL_join hj hp hLp (keep_iff.mp hq.2).1, (aliveR_iff _ _).mp ha⟩⟩
      have := hk r acc hok
      rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left ha]
      omega
    · rw [ite_eq_right ha, ite_eq_right ha, ite_eq_right ha]

theorem lsz_join {p q r : List Rel} (h : R000.joinSeq p q = some r) (hp : p ≠ []) (hq : q ≠ []) :
    lsz r ≤ lsz q + (R002.joinSeq p q).ticks := by
  rcases join_last_cases h hp hq with ⟨c, hc, hcJ, -, -⟩ | ⟨hlast, -⟩
  · rw [lsz_of_lastSpan hc]; omega
  · rw [lsz_congr hlast]; omega

theorem sz_rightBy {S cb : Nat} {Nb : List (List Rel)} (sf : Option (Span × Bool))
    (hsf : ∀ t fl, sf = some (t, fl) →
      t.size ≤ S ∧ t.size + 1 ≤ cb ∧ (fl = true → Nb = [[.span t]]))
    (R : List Span) : sz (rightBy sf R) ≤ sz R + S := by
  match sf, hsf with
  | none, _ => exact Nat.zero_le _
  | some (t, false), hsf =>
    have := (hsf t false rfl).1
    rw [show rightBy (some (t, false)) R = [t] from rfl, sz_cons, sz_nil]
    omega
  | some (t, true), hsf =>
    have := (hsf t true rfl).1
    rw [show rightBy (some (t, true)) R = t :: R from rfl, sz_cons]
    omega

theorem Spec.seq {D S : Nat} {wa wb : Walker} {Na Nb : List (List Rel)} {ca cb : Nat}
    (hD : 3 ≤ D) (ha : Spec D S wa Na ca) (hb : Spec D S wb Nb cb) (sf : Option (Span × Bool))
    (hsf : ∀ t fl, sf = some (t, fl) →
      t.size ≤ S ∧ t.size + 1 ≤ cb ∧ (fl = true → Nb = [[.span t]])) :
    Spec D S (fun L R k acc => do
      tick 1
      wa L (rightBy sf R) (fun p acc => wb (leftAfter L p) R (joinK k R p) acc) acc)
      (Na.flatMap fun p => Nb.filterMap (R000.joinSeq p))
      (1 + ca + (Na.map fun p => cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum).sum) where
  ne := by
    intro r hr
    simp only [List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨p, hp, q, -, hj⟩ := hr
    exact R000.joinSeq_ne_nil hj (ha.ne p hp)
  ls := by
    rw [sum_flatMap_map]
    refine Nat.le_trans (sum_map_le (g := fun p => cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum)
      fun p hp => ?_) (by omega)
    rw [sum_filterMap_map]
    refine Nat.le_trans (sum_map_le (g := fun q => lsz q + (R002.joinSeq p q).ticks) fun q hq => ?_) ?_
    · cases hj : R000.joinSeq p q with
      | none => exact Nat.zero_le _
      | some r => exact lsz_join hj (ha.ne p hp) (hb.ne q hq)
    · rw [sum_map_add']
      exact Nat.add_le_add_right hb.ls _
  pos := by omega
  bound := by
    intro L R k acc G κ hk
    have hka : ∀ p acc, Ok L (rightBy sf R) p →
        (wb (leftAfter L p) R (joinK k R p) acc).ticks +
          G (wb (leftAfter L p) R (joinK k R p) acc).val.2 ≤
        (Phi D S cb (sz (leftAfter L p) + sz R) + (Nb.map fun q =>
          if Ok (leftAfter L p) R q then
            ((R002.joinSeq p q).ticks + (R000.joinSeq p q).elim 0
              (fun r => (aliveR r R).ticks + if (aliveR r R).val = true then κ r else 0)) +
              cb * rch R q
          else 0).sum) + G acc :=
      fun p acc hp => hb.bound _ _ _ acc G _
        (fun q acc hq => joinK_bound k G κ hk hp.1 (keep_iff.mp hp.2).1 q acc hq)
    have h1 := ha.bound L (rightBy sf R) _ acc G _ hka
    have hper : ∀ p ∈ Na,
        (if Ok L (rightBy sf R) p then
          (Phi D S cb (sz (leftAfter L p) + sz R) + (Nb.map fun q =>
            if Ok (leftAfter L p) R q then
              ((R002.joinSeq p q).ticks + (R000.joinSeq p q).elim 0
                (fun r => (aliveR r R).ticks + if (aliveR r R).val = true then κ r else 0)) +
                cb * rch R q
            else 0).sum) + ca * rch (rightBy sf R) p
        else 0) ≤
        ((cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum) * (sz L + sz R + D + 2 * ca + 1) +
          (cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum) *
            (cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum) * (S + 1)) +
        (Nb.map fun q => (R000.joinSeq p q).elim 0 fun r =>
          if Ok L R r then κ r + (1 + ca + (Na.map fun p => cb +
            (Nb.map fun q => (R002.joinSeq p q).ticks).sum).sum) * rch R r else 0).sum := by
      intro p hpN
      split
      · rename_i hp
        have hA : (Nb.map fun q =>
            if Ok (leftAfter L p) R q then
              ((R002.joinSeq p q).ticks + (R000.joinSeq p q).elim 0
                (fun r => (aliveR r R).ticks + if (aliveR r R).val = true then κ r else 0)) +
                cb * rch R q
            else 0).sum ≤
            (Nb.map fun q => ((sz R + 3) * (R002.joinSeq p q).ticks + lsz q) +
              (R000.joinSeq p q).elim 0 fun r =>
                if Ok L R r then κ r + (cb + 1) * rch R r else 0).sum :=
          sum_map_le fun q _ => by
            split
            · rename_i hq
              exact seq_pair κ cb hp.1 (keep_iff.mp hp.2).1 hq
            · exact Nat.zero_le _
        rw [sum_map_add', sum_map_add', sum_map_mul_left'] at hA
        have hB := seq_transfer (L := L) (R := R) (p := p) ca sf hsf hp
        have hY : cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum ≤
            (Na.map fun p => cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum).sum :=
          le_sum_map_of_mem (fun p => cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum) hpN
        have hC : (Nb.map fun q => (R000.joinSeq p q).elim 0 fun r =>
              if Ok L R r then κ r + (cb + 1) * rch R r else 0).sum +
            (Nb.map fun q => (R000.joinSeq p q).elim 0 fun r =>
              if Ok L R r then ca * rch R r else 0).sum ≤
            (Nb.map fun q => (R000.joinSeq p q).elim 0 fun r =>
              if Ok L R r then κ r + (1 + ca + (Na.map fun p => cb +
                (Nb.map fun q => (R002.joinSeq p q).ticks).sum).sum) * rch R r else 0).sum := by
          rw [← sum_map_add']
          refine sum_map_le fun q _ => ?_
          cases R000.joinSeq p q with
          | none => exact Nat.le_refl _
          | some r =>
            simp only [Option.elim_some]
            split
            · rw [Nat.add_assoc, ← Nat.add_mul]
              exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
            · exact Nat.le_refl _
        have hls := hb.ls
        have hlp : lsz p ≤ ca := (le_sum_map_of_mem lsz hpN).trans ha.ls
        have hD' := Phi_mono (S := S) (Nat.le_refl D) (Nat.le_refl cb)
          (show sz (leftAfter L p) + sz R ≤ sz L + sz R + ca by
            have := sz_leftAfter L p; omega)
        have hQ : Phi D S cb (sz L + sz R + ca) +
              (sz R + 3) * (Nb.map fun q => (R002.joinSeq p q).ticks).sum + cb + ca * cb ≤
            (cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum) *
                (sz L + sz R + D + 2 * ca + 1) +
              (cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum) *
                (cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum) * (S + 1) := by
          unfold Phi
          generalize (Nb.map fun q => (R002.joinSeq p q).ticks).sum = J
          nlinarith [Nat.zero_le (cb * J * (S + 1)), Nat.zero_le (J * J * (S + 1)),
            Nat.mul_le_mul_left J hD, Nat.zero_le (J * sz L), Nat.zero_le (J * ca),
            Nat.zero_le (cb * ca)]
        omega
      · exact Nat.zero_le _
    have h2 := sum_map_le hper
    rw [sum_map_add'] at h2
    have h3 := sum_quad_le (sz L + sz R + D + 2 * ca + 1) (S + 1)
      (fun p => cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum) Na
    have h4 : (Na.map fun p => (Nb.map fun q => (R000.joinSeq p q).elim 0 fun r =>
          if Ok L R r then κ r + (1 + ca + (Na.map fun p => cb +
            (Nb.map fun q => (R002.joinSeq p q).ticks).sum).sum) * rch R r else 0).sum).sum ≤
        ((Na.flatMap fun p => Nb.filterMap (R000.joinSeq p)).map fun r =>
          if Ok L R r then κ r + (1 + ca + (Na.map fun p => cb +
            (Nb.map fun q => (R002.joinSeq p q).ticks).sum).sum) * rch R r else 0).sum := by
      rw [sum_flatMap_map]
      refine sum_map_le fun p _ => ?_
      rw [sum_filterMap_map]
    have hRa := sz_rightBy sf hsf R
    have hPa := Phi_mono (S := S) (Nat.le_refl D) (Nat.le_refl ca)
      (show sz L + sz (rightBy sf R) ≤ sz L + sz R + S by omega)
    generalize (Na.map fun p => cb + (Nb.map fun q => (R002.joinSeq p q).ticks).sum).sum = Y at *
    have h5 : 1 + Phi D S ca (sz L + sz R + S) +
          (Y * (sz L + sz R + D + 2 * ca + 1) + Y * Y * (S + 1)) ≤
        Phi D S (1 + ca + Y) (sz L + sz R) := by
      unfold Phi
      nlinarith [Nat.zero_le (ca * Y * S), Nat.zero_le (Y * S), Nat.zero_le (ca * S),
        Nat.zero_le S, Nat.zero_le (sz L + sz R), Nat.zero_le Y, Nat.zero_le ca]
    simp only [bind_ticks, tick_ticks, bind_val]
    rw [Nat.add_assoc]
    refine Nat.le_trans (Nat.add_le_add_left h1 1) ?_
    omega

end R002

end RwLog
