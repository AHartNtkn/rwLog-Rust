/-
# Reading an edge within a budget

`readWithin` reads an edge both ways side by side and gives up when the
reading has spent what a reading at its depth may (`Machine.lean`). Here: it
is a reading the machine can be given (`good_cappedReader`).

It is right about the program because it returns what one of the two ways
returns. It does not give up for ever because, once the depth is enough for
the runs of the first rung, a greater depth changes nothing about them, not
even what they cost (`runs_stable`): so the cost of the reading stops
growing, and what it may spend does not.
-/
import RwLog.Rungs.Symmetric.Faces
import RwLog.Rungs.Framework.Race

namespace RwLog

namespace Cost

variable {α β : Type}

/-- Two computations that continue alike from the value of the first are
one. -/
theorem bind_congr_val {m : Cost α} {f g : α → Cost β} (h : f m.val = g m.val) :
    m >>= f = m >>= g := by
  apply Cost.ext <;> simp [h]

/-- The same, where the continuations need only agree when the second does
not give up. -/
theorem bind_stable {m : Cost α} {f g : α → Cost (Option β)} (h : (m >>= g).val ≠ none)
    (k : ∀ a, (g a).val ≠ none → f a = g a) : m >>= f = m >>= g :=
  bind_congr_val (k _ h)

/-- A fold whose step gives up once it has given up gives up from there. -/
theorem foldL_none {g : Option β → α → Cost (Option β)} (hn : ∀ x, (g none x).val = none) :
    ∀ xs : List α, (foldL g none xs).val = none
  | [] => rfl
  | x :: xs => by
    simp only [foldL, bind_val, hn x]
    exact foldL_none hn xs

/-- Two folds whose steps agree wherever the second does not give up are
one, if the second does not give up. -/
theorem foldL_stable {f g : Option β → α → Cost (Option β)}
    (hn : ∀ x, (g none x).val = none) :
    ∀ (xs : List α), (∀ b x, x ∈ xs → (g b x).val ≠ none → f b x = g b x) →
      ∀ b, (foldL g b xs).val ≠ none → foldL f b xs = foldL g b xs
  | [], _, _, _ => rfl
  | x :: xs, k, b, h => by
    have hx : (g b x).val ≠ none := by
      intro e
      apply h
      simp only [foldL, bind_val, e]
      exact foldL_none hn xs
    simp only [foldL] at h ⊢
    rw [k b x List.mem_cons_self hx]
    exact bind_congr_val (foldL_stable hn xs
      (fun b y hy => k b y (List.mem_cons_of_mem _ hy)) _ h)

/-- A computation run within a budget, with nothing for what was given up
on. -/
theorem within_getD_val (c : Nat) (m : Cost (Option α)) :
    (within c m >>= fun r => pure (r.getD none)).val = if m.ticks ≤ c then m.val else none := by
  unfold within
  split <;> rfl

end Cost

namespace Symmetric

open Traverse Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- **A depth that is enough for the runs at an edge is as good as any
greater**: one more changes neither the runs nor what they cost. -/
theorem runs_stable (last : Bool) : ∀ (d : Nat) (seen : List Rel) (n : Rel),
    (runs (K := DerivationKernel.over D K hK P) last d seen n).val ≠ none →
      runs (K := DerivationKernel.over D K hK P) last (d + 1) seen n =
        runs (K := DerivationKernel.over D K hK P) last d seen n := by
  at_cost K hK
  intro d
  induction d with
  | zero =>
    intro seen n h
    exact absurd rfl h
  | succ d ih =>
    intro seen n h
    unfold runs at h ⊢
    refine Cost.bind_stable h fun v hv => ?_
    cases v with
    | span s => rfl
    | meet xs => rfl
    | union xs =>
      simp only [foldL_std] at hv ⊢
      refine Cost.foldL_stable (fun _ => rfl) xs (fun b x _ hb => ?_) _ hv
      cases b with
      | none => rfl
      | some rs =>
        have hx : (runs (K := DerivationKernel.over D _ hK P) last d seen x).val ≠ none := by
          intro e
          apply hb
          simp only [Cost.bind_val, e, Cost.pure_val]
        simp only [ih seen x hx]
    | call f fl =>
      refine Cost.bind_stable hv fun b hb => ?_
      cases b with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
        refine Cost.bind_stable hb fun bd hbd => ?_
        cases bd with
        | none => rfl
        | some bd => exact ih _ _ hbd
    | chain xs =>
      simp only at hv ⊢
      generalize (if last then xs.reverse else xs) = ys at hv ⊢
      cases ys with
      | nil => rfl
      | cons e rest =>
        simp only [foldL_std] at hv ⊢
        have he : (runs (K := DerivationKernel.over D _ hK P) last d seen e).val ≠ none := by
          intro e'
          apply hv
          simp only [Cost.bind_val, e']
          exact Cost.foldL_none (fun _ => rfl) rest
        rw [ih seen e he]
        refine Cost.bind_stable hv fun r hr => ?_
        refine Cost.foldL_stable (fun _ => rfl) rest (fun b x _ hb => ?_) _ hr
        cases b with
        | none => rfl
        | some rs =>
          by_cases hany : rs.any (·.2) = true
          · simp only [hany, ↓reduceIte] at hb ⊢
            have hx : (runs (K := DerivationKernel.over D _ hK P) last d seen x).val ≠ none := by
              intro e'
              apply hb
              simp only [Cost.bind_val, e', Cost.pure_val]
            simp only [ih seen x hx]
          · rw [Bool.not_eq_true] at hany
            simp only [hany, Bool.false_eq_true, ↓reduceIte]

/-- The runs at an edge are the same at every depth from one that is
enough. -/
theorem runs_stable_le (last : Bool) (seen : List Rel) (n : Rel) {d₀ d : Nat} (hd : d₀ ≤ d)
    (h : (runs (K := DerivationKernel.over D K hK P) last d₀ seen n).val ≠ none) :
    runs (K := DerivationKernel.over D K hK P) last d seen n =
      runs (K := DerivationKernel.over D K hK P) last d₀ seen n := by
  induction d, hd using Nat.le_induction with
  | base => rfl
  | succ d _ ih => rw [runs_stable last d seen n (ih ▸ h), ih]

/-- The reading of the first rung is the same, at the same cost, at every
depth from `readNeed` on. -/
theorem readRuns_stable (last : Bool) (n : Rel) {d : Nat} (hd : readNeed P n ≤ d) :
    readRuns (K := DerivationKernel.over D K hK P) last d n =
      readRuns (K := DerivationKernel.over D K hK P) last (readNeed P n) n := by
  have e := runs_stable_le (K := K) (hK := hK) (P := P) last [] n hd
    (runs_some last _ [] n (Nat.le_refl _))
  unfold readRuns
  rw [e]

/-- A reading made a reading of every node does not give up at a depth past
`readNeed` at which the reading does not. -/
theorem offered_live {rd : Bool → Nat → Rel → Cost (Option (Option (List R)))}
    (last : Bool) (d : Nat) (n : Rel) (hd : readNeed P n ≤ d) (h : (rd last d n).val ≠ none) :
    (offered (K := DerivationKernel.over D K hK P) rd last d n).val ≠ none := by
  have h1 := hasCall_some (K := K) (hK := hK) (P := P) d n (by unfold readNeed at hd; omega)
  at_cost K hK
  simp only [offered, Cost.bind_val]
  split
  · next hc => exact absurd hc h1
  · simp
  · exact h

/-- The depth from which the reading within a budget does not give up: one
that is enough for both ways, and at which a reading may spend seven times
what the runs of the first rung cost at either end. -/
def cappedNeed (D : Domain R) (P : Program) (K : Kernel R Cost) (hK : K.Refines D) (n : Rel) :
    Nat :=
  max (readNeed P n)
    (2 ^ (7 * ((readRuns (K := DerivationKernel.over D K hK P) true (readNeed P n) n).ticks +
      (readRuns (K := DerivationKernel.over D K hK P) false (readNeed P n) n).ticks)))

/-- **The reading within a budget is right about the program and does not
give up for ever.** -/
theorem readWithin_ok (hL : D.Lawful P.sorts.interp) (hP : ProgFO P) :
    ReadOk D P K hK (cappedNeed D P K hK) @cappedReader := by
  have hs1 := readRuns_sound (K := K) (hK := hK) hL hP
  have hs2 := readFaces_sound (K := K) (hK := hK) hL hP
  have hl1 := fun last d n hd => readRuns_some (K := K) (hK := hK) (P := P) last d n hd
  have hl2 := fun last d n hd => readFaces_some (K := K) (hK := hK) (P := P) last d n hd
  have hval : ∀ (last : Bool) (d : Nat) (n : Rel),
      (readCapped (K := DerivationKernel.over D K hK P) last d n).val =
      if (Cost.race (readRuns (K := DerivationKernel.over D K hK P) last d n)
          (readFaces (K := DerivationKernel.over D K hK P) last d n)).ticks ≤ readCap d then
        (Cost.race (readRuns (K := DerivationKernel.over D K hK P) last d n)
          (readFaces (K := DerivationKernel.over D K hK P) last d n)).val
      else none := by
    intro last d n
    at_cost K hK
    exact Cost.within_getD_val _ _
  refine ⟨offered_sound (rd := readCapped (K := DerivationKernel.over D K hK P))
    fun last d n ps h => ?_, fun last d n hd =>
    offered_live (rd := readCapped (K := DerivationKernel.over D K hK P)) last d n (le_trans (le_max_left _ _) hd) ?_⟩
  · rw [hval] at h
    split at h
    · rcases Cost.race_val (readRuns (K := DerivationKernel.over D K hK P) last d n)
        (readFaces (K := DerivationKernel.over D K hK P) last d n) with e | e
      · exact hs1 last d n ps (e ▸ h)
      · exact hs2 last d n ps (e ▸ h)
    · cases h
  · have hn : readNeed P n ≤ d := le_trans (le_max_left _ _) hd
    have hpow := le_trans (le_max_right _ _) hd
    rw [hval]
    have ht := Cost.race_ticks (readRuns (K := DerivationKernel.over D K hK P) last d n)
      (readFaces (K := DerivationKernel.over D K hK P) last d n)
    rw [readRuns_stable last n hn] at ht
    have hd0 : d ≠ 0 := by
      intro e
      rw [e] at hpow
      exact absurd (Nat.pow_pos (by omega : 0 < 2)) (Nat.not_lt.2 hpow)
    have hlog := (Nat.le_log2 hd0).2 hpow
    have hcap : (Cost.race (readRuns (K := DerivationKernel.over D K hK P) last d n)
        (readFaces (K := DerivationKernel.over D K hK P) last d n)).ticks ≤ readCap d := by
      rw [readRuns_stable last n hn]
      unfold readCap
      cases last <;> omega
    rw [ite_of_pos hcap]
    rcases Cost.race_val (readRuns (K := DerivationKernel.over D K hK P) last d n)
      (readFaces (K := DerivationKernel.over D K hK P) last d n) with e | e
    · rw [e]; exact hl1 last d n hn
    · rw [e]; exact hl2 last d n hn

end kernel

/-- The reading within a budget is good. -/
theorem good_cappedReader : GoodReader @cappedReader := fun _ _ hL hP => ⟨_, readWithin_ok hL hP⟩

end Symmetric

end RwLog
