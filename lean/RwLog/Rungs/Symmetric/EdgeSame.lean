/-
# An edge reads the same at every depth and at every kernel

`readEdge` reads an edge of a node to a depth, and gives up if the depth is
not enough. Here: a reading that does not give up returns the same at every
greater depth, and at every kernel that returns what the domain returns
(`readEdge_mono`). So what is read of an edge of a node is one thing
(`Reads.unique`), whichever run read it and when.
-/
import RwLog.Rungs.Symmetric.ReadLive

namespace RwLog

namespace Symmetric

open Traverse Answer

/-! ## Folds that stop at nothing -/

theorem foldl_none {α β : Type} (f : Option β → α → Option β) (hnone : ∀ x, f none x = none) :
    ∀ xs : List α, xs.foldl f none = none
  | [] => rfl
  | x :: xs => by rw [List.foldl_cons, hnone]; exact foldl_none f hnone xs

/-- Two folds that stop at nothing: where every step of the first that
returns something is a step of the second, what the first returns the second
returns. -/
theorem foldl_some_imp {α β : Type} (f g : Option β → α → Option β)
    (hnone : ∀ x, f none x = none) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ b b', f (some b) x = some b' → g (some b) x = some b') →
      ∀ (acc : Option β) (r : β), xs.foldl f acc = some r → xs.foldl g acc = some r
  | [], _, _, _, h => h
  | x :: xs, hstep, acc, r, h => by
    rw [List.foldl_cons] at h ⊢
    cases acc with
    | none => rw [hnone, foldl_none f hnone] at h; cases h
    | some b =>
      cases hf : f (some b) x with
      | none => rw [hf, foldl_none f hnone] at h; cases h
      | some b' =>
        rw [hstep x List.mem_cons_self b b' hf]
        rw [hf] at h
        exact foldl_some_imp f g hnone xs (fun y hy => hstep y (List.mem_cons_of_mem _ hy)) _ r h

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## What the steps of a reading return -/

/-- What `addRun` returns. -/
def addRunP (acc : List (Run R)) (r : Run R) : List (Run R) :=
  if acc.any (fun q => if q.2 = r.2 then decide (q.1 = r.1) else false) then acc else acc ++ [r]

/-- What `extendRuns` returns. -/
def extendRunsP (D : Domain R) (last : Bool) (rs ys : List (Run R)) : List (Run R) :=
  rs.foldl (fun acc r =>
    match r with
    | (some x, true) =>
      ys.foldl (fun acc q =>
        match q.1 with
        | none => addRunP acc (some x, false)
        | some y =>
          match (if last then D.compose y x else D.compose x y) with
          | none => acc
          | some z => addRunP acc (some z, q.2)) acc
    | _ => acc) (rs.filter fun r => !r.2)

/-- A leaf is the same answer at every kernel. -/
theorem leaf_val_same (K₁ : Kernel R Cost) (hK₁ : K₁.Refines D) (K₂ : Kernel R Cost)
    (hK₂ : K₂.Refines D) (lb : Option R) (n : Rel) (rb : Option R) :
    (Ans.leaf D P K₁ hK₁ lb n rb).val = (Ans.leaf D P K₂ hK₂ lb n rb).val := by
  cases h1 : (Ans.leaf D P K₁ hK₁ lb n rb).val with
  | none =>
    cases h2 : (Ans.leaf D P K₂ hK₂ lb n rb).val with
    | none => rfl
    | some c =>
      rw [(Ans.leaf_val K₁ hK₁).2 ((Ans.leaf_val K₂ hK₂).1 h2)] at h1
      cases h1
  | some c => exact ((Ans.leaf_val K₂ hK₂).2 ((Ans.leaf_val K₁ hK₁).1 h1)).symm

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

theorem addRun_val (acc : List (Run R)) (r : Run R) :
    (addRun (K := DerivationKernel.over D K hK P) acc r).val = addRunP acc r := by
  have hsb := fun a b => Goals.sameBound_val (P := P) K hK a b
  at_cost K hK
  simp only [addRun, addRunP, Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val,
    apply_ite Cost.val, hsb]

theorem addRuns_val (acc rs : List (Run R)) :
    (foldL (addRun (K := DerivationKernel.over D K hK P)) acc rs).val = rs.foldl addRunP acc := by
  have hadd := fun acc r => addRun_val (K := K) (hK := hK) (P := P) acc r
  at_cost K hK
  simp only [foldL_std, Cost.foldL_val, hadd]

theorem extendRuns_val (last : Bool) (rs ys : List (Run R)) :
    (extendRuns (K := DerivationKernel.over D K hK P) last rs ys).val =
      extendRunsP D last rs ys := by
  have hadd := fun acc r => addRun_val (K := K) (hK := hK) (P := P) acc r
  at_cost K hK
  simp only [extendRuns, extendRunsP, foldL_std, Cost.foldL_val]
  congr 1
  funext acc r
  obtain ⟨o, w⟩ := r
  cases o with
  | none => rfl
  | some x =>
    cases w with
    | false => rfl
    | true =>
      simp only [Cost.foldL_val]
      congr 1
      funext acc q
      cases hq : q.1 with
      | none => exact hadd _ _
      | some y =>
        cases last
        · simp only [Bool.false_eq_true, ↓reduceIte, Cost.bind_val, hK.compose]
          cases D.compose x y with
          | none => rfl
          | some z => exact hadd _ _
        · simp only [↓reduceIte, Cost.bind_val, hK.compose]
          cases D.compose y x with
          | none => rfl
          | some z => exact hadd _ _

end kernel

/-! ## A reading at a greater depth, at any kernel -/

section two

variable {K₁ : Kernel R Cost} {hK₁ : K₁.Refines D} {K₂ : Kernel R Cost} {hK₂ : K₂.Refines D}

/-- Whether a node contains a call is the same at every greater depth and at
every kernel. -/
theorem hasCall_mono : ∀ (d : Nat) (n : Rel) (b : Bool),
    (hasCall (K := DerivationKernel.over D K₁ hK₁ P) d n).val = some b → ∀ d', d ≤ d' →
    (hasCall (K := DerivationKernel.over D K₂ hK₂ P) d' n).val = some b := by
  at_cost K₁ hK₁
  at_cost K₂ hK₂
  intro d
  induction d with
  | zero => intro n b h; simp [hasCall] at h
  | succ d ih =>
    intro n b h d' hd
    obtain ⟨d', rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have step : ∀ xs : List Rel,
        (foldL (fun (acc : Option Bool) x =>
          match acc with
          | some false => hasCall (K := DerivationKernel.over D _ hK₁ P) d x
          | r => pure r) (some false) xs).val = some b →
        (foldL (fun (acc : Option Bool) x =>
          match acc with
          | some false => hasCall (K := DerivationKernel.over D _ hK₂ P) d' x
          | r => pure r) (some false) xs).val = some b := by
      intro xs hx
      rw [foldL_std, Cost.foldL_val] at hx ⊢
      refine foldl_some_imp _ _ (fun x => rfl) xs (fun x _ c c' hc => ?_) _ _ hx
      cases c with
      | false => exact ih x c' hc d' (by omega)
      | true => exact hc
    simp only [hasCall, Cost.bind_val, over_view] at h ⊢
    split at h
    · exact h
    · exact h
    · next xs _ => exact step xs h
    · next xs _ => exact step xs h
    · next xs _ => exact step xs h

/-- The runs at an edge are the same at every greater depth and at every
kernel. -/
theorem runs_mono (last : Bool) : ∀ (d : Nat) (seen : List Rel) (n : Rel) (rs : List (Run R)),
    (runs (K := DerivationKernel.over D K₁ hK₁ P) last d seen n).val = some rs → ∀ d', d ≤ d' →
    (runs (K := DerivationKernel.over D K₂ hK₂ P) last d' seen n).val = some rs := by
  have hleaf := fun n => leaf_val_same (P := P) K₂ hK₂ K₁ hK₁ none n none
  have hadd1 := fun acc rs => addRuns_val (K := K₁) (hK := hK₁) (P := P) acc rs
  have hadd2 := fun acc rs => addRuns_val (K := K₂) (hK := hK₂) (P := P) acc rs
  have hext1 := fun rs ys => extendRuns_val (K := K₁) (hK := hK₁) (P := P) last rs ys
  have hext2 := fun rs ys => extendRuns_val (K := K₂) (hK := hK₂) (P := P) last rs ys
  at_cost K₁ hK₁
  at_cost K₂ hK₂
  intro d
  induction d with
  | zero => intro seen n rs h; simp [runs] at h
  | succ d ih =>
    intro seen n rs h d' hd
    obtain ⟨d', rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have hd' : d ≤ d' := by omega
    simp only [runs, Cost.bind_val, over_view] at h ⊢
    split at h
    · simp only [Cost.bind_val, Cost.pure_val, over_leaf] at h ⊢
      rw [hleaf]
      exact h
    · exact h
    · next xs _ =>
      simp only [foldL_std, Cost.foldL_val] at h ⊢
      refine foldl_some_imp _ _ (fun x => rfl) xs (fun x _ b b' hb => ?_) _ _ h
      simp only [Cost.bind_val] at hb ⊢
      split at hb
      · cases hb
      · next r hr =>
        rw [ih seen x r hr d' hd']
        simp only [Cost.bind_val, Cost.pure_val] at hb ⊢
        rw [← foldL_std, hadd1] at hb
        rw [← foldL_std, hadd2]
        exact hb
    · simp only [Cost.bind_val, anyL_std, Cost.anyL_val, over_eqNode, over_body] at h ⊢
      split at h
      · next hs => simp only [hs, ↓reduceIte]; exact h
      · next hs =>
        simp only [hs, Bool.false_eq_true, ↓reduceIte]
        simp only [Cost.bind_val] at h ⊢
        split at h
        · exact h
        · next bd _ => exact ih (n :: seen) bd rs h d' hd'
    · split at h
      · exact h
      · next e rest _ =>
        simp only [Cost.bind_val, foldL_std, Cost.foldL_val] at h ⊢
        cases hr : (runs (K := DerivationKernel.over D _ hK₁ P) last d seen e).val with
        | none =>
          rw [hr, foldl_none _ (fun x => rfl)] at h
          cases h
        | some r0 =>
          rw [hr] at h
          rw [ih seen e r0 hr d' hd']
          refine foldl_some_imp _ _ (fun x => rfl) rest (fun x _ b b' hb => ?_) _ _ h
          simp only at hb ⊢
          split at hb
          · next hany =>
            simp only [hany, ↓reduceIte]
            simp only [Cost.bind_val] at hb ⊢
            split at hb
            · cases hb
            · next ys hys =>
              rw [ih seen x ys hys d' hd']
              simp only [Cost.bind_val, Cost.pure_val, hext1] at hb
              simp only [Cost.bind_val, Cost.pure_val, hext2]
              exact hb
          · next hany => simp only [hany, Bool.false_eq_true, ↓reduceIte]; exact hb

/-- **A reading that does not give up returns the same at every greater
depth and at every kernel.** -/
theorem readEdge_mono (last : Bool) (d : Nat) (n : Rel) (e : Option (List R))
    (h : (readEdge (K := DerivationKernel.over D K₁ hK₁ P) last d n).val = some e) (d' : Nat)
    (hd : d ≤ d') : (readEdge (K := DerivationKernel.over D K₂ hK₂ P) last d' n).val = some e := by
  have hc := fun b hb => hasCall_mono (K₁ := K₁) (hK₁ := hK₁) (K₂ := K₂) (hK₂ := hK₂) (P := P)
    d n b hb d' hd
  have hr := fun rs hrs => runs_mono (K₁ := K₁) (hK₁ := hK₁) (K₂ := K₂) (hK₂ := hK₂) (P := P)
    last d [] n rs hrs d' hd
  at_cost K₁ hK₁
  at_cost K₂ hK₂
  simp only [readEdge, Cost.bind_val] at h ⊢
  split at h
  · cases h
  · next hb => rw [hc _ hb]; exact h
  · next hb =>
    rw [hc _ hb]
    simp only [Cost.bind_val] at h ⊢
    split at h
    · cases h
    · next rs hrs =>
      rw [hr rs hrs]
      simp only [Cost.bind_val, Cost.pure_val, foldL_std, Cost.foldL_val] at h ⊢
      rw [← h]
      congr 2
      funext acc r
      cases acc with
      | none => rfl
      | some ps =>
        cases hr1 : r.1 with
        | none => rfl
        | some x =>
          cases last
          · simp only [Bool.false_eq_true, ↓reduceIte, Cost.bind_val, hK₁.leftBound,
              hK₂.leftBound]
            cases D.leftBound x with
            | none => rfl
            | some p =>
              simp only [Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val, hK₁.eq, hK₂.eq]
          · simp only [↓reduceIte, Cost.bind_val, hK₁.rightBound, hK₂.rightBound]
            cases D.rightBound x with
            | none => rfl
            | some p =>
              simp only [Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val, hK₁.eq, hK₂.eq]

end two

/-- **What an edge reads is a fact of the program**: two readings that do not
give up, at any depths and any kernels, return the same. -/
theorem Reads.unique {n : Rel} {last : Bool} {e₁ e₂ : Option (List R)}
    (h₁ : Reads D P n last e₁) (h₂ : Reads D P n last e₂) : e₁ = e₂ := by
  obtain ⟨K₁, hK₁, d₁, h₁⟩ := h₁
  obtain ⟨K₂, hK₂, d₂, h₂⟩ := h₂
  have a := readEdge_mono (K₂ := K₁) (hK₂ := hK₁) last d₁ n e₁ h₁ (max d₁ d₂) (le_max_left _ _)
  have b := readEdge_mono (K₂ := K₁) (hK₂ := hK₁) last d₂ n e₂ h₂ (max d₁ d₂) (le_max_right _ _)
  rw [a] at b
  cases b
  rfl


end Symmetric

end RwLog
