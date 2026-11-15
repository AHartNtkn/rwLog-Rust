/-
# What a reading of an edge returns, with no kernel in it

`readEdge` (`Rungs/Symmetric/Machine.lean`) is written over the operations
of a kernel, at a charge. What it returns does not depend on the kernel
(`Rungs/Symmetric/EdgeSame.lean`). Here it is written out as functions of
the program and the domain alone: `hasCallP`, `runsP`, `readEdgeP`, with
`hasCall_val`, `runs_val`, `readEdge_val`. What is proved of a reading can
then be proved of these.
-/
import RwLog.Rungs.Symmetric.EdgeSame

namespace RwLog

namespace Symmetric

open Traverse Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- What `hasCall` returns. -/
def hasCallP : Nat → Rel → Option Bool
  | 0, _ => none
  | d + 1, n =>
    match n.view with
    | .span _ => some false
    | .call _ _ => some true
    | .chain xs | .meet xs | .union xs =>
      xs.foldl (fun (acc : Option Bool) x =>
        match acc with
        | some false => hasCallP d x
        | r => r) (some false)

/-- The runs of a span: its representative, whole, if it has one. -/
def leafRuns (D : Domain R) : Rel → List (Run R)
  | .span s =>
    match spanBoth D none s none with
    | some c => [(some c, true)]
    | none => []
  | _ => []

/-- What `runs` returns. -/
def runsP (D : Domain R) (P : Program) (last : Bool) : Nat → List Rel → Rel → Option (List (Run R))
  | 0, _, _ => none
  | d + 1, seen, n =>
    match n.view with
    | .span _ => some (leafRuns D n)
    | .meet _ => some [(none, false)]
    | .union xs =>
      xs.foldl (fun (acc : Option (List (Run R))) x =>
        match acc with
        | none => none
        | some rs =>
          match runsP D P last d seen x with
          | none => none
          | some r => some (r.foldl addRunP rs)) (some [])
    | .call _ _ =>
      if seen.any (fun m => decide (m = n)) then some [(none, false)]
      else
        match Charged.bodyOf P n with
        | none => some []
        | some bd => runsP D P last d (n :: seen) bd
    | .chain xs =>
      match (if last then xs.reverse else xs) with
      | [] => some [(none, false)]
      | e :: rest =>
        rest.foldl (fun (acc : Option (List (Run R))) x =>
          match acc with
          | none => none
          | some rs =>
            if rs.any (·.2) then
              match runsP D P last d seen x with
              | none => none
              | some ys => some (extendRunsP D last rs ys)
            else acc) (runsP D P last d seen e)

/-- The interfaces of the runs `rs` at one end, if each has one. -/
def boundsP (D : Domain R) (last : Bool) (rs : List (Run R)) : Option (List R) :=
  rs.foldl (fun (acc : Option (List R)) (r : Run R) =>
    match acc, r.1 with
    | some ps, some x =>
      match (if last then D.rightBound x else D.leftBound x) with
      | none => none
      | some p => some (if ps.any (fun q => decide (q = p)) then ps else ps ++ [p])
    | _, _ => none) (some [])

/-- What `readEdge` returns. -/
def readEdgeP (D : Domain R) (P : Program) (last : Bool) (d : Nat) (n : Rel) :
    Option (Option (List R)) :=
  match hasCallP d n with
  | none => none
  | some false => some none
  | some true =>
    match runsP D P last d [] n with
    | none => none
    | some rs => some (boundsP D last rs)

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

theorem hasCall_val : ∀ (d : Nat) (n : Rel),
    (hasCall (K := DerivationKernel.over D K hK P) d n).val = hasCallP d n := by
  at_cost K hK
  intro d
  induction d with
  | zero => intro n; rfl
  | succ d ih =>
    intro n
    have step : ∀ (xs : List Rel) (acc : Option Bool),
        (foldL (fun (acc : Option Bool) x =>
          match acc with
          | some false => hasCall (K := DerivationKernel.over D _ hK P) d x
          | r => pure r) acc xs).val =
        xs.foldl (fun (acc : Option Bool) x =>
          match acc with
          | some false => hasCallP d x
          | r => r) acc := by
      intro xs acc
      rw [foldL_std, Cost.foldL_val]
      congr 1
      funext acc x
      match acc with
      | some false => exact ih x
      | some true => rfl
      | none => rfl
    simp only [hasCall, hasCallP, Cost.bind_val, over_view, Charged.viewNode, Charged.op]
    cases n.view with
    | span _ => rfl
    | call _ _ => rfl
    | chain xs => exact step xs _
    | meet xs => exact step xs _
    | union xs => exact step xs _

theorem leaf_runs (n : Rel) :
    (match (Ans.leaf D P K hK none n none).val with
      | some a => [(some a.span, true)]
      | none => []) = leafRuns D n := by
  cases h : (Ans.leaf D P K hK none n none).val with
  | some a =>
    obtain ⟨s, rfl, -, -, hs, -⟩ := (Ans.leaf_val K hK).1 h
    simp only [leafRuns, hs]
  | none =>
    cases n with
    | span s =>
      cases hs : spanBoth D none s none with
      | none => simp only [leafRuns, hs]
      | some c =>
        exfalso
        have hv : Valid D P ⟨none, .span s, none⟩ c :=
          Valid.leaf (fun _ h => by cases h) (fun _ h => by cases h) hs
        have := (Ans.leaf_val (P := P) K hK (c := ⟨_, c, hv⟩)).2
          ⟨s, rfl, (fun _ h => by cases h), (fun _ h => by cases h), hs, rfl⟩
        rw [h] at this
        cases this
    | _ => rfl

theorem runs_val (last : Bool) : ∀ (d : Nat) (seen : List Rel) (n : Rel),
    (runs (K := DerivationKernel.over D K hK P) last d seen n).val = runsP D P last d seen n := by
  have hleaf := fun n => leaf_runs (K := K) (hK := hK) (P := P) n
  have hadd := fun acc rs => addRuns_val (K := K) (hK := hK) (P := P) acc rs
  have hext := fun rs ys => extendRuns_val (K := K) (hK := hK) (P := P) last rs ys
  at_cost K hK
  intro d
  induction d with
  | zero => intro seen n; rfl
  | succ d ih =>
    intro seen n
    simp only [runs, runsP, Cost.bind_val, over_view, Charged.viewNode, Charged.op]
    cases hv : n.view with
    | span _ =>
      simp only [NodeView.forget, Cost.bind_val, Cost.pure_val, over_leaf, over_span]
      rw [← hleaf n]
      cases (Ans.leaf D P _ hK none n none).val <;> rfl
    | meet _ => rfl
    | union xs =>
      simp only [NodeView.forget, foldL_std, Cost.foldL_val]
      congr 1
      funext acc x
      cases acc with
      | none => rfl
      | some rs =>
        simp only [Cost.bind_val, ih]
        cases runsP D P last d seen x with
        | none => rfl
        | some r =>
          simp only [Cost.bind_val, Cost.pure_val]
          rw [← foldL_std, hadd]
    | call _ _ =>
      simp only [NodeView.forget, Cost.bind_val, anyL_std, Cost.anyL_val, over_eqNode, over_body, Charged.eqNode,
        Charged.body, Charged.op]
      cases seen.any (fun m => decide (m = n)) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Cost.bind_val]
        cases Charged.bodyOf P n with
        | none => rfl
        | some bd => exact ih _ _
    | chain xs =>
      simp only [NodeView.forget]
      cases (if last = true then xs.reverse else xs) with
      | nil => rfl
      | cons e rest =>
        simp only [Cost.bind_val, foldL_std, Cost.foldL_val, ih]
        congr 1
        funext acc x
        cases acc with
        | none => rfl
        | some rs =>
          cases hany : rs.any (·.2) with
          | false => simp only [hany, Bool.false_eq_true, ↓reduceIte]; rfl
          | true =>
            simp only [hany, ↓reduceIte, Cost.bind_val, ih]
            cases runsP D P last d seen x with
            | none => rfl
            | some ys => simp only [Cost.bind_val, Cost.pure_val, hext]

theorem readEdge_val (last : Bool) (d : Nat) (n : Rel) :
    (readEdge (K := DerivationKernel.over D K hK P) last d n).val = readEdgeP D P last d n := by
  have hc := hasCall_val (K := K) (hK := hK) (P := P) d n
  have hr := runs_val (K := K) (hK := hK) (P := P) last d [] n
  at_cost K hK
  simp only [readEdge, readEdgeP, Cost.bind_val, hc]
  cases hasCallP d n with
  | none => rfl
  | some c =>
    cases c with
    | false => rfl
    | true =>
      simp only [Cost.bind_val, hr]
      cases runsP D P last d [] n with
      | none => rfl
      | some rs =>
        simp only [Cost.bind_val, Cost.pure_val, foldL_std, Cost.foldL_val, boundsP]
        congr 2
        funext acc r
        cases acc with
        | none => rfl
        | some ps =>
          cases hr1 : r.1 with
          | none => rfl
          | some x =>
            cases last
            · simp only [Bool.false_eq_true, ↓reduceIte, Cost.bind_val, hK.leftBound]
              cases D.leftBound x with
              | none => rfl
              | some p =>
                simp only [Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val, hK.eq]
            · simp only [↓reduceIte, Cost.bind_val, hK.rightBound]
              cases D.rightBound x with
              | none => rfl
              | some p =>
                simp only [Cost.bind_val, Cost.pure_val, anyL_std, Cost.anyL_val, hK.eq]

end kernel

/-- **An edge reads `e` exactly when its reading written out returns `e` at
some depth.** -/
theorem reads_iff {n : Rel} {last : Bool} {e : Option (List R)} :
    Reads D P n last e ↔ ∃ (K : Kernel R Cost) (_ : K.Refines D) (d : Nat),
      readEdgeP D P last d n = some e := by
  constructor
  · rintro ⟨K, hK, d, h⟩
    exact ⟨K, hK, d, by rw [← readEdge_val (K := K) (hK := hK)]; exact h⟩
  · rintro ⟨K, hK, d, h⟩
    exact ⟨K, hK, d, by rw [readEdge_val]; exact h⟩

end Symmetric

end RwLog
