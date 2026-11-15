/-
# The reading of an edge, on the mirror image of a node

What the engine reads at an end of a node (`readEdge`, written out in
`Rungs/Symmetric/EdgePure.lean`) and what it reads at the other end of the
image of the node under the node map (`nmap b t`,
`Kernel/NormalFormMap.lean`), in a program whose bodies are the images of
the bodies.

The image has a call where the node has one (`hasCallP_nmap`). Every run of
spans at the end of the image is the image of a run at the end of the node,
conversed when the converse is taken (`runsP_nmap`): the members of a union
are the same up to their order, the members of a chain are met in the same
order from the other end, and the converse of a composition is the
composition of the converses the other way round. An interface is its own
converse, so the image shows no interface the node does not show
(`reads_nmap`): a check that is offered on a node is offered on its image,
over interfaces of the node.

The lists of runs are compared as sets: the two readings meet the members of
a union in different orders.
-/
import RwLog.Rungs.Symmetric.EdgePure
import RwLog.Rungs.Symmetric.ReadLive
import RwLog.Rungs.Tabled.MapGoal

namespace RwLog

namespace Symmetric

open Answer
open Tabled (smap spanBoth_smap leftBound_swap fo_nmap)

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R}

/-! ## What the steps of a reading hold -/

omit [Answer R] in
theorem mem_addRunP {acc : List (Run R)} {r q : Run R} : q ∈ addRunP acc r ↔ q ∈ acc ∨ q = r := by
  unfold addRunP
  split
  · next h =>
    refine ⟨.inl, ?_⟩
    rintro (h' | rfl)
    · exact h'
    · obtain ⟨p, hp, hpe⟩ := List.any_eq_true.1 h
      split at hpe
      · next h2 =>
        have h1 := of_decide_eq_true hpe
        have e : p = q := Prod.ext h1 h2
        exact e ▸ hp
      · cases hpe
  · simp [List.mem_append]

omit [Answer R] in
theorem mem_addRuns {q : Run R} : ∀ (rs acc : List (Run R)),
    q ∈ rs.foldl addRunP acc ↔ q ∈ acc ∨ q ∈ rs
  | [], acc => by simp
  | r :: rs, acc => by
    rw [List.foldl_cons, mem_addRuns rs, mem_addRunP, List.mem_cons, or_assoc]

/-- The run `r` is the run `(some x, true)` continued through the run `q` of
the next member. -/
def StepRun (D : Domain R) (last : Bool) (x : R) (q r : Run R) : Prop :=
  (q.1 = none ∧ r = (some x, false)) ∨
    ∃ y z, q.1 = some y ∧ (if last then D.compose y x else D.compose x y) = some z ∧
      r = (some z, q.2)

/-- One run of the next member, in `extendRunsP`. -/
def innerStep (D : Domain R) (last : Bool) (x : R) (acc : List (Run R)) (q : Run R) :
    List (Run R) :=
  match q.1 with
  | none => addRunP acc (some x, false)
  | some y =>
    match (if last then D.compose y x else D.compose x y) with
    | none => acc
    | some z => addRunP acc (some z, q.2)

/-- One run at the edge, in `extendRunsP`. -/
def outerStep (D : Domain R) (last : Bool) (ys : List (Run R)) (acc : List (Run R)) (r : Run R) :
    List (Run R) :=
  match r with
  | (some x, true) => ys.foldl (innerStep D last x) acc
  | _ => acc

omit [Answer R] in
theorem extendRunsP_eq (last : Bool) (rs ys : List (Run R)) :
    extendRunsP D last rs ys = rs.foldl (outerStep D last ys) (rs.filter fun r => !r.2) := rfl

omit [Answer R] in
theorem mem_innerStep {last : Bool} {x : R} {acc : List (Run R)} {q r : Run R} :
    r ∈ innerStep D last x acc q ↔ r ∈ acc ∨ StepRun D last x q r := by
  unfold innerStep StepRun
  cases hq : q.1 with
  | none =>
    dsimp only
    rw [mem_addRunP]
    refine or_congr_right ⟨fun h => .inl ⟨rfl, h⟩, ?_⟩
    rintro (⟨-, h⟩ | ⟨y, z, hy, -⟩)
    · exact h
    · cases hy
  | some y =>
    dsimp only
    cases hc : (if last = true then D.compose y x else D.compose x y) with
    | none =>
      dsimp only
      refine ⟨.inl, ?_⟩
      rintro (h | ⟨h, -⟩ | ⟨y', z, hy, hz, -⟩)
      · exact h
      · cases h
      · cases hy
        rw [hc] at hz
        cases hz
    | some z =>
      dsimp only
      rw [mem_addRunP]
      refine or_congr_right ⟨fun h => .inr ⟨y, z, rfl, hc, h⟩, ?_⟩
      rintro (⟨h, -⟩ | ⟨y', z', hy, hz, h⟩)
      · cases h
      · cases hy
        rw [hc] at hz
        cases hz
        exact h

omit [Answer R] in
theorem mem_inner {last : Bool} {x : R} {r : Run R} : ∀ (ys acc : List (Run R)),
    r ∈ ys.foldl (innerStep D last x) acc ↔ r ∈ acc ∨ ∃ q ∈ ys, StepRun D last x q r
  | [], acc => by simp
  | q :: ys, acc => by
    rw [List.foldl_cons, mem_inner ys, mem_innerStep, or_assoc]
    simp only [List.mem_cons, exists_eq_or_imp]

omit [Answer R] in
theorem mem_outerStep {last : Bool} {ys acc : List (Run R)} {r p : Run R} :
    p ∈ outerStep D last ys acc r ↔
      p ∈ acc ∨ ∃ x, r = (some x, true) ∧ ∃ q ∈ ys, StepRun D last x q p := by
  obtain ⟨o, w⟩ := r
  cases o with
  | none => simp [outerStep]
  | some x =>
    cases w with
    | false => simp [outerStep]
    | true => simp [outerStep, mem_inner]

omit [Answer R] in
theorem mem_outer {last : Bool} {ys : List (Run R)} {p : Run R} : ∀ (rs acc : List (Run R)),
    p ∈ rs.foldl (outerStep D last ys) acc ↔
      p ∈ acc ∨ ∃ x, (some x, true) ∈ rs ∧ ∃ q ∈ ys, StepRun D last x q p
  | [], acc => by simp
  | r :: rs, acc => by
    rw [List.foldl_cons, mem_outer rs, mem_outerStep, or_assoc]
    refine or_congr_right ?_
    constructor
    · rintro (⟨x, rfl, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, List.mem_cons_self .., h⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
    · rintro ⟨x, hx, h⟩
      rcases List.mem_cons.1 hx with e | hx
      · exact .inl ⟨x, e.symm, h⟩
      · exact .inr ⟨x, hx, h⟩

omit [Answer R] in
/-- The runs continued through a member: those that are not whole, and each
whole one continued through each run of the member. -/
theorem mem_extendRunsP {last : Bool} {rs ys : List (Run R)} {p : Run R} :
    p ∈ extendRunsP D last rs ys ↔
      (p ∈ rs ∧ p.2 = false) ∨ ∃ x, (some x, true) ∈ rs ∧ ∃ q ∈ ys, StepRun D last x q p := by
  rw [extendRunsP_eq, mem_outer]
  simp [List.mem_filter]

/-! ## The folds of a reading -/

theorem callFold_stuck (f : Rel → Option Bool) : ∀ (xs : List Rel) (r : Option Bool),
    r ≠ some false → xs.foldl (callStep f) r = r
  | [], _, _ => rfl
  | x :: xs, r, h => by
    have e : callStep f r x = r := by
      match r, h with
      | none, _ => rfl
      | some true, _ => rfl
      | some false, h => exact absurd rfl h
    rw [List.foldl_cons, e]
    exact callFold_stuck f xs r h

theorem callFold_false (f : Rel → Option Bool) : ∀ xs : List Rel,
    xs.foldl (callStep f) (some false) = some false → ∀ x ∈ xs, f x = some false
  | [], _, _, hx => by cases hx
  | y :: xs, h, x, hx => by
    rw [List.foldl_cons] at h
    have e : callStep f (some false) y = f y := rfl
    rw [e] at h
    cases hf : f y with
    | none => rw [hf, callFold_stuck f xs none (by simp)] at h; cases h
    | some c =>
      cases c with
      | true => rw [hf, callFold_stuck f xs (some true) (by simp)] at h; cases h
      | false =>
        rw [hf] at h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hf
        · exact callFold_false f xs h x hx

theorem callFold_true (f : Rel → Option Bool) : ∀ xs : List Rel,
    xs.foldl (callStep f) (some false) = some true → ∃ x ∈ xs, f x = some true
  | [], h => by cases h
  | y :: xs, h => by
    rw [List.foldl_cons] at h
    have e : callStep f (some false) y = f y := rfl
    rw [e] at h
    cases hf : f y with
    | none => rw [hf, callFold_stuck f xs none (by simp)] at h; cases h
    | some c =>
      cases c with
      | true => exact ⟨y, List.mem_cons_self .., hf⟩
      | false =>
        rw [hf] at h
        obtain ⟨x, hx, hfx⟩ := callFold_true f xs h
        exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

omit [Answer R] in
theorem unionFold_none (f : Rel → Option (List (Run R))) : ∀ xs : List Rel,
    xs.foldl (unionStep f) none = none
  | [] => rfl
  | _ :: xs => unionFold_none f xs

omit [Answer R] in
/-- The runs of a union: every member is read, and the runs are those of the
members. -/
theorem unionFold (f : Rel → Option (List (Run R))) : ∀ (xs : List Rel) (acc rs : List (Run R)),
    xs.foldl (unionStep f) (some acc) = some rs →
      (∀ x ∈ xs, ∃ r, f x = some r) ∧
        ∀ q, q ∈ rs ↔ q ∈ acc ∨ ∃ x ∈ xs, ∃ r, f x = some r ∧ q ∈ r
  | [], acc, rs, h => by
    cases h
    simp
  | y :: xs, acc, rs, h => by
    rw [List.foldl_cons] at h
    cases hf : f y with
    | none =>
      have e : unionStep f (some acc) y = none := by simp only [unionStep, hf]
      rw [e, unionFold_none] at h
      cases h
    | some r =>
      have e : unionStep f (some acc) y = some (r.foldl addRunP acc) := by
        simp only [unionStep, hf]
      rw [e] at h
      obtain ⟨h1, h2⟩ := unionFold f xs _ rs h
      refine ⟨fun x hx => ?_, fun q => ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨r, hf⟩
        · exact h1 x hx
      · rw [h2 q, mem_addRuns, or_assoc]
        refine or_congr_right ?_
        constructor
        · rintro (hq | ⟨x, hx, r', hr', hq⟩)
          · exact ⟨y, List.mem_cons_self .., r, hf, hq⟩
          · exact ⟨x, List.mem_cons_of_mem _ hx, r', hr', hq⟩
        · rintro ⟨x, hx, r', hr', hq⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · rw [hf] at hr'
            cases hr'
            exact .inl hq
          · exact .inr ⟨x, hx, r', hr', hq⟩

omit [Answer R] in
theorem chainFold_none (last : Bool) (f : Rel → Option (List (Run R))) : ∀ xs : List Rel,
    xs.foldl (chainStep D last f) none = none
  | [] => rfl
  | _ :: xs => chainFold_none last f xs

/-- The interface a run shows at one end. -/
def bnd (D : Domain R) (last : Bool) (x : R) : Option R :=
  if last then D.rightBound x else D.leftBound x

theorem boundFold_none (last : Bool) : ∀ rs : List (Run R),
    rs.foldl (boundStep D last) none = none
  | [] => rfl
  | _ :: rs => boundFold_none last rs

/-- The interfaces of the runs: every run shows one of them, and each is
shown by a run. -/
theorem boundFold (last : Bool) : ∀ (rs : List (Run R)) (ps0 ps : List R),
    rs.foldl (boundStep D last) (some ps0) = some ps →
      (∀ r ∈ rs, ∃ x p, r.1 = some x ∧ bnd D last x = some p ∧ p ∈ ps) ∧
        (∀ p ∈ ps0, p ∈ ps) ∧
        ∀ p ∈ ps, p ∈ ps0 ∨ ∃ r ∈ rs, ∃ x, r.1 = some x ∧ bnd D last x = some p
  | [], ps0, ps, h => by
    cases h
    simp
  | (o, w) :: rs, ps0, ps, h => by
    rw [List.foldl_cons] at h
    cases o with
    | none =>
      have e : boundStep D last (some ps0) (none, w) = none := rfl
      rw [e, boundFold_none] at h
      cases h
    | some x =>
      cases hb : bnd D last x with
      | none =>
        have e : boundStep D last (some ps0) (some x, w) = none := by
          unfold bnd at hb
          simp only [boundStep, hb]
        rw [e, boundFold_none] at h
        cases h
      | some p =>
        have e : boundStep D last (some ps0) (some x, w) =
            some (if ps0.any (fun q => decide (q = p)) then ps0 else ps0 ++ [p]) := by
          unfold bnd at hb
          simp only [boundStep, hb]
        rw [e] at h
        obtain ⟨h1, h2, h3⟩ := boundFold last rs _ ps h
        have hp : p ∈ (if ps0.any (fun q => decide (q = p)) then ps0 else ps0 ++ [p]) := by
          split
          · next hany =>
            obtain ⟨q, hq, e⟩ := List.any_eq_true.1 hany
            exact of_decide_eq_true e ▸ hq
          · simp
        have hsub : ∀ q ∈ ps0, q ∈ (if ps0.any (fun q => decide (q = p)) then ps0
            else ps0 ++ [p]) := by
          intro q hq
          split
          · exact hq
          · exact List.mem_append_left _ hq
        refine ⟨fun r hr => ?_, fun q hq => h2 q (hsub q hq), fun q hq => ?_⟩
        · rcases List.mem_cons.1 hr with rfl | hr
          · exact ⟨x, p, rfl, hb, h2 p hp⟩
          · exact h1 r hr
        · rcases h3 q hq with hq0 | ⟨r, hr, y, hy, hyq⟩
          · split at hq0
            · exact .inl hq0
            · rcases List.mem_append.1 hq0 with hq0 | hq0
              · exact .inl hq0
              · obtain rfl : q = p := by simpa using hq0
                exact .inr ⟨_, List.mem_cons_self .., x, rfl, hb⟩
          · exact .inr ⟨r, List.mem_cons_of_mem _ hr, y, hy, hyq⟩

/-- Runs that each show an interface have interfaces. -/
theorem boundFold_some (last : Bool) : ∀ (rs : List (Run R)) (ps0 : List R),
    (∀ r ∈ rs, ∃ x p, r.1 = some x ∧ bnd D last x = some p) →
      ∃ ps, rs.foldl (boundStep D last) (some ps0) = some ps
  | [], ps0, _ => ⟨ps0, rfl⟩
  | (o, w) :: rs, ps0, h => by
    obtain ⟨x, p, hx, hb⟩ := h _ (List.mem_cons_self ..)
    obtain rfl : o = some x := hx
    have e : boundStep D last (some ps0) (some x, w) =
        some (if ps0.any (fun q => decide (q = p)) then ps0 else ps0 ++ [p]) := by
      unfold bnd at hb
      simp only [boundStep, hb]
    rw [List.foldl_cons, e]
    exact boundFold_some last rs _ fun r hr => h r (List.mem_cons_of_mem _ hr)

/-! ## Runs and their images -/

/-- The image of a run: conversed when the converse is taken. -/
def rmap (b : Bool) (r : Run R) : Run R := (r.1.map (smap b), r.2)

/-- Every run of the second list is the image of a run of the first. -/
def Sub (b : Bool) (rs rs' : List (Run R)) : Prop := ∀ r' ∈ rs', ∃ r ∈ rs, r' = rmap b r

omit [DecidableEq R] in
theorem sub_any {b : Bool} {rs rs' : List (Run R)} (h : Sub b rs rs')
    (ha : rs'.any (·.2) = true) : rs.any (·.2) = true := by
  obtain ⟨r', hr', hw⟩ := List.any_eq_true.1 ha
  obtain ⟨r, hr, rfl⟩ := h r' hr'
  exact List.any_eq_true.2 ⟨r, hr, hw⟩

section laws

variable {M : Interp} (hL : D.Lawful M)
include hL

omit [DecidableEq R] in
/-- The converse of a composition is the composition of the converses, taken
from the other end. -/
theorem compose_smap (b last : Bool) (x y : R) :
    (if (last ^^ b) = true then D.compose (smap b y) (smap b x)
      else D.compose (smap b x) (smap b y)) =
      (if last = true then D.compose y x else D.compose x y).map (smap b) := by
  cases b
  · have e : smap (R := R) false = id := rfl
    cases last <;> simp [e]
  · cases last
    · exact hL.compose_swap x y
    · exact hL.compose_swap y x

omit [DecidableEq R] in
/-- The interface of the converse of a run at the other end is its
interface. -/
theorem bnd_smap (b last : Bool) (x : R) : bnd D (last ^^ b) (smap b x) = bnd D last x := by
  cases b
  · cases last <;> rfl
  · cases last
    · show D.rightBound (Answer.swap x) = D.leftBound x
      rfl
    · exact leftBound_swap hL x

/-- The runs continued through a member, on the image. -/
theorem sub_extend {b last : Bool} {rs rs' ys ys' : List (Run R)} (hrs : Sub b rs rs')
    (hys : Sub b ys ys') :
    Sub b (extendRunsP D last rs ys) (extendRunsP D (last ^^ b) rs' ys') := by
  intro r' hr'
  rcases mem_extendRunsP.1 hr' with ⟨h1, h2⟩ | ⟨x', hx', q', hq', hstep⟩
  · obtain ⟨r, hr, rfl⟩ := hrs r' h1
    exact ⟨r, mem_extendRunsP.2 (.inl ⟨hr, h2⟩), rfl⟩
  obtain ⟨⟨o, w⟩, hr0, e0⟩ := hrs _ hx'
  obtain ⟨q, hq, rfl⟩ := hys q' hq'
  cases o with
  | none => cases e0
  | some x =>
    obtain ⟨rfl, rfl⟩ : x' = smap b x ∧ true = w := by
      simpa [rmap] using e0
    rcases hstep with ⟨hn, rfl⟩ | ⟨y', z', hy', hz', rfl⟩
    · have hq1 : q.1 = none := by
        cases h : q.1 with
        | none => rfl
        | some y => simp [rmap, h] at hn
      exact ⟨(some x, false),
        mem_extendRunsP.2 (.inr ⟨x, hr0, q, hq, .inl ⟨hq1, rfl⟩⟩), rfl⟩
    · cases hq1 : q.1 with
      | none => simp [rmap, hq1] at hy'
      | some y =>
        obtain rfl : y' = smap b y := by simpa [rmap, hq1] using hy'.symm
        rw [compose_smap hL] at hz'
        cases hc : (if last = true then D.compose y x else D.compose x y) with
        | none => rw [hc] at hz'; cases hz'
        | some z =>
          rw [hc] at hz'
          obtain rfl : smap b z = z' := by simpa using hz'
          exact ⟨(some z, q.2),
            mem_extendRunsP.2 (.inr ⟨x, hr0, q, hq, .inr ⟨y, z, hq1, hc, rfl⟩⟩), rfl⟩

end laws

/-! ## The members of the image of a node -/

/-- The members of the image of a chain, a meet or a union are the images of
the members. -/
theorem members_nmap {n : Rel} (hn : Normal n) (b t : Bool) :
    (∀ xs, n.view = .chain xs → (∀ x ∈ xs, Normal x) ∧
      (nmap b t n).view = .chain ((if b then xs.reverse else xs).map (nmap b t))) ∧
    (∀ xs, n.view = .meet xs → (∀ x ∈ xs, Normal x) ∧ ∃ xs', (nmap b t n).view = .meet xs' ∧
      ∀ z, z ∈ xs' ↔ ∃ x ∈ xs, z = nmap b t x) ∧
    (∀ xs, n.view = .union xs → (∀ x ∈ xs, Normal x) ∧ ∃ xs', (nmap b t n).view = .union xs' ∧
      ∀ z, z ∈ xs' ↔ ∃ x ∈ xs, z = nmap b t x) := by
  refine ⟨fun xs hv => ⟨fun x hx => ((hn.view_chain hv).2.1 x hx).1, hn.view_chain_nmap hv b t⟩,
    fun xs hv => ⟨fun x hx => ((hn.view_meet hv).2.1 x hx).1, _, hn.view_meet_nmap hv b t,
      fun z => ?_⟩,
    fun xs hv => ⟨fun x hx => ((hn.view_union hv).1 x hx).1, _, hn.view_union_nmap hv b t,
      fun z => ?_⟩⟩
  · rw [(sortedParts_perm _).mem_iff, List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩⟩
  · rw [mem_sortedBranches, List.mem_map]
    constructor
    · rintro ⟨⟨x, hx, e⟩, -⟩
      exact ⟨x, hx, e.symm⟩
    · rintro ⟨x, hx, rfl⟩
      have := (hn.view_union hv).1 x hx
      exact ⟨⟨x, hx, rfl⟩, this.1.nmap_ne_zero this.2.2 b t⟩

/-! ## The image has a call where the node has one -/

theorem hasCallP_nmap (b t : Bool) : ∀ (d : Nat) (n : Rel) (c c' : Bool), Normal n →
    hasCallP d n = some c → hasCallP d (nmap b t n) = some c' → c' = c := by
  intro d
  induction d with
  | zero => intro n c c' _ h; cases h
  | succ d ih =>
    intro n c c' hn h h'
    have close : ∀ xs xs' : List Rel, (∀ x ∈ xs, Normal x) →
        (∀ z, z ∈ xs' ↔ ∃ x ∈ xs, z = nmap b t x) →
        xs.foldl (callStep (hasCallP d)) (some false) = some c →
        xs'.foldl (callStep (hasCallP d)) (some false) = some c' → c' = c := by
      intro xs xs' hnorm hmem hf hf'
      cases c with
      | false =>
        cases c' with
        | false => rfl
        | true =>
          obtain ⟨z, hz, hzt⟩ := callFold_true _ xs' hf'
          obtain ⟨x, hx, rfl⟩ := (hmem z).1 hz
          exact ih x false true (hnorm x hx) (callFold_false _ xs hf x hx) hzt
      | true =>
        cases c' with
        | true => rfl
        | false =>
          obtain ⟨x, hx, hxt⟩ := callFold_true _ xs hf
          exact ih x true false (hnorm x hx) hxt
            (callFold_false _ xs' hf' _ ((hmem _).2 ⟨x, hx, rfl⟩))
    obtain ⟨mc, mm, mu⟩ := members_nmap hn b t
    cases hv : n.view with
    | span s =>
      have hv' := Normal.view_span hv b t
      simp only [hasCallP, hv, hv', Option.some.injEq] at h h'
      rw [← h, ← h']
    | call nm fl =>
      have hv' := Normal.view_call hv b t
      simp only [hasCallP, hv, hv', Option.some.injEq] at h h'
      rw [← h, ← h']
    | chain xs =>
      obtain ⟨hnorm, hv'⟩ := mc xs hv
      simp only [hasCallP, hv, hv'] at h h'
      exact close xs _ hnorm (fun z => by
        cases b <;> simp [List.mem_map, eq_comm]) h h'
    | meet xs =>
      obtain ⟨hnorm, xs', hv', hmem⟩ := mm xs hv
      simp only [hasCallP, hv, hv'] at h h'
      exact close xs xs' hnorm hmem h h'
    | union xs =>
      obtain ⟨hnorm, xs', hv', hmem⟩ := mu xs hv
      simp only [hasCallP, hv, hv'] at h h'
      exact close xs xs' hnorm hmem h h'

/-! ## The runs of the image are images of the runs -/

section runs

variable {P P' : Program} {b t : Bool} {M : Interp} (hL : D.Lawful M)
  (hbody : ∀ e, Normal e → Charged.bodyOf P' (nmap b t e) = (Charged.bodyOf P e).map (nmap b t))
  (hP : ProgFO P)
include hL hbody hP

omit hbody hP in
/-- The members of a chain, on the image. -/
theorem chainFold_sub (last : Bool) (f f' : Rel → Option (List (Run R))) :
    ∀ (rest : List Rel) (a a' rs rs' : List (Run R)),
      (∀ x ∈ rest, ∀ r r', f x = some r → f' (nmap b t x) = some r' → Sub b r r') →
      Sub b a a' →
      rest.foldl (chainStep D last f) (some a) = some rs →
      (rest.map (nmap b t)).foldl (chainStep D (last ^^ b) f') (some a') = some rs' →
      Sub b rs rs'
  | [], a, a', rs, rs', _, ha, h, h' => by
    cases h
    cases h'
    exact ha
  | x :: rest, a, a', rs, rs', hf, ha, h, h' => by
    rw [List.map_cons, List.foldl_cons] at h'
    rw [List.foldl_cons] at h
    have hrest : ∀ y ∈ rest, ∀ r r', f y = some r → f' (nmap b t y) = some r' → Sub b r r' :=
      fun y hy => hf y (List.mem_cons_of_mem _ hy)
    cases hany' : a'.any (·.2) with
    | true =>
      have hany := sub_any ha hany'
      cases hfx : f x with
      | none =>
        have e : chainStep D last f (some a) x = none := by simp only [chainStep, hany, hfx]; rfl
        rw [e, chainFold_none] at h
        cases h
      | some ys =>
        cases hfx' : f' (nmap b t x) with
        | none =>
          have e : chainStep D (last ^^ b) f' (some a') (nmap b t x) = none := by
            simp only [chainStep, hany', hfx']; rfl
          rw [e, chainFold_none] at h'
          cases h'
        | some ys' =>
          have e : chainStep D last f (some a) x = some (extendRunsP D last a ys) := by
            simp only [chainStep, hany, hfx]; rfl
          have e' : chainStep D (last ^^ b) f' (some a') (nmap b t x) =
              some (extendRunsP D (last ^^ b) a' ys') := by
            simp only [chainStep, hany', hfx']; rfl
          rw [e] at h
          rw [e'] at h'
          exact chainFold_sub last f f' rest _ _ rs rs' hrest
            (sub_extend hL ha (hf x (List.mem_cons_self ..) ys ys' hfx hfx')) h h'
    | false =>
      have e' : chainStep D (last ^^ b) f' (some a') (nmap b t x) = some a' := by
        simp only [chainStep, hany']; rfl
      rw [e'] at h'
      cases hany : a.any (·.2) with
      | false =>
        have e : chainStep D last f (some a) x = some a := by simp only [chainStep, hany]; rfl
        rw [e] at h
        exact chainFold_sub last f f' rest _ _ rs rs' hrest ha h h'
      | true =>
        cases hfx : f x with
        | none =>
          have e : chainStep D last f (some a) x = none := by
            simp only [chainStep, hany, hfx]; rfl
          rw [e, chainFold_none] at h
          cases h
        | some ys =>
          have e : chainStep D last f (some a) x = some (extendRunsP D last a ys) := by
            simp only [chainStep, hany, hfx]; rfl
          rw [e] at h
          refine chainFold_sub last f f' rest _ _ rs rs' hrest (fun r' hr' => ?_) h h'
          obtain ⟨r, hr, rfl⟩ := ha r' hr'
          have hw : r.2 = false := by
            cases hw : r.2 with
            | false => rfl
            | true =>
              have : a'.any (·.2) = true := List.any_eq_true.2 ⟨_, hr', hw⟩
              rw [hany'] at this
              cases this
          exact ⟨r, mem_extendRunsP.2 (.inl ⟨hr, hw⟩), rfl⟩

/-- **Every run at the end of the image of a node is the image of a run at
the end of the node.** -/
theorem runsP_nmap (last : Bool) : ∀ (d : Nat) (seen : List Rel) (n : Rel)
    (rs rs' : List (Run R)), (∀ m ∈ seen, Normal m) → Normal n → n.FO →
    runsP D P last d seen n = some rs →
    runsP D P' (last ^^ b) d (seen.map (nmap b t)) (nmap b t n) = some rs' → Sub b rs rs' := by
  intro d
  induction d with
  | zero => intro seen n rs rs' _ _ _ h; cases h
  | succ d ih =>
    intro seen n rs rs' hseen hn hfo h h'
    obtain ⟨mc, mm, mu⟩ := members_nmap hn b t
    have hfom : ∀ x ∈ n.view.members, x.FO := fun x hx => hfo.view_members hx
    cases hv : n.view with
    | span s =>
      obtain rfl : n = .span s := by
        cases n with
        | span s' =>
          obtain rfl : s' = s := by simpa [RelOf.view] using hv
          rfl
        | conv x => cases x <;> simp [RelOf.view] at hv
        | _ => simp [RelOf.view] at hv
      have hs : s.firstOrder = true := hfo s (by simp [RelOf.spans])
      have hv' := Normal.view_span hv b t
      simp only [runsP, hv, hv', Option.some.injEq] at h h'
      subst h h'
      have e := spanBoth_smap hL hs (isBound_none D) (isBound_none D) b
      simp only [ite_self] at e
      rw [nmap_span]
      intro r' hr'
      cases hsb : spanBoth D none s none with
      | none =>
        rw [hsb] at e
        simp only [leafRuns, e, Option.map_none] at hr'
        cases hr'
      | some c =>
        rw [hsb] at e
        simp only [leafRuns, e, Option.map_some, List.mem_singleton] at hr'
        exact ⟨(some c, true), by simp [leafRuns, hsb], hr'⟩
    | meet xs =>
      obtain ⟨-, xs', hv', -⟩ := mm xs hv
      simp only [runsP, hv, hv', Option.some.injEq] at h h'
      subst h h'
      intro r' hr'
      exact ⟨(none, false), by simp, by simpa [rmap] using hr'⟩
    | union xs =>
      obtain ⟨hnorm, xs', hv', hmem⟩ := mu xs hv
      simp only [runsP, hv, hv'] at h h'
      obtain ⟨h1, h2⟩ := unionFold _ xs [] rs h
      obtain ⟨-, h2'⟩ := unionFold _ xs' [] rs' h'
      intro r' hr'
      rcases (h2' r').1 hr' with hr' | ⟨z, hz, r1', hr1', hr'⟩
      · cases hr'
      obtain ⟨x, hx, rfl⟩ := (hmem z).1 hz
      obtain ⟨r1, hr1⟩ := h1 x hx
      obtain ⟨r, hr, e⟩ := ih seen x r1 r1' hseen (hnorm x hx)
        (hfom x (by rw [hv]; exact hx)) hr1 hr1' r' hr'
      exact ⟨r, (h2 r).2 (.inr ⟨x, hx, r1, hr1, hr⟩), e⟩
    | call nm fl =>
      have hv' := Normal.view_call hv b t
      have hany : (seen.map (nmap b t)).any (fun m => decide (m = nmap b t n)) =
          seen.any (fun m => decide (m = n)) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
        constructor
        · rintro ⟨m', hm', e⟩
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm'
          exact ⟨m, hm, decide_eq_true ((hseen m hm).nmap_inj hn (of_decide_eq_true e))⟩
        · rintro ⟨m, hm, e⟩
          exact ⟨_, List.mem_map_of_mem hm, decide_eq_true (by rw [of_decide_eq_true e])⟩
      simp only [runsP, hv, hv', hany, hbody n hn] at h h'
      cases hs : seen.any (fun m => decide (m = n)) with
      | true =>
        simp only [hs, ↓reduceIte, Option.some.injEq] at h h'
        subst h h'
        intro r' hr'
        exact ⟨(none, false), by simp, by simpa [rmap] using hr'⟩
      | false =>
        simp only [hs, Bool.false_eq_true, ↓reduceIte] at h h'
        cases hb : Charged.bodyOf P n with
        | none =>
          simp only [hb, Option.map_none, Option.some.injEq] at h h'
          subst h'
          intro r' hr'
          cases hr'
        | some bd =>
          simp only [hb, Option.map_some] at h h'
          exact ih (n :: seen) bd rs rs'
            (fun m hm => by
              rcases List.mem_cons.1 hm with rfl | hm
              · exact hn
              · exact hseen m hm)
            (bodyOf_normal hb) (bodyOf_fo hP hb) h (by simpa using h')
    | chain xs =>
      obtain ⟨hnorm, hv'⟩ := mc xs hv
      have hlist : (if (last ^^ b) = true
          then ((if b = true then xs.reverse else xs).map (nmap b t)).reverse
          else (if b = true then xs.reverse else xs).map (nmap b t)) =
          (if last = true then xs.reverse else xs).map (nmap b t) := by
        cases b <;> cases last <;> simp [List.map_reverse]
      simp only [runsP, hv, hv', hlist] at h h'
      have hin : ∀ x ∈ (if last = true then xs.reverse else xs), x ∈ xs := by
        intro x hx
        cases last
        · exact hx
        · exact List.mem_reverse.1 hx
      cases hl : (if last = true then xs.reverse else xs) with
      | nil =>
        simp only [hl, List.map_nil, Option.some.injEq] at h h'
        subst h h'
        intro r' hr'
        exact ⟨(none, false), by simp, by simpa [rmap] using hr'⟩
      | cons e rest =>
        rw [hl] at hin
        simp only [hl, List.map_cons] at h h'
        have sub : ∀ x ∈ e :: rest, ∀ r r', runsP D P last d seen x = some r →
            runsP D P' (last ^^ b) d (seen.map (nmap b t)) (nmap b t x) = some r' → Sub b r r' :=
          fun x hx r r' hr hr' => ih seen x r r' hseen (hnorm x (hin x hx))
            (hfom x (by rw [hv]; exact hin x hx)) hr hr'
        cases he : runsP D P last d seen e with
        | none =>
          rw [he, chainFold_none] at h
          cases h
        | some r0 =>
          cases he' : runsP D P' (last ^^ b) d (seen.map (nmap b t)) (nmap b t e) with
          | none =>
            rw [he', chainFold_none] at h'
            cases h'
          | some r0' =>
            rw [he] at h
            rw [he'] at h'
            exact chainFold_sub hL last _ _ rest r0 r0' rs rs'
              (fun x hx => sub x (List.mem_cons_of_mem _ hx))
              (sub e (List.mem_cons_self ..) r0 r0' he he') h h'

/-- **The reading of the image of a node, at the other end when the converse
is taken, is offered when the reading of the node is, over interfaces of the
node.** -/
theorem readEdgeP_nmap {n : Rel} (hn : Normal n) (hfo : n.FO) {last : Bool} {d : Nat}
    {ps : List R} {e' : Option (List R)} (h : readEdgeP D P last d n = some (some ps))
    (h' : readEdgeP D P' (last ^^ b) d (nmap b t n) = some e') :
    ∃ ps', e' = some ps' ∧ ∀ p ∈ ps', p ∈ ps := by
  unfold readEdgeP at h h'
  cases hc : hasCallP d n with
  | none => rw [hc] at h; cases h
  | some c =>
    cases hc' : hasCallP d (nmap b t n) with
    | none => rw [hc'] at h'; cases h'
    | some c' =>
      obtain rfl := hasCallP_nmap b t d n c c' hn hc hc'
      rw [hc] at h
      rw [hc'] at h'
      cases c' with
      | false => cases h
      | true =>
        simp only at h h'
        cases hr : runsP D P last d [] n with
        | none => rw [hr] at h; cases h
        | some rs =>
          cases hr' : runsP D P' (last ^^ b) d [] (nmap b t n) with
          | none => rw [hr'] at h'; cases h'
          | some rs' =>
            rw [hr] at h
            rw [hr'] at h'
            simp only [Option.some.injEq] at h h'
            subst h'
            have hsub := runsP_nmap hL hbody hP last d [] n rs rs' (fun _ hm => by cases hm) hn
              hfo hr hr'
            obtain ⟨h1, -, -⟩ := boundFold last rs [] ps h
            have hshow : ∀ r' ∈ rs', ∃ x p, r'.1 = some x ∧ bnd D (last ^^ b) x = some p ∧
                p ∈ ps := by
              intro r' hr'
              obtain ⟨r, hr, rfl⟩ := hsub r' hr'
              obtain ⟨x, p, hx, hb, hp⟩ := h1 r hr
              exact ⟨smap b x, p, by simp [rmap, hx], by rw [bnd_smap hL]; exact hb, hp⟩
            obtain ⟨ps', hps'⟩ := boundFold_some (last ^^ b) rs' []
              fun r' hr' => by
                obtain ⟨x, p, hx, hb, -⟩ := hshow r' hr'
                exact ⟨x, p, hx, hb⟩
            refine ⟨ps', hps', fun p hp => ?_⟩
            obtain ⟨-, -, h3⟩ := boundFold (last ^^ b) rs' [] ps' hps'
            rcases h3 p hp with hp0 | ⟨r', hr', x, hx, hb⟩
            · cases hp0
            · obtain ⟨x2, p2, hx2, hb2, hp2⟩ := hshow r' hr'
              rw [hx] at hx2
              cases hx2
              rw [hb] at hb2
              cases hb2
              exact hp2

/-- **An edge that is read on a node is read on its image**, at the other
end when the converse is taken, with no interface the node does not show. -/
theorem reads_nmap {n : Rel} (hn : Normal n) (hfo : n.FO) {last : Bool} {ps : List R}
    (h : Reads D P n last (some ps)) :
    ∃ ps', Reads D P' (nmap b t n) (last ^^ b) (some ps') ∧ ∀ p ∈ ps', p ∈ ps := by
  obtain ⟨K, hK, d, h⟩ := h
  have h1 := readEdge_mono (K₂ := K) (hK₂ := hK) last d n _ h
    (max d (readNeed P' (nmap b t n))) (le_max_left _ _)
  have h2 := readEdge_some (K := K) (hK := hK) (P := P') (last ^^ b)
    (max d (readNeed P' (nmap b t n))) (nmap b t n) (le_max_right _ _)
  cases h3 : (readEdge (K := DerivationKernel.over D K hK P') (last ^^ b)
      (max d (readNeed P' (nmap b t n))) (nmap b t n)).val with
  | none => exact absurd h3 h2
  | some e' =>
    rw [readEdge_val] at h1 h3
    obtain ⟨ps', rfl, hsub⟩ := readEdgeP_nmap hL hbody hP hn hfo h1 h3
    exact ⟨ps', ⟨K, hK, _, by rw [readEdge_val]; exact h3⟩, hsub⟩

end runs

end Symmetric

end RwLog
