/-
# A machine run on one orientation of its input

`CostedRuntime.oriented` (`Trusted/Cost.lean`) runs a machine on one chosen
member of the four inputs an input stands with: itself, its converse, its
mirror image, and the converse of its mirror image. This file proves what
that gives, for any machine.

* The choice made from the converse of a query, and from the mirror image of
  an input, is the choice made from the input, the other way round
  (`orient_conv`, `orient_dual`); or it is the same choice, and then the node
  chosen is its own converse.
* The program and the node chosen from a well-formed input are first-order
  (`progFO_orient`, `fo_orient_root`).
* On an input and on its mirror image it pays the same ticks, step for step
  (`CostedRuntime.oriented_paid_dual`), with nothing asked of the machine.
-/
import RwLog.Rungs.Framework.Direction
import RwLog.Kernel.NormalFormStable
import RwLog.Kernel.NormalFormCorrect
import RwLog.Kernel.Order
import RwLog.Kernel.NormalFormSpans

namespace RwLog

/-! ## The least node -/

theorem leastRel_mem : ∀ (m : Rel) (xs : List Rel), leastRel m xs ∈ m :: xs
  | m, [] => List.mem_cons_self
  | m, x :: xs => by
    rw [leastRel]
    have h := leastRel_mem (if relCmp x m = .lt then x else m) xs
    rcases List.mem_cons.1 h with h | h
    · rw [h]; split
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem relCmp_refl (a : Rel) : relCmp a a = .eq := by
  have h := relCmp_swap a a
  cases hc : relCmp a a <;> rw [hc] at h <;> simp_all [Ordering.swap]

theorem relCmp_isLE_of_not_lt {x m : Rel} (h : relCmp x m ≠ .lt) : (relCmp m x).isLE := by
  rw [relCmp_swap m x]
  cases hc : relCmp x m <;> simp_all [Ordering.swap, Ordering.isLE]

theorem relCmp_isLE_of_lt {x m : Rel} (h : relCmp x m = .lt) : (relCmp x m).isLE := by
  rw [h]; rfl

theorem leastRel_le : ∀ (m : Rel) (xs : List Rel), ∀ x ∈ m :: xs, (relCmp (leastRel m xs) x).isLE
  | m, [], x, hx => by
    rw [List.mem_singleton.1 hx, leastRel, relCmp_refl]; rfl
  | m, y :: ys, x, hx => by
    rw [leastRel]
    have ih := leastRel_le (if relCmp y m = .lt then y else m) ys
    have hm' : (relCmp (leastRel (if relCmp y m = .lt then y else m) ys)
        (if relCmp y m = .lt then y else m)).isLE := ih _ List.mem_cons_self
    rcases List.mem_cons.1 hx with rfl | hx
    · refine relCmp_trans hm' ?_
      split
      · next h => exact relCmp_isLE_of_lt h
      · rw [relCmp_refl]; rfl
    rcases List.mem_cons.1 hx with rfl | hx
    · refine relCmp_trans hm' ?_
      split
      · rw [relCmp_refl]; rfl
      · next h => exact relCmp_isLE_of_not_lt h
    · exact ih _ (List.mem_cons_of_mem _ hx)

theorem relCmp_antisymm {a b : Rel} (h₁ : (relCmp a b).isLE) (h₂ : (relCmp b a).isLE) : a = b := by
  rw [relCmp_swap b a] at h₂
  cases hc : relCmp a b <;> rw [hc] at h₁ h₂ <;> simp_all [Ordering.swap, Ordering.isLE]

/-- The least node of a list depends on its members only. -/
theorem leastRel_congr {m m' : Rel} {xs xs' : List Rel}
    (h : ∀ x, x ∈ m :: xs ↔ x ∈ m' :: xs') : leastRel m xs = leastRel m' xs' :=
  relCmp_antisymm (leastRel_le m xs _ ((h _).2 (leastRel_mem m' xs')))
    (leastRel_le m' xs' _ ((h _).1 (leastRel_mem m xs)))

/-! ## The choice, from the other side -/

/-- A choice the other way round: the same program and node with the answers
swapped the other way, or the same choice of a node that is its own
converse. -/
def Oriented.Mirrors (o o' : Oriented) : Prop :=
  o'.P = o.P ∧ o'.root = o.root ∧
    (o'.swap = !o.swap ∨ (o'.swap = o.swap ∧ o.root.normConv = o.root))

theorem normConv_union_self {m : Rel} (hm : Normal m) :
    ((RelOf.or m m.normConv).norm).normConv = (RelOf.or m m.normConv).norm := by
  rw [normConv_norm]
  show normB true (.or m m.normConv) = normB false (.or m m.normConv)
  rw [normB_or_comm false]
  have h1 : normB true m.normConv = normB false m := by
    show m.normConv.normConv = normB false m
    rw [hm.normConv_normConv, hm.normB_false]
  have h2 : normB true m = normB false m.normConv := by
    show m.normConv = m.normConv.norm
    rw [norm_normConv]
  rw [normB, normB, h1, h2]

/-- The candidates the other way round give the choice the other way
round. -/
theorem pick_mirrors (Pn : Program) {f f' : Rel × Bool} {r r' : List (Rel × Bool)}
    (hN : ∀ x ∈ f :: r, Normal x.1)
    (h : ∀ x b, (x, b) ∈ f' :: r' ↔ (x, !b) ∈ f :: r) :
    (pick Pn f r).Mirrors (pick Pn f' r') := by
  have hroots : ∀ x, x ∈ f'.1 :: r'.map Prod.fst ↔ x ∈ f.1 :: r.map Prod.fst := by
    intro x
    have e : ∀ (g : Rel × Bool) (l : List (Rel × Bool)),
        g.1 :: l.map Prod.fst = (g :: l).map Prod.fst := fun _ _ => rfl
    rw [e, e, List.mem_map, List.mem_map]
    constructor
    · rintro ⟨⟨y, b⟩, hy, rfl⟩; exact ⟨(y, !b), (h y b).1 hy, rfl⟩
    · rintro ⟨⟨y, b⟩, hy, rfl⟩
      exact ⟨(y, !b), (h y (!b)).2 (by rwa [Bool.not_not]), rfl⟩
  have hm : leastRel f'.1 (r'.map Prod.fst) = leastRel f.1 (r.map Prod.fst) := leastRel_congr hroots
  set m := leastRel f.1 (r.map Prod.fst) with hmdef
  have hmN : Normal m := by
    have := leastRel_mem f.1 (r.map Prod.fst)
    have e : f.1 :: r.map Prod.fst = (f :: r).map Prod.fst := rfl
    rw [e, List.mem_map] at this
    obtain ⟨y, hy, hy'⟩ := this
    rw [hmdef, ← hy']; exact hN y hy
  have hall : ∀ (l : List (Rel × Bool)) (v : Bool),
      ((l.filter fun x => x.1 = m).map Prod.snd).all (· = v) = true ↔
        ∀ x b, (x, b) ∈ l → x = m → b = v := by
    intro l v
    simp only [List.all_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro H x b hx hxm; exact H b ⟨(x, b), ⟨hx, hxm⟩, rfl⟩
    · rintro H b ⟨⟨x, b'⟩, ⟨hx, hxm⟩, rfl⟩; exact H x b' hx hxm
  have hF : ((((f' :: r').filter fun x => x.1 = m).map Prod.snd).all (· = false) = true) ↔
      ((((f :: r).filter fun x => x.1 = m).map Prod.snd).all (· = true) = true) := by
    rw [hall, hall]
    constructor
    · intro H x b hx hxm
      have := H x (!b) ((h x (!b)).2 (by rwa [Bool.not_not])) hxm
      simpa using this
    · intro H x b hx hxm
      have := H x (!b) ((h x b).1 hx) hxm
      simpa using this
  have hT : ((((f' :: r').filter fun x => x.1 = m).map Prod.snd).all (· = true) = true) ↔
      ((((f :: r).filter fun x => x.1 = m).map Prod.snd).all (· = false) = true) := by
    rw [hall, hall]
    constructor
    · intro H x b hx hxm
      have := H x (!b) ((h x (!b)).2 (by rwa [Bool.not_not])) hxm
      simpa using this
    · intro H x b hx hxm
      have := H x (!b) ((h x b).1 hx) hxm
      simpa using this
  -- the least node is a candidate, so it is not a candidate neither way
  have hex : ∃ b, (m, b) ∈ f :: r := by
    have := leastRel_mem f.1 (r.map Prod.fst)
    have e : f.1 :: r.map Prod.fst = (f :: r).map Prod.fst := rfl
    rw [e, List.mem_map] at this
    obtain ⟨⟨y, b⟩, hy, hy'⟩ := this
    exact ⟨b, by rw [hmdef, ← hy']; exact hy⟩
  have hnot : ¬ (((((f :: r).filter fun x => x.1 = m).map Prod.snd).all (· = false) = true) ∧
      ((((f :: r).filter fun x => x.1 = m).map Prod.snd).all (· = true) = true)) := by
    rw [hall, hall]
    rintro ⟨H1, H2⟩
    obtain ⟨b, hb⟩ := hex
    have := (H1 m b hb rfl).symm.trans (H2 m b hb rfl)
    cases this
  unfold pick
  simp only [hm, ← hmdef]
  by_cases c1 : (((f :: r).filter fun x => x.1 = m).map Prod.snd).all (· = false) = true
  · have c2 : ¬ (((f :: r).filter fun x => x.1 = m).map Prod.snd).all (· = true) = true :=
      fun c2 => hnot ⟨c1, c2⟩
    rw [ite_eq_left c1, ite_eq_right (fun c => c2 (hF.1 c)), ite_eq_left (hT.2 c1)]
    exact ⟨rfl, rfl, .inl rfl⟩
  · by_cases c2 : (((f :: r).filter fun x => x.1 = m).map Prod.snd).all (· = true) = true
    · rw [ite_eq_right c1, ite_eq_left c2, ite_eq_left (hF.2 c2)]
      exact ⟨rfl, rfl, .inl rfl⟩
    · rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right (fun c => c2 (hF.1 c)), ite_eq_right (fun c => c1 (hT.1 c))]
      exact ⟨rfl, rfl, .inr ⟨rfl, normConv_union_self hmN⟩⟩

/-- The mirrored program has the sorts of the program. -/
theorem pick_P (Pn : Program) (f : Rel × Bool) (r : List (Rel × Bool)) : (pick Pn f r).P = Pn := by
  unfold pick
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem orient_sorts (P : Program) (q : Rel) : (orient P q).P.sorts = P.sorts := by
  unfold orient
  split <;> rw [pick_P] <;> rfl

/-- The choice made from the converse of the query is the choice made from
the query, the other way round. -/
theorem orient_conv (P : Program) (q : Rel) : (orient P q).Mirrors (orient P (.conv q)) := by
  unfold orient
  have e1 : (RelOf.conv (.conv q)).norm = q.norm := norm_conv_conv q
  have e2 : (RelOf.conv (RelOf.conv q).dual).norm = q.dual.norm := norm_conv_conv q.dual
  have e3 : (RelOf.conv q).dual = .conv q.dual := rfl
  split
  · refine pick_mirrors _ (fun x hx => ?_) (fun x b => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact normal_norm _
    · rw [e1]; cases b <;> simp [or_comm]
  · refine pick_mirrors _ (fun x hx => ?_) (fun x b => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact normal_norm _
    · rw [e2, e3]; cases b <;> simp [or_comm]
  · refine pick_mirrors _ (fun x hx => ?_) (fun x b => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact normal_norm _
    · rw [e1, e2, e3]; cases b <;> simp [or_comm]

theorem normed_dual_of_eq {P : Program}
    (h : (P.defs.map fun d => d.2.norm) = (P.dual.defs.map fun d => d.2.norm)) :
    P.dual.normed = P.normed := by
  cases P with
  | mk defs sorts =>
    simp only [ProgramOf.dual, ProgramOf.normed, List.map_map] at h ⊢
    congr 1
    refine List.map_congr_left fun d hd => ?_
    have := List.map_inj_left.1 h d hd
    simp only [Function.comp] at this ⊢
    rw [this]

/-- The choice made from the mirror image of an input is the choice made from
the input, the other way round. -/
theorem orient_dual (P : Program) (q : Rel) : (orient P q).Mirrors (orient P.dual q.dual) := by
  unfold orient
  rw [ProgramOf.dual_dual, RelOf.dual_dual,
    listCmp_swap (f := relCmp) (P.dual.defs.map fun d => d.2.norm)]
  cases hc : listCmp relCmp (P.defs.map fun d => d.2.norm) (P.dual.defs.map fun d => d.2.norm)
  · refine pick_mirrors _ (fun x hx => ?_) (fun x b => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact normal_norm _
    · cases b <;> simp
  · rw [normed_dual_of_eq (listCmp_eq (f := relCmp) hc)]
    refine pick_mirrors _ (fun x hx => ?_) (fun x b => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact normal_norm _
    · cases b <;> simp [or_comm]
  · refine pick_mirrors _ (fun x hx => ?_) (fun x b => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact normal_norm _
    · cases b <;> simp

/-! ## The run -/

/-- What a step shows, the other way round or as it is. -/
def Shown.shownAs {A : Type} [Answer A] (b : Bool) (x : Shown A) : Shown A :=
  if b then x.swap else x

theorem map_shownAs_false {A : Type} [Answer A] (t : List (Shown A)) :
    t.map (Shown.shownAs false) = t :=
  (List.map_congr_left fun _ _ => rfl).trans (List.map_id t)

theorem map_shownAs_true {A : Type} [Answer A] (t : List (Shown A)) :
    t.map (Shown.shownAs true) = t.map Shown.swap := rfl

namespace CostedRuntime

variable (C : CostedRuntime)

theorem oriented_step_val (b : Bool) (s : C.State) :
    (C.oriented.step (b, s)).val = (C.step s).val.shownAs b := rfl

theorem oriented_step_ticks (b : Bool) (s : C.State) :
    (C.oriented.step (b, s)).ticks = (C.step s).ticks := by
  show ((C.step s) >>= fun r => pure (r.shownAs b)).ticks = _
  simp

theorem oriented_start (P : Program) (q : Rel) :
    C.oriented.start P q = ((orient P q).swap, C.start (orient P q).P (orient P q).root) := rfl

theorem oriented_init_ticks (P : Program) (q : Rel) :
    (C.oriented.init P q).ticks =
      4 * (P.size + q.size + 1) ^ 2 + (C.init (orient P q).P (orient P q).root).ticks := by
  show ((Charged.orient P q) >>= fun o => (C.init o.P o.root) >>= fun s => pure (o.swap, s)).ticks = _
  simp [Charged.orient]

/-- What a machine run on one orientation shows is what the machine shows on
the chosen input, the other way round if the choice says so. -/
theorem oriented_trace (b : Bool) : ∀ (n : Nat) (s : C.State),
    C.oriented.runtime.trace (b, s) n = (C.runtime.trace s n).map (Shown.shownAs b)
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done fin =>
      have hs' : C.oriented.runtime.step (b, s) =
          .done (if b then fin.map Answer.swap else fin) := by
        show (C.oriented.step (b, s)).val = _; rw [oriented_step_val, hs]; rfl
      rw [C.oriented.runtime.trace_succ_done hs',
        C.runtime.trace_succ_done (show C.runtime.step s = .done fin from hs)]
      cases b <;> rfl
    | emit as s' =>
      have hs' : C.oriented.runtime.step (b, s) =
          .emit (if b then as.map Answer.swap else as) (b, s') := by
        show (C.oriented.step (b, s)).val = _; rw [oriented_step_val, hs]; rfl
      rw [C.oriented.runtime.trace_succ_emit hs',
        C.runtime.trace_succ_emit (show C.runtime.step s = .emit as s' from hs), List.map_cons,
        oriented_trace b n s']
      cases b <;> rfl

/-- A machine run on one orientation spends what the machine spends on the
chosen input. -/
theorem oriented_spent (b : Bool) : ∀ (n : Nat) (s : C.State),
    C.oriented.spent (b, s) n = C.spent s n
  | 0, _ => rfl
  | n + 1, s => by
    cases hs : (C.step s).val with
    | done fin =>
      have hs' : (C.oriented.step (b, s)).val = .done (if b then fin.map Answer.swap else fin) := by
        rw [oriented_step_val, hs]; rfl
      rw [C.oriented.spent_succ_done hs', C.spent_succ_done hs, oriented_step_ticks]
    | emit as s' =>
      have hs' : (C.oriented.step (b, s)).val =
          .emit (if b then as.map Answer.swap else as) (b, s') := by
        rw [oriented_step_val, hs]; rfl
      rw [C.oriented.spent_succ_emit hs', C.spent_succ_emit hs, oriented_step_ticks,
        oriented_spent b n s']

/-- On first-order input with a root that is its own converse the machine
shows, at every step, a
set of answers that is its own converse. This is what the choice of one
orientation leaves to the machine. -/
def SelfConverse : Prop :=
  ∀ (P : Program) (root : Rel), P.sorts.WellFormed → ProgFO P → Normal root → root.FO →
    root.normConv = root →
    ∀ n, TraceEquiv P.sorts.interp (C.runtime.trace (C.start P root) n)
      ((C.runtime.trace (C.start P root) n).map Shown.swap)

variable {C}

theorem traceEquiv_swap_swap {A : Type} [Answer A] (M : Interp) (t : List (Shown A)) :
    TraceEquiv M t ((t.map Shown.swap).map Shown.swap) := by
  rw [List.map_map]
  refine List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun x _ => ?_)
  cases x with
  | answers xs => exact (StepEquiv.swap_swap M xs).symm
  | final xs => exact (StepEquiv.swap_swap M xs).symm

/-- Two choices, one the other way round from the other, show runs that are
each the other swapped. -/
theorem trace_of_mirrors (hS : C.SelfConverse) {P : Program} (hP : P.sorts.WellFormed)
    {o o' : Oriented} (h : o.Mirrors o') (ho : o.P.sorts = P.sorts) (hfP : ProgFO o.P)
    (hN : Normal o.root) (hfo : o.root.FO) (n : Nat) :
    TraceEquiv P.sorts.interp (C.oriented.runtime.trace (o'.swap, C.start o'.P o'.root) n)
      ((C.oriented.runtime.trace (o.swap, C.start o.P o.root) n).map Shown.swap) := by
  obtain ⟨hPe, hre, hsw⟩ := h
  rw [oriented_trace, oriented_trace, hPe, hre]
  rcases hsw with hsw | ⟨hsw, hself⟩
  · rw [hsw]
    cases o.swap
    · rw [Bool.not_false, map_shownAs_true, map_shownAs_false]
      exact TraceEquiv.refl _
    · rw [Bool.not_true, map_shownAs_true, map_shownAs_false]
      exact traceEquiv_swap_swap _ _
  · rw [hsw]
    have hT := hS o.P o.root (ho ▸ hP) hfP hN hfo hself n
    rw [ho] at hT
    cases o.swap
    · rw [map_shownAs_false]
      exact hT
    · rw [map_shownAs_true]
      exact hT.symm.trans (traceEquiv_swap_swap _ _)

end CostedRuntime

theorem normal_pick_root (Pn : Program) {f : Rel × Bool} {r : List (Rel × Bool)}
    (hN : ∀ x ∈ f :: r, Normal x.1) : Normal (pick Pn f r).root := by
  have hm : Normal (leastRel f.1 (r.map Prod.fst)) := by
    have := leastRel_mem f.1 (r.map Prod.fst)
    have e : f.1 :: r.map Prod.fst = (f :: r).map Prod.fst := rfl
    rw [e, List.mem_map] at this
    obtain ⟨y, hy, hy'⟩ := this
    rw [← hy']; exact hN y hy
  unfold pick
  dsimp only
  split
  · exact hm
  · split
    · exact hm
    · exact normal_norm _

theorem normal_orient_root (P : Program) (q : Rel) : Normal (orient P q).root := by
  unfold orient
  split <;> refine normal_pick_root _ fun x hx => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact normal_norm _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact normal_norm _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact normal_norm _

/-! ## The choice is first-order -/

theorem ProgFO.normed {P : Program} (h : ProgFO P) : ProgFO P.normed := fun s hs => by
  obtain ⟨d, hd, hsd⟩ := List.mem_flatMap.1 hs
  simp only [ProgramOf.normed, List.mem_map] at hd
  obtain ⟨d0, hd0, rfl⟩ := hd
  exact RelOf.FO.norm (fun s' hs' => h s' (List.mem_flatMap.2 ⟨d0, hd0, hs'⟩)) s hsd

theorem RelOf.FO.conv {e : Rel} (h : e.FO) : (RelOf.conv e).FO := fun s hs => h s hs

theorem fo_pick_root (Pn : Program) {f : Rel × Bool} {r : List (Rel × Bool)}
    (hF : ∀ x ∈ f :: r, x.1.FO) : (pick Pn f r).root.FO := by
  have hm : (leastRel f.1 (r.map Prod.fst)).FO := by
    have := leastRel_mem f.1 (r.map Prod.fst)
    have e : f.1 :: r.map Prod.fst = (f :: r).map Prod.fst := rfl
    rw [e, List.mem_map] at this
    obtain ⟨y, hy, hy'⟩ := this
    rw [← hy']; exact hF y hy
  unfold pick
  dsimp only
  split
  · exact hm
  · split
    · exact hm
    · refine RelOf.FO.norm fun s hs => ?_
      rcases List.mem_append.1 hs with hs | hs
      · exact hm s hs
      · exact hm.normConv s hs

/-- The program chosen from a well-formed input is first-order. -/
theorem progFO_orient {P : Program} {q : Rel} (wf : P.WellFormed q) : ProgFO (orient P q).P := by
  unfold orient
  split <;> rw [pick_P]
  · exact wf.progFO.normed
  · exact wf.dual.progFO.normed
  · exact wf.progFO.normed

/-- The root chosen from a well-formed input is first-order. -/
theorem fo_orient_root {P : Program} {q : Rel} (wf : P.WellFormed q) : (orient P q).root.FO := by
  unfold orient
  split <;> refine fo_pick_root _ fun x hx => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact wf.fo.norm
    · exact wf.fo.conv.norm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact wf.dual.fo.norm
    · exact wf.dual.fo.conv.norm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact wf.fo.norm
    · exact wf.fo.conv.norm
    · exact wf.dual.fo.norm
    · exact wf.dual.fo.conv.norm

namespace CostedRuntime

variable {C : CostedRuntime}

/-- **The mirror image costs the same.** Run on one orientation, any machine
pays on the mirrored query in the mirrored program exactly what it pays on
the query, at every step. Nothing is asked of the machine. -/
theorem oriented_paid_dual (C : CostedRuntime) (P : Program) (q : Rel) (n : Nat) :
    C.oriented.paid P.dual q.dual n = C.oriented.paid P q n := by
  obtain ⟨hPe, hre, -⟩ := orient_dual P q
  unfold CostedRuntime.paid
  rw [oriented_init_ticks, oriented_init_ticks, oriented_start, oriented_start, oriented_spent,
    oriented_spent, hPe, hre, ProgramOf.size_dual, RelOf.size_dual]

end CostedRuntime

end RwLog
