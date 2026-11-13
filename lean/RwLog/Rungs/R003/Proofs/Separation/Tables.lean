/-
# The separating family: tables, lookups, fresh answers

The run for `sepFam k` has the root table, whose goal is `cRel k`, and a few
tables created by it: shorter members of the family and single spans. Before
the root completes none of the others has an answer or is complete, so every
lookup made by a strategy comes back empty, and what a round costs beyond the
races is the lookups, which are linear in `k`, and the comparison of the
answers the races return, which are copies of the two spans.
-/
import RwLog.Rungs.R003.Proofs.Separation.Race
import RwLog.Rungs.Framework.CostSpec
import RwLog.Rungs.Tabled.Exact
import RwLog.Rungs.R002.Proofs.Separation.Completion

namespace RwLog

namespace R003

namespace Sep

open Cost R001

/-! ## The goals of the run -/

/-- A goal a table of the run asks for: a shorter member of the family, or
one of the two spans. -/
def Sub (k : Nat) (g : Goal) : Prop := (∃ j, j < k ∧ g = gC j) ∨ g = gS xz ∨ g = gS zz

/-- A goal of the run: the root's, or one that is asked for. -/
def Slot (k : Nat) (g : Goal) : Prop := g = gC k ∨ Sub k g

/-- The size of the largest table key of the run. -/
def keyBound (k : Nat) : Nat := 8 * k + 7

theorem goalSize_gC (j : Nat) : goalSize (gC j) = 8 * j + 7 := by simp [goalSize, size_cRel]

theorem goalSize_gS {s : Span} (hs : Good s) : goalSize (gS s) = 3 := by
  simp [goalSize, Rel.size, size_good hs]

theorem goalSize_sub {k : Nat} {g : Goal} (h : Sub k g) : goalSize g ≤ keyBound k := by
  unfold keyBound
  rcases h with ⟨j, hj, rfl⟩ | rfl | rfl
  · rw [goalSize_gC]; omega
  · rw [goalSize_gS good_xz]; omega
  · rw [goalSize_gS good_zz]; omega

theorem goalSize_slot {k : Nat} {g : Goal} (h : Slot k g) : goalSize g ≤ keyBound k := by
  rcases h with rfl | h
  · rw [goalSize_gC]; exact le_rfl
  · exact goalSize_sub h

theorem norm_gC (j : Nat) : (gC j).norm = (false, gC j) := by
  cases j with
  | zero => simp [Goal.norm, cRel, canon_tw, Goal.stripConv]
  | succ j =>
    simp only [Goal.norm, canon_cRel]
    simp [cRel, Goal.stripConv]

theorem norm_gS (s : Span) : (gS s).norm = (false, gS s) := by
  simp [Goal.norm, canon, Goal.stripConv]

theorem norm_sub {k : Nat} {g : Goal} (h : Sub k g) : g.norm = (false, g) := by
  rcases h with ⟨j, _, rfl⟩ | rfl | rfl
  · exact norm_gC j
  · exact norm_gS _
  · exact norm_gS _

theorem cRel_inj {j k : Nat} (h : cRel j = cRel k) : j = k := by
  have := congrArg Rel.size h
  rw [size_cRel, size_cRel] at this
  omega

theorem cRel_ne_span (k : Nat) {s : Span} (hs : Good s) : cRel k ≠ .span s := by
  intro h
  have := congrArg Rel.size h
  rw [size_cRel] at this
  simp [Rel.size, size_good hs] at this

/-- No goal that is asked for has the root's table. -/
theorem same_root_sub {k : Nat} {g : Goal} (h : Sub k g) : (gC k).same g = false := by
  rcases h with ⟨j, hj, rfl⟩ | rfl | rfl
  · have : cRel k ≠ cRel j := fun e => by have := cRel_inj e; omega
    simp [Goal.same, this]
  · simp [Goal.same, cRel_ne_span k good_xz]
  · simp [Goal.same, cRel_ne_span k good_zz]

/-! ## The tables -/

/-- The tables other than the root's, before the root completes: no answers,
not complete, goals that were asked for. -/
def RestOK (k : Nat) (rest : Tables) : Prop :=
  ∀ t ∈ rest, t.answers = [] ∧ t.done = false ∧ Sub k t.goal

/-- The tables of the run: the root's, then the others. -/
abbrev tabs (k : Nat) (a0 : List Span) (rest : Tables) : Tables := ⟨gC k, a0, false⟩ :: rest

theorem slot_of_mem {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {t : Table}
    (ht : t ∈ tabs k a0 rest) : Slot k t.goal := by
  rcases List.mem_cons.1 ht with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (hr t h).2.2

theorem open_of_mem {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {t : Table}
    (ht : t ∈ tabs k a0 rest) : t.done = false := by
  rcases List.mem_cons.1 ht with rfl | h
  · rfl
  · exact (hr t h).2.1

theorem findTable_sub {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : Sub k g) {t : Table} (h : findTable (tabs k a0 rest) g = some t) :
    t.answers = [] ∧ t.done = false := by
  simp only [findTable, List.find?_cons, same_root_sub hg] at h
  have := hr t (List.mem_of_find?_eq_some h)
  exact ⟨this.1, this.2.1⟩

/-- A goal that is asked for has no answers yet. -/
theorem answersOf_sub {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : Sub k g) : answersOf (tabs k a0 rest) g = [] := by
  simp only [answersOf, norm_sub hg]
  cases h : findTable (tabs k a0 rest) g with
  | none => rfl
  | some t => simp [(findTable_sub hr hg h).1, orient]

/-- A goal that is asked for is not complete. -/
theorem doneOf_sub {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : Sub k g) : doneOf (tabs k a0 rest) g = false := by
  simp only [doneOf, norm_sub hg]
  cases h : findTable (tabs k a0 rest) g with
  | none => rfl
  | some t => simp [(findTable_sub hr hg h).2]

/-! ## What a lookup costs -/

theorem same_ticks {k : Nat} {g h : Goal} (hg : goalSize g ≤ keyBound k)
    (hh : goalSize h ≤ keyBound k) : (Tabled.same g h).ticks ≤ 2 * keyBound k := by
  show goalSize g + goalSize h ≤ _
  omega

/-- What one lookup costs at most among `n` tables: the key, and a comparison
with each table. -/
def lookBound (k n : Nat) : Nat := (2 * n + 1) * keyBound k

theorem findTable_ticks {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : goalSize g ≤ keyBound k) :
    (Tabled.findTable (tabs k a0 rest) g).ticks ≤ (tabs k a0 rest).length * (2 * keyBound k) :=
  findL_ticks_le_mul fun _ ht => same_ticks (goalSize_slot (slot_of_mem hr ht)) hg

theorem indexOf_ticks {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : goalSize g ≤ keyBound k) :
    (Tabled.indexOf (tabs k a0 rest) g).ticks ≤ (tabs k a0 rest).length * (2 * keyBound k) :=
  R002.Sep.indexFrom_ticks g _ _ 0 fun _ ht => same_ticks (goalSize_slot (slot_of_mem hr ht)) hg

theorem answersOf_costs {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : Sub k g) :
    Costs (Tabled.answersOf (tabs k a0 rest) g) [] (lookBound k (tabs k a0 rest).length) := by
  refine ⟨by rw [Tabled.answersOf_val, answersOf_sub hr hg], ?_⟩
  have h1 := findTable_ticks (a0 := a0) hr (goalSize_sub hg)
  have h2 := goalSize_sub hg
  have e : (Tabled.norm g).val.2 = g := by rw [Tabled.norm_val, norm_sub hg]
  have e' : (Tabled.norm g).ticks = goalSize g := rfl
  simp only [Tabled.answersOf, bind_ticks, pure_ticks, e, e', Nat.add_zero]
  unfold lookBound
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm]
  omega

theorem doneOf_costs {k : Nat} {a0 : List Span} {rest : Tables} (hr : RestOK k rest) {g : Goal}
    (hg : Sub k g) :
    Costs (Tabled.doneOf (tabs k a0 rest) g) false (lookBound k (tabs k a0 rest).length) := by
  refine ⟨by rw [Tabled.doneOf_val, doneOf_sub hr hg], ?_⟩
  have h1 := findTable_ticks (a0 := a0) hr (goalSize_sub hg)
  have h2 := goalSize_sub hg
  have e : (Tabled.norm g).val.2 = g := by rw [Tabled.norm_val, norm_sub hg]
  have e' : (Tabled.norm g).ticks = goalSize g := rfl
  simp only [Tabled.doneOf, bind_ticks, pure_ticks, e, e', Nat.add_zero]
  unfold lookBound
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm]
  omega

/-! ## Fresh answers among copies of the two spans -/

theorem foldl_keep_xz : ∀ l : List Span, (∀ x ∈ l, x = xz) →
    l.foldl (fun acc x => if acc.any fun y => y.covers? x then acc else acc ++ [x]) [xz] = [xz]
  | [], _ => rfl
  | x :: l, h => by
    have hx : x = xz := h x (by simp)
    subst hx
    simp only [List.foldl_cons, List.any_cons, covers_xz good_xz, Bool.true_or, ↓reduceIte]
    exact foldl_keep_xz l fun y hy => h y (by simp [hy])

/-- Of copies of the two spans with `$x -> z` among them, `$x -> z` is the
one maximal answer. -/
theorem maxima_good {cs : List Span} (hg : ∀ x ∈ cs, Good x) (hx : xz ∈ cs) : maxima cs = [xz] := by
  have htop : ∀ x ∈ cs.filter (fun x => !cs.any fun y => y.covers? x && !x.covers? y), x = xz := by
    intro x hx'
    obtain ⟨hmem, hp⟩ := List.mem_filter.1 hx'
    rcases hg x hmem with rfl | rfl
    · rfl
    · have : (cs.any fun y => y.covers? zz && !zz.covers? y) = true :=
        List.any_eq_true.2 ⟨xz, hx, by simp [covers_xz good_zz, covers_zz_xz]⟩
      simp [this] at hp
  have hin : xz ∈ cs.filter (fun x => !cs.any fun y => y.covers? x && !x.covers? y) := by
    refine List.mem_filter.2 ⟨hx, ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, not_and, Bool.not_eq_false]
    intro y hy _
    exact covers_xz (hg y hy)
  unfold maxima
  generalize cs.filter (fun x => !cs.any fun y => y.covers? x && !x.covers? y) = top at htop hin
  cases top with
  | nil => simp at hin
  | cons a top =>
    have ha : a = xz := htop a (by simp)
    subst ha
    simp only [List.foldl_cons, List.any_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact foldl_keep_xz top fun y hy => htop y (by simp [hy])

theorem fresh_nil_good {cs : List Span} (hg : ∀ x ∈ cs, Good x) (hx : xz ∈ cs) :
    fresh [] cs = [xz] := by
  have : cs.filter (fun c => !([] : List Span).any fun t => t.covers? c) = cs := by simp
  rw [fresh, this, maxima_good hg hx]

/-- Once `$x -> z` is in the table nothing is fresh. -/
theorem fresh_xz_good {cs : List Span} (hg : ∀ x ∈ cs, Good x) : fresh [xz] cs = [] := by
  have : cs.filter (fun c => !([xz] : List Span).any fun t => t.covers? c) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    simp [covers_xz (hg c hc)]
  rw [fresh, this, maxima_nil]

/-! ## What the fresh answers cost -/

theorem covers_ticks {a b : Span} (ha : Good a) (hb : Good b) : (Charged.covers a b).ticks = 4 := by
  simp [Charged.covers, size_good ha, size_good hb]

theorem fold_ticks : ∀ (top acc : List Span), (∀ x ∈ top, Good x) → (∀ x ∈ acc, Good x) →
    (foldL (fun acc x => do
      let b ← anyL (fun y => Charged.covers y x) acc
      pure (if b then acc else acc ++ [x])) acc top).ticks ≤ top.length * (4 * (acc.length + top.length))
  | [], _, _, _ => by simp [foldL]
  | x :: top, acc, ht, ha => by
    have hx : Good x := ht x (by simp)
    have h1 : (anyL (fun y => Charged.covers y x) acc).ticks ≤ acc.length * 4 :=
      anyL_ticks_le_mul fun y hy => le_of_eq (covers_ticks (ha y hy) hx)
    have hlen : ∀ b : Bool, (if b then acc else acc ++ [x]).length ≤ acc.length + 1 := by
      intro b; cases b <;> simp
    have hgood : ∀ b : Bool, ∀ y ∈ (if b then acc else acc ++ [x]), Good y := by
      intro b y hy
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact ha y hy
        · exact hx
      · exact ha y (by simpa using hy)
    have ih := fold_ticks top _ (fun y hy => ht y (by simp [hy]))
      (hgood (anyL (fun y => Charged.covers y x) acc).val)
    have hl := hlen (anyL (fun y => Charged.covers y x) acc).val
    simp only [foldL, bind_ticks, pure_ticks, pure_val, bind_val, Nat.add_zero, List.length_cons]
    have hm : top.length * (4 * ((if (anyL (fun y => Charged.covers y x) acc).val = true then acc
        else acc ++ [x]).length + top.length)) ≤ top.length * (4 * (acc.length + 1 + top.length)) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : (top.length + 1) * (4 * (acc.length + (top.length + 1))) =
        top.length * (4 * (acc.length + 1 + top.length)) + 4 * (acc.length + (top.length + 1)) := by
      ring
    omega

/-- The maximal answers of `n` copies of the two spans cost at most `12 n²`. -/
theorem maxima_ticks {xs : List Span} (hg : ∀ x ∈ xs, Good x) :
    (Tabled.maxima xs).ticks ≤ 12 * xs.length * xs.length := by
  have h1 : (filterL (fun x => do
      let b ← anyL (fun y => do
        let c ← Charged.covers y x
        if c then do
          let c' ← Charged.covers x y
          pure !c'
        else pure false) xs
      pure !b) xs).ticks ≤ xs.length * (xs.length * 8) := by
    refine filterL_ticks_le_mul fun x hx => ?_
    have : (anyL (fun y => do
        let c ← Charged.covers y x
        if c then do
          let c' ← Charged.covers x y
          pure !c'
        else pure false) xs).ticks ≤ xs.length * 8 := by
      refine anyL_ticks_le_mul fun y hy => ?_
      have a1 := covers_ticks (hg y hy) (hg x hx)
      have a2 := covers_ticks (hg x hx) (hg y hy)
      simp only [bind_ticks, ite_ticks, pure_ticks, a1, a2]
      split <;> omega
    simpa using this
  have hsub : ∀ x ∈ (filterL (fun x => do
      let b ← anyL (fun y => do
        let c ← Charged.covers y x
        if c then do
          let c' ← Charged.covers x y
          pure !c'
        else pure false) xs
      pure !b) xs).val, Good x := by
    intro x hx
    rw [filterL_val] at hx
    exact hg x (List.mem_filter.1 hx).1
  have hlen : (filterL (fun x => do
      let b ← anyL (fun y => do
        let c ← Charged.covers y x
        if c then do
          let c' ← Charged.covers x y
          pure !c'
        else pure false) xs
      pure !b) xs).val.length ≤ xs.length := by
    rw [filterL_val]; exact List.length_filter_le _ _
  have h2 := fold_ticks _ [] hsub (by simp)
  simp only [Tabled.maxima, bind_ticks]
  generalize (filterL (fun x => do
      let b ← anyL (fun y => do
        let c ← Charged.covers y x
        if c then do
          let c' ← Charged.covers x y
          pure !c'
        else pure false) xs
      pure !b) xs) = F at h1 h2 hlen ⊢
  have h3 : F.val.length * (4 * (([] : List Span).length + F.val.length)) ≤
      xs.length * (4 * xs.length) := by
    simp only [List.length_nil, Nat.zero_add]
    exact Nat.mul_le_mul hlen (Nat.mul_le_mul_left _ hlen)
  have e : 12 * xs.length * xs.length = xs.length * (xs.length * 8) + xs.length * (4 * xs.length) := by
    ring
  omega

/-- What the fresh answers of at most `n` candidates cost. -/
def freshBound (n : Nat) : Nat := 4 * n + 12 * n * n

theorem freshBound_mono {m n : Nat} (h : m ≤ n) : freshBound m ≤ freshBound n := by
  unfold freshBound
  have : 12 * m * m ≤ 12 * n * n := Nat.mul_le_mul (Nat.mul_le_mul_left _ h) h
  omega

theorem fresh_ticks {old cs : List Span} (ho : old = [] ∨ old = [xz]) (hg : ∀ x ∈ cs, Good x) :
    (Tabled.fresh old cs).ticks ≤ freshBound cs.length := by
  have h1 : (filterL (fun c => do
      let b ← anyL (fun t => Charged.covers t c) old
      pure !b) cs).ticks ≤ cs.length * 4 := by
    refine filterL_ticks_le_mul fun c hc => ?_
    have : (anyL (fun t => Charged.covers t c) old).ticks ≤ old.length * 4 := by
      refine anyL_ticks_le_mul fun t ht => le_of_eq (covers_ticks ?_ (hg c hc))
      rcases ho with rfl | rfl
      · simp at ht
      · rw [List.mem_singleton.1 ht]; exact good_xz
    have hl : old.length ≤ 1 := by rcases ho with rfl | rfl <;> simp
    have : old.length * 4 ≤ 4 := by omega
    simp only [bind_ticks, pure_ticks, Nat.add_zero]
    omega
  have hsub : ∀ x ∈ (filterL (fun c => do
      let b ← anyL (fun t => Charged.covers t c) old
      pure !b) cs).val, Good x := by
    intro x hx
    rw [filterL_val] at hx
    exact hg x (List.mem_filter.1 hx).1
  have hlen : (filterL (fun c => do
      let b ← anyL (fun t => Charged.covers t c) old
      pure !b) cs).val.length ≤ cs.length := by
    rw [filterL_val]; exact List.length_filter_le _ _
  have h2 := maxima_ticks hsub
  simp only [Tabled.fresh, bind_ticks]
  generalize (filterL (fun c => do
      let b ← anyL (fun t => Charged.covers t c) old
      pure !b) cs) = F at h1 h2 hlen ⊢
  have h3 : 12 * F.val.length * F.val.length ≤ 12 * cs.length * cs.length :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hlen) hlen
  unfold freshBound
  omega

end Sep

end R003

end RwLog
