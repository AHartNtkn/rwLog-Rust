/-
# Stores, and a calculus for programs on the machine of the language

* A store only grows (`Heap.le`), and a pointer of the smaller store reads the
  same in the larger one (`Heap.tm_le`, `Heap.cell_le`).
* The term at a pointer follows its node (`Heap.tm_var`, `tm_sym`, `tm_app`).
* `Run m h Q`: the computation `m` finishes from the store `h`, and its
  result, the store it leaves and the ticks it spent satisfy `Q`. There is one
  rule for each way of building a computation (`Run.pure`, `Run.bind`,
  `Run.read`, `Run.alloc`, `Run.step`), so the result and the cost of a
  program are derived together, by following its text.
-/
import RwLog.Trusted.KernelRung

namespace RwLog

namespace Heap

theorem termsOf_append (cs : List Cell) (c : Cell) :
    termsOf (cs ++ [c]) = termsOf cs ++ [cellTerm (termsOf cs) c] := by
  simp [termsOf, List.foldl_append]

@[simp] theorem termsOf_nil : termsOf [] = [] := rfl

@[simp] theorem termsOf_length (cs : List Cell) : (termsOf cs).length = cs.length := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs c ih => simp [termsOf_append, ih]

theorem termsOf_prefix {cs cs' : List Cell} (h : cs <+: cs') : termsOf cs <+: termsOf cs' := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t c ih =>
    rw [← List.append_assoc, termsOf_append]
    exact ih.trans (List.prefix_append _ _)

theorem termsOf_getElem? (cs : List Cell) (p : Nat) :
    (termsOf cs)[p]? = cs[p]?.map (cellTerm (termsOf (cs.take p))) := by
  induction cs using List.reverseRecOn with
  | nil => simp
  | append_singleton cs c ih =>
    rw [termsOf_append]
    rcases Nat.lt_trichotomy p cs.length with hlt | heq | hgt
    · rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_append_left hlt, ih,
        List.take_append_of_le_length (Nat.le_of_lt hlt)]
    · subst heq
      rw [List.getElem?_append_right (by simp)]
      simp
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      rfl

theorem size_def (h : Heap) : h.size = h.cells.length := rfl

/-- The term at a pointer inside the store, by its node. -/
theorem tm_eq (h : Heap) {p : Nat} {c : Cell} (hc : h.cells[p]? = some c) :
    h.tm p = cellTerm (termsOf (h.cells.take p)) c := by
  have := termsOf_getElem? h.cells p
  rw [hc] at this
  simp only [tm, List.getD_eq_getElem?_getD, this, Option.map_some, Option.getD_some]

theorem tm_var (h : Heap) {p v : Nat} (hc : h.cells[p]? = some (.var v)) : h.tm p = .var v := by
  rw [tm_eq h hc]; rfl

theorem tm_sym (h : Heap) {p : Nat} {f : Sym} (hc : h.cells[p]? = some (.sym f)) :
    h.tm p = .sym f := by
  rw [tm_eq h hc]; rfl

theorem tm_app (h : Heap) {p a b : Nat} (hc : h.cells[p]? = some (.app a b)) :
    h.tm p = .app (h.tm a) (h.tm b) := by
  rw [tm_eq h hc]
  obtain ⟨ha, hb⟩ := h.back p a b hc
  have hp : p ≤ h.cells.length := by
    have := (List.getElem?_eq_some_iff.1 hc).1
    omega
  have hpre : termsOf (h.cells.take p) <+: termsOf h.cells := termsOf_prefix (List.take_prefix _ _)
  have key : ∀ x, x < p → (termsOf (h.cells.take p)).getD x (.var 0) = h.tm x := by
    intro x hx
    have hx' : x < (termsOf (h.cells.take p)).length := by
      rw [termsOf_length, List.length_take]; omega
    simp only [tm, List.getD_eq_getElem?_getD]
    rw [List.prefix_iff_eq_take.1 hpre, List.getElem?_take_of_lt hx']
  simp only [cellTerm, key a ha, key b hb]

theorem lt_size_of_cell (h : Heap) {p : Nat} {c : Cell} (hc : h.cells[p]? = some c) : p < h.size :=
  (List.getElem?_eq_some_iff.1 hc).1

theorem cell_of_lt (h : Heap) {p : Nat} (hp : p < h.size) : ∃ c, h.cells[p]? = some c :=
  ⟨h.cells[p], List.getElem?_eq_getElem hp⟩

/-! ### Growing stores -/

theorem le_refl (h : Heap) : h.le h := List.prefix_refl _

theorem le_trans {h₁ h₂ h₃ : Heap} (a : h₁.le h₂) (b : h₂.le h₃) : h₁.le h₃ := List.IsPrefix.trans a b

theorem size_le {h h' : Heap} (hle : h.le h') : h.size ≤ h'.size := List.IsPrefix.length_le hle

theorem cell_le {h h' : Heap} (hle : h.le h') {p : Nat} {c : Cell} (hc : h.cells[p]? = some c) :
    h'.cells[p]? = some c := by
  obtain ⟨t, ht⟩ := hle
  rw [← ht, List.getElem?_append_left (lt_size_of_cell h hc)]
  exact hc

theorem cell_le' {h h' : Heap} (hle : h.le h') {p : Nat} (hp : p < h.size) :
    h'.cells[p]? = h.cells[p]? := by
  obtain ⟨t, ht⟩ := hle
  rw [← ht, List.getElem?_append_left hp]

theorem tm_le {h h' : Heap} (hle : h.le h') {p : Nat} (hp : p < h.size) : h'.tm p = h.tm p := by
  have hpre := termsOf_prefix hle
  have hp' : p < (termsOf h.cells).length := by rw [termsOf_length]; exact hp
  simp only [tm, List.getD_eq_getElem?_getD]
  rw [List.prefix_iff_eq_take.1 hpre, List.getElem?_take_of_lt hp']

theorem le_push (h : Heap) (c : Cell) (hc : c.Fits h.size) (hn : c ∉ h.cells) :
    h.le (h.push c hc hn) :=
  List.prefix_append _ _

@[simp] theorem size_push (h : Heap) (c : Cell) (hc : c.Fits h.size) (hn : c ∉ h.cells) :
    (h.push c hc hn).size = h.size + 1 := by
  simp [size, push]

theorem cell_push (h : Heap) (c : Cell) (hc : c.Fits h.size) (hn : c ∉ h.cells) :
    (h.push c hc hn).cells[h.size]? = some c := by
  simp [push, size]

/-- A node is stored once. -/
theorem cell_inj (h : Heap) {p q : Nat} {c : Cell} (hp : h.cells[p]? = some c)
    (hq : h.cells[q]? = some c) : p = q := by
  obtain ⟨hp₁, hp₂⟩ := List.getElem?_eq_some_iff.1 hp
  obtain ⟨hq₁, hq₂⟩ := List.getElem?_eq_some_iff.1 hq
  exact (List.Nodup.getElem_inj_iff h.nodup).1 (hp₂.trans hq₂.symm)

/-- Two pointers that read as the same term are the same pointer. -/
theorem tm_inj (h : Heap) : ∀ p q, p < h.size → q < h.size → h.tm p = h.tm q → p = q := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro q hp hq heq
    obtain ⟨n, cp⟩ := h.cell_of_lt hp
    obtain ⟨m, cq⟩ := h.cell_of_lt hq
    cases n with
    | var v =>
      rw [tm_var h cp] at heq
      cases m with
      | var w => rw [tm_var h cq] at heq; cases heq; exact h.cell_inj cp cq
      | sym g => rw [tm_sym h cq] at heq; cases heq
      | app c d => rw [tm_app h cq] at heq; cases heq
    | sym f =>
      rw [tm_sym h cp] at heq
      cases m with
      | var w => rw [tm_var h cq] at heq; cases heq
      | sym g => rw [tm_sym h cq] at heq; cases heq; exact h.cell_inj cp cq
      | app c d => rw [tm_app h cq] at heq; cases heq
    | app a b =>
      rw [tm_app h cp] at heq
      cases m with
      | var w => rw [tm_var h cq] at heq; cases heq
      | sym g => rw [tm_sym h cq] at heq; cases heq
      | app c d =>
        rw [tm_app h cq] at heq
        injection heq with h₁ h₂
        obtain ⟨ha, hb⟩ := h.back p a b cp
        obtain ⟨hc, hd⟩ := h.back q c d cq
        have e₁ := ih a ha c (by omega) (by omega) h₁
        have e₂ := ih b hb d (by omega) (by omega) h₂
        subst e₁ e₂
        exact h.cell_inj cp cq

end Heap

/-! ## The calculus -/

/-- `m` finishes from `h`; its result, the store it leaves and its ticks
satisfy `Q`. -/
def Run {α : Type} (m : Mach α) (h : Heap) (Q : α → Heap → Nat → Prop) : Prop :=
  ∃ r, m h = some r ∧ Q r.val.1 r.val.2 r.ticks

namespace Run

variable {α β : Type}

theorem pure {a : α} {h : Heap} {Q : α → Heap → Nat → Prop} (hq : Q a h 0) :
    Run (Pure.pure a : Mach α) h Q := ⟨⟨(a, h), 0⟩, rfl, hq⟩

theorem bind {m : Mach α} {f : α → Mach β} {h : Heap} {Q₁ : α → Heap → Nat → Prop}
    {Q : β → Heap → Nat → Prop} (hm : Run m h Q₁)
    (hf : ∀ a h' t, Q₁ a h' t → Run (f a) h' fun b h'' t' => Q b h'' (t + t')) :
    Run (m >>= f) h Q := by
  obtain ⟨r, hr, hq⟩ := hm
  obtain ⟨r', hr', hq'⟩ := hf _ _ _ hq
  refine ⟨⟨r'.val, r.ticks + r'.ticks⟩, ?_, hq'⟩
  change Mach.bind m f h = _
  simp only [Mach.bind, hr, hr']

theorem mono {m : Mach α} {h : Heap} {Q Q' : α → Heap → Nat → Prop} (hm : Run m h Q)
    (hq : ∀ a h' t, Q a h' t → Q' a h' t) : Run m h Q' := by
  obtain ⟨r, hr, hq'⟩ := hm
  exact ⟨r, hr, hq _ _ _ hq'⟩

theorem step {a : α} {h : Heap} {Q : α → Heap → Nat → Prop} (hq : Q a h 1) :
    Run (Mach.step a) h Q := ⟨⟨(a, h), 1⟩, rfl, hq⟩

theorem tick {n : Nat} {h : Heap} {Q : Unit → Heap → Nat → Prop} (hq : Q () h n) :
    Run (Mach.tick n) h Q := ⟨⟨((), h), n⟩, rfl, hq⟩

theorem read {p : Nat} {c : Cell} {h : Heap} {Q : Cell → Heap → Nat → Prop}
    (hc : h.cells[p]? = some c) (hq : Q c h 1) : Run (Mach.read p) h Q :=
  ⟨⟨(c, h), 1⟩, by simp [Mach.read, hc], hq⟩

/-- Asking for a node whose parts are in the store: its pointer, in a store
with at most one node more. -/
theorem alloc {c : Cell} {h : Heap} {Q : Nat → Heap → Nat → Prop} (hc : c.Fits h.size)
    (hq : ∀ p h', h.le h' → h'.cells[p]? = some c → h'.size ≤ h.size + 1 → Q p h' 1) :
    Run (Mach.alloc c) h Q := by
  by_cases hn : c ∈ h.cells
  · refine ⟨⟨(h.cells.idxOf c, h), 1⟩, by simp [Mach.alloc, hn], ?_⟩
    exact hq _ _ h.le_refl (by
      rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hn)]
      simp) (Nat.le_add_right _ _)
  · refine ⟨⟨(h.size, h.push c hc hn), 1⟩, by simp [Mach.alloc, hn, hc], ?_⟩
    exact hq _ _ (h.le_push c hc hn) (h.cell_push c hc hn) (by simp)

theorem step_bind {a : α} {f : α → Mach β} {h : Heap} {Q : β → Heap → Nat → Prop}
    (hf : Run (f a) h fun b h' t => Q b h' (1 + t)) : Run (Mach.step a >>= f) h Q :=
  bind (Q₁ := fun x h' t => x = a ∧ h' = h ∧ t = 1) (step ⟨rfl, rfl, rfl⟩)
    (by rintro _ _ _ ⟨rfl, rfl, rfl⟩; exact hf)

theorem read_bind {p : Nat} {c : Cell} {f : Cell → Mach β} {h : Heap} {Q : β → Heap → Nat → Prop}
    (hc : h.cells[p]? = some c) (hf : Run (f c) h fun b h' t => Q b h' (1 + t)) :
    Run (Mach.read p >>= f) h Q :=
  bind (Q₁ := fun x h' t => x = c ∧ h' = h ∧ t = 1) (read hc ⟨rfl, rfl, rfl⟩)
    (by rintro _ _ _ ⟨rfl, rfl, rfl⟩; exact hf)

theorem alloc_bind {c : Cell} {f : Nat → Mach β} {h : Heap} {Q : β → Heap → Nat → Prop}
    (hc : c.Fits h.size)
    (hf : ∀ p h', h.le h' → h'.cells[p]? = some c → h'.size ≤ h.size + 1 →
      Run (f p) h' fun b h'' t => Q b h'' (1 + t)) :
    Run (Mach.alloc c >>= f) h Q :=
  bind (Q₁ := fun p h' t => h.le h' ∧ h'.cells[p]? = some c ∧ h'.size ≤ h.size + 1 ∧ t = 1)
    (alloc hc fun _ _ h₁ h₂ h₃ => ⟨h₁, h₂, h₃, rfl⟩)
    (by rintro p h' _ ⟨h₁, h₂, h₃, rfl⟩; exact hf p h' h₁ h₂ h₃)

/-- The value of a computation that finishes. -/
theorem elim {m : Mach α} {h : Heap} {Q : α → Heap → Nat → Prop} (hm : Run m h Q) :
    ∃ a h' t, m h = some ⟨(a, h'), t⟩ ∧ Q a h' t := by
  obtain ⟨r, hr, hq⟩ := hm
  exact ⟨r.val.1, r.val.2, r.ticks, hr, hq⟩

end Run

/-! ## The operations of the machine of the language, by name -/

section std

@[simp] theorem std_read (p : Nat) : (Base.read p : Mach Cell) = Mach.read p := rfl
@[simp] theorem std_alloc (c : Cell) : (Base.alloc c : Mach Nat) = Mach.alloc c := rfl
@[simp] theorem std_same (p q : Nat) : (Base.same p q : Mach Bool) = Mach.step (decide (p = q)) := rfl
@[simp] theorem std_eqV (v w : Nat) : (Base.eqV Nat v w : Mach Bool) = Mach.step (decide (v = w)) := rfl
@[simp] theorem std_cmpV (v w : Nat) : (Base.cmpV Nat v w : Mach Ordering) = Mach.step (compare v w) :=
  rfl
@[simp] theorem std_eqF (f g : Sym) : (Base.eqF Nat f g : Mach Bool) = Mach.step (decide (f = g)) := rfl
@[simp] theorem std_cmpF (f g : Sym) : (Base.cmpF Nat f g : Mach Ordering) = Mach.step (compare f g) :=
  rfl
@[simp] theorem std_inl (v : Nat) : (Base.inl Nat v : Mach Nat) = Mach.step (2 * v) := rfl
@[simp] theorem std_inr (v : Nat) : (Base.inr Nat v : Mach Nat) = Mach.step (2 * v + 1) := rfl
@[simp] theorem std_get {α : Type} (t : Mach.Tbl α) (k : Key Nat Nat Sym) :
    (Base.get (P := Nat) t k : Mach (Option α)) = Mach.step (t.lookup k) := rfl
@[simp] theorem std_set {α : Type} (t : Mach.Tbl α) (k : Key Nat Nat Sym) (a : α) :
    (Base.set (P := Nat) t k a : Mach (Mach.Tbl α)) = Mach.step ((k, a) :: t) := rfl
@[simp] theorem std_empty {α : Type} : (Base.empty (P := Nat) : Mach.Tbl α) = [] := rfl

end std

end RwLog
