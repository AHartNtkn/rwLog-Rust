/-
# Rebuilding a term

`rebuild leaf memo p` copies the term at `p` with its variables replaced.
`LeafOK leaf σ cl h₀`: in any store that extends `h₀`, `leaf` returns a
pointer that reads as `σ v` for the variable `v`, in at most `cl` ticks. Then
(`rebuild_spec`) `rebuild` returns a pointer that reads as the term
instantiated by `σ`, and it spends one tick, plus `cl + 5` for every node it
had not visited before. The nodes visited are entries of the memo, the memo
never has two entries for a node, and every entry is in any set of pointers
that is closed under parts and contains `p` (`MemoIn`). So what a pass over
several terms spends is bounded by the number of nodes they reach together.
-/
import RwLog.Kernel.Machine.Prog
import RwLog.Kernel.Machine.Heap

namespace RwLog

namespace Prog

open Term

theorem lookup_cons_if {κ α : Type} [DecidableEq κ] (k k' : κ) (a : α) (t : List (κ × α)) :
    List.lookup k ((k', a) :: t) = if k = k' then some a else List.lookup k t := by
  rw [List.lookup_cons]
  by_cases h : k = k'
  · subst h; simp
  · have : (k == k') = false := by simpa using h
    simp [this, h]

theorem lookup_cons_ptr_ne {α : Type} {k p : Nat} (hk : k ≠ p) (a : α) (t : Mach.Tbl α) :
    List.lookup (Key.ptr k) ((Key.ptr p, a) :: t) = List.lookup (Key.ptr k) t := by
  rw [lookup_cons_if]
  simp [hk]

/-- A set of pointers of the store that has the parts of each member. -/
def Closed (h : Heap) (R : Set Nat) : Prop :=
  ∀ p ∈ R, p < h.size ∧ ∀ a b, h.cells[p]? = some (.app a b) → a ∈ R ∧ b ∈ R

theorem Closed.le {h h' : Heap} {R : Set Nat} (hc : Closed h R) (hle : h.le h') : Closed h' R := by
  intro p hp
  obtain ⟨h₁, h₂⟩ := hc p hp
  refine ⟨Nat.lt_of_lt_of_le h₁ (Heap.size_le hle), fun a b hab => h₂ a b ?_⟩
  rwa [Heap.cell_le' hle h₁] at hab

/-- What a leaf function does: in a store that extends `h₀`, a pointer that
reads as `σ v`, in at most `cl` ticks. -/
def LeafOK (leaf : Nat → Nat → Mach Nat) (σ : Nat → Pat) (cl : Nat) (h₀ : Heap) : Prop :=
  ∀ h p v, h₀.le h → h.cells[p]? = some (.var v) →
    Run (leaf p v) h fun r h' t => h.le h' ∧ r < h'.size ∧ h'.tm r = σ v ∧ t ≤ cl

/-- Every entry of the memo is the node instantiated by `σ`. -/
def MemoOK (σ : Nat → Pat) (h : Heap) (memo : Mach.Tbl Nat) : Prop :=
  ∀ k r, List.lookup (Key.ptr k) memo = some r →
    k < h.size ∧ r < h.size ∧ h.tm r = (h.tm k).bind σ

theorem MemoOK.le {σ : Nat → Pat} {h h' : Heap} {memo : Mach.Tbl Nat} (mo : MemoOK σ h memo)
    (hle : h.le h') : MemoOK σ h' memo := by
  intro k r hk
  obtain ⟨h₁, h₂, h₃⟩ := mo k r hk
  have := Heap.size_le hle
  exact ⟨by omega, by omega, by rw [Heap.tm_le hle h₁, Heap.tm_le hle h₂, h₃]⟩

theorem MemoOK.cons {σ : Nat → Pat} {h : Heap} {memo : Mach.Tbl Nat} (mo : MemoOK σ h memo)
    {p r : Nat} (hp : p < h.size) (hr : r < h.size) (ht : h.tm r = (h.tm p).bind σ) :
    MemoOK σ h ((Key.ptr p, r) :: memo) := by
  intro k r' hk
  rw [lookup_cons_if] at hk
  by_cases hkp : (Key.ptr k : Key Nat Nat Sym) = Key.ptr p
  · simp only [hkp, ↓reduceIte, Option.some.injEq] at hk
    injection hkp with hkp
    subst hkp hk
    exact ⟨hp, hr, ht⟩
  · simp only [hkp, ↓reduceIte] at hk
    exact mo k r' hk

theorem MemoOK.nil (σ : Nat → Pat) (h : Heap) : MemoOK σ h [] := by
  intro k r hk; simp at hk

/-- The memo has one entry for a node, and its nodes are in `R`. -/
structure MemoIn {α : Type} (memo : Mach.Tbl α) (R : Set Nat) : Prop where
  nodup : (memo.map Prod.fst).Nodup
  keys : ∀ e ∈ memo, ∃ k, e.1 = Key.ptr k ∧ k ∈ R

theorem MemoIn.nil {α : Type} (R : Set Nat) : MemoIn ([] : Mach.Tbl α) R :=
  ⟨by simp, by simp⟩

theorem MemoIn.cons {α : Type} {memo : Mach.Tbl α} {R : Set Nat} (mi : MemoIn memo R) {p : Nat}
    (a : α) (hp : p ∈ R) (hn : List.lookup (Key.ptr p) memo = none) :
    MemoIn ((Key.ptr p, a) :: memo) R := by
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, mi.nodup⟩
    intro hmem
    obtain ⟨e, he, hk⟩ := List.mem_map.1 hmem
    rw [List.lookup_eq_none_iff] at hn
    exact absurd (hn e he) (by simp [hk])
  · intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨p, rfl, hp⟩
    · exact mi.keys e he

/-- A memo whose nodes are pointers of the store that read as members of `S`
has at most as many entries as `S` has members. -/
theorem MemoIn.length_le {α : Type} {memo : Mach.Tbl α} {h : Heap} {S : Finset Pat}
    (mi : MemoIn memo {q | q < h.size ∧ h.tm q ∈ S}) : memo.length ≤ S.card := by
  classical
  let f : Key Nat Nat Sym → Pat := fun k =>
    match k with
    | .ptr q => h.tm q
    | _ => .var 0
  have hinj : ∀ x ∈ memo.map Prod.fst, ∀ y ∈ memo.map Prod.fst, f x = f y → x = y := by
    intro x hx y hy hxy
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hy
    obtain ⟨k, hk, hk₁, _⟩ := mi.keys e he
    obtain ⟨k', hk', hk₁', _⟩ := mi.keys e' he'
    rw [hk, hk'] at hxy ⊢
    rw [h.tm_inj k k' hk₁ hk₁' hxy]
  have hnd : ((memo.map Prod.fst).map f).Nodup := List.Nodup.map_on hinj mi.nodup
  have hsub : ((memo.map Prod.fst).map f).toFinset ⊆ S := by
    intro t ht
    simp only [List.mem_toFinset, List.mem_map] at ht
    obtain ⟨_, ⟨e, he, rfl⟩, rfl⟩ := ht
    obtain ⟨k, hk, _, hk₂⟩ := mi.keys e he
    rw [hk]
    exact hk₂
  calc memo.length = ((memo.map Prod.fst).map f).length := by simp
    _ = ((memo.map Prod.fst).map f).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ S.card := Finset.card_le_card hsub

/-- `rebuild` returns the term instantiated by `σ`; it spends a tick, and
`cl + 5` for each node it had not visited. -/
theorem rebuild_spec {leaf : Nat → Nat → Mach Nat} {σ : Nat → Pat} {cl : Nat} {h₀ : Heap}
    (L : LeafOK leaf σ cl h₀) (R : Set Nat) :
    ∀ (p : Nat) (h : Heap) (memo : Mach.Tbl Nat), h₀.le h → MemoOK σ h memo → MemoIn memo R →
      Closed h R → p ∈ R →
      Run (rebuild leaf memo p) h fun r h' t =>
        h.le h' ∧ MemoOK σ h' r.2 ∧ MemoIn r.2 R ∧ r.1 < h'.size ∧
        h'.tm r.1 = (h.tm p).bind σ ∧
        (∀ k, p < k → List.lookup (Key.ptr k) r.2 = List.lookup (Key.ptr k) memo) ∧
        ∃ d, r.2.length = memo.length + d ∧ t ≤ 1 + (cl + 5) * d := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro h memo h0 mo mi hcl hp
    rw [rebuild]
    simp only [std_get, std_read, std_set, std_alloc]
    apply Run.step_bind
    cases hlk : List.lookup (Key.ptr p) memo with
    | some r =>
      obtain ⟨_, hr, ht⟩ := mo p r hlk
      exact Run.pure ⟨h.le_refl, mo, mi, hr, ht, fun _ _ => rfl, 0, rfl, by omega⟩
    | none =>
      obtain ⟨hps, hch⟩ := hcl p hp
      obtain ⟨c, hc⟩ := h.cell_of_lt hps
      apply Run.read_bind hc
      cases c with
      | var v =>
        apply Run.bind (L h p v h0 hc)
        rintro r h' t ⟨hle, hr, ht, hcost⟩
        apply Run.step_bind
        apply Run.pure
        have hps' : p < h'.size := Nat.lt_of_lt_of_le hps (Heap.size_le hle)
        refine ⟨hle, (mo.le hle).cons hps' hr ?_, mi.cons r hp hlk, hr, ?_, ?_, 1, rfl, ?_⟩
        · rw [Heap.tm_le hle hps, Heap.tm_var h hc]; exact ht
        · rw [Heap.tm_var h hc]; exact ht
        · intro k hk
          rw [lookup_cons_ptr_ne (by omega)]
        · omega
      | sym f =>
        apply Run.step_bind
        apply Run.pure
        refine ⟨h.le_refl, mo.cons hps hps ?_, mi.cons p hp hlk, hps, ?_, ?_, 1, rfl, by omega⟩
        · rw [Heap.tm_sym h hc]; rfl
        · rw [Heap.tm_sym h hc]; rfl
        · intro k hk
          rw [lookup_cons_ptr_ne (by omega)]
      | app a b =>
        obtain ⟨haR, hbR⟩ := hch a b hc
        obtain ⟨hap, hbp⟩ := h.back p a b hc
        apply Run.bind (ih a hap h memo h0 mo mi hcl haR)
        rintro ⟨ra, ma⟩ h₁ ta ⟨hle₁, mo₁, mi₁, hra, tma, fr₁, da, hla, hta⟩
        apply Run.bind (ih b hbp h₁ ma (h0.trans hle₁) mo₁ mi₁ (hcl.le hle₁) hbR)
        rintro ⟨rb, mb⟩ h₂ tb ⟨hle₂, mo₂, mi₂, hrb, tmb, fr₂, db, hlb, htb⟩
        have hra₂ : ra < h₂.size := Nat.lt_of_lt_of_le hra (Heap.size_le hle₂)
        apply Run.alloc_bind (c := .app ra rb) ⟨hra₂, hrb⟩
        intro r h₃ hle₃ hcr _
        apply Run.step_bind
        apply Run.pure
        have hle : h.le h₃ := (hle₁.trans hle₂).trans hle₃
        have hr : r < h₃.size := Heap.lt_size_of_cell h₃ hcr
        have hps' : p < h₃.size := Nat.lt_of_lt_of_le hps (Heap.size_le hle)
        have htm : h₃.tm r = (h.tm p).bind σ := by
          rw [Heap.tm_app h₃ hcr, Heap.tm_le hle₃ hra₂, Heap.tm_le hle₂ hra, tma,
            Heap.tm_le hle₃ hrb, tmb, Heap.tm_le hle₁ (by omega), Heap.tm_app h hc]
          rfl
        have hnone : List.lookup (Key.ptr p) mb = none := by
          rw [fr₂ p hbp, fr₁ p hap]; exact hlk
        refine ⟨hle, (mo₂.le hle₃).cons hps' hr ?_, mi₂.cons r hp hnone, hr, htm, ?_,
          da + db + 1, ?_, ?_⟩
        · rw [Heap.tm_le hle hps]; exact htm
        · intro k hk
          rw [lookup_cons_ptr_ne (by omega), fr₂ k (by omega), fr₁ k (by omega)]
        · simp only [List.length_cons, hlb, hla]; omega
        · have e : (cl + 5) * (da + db + 1) = (cl + 5) * da + (cl + 5) * db + (cl + 5) := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
          rw [e]; omega

end Prog

end RwLog
