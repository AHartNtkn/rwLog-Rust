/-
# The trie that finds a node by its key, as a list

A trie is a list of trie nodes. A trie node has seventeen positions of
children and a value. Position `0` is the root; a child `0` means there is no
child. `walk` follows a key from a node. Adding a missing child (`addKid`)
keeps every walk there was and adds only walks that end at the new node, so
it keeps the walks from the root injective: two keys never lead to the same
trie node.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace RwLogVerified

structure TN where
  kids : List Nat
  val : Nat

abbrev TrieM := List TN

namespace TrieM

def kidAt (tr : TrieM) (p d : Nat) : Nat :=
  match tr[p]? with
  | some n => n.kids.getD d 0
  | none => 0

def valAt (tr : TrieM) (q : Nat) : Nat :=
  match tr[q]? with
  | some n => n.val
  | none => 0

def walk (tr : TrieM) : Nat → List Nat → Option Nat
  | p, [] => some p
  | p, d :: ds => if kidAt tr p d = 0 then none else walk tr (kidAt tr p d) ds

theorem walk_append (tr : TrieM) (p : Nat) (k₁ k₂ : List Nat) :
    walk tr p (k₁ ++ k₂) = (walk tr p k₁).bind fun q => walk tr q k₂ := by
  induction k₁ generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.cons_append, walk]
    split
    · rfl
    · exact ih _

/-- The trie node with no children and no value. -/
def blank : TN := ⟨List.replicate 17 0, 0⟩

theorem blank_getD (d : Nat) : blank.kids.getD d 0 = 0 := by
  simp only [blank, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- Give `p` the new child `tr.length` at digit `d`. -/
def addKid (tr : TrieM) (p d : Nat) : TrieM :=
  tr.modify p (fun n => { n with kids := n.kids.set d tr.length }) ++ [blank]

/-- Set the value of `q`. -/
def setVal (tr : TrieM) (q v : Nat) : TrieM := tr.modify q fun n => { n with val := v }

structure WF (tr : TrieM) : Prop where
  pos : 0 < tr.length
  kids_len : ∀ n ∈ tr, n.kids.length = 17
  kid_lt : ∀ p d, kidAt tr p d < tr.length
  inj : ∀ k₁ k₂ q, walk tr 0 k₁ = some q → walk tr 0 k₂ = some q → k₁ = k₂

theorem walk_lt {tr : TrieM} (h : WF tr) {s : Nat} (hs : s < tr.length) (k : List Nat) {q : Nat}
    (hw : walk tr s k = some q) : q < tr.length := by
  induction k generalizing s with
  | nil => simp only [walk, Option.some.injEq] at hw; omega
  | cons d ds ih =>
    simp only [walk] at hw
    split at hw
    · cases hw
    · exact ih (h.kid_lt s d) hw

@[simp] theorem length_addKid (tr : TrieM) (p d : Nat) : (addKid tr p d).length = tr.length + 1 := by
  simp [addKid]

@[simp] theorem length_setVal (tr : TrieM) (q v : Nat) : (setVal tr q v).length = tr.length := by
  simp [setVal]

theorem kidAt_addKid {tr : TrieM} (h : WF tr) {p d : Nat} (hp : p < tr.length) (hd : d < 17)
    (p' d' : Nat) :
    kidAt (addKid tr p d) p' d' =
      if p' = p ∧ d' = d then tr.length else if p' = tr.length then 0 else kidAt tr p' d' := by
  unfold kidAt addKid
  rcases Nat.lt_trichotomy p' tr.length with hlt | heq | hgt
  · rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_modify]
    have hne : p' ≠ tr.length := by omega
    by_cases hpp : p = p'
    · subst hpp
      have hk : (tr[p]).kids.length = 17 := h.kids_len _ (List.getElem_mem hp)
      simp only [↓reduceIte, List.getElem?_eq_getElem hp, true_and, hne]
      by_cases hdd : d' = d
      · subst hdd
        simp [List.getD_eq_getElem?_getD, hk, hd]
      · simp [List.getD_eq_getElem?_getD, Ne.symm hdd, hdd]
    · have : ¬ (p' = p ∧ d' = d) := fun e => hpp e.1.symm
      simp [hpp, this, hne, List.getElem?_eq_getElem hlt]
  · subst heq
    have : ¬ (tr.length = p ∧ d' = d) := fun e => by omega
    simp only [List.length_modify, Nat.le_refl, List.getElem?_append_right, Nat.sub_self,
      List.getElem?_cons_zero, this, ↓reduceIte]
    exact blank_getD d' 
  · have h1 : ¬ (p' = p ∧ d' = d) := fun e => by omega
    have h2 : p' ≠ tr.length := by omega
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    simp [h1, h2]

/-- What walks there are after a child is added. -/
theorem walk_addKid {tr : TrieM} (h : WF tr) {p d : Nat} (hp : p < tr.length) (hd : d < 17)
    (hpd : kidAt tr p d = 0) (s : Nat) (hs : s < tr.length) (k : List Nat) (q : Nat) :
    walk (addKid tr p d) s k = some q ↔
      walk tr s k = some q ∨ (q = tr.length ∧ ∃ k₀, k = k₀ ++ [d] ∧ walk tr s k₀ = some p) := by
  induction k generalizing s with
  | nil =>
    simp only [walk, Option.some.injEq, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self,
      and_false, false_and, exists_false, or_false]
  | cons d' ds ih =>
    simp only [walk]
    rw [kidAt_addKid h hp hd]
    by_cases hc : s = p ∧ d' = d
    · obtain ⟨rfl, rfl⟩ := hc
      have hpos := h.pos
      have hne : tr.length ≠ 0 := by omega
      simp only [and_self, ↓reduceIte, hne, hpd]
      constructor
      · intro hw
        cases ds with
        | nil =>
          simp only [walk, Option.some.injEq] at hw
          exact Or.inr ⟨hw.symm, [], rfl, rfl⟩
        | cons e es =>
          simp only [walk] at hw
          rw [kidAt_addKid h hp hd] at hw
          have : ¬ (tr.length = s ∧ e = d') := fun e => by omega
          simp [this] at hw
      · rintro (hw | ⟨rfl, k₀, hk, hw⟩)
        · cases hw
        · cases k₀ with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, true_and] at hk
            subst hk; rfl
          | cons e es =>
            simp only [List.cons_append, List.cons.injEq] at hk
            obtain ⟨rfl, -⟩ := hk
            simp [walk, hpd] at hw
    · have hne : s ≠ tr.length := by omega
      simp only [hc, ↓reduceIte, hne]
      by_cases hz : kidAt tr s d' = 0
      · simp only [hz, ↓reduceIte, reduceCtorEq, false_or, false_iff, not_and, not_exists]
        rintro - k₀ hk hw
        cases k₀ with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hk
          simp only [walk, Option.some.injEq] at hw
          exact hc ⟨hw, hk.1⟩
        | cons e es =>
          simp only [List.cons_append, List.cons.injEq] at hk
          obtain ⟨rfl, -⟩ := hk
          simp [walk, hz] at hw
      · simp only [hz, ↓reduceIte]
        rw [ih _ (h.kid_lt s d')]
        constructor
        · rintro (hw | ⟨rfl, k₀, rfl, hw⟩)
          · exact Or.inl hw
          · exact Or.inr ⟨rfl, d' :: k₀, rfl, by simp [walk, hz, hw]⟩
        · rintro (hw | ⟨rfl, k₀, hk, hw⟩)
          · exact Or.inl hw
          · cases k₀ with
            | nil =>
              simp only [List.nil_append, List.cons.injEq] at hk
              simp only [walk, Option.some.injEq] at hw
              exact absurd ⟨hw, hk.1⟩ hc
            | cons e es =>
              simp only [List.cons_append, List.cons.injEq] at hk
              obtain ⟨rfl, rfl⟩ := hk
              simp only [walk, hz, ↓reduceIte] at hw
              exact Or.inr ⟨rfl, es, rfl, hw⟩

theorem valAt_addKid (tr : TrieM) (p d q : Nat) :
    valAt (addKid tr p d) q = valAt tr q := by
  unfold valAt addKid
  rcases Nat.lt_trichotomy q tr.length with hlt | heq | hgt
  · rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_modify]
    by_cases hpq : p = q
    · subst hpq; simp [List.getElem?_eq_getElem hlt]
    · simp [hpq]
  · subst heq
    simp [blank]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem WF.addKid {tr : TrieM} (h : WF tr) {p d : Nat} (hp : p < tr.length) (hd : d < 17)
    (hpd : kidAt tr p d = 0) : WF (addKid tr p d) where
  pos := by simp
  kids_len := by
    intro n hn
    simp only [TrieM.addKid, List.mem_append, List.mem_singleton] at hn
    rcases hn with hn | rfl
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
      simp only [List.getElem_modify]
      split
      · simp only [List.length_set]
        exact h.kids_len _ (List.getElem_mem _)
      · exact h.kids_len _ (List.getElem_mem _)
    · simp [blank]
  kid_lt := by
    intro p' d'
    rw [kidAt_addKid h hp hd, length_addKid]
    have := h.kid_lt p' d'
    split
    · omega
    · split <;> omega
  inj := by
    intro k₁ k₂ q h₁ h₂
    rw [walk_addKid h hp hd hpd 0 h.pos] at h₁ h₂
    rcases h₁ with h₁ | ⟨rfl, a, rfl, ha⟩ <;> rcases h₂ with h₂ | ⟨hq, b, rfl, hb⟩
    · exact h.inj _ _ _ h₁ h₂
    · have := walk_lt h h.pos _ h₁; omega
    · have := walk_lt h h.pos _ h₂; omega
    · rw [h.inj _ _ _ ha hb]

theorem kidAt_setVal (tr : TrieM) (q v p d : Nat) : kidAt (setVal tr q v) p d = kidAt tr p d := by
  unfold kidAt setVal
  rw [List.getElem?_modify]
  by_cases hqp : q = p
  · subst hqp
    cases tr[q]? <;> simp
  · simp [hqp]

theorem walk_setVal (tr : TrieM) (q v s : Nat) (k : List Nat) :
    walk (setVal tr q v) s k = walk tr s k := by
  induction k generalizing s with
  | nil => rfl
  | cons d ds ih => simp only [walk, kidAt_setVal, ih]

theorem valAt_setVal (tr : TrieM) {q : Nat} (hq : q < tr.length) (v q' : Nat) :
    valAt (setVal tr q v) q' = if q' = q then v else valAt tr q' := by
  unfold valAt setVal
  rw [List.getElem?_modify]
  by_cases hqq : q = q'
  · subst hqq
    simp [List.getElem?_eq_getElem hq]
  · have : q' ≠ q := fun e => hqq e.symm
    simp [hqq, this]

theorem WF.setVal {tr : TrieM} (h : WF tr) (q v : Nat) : WF (setVal tr q v) where
  pos := by simpa using h.pos
  kids_len := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
    simp only [TrieM.setVal, List.getElem_modify]
    have hi' : i < tr.length := by simpa using hi
    have := h.kids_len (tr[i]'hi') (List.getElem_mem _)
    split <;> exact this
  kid_lt := by
    intro p d
    rw [kidAt_setVal, length_setVal]
    exact h.kid_lt p d
  inj := by
    intro k₁ k₂ q'
    rw [walk_setVal, walk_setVal]
    exact h.inj k₁ k₂ q'

/-- `tr'` is `tr` with children added: every walk is kept, the walks from the
root that end in `tr` are the old ones, and values are kept. -/
structure Ext (tr tr' : TrieM) : Prop where
  len : tr.length ≤ tr'.length
  keep : ∀ s, s < tr.length → ∀ k q, walk tr s k = some q → walk tr' s k = some q
  old : ∀ k q, q < tr.length → walk tr' 0 k = some q → walk tr 0 k = some q
  val : ∀ q, valAt tr' q = valAt tr q

theorem Ext.refl (tr : TrieM) : Ext tr tr :=
  ⟨Nat.le_refl _, fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ => rfl⟩

theorem Ext.trans {a b c : TrieM} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c where
  len := h₁.len.trans h₂.len
  keep := fun s hs k q h => h₂.keep s (by have := h₁.len; omega) k q (h₁.keep s hs k q h)
  old := fun k q hq h => h₁.old k q hq (h₂.old k q (by have := h₁.len; omega) h)
  val := fun q => (h₂.val q).trans (h₁.val q)

theorem Ext.addKid {tr : TrieM} (h : WF tr) {p d : Nat} (hp : p < tr.length) (hd : d < 17)
    (hpd : kidAt tr p d = 0) : Ext tr (addKid tr p d) where
  len := by simp
  keep := fun s hs k q hw => (walk_addKid h hp hd hpd s hs k q).2 (Or.inl hw)
  old := by
    intro k q hq hw
    rcases (walk_addKid h hp hd hpd 0 h.pos k q).1 hw with hw | ⟨rfl, -⟩
    · exact hw
    · omega
  val := valAt_addKid tr p d

end TrieM

end RwLogVerified
