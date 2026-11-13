import Aeneas
import RwlogCore.Funs
import RwLogVerified.Digits
import RwLogVerified.TrieModel

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core

/-- A trie node of the store, as a node of the list model. -/
def tnM (t : store.Trie) : TN := ⟨t.kids.val.map (·.val), t.val.val⟩

/-- The trie of a store, as a list. -/
def trieM (v : List store.Trie) : TrieM := v.map tnM

@[simp] theorem trieM_length (v : List store.Trie) : (trieM v).length = v.length := by
  simp [trieM]

theorem kidAt_trieM (l : List store.Trie) (p d : Nat) (hp : p < l.length) (hd : d < 17) :
    TrieM.kidAt (trieM l) p d = ((l[p]).kids.val[d]'(by simpa using hd)).val := by
  simp [TrieM.kidAt, trieM, tnM, List.getElem?_eq_getElem hp, List.getD_eq_getElem?_getD, hd]

theorem valAt_trieM (l : List store.Trie) (q : Nat) (hq : q < l.length) :
    TrieM.valAt (trieM l) q = (l[q]).val.val := by
  simp [TrieM.valAt, trieM, tnM, List.getElem?_eq_getElem hq]

theorem trieM_addKid (l : List store.Trie) (p : Nat) (hp : p < l.length) (d n : Usize)
    (hn : n.val = l.length) :
    trieM ((l ++ [({ kids := Array.repeat 17#usize 0#usize, val := 0#usize } : store.Trie)]).set p
      { kids := (l[p]).kids.set d n, val := (l[p]).val }) = TrieM.addKid (trieM l) p d.val := by
  rw [List.set_append_left _ _ hp]
  simp only [trieM, List.map_append, List.map_set, TrieM.addKid, List.map_cons, List.map_nil,
    List.length_map]
  congr 1
  rw [List.modify_eq_set_getElem?]
  simp [tnM, List.getElem?_eq_getElem hp, hn, List.map_set]

theorem trieM_setVal (l : List store.Trie) (q : Nat) (hq : q < l.length) (v : Usize) :
    trieM (l.set q { kids := (l[q]).kids, val := v }) = TrieM.setVal (trieM l) q v.val := by
  simp only [trieM, List.map_set, TrieM.setVal]
  rw [List.modify_eq_set_getElem?]
  simp [tnM, List.getElem?_eq_getElem hq]

/-- Only the trie changed, by adding at most `n` trie nodes. -/
structure Grew (s s' : store.Store) (n : Nat) : Prop where
  nodes : s'.nodes = s.nodes
  slots : s'.slots = s.slots
  ea : s'.ea = s.ea
  eb : s'.eb = s.eb
  ticks : s'.ticks = s.ticks
  wf : (trieM s'.trie.val).WF
  ext : (trieM s.trie.val).Ext (trieM s'.trie.val)
  len : s'.trie.val.length ≤ s.trie.val.length + n

theorem Grew.refl {s : store.Store} (h : (trieM s.trie.val).WF) : Grew s s 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, h, TrieM.Ext.refl _, Nat.le_refl _⟩

theorem Grew.trans {a b c : store.Store} {n m : Nat} (h₁ : Grew a b n) (h₂ : Grew b c m) :
    Grew a c (n + m) :=
  ⟨h₂.nodes.trans h₁.nodes, h₂.slots.trans h₁.slots, h₂.ea.trans h₁.ea, h₂.eb.trans h₁.eb,
    h₂.ticks.trans h₁.ticks, h₂.wf, h₁.ext.trans h₂.ext, by have := h₁.len; have := h₂.len; omega⟩

theorem Grew.mono {a b : store.Store} {n m : Nat} (h : Grew a b n) (hnm : n ≤ m) : Grew a b m :=
  { h with len := by have := h.len; omega }

theorem kid_spec (s : store.Store) (p d : Usize)
    (hW : (trieM s.trie.val).WF) (hp : p.val < s.trie.val.length) (hd : d.val < 17)
    (hroom : s.trie.val.length < Usize.max) :
    store.Store.kid s p d ⦃ c s' =>
      Grew s s' 1 ∧ TrieM.walk (trieM s'.trie.val) p.val [d.val] = some c.val ⦄ := by
  unfold store.Store.kid
  step*
  · rename_i h
    have hc : c.val ≠ 0 := by
      intro e
      have : c = 0#usize := by scalar_tac
      simp [this] at h
    have hk := kidAt_trieM s.trie.val p.val d.val hp hd
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, hW, TrieM.Ext.refl _, by omega⟩, ?_⟩
    simp only [TrieM.walk, hk, ← t_post, ← c_post, hc, ↓reduceIte]
  · have h : ¬ ((c != 0#usize) = true) := by assumption
    have hc : c.val = 0 := by simpa using h
    have hk : TrieM.kidAt (trieM s.trie.val) p.val d.val = 0 := by
      rw [kidAt_trieM s.trie.val p.val d.val hp hd, ← t_post, ← c_post, hc]
    have hlen : s.trie.len.val = s.trie.val.length := by simp
    have e : trieM (index_mut_back { kids := a1, val := t1.val }).val =
        TrieM.addKid (trieM s.trie.val) p.val d.val := by
      rw [index_mut_back_post, a1_post, t1_post]
      simp only [alloc.vec.Vec.set_val_eq, v_post]
      have h1 : (s.trie.val ++ [({ kids := Array.repeat 17#usize 0#usize, val := 0#usize } :
          store.Trie)])[p.val]'(by simp; omega) = s.trie.val[p.val] :=
        List.getElem_append_left hp
      simp only [h1]
      exact trieM_addKid s.trie.val p.val hp d s.trie.len hlen
    have hlen' : (index_mut_back { kids := a1, val := t1.val }).val.length = s.trie.val.length + 1 := by
      have := congrArg List.length e
      simpa only [trieM_length, TrieM.length_addKid] using this
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, by dsimp only; omega⟩, ?_⟩
    · rw [e]; exact hW.addKid (by simpa using hp) hd hk
    · rw [e]; exact TrieM.Ext.addKid hW (by simpa using hp) hd hk
    · rw [e]
      have := TrieM.kidAt_addKid hW (p := p.val) (d := d.val) (by simpa using hp) hd p.val d.val
      simp only [and_self, ↓reduceIte, trieM_length] at this
      have hpos : s.trie.val.length ≠ 0 := by omega
      simp [TrieM.walk, this, hpos, hlen]

/-- Walking on from the end of a walk, in a trie that has grown since. -/
theorem walk_snoc {a b : store.Store} {n : Nat} (g : Grew a b n)
    {p q c : Nat} {k : List Nat} {d : Nat} (hp : p < a.trie.val.length)
    (h₁ : TrieM.walk (trieM a.trie.val) p k = some q)
    (h₂ : TrieM.walk (trieM b.trie.val) q [d] = some c) :
    TrieM.walk (trieM b.trie.val) p (k ++ [d]) = some c := by
  rw [TrieM.walk_append, g.ext.keep p (by simpa using hp) k q h₁]
  exact h₂

theorem digits_spec (s : store.Store) (p x : Usize)
    (hW : (trieM s.trie.val).WF) (hp : p.val < s.trie.val.length)
    (hroom : s.trie.val.length + (digits x.val).length ≤ Usize.max) :
    store.Store.digits s p x ⦃ q s' =>
      Grew s s' (digits x.val).length ∧
        TrieM.walk (trieM s'.trie.val) p.val (digits x.val) = some q.val ⦄ := by
  induction hx : x.val using Nat.strong_induction_on generalizing s p x with
  | _ k ih => ?_
  subst hx
  unfold store.Store.digits
  split
  · rename_i h0
    have : x.val = 0 := by simp [h0]
    simp only [this, digits_zero, List.length_nil, TrieM.walk]
    step*
    exact Grew.refl hW
  · rename_i h0
    have hx0 : x.val ≠ 0 := by
      intro e; apply h0; scalar_tac
    rw [digits_pos hx0, List.length_append, List.length_singleton] at hroom
    step as ⟨i, hi⟩
    have hi' : i.val = x.val / 16 := by simpa using hi
    have IH := ih i.val (by omega) s p i hW hp (by rw [hi']; omega) rfl
    step with IH as ⟨q, s1, hG, hw⟩
    step as ⟨i1, hi1⟩
    have hi1' : i1.val = x.val % 16 := by simpa using hi1
    have hq : q.val < s1.trie.val.length := by
      have := TrieM.walk_lt hG.wf (s := p.val) (by have := hG.ext.len; simp at this ⊢; omega) _ hw
      simpa using this
    have hlen1 := hG.len
    step with kid_spec s1 q i1 hG.wf hq (by omega) (by rw [hi'] at hlen1; omega) as ⟨c, s2, hG2, hw2⟩
    rw [digits_pos hx0, ← hi', ← hi1']
    refine ⟨by simpa using hG.trans hG2, ?_⟩
    exact walk_snoc hG2 (by have := hG.ext.len; simp at this; omega) hw hw2

theorem word_spec (s : store.Store) (p x : Usize)
    (hW : (trieM s.trie.val).WF) (hp : p.val < s.trie.val.length)
    (hroom : s.trie.val.length + (wd x.val).length ≤ Usize.max) :
    store.Store.word s p x ⦃ q s' =>
      Grew s s' (wd x.val).length ∧
        TrieM.walk (trieM s'.trie.val) p.val (wd x.val) = some q.val ⦄ := by
  unfold store.Store.word
  simp only [wd, List.length_append, List.length_singleton] at hroom ⊢
  step with digits_spec s p x hW hp (by omega) as ⟨q, s1, hG, hw⟩
  have hq : q.val < s1.trie.val.length := by
    have := TrieM.walk_lt hG.wf (s := p.val) (by have := hG.ext.len; simp at this ⊢; omega) _ hw
    simpa using this
  have hlen1 := hG.len
  step with kid_spec s1 q 16#usize hG.wf hq (by simp) (by omega) as ⟨c, s2, hG2, hw2⟩
  exact ⟨hG.trans hG2, walk_snoc hG2 (by have := hG.ext.len; simp at this; omega) hw hw2⟩

end RwLogVerified
