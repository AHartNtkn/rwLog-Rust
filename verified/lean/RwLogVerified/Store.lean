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

/-! ## Keys of nodes -/

/-- The key of a node: a digit for its kind, then the keys of its parts. -/
def key : store.Node → List Nat
  | .V0 => [0]
  | .Nil => [1]
  | .VL a => 2 :: wd a.val
  | .VR a => 3 :: wd a.val
  | .Sym f => 4 :: wd f.val
  | .App a b => 5 :: (wd a.val ++ wd b.val)

theorem wd_inj {x y : Nat} (h : wd x = wd y) : x = y :=
  (wd_append_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

theorem key_inj {n m : store.Node} (h : key n = key m) : n = m := by
  cases n <;> cases m <;> simp only [key, List.cons.injEq, reduceCtorEq, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, Nat.reduceEqDiff, false_and,
    true_and, and_true] at h
  · rfl
  · have := wd_inj h; congr 1; scalar_tac
  · have := wd_inj h; congr 1; scalar_tac
  · have := wd_inj h; congr 1; scalar_tac
  · obtain ⟨e₁, e₂⟩ := wd_append_inj h
    have e₂ := wd_inj e₂
    congr 1 <;> scalar_tac
  · rfl

theorem wd_length_usize (a : Usize) : (wd a.val).length ≤ 17 := by
  apply wd_length_le 16
  have h1 : a.val ≤ Usize.max := by scalar_tac
  have h2 : Usize.max ≤ 18446744073709551615 := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> scalar_tac
  have h3 : (16 : Nat) ^ 16 = 18446744073709551616 := by norm_num
  omega

/-! ## Well-formed stores -/

def IsVarNode : store.Node → Prop
  | .V0 => True
  | .VL _ => True
  | .VR _ => True
  | _ => False

/-- A node may be asked for: its parts are in the store, and the part of a
variable is a variable. -/
def ArgOK (nodes : List store.Node) : store.Node → Prop
  | .VL a => ∃ m, nodes[a.val]? = some m ∧ IsVarNode m
  | .VR a => ∃ m, nodes[a.val]? = some m ∧ IsVarNode m
  | .App a b => a.val < nodes.length ∧ b.val < nodes.length
  | _ => True

/-- The node as it is stored: the left of the variable at `0` is that
variable. -/
def norm : store.Node → store.Node
  | .VL a => if a.val = 0 then .V0 else .VL a
  | n => n

/-- The node at position `i` refers to earlier nodes only, the part of a
variable is a variable, and no node is the left of position `0`. -/
def Fits (nodes : List store.Node) (i : Nat) : store.Node → Prop
  | .VL a => a.val < i ∧ a.val ≠ 0 ∧ ∃ m, nodes[a.val]? = some m ∧ IsVarNode m
  | .VR a => a.val < i ∧ ∃ m, nodes[a.val]? = some m ∧ IsVarNode m
  | .App a b => a.val < i ∧ b.val < i
  | _ => True

theorem Fits.append {nodes : List store.Node} {i : Nat} {n : store.Node} (h : Fits nodes i n)
    (more : List store.Node) : Fits (nodes ++ more) i n := by
  cases n <;> simp only [Fits] at h ⊢
  · obtain ⟨h₁, h₂, m, hm, hv⟩ := h
    exact ⟨h₁, h₂, m, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hm).1]; exact hm, hv⟩
  · obtain ⟨h₁, m, hm, hv⟩ := h
    exact ⟨h₁, m, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hm).1]; exact hm, hv⟩
  · exact h

theorem Fits.of_argOK {nodes : List store.Node} {n : store.Node} (h : ArgOK nodes n) :
    Fits nodes nodes.length (norm n) := by
  cases n with
  | V0 => trivial
  | Nil => trivial
  | Sym f => trivial
  | VL a =>
    obtain ⟨m, hm, hv⟩ := h
    simp only [norm]
    split
    · trivial
    · rename_i ha
      exact ⟨(List.getElem?_eq_some_iff.1 hm).1, ha, m, hm, hv⟩
  | VR a =>
    obtain ⟨m, hm, hv⟩ := h
    exact ⟨(List.getElem?_eq_some_iff.1 hm).1, m, hm, hv⟩
  | App a b => exact h

/-- The structure of a store: nodes refer backwards, no node occurs twice,
every node has cells that are not from the future, and the trie finds exactly
the nodes there are. -/
structure Shape (s : store.Store) : Prop where
  fits : ∀ i n, s.nodes.val[i]? = some n → Fits s.nodes.val i n
  nodup : s.nodes.val.Nodup
  slots : s.slots.val.length = s.nodes.val.length
  epA : ∀ sl ∈ s.slots.val, sl.ea.val ≤ s.ea.val
  epB : ∀ sl ∈ s.slots.val, sl.eb.val ≤ s.eb.val
  ea_pos : 1 ≤ s.ea.val
  eb_pos : 1 ≤ s.eb.val
  wf : (trieM s.trie.val).WF
  t1 : ∀ i n, s.nodes.val[i]? = some n →
    ∃ q, TrieM.walk (trieM s.trie.val) 0 (key n) = some q ∧ TrieM.valAt (trieM s.trie.val) q = i + 1
  t2 : ∀ q, TrieM.valAt (trieM s.trie.val) q ≠ 0 →
    ∃ n, s.nodes.val[TrieM.valAt (trieM s.trie.val) q - 1]? = some n ∧
      TrieM.walk (trieM s.trie.val) 0 (key n) = some q

theorem Shape.grew {s s' : store.Store} {n : Nat} (h : Shape s) (g : Grew s s' n) : Shape s' where
  fits := by rw [g.nodes]; exact h.fits
  nodup := by rw [g.nodes]; exact h.nodup
  slots := by rw [g.nodes, g.slots]; exact h.slots
  epA := by rw [g.slots, g.ea]; exact h.epA
  epB := by rw [g.slots, g.eb]; exact h.epB
  ea_pos := by rw [g.ea]; exact h.ea_pos
  eb_pos := by rw [g.eb]; exact h.eb_pos
  wf := g.wf
  t1 := by
    intro i m hm
    rw [g.nodes] at hm
    obtain ⟨q, hq, hv⟩ := h.t1 i m hm
    exact ⟨q, g.ext.keep 0 h.wf.pos _ _ hq, by rw [g.ext.val]; exact hv⟩
  t2 := by
    intro q hq
    rw [g.ext.val] at hq ⊢
    obtain ⟨m, hm, hw⟩ := h.t2 q hq
    exact ⟨m, by rw [g.nodes]; exact hm, g.ext.keep 0 h.wf.pos _ _ hw⟩

theorem is_var_spec (s : store.Store) (a : Usize) (ha : a.val < s.nodes.val.length) :
    store.Store.is_var s a ⦃ b => (b = true ↔ IsVarNode (s.nodes.val[a.val])) ⦄ := by
  unfold store.Store.is_var
  step as ⟨n, hn⟩
  subst hn
  cases s.nodes.val[a.val] <;> simp [IsVarNode]

theorem path_spec (s : store.Store) (n : store.Node)
    (hW : (trieM s.trie.val).WF) (hn : ArgOK s.nodes.val n)
    (hroom : s.trie.val.length + 35 ≤ Usize.max) :
    store.Store.path s n ⦃ r s' =>
      r.1 = norm n ∧ Grew s s' 35 ∧
        TrieM.walk (trieM s'.trie.val) 0 (key (norm n)) = some r.2.val ⦄ := by
  have hpos := hW.pos
  simp only [trieM_length] at hpos
  unfold store.Store.path
  cases n with
  | V0 =>
    simp only [norm, key]
    step with kid_spec s 0#usize 0#usize hW hpos (by simp) (by omega) as ⟨c, s1, hG, hw⟩
    exact ⟨hG.mono (by omega), hw⟩
  | Nil =>
    simp only [norm, key]
    step with kid_spec s 0#usize 1#usize hW hpos (by simp) (by omega) as ⟨c, s1, hG, hw⟩
    exact ⟨hG.mono (by omega), hw⟩
  | VL a =>
    obtain ⟨m, hm, hv⟩ := hn
    have ha := (List.getElem?_eq_some_iff.1 hm).1
    have hl := wd_length_usize a
    step
    step with is_var_spec s a ha as ⟨b, hb⟩
    have hbt : b = true := hb.2 (by rw [(List.getElem?_eq_some_iff.1 hm).2]; exact hv)
    subst hbt
    step
    split
    · rename_i h0
      have h0' : a.val = 0 := by simp [h0]
      simp only [norm, h0', ↓reduceIte, key]
      step with kid_spec s 0#usize 0#usize hW hpos (by simp) (by omega) as ⟨c, s1, hG, hw⟩
      exact ⟨hG.mono (by omega), hw⟩
    · rename_i h0
      have h0' : a.val ≠ 0 := by intro e; apply h0; scalar_tac
      simp only [norm, h0', ↓reduceIte, key]
      step with kid_spec s 0#usize 2#usize hW hpos (by simp) (by omega) as ⟨p, s1, hG, hw⟩
      have hp : p.val < s1.trie.val.length := by
        have := TrieM.walk_lt hG.wf (s := 0) hG.wf.pos _ hw
        simpa using this
      have hlen1 := hG.len
      step with word_spec s1 p a hG.wf hp (by omega) as ⟨q, s2, hG2, hw2⟩
      refine ⟨(hG.trans hG2).mono (by omega), ?_⟩
      show TrieM.walk _ 0 ([2] ++ wd a.val) = _
      rw [TrieM.walk_append, hG2.ext.keep 0 hG.wf.pos _ _ hw]
      exact hw2
  | VR a =>
    obtain ⟨m, hm, hv⟩ := hn
    have ha := (List.getElem?_eq_some_iff.1 hm).1
    have hl := wd_length_usize a
    step
    step with is_var_spec s a ha as ⟨b, hb⟩
    have hbt : b = true := hb.2 (by rw [(List.getElem?_eq_some_iff.1 hm).2]; exact hv)
    subst hbt
    step
    simp only [norm, key]
    step with kid_spec s 0#usize 3#usize hW hpos (by simp) (by omega) as ⟨p, s1, hG, hw⟩
    have hp : p.val < s1.trie.val.length := by
      have := TrieM.walk_lt hG.wf (s := 0) hG.wf.pos _ hw
      simpa using this
    have hlen1 := hG.len
    step with word_spec s1 p a hG.wf hp (by omega) as ⟨q, s2, hG2, hw2⟩
    refine ⟨(hG.trans hG2).mono (by omega), ?_⟩
    show TrieM.walk _ 0 ([3] ++ wd a.val) = _
    rw [TrieM.walk_append, hG2.ext.keep 0 hG.wf.pos _ _ hw]
    exact hw2
  | Sym f =>
    simp only [norm, key]
    step with kid_spec s 0#usize 4#usize hW hpos (by simp) (by omega) as ⟨p, s1, hG, hw⟩
    have hp : p.val < s1.trie.val.length := by
      have := TrieM.walk_lt hG.wf (s := 0) hG.wf.pos _ hw
      simpa using this
    have hlen1 := hG.len
    step as ⟨i, hi⟩
    have hi' : i.val = f.val := by scalar_tac
    have hl := wd_length_usize i
    step with word_spec s1 p i hG.wf hp (by omega) as ⟨q, s2, hG2, hw2⟩
    refine ⟨(hG.trans hG2).mono (by omega), ?_⟩
    show TrieM.walk _ 0 ([4] ++ wd f.val) = _
    rw [TrieM.walk_append, hG2.ext.keep 0 hG.wf.pos _ _ hw, ← hi']
    exact hw2
  | App a b =>
    obtain ⟨ha, hb⟩ := hn
    have hla := wd_length_usize a
    have hlb := wd_length_usize b
    step
    step
    simp only [norm, key]
    step with kid_spec s 0#usize 5#usize hW hpos (by simp) (by omega) as ⟨p, s1, hG, hw⟩
    have hp : p.val < s1.trie.val.length := by
      have := TrieM.walk_lt hG.wf (s := 0) hG.wf.pos _ hw
      simpa using this
    have hlen1 := hG.len
    step with word_spec s1 p a hG.wf hp (by omega) as ⟨p1, s2, hG2, hw2⟩
    have hp1 : p1.val < s2.trie.val.length := by
      have := TrieM.walk_lt hG2.wf (s := p.val)
        (by have := hG2.ext.len; simp at this ⊢; omega) _ hw2
      simpa using this
    have hlen2 := hG2.len
    step with word_spec s2 p1 b hG2.wf hp1 (by omega) as ⟨q, s3, hG3, hw3⟩
    refine ⟨((hG.trans hG2).trans hG3).mono (by omega), ?_⟩
    show TrieM.walk _ 0 ([5] ++ (wd a.val ++ wd b.val)) = _
    have hpos1 : 0 < (trieM s1.trie.val).length := hG.wf.pos
    have hpos0 : 0 < (trieM s.trie.val).length := hW.pos
    rw [TrieM.walk_append, hG3.ext.keep 0 hG2.wf.pos _ _ (hG2.ext.keep 0 hpos1 _ _ hw)]
    simp only [Option.bind_some]
    rw [TrieM.walk_append, hG3.ext.keep p.val (by have := hG2.ext.len; simp at this ⊢; omega) _ _ hw2]
    exact hw3

/-- The cells of a node just added. -/
def blankSlot : store.Slot := { ea := 0#u64, va := 0#usize, eb := 0#u64, vb := 0#usize }

theorem intern_spec (s : store.Store) (n : store.Node) (hS : Shape s) (hn : ArgOK s.nodes.val n)
    (hroom : s.trie.val.length + 35 ≤ Usize.max) (hnodes : s.nodes.val.length < Usize.max) :
    store.Store.intern s n ⦃ id s' =>
      Shape s' ∧ s'.nodes.val[id.val]? = some (norm n) ∧
      ((s'.nodes = s.nodes ∧ s'.slots = s.slots) ∨
        (s'.nodes.val = s.nodes.val ++ [norm n] ∧ s'.slots.val = s.slots.val ++ [blankSlot])) ∧
      s'.ea = s.ea ∧ s'.eb = s.eb ∧ s'.ticks = s.ticks ∧
      s'.trie.val.length ≤ s.trie.val.length + 35 ⦄ := by
  unfold store.Store.intern
  step with path_spec s n hS.wf hn hroom as ⟨m, q, s1, hm, hG, hw⟩
  subst hm
  have hS1 : Shape s1 := hS.grew hG
  have hq : q.val < s1.trie.val.length := by
    simpa using TrieM.walk_lt hG.wf hG.wf.pos _ hw
  have hnodes1 : s1.nodes.val.length < Usize.max := by rw [hG.nodes]; exact hnodes
  have hslots1 : s1.slots.val.length < Usize.max := by rw [hS1.slots]; exact hnodes1
  step as ⟨t, ht⟩
  have hval : TrieM.valAt (trieM s1.trie.val) q.val = t.val.val := by
    rw [valAt_trieM _ _ hq, ht]
  split
  · rename_i hne
    have hv0 : t.val.val ≠ 0 := by
      intro e
      have : t.val = 0#usize := by scalar_tac
      simp [this] at hne
    step as ⟨i, hi, _⟩
    obtain ⟨m', hm', hw'⟩ := hS1.t2 q.val (by rw [hval]; exact hv0)
    have e : m' = norm n := key_inj (hS1.wf.inj _ _ _ hw' hw)
    refine ⟨hS1, ?_, Or.inl ⟨hG.nodes, hG.slots⟩, hG.ea, hG.eb, hG.ticks, hG.len⟩
    rw [hi, ← hval, ← e]; exact hm'
  · rename_i hne
    have hv0 : t.val.val = 0 := by simpa using hne
    have hnew : norm n ∉ s1.nodes.val := by
      intro hmem
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hmem
      obtain ⟨q', hq', hv'⟩ := hS1.t1 j (norm n) (by rw [← e]; exact List.getElem?_eq_getElem hj)
      rw [hw] at hq'
      cases hq'
      omega
    step*
    have hlen : s1.nodes.len.val = s1.nodes.val.length := by simp
    have htrie : trieM (index_mut_back { kids := t1.kids, val := i }).val =
        TrieM.setVal (trieM s1.trie.val) q.val i.val := by
      rw [index_mut_back_post, t1_post]
      simp only [alloc.vec.Vec.set_val_eq]
      exact trieM_setVal _ _ hq i
    have hq' : q.val < (trieM s1.trie.val).length := by simpa using hq
    have hArg : ArgOK s1.nodes.val n := by rw [hG.nodes]; exact hn
    refine ⟨?_, ?_, Or.inr ⟨?_, ?_⟩, hG.ea, hG.eb, hG.ticks, ?_⟩
    · constructor
      · intro j m hm
        simp only [v_post] at hm ⊢
        rcases Nat.lt_trichotomy j s1.nodes.val.length with hlt | heq | hgt
        · rw [List.getElem?_append_left hlt] at hm
          exact (hS1.fits j m hm).append _
        · subst heq
          simp only [List.getElem?_concat_length, Option.some.injEq] at hm
          subst hm
          exact (Fits.of_argOK hArg).append _
        · rw [List.getElem?_eq_none (by simp; omega)] at hm
          cases hm
      · simp only [v_post]
        rw [List.nodup_append]
        refine ⟨hS1.nodup, by simp, ?_⟩
        intro a ha b hb e
        simp only [List.mem_singleton] at hb
        subst hb e
        exact hnew ha
      · simp only [v_post, v1_post, List.length_append, List.length_singleton, hS1.slots]
      · intro sl hsl
        simp only [v1_post, List.mem_append, List.mem_singleton] at hsl
        rcases hsl with hsl | rfl
        · exact hS1.epA sl hsl
        · simp
      · intro sl hsl
        simp only [v1_post, List.mem_append, List.mem_singleton] at hsl
        rcases hsl with hsl | rfl
        · exact hS1.epB sl hsl
        · simp
      · exact hS1.ea_pos
      · exact hS1.eb_pos
      · show (trieM (index_mut_back { kids := t1.kids, val := i }).val).WF
        rw [htrie]; exact hS1.wf.setVal _ _
      · intro j m hm
        show ∃ q', TrieM.walk (trieM (index_mut_back { kids := t1.kids, val := i }).val) 0 (key m)
          = some q' ∧ TrieM.valAt (trieM (index_mut_back { kids := t1.kids, val := i }).val) q'
          = j + 1
        rw [htrie]
        simp only [v_post] at hm
        rcases Nat.lt_trichotomy j s1.nodes.val.length with hlt | heq | hgt
        · rw [List.getElem?_append_left hlt] at hm
          obtain ⟨q', hq'w, hv'⟩ := hS1.t1 j m hm
          refine ⟨q', by rw [TrieM.walk_setVal]; exact hq'w, ?_⟩
          rw [TrieM.valAt_setVal _ hq']
          have : q' ≠ q.val := by intro e; rw [e, hval] at hv'; omega
          simp [this, hv']
        · subst heq
          simp only [List.getElem?_concat_length, Option.some.injEq] at hm
          subst hm
          refine ⟨q.val, by rw [TrieM.walk_setVal]; exact hw, ?_⟩
          rw [TrieM.valAt_setVal _ hq']
          simp [i_post, hlen]
        · rw [List.getElem?_eq_none (by simp; omega)] at hm
          cases hm
      · intro q'
        show TrieM.valAt (trieM (index_mut_back { kids := t1.kids, val := i }).val) q' ≠ 0 →
          ∃ m, v.val[TrieM.valAt (trieM (index_mut_back { kids := t1.kids, val := i }).val) q' - 1]?
            = some m ∧
            TrieM.walk (trieM (index_mut_back { kids := t1.kids, val := i }).val) 0 (key m) = some q'
        rw [htrie, TrieM.valAt_setVal _ hq']
        by_cases hqq : q' = q.val
        · subst hqq
          intro _
          refine ⟨norm n, ?_, by rw [TrieM.walk_setVal]; exact hw⟩
          simp [v_post, i_post, hlen]
        · simp only [hqq, ↓reduceIte]
          intro hne'
          obtain ⟨m, hm, hwm⟩ := hS1.t2 q' hne'
          refine ⟨m, ?_, by rw [TrieM.walk_setVal]; exact hwm⟩
          rw [v_post, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hm).1]
          exact hm
    · simp [v_post, hlen]
    · rw [v_post, hG.nodes]
    · rw [v1_post, hG.slots]; rfl
    · have := congrArg List.length htrie
      simp only [trieM_length, TrieM.length_setVal] at this
      show (index_mut_back { kids := t1.kids, val := i }).val.length ≤ _
      have := hG.len
      omega

end RwLogVerified
