/-
# The Rust store, as translated by Aeneas: what each primitive does and costs

`verified/rust/src/store.rs` is the base machine. This file proves, for the
Lean that Aeneas generates from it, that every public operation keeps the
invariant of the store (`Inv`), does what its comment says, and advances the
tick counter by exactly one.

* `Shape`: nodes refer to earlier nodes, no node occurs twice, and the trie
  finds exactly the nodes there are. `intern_spec`: asking for a node returns
  the one identifier of that node, adding it if it is new.
* `tbl s t k`: what table `t` holds for `k`. `get`, `set`, `get_flag`,
  `set_flag` and `clear` read and write this function and nothing else.
* `Room s n`: there is room for `n` more ticks. The sizes of the store are
  bounded by the ticks spent, so this one hypothesis rules out every overflow.
-/
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

/-! ## Tables, the invariant, and the primitives -/

/-- What table `t` holds for `k`. -/
def tbl (s : store.Store) (t : store.Tbl) (k : Nat) : Option Nat :=
  match s.slots.val[k]? with
  | none => none
  | some sl =>
    match t with
    | .A => if sl.ea = s.ea then some sl.va.val else none
    | .B => if sl.eb = s.eb then some sl.vb.val else none

/-- The invariant of a store: its shape, the variable `0` at position `0`,
and sizes bounded by the ticks spent. -/
structure Inv (s : store.Store) : Prop where
  shape : Shape s
  root : s.nodes.val[0]? = some .V0
  nodes_le : s.nodes.val.length ≤ s.ticks.val + 1
  trie_le : s.trie.val.length ≤ 40 * (s.ticks.val + 1) + 1
  ea_le : s.ea.val ≤ s.ticks.val + 1
  eb_le : s.eb.val ≤ s.ticks.val + 1

/-- There is room for `n` more ticks: no counter and no index can overflow
within them. -/
def Room (s : store.Store) (n : Nat) : Prop := 40 * (s.ticks.val + n) + 100 ≤ Usize.max

theorem usize_le_u64 : Usize.max ≤ U64.max := by
  rcases Usize.bounds_eq with h | h
  · rw [h]; scalar_tac
  · rw [h]

theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> scalar_tac

theorem Room.mono {s : store.Store} {n m : Nat} (h : Room s n) (hmn : m ≤ n) : Room s m := by
  unfold Room at h ⊢; omega

theorem Room.next {s s' : store.Store} {n k : Nat} (h : Room s n) (ht : s'.ticks.val ≤ s.ticks.val + k)
    (hk : k ≤ n) : Room s' (n - k) := by
  unfold Room at h ⊢; omega

/-- Nodes and tables are as they were, and `n` ticks were spent. -/
structure Kept (s s' : store.Store) (n : Nat) : Prop where
  nodes : s'.nodes.val = s.nodes.val
  tbl : tbl s' = tbl s
  ticks : s'.ticks.val = s.ticks.val + n
  inv : Inv s'

theorem Shape.of_eq {s s' : store.Store} (h : Shape s) (hn : s'.nodes = s.nodes)
    (hs : s'.slots = s.slots) (ht : s'.trie = s.trie) (ha : s'.ea = s.ea) (hb : s'.eb = s.eb) :
    Shape s' := by
  obtain ⟨f, nd, sl, epA, epB, ap, bp, wf, t1, t2⟩ := h
  constructor <;> simp only [hn, hs, ht, ha, hb] <;> assumption

theorem tbl_of_eq {s s' : store.Store} (hs : s'.slots = s.slots) (ha : s'.ea = s.ea)
    (hb : s'.eb = s.eb) : tbl s' = tbl s := by
  funext t k
  simp only [tbl, hs, ha, hb]

theorem tick_spec (s : store.Store) (h : s.ticks.val < U64.max) :
    store.Store.tick s ⦃ s' =>
      s'.nodes = s.nodes ∧ s'.slots = s.slots ∧ s'.trie = s.trie ∧ s'.ea = s.ea ∧ s'.eb = s.eb ∧
        s'.ticks.val = s.ticks.val + 1 ⦄ := by
  unfold store.Store.tick
  step*

theorem Room.tick_lt {s : store.Store} {n : Nat} (h : Room s n) (hn : 1 ≤ n) :
    s.ticks.val < U64.max := by
  have := usize_le_u64
  unfold Room at h; omega

theorem Inv.kept {s s' : store.Store} (hI : Inv s) (hn : s'.nodes = s.nodes)
    (hs : s'.slots = s.slots) (ht : s'.trie = s.trie) (ha : s'.ea = s.ea) (hb : s'.eb = s.eb)
    (n : Nat) (hk : s'.ticks.val = s.ticks.val + n) : Kept s s' n where
  nodes := by rw [hn]
  tbl := tbl_of_eq hs ha hb
  ticks := hk
  inv := by
    obtain ⟨sh, rt, nl, tl, al, bl⟩ := hI
    refine ⟨sh.of_eq hn hs ht ha hb, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hn, ht, ha, hb, hk]
    · exact rt
    · omega
    · omega
    · omega
    · omega

@[step]
theorem read_spec (s : store.Store) (i : store.TermId) (hI : Inv s)
    (hi : i.val < s.nodes.val.length) (hroom : Room s 1) :
    store.Store.read s i ⦃ n s' => s.nodes.val[i.val]? = some n ∧ Kept s s' 1 ⦄ := by
  unfold store.Store.read
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  have : i.val < s1.nodes.val.length := by rw [h1]; exact hi
  step as ⟨n, hn⟩
  refine ⟨?_, hI.kept h1 h2 h3 h4 h5 1 h6⟩
  rw [hn]; simp only [h1]
  exact List.getElem?_eq_getElem hi

@[step]
theorem same_spec (s : store.Store) (a b : store.TermId) (hI : Inv s) (hroom : Room s 1) :
    store.Store.same s a b ⦃ r s' => r = decide (a.val = b.val) ∧ Kept s s' 1 ⦄ := by
  unfold store.Store.same
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  refine ⟨?_, hI.kept h1 h2 h3 h4 h5 1 h6⟩
  by_cases e : a = b
  · subst e; simp
  · have : a.val ≠ b.val := by intro h; apply e; scalar_tac
    simp [e, this]

@[step]
theorem word_eq_spec (s : store.Store) (a b : U32) (hI : Inv s) (hroom : Room s 1) :
    store.Store.word_eq s a b ⦃ r s' => r = decide (a = b) ∧ Kept s s' 1 ⦄ := by
  unfold store.Store.word_eq
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  exact hI.kept h1 h2 h3 h4 h5 1 h6

theorem cell_spec (s : store.Store) (t : store.Tbl) (k : store.TermId)
    (hk : k.val < s.slots.val.length) :
    store.Store.cell s t k ⦃ r => tbl s t k.val = if r.1 then some r.2.val else none ⦄ := by
  unfold store.Store.cell
  step as ⟨sl, hsl⟩
  have e : s.slots.val[k.val]? = some sl := by rw [hsl]; exact List.getElem?_eq_getElem hk
  cases t <;> simp only [tbl, e] <;> step*

@[step]
theorem get_spec (s : store.Store) (t : store.Tbl) (k : store.TermId) (hI : Inv s)
    (hk : k.val < s.nodes.val.length) (hroom : Room s 1) :
    store.Store.get s t k ⦃ r s' => r.map (·.val) = tbl s t k.val ∧ Kept s s' 1 ⦄ := by
  unfold store.Store.get
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  have hK := hI.kept h1 h2 h3 h4 h5 1 h6
  have : k.val < s1.slots.val.length := by rw [h2, hI.shape.slots]; exact hk
  step with cell_spec s1 t k this as ⟨live, v, hc⟩
  rw [hK.tbl] at hc
  split
  · rename_i hl
    simp only [hl, ↓reduceIte] at hc
    step*
    exact ⟨hc.symm, hK⟩
  · rename_i hl
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at hc
    step*
    exact ⟨hc.symm, hK⟩

@[step]
theorem get_flag_spec (s : store.Store) (t : store.Tbl) (k : store.TermId) (hI : Inv s)
    (hk : k.val < s.nodes.val.length) (hroom : Room s 1) :
    store.Store.get_flag s t k ⦃ r s' =>
      r = (tbl s t k.val).map (fun v => decide (v ≠ 0)) ∧ Kept s s' 1 ⦄ := by
  unfold store.Store.get_flag
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  have hK := hI.kept h1 h2 h3 h4 h5 1 h6
  have : k.val < s1.slots.val.length := by rw [h2, hI.shape.slots]; exact hk
  step with cell_spec s1 t k this as ⟨live, v, hc⟩
  rw [hK.tbl] at hc
  split
  · rename_i hl
    simp only [hl, ↓reduceIte] at hc
    step*
    refine ⟨?_, hK⟩
    rw [hc]
    by_cases e : v = 0#usize
    · subst e; simp
    · have : v.val ≠ 0 := by intro h; apply e; scalar_tac
      simp [e, this]
  · rename_i hl
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at hc
    step*
    exact ⟨by rw [hc]; rfl, hK⟩

theorem Shape.set_slot {s s' : store.Store} (hS : Shape s) (hn : s'.nodes = s.nodes)
    (ht : s'.trie = s.trie) (ha : s'.ea = s.ea) (hb : s'.eb = s.eb) {k : Nat} {y : store.Slot}
    (hsl : s'.slots.val = s.slots.val.set k y) (hya : y.ea.val ≤ s.ea.val)
    (hyb : y.eb.val ≤ s.eb.val) : Shape s' := by
  obtain ⟨f, nd, sl, epA, epB, ap, bp, wf, t1, t2⟩ := hS
  constructor <;> simp only [hn, ht, ha, hb, hsl] <;> try assumption
  · simpa using sl
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with h | rfl
    · exact epA x h
    · exact hya
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with h | rfl
    · exact epB x h
    · exact hyb

/-- What a slot holds for a table, given the table's current clearing. -/
def slotVal (s : store.Store) (t : store.Tbl) (sl : store.Slot) : Option Nat :=
  match t with
  | .A => if sl.ea = s.ea then some sl.va.val else none
  | .B => if sl.eb = s.eb then some sl.vb.val else none

theorem tbl_eq_slotVal (s : store.Store) (t : store.Tbl) (k : Nat) :
    tbl s t k = (s.slots.val[k]?).bind (slotVal s t) := by
  unfold tbl slotVal
  cases s.slots.val[k]? <;> cases t <;> rfl

theorem tbl_set_slot {s s' : store.Store} (ha : s'.ea = s.ea) (hb : s'.eb = s.eb) {k : Nat}
    {y : store.Slot} (hk : k < s.slots.val.length) (hsl : s'.slots.val = s.slots.val.set k y)
    (t : store.Tbl) : tbl s' t = Function.update (tbl s t) k (slotVal s t y) := by
  funext k'
  have e : slotVal s' t = slotVal s t := by funext sl; cases t <;> simp [slotVal, ha, hb]
  rw [tbl_eq_slotVal, hsl, e, List.getElem?_set]
  by_cases hkk : k = k'
  · subst hkk; simp [hk]
  · have : k' ≠ k := fun h => hkk h.symm
    simp [hkk, Function.update_of_ne this, tbl_eq_slotVal]

theorem set_cell_spec (st : store.Store) (t : store.Tbl) (k : store.TermId) (v : Usize)
    (hS : Shape st) (hk : k.val < st.slots.val.length) :
    store.Store.set_cell st t k v ⦃ s' =>
      s'.nodes = st.nodes ∧ s'.trie = st.trie ∧ s'.ea = st.ea ∧ s'.eb = st.eb ∧ s'.ticks = st.ticks ∧
      Shape s' ∧ tbl s' t = Function.update (tbl st t) k.val (some v.val) ∧
      ∀ t', t' ≠ t → tbl s' t' = tbl st t' ⦄ := by
  have hsl : st.slots.val[k.val]? = some (st.slots.val[k.val]) := List.getElem?_eq_getElem hk
  unfold store.Store.set_cell
  cases t
  · step*
    · simp [index_mut_back_post, hk]
    · have e : (index_mut_back1 { ea := s1.ea, va := v, eb := s1.eb, vb := s1.vb }).val =
          st.slots.val.set k.val ⟨st.ea, v, (st.slots.val[k.val]).eb, (st.slots.val[k.val]).vb⟩ := by
        simp [index_mut_back1_post, s1_post, index_mut_back_post, s_post]
      refine ⟨hS.set_slot rfl rfl rfl rfl e (Nat.le_refl _) (hS.epB (st.slots.val[k.val]) (List.getElem_mem hk)), ?_, ?_⟩
      · rw [tbl_set_slot (s := st) (s' := { st with slots := index_mut_back1 { ea := s1.ea, va := v, eb := s1.eb, vb := s1.vb } }) rfl rfl hk e]; simp [slotVal]
      · intro t' ht'
        cases t'
        · exact absurd rfl ht'
        · rw [tbl_set_slot (s := st) (s' := { st with slots := index_mut_back1 { ea := s1.ea, va := v, eb := s1.eb, vb := s1.vb } }) rfl rfl hk e]
          funext k'
          by_cases hkk : k' = k.val
          · subst hkk; simp [slotVal, tbl, hsl]
          · simp [Function.update_of_ne hkk]
  · step*
    · simp [index_mut_back_post, hk]
    · have e : (index_mut_back1 { ea := s1.ea, va := s1.va, eb := s1.eb, vb := v }).val =
          st.slots.val.set k.val ⟨(st.slots.val[k.val]).ea, (st.slots.val[k.val]).va, st.eb, v⟩ := by
        simp [index_mut_back1_post, s1_post, index_mut_back_post, s_post]
      refine ⟨hS.set_slot rfl rfl rfl rfl e (hS.epA (st.slots.val[k.val]) (List.getElem_mem hk)) (Nat.le_refl _), ?_, ?_⟩
      · rw [tbl_set_slot (s := st) (s' := { st with slots := index_mut_back1 { ea := s1.ea, va := s1.va, eb := s1.eb, vb := v } }) rfl rfl hk e]; simp [slotVal]
      · intro t' ht'
        cases t'
        · rw [tbl_set_slot (s := st) (s' := { st with slots := index_mut_back1 { ea := s1.ea, va := s1.va, eb := s1.eb, vb := v } }) rfl rfl hk e]
          funext k'
          by_cases hkk : k' = k.val
          · subst hkk; simp [slotVal, tbl, hsl]
          · simp [Function.update_of_ne hkk]
        · exact absurd rfl ht'

theorem Inv.of_shape {s s' : store.Store} (hI : Inv s) (hS : Shape s') (hn : s'.nodes = s.nodes)
    (ht : s'.trie = s.trie) (ha : s'.ea = s.ea) (hb : s'.eb = s.eb)
    (hk : s.ticks.val ≤ s'.ticks.val) : Inv s' := by
  obtain ⟨sh, rt, nl, tl, al, bl⟩ := hI
  refine ⟨hS, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hn, ht, ha, hb]
  · exact rt
  · omega
  · omega
  · omega
  · omega

@[step]
theorem set_spec (s : store.Store) (t : store.Tbl) (k v : store.TermId) (hI : Inv s)
    (hk : k.val < s.nodes.val.length) (hroom : Room s 1) :
    store.Store.set s t k v ⦃ s' =>
      s'.nodes.val = s.nodes.val ∧ s'.ticks.val = s.ticks.val + 1 ∧ Inv s' ∧
      tbl s' t = Function.update (tbl s t) k.val (some v.val) ∧
      ∀ t', t' ≠ t → tbl s' t' = tbl s t' ⦄ := by
  unfold store.Store.set
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  have hK := hI.kept h1 h2 h3 h4 h5 1 h6
  have hk1 : k.val < s1.slots.val.length := by rw [h2, hI.shape.slots]; exact hk
  step with set_cell_spec s1 t k v hK.inv.shape hk1 as ⟨s2, g1, g2, g3, g4, g5, g6, g7, g8⟩
  refine ⟨by rw [g1, h1], by rw [g5, h6], ?_, by rw [g7, hK.tbl], fun t' ht' => by rw [g8 t' ht', hK.tbl]⟩
  exact hK.inv.of_shape g6 g1 g2 g3 g4 (by rw [g5])

@[step]
theorem set_flag_spec (s : store.Store) (t : store.Tbl) (k : store.TermId) (b : Bool) (hI : Inv s)
    (hk : k.val < s.nodes.val.length) (hroom : Room s 1) :
    store.Store.set_flag s t k b ⦃ s' =>
      s'.nodes.val = s.nodes.val ∧ s'.ticks.val = s.ticks.val + 1 ∧ Inv s' ∧
      tbl s' t = Function.update (tbl s t) k.val (some (if b then 1 else 0)) ∧
      ∀ t', t' ≠ t → tbl s' t' = tbl s t' ⦄ := by
  unfold store.Store.set_flag
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  have hK := hI.kept h1 h2 h3 h4 h5 1 h6
  have hk1 : k.val < s1.slots.val.length := by rw [h2, hI.shape.slots]; exact hk
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step with set_cell_spec s1 t k 0#usize hK.inv.shape hk1 as ⟨s2, g1, g2, g3, g4, g5, g6, g7, g8⟩
    refine ⟨by rw [g1, h1], by rw [g5, h6], ?_, by rw [g7, hK.tbl],
      fun t' ht' => by rw [g8 t' ht', hK.tbl]⟩
    exact hK.inv.of_shape g6 g1 g2 g3 g4 (by rw [g5])
  · simp only [↓reduceIte]
    step with set_cell_spec s1 t k 1#usize hK.inv.shape hk1 as ⟨s2, g1, g2, g3, g4, g5, g6, g7, g8⟩
    refine ⟨by rw [g1, h1], by rw [g5, h6], ?_, by rw [g7, hK.tbl],
      fun t' ht' => by rw [g8 t' ht', hK.tbl]⟩
    exact hK.inv.of_shape g6 g1 g2 g3 g4 (by rw [g5])

@[step]
theorem clear_spec (s : store.Store) (t : store.Tbl) (hI : Inv s) (hroom : Room s 1) :
    store.Store.clear s t ⦃ s' =>
      s'.nodes.val = s.nodes.val ∧ s'.ticks.val = s.ticks.val + 1 ∧ Inv s' ∧
      (∀ k, tbl s' t k = none) ∧ ∀ t', t' ≠ t → tbl s' t' = tbl s t' ⦄ := by
  unfold store.Store.clear
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  have hK := hI.kept h1 h2 h3 h4 h5 1 h6
  have hI1 := hK.inv
  have hmax := usize_le_u64
  have hea := hI.ea_le
  have heb := hI.eb_le
  have hea1 : s1.ea.val = s.ea.val := by rw [h4]
  have heb1 : s1.eb.val = s.eb.val := by rw [h5]
  unfold Room at hroom
  cases t
  · step*
    obtain ⟨sh, rt, nl, tl, al, bl⟩ := hI1
    obtain ⟨f, nd, sl, epA, epB, ap, bp, wf, t1, t2⟩ := sh
    refine ⟨by rw [h1], h6, ⟨⟨f, nd, sl, ?_, epB, ?_, bp, wf, t1, t2⟩, rt, nl, tl, ?_, bl⟩, ?_, ?_⟩
    · intro x hx; have := epA x hx; simp only; omega
    · simp only; omega
    · simp only; omega
    · intro k
      simp only [tbl]
      cases hsl : s1.slots.val[k]? with
      | none => rfl
      | some x =>
        have := epA x (List.mem_of_getElem? hsl)
        have hne : x.ea ≠ i := by intro e; rw [e] at this; omega
        simp [hne]
    · intro t' ht'
      cases t'
      · exact absurd rfl ht'
      · rw [← hK.tbl]; funext k; simp only [tbl]
  · step*
    obtain ⟨sh, rt, nl, tl, al, bl⟩ := hI1
    obtain ⟨f, nd, sl, epA, epB, ap, bp, wf, t1, t2⟩ := sh
    refine ⟨by rw [h1], h6, ⟨⟨f, nd, sl, epA, ?_, ap, ?_, wf, t1, t2⟩, rt, nl, tl, al, ?_⟩, ?_, ?_⟩
    · intro x hx; have := epB x hx; simp only; omega
    · simp only; omega
    · simp only; omega
    · intro k
      simp only [tbl]
      cases hsl : s1.slots.val[k]? with
      | none => rfl
      | some x =>
        have := epB x (List.mem_of_getElem? hsl)
        have hne : x.eb ≠ i := by intro e; rw [e] at this; omega
        simp [hne]
    · intro t' ht'
      cases t'
      · rw [← hK.tbl]; funext k; simp only [tbl]
      · exact absurd rfl ht'

@[step]
theorem alloc_spec (s : store.Store) (n : store.Node) (hI : Inv s) (hn : ArgOK s.nodes.val n)
    (hroom : Room s 1) :
    store.Store.alloc s n ⦃ id s' =>
      Inv s' ∧ s'.ticks.val = s.ticks.val + 1 ∧ tbl s' = tbl s ∧
      (∃ more, s'.nodes.val = s.nodes.val ++ more) ∧
      s'.nodes.val[id.val]? = some (norm n) ⦄ := by
  unfold store.Store.alloc
  step with tick_spec s (hroom.tick_lt (Nat.le_refl _)) as ⟨s1, h1, h2, h3, h4, h5, h6⟩
  have hK := hI.kept h1 h2 h3 h4 h5 1 h6
  have hI1 := hK.inv
  have hnl := hI.nodes_le
  have htl := hI.trie_le
  unfold Room at hroom
  step with intern_spec s1 n hI1.shape (by rw [h1]; exact hn) (by rw [h3]; omega)
    (by rw [h1]; omega) as ⟨id, s2, hS2, hid, hcase, ga, gb, gt, glen⟩
  have hroot := hI1.root
  refine ⟨?_, by rw [gt, h6], ?_, ?_, hid⟩
  · rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨hS2, by rw [e1]; exact hroot, ?_, ?_, ?_, ?_⟩ <;> simp only [e1, ga, gb, gt, h1, h4, h5, h6]
      · omega
      · rw [h3] at glen; omega
      · have := hI.ea_le; omega
      · have := hI.eb_le; omega
    · refine ⟨hS2, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [e1, ga, gb, gt, h1, h4, h5, h6]
      · have hpos : 0 < s.nodes.val.length := by
          have := (List.getElem?_eq_some_iff.1 hI.root).1; exact this
        rw [List.getElem?_append_left hpos]; exact hI.root
      · simp; omega
      · rw [h3] at glen; omega
      · have := hI.ea_le; omega
      · have := hI.eb_le; omega
  · rw [← hK.tbl]
    rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact tbl_of_eq e2 ga gb
    · funext t k
      simp only [tbl, e2, ga, gb]
      rcases Nat.lt_trichotomy k s1.slots.val.length with hlt | heq | hgt
      · rw [List.getElem?_append_left hlt]
      · subst heq
        have ha := hI1.shape.ea_pos
        have hb := hI1.shape.eb_pos
        have hna : (0#u64 : U64) ≠ s1.ea := by intro e; rw [← e] at ha; simp at ha
        have hnb : (0#u64 : U64) ≠ s1.eb := by intro e; rw [← e] at hb; simp at hb
        cases t <;> simp [blankSlot, hna, hnb]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  · rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨[], by rw [e1, h1]; simp⟩
    · exact ⟨[norm n], by rw [e1, h1]⟩

theorem wf_blank : TrieM.WF [TrieM.blank] where
  pos := by simp
  kids_len := by intro n hn; simp only [List.mem_singleton] at hn; subst hn; simp [TrieM.blank]
  kid_lt := by
    intro p d
    have : TrieM.kidAt [TrieM.blank] p d = 0 := by
      unfold TrieM.kidAt
      cases p with
      | zero => exact TrieM.blank_getD d
      | succ p => rfl
    simp [this]
  inj := by
    have h0 : ∀ p d, TrieM.kidAt [TrieM.blank] p d = 0 := by
      intro p d
      unfold TrieM.kidAt
      cases p with
      | zero => exact TrieM.blank_getD d
      | succ p => rfl
    have : ∀ k q, TrieM.walk [TrieM.blank] 0 k = some q → k = [] := by
      intro k q h
      cases k with
      | nil => rfl
      | cons d ds => simp [TrieM.walk, h0] at h
    intro k₁ k₂ q h₁ h₂
    rw [this k₁ q h₁, this k₂ q h₂]

theorem new_spec :
    store.Store.new ⦃ s =>
      Inv s ∧ s.ticks.val = 0 ∧ s.nodes.val = [store.Node.V0] ∧ ∀ t k, tbl s t k = none ⦄ := by
  unfold store.Store.new
  step as ⟨v, hv⟩
  have hv' : v.val = [({ kids := Array.repeat 17#usize 0#usize, val := 0#usize } : store.Trie)] := by
    simpa using hv
  have htr : trieM v.val = [TrieM.blank] := by
    rw [hv']; simp [trieM, tnM, TrieM.blank]
  have hS : Shape ⟨alloc.vec.Vec.new store.Node, alloc.vec.Vec.new store.Slot, v, 1#u64, 1#u64,
      0#u64⟩ := by
    constructor
    · intro i n h; simp at h
    · simp
    · simp
    · intro sl h; simp at h
    · intro sl h; simp at h
    · simp
    · simp
    · show (trieM v.val).WF; rw [htr]; exact wf_blank
    · intro i n h; simp at h
    · intro q
      show TrieM.valAt (trieM v.val) q ≠ 0 → _
      rw [htr]
      intro h
      exfalso; apply h
      unfold TrieM.valAt
      cases q with
      | zero => rfl
      | succ q => rfl
  have hbig := usize_max_ge
  have hvl : v.val.length = 1 := by rw [hv']; rfl
  have hroom : v.val.length + 35 ≤ Usize.max := by omega
  have hnl : (alloc.vec.Vec.new store.Node).val.length < Usize.max := by
    show (0 : Nat) < Usize.max; omega
  step with intern_spec _ store.Node.V0 hS trivial hroom hnl
    as ⟨id, s, hS2, hid, hcase, ga, gb, gt, glen⟩
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at hid; simp at hid
  · have e1' : s.nodes.val = [store.Node.V0] := by rw [e1]; rfl
    have e2' : s.slots.val = [blankSlot] := by rw [e2]; rfl
    have glen' : s.trie.val.length ≤ 36 := by
      have : s.trie.val.length ≤ v.val.length + 35 := glen
      omega
    have hga : s.ea.val = 1 := by rw [ga]; rfl
    have hgb : s.eb.val = 1 := by rw [gb]; rfl
    have hgt : s.ticks.val = 0 := by rw [gt]; rfl
    refine ⟨⟨hS2, by rw [e1']; rfl, by rw [e1', hgt]; simp, by omega, by omega, by omega⟩, hgt,
      e1', ?_⟩
    intro t k
    simp only [tbl, e2', ga, gb]
    cases k with
    | zero => cases t <;> simp [blankSlot]
    | succ k => simp

end RwLogVerified
