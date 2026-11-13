/-
# The normal form is stable

`Normal e` says, by the shape of `e` alone, that `e` is a node of the normal
form: a right-nested chain whose members are not chains, a right-nested meet
whose members are not meets and stand in the structural order, a right-nested
union whose members are not unions, are not `0`, and stand in the strict
structural order, with a converse only on a call, and every member a node.

* `normal_normB`: the normal form of an expression, and of its converse, is a
  node.
* `Normal.norm_eq`: the normal form of a node is that node. So the nodes are
  exactly the fixed points of `norm` (`normal_iff_norm_eq`).
* `normB_normB`: `normB b (normB c e) = normB (b ^^ c) e`. Normalising twice
  is normalising once, the converse of the normal form is the normal form of
  the converse, and the converse of the converse of a node is the node
  (`Normal.normConv_normConv`). So a goal and its converse name each other,
  and one table can serve both.
* `Normal.view_members`: the members `view` lists are nodes, and the three
  kinds of node are what `NodeView` says they are (`Normal.view_chain`,
  `Normal.view_meet`, `Normal.view_union`).
* Every node the kernel makes is a node: a stretch of a chain
  (`Normal.interval`), a meet without a member (`Normal.without`), a joined
  chain (`Normal.join`), a merged meet (`Normal.meet`), a member of a union
  (`Normal.of_mem_unionParts`).
-/
import RwLog.Kernel.NormalFormCorrect

namespace RwLog

/-- `a` does not stand after `b` in the structural order. -/
abbrev RelLE (a b : Rel) : Prop := (relCmp a b != .gt) = true

/-- `a` stands strictly before `b` in the structural order. -/
abbrev RelLT (a b : Rel) : Prop := (relCmp a b != .gt) = true ∧ a ≠ b

/-- A node of the normal form. -/
def Normal : Rel → Prop
  | .zero => True
  | .span _ => True
  | .call _ => True
  | .conv (.call _) => True
  | .conv _ => False
  | .seq a b => NotSeq a ∧ Normal a ∧ Normal b
  | .and a b => NotAnd a ∧ Normal a ∧ Normal b ∧ ∀ y ∈ andParts b, RelLE a y
  | .or a b => NotOr a ∧ a ≠ .zero ∧ Normal a ∧ Normal b ∧ b ≠ .zero ∧
      ∀ y ∈ orBranches b, RelLT a y

theorem normal_seq {a b : Rel} : Normal (.seq a b) ↔ NotSeq a ∧ Normal a ∧ Normal b := by
  simp [Normal]

theorem normal_and {a b : Rel} :
    Normal (.and a b) ↔ NotAnd a ∧ Normal a ∧ Normal b ∧ ∀ y ∈ andParts b, RelLE a y := by
  simp [Normal]

theorem normal_or {a b : Rel} :
    Normal (.or a b) ↔ NotOr a ∧ a ≠ .zero ∧ Normal a ∧ Normal b ∧ b ≠ .zero ∧
      ∀ y ∈ orBranches b, RelLT a y := by
  simp [Normal]

theorem normal_conv {a : Rel} : Normal (.conv a) ↔ ∃ n, a = .call n := by
  cases a <;> simp [Normal]

/-! ## Sorted lists -/

theorem relLE_antisymm {a b : Rel} (h₁ : RelLE a b) (h₂ : RelLE b a) : a = b := by
  unfold RelLE at h₁ h₂
  rw [relLE_iff] at h₁ h₂
  rw [relCmp_swap] at h₁
  cases hc : relCmp b a with
  | eq => exact (relCmp_eq hc).symm
  | lt => rw [hc] at h₁; cases h₁
  | gt => rw [hc] at h₂; cases h₂

/-- Two sorted lists with the same members, counted with repeats, are equal. -/
theorem eq_of_perm_of_sorted {xs ys : List Rel} (h : xs.Perm ys) (hx : xs.Pairwise RelLE)
    (hy : ys.Pairwise RelLE) : xs = ys :=
  List.Perm.eq_of_pairwise (le := RelLE) (fun _ _ _ _ h₁ h₂ => relLE_antisymm h₁ h₂) hx hy h

/-- Two strictly sorted lists with the same members are equal. -/
theorem eq_of_mem_iff_of_strict {xs ys : List Rel} (h : ∀ z, z ∈ xs ↔ z ∈ ys)
    (hx : xs.Pairwise RelLT) (hy : ys.Pairwise RelLT) : xs = ys :=
  eq_of_perm_of_sorted
    ((List.perm_ext_iff_of_nodup (hx.imp fun h => h.2) (hy.imp fun h => h.2)).2 h)
    (hx.imp fun h => h.1) (hy.imp fun h => h.1)

/-- Sorting a sorted list changes nothing. -/
theorem sortedParts_of_sorted {xs : List Rel} (h : xs.Pairwise RelLE) : sortedParts xs = xs :=
  eq_of_perm_of_sorted (sortedParts_perm xs) (pairwise_sortedParts xs) h

/-- Sorting a strictly sorted list with no `0` changes nothing. -/
theorem sortedBranches_of_strict {xs : List Rel} (h : xs.Pairwise RelLT)
    (h0 : ∀ x ∈ xs, x ≠ .zero) : sortedBranches xs = xs :=
  eq_of_mem_iff_of_strict
    (fun z => by rw [mem_sortedBranches]; exact ⟨fun h => h.1, fun h => ⟨h, h0 z h⟩⟩)
    (pairwise_sortedBranches xs) h

/-! ## Rebuilding -/

theorem mkSeq_cons {x : Rel} : ∀ {L : List Rel}, L ≠ [] → mkSeq (x :: L) = .seq x (mkSeq L)
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem mkAnd_cons {x : Rel} : ∀ {L : List Rel}, L ≠ [] → mkAnd (x :: L) = .and x (mkAnd L)
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem mkOr_cons {x : Rel} : ∀ {L : List Rel}, L ≠ [] → mkOr (x :: L) = .or x (mkOr L)
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem orBranches_ne_nil : ∀ e : Rel, orBranches e ≠ []
  | .or a b => by simp [orBranches, orBranches_ne_nil a]
  | .zero | .span _ | .and _ _ | .seq _ _ | .conv _ | .call _ => by simp [orBranches]

/-- The branches of a rebuilt union are the branches it was built from. -/
theorem orBranches_mkOr : ∀ {L : List Rel}, L ≠ [] → (∀ x ∈ L, NotOr x) → orBranches (mkOr L) = L
  | [], h, _ => absurd rfl h
  | [e], _, hL => orBranches_notOr (hL e (by simp))
  | e :: e' :: es, _, hL => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, orBranches,
      orBranches_notOr (hL e (by simp)),
      orBranches_mkOr (L := e' :: es) (by simp) fun x hx => hL x (List.mem_cons_of_mem _ hx)]
    rfl

theorem unionParts_of_ne_zero {e : Rel} (h : e ≠ .zero) : e.unionParts = orBranches e := by
  cases e with
  | zero => exact absurd rfl h
  | _ => rfl

/-! ## The members of a node -/

theorem Normal.of_mem_seqParts : ∀ {e x : Rel}, Normal e → x ∈ seqParts e → Normal x
  | .seq a b, x, h, hx => by
    obtain ⟨ha, hna, hnb⟩ := normal_seq.1 h
    rw [seqParts, seqParts_notSeq ha] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [List.mem_singleton.1 hx]; exact hna
    · exact hnb.of_mem_seqParts hx
  | .zero, x, h, hx | .span _, x, h, hx | .and _ _, x, h, hx | .or _ _, x, h, hx
  | .conv _, x, h, hx | .call _, x, h, hx => by
    rw [List.mem_singleton.1 hx]; exact h

theorem Normal.of_mem_andParts : ∀ {e x : Rel}, Normal e → x ∈ andParts e → Normal x
  | .and a b, x, h, hx => by
    obtain ⟨ha, hna, hnb, _⟩ := normal_and.1 h
    rw [andParts, andParts_notAnd ha] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [List.mem_singleton.1 hx]; exact hna
    · exact hnb.of_mem_andParts hx
  | .zero, x, h, hx | .span _, x, h, hx | .seq _ _, x, h, hx | .or _ _, x, h, hx
  | .conv _, x, h, hx | .call _, x, h, hx => by
    rw [List.mem_singleton.1 hx]; exact h

theorem Normal.of_mem_orBranches : ∀ {e x : Rel}, Normal e → x ∈ orBranches e → Normal x
  | .or a b, x, h, hx => by
    obtain ⟨ha, _, hna, hnb, _, _⟩ := normal_or.1 h
    rw [orBranches, orBranches_notOr ha] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [List.mem_singleton.1 hx]; exact hna
    · exact hnb.of_mem_orBranches hx
  | .zero, x, h, hx | .span _, x, h, hx | .seq _ _, x, h, hx | .and _ _, x, h, hx
  | .conv _, x, h, hx | .call _, x, h, hx => by
    rw [List.mem_singleton.1 hx]; exact h

/-- A node is the chain of its members. -/
theorem Normal.mkSeq_seqParts : ∀ {e : Rel}, Normal e → mkSeq (seqParts e) = e
  | .seq a b, h => by
    obtain ⟨ha, _, hnb⟩ := normal_seq.1 h
    rw [seqParts, seqParts_notSeq ha, List.singleton_append, mkSeq_cons (seqParts_ne_nil b),
      hnb.mkSeq_seqParts]
  | .zero, _ | .span _, _ | .and _ _, _ | .or _ _, _ | .conv _, _ | .call _, _ => rfl

/-- A node is the meet of its members. -/
theorem Normal.mkAnd_andParts : ∀ {e : Rel}, Normal e → mkAnd (andParts e) = e
  | .and a b, h => by
    obtain ⟨ha, _, hnb, _⟩ := normal_and.1 h
    rw [andParts, andParts_notAnd ha, List.singleton_append, mkAnd_cons (andParts_ne_nil b),
      hnb.mkAnd_andParts]
  | .zero, _ | .span _, _ | .seq _ _, _ | .or _ _, _ | .conv _, _ | .call _, _ => rfl

/-- The members of a meet stand in the structural order. -/
theorem Normal.sorted_andParts : ∀ {e : Rel}, Normal e → (andParts e).Pairwise RelLE
  | .and a b, h => by
    obtain ⟨ha, _, hnb, hle⟩ := normal_and.1 h
    rw [andParts, andParts_notAnd ha, List.singleton_append]
    exact List.pairwise_cons.2 ⟨hle, hnb.sorted_andParts⟩
  | .zero, _ | .span _, _ | .seq _ _, _ | .or _ _, _ | .conv _, _ | .call _, _ =>
    List.pairwise_singleton _ _

theorem Normal.mkOr_orBranches : ∀ {e : Rel}, Normal e → mkOr (orBranches e) = e
  | .or a b, h => by
    obtain ⟨ha, _, _, hnb, _, _⟩ := normal_or.1 h
    rw [orBranches, orBranches_notOr ha, List.singleton_append, mkOr_cons (orBranches_ne_nil b),
      hnb.mkOr_orBranches]
  | .zero, _ | .span _, _ | .seq _ _, _ | .and _ _, _ | .conv _, _ | .call _, _ => rfl

theorem Normal.strict_orBranches : ∀ {e : Rel}, Normal e → (orBranches e).Pairwise RelLT
  | .or a b, h => by
    obtain ⟨ha, _, _, hnb, _, hlt⟩ := normal_or.1 h
    rw [orBranches, orBranches_notOr ha, List.singleton_append]
    exact List.pairwise_cons.2 ⟨hlt, hnb.strict_orBranches⟩
  | .zero, _ | .span _, _ | .seq _ _, _ | .and _ _, _ | .conv _, _ | .call _, _ =>
    List.pairwise_singleton _ _

/-- No branch of a node other than `0` is `0`. -/
theorem Normal.ne_zero_of_mem_orBranches : ∀ {e x : Rel}, Normal e → e ≠ .zero →
    x ∈ orBranches e → x ≠ .zero
  | .or a b, x, h, _, hx => by
    obtain ⟨ha, ha0, _, hnb, hb0, _⟩ := normal_or.1 h
    rw [orBranches, orBranches_notOr ha] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [List.mem_singleton.1 hx]; exact ha0
    · exact hnb.ne_zero_of_mem_orBranches hb0 hx
  | .zero, x, _, h0, _ => absurd rfl h0
  | .span _, x, _, h0, hx | .seq _ _, x, _, h0, hx | .and _ _, x, _, h0, hx
  | .conv _, x, _, h0, hx | .call _, x, _, h0, hx => by
    rw [List.mem_singleton.1 hx]; exact h0

/-- The members of a node read as a union are its branches other than `0`. -/
theorem Normal.mem_unionParts {e z : Rel} (h : Normal e) :
    z ∈ e.unionParts ↔ z ∈ orBranches e ∧ z ≠ .zero := by
  by_cases h0 : e = .zero
  · subst h0
    simp only [RelOf.unionParts, orBranches, List.not_mem_nil, List.mem_singleton, false_iff]
    exact fun h => h.2 h.1
  · rw [unionParts_of_ne_zero h0]
    exact ⟨fun hz => ⟨hz, h.ne_zero_of_mem_orBranches h0 hz⟩, fun hz => hz.1⟩

/-- A node is the union of its members. -/
theorem Normal.mkOr_unionParts {e : Rel} (h : Normal e) : mkOr e.unionParts = e := by
  by_cases h0 : e = .zero
  · subst h0; rfl
  · rw [unionParts_of_ne_zero h0, h.mkOr_orBranches]

/-- The members of a union stand in the strict structural order. -/
theorem Normal.strict_unionParts {e : Rel} (h : Normal e) : e.unionParts.Pairwise RelLT := by
  by_cases h0 : e = .zero
  · subst h0; exact List.Pairwise.nil
  · rw [unionParts_of_ne_zero h0]; exact h.strict_orBranches

theorem Normal.of_mem_unionParts {e x : Rel} (h : Normal e) (hx : x ∈ e.unionParts) : Normal x :=
  h.of_mem_orBranches (h.mem_unionParts.1 hx).1

/-! ## Building a node -/

/-- A chain of nodes that are not chains is a node. -/
theorem normal_mkSeq : ∀ {L : List Rel}, L ≠ [] → (∀ x ∈ L, Normal x ∧ NotSeq x) →
    Normal (mkSeq L)
  | [], h, _ => absurd rfl h
  | [e], _, hL => (hL e (by simp)).1
  | e :: e' :: es, _, hL => by
    rw [show mkSeq (e :: e' :: es) = .seq e (mkSeq (e' :: es)) from rfl, normal_seq]
    exact ⟨(hL e (by simp)).2, (hL e (by simp)).1,
      normal_mkSeq (by simp) fun x hx => hL x (List.mem_cons_of_mem _ hx)⟩

/-- A sorted meet of nodes that are not meets is a node. -/
theorem normal_mkAnd : ∀ {L : List Rel}, L ≠ [] → (∀ x ∈ L, Normal x ∧ NotAnd x) →
    L.Pairwise RelLE → Normal (mkAnd L)
  | [], h, _, _ => absurd rfl h
  | [e], _, hL, _ => (hL e (by simp)).1
  | e :: e' :: es, _, hL, hs => by
    obtain ⟨hle, hs'⟩ := List.pairwise_cons.1 hs
    have hL' : ∀ x ∈ e' :: es, Normal x ∧ NotAnd x := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    rw [show mkAnd (e :: e' :: es) = .and e (mkAnd (e' :: es)) from rfl, normal_and,
      andParts_mkAnd (by simp) fun x hx => (hL' x hx).2]
    exact ⟨(hL e (by simp)).2, (hL e (by simp)).1, normal_mkAnd (by simp) hL' hs', hle⟩

/-- A strictly sorted union of nodes that are neither unions nor `0` is a
node. -/
theorem normal_mkOr : ∀ {L : List Rel}, (∀ x ∈ L, Normal x ∧ NotOr x ∧ x ≠ .zero) →
    L.Pairwise RelLT → Normal (mkOr L)
  | [], _, _ => trivial
  | [e], hL, _ => (hL e (by simp)).1
  | e :: e' :: es, hL, hs => by
    obtain ⟨hlt, hs'⟩ := List.pairwise_cons.1 hs
    have hL' : ∀ x ∈ e' :: es, Normal x ∧ NotOr x ∧ x ≠ .zero :=
      fun x hx => hL x (List.mem_cons_of_mem _ hx)
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, normal_or,
      orBranches_mkOr (by simp) fun x hx => (hL' x hx).2.1]
    refine ⟨(hL e (by simp)).2.1, (hL e (by simp)).2.2, (hL e (by simp)).1,
      normal_mkOr hL' hs', ?_, hlt⟩
    cases es with
    | nil => exact (hL' e' (by simp)).2.2
    | cons _ _ => intro h; cases h

/-! ## The normal form is a node -/

/-- The normal form of an expression, and of its converse, is a node. -/
theorem normal_normB : ∀ (b : Bool) (e : Rel), Normal (normB b e)
  | _, .zero => by simp [normB, Normal]
  | false, .span _ | true, .span _ => by simp [normB, Normal]
  | false, .call _ | true, .call _ => by simp [normB, Normal]
  | b, .conv x => by rw [normB]; exact normal_normB (!b) x
  | false, .seq x y => by
    rw [normB]
    refine normal_mkSeq (by simp [seqParts_ne_nil]) fun z hz => ?_
    exact (List.mem_append.1 hz).elim
      (fun h => ⟨(normal_normB false x).of_mem_seqParts h, notSeq_of_mem_seqParts h⟩)
      (fun h => ⟨(normal_normB false y).of_mem_seqParts h, notSeq_of_mem_seqParts h⟩)
  | true, .seq x y => by
    rw [normB]
    refine normal_mkSeq (by simp [seqParts_ne_nil]) fun z hz => ?_
    exact (List.mem_append.1 hz).elim
      (fun h => ⟨(normal_normB true y).of_mem_seqParts h, notSeq_of_mem_seqParts h⟩)
      (fun h => ⟨(normal_normB true x).of_mem_seqParts h, notSeq_of_mem_seqParts h⟩)
  | b, .and x y => by
    rw [normB]
    refine normal_mkAnd (sortedParts_ne_nil (by simp [andParts_ne_nil])) (fun z hz => ?_)
      (pairwise_sortedParts _)
    exact (List.mem_append.1 ((sortedParts_perm _).mem_iff.1 hz)).elim
      (fun h => ⟨(normal_normB b x).of_mem_andParts h, notAnd_of_mem_andParts h⟩)
      (fun h => ⟨(normal_normB b y).of_mem_andParts h, notAnd_of_mem_andParts h⟩)
  | b, .or x y => by
    rw [normB]
    refine normal_mkOr (fun z hz => ?_) (pairwise_sortedBranches _)
    obtain ⟨hz, h0⟩ := mem_sortedBranches.1 hz
    exact (List.mem_append.1 hz).elim
      (fun h => ⟨(normal_normB b x).of_mem_orBranches h, notOr_of_mem_orBranches h, h0⟩)
      (fun h => ⟨(normal_normB b y).of_mem_orBranches h, notOr_of_mem_orBranches h, h0⟩)

theorem normal_norm (e : Rel) : Normal e.norm := normal_normB false e

theorem normal_normConv (e : Rel) : Normal e.normConv := normal_normB true e

/-! ## The normal form of a node is that node -/

/-- The normal form of a node is that node. -/
theorem Normal.normB_false : ∀ {e : Rel}, Normal e → normB false e = e
  | .zero, _ | .span _, _ | .call _, _ => by simp [normB]
  | .conv a, h => by
    obtain ⟨n, rfl⟩ := normal_conv.1 h
    simp [normB]
  | .seq a b, h => by
    obtain ⟨_, hna, hnb⟩ := normal_seq.1 h
    rw [normB, hna.normB_false, hnb.normB_false]
    exact h.mkSeq_seqParts
  | .and a b, h => by
    obtain ⟨_, hna, hnb, _⟩ := normal_and.1 h
    rw [normB, hna.normB_false, hnb.normB_false]
    rw [show andParts a ++ andParts b = andParts (.and a b) from rfl,
      sortedParts_of_sorted h.sorted_andParts]
    exact h.mkAnd_andParts
  | .or a b, h => by
    obtain ⟨_, _, hna, hnb, _, _⟩ := normal_or.1 h
    rw [normB, hna.normB_false, hnb.normB_false]
    rw [show orBranches a ++ orBranches b = orBranches (.or a b) from rfl,
      sortedBranches_of_strict h.strict_orBranches
        fun x hx => h.ne_zero_of_mem_orBranches (fun h => by cases h) hx]
    exact h.mkOr_orBranches

/-- The normal form of a node is that node. -/
theorem Normal.norm_eq {e : Rel} (h : Normal e) : e.norm = e := h.normB_false

/-- The nodes of the normal form are the fixed points of `norm`. -/
theorem normal_iff_norm_eq {e : Rel} : Normal e ↔ e.norm = e :=
  ⟨Normal.norm_eq, fun h => h ▸ normal_norm e⟩

/-- The nodes of the normal form are the normal forms of expressions. -/
theorem normal_iff_exists {e : Rel} : Normal e ↔ ∃ b e', e = normB b e' :=
  ⟨fun h => ⟨false, e, h.normB_false.symm⟩, fun ⟨b, e', h⟩ => h ▸ normal_normB b e'⟩

/-! ## Normalising a member at a time -/

/-- The members of the normal form of a chain are those of the normal forms
of its members, in the reverse order for the converse. -/
theorem seqParts_normB : ∀ (b : Bool) (e : Rel), seqParts (normB b e) =
    (if b then (seqParts e).reverse else seqParts e).flatMap fun x => seqParts (normB b x)
  | b, .seq x y => by
    have hx := seqParts_normB b x
    have hy := seqParts_normB b y
    rw [seqParts_normB_seq]
    cases b
    · rw [ite_eq_right Bool.false_ne_true, hx, hy]; simp [seqParts]
    · rw [ite_eq_left rfl, hx, hy]; simp [seqParts]
  | b, .zero | b, .span _ | b, .and _ _ | b, .or _ _ | b, .conv _ | b, .call _ => by
    cases b <;> simp [seqParts]

/-- The members of the normal form of a meet are those of the normal forms
of its members. -/
theorem andParts_normB_perm : ∀ (b : Bool) (e : Rel),
    (andParts (normB b e)).Perm ((andParts e).flatMap fun x => andParts (normB b x))
  | b, .and x y => by
    rw [andParts_normB_and, andParts, List.flatMap_append]
    exact (sortedParts_perm _).trans ((andParts_normB_perm b x).append (andParts_normB_perm b y))
  | b, .zero | b, .span _ | b, .seq _ _ | b, .or _ _ | b, .conv _ | b, .call _ => by
    simp [andParts]

/-- The branches of the normal form of a union are those of the normal forms
of its branches. -/
theorem mem_orBranches_normB (b : Bool) {z : Rel} (hz : z ≠ .zero) : ∀ e : Rel,
    z ∈ orBranches (normB b e) ↔ ∃ w ∈ orBranches e, z ∈ orBranches (normB b w)
  | .or x y => by
    rw [mem_orBranches_normB_or b hz, mem_orBranches_normB b hz x, mem_orBranches_normB b hz y]
    simp only [orBranches, List.mem_append]
    constructor
    · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
      · exact ⟨w, Or.inl hw, h⟩
      · exact ⟨w, Or.inr hw, h⟩
    · rintro ⟨w, hw | hw, h⟩
      · exact Or.inl ⟨w, hw, h⟩
      · exact Or.inr ⟨w, hw, h⟩
  | .zero | .span _ | .seq _ _ | .and _ _ | .conv _ | .call _ => by
    simp [orBranches]

/-! ## Normalising twice -/

/-- Normalising twice is normalising once, with the two converses cancelling:
the converse of the normal form is the normal form of the converse, and the
converse of the converse is the normal form. -/
theorem normB_normB : ∀ (b c : Bool) (e : Rel), normB b (normB c e) = normB (b ^^ c) e
  | b, c, .zero => by simp [normB]
  | b, c, .span s => by cases b <;> cases c <;> simp [normB]
  | b, c, .call n => by cases b <;> cases c <;> simp [normB]
  | b, c, .conv x => by
    rw [normB, normB, normB_normB b (!c) x]
    cases b <;> cases c <;> rfl
  | b, c, .seq x y => by
    have hx : seqParts (normB (b ^^ c) x) =
        (if b then (seqParts (normB c x)).reverse else seqParts (normB c x)).flatMap
          fun w => seqParts (normB b w) := by
      rw [← seqParts_normB, normB_normB b c x]
    have hy : seqParts (normB (b ^^ c) y) =
        (if b then (seqParts (normB c y)).reverse else seqParts (normB c y)).flatMap
          fun w => seqParts (normB b w) := by
      rw [← seqParts_normB, normB_normB b c y]
    rw [← (normal_normB b (normB c (.seq x y))).mkSeq_seqParts, seqParts_normB,
      seqParts_normB_seq]
    cases b <;> cases c <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, List.reverse_append, List.flatMap_append, normB] at hx hy ⊢ <;>
      rw [← hx, ← hy]
  | b, c, .and x y => by
    have hN := normal_normB b (normB c (.and x y))
    rw [← hN.mkAnd_andParts]
    conv => rhs; rw [normB]
    congr 1
    refine eq_of_perm_of_sorted ?_ hN.sorted_andParts (pairwise_sortedParts _)
    refine (andParts_normB_perm b _).trans ?_
    rw [andParts_normB_and]
    refine ((sortedParts_perm _).flatMap_right _).trans ?_
    rw [List.flatMap_append, ← normB_normB b c x, ← normB_normB b c y]
    exact ((andParts_normB_perm b _).symm.append (andParts_normB_perm b _).symm).trans
      (sortedParts_perm _).symm
  | b, c, .or x y => by
    have hN := normal_normB b (normB c (.or x y))
    rw [← hN.mkOr_unionParts]
    conv => rhs; rw [normB]
    congr 1
    refine eq_of_mem_iff_of_strict (fun z => ?_) hN.strict_unionParts (pairwise_sortedBranches _)
    rw [hN.mem_unionParts, mem_sortedBranches, List.mem_append]
    refine and_congr_left fun hz => ?_
    rw [← normB_normB b c x, ← normB_normB b c y, mem_orBranches_normB b hz,
      mem_orBranches_normB b hz (normB c x), mem_orBranches_normB b hz (normB c y)]
    have h0 : z ∉ orBranches (normB b .zero) := by simpa [normB, orBranches] using hz
    constructor
    · rintro ⟨w, hw, h⟩
      have hw0 : w ≠ .zero := fun e => h0 (e ▸ h)
      rcases (mem_orBranches_normB_or c hw0).1 hw with hw | hw
      · exact Or.inl ⟨w, hw, h⟩
      · exact Or.inr ⟨w, hw, h⟩
    · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
      · exact ⟨w, (mem_orBranches_normB_or c fun e => h0 (e ▸ h)).2 (Or.inl hw), h⟩
      · exact ⟨w, (mem_orBranches_normB_or c fun e => h0 (e ▸ h)).2 (Or.inr hw), h⟩

/-- The normal form of a normal form is that normal form. -/
theorem norm_norm (e : Rel) : e.norm.norm = e.norm := normB_normB false false e

/-- The converse of the normal form is the normal form of the converse. -/
theorem normConv_norm (e : Rel) : e.norm.normConv = e.normConv := normB_normB true false e

/-- The normal form of the converse is already normal. -/
theorem norm_normConv (e : Rel) : e.normConv.norm = e.normConv := normB_normB false true e

/-- The converse of the converse is the normal form. -/
theorem normConv_normConv (e : Rel) : e.normConv.normConv = e.norm := normB_normB true true e

/-- The converse of the converse of a node is the node. -/
theorem Normal.normConv_normConv {e : Rel} (h : Normal e) : e.normConv.normConv = e :=
  (RwLog.normConv_normConv e).trans h.norm_eq

/-- Converse is one-to-one on nodes. -/
theorem Normal.normConv_inj {a b : Rel} (ha : Normal a) (hb : Normal b)
    (h : a.normConv = b.normConv) : a = b := by
  rw [← ha.normConv_normConv, ← hb.normConv_normConv, h]

/-! ## Reading a node -/

/-- The members a node is read with. -/
def NodeView.members {S N : Type} : NodeView S N → List N
  | .span _ => []
  | .call _ _ => []
  | .chain xs => xs
  | .meet xs => xs
  | .union xs => xs

/-- The members `view` lists of a node are nodes. -/
theorem Normal.view_members {e x : Rel} (h : Normal e) (hx : x ∈ e.view.members) : Normal x := by
  cases e with
  | zero => simp [RelOf.view, NodeView.members] at hx
  | span s => simp [RelOf.view, NodeView.members] at hx
  | call n => simp [RelOf.view, NodeView.members] at hx
  | conv a =>
    obtain ⟨n, rfl⟩ := normal_conv.1 h
    simp [RelOf.view, NodeView.members] at hx
  | seq a b => exact h.of_mem_seqParts hx
  | and a b => exact h.of_mem_andParts hx
  | or a b => exact h.of_mem_orBranches hx

/-- A node read as a chain: at least two members, each a node and not a
chain, and the node is the chain of them. -/
theorem Normal.view_chain {e : Rel} {xs : List Rel} (h : Normal e) (hv : e.view = .chain xs) :
    2 ≤ xs.length ∧ (∀ x ∈ xs, Normal x ∧ NotSeq x) ∧ mkSeq xs = e := by
  cases e with
  | seq a b =>
    obtain rfl : seqParts (.seq a b) = xs := by simpa [RelOf.view] using hv
    refine ⟨?_, fun x hx => ⟨h.of_mem_seqParts hx, notSeq_of_mem_seqParts hx⟩, h.mkSeq_seqParts⟩
    have ha := List.length_pos_iff.2 (seqParts_ne_nil a)
    have hb := List.length_pos_iff.2 (seqParts_ne_nil b)
    simp only [seqParts, List.length_append]; omega
  | conv a => obtain ⟨n, rfl⟩ := normal_conv.1 h; simp [RelOf.view] at hv
  | _ => simp [RelOf.view] at hv

/-- A node read as a meet: at least two members, each a node and not a meet,
in the structural order, and the node is the meet of them. -/
theorem Normal.view_meet {e : Rel} {xs : List Rel} (h : Normal e) (hv : e.view = .meet xs) :
    2 ≤ xs.length ∧ (∀ x ∈ xs, Normal x ∧ NotAnd x) ∧ xs.Pairwise RelLE ∧ mkAnd xs = e := by
  cases e with
  | and a b =>
    obtain rfl : andParts (.and a b) = xs := by simpa [RelOf.view] using hv
    refine ⟨?_, fun x hx => ⟨h.of_mem_andParts hx, notAnd_of_mem_andParts hx⟩,
      h.sorted_andParts, h.mkAnd_andParts⟩
    have ha := List.length_pos_iff.2 (andParts_ne_nil a)
    have hb := List.length_pos_iff.2 (andParts_ne_nil b)
    simp only [andParts, List.length_append]; omega
  | conv a => obtain ⟨n, rfl⟩ := normal_conv.1 h; simp [RelOf.view] at hv
  | _ => simp [RelOf.view] at hv

/-- A node read as a union: each member a node, not a union and not `0`, in
the strict structural order, and the node is the union of them. -/
theorem Normal.view_union {e : Rel} {xs : List Rel} (h : Normal e) (hv : e.view = .union xs) :
    (∀ x ∈ xs, Normal x ∧ NotOr x ∧ x ≠ .zero) ∧ xs.Pairwise RelLT ∧ mkOr xs = e := by
  cases e with
  | zero =>
    have hxs : xs = [] := by simpa [RelOf.view] using hv.symm
    subst hxs
    exact ⟨fun x hx => (by cases hx), List.Pairwise.nil, rfl⟩
  | or a b =>
    obtain rfl : orBranches (.or a b) = xs := by simpa [RelOf.view] using hv
    exact ⟨fun x hx => ⟨h.of_mem_orBranches hx, notOr_of_mem_orBranches hx,
      h.ne_zero_of_mem_orBranches (fun h => by cases h) hx⟩, h.strict_orBranches,
      h.mkOr_orBranches⟩
  | conv a => obtain ⟨n, rfl⟩ := normal_conv.1 h; simp [RelOf.view] at hv
  | _ => simp [RelOf.view] at hv

/-- A node read as a union lists the members of the node read as a union. -/
theorem Normal.view_union_eq {e : Rel} {xs : List Rel} (h : Normal e) (hv : e.view = .union xs) :
    xs = e.unionParts := by
  cases e with
  | zero => simpa [RelOf.view, RelOf.unionParts] using hv.symm
  | or a b => simpa [RelOf.view, RelOf.unionParts] using hv.symm
  | conv a => obtain ⟨n, rfl⟩ := normal_conv.1 h; simp [RelOf.view] at hv
  | _ => simp [RelOf.view] at hv

/-! ## The nodes the kernel makes -/

/-- A stretch of a chain is a node. -/
theorem Normal.interval {e m : Rel} {i j : Nat} (h : Normal e) (hm : e.interval i j = some m) :
    Normal m := by
  unfold RelOf.interval at hm
  split at hm
  · rename_i hij
    obtain rfl := Option.some.inj hm
    refine normal_mkSeq (fun hnil => ?_) fun x hx => ?_
    · have := congrArg List.length hnil
      simp only [List.length_drop, List.length_take, List.length_nil] at this
      omega
    · have hx' : x ∈ seqParts e := List.mem_of_mem_take (List.mem_of_mem_drop hx)
      exact ⟨h.of_mem_seqParts hx', notSeq_of_mem_seqParts hx'⟩
  · cases hm

/-- A meet without one of its members is a node. -/
theorem Normal.without {e m : Rel} {i : Nat} (h : Normal e) (hm : e.without i = some m) :
    Normal m := by
  unfold RelOf.without at hm
  split at hm
  · rename_i hi
    obtain rfl := Option.some.inj hm
    refine normal_mkAnd (fun hnil => ?_) (fun x hx => ?_)
      (h.sorted_andParts.sublist (List.eraseIdx_sublist _ _))
    · have := congrArg List.length hnil
      rw [List.length_eraseIdx_of_lt hi.1, List.length_nil] at this
      omega
    · have hx' : x ∈ andParts e := List.mem_of_mem_eraseIdx hx
      exact ⟨h.of_mem_andParts hx', notAnd_of_mem_andParts hx'⟩
  · cases hm

/-- Two chains joined are a node. -/
theorem Normal.join {a b : Rel} (ha : Normal a) (hb : Normal b) :
    Normal (mkSeq (seqParts a ++ seqParts b)) :=
  normal_mkSeq (by simp [seqParts_ne_nil]) fun _ hx => (List.mem_append.1 hx).elim
    (fun h => ⟨ha.of_mem_seqParts h, notSeq_of_mem_seqParts h⟩)
    (fun h => ⟨hb.of_mem_seqParts h, notSeq_of_mem_seqParts h⟩)

/-- Two meets merged are a node. -/
theorem Normal.meet {a b : Rel} (ha : Normal a) (hb : Normal b) :
    Normal (mkAnd (sortedParts (andParts a ++ andParts b))) :=
  normal_mkAnd (sortedParts_ne_nil (by simp [andParts_ne_nil]))
    (fun _ hx => (List.mem_append.1 ((sortedParts_perm _).mem_iff.1 hx)).elim
      (fun h => ⟨ha.of_mem_andParts h, notAnd_of_mem_andParts h⟩)
      (fun h => ⟨hb.of_mem_andParts h, notAnd_of_mem_andParts h⟩))
    (pairwise_sortedParts _)

end RwLog
