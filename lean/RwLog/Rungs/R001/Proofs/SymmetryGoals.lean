/-
# Rung R001, Symmetry: table keys of mirrored goals

* `Goal.same` is an equivalence relation, preserved by mirroring and by
  normalization.
* The canonical form is idempotent and commutes with mirroring up to
  canonicalization: `canon e.dual = canon (canon e).dual`.
* The key of a mirrored goal is the key of the mirror of its key:
  `g.dual.norm` is `g.norm.2.dual.norm`, with the orientations combined.
-/
import RwLog.Rungs.R001.Proofs.Symmetry
import RwLog.Rungs.R001.Proofs.SymmetryLists

namespace RwLog

namespace R001

namespace Symmetry

/-! ## Boundaries and goals as table keys -/

theorem boundEq_refl : ∀ a : Option Span, boundEq a a = true
  | none => rfl
  | some a => by simp [boundEq, covers?_refl]

theorem boundEq_symm : ∀ {a b : Option Span}, boundEq a b = true → boundEq b a = true
  | none, none, _ => rfl
  | some a, some b, h => by
    simp only [boundEq, Bool.and_eq_true] at h ⊢; exact ⟨h.2, h.1⟩
  | none, some _, h | some _, none, h => by cases h

theorem boundEq_trans : ∀ {a b c : Option Span}, boundEq a b = true → boundEq b c = true →
    boundEq a c = true
  | none, none, none, _, _ => rfl
  | some a, some b, some c, h₁, h₂ => by
    simp only [boundEq, Bool.and_eq_true] at h₁ h₂ ⊢
    exact ⟨covers?_trans h₁.1 h₂.1, covers?_trans h₂.2 h₁.2⟩
  | none, some _, _, h, _ | some _, none, _, h, _ => by cases h
  | none, none, some _, _, h | some _, some _, none, _, h => by cases h

theorem boundEq_swap : ∀ (a b : Option Span),
    boundEq (a.map Span.swap) (b.map Span.swap) = boundEq a b
  | none, none => rfl
  | some a, some b => by simp [boundEq, covers?_swap]
  | none, some _ => rfl
  | some _, none => rfl

/-- `boundEq` as an equivalence between the boundaries' spans. -/
theorem boundEq_equiv : ∀ {a b : Option Span}, boundEq a b = true → Option.Rel Span.Equiv a b
  | none, none, _ => .none
  | some a, some b, h => by
    simp only [boundEq, Bool.and_eq_true, covers?_iff] at h
    exact .some ⟨h.1, h.2⟩
  | none, some _, h | some _, none, h => by cases h

theorem Goal.same_refl (g : Goal) : g.same g = true := by
  simp [Goal.same, boundEq_refl]

theorem Goal.same_symm {g h : Goal} (e : g.same h = true) : h.same g = true := by
  simp only [Goal.same, Bool.and_eq_true, decide_eq_true_eq] at e ⊢
  exact ⟨⟨e.1.1.symm, boundEq_symm e.1.2⟩, boundEq_symm e.2⟩

theorem Goal.same_trans {g h k : Goal} (e₁ : g.same h = true) (e₂ : h.same k = true) :
    g.same k = true := by
  simp only [Goal.same, Bool.and_eq_true, decide_eq_true_eq] at e₁ e₂ ⊢
  exact ⟨⟨e₁.1.1.trans e₂.1.1, boundEq_trans e₁.1.2 e₂.1.2⟩, boundEq_trans e₁.2 e₂.2⟩

theorem _root_.RwLog.R001.Goal.same_iff {g h : Goal} :
    g.same h = true ↔ g.e = h.e ∧ boundEq g.lb h.lb = true ∧ boundEq g.rb h.rb = true := by
  simp only [Goal.same, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem _root_.RwLog.R001.Goal.same_dual {g h : Goal} (e : g.same h = true) : g.dual.same h.dual = true := by
  rw [Goal.same_iff] at e ⊢
  simp only [Goal.dual, boundEq_swap]
  exact ⟨by rw [e.1], e.2.2, e.2.1⟩

theorem _root_.RwLog.Rel.dual_dual : ∀ e : Rel, e.dual.dual = e
  | .zero => rfl
  | .span s => by simp [Rel.dual]
  | .or a b => by simp [Rel.dual, Rel.dual_dual a, Rel.dual_dual b]
  | .and a b => by simp [Rel.dual, Rel.dual_dual a, Rel.dual_dual b]
  | .seq a b => by simp [Rel.dual, Rel.dual_dual a, Rel.dual_dual b]
  | .conv a => by simp [Rel.dual, Rel.dual_dual a]
  | .call _ => rfl

theorem _root_.RwLog.R001.Goal.dual_dual (g : Goal) : g.dual.dual = g := by
  obtain ⟨lb, e, rb⟩ := g
  simp [Goal.dual, Option.map_map, Function.comp_def, Rel.dual_dual]

/-! ## Mirroring and the canonical form -/

theorem orBranches_dual : ∀ e : Rel, orBranches e.dual = (orBranches e).map Rel.dual
  | .or a b => by simp [Rel.dual, orBranches, orBranches_dual a, orBranches_dual b]
  | .zero | .span _ | .and _ _ | .seq _ _ | .conv _ | .call _ => rfl

theorem notOr_canon_of_notOr {e : Rel} (h : NotOr e) : NotOr (canon e) := by
  cases e with
  | or a b => exact absurd rfl (h a b)
  | _ => intro a b h; simp [canon] at h

/-- The non-`0` branches of a canonical form are the canonical forms of the
branches. -/
theorem mem_orBranches_canon : ∀ (E : Rel) {z : Rel}, z ≠ .zero →
    (z ∈ orBranches (canon E) ↔ ∃ l ∈ orBranches E, canon l = z)
  | .or a b, z, hz => by
    rw [mem_orBranches_canon_or hz, mem_orBranches_canon a hz, mem_orBranches_canon b hz]
    simp only [orBranches, List.mem_append]
    constructor
    · rintro (⟨l, hl, e⟩ | ⟨l, hl, e⟩)
      · exact ⟨l, .inl hl, e⟩
      · exact ⟨l, .inr hl, e⟩
    · rintro ⟨l, hl | hl, e⟩
      · exact .inl ⟨l, hl, e⟩
      · exact .inr ⟨l, hl, e⟩
  | .zero, z, hz | .span _, z, hz | .and _ _, z, hz | .seq _ _, z, hz | .conv _, z, hz
  | .call _, z, hz => by
    rw [orBranches_notOr (notOr_canon_of_notOr (fun a b h => by cases h))]
    simp [orBranches, eq_comm]

theorem sortedBranches_idem (xs : List Rel) :
    sortedBranches (sortedBranches xs) = sortedBranches xs :=
  sortedBranches_eq fun z hz => by rw [mem_sortedBranches]; simp [hz]

/-- A canonical form is determined by its non-`0` branches. -/
theorem canon_eq_mkOr (E : Rel) : canon E = mkOr (sortedBranches (orBranches (canon E))) := by
  cases E with
  | or a b =>
    conv => lhs; rw [canon]
    rw [show canon (.or a b) = mkOr (sortedBranches (orBranches (canon a) ++ orBranches (canon b)))
      from rfl]
    congr 1
    have hno : ∀ x ∈ sortedBranches (orBranches (canon a) ++ orBranches (canon b)), NotOr x := by
      intro x hx
      rw [mem_sortedBranches, List.mem_append] at hx
      exact hx.1.elim notOr_of_mem_orBranches notOr_of_mem_orBranches
    refine sortedBranches_eq fun z hz => ?_
    rw [mem_orBranches_mkOr hno z hz, mem_sortedBranches]
    simp [hz]
  | _ =>
    rw [orBranches_notOr (notOr_canon_of_notOr (fun a b h => by cases h))]
    generalize hc : canon _ = c
    by_cases h0 : c = .zero
    · subst h0; simp [sortedBranches, mkOr]
    · have : sortedBranches [c] = [c] := by
        simp [sortedBranches, h0, List.eraseDups_cons]
      rw [this]; rfl

theorem canon_ext {E E' : Rel}
    (h : ∀ z, z ≠ .zero → (z ∈ orBranches (canon E) ↔ z ∈ orBranches (canon E'))) :
    canon E = canon E' := by
  rw [canon_eq_mkOr E, canon_eq_mkOr E', sortedBranches_eq h]

theorem sizeOf_lt_of_mem_orBranches {a b l : Rel} (h : l ∈ orBranches (.or a b)) :
    sizeOf l < sizeOf (Rel.or a b) := by
  have key : ∀ (e l : Rel), l ∈ orBranches e → sizeOf l ≤ sizeOf e := by
    intro e
    induction e with
    | or a b iha ihb =>
      intro l hl
      rw [orBranches, List.mem_append] at hl
      rcases hl with hl | hl
      · have := iha l hl; simp; omega
      · have := ihb l hl; simp; omega
    | _ => intro l hl; simp only [orBranches, List.mem_singleton] at hl; subst hl; exact le_rfl
  rw [orBranches, List.mem_append] at h
  rcases h with h | h
  · have := key a l h; simp; omega
  · have := key b l h; simp; omega

theorem canon_idem : ∀ e : Rel, canon (canon e) = canon e
  | .zero => rfl
  | .span _ => rfl
  | .call _ => rfl
  | .and a b => by simp only [canon, canon_idem a, canon_idem b]
  | .seq a b => by simp only [canon, canon_idem a, canon_idem b]
  | .conv a => by simp only [canon, canon_idem a]
  | .or a b => by
    refine canon_ext fun z hz => ?_
    rw [mem_orBranches_canon _ hz]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x ≠ .zero := by rintro rfl; exact hz rfl
      obtain ⟨l, hl, rfl⟩ := (mem_orBranches_canon _ hx0).1 hx
      have := sizeOf_lt_of_mem_orBranches hl
      rw [canon_idem l]
      exact hx
    · intro h
      obtain ⟨l, hl, rfl⟩ := (mem_orBranches_canon _ hz).1 h
      have := sizeOf_lt_of_mem_orBranches hl
      exact ⟨canon l, h, canon_idem l⟩
termination_by e => sizeOf e
decreasing_by all_goals first | exact this | (simp_wf; try omega)

theorem dual_zero_iff {e : Rel} : e.dual = .zero ↔ e = .zero := by
  cases e <;> simp [Rel.dual]

theorem canon_dual : ∀ e : Rel, canon e.dual = canon (canon e).dual
  | .zero => rfl
  | .span _ => rfl
  | .call _ => rfl
  | .and a b => by simp only [Rel.dual, canon, canon_dual a, canon_dual b]
  | .seq a b => by simp only [Rel.dual, canon, canon_dual a, canon_dual b]
  | .conv a => by simp only [Rel.dual, canon, canon_dual a]
  | .or a b => by
    refine canon_ext fun z hz => ?_
    rw [mem_orBranches_canon _ hz, mem_orBranches_canon _ hz, orBranches_dual, orBranches_dual]
    simp only [List.mem_map, exists_exists_and_eq_and]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have := sizeOf_lt_of_mem_orBranches hl
      have hl0 : canon l ≠ .zero := by
        intro h0; apply hz; rw [canon_dual l, h0]; rfl
      exact ⟨canon l, (mem_orBranches_canon _ hl0).2 ⟨l, hl, rfl⟩, (canon_dual l).symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x ≠ .zero := by rintro rfl; exact hz rfl
      obtain ⟨l, hl, rfl⟩ := (mem_orBranches_canon _ hx0).1 hx
      have := sizeOf_lt_of_mem_orBranches hl
      exact ⟨l, hl, canon_dual l⟩
termination_by e => sizeOf e
decreasing_by all_goals first | exact this | (simp_wf; try omega)

/-! ## Keys of mirrored goals -/

theorem stripConv_conv (lb rb : Option Span) (a : Rel) :
    Goal.stripConv ⟨lb, .conv a, rb⟩ =
      (!(Goal.stripConv ⟨rb.map Span.swap, a, lb.map Span.swap⟩).1,
        (Goal.stripConv ⟨rb.map Span.swap, a, lb.map Span.swap⟩).2) := by
  rw [Goal.stripConv]

theorem stripConv_other (lb rb : Option Span) (e : Rel) (h : ∀ a, e ≠ .conv a) :
    Goal.stripConv ⟨lb, e, rb⟩ = (false, ⟨lb, e, rb⟩) := by
  cases e with
  | conv a => exact absurd rfl (h a)
  | _ => rw [Goal.stripConv]; simp

theorem stripConv_dual : ∀ (C : Rel) (lb rb : Option Span),
    Goal.stripConv ⟨rb.map Span.swap, canon C.dual, lb.map Span.swap⟩ =
      let r := Goal.stripConv ⟨lb, C, rb⟩
      let r' := Goal.stripConv ⟨r.2.rb.map Span.swap, canon r.2.e.dual, r.2.lb.map Span.swap⟩
      (r.1 ^^ r'.1, r'.2)
  | .conv a, lb, rb => by
    have ih := stripConv_dual a (rb.map Span.swap) (lb.map Span.swap)
    simp only [Option.map_map, Function.comp_def, Span.swap_swap, Option.map_id'] at ih
    simp only [Rel.dual, canon, stripConv_conv, Option.map_map, Function.comp_def, Span.swap_swap,
      Option.map_id', ih]
    cases (Goal.stripConv ⟨rb.map Span.swap, a, lb.map Span.swap⟩).1 <;> simp
  | .zero, lb, rb | .span _, lb, rb | .or _ _, lb, rb | .and _ _, lb, rb | .seq _ _, lb, rb
  | .call _, lb, rb => by
    rw [stripConv_other lb rb _ (fun a h => by cases h)]
    simp

theorem norm_dual (g : Goal) :
    g.dual.norm = (g.norm.1 ^^ g.norm.2.dual.norm.1, g.norm.2.dual.norm.2) := by
  simp only [Goal.norm, Goal.dual]
  rw [canon_dual, stripConv_dual]

theorem stripConv_same : ∀ (C : Rel) {lb lb' rb rb' : Option Span},
    boundEq lb lb' = true → boundEq rb rb' = true →
    (Goal.stripConv ⟨lb, C, rb⟩).1 = (Goal.stripConv ⟨lb', C, rb'⟩).1 ∧
      (Goal.stripConv ⟨lb, C, rb⟩).2.same (Goal.stripConv ⟨lb', C, rb'⟩).2 = true
  | .conv a, lb, lb', rb, rb', hl, hr => by
    rw [stripConv_conv, stripConv_conv]
    have := stripConv_same a (lb := rb.map Span.swap) (lb' := rb'.map Span.swap)
      (rb := lb.map Span.swap) (rb' := lb'.map Span.swap) (by rwa [boundEq_swap])
      (by rwa [boundEq_swap])
    exact ⟨by rw [this.1], this.2⟩
  | .zero, lb, lb', rb, rb', hl, hr | .span _, lb, lb', rb, rb', hl, hr
  | .or _ _, lb, lb', rb, rb', hl, hr | .and _ _, lb, lb', rb, rb', hl, hr
  | .seq _ _, lb, lb', rb, rb', hl, hr | .call _, lb, lb', rb, rb', hl, hr => by
    rw [stripConv_other _ _ _ (fun a h => by cases h), stripConv_other _ _ _ (fun a h => by cases h)]
    exact ⟨rfl, Goal.same_iff.2 ⟨rfl, hl, hr⟩⟩

theorem norm_same {g h : Goal} (e : g.same h = true) :
    g.norm.1 = h.norm.1 ∧ g.norm.2.same h.norm.2 = true := by
  rw [Goal.same_iff] at e
  obtain ⟨lb, eg, rb⟩ := g
  obtain ⟨lb', eh, rb'⟩ := h
  simp only at e
  obtain ⟨rfl, hl, hr⟩ := e
  exact stripConv_same _ hl hr


/-! ## Table keys -/

/-- A table key: a goal its own normal form (canonical, not a converse). -/
def IsKey (G : Goal) : Prop := G.norm = (false, G)

theorem stripConv_canonical : ∀ (C : Rel) (lb rb : Option Span), canon C = C →
    canon (Goal.stripConv ⟨lb, C, rb⟩).2.e = (Goal.stripConv ⟨lb, C, rb⟩).2.e ∧
      ∀ a, (Goal.stripConv ⟨lb, C, rb⟩).2.e ≠ .conv a
  | .conv a, lb, rb, h => by
    rw [stripConv_conv]
    simp only [canon, Rel.conv.injEq] at h
    exact stripConv_canonical a _ _ h
  | .zero, lb, rb, h | .span _, lb, rb, h | .or _ _, lb, rb, h | .and _ _, lb, rb, h
  | .seq _ _, lb, rb, h | .call _, lb, rb, h => by
    rw [stripConv_other _ _ _ (fun a h => by cases h)]
    exact ⟨h, fun a h => by cases h⟩

theorem isKey_of {G : Goal} (hc : canon G.e = G.e) (hn : ∀ a, G.e ≠ .conv a) : IsKey G := by
  obtain ⟨lb, e, rb⟩ := G
  simp only at hc hn
  simp only [IsKey, Goal.norm, hc, stripConv_other _ _ _ hn]

theorem IsKey.canonical {G : Goal} (h : IsKey G) : canon G.e = G.e ∧ ∀ a, G.e ≠ .conv a := by
  have := stripConv_canonical (canon G.e) G.lb G.rb (canon_idem _)
  unfold IsKey Goal.norm at h
  rw [h] at this
  exact this

theorem isKey_norm (g : Goal) : IsKey g.norm.2 := by
  have := stripConv_canonical (canon g.e) g.lb g.rb (canon_idem _)
  exact isKey_of this.1 this.2

theorem IsKey.norm_eq {G : Goal} (h : IsKey G) : G.norm = (false, G) := h

theorem canon_dual_canon (x : Rel) : canon (canon (canon x).dual).dual = canon x := by
  rw [← canon_dual x, ← canon_dual x.dual, Rel.dual_dual]

theorem mkOr_or : ∀ {S : List Rel} {a b : Rel}, mkOr S = .or a b → (∀ x ∈ S, NotOr x) →
    ∃ x y rest, S = x :: y :: rest
  | [], _, _, h, _ => by cases h
  | [x], a, b, h, hS => by simp only [mkOr] at h; exact absurd h (hS x (by simp) a b)
  | x :: y :: rest, _, _, _, _ => ⟨x, y, rest, rfl⟩

theorem two_le_length_of_mem {L : List Rel} (hL : L.Nodup) {x y : Rel} (hx : x ∈ L) (hy : y ∈ L)
    (hxy : x ≠ y) : ∃ u v rest, L = u :: v :: rest := by
  match L, hx, hy with
  | [], hx, _ => cases hx
  | [u], hx, hy => simp at hx hy; exact absurd (hx.trans hy.symm) hxy
  | u :: v :: rest, _, _ => exact ⟨u, v, rest, rfl⟩

/-- The mirror of a canonical `|` has at least two branches after
canonicalization. -/
theorem canon_dual_or_two {b c : Rel} (hc : canon (Rel.or b c) = Rel.or b c) :
    ∃ u v rest, sortedBranches (orBranches (canon (Rel.or b c).dual)) = u :: v :: rest := by
  -- the branches of `E` are canonical, nonzero and at least two
  have hE := hc
  rw [show canon (Rel.or b c) = mkOr (sortedBranches (orBranches (canon b) ++ orBranches (canon c)))
    from rfl] at hE
  have hT : ∀ x ∈ sortedBranches (orBranches (canon b) ++ orBranches (canon c)), NotOr x :=
    fun x hx => by
      rw [mem_sortedBranches, List.mem_append] at hx
      exact hx.1.elim notOr_of_mem_orBranches notOr_of_mem_orBranches
  obtain ⟨x, y, rest, hxy⟩ := mkOr_or hE hT
  have hnd := (pairwise_sortedBranches (orBranches (canon b) ++ orBranches (canon c))).imp
    fun h => h.2
  rw [hxy] at hnd
  have hne : x ≠ y := (List.pairwise_cons.1 hnd).1 y (by simp)
  have hmem : ∀ z ∈ sortedBranches (orBranches (canon b) ++ orBranches (canon c)),
      z ≠ .zero ∧ canon z = z ∧ z ∈ orBranches (Rel.or b c |> canon) := by
    intro z hz
    have hz0 := (mem_sortedBranches.1 hz).2
    refine ⟨hz0, ?_, ?_⟩
    · obtain ⟨l, _, rfl⟩ := (mem_orBranches_canon (.or b c) hz0).1
        ((mem_orBranches_canon_or hz0).2 (List.mem_append.1 (mem_sortedBranches.1 hz).1))
      exact canon_idem l
    · rw [hc]; exact (mem_orBranches_canon_or hz0).2 (List.mem_append.1 (mem_sortedBranches.1 hz).1)
        |> fun h => by rw [← hc]; exact h
  have hx := hmem x (by rw [hxy]; simp)
  have hy := hmem y (by rw [hxy]; simp)
  -- their mirrors are distinct non-`0` branches of the canonical mirror
  have himg : ∀ z, z ≠ .zero ∧ canon z = z ∧ z ∈ orBranches (canon (Rel.or b c)) →
      canon z.dual ≠ .zero ∧ canon z.dual ∈ sortedBranches (orBranches (canon (Rel.or b c).dual)) := by
    rintro z ⟨hz0, hzc, hz⟩
    have h0 : canon z.dual ≠ .zero := by
      intro h0
      apply hz0
      rw [← hzc, ← canon_dual_canon z, ← canon_dual z, h0]; rfl
    refine ⟨h0, mem_sortedBranches.2 ⟨?_, h0⟩⟩
    rw [mem_orBranches_canon _ h0, orBranches_dual]
    rw [hc] at hz
    exact ⟨z.dual, List.mem_map.2 ⟨z, hz, rfl⟩, rfl⟩
  have hx' := himg x hx
  have hy' := himg y hy
  have hne' : canon x.dual ≠ canon y.dual := by
    intro e
    apply hne
    rw [← hx.2.1, ← hy.2.1, ← canon_dual_canon x, ← canon_dual_canon y, ← canon_dual x,
      ← canon_dual y, e]
  have hnd' := (pairwise_sortedBranches (orBranches (canon (Rel.or b c).dual))).imp fun h => h.2
  exact two_le_length_of_mem hnd' hx'.2 hy'.2 hne'

/-- The mirror of a canonical non-converse expression is not a converse after
canonicalization: so the key of a mirrored key carries no orientation. -/
theorem canon_dual_not_conv {E : Rel} (hc : canon E = E) (hn : ∀ a, E ≠ .conv a) :
    ∀ a, canon E.dual ≠ .conv a := by
  intro a h
  cases E with
  | conv b => exact hn b rfl
  | zero | span _ | and _ _ | seq _ _ | call _ => simp [Rel.dual, canon] at h
  | or b c =>
    rw [canon_eq_mkOr (Rel.or b c).dual] at h
    obtain ⟨u, v, rest', hl⟩ := canon_dual_or_two hc
    rw [hl] at h
    cases h

end Symmetry

end R001

end RwLog
