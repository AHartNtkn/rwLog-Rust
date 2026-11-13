/-
# Rung R001, Symmetry: table keys of mirrored goals

* `GoalOf.same` is an equivalence relation, preserved by mirroring and by
  normalization.
* The canonical form is idempotent and commutes with mirroring up to
  canonicalization: `canon e.dual = canon (canon e).dual`.
* The key of a mirrored goal is the key of the mirror of its key:
  `g.dual.norm` is `g.norm.2.dual.norm`, with the orientations combined.
-/
import RwLog.Rungs.Tabled.Base.Proofs.Symmetry
import RwLog.Rungs.Tabled.Base.Proofs.SymmetryLists
import RwLog.Rungs.Framework.Direction

namespace RwLog

namespace R001

namespace Symmetry

/-! ## Boundaries and goals as table keys -/

theorem _root_.RwLog.R001.GoalOf.same_dual {g h : Goal} (e : g.same h = true) : g.dual.same h.dual = true := by
  rw [GoalOf.same_iff] at e ⊢
  simp only [GoalOf.dual, boundEq_swap]
  exact ⟨by rw [e.1], e.2.2, e.2.1⟩

theorem _root_.RwLog.R001.GoalOf.dual_dual (g : Goal) : g.dual.dual = g := by
  obtain ⟨lb, e, rb⟩ := g
  simp [GoalOf.dual, Option.map_map, Function.comp_def, RelOf.dual_dual]

/-! ## Mirroring and the canonical form -/

theorem orBranches_dual : ∀ e : Rel, orBranches e.dual = (orBranches e).map RelOf.dual
  | .or a b => by simp [RelOf.dual, orBranches, orBranches_dual a, orBranches_dual b]
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
    sizeOf l < sizeOf (RelOf.or a b) := by
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
  cases e <;> simp [RelOf.dual]

theorem canon_dual : ∀ e : Rel, canon e.dual = canon (canon e).dual
  | .zero => rfl
  | .span _ => rfl
  | .call _ => rfl
  | .and a b => by simp only [RelOf.dual, canon, canon_dual a, canon_dual b]
  | .seq a b => by simp only [RelOf.dual, canon, canon_dual a, canon_dual b]
  | .conv a => by simp only [RelOf.dual, canon, canon_dual a]
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
    GoalOf.stripConv ⟨lb, .conv a, rb⟩ =
      (!(GoalOf.stripConv ⟨rb.map Span.swap, a, lb.map Span.swap⟩).1,
        (GoalOf.stripConv ⟨rb.map Span.swap, a, lb.map Span.swap⟩).2) := by
  rw [GoalOf.stripConv]

theorem stripConv_other (lb rb : Option Span) (e : Rel) (h : ∀ a, e ≠ .conv a) :
    GoalOf.stripConv ⟨lb, e, rb⟩ = (false, ⟨lb, e, rb⟩) := by
  cases e with
  | conv a => exact absurd rfl (h a)
  | _ => rw [GoalOf.stripConv]; simp

theorem stripConv_dual : ∀ (C : Rel) (lb rb : Option Span),
    GoalOf.stripConv ⟨rb.map Span.swap, canon C.dual, lb.map Span.swap⟩ =
      let r := GoalOf.stripConv ⟨lb, C, rb⟩
      let r' := GoalOf.stripConv ⟨r.2.rb.map Span.swap, canon r.2.e.dual, r.2.lb.map Span.swap⟩
      (r.1 ^^ r'.1, r'.2)
  | .conv a, lb, rb => by
    have ih := stripConv_dual a (rb.map Span.swap) (lb.map Span.swap)
    simp only [Option.map_map, Function.comp_def, Span.swap_swap, Option.map_id'] at ih
    simp only [RelOf.dual, canon, stripConv_conv, Option.map_map, Function.comp_def, Span.swap_swap,
      Option.map_id', ih]
    cases (GoalOf.stripConv ⟨rb.map Span.swap, a, lb.map Span.swap⟩).1 <;> simp
  | .zero, lb, rb | .span _, lb, rb | .or _ _, lb, rb | .and _ _, lb, rb | .seq _ _, lb, rb
  | .call _, lb, rb => by
    rw [stripConv_other lb rb _ (fun a h => by cases h)]
    simp

theorem norm_dual (g : Goal) :
    g.dual.norm = (g.norm.1 ^^ g.norm.2.dual.norm.1, g.norm.2.dual.norm.2) := by
  simp only [GoalOf.norm, GoalOf.dual]
  rw [canon_dual, stripConv_dual]

theorem stripConv_same : ∀ (C : Rel) {lb lb' rb rb' : Option Span},
    boundEq lb lb' = true → boundEq rb rb' = true →
    (GoalOf.stripConv ⟨lb, C, rb⟩).1 = (GoalOf.stripConv ⟨lb', C, rb'⟩).1 ∧
      (GoalOf.stripConv ⟨lb, C, rb⟩).2.same (GoalOf.stripConv ⟨lb', C, rb'⟩).2 = true
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
    exact ⟨rfl, GoalOf.same_iff.2 ⟨rfl, hl, hr⟩⟩

theorem norm_same {g h : Goal} (e : g.same h = true) :
    g.norm.1 = h.norm.1 ∧ g.norm.2.same h.norm.2 = true := by
  rw [GoalOf.same_iff] at e
  obtain ⟨lb, eg, rb⟩ := g
  obtain ⟨lb', eh, rb'⟩ := h
  simp only at e
  obtain ⟨rfl, hl, hr⟩ := e
  exact stripConv_same _ hl hr


/-! ## Table keys -/

/-- A table key: a goal its own normal form (canonical, not a converse). -/
def IsKey (G : Goal) : Prop := G.norm = (false, G)

theorem stripConv_canonical : ∀ (C : Rel) (lb rb : Option Span), canon C = C →
    canon (GoalOf.stripConv ⟨lb, C, rb⟩).2.e = (GoalOf.stripConv ⟨lb, C, rb⟩).2.e ∧
      ∀ a, (GoalOf.stripConv ⟨lb, C, rb⟩).2.e ≠ .conv a
  | .conv a, lb, rb, h => by
    rw [stripConv_conv]
    simp only [canon, RelOf.conv.injEq] at h
    exact stripConv_canonical a _ _ h
  | .zero, lb, rb, h | .span _, lb, rb, h | .or _ _, lb, rb, h | .and _ _, lb, rb, h
  | .seq _ _, lb, rb, h | .call _, lb, rb, h => by
    rw [stripConv_other _ _ _ (fun a h => by cases h)]
    exact ⟨h, fun a h => by cases h⟩

theorem isKey_of {G : Goal} (hc : canon G.e = G.e) (hn : ∀ a, G.e ≠ .conv a) : IsKey G := by
  obtain ⟨lb, e, rb⟩ := G
  simp only at hc hn
  simp only [IsKey, GoalOf.norm, hc, stripConv_other _ _ _ hn]

theorem IsKey.canonical {G : Goal} (h : IsKey G) : canon G.e = G.e ∧ ∀ a, G.e ≠ .conv a := by
  have := stripConv_canonical (canon G.e) G.lb G.rb (canon_idem _)
  unfold IsKey GoalOf.norm at h
  rw [h] at this
  exact this

theorem isKey_norm (g : Goal) : IsKey g.norm.2 := by
  have := stripConv_canonical (canon g.e) g.lb g.rb (canon_idem _)
  exact isKey_of this.1 this.2

theorem IsKey.norm_eq {G : Goal} (h : IsKey G) : G.norm = (false, G) := h

theorem canon_dual_canon (x : Rel) : canon (canon (canon x).dual).dual = canon x := by
  rw [← canon_dual x, ← canon_dual x.dual, RelOf.dual_dual]

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
theorem canon_dual_or_two {b c : Rel} (hc : canon (RelOf.or b c) = RelOf.or b c) :
    ∃ u v rest, sortedBranches (orBranches (canon (RelOf.or b c).dual)) = u :: v :: rest := by
  -- the branches of `E` are canonical, nonzero and at least two
  have hE := hc
  rw [show canon (RelOf.or b c) = mkOr (sortedBranches (orBranches (canon b) ++ orBranches (canon c)))
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
      z ≠ .zero ∧ canon z = z ∧ z ∈ orBranches (RelOf.or b c |> canon) := by
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
  have himg : ∀ z, z ≠ .zero ∧ canon z = z ∧ z ∈ orBranches (canon (RelOf.or b c)) →
      canon z.dual ≠ .zero ∧ canon z.dual ∈ sortedBranches (orBranches (canon (RelOf.or b c).dual)) := by
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
  have hnd' := (pairwise_sortedBranches (orBranches (canon (RelOf.or b c).dual))).imp fun h => h.2
  exact two_le_length_of_mem hnd' hx'.2 hy'.2 hne'

/-- The mirror of a canonical non-converse expression is not a converse after
canonicalization: so the key of a mirrored key carries no orientation. -/
theorem canon_dual_not_conv {E : Rel} (hc : canon E = E) (hn : ∀ a, E ≠ .conv a) :
    ∀ a, canon E.dual ≠ .conv a := by
  intro a h
  cases E with
  | conv b => exact hn b rfl
  | zero | span _ | and _ _ | seq _ _ | call _ => simp [RelOf.dual, canon] at h
  | or b c =>
    rw [canon_eq_mkOr (RelOf.or b c).dual] at h
    obtain ⟨u, v, rest', hl⟩ := canon_dual_or_two hc
    rw [hl] at h
    cases h

end Symmetry

end R001

end RwLog
