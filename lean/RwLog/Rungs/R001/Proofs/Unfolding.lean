/-
# Rung R001: what the unfolding strategy keeps

The unfolding strategy of a goal asks rung zero whether round `d` of the
goal's expression is final (`unfoldFinal`). Three facts about that test:

* `final_mono`: a final round stays final at every later depth. Unfolding once
  more replaces calls by bodies; a product without calls is left as it is, and
  a product that fused to nothing still fuses to nothing, because the spans at
  the ends of a product only get composed with more (`E`).
* `unfoldFinal_same`: goals that share a table (`GoalOf.same`) are final at the
  same depths.
* `roundFinal_key`: a query and its table key are final at the same depths.
-/
import RwLog.Rungs.R001.Proofs.SymmetryUnfold
import RwLog.Rungs.R001.Proofs.Tier0

namespace RwLog

namespace R001

namespace Unf

open R000 Symmetry

/-! ## One more unfolding refines the products -/

/-- The last factor after unfolding: a span stays a span, composed with more on
its left. -/
def LastR (x x' : Rel) : Prop :=
  ∀ a, x = .span a → ∃ a' X, x' = .span a' ∧ a'.den = GRel.comp X a.den

/-- The first factor after unfolding: a span stays a span, composed with more
on its right. -/
def HeadR (y y' : Rel) : Prop :=
  ∀ b, y = .span b → ∃ b' Y, y' = .span b' ∧ b'.den = (b.den).comp Y

/-- `p'` is a product of the unfolded expression that comes from the product
`p`: it is `p` when `p` has no call, and the spans at the ends of `p` are still
there, composed with more. -/
structure E (p p' : List Rel) : Prop where
  same : (∀ f ∈ p, f.calls = []) → p' = p
  last : ∀ A x, p = A ++ [x] → ∃ A' x', p' = A' ++ [x'] ∧ LastR x x'
  head : ∀ y B, p = y :: B → ∃ y' B', p' = y' :: B' ∧ HeadR y y'

theorem LastR.refl (x : Rel) : LastR x x :=
  fun a h => ⟨a, GRel.id, h, (GRel.id_comp _).symm⟩

theorem HeadR.refl (x : Rel) : HeadR x x :=
  fun a h => ⟨a, GRel.id, h, (GRel.comp_id _).symm⟩

theorem E.refl (p : List Rel) : E p p :=
  ⟨fun _ => rfl, fun A x h => ⟨A, x, h, LastR.refl x⟩, fun y B h => ⟨y, B, h, HeadR.refl y⟩⟩

theorem LastR.extend {z x z' : Rel} (h : LastR z x)
    (hz : z' = x ∨ ∃ a₁ b₁ c' : Span, x = .span b₁ ∧ z' = .span c' ∧
      c'.den = (a₁.den).comp b₁.den) : LastR z z' := by
  rcases hz with rfl | ⟨a₁, b₁, c', rfl, rfl, hc⟩
  · exact h
  · intro zz hzz
    obtain ⟨a₂, X₂, e, hd⟩ := h zz hzz
    cases e
    exact ⟨c', (a₁.den).comp X₂, rfl, by rw [hc, hd, GRel.comp_assoc]⟩

theorem HeadR.extend {z y z' : Rel} (h : HeadR z y)
    (hz : z' = y ∨ ∃ a₁ b₁ c' : Span, y = .span a₁ ∧ z' = .span c' ∧
      c'.den = (a₁.den).comp b₁.den) : HeadR z z' := by
  rcases hz with rfl | ⟨a₁, b₁, c', rfl, rfl, hc⟩
  · exact h
  · intro zz hzz
    obtain ⟨b₂, Y₂, e, hd⟩ := h zz hzz
    cases e
    exact ⟨c', Y₂.comp b₁.den, rfl, by rw [hc, hd, GRel.comp_assoc]⟩

theorem mid_nonempty {X A B Y : GRel} (h : ((X.comp A).comp (B.comp Y)).Nonempty) :
    (A.comp B).Nonempty := by
  obtain ⟨t, m, S₁, S₂, ⟨m₁, T₁, T₂, -, hA, -⟩, ⟨m₂, U₁, U₂, hB, -, -⟩, -⟩ := h
  exact ⟨(m₁, m₂, T₂ ∪ U₁), m, T₂, U₁, hA, hB, rfl⟩

theorem fuse_some_span {a b : Span} {F : List Rel} (h : fuse (.span a) (.span b) = some F) :
    ∃ c, a.compose b = some c ∧ F = [.span c] := by
  rw [fuse_span] at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨c, hc, rfl⟩

/-- The shape of a fusion of two end factors. -/
theorem fuse_cases {x y : Rel} {F : List Rel} (h : fuse x y = some F) :
    F = [x, y] ∨ ∃ a b c : Span, x = .span a ∧ y = .span b ∧ a.compose b = some c ∧
      F = [.span c] := by
  rcases spanOr x with ⟨a, rfl⟩ | hx
  · rcases spanOr y with ⟨b, rfl⟩ | hy
    · obtain ⟨c, hc, rfl⟩ := fuse_some_span h
      exact .inr ⟨a, b, c, rfl, rfl, hc, rfl⟩
    · rw [fuse_right hy] at h; cases h; exact .inl rfl
  · rw [fuse_left hx] at h; cases h; exact .inl rfl

theorem join_some {A B : List Rel} {x y : Rel} {p : List Rel}
    (h : joinSeq (A ++ [x]) (y :: B) = some p) : ∃ F, fuse x y = some F ∧ p = A ++ F ++ B := by
  rw [joinSeq_fuse] at h
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨F, hF, rfl⟩

theorem concat_inj {α : Type} {A B : List α} {x y : α} (h : A ++ [x] = B ++ [y]) :
    A = B ∧ x = y := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  exact ⟨h1, by simpa using h2⟩

theorem exists_concat {α : Type} {l : List α} (h : l ≠ []) : ∃ A x, l = A ++ [x] := by
  rcases List.eq_nil_or_concat l with e | ⟨A, x, e⟩
  · exact absurd e h
  · exact ⟨A, x, by rw [e, List.concat_eq_append]⟩

/-- The last factor of a join, on the unfolded side. -/
theorem join_last' {A' A'' : List Rel} {x' x'' : Rel} {pb' p' : List Rel}
    (h : joinSeq (A' ++ [x']) pb' = some p') (hb : pb' = A'' ++ [x'']) :
    ∃ P' z', p' = P' ++ [z'] ∧ (z' = x'' ∨ ∃ a₁ b₁ c' : Span, x'' = .span b₁ ∧ z' = .span c' ∧
      c'.den = (a₁.den).comp b₁.den) := by
  subst hb
  cases A'' with
  | nil =>
    obtain ⟨F, hF, rfl⟩ := join_some (B := []) h
    rcases fuse_cases hF with rfl | ⟨a, b, c, rfl, rfl, hc, rfl⟩
    · exact ⟨A' ++ [x'], x'', by simp, .inl rfl⟩
    · exact ⟨A', .span c, by simp, .inr ⟨a, b, c, rfl, rfl, compose_some hc⟩⟩
  | cons y' A₂ =>
    obtain ⟨F, -, rfl⟩ := join_some (B := A₂ ++ [x'']) h
    exact ⟨A' ++ F ++ A₂, x'', by simp, .inl rfl⟩

/-- The first factor of a join, on the unfolded side. -/
theorem join_head' {B' B'' : List Rel} {y' y'' : Rel} {pa' p' : List Rel}
    (h : joinSeq pa' (y' :: B') = some p') (ha : pa' = y'' :: B'') :
    ∃ z' P', p' = z' :: P' ∧ (z' = y'' ∨ ∃ a₁ b₁ c' : Span, y'' = .span a₁ ∧ z' = .span c' ∧
      c'.den = (a₁.den).comp b₁.den) := by
  subst ha
  obtain ⟨A', x', e⟩ := exists_concat (l := y'' :: B'') (by simp)
  rw [e] at h
  obtain ⟨F, hF, rfl⟩ := join_some h
  cases A' with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rcases fuse_cases hF with rfl | ⟨a, b, c, rfl, rfl, hc, rfl⟩
    · exact ⟨_, _, rfl, .inl rfl⟩
    · exact ⟨.span c, B', rfl, .inr ⟨a, b, c, rfl, rfl, compose_some hc⟩⟩
  | cons h₀ A₂ =>
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact ⟨_, _, rfl, .inl rfl⟩

/-- The last factor of a join, on the original side. -/
theorem join_last {A B A₀ : List Rel} {x y z : Rel} {p : List Rel}
    (h : joinSeq (A ++ [x]) (y :: B) = some p) (hp : p = A₀ ++ [z]) :
    (∃ Bp, y :: B = Bp ++ [z]) ∨
      ∃ a b c : Span, x = .span a ∧ y = .span b ∧ B = [] ∧ z = .span c ∧ a.compose b = some c := by
  obtain ⟨F, hF, rfl⟩ := join_some h
  by_cases hB : B = []
  · subst hB
    rcases fuse_cases hF with rfl | ⟨a, b, c, rfl, rfl, hc, rfl⟩
    · have : (A ++ [x]) ++ [y] = A₀ ++ [z] := by simpa using hp
      obtain ⟨-, rfl⟩ := concat_inj this
      exact .inl ⟨[], rfl⟩
    · have : A ++ [RelOf.span c] = A₀ ++ [z] := by simpa using hp
      obtain ⟨-, rfl⟩ := concat_inj this
      exact .inr ⟨a, b, c, rfl, rfl, rfl, rfl, hc⟩
  · obtain ⟨B₁, w, rfl⟩ := exists_concat hB
    have : (A ++ F ++ B₁) ++ [w] = A₀ ++ [z] := by simpa using hp
    obtain ⟨-, rfl⟩ := concat_inj this
    exact .inl ⟨y :: B₁, rfl⟩

/-- The first factor of a join, on the original side. -/
theorem join_head {A B P₀ : List Rel} {x y z : Rel} {p : List Rel}
    (h : joinSeq (A ++ [x]) (y :: B) = some p) (hp : p = z :: P₀) :
    (∃ Ap, A ++ [x] = z :: Ap) ∨
      ∃ a b c : Span, A = [] ∧ x = .span a ∧ y = .span b ∧ z = .span c ∧ a.compose b = some c := by
  obtain ⟨F, hF, rfl⟩ := join_some h
  cases A with
  | nil =>
    rcases fuse_cases hF with rfl | ⟨a, b, c, rfl, rfl, hc, rfl⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      exact .inl ⟨[], rfl⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      exact .inr ⟨a, b, c, rfl, rfl, rfl, rfl, hc⟩
  | cons h₀ A₂ =>
    simp only [List.cons_append, List.cons.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    exact .inl ⟨A₂ ++ [x], rfl⟩

theorem join_calls {A B : List Rel} {x y : Rel} {p : List Rel}
    (h : joinSeq (A ++ [x]) (y :: B) = some p) (hp : ∀ f ∈ p, f.calls = []) :
    (∀ f ∈ A ++ [x], f.calls = []) ∧ ∀ f ∈ y :: B, f.calls = [] := by
  obtain ⟨F, hF, rfl⟩ := join_some h
  rcases fuse_cases hF with rfl | ⟨a, b, c, rfl, rfl, hc, rfl⟩
  · constructor
    · intro f hf
      refine hp f ?_
      simp only [List.mem_append, List.mem_cons] at hf ⊢
      tauto
    · intro f hf
      refine hp f ?_
      simp only [List.mem_append, List.mem_cons] at hf ⊢
      tauto
  · constructor
    · intro f hf
      simp only [List.mem_append, List.mem_singleton] at hf
      rcases hf with hf | rfl
      · exact hp f (by simp [hf])
      · rfl
    · intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · rfl
      · exact hp f (by simp [hf])

/-- Joining products of the unfolded expression: the join comes from the join
of the products they come from. -/
theorem joinSeq_E {pa pb pa' pb' p' : List Rel} (Ea : E pa pa') (Eb : E pb pb')
    (hpa : pa ≠ []) (hpb : pb ≠ []) (h : joinSeq pa' pb' = some p') :
    ∃ p, joinSeq pa pb = some p ∧ E p p' := by
  obtain ⟨A, x, rfl⟩ := exists_concat hpa
  obtain ⟨y, B, rfl⟩ := List.exists_cons_of_ne_nil hpb
  obtain ⟨A', x', rfl, hlx⟩ := Ea.last A x rfl
  obtain ⟨y', B', rfl, hhy⟩ := Eb.head y B rfl
  -- the original products join
  have hex : ∃ p, joinSeq (A ++ [x]) (y :: B) = some p := by
    rw [joinSeq_fuse]
    rcases spanOr x with ⟨a, rfl⟩ | hx
    · rcases spanOr y with ⟨b, rfl⟩ | hy
      · obtain ⟨a', X, rfl, ha'⟩ := hlx a rfl
        obtain ⟨b', Y, rfl, hb'⟩ := hhy b rfl
        obtain ⟨F', hF', -⟩ := join_some h
        obtain ⟨c', hc', -⟩ := fuse_some_span hF'
        have hne : ((a.den).comp b.den).Nonempty := by
          have := c'.den_nonempty
          rw [compose_some hc', ha', hb'] at this
          exact mid_nonempty this
        obtain ⟨c, hc, -⟩ := compose_isSome hne
        exact ⟨_, by rw [fuse_span, hc]; rfl⟩
      · exact ⟨_, by rw [fuse_right hy]; rfl⟩
    · exact ⟨_, by rw [fuse_left hx]; rfl⟩
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · intro hcf
    obtain ⟨h1, h2⟩ := join_calls hp hcf
    rw [Ea.same h1, Eb.same h2, hp] at h
    exact (Option.some.inj h).symm
  · intro A₀ z hz
    rcases join_last hp hz with ⟨Bp, hBp⟩ | ⟨a, b, c, rfl, rfl, rfl, rfl, hc⟩
    · obtain ⟨A'', x'', e, hl⟩ := Eb.last Bp z hBp
      obtain ⟨P', z', e', hz'⟩ := join_last' h e
      exact ⟨P', z', e', hl.extend hz'⟩
    · have hsame : (y' :: B' : List Rel) = [.span b] :=
        Eb.same (by intro f hf; simp only [List.mem_singleton] at hf; subst hf; rfl)
      obtain ⟨a', X, rfl, ha'⟩ := hlx a rfl
      rw [hsame] at h
      obtain ⟨F', hF', rfl⟩ := join_some (B := []) h
      obtain ⟨c', hc', rfl⟩ := fuse_some_span hF'
      refine ⟨A', .span c', by simp, ?_⟩
      intro cc hcc
      cases hcc
      exact ⟨c', X, rfl, by rw [compose_some hc', ha', compose_some hc, GRel.comp_assoc]⟩
  · intro z P₀ hz
    rcases join_head hp hz with ⟨Ap, hAp⟩ | ⟨a, b, c, rfl, rfl, rfl, rfl, hc⟩
    · obtain ⟨y'', B'', e, hh⟩ := Ea.head z Ap hAp
      obtain ⟨z', P', e', hz'⟩ := join_head' h e
      exact ⟨z', P', e', hh.extend hz'⟩
    · have hsame : (A' ++ [x'] : List Rel) = [.span a] :=
        Ea.same (by intro f hf; simp only [List.nil_append, List.mem_singleton] at hf; subst hf; rfl)
      obtain ⟨b', Y, rfl, hb'⟩ := hhy b rfl
      rw [hsame] at h
      obtain ⟨F', hF', rfl⟩ := join_some (A := []) h
      obtain ⟨c', hc', rfl⟩ := fuse_some_span hF'
      refine ⟨.span c', B', by simp, ?_⟩
      intro cc hcc
      cases hcc
      exact ⟨c', Y, rfl, by rw [compose_some hc', hb', compose_some hc, GRel.comp_assoc]⟩

theorem E.calls_iff {p : List Rel} : (toRel p).calls = [] ↔ ∀ f ∈ p, f.calls = [] := calls_toRel p

/-- Conjoining products of the unfolded expression. -/
theorem mkAnd_E {pa pb pa' pb' p' : List Rel} (Ea : E pa pa') (Eb : E pb pb')
    (h : mkAnd pa' pb' = some p') : ∃ p, mkAnd pa pb = some p ∧ E p p' := by
  by_cases hs : isSingleSpan pa = false ∨ isSingleSpan pb = false
  · refine ⟨_, mkAnd_other hs, ?_, ?_, ?_⟩
    · intro hcf
      have hc := hcf _ (List.mem_singleton_self _)
      simp only [RelOf.calls, List.append_eq_nil_iff] at hc
      rw [Ea.same ((calls_toRel pa).1 hc.1), Eb.same ((calls_toRel pb).1 hc.2), mkAnd_other hs] at h
      exact (Option.some.inj h).symm
    · intro A x hx
      have : ([] : List Rel) ++ [RelOf.and (toRel pa) (toRel pb)] = A ++ [x] := hx
      obtain ⟨-, rfl⟩ := concat_inj this
      obtain ⟨P', z', e⟩ := exists_concat (mkAnd_ne_nil h)
      exact ⟨P', z', e, fun a ha => by cases ha⟩
    · intro y B hy
      simp only [List.cons.injEq] at hy
      obtain ⟨rfl, -⟩ := hy
      obtain ⟨z', P', e⟩ := List.exists_cons_of_ne_nil (mkAnd_ne_nil h)
      exact ⟨z', P', e, fun a ha => by cases ha⟩
  · simp only [not_or, Bool.not_eq_false] at hs
    obtain ⟨a, rfl⟩ := eq_single_of_isSingleSpan hs.1
    obtain ⟨b, rfl⟩ := eq_single_of_isSingleSpan hs.2
    have ha : pa' = [.span a] :=
      Ea.same (by intro f hf; simp only [List.mem_singleton] at hf; subst hf; rfl)
    have hb : pb' = [.span b] :=
      Eb.same (by intro f hf; simp only [List.mem_singleton] at hf; subst hf; rfl)
    subst ha hb
    exact ⟨p', h, E.refl p'⟩

variable (P : Program)

/-- Every product of the unfolded expression comes from a product of the
expression. -/
theorem unfold_E : ∀ (neg : Bool) (e : Rel), ∀ p' ∈ norm neg (unfold P e),
    ∃ p ∈ norm neg e, E p p'
  | _, .zero, p', hp' => by simp [unfold, norm] at hp'
  | neg, .span s, p', hp' => ⟨p', hp', E.refl p'⟩
  | neg, .or a b, p', hp' => by
    simp only [unfold, norm, List.mem_append] at hp' ⊢
    rcases hp' with hp' | hp'
    · obtain ⟨p, hp, e⟩ := unfold_E neg a p' hp'
      exact ⟨p, .inl hp, e⟩
    · obtain ⟨p, hp, e⟩ := unfold_E neg b p' hp'
      exact ⟨p, .inr hp, e⟩
  | false, .seq a b, p', hp' => by
    simp only [unfold, norm_seq, Bool.false_eq_true, ite_false] at hp' ⊢
    obtain ⟨pa', ha', pb', hb', hj⟩ := mem_seqP.1 hp'
    obtain ⟨pa, ha, ea⟩ := unfold_E false a pa' ha'
    obtain ⟨pb, hb, eb⟩ := unfold_E false b pb' hb'
    obtain ⟨p, hp, e⟩ := joinSeq_E ea eb (norm_ne_nil _ _ _ ha) (norm_ne_nil _ _ _ hb) hj
    exact ⟨p, mem_seqP.2 ⟨pa, ha, pb, hb, hp⟩, e⟩
  | true, .seq a b, p', hp' => by
    simp only [unfold, norm_seq, ite_true] at hp' ⊢
    obtain ⟨pb', hb', pa', ha', hj⟩ := mem_seqP.1 hp'
    obtain ⟨pa, ha, ea⟩ := unfold_E true a pa' ha'
    obtain ⟨pb, hb, eb⟩ := unfold_E true b pb' hb'
    obtain ⟨p, hp, e⟩ := joinSeq_E eb ea (norm_ne_nil _ _ _ hb) (norm_ne_nil _ _ _ ha) hj
    exact ⟨p, mem_seqP.2 ⟨pb, hb, pa, ha, hp⟩, e⟩
  | neg, .and a b, p', hp' => by
    simp only [unfold, norm_and] at hp' ⊢
    obtain ⟨pa', ha', pb', hb', hj⟩ := mem_andP.1 hp'
    obtain ⟨pa, ha, ea⟩ := unfold_E neg a pa' ha'
    obtain ⟨pb, hb, eb⟩ := unfold_E neg b pb' hb'
    obtain ⟨p, hp, e⟩ := mkAnd_E ea eb hj
    exact ⟨p, mem_andP.2 ⟨pa, ha, pb, hb, hp⟩, e⟩
  | neg, .conv a, p', hp' => by
    simp only [unfold, norm] at hp' ⊢
    exact unfold_E (!neg) a p' hp'
  | neg, .call n, p', hp' => by
    refine ⟨_, by simp only [norm]; exact List.mem_singleton_self _, ?_, ?_, ?_⟩
    · intro hcf
      have := hcf _ (List.mem_singleton_self _)
      cases neg <;> simp [RelOf.calls] at this
    · intro A x hx
      have hx' : ([] : List Rel) ++ [if neg then RelOf.conv (.call n) else .call n] = A ++ [x] := hx
      obtain ⟨-, rfl⟩ := concat_inj hx'
      obtain ⟨P', z', e⟩ := exists_concat (norm_ne_nil _ _ _ hp')
      exact ⟨P', z', e, fun a ha => by cases neg <;> simp at ha⟩
    · intro y B hy
      simp only [List.cons.injEq] at hy
      obtain ⟨rfl, -⟩ := hy
      obtain ⟨z', P', e⟩ := List.exists_cons_of_ne_nil (norm_ne_nil _ _ _ hp')
      exact ⟨z', P', e, fun a ha => by cases neg <;> simp at ha⟩

/-- A final round stays final one round later, with products among those it
had. -/
theorem final_succ {q : Rel} {k : Nat} (h : roundFinal P q k = true) :
    roundFinal P q (k + 1) = true ∧ ∀ p ∈ products P q (k + 1), p ∈ products P q k := by
  rw [roundFinal_iff] at h
  have key : ∀ p' ∈ products P q (k + 1), p' ∈ products P q k := by
    intro p' hp'
    have hp'' : p' ∈ norm false (unfold P (unfoldN P k q)) := by
      have : unfoldN P (k + 1) q = unfold P (unfoldN P k q) := Function.iterate_succ_apply' _ _ _
      rw [← this]; exact hp'
    obtain ⟨p, hp, e⟩ := unfold_E P false _ p' hp''
    rw [e.same ((calls_toRel p).1 (h p hp))]
    exact hp
  exact ⟨roundFinal_iff.2 fun p' hp' => h p' (key p' hp'), key⟩

theorem final_mono {q : Rel} {k : Nat} (h : roundFinal P q k = true) :
    ∀ k', k ≤ k' → roundFinal P q k' = true := by
  intro k' hk
  induction k' with
  | zero => rw [Nat.le_zero.1 hk] at h; exact h
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · exact (final_succ P (ih (by omega))).1
    · have : k = k' + 1 := by omega
      rw [this] at h; exact h

/-! ## Goals that share a table -/

theorem mk_rel {g h : Goal} (hs : g.same h = true) : Mk false P P g.rel h.rel := by
  obtain ⟨glb, ge, grb⟩ := g
  obtain ⟨hlb, he, hrb⟩ := h
  simp only [GoalOf.same, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨rfl, hl⟩, hr⟩ := hs
  have core : Mk false P P (GoalOf.rel ⟨none, ge, grb⟩) (GoalOf.rel ⟨none, ge, hrb⟩) := by
    cases grb with
    | none => cases hrb with
      | none => exact Mk.refl _
      | some _ => simp [boundEq] at hr
    | some r => cases hrb with
      | none => simp [boundEq] at hr
      | some r' => exact Mk.seq (m := false) (Mk.refl ge) (Mk.bound hr)
  cases glb with
  | none => cases hlb with
    | none => exact core
    | some _ => simp [boundEq] at hl
  | some l => cases hlb with
    | none => simp [boundEq] at hl
    | some l' =>
      cases grb <;> cases hrb <;> exact Mk.seq (m := false) (Mk.bound hl) core

/-- Goals that share a table are final at the same depths. -/
theorem unfoldFinal_same {g h : Goal} (hs : g.same h = true) (d : Nat) :
    unfoldFinal P d g = unfoldFinal P d h :=
  pcorr_final (mk_rel P hs false d)

theorem unfoldFinal_mono {g : Goal} {d : Nat} (h : unfoldFinal P d g = true) :
    ∀ d', d ≤ d' → unfoldFinal P d' g = true :=
  final_mono P h

/-! ## The table key of a query -/

theorem strip_root : ∀ (e : Rel) (k : Nat),
    ∃ e₀, (GoalOf.stripConv ⟨none, e, none⟩).2 = ⟨none, e₀, none⟩ ∧
      roundFinal P e₀ k = roundFinal P e k
  | .conv a, k => by
    rw [Tier0.strip_conv]
    obtain ⟨e₀, h1, h2⟩ := strip_root a k
    exact ⟨e₀, h1, by rw [h2, roundFinal_conv]⟩
  | .zero, k => ⟨_, by rw [Tier0.strip_nc _ (by simp)], rfl⟩
  | .span _, k => ⟨_, by rw [Tier0.strip_nc _ (by simp)], rfl⟩
  | .or _ _, k => ⟨_, by rw [Tier0.strip_nc _ (by simp)], rfl⟩
  | .and _ _, k => ⟨_, by rw [Tier0.strip_nc _ (by simp)], rfl⟩
  | .seq _ _, k => ⟨_, by rw [Tier0.strip_nc _ (by simp)], rfl⟩
  | .call _, k => ⟨_, by rw [Tier0.strip_nc _ (by simp)], rfl⟩

/-- A query and its table key are final at the same depths. -/
theorem unfoldFinal_key (q : Rel) (k : Nat) :
    unfoldFinal P k (GoalOf.norm ⟨none, q, none⟩).2 = roundFinal P q k := by
  obtain ⟨e₀, h1, h2⟩ := strip_root P (canon q) k
  have hn : (GoalOf.norm ⟨none, q, none⟩).2 = ⟨none, e₀, none⟩ := h1
  rw [hn]
  show roundFinal P e₀ k = _
  rw [h2]
  exact pcorr_final (mk_canon (Q := P) q false k)

end Unf

end R001

end RwLog
