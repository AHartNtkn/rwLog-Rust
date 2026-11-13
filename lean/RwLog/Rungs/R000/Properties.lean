/-
# Rung zero: the further naive-stage properties

* P1.4 (weak duality): running the converse of a query emits the swaps of
  the answers of the query, each answer of one run covered by an answer of
  the other, and the converse terminates exactly when the query does
  (`dual_answers`, `dual_terminates`).
* P1.1 (disjunct order independence): `a | b` and `b | a` emit the same
  answers and terminate together, and `|` is associative in the same sense
  (`or_comm_answers`, `or_comm_terminates`, `or_assoc_answers`,
  `or_assoc_terminates`).
* P2.3 (constraints never cause divergence): rung zero never consults the
  constraint theory, so its answers and its termination are the same under
  every theory (`theory_answers`, `theory_terminates`).

The duality proof has two halves. For answers, every span a product derives
is covered by a span the unnormalized expression derives (`norm_reflect`,
the converse of `norm_complete`), and derivations of a converse are swaps.
For termination, the products of `e` and of its converse correspond one to
one up to reversal (`norm_corr`): a fusion of two spans succeeds exactly when
the fusion of their swaps in the other order does, because every span has a
ground instance.
-/
import RwLog.Rungs.R000.Correct

namespace RwLog

namespace R000

variable {P : Program}

/-! ## Comparing runs through their rounds -/

theorem answers_congr {P' : Program} {q q' : Rel}
    (hf : ∀ k, roundFinal P q k = roundFinal P' q' k)
    (hs : ∀ k a, a ∈ roundSpans P q k ↔ a ∈ roundSpans P' q' k) :
    runtime.Answers P q = runtime.Answers P' q' := by
  ext a
  simp only [mem_answers, hf, hs]

theorem terminates_congr {P' : Program} {q q' : Rel}
    (hf : ∀ k, roundFinal P q k = roundFinal P' q' k) :
    runtime.Terminates P q ↔ runtime.Terminates P' q' := by
  simp only [terminates_iff, hf]

theorem unfoldN_or (k : Nat) (a b : Rel) :
    unfoldN P k (.or a b) = .or (unfoldN P k a) (unfoldN P k b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldN, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]; rfl

theorem unfoldN_conv (k : Nat) (a : Rel) : unfoldN P k (.conv a) = .conv (unfoldN P k a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldN, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]; rfl

/-! ## P1.1: disjunct order independence -/

theorem products_or (k : Nat) (a b : Rel) :
    products P (.or a b) k = products P a k ++ products P b k := by
  simp [products, unfoldN_or, norm]

theorem or_comm_answers (a b : Rel) :
    runtime.Answers P (.or a b) = runtime.Answers P (.or b a) :=
  answers_congr (fun k => by simp [roundFinal, products_or, Bool.and_comm])
    (fun k x => by simp [roundSpans, products_or, or_comm])

theorem or_comm_terminates (a b : Rel) :
    runtime.Terminates P (.or a b) ↔ runtime.Terminates P (.or b a) :=
  terminates_congr (fun k => by simp [roundFinal, products_or, Bool.and_comm])

theorem or_assoc_answers (a b c : Rel) :
    runtime.Answers P (.or (.or a b) c) = runtime.Answers P (.or a (.or b c)) :=
  answers_congr (fun k => by simp [roundFinal, products_or])
    (fun k x => by simp [roundSpans, products_or])

theorem or_assoc_terminates (a b c : Rel) :
    runtime.Terminates P (.or (.or a b) c) ↔ runtime.Terminates P (.or a (.or b c)) :=
  terminates_congr (fun k => by simp [roundFinal, products_or])

/-! ## P2.3: the constraint theory is never consulted -/

theorem unfold_theory (T : Theory) : unfold { P with theory := T } = unfold P := by
  funext e
  induction e <;> simp_all [unfold, Program.body]

theorem products_theory (T : Theory) (q : Rel) (k : Nat) :
    products { P with theory := T } q k = products P q k := by
  simp only [products, unfoldN, unfold_theory]

theorem theory_answers (T : Theory) (q : Rel) :
    runtime.Answers { P with theory := T } q = runtime.Answers P q :=
  answers_congr (fun k => by simp only [roundFinal, products_theory])
    (fun k a => by simp only [roundSpans, products_theory])

theorem theory_terminates (T : Theory) (q : Rel) :
    runtime.Terminates { P with theory := T } q ↔ runtime.Terminates P q :=
  terminates_congr (fun k => by simp only [roundFinal, products_theory])

/-! ## Products derive only what the expression derives -/

theorem joinSeq_split {n : Nat} {p q r : List Rel} {s : Span} (h : joinSeq p q = some r)
    (hd : DerivesN P n (toRel r) s) :
    ∃ s₁ s₂, DerivesN P n (toRel p) s₁ ∧ DerivesN P n (toRel q) s₂ ∧
      s.den = (s₁.den).comp s₂.den := by
  unfold joinSeq at h
  split at h
  · rename_i a b q' hl
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
    have hp : p = p.dropLast ++ [.span a] := (List.dropLast_append_getLast? _ hl).symm
    obtain ⟨sp, t, hsp, ht, hs⟩ := chain_split _ _ hd (Span.den_nonempty s)
    obtain ⟨sc, sq, hsc, hsq, ht'⟩ := chain_cons_split ht
    obtain rfl : sc = c := by cases hsc; rfl
    have hsub : s.den = ((sp.den).comp a.den).comp ((b.den).comp sq.den) := by
      rw [hs, ht', compose_some hc]
      simp only [GRel.comp_assoc]
    have hne : (((sp.den).comp a.den).comp ((b.den).comp sq.den)).Nonempty :=
      hsub ▸ Span.den_nonempty s
    obtain ⟨u, hu, hu'⟩ := chain_join p.dropLast [.span a] hsp (.span n a)
      (GRel.comp_nonempty_left hne)
    obtain ⟨v, hv, hv'⟩ := chain_cons_join (.span n b) hsq (GRel.comp_nonempty_right hne)
    exact ⟨u, v, by rw [hp]; exact hu, hv, by rw [hsub, hu', hv']⟩
  · cases h
    exact chain_split _ _ hd (Span.den_nonempty s)

theorem mkAnd_split {n : Nat} {p q r : List Rel} {s : Span} (h : mkAnd p q = some r)
    (hd : DerivesN P n (toRel r) s) :
    ∃ s₁ s₂, DerivesN P n (toRel p) s₁ ∧ DerivesN P n (toRel q) s₂ ∧
      s.den = (s₁.den).meet s₂.den := by
  unfold mkAnd at h
  split at h
  · rename_i a b
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
    cases hd
    exact ⟨a, b, .span n a, .span n b, meet_some hc⟩
  · cases h
    cases hd with
    | and h₁ h₂ hc => exact ⟨_, _, h₁, h₂, meet_some hc⟩

theorem inv_nonempty {R : GRel} (h : R.inv.Nonempty) : R.Nonempty := by
  obtain ⟨_, hx⟩ := h
  exact ⟨_, hx⟩

/-- Every span a product of `norm neg e` derives denotes what a span `e`
derives denotes, oriented by `neg`. The converse of `norm_complete`. -/
theorem norm_reflect {n : Nat} : ∀ (neg : Bool) (e : Rel), ∀ p ∈ norm neg e, ∀ s,
    DerivesN P n (toRel p) s → ∃ s', DerivesN P n e s' ∧ s.den = (orientS neg s').den
  | _, .zero, p, hp, _, _ => by simp [norm] at hp
  | neg, .span s, p, hp, t, ht => by
    simp only [norm, List.mem_singleton] at hp
    subst hp
    refine ⟨s, .span n s, ?_⟩
    cases neg <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ht <;> cases ht <;>
      simp [orientS]
  | neg, .or a b, p, hp, t, ht => by
    simp only [norm, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨s', h', hs⟩ := norm_reflect neg a p hp t ht
      exact ⟨s', .orl h', hs⟩
    · obtain ⟨s', h', hs⟩ := norm_reflect neg b p hp t ht
      exact ⟨s', .orr h', hs⟩
  | false, .seq a b, p, hp, t, ht => by
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    obtain ⟨s₁, s₂, h₁, h₂, hs⟩ := joinSeq_split hj ht
    obtain ⟨u₁, hu₁, hs₁⟩ := norm_reflect false a p₁ hp₁ s₁ h₁
    obtain ⟨u₂, hu₂, hs₂⟩ := norm_reflect false b p₂ hp₂ s₂ h₂
    simp only [orientS, Bool.false_eq_true, ite_false] at hs₁ hs₂ ⊢
    have hsub : t.den = (u₁.den).comp u₂.den := by rw [hs, hs₁, hs₂]
    obtain ⟨u, hu, hud⟩ := compose_isSome (hsub ▸ Span.den_nonempty t)
    exact ⟨u, .seq hu₁ hu₂ hu, by rw [hud]; exact hsub⟩
  | true, .seq a b, p, hp, t, ht => by
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    obtain ⟨s₁, s₂, h₁, h₂, hs⟩ := joinSeq_split hj ht
    obtain ⟨ub, hub, hs₁⟩ := norm_reflect true b p₁ hp₁ s₁ h₁
    obtain ⟨ua, hua, hs₂⟩ := norm_reflect true a p₂ hp₂ s₂ h₂
    simp only [orientS, ite_true, swap_den] at hs₁ hs₂ ⊢
    have hsub : t.den = ((ua.den).comp ub.den).inv := by
      rw [GRel.inv_comp, hs, hs₁, hs₂]
    obtain ⟨u, hu, hud⟩ := compose_isSome (inv_nonempty (hsub ▸ Span.den_nonempty t))
    exact ⟨u, .seq hua hub hu, by rw [hud]; exact hsub⟩
  | neg, .and a b, p, hp, t, ht => by
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    obtain ⟨s₁, s₂, h₁, h₂, hs⟩ := mkAnd_split hj ht
    obtain ⟨u₁, hu₁, hs₁⟩ := norm_reflect neg a p₁ hp₁ s₁ h₁
    obtain ⟨u₂, hu₂, hs₂⟩ := norm_reflect neg b p₂ hp₂ s₂ h₂
    have hsub : t.den = ((orientS neg u₁).den).meet (orientS neg u₂).den := by
      rw [hs, hs₁, hs₂]
    rw [orientS_den, orientS_den] at hsub
    cases neg
    · simp only [Bool.false_eq_true, ite_false] at hsub
      obtain ⟨u, hu, hud⟩ := meet_isSome (hsub ▸ Span.den_nonempty t)
      exact ⟨u, .and hu₁ hu₂ hu, by simp only [orientS, Bool.false_eq_true, ite_false]; rw [hud]; exact hsub⟩
    · simp only [ite_true] at hsub
      rw [← GRel.inv_meet] at hsub
      obtain ⟨u, hu, hud⟩ := meet_isSome (inv_nonempty (hsub ▸ Span.den_nonempty t))
      exact ⟨u, .and hu₁ hu₂ hu, by simp only [orientS, ite_true, swap_den]; rw [hud]; exact hsub⟩
  | neg, .conv a, p, hp, t, ht => by
    simp only [norm] at hp
    obtain ⟨s', h', hs⟩ := norm_reflect (!neg) a p hp t ht
    refine ⟨s'.swap, .conv h', ?_⟩
    have heq : orientS neg s'.swap = orientS (!neg) s' := by cases neg <;> rfl
    rw [heq]; exact hs
  | neg, .call m, p, hp, t, ht => by
    simp only [norm, List.mem_singleton] at hp
    subst hp
    cases neg
    · exact ⟨t, ht, rfl⟩
    · simp only [ite_true] at ht
      cases ht with
      | conv h => exact ⟨_, h, rfl⟩

/-! ## The products of an expression and of its converse correspond -/

/-- Whether an expression is a single span. -/
def _root_.RwLog.Rel.isSpan : Rel → Bool
  | .span _ => true
  | _ => false

/-- Corresponding factors of a product and of its converse: two spans whose
meanings are converse, or two factors that are not spans and that contain
calls on both sides or on neither. -/
inductive DE : Rel → Rel → Prop
  | span {a b : Span} : b.den = (a.den).inv → DE (.span a) (.span b)
  | other {x y : Rel} : x.isSpan = false → y.isSpan = false → (x.calls = [] ↔ y.calls = []) →
      DE x y

theorem DE.symm {x y : Rel} (h : DE x y) : DE y x := by
  cases h with
  | span h => exact .span (by rw [h, GRel.inv_inv])
  | other hx hy hc => exact .other hy hx hc.symm

theorem DE.calls {x y : Rel} (h : DE x y) : x.calls = [] ↔ y.calls = [] := by
  cases h with
  | span _ => simp [Rel.calls]
  | other _ _ hc => exact hc

/-- A product of an expression and a product of its converse correspond
when their factors correspond in reverse order. -/
def D (p p' : List Rel) : Prop := List.Forall₂ DE p p'.reverse

theorem D.symm {p p' : List Rel} (h : D p p') : D p' p := by
  unfold D at h ⊢
  rw [← List.forall₂_reverse_iff, List.reverse_reverse] at h
  exact List.Forall₂.flip (h.imp fun _ _ h => h.symm)

theorem calls_toRel (p : List Rel) : (toRel p).calls = [] ↔ ∀ x ∈ p, x.calls = [] := by
  induction p with
  | nil => simp [toRel, idRel, Rel.calls]
  | cons f p ih =>
    cases p with
    | nil => simp [toRel]
    | cons g p =>
      simp only [toRel, Rel.calls, List.append_eq_nil_iff] at ih ⊢
      rw [ih]
      simp

theorem forall₂_calls {l l' : List Rel} (h : List.Forall₂ DE l l') :
    (∀ x ∈ l, x.calls = []) ↔ (∀ y ∈ l', y.calls = []) := by
  induction h with
  | nil => simp
  | cons hxy _ ih => simp only [List.mem_cons, forall_eq_or_imp, hxy.calls, ih]

theorem D.calls {p p' : List Rel} (h : D p p') :
    (toRel p).calls = [] ↔ (toRel p').calls = [] := by
  rw [calls_toRel, calls_toRel, forall₂_calls h]
  simp

/-- An optional fusion result and an optional fusion result whose meaning is
the converse correspond: both fail or both succeed, with converse
meanings. -/
theorem opt_dual {o o' : Option Span} {R : GRel}
    (hn : o = none → R = ∅) (hs : ∀ c, o = some c → c.den = R)
    (hn' : o' = none → R.inv = ∅) (hs' : ∀ c, o' = some c → c.den = R.inv) :
    Option.Rel (fun c c' : Span => c'.den = (c.den).inv) o o' := by
  cases o with
  | none =>
    cases o' with
    | none => exact .none
    | some c' =>
      obtain ⟨x, hx⟩ := Span.den_nonempty c'
      rw [hs' c' rfl, hn rfl] at hx
      exact absurd hx (by simp [GRel.inv])
  | some c =>
    cases o' with
    | none =>
      obtain ⟨x, hx⟩ := Span.den_nonempty c
      rw [hs c rfl] at hx
      have : (x.2.1, x.1, x.2.2) ∈ R.inv := by simpa [GRel.inv] using hx
      rw [hn' rfl] at this
      exact this.elim
    | some c' => exact .some (by rw [hs' c' rfl, hs c rfl])

theorem compose_dual {a b a' b' : Span} (ha : a'.den = (a.den).inv) (hb : b'.den = (b.den).inv) :
    Option.Rel (fun c c' : Span => c'.den = (c.den).inv) (a.compose b) (b'.compose a') := by
  have key : (b'.den).comp a'.den = ((a.den).comp b.den).inv := by
    rw [ha, hb, GRel.inv_comp]
  exact opt_dual compose_none (fun _ h => compose_some h)
    (fun h => key ▸ compose_none h) (fun _ h => key ▸ compose_some h)

theorem meet_dual {a b a' b' : Span} (ha : a'.den = (a.den).inv) (hb : b'.den = (b.den).inv) :
    Option.Rel (fun c c' : Span => c'.den = (c.den).inv) (a.meet b) (a'.meet b') := by
  have key : (a'.den).meet b'.den = ((a.den).meet b.den).inv := by
    rw [ha, hb, GRel.inv_meet]
  exact opt_dual meet_none (fun _ h => meet_some h)
    (fun h => key ▸ meet_none h) (fun _ h => key ▸ meet_some h)

theorem forall₂_concat_left {A : List Rel} {x : Rel} {r : List Rel}
    (h : List.Forall₂ DE (A ++ [x]) r) :
    ∃ A' x', r = A' ++ [x'] ∧ List.Forall₂ DE A A' ∧ DE x x' := by
  rw [← List.forall₂_reverse_iff, List.reverse_append] at h
  obtain ⟨x', R, hx, hR, hr⟩ := List.forall₂_cons_left_iff.1 h
  refine ⟨R.reverse, x', List.reverse_eq_cons_iff.1 hr, ?_, hx⟩
  rw [← List.forall₂_reverse_iff, List.reverse_reverse]
  simpa using hR

theorem joinSeq_nofuse {p q : List Rel}
    (h : ∀ a b q', p.getLast? = some (.span a) → q = .span b :: q' → False) :
    joinSeq p q = some (p ++ q) := by
  unfold joinSeq
  split
  · rename_i a b q' hl
    exact (h a b q' hl rfl).elim
  · rfl

theorem joinSeq_nofuse' {A B : List Rel} {x y : Rel} (hxy : x.isSpan = false ∨ y.isSpan = false) :
    joinSeq (A ++ [x]) (y :: B) = some (A ++ [x] ++ y :: B) := by
  refine joinSeq_nofuse fun a b q' hl hq => ?_
  simp only [List.getLast?_concat, Option.some.injEq] at hl
  simp only [List.cons.injEq] at hq
  rcases hxy with h | h
  · rw [hl] at h; simp [Rel.isSpan] at h
  · rw [hq.1] at h; simp [Rel.isSpan] at h

theorem joinSeq_D_aux {pa ra pb rb : List Rel} (ha : List.Forall₂ DE pa ra)
    (hb : List.Forall₂ DE pb rb) :
    Option.Rel D (joinSeq pa pb) (joinSeq rb.reverse ra.reverse) := by
  rcases List.eq_nil_or_concat pa with rfl | ⟨A, x, rfl⟩
  · cases ha
    rw [joinSeq_nofuse (by simp), joinSeq_nofuse (by simp)]
    exact .some (by simpa [D] using hb)
  · rw [List.concat_eq_append] at ha
    obtain ⟨A', x', rfl, hA, hx⟩ := forall₂_concat_left ha
    cases hb with
    | nil =>
      rw [joinSeq_nofuse (by simp), joinSeq_nofuse (by simp)]
      exact .some (by simpa [D] using List.rel_append hA (.cons hx .nil))
    | @cons y y' B B' hy hB =>
      simp only [List.reverse_cons, List.reverse_append, List.reverse_nil, List.nil_append,
        List.singleton_append, List.concat_eq_append]
      have hD : ∀ u u', DE u u' → x.isSpan = false ∨ y.isSpan = false →
          x'.isSpan = false ∨ y'.isSpan = false → (u = x ∧ u' = x') →
          Option.Rel D (joinSeq (A ++ [x]) (y :: B)) (joinSeq (B'.reverse ++ [y']) (x' :: A'.reverse)) := by
        intro _ _ _ h₁ h₂ _
        rw [joinSeq_nofuse' h₁, joinSeq_nofuse' (h₂.symm)]
        refine .some ?_
        simp only [D, List.reverse_append, List.reverse_cons, List.reverse_reverse,
          List.nil_append, List.append_assoc, List.cons_append]
        exact List.rel_append hA (.cons hx (.cons hy hB))
      cases hx with
      | @span a a' hxa =>
        cases hy with
        | @span b b' hyb =>
          simp only [joinSeq, List.getLast?_concat, List.dropLast_concat]
          have hc := compose_dual hxa hyb
          revert hc
          cases a.compose b <;> cases b'.compose a' <;> intro hc <;> cases hc
          · exact .none
          · rename_i c c' hcc
            refine .some ?_
            simp only [D, List.reverse_append, List.reverse_cons, List.reverse_reverse,
              List.nil_append, List.append_assoc, List.cons_append]
            exact List.rel_append hA (.cons (.span hcc) hB)
        | other hy₁ hy₂ hyc =>
          exact hD _ _ (.span hxa) (.inr hy₁) (.inr hy₂) ⟨rfl, rfl⟩
      | other hx₁ hx₂ hxc =>
        exact hD _ _ (.other hx₁ hx₂ hxc) (.inl hx₁) (.inl hx₂) ⟨rfl, rfl⟩

theorem joinSeq_D {pa pa' pb pb' : List Rel} (ha : D pa pa') (hb : D pb pb') :
    Option.Rel D (joinSeq pa pb) (joinSeq pb' pa') := by
  have := joinSeq_D_aux ha hb
  rwa [List.reverse_reverse, List.reverse_reverse] at this

/-- Whether a product is a single span. -/
def isSingleSpan : List Rel → Bool
  | [x] => x.isSpan
  | _ => false

theorem D.isSingleSpan {p p' : List Rel} (h : D p p') : isSingleSpan p = isSingleSpan p' := by
  unfold D at h
  have hl := h.length_eq
  rw [List.length_reverse] at hl
  match p, p', h, hl with
  | [], [], _, _ => rfl
  | [x], [x'], h, _ =>
    simp only [List.reverse_singleton, List.forall₂_cons, List.Forall₂.nil, and_true] at h
    cases h with
    | span _ => rfl
    | other h₁ h₂ _ => simp [R000.isSingleSpan, h₁, h₂]
  | _ :: _ :: _, _ :: _ :: _, _, _ => rfl

theorem mkAnd_other {p q : List Rel} (h : isSingleSpan p = false ∨ isSingleSpan q = false) :
    mkAnd p q = some [.and (toRel p) (toRel q)] := by
  unfold mkAnd
  split
  · simp [isSingleSpan, Rel.isSpan] at h
  · rfl

theorem eq_single_of_isSingleSpan {p : List Rel} (h : isSingleSpan p = true) :
    ∃ a, p = [.span a] := by
  match p, h with
  | [.span a], _ => exact ⟨a, rfl⟩
  | [.zero], h | [.or _ _], h | [.and _ _], h | [.seq _ _], h | [.conv _], h | [.call _], h
  | [], h | _ :: _ :: _, h => simp [isSingleSpan, Rel.isSpan] at h

theorem mkAnd_D {p p' q q' : List Rel} (hp : D p p') (hq : D q q') :
    Option.Rel D (mkAnd p q) (mkAnd p' q') := by
  by_cases hs : isSingleSpan p = true ∧ isSingleSpan q = true
  · obtain ⟨a, rfl⟩ := eq_single_of_isSingleSpan hs.1
    obtain ⟨b, rfl⟩ := eq_single_of_isSingleSpan hs.2
    obtain ⟨a', rfl⟩ := eq_single_of_isSingleSpan (hp.isSingleSpan ▸ hs.1)
    obtain ⟨b', rfl⟩ := eq_single_of_isSingleSpan (hq.isSingleSpan ▸ hs.2)
    have ha : a'.den = (a.den).inv := by
      simp only [D, List.reverse_singleton, List.forall₂_cons, List.Forall₂.nil, and_true] at hp
      cases hp with
      | span h => exact h
      | other h => simp [Rel.isSpan] at h
    have hb : b'.den = (b.den).inv := by
      simp only [D, List.reverse_singleton, List.forall₂_cons, List.Forall₂.nil, and_true] at hq
      cases hq with
      | span h => exact h
      | other h => simp [Rel.isSpan] at h
    simp only [mkAnd]
    have hc := meet_dual ha hb
    revert hc
    cases a.meet b <;> cases a'.meet b' <;> intro hc <;> cases hc
    · exact .none
    · rename_i c c' hcc
      exact .some (by simp only [D, List.reverse_singleton]; exact .cons (.span hcc) .nil)
  · have h : isSingleSpan p = false ∨ isSingleSpan q = false := by
      cases h₁ : isSingleSpan p <;> cases h₂ : isSingleSpan q <;> simp_all
    have h' : isSingleSpan p' = false ∨ isSingleSpan q' = false := by
      rwa [← hp.isSingleSpan, ← hq.isSingleSpan]
    rw [mkAnd_other h, mkAnd_other h']
    refine .some ?_
    simp only [D, List.reverse_singleton]
    refine .cons (.other rfl rfl ?_) .nil
    simp only [Rel.calls, List.append_eq_nil_iff, hp.calls, hq.calls]

/-- Two lists of products correspond when each product of either has a
corresponding product in the other. -/
def Corr (L L' : List (List Rel)) : Prop :=
  (∀ p ∈ L, ∃ p' ∈ L', D p p') ∧ (∀ p' ∈ L', ∃ p ∈ L, D p p')

theorem Corr.symm {L L' : List (List Rel)} (h : Corr L L') : Corr L' L :=
  ⟨fun p' hp' => let ⟨p, hp, hd⟩ := h.2 p' hp'; ⟨p, hp, hd.symm⟩,
   fun p hp => let ⟨p', hp', hd⟩ := h.1 p hp; ⟨p', hp', hd.symm⟩⟩

theorem Corr.append {L₁ L₁' L₂ L₂' : List (List Rel)} (h₁ : Corr L₁ L₁') (h₂ : Corr L₂ L₂') :
    Corr (L₁ ++ L₂) (L₁' ++ L₂') := by
  constructor
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨p', hp', hd⟩ := h₁.1 p hp; exact ⟨p', List.mem_append_left _ hp', hd⟩
    · obtain ⟨p', hp', hd⟩ := h₂.1 p hp; exact ⟨p', List.mem_append_right _ hp', hd⟩
  · intro p' hp'
    rcases List.mem_append.1 hp' with hp' | hp'
    · obtain ⟨p, hp, hd⟩ := h₁.2 p' hp'; exact ⟨p, List.mem_append_left _ hp, hd⟩
    · obtain ⟨p, hp, hd⟩ := h₂.2 p' hp'; exact ⟨p, List.mem_append_right _ hp, hd⟩

theorem seq_corr {a b : Rel} (ha : Corr (norm false a) (norm true a))
    (hb : Corr (norm false b) (norm true b)) :
    Corr (norm false (.seq a b)) (norm true (.seq a b)) := by
  simp only [norm]
  constructor
  · intro r hr
    simp only [List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨pa, hpa, pb, hpb, hj⟩ := hr
    obtain ⟨pa', hpa', hda⟩ := ha.1 pa hpa
    obtain ⟨pb', hpb', hdb⟩ := hb.1 pb hpb
    have hrel := joinSeq_D hda hdb
    rw [hj] at hrel
    cases h' : joinSeq pb' pa' with
    | none => rw [h'] at hrel; cases hrel
    | some r' =>
      rw [h'] at hrel
      cases hrel with
      | some hd =>
        exact ⟨r', List.mem_flatMap.2 ⟨pb', hpb', List.mem_filterMap.2 ⟨pa', hpa', h'⟩⟩, hd⟩
  · intro r' hr'
    simp only [List.mem_flatMap, List.mem_filterMap] at hr'
    obtain ⟨pb', hpb', pa', hpa', hj⟩ := hr'
    obtain ⟨pa, hpa, hda⟩ := ha.2 pa' hpa'
    obtain ⟨pb, hpb, hdb⟩ := hb.2 pb' hpb'
    have hrel := joinSeq_D hda hdb
    rw [hj] at hrel
    cases h' : joinSeq pa pb with
    | none => rw [h'] at hrel; cases hrel
    | some r =>
      rw [h'] at hrel
      cases hrel with
      | some hd =>
        exact ⟨r, List.mem_flatMap.2 ⟨pa, hpa, List.mem_filterMap.2 ⟨pb, hpb, h'⟩⟩, hd⟩

theorem and_corr {neg : Bool} {a b : Rel} (ha : Corr (norm neg a) (norm (!neg) a))
    (hb : Corr (norm neg b) (norm (!neg) b)) :
    Corr (norm neg (.and a b)) (norm (!neg) (.and a b)) := by
  simp only [norm]
  constructor
  · intro r hr
    simp only [List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨pa, hpa, pb, hpb, hj⟩ := hr
    obtain ⟨pa', hpa', hda⟩ := ha.1 pa hpa
    obtain ⟨pb', hpb', hdb⟩ := hb.1 pb hpb
    have hrel := mkAnd_D hda hdb
    rw [hj] at hrel
    cases h' : mkAnd pa' pb' with
    | none => rw [h'] at hrel; cases hrel
    | some r' =>
      rw [h'] at hrel
      cases hrel with
      | some hd =>
        exact ⟨r', List.mem_flatMap.2 ⟨pa', hpa', List.mem_filterMap.2 ⟨pb', hpb', h'⟩⟩, hd⟩
  · intro r' hr'
    simp only [List.mem_flatMap, List.mem_filterMap] at hr'
    obtain ⟨pa', hpa', pb', hpb', hj⟩ := hr'
    obtain ⟨pa, hpa, hda⟩ := ha.2 pa' hpa'
    obtain ⟨pb, hpb, hdb⟩ := hb.2 pb' hpb'
    have hrel := mkAnd_D hda hdb
    rw [hj] at hrel
    cases h' : mkAnd pa pb with
    | none => rw [h'] at hrel; cases hrel
    | some r =>
      rw [h'] at hrel
      cases hrel with
      | some hd =>
        exact ⟨r, List.mem_flatMap.2 ⟨pa, hpa, List.mem_filterMap.2 ⟨pb, hpb, h'⟩⟩, hd⟩

/-- The products of an expression correspond to the products of its
converse. -/
theorem norm_corr : ∀ (neg : Bool) (e : Rel), Corr (norm neg e) (norm (!neg) e)
  | _, .zero => by simp [norm, Corr]
  | neg, .span s => by
    simp only [norm, Corr, List.mem_singleton, forall_eq, exists_eq_left, D, List.reverse_singleton,
      and_self]
    refine .cons (.span ?_) .nil
    cases neg
    · simp [swap_den]
    · simp [swap_den, GRel.inv_inv]
  | neg, .or a b => by
    simp only [norm]
    exact (norm_corr neg a).append (norm_corr neg b)
  | false, .seq a b => seq_corr (norm_corr false a) (norm_corr false b)
  | true, .seq a b => (seq_corr (norm_corr false a) (norm_corr false b)).symm
  | neg, .and a b => and_corr (norm_corr neg a) (norm_corr neg b)
  | neg, .conv a => by
    simpa [norm] using norm_corr (!neg) a
  | neg, .call m => by
    simp only [norm, Corr, List.mem_singleton, forall_eq, exists_eq_left, D, List.reverse_singleton,
      and_self]
    refine .cons (.other ?_ ?_ ?_) .nil <;> cases neg <;> simp [Rel.isSpan, Rel.calls]

/-! ## P1.4: weak duality -/

theorem products_conv (q : Rel) (k : Nat) : products P (.conv q) k = norm true (unfoldN P k q) := by
  simp [products, unfoldN_conv, norm]

theorem roundFinal_conv (q : Rel) (k : Nat) : roundFinal P (.conv q) k = roundFinal P q k := by
  have hc := norm_corr false (unfoldN P k q)
  apply Bool.eq_iff_iff.2
  rw [roundFinal_iff, roundFinal_iff, products_conv]
  constructor
  · intro h p hp
    obtain ⟨p', hp', hd⟩ := hc.1 p hp
    exact hd.calls.2 (h p' hp')
  · intro h p' hp'
    obtain ⟨p, hp, hd⟩ := hc.2 p' hp'
    exact hd.calls.1 (h p hp)

theorem roundSpans_conv_le {q : Rel} {k : Nat} {a : Span} (ha : a ∈ roundSpans P (.conv q) k) :
    ∃ b ∈ roundSpans P q k, a.den ⊆ b.swap.den := by
  simp only [roundSpans, products_conv, List.mem_flatMap] at ha
  obtain ⟨p, hp, ha⟩ := ha
  obtain ⟨s', hs', hsub⟩ := norm_reflect (P := P) true _ p hp a (mem_derivs.1 ha)
  obtain ⟨p₂, hp₂, t, ht, hst⟩ := norm_complete hs' false (Span.den_nonempty _)
  refine ⟨t, List.mem_flatMap.2 ⟨p₂, hp₂, mem_derivs.2 ht⟩, ?_⟩
  simp only [orientS, ite_true, Bool.false_eq_true, ite_false, swap_den] at hsub hst ⊢
  exact hsub.le.trans (GRel.inv_mono hst)

theorem roundSpans_conv_ge {q : Rel} {k : Nat} {b : Span} (hb : b ∈ roundSpans P q k) :
    ∃ a ∈ roundSpans P (.conv q) k, b.swap.den ⊆ a.den := by
  simp only [roundSpans, products, List.mem_flatMap] at hb
  obtain ⟨p, hp, hb⟩ := hb
  obtain ⟨s', hs', hsub⟩ := norm_reflect (P := P) false _ p hp b (mem_derivs.1 hb)
  obtain ⟨p₂, hp₂, t, ht, hst⟩ := norm_complete hs' true (Span.den_nonempty _)
  refine ⟨t, ?_, ?_⟩
  · simp only [roundSpans, products_conv, List.mem_flatMap]
    exact ⟨p₂, hp₂, mem_derivs.2 ht⟩
  · simp only [orientS, ite_true, Bool.false_eq_true, ite_false, swap_den] at hsub hst ⊢
    exact (GRel.inv_mono hsub.le).trans hst

/-- **P1.4, answers.** Every answer of the converse of a query is covered by
the swap of an answer of the query, and the swap of every answer of the
query is covered by an answer of the converse. So the two runs have the
same answers up to generality, read in opposite directions. -/
theorem dual_answers (q : Rel) :
    (∀ a ∈ runtime.Answers P (.conv q), ∃ b ∈ runtime.Answers P q, a.den ⊆ b.swap.den) ∧
    (∀ b ∈ runtime.Answers P q, ∃ a ∈ runtime.Answers P (.conv q), b.swap.den ⊆ a.den) := by
  constructor
  · intro a ha
    obtain ⟨k, hk, ha⟩ := mem_answers.1 ha
    obtain ⟨b, hb, hsub⟩ := roundSpans_conv_le ha
    refine ⟨b, mem_answers.2 ⟨k, fun j hj => ?_, hb⟩, hsub⟩
    rw [← roundFinal_conv]; exact hk j hj
  · intro b hb
    obtain ⟨k, hk, hb⟩ := mem_answers.1 hb
    obtain ⟨a, ha, hsub⟩ := roundSpans_conv_ge hb
    refine ⟨a, mem_answers.2 ⟨k, fun j hj => ?_, ha⟩, hsub⟩
    rw [roundFinal_conv]; exact hk j hj

/-- **P1.4, termination.** The converse of a query terminates exactly when
the query does. -/
theorem dual_terminates (q : Rel) :
    runtime.Terminates P (.conv q) ↔ runtime.Terminates P q :=
  terminates_congr (roundFinal_conv q)

end R000

end RwLog
