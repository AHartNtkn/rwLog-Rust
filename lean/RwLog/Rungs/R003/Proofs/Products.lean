/-
# The products the shared evaluation tells apart

Of a normal form the shared evaluation keeps two things (`Summary`): the
products that are a single span (`closed`), and, of every other product (which
then contains a call, `open_calls`), what it lets through on its right once
it is known to be alive on its left (`OpenR`).

This file computes both for the normal form of a sequence and of a
conjunction from those of the two factors (`closed_seq`, `openR_seq`,
`closed_and`, `openR_and`), with no reference to the evaluation.
-/
import RwLog.Rungs.R003.Proofs.Ranges
import RwLog.Rungs.R000.Properties

namespace RwLog

namespace R003

open R002 (headSpan lastSpan)

/-- The span of a product that is a single span. -/
def single : List Rel → Option Span
  | [.span s] => some s
  | _ => none

/-- The products that are a single span, as spans. -/
def closed (N : List (List Rel)) : List Span := N.filterMap single

/-- The first span of the product, if it has one, accepts a term of `ρ`. -/
def HeadOK (ρ : Set GTerm) (p : List Rel) : Prop := ∀ h, headSpan p = some h → AliveP ρ h

/-- What the products that are not a single span, and are alive after `ρ`,
let through on their right. -/
def OpenR (N : List (List Rel)) (ρ : Set GTerm) : Set (Set GTerm) :=
  {t | ∃ p ∈ N, single p = none ∧ HeadOK ρ p ∧ t = rng (lastSpan p)}

@[simp] theorem single_span (s : Span) : single [.span s] = some s := rfl

@[simp] theorem single_and (a b : Rel) : single [.and a b] = none := rfl

theorem single_eq_some {p : List Rel} {s : Span} : single p = some s ↔ p = [.span s] := by
  constructor
  · intro h
    unfold single at h
    split at h
    · cases h; rfl
    · cases h
  · rintro rfl; rfl

theorem mem_closed {N : List (List Rel)} {s : Span} : s ∈ closed N ↔ [.span s] ∈ N := by
  simp only [closed, List.mem_filterMap, single_eq_some]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro h; exact ⟨_, h, rfl⟩

theorem closed_append (N N' : List (List Rel)) : closed (N ++ N') = closed N ++ closed N' :=
  List.filterMap_append

theorem headOK_univ (p : List Rel) : HeadOK Set.univ p := fun h _ => aliveP_univ h

theorem openR_append (N N' : List (List Rel)) (ρ : Set GTerm) :
    OpenR (N ++ N') ρ = OpenR N ρ ∪ OpenR N' ρ := by
  ext t
  simp only [OpenR, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, h⟩
    · exact .inl ⟨p, hp, h⟩
    · exact .inr ⟨p, hp, h⟩
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, .inl hp, h⟩
    · exact ⟨p, .inr hp, h⟩

/-! ## Pairs of products -/

/-- The single spans among the pairwise combinations of two lists of
products, when a combination is a single span exactly when both parts are. -/
theorem closed_prod (J : List Rel → List Rel → Option (List Rel)) (f : Span → Span → Option Span)
    (Na Nb : List (List Rel))
    (h : ∀ p ∈ Na, ∀ q ∈ Nb, (J p q).bind single = (single p).bind fun x => (single q).bind (f x)) :
    closed (Na.flatMap fun p => Nb.filterMap (J p)) =
      (closed Na).flatMap fun x => (closed Nb).filterMap (f x) := by
  induction Na with
  | nil => rfl
  | cons p Na ih =>
    have ih := ih fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [List.flatMap_cons, closed_append, ih]
    have hp : closed (Nb.filterMap (J p)) =
        Nb.filterMap fun q => (single p).bind fun x => (single q).bind (f x) := by
      unfold closed
      rw [List.filterMap_filterMap]
      exact List.filterMap_congr fun q hq => h p List.mem_cons_self q hq
    rw [hp]
    unfold closed
    rw [List.filterMap_cons]
    cases hs : single p with
    | none => simp
    | some x => simp [List.filterMap_filterMap]

/-! ## Sequences -/

theorem joinSeq_append_of {p q : List Rel} (h : lastSpan p = none ∨ headSpan q = none) :
    R000.joinSeq p q = some (p ++ q) := by
  unfold R000.joinSeq
  split
  · rename_i a b q' hl
    rcases h with h | h
    · rw [R002.lastSpan_of_getLast? hl] at h; cases h
    · cases h
  · rfl

/-- A joined product is a single span only when both parts are, and their
spans compose to it. -/
theorem single_join {p q r : List Rel} {z : Span} (h : R000.joinSeq p q = some r) (hp : p ≠ [])
    (hq : q ≠ []) (hr : single r = some z) :
    ∃ x y, p = [.span x] ∧ q = [.span y] ∧ x.compose y = some z := by
  rw [single_eq_some] at hr
  subst hr
  rcases R000.joinSeq_cases h with ⟨a, b, q', c, hl, rfl, hc, hr⟩ | hr
  · match p, hp, hl with
    | [x], _, hl =>
      obtain rfl : x = .span a := by simpa using hl
      simp only [List.dropLast_singleton, List.nil_append, List.cons.injEq, Rel.span.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨a, b, rfl, rfl, hc⟩
    | x :: y :: p', _, _ => simp at hr
  · have := congrArg List.length hr
    have h₁ := List.length_pos_of_ne_nil hp
    have h₂ := List.length_pos_of_ne_nil hq
    simp only [List.length_cons, List.length_nil, List.length_append] at this
    omega

theorem joinSeq_singles (x y : Span) :
    R000.joinSeq [.span x] [.span y] = (x.compose y).map fun c => [.span c] :=
  R002.joinSeq_fused (p := [.span x]) rfl y []

theorem closed_seq (Na Nb : List (List Rel)) (ha : ∀ p ∈ Na, p ≠ []) (hb : ∀ q ∈ Nb, q ≠ []) :
    closed (Na.flatMap fun p => Nb.filterMap (R000.joinSeq p)) =
      (closed Na).flatMap fun x => (closed Nb).filterMap x.compose := by
  refine closed_prod _ _ Na Nb fun p hp q hq => ?_
  cases hsp : single p with
  | none =>
    cases hj : R000.joinSeq p q with
    | none => rfl
    | some r =>
      cases hr : single r with
      | none => simp [hr]
      | some z =>
        obtain ⟨x, y, rfl, -, -⟩ := single_join hj (ha p hp) (hb q hq) hr
        cases hsp
  | some x =>
    cases hsq : single q with
    | none =>
      cases hj : R000.joinSeq p q with
      | none => rfl
      | some r =>
        cases hr : single r with
        | none => simp [hr]
        | some z =>
          obtain ⟨x, y, -, rfl, -⟩ := single_join hj (ha p hp) (hb q hq) hr
          cases hsq
    | some y =>
      obtain rfl := single_eq_some.mp hsp
      obtain rfl := single_eq_some.mp hsq
      rw [joinSeq_singles]
      cases hc : x.compose y <;> simp [hc]

theorem lastSpan_fused {l : List Rel} (b c : Span) {q' : List Rel} (hq' : q' ≠ []) :
    lastSpan (l ++ .span c :: q') = lastSpan (.span b :: q') := by
  rw [R002.lastSpan_append (List.cons_ne_nil _ _)]
  exact (R002.lastSpan_append (p := [Rel.span c]) hq').trans
    (R002.lastSpan_append (p := [Rel.span b]) hq').symm

/-- Joining a single span with a product that is not one. -/
theorem join_closed_open {x : Span} {q : List Rel} (hq : q ≠ []) (hsq : single q = none)
    (ρ : Set GTerm) :
    (∀ r, R000.joinSeq [.span x] q = some r →
      single r = none ∧ lastSpan r = lastSpan q ∧ (HeadOK ρ r ↔ AliveP ρ x ∧ HeadOK (img ρ x) q)) ∧
    (AliveP ρ x → HeadOK (img ρ x) q → ∃ r, R000.joinSeq [.span x] q = some r) := by
  cases hh : headSpan q with
  | none =>
    have hj : R000.joinSeq [.span x] q = some ([.span x] ++ q) := joinSeq_append_of (.inr hh)
    refine ⟨fun r hr => ?_, fun _ _ => ⟨_, hj⟩⟩
    rw [hj] at hr
    cases hr
    refine ⟨?_, R002.lastSpan_append hq, ?_⟩
    · match q, hq with
      | y :: q', _ => rfl
    · constructor
      · exact fun h => ⟨h x rfl, fun b hb => by rw [hh] at hb; cases hb⟩
      · rintro ⟨h, -⟩ b hb
        cases hb
        exact h
  | some b =>
    obtain ⟨q', rfl⟩ := R002.headSpan_eq_some hh
    have hq' : q' ≠ [] := by
      rintro rfl
      cases hsq
    have hj := R002.joinSeq_fused (p := [.span x]) (a := x) rfl b q'
    refine ⟨fun r hr => ?_, fun _ h => ?_⟩
    · rw [hj] at hr
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hr
      refine ⟨?_, lastSpan_fused b c hq', ?_⟩
      · match q', hq' with
        | y :: q'', _ => rfl
      · constructor
        · intro h
          have := (aliveP_compose hc ρ).mp (h c rfl)
          exact ⟨this.of_img, fun b' hb' => by cases hb'; exact this⟩
        · rintro ⟨-, h⟩ c' hc'
          cases hc'
          exact (aliveP_compose hc ρ).mpr (h b rfl)
    · have := (compose_isSome_iff x b).mpr ((h b rfl).mono (img_mono x (Set.subset_univ ρ)))
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp this
      exact ⟨_, by rw [hj, hc]; rfl⟩

/-- Joining a product that is not a single span with another product. -/
theorem join_open {p q : List Rel} (hp : p ≠ []) (hq : q ≠ []) (hsp : single p = none) :
    (∀ r, R000.joinSeq p q = some r →
      single r = none ∧ headSpan r = headSpan p ∧
        (∀ h, single q = some h → rng (lastSpan r) = img (rng (lastSpan p)) h) ∧
        (single q = none → lastSpan r = lastSpan q)) ∧
    ((∃ r, R000.joinSeq p q = some r) ↔ HeadOK (rng (lastSpan p)) q) := by
  have hsingle : ∀ r, R000.joinSeq p q = some r → single r = none := by
    intro r hr
    cases hs : single r with
    | none => rfl
    | some z =>
      obtain ⟨x, y, rfl, -, -⟩ := single_join hr hp hq hs
      cases hsp
  have hhead : ∀ r, R000.joinSeq p q = some r → headSpan r = headSpan p := by
    intro r hr
    rcases R002.joinSeq_head hr hp with ⟨a, b, q', c, rfl, -, -, -⟩ | h
    · cases hsp
    · exact h
  by_cases hfuse : ∃ a b, lastSpan p = some a ∧ headSpan q = some b
  · obtain ⟨a, b, hl, hh⟩ := hfuse
    obtain ⟨q', rfl⟩ := R002.headSpan_eq_some hh
    have hj := R002.joinSeq_fused (R002.lastSpan_eq_some hl) b q'
    refine ⟨fun r hr => ⟨hsingle r hr, hhead r hr, ?_, ?_⟩, ?_⟩
    · intro h hqs
      rw [hj] at hr
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hr
      rw [single_eq_some] at hqs
      simp only [List.cons.injEq, Rel.span.injEq] at hqs
      obtain ⟨rfl, rfl⟩ := hqs
      rw [R002.lastSpan_append (List.cons_ne_nil _ _), hl]
      exact img_compose hc Set.univ
    · intro hqs
      rw [hj] at hr
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hr
      have hq' : q' ≠ [] := by
        rintro rfl
        cases hqs
      exact lastSpan_fused b c hq'
    · rw [hj, hl]
      constructor
      · rintro ⟨r, hr⟩ b' hb'
        cases hb'
        obtain ⟨c, hc, -⟩ := Option.map_eq_some_iff.mp hr
        exact (compose_isSome_iff a b).mp (by rw [hc]; rfl)
      · intro h
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ((compose_isSome_iff a b).mpr (h b rfl))
        exact ⟨_, by rw [hc]; rfl⟩
  · have hor : lastSpan p = none ∨ headSpan q = none := by
      cases hl : lastSpan p with
      | none => exact .inl rfl
      | some a =>
        cases hh : headSpan q with
        | none => exact .inr rfl
        | some b => exact (hfuse ⟨a, b, hl, hh⟩).elim
    have hj := joinSeq_append_of hor
    refine ⟨fun r hr => ⟨hsingle r hr, hhead r hr, ?_, ?_⟩, ?_⟩
    · intro h hqs
      rw [hj] at hr
      cases hr
      rw [single_eq_some] at hqs
      subst hqs
      rcases hor with hl | hh
      · rw [R002.lastSpan_append hq, hl]
        rfl
      · cases hh
    · intro _
      rw [hj] at hr
      cases hr
      exact R002.lastSpan_append hq
    · refine ⟨fun _ b hb => ?_, fun _ => ⟨_, hj⟩⟩
      rcases hor with hl | hh
      · rw [hl]
        exact aliveP_univ b
      · rw [hh] at hb
        cases hb

/-- What the products of a sequence that are not a single span let through:
after a single span of the first factor, what those of the second factor let
through after it; after another product of the first factor, what the products
of the second factor let through after that. -/
theorem openR_seq (Na Nb : List (List Rel)) (ha : ∀ p ∈ Na, p ≠ []) (hb : ∀ q ∈ Nb, q ≠ [])
    (ρ : Set GTerm) :
    OpenR (Na.flatMap fun p => Nb.filterMap (R000.joinSeq p)) ρ =
      {t | ∃ x ∈ closed Na, AliveP ρ x ∧ t ∈ OpenR Nb (img ρ x)} ∪
      {t | ∃ p ∈ Na, single p = none ∧ HeadOK ρ p ∧
        (t ∈ OpenR Nb (rng (lastSpan p)) ∨
          ∃ h ∈ closed Nb, AliveP (rng (lastSpan p)) h ∧ t = img (rng (lastSpan p)) h)} := by
  ext t
  constructor
  · rintro ⟨r, hr, hsr, hok, rfl⟩
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨q, hq, hj⟩ := List.mem_filterMap.mp hr
    cases hsp : single p with
    | some x =>
      obtain rfl := single_eq_some.mp hsp
      cases hsq : single q with
      | some y =>
        obtain rfl := single_eq_some.mp hsq
        rw [joinSeq_singles] at hj
        obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp hj
        cases hsr
      | none =>
        obtain ⟨-, hl, hiff⟩ := (join_closed_open (hb q hq) hsq ρ).1 r hj
        obtain ⟨hx, hqok⟩ := hiff.mp hok
        exact .inl ⟨x, mem_closed.mpr hp, hx, q, hq, hsq, hqok, by rw [hl]⟩
    | none =>
      obtain ⟨hall, hex⟩ := join_open (ha p hp) (hb q hq) hsp
      obtain ⟨-, hh, hs, hn⟩ := hall r hj
      have hqok := hex.mp ⟨r, hj⟩
      refine .inr ⟨p, hp, hsp, fun h hh' => hok h (hh.trans hh'), ?_⟩
      cases hsq : single q with
      | some h =>
        obtain rfl := single_eq_some.mp hsq
        exact .inr ⟨h, mem_closed.mpr hq, hqok h rfl, hs h hsq⟩
      | none => exact .inl ⟨q, hq, hsq, hqok, by rw [hn hsq]⟩
  · rintro (⟨x, hx, hal, q, hq, hsq, hqok, rfl⟩ | ⟨p, hp, hsp, hok, h⟩)
    · have hp := mem_closed.mp hx
      obtain ⟨hall, hex⟩ := join_closed_open (x := x) (hb q hq) hsq ρ
      obtain ⟨r, hj⟩ := hex hal hqok
      obtain ⟨hsr, hl, hiff⟩ := hall r hj
      exact ⟨r, List.mem_flatMap.mpr ⟨_, hp, List.mem_filterMap.mpr ⟨q, hq, hj⟩⟩, hsr,
        hiff.mpr ⟨hal, hqok⟩, by rw [hl]⟩
    · rcases h with ⟨q, hq, hsq, hqok, rfl⟩ | ⟨h, hh, hal, rfl⟩
      · obtain ⟨hall, hex⟩ := join_open (ha p hp) (hb q hq) hsp
        obtain ⟨r, hj⟩ := hex.mpr hqok
        obtain ⟨hsr, hh, -, hn⟩ := hall r hj
        exact ⟨r, List.mem_flatMap.mpr ⟨_, hp, List.mem_filterMap.mpr ⟨q, hq, hj⟩⟩, hsr,
          fun h' hh' => hok h' (hh.symm.trans hh'), by rw [hn hsq]⟩
      · have hq := mem_closed.mp hh
        obtain ⟨hall, hex⟩ := join_open (q := [.span h]) (ha p hp) (List.cons_ne_nil _ _) hsp
        obtain ⟨r, hj⟩ := hex.mpr fun h' hh' => by cases hh'; exact hal
        obtain ⟨hsr, hh', hs, -⟩ := hall r hj
        exact ⟨r, List.mem_flatMap.mpr ⟨_, hp, List.mem_filterMap.mpr ⟨_, hq, hj⟩⟩, hsr,
          fun h' hh'' => hok h' (hh'.symm.trans hh''), (hs h rfl).symm⟩

/-! ## Conjunctions -/

theorem mkAnd_cases (p q : List Rel) :
    (∃ a b, p = [.span a] ∧ q = [.span b] ∧
        R000.mkAnd p q = (a.meet b).map fun c => [.span c]) ∨
      ((single p = none ∨ single q = none) ∧
        R000.mkAnd p q = some [.and (toRel p) (toRel q)]) := by
  cases hsp : single p with
  | some a =>
    cases hsq : single q with
    | some b =>
      obtain rfl := single_eq_some.mp hsp
      obtain rfl := single_eq_some.mp hsq
      exact .inl ⟨a, b, rfl, rfl, rfl⟩
    | none =>
      refine .inr ⟨.inr rfl, ?_⟩
      unfold R000.mkAnd
      split
      · cases hsq
      · rfl
  | none =>
    refine .inr ⟨.inl rfl, ?_⟩
    unfold R000.mkAnd
    split
    · cases hsp
    · rfl

theorem closed_and (Na Nb : List (List Rel)) :
    closed (Na.flatMap fun p => Nb.filterMap (R000.mkAnd p)) =
      (closed Na).flatMap fun x => (closed Nb).filterMap x.meet := by
  refine closed_prod _ _ Na Nb fun p _ q _ => ?_
  rcases mkAnd_cases p q with ⟨a, b, rfl, rfl, h⟩ | ⟨hs, h⟩
  · rw [h]
    cases hm : a.meet b <;> simp [hm]
  · rw [h]
    rcases hs with hs | hs
    · simp [hs]
    · cases hsp : single p <;> simp [hs]

/-- The products of a conjunction that are not a single span are barriers:
they let everything through, and there is one as soon as one of the two parts
is not a single span. -/
theorem openR_and (Na Nb : List (List Rel)) (ρ : Set GTerm) :
    OpenR (Na.flatMap fun p => Nb.filterMap (R000.mkAnd p)) ρ =
      {t | t = Set.univ ∧ ∃ p ∈ Na, ∃ q ∈ Nb, single p = none ∨ single q = none} := by
  ext t
  constructor
  · rintro ⟨r, hr, hsr, -, rfl⟩
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨q, hq, hj⟩ := List.mem_filterMap.mp hr
    rcases mkAnd_cases p q with ⟨a, b, rfl, rfl, h⟩ | ⟨hs, h⟩
    · rw [h] at hj
      obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp hj
      cases hsr
    · rw [h] at hj
      cases hj
      exact ⟨rfl, p, hp, q, hq, hs⟩
  · rintro ⟨rfl, p, hp, q, hq, hs⟩
    rcases mkAnd_cases p q with ⟨a, b, rfl, rfl, -⟩ | ⟨-, h⟩
    · rcases hs with hs | hs <;> cases hs
    · exact ⟨_, List.mem_flatMap.mpr ⟨p, hp, List.mem_filterMap.mpr ⟨q, hq, h⟩⟩, rfl,
        fun h hh => (by cases hh), rfl⟩

/-! ## Products of a normal form -/

/-- A product of a normal form that is not a single span contains a call. -/
theorem open_calls : ∀ (e : Rel) (neg : Bool), ∀ p ∈ R000.norm neg e, single p = none →
    ∃ x ∈ p, x.calls ≠ [] := by
  intro e
  induction e with
  | zero => intro neg p hp; simp [R000.norm] at hp
  | span s =>
    intro neg p hp hs
    simp only [R000.norm, List.mem_singleton] at hp
    subst hp
    cases hs
  | or a b iha ihb =>
    intro neg p hp
    simp only [R000.norm, List.mem_append] at hp
    exact hp.elim (iha neg p) (ihb neg p)
  | and a b iha ihb =>
    intro neg r hr hsr
    simp only [R000.norm, List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨p, hp, q, hq, hj⟩ := hr
    rcases mkAnd_cases p q with ⟨x, y, rfl, rfl, h⟩ | ⟨hs, h⟩
    · rw [h] at hj
      obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp hj
      cases hsr
    · rw [h] at hj
      cases hj
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [Rel.calls, ne_eq, List.append_eq_nil_iff, not_and_or]
      rcases hs with hs | hs
      · obtain ⟨x, hx, hc⟩ := iha neg p hp hs
        exact .inl fun h0 => hc ((R000.calls_toRel p).mp h0 x hx)
      · obtain ⟨x, hx, hc⟩ := ihb neg q hq hs
        exact .inr fun h0 => hc ((R000.calls_toRel q).mp h0 x hx)
  | seq a b iha ihb =>
    have key : ∀ (Na Nb : List (List Rel)), (∀ p ∈ Na, p ≠ []) → (∀ q ∈ Nb, q ≠ []) →
        (∀ p ∈ Na, single p = none → ∃ x ∈ p, x.calls ≠ []) →
        (∀ q ∈ Nb, single q = none → ∃ x ∈ q, x.calls ≠ []) →
        ∀ r ∈ Na.flatMap fun p => Nb.filterMap (R000.joinSeq p), single r = none →
          ∃ x ∈ r, x.calls ≠ [] := by
      intro Na Nb ha hb iha ihb r hr hsr
      obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨q, hq, hj⟩ := List.mem_filterMap.mp hr
      have hpq : single p = none ∨ single q = none := by
        cases hsp : single p with
        | none => exact .inl rfl
        | some x =>
          cases hsq : single q with
          | none => exact .inr rfl
          | some y =>
            obtain rfl := single_eq_some.mp hsp
            obtain rfl := single_eq_some.mp hsq
            rw [joinSeq_singles] at hj
            obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp hj
            cases hsr
      have hin : ∃ x, (x ∈ p ∨ x ∈ q) ∧ x.calls ≠ [] := by
        rcases hpq with hs | hs
        · obtain ⟨x, hx, hc⟩ := iha p hp hs
          exact ⟨x, .inl hx, hc⟩
        · obtain ⟨x, hx, hc⟩ := ihb q hq hs
          exact ⟨x, .inr hx, hc⟩
      obtain ⟨x, hx, hc⟩ := hin
      refine ⟨x, ?_, hc⟩
      rcases R000.joinSeq_cases hj with ⟨a', b', q', c, hl, rfl, -, rfl⟩ | rfl
      · have hpe : p.dropLast ++ [.span a'] = p := List.dropLast_append_getLast? _ hl
        rcases hx with hx | hx
        · rw [← hpe, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact List.mem_append_left _ hx
          · exact (hc rfl).elim
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact (hc rfl).elim
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
      · exact List.mem_append.mpr hx
    intro neg r hr
    cases neg
    · exact key _ _ (R000.norm_ne_nil a false) (R000.norm_ne_nil b false) (iha false) (ihb false)
        r (by simpa only [R000.norm] using hr)
    · exact key _ _ (R000.norm_ne_nil b true) (R000.norm_ne_nil a true) (ihb true) (iha true)
        r (by simpa only [R000.norm] using hr)
  | conv a iha => intro neg p hp; exact iha (!neg) p hp
  | call n =>
    intro neg p hp _
    simp only [R000.norm, List.mem_singleton] at hp
    subst hp
    exact ⟨_, List.mem_singleton_self _, by cases neg <;> simp [Rel.calls]⟩

/-- No product of a normal form contains a call exactly when every product is
a single span, that is when nothing is let through by another product. -/
theorem all_callFree_iff (e : Rel) (neg : Bool) :
    ((R000.norm neg e).all fun p => (toRel p).calls.isEmpty) = true ↔
      OpenR (R000.norm neg e) Set.univ = ∅ := by
  rw [List.all_eq_true, Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro h t ⟨p, hp, hs, -, -⟩
    obtain ⟨x, hx, hc⟩ := open_calls e neg p hp hs
    exact hc ((R000.calls_toRel p).mp (List.isEmpty_iff.mp (h p hp)) x hx)
  · intro h p hp
    cases hs : single p with
    | none => exact (h _ ⟨p, hp, hs, headOK_univ p, rfl⟩).elim
    | some s =>
      obtain rfl := single_eq_some.mp hs
      rfl

/-- When every product is a single span, the spans derived by the products
are those spans. -/
theorem derivs_of_closed : ∀ N : List (List Rel), (∀ p ∈ N, single p ≠ none) →
    (N.flatMap fun p => R000.derivs (toRel p)) = closed N
  | [], _ => rfl
  | p :: N, h => by
    have ih := derivs_of_closed N fun p hp => h p (List.mem_cons_of_mem _ hp)
    cases hs : single p with
    | none => exact (h p List.mem_cons_self hs).elim
    | some s =>
      obtain rfl := single_eq_some.mp hs
      rw [List.flatMap_cons, ih]
      rfl

end R003

end RwLog
