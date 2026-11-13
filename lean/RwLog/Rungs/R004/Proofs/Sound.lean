/-
# Why pruning from the right loses nothing

The walk from the right drops a span when it does not compose with the chain
of spans to its right: the spans the derivation chosen for the second factor
starts with (`front`), followed by the chain of the sequence itself when that
derivation is nothing but spans. This file proves that a derivation the walk
does not hand on has no product (`norm_of_not_mem_WR`).

* The first span of the product of a derivation is made of the spans of
  `front` and of whatever was fused after them, as ground relations
  (`front_head`).
* So a product whose last span does not compose with `front` cannot be joined
  to that derivation's product, or joins into a product that does not compose
  with the chain of the sequence (`alive_first`); and a product that does not
  compose with the chain still does not after something is joined on its left
  (`alive_second`).
-/
import RwLog.Rungs.R004.Proofs.Paths
import RwLog.Rungs.R002.Proofs.Chains

namespace RwLog

namespace R004

open R000 Cost
open R002 (AR headSpan lastSpan)

/-- The ground relation of a chain. -/
abbrev C (X : List Span) : GRel := GRel.chain (X.map Span.den)

theorem C_cons (s : Span) (X : List Span) : C (s :: X) = s.den.comp (C X) := rfl

theorem nonempty_of_comp_left {A G : GRel} (h : (A.comp G).Nonempty) : A.Nonempty := by
  obtain ⟨x, m, S₁, S₂, h1, -, -⟩ := h
  exact ⟨_, h1⟩

theorem nonempty_of_comp_right {A G : GRel} (h : (A.comp G).Nonempty) : G.Nonempty := by
  obtain ⟨x, m, S₁, S₂, -, h2, -⟩ := h
  exact ⟨_, h2⟩

/-! ## The test -/

theorem fits_eq (s : Span) (R : List Span) : fits s R = R002.aliveR [.span s] R := by
  cases R <;> rfl

theorem fits_iff (s : Span) (R : List Span) : (fits s R).val = true ↔ AR [.span s] R := by
  rw [fits_eq, R002.aliveR_iff]

/-- Nothing is ruled out by an empty chain. -/
theorem AR_nil (p : List Rel) : AR p [] := fun h => (h rfl).elim

/-! ## The first span of a derivation's product -/

/-- The first span of the product of a derivation: either the product is that
span alone and, followed by `R`, it is the chain `front pe R`; or it is that
chain followed by something. -/
theorem front_head : ∀ (pe : Rel) (R : List Span), front pe R ≠ [] → ∀ q ∈ norm false pe,
    ∃ B rest, q = .span B :: rest ∧
      ((rest = [] ∧ C (front pe R) = B.den.comp (C R)) ∨ ∃ G, B.den = (C (front pe R)).comp G) := by
  intro pe
  induction pe with
  | zero => intro R h; exact (h rfl).elim
  | span s =>
    intro R _ q hq
    simp only [norm, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hq
    subst hq
    exact ⟨s, [], rfl, .inl ⟨rfl, rfl⟩⟩
  | or a b _ _ => intro R h; exact (h rfl).elim
  | and a b _ _ => intro R h; exact (h rfl).elim
  | conv a _ => intro R h; exact (h rfl).elim
  | call n => intro R h; exact (h rfl).elim
  | seq a b iha ihb =>
    intro R hne q hq
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hq
    obtain ⟨p₀, hp₀, q₀, hq₀, hj⟩ := hq
    have hfr : front (.seq a b) R = front a (front b R) := rfl
    rw [hfr] at hne ⊢
    obtain ⟨A, restA, rfl, hA⟩ := iha (front b R) hne p₀ hp₀
    have hq₀ne : q₀ ≠ [] := norm_ne_nil b false q₀ hq₀
    rcases hA with ⟨rfl, hA⟩ | ⟨G, hG⟩
    · -- the first factor's product is the span `A` alone
      by_cases hR' : front b R = []
      · rw [hR'] at hA ⊢
        have hAd : A.den = C (front a []) := by
          rw [hA]; exact (GRel.comp_id _).symm
        rcases R002.joinSeq_head hj (List.cons_ne_nil _ _) with
          ⟨a', b', q', c, hp, rfl, hc, rfl⟩ | hh
        · cases hp
          exact ⟨c, q', rfl, .inr ⟨b'.den, by rw [compose_some hc, hAd]⟩⟩
        · obtain ⟨q', rfl⟩ := R002.headSpan_eq_some (hh.trans rfl)
          exact ⟨A, q', rfl, .inr ⟨GRel.id, by rw [GRel.comp_id, hAd]⟩⟩
      · obtain ⟨B, restB, rfl, hB⟩ := ihb R hR' q₀ hq₀
        have hf : R000.joinSeq [.span A] (.span B :: restB) =
            (A.compose B).map fun c => [] ++ .span c :: restB :=
          R002.joinSeq_fused (p := [.span A]) rfl B restB
        rw [hf] at hj
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hj
        refine ⟨c, restB, rfl, ?_⟩
        rcases hB with ⟨rfl, hB⟩ | ⟨G, hG⟩
        · exact .inl ⟨rfl, by rw [hA, hB, compose_some hc, GRel.comp_assoc]⟩
        · exact .inr ⟨G, by rw [compose_some hc, hG, hA, GRel.comp_assoc]⟩
    · rcases R002.joinSeq_head hj (List.cons_ne_nil _ _) with
        ⟨a', b', q', c, hp, rfl, hc, rfl⟩ | hh
      · cases hp
        exact ⟨c, q', rfl, .inr ⟨G.comp b'.den, by rw [compose_some hc, hG, GRel.comp_assoc]⟩⟩
      · obtain ⟨q', rfl⟩ := R002.headSpan_eq_some (hh.trans rfl)
        exact ⟨A, q', rfl, .inr ⟨G, hG⟩⟩

/-! ## The two steps of a sequence -/

/-- A product that joins a derivation's product into something alive before
`R` is itself alive before what the derivation starts with. -/
theorem alive_first {pe : Rel} {R : List Span} {p q r : List Rel} (hq : q ∈ norm false pe)
    (hj : R000.joinSeq p q = some r) (hr : AR r R) : AR p (front pe R) := by
  intro hne s hs
  obtain ⟨B, rest, rfl, hB⟩ := front_head pe R hne q hq
  obtain ⟨c, q', hc, hq', rfl⟩ := R002.joinSeq_junction hj hs rfl
  cases hq'
  have hcn : (s.den.comp B.den).Nonempty := compose_some hc ▸ c.den_nonempty
  show (s.den.comp (C (front pe R))).Nonempty
  rcases hB with ⟨rfl, hB⟩ | ⟨G, hG⟩
  · rw [hB, ← GRel.comp_assoc, ← compose_some hc]
    by_cases hR : R = []
    · subst hR
      show (c.den.comp GRel.id).Nonempty
      rw [GRel.comp_id]
      exact c.den_nonempty
    · exact hr hR c (R002.lastSpan_append (List.cons_ne_nil _ _))
  · rw [hG, ← GRel.comp_assoc] at hcn
    exact nonempty_of_comp_left hcn

/-- A product that is alive before `R` after something is joined on its left
was alive before `R`. -/
theorem alive_second {R : List Span} {p q r : List Rel} (hqne : q ≠ [])
    (hj : R000.joinSeq p q = some r) (hr : AR r R) : AR q R := by
  intro hne t ht
  rcases R002.joinSeq_last hj hqne with ⟨a, b, c, -, rfl, hc, hl⟩ | hl
  · cases ht
    have := hr hne c hl
    rw [compose_some hc, GRel.comp_assoc] at this
    exact nonempty_of_comp_right this
  · exact hr hne t (hl.trans ht)

/-! ## A derivation the walk drops has no product alive -/

/-- No product of the derivation is alive before `R`. -/
def Dead (R : List Span) (x : Path) : Prop := ∀ p ∈ norm false x.pe, ¬ AR p R

theorem dead_seq_second {R : List Span} {p q : Path} (h : Dead R q) : Dead R (p.seq q) := by
  intro r hr har
  simp only [Path.seq, norm, List.mem_flatMap, List.mem_filterMap] at hr
  obtain ⟨p', -, q', hq', hj⟩ := hr
  exact h q' hq' (alive_second (norm_ne_nil _ _ q' hq') hj har)

theorem dead_seq_first {R : List Span} {p q : Path} (h : Dead (front q.pe R) p) :
    Dead R (p.seq q) := by
  intro r hr har
  simp only [Path.seq, norm, List.mem_flatMap, List.mem_filterMap] at hr
  obtain ⟨p', hp', q', hq', hj⟩ := hr
  exact h p' hp' (alive_first hq' hj har)

theorem norm_nil_of_dead {x : Path} (h : Dead [] x) : norm false x.pe = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun p hp => h p hp (AR_nil p)

/-- A derivation the walk from the right does not hand on has no product
alive before the chain. -/
theorem dead_of_not_mem_WR : ∀ (e : Rel) (neg : Bool) (R : List Span), ∀ x ∈ paths neg e,
    x ∉ WR neg e R → Dead R x := by
  intro e
  induction e with
  | zero => intro neg R x hx; simp [paths] at hx
  | span s =>
    intro neg R x hx hn
    simp only [paths, List.mem_singleton] at hx
    subst hx
    have hf : ¬ (fits (if neg = true then s.swap else s) R).val = true := by
      intro hf
      exact hn (by simp [WR, hf])
    intro p hp har
    simp only [norm, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hp
    subst hp
    exact hf ((fits_iff _ R).mpr har)
  | or a b iha ihb =>
    intro neg R x hx hn
    simp only [paths, List.mem_append, List.mem_map] at hx
    simp only [WR, List.mem_append, List.mem_map, not_or, not_exists, not_and] at hn
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact iha neg R y hy fun h => hn.1 y h rfl
    · exact ihb neg R y hy fun h => hn.2 y h rfl
  | seq a b iha ihb =>
    intro neg R x hx hn
    cases neg
    · simp only [paths, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      simp only [WR, List.mem_flatMap, List.mem_map, not_exists, not_and] at hn
      by_cases hqw : q ∈ WR false b R
      · exact dead_seq_first (iha false _ p hp fun h => hn q hqw p h rfl)
      · exact dead_seq_second (ihb false R q hq hqw)
    · simp only [paths, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      simp only [WR, List.mem_flatMap, List.mem_map, not_exists, not_and] at hn
      by_cases hqw : q ∈ WR true a R
      · exact dead_seq_first (ihb true _ p hp fun h => hn q hqw p h rfl)
      · exact dead_seq_second (iha true R q hq hqw)
  | and a b iha ihb =>
    intro neg R x hx hn
    simp only [paths, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hx
    simp only [WR, List.mem_flatMap, List.mem_map, not_exists, not_and] at hn
    intro r hr
    simp only [Path.and, norm, List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨p', hp', q', hq', -⟩ := hr
    by_cases hpw : p ∈ WR neg a []
    · have hqd := ihb neg [] q hq fun h => hn p hpw q h rfl
      rw [norm_nil_of_dead hqd] at hq'
      cases hq'
    · have hpd := iha neg [] p hp hpw
      rw [norm_nil_of_dead hpd] at hp'
      cases hp'
  | conv a iha => intro neg R x hx hn; exact iha (!neg) R x hx hn
  | call n =>
    intro neg R x hx hn
    exact (hn (by simpa [WR, paths] using hx)).elim

/-- A derivation the walk from the right does not hand on has no product. -/
theorem norm_of_not_mem_WR {e : Rel} {neg : Bool} {x : Path} (hx : x ∈ paths neg e)
    (hn : x ∉ WR neg e []) : norm false x.pe = [] :=
  norm_nil_of_dead (dead_of_not_mem_WR e neg [] x hx hn)

end R004

end RwLog
