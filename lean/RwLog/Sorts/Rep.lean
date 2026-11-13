/-
# Representatives

A *representative* for the sorts `S` is a normal store whose pattern is a
pair: the two sides of a span. It relates the pairs its store denotes
(`Raw.rel`). Two representatives that relate the same pairs are equal
(`Rep.ext_rel`), and every first-order constraint problem over a pair that
has a solution has a representative (`exists_rep`).

There are representatives only for well-formed sorts: the type is empty
otherwise.

`Raw.toSpan` writes a representative as a span, with its sorts and its
exclusions as constraints. In the interpretation of the sorts the span
relates the pairs the representative relates (`Raw.toSpan_den`).
-/
import RwLog.Sorts.Reduce
import RwLog.Trusted.Domain

namespace RwLog
namespace Sorts

open Function

/-- The pairs a raw store relates, its pattern being the pair of its two
sides. -/
def Raw.rel (S : Sorts) (r : Raw) : PRel := {p | tpair p.1 p.2 ∈ r.store.Den S}

theorem Raw.rel_eq {S : Sorts} {r : Raw} {a b : Pat} (h : r.t = tpair a b) :
    r.rel S = {p | ∃ σ ∈ r.store.Sol S, p.1 = a.bind σ ∧ p.2 = b.bind σ} := by
  ext p
  constructor
  · rintro ⟨σ, hσ, e⟩
    have e' : tpair p.1 p.2 = tpair (a.bind σ) (b.bind σ) := by
      rw [e]; show r.t.bind σ = _; rw [h, tpair_bind]
    exact ⟨σ, hσ, tpair_inj e'⟩
  · rintro ⟨σ, hσ, e₁, e₂⟩
    refine ⟨σ, hσ, ?_⟩
    show _ = r.t.bind σ
    rw [h, tpair_bind, e₁, e₂]

/-- A representative for the sorts `S`: a normal store over a pair. -/
def Rep (S : Sorts) : Type := {r : Raw // S.WellFormed ∧ r.Normal S ∧ ∃ a b, r.t = tpair a b}

instance (S : Sorts) : DecidableEq (Rep S) := by unfold Rep; infer_instance

namespace Rep

variable {S : Sorts}

theorem wf (ρ : Rep S) : S.WellFormed := ρ.2.1

theorem normal (ρ : Rep S) : ρ.1.Normal S := ρ.2.2.1

/-- Representatives that relate the same pairs are equal. -/
theorem ext_rel {ρ ρ' : Rep S} (h : ρ.1.rel S = ρ'.1.rel S) : ρ = ρ' := by
  have key : ∀ {ρ ρ' : Rep S}, ρ.1.rel S = ρ'.1.rel S → ρ.1.store.Den S ⊆ ρ'.1.store.Den S := by
    intro ρ ρ' h g hg
    obtain ⟨a, b, hab⟩ := ρ.2.2.2
    obtain ⟨σ, hσ, rfl⟩ := hg
    have e : ρ.1.store.t.bind σ = tpair (a.bind σ) (b.bind σ) := by
      show ρ.1.t.bind σ = _; rw [hab, tpair_bind]
    have : (a.bind σ, b.bind σ) ∈ ρ.1.rel S := ⟨σ, hσ, e.symm⟩
    rw [h] at this
    rw [e]; exact this
  exact Subtype.ext (Raw.Normal.eq ρ.wf ρ.normal ρ'.normal
    (Set.Subset.antisymm (key h) (key h.symm)))

/-- A representative relates some pair. -/
theorem rel_nonempty (ρ : Rep S) : (ρ.1.rel S).Nonempty := by
  obtain ⟨a, b, hab⟩ := ρ.2.2.2
  obtain ⟨σ, hσ⟩ := ρ.normal.sol_nonempty ρ.wf
  rw [Raw.rel_eq hab]
  exact ⟨(a.bind σ, b.bind σ), σ, hσ, rfl, rfl⟩

end Rep

/-- A first-order problem over a pair that has a solution has a
representative. -/
theorem exists_rep {S : Sorts} (hS : S.WellFormed) {P : Prob} (hP : P.FO) {l r : Pat}
    (ht : P.t = tpair l r) (hne : (P.Den S).Nonempty) :
    ∃ ρ : Rep S, ρ.1.rel S = {p | tpair p.1 p.2 ∈ P.Den S} := by
  obtain ⟨r₀, hr, hden⟩ := Prob.normal hS hP hne
  obtain ⟨a, b, hab⟩ := shape_pair hr (hr.sol_nonempty hS) (by
    rw [hden]; rintro g ⟨σ, -, rfl⟩
    exact ⟨_, _, by rw [ht, tpair_bind]⟩)
  exact ⟨⟨r₀, hS, hr, a, b, hab⟩, by simp only [Raw.rel, hden]⟩

/-! ## The representative of a relation -/

/-- The representative that relates the pairs of `X`, if there is one. -/
noncomputable def Rep.mk? (S : Sorts) (X : PRel) : Option (Rep S) :=
  open Classical in if h : ∃ ρ : Rep S, ρ.1.rel S = X then some (Classical.choose h) else none

theorem Rep.mk?_some {S : Sorts} {X : PRel} {ρ : Rep S} (h : Rep.mk? S X = some ρ) :
    ρ.1.rel S = X := by
  unfold Rep.mk? at h
  split at h
  · rename_i hex
    cases h; exact Classical.choose_spec hex
  · cases h

theorem Rep.mk?_none {S : Sorts} {X : PRel} (h : Rep.mk? S X = none) (ρ : Rep S) :
    ρ.1.rel S ≠ X := by
  unfold Rep.mk? at h
  split at h
  · cases h
  · rename_i hno
    exact fun e => hno ⟨ρ, e⟩

theorem Rep.mk?_rel {S : Sorts} (ρ : Rep S) : Rep.mk? S (ρ.1.rel S) = some ρ := by
  cases h : Rep.mk? S (ρ.1.rel S) with
  | none => exact absurd rfl (Rep.mk?_none h ρ)
  | some ρ' => rw [Rep.ext_rel (Rep.mk?_some h)]

/-! ## A raw store as part of a problem -/

/-- The sorts of the variables of a raw store, the variables renamed. -/
noncomputable def Raw.atoms (r : Raw) (ρ : Nat → Nat) : List (Name × Pat) :=
  (List.range r.c.length).flatMap fun v => (r.conj v).toList.map fun n => (n, .var (ρ v))

/-- The exclusions of a raw store, the variables renamed. -/
def Raw.excl (r : Raw) (ρ : Nat → Nat) : List (Eqns Nat) :=
  r.x.map fun θ => Eqns.ren ρ (eqnsOf θ)

theorem Raw.atoms_fo (r : Raw) (ρ : Nat → Nat) : ∀ a ∈ r.atoms ρ, a.2.firstOrder = true := by
  intro a ha
  obtain ⟨v, -, ha⟩ := List.mem_flatMap.1 ha
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 ha
  rfl

theorem Raw.excl_fo {S : Sorts} {r : Raw} (hr : r.Normal S) (ρ : Nat → Nat) :
    ∀ E ∈ r.excl ρ, E.FO := by
  intro E hE q hq
  obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
  exact ⟨rfl, rename_fo ((hr.ex θ hθ).fo b hb) ρ⟩

/-- A substitution satisfies the renamed sorts and exclusions of a raw store
exactly when, read through the renaming, it is a solution of the store. -/
theorem Raw.sol_shift {S : Sorts} (r : Raw) (ρ : Nat → Nat) (σ : Nat → GTerm) :
    ((∀ a ∈ r.atoms ρ, mem S a.1 (a.2.bind σ) = true) ∧ ∀ E ∈ r.excl ρ, ¬ Eqns.Unifies σ E) ↔
      σ ∘ ρ ∈ r.store.Sol S := by
  constructor
  · rintro ⟨ha, hx⟩
    refine ⟨fun v n hn => ?_, fun E hE hu => ?_⟩
    · have hv : v < r.c.length := by
        by_contra h
        change n ∈ r.conj v at hn
        rw [Raw.Normal.conj_of_ge r (Nat.le_of_not_lt h)] at hn; simp at hn
      exact ha (n, .var (ρ v)) (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv,
        List.mem_map.2 ⟨n, Finset.mem_toList.2 hn, rfl⟩⟩)
    · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
      exact hx _ (List.mem_map.2 ⟨θ, hθ, rfl⟩) (unifies_ren.2 hu)
  · rintro ⟨hp, hx⟩
    refine ⟨fun a ha => ?_, fun E hE hu => ?_⟩
    · obtain ⟨v, -, ha⟩ := List.mem_flatMap.1 ha
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 ha
      exact hp v n (Finset.mem_toList.1 hn)
    · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
      exact hx _ (List.mem_map.2 ⟨θ, hθ, rfl⟩) (unifies_ren.1 hu)

/-! ## A representative as a span -/

/-- The two sides of the pattern. -/
def Raw.sides (r : Raw) : Pat × Pat :=
  match r.t with
  | .app (.app _ a) b => (a, b)
  | t => (t, t)

theorem Raw.sides_of {r : Raw} {a b : Pat} (h : r.t = tpair a b) : r.sides = (a, b) := by
  simp [Raw.sides, h, tpair]

/-- The bound variables of an exclusion, as one term. -/
def tupL (θ : Binds) : Pat := θ.foldr (fun b acc => tpair (.var b.1) acc) (.sym "")

/-- The values of an exclusion, as one term. -/
def tupR (θ : Binds) : Pat := θ.foldr (fun b acc => tpair b.2 acc) (.sym "")

theorem tup_unifies (σ : Nat → GTerm) : ∀ θ : Binds,
    (tupL θ).bind σ = (tupR θ).bind σ ↔ Eqns.Unifies σ (eqnsOf θ)
  | [] => by simp [tupL, tupR, eqnsOf, Eqns.Unifies]
  | b :: θ => by
    have ih := tup_unifies σ θ
    show (tpair (.var b.1) (tupL θ)).bind σ = (tpair b.2 (tupR θ)).bind σ ↔
      Eqns.Unifies σ ((Term.var b.1, b.2) :: eqnsOf θ)
    rw [tpair_bind, tpair_bind, Eqns.unifies_cons, ← ih]
    exact ⟨tpair_inj, fun h => by rw [h.1, h.2]⟩

/-- The constraints of a raw store: `(s $v)` for each sort of each variable,
and `(!= l r)` for each exclusion, `l` the tuple of its variables and `r` of
their values. -/
noncomputable def Raw.cons (r : Raw) : List Pat :=
  ((List.range r.c.length).flatMap fun v =>
    (r.conj v).toList.map fun n => Term.app (.sym n) (.var v)) ++
  r.x.map fun θ => .app (.app (.sym neSym) (tupL θ)) (tupR θ)

/-- A raw store over a pair, as a span. -/
noncomputable def Raw.toSpan (r : Raw) : Span := ⟨r.sides.1, r.sides.2, r.cons⟩

theorem Raw.cons_holds {S : Sorts} (r : Raw) (σ : Nat → GTerm) :
    (∀ c ∈ r.cons, c.bind σ ∈ S.interp) ↔ σ ∈ r.store.Sol S := by
  constructor
  · intro h
    refine ⟨fun v n hn => ?_, fun E hE hu => ?_⟩
    · have hv : v < r.c.length := by
        by_contra h'
        change n ∈ r.conj v at hn
        rw [Raw.Normal.conj_of_ge r (Nat.le_of_not_lt h')] at hn; simp at hn
      have := h (.app (.sym n) (.var v)) (List.mem_append_left _ (List.mem_flatMap.2
        ⟨v, List.mem_range.2 hv, List.mem_map.2 ⟨n, Finset.mem_toList.2 hn, rfl⟩⟩))
      exact mem_iff_Mem.2 this
    · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hE
      have := h _ (List.mem_append_right _ (List.mem_map.2 ⟨θ, hθ, rfl⟩))
      exact this.2 ((tup_unifies σ θ).2 hu)
  · rintro ⟨hp, hx⟩ c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨v, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hc
      exact mem_iff_Mem.1 (hp v n (Finset.mem_toList.1 hn))
    · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hc
      exact ⟨rfl, fun e => hx _ (List.mem_map.2 ⟨θ, hθ, rfl⟩) ((tup_unifies σ θ).1 e)⟩

/-- Written as a span, a raw store over a pair relates in the interpretation
of the sorts the pairs it relates. -/
theorem Raw.toSpan_den {S : Sorts} {r : Raw} {a b : Pat} (h : r.t = tpair a b) :
    r.toSpan.denAt S.interp = r.rel S := by
  rw [Raw.rel_eq h]
  ext p
  simp only [Span.denAt, Raw.toSpan, Raw.sides_of h, Set.mem_ofPred_eq, Raw.cons_holds]
  constructor
  · rintro ⟨σ, e₁, e₂, hσ⟩; exact ⟨σ, hσ, e₁, e₂⟩
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨σ, e₁, e₂, hσ⟩

end Sorts
end RwLog
