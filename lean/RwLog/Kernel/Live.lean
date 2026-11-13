/-
# Kernel steps with pruning

`live T s` simplifies a span by its theory: it instantiates the span by every
equation the theory forces and drops it if the theory refutes it.
`composeLive` and `meetLive` are `;` and `&` on two answers followed by that.

For a well-formed theory these are exact up to the theory: what they return
stands for the relation computed (`live_ref`, `composeLive_ref`,
`meetLive_ref`), and they return something whenever the relation is live
(`live_dc`, `composeLive_dc`, `meetLive_dc`, and the `_spec` forms with
`LEq`). These are the lemmas a rung's soundness and completeness proofs use
for each kernel step.
-/
import RwLog.Kernel.SimplifyMono
import RwLog.Kernel.Iface
import RwLog.SpanLayer.Modulo

namespace RwLog

variable {T : Theory}

/-- Simplify a span by its theory: instantiate it by every equation the
theory forces, and drop it if the theory refutes it. -/
def live (T : Theory) (s : Span) : List Span := (T.simplify s).toList

def composeLive (T : Theory) (x y : Span) : List Span :=
  match x.compose y with
  | some z => live T z
  | none => []

def meetLive (T : Theory) (x y : Span) : List Span :=
  match x.meet y with
  | some z => live T z
  | none => []

/-- Simplify an optional span. -/
def liveO (T : Theory) : Option Span → List Span
  | some z => live T z
  | none => []

theorem composeLive_eq (T : Theory) (x y : Span) : composeLive T x y = liveO T (x.compose y) := by
  unfold composeLive; cases x.compose y <;> rfl

theorem meetLive_eq (T : Theory) (x y : Span) : meetLive T x y = liveO T (x.meet y) := by
  unfold meetLive; cases x.meet y <;> rfl

theorem live_swap (T : Theory) (s : Span) : live T s.swap = (live T s).map Span.swap := by
  simp only [live, simplify_swap]; cases T.simplify s <;> rfl

/-! ## What simplification keeps -/

/-- The store of an interface of an unrefuted span is unrefuted. -/
theorem storeOn_unref {T : Theory} {x : Span} (hx : T.refutes? x.c = false) (p : Pat) :
    T.refutes? (x.storeOn p) = false := by
  cases h : T.refutes? (x.storeOn p)
  · rfl
  · rw [← hx]
    exact (Checker.refutes_mono T (fun y hy => (List.mem_filter.1 hy).1) h).symm

theorem simplifyWithin_inst (T : Theory) : ∀ (n : Nat) (s s' : Span),
    T.simplifyWithin n s = some s' → ∃ θ : Nat → Pat, s'.l = s.l.bind θ ∧ s'.r = s.r.bind θ
  | n, s, s', h => by
    unfold Theory.simplifyWithin at h
    split at h
    · simp at h
    · split at h
      · rename_i m θ _
        obtain ⟨θ', h1, h2⟩ := simplifyWithin_inst T m _ _ h
        exact ⟨fun v => (θ v).bind θ', by rw [h1]; simp [Span.inst], by rw [h2]; simp [Span.inst]⟩
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨Term.var, by simp [Term.bind_var_id], by simp [Term.bind_var_id]⟩

/-- Every pair a simplified span relates, the original relates too. -/
theorem simplify_pairs {T : Theory} {s s' : Span} (h : T.simplify s = some s') :
    s'.den.at Set.univ ⊆ s.den.at Set.univ := by
  obtain ⟨θ, h1, h2⟩ := simplifyWithin_inst T _ _ _ h
  rintro ⟨u, v⟩ ⟨S, ⟨σ, hx⟩, -⟩
  simp only [Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl, -⟩ := hx
  refine ⟨s.c.at fun w => (θ w).bind σ, ⟨fun w => (θ w).bind σ, ?_⟩, Set.subset_univ _⟩
  simp only [h1, h2, Term.bind_bind]

/-! ## Exactness up to the theory -/

section LiveSpec

variable (hT : ∀ ρ ∈ T, ρ.WellFormed)
include hT

/-- Simplifying keeps a span's meaning up to the theory, and keeps every live
span. -/
theorem liveO_spec {o : Option Span} {D : GRel} (hD : Span.denO o = D) :
    (∀ z ∈ liveO T o, LEq T z.den D) ∧ (Live T D → ∃ z, z ∈ liveO T o) := by
  cases o with
  | none =>
    subst hD
    refine ⟨fun z hz => by simp [liveO] at hz, ?_⟩
    rintro ⟨M, -, p, S, h, -⟩
    exact absurd h (Set.notMem_empty _)
  | some u =>
    subst hD
    refine ⟨fun z hz => ?_, fun hl => ?_⟩
    · have hz : T.simplify u = some z := by simpa [liveO, live] using hz
      have he := (Theory.simplify_exact hT u).2 z hz
      have hd : ∀ M, T.Model M → (z.den).at M = (Span.denO (some u)).at M := fun M hM => by
        show (z.den).at M = (u.den).at M
        rw [← Span.denAt_eq, ← Span.denAt_eq, he M hM]
      exact ⟨fun M hM => (hd M hM).ge, fun M hM => (hd M hM).le⟩
    · cases hs : T.simplify u with
      | none => exact absurd ((Theory.simplify_exact hT u).1 hs) (not_dead_iff.2 hl)
      | some z => exact ⟨z, by simp [liveO, live, hs]⟩

theorem composeLive_spec (x y : Span) :
    (∀ z ∈ composeLive T x y, LEq T z.den ((x.den).comp y.den)) ∧
      (Live T ((x.den).comp y.den) → ∃ z, z ∈ composeLive T x y) :=
  liveO_spec hT (o := x.compose y) (compose_den x y)

theorem meetLive_spec (x y : Span) :
    (∀ z ∈ meetLive T x y, LEq T z.den ((x.den).meet y.den)) ∧
      (Live T ((x.den).meet y.den) → ∃ z, z ∈ meetLive T x y) :=
  liveO_spec hT (o := x.meet y) (meet_den x y)

theorem live_leq {u z : Span} (hz : z ∈ live T u) : LEq T z.den u.den :=
  (liveO_spec hT (o := some u) rfl).1 z hz

end LiveSpec

/-! ## Simplified candidates -/

section Live

variable (hwf : ∀ ρ ∈ T, ρ.WellFormed)
include hwf

theorem live_ref {z c : Span} (h : c ∈ live T z) : Ref T c z.den := by
  have he := live_leq hwf h
  have hs : T.simplify z = some c := by simpa [live] using h
  exact ⟨⟨he.2, simplify_pairs hs⟩, he.1⟩

theorem live_dc {z : Span} {X : GRel} (h : LCov T z.den X) : DC T (live T z) X := by
  cases hs : T.simplify z with
  | none =>
    have hd := (Theory.simplify_exact hwf z).1 hs
    exact Or.inl (DeadR.of_dom h (deadR_den.2 hd))
  | some c =>
    have hc : c ∈ live T z := by simp [live, hs]
    exact Or.inr ⟨c, hc, (live_ref hwf hc).2.trans h⟩

theorem composeLive_ref {x y c : Span} {X Y : GRel} (hx : Ref T x X) (hy : Ref T y Y)
    (hc : c ∈ composeLive T x y) : Ref T c (X.comp Y) := by
  unfold composeLive at hc
  split at hc
  · rename_i z hz
    refine (live_ref hwf hc).trans ?_ ?_ <;> rw [compose_some hz]
    · exact hx.1.comp hy.1
    · exact hx.2.comp hy.2
  · simp at hc

theorem meetLive_ref {x y c : Span} {X Y : GRel} (hx : Ref T x X) (hy : Ref T y Y)
    (hc : c ∈ meetLive T x y) : Ref T c (X.meet Y) := by
  unfold meetLive at hc
  split at hc
  · rename_i z hz
    refine (live_ref hwf hc).trans ?_ ?_ <;> rw [meet_some hz]
    · exact hx.1.meet hy.1
    · exact hx.2.meet hy.2
  · simp at hc

theorem composeLive_dc {x y : Span} {X Y : GRel} (hx : LCov T x.den X) (hy : LCov T y.den Y) :
    DC T (composeLive T x y) (X.comp Y) := by
  have hd := hx.comp hy
  unfold composeLive
  split
  · rename_i z hz
    rw [← compose_some hz] at hd
    exact live_dc hwf hd
  · rename_i hz
    rw [compose_none hz] at hd
    exact Or.inl (DeadR.of_empty hd)

theorem meetLive_dc {x y : Span} {X Y : GRel} (hx : LCov T x.den X) (hy : LCov T y.den Y) :
    DC T (meetLive T x y) (X.meet Y) := by
  have hd := hx.meet hy
  unfold meetLive
  split
  · rename_i z hz
    rw [← meet_some hz] at hd
    exact live_dc hwf hd
  · rename_i hz
    rw [meet_none hz] at hd
    exact Or.inl (DeadR.of_empty hd)

/-- Joining every answer of one side with every answer of the other covers
the composition of what they cover. -/
theorem join_comp_dc {xs ys : List Span} {X Y : GRel} (hx : DC T xs X) (hy : DC T ys Y) :
    DC T (xs.flatMap fun x => ys.flatMap fun y => composeLive T x y) (X.comp Y) := by
  rcases hx with hx | ⟨x, hxm, hx⟩
  · exact Or.inl hx.comp_left
  rcases hy with hy | ⟨y, hym, hy⟩
  · exact Or.inl hy.comp_right
  refine (composeLive_dc hwf hx hy).mono fun c hc => ?_
  simp only [List.mem_flatMap]
  exact ⟨x, hxm, y, hym, hc⟩

theorem join_meet_dc {xs ys : List Span} {X Y : GRel} (hx : DC T xs X) (hy : DC T ys Y) :
    DC T (xs.flatMap fun x => ys.flatMap fun y => meetLive T x y) (X.meet Y) := by
  rcases hx with hx | ⟨x, hxm, hx⟩
  · exact Or.inl hx.meet_left
  rcases hy with hy | ⟨y, hym, hy⟩
  · exact Or.inl hy.meet_right
  refine (meetLive_dc hwf hx hy).mono fun c hc => ?_
  simp only [List.mem_flatMap]
  exact ⟨x, hxm, y, hym, hc⟩

end Live

end RwLog
