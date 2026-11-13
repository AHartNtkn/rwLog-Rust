/-
# Simplification keeps coverage (`SimpLaws`)

Simplification refutes a span or instantiates it by the equations its theory
forces; both are read off firings on the closure of the store. The closure
only adds atoms, so a firing on a store lifts to every store that contains an
instance of it (`firings_lift`): the match is found again (`matchAll` is
complete), equations that hold still hold, and equations without a unifier
still have none. Hence:

* the closure is monotone under instance and superset (`saturate_inst`);
* if a store `e` has no refutation and no forced equation left, a store `c`
  with an instance inside `e` is not refuted, and every equation it forces
  already holds under that instance (`stable_lift`);
* so simplifying a span that covers a simplified span never drops it and
  only instantiates it in ways the cover factors through
  (`simplifyWithin_under`), which is the coverage half of `simplify_mono`.

The composition and intersection laws follow from the coverage half: the
composite of a simplified operand is an instance of the composite, and a
simplified composite is covered by the composite of the simplified operand,
because each operand covers its part of the simplified composite, whose store
is stable (`under_stable`).
-/
import RwLog.Kernel.RefuteCorrect

namespace RwLog

namespace Mono

open Term Checker Matching

/-! ## Lifting a match along an instance -/

/-- `matchAll` finds a match that agrees with any substitution sending every
pattern into the targets. -/
theorem matchAll_agree (σ : Nat → Pat) : ∀ (ps ts : List Pat) (θ : PSubst), Agree θ σ →
    (∀ p ∈ ps, p.bind σ ∈ ts) → ∃ r ∈ matchAll ps ts θ, Agree r.1 σ
  | [], _, θ, hθ, _ => ⟨(θ, []), by simp [matchAll], hθ⟩
  | p :: ps, ts, θ, hθ, hps => by
    obtain ⟨θ₁, h₁, a₁⟩ := matchInto_complete σ p θ hθ
    obtain ⟨r, hr, ha⟩ :=
      matchAll_agree σ ps ts θ₁ a₁ fun q hq => hps q (List.mem_cons_of_mem _ hq)
    refine ⟨(r.1, p.bind σ :: r.2), ?_, ha⟩
    simp only [matchAll, List.mem_flatMap]
    refine ⟨p.bind σ, hps p (List.mem_cons_self ..), ?_⟩
    rw [h₁]
    exact List.mem_map.2 ⟨r, hr, rfl⟩

/-- A match of a rule's heads into `d` lifts to a match into any store that
contains the instance of `d` by `τ`, and agrees with it on every term over the
head variables. -/
theorem match_lift {ρ : TRule} {d e : Store} {r : PSubst × List Pat}
    (hr : r ∈ matchAll ρ.heads d []) (τ : Nat → Pat) (hde : ∀ x ∈ d, x.bind τ ∈ e) :
    ∃ r' ∈ matchAll ρ.heads e [], ∀ t : Pat, (∀ v ∈ t.vars, ∃ h ∈ ρ.heads, v ∈ h.vars) →
      t.bind r'.1.apply = (t.bind r.1.apply).bind τ := by
  obtain ⟨-, -, hrd, hrh⟩ := matchAll_sound _ _ _ _ hr
  let σ : Nat → Pat := fun v => (r.1.apply v).bind τ
  have hheads : ∀ p ∈ ρ.heads, p.bind σ ∈ e := fun p hp => by
    have hm : p.bind r.1.apply ∈ r.2 := by
      rw [← hrh r.1 (Ext.refl _)]; exact List.mem_map_of_mem hp
    have := hde _ (hrd _ hm)
    rwa [bind_bind] at this
  obtain ⟨r', hr', ha⟩ := matchAll_agree σ ρ.heads e [] (fun _ _ h => by simp at h) hheads
  refine ⟨r', hr', fun t ht => ?_⟩
  rw [bind_bind]
  refine bind_congr fun v hv => ?_
  obtain ⟨h, hh, hvh⟩ := ht v hv
  obtain ⟨x, hx⟩ := (matchAll_sound _ _ _ _ hr').2.1 h hh v hvh
  have : r'.1.apply v = x := by simp [PSubst.apply, hx]
  rw [this]
  exact (ha v x hx).symm

/-! ## Lifting a firing -/

/-- The three outcomes of solving a firing's equations. -/
theorem firingOfEqs_cases (E : List (Pat × Pat)) (bs : Store) :
    ((∀ e ∈ E, e.1 = e.2) ∧ firingOfEqs E bs = .add bs) ∨
    (¬ (∀ e ∈ E, e.1 = e.2) ∧ solve E = none ∧ firingOfEqs E bs = .refuted) ∨
    (¬ (∀ e ∈ E, e.1 = e.2) ∧ ∃ θ, solve E = some θ ∧ firingOfEqs E bs = .bind θ) := by
  unfold firingOfEqs
  by_cases hall : ∀ e ∈ E, e.1 = e.2
  · left
    have hy : (E.all fun e => decide (e.1 = e.2)) = true := by simpa using hall
    refine ⟨hall, ?_⟩
    simp only [hy, ↓reduceIte]
  · right
    have hn : ¬ (E.all fun e => decide (e.1 = e.2)) = true := by simpa using hall
    cases hs : solve E with
    | none => left; exact ⟨hall, rfl, by simp [hn]⟩
    | some θ => right; exact ⟨hall, θ, rfl, by simp [hn]⟩

/-- What a firing becomes among the firings `F` on a store that contains the
instance by `τ` of the store it fired on. -/
def Lifted (τ : Nat → Pat) (F : List Firing) : Firing → Prop
  | .refuted => Firing.refuted ∈ F
  | .add bs => Firing.add (bs.map (Term.bind τ)) ∈ F
  | .bind θ => Firing.refuted ∈ F ∨ (∃ θ', Firing.bind θ' ∈ F) ∨ ∀ v, (θ v).bind τ = τ v

theorem mk_firing_fail {ρ : TRule} {c : Store} {r : PSubst × List Pat}
    (hr : r ∈ matchAll ρ.heads c []) (hb : ρ.body = .fail) : Firing.refuted ∈ ρ.firings c := by
  simp only [TRule.firings, List.mem_map]
  exact ⟨r, hr, by rw [hb]⟩

theorem mk_firing_conj {ρ : TRule} {c : Store} {r : PSubst × List Pat}
    (hr : r ∈ matchAll ρ.heads c []) {eqs : List (Pat × Pat)} {cs : List Pat}
    (hb : ρ.body = .conj eqs cs) :
    firingOfEqs (instEqs eqs r) (cs.map (Term.bind r.1.apply)) ∈ ρ.firings c := by
  simp only [TRule.firings, List.mem_map]
  exact ⟨r, hr, by rw [hb]; rfl⟩

theorem firings_lift {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {d e : Store} {τ : Nat → Pat}
    (hde : ∀ x ∈ d, x.bind τ ∈ e) {f : Firing} (hf : f ∈ T.firings d) :
    Lifted τ (T.firings e) f := by
  simp only [Theory.firings, List.mem_flatMap] at hf
  obtain ⟨ρ, hρ, hf⟩ := hf
  split_ifs at hf with hbd
  swap
  · cases hf
  have up : ∀ f', f' ∈ ρ.firings e → f' ∈ T.firings e := fun f' h =>
    List.mem_flatMap.2 ⟨ρ, hρ, by simp only [hbd, ↓reduceIte]; exact h⟩
  obtain ⟨r, hr, h⟩ := mem_firings hf
  obtain ⟨r', hr', hl⟩ := match_lift hr τ hde
  rcases h with ⟨hb, rfl⟩ | ⟨eqs, cs, hb, rfl⟩
  · exact up _ (mk_firing_fail hr' hb)
  have hwa := (hwf ρ hρ).1
  have hwe := (hwf ρ hρ).2
  rw [hb] at hwa hwe
  have hE : instEqs eqs r' = (instEqs eqs r).map fun e => (e.1.bind τ, e.2.bind τ) := by
    simp only [instEqs, List.map_map]
    refine List.map_congr_left fun e he => ?_
    simp only [Function.comp_apply]
    rw [hl e.1 fun v hv => hwe e he v (List.mem_append_left _ hv),
      hl e.2 fun v hv => hwe e he v (List.mem_append_right _ hv)]
  have hB : cs.map (Term.bind r'.1.apply) = (cs.map (Term.bind r.1.apply)).map (Term.bind τ) := by
    rw [List.map_map]
    exact List.map_congr_left fun b hb' => hl b (hwa b hb')
  have hmem := up _ (mk_firing_conj hr' hb)
  rw [hE, hB] at hmem
  set E := instEqs eqs r
  set bs := cs.map (Term.bind r.1.apply)
  have hU : (∀ e ∈ E.map fun e => (e.1.bind τ, e.2.bind τ), e.1 = e.2) ↔ Eqns.Unifies τ E := by
    constructor
    · intro h p hp
      exact h (p.1.bind τ, p.2.bind τ) (List.mem_map.2 ⟨p, hp, rfl⟩)
    · intro h e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact h p hp
  have hsol : ∀ θ'', solve (E.map fun e => (e.1.bind τ, e.2.bind τ)) = some θ'' →
      Eqns.Unifies (fun v => (τ v).bind θ'') E := by
    intro θ'' hs p hp
    have := (solve_some hs).1 (p.1.bind τ, p.2.bind τ) (List.mem_map.2 ⟨p, hp, rfl⟩)
    simpa [bind_bind] using this
  rcases firingOfEqs_cases E bs with ⟨ht, hf⟩ | ⟨hnt, hs, hf⟩ | ⟨hnt, θ, hs, hf⟩
  · rw [hf]
    have ht' : ∀ e ∈ E.map fun e => (e.1.bind τ, e.2.bind τ), e.1 = e.2 :=
      hU.2 fun p hp => by rw [ht p hp]
    rcases firingOfEqs_cases (E.map fun e => (e.1.bind τ, e.2.bind τ)) (bs.map (Term.bind τ))
      with ⟨-, hf'⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [hf'] at hmem; exact hmem
    · exact absurd ht' hn
    · exact absurd ht' hn
  · rw [hf]
    rcases firingOfEqs_cases (E.map fun e => (e.1.bind τ, e.2.bind τ)) (bs.map (Term.bind τ))
      with ⟨ht', -⟩ | ⟨-, -, hf'⟩ | ⟨-, θ'', hs', -⟩
    · exact absurd (hU.1 ht') (solve_none hs _)
    · rw [hf'] at hmem; exact hmem
    · exact absurd (hsol θ'' hs') (solve_none hs _)
  · rw [hf]
    rcases firingOfEqs_cases (E.map fun e => (e.1.bind τ, e.2.bind τ)) (bs.map (Term.bind τ))
      with ⟨ht', -⟩ | ⟨-, -, hf'⟩ | ⟨-, θ'', -, hf'⟩
    · exact Or.inr (Or.inr ((solve_some hs).2 τ (hU.1 ht')))
    · rw [hf'] at hmem; exact Or.inl hmem
    · rw [hf'] at hmem; exact Or.inr (Or.inl ⟨θ'', hmem⟩)

/-! ## The closure is monotone under instance -/

/-- The atoms a firing on a closure adds are in the closure. -/
theorem add_closed {T : Theory} {c : Store} {bs : Store}
    (h : Firing.add bs ∈ T.firings (T.saturate c)) : ∀ x ∈ bs, x ∈ T.saturate c := by
  intro x hx
  by_contra hn
  have hnew : x ∈ T.newAtoms (T.saturate c) := by
    simp only [Theory.newAtoms, List.mem_filter, List.mem_eraseDups, List.mem_flatMap,
      Bool.not_eq_true']
    refine ⟨⟨_, h, hx⟩, ?_⟩
    cases hc : (T.saturate c).contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hn
  rw [T.saturate_closed c] at hnew
  cases hnew

/-- The closure of a store, instantiated, lies in the closure of every store
that contains the instance of the store. -/
theorem saturate_inst {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {c e : Store} {τ : Nat → Pat}
    (h : ∀ x ∈ c, x.bind τ ∈ e) : ∀ x ∈ T.saturate c, x.bind τ ∈ T.saturate e := by
  refine saturate_induct (T := T) (fun x => x.bind τ ∈ T.saturate e) ?_ c
    (fun x hx => T.sub_saturate e _ (h x hx))
  intro d hd bs hf x hx
  have hl : Lifted τ (T.firings (T.saturate e)) (.add bs) := firings_lift hwf hd hf
  exact add_closed hl _ (List.mem_map_of_mem hx)

/-- A store with no refutation and no forced equation left. -/
def Stable (T : Theory) (c : Store) : Prop := T.refutes? c = false ∧ T.bind? c = none

/-- A store with an instance inside a stable store is not refuted, and the
equations it forces hold under that instance. -/
theorem stable_lift {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {c e : Store} {τ : Nat → Pat}
    (hst : Stable T e) (h : ∀ x ∈ c, x.bind τ ∈ e) :
    T.refutes? c = false ∧ ∀ θ, T.bind? c = some θ → ∀ v, (θ v).bind τ = τ v := by
  have hsat := saturate_inst hwf h
  have hnoref : Firing.refuted ∉ T.firings (T.saturate e) := fun hm => by
    have : T.refutes? e = true := by
      rw [Theory.refutes?]; exact List.any_eq_true.2 ⟨_, hm, rfl⟩
    rw [hst.1] at this; cases this
  have hnobind : ∀ θ', Firing.bind θ' ∉ T.firings (T.saturate e) := fun θ' hm => by
    have := hst.2
    rw [Theory.bind?, List.findSome?_eq_none_iff] at this
    have := this _ hm
    cases this
  constructor
  · cases hr : T.refutes? c with
    | false => rfl
    | true =>
      rw [Theory.refutes?] at hr
      obtain ⟨f, hf, hfr⟩ := List.any_eq_true.1 hr
      cases f with
      | refuted => exact absurd (firings_lift hwf hsat hf) hnoref
      | add _ => cases hfr
      | bind _ => cases hfr
  · intro θ hb
    rw [Theory.bind?] at hb
    obtain ⟨f, hf, hfb⟩ := List.exists_of_findSome?_eq_some hb
    cases f with
    | refuted => cases hfb
    | add _ => cases hfb
    | bind θ' =>
      cases hfb
      have hl : Lifted τ (T.firings (T.saturate e)) (.bind θ) := firings_lift hwf hsat hf
      rcases hl with h1 | ⟨θ'', h2⟩ | h3
      · exact absurd h1 hnoref
      · exact absurd h2 (hnobind θ'')
      · exact h3

/-! ## Simplification instantiates -/

/-- A simplified span is an instance of the span, with the instance of its
store. -/
theorem simplifyWithin_parts (T : Theory) : ∀ (n : Nat) (s s' : Span),
    T.simplifyWithin n s = some s' → ∃ θ : Nat → Pat, s'.l = s.l.bind θ ∧ s'.r = s.r.bind θ ∧
      ∀ x, x ∈ s'.c ↔ ∃ a ∈ s.c, a.bind θ = x := by
  intro n
  induction n with
  | zero =>
    intro s s' h
    cases hr : T.refutes? s.c
    · rw [sw_done hr (Or.inl rfl)] at h; cases h
      exact ⟨Term.var, by simp, by simp, by simp [List.mem_eraseDups]⟩
    · rw [sw_refuted hr] at h; cases h
  | succ n ih =>
    intro s s' h
    cases hr : T.refutes? s.c
    · cases hb : T.bind? s.c with
      | some θ =>
        rw [sw_bind hr hb] at h
        obtain ⟨θ', h1, h2, h3⟩ := ih _ s' h
        refine ⟨fun v => (θ v).bind θ', by rw [h1]; simp [Span.inst], by rw [h2]; simp [Span.inst],
          fun x => ?_⟩
        rw [h3]
        simp [Span.inst, List.mem_eraseDups]
      | none =>
        rw [sw_done hr (Or.inr hb)] at h; cases h
        exact ⟨Term.var, by simp, by simp, by simp [List.mem_eraseDups]⟩
    · rw [sw_refuted hr] at h; cases h

/-- Simplifying a span whose store has an instance inside a stable store keeps
it, and instantiates it only in ways that instance factors through. -/
theorem simplifyWithin_under {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {e : Store}
    (hst : Stable T e) (τ : Nat → Pat) : ∀ (n : Nat) (f : Span), (∀ a ∈ f.c, a.bind τ ∈ e) →
      ∃ f' θ, T.simplifyWithin n f = some f' ∧ (∀ v, (θ v).bind τ = τ v) ∧
        f'.l = f.l.bind θ ∧ f'.r = f.r.bind θ ∧ ∀ x ∈ f'.c, ∃ a ∈ f.c, a.bind θ = x := by
  intro n
  induction n with
  | zero =>
    intro f hf
    obtain ⟨hr, -⟩ := stable_lift hwf hst hf
    exact ⟨_, Term.var, sw_done hr (Or.inl rfl), fun _ => rfl, by simp, by simp,
      by simp [List.mem_eraseDups]⟩
  | succ n ih =>
    intro f hf
    obtain ⟨hr, hbind⟩ := stable_lift hwf hst hf
    cases hb : T.bind? f.c with
    | none =>
      exact ⟨_, Term.var, sw_done hr (Or.inr hb), fun _ => rfl, by simp, by simp,
        by simp [List.mem_eraseDups]⟩
    | some θ =>
      have hθ := hbind θ hb
      have hτ : (fun v => (θ v).bind τ) = τ := funext hθ
      have hf' : ∀ a ∈ (f.inst θ).c, a.bind τ ∈ e := by
        intro a ha
        simp only [Span.inst, List.mem_eraseDups, List.mem_map] at ha
        obtain ⟨b, hb', rfl⟩ := ha
        rw [bind_bind, hτ]; exact hf b hb'
      obtain ⟨f', θ', h1, h2, h3, h4, h5⟩ := ih (f.inst θ) hf'
      refine ⟨f', fun v => (θ v).bind θ', by rw [sw_bind hr hb]; exact h1, fun v => ?_,
        by rw [h3]; simp [Span.inst], by rw [h4]; simp [Span.inst], fun x hx => ?_⟩
      · rw [bind_bind]
        have : (fun w => (θ' w).bind τ) = τ := funext h2
        rw [this]; exact hθ v
      · obtain ⟨a, ha, rfl⟩ := h5 x hx
        simp only [Span.inst, List.mem_eraseDups, List.mem_map] at ha
        obtain ⟨b, hb', rfl⟩ := ha
        exact ⟨b, hb', by simp⟩

/-! ## Coverage as a substitution -/

/-- `τ` sends `f` onto `x`: the sides agree and the store of `f` lands inside
the store of `x`. -/
def SCov (f x : Span) (τ : Nat → Pat) : Prop :=
  f.l.bind τ = x.l ∧ f.r.bind τ = x.r ∧ ∀ a ∈ f.c, a.bind τ ∈ x.c

theorem SCov.covers {f x : Span} {τ : Nat → Pat} (h : SCov f x τ) : f.Covers x := by
  rintro _ ⟨σ, rfl⟩
  let g : Nat → GTerm := fun v => (τ v).bind σ
  refine ⟨(f.l.bind g, f.r.bind g, f.c.at g), ⟨g, rfl⟩, ?_, ?_, ?_⟩
  · show f.l.bind g = x.l.bind σ
    rw [← h.1, bind_bind]
  · show f.r.bind g = x.r.bind σ
    rw [← h.2.1, bind_bind]
  · intro t ht
    simp only [Store.at, List.mem_toFinset, List.mem_map] at ht ⊢
    obtain ⟨c, hc, rfl⟩ := ht
    exact ⟨c.bind τ, h.2.2 c hc, by rw [bind_bind]⟩

theorem covers_scov {f x : Span} (h : f.Covers x) : ∃ τ, SCov f x τ := by
  have h := covers?_complete h
  unfold Span.covers? at h
  cases h₁ : matchInto f.l x.l [] with
  | none => rw [h₁] at h; simp at h
  | some θ₁ =>
    rw [h₁, Option.bind_some] at h
    cases h₂ : matchInto f.r x.r θ₁ with
    | none => rw [h₂] at h; simp at h
    | some θ₂ =>
      rw [h₂] at h
      simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ h
      obtain ⟨-, -, k₁⟩ := matchInto_sound _ _ _ _ h₁
      obtain ⟨e₂, -, k₂⟩ := matchInto_sound _ _ _ _ h₂
      obtain ⟨e₃, -, -, -⟩ := matchAll_sound _ _ _ _ hr
      exact ⟨r.1.apply, k₁ r.1 (e₂.trans e₃), k₂ r.1 e₃, matchAll_sound_mem hr r.1 (Ext.refl _)⟩

theorem covers_eraseDups (s : Span) : Span.Covers ⟨s.l, s.r, s.c.eraseDups⟩ s :=
  SCov.covers (τ := Term.var) ⟨by simp, by simp, by simp [List.mem_eraseDups]⟩

theorem simplify_of_stable {T : Theory} {s : Span} (h : Stable T s.c) :
    T.simplify s = some ⟨s.l, s.r, s.c.eraseDups⟩ :=
  sw_done h.1 (Or.inr h.2)

theorem stable_of_simplify {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {s s' : Span}
    (h : T.simplify s = some s') : Stable T s'.c :=
  simplifyWithin_stable hwf _ s s' le_rfl h

/-- A span covers its simplification. -/
theorem simplify_covers {T : Theory} {s s' : Span} (h : T.simplify s = some s') : s.Covers s' := by
  obtain ⟨θ, h1, h2, h3⟩ := simplifyWithin_parts T _ _ _ h
  exact SCov.covers (τ := θ) ⟨h1.symm, h2.symm, fun a ha => (h3 _).2 ⟨a, ha, rfl⟩⟩

/-! ## The coverage half -/

/-- A span that covers a span with a stable store simplifies to a span that
still covers it. -/
theorem under_stable {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {f w : Span}
    (hst : Stable T w.c) (h : f.Covers w) : ∃ f', T.simplify f = some f' ∧ f'.Covers w := by
  obtain ⟨τ, hl, hr, hc⟩ := covers_scov h
  obtain ⟨f', θ, h1, h2, h3, h4, h5⟩ := simplifyWithin_under hwf hst τ f.c.varCount f hc
  have hτ : (fun v => (θ v).bind τ) = τ := funext h2
  refine ⟨f', h1, SCov.covers (τ := τ) ⟨?_, ?_, fun x hx => ?_⟩⟩
  · rw [h3, bind_bind, hτ, hl]
  · rw [h4, bind_bind, hτ, hr]
  · obtain ⟨a, ha, rfl⟩ := h5 x hx
    rw [bind_bind, hτ]; exact hc a ha

theorem simplify_keeps {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) {f x : Span}
    (h : f.Covers x) : T.simplify x = none ∨
      ∃ f' x', T.simplify f = some f' ∧ T.simplify x = some x' ∧ f'.Covers x' := by
  cases hx : T.simplify x with
  | none => exact Or.inl rfl
  | some x' =>
    obtain ⟨f', hf', hc⟩ :=
      under_stable hwf (stable_of_simplify hwf hx) (h.trans (simplify_covers hx))
    exact Or.inr ⟨f', x', hf', rfl, hc⟩

/-! ## Composition and intersection -/

/-- Whatever relates every triple of `w` up to a smaller store is a span that
covers `w`. -/
theorem of_dominates {o : Option Span} {w : Span}
    (h : ∀ x ∈ w.den, ∃ y ∈ Span.denO o, y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 ⊆ x.2.2) :
    ∃ u, o = some u ∧ u.Covers w := by
  cases o with
  | none =>
    obtain ⟨x, hx⟩ := w.den_nonempty
    obtain ⟨y, hy, -⟩ := h x hx
    cases hy
  | some u => exact ⟨u, rfl, h⟩

theorem compose_covers {s s' t t' w₁ : Span} (hs : s.Covers s') (ht : t.Covers t')
    (h : s'.compose t' = some w₁) : ∃ w, s.compose t = some w ∧ w.Covers w₁ := by
  apply of_dominates
  rw [compose_den, compose_some h]
  rintro ⟨a, b, S⟩ ⟨m, S₁, S₂, h₁, h₂, hS⟩
  obtain ⟨⟨a', m', S₁'⟩, hy₁, e1, e2, e3⟩ := hs _ h₁
  obtain ⟨⟨m'', b', S₂'⟩, hy₂, f1, f2, f3⟩ := ht _ h₂
  simp only at e1 e2 e3 f1 f2 f3 hS
  subst e1 e2 f1 f2 hS
  exact ⟨(_, _, S₁' ∪ S₂'), ⟨_, S₁', S₂', hy₁, hy₂, rfl⟩, rfl, rfl, Finset.union_subset_union e3 f3⟩

theorem meet_covers {s s' t t' w₁ : Span} (hs : s.Covers s') (ht : t.Covers t')
    (h : s'.meet t' = some w₁) : ∃ w, s.meet t = some w ∧ w.Covers w₁ := by
  apply of_dominates
  rw [meet_den, meet_some h]
  rintro ⟨a, b, S⟩ ⟨S₁, S₂, h₁, h₂, hS⟩
  obtain ⟨⟨a', b', S₁'⟩, hy₁, e1, e2, e3⟩ := hs _ h₁
  obtain ⟨⟨a'', b'', S₂'⟩, hy₂, f1, f2, f3⟩ := ht _ h₂
  simp only at e1 e2 e3 f1 f2 f3 hS
  subst e1 e2 f1 f2 hS
  exact ⟨(_, _, S₁' ∪ S₂'), ⟨S₁', S₂', hy₁, hy₂, rfl⟩, rfl, rfl, Finset.union_subset_union e3 f3⟩

/-- Spans that cover the two halves of `w` through a middle term compose to a
span that covers `w`. -/
theorem compose_back {s₁ s₂ w : Span} {M : Pat} (h₁ : s₁.Covers ⟨w.l, M, w.c⟩)
    (h₂ : s₂.Covers ⟨M, w.r, w.c⟩) : ∃ u, s₁.compose s₂ = some u ∧ u.Covers w := by
  apply of_dominates
  rw [compose_den]
  rintro _ ⟨σ, rfl⟩
  obtain ⟨⟨a, m, S₁⟩, hy₁, e1, e2, e3⟩ := h₁ _ ⟨σ, rfl⟩
  obtain ⟨⟨m', b, S₂⟩, hy₂, f1, f2, f3⟩ := h₂ _ ⟨σ, rfl⟩
  simp only at e1 e2 e3 f1 f2 f3
  subst e1 e2 f2
  rw [f1] at hy₂
  exact ⟨(_, _, S₁ ∪ S₂), ⟨_, S₁, S₂, hy₁, hy₂, rfl⟩, rfl, rfl, Finset.union_subset e3 f3⟩

theorem meet_back {s₁ s₂ w : Span} (h₁ : s₁.Covers w) (h₂ : s₂.Covers w) :
    ∃ u, s₁.meet s₂ = some u ∧ u.Covers w := by
  apply of_dominates
  rw [meet_den]
  intro x hx
  obtain ⟨⟨a, b, S₁⟩, hy₁, e1, e2, e3⟩ := h₁ _ hx
  obtain ⟨⟨a', b', S₂⟩, hy₂, f1, f2, f3⟩ := h₂ _ hx
  simp only at e1 e2 e3 f1 f2 f3
  subst e1 e2
  rw [f1, f2] at hy₂
  exact ⟨(_, _, S₁ ∪ S₂), ⟨S₁, S₂, hy₁, hy₂, rfl⟩, rfl, rfl, Finset.union_subset e3 f3⟩

theorem left_fin (μ : Nat ⊕ Nat → Term (Nat ⊕ Nat)) (p : Pat) :
    ((Pat.left p).bind μ).rename enc = p.bind fun v => (μ (.inl v)).rename enc := by
  simp only [Pat.left, Term.rename, bind_bind, bind_var]

theorem right_fin (μ : Nat ⊕ Nat → Term (Nat ⊕ Nat)) (p : Pat) :
    ((Pat.right p).bind μ).rename enc = p.bind fun v => (μ (.inr v)).rename enc := by
  simp only [Pat.right, Term.rename, bind_bind, bind_var]

/-- A composite is an instance of each operand, joined at the middle. -/
theorem compose_parts {s t w : Span} (h : s.compose t = some w) : ∃ α β : Nat → Pat,
    w.l = s.l.bind α ∧ w.r = t.r.bind β ∧ s.r.bind α = t.l.bind β ∧
      (∀ a ∈ s.c, a.bind α ∈ w.c) ∧ ∀ a ∈ t.c, a.bind β ∈ w.c := by
  unfold Span.compose at h
  cases hs : solve [(Pat.left s.r, Pat.right t.l)] with
  | none => rw [hs] at h; cases h
  | some μ =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hu := (solve_some hs).1 _ (List.mem_singleton_self _)
    refine ⟨fun v => (μ (.inl v)).rename enc, fun v => (μ (.inr v)).rename enc,
      left_fin μ _, right_fin μ _, ?_, fun a ha => ?_, fun a ha => ?_⟩
    · rw [← left_fin, ← right_fin]; exact congrArg (Term.rename enc) hu
    · rw [← left_fin]
      exact List.mem_map.2 ⟨Pat.left a, List.mem_append_left _ (List.mem_map_of_mem ha), rfl⟩
    · rw [← right_fin]
      exact List.mem_map.2 ⟨Pat.right a, List.mem_append_right _ (List.mem_map_of_mem ha), rfl⟩

/-- A conjunction is an instance of each operand. -/
theorem meet_parts {s t w : Span} (h : s.meet t = some w) : ∃ α β : Nat → Pat,
    w.l = s.l.bind α ∧ w.r = s.r.bind α ∧ w.l = t.l.bind β ∧ w.r = t.r.bind β ∧
      (∀ a ∈ s.c, a.bind α ∈ w.c) ∧ ∀ a ∈ t.c, a.bind β ∈ w.c := by
  unfold Span.meet at h
  cases hs : solve [(Pat.left s.l, Pat.right t.l), (Pat.left s.r, Pat.right t.r)] with
  | none => rw [hs] at h; cases h
  | some μ =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hu1 := (solve_some hs).1 (Pat.left s.l, Pat.right t.l) (by simp)
    have hu2 := (solve_some hs).1 (Pat.left s.r, Pat.right t.r) (by simp)
    refine ⟨fun v => (μ (.inl v)).rename enc, fun v => (μ (.inr v)).rename enc,
      left_fin μ _, left_fin μ _, ?_, ?_, fun a ha => ?_, fun a ha => ?_⟩
    · rw [← right_fin]; exact congrArg (Term.rename enc) hu1
    · rw [← right_fin]; exact congrArg (Term.rename enc) hu2
    · rw [← left_fin]
      exact List.mem_map.2 ⟨Pat.left a, List.mem_append_left _ (List.mem_map_of_mem ha), rfl⟩
    · rw [← right_fin]
      exact List.mem_map.2 ⟨Pat.right a, List.mem_append_right _ (List.mem_map_of_mem ha), rfl⟩

/-- An operand of a composite covers its part of the simplified composite. -/
theorem part_scov {T : Theory} {w w' : Span} (hw : T.simplify w = some w') :
    ∃ θ : Nat → Pat, w'.l = w.l.bind θ ∧ w'.r = w.r.bind θ ∧ ∀ a ∈ w.c, a.bind θ ∈ w'.c := by
  obtain ⟨θ, h1, h2, h3⟩ := simplifyWithin_parts T _ _ _ hw
  exact ⟨θ, h1, h2, fun a ha => (h3 _).2 ⟨a, ha, rfl⟩⟩

/-- The shape shared by the four laws: `u` is the operation on the operands,
`u₁` the operation after simplifying one operand. -/
theorem law {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) (u u₁ : Option Span)
    (ha : ∀ w₁, u₁ = some w₁ → ∃ w, u = some w ∧ w.Covers w₁)
    (hb : ∀ w w', u = some w → T.simplify w = some w' → ∃ w₁, u₁ = some w₁ ∧ w₁.Covers w') :
    Option.Rel Span.Equiv (u₁.bind T.simplify) (u.bind T.simplify) := by
  have key : ∀ w w', u = some w → T.simplify w = some w' →
      ∃ w₁ a, u₁ = some w₁ ∧ T.simplify w₁ = some a ∧ a.Covers w' := by
    intro w w' hu hw
    obtain ⟨w₁, hu₁, hc⟩ := hb w w' hu hw
    obtain ⟨a, ha', hca⟩ := under_stable hwf (stable_of_simplify hwf hw) hc
    exact ⟨w₁, a, hu₁, ha', hca⟩
  have key2 : ∀ w₁ a, u₁ = some w₁ → T.simplify w₁ = some a →
      ∃ w b, u = some w ∧ T.simplify w = some b ∧ b.Covers a := by
    intro w₁ a hu₁ hw₁
    obtain ⟨w, hu, hc⟩ := ha w₁ hu₁
    rcases simplify_keeps hwf hc with hn | ⟨b, a', hb', ha', hcb⟩
    · rw [hw₁] at hn; cases hn
    · rw [hw₁] at ha'; cases ha'
      exact ⟨w, b, hu, hb', hcb⟩
  cases hu₁ : u₁ with
  | none =>
    cases hu : u with
    | none => exact Option.Rel.none
    | some w =>
      cases hw : T.simplify w with
      | none => simp [hw]
      | some w' =>
        obtain ⟨w₁, -, h, -⟩ := key w w' hu hw
        rw [hu₁] at h; cases h
  | some w₁ =>
    cases hw₁ : T.simplify w₁ with
    | none =>
      cases hu : u with
      | none => simp [hw₁]
      | some w =>
        cases hw : T.simplify w with
        | none => simp [hw, hw₁]
        | some w' =>
          obtain ⟨w₁', a, h, ha', -⟩ := key w w' hu hw
          rw [hu₁] at h; cases h
          rw [hw₁] at ha'; cases ha'
    | some a =>
      obtain ⟨w, b, hu, hb', hcb⟩ := key2 w₁ a hu₁ hw₁
      obtain ⟨w₁', a', h, ha', hca⟩ := key w b hu hb'
      rw [hu₁] at h; cases h
      rw [hw₁] at ha'; cases ha'
      rw [hu]
      simpa [hw₁, hb'] using Option.Rel.some ⟨hca, hcb⟩

variable {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed)
include hwf

theorem compose_right (s t : Span) :
    Option.Rel Span.Equiv (((T.simplify t).bind s.compose).bind T.simplify)
      ((s.compose t).bind T.simplify) := by
  refine law hwf _ _ (fun w₁ h => ?_) fun w w' hu hw => ?_
  · obtain ⟨t', ht, hc⟩ := Option.bind_eq_some_iff.1 h
    exact compose_covers (Span.Covers.refl s) (simplify_covers ht) hc
  · obtain ⟨α, β, hl, hr, hm, hcs, hct⟩ := compose_parts hu
    obtain ⟨θ, kl, kr, kc⟩ := part_scov hw
    have hs : s.Covers ⟨w'.l, (s.r.bind α).bind θ, w'.c⟩ :=
      SCov.covers (τ := fun v => (α v).bind θ) ⟨by rw [kl, hl, bind_bind], by rw [bind_bind],
        fun a ha => by rw [← bind_bind]; exact kc _ (hcs a ha)⟩
    have ht : t.Covers ⟨(s.r.bind α).bind θ, w'.r, w'.c⟩ :=
      SCov.covers (τ := fun v => (β v).bind θ) ⟨by rw [hm, bind_bind], by rw [kr, hr, bind_bind],
        fun a ha => by rw [← bind_bind]; exact kc _ (hct a ha)⟩
    have hst : Stable T w'.c := stable_of_simplify hwf hw
    obtain ⟨t', ht', hc⟩ := under_stable hwf (w := ⟨(s.r.bind α).bind θ, w'.r, w'.c⟩) hst ht
    obtain ⟨w₁, hw₁, hcw⟩ := compose_back hs hc
    exact ⟨w₁, by rw [ht']; exact hw₁, hcw⟩

theorem compose_left (s t : Span) :
    Option.Rel Span.Equiv (((T.simplify s).bind (·.compose t)).bind T.simplify)
      ((s.compose t).bind T.simplify) := by
  refine law hwf _ _ (fun w₁ h => ?_) fun w w' hu hw => ?_
  · obtain ⟨s', hs, hc⟩ := Option.bind_eq_some_iff.1 h
    exact compose_covers (simplify_covers hs) (Span.Covers.refl t) hc
  · obtain ⟨α, β, hl, hr, hm, hcs, hct⟩ := compose_parts hu
    obtain ⟨θ, kl, kr, kc⟩ := part_scov hw
    have hs : s.Covers ⟨w'.l, (s.r.bind α).bind θ, w'.c⟩ :=
      SCov.covers (τ := fun v => (α v).bind θ) ⟨by rw [kl, hl, bind_bind], by rw [bind_bind],
        fun a ha => by rw [← bind_bind]; exact kc _ (hcs a ha)⟩
    have ht : t.Covers ⟨(s.r.bind α).bind θ, w'.r, w'.c⟩ :=
      SCov.covers (τ := fun v => (β v).bind θ) ⟨by rw [hm, bind_bind], by rw [kr, hr, bind_bind],
        fun a ha => by rw [← bind_bind]; exact kc _ (hct a ha)⟩
    have hst : Stable T w'.c := stable_of_simplify hwf hw
    obtain ⟨s', hs', hc⟩ := under_stable hwf (w := ⟨w'.l, (s.r.bind α).bind θ, w'.c⟩) hst hs
    obtain ⟨w₁, hw₁, hcw⟩ := compose_back hc ht
    exact ⟨w₁, by rw [hs']; exact hw₁, hcw⟩

omit hwf in
theorem meet_scov {s t w w' : Span} (hu : s.meet t = some w) (hw : T.simplify w = some w') :
    s.Covers w' ∧ t.Covers w' := by
  obtain ⟨α, β, hl, hr, hl', hr', hcs, hct⟩ := meet_parts hu
  obtain ⟨θ, kl, kr, kc⟩ := part_scov hw
  exact ⟨SCov.covers (τ := fun v => (α v).bind θ) ⟨by rw [kl, hl, bind_bind],
      by rw [kr, hr, bind_bind], fun a ha => by rw [← bind_bind]; exact kc _ (hcs a ha)⟩,
    SCov.covers (τ := fun v => (β v).bind θ) ⟨by rw [kl, hl', bind_bind],
      by rw [kr, hr', bind_bind], fun a ha => by rw [← bind_bind]; exact kc _ (hct a ha)⟩⟩

theorem meet_right (s t : Span) :
    Option.Rel Span.Equiv (((T.simplify t).bind s.meet).bind T.simplify)
      ((s.meet t).bind T.simplify) := by
  refine law hwf _ _ (fun w₁ h => ?_) fun w w' hu hw => ?_
  · obtain ⟨t', ht, hc⟩ := Option.bind_eq_some_iff.1 h
    exact meet_covers (Span.Covers.refl s) (simplify_covers ht) hc
  · obtain ⟨hs, ht⟩ := meet_scov hu hw
    obtain ⟨t', ht', hc⟩ := under_stable hwf (stable_of_simplify hwf hw) ht
    obtain ⟨w₁, hw₁, hcw⟩ := meet_back hs hc
    exact ⟨w₁, by rw [ht']; exact hw₁, hcw⟩

theorem meet_left (s t : Span) :
    Option.Rel Span.Equiv (((T.simplify s).bind (·.meet t)).bind T.simplify)
      ((s.meet t).bind T.simplify) := by
  refine law hwf _ _ (fun w₁ h => ?_) fun w w' hu hw => ?_
  · obtain ⟨s', hs, hc⟩ := Option.bind_eq_some_iff.1 h
    exact meet_covers (simplify_covers hs) (Span.Covers.refl t) hc
  · obtain ⟨hs, ht⟩ := meet_scov hu hw
    obtain ⟨s', hs', hc⟩ := under_stable hwf (stable_of_simplify hwf hw) hs
    obtain ⟨w₁, hw₁, hcw⟩ := meet_back hc ht
    exact ⟨w₁, by rw [hs']; exact hw₁, hcw⟩

end Mono


/-! ## The laws -/

theorem Span.inst_swap (s : Span) (θ : Nat → Pat) : s.swap.inst θ = (s.inst θ).swap := rfl

theorem Theory.simplifyWithin_swap (T : Theory) : ∀ (n : Nat) (s : Span),
    T.simplifyWithin n s.swap = (T.simplifyWithin n s).map Span.swap
  | 0, s => by
    unfold Theory.simplifyWithin
    by_cases hr : T.refutes? s.c = true <;> simp [Span.swap, hr]
  | n + 1, s => by
    unfold Theory.simplifyWithin
    have hc : s.swap.c = s.c := rfl
    by_cases hr : T.refutes? s.c = true
    · simp [hc, hr]
    · simp only [hc, hr, Bool.false_eq_true, ite_false]
      cases hb : T.bind? s.c with
      | none => simp [Span.swap]
      | some θ => simp only [Span.inst_swap]; exact Theory.simplifyWithin_swap T n (s.inst θ)

/-- Simplification commutes with converse (syntactically). -/
theorem simplify_swap (T : Theory) (s : Span) : T.simplify s.swap = (T.simplify s).map Span.swap :=
  Theory.simplifyWithin_swap T _ s

/-- What proofs about answers kept up to syntactic coverage need from
simplification: it preserves coverage, it can be applied before or after
composing or conjoining with the same result up to equivalence, and it
commutes with converse. Every well-formed theory has these (`simpLaws_of_wf`);
proofs take `SimpLaws T` rather than well-formedness so that they do not
depend on how the checker works. -/
structure SimpLaws (T : Theory) : Prop where
  mono : ∀ f x : Span, f.Covers x → T.simplify x = none ∨
    ∃ f' x', T.simplify f = some f' ∧ T.simplify x = some x' ∧ f'.Covers x'
  compR : ∀ s t : Span, Option.Rel Span.Equiv (((T.simplify t).bind s.compose).bind T.simplify)
    ((s.compose t).bind T.simplify)
  compL : ∀ s t : Span, Option.Rel Span.Equiv (((T.simplify s).bind (·.compose t)).bind T.simplify)
    ((s.compose t).bind T.simplify)
  meetR : ∀ s t : Span, Option.Rel Span.Equiv (((T.simplify t).bind s.meet).bind T.simplify)
    ((s.meet t).bind T.simplify)
  meetL : ∀ s t : Span, Option.Rel Span.Equiv (((T.simplify s).bind (·.meet t)).bind T.simplify)
    ((s.meet t).bind T.simplify)
  swap : ∀ s : Span, T.simplify s.swap = (T.simplify s).map Span.swap

theorem simpLaws_of_wf {T : Theory} (hwf : ∀ ρ ∈ T, ρ.WellFormed) : SimpLaws T where
  mono _ _ h := Mono.simplify_keeps hwf h
  compR := Mono.compose_right hwf
  compL := Mono.compose_left hwf
  meetR := Mono.meet_right hwf
  meetL := Mono.meet_left hwf
  swap := simplify_swap T

/-- Simplification respects equivalent spans: equivalent spans are both
dropped or simplify to equivalent spans. -/
theorem SimpLaws.respects {T : Theory} (hL : SimpLaws T) {z z' : Span} (h : z.Equiv z') :
    Option.Rel Span.Equiv (T.simplify z) (T.simplify z') := by
  rcases hL.mono z z' h.1 with h₁ | ⟨f, x, hf, hx, hfx⟩
  · rcases hL.mono z' z h.2 with h₂ | ⟨_, _, h₃, _, _⟩
    · rw [h₁, h₂]; exact .none
    · rw [h₁] at h₃; cases h₃
  · rcases hL.mono z' z h.2 with h₂ | ⟨a, b, ha, hb, hab⟩
    · rw [hf] at h₂; cases h₂
    · rw [hf, hx]
      rw [hx] at ha; rw [hf] at hb
      cases ha; cases hb
      exact .some ⟨hfx, hab⟩

end RwLog
