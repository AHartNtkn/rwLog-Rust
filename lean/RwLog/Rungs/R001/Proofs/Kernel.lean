/-
# Rung R001, Kernel obligations

* `covers_iff`: the coverage check `Span.covers?` decides `Span.Covers`.
  Soundness reads the matching off as a substitution. Completeness freezes
  the covered span: each of its variables becomes a distinct constant that
  occurs nowhere in either span (the signature is infinite), coverage of that
  one ground instance yields a substitution, and thawing the constants back
  into variables turns it into a matching that `matchInto` and `matchAll`
  are shown to find.
* `iface_exact`: a span composed with its right interface, or preceded by its
  left one, is itself, and a trivial interface is the identity.
* `iface_equiv`: coverage passes to interfaces, so equivalent answers have
  equivalent interfaces and agree on whether the interface is trivial.
* `denote_dual`: the mirrored program denotes the converse, by induction on
  expressions and by conjugating the least fixpoint with the converse.
-/
import RwLog.Rungs.R001.Spec
import RwLog.SpanLayer.Algebra

namespace RwLog

namespace R001

open Term

/-! ## Terms: variables and symbols under substitution -/

section TermFacts

variable {V W : Type}

theorem bind_agree {σ τ : V → Term W} {t : Term V} (h : t.bind σ = t.bind τ) :
    ∀ v ∈ t.vars, σ v = τ v := by
  induction t with
  | var v => intro w hw; simp [Term.vars] at hw; subst hw; exact h
  | sym f => intro w hw; simp [Term.vars] at hw
  | app t u iht ihu =>
    simp only [bind_app, Term.app.injEq] at h
    intro w hw
    simp only [Term.vars, List.mem_append] at hw
    rcases hw with hw | hw
    · exact iht h.1 w hw
    · exact ihu h.2 w hw

theorem syms_bind_sub {σ : V → Term W} {t : Term V} {f : Sym} (h : f ∈ (t.bind σ).syms) :
    f ∈ t.syms ∨ ∃ v ∈ t.vars, f ∈ (σ v).syms := by
  induction t with
  | var v => exact .inr ⟨v, by simp [Term.vars], h⟩
  | sym g => exact .inl (by simpa [Term.syms] using h)
  | app t u iht ihu =>
    simp only [bind_app, Term.syms, List.mem_append] at h
    rcases h with h | h
    · rcases iht h with h | ⟨v, hv, h⟩
      · exact .inl (by simp [Term.syms, h])
      · exact .inr ⟨v, by simp [Term.vars, hv], h⟩
    · rcases ihu h with h | ⟨v, hv, h⟩
      · exact .inl (by simp [Term.syms, h])
      · exact .inr ⟨v, by simp [Term.vars, hv], h⟩

theorem syms_var_sub {σ : V → Term W} {t : Term V} {v : V} (hv : v ∈ t.vars) {f : Sym}
    (h : f ∈ (σ v).syms) : f ∈ (t.bind σ).syms := by
  induction t with
  | var w => simp [Term.vars] at hv; subst hv; exact h
  | sym g => simp [Term.vars] at hv
  | app t u iht ihu =>
    simp only [Term.vars, List.mem_append] at hv
    simp only [bind_app, Term.syms, List.mem_append]
    rcases hv with hv | hv
    · exact .inl (iht hv)
    · exact .inr (ihu hv)

end TermFacts

/-! ## Fresh symbols

The signature is infinite: the strings `x…x` of distinct lengths are distinct
symbols, and those longer than every member of a finite list avoid it. -/

/-- A string of length `n`. -/
def code (n : Nat) : String := String.ofList (List.replicate n 'x')

@[simp] theorem code_length (n : Nat) : (code n).length = n := by
  simp [code, String.length_ofList]

/-- A bound strictly above the length of every member of a list. -/
def lenBound (L : List String) : Nat := L.foldr (fun f n => max f.length n) 0 + 1

theorem lt_lenBound {L : List String} {f : String} (h : f ∈ L) : f.length < lenBound L := by
  unfold lenBound
  induction L with
  | nil => simp at h
  | cons g L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem code_not_mem {L : List String} {n : Nat} (h : lenBound L ≤ n) : code n ∉ L := by
  intro hm
  have := lt_lenBound hm
  simp at this; omega

/-! ## Matching

`Agree θ σ`: every binding of the partial substitution `θ` is the value of the
total substitution `σ`. `Ext θ θ'`: `θ'` keeps every binding of `θ`. -/

def Agree (θ : PSubst) (σ : Nat → Pat) : Prop := ∀ v u, θ.lookup v = some u → σ v = u

def Ext (θ θ' : PSubst) : Prop := ∀ v u, θ.lookup v = some u → θ'.lookup v = some u

theorem Ext.refl (θ : PSubst) : Ext θ θ := fun _ _ h => h

theorem Ext.trans {θ₁ θ₂ θ₃ : PSubst} (h₁ : Ext θ₁ θ₂) (h₂ : Ext θ₂ θ₃) : Ext θ₁ θ₃ :=
  fun v u h => h₂ v u (h₁ v u h)

theorem lookup_cons_eq (v : Nat) (t : Pat) (θ : PSubst) : ((v, t) :: θ).lookup v = some t := by
  simp

theorem lookup_cons_ne {v w : Nat} (h : w ≠ v) (t : Pat) (θ : PSubst) :
    ((v, t) :: θ).lookup w = θ.lookup w := by
  have hb : (w == v) = false := by simp [h]
  simp only [List.lookup_cons, hb]

theorem Ext.cons {θ : PSubst} {v : Nat} (hv : θ.lookup v = none) (t : Pat) :
    Ext θ ((v, t) :: θ) := by
  intro w u hw
  by_cases hwv : w = v
  · subst hwv; rw [hv] at hw; cases hw
  · rw [lookup_cons_ne hwv]; exact hw

/-- What a successful `matchInto` guarantees: it only adds bindings, and every
further extension sends the pattern to the target. -/
theorem matchInto_sound : ∀ (p t : Pat) (θ θ' : PSubst), matchInto p t θ = some θ' →
    Ext θ θ' ∧ ∀ θ'', Ext θ' θ'' → p.bind (PSubst.apply θ'') = t
  | .var v, t, θ, θ', h => by
    cases hl : θ.lookup v with
    | some u =>
      simp only [matchInto, hl] at h
      split at h
      · cases h
        refine ⟨Ext.refl _, fun θ'' he => ?_⟩
        simp [PSubst.apply, he v u hl, *]
      · cases h
    | none =>
      simp only [matchInto, hl, Option.some.injEq] at h
      subst h
      refine ⟨Ext.cons hl t, fun θ'' he => ?_⟩
      simp [PSubst.apply, he v t (lookup_cons_eq v t θ)]
  | .sym f, t, θ, θ', h => by
    cases t with
    | var _ => simp [matchInto] at h
    | app _ _ => simp [matchInto] at h
    | sym g =>
      simp only [matchInto] at h
      split at h
      · cases h; subst_vars; exact ⟨Ext.refl _, fun _ _ => rfl⟩
      · cases h
  | .app p q, t, θ, θ', h => by
    cases t with
    | var _ => simp [matchInto] at h
    | sym _ => simp [matchInto] at h
    | app t u =>
      simp only [matchInto] at h
      cases h₁ : matchInto p t θ with
      | none => rw [h₁] at h; cases h
      | some θ₁ =>
        rw [h₁, Option.bind_some] at h
        obtain ⟨e₁, k₁⟩ := matchInto_sound p t θ θ₁ h₁
        obtain ⟨e₂, k₂⟩ := matchInto_sound q u θ₁ θ' h
        refine ⟨e₁.trans e₂, fun θ'' he => ?_⟩
        simp only [bind_app, k₂ θ'' he, k₁ θ'' (e₂.trans he)]

/-- `matchInto` finds every matching that agrees with what is already bound. -/
theorem matchInto_complete (σ : Nat → Pat) : ∀ (p : Pat) (θ : PSubst), Agree θ σ →
    ∃ θ', matchInto p (p.bind σ) θ = some θ' ∧ Agree θ' σ
  | .var v, θ, hθ => by
    cases hl : θ.lookup v with
    | some u =>
      have hu := hθ v u hl
      subst hu
      exact ⟨θ, by simp [matchInto, hl], hθ⟩
    | none =>
      refine ⟨(v, σ v) :: θ, by simp [matchInto, hl], fun w u hw => ?_⟩
      by_cases hwv : w = v
      · subst hwv; rw [lookup_cons_eq] at hw; cases hw; rfl
      · rw [lookup_cons_ne hwv] at hw; exact hθ w u hw
  | .sym f, θ, hθ => ⟨θ, by simp [matchInto], hθ⟩
  | .app p q, θ, hθ => by
    obtain ⟨θ₁, h₁, a₁⟩ := matchInto_complete σ p θ hθ
    obtain ⟨θ₂, h₂, a₂⟩ := matchInto_complete σ q θ₁ a₁
    exact ⟨θ₂, by simp [matchInto, h₁, h₂], a₂⟩

theorem matchAll_sound : ∀ (ps ts : List Pat) (θ : PSubst) (r : PSubst × List Pat),
    r ∈ matchAll ps ts θ →
    Ext θ r.1 ∧ ∀ θ'', Ext r.1 θ'' → ∀ p ∈ ps, p.bind (PSubst.apply θ'') ∈ ts
  | [], ts, θ, r, h => by
    simp only [matchAll, List.mem_singleton] at h
    subst h
    exact ⟨Ext.refl _, fun _ _ p hp => by simp at hp⟩
  | p :: ps, ts, θ, r, h => by
    simp only [matchAll, List.mem_flatMap] at h
    obtain ⟨t, ht, hr⟩ := h
    cases h₁ : matchInto p t θ with
    | none => rw [h₁] at hr; simp at hr
    | some θ₁ =>
      rw [h₁] at hr
      simp only [List.mem_map] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      obtain ⟨e₁, k₁⟩ := matchInto_sound p t θ θ₁ h₁
      obtain ⟨e₂, k₂⟩ := matchAll_sound ps ts θ₁ r' hr'
      refine ⟨e₁.trans e₂, fun θ'' he q hq => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [k₁ θ'' (e₂.trans he)]; exact ht
      · exact k₂ θ'' he q hq

theorem matchAll_complete (σ : Nat → Pat) : ∀ (ps ts : List Pat) (θ : PSubst), Agree θ σ →
    (∀ p ∈ ps, p.bind σ ∈ ts) → matchAll ps ts θ ≠ []
  | [], _, _, _, _ => by simp [matchAll]
  | p :: ps, ts, θ, hθ, hps => by
    obtain ⟨θ₁, h₁, a₁⟩ := matchInto_complete σ p θ hθ
    have hrest := matchAll_complete σ ps ts θ₁ a₁ fun q hq => hps q (List.mem_cons_of_mem _ hq)
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hrest
    simp only [matchAll, ne_eq, List.flatMap_eq_nil_iff, not_forall]
    refine ⟨p.bind σ, hps p (List.mem_cons_self ..), ?_⟩
    rw [h₁]
    simp only [List.map_eq_nil_iff]
    exact hrest

/-! ## Coverage -/

theorem covers?_sound {a s : Span} (h : a.covers? s = true) : a.Covers s := by
  unfold Span.covers? at h
  cases h₁ : matchInto a.l s.l [] with
  | none => rw [h₁] at h; simp at h
  | some θ₁ =>
    rw [h₁, Option.bind_some] at h
    cases h₂ : matchInto a.r s.r θ₁ with
    | none => rw [h₂] at h; simp at h
    | some θ₂ =>
      rw [h₂] at h
      simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ h
      obtain ⟨e₁, k₁⟩ := matchInto_sound _ _ _ _ h₁
      obtain ⟨e₂, k₂⟩ := matchInto_sound _ _ _ _ h₂
      obtain ⟨e₃, k₃⟩ := matchAll_sound _ _ _ _ hr
      have hl := k₁ r.1 (e₂.trans e₃)
      have hrr := k₂ r.1 e₃
      have hc := k₃ r.1 (Ext.refl _)
      rintro x ⟨σ, rfl⟩
      let τ : Nat → GTerm := fun v => (PSubst.apply r.1 v).bind σ
      refine ⟨(a.l.bind τ, a.r.bind τ, a.c.at τ), ⟨τ, rfl⟩, ?_, ?_, ?_⟩
      · show a.l.bind τ = s.l.bind σ
        rw [← hl, bind_bind]
      · show a.r.bind τ = s.r.bind σ
        rw [← hrr, bind_bind]
      · intro g hg
        simp only [Store.at, List.mem_toFinset, List.mem_map] at hg ⊢
        obtain ⟨c, hc', rfl⟩ := hg
        exact ⟨c.bind (PSubst.apply r.1), hc c hc', by rw [bind_bind]⟩

/-- Thaw a frozen ground term: a symbol of length at least `k` is the frozen
variable `length - k`. -/
def thaw (k : Nat) : GTerm → Pat
  | .var e => e.elim
  | .sym f => if k ≤ f.length then .var (f.length - k) else .sym f
  | .app t u => .app (thaw k t) (thaw k u)

/-- Freeze variable `v` as the symbol of length `k + v`. -/
def frz (k : Nat) (v : Nat) : GTerm := .sym (code (k + v))

theorem thaw_bind {k : Nat} {τ : Nat → GTerm} :
    ∀ p : Pat, (∀ f ∈ p.syms, f.length < k) → thaw k (p.bind τ) = p.bind (thaw k ∘ τ)
  | .var _, _ => rfl
  | .sym f, h => by
    have := h f (by simp [Term.syms])
    simp [thaw]; omega
  | .app p q, h => by
    simp only [bind_app, thaw]
    rw [thaw_bind p fun f hf => h f (by simp [Term.syms, hf]),
      thaw_bind q fun f hf => h f (by simp [Term.syms, hf])]

theorem thaw_frz {k : Nat} : ∀ p : Pat, (∀ f ∈ p.syms, f.length < k) → thaw k (p.bind (frz k)) = p
  | .var v, _ => by simp [frz, thaw]
  | .sym f, h => by
    have := h f (by simp [Term.syms])
    simp [thaw]; omega
  | .app p q, h => by
    simp only [bind_app, thaw]
    rw [thaw_frz p fun f hf => h f (by simp [Term.syms, hf]),
      thaw_frz q fun f hf => h f (by simp [Term.syms, hf])]

/-- Every symbol of a span. -/
def spanSyms (s : Span) : List Sym := s.l.syms ++ s.r.syms ++ s.c.flatMap Term.syms

theorem covers?_complete {a s : Span} (h : a.Covers s) : a.covers? s = true := by
  let k := lenBound (spanSyms a ++ spanSyms s)
  have hk : ∀ f, f ∈ spanSyms a ++ spanSyms s → f.length < k := fun f hf => lt_lenBound hf
  have ha : ∀ f, f ∈ spanSyms a → f.length < k := fun f hf => hk f (by simp [hf])
  have hs : ∀ f, f ∈ spanSyms s → f.length < k := fun f hf => hk f (by simp [hf])
  obtain ⟨y, ⟨τ, rfl⟩, hyl, hyr, hyc⟩ := h _ ⟨frz k, rfl⟩
  simp only at hyl hyr hyc
  let θ : Nat → Pat := thaw k ∘ τ
  have hl : a.l.bind θ = s.l := by
    rw [← thaw_bind a.l fun f hf => ha f (by simp [spanSyms, hf]), hyl,
      thaw_frz s.l fun f hf => hs f (by simp [spanSyms, hf])]
  have hr : a.r.bind θ = s.r := by
    rw [← thaw_bind a.r fun f hf => ha f (by simp [spanSyms, hf]), hyr,
      thaw_frz s.r fun f hf => hs f (by simp [spanSyms, hf])]
  have hc : ∀ c ∈ a.c, c.bind θ ∈ s.c := by
    intro c hcm
    have hm : c.bind τ ∈ a.c.at τ := by
      simp only [Store.at, List.mem_toFinset, List.mem_map]; exact ⟨c, hcm, rfl⟩
    have := hyc hm
    simp only [Store.at, List.mem_toFinset, List.mem_map] at this
    obtain ⟨t, ht, he⟩ := this
    rw [← thaw_bind c fun f hf => ha f (by simp [spanSyms]; exact .inr (.inr ⟨c, hcm, hf⟩)), ← he,
      thaw_frz t fun f hf => hs f (by simp [spanSyms]; exact .inr (.inr ⟨t, ht, hf⟩))]
    exact ht
  have a0 : Agree [] θ := fun _ _ h => by simp at h
  obtain ⟨θ₁, h₁, a₁⟩ := matchInto_complete θ a.l [] a0
  obtain ⟨θ₂, h₂, a₂⟩ := matchInto_complete θ a.r θ₁ a₁
  rw [hl] at h₁
  rw [hr] at h₂
  have h₃ := matchAll_complete θ a.c s.c θ₂ a₂ hc
  unfold Span.covers?
  rw [h₁, Option.bind_some, h₂]
  simpa [List.isEmpty_iff] using h₃

theorem covers_iff : Obligation.covers_iff :=
  fun _ _ => ⟨covers?_sound, covers?_complete⟩

/-! ## Interfaces -/

theorem mem_storeOn {s : Span} {p c : Pat} : c ∈ s.storeOn p ↔ c ∈ s.c ∧ ∀ v ∈ c.vars, v ∈ p.vars := by
  simp [Span.storeOn, List.mem_filter, List.all_eq_true]

theorem storeOn_sub (s : Span) (p : Pat) (σ : Nat → GTerm) : (s.storeOn p).at σ ⊆ s.c.at σ := by
  intro g hg
  simp only [Store.at, List.mem_toFinset, List.mem_map] at hg ⊢
  obtain ⟨c, hc, rfl⟩ := hg
  exact ⟨c, (mem_storeOn.1 hc).1, rfl⟩

/-- The store on `p` only reads the variables of `p`. -/
theorem storeOn_at_congr (s : Span) (p : Pat) {σ τ : Nat → GTerm} (h : p.bind σ = p.bind τ) :
    (s.storeOn p).at σ = (s.storeOn p).at τ := by
  have hv := bind_agree h
  unfold Store.at
  congr 1
  refine List.map_congr_left fun c hc => bind_congr fun v hvc => hv v ((mem_storeOn.1 hc).2 v hvc)

/-- `s ; s.rightIface = s`. -/
theorem comp_rightIface (s : Span) : (s.den).comp s.rightIface.den = s.den := by
  ext ⟨a, b, S⟩
  simp only [GRel.comp, Span.den, Span.rightIface, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨m, S₁, S₂, ⟨σ, rfl, rfl, rfl⟩, ⟨τ, hm, rfl, rfl⟩, rfl⟩
    refine ⟨σ, rfl, hm.symm, ?_⟩
    rw [storeOn_at_congr s s.r hm.symm, Finset.union_eq_left.2 (storeOn_sub s s.r σ)]
  · rintro ⟨σ, rfl, rfl, rfl⟩
    exact ⟨_, _, _, ⟨σ, rfl, rfl, rfl⟩, ⟨σ, rfl, rfl, rfl⟩,
      (Finset.union_eq_left.2 (storeOn_sub s s.r σ)).symm⟩

/-- `s.leftIface ; s = s`. -/
theorem leftIface_comp (s : Span) : (s.leftIface.den).comp s.den = s.den := by
  ext ⟨a, b, S⟩
  simp only [GRel.comp, Span.den, Span.leftIface, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨m, S₁, S₂, ⟨τ, rfl, hm, rfl⟩, ⟨σ, hm', rfl, rfl⟩, rfl⟩
    refine ⟨σ, hm.symm.trans hm', rfl, ?_⟩
    rw [storeOn_at_congr s s.l (hm.symm.trans hm'), Finset.union_eq_right.2 (storeOn_sub s s.l σ)]
  · rintro ⟨σ, rfl, rfl, rfl⟩
    exact ⟨_, _, _, ⟨σ, rfl, rfl, rfl⟩, ⟨σ, rfl, rfl, rfl⟩,
      (Finset.union_eq_right.2 (storeOn_sub s s.l σ)).symm⟩

theorem bound_none {s : Span} (h : bound s = none) : (∃ v, s.l = .var v) ∧ s.c = [] := by
  unfold bound at h
  split at h
  · rename_i v h₁ h₂; exact ⟨⟨v, h₁⟩, h₂⟩
  · cases h

theorem bound_some {s s' : Span} (h : bound s = some s') : s' = s := by
  unfold bound at h
  split at h
  · cases h
  · cases h; rfl

/-- The span `$v -> $v` with no constraints denotes the identity. -/
theorem den_trivial {s : Span} {v : Nat} (hl : s.l = .var v) (hr : s.r = .var v) (hc : s.c = []) :
    s.den = GRel.id := by
  ext ⟨a, b, S⟩
  simp only [Span.den, GRel.id, Set.mem_ofPred_eq, Prod.mk.injEq, hl, hr, hc]
  constructor
  · rintro ⟨σ, rfl, rfl, rfl⟩; exact ⟨rfl, by simp [Store.at]⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun _ => a, rfl, h1, by simp [Store.at, h2]⟩

theorem iface_exact : Obligation.iface_exact := by
  intro s
  refine ⟨comp_rightIface s, leftIface_comp s, fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨v, hv⟩, hc⟩ := bound_none h
    exact den_trivial hv hv hc
  · obtain ⟨⟨v, hv⟩, hc⟩ := bound_none h
    exact den_trivial hv hv hc

/-- A span that covers a trivial span is trivial: it must reach every ground
term on the left with the empty store. -/
theorem bound_none_of_covers {a b : Span} (ha : bound a = none) (h : b.Covers a) : bound b = none := by
  obtain ⟨⟨v, hv⟩, hc⟩ := bound_none ha
  have inst : ∀ g : GTerm, ∃ τ : Nat → GTerm, b.l.bind τ = g ∧ b.c.at τ = ∅ := by
    intro g
    obtain ⟨y, ⟨τ, rfl⟩, h1, _, h3⟩ := h (g, a.r.bind fun _ => g, ∅) ⟨fun _ => g, by
      simp [hv, hc, Store.at]⟩
    exact ⟨τ, h1, Finset.subset_empty.1 h3⟩
  obtain ⟨τ₁, h₁, hc₁⟩ := inst (.sym "a")
  obtain ⟨τ₂, h₂, _⟩ := inst (.sym "b")
  have hbc : b.c = [] := by
    cases hb : b.c with
    | nil => rfl
    | cons c cs =>
      rw [hb] at hc₁; simp [Store.at] at hc₁
  unfold bound
  cases hl : b.l with
  | var w => simp [hbc]
  | sym f =>
    rw [hl] at h₁ h₂; simp at h₁ h₂; subst h₁; simp at h₂
  | app p q => rw [hl] at h₁; simp at h₁

theorem covers_swap {a b : Span} (h : a.Covers b) : a.swap.Covers b.swap := by
  rintro x ⟨σ, rfl⟩
  obtain ⟨y, ⟨τ, rfl⟩, h1, h2, h3⟩ := h _ ⟨σ, rfl⟩
  exact ⟨_, ⟨τ, rfl⟩, h2, h1, h3⟩

theorem leftIface_eq (s : Span) : s.leftIface = s.swap.rightIface := rfl

/-- Coverage passes to right interfaces. The covered span's variables off its
right side are sent to a fresh constant, so no constraint mentioning them can
be hit by a constraint of the covering interface. -/
theorem rightIface_covers {x y : Span} (h : x.Covers y) : x.rightIface.Covers y.rightIface := by
  rintro z ⟨τ, rfl⟩
  let L : List Sym := x.c.flatMap Term.syms ++ y.r.syms ++ y.r.vars.flatMap fun w => (τ w).syms
  let F : Sym := code (lenBound L)
  have hF : F ∉ L := code_not_mem le_rfl
  let τ' : Nat → GTerm := fun w => if w ∈ y.r.vars then τ w else .sym F
  have hrτ : y.r.bind τ' = y.r.bind τ := bind_congr fun w hw => by simp [τ', hw]
  obtain ⟨u, ⟨σ', rfl⟩, _, hr, hst⟩ := h _ ⟨τ', rfl⟩
  simp only at hr hst
  refine ⟨_, ⟨σ', rfl⟩, ?_, ?_, ?_⟩
  · simp only [Span.rightIface]; exact hr.trans hrτ
  · simp only [Span.rightIface]; exact hr.trans hrτ
  · simp only [Span.rightIface]
    intro g hg
    simp only [Store.at, List.mem_toFinset, List.mem_map] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    obtain ⟨hcx, hcv⟩ := mem_storeOn.1 hc
    have hin : c.bind σ' ∈ y.c.at τ' := hst (by
      simp only [Store.at, List.mem_toFinset, List.mem_map]; exact ⟨c, hcx, rfl⟩)
    simp only [Store.at, List.mem_toFinset, List.mem_map] at hin
    obtain ⟨c', hc', he⟩ := hin
    by_cases hall : ∀ w ∈ c'.vars, w ∈ y.r.vars
    · simp only [Store.at, List.mem_toFinset, List.mem_map]
      refine ⟨c', mem_storeOn.2 ⟨hc', hall⟩, ?_⟩
      rw [← he]
      exact bind_congr fun w hw => by simp [τ', hall w hw]
    · exfalso
      push Not at hall
      obtain ⟨w, hw, hwr⟩ := hall
      have hFin : F ∈ (c'.bind τ').syms :=
        syms_var_sub hw (by simp [τ', hwr, Term.syms])
      rw [he] at hFin
      apply hF
      rcases syms_bind_sub hFin with hf | ⟨v, hv, hf⟩
      · simp only [L, List.mem_append, List.mem_flatMap]; exact .inl (.inl ⟨c, hcx, hf⟩)
      · have hf' : F ∈ (y.r.bind τ).syms := by
          rw [← hrτ, ← hr]; exact syms_var_sub (hcv v hv) hf
        rcases syms_bind_sub hf' with hf' | ⟨w', hw', hf'⟩
        · simp only [L, List.mem_append]; exact .inl (.inr hf')
        · simp only [L, List.mem_append, List.mem_flatMap]; exact .inr ⟨w', hw', hf'⟩

/-- Covering in both directions makes boundaries equal as table keys. -/
theorem boundEq_of_equiv {a b : Span} (hab : a.Covers b) (hba : b.Covers a) :
    boundEq (bound a) (bound b) = true := by
  cases ha : bound a with
  | none =>
    rw [bound_none_of_covers ha hba]; rfl
  | some a' =>
    cases hb : bound b with
    | none => rw [bound_none_of_covers hb hab] at ha; cases ha
    | some b' =>
      rw [bound_some ha, bound_some hb]
      simp [boundEq, covers?_complete hab, covers?_complete hba]

theorem iface_equiv : Obligation.iface_equiv := by
  rintro x y ⟨hxy, hyx⟩
  refine ⟨boundEq_of_equiv (rightIface_covers hxy) (rightIface_covers hyx), ?_⟩
  rw [leftIface_eq, leftIface_eq]
  exact boundEq_of_equiv (rightIface_covers (covers_swap hxy)) (rightIface_covers (covers_swap hyx))

/-! ## The mirrored program -/

theorem GRel.inv_inv (R : GRel) : R.inv.inv = R := rfl

theorem GRel.comp_inv (R S : GRel) : (R.comp S).inv = S.inv.comp R.inv := by
  ext ⟨a, b, X⟩
  simp only [GRel.comp, GRel.inv, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, S₁, S₂, h₁, h₂, rfl⟩; exact ⟨m, S₂, S₁, h₂, h₁, Finset.union_comm _ _⟩
  · rintro ⟨m, S₁, S₂, h₁, h₂, rfl⟩; exact ⟨m, S₂, S₁, h₂, h₁, Finset.union_comm _ _⟩

theorem GRel.meet_inv (R S : GRel) : (R.meet S).inv = R.inv.meet S.inv := rfl

/-- Pointwise converse of the meaning of every name. -/
def invAll (ρ : Name → GRel) : Name → GRel := fun n => (ρ n).inv

theorem invAll_invAll (ρ : Name → GRel) : invAll (invAll ρ) = ρ := rfl

theorem invAll_mono {ρ ρ' : Name → GRel} (h : ρ ≤ ρ') : invAll ρ ≤ invAll ρ' :=
  fun n _ hx => h n hx

theorem denote_dual_inv (ρ : Name → GRel) : ∀ e : Rel, denote (invAll ρ) e.dual = (denote ρ e).inv
  | .zero => by ext; simp [denote, Rel.dual, GRel.inv]
  | .span s => swap_den s
  | .or a b => by
    simp only [Rel.dual, denote, denote_dual_inv ρ a, denote_dual_inv ρ b]; rfl
  | .and a b => by simp only [Rel.dual, denote, denote_dual_inv ρ a, denote_dual_inv ρ b]; rfl
  | .seq a b => by
    simp only [Rel.dual, denote, denote_dual_inv ρ a, denote_dual_inv ρ b, GRel.comp_inv]
  | .conv a => by simp only [Rel.dual, denote, denote_dual_inv ρ a]
  | .call n => rfl

theorem lookup_dual (n : Name) : ∀ defs : List (Name × Rel),
    (defs.map fun d => (d.1, d.2.dual)).lookup n = (defs.lookup n).map Rel.dual
  | [] => rfl
  | (k, e) :: defs => by
    simp only [List.map_cons, List.lookup_cons]
    cases n == k
    · exact lookup_dual n defs
    · rfl

theorem Program.dual_body (P : Program) (n : Name) : P.dual.body n = (P.body n).dual := by
  unfold Program.body Program.dual
  simp only
  rw [lookup_dual]
  cases P.defs.lookup n <;> rfl

theorem Program.dual_step (P : Program) (ρ : Name → GRel) :
    P.dual.step ρ = invAll (P.step (invAll ρ)) := by
  funext n
  show denote ρ (P.dual.body n) = (denote (invAll ρ) (P.body n)).inv
  rw [Program.dual_body, ← denote_dual_inv, invAll_invAll]

theorem Program.dual_meaning (P : Program) : P.dual.meaning = invAll P.meaning := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    rw [Program.dual_step, invAll_invAll]
    exact le_of_eq (congrArg invAll (OrderHom.map_lfp P.step))
  · have : P.meaning ≤ invAll P.dual.meaning := by
      apply OrderHom.lfp_le
      have h := OrderHom.map_lfp P.dual.step
      rw [Program.dual_step] at h
      have h' := congrArg invAll h
      rw [invAll_invAll] at h'
      exact le_of_eq h'
    exact invAll_mono this

theorem denote_dual : Obligation.denote_dual := by
  intro P e
  show denote P.dual.meaning e.dual = _
  rw [Program.dual_meaning, denote_dual_inv]
  rfl

end R001

end RwLog
