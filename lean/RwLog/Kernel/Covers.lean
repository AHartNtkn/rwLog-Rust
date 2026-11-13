/-
# Coverage is decided by matching

`Span.covers?` decides `Span.Covers` (`Span.covers?_iff`). Soundness reads the
matching off as a substitution. Completeness freezes the covered span: each
of its variables becomes a distinct constant that occurs nowhere in either
span (the signature is infinite), coverage of that one ground instance yields
a substitution, and thawing the constants back into variables turns it into a
matching that `matchInto` and `matchAll` are shown to find.

Also here: the order and equivalence facts about coverage every rung uses
(`covers?_refl`, `covers?_trans`, `covers_swap`, `Span.Equiv`).
-/
import RwLog.Kernel.TermFacts
import RwLog.SpanLayer.Coverage

namespace RwLog

open Term

/-! ## Terms: variables under substitution -/

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

end TermFacts

/-! ## Fresh symbols

The signature is infinite: the strings `x…x` of distinct lengths are distinct
symbols, and those longer than every member of a finite list avoid it. -/


namespace Fresh

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
end Fresh

/-! ## Matching finds every matching

`Agree θ σ`: every binding of the partial substitution `θ` is the value of the
total substitution `σ`. -/

namespace Matching

def Agree (θ : PSubst) (σ : Nat → Pat) : Prop := ∀ v u, θ.lookup v = some u → σ v = u

theorem lookup_cons_eq (v : Nat) (t : Pat) (θ : PSubst) : ((v, t) :: θ).lookup v = some t := by
  simp

theorem lookup_cons_ne {v w : Nat} (h : w ≠ v) (t : Pat) (θ : PSubst) :
    ((v, t) :: θ).lookup w = θ.lookup w := by
  have hb : (w == v) = false := by simp [h]
  simp only [List.lookup_cons, hb]

/-- The patterns land in the targets under every extension of a match. -/
theorem matchAll_sound_mem {ps ts : List Pat} {θ : PSubst} {r : PSubst × List Pat}
    (h : r ∈ matchAll ps ts θ) (θ'' : PSubst) (he : Ext r.1 θ'') :
    ∀ p ∈ ps, p.bind θ''.apply ∈ ts := by
  obtain ⟨-, -, hm, hk⟩ := matchAll_sound ps ts θ r h
  intro p hp
  exact hm _ (hk θ'' he ▸ List.mem_map_of_mem hp)

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

end Matching

open Matching Fresh

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
      obtain ⟨-, -, k₁⟩ := matchInto_sound _ _ _ _ h₁
      obtain ⟨e₂, -, k₂⟩ := matchInto_sound _ _ _ _ h₂
      obtain ⟨e₃, -, -, -⟩ := matchAll_sound _ _ _ _ hr
      have hl := k₁ r.1 (e₂.trans e₃)
      have hrr := k₂ r.1 e₃
      have hc := matchAll_sound_mem hr r.1 (Ext.refl _)
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


theorem Span.covers?_iff (a s : Span) : a.covers? s = true ↔ a.Covers s :=
  ⟨covers?_sound, covers?_complete⟩

theorem covers?_iff (a s : Span) : a.covers? s = true ↔ a.Covers s := Span.covers?_iff a s

theorem covers?_refl (a : Span) : a.covers? a = true := covers?_complete (Span.Covers.refl a)

theorem covers?_trans {a b c : Span} (h₁ : a.covers? b = true) (h₂ : b.covers? c = true) :
    a.covers? c = true :=
  covers?_complete ((covers?_sound h₁).trans (covers?_sound h₂))

/-! ## Coverage and converse; equivalent spans -/

theorem covers_swap {a b : Span} (h : a.Covers b) : a.swap.Covers b.swap := by
  rintro x ⟨σ, rfl⟩
  obtain ⟨y, ⟨τ, rfl⟩, h1, h2, h3⟩ := h _ ⟨σ, rfl⟩
  exact ⟨_, ⟨τ, rfl⟩, h2, h1, h3⟩

theorem Span.Equiv.refl (a : Span) : a.Equiv a := ⟨Span.Covers.refl a, Span.Covers.refl a⟩

theorem Span.Equiv.symm {a b : Span} (h : a.Equiv b) : b.Equiv a := ⟨h.2, h.1⟩

theorem Span.Equiv.trans {a b c : Span} (h₁ : a.Equiv b) (h₂ : b.Equiv c) : a.Equiv c :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem Span.Equiv.swap {a b : Span} (h : a.Equiv b) : a.swap.Equiv b.swap :=
  ⟨covers_swap h.1, covers_swap h.2⟩

theorem Span.Covers.of_swap {a b : Span} (h : a.swap.Covers b.swap) : a.Covers b := by
  simpa using covers_swap h

theorem covers?_swap (a b : Span) : a.swap.covers? b.swap = a.covers? b := by
  apply Bool.eq_iff_iff.2
  rw [covers?_iff, covers?_iff]
  exact ⟨Span.Covers.of_swap, covers_swap⟩

/-- Equivalence is read the same through `covers?`. -/
theorem covers?_congr {a a' b b' : Span} (ha : a.Equiv a') (hb : b.Equiv b') :
    a.covers? b = a'.covers? b' := by
  apply Bool.eq_iff_iff.2
  rw [covers?_iff, covers?_iff]
  exact ⟨fun h => ha.2.trans (h.trans hb.1), fun h => ha.1.trans (h.trans hb.2)⟩

theorem equiv_of_den_eq {a b : Span} (h : a.den = b.den) : a.Equiv b :=
  ⟨Span.Covers.of_den_subset h.ge, Span.Covers.of_den_subset h.le⟩

end RwLog
