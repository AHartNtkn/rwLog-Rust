/-
# Pushing a sort down a pattern

`$x : n` is a sort on a variable. A sort on a pattern, `(f $x $y) : n`, says
the same as sorts on its variables: one step of `n` on `f` names the sorts of
the arguments, and so on down to the variables. `push S n p` is that list of
sorts on variables, or nothing when the sort rejects a symbol of the pattern
(then no instance of the pattern is in the sort).

`push_some` and `push_none` say this is exact for a first-order pattern: an
instance of the pattern is in the sort exactly when the values of its
variables are in the sorts pushed down to them.
-/
import RwLog.Sorts.Trusted

namespace RwLog
namespace Sorts

/-- Sorts on variables. -/
abbrev Atoms := List (Nat × Name)

/-- The substitution puts each variable in the sort named for it. -/
def Atoms.Holds (S : Sorts) (as : Atoms) (σ : Nat → GTerm) : Prop :=
  ∀ a ∈ as, mem S a.2 (σ a.1) = true

theorem Atoms.holds_append {S : Sorts} {as bs : Atoms} {σ : Nat → GTerm} :
    Atoms.Holds S (as ++ bs) σ ↔ Atoms.Holds S as σ ∧ Atoms.Holds S bs σ := by
  simp only [Atoms.Holds, List.mem_append]
  constructor
  · intro h; exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨h₁, h₂⟩ a (ha | ha)
    · exact h₁ a ha
    · exact h₂ a ha

/-- The pattern read as a function part with `extra` arguments still to come:
the sorts of all the arguments, and the sorts pushed to the variables read so
far. -/
def pushK (S : Sorts) : Pat → Name → Nat → Option (List (Option Name) × Atoms)
  | .var x, n, _ => some ([], [(x, n)])
  | .sym f, n, extra => (step S n f extra).map fun ks => (ks, [])
  | .app t u, n, extra =>
    match pushK S t n (extra + 1) with
    | none => none
    | some (ks, as) =>
      match ks[ks.length - extra - 1]? with
      | none => none
      | some none => some (ks, as)
      | some (some m) =>
        match pushK S u m 0 with
        | none => none
        | some (_, bs) => some (ks, as ++ bs)

/-- The sort `n` on the pattern `p`, as sorts on its variables. -/
def push (S : Sorts) (n : Name) (p : Pat) : Option Atoms := (pushK S p n 0).map Prod.snd

/-- What `pushK` says of a pattern that is not a variable. -/
def PushKSpec (S : Sorts) (p : Pat) : Prop :=
  ∀ (n : Name) (extra : Nat),
    (∀ ks as, pushK S p n extra = some (ks, as) → ∀ (σ : Nat → GTerm) (ks' : List (Option Name)),
      kids S (p.bind σ) n extra = some ks' ↔ ks' = ks ∧ Atoms.Holds S as σ) ∧
    (pushK S p n extra = none → ∀ σ : Nat → GTerm, kids S (p.bind σ) n extra = none)

/-- What `push` says of a pattern. -/
def PushSpec (S : Sorts) (p : Pat) : Prop :=
  ∀ n : Name,
    (∀ as, push S n p = some as → ∀ σ : Nat → GTerm,
      mem S n (p.bind σ) = true ↔ Atoms.Holds S as σ) ∧
    (push S n p = none → ∀ σ : Nat → GTerm, mem S n (p.bind σ) = false)

theorem pushSpec_of_K {S : Sorts} {p : Pat} (h : PushKSpec S p) : PushSpec S p := by
  intro n
  obtain ⟨h₁, h₂⟩ := h n 0
  constructor
  · intro as has σ
    unfold push at has
    cases hk : pushK S p n 0 with
    | none => simp [hk] at has
    | some r =>
      obtain ⟨ks, as'⟩ := r
      simp only [hk, Option.map_some, Option.some.injEq] at has
      subst has
      have := h₁ ks as' hk σ
      unfold mem
      rw [Option.isSome_iff_exists]
      constructor
      · rintro ⟨ks', hks'⟩; exact ((this ks').1 hks').2
      · intro ha; exact ⟨ks, (this ks).2 ⟨rfl, ha⟩⟩
  · intro hn σ
    unfold push at hn
    cases hk : pushK S p n 0 with
    | none => simp [mem, h₂ hk σ]
    | some r => simp [hk] at hn

theorem push_spec {S : Sorts} : ∀ p : Pat, p.firstOrder = true →
    PushSpec S p ∧ ((∀ x, p ≠ .var x) → PushKSpec S p)
  | .var x, _ => by
    refine ⟨?_, fun h => absurd rfl (h x)⟩
    intro n
    constructor
    · intro as has σ
      simp only [push, pushK, Option.map_some, Option.some.injEq] at has
      subst has
      simp [Atoms.Holds, Term.bind]
    · intro hn; simp [push, pushK] at hn
  | .sym f, _ => by
    have hK : PushKSpec S (.sym f) := by
      intro n extra
      constructor
      · intro ks as h σ ks'
        simp only [pushK, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨ks₀, hs, rfl, rfl⟩ := h
        simp only [Term.bind, kids, hs, Option.some.injEq, Atoms.Holds, List.not_mem_nil,
          false_imp_iff, implies_true, and_true]
        exact eq_comm
      · intro h σ
        simp only [pushK, Option.map_eq_none_iff] at h
        simp [Term.bind, kids, h]
    exact ⟨pushSpec_of_K hK, fun _ => hK⟩
  | .app t u, hfo => by
    have ht : t.firstOrder = true ∧ u.firstOrder = true ∧ ∀ x, t ≠ .var x := by
      cases t with
      | var x => simp [Term.firstOrder] at hfo
      | sym f => simp [Term.firstOrder] at hfo ⊢; exact hfo
      | app a b => simp only [Term.firstOrder, Bool.and_eq_true] at hfo ⊢; exact ⟨hfo.1, hfo.2, by simp⟩
    have hKt : PushKSpec S t := (push_spec t ht.1).2 ht.2.2
    have hPu : PushSpec S u := (push_spec u ht.2.1).1
    have hK : PushKSpec S (.app t u) := by
      intro n extra
      obtain ⟨t₁, t₂⟩ := hKt n (extra + 1)
      constructor
      · intro ks as h σ ks'
        simp only [pushK] at h
        cases hk : pushK S t n (extra + 1) with
        | none => simp [hk] at h
        | some r =>
          obtain ⟨ks₀, as₀⟩ := r
          have ht' := t₁ ks₀ as₀ hk σ
          simp only [hk] at h
          simp only [Term.bind]
          rw [kids_app]
          cases hg : ks₀[ks₀.length - extra - 1]? with
          | none => simp [hg] at h
          | some o =>
            cases o with
            | none =>
              simp only [hg, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [ht' ks']
              constructor
              · rintro ⟨h₁, -⟩; exact h₁
              · rintro ⟨rfl, h₂⟩; exact ⟨⟨rfl, h₂⟩, by simp [hg, memO]⟩
            | some m =>
              simp only [hg] at h
              obtain ⟨u₁, u₂⟩ := hPu m
              cases hu : pushK S u m 0 with
              | none => simp [hu] at h
              | some r' =>
                obtain ⟨ks₁, bs⟩ := r'
                simp only [hu, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hub := u₁ bs (by simp [push, hu]) σ
                rw [ht' ks', Atoms.holds_append]
                constructor
                · rintro ⟨⟨rfl, h₁⟩, h₂⟩
                  simp only [hg, Option.getD_some, memO] at h₂
                  exact ⟨rfl, h₁, hub.1 h₂⟩
                · rintro ⟨rfl, h₁, h₂⟩
                  exact ⟨⟨rfl, h₁⟩, by simp only [hg, Option.getD_some, memO]; exact hub.2 h₂⟩
      · intro h σ
        simp only [pushK] at h
        simp only [Term.bind]
        cases hres : kids S (.app (t.bind σ) (u.bind σ)) n extra with
        | none => rfl
        | some ks' =>
          exfalso
          rw [kids_app] at hres
          obtain ⟨hk', hm⟩ := hres
          cases hk : pushK S t n (extra + 1) with
          | none => rw [t₂ hk σ] at hk'; cases hk'
          | some r =>
            obtain ⟨ks₀, as₀⟩ := r
            obtain ⟨rfl, -⟩ := (t₁ ks₀ as₀ hk σ ks').1 hk'
            simp only [hk] at h
            have hlen := kids_length hk'
            have hlt : ks'.length - extra - 1 < ks'.length := by omega
            cases hg : ks'[ks'.length - extra - 1]? with
            | none => rw [List.getElem?_eq_getElem hlt] at hg; cases hg
            | some o =>
              cases o with
              | none => simp [hg] at h
              | some m =>
                simp only [hg] at h
                simp only [hg, Option.getD_some, memO] at hm
                cases hu : pushK S u m 0 with
                | none =>
                  have := (hPu m).2 (by simp [push, hu]) σ
                  rw [this] at hm; cases hm
                | some r' => simp [hu] at h
    exact ⟨pushSpec_of_K hK, fun _ => hK⟩

/-- An instance of the pattern is in the sort exactly when its variables are
in the sorts pushed down to them. -/
theorem push_some {S : Sorts} {n : Name} {p : Pat} {as : Atoms} (hp : p.firstOrder = true)
    (h : push S n p = some as) (σ : Nat → GTerm) :
    mem S n (p.bind σ) = true ↔ Atoms.Holds S as σ :=
  ((push_spec p hp).1 n).1 as h σ

/-- When the sort rejects a symbol of the pattern, no instance is in the
sort. -/
theorem push_none {S : Sorts} {n : Name} {p : Pat} (hp : p.firstOrder = true)
    (h : push S n p = none) (σ : Nat → GTerm) : mem S n (p.bind σ) = false :=
  ((push_spec p hp).1 n).2 h σ

end Sorts
end RwLog
