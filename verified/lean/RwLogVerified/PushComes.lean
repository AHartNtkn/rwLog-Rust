/-
# The push-down of the store and the push-down of the specification

`Sorts.push` reads a pattern from its symbol outward and gathers the sorts
it puts on the variables. `push_sort` works through the pairs of a sort and
a subterm it comes to (`Comes`). They agree: `Sorts.push` gives nothing
exactly when a step fails on the way (`Fails`), and otherwise its atoms are
the pairs of a variable `push_sort` comes to.
-/
import RwLogVerified.Push

namespace RwLogVerified

open RwLog

variable {S : Sorts}

theorem unspine_append : ∀ (p : Pat) (acc : List Pat),
    unspine p acc = ((unspine p []).1, (unspine p []).2 ++ acc)
  | .var _, _ => rfl
  | .sym _, _ => rfl
  | .app g u, acc => by
    rw [unspine, unspine_append g (u :: acc), unspine, unspine_append g [u]]
    simp

theorem mem_zip_snoc {α β : Type} : ∀ (ks : List α) (L : List β) (u : β) (x : α × β),
    x ∈ ks.zip (L ++ [u]) ↔ x ∈ ks.zip L ∨ (ks[L.length]? = some x.1 ∧ x.2 = u)
  | [], L, u, x => by simp
  | k :: ks, [], u, x => by
    obtain ⟨a, b⟩ := x
    simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton,
      Prod.mk.injEq, List.not_mem_nil, List.length_nil, List.getElem?_cons_zero,
      Option.some.injEq, false_or]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | k :: ks, l :: L, u, x => by
    simp only [List.cons_append, List.zip_cons_cons, List.mem_cons, List.length_cons,
      List.getElem?_cons_succ, mem_zip_snoc ks L u x, or_assoc]

/-- What `pushK` returns on a pattern with a symbol at its head: the step of
the sort on the symbol, and the atoms of the arguments that have a sort. -/
theorem pushK_some : ∀ (p : Pat) (n : Name) (extra : Nat) (f : Sym),
    (unspine p []).1 = .sym f → ∀ ks ats, Sorts.pushK S p n extra = some (ks, ats) →
    Sorts.step S n f ((unspine p []).2.length + extra) = some ks ∧
      (∀ m a, (some m, a) ∈ ks.zip (unspine p []).2 → ∃ bs, Sorts.push S m a = some bs) ∧
      ∀ x, x ∈ ats ↔ ∃ m a bs, (some m, a) ∈ ks.zip (unspine p []).2 ∧
        Sorts.push S m a = some bs ∧ x ∈ bs
  | .var v, _, _, _, hd, _, _, _ => by simp [unspine] at hd
  | .sym g, n, extra, f, hd, ks, ats, h => by
    simp only [unspine, Term.sym.injEq] at hd
    subst hd
    simp only [Sorts.pushK, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨ks', hs, rfl, rfl⟩ := h
    simp [unspine, hs]
  | .app t u, n, extra, f, hd, ks, ats, h => by
    rw [unspine, unspine_append t [u]] at hd ⊢
    simp only at hd ⊢
    simp only [Sorts.pushK] at h
    cases ht : Sorts.pushK S t n (extra + 1) with
    | none => simp [ht] at h
    | some r =>
      obtain ⟨ks', ats'⟩ := r
      obtain ⟨hs, hk, hm⟩ := pushK_some t n (extra + 1) f hd ks' ats' ht
      have hlen := Sorts.step_length hs
      have hidx : ks'.length - extra - 1 = (unspine t []).2.length := by omega
      simp only [ht, hidx] at h
      have hs' : Sorts.step S n f (((unspine t []).2 ++ [u]).length + extra) = some ks' := by
        rw [← hs]; congr 1; simp; omega
      cases hi : ks'[(unspine t []).2.length]? with
      | none => simp [hi] at h
      | some o =>
        cases o with
        | none =>
          simp only [hi, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hs', fun m a hz => ?_, fun x => ?_⟩
          · rcases (mem_zip_snoc _ _ _ _).1 hz with hz | ⟨hz, -⟩
            · exact hk m a hz
            · rw [hi] at hz; cases hz
          · rw [hm x]
            constructor
            · rintro ⟨m, a, bs, hz, hp, hx⟩
              exact ⟨m, a, bs, (mem_zip_snoc _ _ _ _).2 (.inl hz), hp, hx⟩
            · rintro ⟨m, a, bs, hz, hp, hx⟩
              rcases (mem_zip_snoc _ _ _ _).1 hz with hz | ⟨hz, -⟩
              · exact ⟨m, a, bs, hz, hp, hx⟩
              · rw [hi] at hz; cases hz
        | some m0 =>
          simp only [hi] at h
          cases hu : Sorts.pushK S u m0 0 with
          | none => simp [hu] at h
          | some r' =>
            obtain ⟨ks2, bs0⟩ := r'
            simp only [hu, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hpu : Sorts.push S m0 u = some bs0 := by simp [Sorts.push, hu]
            refine ⟨hs', fun m a hz => ?_, fun x => ?_⟩
            · rcases (mem_zip_snoc _ _ _ _).1 hz with hz | ⟨hz, ha⟩
              · exact hk m a hz
              · rw [hi] at hz
                simp only [Option.some.injEq] at hz ha
                subst hz ha
                exact ⟨bs0, hpu⟩
            · rw [List.mem_append, hm x]
              constructor
              · rintro (⟨m, a, bs, hz, hp, hx⟩ | hx)
                · exact ⟨m, a, bs, (mem_zip_snoc _ _ _ _).2 (.inl hz), hp, hx⟩
                · exact ⟨m0, u, bs0, (mem_zip_snoc _ _ _ _).2 (.inr ⟨hi, rfl⟩), hpu, hx⟩
              · rintro ⟨m, a, bs, hz, hp, hx⟩
                rcases (mem_zip_snoc _ _ _ _).1 hz with hz | ⟨hz, ha⟩
                · exact .inl ⟨m, a, bs, hz, hp, hx⟩
                · rw [hi] at hz
                  simp only [Option.some.injEq] at hz ha
                  subst hz ha
                  rw [hpu] at hp
                  cases hp
                  exact .inr hx

/-- When `pushK` returns nothing on a pattern with a symbol at its head, the
sort has no step on the symbol or an argument with a sort has no push-down. -/
theorem pushK_none : ∀ (p : Pat) (n : Name) (extra : Nat) (f : Sym),
    (unspine p []).1 = .sym f → Sorts.pushK S p n extra = none →
    Sorts.step S n f ((unspine p []).2.length + extra) = none ∨
      ∃ ks m a, Sorts.step S n f ((unspine p []).2.length + extra) = some ks ∧
        (some m, a) ∈ ks.zip (unspine p []).2 ∧ Sorts.push S m a = none
  | .var v, _, _, _, hd, _ => by simp [unspine] at hd
  | .sym g, n, extra, f, hd, h => by
    simp only [unspine, Term.sym.injEq] at hd
    subst hd
    simp only [Sorts.pushK, Option.map_eq_none_iff] at h
    simp [unspine, h]
  | .app t u, n, extra, f, hd, h => by
    rw [unspine, unspine_append t [u]] at hd ⊢
    simp only at hd ⊢
    have hl : ((unspine t []).2 ++ [u]).length + extra = (unspine t []).2.length + (extra + 1) := by
      simp; omega
    rw [hl]
    simp only [Sorts.pushK] at h
    cases ht : Sorts.pushK S t n (extra + 1) with
    | none =>
      rcases pushK_none t n (extra + 1) f hd ht with hs | ⟨ks, m, a, hs, hz, hp⟩
      · exact .inl hs
      · exact .inr ⟨ks, m, a, hs, (mem_zip_snoc _ _ _ _).2 (.inl hz), hp⟩
    | some r =>
      obtain ⟨ks', ats'⟩ := r
      obtain ⟨hs, -, -⟩ := pushK_some t n (extra + 1) f hd ks' ats' ht
      have hlen := Sorts.step_length hs
      have hidx : ks'.length - extra - 1 = (unspine t []).2.length := by omega
      simp only [ht, hidx] at h
      cases hi : ks'[(unspine t []).2.length]? with
      | none =>
        have := List.getElem?_eq_none_iff.1 hi
        omega
      | some o =>
        cases o with
        | none => simp [hi] at h
        | some m0 =>
          simp only [hi] at h
          cases hu : Sorts.pushK S u m0 0 with
          | none =>
            exact .inr ⟨ks', m0, u, hs, (mem_zip_snoc _ _ _ _).2 (.inr ⟨hi, rfl⟩),
              by simp [Sorts.push, hu]⟩
          | some r' => simp [hu] at h

theorem Comes.trans {n : Name} {p : Pat} {x y : Name × Pat} (h : Comes S n p x)
    (h' : Comes S x.1 x.2 y) : Comes S n p y := by
  induction h' with
  | root => exact h
  | kid _ hu hs hz ih => exact .kid ih hu hs hz

/-- A pair come to is the pair asked about or is come to from an argument of
it that has a sort. -/
theorem Comes.inv {n : Name} {p : Pat} {y : Name × Pat} (h : Comes S n p y) :
    y = (n, p) ∨ ∃ f args ks m a, unspine p [] = (.sym f, args) ∧
      Sorts.step S n f args.length = some ks ∧ (some m, a) ∈ ks.zip args ∧ Comes S m a y := by
  induction h with
  | root => exact .inl rfl
  | kid hx hu hs hz ih =>
    rcases ih with rfl | ⟨f', args', ks', m', a', hu', hs', hz', hc⟩
    · exact .inr ⟨_, _, _, _, _, hu, hs, hz, .root⟩
    · exact .inr ⟨f', args', ks', m', a', hu', hs', hz', .kid hc hu hs hz⟩

/-- The push-down of the specification and the pairs `push_sort` comes to. -/
theorem push_comes : ∀ (k : Nat) (p : Pat) (n : Name), p.size ≤ k → p.firstOrder = true →
    (∀ ats, Sorts.push S n p = some ats →
      (∀ a, a ∈ ats ↔ Comes S n p (a.2, .var a.1)) ∧ ¬ Fails S n p) ∧
    (Sorts.push S n p = none → Fails S n p) := by
  intro k
  induction k with
  | zero =>
    intro p n hk
    cases p <;> simp [Term.size] at hk
  | succ k ih =>
    intro p n hk hfo
    by_cases hv : ∃ v, p = .var v
    · obtain ⟨v, rfl⟩ := hv
      have hnk : ∀ y, Comes S n (.var v) y → y = (n, .var v) := by
        intro y hy
        rcases hy.inv with h | ⟨f, args, ks, m, a, hu, -⟩
        · exact h
        · simp [unspine] at hu
      refine ⟨fun ats h => ?_, fun h => ?_⟩
      · simp only [Sorts.push, Sorts.pushK, Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨fun a => ?_, ?_⟩
        · obtain ⟨x, m⟩ := a
          simp only [List.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩; exact .root
          · intro hc
            have := hnk _ hc
            simp only [Prod.mk.injEq, Term.var.injEq] at this
            exact ⟨this.2, this.1⟩
        · rintro ⟨x, f, args, hx, hu, -⟩
          rw [hnk x hx] at hu
          simp [unspine] at hu
      · simp [Sorts.push, Sorts.pushK] at h
    · have hnv : ∀ v, p ≠ .var v := fun v e => hv ⟨v, e⟩
      obtain ⟨f, hf⟩ := unspine_head p [] hfo hnv
      have hun : unspine p [] = (.sym f, (unspine p []).2) := Prod.ext hf rfl
      have harg : ∀ {o : Option Name} {a : Pat} {ks : List (Option Name)},
          (o, a) ∈ ks.zip (unspine p []).2 → a.size ≤ k ∧ a.firstOrder = true := by
        intro o a ks hz
        rcases unspine_mem p [] a (List.of_mem_zip hz).2 with h | ⟨-, h2, h3⟩
        · cases h
        · exact ⟨by omega, h3 hfo⟩
      refine ⟨fun ats h => ?_, fun h => ?_⟩
      · simp only [Sorts.push, Option.map_eq_some_iff] at h
        obtain ⟨⟨ks, ats'⟩, hK, rfl⟩ := h
        obtain ⟨hs, hkid, hm⟩ := pushK_some p n 0 f hf ks ats' hK
        rw [Nat.add_zero] at hs
        refine ⟨fun a => ?_, ?_⟩
        · rw [hm a]
          constructor
          · rintro ⟨m, arg, bs, hz, hp, ha⟩
            obtain ⟨h1, h2⟩ := harg hz
            exact Comes.trans (.kid .root hun hs hz) (((ih arg m h1 h2).1 bs hp).1 a |>.1 ha)
          · intro hc
            rcases hc.inv with e | ⟨f', args', ks', m, arg, hu', hs', hz, hc'⟩
            · simp only [Prod.mk.injEq] at e
              exact absurd e.2.symm (hnv _)
            · rw [hun] at hu'
              simp only [Prod.mk.injEq, Term.sym.injEq] at hu'
              obtain ⟨rfl, hargs⟩ := hu'
              rw [← hargs] at hs' hz
              rw [hs] at hs'
              simp only [Option.some.injEq] at hs'
              subst hs'
              obtain ⟨bs, hp⟩ := hkid m arg hz
              obtain ⟨h1, h2⟩ := harg hz
              exact ⟨m, arg, bs, hz, hp, (((ih arg m h1 h2).1 bs hp).1 a).2 hc'⟩
        · rintro ⟨x, g, args', hx, hu, hsn⟩
          rcases hx.inv with rfl | ⟨f', args'', ks', m, arg, hu', hs', hz, hc'⟩
          · rw [hun] at hu
            simp only [Prod.mk.injEq, Term.sym.injEq] at hu
            obtain ⟨rfl, hargs⟩ := hu
            rw [← hargs, hs] at hsn
            cases hsn
          · rw [hun] at hu'
            simp only [Prod.mk.injEq, Term.sym.injEq] at hu'
            obtain ⟨rfl, hargs⟩ := hu'
            rw [← hargs] at hs' hz
            rw [hs] at hs'
            simp only [Option.some.injEq] at hs'
            subst hs'
            obtain ⟨bs, hp⟩ := hkid m arg hz
            obtain ⟨h1, h2⟩ := harg hz
            exact ((ih arg m h1 h2).1 bs hp).2 ⟨x, g, args', hc', hu, hsn⟩
      · simp only [Sorts.push, Option.map_eq_none_iff] at h
        rcases pushK_none p n 0 f hf h with hs | ⟨ks, m, arg, hs, hz, hp⟩
        · rw [Nat.add_zero] at hs
          exact ⟨(n, p), f, _, .root, hun, hs⟩
        · rw [Nat.add_zero] at hs
          obtain ⟨h1, h2⟩ := harg hz
          obtain ⟨x, g, args', hx, hu, hsn⟩ := (ih arg m h1 h2).2 hp
          exact ⟨x, g, args', Comes.trans (.kid .root hun hs hz) hx, hu, hsn⟩

end RwLogVerified
