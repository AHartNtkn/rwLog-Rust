/-
# Tier 0 proofs, part 0: what refutation and simplification keep

* A store contained in another is refuted only if the larger one is
  (`refutes_mono`). The closure only adds atoms, so every firing on the
  smaller store's closure is a firing on the larger one's. This keeps the
  interfaces of an unrefuted answer unrefuted (`prompt_pruning`).
* Simplifying a span instantiates its two sides, so every pair of terms the
  result relates (whatever its store) the original relates too
  (`simplify_pairs`).
-/
import RwLog.Rungs.R001.Proofs.Kernel

namespace RwLog

namespace R001

namespace Tier0

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  cases l with
  | nil => simp
  | cons a as =>
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨by simp, ih _ ?_ _ rfl⟩
    have := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons] at h
    omega

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

end Tier0

end R001

end RwLog
