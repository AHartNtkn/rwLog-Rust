/-
# Facts about sorts and first-order spans

A program that declares no sort is well formed in its sorts: no term belongs
to a sort that is not declared, and every ground term belongs to all of no
sorts, which are infinitely many terms.

A span with its sides exchanged is first-order when the span is.
-/
import RwLog.Trusted.Semantics

namespace RwLog

theorem Span.firstOrder_swap (s : Span) : s.swap.firstOrder = s.firstOrder := by
  simp only [Span.firstOrder, Span.swap, Bool.and_comm]

/-- `s (s (… z))`, `n` deep, as a ground term. -/
def gtower : Nat → GTerm
  | 0 => .sym "z"
  | n + 1 => .app (.sym "s") (gtower n)

theorem gtower_injective : Function.Injective gtower := by
  intro m
  induction m with
  | zero => intro n h; cases n with
    | zero => rfl
    | succ n => cases h
  | succ m ih => intro n h; cases n with
    | zero => cases h
    | succ n =>
      simp only [gtower, Term.app.injEq, true_and] at h
      rw [ih h]

/-- There are infinitely many ground terms. -/
theorem GTerm.univ_infinite : (Set.univ : Set GTerm).Infinite :=
  Set.infinite_of_injective_forall_mem gtower_injective fun _ => Set.mem_univ _

/-- No term belongs to a sort when none is declared. -/
theorem Sorts.not_mem_nil {n : Name} {t : GTerm} : ¬ Sorts.Mem [] n t := by
  intro h
  cases h with
  | case h _ _ _ => cases h
  | rest h _ _ _ _ _ => cases h

/-- No sorts are well-formed sorts. -/
theorem Sorts.wellFormed_nil : Sorts.WellFormed [] := by
  intro ns
  cases ns with
  | nil =>
    refine .inr (.inr ?_)
    have : {t : GTerm | ∀ n ∈ ([] : List Name), Sorts.Mem [] n t} = Set.univ := by
      ext; simp
    rw [this]
    exact GTerm.univ_infinite
  | cons n ns =>
    refine .inl (Set.eq_empty_of_forall_notMem fun t h => ?_)
    exact Sorts.not_mem_nil (h n List.mem_cons_self)

end RwLog
