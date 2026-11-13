/-
# Sizes

The sizes of `Trusted/Cost.lean` are what the cost model charges by. Every
term (`Term.size_pos`, in `Solve.lean`), span and expression has size at least one, and converse does not change
the size of a span.
-/
import RwLog.Trusted.Cost
import RwLog.Kernel.Solve

namespace RwLog

theorem Span.size_pos (s : Span) : 1 ≤ s.size := by
  have := Term.size_pos s.l
  unfold Span.size
  omega

theorem Span.size_swap (s : Span) : s.swap.size = s.size := by
  simp only [Span.size, Span.swap]
  omega

theorem Rel.size_pos (e : Rel) : 1 ≤ e.size := by
  cases e <;> simp only [Rel.size] <;> omega

end RwLog
