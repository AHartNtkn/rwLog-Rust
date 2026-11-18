/-
# A machine run on one orientation costs the same in both directions

A machine run on one orientation of its input (`CostedRuntime.oriented`) is
run, on an input, on its converse and on its mirror image, on the same chosen
input. If on a root that is its own converse it shows sets of answers that
are their own converse (`CostedRuntime.SelfConverse`), the three runs show
the same, the right way round (`oriented_trace_conv`, `oriented_trace_dual`).
They cost the same from the first step on; choosing the input costs the same
on the mirror image (`oriented_paid_dual`) and `8 * n + 12` ticks more on the
converse of an input of size `n`, which is one node larger
(`oriented_paid_conv`).

So the cost of such a machine does not depend on the direction a query is
written in, within that sum (`oriented_directionFree`,
`oriented_directionFree_bound`): this is
`DirectionFree` (`Trusted/Cost.lean`), what an admission asks of the cost of
a relation forward and backward.
-/
import RwLog.Rungs.Framework.Oriented
import Mathlib.Tactic.Ring

namespace RwLog

namespace CostedRuntime

variable {C : CostedRuntime}

/-- The run on the converse of a query is the run on the query with every
answer swapped, step for step. -/
theorem oriented_trace_conv (hS : C.SelfConverse) {P : Program} {q : Rel} (hwf : P.WellFormed q)
    (n : Nat) :
    TraceEquiv P.sorts.interp (C.oriented.runtime.trace (C.oriented.start P (.conv q)) n)
      ((C.oriented.runtime.trace (C.oriented.start P q) n).map Shown.swap) :=
  trace_of_mirrors hS hwf.2.2.1 (orient_conv P q) (orient_sorts P q) (progFO_orient hwf)
    (normal_orient_root P q) (fo_orient_root hwf) n

/-- The run on the mirrored query in the mirrored program is the run on the
query with every answer swapped, step for step. -/
theorem oriented_trace_dual (hS : C.SelfConverse) {P : Program} {q : Rel} (hwf : P.WellFormed q)
    (n : Nat) :
    TraceEquiv P.sorts.interp (C.oriented.runtime.trace (C.oriented.start P.dual q.dual) n)
      ((C.oriented.runtime.trace (C.oriented.start P q) n).map Shown.swap) :=
  trace_of_mirrors hS hwf.2.2.1 (orient_dual P q) (orient_sorts P q) (progFO_orient hwf)
    (normal_orient_root P q) (fo_orient_root hwf) n

/-- **The converse costs the same from the first step on.** Run on one
orientation, any machine pays on the converse of a query what it pays on the
query and `8 * n + 12` ticks more for choosing the input, `n` the size of the
input. Nothing is asked of the machine. -/
theorem oriented_paid_conv (C : CostedRuntime) (P : Program) (q : Rel) (n : Nat) :
    C.oriented.paid P (.conv q) n = C.oriented.paid P q n + (8 * (P.size + q.size) + 12) := by
  obtain ⟨hPe, hre, -⟩ := orient_conv P q
  unfold CostedRuntime.paid
  rw [oriented_init_ticks, oriented_init_ticks, oriented_start, oriented_start, oriented_spent,
    oriented_spent, hPe, hre]
  show 4 * (P.size + (1 + q.size) + 1) ^ 2 + _ + _ = _
  ring

/-- A trace swapped twice agrees with the trace. -/
theorem traceEquiv_of_swap {A : Type} [Answer A] {M : Interp} {t t' : List (Shown A)}
    (h : TraceEquiv M t' (t.map Shown.swap)) : TraceEquiv M (t'.map Shown.swap) t :=
  h.map_swap.trans (traceEquiv_swap_swap M t).symm

/-- **The cost of a machine run on one orientation does not depend on the
direction a query is written in**: the machine, the machine run on the
mirror image and the machine run on the converse each cover every level another
has covered, and halt where it has halted, having paid at most what it has paid and `8 * n + 12` ticks, `n` the
size of the input. Asked of the machine: that on a root that is its own
converse it shows sets of answers that are their own converse. -/
theorem oriented_directionFree (hS : C.SelfConverse) :
    DirectionFree C.oriented fun c n => c + (8 * n + 12) := by
  have hmono : ∀ a n n' : Nat, n ≤ n' → a + (8 * n + 12) ≤ a + (8 * n' + 12) :=
    fun a n n' h => by omega
  exact {
  toMirror := neverWorse_of_trace hmono fun P q hwf =>
    ⟨fun m => by
      show TraceEquiv _ (C.oriented.mirror.runtime.trace (C.oriented.start P.dual q.dual) m) _
      rw [mirror_trace]
      exact traceEquiv_of_swap (oriented_trace_dual hS hwf m),
    fun n m hm _ => by
      rw [mirror_paid, oriented_paid_dual]
      exact le_trans (C.oriented.paid_mono P q hm) (Nat.le_add_right _ _)⟩
  ofMirror := neverWorse_of_trace hmono fun P q hwf =>
    ⟨fun m => by
      show TraceEquiv _ _ (C.oriented.mirror.runtime.trace (C.oriented.start P.dual q.dual) m)
      rw [mirror_trace]
      exact (traceEquiv_of_swap (oriented_trace_dual hS hwf m)).symm,
    fun n m hm _ => by
      rw [mirror_paid, oriented_paid_dual]
      exact le_trans (C.oriented.paid_mono P q hm) (Nat.le_add_right _ _)⟩
  toConv := neverWorse_of_trace hmono fun P q hwf =>
    ⟨fun m => by
      show TraceEquiv _ (C.oriented.conv.runtime.trace (C.oriented.start P (.conv q)) m) _
      rw [conv_trace]
      exact traceEquiv_of_swap (oriented_trace_conv hS hwf m),
    fun n m hm _ => by
      rw [conv_paid, oriented_paid_conv]
      exact Nat.add_le_add_right (C.oriented.paid_mono P q hm) _⟩
  ofConv := neverWorse_of_trace hmono fun P q hwf =>
    ⟨fun m => by
      show TraceEquiv _ _ (C.oriented.conv.runtime.trace (C.oriented.start P (.conv q)) m)
      rw [conv_trace]
      exact (traceEquiv_of_swap (oriented_trace_conv hS hwf m)).symm,
    fun n m hm _ => by
      rw [conv_paid, oriented_paid_conv]
      exact le_trans (C.oriented.paid_mono P q hm)
        (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))⟩ }

/-- The same within the bound of an admission: `12 * (c + n + 1)`. -/
theorem oriented_directionFree_bound (hS : C.SelfConverse) :
    DirectionFree C.oriented (PolyBound.fn ⟨12, 1⟩) := by
  have h := oriented_directionFree hS
  have hle : ∀ c n : Nat, c + (8 * n + 12) ≤ PolyBound.fn ⟨12, 1⟩ c n := fun c n => by
    show c + (8 * n + 12) ≤ 12 * (c + n + 1) ^ 1
    rw [Nat.pow_one]
    omega
  exact ⟨h.toMirror.mono hle, h.ofMirror.mono hle, h.toConv.mono hle, h.ofConv.mono hle⟩

end CostedRuntime

end RwLog
