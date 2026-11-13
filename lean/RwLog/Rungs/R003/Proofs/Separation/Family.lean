/-
# The separating family: spans, expressions, table keys

Facts about `sepFam k` that mention no machine. The table key of the query is
`cRel k`: the query with the two spans of every choice in sorted order,
`$x -> z` before `z -> z`. Composing any chain of the two spans gives its
first span back, so every chain composes.
-/
import RwLog.Rungs.R003.Spec
import RwLog.Rungs.Framework.CostCalculus
import RwLog.Rungs.Framework.Cost
import RwLog.Kernel.Covers
import Mathlib.Tactic.Ring

namespace RwLog

namespace R003

namespace Sep

open Cost R001

/-! ## The two spans -/

/-- `$x -> z`, the one answer. -/
abbrev xz : Span := ⟨.var 0, .sym "z", []⟩

/-- `z -> z`. -/
abbrev zz : Span := ⟨.sym "z", .sym "z", []⟩

/-- One of the two spans of a choice. -/
def Good (s : Span) : Prop := s = xz ∨ s = zz

theorem good_xz : Good xz := Or.inl rfl
theorem good_zz : Good zz := Or.inr rfl

theorem enc_inl_zero : enc (Sum.inl 0) = 0 := by simp [enc, Equiv.natSumNatEquivNat]

theorem compose_xz {s : Span} (h : Good s) : xz.compose s = some xz := by
  rcases h with rfl | rfl
  · simp [Span.compose, Pat.left, Pat.right, Term.rename, solve, Eqns.subst, finish, RwLog.extend,
      Term.single, enc_inl_zero]
  · simp [Span.compose, Pat.left, Pat.right, Term.rename, solve, finish, enc_inl_zero]

theorem compose_zz {s : Span} (h : Good s) : zz.compose s = some zz := by
  rcases h with rfl | rfl
  · simp [Span.compose, Pat.left, Pat.right, Term.rename, solve, Eqns.subst, finish]
  · simp [Span.compose, Pat.left, Pat.right, Term.rename, solve, finish]

/-- Composing two of the spans gives the first one. -/
theorem compose_good {a b : Span} (ha : Good a) (hb : Good b) : a.compose b = some a := by
  rcases ha with rfl | rfl
  · exact compose_xz hb
  · exact compose_zz hb

theorem size_good {s : Span} (h : Good s) : s.size = 2 := by
  rcases h with rfl | rfl <;> simp [Span.size, Store.size, Term.size]

theorem sum_size_good : ∀ {L : List Span}, (∀ s ∈ L, Good s) → (L.map Span.size).sum = 2 * L.length
  | [], _ => rfl
  | s :: L, h => by
    have ih := sum_size_good (L := L) fun t ht => h t (by simp [ht])
    simp only [List.map_cons, List.sum_cons, List.length_cons, size_good (h s (by simp)), ih]
    omega

theorem foldl_compose_good (a : Span) : ∀ L : List Span, (∀ s ∈ L, Good s) → Good a →
    L.foldl (fun acc t => acc.bind (·.compose t)) (some a) = some a
  | [], _, _ => rfl
  | s :: L, h, ha => by
    simp only [List.foldl_cons, Option.bind_some, compose_good ha (h s (by simp))]
    exact foldl_compose_good a L (fun t ht => h t (by simp [ht])) ha

/-- Every chain of the two spans composes. -/
theorem chain_good {L : List Span} (h : ∀ s ∈ L, Good s) : (Span.chain L).isSome = true := by
  cases L with
  | nil => rfl
  | cons a L =>
    simp only [Span.chain]
    rw [foldl_compose_good a L (fun t ht => h t (by simp [ht])) (h a (by simp))]
    rfl

theorem rightIface_good {s : Span} (h : Good s) : s.rightIface = zz := by
  rcases h with rfl | rfl <;> decide

theorem bound_zz : bound zz = some zz := rfl

theorem covers_xz {s : Span} (h : Good s) : xz.covers? s = true := by
  rcases h with rfl | rfl <;> decide

theorem covers_zz_xz : zz.covers? xz = false := by decide

theorem covers_zz_zz : zz.covers? zz = true := by decide

/-! ## The empty theory -/

/-- The family's program: no definitions and no theory. -/
abbrev P0 : Program := ⟨[], []⟩

theorem saturate_nil (c : Store) : Theory.saturate [] c = c := by
  rw [Theory.saturate]
  simp [Theory.newAtoms, Theory.firings]

/-- Simplifying one of the two spans by the empty theory returns it, for
three ticks. -/
theorem live_good {s : Span} (h : Good s) : Costs (Tabled.live [] s) [s] 3 := by
  rcases h with rfl | rfl
  all_goals
    refine ⟨?_, ?_⟩
    · simp [Tabled.live, Charged.simplify, Theory.simplify, Theory.simplifyWithin,
        Theory.refutes?, Theory.firings, Store.varCount]
    · simp [Tabled.live, Charged.simplify, Theory.simplifyCharge, Theory.refutes?,
        Theory.firings, Store.varCount, saturate_nil, Theory.saturateWork_nil, Theory.firingsWork_nil, Theory.size, Span.size, Store.size,
        Term.size]

/-! ## The expressions -/

/-- A choice, as it stands in a table key. -/
abbrev tw : Rel := .or (.span xz) (.span zz)

/-- The table key of `sepRel j`. -/
def cRel : Nat → Rel
  | 0 => tw
  | j + 1 => .seq tw (cRel j)

theorem canon_twoWays : canon twoWays = tw := by
  simp [twoWays, Rel.at_, Rel.rw, canon, orBranches, sortedBranches, relCmp, spanCmp, patCmp,
    List.eraseDups_cons, mkOr]

theorem canon_tw : canon tw = tw := by
  simp [canon, orBranches, sortedBranches, relCmp, spanCmp, patCmp, List.eraseDups_cons, mkOr]

theorem canon_sepRel : ∀ k, canon (sepRel k) = cRel k
  | 0 => canon_twoWays
  | k + 1 => by rw [sepRel, canon, canon_twoWays, canon_sepRel k, cRel]

theorem canon_cRel : ∀ k, canon (cRel k) = cRel k
  | 0 => canon_tw
  | k + 1 => by rw [cRel, canon, canon_tw, canon_cRel k]

theorem size_tw : tw.size = 7 := by simp [Rel.size, Span.size, Store.size, Term.size]

theorem size_cRel : ∀ j, (cRel j).size = 8 * j + 7
  | 0 => size_tw
  | j + 1 => by rw [cRel, Rel.size, size_tw, size_cRel j]; omega

theorem cRel_zero_ne_succ (j : Nat) : cRel 0 ≠ cRel (j + 1) := by simp [cRel]

/-- The goal of `cRel j`, and the goal of a span, with no boundaries. -/
abbrev gC (j : Nat) : Goal := ⟨none, cRel j, none⟩
abbrev gS (s : Span) : Goal := ⟨none, .span s, none⟩

theorem calls_sepRel : ∀ k, (sepRel k).calls = []
  | 0 => by simp [sepRel, twoWays, Rel.calls, Rel.at_, Rel.rw]
  | k + 1 => by
    rw [sepRel, Rel.calls, calls_sepRel k]
    simp [twoWays, Rel.calls, Rel.at_, Rel.rw]

theorem wellFormed (k : Nat) : (sepFam k).1.WellFormed (sepFam k).2 := by
  refine ⟨by simp [sepFam], ?_, by simp [sepFam]⟩
  intro n hn
  simp [sepFam, calls_sepRel] at hn

end Sep

end R003

end RwLog
