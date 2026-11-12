/-
# Refuting a non-ground store

`Theory.refutes? T c` decides whether the rules of `T` derive `fail` from the
store `c` symbolically, in a way that is sound for every ground instance:
whenever it answers `true`, every ground instance of `c` is refuted
(obligation `Kernel.refutes_sound`). The engine prunes exactly the spans whose
store it refutes.

A symbolic firing of a rule matches the rule's heads onto members of the
store (one-way: the store's variables are rigid). Two conditions keep it
sound for every instance:

* the matched members must be pairwise apart (no common instance), so they
  stay distinct members in every ground instance, as `TRule.Fires` requires;
* when the body replaces the matched members, every member that has a common
  instance with one of them is dropped as well. In a ground instance where
  such a member coincides with a matched one, the ground firing removes it;
  dropping it symbolically keeps the symbolic successor a subset of every
  ground successor, and refutation is monotone (`Refutes.mono`).

Search terminates for decreasing theories (`Theory.Decreasing`, part of
`Program.WellFormed`): every firing lowers `storeWeight`, so a refutation, if
one exists, is found within `storeWeight T c + 1` firings
(obligation `Kernel.refutes_complete_symbolic`). The weight is the derivation
length bound, not a tuning constant.
-/
import RwLog.Kernel.Match

namespace RwLog

/-- The result of one symbolic firing. -/
inductive Firing where
  | refuted
  | next (c : Store)

/-- All symbolic firings of one rule on a store. -/
def TRule.firings (ρ : TRule) (c : Store) : List Firing :=
  (matchAll ρ.heads c []).filterMap fun r =>
    if pairwiseApart r.2 then
      some <| match ρ.body with
        | .fail => .refuted
        | .conj cs =>
          .next (c.filter (fun a => r.2.all fun h => !unifiable a h) ++ cs.map (Term.bind r.1.apply))
    else none

/-- The largest number of atoms a rule body adds, plus one. -/
def Theory.base (T : Theory) : Nat :=
  1 + T.foldl (fun m ρ => max m (match ρ.body with | .fail => 0 | .conj cs => cs.length)) 0

/-- A weight that every firing of a decreasing rule strictly lowers: each
atom of size `n` weighs `base ^ n`, and a decreasing firing trades an atom for
fewer than `base` strictly smaller ones. -/
def Theory.storeWeight (T : Theory) (c : Store) : Nat := (c.map fun a => T.base ^ a.size).sum

/-- Search for a symbolic refutation using at most `n` firings. -/
def Theory.refutesWithin (T : Theory) : Nat → Store → Bool
  | 0, _ => false
  | n + 1, c =>
    T.any fun ρ => (ρ.firings c).any fun
      | .refuted => true
      | .next c' => Theory.refutesWithin T n c'

/-- The store is refuted symbolically. -/
def Theory.refutes? (T : Theory) (c : Store) : Bool := T.refutesWithin (T.storeWeight c + 1) c

end RwLog
