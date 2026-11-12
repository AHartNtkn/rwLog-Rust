/-
# Simplifying a non-ground span by its theory

A symbolic firing of a rule matches the rule's heads onto members of a store
(one-way: the store's variables are rigid). Two conditions keep it sound for
every ground instance:

* the matched members must be pairwise apart (no common instance), so they
  stay distinct members in every ground instance, as `TRule.Fires` requires;
* when the body replaces the matched members, every member that has a common
  instance with one of them is dropped as well. In a ground instance where
  such a member coincides with a matched one, the ground firing removes it;
  dropping it symbolically keeps the symbolic successor a subset of every
  ground successor, and refutation is monotone (`Refutes.mono`).

A body's equations, instantiated by the match, are solved over the store's
variables. On a ground store an equation is a test, so a symbolic firing has
three outcomes:

* `refuted`: the body is `fail`, or its equations have no common instance, so
  the firing refutes every ground instance;
* `next c`: the equations hold syntactically, so they hold in every ground
  instance and the firing continues with the successor store `c`;
* `bind θ`: the equations have a most general unifier `θ` that is not the
  identity. Every ground instance that `θ` does not cover fails the test and
  is refuted, so instantiating the whole span by `θ` keeps exactly its
  unrefuted instances. The equations never enter the store.

`Theory.refutes? T c` decides, from the store alone, that every ground
instance of `c` is refuted (obligation `Kernel.refutes_sound`); it follows
`refuted` and `next` firings only. `Theory.simplify T s` instantiates the span
`s` by every equation its theory forces, replaces each atom that only one
single-head rule can fire on by that rule's body (`Theory.soleFiring`), and
drops the span if it is refuted.

Replacing an atom by a rule body is sound only when nothing else could use the
atom: refutation is existential over firings, so with `(pin $x) <=> $x = z.`
and `(pin z), bad <=> fail.` the store `{(pin z)}` is refuted in the context
`{bad}` while the empty store is not. A sole firing is exactly the case where
the replacement keeps the store's meaning in every context.

Bounds, all proved rather than tuned:

* Search terminates for decreasing theories (`Theory.Decreasing`, part of
  `Program.WellFormed`): every firing lowers `storeWeight`, so every symbolic
  derivation has at most `storeWeight T c` firings
  (obligation `Kernel.refutes_complete_symbolic`).
* Every variable of a rule body occurs in its heads, so the equations of a
  firing mention only the store's variables, and a non-identity most general
  unifier eliminates at least one of them. A span is therefore instantiated at
  most as many times as its store has variables
  (obligation `Kernel.simplify_stable`).
-/
import RwLog.Kernel.Match

namespace RwLog

/-- The result of one symbolic firing. -/
inductive Firing where
  | refuted
  | next (c : Store)
  | bind (θ : Nat → Pat)

/-- Solve the equations of a firing. -/
def firingOfEqs (eqs : List (Pat × Pat)) (c : Store) : Firing :=
  if eqs.all fun e => e.1 = e.2 then .next c
  else match solve eqs with
    | none => .refuted
    | some θ => .bind θ

/-- All symbolic firings of one rule on a store. -/
def TRule.firings (ρ : TRule) (c : Store) : List Firing :=
  (matchAll ρ.heads c []).filterMap fun r =>
    if pairwiseApart r.2 then
      some <| match ρ.body with
        | .fail => .refuted
        | .conj eqs cs =>
          firingOfEqs (eqs.map fun e => (e.1.bind r.1.apply, e.2.bind r.1.apply))
            (c.filter (fun a => r.2.all fun h => !unifiable a h) ++ cs.map (Term.bind r.1.apply))
    else none

/-- The largest number of atoms a rule body adds, plus one. -/
def Theory.base (T : Theory) : Nat :=
  1 + T.foldl (fun m ρ => max m ρ.body.atoms.length) 0

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
      | .bind _ => false

/-- Every ground instance of the store is refuted, found symbolically. -/
def Theory.refutes? (T : Theory) (c : Store) : Bool := T.refutesWithin (T.storeWeight c + 1) c

/-- The first equation instantiation reachable within `n` firings. -/
def Theory.bindWithin (T : Theory) : Nat → Store → Option (Nat → Pat)
  | 0, _ => none
  | n + 1, c =>
    T.findSome? fun ρ => (ρ.firings c).findSome? fun
      | .refuted => none
      | .next c' => Theory.bindWithin T n c'
      | .bind θ => some θ

/-- An equation instantiation the theory forces on the store, if any. -/
def Theory.bind? (T : Theory) (c : Store) : Option (Nat → Pat) :=
  T.bindWithin (T.storeWeight c + 1) c

/-- Instantiate a span. Atoms that become equal are kept once: a ground store
is a set, so this does not change the span's ground triples. -/
def Span.inst (s : Span) (θ : Nat → Pat) : Span :=
  ⟨s.l.bind θ, s.r.bind θ, (s.c.map (Term.bind θ)).eraseDups⟩

/-- The distinct variables of a store. -/
def Store.varCount (c : Store) : Nat := (c.flatMap Term.vars).eraseDups.length

/-- Every head of the theory, with its rule's index and its own index. -/
def Theory.indexedHeads (T : Theory) : List ((Nat × Nat) × Pat) :=
  T.zipIdx.flatMap fun (ρ, i) => ρ.heads.zipIdx.map fun (h, j) => ((i, j), h)

/-- The body that replaces the atom `a` when `a` admits a sole firing: a
single-head rule matches `a`, its equations hold syntactically under the
match, and no other head of the theory has a common instance with `a`. Every
ground instance of `a` can then be fired on only by that rule, and firing it
removes the instance and adds the body, so in every context a store with `a`
is refuted exactly when the store with `a` replaced by the body is. -/
def Theory.soleFiring (T : Theory) (a : Pat) : Option (List Pat) :=
  T.zipIdx.findSome? fun (ρ, i) =>
    match ρ.heads, ρ.body with
    | [h], .conj eqs cs =>
      (matchInto h a []).bind fun θ =>
        if (eqs.all fun e => e.1.bind θ.apply = e.2.bind θ.apply) &&
            T.indexedHeads.all (fun (k, h') => k == (i, 0) || !unifiableApart a h') then
          some (cs.map (Term.bind θ.apply))
        else none
    | _, _ => none

/-- Replace the first atom of the store that admits a sole firing by that
firing's body. -/
def Theory.drop? (T : Theory) (c : Store) : Option Store :=
  c.findSome? fun a => (T.soleFiring a).map fun body => (c.filter (· ≠ a) ++ body).eraseDups

/-- Simplify with a budget of `n` instantiations, and of `w` sole firings
between two instantiations: `none` when the span is refuted. -/
def Theory.simplifyWithin (T : Theory) : Nat → Nat → Span → Option Span
  | n + 1, w + 1, s =>
    if T.refutes? s.c then none
    else match T.bind? s.c with
      | some θ =>
        let s' := s.inst θ
        T.simplifyWithin n (T.storeWeight s'.c + 1) s'
      | none => match T.drop? s.c with
        | none => some s
        | some c' => T.simplifyWithin (n + 1) w ⟨s.l, s.r, c'⟩
  | _, _, s => if T.refutes? s.c then none else some s
termination_by n w => (n, w)

/-- Simplify a span by its theory: instantiate it by every equation the theory
forces, replace every atom that admits a sole firing by that firing's body, and
drop the span when the theory refutes it.

The budgets are bounds, not tuning: an instantiation removes a variable of the
store and a sole firing never adds one, so there are at most as many
instantiations as the store has variables; a sole firing of a decreasing rule
lowers `storeWeight`, so between two instantiations there are at most
`storeWeight` of them (obligation `Kernel.simplify_stable`). -/
def Theory.simplify (T : Theory) (s : Span) : Option Span :=
  T.simplifyWithin (s.c.varCount + 1) (T.storeWeight s.c + 1) s

end RwLog
