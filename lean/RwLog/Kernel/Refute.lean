/-
# Simplifying a non-ground span by its theory

A rule `H₁, …, Hₙ <=> B` means that, in every model of the theory, the heads
all hold exactly when the body holds. The engine uses this as a rewrite on a
span's store: when the heads match members of the store (one-way, the store's
variables are rigid), those members are replaced by the body instantiated by
the match. In every ground instance the models containing the store are then
exactly the models containing the successor, and the same holds with any
further atoms beside it, so a step changes no span's meaning in any context.
Two matched heads may land on one member, and an atom of the body may already
be in the store; both are instances of the rule's axiom and need no special
case. A rule keeps a constraint by writing it back in its body.

A body's equations, instantiated by the match, are solved over the store's
variables. So a symbolic firing has three outcomes:

* `refuted`: the body is `fail`, or its equations have no common instance, so
  no model contains any ground instance of the store;
* `next c`: the equations hold syntactically, and the store becomes `c`;
* `bind θ`: the equations have a most general unifier `θ` that is not the
  identity. A ground instance that `θ` does not cover makes the body false, so
  no model contains it, and instantiating the whole span by `θ` keeps exactly
  the instances some model can contain. Equations never enter the store.

The engine takes a `next` firing only from a decreasing rule
(`TRule.decreasing`, a check on the rule itself) and only when it lowers
`storeWeight`, a measure on the symbolic store. The weight makes every search
below terminate by construction, for every theory. The rule check makes the
choice stable under instantiation: a single-head decreasing rule lowers the
weight of every instance it fires on, so whatever fires on a span fires on
each of its instances. A firing that changes nothing, such as a write-back rule
firing on what it writes back, is not decreasing, so it is never taken.
Leaving a firing untaken never changes a meaning, because every firing
preserves it; it can only leave a refutation unfound.

* `Theory.refutes? T c` follows `refuted` firings and weight-lowering `next`
  firings, over every rule and every match, and answers whether some path
  refutes `c` (obligation `Kernel.refutes_sound`).
* `Theory.bind? T c` finds, along the same paths, an equation instantiation the
  theory forces on `c`.
* `Theory.normalize T c` commits to the first weight-lowering firing, again and
  again, until none is left.
* `Theory.simplify T s` drops `s` when it is refuted, instantiates it by every
  forced equation, and then normalizes its store.

A non-identity most general unifier eliminates at least one variable of the
store, and no firing adds one (every variable of a rule's body occurs in its
heads), so a span is instantiated at most as many times as its store has
variables (obligation `Kernel.simplify_stable`).
-/
import RwLog.Kernel.Match

namespace RwLog

/-- The result of one symbolic firing. -/
inductive Firing where
  | refuted
  | next (c : Store)
  | bind (θ : Nat → Pat)

/-- Solve the equations of a firing whose successor store is `c`. -/
def firingOfEqs (eqs : List (Pat × Pat)) (c : Store) : Firing :=
  if eqs.all fun e => e.1 = e.2 then .next c
  else match solve eqs with
    | none => .refuted
    | some θ => .bind θ

/-- Replace the matched members `ms` of the store `c` by the atoms `bs`. A
store is a set, so copies are kept once. -/
def Store.replace (c ms bs : Store) : Store :=
  (c.filter (fun a => !ms.contains a) ++ bs).eraseDups

/-- `u` is smaller than `t` under every substitution: it is smaller, and no
variable occurs more often in `u` than in `t`. -/
def Pat.smaller (u t : Pat) : Bool :=
  decide (u.size < t.size) && u.vars.all fun v => decide (u.vars.count v ≤ t.vars.count v)

/-- A rule decreases when, once its equations hold (under their most general
unifier `μ`), its body is smaller than its heads in the multiset extension of
`Pat.smaller`: after cancelling the atoms it writes back, some head is left and
every other body atom is smaller than a head that is left. This is a property
of the rule, so a firing of a decreasing rule on a store is a decreasing
firing on every instance of the store. A rule whose equations have no unifier
never takes a step. -/
def TRule.decreasing (ρ : TRule) : Bool :=
  match ρ.body with
  | .fail => true
  | .conj eqs cs =>
    match solve eqs with
    | none => true
    | some μ =>
      let H := ρ.heads.map (Term.bind μ)
      let B := cs.map (Term.bind μ)
      let H' := H.diff B
      !H'.isEmpty && (B.diff H).all fun b => H'.any fun h => Pat.smaller b h

/-- All symbolic firings of one rule on a store, one for each match of its
heads. -/
def TRule.firings (ρ : TRule) (c : Store) : List Firing :=
  (matchAll ρ.heads c []).map fun r =>
    match ρ.body with
    | .fail => .refuted
    | .conj eqs cs =>
      firingOfEqs (eqs.map fun e => (e.1.bind r.1.apply, e.2.bind r.1.apply))
        (c.replace r.2 (cs.map (Term.bind r.1.apply)))

/-- The largest number of atoms a rule body adds, plus one. -/
def Theory.base (T : Theory) : Nat :=
  1 + T.foldl (fun m ρ => max m ρ.body.atoms.length) 0

/-- The measure a firing must lower to be taken: each atom of size `n` weighs
`base ^ n`, so trading an atom for fewer than `base` strictly smaller ones
lowers it. -/
def Theory.storeWeight (T : Theory) (c : Store) : Nat := (c.map fun a => T.base ^ a.size).sum

/-- Some path of refuting and weight-lowering firings refutes the store. -/
def Theory.refutes? (T : Theory) (c : Store) : Bool :=
  T.any fun ρ => (ρ.firings c).any fun
    | .refuted => true
    | .next c' =>
      if ρ.decreasing then (if T.storeWeight c' < T.storeWeight c then T.refutes? c' else false)
      else false
    | .bind _ => false
termination_by T.storeWeight c

/-- The first equation instantiation reachable along weight-lowering firings. -/
def Theory.bind? (T : Theory) (c : Store) : Option (Nat → Pat) :=
  T.findSome? fun ρ => (ρ.firings c).findSome? fun
    | .refuted => none
    | .next c' =>
      if ρ.decreasing then (if T.storeWeight c' < T.storeWeight c then T.bind? c' else none)
      else none
    | .bind θ => some θ
termination_by T.storeWeight c

/-- The first weight-lowering firing on the store. -/
def Theory.step? (T : Theory) (c : Store) :
    Option {c' : Store // T.storeWeight c' < T.storeWeight c} :=
  T.findSome? fun ρ => (ρ.firings c).findSome? fun
    | .next c' =>
      if h : ρ.decreasing && T.storeWeight c' < T.storeWeight c then some ⟨c', by simp_all⟩ else none
    | _ => none

/-- Take weight-lowering firings until none is left. -/
def Theory.normalize (T : Theory) (c : Store) : Store :=
  match T.step? c with
  | none => c
  | some c' => T.normalize c'.1
termination_by T.storeWeight c
decreasing_by exact c'.2

/-- Instantiate a span. Atoms that become equal are kept once: a ground store
is a set, so this does not change the span's ground triples. -/
def Span.inst (s : Span) (θ : Nat → Pat) : Span :=
  ⟨s.l.bind θ, s.r.bind θ, (s.c.map (Term.bind θ)).eraseDups⟩

/-- The distinct variables of a store. -/
def Store.varCount (c : Store) : Nat := (c.flatMap Term.vars).eraseDups.length

/-- Simplify with a budget of `n` instantiations: `none` when the span is
refuted. -/
def Theory.simplifyWithin (T : Theory) : Nat → Span → Option Span
  | n, s =>
    if T.refutes? s.c then none
    else match n, T.bind? s.c with
      | n + 1, some θ => T.simplifyWithin n (s.inst θ)
      | _, _ => some ⟨s.l, s.r, T.normalize s.c⟩

/-- Simplify a span by its theory: drop it when the theory refutes it,
instantiate it by every equation the theory forces, and normalize its store.

The budget is a bound, not tuning: an instantiation removes a variable of the
store and a firing never adds one, so there are at most as many instantiations
as the store has variables (obligation `Kernel.simplify_stable`). -/
def Theory.simplify (T : Theory) (s : Span) : Option Span :=
  T.simplifyWithin s.c.varCount s

end RwLog
