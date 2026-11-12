/-
# One-way matching, coverage and unifiability

* `matchInto p t θ` extends the partial substitution `θ` so that `p`
  instantiated by it is `t`. Only the variables of `p` are bound; the
  variables of `t` are rigid, so `p` and `t` live in separate namespaces.
* `matchAll ps ts θ` lists every way to send each pattern of `ps` to some
  member of `ts` under one common extension of `θ`.
* `Span.covers? a s` decides whether `a` covers `s` (`Span.Covers`): match
  `a`'s two sides onto `s`'s and every constraint of `a` onto some constraint
  of `s`.
* `unifiable a b` decides whether two patterns over one namespace have a
  common instance; `unifiableApart a b` does so for patterns from separate
  namespaces.

The specifications these must meet are stated in `Rungs/R001/Spec.lean`
(`Kernel` obligations).
-/
import RwLog.Kernel.Span

namespace RwLog

/-- A partial substitution, as an association list. -/
abbrev PSubst := List (Nat × Pat)

/-- Apply a partial substitution; unbound variables are left as they are. -/
def PSubst.apply (θ : PSubst) (v : Nat) : Pat := (θ.lookup v).getD (.var v)

/-- One-way matching of `p` onto `t`, extending `θ`. -/
def matchInto : Pat → Pat → PSubst → Option PSubst
  | .var v, t, θ =>
    match θ.lookup v with
    | some u => if u = t then some θ else none
    | none => some ((v, t) :: θ)
  | .sym f, .sym g, θ => if f = g then some θ else none
  | .app p q, .app t u, θ => (matchInto p t θ).bind (matchInto q u)
  | _, _, _ => none

/-- Every way to match each pattern of `ps` onto some member of `ts` under a
common extension of `θ`, with the members chosen, in order. -/
def matchAll : List Pat → List Pat → PSubst → List (PSubst × List Pat)
  | [], _, θ => [(θ, [])]
  | p :: ps, ts, θ =>
    ts.flatMap fun t =>
      match matchInto p t θ with
      | some θ' => (matchAll ps ts θ').map fun r => (r.1, t :: r.2)
      | none => []

/-- `a` covers `s`, decided by matching. -/
def Span.covers? (a s : Span) : Bool :=
  match (matchInto a.l s.l []).bind (matchInto a.r s.r) with
  | none => false
  | some θ => !(matchAll a.c s.c θ).isEmpty

/-- Two patterns over one namespace have a common instance. -/
def unifiable (a b : Pat) : Bool := (solve [(a, b)]).isSome

/-- Two patterns from separate namespaces have a common instance: their
variables are renamed apart first. -/
def unifiableApart (a b : Pat) : Bool := (solve [(Pat.left a, Pat.right b)]).isSome

/-- No two members of the list have a common instance. -/
def pairwiseApart : List Pat → Bool
  | [] => true
  | a :: as => as.all (fun b => !unifiable a b) && pairwiseApart as

end RwLog
